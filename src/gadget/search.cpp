// wsearch - exhaustive search for width-s NRD patterns.
//
//   ./bin/wsearch --k K --s S --r R --W w0,w1,...   [options]      (symmetric)
//   ./bin/wsearch --k K --s S --r R --R <hexmask>   [options]      (general)
//
// Options
//   --mmin/--mmax INT   own-weight window override (default: auto-derived)
//   --sym D             symmetry-break at depths <= D (0 = off, exact counts)
//   --canon             also test canonicity at the leaf (orbit enumeration)
//   --threads T         worker threads (default: hardware concurrency)
//   --emit N            print up to N witnesses, each independently re-verified
//   --u U               known upper-bound exponent, used to report k_max
//   --maxperms N        cap on |Sym(k)| subset used for symmetry breaking
//
// Exit status 0 always; parse "DONE" line for results.
#include "nrd.hpp"

#include <atomic>
#include <chrono>
#include <mutex>
#include <thread>

using namespace nrd;

// ------------------------------------------------------------------ context
struct Ctx {
	int k = 0, s = 0, r = 0, ROWS = 0, OWN = 0, NW = 0, T = 0;
	Predicate P;
	std::vector<EntryType> ty;      // in ord order
	std::vector<std::vector<u64>> spr;
	std::vector<u8> ownbit;
	std::vector<u32> tmask;
	std::vector<std::vector<int8_t>> del;
	u8 sentinel = 0;
	int mMin = 0, mMax = 0;
	std::vector<std::vector<u8>> bad;   // bad[rem] = byte values that cannot survive
	std::vector<std::vector<u8>> ownOk; // ownOk[rem][m]
	std::vector<std::vector<u8>> dOk;   // dOk[rem][dc + r]
	int symDepth = 0;
	bool canon = false;
	int emit = 0;
	std::vector<std::vector<u16>> pact; // pact[perm][ordpos]
	// general-predicate mode
	bool general = false;
	std::vector<std::vector<u8>> extMem, extNon;
};

static Ctx C;
static std::mutex outMx;
static std::atomic<int> rootCursor{0};
static std::atomic<long long> gEmitted{0};

// ------------------------------------------------------------------ worker
struct Worker {
	std::vector<u64> acc;
	std::vector<int8_t> dc;
	std::vector<int> chosen;
	std::vector<u16> img;
	u32 cover = 0;
	int m = 0;
	long long nodes = 0, found = 0;
	long double orbitTotal = 0;
	std::vector<u16> pref;  // general mode: per-row prefix bits

	void init() {
		acc.assign(C.NW, 0);
		for (int w = 0; w < C.NW; w++)
			for (int b = 0; b < 8; b++) {
				const int row = w * 8 + b;
				if (row >= C.ROWS || row == C.OWN)
					acc[w] |= (u64)C.sentinel << (8 * b);
			}
		dc.assign(C.k, 0);
		chosen.assign(C.r, 0);
		img.assign(C.r, 0);
		pref.assign(C.ROWS, 0);
		cover = 0;
		m = 0;
	}

	inline bool rowsOK(int rem) const {
		const std::vector<u8>& bv = C.bad[rem];
		if (bv.empty()) return true;
		for (int w = 0; w < C.NW; w++) {
			const u64 x = acc[w];
			for (u8 b : bv)
				if (hasByte(x, b)) return false;
		}
		return true;
	}

	// Sound partial-canonicity test: prune when some coordinate permutation maps
	// the (sorted) prefix to a lexicographically smaller sorted sequence.
	inline bool lexOK(int d) {
		if (C.pact.empty()) return true;
		for (const auto& pa : C.pact) {
			for (int i = 0; i < d; i++) img[i] = pa[chosen[i]];
			std::sort(img.begin(), img.begin() + d);
			for (int i = 0; i < d; i++) {
				if (img[i] < (u16)chosen[i]) return false;
				if (img[i] > (u16)chosen[i]) break;
			}
		}
		return true;
	}

	inline long long autCount() {
		long long a = 0;
		for (const auto& pa : C.pact) {
			for (int i = 0; i < C.r; i++) img[i] = pa[chosen[i]];
			std::sort(img.begin(), img.begin() + C.r);
			bool eq = true;
			for (int i = 0; i < C.r && eq; i++)
				if (img[i] != (u16)chosen[i]) eq = false;
			if (eq) a++;
		}
		return a ? a : 1;
	}

	// Independent naive re-verification of a completed pattern.
	bool reverify() const {
		for (int v = 0; v < C.ROWS; v++) {
			if (C.general) {
				int t = 0;
				for (int j = 0; j < C.r; j++) t |= (int)C.ty[chosen[j]].val[v] << j;
				const bool in = C.P.mem[t] != 0;
				if (v == C.OWN ? in : !in) return false;
			} else {
				int w = 0;
				for (int j = 0; j < C.r; j++) w += C.ty[chosen[j]].val[v];
				const bool in = C.P.wHas(w);
				if (v == C.OWN ? in : !in) return false;
			}
		}
		u32 cv = 0;
		for (int j = 0; j < C.r; j++) cv |= C.ty[chosen[j]].mask;
		return pc(cv) == C.k;
	}

	void report() {
		if (gEmitted.fetch_add(1) >= C.emit) return;
		const bool ok = reverify();
		std::lock_guard<std::mutex> lk(outMx);
		printf("PATTERN k=%d s=%d r=%d verify=%s entries=", C.k, C.s, C.r,
		       ok ? "OK" : "FAIL");
		for (int j = 0; j < C.r; j++)
			printf("%s%u:%u", j ? "," : "", C.ty[chosen[j]].mask, C.ty[chosen[j]].ftab);
		printf("\n");
		fflush(stdout);
	}

	// ------------------------------------------------ symmetric-predicate DFS
	void recSym(int start, int depth) {
		nodes++;
		if (depth == C.r) {
			if (C.canon && !lexOK(C.r)) return;
			found++;
			if (C.canon) {
				long double fact = 1;
				for (int i = 2; i <= C.k; i++) fact *= i;
				orbitTotal += fact / (long double)autCount();
			}
			if (C.emit) report();
			return;
		}
		const int rem = C.r - depth - 1;
		const std::vector<u8>& ok = C.ownOk[rem];
		const std::vector<u8>& dk = C.dOk[rem];
		for (int ti = start; ti < C.T; ti++) {
			const int nm = m + C.ownbit[ti];
			if (nm > C.mMax || nm + rem < C.mMin || !ok[nm]) continue;
			const u32 nc = cover | C.tmask[ti];
			if (C.k - pc(nc) > rem * C.s) continue;
			const auto& sp = C.spr[ti];
			for (int w = 0; w < C.NW; w++) acc[w] += sp[w];
			bool good = rowsOK(rem);
			if (good) {
				const auto& dl = C.del[ti];
				for (int i = 0; i < C.k; i++) dc[i] = (int8_t)(dc[i] + dl[i]);
				for (int i = 0; i < C.k && good; i++)
					if (!dk[dc[i] + C.r]) good = false;
				if (good) {
					chosen[depth] = ti;
					if (depth + 1 <= C.symDepth && !lexOK(depth + 1)) {
						good = false;
					} else {
						const u32 oc = cover;
						const int om = m;
						cover = nc;
						m = nm;
						recSym(ti, depth + 1);
						cover = oc;
						m = om;
					}
				}
				for (int i = 0; i < C.k; i++) dc[i] = (int8_t)(dc[i] - dl[i]);
			}
			for (int w = 0; w < C.NW; w++) acc[w] -= sp[w];
		}
	}

	// -------------------------------------------------- general-predicate DFS
	void recGen(int depth) {
		nodes++;
		if (depth == C.r) {
			found++;
			if (C.emit) report();
			return;
		}
		const int rem = C.r - depth - 1;
		for (int ti = 0; ti < C.T; ti++) {
			const u32 nc = cover | C.tmask[ti];
			if (C.k - pc(nc) > rem * C.s) continue;
			const auto& vv = C.ty[ti].val;
			bool good = true;
			const auto& em = C.extMem[depth + 1];
			const auto& en = C.extNon[depth + 1];
			for (int v = 0; v < C.ROWS; v++) {
				const u16 np = (u16)(pref[v] | ((u16)vv[v] << depth));
				if (v == C.OWN ? !en[np] : !em[np]) { good = false; break; }
			}
			if (!good) continue;
			chosen[depth] = ti;
			if (depth + 1 <= C.symDepth) {
				bool bad2 = false;
				for (const auto& pa : C.pact) {
					for (int i = 0; i <= depth; i++) {
						const u16 x = pa[chosen[i]];
						if (x < (u16)chosen[i]) { bad2 = true; break; }
						if (x > (u16)chosen[i]) break;
					}
					if (bad2) break;
				}
				if (bad2) continue;
			}
			std::vector<u16> save(pref);
			for (int v = 0; v < C.ROWS; v++) pref[v] |= (u16)vv[v] << depth;
			const u32 oc = cover;
			cover = nc;
			recGen(depth + 1);
			cover = oc;
			pref.swap(save);
		}
	}

	void runRoots() {
		for (;;) {
			const int ti = rootCursor.fetch_add(1);
			if (ti >= C.T) return;
			init();
			if (C.general) {
				const int rem = C.r - 1;
				const u32 nc = C.tmask[ti];
				if (C.k - pc(nc) > rem * C.s) continue;
				const auto& vv = C.ty[ti].val;
				bool good = true;
				for (int v = 0; v < C.ROWS && good; v++) {
					const u16 np = (u16)vv[v];
					if (v == C.OWN ? !C.extNon[1][np] : !C.extMem[1][np]) good = false;
				}
				if (!good) continue;
				chosen[0] = ti;
				if (C.symDepth >= 1) {
					bool bad2 = false;
					for (const auto& pa : C.pact)
						if (pa[ti] < (u16)ti) { bad2 = true; break; }
					if (bad2) continue;
				}
				for (int v = 0; v < C.ROWS; v++) pref[v] = vv[v];
				cover = nc;
				nodes++;
				recGen(1);
			} else {
				const int rem = C.r - 1;
				const int nm = C.ownbit[ti];
				if (nm > C.mMax || nm + rem < C.mMin || !C.ownOk[rem][nm]) continue;
				const u32 nc = C.tmask[ti];
				if (C.k - pc(nc) > rem * C.s) continue;
				const auto& sp = C.spr[ti];
				for (int w = 0; w < C.NW; w++) acc[w] += sp[w];
				if (!rowsOK(rem)) continue;
				const auto& dl = C.del[ti];
				bool good = true;
				for (int i = 0; i < C.k; i++) dc[i] = dl[i];
				for (int i = 0; i < C.k && good; i++)
					if (!C.dOk[rem][dc[i] + C.r]) good = false;
				if (!good) continue;
				chosen[0] = ti;
				if (C.symDepth >= 1 && !lexOK(1)) continue;
				cover = nc;
				m = nm;
				nodes++;
				recSym(ti, 1);
			}
		}
	}
};

// -------------------------------------------------------------------- setup
static std::vector<int> parseInts(const char* s) {
	std::vector<int> v;
	int cur = 0;
	bool any = false;
	for (const char* p = s;; p++) {
		if (*p >= '0' && *p <= '9') { cur = cur * 10 + (*p - '0'); any = true; }
		else { if (any) v.push_back(cur); cur = 0; any = false; if (!*p) break; }
	}
	return v;
}

int main(int argc, char** argv) {
	int k = 0, s = 2, r = 0, u = 0, threads = 0, maxperms = 60000;
	int mMinArg = -1, mMaxArg = -1;
	const char* Wstr = nullptr;
	const char* Rstr = nullptr;
	for (int i = 1; i < argc; i++) {
		std::string a = argv[i];
		auto nx = [&]() { return (i + 1 < argc) ? argv[++i] : (char*)"0"; };
		if (a == "--k") k = atoi(nx());
		else if (a == "--s") s = atoi(nx());
		else if (a == "--r") r = atoi(nx());
		else if (a == "--u") u = atoi(nx());
		else if (a == "--W") Wstr = nx();
		else if (a == "--R") Rstr = nx();
		else if (a == "--mmin") mMinArg = atoi(nx());
		else if (a == "--mmax") mMaxArg = atoi(nx());
		else if (a == "--sym") C.symDepth = atoi(nx());
		else if (a == "--canon") C.canon = true;
		else if (a == "--emit") C.emit = atoi(nx());
		else if (a == "--threads") threads = atoi(nx());
		else if (a == "--maxperms") maxperms = atoi(nx());
	}
	if (!k || !r || (!Wstr && !Rstr)) {
		fprintf(stderr, "usage: wsearch --k K --s S --r R (--W w,w,.. | --R hex) [opts]\n");
		return 2;
	}
	C.k = k; C.s = s; C.r = r;
	C.ROWS = 1 << k; C.OWN = C.ROWS - 1; C.NW = (C.ROWS + 7) / 8;
	C.P.r = r;
	if (Wstr) {
		C.P.symmetric = true;
		C.P.W = parseInts(Wstr);
		C.P.buildMem();
	} else {
		C.general = true;
		C.P.symmetric = false;
		C.P.mem.assign(1 << r, 0);
		const u64 msk = strtoull(Rstr, nullptr, 0);
		for (int t = 0; t < (1 << r); t++) C.P.mem[t] = (msk >> t) & 1;
	}

	// entry types, ordered to front-load own-active high-degree entries
	auto raw = makeTypes(k, s);
	std::vector<int> ord(raw.size());
	std::iota(ord.begin(), ord.end(), 0);
	std::sort(ord.begin(), ord.end(), [&](int a, int b) {
		if (raw[a].ownbit != raw[b].ownbit) return raw[a].ownbit > raw[b].ownbit;
		if (raw[a].deg != raw[b].deg) return raw[a].deg > raw[b].deg;
		if (raw[a].mask != raw[b].mask) return raw[a].mask < raw[b].mask;
		return raw[a].ftab < raw[b].ftab;
	});
	C.ty.reserve(raw.size());
	for (int i : ord) C.ty.push_back(raw[i]);
	C.T = (int)C.ty.size();

	C.ownbit.resize(C.T); C.tmask.resize(C.T); C.del.resize(C.T); C.spr.resize(C.T);
	for (int t = 0; t < C.T; t++) {
		C.ownbit[t] = (u8)C.ty[t].ownbit;
		C.tmask[t] = C.ty[t].mask;
		C.del[t] = C.ty[t].del;
		C.spr[t].assign(C.NW, 0);
		for (int v = 0; v < C.ROWS; v++)
			if (v != C.OWN && C.ty[t].val[v])
				C.spr[t][v / 8] += (u64)1 << (8 * (v % 8));
	}

	if (!C.general) {
		if (C.P.W.empty()) { fprintf(stderr, "empty W\n"); return 2; }
		C.sentinel = (u8)C.P.W[0];
		auto ms = admissibleOwnWeights(C.P, s, k);
		if (ms.empty()) { printf("DONE nodes=0 found=0 (own-weight window empty)\n"); return 0; }
		C.mMin = mMinArg >= 0 ? mMinArg : *std::min_element(ms.begin(), ms.end());
		C.mMax = mMaxArg >= 0 ? mMaxArg : *std::max_element(ms.begin(), ms.end());
		auto ds = admissibleDeltas(C.P, ms);
		C.bad.assign(r + 1, {});
		C.ownOk.assign(r + 1, std::vector<u8>(r + 2, 0));
		C.dOk.assign(r + 1, std::vector<u8>(2 * r + 2, 0));
		for (int rem = 0; rem <= r; rem++) {
			for (int v = 0; v <= r; v++) {
				bool ok = false;
				for (int w : C.P.W) if (w >= v && w <= v + rem) ok = true;
				if (!ok) C.bad[rem].push_back((u8)v);
			}
			for (int mm = 0; mm <= r; mm++) {
				bool ok = false;
				for (int x = mm; x <= mm + rem && x <= r; x++) if (!C.P.wHas(x)) ok = true;
				C.ownOk[rem][mm] = ok;
			}
			for (int d = -r; d <= r; d++) {
				bool ok = false;
				for (int dd : ds) if (std::abs(dd - d) <= rem) ok = true;
				C.dOk[rem][d + r] = ok;
			}
		}
		printf("# types=%d mwindow=[%d,%d] admissible_m={", C.T, C.mMin, C.mMax);
		for (size_t i = 0; i < ms.size(); i++) printf("%s%d", i ? "," : "", ms[i]);
		printf("} kmax=%d\n", kMax(s, r, u));
	} else {
		C.extMem.assign(r + 1, {});
		C.extNon.assign(r + 1, {});
		for (int d = 0; d <= r; d++) {
			C.extMem[d].assign(1 << d, 0);
			C.extNon[d].assign(1 << d, 0);
			for (int t = 0; t < (1 << r); t++) {
				const int p = t & ((1 << d) - 1);
				if (C.P.mem[t]) C.extMem[d][p] = 1; else C.extNon[d][p] = 1;
			}
		}
		printf("# types=%d mode=general kmax=%d\n", C.T, kMax(s, r, u));
	}

	// permutation action tables
	if (C.symDepth > 0 || C.canon) {
		const int FT = 1 << (1 << s);
		std::vector<int> idx((size_t)(1 << k) * FT, -1);
		for (int t = 0; t < C.T; t++) idx[(size_t)C.ty[t].mask * FT + C.ty[t].ftab] = t;
		std::vector<int> p(k);
		std::iota(p.begin(), p.end(), 0);
		int made = 0;
		do {
			std::vector<u16> row(C.T);
			for (int t = 0; t < C.T; t++) {
				u32 nm, nf;
				permType(C.ty[t], p, k, nm, nf);
				row[t] = (u16)idx[(size_t)nm * FT + nf];
			}
			C.pact.push_back(std::move(row));
		} while (++made < maxperms && std::next_permutation(p.begin(), p.end()));
		printf("# perms=%zu\n", C.pact.size());
	}
	fflush(stdout);

	if (threads <= 0) threads = (int)std::max(1u, std::thread::hardware_concurrency());
	std::vector<Worker> ws(threads);
	std::vector<std::thread> th;
	const auto t0 = std::chrono::steady_clock::now();
	for (int i = 0; i < threads; i++) th.emplace_back([&, i] { ws[i].runRoots(); });
	for (auto& t : th) t.join();
	const double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

	long long nodes = 0, found = 0;
	long double orb = 0;
	for (auto& w : ws) { nodes += w.nodes; found += w.found; orb += w.orbitTotal; }
	if (C.canon)
		printf("DONE nodes=%lld orbits=%lld total=%.0Lf secs=%.2f\n", nodes, found, orb, secs);
	else
		printf("DONE nodes=%lld found=%lld secs=%.2f\n", nodes, found, secs);
	return 0;
}
