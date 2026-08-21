// ---------------------------------------------------------------------------
// analyze.cpp -- two things the sweep could not do.
//
// MODE "exact":  seeded exhaustive search for the TRUE value of NRD_n(R).
//   The plain DFS in nrdx.hpp starts from bestExact = 0, so the optimistic
//   bound  sz + (N - i) <= bestExact  almost never fires near the root.  Here
//   we seed the incumbent with the best heuristic family first.  Since we only
//   ever need to know whether something STRICTLY better exists, seeding is
//   sound and makes the bound bite immediately.  If the node cap is not hit,
//   the returned value is EXACT -- ground truth against which the heuristic's
//   slack can be measured for the first time.
//
// MODE "dump":  print the best family explicitly, plus permutation-invariant
//   structure (pairwise Hamming distance spectrum, per-member private-
//   constraint counts, level profile).  The point is to find out whether the
//   multi-level families that beat the lifted-OR2 construction have any
//   generalisable shape, or are just metaheuristic noise.
// ---------------------------------------------------------------------------
#include "nrdx.hpp"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <string>
#include <vector>

using namespace nrdx;

struct Target {
	int r;
	std::vector<int> W;
	const char* label;
};

static const Target TARGETS[] = {
    {5, {0, 2, 3}, "R023  arity 5  -- OPEN in Sharma-Velusamy"},
    {5, {1, 2, 4}, "R124  arity 5  -- OPEN in Sharma-Velusamy"},
    {7, {0, 1, 3, 4}, "G7    arity 7  -- two-level gap"},
    {3, {1, 2}, "NAE3  arity 3  -- CONTROL, proven Theta(n^2)"},
    {2, {1, 2}, "OR2   arity 2  -- CONTROL, proven Theta(n^2)"},
};
static const int NT = 5;

static Predicate mk(const Target& t) {
	u32 wm = 0;
	for (int w : t.W) wm |= (1u << w);
	return pred_from_mask(t.r, wm);
}

static long long binom(int n, int k) {
	if (k < 0 || k > n || n < 0) return 0;
	long long r = 1;
	for (int i = 0; i < k; ++i) r = r * (n - i) / (i + 1);
	return r;
}

static std::string bitstr(u32 a, int n) {
	std::string s((size_t)n, '0');
	for (int i = 0; i < n; ++i)
		if ((a >> i) & 1u) s[(size_t)i] = '1';
	return s;
}

// ---------------------------------------------------------------------------
// Heuristic: level-greedy baseline followed by ruin-and-recreate.
// ---------------------------------------------------------------------------
static std::vector<u32> heuristic(const Predicate& P, int n, long iters,
                                  int kmax, uint64_t seed) {
	std::vector<int> levels;
	for (int d = 0; d <= n; ++d) levels.push_back(d);
	const BestResult base = best_lower_bound(P, n, 8, levels);

	Solver sv;
	sv.init(P, n);
	std::vector<u32> cur = base.A, best = base.A;
	std::mt19937_64 rng(seed);
	const u32 N = 1u << n;
	std::vector<u32> all(N);
	for (u32 a = 0; a < N; ++a) all[a] = a;

	for (long it = 0; it < iters; ++it) {
		std::vector<u32> S = cur;
		const int k = 1 + (int)(rng() % (uint64_t)kmax);
		for (int j = 0; j < k && !S.empty(); ++j) {
			const size_t p = (size_t)(rng() % (uint64_t)S.size());
			S[p] = S.back();
			S.pop_back();
		}
		sv.reset();
		for (u32 a : S) sv.try_add(a);
		std::shuffle(all.begin(), all.end(), rng);
		for (u32 a : all)
			if (!sv.inA[a]) sv.try_add(a);
		std::vector<u32> cand = sv.family();
		if (cand.size() >= cur.size()) cur = cand;
		if (cand.size() > best.size()) best = cand;
	}
	return best;
}

// ---------------------------------------------------------------------------
// Seeded exhaustive search.
// ---------------------------------------------------------------------------
struct Exhaustive {
	Solver& sv;
	const std::vector<u32>& ord;
	i64 best = 0;
	i64 nodes = 0, cap = 0;
	bool capHit = false;
	std::vector<u32> bestA;
	std::vector<u32> curA;

	Exhaustive(Solver& s, const std::vector<u32>& o) : sv(s), ord(o) {}

	void dfs(size_t i) {
		if (capHit) return;
		if (++nodes > cap) {
			capHit = true;
			return;
		}
		if (sv.sz > best) {
			best = sv.sz;
			bestA = curA;
		}
		if (i >= ord.size()) return;
		// optimistic bound: even taking every remaining element cannot beat
		// the incumbent
		if (sv.sz + (i64)(ord.size() - i) <= best) return;
		const u32 a = ord[i];
		const size_t mark = sv.undoC.size();
		const bool ok = sv.push_add(a);
		// downward closure: if A + {a} is invalid, so is every superset
		if (ok) {
			curA.push_back(a);
			dfs(i + 1);
			curA.pop_back();
		}
		sv.pop_add(a, mark, ok);
		if (capHit) return;
		dfs(i + 1);
	}
};

static void run_exact(const Target& T, int nlo, int nhi, i64 cap, long iters) {
	const Predicate P = mk(T);
	printf("=== EXACT NRD  %s ===\n", T.label);
	printf(" arity %d  W=%s   node cap = %lld\n", T.r, fmt_W(P).c_str(),
	       (long long)cap);
	printf("  n | heuristic |   EXACT | status     |      nodes | C(n-3,2)+1 |  "
	       "secs\n");
	fflush(stdout);

	for (int n = nlo; n <= nhi; ++n) {
		const auto t0 = std::chrono::steady_clock::now();
		const std::vector<u32> h =
		    heuristic(P, n, iters, 4, 0xABCDEFULL + 31ULL * (uint64_t)n);

		Solver sv;
		sv.init(P, n);
		// Order matters for pruning: try promising (low-weight-first) order.
		std::vector<u32> ord = order_by_weight(n, true);
		Exhaustive ex(sv, ord);
		ex.cap = cap;
		ex.best = (i64)h.size();   // seed the incumbent
		ex.bestA = h;
		sv.reset();
		ex.dfs(0);

		const auto t1 = std::chrono::steady_clock::now();
		const double secs =
		    std::chrono::duration<double>(t1 - t0).count();
		const bool verified = reference_is_nonredundant(P, n, ex.bestA);
		printf("  %2d | %9zu | %7lld | %-10s | %10lld | %10lld |%6.1f%s\n", n,
		       h.size(), (long long)ex.best,
		       ex.capHit ? "CAPPED" : "PROVEN OPT", (long long)ex.nodes,
		       binom(n - 3, 2) + 1, secs, verified ? "" : "  ** CHECK FAIL **");
		fflush(stdout);
	}
	printf("\n");
}

static void run_dump(const Target& T, int n, long iters) {
	const Predicate P = mk(T);
	const std::vector<u32> A =
	    heuristic(P, n, iters, 4, 0xC0FFEEULL + 7919ULL * (uint64_t)n);

	printf("=== STRUCTURE DUMP  %s   n=%d   iters=%ld ===\n", T.label, n,
	       iters);
	printf(" |A| = %zu     C(n,2) = %lld     C(n-3,2)+1 = %lld\n", A.size(),
	       binom(n, 2), binom(n - 3, 2) + 1);
	printf(" reference checker: %s\n",
	       reference_is_nonredundant(P, n, A) ? "VERIFIED" : "** FAILED **");

	// rebuild solver state to read per-member private-constraint counts
	Solver sv;
	sv.init(P, n);
	sv.reset();
	for (u32 a : A) sv.try_add(a);

	std::vector<u32> srt = A;
	std::sort(srt.begin(), srt.end(), [](u32 x, u32 y) {
		const int px = __builtin_popcount(x), py = __builtin_popcount(y);
		if (px != py) return px < py;
		return x < y;
	});

	printf("\n member (bit i = variable i)      wt   private\n");
	for (u32 a : srt)
		printf("   %s   %2d   %7d\n", bitstr(a, n).c_str(),
		       __builtin_popcount(a), sv.cover[a]);

	// permutation-invariant signature: pairwise Hamming distance spectrum
	std::map<int, int> dist;
	for (size_t i = 0; i < srt.size(); ++i)
		for (size_t j = i + 1; j < srt.size(); ++j)
			dist[__builtin_popcount(srt[i] ^ srt[j])]++;
	printf("\n pairwise Hamming distance spectrum:");
	for (const auto& kv : dist) printf("  d%d:%d", kv.first, kv.second);
	printf("\n");

	// column profile: how often each variable is 1 across the family
	printf(" column sums (should be flat if the family is symmetric):");
	for (int c = 0; c < n; ++c) {
		int s = 0;
		for (u32 a : srt) s += (int)((a >> c) & 1u);
		printf(" %d", s);
	}
	printf("\n");

	std::map<int, int> lv;
	for (u32 a : srt) lv[__builtin_popcount(a)]++;
	printf(" level profile:");
	for (const auto& kv : lv) printf(" %d^%d", kv.first, kv.second);
	printf("\n\n");
	fflush(stdout);
}

int main(int argc, char** argv) {
	if (argc < 4) {
		printf("usage:\n");
		printf("  analyze exact <idx> <nlo> <nhi> [capMillions] [iters]\n");
		printf("  analyze dump  <idx> <n> [iters]\n");
		return 2;
	}
	const char* mode = argv[1];
	const int idx = atoi(argv[2]);
	if (idx < 0 || idx >= NT) {
		printf("idx out of range\n");
		return 2;
	}
	const Target& T = TARGETS[idx];

	if (strcmp(mode, "exact") == 0) {
		const int nlo = atoi(argv[3]);
		const int nhi = (argc > 4) ? atoi(argv[4]) : nlo;
		const i64 cap =
		    ((argc > 5) ? (i64)atoll(argv[5]) : (i64)200) * 1000000LL;
		const long iters = (argc > 6) ? atol(argv[6]) : 300;
		if (nlo < T.r + 1 || nhi > 14) {
			printf("n out of supported range\n");
			return 2;
		}
		run_exact(T, nlo, nhi, cap, iters);
	} else if (strcmp(mode, "dump") == 0) {
		const int n = atoi(argv[3]);
		const long iters = (argc > 4) ? atol(argv[4]) : 2000;
		if (n < T.r + 1 || n > 16) {
			printf("n out of supported range\n");
			return 2;
		}
		run_dump(T, n, iters);
	} else {
		printf("unknown mode\n");
		return 2;
	}
	return 0;
}
