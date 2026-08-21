// wrealize - turn a width-s pattern into an explicit CSP instance and PROVE
// non-redundancy by brute force.  This is the step that converts a search hit
// into a theorem: it materialises the variable set, checks that the r variables
// of every constraint are distinct, and verifies that every constraint is
// violated by its own witness and satisfied by every other witness.
//
//   ./bin/wrealize --k K --s S --r R --W w,w,.. --N POOL \
//                  --pattern mask:ftab,mask:ftab,...
//
// Reports n (actual variable count), |I| (constraint count) and the realised
// exponent log|I| / log n, which converges to k/s.
#include "nrd.hpp"

#include <cmath>
#include <map>

using namespace nrd;

static std::vector<int> parseInts(const char* s) {
	std::vector<int> v; int cur = 0; bool any = false;
	for (const char* p = s;; p++) {
		if (*p >= '0' && *p <= '9') { cur = cur * 10 + (*p - '0'); any = true; }
		else { if (any) v.push_back(cur); cur = 0; any = false; if (!*p) break; }
	}
	return v;
}

struct Entry { u32 mask; u32 ftab; int copy; std::vector<int> co; };

int main(int argc, char** argv) {
	int k = 0, s = 2, r = 0, N = 0;
	const char* Wstr = nullptr; const char* pat = nullptr;
	for (int i = 1; i < argc; i++) {
		std::string a = argv[i];
		auto nx = [&]() { return (i + 1 < argc) ? argv[++i] : (char*)"0"; };
		if (a == "--k") k = atoi(nx());
		else if (a == "--s") s = atoi(nx());
		else if (a == "--r") r = atoi(nx());
		else if (a == "--N") N = atoi(nx());
		else if (a == "--W") Wstr = nx();
		else if (a == "--pattern") pat = nx();
	}
	if (!k || !r || !N || !Wstr || !pat) {
		fprintf(stderr, "usage: wrealize --k K --s S --r R --W w,.. --N POOL --pattern m:f,..\n");
		return 2;
	}
	Predicate P; P.r = r; P.symmetric = true; P.W = parseInts(Wstr);

	// --- parse pattern -----------------------------------------------------
	std::vector<Entry> E;
	{
		std::vector<int> nums = parseInts(pat);
		if ((int)nums.size() != 2 * r) {
			fprintf(stderr, "pattern needs %d mask:ftab pairs, got %zu numbers\n", r, nums.size());
			return 2;
		}
		std::map<std::pair<u32, u32>, int> seen;
		for (int j = 0; j < r; j++) {
			Entry e; e.mask = (u32)nums[2 * j]; e.ftab = (u32)nums[2 * j + 1];
			e.copy = seen[{e.mask, e.ftab}]++;
			for (int i = 0; i < k; i++) if ((e.mask >> i) & 1) e.co.push_back(i);
			E.push_back(std::move(e));
		}
	}

	// --- sanity: the pattern must actually be valid on the cube ------------
	{
		const int ROWS = 1 << k, OWN = ROWS - 1;
		for (int v = 0; v < ROWS; v++) {
			int w = 0;
			for (const auto& e : E) {
				int a = 0;
				for (size_t j = 0; j < e.co.size(); j++) if ((v >> e.co[j]) & 1) a |= 1 << j;
				w += (e.ftab >> a) & 1;
			}
			const bool in = P.wHas(w);
			if (v == OWN ? in : !in) {
				printf("INVALID pattern at row %d (weight %d)\n", v, w);
				return 1;
			}
		}
	}

	// --- enumerate the k-subsets of the pool ------------------------------
	std::vector<std::vector<int>> S;
	{
		std::vector<int> c(k);
		std::iota(c.begin(), c.end(), 0);
		for (;;) {
			S.push_back(c);
			int i = k - 1;
			while (i >= 0 && c[i] == N - k + i) i--;
			if (i < 0) break;
			c[i]++;
			for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
		}
	}
	const size_t M = S.size();

	// --- build the variable set -------------------------------------------
	std::map<std::vector<int>, int> vid;   // key = tuple | ftab | copy
	std::vector<std::vector<int>> conVars(M, std::vector<int>(r));
	for (size_t ci = 0; ci < M; ci++) {
		for (int j = 0; j < r; j++) {
			std::vector<int> key;
			for (int a : E[j].co) key.push_back(S[ci][a]);
			key.push_back(-1);
			key.push_back((int)E[j].ftab);
			key.push_back(E[j].copy);
			auto it = vid.find(key);
			if (it == vid.end()) it = vid.emplace(key, (int)vid.size()).first;
			conVars[ci][j] = it->second;
		}
	}
	const int n = (int)vid.size();

	// --- distinctness of the r variables inside each constraint -----------
	size_t dupCon = 0;
	for (size_t ci = 0; ci < M; ci++) {
		std::vector<int> t = conVars[ci];
		std::sort(t.begin(), t.end());
		if (std::adjacent_find(t.begin(), t.end()) != t.end()) dupCon++;
	}

	// --- brute-force non-redundancy ---------------------------------------
	size_t ownMiss = 0, foreignViol = 0;
	std::vector<char> inS(N);
	for (size_t wi = 0; wi < M; wi++) {
		std::fill(inS.begin(), inS.end(), 0);
		for (int p : S[wi]) inS[p] = 1;
		for (size_t ci = 0; ci < M; ci++) {
			int w = 0;
			for (const auto& e : E) {
				int a = 0;
				for (size_t j = 0; j < e.co.size(); j++)
					if (inS[S[ci][e.co[j]]]) a |= 1 << j;
				w += (e.ftab >> a) & 1;
			}
			const bool sat = P.wHas(w);
			if (ci == wi) { if (sat) ownMiss++; }
			else if (!sat) foreignViol++;
		}
	}

	const double expo = (n > 1) ? std::log((double)M) / std::log((double)n) : 0.0;
	printf("N=%d n=%d constraints=%zu dup-var-constraints=%zu own-missing=%zu foreign-violations=%zu\n",
	       N, n, M, dupCon, ownMiss, foreignViol);
	printf("realised-exponent=%.4f target=%.4f verdict=%s\n", expo, (double)k / s,
	       (dupCon || ownMiss || foreignViol) ? "FAIL" : "PROVED-NONREDUNDANT");
	return (dupCon || ownMiss || foreignViol) ? 1 : 0;
}
