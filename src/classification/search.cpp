// ---------------------------------------------------------------------------
// search.cpp -- INTENSIVE search: can ANY family beat the lifted-OR2
// construction for the two open arity-5 predicates of Sharma-Velusamy?
//
// The calibrated sweep produced certified lower bounds that match, exactly,
//        NRD_n(R023) >= C(n-3,2) + 1
//        NRD_n(R124) >= C(n-3,2) + 2
// for every n in 11..14.  Those are *quadratic*.  The log-log fits looked
// superquadratic (2.67 / 2.73) but the calibration block shows the estimator
// overshoots by ~k^2/(2n) at these sizes, and a shifted quadratic C(n-s,2)
// reads high by even more.  So the fits carry no signal.
//
// The scientific question is therefore NOT "what does the fit say" but:
//        can a much stronger search beat C(n-3,2)+O(1) at fixed n?
// If yes  -> superquadratic signal, and a fractional-exponent candidate.
// If no   -> strong evidence that NRD_n = Theta(n^2), i.e. the LOWER bound is
//            the truth and the published O(n^3) upper bound is not tight.
//
// Method: ruin-and-recreate metaheuristic with plateau moves, seeded from the
// best level-order greedy solution.  Controls: OR2 and NAE3, both PROVEN
// Theta(n^2), whose optima are known in closed form.  If the metaheuristic
// exceeds the known optimum on a control, the search itself is buggy.
//
// Every reported family is re-verified by the independent reference checker.
// ---------------------------------------------------------------------------
#include "nrdx.hpp"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <random>
#include <vector>

using namespace nrdx;

struct Target {
	int r;
	std::vector<int> W;
	const char* label;
};

static const Target TARGETS[] = {
    {5, {0, 2, 3}, "R023  arity 5  -- OPEN in Sharma-Velusamy 2026"},
    {5, {1, 2, 4}, "R124  arity 5  -- OPEN in Sharma-Velusamy 2026"},
    {7, {0, 1, 3, 4}, "G7    arity 7  -- two-level gap (this work)"},
    {3, {1, 2}, "NAE3  arity 3  -- CONTROL, proven Theta(n^2)"},
    {2, {1, 2}, "OR2   arity 2  -- CONTROL, proven Theta(n^2), opt = C(n,2)"},
    {3, {1, 2, 3}, "OR3   arity 3  -- CONTROL, proven Theta(n^3), opt = C(n,3)"},
    {6, {0, 1, 3, 4}, "H6a   arity 6  -- Omega(n^5/2) .. O(n^3)  (this work)"},
    {7, {1, 2, 4, 5}, "H7a   arity 7  -- Omega(n^5/2) .. O(n^3)  (this work)"},
    {7, {0, 1, 4, 5, 7}, "H7b   arity 7  -- Omega(n^5/2) .. O(n^3)  (this work)"},
};
static const int NTARGETS = 9;

static long long binom(int n, int k) {
	if (k < 0 || k > n || n < 0) return 0;
	long long r = 1;
	for (int i = 0; i < k; ++i) r = r * (n - i) / (i + 1);
	return r;
}

static Predicate mk(const Target& t) {
	u32 wm = 0;
	for (int w : t.W) wm |= (1u << w);
	return pred_from_mask(t.r, wm);
}

int main(int argc, char** argv) {
	const int idx = argc > 1 ? atoi(argv[1]) : 0;
	const int n = argc > 2 ? atoi(argv[2]) : 12;
	const long iters = argc > 3 ? atol(argv[3]) : 2000;
	const int kmax = argc > 4 ? atoi(argv[4]) : 4;

	if (idx < 0 || idx >= NTARGETS) {
		printf("usage: bin_search <0..%d> <n> <iters> [kmax]\n", NTARGETS - 1);
		return 2;
	}
	if (n < 3 || n > 16) {
		printf("n out of supported range\n");
		return 2;
	}

	const Target& T = TARGETS[idx];
	const Predicate P = mk(T);

	printf("==================================================================\n");
	printf(" %s\n", T.label);
	printf(" arity %d   W=%s   n=%d   iters=%ld   kmax=%d\n", T.r,
	       fmt_W(P).c_str(), n, iters, kmax);
	printf("------------------------------------------------------------------\n");
	fflush(stdout);

	// ---- baseline: every level order + 8 random orders --------------------
	std::vector<int> levels;
	for (int d = 0; d <= n; ++d) levels.push_back(d);
	const BestResult base = best_lower_bound(P, n, 8, levels);
	printf(" baseline  (all %d level orders + 8 random) : %lld   [%s]\n",
	       n + 1, (long long)base.size, base.order.c_str());
	fflush(stdout);

	// ---- ruin-and-recreate with plateau moves ----------------------------
	Solver sv;
	sv.init(P, n);

	std::vector<u32> cur = base.A;
	std::vector<u32> best = cur;
	std::mt19937_64 rng(0xC0FFEEULL + 7919ULL * (uint64_t)idx +
	                    104729ULL * (uint64_t)n);

	const u32 N = 1u << n;
	std::vector<u32> all(N);
	for (u32 a = 0; a < N; ++a) all[a] = a;

	long improvedAt = -1;
	long plateauMoves = 0;
	for (long it = 0; it < iters; ++it) {
		// ruin: drop k random members of the current family
		std::vector<u32> S = cur;
		const int k = 1 + (int)(rng() % (uint64_t)kmax);
		for (int j = 0; j < k && !S.empty(); ++j) {
			const size_t p = (size_t)(rng() % (uint64_t)S.size());
			S[p] = S.back();
			S.pop_back();
		}

		// recreate: reinstate the survivors, then fill in a fresh random order
		sv.reset();
		for (u32 a : S) sv.try_add(a);
		std::shuffle(all.begin(), all.end(), rng);
		for (u32 a : all)
			if (!sv.inA[a]) sv.try_add(a);

		std::vector<u32> cand = sv.family();
		if (cand.size() > cur.size()) {
			cur = cand;
		} else if (cand.size() == cur.size()) {
			cur = cand;   // plateau move: drift sideways to diversify
			++plateauMoves;
		}
		if (cand.size() > best.size()) {
			best = cand;
			improvedAt = it;
		}
	}

	// ---- verify and report ----------------------------------------------
	const bool okRef = reference_is_nonredundant(P, n, best);
	const long long m = (long long)best.size();
	const long long cf3 = binom(n - 3, 2);
	const long long cf0 = binom(n, 2);

	std::map<int, int> hist;
	for (u32 a : best) hist[__builtin_popcount(a)]++;

	printf(" best found after %ld iterations           : %lld\n", iters, m);
	printf(" reference checker                         : %s\n",
	       okRef ? "VERIFIED non-redundant" : "*** CHECK FAILED ***");
	printf(" improvement over baseline first seen at   : %s\n",
	       improvedAt < 0 ? "never" : std::to_string(improvedAt).c_str());
	printf(" plateau moves accepted                    : %ld\n", plateauMoves);
	printf(" C(n,2)   = %-6lld   best - C(n,2)   = %lld\n", cf0, m - cf0);
	printf(" C(n-3,2) = %-6lld   best - C(n-3,2) = %lld\n", cf3, m - cf3);
	printf(" witness Hamming weights:");
	for (const auto& kv : hist) printf(" %d^%d", kv.first, kv.second);
	printf("\n");
	printf(" distinct levels occupied                  : %zu\n", hist.size());
	fflush(stdout);

	return okRef ? 0 : 1;
}
