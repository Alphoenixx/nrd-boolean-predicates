// Validation gate for src/nrdx.hpp, the direct non-redundancy solver.
//
// Group 4 is the load-bearing check.  For every symmetric predicate of arity
// 2, 3 and 4 the incremental depth-first search is compared at n = 4 against
// reference_exact_nrd, which enumerates all 2^16 subfamilies of {0,1}^4.  The
// two implementations share no code, so a disagreement is informative.
//
// Nothing in docs/FINDINGS-exact-nrd.md is trusted until this prints ALL PASS.
// Runtime is a few seconds; the brute-force reference dominates.

#include "../src/classification/nrdx.hpp"

#include <cstdio>
#include <random>
#include <string>
#include <vector>

using namespace nrdx;

static int checks = 0, failures = 0;

static void expect(bool ok, const std::string& what) {
    ++checks;
    if (!ok) { ++failures; printf("  FAIL  %s\n", what.c_str()); }
}

static void expect_eq(long got, long want, const std::string& what) {
    ++checks;
    if (got != want) {
        ++failures;
        printf("  FAIL  %s : got %ld want %ld\n", what.c_str(), got, want);
    }
}

static long long binom(int n, int k) {
    if (k < 0 || k > n || n < 0) return 0;
    long long r = 1;
    for (int i = 0; i < k; ++i) r = r * (n - i) / (i + 1);
    return r;
}

static u32 flip_wmask(int r, u32 wmask) {
    u32 m = 0;
    for (int w = 0; w <= r; ++w)
        if ((wmask >> w) & 1u) m |= (1u << (r - w));
    return m;
}

static std::vector<int> all_levels(int n) {
    std::vector<int> v;
    for (int d = 0; d <= n; ++d) v.push_back(d);
    return v;
}

int main() {
    printf("=== group 1 : combinatorial primitives ===\n");
    {
        const std::vector<u32> s52 = subset_masks(5, 2);
        expect_eq((long)s52.size(), 10, "subset_masks(5,2) count");
        bool allTwo = true, distinct = true;
        for (size_t i = 0; i < s52.size(); ++i) {
            if (__builtin_popcount(s52[i]) != 2) allTwo = false;
            for (size_t j = i + 1; j < s52.size(); ++j)
                if (s52[i] == s52[j]) distinct = false;
        }
        expect(allTwo, "subset_masks(5,2) all of size 2");
        expect(distinct, "subset_masks(5,2) pairwise distinct");
        expect(subset_masks(4, 5).empty(), "subset_masks r>n is empty");
        expect(subset_masks(4, 0).empty(), "subset_masks r=0 is empty");
    }
    {
        expect_eq((long)pext32(0xBu, 0xAu), 3, "pext32 gathers selected bits");
        expect_eq((long)pext32(0x5Au, 0xFFu), 0x5A, "pext32 with full mask");
    }
    {
        // |bad| = 2^r - |R| where |R| = sum over w in W of C(r,w).
        for (int r = 2; r <= 5; ++r) {
            const u32 wm = ((1u << 0) | (1u << 2) | (1u << 3)) &
                           ((1u << (r + 1)) - 1u);
            const Predicate P = pred_from_mask(r, wm);
            long sz = 0;
            for (int w = 0; w <= r; ++w)
                if ((wm >> w) & 1u) sz += (long)binom(r, w);
            expect_eq((long)bad_patterns(P).size(), (1L << r) - sz,
                      "bad_patterns count r=" + std::to_string(r));
        }
    }

    printf("=== group 2 : independent reference checker ===\n");
    {
        const Predicate OR2 = make_pred(2, {1, 2});
        const std::vector<u32> none;
        expect(reference_is_nonredundant(OR2, 5, none), "empty family accepted");
        std::vector<u32> dup;
        dup.push_back(3);
        dup.push_back(3);
        expect(!reference_is_nonredundant(OR2, 5, dup),
               "repeated member rejected");
        // In the full cube every constraint has 2^(n-2) violators, so no
        // constraint is private and the family must be rejected.
        std::vector<u32> cube;
        for (u32 a = 0; a < (1u << 5); ++a) cube.push_back(a);
        expect(!reference_is_nonredundant(OR2, 5, cube), "full cube rejected");
    }

    printf("=== group 3 : the OR_k level construction, k = 2,3 ===\n");
    for (int k = 2; k <= 3; ++k) {
        const u32 wm = ((1u << (k + 1)) - 1u) & ~1u;   // every weight except 0
        const Predicate P = pred_from_mask(k, wm);
        for (int n = k + 2; n <= 8; ++n) {
            // Each weight-(n-k) assignment privately violates the constraint on
            // its own set of k zeros, so the level is non-redundant and realises
            // the classical C(n,k) lower bound.  It is not optimal at small n:
            // OR_2 already reaches 8 > C(4,2) at n = 4.
            std::vector<u32> lev;
            for (u32 a = 0; a < (1u << n); ++a)
                if (__builtin_popcount(a) == n - k) lev.push_back(a);
            expect((long)lev.size() == (long)binom(n, k) &&
                       reference_is_nonredundant(P, n, lev),
                   "OR_" + std::to_string(k) +
                       " level of size C(n,k) certified at n=" +
                       std::to_string(n));
            const BestResult R = best_lower_bound(P, n, 8, all_levels(n));
            expect((long)R.size >= (long)binom(n, k) &&
                       reference_is_nonredundant(P, n, R.A),
                   "OR_" + std::to_string(k) + " greedy at least C(n,k) at n=" +
                       std::to_string(n));
        }
    }

    printf("=== group 4 : exact DFS vs brute force over all 2^16 subfamilies ===\n");
    std::vector<std::vector<long>> exact4(5);
    for (int r = 2; r <= 4; ++r) {
        const int n = 4;
        const u32 nmasks = 1u << (r + 1);
        exact4[(size_t)r].assign((size_t)nmasks, -1);
        int disagree = 0, capped = 0;
        for (u32 wm = 0; wm < nmasks; ++wm) {
            const Predicate P = pred_from_mask(r, wm);
            Solver sv;
            sv.init(P, n);
            const i64 got = sv.exact(200000000LL);
            if (sv.capHit) ++capped;
            const long want = (long)reference_exact_nrd(P, n);
            exact4[(size_t)r][(size_t)wm] = want;
            if ((long)got != want) {
                ++disagree;
                printf("    r=%d W=%s : dfs %lld, brute force %ld\n", r,
                       fmt_W(P).c_str(), (long long)got, want);
            }
        }
        expect_eq(disagree, 0,
                  "arity " + std::to_string(r) + " : DFS agrees on all " +
                      std::to_string(nmasks) + " predicates");
        expect_eq(capped, 0,
                  "arity " + std::to_string(r) + " : node cap never reached");
    }

    printf("=== group 5 : bit-flip symmetry NRD(W) = NRD(r-W) ===\n");
    for (int r = 2; r <= 4; ++r) {
        int bad = 0;
        for (u32 wm = 0; wm < (1u << (r + 1)); ++wm)
            if (exact4[(size_t)r][(size_t)wm] !=
                exact4[(size_t)r][(size_t)flip_wmask(r, wm)])
                ++bad;
        expect_eq(bad, 0, "arity " + std::to_string(r) + " : symmetric under W -> r-W");
    }

    printf("=== group 6 : 60 randomised runs, incremental state vs recount ===\n");
    {
        std::mt19937_64 rng(0x5DEECE66Dull);
        int stateBad = 0, sizeBad = 0, refBad = 0;
        for (int run = 0; run < 60; ++run) {
            const int r = 2 + (int)(rng() % 4);        // 2..5
            const int n = r + 1 + (int)(rng() % 3);    // r+1 .. r+3
            const u32 wm = (u32)(rng() & (uint64_t)((1u << (r + 1)) - 1u));
            const Predicate P = pred_from_mask(r, wm);
            Solver sv;
            sv.init(P, n);
            sv.greedy(order_random(n, rng()));
            if (!sv.verify_state()) ++stateBad;
            const std::vector<u32> A = sv.family();
            if ((i64)A.size() != sv.sz) ++sizeBad;
            if (!reference_is_nonredundant(P, n, A)) ++refBad;
        }
        expect_eq(stateBad, 0, "incremental counters match a full recount");
        expect_eq(sizeBad, 0, "reported size matches the extracted family");
        expect_eq(refBad, 0, "every family certified by the reference checker");
    }

    printf("=== group 7 : degenerate predicates ===\n");
    for (int r = 2; r <= 4; ++r) {
        Solver t;
        t.init(pred_from_mask(r, (1u << (r + 1)) - 1u), 4);
        expect_eq((long)t.exact(10000000LL), 0,
                  "always-true predicate has NRD 0, r=" + std::to_string(r));
        Solver f;
        f.init(pred_from_mask(r, 0u), 4);
        expect_eq((long)f.exact(10000000LL), 1,
                  "always-false predicate has NRD 1, r=" + std::to_string(r));
    }

    printf("=== group 8 : certified families embed from n into n+1 ===\n");
    {
        const Predicate tg[3] = {make_pred(3, {1, 2}), make_pred(4, {0, 2, 3}),
                                 make_pred(5, {0, 2, 3})};
        for (int i = 0; i < 3; ++i) {
            const Predicate& P = tg[i];
            int bad = 0;
            for (int n = P.r + 1; n <= P.r + 3; ++n) {
                const BestResult R = best_lower_bound(P, n, 2, all_levels(n));
                // Padding every witness with a zero coordinate leaves each
                // private constraint private, so NRD is non-decreasing in n.
                if (!reference_is_nonredundant(P, n + 1, R.A)) ++bad;
            }
            expect_eq(bad, 0, "embedding holds for r=" + std::to_string(P.r) +
                                  " W=" + fmt_W(P));
        }
    }

    printf("=== group 9 : certified families for every predicate of arity 2..5 ===\n");
    {
        int total = 0, bad = 0;
        for (int r = 2; r <= 5; ++r) {
            const int n = r + 2;
            for (u32 wm = 0; wm < (1u << (r + 1)); ++wm) {
                const Predicate P = pred_from_mask(r, wm);
                const BestResult R = best_lower_bound(P, n, 3, all_levels(n));
                ++total;
                if (!reference_is_nonredundant(P, n, R.A)) ++bad;
            }
        }
        expect_eq(bad, 0, "every heuristic family independently certified");
        expect_eq(total, 120, "predicate count covered");
    }

    printf("\nchecks=%d failures=%d -> %s\n", checks, failures,
           failures == 0 ? "ALL PASS" : "FAILURES PRESENT");
    return failures == 0 ? 0 : 1;
}
