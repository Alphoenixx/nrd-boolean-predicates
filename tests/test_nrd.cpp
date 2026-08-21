// Validation gate.  Nothing downstream is trusted until this passes.
//
// The load-bearing checks are groups 5 and 6: they must reproduce, from an
// independent C++ implementation, the published headline claims
//   * arity <= 4 : every symmetric predicate resolved, zero mismatches
//   * arity 5    : EXACTLY two mismatches, at W={0,2,3} and W={1,2,4}

#include "../src/classification/nrd.hpp"
#include <cstdio>
#include <vector>
#include <string>

using namespace nrd;

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

static u32 wmask_of(const std::vector<int>& ws) {
    u32 m = 0;
    for (size_t i = 0; i < ws.size(); ++i) m |= (1u << ws[i]);
    return m;
}

int main() {
    printf("=== group 1 : checked i128 arithmetic ===\n");
    expect(mul_ck(3, 4) == 12, "mul_ck small");
    expect(add_ck(-5, 9) == 4, "add_ck small");
    expect(sub_ck(7, 19) == -12, "sub_ck small");
    {
        bool threw = false;
        try { i128 big = (i128)1 << 100; mul_ck(big, big); }
        catch (const OverflowError&) { threw = true; }
        expect(threw, "mul_ck detects overflow");
    }

    printf("=== group 2 : integer-span (Hermite) membership ===\n");
    {
        // single column (2); 4 is in the span, 3 is not
        std::vector<std::vector<i128>> M(1, std::vector<i128>(1, 2));
        IntSpan S(M);
        expect(S.contains(std::vector<i128>(1, 4)), "2Z contains 4");
        expect(!S.contains(std::vector<i128>(1, 3)), "2Z excludes 3");
    }
    {
        // columns (1,0) and (1,2) generate { (a,b) : b even }.
        // (Do NOT use (1,0),(1,1) here: that pair has determinant 1 and so
        //  spans all of Z^2, making any "excludes" assertion false.)
        std::vector<std::vector<i128>> M(2, std::vector<i128>(2, 0));
        M[0][0] = 1; M[1][0] = 0;
        M[0][1] = 1; M[1][1] = 2;
        IntSpan S(M);
        std::vector<i128> y(2); y[0] = 1; y[1] = 2;
        expect(S.contains(y), "index-2 sublattice contains (1,2)");
        std::vector<i128> z(2); z[0] = 1; z[1] = 3;
        expect(!S.contains(z), "index-2 sublattice excludes (1,3)");
    }
    {
        // empty generating set spans only 0
        std::vector<std::vector<i128>> M(2, std::vector<i128>());
        IntSpan S(M);
        std::vector<i128> y(2, 0);
        expect(S.contains(y), "empty span contains 0");
        std::vector<i128> w(2, 0); w[0] = 1;
        expect(!S.contains(w), "empty span excludes nonzero");
    }

    printf("=== group 3 : k-cube closed form vs literal reference ===\n");
    for (int r = 2; r <= 7; ++r) {
        for (int k = 2; k <= r; ++k) {
            std::vector<Sig> fast = kcube_signatures(r, k);
            std::vector<Sig> ref  = kcube_signatures_reference(r, k);
            expect(fast == ref,
                   "kcube sig r=" + std::to_string(r) + " k=" + std::to_string(k));
        }
    }

    printf("=== group 4 : known predicates ===\n");
    {
        // NAE_3 : W = {1,2} is 2-balanced but not 1-balanced -> Theta(n^2)
        int r = 3;
        std::vector<LiftCtx> L((size_t)r + 1);
        for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
        std::vector<int> w; w.push_back(1); w.push_back(2);
        u32 nae = wmask_of(w);
        expect(!is_t_balanced(r, nae, L[1]), "NAE_3 not 1-balanced");
        expect(is_t_balanced(r, nae, L[2]),  "NAE_3 is 2-balanced");
        std::vector<std::vector<Sig>> sk((size_t)r + 1);
        for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);
        expect_eq(max_k_cube_failure(r, nae, sk), 2, "NAE_3 lower exponent");
    }
    {
        // OR_r : W = {1,...,r} has NRD = Theta(n^r)
        for (int r = 2; r <= 5; ++r) {
            std::vector<LiftCtx> L((size_t)r + 1);
            for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
            std::vector<std::vector<Sig>> sk((size_t)r + 1);
            for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);
            u32 orm = ((1u << (r + 1)) - 1u) & ~1u;   // all weights except 0
            expect_eq(min_t_balanced(r, orm, L), r,
                      "OR_" + std::to_string(r) + " upper exponent");
            expect_eq(max_k_cube_failure(r, orm, sk), r,
                      "OR_" + std::to_string(r) + " lower exponent");
        }
    }

    printf("=== group 5 : arity <= 4 fully resolved (published) ===\n");
    for (int r = 1; r <= 4; ++r) {
        std::vector<LiftCtx> L((size_t)r + 1);
        for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
        std::vector<std::vector<Sig>> sk((size_t)r + 1);
        for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);
        std::vector<u32> reps = weight_mask_reps(r, true);
        int mism = 0;
        for (size_t z = 0; z < reps.size(); ++z) {
            int u = min_t_balanced(r, reps[z], L);
            int l = max_k_cube_failure(r, reps[z], sk);
            if (u != l) ++mism;
        }
        expect_eq(mism, 0, "arity " + std::to_string(r) + " mismatch count");
    }

    printf("=== group 6 : arity 5 has EXACTLY the two published exceptions ===\n");
    {
        int r = 5;
        std::vector<LiftCtx> L((size_t)r + 1);
        for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
        std::vector<std::vector<Sig>> sk((size_t)r + 1);
        for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);
        std::vector<u32> reps = weight_mask_reps(r, true);
        std::vector<u32> mism;
        for (size_t z = 0; z < reps.size(); ++z) {
            int u = min_t_balanced(r, reps[z], L);
            int l = max_k_cube_failure(r, reps[z], sk);
            if (u != l) mism.push_back(reps[z]);
        }
        expect_eq((long)mism.size(), 2, "arity 5 mismatch count");
        std::vector<int> a; a.push_back(0); a.push_back(2); a.push_back(3);
        std::vector<int> b; b.push_back(1); b.push_back(2); b.push_back(4);
        u32 w023 = wmask_of(a), w124 = wmask_of(b);
        bool has023 = false, has124 = false;
        for (size_t z = 0; z < mism.size(); ++z) {
            if (mism[z] == w023) has023 = true;
            if (mism[z] == w124) has124 = true;
        }
        expect(has023, "arity 5 exception W={0,2,3}");
        expect(has124, "arity 5 exception W={1,2,4}");
        // and both must show the published Omega(n^2) / O(n^3) window
        expect_eq(min_t_balanced(r, w023, L), 3, "W={0,2,3} upper exponent 3");
        expect_eq(max_k_cube_failure(r, w023, sk), 2, "W={0,2,3} lower exponent 2");
        expect_eq(min_t_balanced(r, w124, L), 3, "W={1,2,4} upper exponent 3");
        expect_eq(max_k_cube_failure(r, w124, sk), 2, "W={1,2,4} lower exponent 2");
    }

    printf("=== group 7 : structural sanity at the NEW arities 6 and 7 ===\n");
    for (int r = 6; r <= 7; ++r) {
        std::vector<LiftCtx> L((size_t)r + 1);
        for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
        std::vector<std::vector<Sig>> sk((size_t)r + 1);
        for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);
        std::vector<u32> reps = weight_mask_reps(r, true);
        int bad = 0, computed = 0;
        for (size_t z = 0; z < reps.size(); ++z) {
            int u = min_t_balanced(r, reps[z], L);
            int l = max_k_cube_failure(r, reps[z], sk);
            ++computed;
            // the certified upper exponent can never be below the certified
            // lower exponent; a violation would mean one of the two criteria
            // is mis-implemented
            if (u < 0 || u < l) ++bad;
        }
        expect_eq(bad, 0, "arity " + std::to_string(r) + " : u(R) >= l(R) everywhere");
        expect_eq(computed, (long)reps.size(),
                  "arity " + std::to_string(r) + " : every predicate computed");

        u32 orm = ((1u << (r + 1)) - 1u) & ~1u;   // OR_r
        expect_eq(min_t_balanced(r, orm, L), r,
                  "OR_" + std::to_string(r) + " upper exponent");
        expect_eq(max_k_cube_failure(r, orm, sk), r,
                  "OR_" + std::to_string(r) + " lower exponent");
    }

    printf("=== group 8 : arbitrary-precision fallback arithmetic ===\n");
    {
        // The representation must be canonical, so that equality and the
        // zero test cannot be fooled by a padded or negative zero.
        expect(BigInt().isZero(), "default BigInt is zero");
        expect(BigInt::fromI128(0).isZero(), "fromI128(0) is zero");
        expect(BigInt::fromI128(0).str() == "0", "zero prints as 0");
        expect(BigInt::fromI128(-1).str() == "-1", "minus one prints as -1");

        // Agreement with __int128 on operands where __int128 is itself exact.
        // Signs are covered on both sides, which is what pins the truncation
        // and remainder-sign conventions the fixed-width path relies on.
        long mism_add = 0, mism_sub = 0, mism_mul = 0, mism_div = 0, mism_rem = 0;
        unsigned long long s = 88172645463325252ull;
        for (int it = 0; it < 4000; ++it) {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            i128 a = (i128)(long long)s;
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            i128 b = (i128)(long long)s;
            a >>= (it % 40);
            b >>= (it % 33);
            if (b == 0) b = 1;
            const BigInt A = BigInt::fromI128(a), B = BigInt::fromI128(b);
            if (!(A + B).equalsI128(a + b)) ++mism_add;
            if (!(A - B).equalsI128(a - b)) ++mism_sub;
            if (!(A * B).equalsI128(a * b)) ++mism_mul;
            BigInt q, r;
            BigInt::divmod(A, B, q, r);
            if (!q.equalsI128(a / b)) ++mism_div;
            if (!r.equalsI128(a % b)) ++mism_rem;
        }
        expect_eq(mism_add, 0, "BigInt add agrees with i128 over 4000 signed pairs");
        expect_eq(mism_sub, 0, "BigInt subtract agrees with i128 over 4000 signed pairs");
        expect_eq(mism_mul, 0, "BigInt multiply agrees with i128 over 4000 signed pairs");
        expect_eq(mism_div, 0, "BigInt divide truncates toward zero like i128");
        expect_eq(mism_rem, 0, "BigInt remainder takes the dividend sign like i128");

        // Past the fixed-width range, where there is nothing to compare
        // against but the decimal expansion.
        BigInt p = BigInt::fromI128(1);
        for (int i = 0; i < 100; ++i) p = p * BigInt::fromI128(10);
        std::string want = "1";
        for (int i = 0; i < 100; ++i) want += "0";
        expect(p.str() == want, "10^100 is exact");
        expect_eq((long)p.bitLength(), 333, "10^100 has 333 bits");

        int exact = 1;
        BigInt back = p, q2, r2;
        for (int i = 0; i < 100; ++i) {
            BigInt::divmod(back, BigInt::fromI128(10), q2, r2);
            if (!r2.isZero()) exact = 0;
            back = q2;
        }
        expect(exact == 1, "10^100 divides by 10 exactly at every step");
        expect(back.equalsI128(1), "10^100 after a hundred divisions is 1");

        // Wider than the 3099 bits the arity-8 solve actually reaches.
        BigInt big = BigInt::fromI128(1);
        const BigInt two = BigInt::fromI128(2);
        for (int i = 0; i < 5000; ++i) big = big * two;
        expect_eq((long)big.bitLength(), 5001, "2^5000 has 5001 bits");
        BigInt q3, r3;
        BigInt::divmod(big, BigInt::fromI128((i128)1 << 40), q3, r3);
        expect(r3.isZero(), "2^5000 is divisible by 2^40");
        expect_eq((long)q3.bitLength(), 4961, "2^5000 / 2^40 has 4961 bits");

        // The 96-bit divisor bound is what keeps the running remainder inside
        // 128 bits, so it must be enforced rather than silently violated.
        {
            bool threw = false;
            BigInt huge = BigInt::fromI128(1);
            for (int i = 0; i < 4; ++i) huge = huge * BigInt::fromI128((i128)1 << 30);
            BigInt q4, r4;
            try { BigInt::divmod(BigInt::fromI128(1), huge, q4, r4); }
            catch (const OverflowError&) { threw = true; }
            expect(threw, "divisor beyond 96 bits is rejected, not silently wrong");
        }
        {
            bool threw = false;
            BigInt q5, r5;
            try { BigInt::divmod(BigInt::fromI128(5), BigInt(), q5, r5); }
            catch (const OverflowError&) { threw = true; }
            expect(threw, "division by zero is rejected");
        }

        // The fallback must not be entered where 128 bits already suffices,
        // otherwise the fixed-width path is silently dead code.
        const long long before = g_bigFallbacks;
        {
            const int r = 6;
            std::vector<LiftCtx> L((size_t)r + 1);
            for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);
            std::vector<u32> reps = weight_mask_reps(r, true);
            for (size_t z = 0; z < reps.size(); ++z) min_t_balanced(r, reps[z], L);
        }
        expect_eq((long)(g_bigFallbacks - before), 0,
                  "arity 6 classification needs no multiprecision fallback");
    }

    printf("\nchecks=%d failures=%d -> %s\n", checks, failures,
           failures == 0 ? "ALL PASS" : "FAILURES PRESENT");
    return failures == 0 ? 0 : 1;
}
