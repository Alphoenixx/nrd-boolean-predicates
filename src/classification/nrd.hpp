#pragma once
// Exact-integer engine for non-redundancy classification of symmetric Boolean
// predicates.  Port of the reference criteria used by:
//   [SV26] Sharma & Velusamy, "Non-Redundancy of Low-Arity Symmetric Boolean
//          CSPs", arXiv:2605.14007  (t-balancedness + universal k-cube)
//   [BGP26] Brakensiek, Guruswami & Putterman, CP 2026 (arity-4 Boolean)
//
// NO FLOATING POINT ANYWHERE.  All arithmetic is exact over Z: checked
// overflow on __int128, with an arbitrary-precision fallback for the one place
// where 128 bits is not enough.  See bigint.hpp.

#include "bigint.hpp"

#include <cstdint>
#include <cstdio>
#include <vector>
#include <set>
#include <string>
#include <stdexcept>
#include <algorithm>
#include <functional>

namespace nrd {

using i128 = __int128;
using u32  = uint32_t;

// OverflowError and BigInt are defined in bigint.hpp; both the fixed-width
// path below and the fallback in IntSpan::contains need them.

// NOTE: these MUST use the __builtin_*_overflow intrinsics.  The obvious
// formulation "i128 r = a*b; if (r/b != a) throw" is signed-overflow UB, and
// GCC at -O2 proves the guard unreachable and deletes it outright.  Caught by
// the validation gate, group 1.
inline i128 mul_ck(i128 a, i128 b) {
    i128 r;
    if (__builtin_mul_overflow(a, b, &r)) throw OverflowError("i128 multiply overflow");
    return r;
}
inline i128 add_ck(i128 a, i128 b) {
    i128 r;
    if (__builtin_add_overflow(a, b, &r)) throw OverflowError("i128 add overflow");
    return r;
}
inline i128 sub_ck(i128 a, i128 b) {
    i128 r;
    if (__builtin_sub_overflow(a, b, &r)) throw OverflowError("i128 subtract overflow");
    return r;
}

inline std::string i128_str(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    unsigned __int128 u = neg ? (unsigned __int128)(-v) : (unsigned __int128)v;
    char buf[64]; int p = 0;
    while (u) { buf[p++] = (char)('0' + (int)(u % 10)); u /= 10; }
    std::string s; if (neg) s.push_back('-');
    while (p) s.push_back(buf[--p]);
    return s;
}

// Largest absolute entry ever produced during Hermite reduction.  Watched so
// that proximity to the 2^127 ceiling is visible rather than silent.
inline i128 g_maxAbs = 0;

// How many membership queries exceeded 128 bits and were redone in arbitrary
// precision.  Reported by the sweep so that the fallback is visible in the
// output rather than silent.
inline long long g_bigFallbacks = 0;

// Widest value the arbitrary-precision solve actually produced, in bits.
// Reported next to g_maxAbs so that the gap between the size of the reduced
// basis and the size of the solve coefficients is visible in the output rather
// than something the reader has to take on trust.
inline size_t g_bigMaxBits = 0;

// ---------------------------------------------------------------------------
// Integer-span membership via column-style Hermite reduction.
// Build once from the matrix whose COLUMNS generate the lattice, then answer
// many membership queries cheaply.  This is the exact analogue of the
// reference implementation's single Smith-normal-form + repeated accept_b().
// ---------------------------------------------------------------------------
class IntSpan {
public:
    explicit IntSpan(const std::vector<std::vector<i128>>& Min) {
        rows_ = (int)Min.size();
        cols_ = rows_ ? (int)Min[0].size() : 0;
        H_ = Min;
        int piv = 0;
        for (int i = 0; i < rows_ && piv < cols_; ++i) {
            // Reduce row i across columns [piv, cols_) until at most one
            // nonzero remains.  Always pivot on the SMALLEST magnitude entry
            // and use nearest-remainder division.  Pivoting on the first
            // nonzero with truncating division is what blew up the 128-bit
            // range at arity 6.
            for (;;) {
                int best = -1;
                i128 bestAbs = 0;
                int nz = 0;
                for (int j = piv; j < cols_; ++j) {
                    i128 v = H_[i][j];
                    if (v == 0) continue;
                    ++nz;
                    i128 a = (v < 0) ? -v : v;
                    if (best < 0 || a < bestAbs) { best = j; bestAbs = a; }
                }
                if (nz <= 1) {
                    if (nz == 1 && best != piv) swapCols(piv, best);
                    break;
                }
                for (int j = piv; j < cols_; ++j) {
                    if (j == best || H_[i][j] == 0) continue;
                    i128 p = H_[i][best];
                    i128 a = H_[i][j];
                    i128 q = a / p;
                    i128 rem = sub_ck(a, mul_ck(q, p));
                    if (rem != 0) {
                        i128 ra = (rem < 0) ? -rem : rem;
                        i128 pa = (p < 0) ? -p : p;
                        if (ra > pa - ra) q += (((rem > 0) == (p > 0)) ? 1 : -1);
                    }
                    if (q != 0) {
                        for (int rr = 0; rr < rows_; ++rr) {
                            i128 nv = sub_ck(H_[rr][j], mul_ck(q, H_[rr][best]));
                            H_[rr][j] = nv;
                            i128 na = (nv < 0) ? -nv : nv;
                            if (na > g_maxAbs) g_maxAbs = na;
                        }
                    }
                }
            }
            if (H_[i][piv] == 0) continue;
            if (H_[i][piv] < 0)
                for (int rr = 0; rr < rows_; ++rr) H_[rr][piv] = -H_[rr][piv];
            pivotRow_.push_back(i);
            ++piv;
        }
        nPiv_ = piv;
    }

    // Is y in the Z-span of the original columns?
    //
    // The reduced matrix is small: 63 bits is the largest entry seen anywhere
    // at arity at most 8.  The coefficients of this solve are not, reaching
    // 3099 bits at arity 8.  So the 128-bit path runs first and, if it
    // overflows, the identical computation is redone in arbitrary precision.
    // The two paths agree wherever both complete; only the width differs.
    bool contains(const std::vector<i128>& y) const {
        try {
            return containsFixed(y);
        } catch (const OverflowError&) {
            ++g_bigFallbacks;
            return containsBig(y);
        }
    }

    int rank() const { return nPiv_; }

private:
    bool containsFixed(const std::vector<i128>& y) const {
        std::vector<i128> w(nPiv_ > 0 ? nPiv_ : 1, 0);
        for (int p = 0; p < nPiv_; ++p) {
            int i = pivotRow_[p];
            i128 rhs = y[i];
            for (int q = 0; q < p; ++q) rhs = sub_ck(rhs, mul_ck(H_[i][q], w[q]));
            i128 d = H_[i][p];
            if (d == 0) return false;
            if (rhs % d != 0) return false;
            w[p] = rhs / d;
        }
        for (int i = 0; i < rows_; ++i) {
            i128 s = 0;
            for (int p = 0; p < nPiv_; ++p) s = add_ck(s, mul_ck(H_[i][p], w[p]));
            if (s != y[i]) return false;
        }
        return true;
    }

    bool containsBig(const std::vector<i128>& y) const {
        std::vector<BigInt> w((size_t)(nPiv_ > 0 ? nPiv_ : 1));
        for (int p = 0; p < nPiv_; ++p) {
            const int i = pivotRow_[p];
            BigInt rhs = BigInt::fromI128(y[i]);
            for (int q = 0; q < p; ++q) {
                if (H_[i][q] == 0 || w[(size_t)q].isZero()) continue;
                rhs = rhs - BigInt::fromI128(H_[i][q]) * w[(size_t)q];
            }
            if (rhs.bitLength() > g_bigMaxBits) g_bigMaxBits = rhs.bitLength();
            const i128 d = H_[i][p];
            if (d == 0) return false;
            BigInt quo, rem;
            BigInt::divmod(rhs, BigInt::fromI128(d), quo, rem);
            if (!rem.isZero()) return false;
            if (quo.bitLength() > g_bigMaxBits) g_bigMaxBits = quo.bitLength();
            w[(size_t)p] = quo;
        }
        for (int i = 0; i < rows_; ++i) {
            BigInt s;
            for (int p = 0; p < nPiv_; ++p) {
                if (H_[i][p] == 0 || w[(size_t)p].isZero()) continue;
                s = s + BigInt::fromI128(H_[i][p]) * w[(size_t)p];
            }
            if (!s.equalsI128(y[i])) return false;
        }
        return true;
    }

    void swapCols(int a, int b) {
        if (a == b) return;
        for (int rr = 0; rr < rows_; ++rr) std::swap(H_[rr][a], H_[rr][b]);
    }
    int rows_ = 0, cols_ = 0, nPiv_ = 0;
    std::vector<std::vector<i128>> H_;
    std::vector<int> pivotRow_;
};

// ---------------------------------------------------------------------------
// Degree-t monomial lift:  nu_t(x)_S = prod_{i in S} x_i  for 1 <= |S| <= t.
// ---------------------------------------------------------------------------
struct LiftCtx {
    int r = 0, t = 0, k = 0;
    std::vector<int> subs;   // subset bitmasks, ordered by degree then lex
};

inline LiftCtx make_lift(int r, int t) {
    LiftCtx L; L.r = r; L.t = t;
    for (int d = 1; d <= t; ++d)
        for (int m = 1; m < (1 << r); ++m)
            if (__builtin_popcount((unsigned)m) == d) L.subs.push_back(m);
    L.k = (int)L.subs.size();
    return L;
}

// ext(nu_t(x)) = (1, nu_t(x))
inline std::vector<i128> ext_lift(int x, const LiftCtx& L) {
    std::vector<i128> v((size_t)L.k + 1, 0);
    v[0] = 1;
    for (int j = 0; j < L.k; ++j)
        v[(size_t)j + 1] = ((x & L.subs[j]) == L.subs[j]) ? 1 : 0;
    return v;
}

inline bool weight_in(u32 wmask, int w) { return ((wmask >> w) & 1u) != 0u; }

// R = { x : |x| in W }.  R is t-balanced iff no rejected lift lies in the
// integer span of the accepted lifts (after the leading-1 extension).
inline bool is_t_balanced(int r, u32 wmask, const LiftCtx& L) {
    std::vector<int> acc, rej;
    for (int x = 0; x < (1 << r); ++x) {
        if (weight_in(wmask, __builtin_popcount((unsigned)x))) acc.push_back(x);
        else rej.push_back(x);
    }
    if (rej.empty()) return true;          // R is the full cube
    std::vector<std::vector<i128>> M((size_t)L.k + 1,
                                     std::vector<i128>(acc.size(), 0));
    for (size_t c = 0; c < acc.size(); ++c) {
        std::vector<i128> col = ext_lift(acc[c], L);
        for (int rr = 0; rr <= L.k; ++rr) M[(size_t)rr][c] = col[(size_t)rr];
    }
    IntSpan span(M);
    for (size_t z = 0; z < rej.size(); ++z)
        if (span.contains(ext_lift(rej[z], L))) return false;
    return true;
}

// smallest t in 1..r with t-balancedness; -1 if none
inline int min_t_balanced(int r, u32 wmask, const std::vector<LiftCtx>& lifts) {
    for (int t = 1; t <= r; ++t)
        if (is_t_balanced(r, wmask, lifts[(size_t)t])) return t;
    return -1;
}

// ---------------------------------------------------------------------------
// Carbonnel universal k-cube test.
//
// Columns of the partial operation f_k (arity m = 2^k - 1, rows indexed by the
// nonzero v in {0,1}^k):
//     0^m -> 0 ,  1^m -> 1 ,  c_i -> 0 ,  (1-c_i) -> 1     where (c_i)_v = v_i
//
// With multiplicities n0, a := n_{1^m}, p_i := n_{c_i}, q_i := n_{1-c_i} and
// n0 + a + sum_i (p_i + q_i) = r, a direct computation gives
//     weight(row v) = base + sum_{i in v} d_i ,   base := a + sum_i q_i ,
//                                                 d_i  := p_i - q_i
//     output weight = base
// so the whole test is a subset-sum scan over the multiset {d_i}.  Because the
// signature depends only on that multiset, we enumerate the pairs (p_i,q_i) in
// non-increasing lexicographic order (multiset symmetry reduction).
// ---------------------------------------------------------------------------
struct Sig {
    u32 rowmask;   // set of Hamming weights appearing among the m input rows
    int outw;      // Hamming weight of the output row
    bool operator<(const Sig& o) const {
        if (rowmask != o.rowmask) return rowmask < o.rowmask;
        return outw < o.outw;
    }
    bool operator==(const Sig& o) const {
        return rowmask == o.rowmask && outw == o.outw;
    }
};

inline std::vector<Sig> kcube_signatures(int r, int k) {
    std::set<Sig> out;
    std::vector<int> p((size_t)k, 0), q((size_t)k, 0);
    std::vector<int> vals;
    vals.reserve((size_t)1 << k);

    std::function<void(int,int,int,int)> dfs =
        [&](int i, int used, int pp, int pq) {
        if (i == k) {
            int Q = 0;
            for (int j = 0; j < k; ++j) Q += q[(size_t)j];
            for (int a = 0; a + used <= r; ++a) {
                int base = a + Q;
                vals.clear();
                vals.push_back(base);
                for (int j = 0; j < k; ++j) {
                    int d = p[(size_t)j] - q[(size_t)j];
                    size_t n = vals.size();
                    for (size_t s = 0; s < n; ++s) vals.push_back(vals[s] + d);
                }
                u32 rowmask = 0;
                for (size_t s = 1; s < vals.size(); ++s)
                    rowmask |= (1u << vals[s]);
                Sig sg; sg.rowmask = rowmask; sg.outw = base;
                out.insert(sg);
            }
            return;
        }
        for (int pi = 0; pi <= r - used; ++pi) {
            for (int qi = 0; qi + pi <= r - used; ++qi) {
                if (i > 0 && (pi > pp || (pi == pp && qi > pq))) continue;
                p[(size_t)i] = pi; q[(size_t)i] = qi;
                dfs(i + 1, used + pi + qi, pi, qi);
            }
        }
    };
    dfs(0, 0, r, r);
    return std::vector<Sig>(out.begin(), out.end());
}

// Literal transcription of the reference construction, used only to
// cross-validate kcube_signatures() on small (r,k).
inline std::vector<Sig> kcube_signatures_reference(int r, int k) {
    int m = (1 << k) - 1;
    std::vector<std::vector<int>> V;
    for (int x = (1 << k) - 1; x >= 1; --x) {
        std::vector<int> bits((size_t)k);
        for (int i = 0; i < k; ++i) bits[(size_t)i] = (x >> (k - 1 - i)) & 1;
        V.push_back(bits);
    }
    std::vector<std::vector<int>> cb;
    std::vector<int> co;
    cb.push_back(std::vector<int>((size_t)m, 0)); co.push_back(0);
    cb.push_back(std::vector<int>((size_t)m, 1)); co.push_back(1);
    for (int i = 0; i < k; ++i) {
        std::vector<int> c((size_t)m), cc((size_t)m);
        for (int idx = 0; idx < m; ++idx) {
            c[(size_t)idx]  = V[(size_t)idx][(size_t)i];
            cc[(size_t)idx] = 1 - c[(size_t)idx];
        }
        cb.push_back(c);  co.push_back(0);
        cb.push_back(cc); co.push_back(1);
    }
    std::vector<std::vector<int>> ub; std::vector<int> uo;
    for (size_t j = 0; j < cb.size(); ++j) {
        bool dup = false;
        for (size_t z = 0; z < ub.size(); ++z) if (ub[z] == cb[j]) { dup = true; break; }
        if (!dup) { ub.push_back(cb[j]); uo.push_back(co[j]); }
    }
    int M = (int)ub.size();
    std::set<Sig> out;
    std::vector<int> cnt((size_t)M, 0);
    std::function<void(int,int)> rec = [&](int j, int rem) {
        if (j == M - 1) {
            cnt[(size_t)j] = rem;
            int outw = 0;
            for (int z = 0; z < M; ++z) outw += cnt[(size_t)z] * uo[(size_t)z];
            u32 rowmask = 0;
            for (int i = 0; i < m; ++i) {
                int wi = 0;
                for (int z = 0; z < M; ++z)
                    if (cnt[(size_t)z]) wi += cnt[(size_t)z] * ub[(size_t)z][(size_t)i];
                rowmask |= (1u << wi);
            }
            Sig sg; sg.rowmask = rowmask; sg.outw = outw;
            out.insert(sg);
            return;
        }
        for (int c = 0; c <= rem; ++c) { cnt[(size_t)j] = c; rec(j + 1, rem - c); }
    };
    rec(0, r);
    return std::vector<Sig>(out.begin(), out.end());
}

inline bool is_invariant_kcube(u32 wmask, const std::vector<Sig>& sigs) {
    for (size_t z = 0; z < sigs.size(); ++z) {
        const Sig& s = sigs[z];
        if ((wmask & s.rowmask) == s.rowmask && !((wmask >> s.outw) & 1u))
            return false;
    }
    return true;
}

// largest k in 2..r whose cube pattern FAILS to preserve R (k=1 assumed to fail)
inline int max_k_cube_failure(int r, u32 wmask,
                              const std::vector<std::vector<Sig>>& sigs_by_k) {
    int last = 1;
    for (int k = 2; k <= r; ++k)
        if (!is_invariant_kcube(wmask, sigs_by_k[(size_t)k])) last = k;
    return last;
}

// ---------------------------------------------------------------------------
// Enumeration of symmetric predicates up to the global bit-flip W ~ (r - W).
// ---------------------------------------------------------------------------
inline u32 reverse_weight_mask(u32 mask, int r) {
    u32 out = 0;
    for (int w = 0; w <= r; ++w) if ((mask >> w) & 1u) out |= (1u << (r - w));
    return out;
}

inline std::vector<u32> weight_mask_reps(int r, bool skip_trivial) {
    std::vector<u32> reps;
    u32 full = (1u << (r + 1)) - 1u;
    for (u32 m = 0; m <= full; ++m) {
        if (skip_trivial && (m == 0u || m == full)) continue;
        if (m <= reverse_weight_mask(m, r)) reps.push_back(m);
    }
    return reps;
}

inline std::string fmt_W(u32 mask, int r) {
    std::string s = "{";
    bool first = true;
    for (int w = 0; w <= r; ++w) if ((mask >> w) & 1u) {
        if (!first) s += ",";
        s += std::to_string(w);
        first = false;
    }
    s += "}";
    return s;
}

inline int relation_size(int r, u32 wmask) {
    int n = 0;
    for (int x = 0; x < (1 << r); ++x)
        if (weight_in(wmask, __builtin_popcount((unsigned)x))) ++n;
    return n;
}

} // namespace nrd
