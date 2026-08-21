#pragma once
// ---------------------------------------------------------------------------
// nrdx.hpp -- machinery for computing NON-REDUNDANCY ITSELF (not just the
// algebraic upper/lower-bound criteria) for symmetric Boolean predicates.
//
// MODEL (the "literal model" used by Sharma-Velusamy and by
// Brakensiek-Guruswami-Putterman).  A constraint is a pair (T, sigma) where T
// is a set of r DISTINCT variables of [n] and sigma in {0,1}^r assigns a
// polarity to each position of T taken in increasing variable order.  For an
// assignment a in {0,1}^n the value fed to position j is 1 iff a_{T[j]} ==
// sigma_j.  The constraint is SATISFIED iff the number of 1s among those r
// values lies in W(R).  An instance is a set of constraints; it is
// NON-REDUNDANT iff for every constraint c some assignment satisfies all the
// others but not c.  NRD_n(R) is the largest size of such an instance.
//
// THE REFORMULATION THAT MAKES THIS COMPUTABLE.
//   Let a_i be the assignment witnessing constraint c_i.  Then a_i violates
//   c_i and no a_j (j != i) violates c_i.  Writing S(a) for the set of
//   constraints violated by a, non-redundancy says precisely that every
//   member of A = {a_1,...,a_m} owns a PRIVATE constraint:
//
//        S(a)  \  union_{b in A, b != a} S(b)   is nonempty.
//
//   Conversely, any family A with that property yields a non-redundant
//   instance of size |A| (take one private constraint per element; they are
//   distinct because they are private).  Two witnesses can never coincide, so
//   m = |A|.  Therefore
//
//        NRD_n(R) = max { |A| : A subset of {0,1}^n, every a in A privately
//                          violates some constraint }.
//
//   This property is DOWNWARD CLOSED: shrinking A only shrinks the union that
//   each surviving element has to escape.  So the valid families form an
//   independence system.  Two consequences we lean on hard:
//     * every family we construct is a CERTIFIED lower bound on NRD_n(R);
//     * in a depth-first search, once A + {a} is invalid, every superset is
//       invalid too, so the branch can be cut with no loss of exactness.
//
//   Operationally, c is private to a exactly when a is the UNIQUE member of A
//   violating c.  So we maintain, per constraint, the number of violators in A
//   and (when that count is 1) the identity of the sole violator.  Insertions
//   update those counters incrementally and are fully reversible.
// ---------------------------------------------------------------------------

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <initializer_list>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>
#if defined(__BMI2__)
#include <immintrin.h>
#endif

namespace nrdx {

using u32 = uint32_t;
using i64 = int64_t;

// Gather the bits of v selected by mask into the low bits, preserving order.
inline u32 pext32(u32 v, u32 mask) {
#if defined(__BMI2__)
	return (u32)_pext_u32(v, mask);
#else
	u32 res = 0, bb = 1;
	while (mask) {
		const u32 low = mask & (0u - mask);
		if (v & low) res |= bb;
		bb <<= 1;
		mask ^= low;
	}
	return res;
#endif
}

struct Predicate {
	int r = 0;
	u32 wmask = 0;  // bit w set  <=>  accepted weight w
};

inline Predicate make_pred(int r, std::initializer_list<int> ws) {
	Predicate P;
	P.r = r;
	for (int w : ws) P.wmask |= (1u << w);
	return P;
}

inline Predicate pred_from_mask(int r, u32 wmask) {
	Predicate P;
	P.r = r;
	P.wmask = wmask;
	return P;
}

inline std::string fmt_W(const Predicate& P) {
	std::string s = "{";
	bool first = true;
	for (int w = 0; w <= P.r; ++w) {
		if ((P.wmask >> w) & 1u) {
			if (!first) s += ",";
			s += std::to_string(w);
			first = false;
		}
	}
	return s + "}";
}

// A constraint (T,sigma) is violated by an assignment whose T-pattern is p
// exactly when (p ^ sigma) is one of these patterns q, because the number of
// satisfied literals equals r - popcount(q).
inline std::vector<u32> bad_patterns(const Predicate& P) {
	std::vector<u32> bad;
	for (u32 q = 0; q < (1u << P.r); ++q) {
		const int w = P.r - __builtin_popcount(q);
		if (!((P.wmask >> w) & 1u)) bad.push_back(q);
	}
	return bad;
}

inline std::vector<u32> subset_masks(int n, int r) {
	std::vector<u32> out;
	if (r <= 0 || r > n) return out;
	std::vector<int> idx((size_t)r);
	for (int i = 0; i < r; ++i) idx[(size_t)i] = i;
	for (;;) {
		u32 m = 0;
		for (int i = 0; i < r; ++i) m |= (1u << idx[(size_t)i]);
		out.push_back(m);
		int i = r - 1;
		while (i >= 0 && idx[(size_t)i] == n - r + i) --i;
		if (i < 0) break;
		++idx[(size_t)i];
		for (int j = i + 1; j < r; ++j) idx[(size_t)j] = idx[(size_t)j - 1] + 1;
	}
	return out;
}

// --------------------------------------------------------------------------
// Deliberately independent, slow reference implementations.  These share no
// code with the incremental solver so that disagreement is informative.
// --------------------------------------------------------------------------
inline bool reference_is_nonredundant(const Predicate& P, int n,
                                      const std::vector<u32>& A) {
	if (A.empty()) return true;
	std::vector<u32> srt = A;
	std::sort(srt.begin(), srt.end());
	if (std::adjacent_find(srt.begin(), srt.end()) != srt.end()) return false;
	const std::vector<u32> ts = subset_masks(n, P.r);
	const u32 S = 1u << P.r;
	std::vector<char> owned(A.size(), 0);
	std::vector<u32> pat(A.size());
	for (u32 tm : ts) {
		for (size_t i = 0; i < A.size(); ++i) pat[i] = pext32(A[i], tm);
		for (u32 sig = 0; sig < S; ++sig) {
			long tot = 0;
			size_t who = 0;
			for (size_t i = 0; i < A.size(); ++i) {
				const int w = P.r - __builtin_popcount(pat[i] ^ sig);
				if (!((P.wmask >> w) & 1u)) {
					++tot;
					who = i;
					if (tot > 1) break;
				}
			}
			if (tot == 1) owned[who] = 1;
		}
	}
	for (size_t i = 0; i < A.size(); ++i)
		if (!owned[i]) return false;
	return true;
}

// Exhaustive maximum over all 2^(2^n) subfamilies.  Only sane for n <= 4.
inline int reference_exact_nrd(const Predicate& P, int n) {
	const int N = 1 << n;
	if (N > 20) throw std::runtime_error("reference_exact_nrd: n too large");
	const long long total = 1LL << N;
	int best = 0;
	std::vector<u32> A;
	for (long long mask = 0; mask < total; ++mask) {
		const int pc = __builtin_popcountll((unsigned long long)mask);
		if (pc <= best) continue;  // cannot improve
		A.clear();
		for (int i = 0; i < N; ++i)
			if ((mask >> i) & 1LL) A.push_back((u32)i);
		if (reference_is_nonredundant(P, n, A)) best = pc;
	}
	return best;
}

// --------------------------------------------------------------------------
// Incremental solver.
// --------------------------------------------------------------------------
struct Solver {
	Predicate P;
	int n = 0;
	u32 S = 0;
	std::vector<u32> tms;   // r-subset masks
	std::vector<u32> bad;   // violating xor-patterns
	std::vector<u32> cnt;   // violators in A, per constraint
	std::vector<int32_t> own;    // sole violator when cnt == 1, else -1
	std::vector<int32_t> cover;  // per assignment: number of private constraints
	std::vector<uint8_t> inA;
	i64 sz = 0;
	std::vector<u32> undoC;
	std::vector<int32_t> undoO;

	// exact-search state
	i64 bestExact = 0, nodes = 0, nodeCap = 0;
	bool capHit = false;

	void init(const Predicate& p, int nn) {
		P = p;
		n = nn;
		S = 1u << P.r;
		tms = subset_masks(n, P.r);
		bad = bad_patterns(P);
		cnt.assign(tms.size() * (size_t)S, 0u);
		own.assign(tms.size() * (size_t)S, -1);
		cover.assign((size_t)1 << n, 0);
		inA.assign((size_t)1 << n, 0);
		sz = 0;
		undoC.clear();
		undoO.clear();
		undoC.reserve(tms.size() * bad.size() + 8);
		undoO.reserve(tms.size() * bad.size() + 8);
	}

	void reset() {
		std::fill(cnt.begin(), cnt.end(), 0u);
		std::fill(own.begin(), own.end(), (int32_t)-1);
		std::fill(cover.begin(), cover.end(), 0);
		std::fill(inA.begin(), inA.end(), (uint8_t)0);
		sz = 0;
		undoC.clear();
		undoO.clear();
	}

	// Apply a's violator-count updates, appending undo records.  Returns true
	// iff A + {a} is still fully non-redundant.
	bool push_add(u32 a) {
		int broken = 0;
		const size_t nb = bad.size();
		for (size_t ti = 0; ti < tms.size(); ++ti) {
			const u32 p = pext32(a, tms[ti]);
			const size_t base = ti * (size_t)S;
			for (size_t k = 0; k < nb; ++k) {
				const size_t c = base + (size_t)(p ^ bad[k]);
				const u32 before = cnt[c]++;
				undoC.push_back((u32)c);
				undoO.push_back(own[c]);
				if (before == 0) {
					own[c] = (int32_t)a;
					++cover[a];
				} else if (before == 1) {
					const int32_t b = own[c];
					own[c] = -1;
					if (--cover[(size_t)b] == 0) ++broken;
				}
			}
		}
		const bool ok = (broken == 0 && cover[a] > 0);
		if (ok) {
			inA[a] = 1;
			++sz;
		}
		return ok;
	}

	void pop_add(u32 a, size_t mark, bool wasOk) {
		for (size_t z = undoC.size(); z-- > mark;) {
			const size_t c = undoC[z];
			const u32 after = cnt[c]--;
			if (after == 1) {
				own[c] = -1;
				--cover[a];
			} else if (after == 2) {
				own[c] = undoO[z];
				++cover[(size_t)undoO[z]];
			}
		}
		undoC.resize(mark);
		undoO.resize(mark);
		if (wasOk) {
			inA[a] = 0;
			--sz;
		}
	}

	bool try_add(u32 a) {
		if (inA[a]) return false;
		if (bad.empty() || tms.empty()) return false;
		const size_t mark = undoC.size();
		if (push_add(a)) {
			undoC.resize(mark);  // committed; undo info no longer needed
			undoO.resize(mark);
			return true;
		}
		pop_add(a, mark, false);
		return false;
	}

	std::vector<u32> family() const {
		std::vector<u32> A;
		for (size_t i = 0; i < inA.size(); ++i)
			if (inA[i]) A.push_back((u32)i);
		return A;
	}

	// Recompute cnt / own / cover from scratch and compare against the
	// incrementally maintained arrays.  Guards against bookkeeping drift.
	bool verify_state() const {
		const std::vector<u32> A = family();
		if ((i64)A.size() != sz) return false;
		std::vector<u32> c2(cnt.size(), 0u);
		std::vector<int32_t> cv2(cover.size(), 0);
		for (u32 a : A)
			for (size_t ti = 0; ti < tms.size(); ++ti) {
				const u32 p = pext32(a, tms[ti]);
				for (size_t k = 0; k < bad.size(); ++k)
					++c2[ti * (size_t)S + (size_t)(p ^ bad[k])];
			}
		for (size_t c = 0; c < c2.size(); ++c)
			if (c2[c] != cnt[c]) return false;
		for (size_t ti = 0; ti < tms.size(); ++ti)
			for (u32 sig = 0; sig < S; ++sig) {
				const size_t c = ti * (size_t)S + sig;
				if (c2[c] != 1) {
					if (own[c] != -1) return false;
					continue;
				}
				int32_t who = -1;
				for (u32 a : A) {
					const u32 p = pext32(a, tms[ti]);
					const int w = P.r - __builtin_popcount(p ^ sig);
					if (!((P.wmask >> w) & 1u)) {
						who = (int32_t)a;
						break;
					}
				}
				if (own[c] != who) return false;
				if (who >= 0) ++cv2[(size_t)who];
			}
		for (size_t i = 0; i < cv2.size(); ++i)
			if (cv2[i] != cover[i]) return false;
		return true;
	}

	void dfs(u32 i, u32 N) {
		if (capHit) return;
		if (++nodes > nodeCap) {
			capHit = true;
			return;
		}
		if (sz > bestExact) bestExact = sz;
		if (i >= N) return;
		if (sz + (i64)(N - i) <= bestExact) return;  // optimistic bound
		const size_t mark = undoC.size();
		const bool ok = push_add(i);
		// If A + {i} is invalid, every superset is invalid (downward closure),
		// so the inclusion branch is cut without losing exactness.
		if (ok) dfs(i + 1, N);
		pop_add(i, mark, ok);
		if (capHit) return;
		dfs(i + 1, N);
	}

	i64 exact(i64 cap) {
		reset();
		bestExact = 0;
		nodes = 0;
		nodeCap = cap;
		capHit = false;
		if (!bad.empty() && !tms.empty()) dfs(0u, 1u << n);
		return bestExact;
	}

	i64 greedy(const std::vector<u32>& order, int passes = 2) {
		reset();
		for (int pass = 0; pass < passes; ++pass) {
			const i64 before = sz;
			for (u32 a : order)
				if (!inA[a]) try_add(a);
			if (sz == before) break;
		}
		return sz;
	}
};

// --------------------------------------------------------------------------
// Insertion orders.  Greedy insertion into a downward-closed system is
// order-sensitive, so we try several and keep the best certified family.
// --------------------------------------------------------------------------
inline std::vector<u32> order_ascending(int n) {
	std::vector<u32> v((size_t)1 << n);
	for (size_t i = 0; i < v.size(); ++i) v[i] = (u32)i;
	return v;
}

inline std::vector<u32> order_by_weight(int n, bool ascending) {
	std::vector<u32> v = order_ascending(n);
	std::stable_sort(v.begin(), v.end(), [ascending](u32 x, u32 y) {
		const int px = __builtin_popcount(x), py = __builtin_popcount(y);
		return ascending ? (px < py) : (px > py);
	});
	return v;
}

// Assignments of Hamming weight d first, then outward by |weight - d|.  This
// is the shape of the classical extremal families (e.g. for OR_k the optimum
// is exactly the weight-(n-k) level).
inline std::vector<u32> order_level_first(int n, int d) {
	std::vector<u32> v = order_ascending(n);
	std::stable_sort(v.begin(), v.end(), [d](u32 x, u32 y) {
		return std::abs(__builtin_popcount(x) - d) <
		       std::abs(__builtin_popcount(y) - d);
	});
	return v;
}

inline std::vector<u32> order_random(int n, uint64_t seed) {
	std::vector<u32> v = order_ascending(n);
	std::mt19937_64 rng(seed);
	std::shuffle(v.begin(), v.end(), rng);
	return v;
}

struct BestResult {
	i64 size = 0;
	std::vector<u32> A;
	std::string order;
	int level = -1;
};

inline BestResult best_lower_bound(const Predicate& P, int n, int nRandom,
                                  const std::vector<int>& levels) {
	Solver sv;
	sv.init(P, n);
	BestResult R;
	struct Ord {
		std::string name;
		int level;
		std::vector<u32> v;
	};
	std::vector<Ord> ords;
	ords.push_back({"asc", -1, order_ascending(n)});
	ords.push_back({"wt-asc", -1, order_by_weight(n, true)});
	ords.push_back({"wt-desc", -1, order_by_weight(n, false)});
	for (int d : levels)
		if (d >= 0 && d <= n)
			ords.push_back({"lvl" + std::to_string(d), d, order_level_first(n, d)});
	for (int s = 0; s < nRandom; ++s)
		ords.push_back({"rnd" + std::to_string(s), -1,
		                order_random(n, 0x9E3779B97F4A7C15ull +
		                                    1315423911ull * (uint64_t)s)});
	for (const Ord& o : ords) {
		const i64 m = sv.greedy(o.v);
		if (m > R.size) {
			R.size = m;
			R.A = sv.family();
			R.order = o.name;
			R.level = o.level;
		}
	}
	return R;
}

}  // namespace nrdx
