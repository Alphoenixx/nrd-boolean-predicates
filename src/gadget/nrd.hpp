// nrd.hpp - core types for the width-s NRD lower-bound hierarchy.
//
// A *width-s pattern* on k positions for an r-ary predicate R is a multiset of r
// Boolean entries f_1..f_r, each depending on at most s of the coordinates
// v_1..v_k, such that the induced tuple/weight is REJECTED at v = 1^k and
// ACCEPTED at every v != 1^k.  Existence of such a pattern certifies
//
//        NRD_n(R) = Omega( n^{k/s} ).
//
// s = 1 is exactly Carbonnel's universal k-cube test.
#pragma once
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <numeric>
#include <string>
#include <vector>

namespace nrd {

using u8 = uint8_t;
using u16 = uint16_t;
using u32 = uint32_t;
using u64 = uint64_t;

inline int pc(u32 x) { return __builtin_popcount(x); }

// ---------------------------------------------------------------- predicate
struct Predicate {
	int r = 0;              // arity
	bool symmetric = true;  // true => defined by accepted weight set W
	std::vector<int> W;     // accepted Hamming weights
	std::vector<u8> mem;    // size 1<<r, membership indicator (general case)

	bool wHas(int w) const {
		return std::find(W.begin(), W.end(), w) != W.end();
	}
	void buildMem() {
		mem.assign(1 << r, 0);
		for (int t = 0; t < (1 << r); t++) mem[t] = symmetric ? (u8)wHas(pc(t)) : mem[t];
	}
};

// ------------------------------------------------------------- entry types
struct EntryType {
	u32 mask = 0;             // coordinate subset A subset of [k]
	int deg = 0;              // |A|
	u32 ftab = 0;             // truth table of f over A (bit a = f(a))
	int ownbit = 0;           // f(1^k)
	std::vector<u8> val;      // value at each of 1<<k rows
	std::vector<int8_t> del;  // del[i] = f(1^k) - f(1^k ^ e_i)
};

// All entries of width <= s on k coordinates, each depending genuinely on all
// of its coordinate set (so no duplicates across different masks).
inline std::vector<EntryType> makeTypes(int k, int s) {
	const int ROWS = 1 << k, OWN = ROWS - 1;
	std::vector<EntryType> T;
	for (u32 A = 0; A < (1u << k); A++) {
		const int d = pc(A);
		if (d > s) continue;
		std::vector<int> co;
		for (int i = 0; i < k; i++)
			if ((A >> i) & 1) co.push_back(i);
		const int nf = 1 << (1 << d);
		for (int ft = 0; ft < nf; ft++) {
			bool genuine = true;
			for (int j = 0; j < d && genuine; j++) {
				bool dep = false;
				for (int a = 0; a < (1 << d) && !dep; a++)
					if (!((a >> j) & 1) && (((ft >> a) & 1) != ((ft >> (a | (1 << j))) & 1)))
						dep = true;
				if (!dep) genuine = false;
			}
			if (!genuine) continue;
			EntryType e;
			e.mask = A;
			e.deg = d;
			e.ftab = (u32)ft;
			e.val.assign(ROWS, 0);
			for (int v = 0; v < ROWS; v++) {
				int a = 0;
				for (int j = 0; j < d; j++)
					if ((v >> co[j]) & 1) a |= 1 << j;
				e.val[v] = (u8)((ft >> a) & 1);
			}
			e.ownbit = e.val[OWN];
			e.del.assign(k, 0);
			for (int i = 0; i < k; i++)
				e.del[i] = (int8_t)(e.val[OWN] - e.val[OWN ^ (1 << i)]);
			T.push_back(std::move(e));
		}
	}
	return T;
}

// Apply a coordinate permutation p (i -> p[i]) to a type, return (mask, ftab).
inline void permType(const EntryType& e, const std::vector<int>& p, int /*k*/,
                     u32& nmask, u32& nftab) {
	std::vector<int> co, nco;
	for (int i = 0; i < (int)p.size(); i++)
		if ((e.mask >> i) & 1) co.push_back(i);
	nmask = 0;
	for (int c : co) nmask |= 1u << p[c];
	for (int i = 0; i < (int)p.size(); i++)
		if ((nmask >> i) & 1) nco.push_back(i);
	// position j of co maps to the position of p[co[j]] inside nco
	std::vector<int> where(co.size());
	for (size_t j = 0; j < co.size(); j++)
		where[j] = (int)(std::lower_bound(nco.begin(), nco.end(), p[co[j]]) - nco.begin());
	const int d = (int)co.size();
	nftab = 0;
	for (int na = 0; na < (1 << d); na++) {
		int a = 0;
		for (int j = 0; j < d; j++)
			if ((na >> where[j]) & 1) a |= 1 << j;
		if ((e.ftab >> a) & 1) nftab |= 1u << na;
	}
}

// ------------------------------------------------- admissible own-weights
// Generalises Lemma 5.1 of the research note to arbitrary (W, r, s, k).
//
// Every coordinate i must satisfy Delta_i != 0 (else row 1^k ^ e_i has the same
// weight as the rejected own row).  Positive Delta comes only from the m entries
// that are 1 at the own row, each contributing at most s; negative Delta only
// from the r-m entries that are 0 there, each contributing at most s.  Writing
// a = min positive admissible Delta and b = min |negative| admissible Delta,
//        k <= floor(s*m/a) + floor(s*(r-m)/b).
inline std::vector<int> admissibleOwnWeights(const Predicate& P, int s, int k) {
	std::vector<int> out;
	for (int m = 0; m <= P.r; m++) {
		if (P.wHas(m)) continue;  // own row must be rejected
		int a = INT32_MAX, b = INT32_MAX;
		for (int w : P.W) {
			const int d = m - w;  // Delta such that m - Delta = w in W
			if (d > 0) a = std::min(a, d);
			if (d < 0) b = std::min(b, -d);
		}
		long long cap = 0;
		if (a != INT32_MAX) cap += (long long)s * m / a;
		if (b != INT32_MAX) cap += (long long)s * (P.r - m) / b;
		if (cap >= k) out.push_back(m);
	}
	return out;
}

// Admissible Delta values across the surviving own-weight window.
inline std::vector<int> admissibleDeltas(const Predicate& P,
                                         const std::vector<int>& ms) {
	std::vector<int> d;
	for (int m : ms)
		for (int w : P.W) {
			const int v = m - w;
			if (std::find(d.begin(), d.end(), v) == d.end()) d.push_back(v);
		}
	std::sort(d.begin(), d.end());
	return d;
}

// ---------------------------------------------------------- SWAR utilities
static const u64 ONES = 0x0101010101010101ULL;
static const u64 HIGH = 0x8080808080808080ULL;
inline bool hasByte(u64 x, u8 b) {
	const u64 t = x ^ (ONES * b);
	return ((t - ONES) & ~t & HIGH) != 0;
}

// Search-space bounds implied by the theory (see docs/THEORY.md).
//   k <= s * r        (sensitivity: every coordinate must be read)
//   k <= s * u(R)     (a valid pattern certifies Omega(n^{k/s}) <= O(n^u))
inline int kMax(int s, int r, int u) {
	const int a = s * r;
	const int b = (u > 0) ? s * u : a;
	return std::min(a, b);
}

}  // namespace nrd
