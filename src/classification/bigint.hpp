#pragma once
// Arbitrary-precision signed integers, and the overflow exception shared with
// the fixed-width path.
//
// Why this exists.  The Hermite reduction in IntSpan stays comfortably inside
// 128 bits: the largest entry it produces anywhere at arity at most 8 is
// 4425430010319033550, which is 63 bits.  The coefficients of the membership
// solve are a different matter, reaching 3099 bits at arity 8.  Widening the
// reduction would not have helped, and a modular Hermite normal form would not
// have helped either, because the growth is in the solve and not in the basis.
// Only the solve needs arbitrary precision, and only on the predicates that
// hit it, so it is reached through a fallback in IntSpan::contains rather than
// used throughout.  Both figures are measured by the sweep and printed in its
// per-arity summary, so they can be checked rather than taken on trust.
//
// Representation: sign and magnitude, base 2^32, little-endian limbs, no
// trailing zero limbs.  Zero has an empty limb vector and neg_ == false, so
// every value has exactly one representation.

#include <cstdint>
#include <cstdio>
#include <vector>
#include <string>
#include <stdexcept>
#include <algorithm>

namespace nrd {

struct OverflowError : std::runtime_error {
    explicit OverflowError(const std::string& m) : std::runtime_error(m) {}
};

class BigInt {
public:
    BigInt() = default;

    static BigInt fromI128(__int128 v) {
        BigInt b;
        if (v == 0) return b;
        b.neg_ = (v < 0);
        // -v is undefined at the minimum of the range, so negate through the
        // unsigned type instead.
        unsigned __int128 u = b.neg_
            ? ((unsigned __int128)(-(v + 1))) + 1u
            : (unsigned __int128)v;
        while (u) { b.d_.push_back((uint32_t)(u & 0xFFFFFFFFu)); u >>= 32; }
        return b;
    }

    bool isZero() const { return d_.empty(); }
    bool negative() const { return neg_; }

    size_t bitLength() const {
        if (d_.empty()) return 0;
        size_t n = (d_.size() - 1) * 32;
        uint32_t top = d_.back();
        while (top) { ++n; top >>= 1; }
        return n;
    }

    bool equalsI128(__int128 v) const { return cmp(*this, fromI128(v)) == 0; }

    static int cmpMag(const BigInt& a, const BigInt& b) {
        if (a.d_.size() != b.d_.size()) return a.d_.size() < b.d_.size() ? -1 : 1;
        for (size_t i = a.d_.size(); i-- > 0; )
            if (a.d_[i] != b.d_[i]) return a.d_[i] < b.d_[i] ? -1 : 1;
        return 0;
    }

    static int cmp(const BigInt& a, const BigInt& b) {
        if (a.neg_ != b.neg_) return a.neg_ ? -1 : 1;
        const int c = cmpMag(a, b);
        return a.neg_ ? -c : c;
    }

    friend BigInt operator+(const BigInt& a, const BigInt& b) {
        if (a.neg_ == b.neg_) {
            BigInt r = addMag(a, b); r.neg_ = a.neg_; r.fix(); return r;
        }
        const int c = cmpMag(a, b);
        if (c == 0) return BigInt();
        if (c > 0) { BigInt r = subMag(a, b); r.neg_ = a.neg_; r.fix(); return r; }
        BigInt r = subMag(b, a); r.neg_ = b.neg_; r.fix(); return r;
    }

    friend BigInt operator-(const BigInt& a, const BigInt& b) {
        BigInt nb = b;
        if (!nb.isZero()) nb.neg_ = !nb.neg_;
        return a + nb;
    }

    friend BigInt operator*(const BigInt& a, const BigInt& b) {
        BigInt r;
        if (a.isZero() || b.isZero()) return r;
        r.d_.assign(a.d_.size() + b.d_.size(), 0u);
        for (size_t i = 0; i < a.d_.size(); ++i) {
            uint64_t carry = 0;
            const uint64_t ai = a.d_[i];
            for (size_t j = 0; j < b.d_.size(); ++j) {
                // (2^32-1)^2 + 2(2^32-1) = 2^64-1, so this cannot overflow.
                const uint64_t cur =
                    (uint64_t)r.d_[i + j] + ai * (uint64_t)b.d_[j] + carry;
                r.d_[i + j] = (uint32_t)(cur & 0xFFFFFFFFu);
                carry = cur >> 32;
            }
            size_t k = i + b.d_.size();
            while (carry) {
                const uint64_t cur = (uint64_t)r.d_[k] + carry;
                r.d_[k] = (uint32_t)(cur & 0xFFFFFFFFu);
                carry = cur >> 32;
                ++k;
            }
        }
        r.neg_ = (a.neg_ != b.neg_);
        r.trim(); r.fix();
        return r;
    }

    // Truncating division, matching the C++ operators the fixed-width path
    // uses: the quotient rounds toward zero and the remainder takes the sign
    // of the dividend.
    //
    // The divisor magnitude must fit in 96 bits.  That is guaranteed at every
    // call site here, because divisors are entries of the reduced matrix and
    // those stay at 63 bits.  The bound is what keeps the running remainder
    // inside 128 bits: rem < |b| <= 2^96-1 gives rem*2^32 + limb <= 2^128-1.
    static void divmod(const BigInt& a, const BigInt& b, BigInt& q, BigInt& r) {
        if (b.isZero()) throw OverflowError("bigint division by zero");
        if (b.d_.size() > 3) throw OverflowError("bigint divisor exceeds 96 bits");
        unsigned __int128 bd = 0;
        for (size_t i = b.d_.size(); i-- > 0; )
            bd = (bd << 32) | (unsigned __int128)b.d_[i];
        q = BigInt();
        r = BigInt();
        if (a.isZero()) return;
        q.d_.assign(a.d_.size(), 0u);
        unsigned __int128 rem = 0;
        for (size_t i = a.d_.size(); i-- > 0; ) {
            rem = (rem << 32) | (unsigned __int128)a.d_[i];
            const unsigned __int128 qd = rem / bd;   // < 2^32 by the invariant
            rem -= qd * bd;
            q.d_[i] = (uint32_t)qd;
        }
        q.neg_ = (a.neg_ != b.neg_);
        q.trim(); q.fix();
        while (rem) { r.d_.push_back((uint32_t)(rem & 0xFFFFFFFFu)); rem >>= 32; }
        r.neg_ = a.neg_;
        r.fix();
    }

    std::string str() const {
        if (d_.empty()) return "0";
        std::vector<uint32_t> t = d_;
        std::string s;
        while (!t.empty()) {
            uint64_t rem = 0;
            for (size_t i = t.size(); i-- > 0; ) {
                const uint64_t cur = (rem << 32) | (uint64_t)t[i];
                t[i] = (uint32_t)(cur / 1000000000ull);
                rem = cur % 1000000000ull;
            }
            while (!t.empty() && t.back() == 0u) t.pop_back();
            char buf[16];
            if (t.empty()) snprintf(buf, sizeof buf, "%llu", (unsigned long long)rem);
            else           snprintf(buf, sizeof buf, "%09llu", (unsigned long long)rem);
            s = std::string(buf) + s;
        }
        return (neg_ ? "-" : "") + s;
    }

private:
    static BigInt addMag(const BigInt& a, const BigInt& b) {
        BigInt r;
        r.d_.assign(std::max(a.d_.size(), b.d_.size()) + 1, 0u);
        uint64_t carry = 0;
        for (size_t i = 0; i < r.d_.size(); ++i) {
            uint64_t cur = carry;
            if (i < a.d_.size()) cur += a.d_[i];
            if (i < b.d_.size()) cur += b.d_[i];
            r.d_[i] = (uint32_t)(cur & 0xFFFFFFFFu);
            carry = cur >> 32;
        }
        r.trim();
        return r;
    }

    // Requires |a| >= |b|.
    static BigInt subMag(const BigInt& a, const BigInt& b) {
        BigInt r;
        r.d_ = a.d_;
        int64_t borrow = 0;
        for (size_t i = 0; i < r.d_.size(); ++i) {
            int64_t cur = (int64_t)r.d_[i] - borrow
                        - (i < b.d_.size() ? (int64_t)b.d_[i] : 0);
            if (cur < 0) { cur += ((int64_t)1 << 32); borrow = 1; }
            else borrow = 0;
            r.d_[i] = (uint32_t)cur;
        }
        r.trim();
        return r;
    }

    void trim() { while (!d_.empty() && d_.back() == 0u) d_.pop_back(); }
    void fix()  { if (d_.empty()) neg_ = false; }

    std::vector<uint32_t> d_;
    bool neg_ = false;
};

}  // namespace nrd
