// Certified lower bounds on NRD_n(R) for symmetric Boolean predicates, with
// calibration against predicates whose exponent is already known.
//
// The point of the calibration group is methodological.  Greedy insertion into
// a downward-closed system returns a certified lower bound, not the maximum,
// so a fitted exponent could in principle be biased low.  By running the SAME
// procedure on predicates whose exponent is classical (OR_k is Theta(n^k),
// equality is Theta(n)), we can measure that bias directly instead of assuming
// it away.  Only then does the fitted exponent for the open predicates carry
// any information.

#include "nrd.hpp"
#include "nrdx.hpp"

#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <string>
#include <vector>

using namespace nrdx;

struct Target {
	int r;
	std::vector<int> W;
	const char* label;
	int group;  // 0 = calibration, 1 = open arity 5, 2 = arity-7 two-level gap
};

static const Target TARGETS[] = {
    {2, {0, 2}, "EQ2    calibration -- classical Theta(n^1)", 0},
    {2, {1, 2}, "OR2    calibration -- classical Theta(n^2)", 0},
    {3, {1, 2}, "NAE3   calibration -- published Theta(n^2)", 0},
    {3, {1, 2, 3}, "OR3    calibration -- classical Theta(n^3)", 0},
    {4, {1, 2, 3, 4}, "OR4    calibration -- classical Theta(n^4)", 0},
    {5, {0, 2, 3}, "R023   OPEN in Sharma-Velusamy (arity 5)", 1},
    {5, {1, 2, 4}, "R124   OPEN in Sharma-Velusamy (arity 5)", 1},
    {7, {0, 1, 3, 4}, "G7     arity-7 two-level gap (this work)", 2},
};
static const int NTARGETS = (int)(sizeof(TARGETS) / sizeof(TARGETS[0]));

static u32 wmask_of(const std::vector<int>& W) {
	u32 m = 0;
	for (int w : W) m |= (1u << w);
	return m;
}

// Reuse the already-validated criteria engine (61-check gate) for u(R), l(R).
static void criteria(int r, u32 wmask, int& u, int& l) {
	std::vector<nrd::LiftCtx> L((size_t)r + 1);
	for (int t = 1; t <= r; ++t) L[(size_t)t] = nrd::make_lift(r, t);
	std::vector<std::vector<nrd::Sig>> sk((size_t)r + 1);
	for (int k = 2; k <= r; ++k) sk[(size_t)k] = nrd::kcube_signatures(r, k);
	u = nrd::min_t_balanced(r, (nrd::u32)wmask, L);
	l = nrd::max_k_cube_failure(r, (nrd::u32)wmask, sk);
}

static void loglog_fit(const std::vector<int>& ns, const std::vector<i64>& ms,
                       int lastK, double& expo, double& r2) {
	expo = 0.0;
	r2 = 0.0;
	const int N = (int)ns.size();
	const int start = (N > lastK) ? (N - lastK) : 0;
	const int cnt = N - start;
	if (cnt < 3) return;
	double sx = 0, sy = 0, sxx = 0, sxy = 0, syy = 0;
	for (int i = start; i < N; ++i) {
		if (ms[(size_t)i] <= 0) return;
		const double x = std::log((double)ns[(size_t)i]);
		const double y = std::log((double)ms[(size_t)i]);
		sx += x;
		sy += y;
		sxx += x * x;
		sxy += x * y;
		syy += y * y;
	}
	const double dxx = cnt * sxx - sx * sx;
	const double dyy = cnt * syy - sy * sy;
	const double dxy = cnt * sxy - sx * sy;
	if (dxx <= 0.0) return;
	expo = dxy / dxx;
	if (dyy > 0.0) r2 = (dxy * dxy) / (dxx * dyy);
}

int main(int argc, char** argv) {
	const int nmaxCal = (argc > 1) ? atoi(argv[1]) : 13;
	const int nmax5 = (argc > 2) ? atoi(argv[2]) : 14;
	const int nmax7 = (argc > 3) ? atoi(argv[3]) : 12;
	const int onlyGroup = (argc > 4) ? atoi(argv[4]) : -1;
	const auto t0 = std::chrono::steady_clock::now();

	printf("CERTIFIED LOWER BOUNDS ON NRD_n(R), SYMMETRIC BOOLEAN PREDICATES\n");
	printf("literal model; each constraint uses r distinct variables with "
	       "arbitrary polarities\n");
	printf("every reported family is re-verified by an independent checker "
	       "(chk column)\n");
	printf("'local e' is log(m_n/m_{n-1}) / log(n/(n-1))\n\n");

	for (int ti = 0; ti < NTARGETS; ++ti) {
		const Target& T = TARGETS[ti];
		if (onlyGroup >= 0 && T.group != onlyGroup) continue;
		const u32 wm = wmask_of(T.W);
		const Predicate P = pred_from_mask(T.r, wm);
		int u = -1, l = -1;
		criteria(T.r, wm, u, l);
		const int nmax =
		    (T.group == 2) ? nmax7 : (T.r >= 5 ? nmax5 : nmaxCal);

		printf("==============================================================="
		       "=========\n");
		printf(" %s\n", T.label);
		printf(" arity %d   W=%s   criteria: u(R)=%d  l(R)=%d\n", T.r,
		       fmt_W(P).c_str(), u, l);
		printf("---------------------------------------------------------------"
		       "---------\n");
		printf("   n |     2^n |  #clauses | NRD_n >= | ratio | local e | order   "
		       "| chk\n");

		std::vector<int> ns;
		std::vector<i64> ms;
		int prevLevel = -1;
		for (int n = T.r + 1; n <= nmax; ++n) {
			std::vector<int> levels;
			if (n <= 12) {
				for (int d = 0; d <= n; ++d) levels.push_back(d);
			} else {
				std::set<int> s;
				for (int d = (n - T.r > 0 ? n - T.r : 0); d <= n - 1; ++d)
					s.insert(d);
				if (prevLevel >= 0)
					for (int o = -2; o <= 3; ++o) {
						const int d = prevLevel + o;
						if (d >= 0 && d <= n) s.insert(d);
					}
				levels.assign(s.begin(), s.end());
			}
			const BestResult R = best_lower_bound(P, n, 3, levels);
			const bool okref = reference_is_nonredundant(P, n, R.A);
			if (R.level >= 0) prevLevel = R.level;
			ns.push_back(n);
			ms.push_back(R.size);
			const long long nclauses =
			    (long long)subset_masks(n, T.r).size() * (1LL << T.r);
			char ratio[32], lexp[32];
			if (ms.size() >= 2 && ms[ms.size() - 2] > 0) {
				const double rr =
				    (double)R.size / (double)ms[ms.size() - 2];
				snprintf(ratio, sizeof ratio, "%5.3f", rr);
				snprintf(lexp, sizeof lexp, "%7.3f",
				         std::log(rr) /
				             std::log((double)n / (double)(n - 1)));
			} else {
				snprintf(ratio, sizeof ratio, "  -  ");
				snprintf(lexp, sizeof lexp, "   -   ");
			}
			printf("  %2d | %7lld | %9lld | %8lld | %s | %s | %-7s | %s\n", n,
			       1LL << n, nclauses, (long long)R.size, ratio, lexp,
			       R.order.c_str(), okref ? "ok" : "BAD");
			if (T.group != 0) {
				std::vector<int> hist((size_t)n + 1, 0);
				for (u32 a : R.A) ++hist[(size_t)__builtin_popcount(a)];
				printf("     |  witness Hamming weights:");
				for (int d = 0; d <= n; ++d)
					if (hist[(size_t)d])
						printf(" %d^%d", d, hist[(size_t)d]);
				printf("\n");
			}
			fflush(stdout);
		}
		double e5 = 0, r5 = 0, e4 = 0, r4 = 0;
		loglog_fit(ns, ms, 5, e5, r5);
		loglog_fit(ns, ms, 4, e4, r4);
		printf("  log-log fit over last 5 points : exponent = %.3f  (R^2 = "
		       "%.5f)\n",
		       e5, r5);
		printf("  log-log fit over last 4 points : exponent = %.3f  (R^2 = "
		       "%.5f)\n",
		       e4, r4);
		printf("\n");
		fflush(stdout);
	}
	const auto t1 = std::chrono::steady_clock::now();
	printf("wall %.3f s\n",
	       std::chrono::duration<double>(t1 - t0).count());
	return 0;
}
