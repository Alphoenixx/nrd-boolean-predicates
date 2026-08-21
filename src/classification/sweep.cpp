// Sweep the non-redundancy classification of symmetric Boolean predicates
// across arities.  Arities 1-5 reproduce published results (validation);
// arities 6+ are new territory.
//
// usage:  ./bin_sweep [max_arity]        1 <= max_arity <= 8, default 7

#include "nrd.hpp"
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <vector>
#include <string>

using namespace nrd;

struct Row {
    u32 wmask;
    int size;
    int u;
    int l;
};

static const int MAX_ARITY = 8;

int main(int argc, char** argv) {
    int maxr = 7;
    if (argc > 1) {
        char* end = 0;
        const long v = strtol(argv[1], &end, 10);
        if (end == argv[1] || *end != '\0' || v < 1 || v > MAX_ARITY) {
            fprintf(stderr,
                    "usage: %s [max_arity]   1 <= max_arity <= %d, default 7\n"
                    "arity 8 is computed in full; the membership solve falls back\n"
                    "to arbitrary precision on the predicates that need it\n",
                    argv[0], MAX_ARITY);
            return 2;
        }
        maxr = (int)v;
    }

    clock_t t_all = clock();

    for (int r = 1; r <= maxr; ++r) {
        clock_t t0 = clock();

        std::vector<LiftCtx> L((size_t)r + 1);
        for (int t = 1; t <= r; ++t) L[(size_t)t] = make_lift(r, t);

        std::vector<std::vector<Sig>> sk((size_t)r + 1);
        for (int k = 2; k <= r; ++k) sk[(size_t)k] = kcube_signatures(r, k);

        std::vector<u32> reps = weight_mask_reps(r, true);

        std::vector<Row> rows;
        std::vector<Row> mismatches;
        int unresolved_u = 0;
        int errors = 0;

        for (size_t z = 0; z < reps.size(); ++z) {
            Row row;
            row.wmask = reps[z];
            row.size  = relation_size(r, reps[z]);
            try {
                row.u = min_t_balanced(r, reps[z], L);
            } catch (const std::exception& e) {
                printf("  !! EXCEPTION r=%d W=%s : %s\n",
                       r, fmt_W(reps[z], r).c_str(), e.what());
                fflush(stdout);
                row.u = -2;
                ++errors;
            }
            row.l = max_k_cube_failure(r, reps[z], sk);
            if (row.u == -1) ++unresolved_u;
            rows.push_back(row);
            if (row.u != row.l) mismatches.push_back(row);
        }

        double secs = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;

        printf("\n");
        printf("================================================================\n");
        printf(" ARITY r = %d   (%zu predicates up to bit-flip, trivial excluded)\n",
               r, reps.size());
        printf("================================================================\n");
        printf("%4s | %-22s | %4s | %4s | %4s | %s\n",
               "idx", "W", "|R|", "u(R)", "l(R)", "mismatch");
        printf("-----+------------------------+------+------+------+---------\n");
        for (size_t z = 0; z < rows.size(); ++z) {
            const Row& x = rows[z];
            char ub[16], lb[16];
            if (x.u == -2) snprintf(ub, sizeof ub, "%s", "ERR");
            else if (x.u < 0) snprintf(ub, sizeof ub, "%s", "none");
            else snprintf(ub, sizeof ub, "%d", x.u);
            snprintf(lb, sizeof lb, "%d", x.l);
            printf("%4zu | %-22s | %4d | %4s | %4s | %s\n",
                   z, fmt_W(x.wmask, r).c_str(), x.size, ub, lb,
                   (x.u != x.l) ? "YES" : "");
        }

        printf("\n  arity %d summary: %zu predicates, %zu mismatches, %d with no t-balance, %d errors\n",
               r, reps.size(), mismatches.size(), unresolved_u, errors);
        printf("  max |entry| seen in Hermite reduction so far: %s\n",
               i128_str(g_maxAbs).c_str());
        printf("  membership queries redone in arbitrary precision so far: %lld\n",
               g_bigFallbacks);
        printf("  widest value in the arbitrary-precision solve so far: %zu bits\n",
               g_bigMaxBits);
        if (!mismatches.empty()) {
            printf("  UNRESOLVED PREDICATES AT ARITY %d:\n", r);
            for (size_t z = 0; z < mismatches.size(); ++z) {
                const Row& x = mismatches[z];
                int gap = (x.u < 0) ? -1 : (x.u - x.l);
                printf("    W=%-20s |R|=%3d  Omega(n^%d) .. O(n^%s)   gap=%d\n",
                       fmt_W(x.wmask, r).c_str(), x.size, x.l,
                       (x.u < 0 ? "?" : std::to_string(x.u).c_str()), gap);
            }
        }
        printf("  arity %d wall time: %.3f s\n", r, secs);
        fflush(stdout);
    }

    printf("\ntotal wall time: %.3f s\n",
           (double)(clock() - t_all) / (double)CLOCKS_PER_SEC);
    return 0;
}
