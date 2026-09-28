# One global phase assignment realizes every unary root count

For every fixed eleven-cofactor head inventory, one assignment of the actual outside roots simultaneously attains the maximum possible number of distinct blocked roots at every head row. Thus the worst root-count profiles used in the conditional source criterion are jointly realizable. This does not make its separate query-cylinder upper bounds sharp.

The result concerns the numerical labels `c*q`, where `c` is a nonunit divisor of 315 and `q>=11` is prime. It is an ordinary construction with exact finite checks, not new Lean verification or a uniform continuation theorem.

## 1. Keep one original phase per numerical label

Put

    C={3,5,7,9,15,21,35,45,63,105,315}.

Fix arbitrary head phases `alpha_c mod c` for the eleven originals `c*q`. Normalize the pure outside forbidden root to zero. At a head row `u mod315`, define

    n_q(u)=#{c in C : u=alpha_c mod c}.

For a globally fixed assignment of nonzero outside roots `beta_c mod q`, let

    r_q(u)=|{beta_c : u=alpha_c mod c}|.

There exists ONE such assignment satisfying

    r_q(u)=min(n_q(u),q-1) for every u mod315.          (GC1)

The actual full phase at modulus `c*q` is the unique CRT solution of the prescribed head and outside components. No original receives different phases at different rows.

## 2. A repeated color can be placed on disjoint predicates

If `q>=13`, assign eleven different nonzero roots to the eleven labels. Every active label contributes a different root, proving GC1.

For `q=11`, write `u0=alpha_315`. If some `c<315` has `alpha_c != u0 mod c`, give this label and the 315 label the same root; give the remaining nine labels the other nine distinct nonzero roots. The repeated-color predicates are disjoint: the 315 predicate holds only at `u0`, where the selected `c` predicate fails. Therefore no row contains a repeated active root, and no row has all eleven labels active. Hence `r_11=n_11<=10` everywhere.

Otherwise every head phase equals the corresponding reduction of `u0`. Give the 315 and 3 labels the same root and assign distinct other roots to the remaining nine labels. At `u0`, all eleven labels are active and exactly one pair shares a root, so `r_11=10`. Away from `u0`, the 315 label is inactive and all active roots are distinct. Again GC1 holds everywhere.

No surviving-head assumption was used. The construction can be restricted to any subset of the 315 rows. If fewer than eleven singleton labels are present, ten nonzero roots already suffice at `q=11`; all present labels can simply have distinct roots.

Different outside primes can use these constructions simultaneously. Their numerical label sets are disjoint, so CRT produces one actual family with all specified head projections. In particular, the four primes 11,13,17,19 realize their entire root-count profiles in one 44-original assignment.

## 3. The worst live-root counts are attained on one actual source

For the four outside primes `B={11,13,17,19}`, fix any actual head survivor `U`. Define

    G_alpha={u in U : n_11(u)<10},
    tbar_q(u)=q-1-n_q(u), u in G_alpha.

Since there are only eleven cofactor slots, the other three coordinates always have positive `tbar`. The common-inventory bound of [Report 721](721-common-original-label-inventory-limits-simultaneous-bad-head-rows.md) shows that at most one row is excluded from `U` by this definition. Thus `G_alpha` is nonempty for either actual 75/85-row head of Report 723.

Every actual outside-root assignment `beta` leaves at least `tbar_q(u)` roots on `G_alpha`. Construction GC1 gives a single assignment `beta_star` leaving exactly that many roots on every such row. It leaves no 11 root on `U` outside `G_alpha`.

Consequently, the possible loss of a head row with count at least ten is real for the specified pure/unary avoidance source. It is not produced by independently optimizing different rows.

## 4. An exact minimax identity for the declared reciprocal-cap score

This section retains the precise score from [Report 723](723-global-unary-inventories-and-one-reweighted-source-free-all-outside-roots.md), including its omission of queried-root-live indicators. It does not replace actual cylinder probabilities by equalities.

For a head probability `p` and a nonempty actual unary-live head support, define

    C_(c,T)^beta(p)=max_(a mod c)
        sum_(u=a mod c)p(u) product_(q in T)1/t_q^beta(u),

where `t_q^beta(u)` is the actual positive live-root count. Let `Psi_(alpha,beta)(p)` be any fixed nonnegative weighted sum of these caps. Let `Phi_alpha(p)` be the same expression with `tbar_q` on `G_alpha`.

Then

    max_beta min_(p on actual unary-live rows) Psi_(alpha,beta)(p)
       = min_(p on G_alpha) Phi_alpha(p).             (GC2)

For every `beta`, laws supported on `G_alpha` are admissible and each reciprocal cap is at most its `tbar` counterpart. This proves the upper inequality. For `beta_star`, the admissible rows are exactly `G_alpha` and all live-root counts equal `tbar`, proving the reverse inequality. These finite-dimensional minima exist because the respective probability simplexes are nonempty and the cap functions are continuous.

Report 723's positive coefficients satisfy these hypotheses, so GC2 applies to its sufficient continuation score. The remaining outer variation is the globally fixed head projections, not arbitrary independently chosen row loads.

An actual mixed query has the smaller expression

    sum_(u=a mod c)p(u)
       product_(q in T)[1_(queried root is live at u)/t_q^beta(u)].

Even when every live-root COUNT is worst simultaneously, the same queried root need not be live at every contributing row. GC1 and GC2 therefore do not prove simultaneous sharpness of the actual query caps, equality with an unrestricted source game, or universal positivity of the continuation gate.

## Exact checks and remaining scope

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_global_colors.py) checks all 97,020 maximum-anchor/cofactor/phase combinations in the repeated-color intersection argument, the finite indicator cases, all 315 coherent head-phase assignments, and 1,024 additional complete phase/prime configurations. Every literal numerical family is reconstructed by CRT and its counts are read back on all 315 rows. The result is [retained here](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_global_colors.json).

The two-case construction proves the universal assertion; the additional finite configurations are diagnostics. The construction has also been independently reviewed. No statement about missing higher powers, additional mixed-prime labels, or unrestricted Erdős #7 follows merely from attaining these count profiles.
