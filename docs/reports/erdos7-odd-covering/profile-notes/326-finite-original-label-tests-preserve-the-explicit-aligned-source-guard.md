[Index](../marked_head_profile.md) · [Explicit aligned guard](325-an-explicit-aligned-parameter-neighborhood-keeps-the-complete-comparison-below400.md) · [Exact tail calculator](../frontier/j_aligned_source_guard_truncation.py)

# Finite original-label tests for the explicit aligned source guard

Let f be an actual finite original357 source, or its countable actual-label
completion, in302's fixed effective9 chart. Let f_c retain exactly its
original forbidden labels3^a5^b7^e with

    0<=a<=A, 0<=b<=B, 0<=e<=C, A>=4, B>=1, C>=1.

All other labels are absent in f_c. A retained label keeps its original
residue; no modulus is identified with another. Write subscripts c for
quantities evaluated on this actual finite retained source. In particular
q_c and rho_c are its complete source parameters, with the absent tail
treated as absent in the original formulas. They are not parameter values
obtained by discarding terms from a different source measure.

Suppose the original45 and135 are present and aligned in a surviving
root1 mod9 cell. This condition, the effective9 shallow pair, and every
present original405 remain literally unchanged in f_c. No assertion is
made that numerical qJ/rho guards are automatically preserved.

Put eta0=10^-14 and r*=2/675. The following FINITE data test is sufficient
for f to satisfy325's guard:

    q_c >= 1-eta0+Qdown,
    rho_c <= r*+eta0-Rup,                         (FG1)

where the complete explicit errors are

    Qdown=36*3^-A+33*5^-B,
    Rup=T35+(S_c+2s_c)*7^-C/5
        <=T35+7^-C/3.                            (FG2)

Here s_c is actual raw35 source mass and S_c its actual normalized357
survivor mass. The constant T35 is the full omitted geometric tail below.
All data in(FG1) are determined by finitely many original residues.
The inference includes every actual continuation of those source labels
in the fixed effective9 chart with the retained original45/135 alignment.

For example, with(A,B,C)=(34,24,19), the simpler buffered finite test

    q_c>=1-eta0/2, rho_c<=r*+eta0/2                (FG3)

implies325's full guard. This is a sufficient test with a boundary buffer,
not an assertion that every source in325's closed box passes(FG3).

## Complete tail constants

Define

    t3=3^-A/2, t5=5^-B/4, t7=7^-C/6,
    T35=(15/8)[1-(1-3^(-A-1))(1-5^(-B-1))],
    T357=(35/16)[1-(1-3^(-A-1))(1-5^(-B-1))(1-7^(-C-1))],
    Tlate=(1/72)[1-(1-3^(2-A))(1-5^-B)],
    Tearly=t3+(13/9)t5=T35-Tlate,
    v7=7^-C.

Each is the sum of reciprocal ORIGINAL moduli in the indicated omitted
family, with no finite-height assumption on f. The early35 families are
pure3, pure5,3*5^b and9*5^b; the late family is3^a5^b witha>=3,b>=1.
The identity Tearly=T35-Tlate follows from this disjoint label partition.
These tails vanish as the individual cutoffs tend to infinity.

The same original forbidden-cylinder union argument as302 gives

    ||eta_c-eta||var=h_c-h<=t3,
    ||Lambda_c-Lambda||var=s_c-s<=T35,
    sum_l|n_c,l-n_l|=s_c-s<=T35.                  (FG4)

All these differences are nonnegative measures. The norm is full signed
variation, not half its value. The complete normalized357 measures obey

    ||mu_c-mu||var<=(6/5)(T357+t7),
    -(6/5)T357<=S-S_c<=S_c*v7/5.                  (FG5)

Indeed full Haar survivors H are contained in H_c, and pure-seven masses
obey0<=u7_c-u7<=t7 withu7>=5/6. For the norm split

    1_H/u7-1_Hc/u7_c
       =(1_H-1_Hc)/u7+1_Hc(1/u7-1/u7_c).

The first norm is at most(6/5)T357. SinceH_c lies in the pure-seven
survivor, the second is at most(6/5)t7. For the sharper upper mass bound,
S<=S_c*u7_c/u7<=S_c+(6/5)S_c*t7. For the lower mass bound retain the
nonnegative normalization term and pay only the first term. This keeps
the actual normalization; neither mu nor its old35 projection is silently
replaced by unnormalized Haar.

## Actual stage variables have directed errors

The source quantities are48's

    eta_l=(1-deficit_l)/9,
    d_l=z-alpha_ROOT(l)-beta_l,
    n_l=eta_l*d_l-late_l.

The pure5 forbidden union increases when omitted labels are added. Thus

    0<=z_c-z<=t5,
    0<=d_c,l-d_l<=3t5.                           (FG6)

For the second bound, d_l is the five-coordinate complement of the union
of pure5, the alpha labels in its root and the beta labels in its cell.
Each omitted family adds width at mostt5. This is the actual section
description; it is not inferred from cell masses.

Write alpha_1 for the root1 additional alpha width and beta_B for the SUM
of the three root1 additional beta widths. Direct set-difference bounds
give

    -t5<=alpha_1-alpha_c,1<=t5,
    -6t5<=beta_B-beta_c,B<=t5.                    (FG7)

For alpha, added alpha cylinders can increase the assigned union by at
mostt5, and added preceding pure5 cylinders can decrease it by at mostt5.
For beta, the total omitted beta widths over the three cells are at
mostt5. In each cell preceding pure5 and root1 alpha additions remove at
most2t5; summing those three cell-width coordinates costs at most6t5.
The beta width normalization has no ternary1/9 factor.

For the late ROOT1 RAW mass, both preceding source deletion and the late
union itself increase under adding labels. Therefore

    -Tearly<=late_B-late_c,B<=Tlate.              (FG8)

The loss can only occur on omitted early35 cylinders, and the gain only
on omitted late cylinders. All other already present source cylinders
retain their residues. This remains true if late rectangles overlap each
other or preceding deletions. No disjointness assumption is needed.

For completeness each alpha-root coordinate has absolute error<=t5;
each beta-cell coordinate has error between-2t5 andt5. The same late
bounds hold after restricting to any fixed mod9 cell, and its full vector
has variation at mostT35. These are complete bounds for all source-stage
factors needed below.

## The original carrier mixture and qJ polynomial

Use46's actual carrier definition: at every positive depth e, the original
3*7^e root and9*7^e cell give c_e. Absent or SHALLOW-killed carriers are
empty. This is geometric classification relative to the fixed3/9 chart,
not a test of zero mass after the complete pure-seven union. Hence c_e is
exactly unchanged fore<=C. For larger e the retained source has empty
carrier. With the original weightsu_e=6/(5*7^e),

    pi_c=5 sum_e u_e 1_(c_e=c),
    ||pi-pi_core||_1<=2v7.                        (FG9)

Each nonempty carrier coordinate can only increase. No optimizing carrier
is selected or transported.

In71's barycentric coordinates put

    a2=4alpha_1, z0=4(1-z), bB=4beta_B, lB=72late_B,
    d1=18(1/9-eta_0), d2=18(1/9-eta_1),
    W=d1*pi_(0,1)+d2*pi_(0,0),
    qJ=a2*z0*bB*lB*W.                            (FG10)

Every factor lies in[0,1]. Both deficit coordinates, z0, and W increase
under adding omitted labels: the relevant nonempty carrier coordinates
also increase. Moreover

    0<=W-W_c<=18t3+v7.

The deficit bound uses the total pure3 mass loss, while the added carrier
part has total weight at mostv7 and deficits at most1. Equations(FG7) and
(FG8), followed by the elementary product Lipschitz bound on[0,1], give

    -Qdown<=qJ-q_c<=Qup,
    Qdown=4t5+24t5+72Tearly=36*3^-A+33*5^-B,
    Qup=12t5+72Tlate+18t3+v7.                    (FG11)

A sharper directly evaluable lower uses the positive parts of
a2_c-4t5, bB_c-24t5 andlB_c-72Tearly, multiplied byz0_c*W_c.
The simpler Qdown bound in(FG11) suffices for(FG1). Beneficial monotone
deficit and carrier errors are not paid as losses in Qdown.

## The same mixed-carrier lower mass and rho

Keep46's ORIGINAL mass formula

    T2=(1/5)[max(d)/18+(h+h1+max(eta))/4+1/72],
    Hpi=sum_c pi_c*h(c),
    h(c)=[n(ROOT=c.root)+n(c.cell)]/5,
    S0=s-T2-Hpi, rho=S-S0.                       (FG12)

Empty root or cell entries contribute zero. This h(c) is at most2s/5;
each cell coefficient in its positive mixture is at most2/5. The h1
term is the larger pure3 root throughout the fixed effective9 chart,
by48(SC3). All quantities remain those of their actual source.

Equation(FG6) and monotonicity of eta give

    0<=T2_c-T2<=T2err:=t5/30+3t3/20.              (FG13)

The existing carrier part loses at most(2/5)(s_c-s) from its n values.
The new carrier tail adds at most(2s_c/5)v7. Consequently

    -T35-(2s_c/5)v7 <= S0-S0_c <= T2err.          (FG14)

For the upper bound the negative s change absorbs the existing-carrier
loss; for the lower bound discard the beneficial T2 reduction. Combining
with(FG5) gives both useful directions

    -[(6/5)T357+T2err] <= rho-rho_c
         <= T35+[(S_c+2s_c)/5]v7 = Rup.          (FG15)

Since0<=S_c<=s_c<=5/9, Rup<=T35+v7/3. This proves(FG1).
There is no substitution of the aligned floor for the actual rho.

The reverse buffered implication is also available. A full source with

    qJ>=1-eta0/2, rho<=r*+eta0/2

has its retained source inside325's unbuffered guard whenever
Qup<=eta0/2 and(6/5)T357+T2err<=eta0/2. Thus the retained numerical
hypothesis is justified by a measured buffer, not by label retention alone.

## Old core boxes cannot meet the new narrow guard

For ANY actual source cut at(A,B,C), complete missing source budgets give

    q_c <= (1-3^(2-A))^2(1-5^-B)^4(1-7^-C).       (FG16)

Indeed the normalized deficit total is at most1-3^(2-A); each ofz0,
a2,bB is at most1-5^-B; lB is at most(1-3^(2-A))(1-5^-B); and the
nonempty carrier total is at most1-7^-C. Apply(FG10). No choice of
the retained residues can remove these missing-label deficits.

For301's uniform20 core this forces

    1-q_c>=5.162391532336257...*10^-9,

and for its unequal357 cut(17,10,8) it forces

    1-q_c>=7.224497442167777...*10^-7.

Both exceed10^-14. Thus these two old cores cannot themselves satisfy
325's new guard, even before evaluating a truncation error. The earlier
absence/ineffectiveness branches survive those cores for the finite
blocker reasons in301/305; a tiny numerical parameter box is different.

At the larger but still finite cut(34,24,19), exact rational evaluation
of the displayed full tails gives

| Directed error | Decimal display | Strict rational upper |
|---|---:|---:|
| Qdown | 2.7122862389417161e-15 | 2.713e-15 |
| Qup | 1.2341557197302360e-15 | 1.235e-15 |
| T35+v7/3 | 7.3010412179197440e-17 | 7.302e-17 |
| (6/5)T357+T2err | 9.8809834891562013e-17 | 9.882e-17 |

Each rational upper is less thaneta0/2. The exact source-independent
formulas above determine the values; decimals are displays only.
Thus both buffered implications above apply. The universal obstruction
in(FG16) is then only1.234155719730236...*10^-15, beloweta0/2.
This last observation checks compatibility of the scalar buffer with
the missing-budget bound; it is not a source realizability assertion.

The finite buffered domain is nevertheless nonempty by the EXISTING311
matching families. Their original residue rules do not depend on the
height N. Every N>=34 family consequently restricts to the same fixed
actual f_c at(34,24,19). Since311 provesqJ(f_N)->1 andrho(f_N)->r*, apply
(FG11),(FG15) to each f_N and then take those scalar limits. They give

    q_c>=1-Qup>1-eta0/2,
    rho_c<=r*+(6/5)T357+T2err<r*+eta0/2.

Thus this fixed actual finite source satisfies(FG3). This proof reuses
the published all-height family and its limits; it does not replace
them by a new CRT scan or assert an independently computed exact q_c
or rho_c value.

All finite quantities can in principle be obtained by exact CRT union
counts at period3^A5^B7^C with the original retained residues. This proof
does not assert that enumeration of that entire period is computationally
efficient; symbolic cylinder counting or independently certified bounds
may be used to establish(FG1) or(FG3).

The [numerical companion](../frontier/j_aligned_source_guard_truncation.py) accepts
cutoffs A,B,C and reconstructs the complete geometric tails, all directed
parameter errors and the resulting buffered thresholds using fractions.
Its default report contains the two old core cuts and(34,24,19). It
binds this proof and the existing46/48/71/301/302/305/311/325 source files
by their logical bytes. It does not evaluate q_c,rho_c or any high-period
source union, and does not certify a particular source's membership from
unverified parameter input.

From the repository root, replay the default cuts and bound sources with

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/j_aligned_source_guard_truncation.py --check
```

The [canonical certificate](../certificates/source_norms/j_aligned_source_guard_truncation.json)
stores exact fractions. Additional cuts use `--cut A B C` with a separate
`--certificate` output; `--write` produces it and `--check` replays it.

This theorem certifies entry to325's J source comparison. It does not
identify J with K or Gamma19, does not reuse301's old core errors on a
different law, and does not supply a global source join or arbitrary
later-prime continuation. Any use of a larger seven-prime core must
retain and price that core's own source-law, forbidden-mask and complete
test tails. No new LP, source scan or altered325 consumer is required.
