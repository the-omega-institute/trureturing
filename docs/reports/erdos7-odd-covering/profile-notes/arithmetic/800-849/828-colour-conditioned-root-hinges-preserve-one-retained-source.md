# Colour-conditioned root hinges preserve one retained source

One retained kernel admits a complete conditional hinge comparison that
keeps its ternary mixture inside every nonternary colour cell. This bound
is always no larger than the version that also separates ternary leaves.
For fixed colour probabilities it is convex in the retained kernel; on a
fixed live source cell it is affine in each whole probability block.

The fixed phase31 candidate and C point of [Report827](827-retained-factorial-hinges-preserve-complete-heights-but-need-not-improve-the-gate.md)
do not benefit from this comparison. Its new h16 hinge is approximately
1.1950722249, compared with the inherited full-source hinge0.2927768848.
The complete new gate is negative for every real threshold0<=h<28 on
that same candidate and point. This is a candidate diagnostic, not an
obstruction for all kernels or an actual covering example.

The result is ordinary mathematics with exact rational arithmetic checks,
not Lean verification or unrestricted Erdős#7.

## 1. Condition the one retained source

Use the actual product source and categorical kernel of
[Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md).
The ternary leaves are(4,7,2,5,8), in roots{4,7} and{2,5,8}, with Haar
suffixes above depth2. For each nonternary head prime q, the one actual
normalized pure-q law lambda_q satisfies every literal cylinder bound

    lambda_q(a modq^e)<=C_q/q^e,  C_q=(q-1)/(q-2), e>=1.

The fixed first-digit colour probabilities are pi_q(c). One normalized
leaf vector w and one table satisfy0<=u_l(s)<=w_l. As in Report810, the
retained measure nu_u has mass

    u_l(s) pi(s),  pi(s)=product_q pi_q(s_q)

on the leaf/colour cell, using the original laws within that cell.
Every subsequent query and restriction uses this same u, pi and source.

For each colour pattern s define

    M_s=sum_l u_l(s),
    R_s=max(u_4(s)+u_7(s), u_2(s)+u_5(s)+u_8(s)),
    V_s=max_l u_l(s).                                      (CR1)

Thus0<=V_s<=R_s<=M_s. If pi(s)>0 and M_s>0, conditioning only on s
leaves a product law: the ternary mixture with weights u_l(s)/M_s,
times the independent lambda_q conditioned on their declared colours.
Cells of zero mass contribute zero and need no conditional division.

A compatible literal q^e cylinder in a positive colour c has conditional
mass at most

    t_(q,c)(e)=min(1,C_q/[pi_q(c)q^e]), e>=1.                 (CR2)

An incompatible first digit has mass zero. For a singleton colour, the
compatible depth1 event has mass1; CR2 gives1 because pi_q(c)<=C_q/q.
The conditional ternary bounds are

    Pr(J_(3,s)>=1)=R_s/M_s,
    Pr(J_(3,s)>=j)=(V_s/M_s)3^(2-j), j>=2.                  (CR3)

The nonternary run J_(q,c) has tails CR2. These nonincreasing sequences
are genuine probability tails with finite means. They define auxiliary
runs, not the simultaneous incidence indicators of an actual layout.

## 2. Arbitrary cofactor phases and complete heights

A finite complete query Q_a chooses one arbitrary literal phase for each
numerical modulus in a finite exponent box, including the unit term.
Different cofactors may choose unrelated phases in the same coordinate.
Distinctness is numerical; no label is split into independently chosen
pieces or counted twice.

[Report790 PC9](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md)
already proves the needed rearrangement. For nonnegative coefficients
c_i and events with probabilities bounded by t_i,

    E(sum_i c_i 1_(A_i)-h)_+
      <=E(sum_i c_i 1_(U<=t_i)-h)_+,                       (CR4)

where U is an auxiliary uniform variable. Apply CR4 to the conditional
product law of section1, one coordinate at a time. All remaining
coordinates supply nonnegative coefficients, and each actual numerical
label keeps its own cylinder and phase during the comparison. Independent
auxiliary uniforms arise from successive product integrations. Only after
those replacements does the completed exponent box factor as a product
of(1+J). [Problem-details32 JR8--JR9](../../../problem-details/32-conditional-root-measures-and-unrestricted-prime-tails.md)
gives the earlier conditional-label formulation of the same argument.

Completing missing labels enlarges the nonnegative load. Monotone
convergence and the finite complete product mean therefore give, for
every one actual query layout,

    integral (Q_a-h)_+ dnu_u <= H_root(h;pi,u),
    H_root=sum_s M_s pi(s)
       E[((1+J_(3,s)) product_q(1+J_(q,s_q))-h)_+].          (CR5)

The sum contains all heights. The actual layout is the same before and
after summing cells. Its bound does not require layouts attaining the
different cell envelopes to be jointly realizable; replacing each cell
by an upper bound is conservative.

## 3. Keep the same survivor denominator

Let U be the complete actual old survivor, alpha_u=nu_u(U)>0, and use
the supported normalized source of [Report815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md),

    mu_u=nu_u restricted to U / alpha_u.

For h>=0, integrate Q_a<=h+(Q_a-h)_+ and restrict the nonnegative
hinge to U. EquationCR5 gives

    integral Q_a dmu_u <= h+H_root(h;pi,u)/alpha_u.          (CR6)

There is no normalization by initial retained mass or by a separate
cell/query mass. Keep the same certified head floor L(pi,u), retained
fourth-moment numerator K_u(pi), actual pure29 factor T29, and complete
[Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md)
tail T. Within that report's unchanged29 and finite-prime-tail support
conditions, the sufficient complete gate becomes

    G_h=(28-h)L-H_root(h;pi,u)-27T29 T K_u(pi)>0,
    0<=h<28.                                             (CR7)

The hinge and moment debits are nonnegative, so positivity itself
implies L>0 and supplies alpha_u>0. CR7 does not assert positivity for
every kernel, phase family or source law.

## 4. Positive unnormalized laws on a fixed live cell

The standard partitions are{0},{1},{2,3,4} at5 and{0},nonzero at the
other observed primes. On the fixed actual structural cells of
[Reports816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md)
and [820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md),
each live singleton has

    pi_q(c)>=(q-2)/(q^2-q-1)>C_q/q^2.

Each nonsingleton other-colour has pi_q(c)>C_q/q. Thus no live
depth>=2 cap is saturated. Multiplying the conditional law of N=1+J
by pi=pi_q(c) removes all divisions. For a singleton the positive measure
B_(q,c) is

    B(1)=0, B(2)=pi-C_q/q^2,
    B(n)=C_q(q-1)/q^n for n>=3,
    mass=pi, mean=2pi+C_q/[q(q-1)].                        (CR8)

For an other-colour it is

    B(1)=pi-C_q/q,
    B(n)=C_q(q-1)/q^n for n>=2,
    mass=pi, mean=pi+C_q/(q-1).                            (CR9)

Multiplying the ternary law by M_s gives

    B_(3,s)(1)=M_s-R_s,
    B_(3,s)(2)=R_s-V_s,
    B_(3,s)(n)=2V_s/3^(n-2) for n>=3,
    mass=M_s, mean=M_s+R_s+3V_s/2.                         (CR10)

FormulaCR10 includes M_s=0 without division. Accordingly H_root is
the sum of the hinge integrals against B_(3,s) times the product of
B_(q,s_q). Its complete mean follows from CR8--CR10. For integer h,

    H_root=complete_first_moment-h total_mass
           +sum_(m<h)(h-m) weight_of_product_m.            (CR11)

Only the subthreshold atoms are finite. The first moment retains every
infinite geometric tail; CR11 is not a height truncation.

## 5. Root versus leaf bounds, and the two shape properties

For fixed s, put W=product_q N_q and integrate against product_q B_q.
Define the nonnegative coefficients

    A0_s=integral(W-h)_+,
    A1_s=integral[(2W-h)_+-(W-h)_+],
    A2_s=sum_(j>=2)3^(2-j)
            integral[((j+1)W-h)_+-(jW-h)_+].

The last sum converges because every increment is at most W. Tail
summation gives

    H_root=sum_s(M_s A0_s+R_s A1_s+V_s A2_s).              (CR12)

Separating each ternary leaf first would replace R_s,V_s by M_s.
Its bound H_leaf therefore satisfies the universal identity

    H_leaf-H_root
      =sum_s[(M_s-R_s)A1_s+(M_s-V_s)A2_s]>=0.              (CR13)

At fixed pi, M_s is linear in u, and R_s,V_s are maxima of linear
forms. The coefficients in CR12 are nonnegative, so H_root is convex
in u. At fixed u, each unnormalized B_q in CR8--CR9 is affine in its
whole local probability block; hence H_root is affine in each such
block on the stated fixed live cell. The existing L is block-concave
and K_u block-convex, so CR7 retains block-concavity for one common
fixed kernel. Passing the product vertices with that same kernel is
sufficient throughout that cell. These arguments do not permit unrelated
kernels at vertices or interpolation across a live/dead change or a
previously unaccounted saturation breakpoint.

## 6. Conditioning need not improve the inherited full hinge

Take one prime q, Haar, C_q=1, each first digit as its own singleton
colour, u=1 throughout, and h=1. The unit is always present. Every
complete query therefore has full hinge

    sum_(e>=1)q^-e=1/(q-1).

In each conditioned singleton, CR2 gives t(e)=q^(1-e). Its complete
hinge is q/(q-1); summing with cell weights1/q still gives q/(q-1).
Every cell was allowed to align its own query root. This proves that
the valid conditional bound need not dominate the full-source bound.
It is a method-loss example on an actual source, not a covering example.

The same loss occurs with the inherited constant C_q=(q-1)/(q-2).
For this one-prime Haar example the full cap comparator has h1 hinge
C_q/(q-1), whereas the separated singleton bound is
1+C_q/(q-1): its depth1 tail saturates at1 and its remaining tails sum
to C_q/(q-1). Thus the phenomenon does not depend on choosing the
sharper Haar constant1.

Both bounds may be retained and their minimum used at a specified point.
That minimum need not have the block-convexity required by a vertex
argument. A uniform certificate must instead justify a fixed choice,
fixed convex combination, or its own regionwise proof.

## 7. The fixed phase31/C threshold diagnostic

Use exactly Report827's rational table and its C point:
pi5=(4/15,4/15,7/15), and pi_q(0)=C_q/q at each of
q=7,11,13,17,19,23. This is a boundary point of the closed source
domain; no exact finite pure-family realization of that point is claimed.
The candidate has106 positive retained entries and38 active colour patterns.
Its complete head floor, retained moment and tail debit are unchanged.

| Quantity | Decimal display of an exact rational |
|---|---:|
| Inherited full-source H16 | 0.2927768847683014 |
| Conditional root H16 | 1.1950722248591517 |
| Conditional leaf H16 | 2.3934905335527117 |
| Conditional root G16 | -1.08885983496497 |
| Largest G at integer h=0,...,27 | -0.6510065799648083, at27 |
| Upper bound on closed interval0<=h<=28 | -0.6330689608207071, at28 |

The auxiliary loads are integer-valued, so H_root and G_h are affine
between successive integers. Computing the complete first moment and
all product atoms below28 therefore certifies the entire real interval
0<=h<28. The negative value at28 is included only as an upper endpoint
for its final open interval; it is not an admissible attained maximum.
Every threshold in the original contract fails for this fixed candidate.
The supremum for the real contract is the displayed limit as h approaches
28 from below, and it is not attained. The h27 entry is only the largest
value on the permitted integer grid.
This conclusion neither optimizes u nor excludes another retained source.

## 8. Standalone consumer and explicit dependencies

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/conditional_root_hinge.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/conditional_root_hinge_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/conditional_root_hinge.json)
use only the Python standard library. They consume the adjacent827
certificate and result with respective SHA-256 values

    17557f86d60a40310275025219d893e28ba103b5f099cf53886a8eb8ef970aca
    1e76928fa5e63ca221913ad6cdd7ba0db4a54ab093a3a2c26086e1e08b1710e5

All mathematical fields of that candidate are also bound by a canonical
JSON digest. The828 consumer checks the same probability point, inherited
floor, moment and tail identities, then computes its new full mean,
subthreshold atoms and 29 integer endpoint values. It does not rerun827's
complete head/moment inventory or copy its candidate into a second source.

Small controls on the actual period675 include four complete layouts
whose phases vary across cofactors, fractional five-leaf retention, the
root/leaf identity, retained-table convexity and fixed-live-cell block
affineness. Finite controls support the implementation; CR1--CR13 supply
the unbounded ordinary argument.

The consumer completes4991 exact arithmetic checks. Normal and optimized
verification pass, including a relocated default run and byte-identical
regeneration. Optimized execution rejects ten altered inputs covering the
survivor denominator, threshold endpoint, root partition, source point,
mathematical-field binding, upstream retained table, inherited floor,
computed hinge, omitted atom and duplicate JSON key. An independently
implemented calculation passes4480 checks and matches all29 hinge/gate
values, both complete means, all27 low atoms, all38 active-cell rows and
the inherited source quantities in435 exact comparisons. These checks
do not add a Lean proof or an all-kernel obstruction.

Normal execution verifies the retained result without rewriting it:

```sh
python3 -I -S -B conditional_root_hinge.py
```

`--certificate`, `--source-certificate`, `--source-result` and `--result`
accept explicit paths. `--write-result PATH` regenerates the result.
No working-directory search, optional package, solver or external service
is needed. Exact rational values decide every sign; decimals are displays.
