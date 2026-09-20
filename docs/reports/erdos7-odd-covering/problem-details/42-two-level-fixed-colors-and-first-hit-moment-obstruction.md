[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="two-level-fixed-colors-and-first-hit-moment-obstruction"></a>
# Two-level fixed colors require a triple incidence in the first-hit cost

One containment-reduced family of seven distinct odd original moduli admits
two positive incoming survivor laws with the same complete two-coordinate
marginals, all original-label unary and pair moments, the same fixed colors
and every resulting pair/chain zero. Both laws obey the stated full-history
conditional prefix caps. Nevertheless, their actual clipped-kernel first-hit
costs differ by exactly `1/138600`.

For this same family, a linear program on its 144 actual old CRT atoms has
the exact optimum `97/5775`. A six-price rational dual and one of the two
incoming laws attain the same value. This is a finite ordinary result with
an exact certificate. It does not give an unrestricted head estimate or an
improvement to [Chapter 40](40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md)'s independent-run model.

## 1. Original moduli, fixed colors and one physical union

Use the original `(modulus,residue)` pairs

    (3,0), (5,0), (7,0), (33,22), (99,11), (55,1), (847,484).

The complete period is `38115 = 315*121`. The current prime is `q=11`;
the full old coordinates are `Z/9Z`, `Z/5Z`, `Z/7Z`, including the second
ternary digit needed by the later-ending modulus 99. Let

    S3 = {1,2,4,5,7,8} mod 9,
    S5 = {1,2,3,4} mod 5,
    S7 = {1,2,3,4,5,6} mod 7,
    X  = S3 times S5 times S7.

All 144 points of X avoid the three earlier pure classes. Define on X

    I1 = 1{x3 = 1 mod 3},
    I4 = 1{x3 = 2 mod 9},
    A = I1+I4,  B = 1{x5=1},  C = 1{x7=1}.

Here `I1*I4=0`, so A is an indicator. The four current-ending classes are
exactly the following fixed rectangles:

| Original modulus | Old condition | Literal current prefix |
| --- | --- | --- |
| 33 | I1=1 | 0 mod 11 |
| 99 | I4=1 | 0 mod 11 |
| 55 | B=1 | 1 mod 11 |
| 847 | C=1 | 0 mod 121 |

In particular the fixed current color of the cofactor-3/cofactor-9 pair is
the same, and the actual old conditions are disjoint. This gives a
nonvacuous comparable-cofactor zero. The other comparable original pairs
are the pure classes 3 with 33 and 99, 5 with 55, and 7 with 847; all are
disjoint. Thus no original class contains another, and literal containment
reduction retains all seven labels. No modulus is replaced or duplicated.

The current depth-two prefix belongs to root zero. Consequently the actual
uniform forbidden-fibre proportion, with its overlap counted only once, is

    alpha = (A+B)/11 + (1-A)*C/121.                       (TF1)

Take the actual full-Haar clipped kernel at threshold `delta=1/11` as in
Chapter 08. Its conditional forbidden mass is

    b(x) = (alpha(x)-1/11)_+ / (10/11)
         = A*B/10 + (1-A)*B*C/110.                       (TF2)

The equality follows by checking the four values of (A,B), leaving C as an
indicator. Since every incoming point avoids all earlier original classes,
the expectation of b is also the true first-hit mass at this stage. The
current kernel is normalized even at zero loads; its point mass is at most
`1/110` on `Z/121Z`.

The additional information in (TF2) is the mass of the same-source triple
event `A^c intersect B intersect C`. For this fixed local union and threshold,
retaining that event together with `E[A B]` suffices for the exact charge.
This is not a sufficient state claim for arbitrary future updates.

## 2. Two genuine capped incoming laws with identical pair observations

Let `nu=nu3 times nu5 times nu7` be uniform on X; every atom has mass 1/144.
Let h3 be +1 on ternary root 1 and -1 on ternary root 2. For p=5,7 let hp
be +1 at residue 1, -1 at residue 2, and zero at the remaining survivor
residues. Each hp has zero mean under its own nu-coordinate. Put

    mu_plus(x)  = nu(x) [1+(1/35) h3(x3)h5(x5)h7(x7)],
    mu_minus(x) = nu(x) [1-(1/35) h3(x3)h5(x5)h7(x7)].   (TF3)

Both laws are strictly positive and normalized. Summing over any coordinate
annihilates the perturbation. Thus every full two-coordinate marginal of
both laws equals that of nu, not just the marginals of the four indicators.

The laws have an explicit full-history sequential realization. Draw the
complete ternary coordinate by nu3, then the five-coordinate by nu5, then
use

    K7(c | a,b) = [1 +/- h3(a)h5(b)h7(c)/35]/6,
                 c in S7.                              (TF4)

The kernel is normalized because the mean of h7 is zero. Its cap is
`(1+1/35)/6 = 6/35`. In the original pure-survivor cap notation
`c_p=(p-1)/(p-2)`, the entire preceding chain satisfies

    ternary depth e=1,2: prefix mass <= 2*3^(-e),
    five given the full ternary coordinate: 1/4 <= 4/15,
    seven given the entire previous history: K7 <= 6/35.

These are pointwise conditional bounds, not products of separate marginal
caps. The laws are realizable by the displayed normalized history-dependent
kernels. They are not asserted to be the outputs of an earlier prescribed
BBMST policy for the three pure classes; a theorem requiring that additional
policy identity is outside this counterexample.

Every current original old condition depends on one coordinate. Therefore
all original old-label unary and pair moments are identical under mu_plus
and mu_minus, including `E[I1 I4]=0`. Fixed labels also make every actual
chain zero identical pointwise. Moreover, under the corresponding joint law
`mu_plus times Haar_121` or `mu_minus times Haar_121`, every full original AP
unary and pair intersection probability is identical: the current-prefix
intersection is a fixed numerical Haar factor multiplying an old unary/pair
moment. This assertion concerns the incoming Haar extension, before the
nonlinear clipped kernel is applied.

On the other hand,

    E[A B] = 1/6,  E[B C] = 1/24,
    E_nu[A B C] = 1/36,
    E_mu_plus[A B C]  = 71/2520,
    E_mu_minus[A B C] = 23/840.                         (TF5)

Indeed `E_nu3[A h3]=1/3`, `E_nu5[B h5]=1/4`, and
`E_nu7[C h7]=1/6`; the signed triple correction is 1/2520. Substitution in
(TF2) gives

    E_mu_plus[b]  = 2327/138600,
    E_mu_minus[b] = 97/5775 = 2328/138600.              (TF6)

Thus those complete pair observations and structural zeros do not determine
the actual first-hit charge. An upper bound based on them can remain sound
by optimizing over the missing triple, but it cannot silently substitute
its value from a different joint law. The counterexample does not say that
all pair-based upper bounds are useless or that no uniform bound exists.

## 3. A realizable finite LP and its exact dual

Use variables `z_(a,b,c)>=0` on the actual X, not on unconstrained abstract
event patterns. Impose all three pair-coordinate marginals of nu:

    sum_c z_(a,b,c) = 1/24    for each a in S3, b in S5,
    sum_b z_(a,b,c) = 1/36    for each a in S3, c in S7,
    sum_a z_(a,b,c) = 1/24    for each b in S5, c in S7,

and the full-history atom cap

    z_(a,b,c) <= 1/140.                                (TF7)

Since the (a,b)-row mass is 1/24, (TF7) is exactly the conditional cap
`24 z_(a,b,c)<=6/35`. Every feasible table is an actual law on this fixed
original CRT carrier and has a sequential realization with the same caps
as above. Fixed colors, forbidden union and all structural zeros stay
inside the objective b of (TF2).

For every feasible table,

    E_z[b] = (1/10) E_z[A B]
             +(1/110) sum_(a not in A,b=1,c=1) z_(a,b,c)
           <= 1/60 + 2/(140*110)
            = 97/5775.                                 (TF8)

This is a sparse exact LP dual: put price 1/10 on the four (a,b)-marginal
equalities with `a in {1,2,4,7}, b=1`, and price 1/110 on the two atom-cap
inequalities with `a in {5,8}, b=c=1`. All other prices are zero. The dual
coefficient equals the objective coefficient at all 144 atoms, so there
are no unchecked columns or tolerances. The priced old CRT atoms are 71
and 176 modulo 315.

At both cap-priced atoms, mu_minus has density factor 36/35 and mass
1/140. It has all required pair marginals, so it attains (TF8). The exact
optimum is therefore 97/5775. In this configuration the conditional cap
controls the triple directly:

    E[(1-A) B C] <= (6/35) E[(1-A) B] = 1/70.

The mask `(1-A)B` is measurable before the seven-coordinate is exposed;
this is why the same full-history cap may be applied. It is not a clipping
operation on an independently compressed count.

For a precise comparator, remove only the cap (TF7) while keeping all pair
marginals and actual atoms. Then `E[b]<=1/60+(1/24)/110=3/176` since the
triple `E[A B C]` is nonnegative, and this is sharp. An attaining table is
specified by its c=1 masses, for each fixed (a,b):

| A(a) | B(b) | z_(a,b,1) |
| --- | --- | --- |
| 1 | 1 | 0 |
| 0 | 1 | 1/48 |
| 1 | 0 | 1/108 |
| 0 | 0 | 1/432 |

Distribute the remaining row mass `1/24-z_(a,b,1)` uniformly over the five
other c-values. The three pair marginals follow by addition. This table
violates (TF7) and is used only for the uncapped comparison. Retaining the
actual cap improves this particular LP optimum by exactly `23/92400`.

## 4. Actual-union saving and scope

The literal additive row, before accounting for the depth-two prefix
already covered by root zero, is

    alpha_add = (A+B)/11 + C/121.

Its clipped charge exceeds (TF2) pointwise by `A C/110`; under either
displayed capped law the expectation is `1/990`. This saving is caused by
the actual nested colors in the fixed family. It is not a uniform rebate
for all label families: if the depth-two color belongs to a different
root, that overlap disappears. It cannot be subtracted from Chapter 40's
different independent-run ledger without a separate proved comparison.

The existing [Chapter 08](08-arbitrary-head-transfer-by-the-joint-load-invariant.md#transfer-retaining-the-actual-forbidden-fibre-geometry) already supplies the actual-union clipped-kernel
formula and generic second-moment/Gram interfaces. [Chapter 16](16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#congruence-and-complete-layout-specialization) supplies
containment reduction and comparable-modulus conflict. [Profile 340](../profile-notes/321-384/340-whole-cover-completion-constrains-original-prefix-loads.md) keeps
whole-cover future-prefix completion and complete tree-certificate
intersections; [profile 363](../profile-notes/321-384/363-common-source-antichain-capacity.md) uses one actual active-antichain law and warns
that marginal feasibility need not imply an AP realization. The present
finite construction uses those boundaries: it provides a specific sharp
two-depth cap-aware objective and an actual same-family nonidentifiability
witness for pair observations. No new general antichain theorem, generic
projection identity, literature priority or Lean declaration is claimed.

The missing unrestricted input remains a quantitative bound for the
relevant higher intersections under the one specified incoming/killed law,
uniform over original prime powers, all cofactor supports and the required
future continuation. This example demonstrates one triple that must be
represented or validly bounded; it does not establish how many observations
suffice for the unrestricted task.

## 5. Reproduction

The self-contained [producer](../frontier/cover-geometry/two_level_colored_first_hit.py)
and deterministic [JSON](../frontier/cover-geometry/two_level_colored_first_hit.json)
use Python 3.9 or later and only its standard library. From the repository root run

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_level_colored_first_hit.py --output docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_level_colored_first_hit.json
```

The producer checks the literal original residues on all 144 old fibres
and 17,424 old/current points, all five comparable original pairs,
the complete pair marginals, 28 old and 28 full-AP unary/pair moments,
the full-history caps, normalized current kernels, exact hinge identities,
all 144 dual columns and primal attainment. Its JSON embeds the mathematical
input hash and producer source hash. It uses explicit exceptions, exact
rational arithmetic and no optimizer. The ordinary proof above supplies
the mathematical interpretation of these finite checks.

Program and output paths may instead be explicit absolute paths; no external
data or current-working-directory lookup is used. Isolated optimized execution
from `/` and a program/output path containing spaces produced byte-identical
JSON on macOS with Python 3.14.3. Other platforms and Python versions were not
executed in this check.
