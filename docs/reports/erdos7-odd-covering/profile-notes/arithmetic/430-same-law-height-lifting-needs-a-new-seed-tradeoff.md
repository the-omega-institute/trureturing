[Index](../../marked_head_profile.md) · [Height-two common law](429-phase-conflict-cap-flow-closes-the-height-two-bound.md) · [Height lifting](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md) · [Fixed components](427-shared-row-cap-mixtures-break-the-six-barrier.md)

# Same-law height lifting needs a new seed tradeoff

Report 429 supplies `Gamma_(1,2)<=46/9`, and with report 427 closes
`Gamma_(1,K)<=2t_K` for the stated first-five-layer source class.
The existing height-lifting inequalities do not turn these supplied
constants into the all-height target nine. Even an optimistic calculation
that pays no seven-adic lifting cost gives a bound exceeding nine.
The two-constant smoothing formula identifies a precise joint tradeoff
that would suffice, but the seven fixed components of report 427 already
refute that stronger tradeoff for their convex mixtures.

These are limitations of specified certificate formulas and fixed-law
choices. They are not lower bounds of nine on actual survivor moments,
not counterexamples to a theorem allowing free choice of the source law,
and not a resolution of unrestricted Erdős #7. The arguments and exact
checker below are ordinary mathematics, not Lean certification.

## 1. The support premise needed before using a seed

Chapter 09 requires a probability on the actual survivors of every
original class dividing the finite base modulus. The whole family must
still have distinct original nonunit moduli, with all omitted classes
charged by the extension. Its conclusion conditions one extended measure
on avoiding those additional actual classes.

Report 429 instead starts with an admissible source in
`{1,2,3,4} x Z/7^K`. Its theorem constructs one supported probability
for the two-prime layout game. When this source is a projection of a
larger actual residual, its law is not automatically a probability on
survivors of the full original head. Choosing witnesses in the other
coordinates gives no bound on the missing mixed-divisor test costs.
For a general abstract source, the complement also need not have a
presentation by distinct original congruence labels to which Chapter 09
applies.

All lifting calculations below therefore grant the separate extraction
premise of Chapter 09 for a two-prime family. Establishing that premise
for the intended actual family and controlling its other prime
coordinates remain additional obligations. Passing the inequalities
below would not by itself supply a full-prime head seed.

## 2. An unavoidable cost in the one-constant smoothing formula

Use old heights `(H_5,H_7)=(1,K)` and coarse heights `(h_5,h_7)=(1,h)`,
where `1<=h<=K`. Thus the five-coordinate smoothing width is zero.
For the all-height majorants in Chapter 09, the five factor is

    B_5 = 1 + 2(1/4)/2 + (3/8)/4 = 43/32.                 (HL1)

Write `B_7(infinity)` and `B_7(K-h)` for its seven-coordinate factors.
The extra square coefficient is

    E = (43/32) B_7(infinity) - B_7(K-h) >= 11/32,          (HL2)

because `B_7(infinity)>=B_7(K-h)>=1`. For a supplied constant `C>=4`,
the singleton-five term in the deletion majorant is

    lambda_5(C)
      = (1/4) min(sqrt(C)/2, C/4, (C-1)/3)
      = sqrt(C)/8.                                        (HL3)

Both comparisons follow by writing `sqrt(C)>=2`. Every remaining
subset contribution to `lambda` is nonnegative. If the full deletion
majorant is below one, monotonicity of Chapter 09's quotient therefore
bounds its **reported upper expression from below** by

    U_5(C) = [(43/32)C - sqrt(C)/8]/[1-sqrt(C)/8].           (HL4)

If `C>=64`, already HL3 is at least one and this certificate has no
positive denominator. On `4<=C<64`, HL4 increases with C: the quotient
increases separately with its square numerator and deletion parameter.
This lower bound on an upper expression is not a lower bound on any
actual `Gamma`.

At the new height-two input,

    C=46/9,
    U_5(C)=(989-6sqrt(46))/(144-6sqrt(46))
           in (9.179581394887060,9.179581394887061).          (HL5)

The strict comparison to nine is exact. It is equivalent to
`sqrt(46/9)>307/144`, and

    46/9-(307/144)^2=11735/20736>0.                         (HL6)

Thus no seven-coordinate smoothing width repairs the one-constant
formula with this C. The larger supplied constants at K three and above
also fail the same comparison. Report 427's finite certificate values
are monotone in its three height-dependent nonnegative inputs; in
particular they are at least `146409/26585>46/9` for `K>=3`.

For comparison, the old root input `C=4,K=1` has only `h=1`. The complete
two-prime majorants are `E=185/288`, `lambda=17/40`, and give exactly

    [4(1+185/288)-17/40]/[1-17/40]=2212/207>9.             (HL7)

For the height-two input the two allowed coarse seven heights give

| Coarse seven height h | Extra coefficient E | S1 upper expression |
| --- | --- | --- |
| 1 | `935/2016` | `(13.522755379921600,13.522755379921601)` |
| 2 | `341/648` | `(11.848910545578042,11.848910545578043)` |

These statements concern the uniform all-height geometric majorants.
A particular finite extension has smaller sums and is not excluded by
this calculation.

Solving `U_5(C)<=9` in the relevant regime `C>=4` gives the necessary
seed threshold

    C <= C_* = 16(sqrt(790)-4)^2/1849
      in (5.028832803367155,5.028832803367156).              (HL8)

This is necessary only for this optimistic certificate, not sufficient:
it has discarded the seven-coordinate costs and assumed the support
premise of section 1.

## 3. The two-constant formula asks for a joint tradeoff

At old heights `(1,2)`, smooth to coarse heights `(1,1)`. Suppose the
**same** probability has bounds `Gamma_(1,2)<=C_H` and
`Gamma_(1,1)<=C_h`, with `1<=C_h<=min(4,C_H)`. Then

    E=935/2016,
    lambda(C_h)=(C_h-1)(1/12+1/18+1/360)
               =17(C_h-1)/120.                            (HL9)

For each subset, the `(C_h-1)/(D^2-1)` choice is the minimum throughout
this regime. Chapter 09, S2, certifies the target nine precisely when

    C_H + (16099/10080) C_h <= 152/15.                     (HL10)

Indeed, multiplying its positive denominator gives
`C_H+E C_h+8lambda(C_h)<=9`, which is HL10. With the uniform high input
`C_H=46/9`, it requires

    C_h <= 50624/16099 = 3.1445431393... .                  (HL11)

Report 390's separately selected root probability with `Gamma<=4`
does not supply HL11 on the probability selected by report 429.
The omitted regime cannot improve the certificate: `lambda(C_h)` is
nondecreasing, `lambda(4)=17/40`, and `C_H>=C_h`. For `C_h>=4`, a
positive-denominator S2 expression is therefore at least its value at
`C_H=C_h=4`, namely `13684/1449=9+643/1449`; if `lambda>=1`, S2 does
not apply. Thus a successful S2 seed must have `C_h<4`.
Moreover HL11 is not a universal root bound for the source class.
Take three rows times a complete five-ary seven-tree. Its root projection
is a `3 x 5` rectangle. Averaging the fifteen complete root layouts
centred on that rectangle gives cost `16/5` at each point, so every
supported probability has root `Gamma>=16/5`. The exact gap is

    16/5-50624/16099=4464/80495>0.                         (HL12)

This does not refute HL10 with source-dependent costs. For example,
uniform mass on those three rows and a depth-two five-ary tree has
`C_H=18/5,C_h=16/5`; the usual joint prefix expansion and one centred
layout give those exact values, and they satisfy HL10. The required
information is their joint behavior on one actual source and one law.

## 4. The existing seven fixed components refute the stronger target

Use the seven actual laws and three equally weighted complete layouts
from report 427, JC16--JC19, retained by
[`fixed_cap_mixture_boundary.py`](../../frontier/cover-geometry/fixed_cap_mixture_boundary.py).
For each high layout use its first four original labels as a coarse
layout. This is a legitimate distribution on pairs of independently
allowed high and coarse layouts; imposing this relation is permitted
for a lower witness, not for an upper proof over all layout pairs.

Direct evaluation of the original predicates gives

| Fixed component | Mean high cost | Mean coarse cost |
| --- | ---: | ---: |
| Full five-cap law | `26/5` | `22/5` |
| Pairs 12,13,23 | `20/3` | `5` |
| Pairs 14,24,34 | `46/9` | `4` |

Let `w=16099/10080`. Every convex mixture `nu` of these seven fixed
laws therefore obeys

    Gamma_(1,2)(nu) + w Gamma_(1,1)(nu)
       >= min_component E_theta[L_high^2+w L_coarse^2]
       = 28979/2520
       = 152/15 + 3443/2520.                              (HL13)

The same three-layout distribution is used for both costs and every
component. Linearity proves HL13 for all mixture weights. The equal
mixture of pairs 14,24,34 has actual high value `46/9` and coarse
value four, so it also attains the displayed lower bound for the
weighted game: its independent three-row and ternary-tree factors
supply the matching upper bounds at both heights.

Consequently one cannot strengthen report 429's universal statement
about **arbitrary prescribed components** to HL10 by retuning weights.
This does not exclude free selection of component laws or arbitrary
probabilities on the source. For example, all seven components can
be viewed on the full carrier `{1,2,3,4} x Z/49`; uniform mass on that
carrier has `Gamma_(1,2)=75/28` and `Gamma_(1,1)=5/2`, and satisfies
HL10. The failure concerns the prescribed component menu.

## 5. What a combined-cost computation would have to retain

A weighted cost remains linear in the probability. Report 429's
row-to-leaf-to-root integral cap network can therefore use integer
point prices

    10080 L_high^2 + 16099 L_coarse^2,
    target 102144.                                        (HL14)

Its present 1280 columns describe one high layout. An upper bound for
HL10 needs two independently chosen layouts, including independent
coarse row and phase choices. There are six labelled seven-root phases:
the high pure and mixed roots, the parents of its two depth-two phases,
and the coarse pure and mixed roots. Their equality partitions number
203. When the two high parents agree, the two leaves may agree or
not; 52 partitions have this property. Thus there are 255 joint phase
types. The five mixed row choices give `4^5` words and

    255 * 4^5 = 261120 columns.                            (HL15)

Seven roots and seven children per root realize every such type.
The 3276 full-law row quotas and ten choices per pair remain the same.
The old dual numbers are not certificates for these expanded prices;
they would need to be checked against every new column.

HL13 already refutes the desired bound for arbitrary prescribed
components, so solving that larger fixed-component certificate problem
cannot prove it. A potentially valid route must allow source-dependent
component selection or use report 400's free-source tree-rank game
with the combined cost. Neither change is supplied by the present
height-two theorem. In addition, the three-prime and full-head support
and cost obligations in section 1 remain.

## 6. Exact verification

[`common_law_height_lift_boundary.py`](../../frontier/cover-geometry/common_law_height_lift_boundary.py)
uses the standard library. It imports only the existing fixed-component
fixture generator, then independently checks every probability, row
support, whole-prefix cap, original high/coarse predicate price and
weighted lower witness. It verifies the height-lifting identities with
rational arithmetic and integer-square-root enclosures, checks the
rectangle lower witness, and regenerates the 255 joint phase types.
The complete retained fixture is not duplicated.

```sh
python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/common_law_height_lift_boundary.py --compact
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/common_law_height_lift_boundary.py --compact
```

Failures use explicit exceptions and remain active under `-O`. The
checks certify these formulas and this fixed-component obstruction;
they do not verify the missing actual-head extraction premise or an
unrestricted covering statement.
