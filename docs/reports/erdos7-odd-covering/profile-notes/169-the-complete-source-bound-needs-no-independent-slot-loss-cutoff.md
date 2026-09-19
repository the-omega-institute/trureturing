[Index](../marked_head_profile.md) · [Actual packing gaps](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Fixed-support heavy margins](162-fixed-supports-preserve-both-heavy-margins-on-the-source-slab.md) · [Complete comparison](166-the-complete-local-source-domain-crosses-the-outer-strip.md)

# The complete source bound needs no independent slot-loss cutoff

For both actual K orientations, the complete comparison satisfies

    sigma<=1/27, rho<=1/1000
        ==> K<=500.7256739756091971...<509.          (FR1)

There is no additional hypothesis r<=1/520. The globally valid
r<=5rho supplies r<=1/200 throughout this rectangle. The result
retains all52 independent original tests, five original survival
objectives, the same actual carrier mass, and every infinite tail.
It is an ordinary local continuous-source theorem with an exact
rational certificate, not a global K bound, a Lean theorem or a
solution of unrestricted Erdos7.

## 1. Actual packing gaps remain positive on the larger slot domain

Put delta=1/27 and R=1/1000. Write the actual source losses as

    Delta=p+a+b=(uz+ua+ub)/4.

The joint budget153 gives Delta<=delta/[4(1-delta)]=1/104.
The exposed support156 applies to this same price vector
(1/4,1/4,1/4,0,0,0), and gives the stronger bound

    Delta<=D:=3delta/[4(3-2delta)]=3/316.           (FR2)

This is a bound on the actual source losses, not an inference from
a small observed change in one source coordinate. The wider1/104
bound suffices for the fixed-support slab and cap enlargement below.
Concentration also gives

    h>=1/2, h1>=161/486, eta_L>=53/486,
    h1-h0>=1/6-delta/9, h<=122/243,
    z<=3/4+delta/4=41/54<4/5.                     (FR3)

The three source budgets are at least1/4-3delta/4=2/9>1/20.
Thus85/117's first-label argument forces source labels5,15,45,
with15 on root1 and45 in a root1 cell L, and forces their slots
P,A,B to be distinct. This argument precedes the slot-loss bound.
For r<=5R=1/200, all five general gap guards of91/117 are positive:

| Guard | Uniform lower bound |
| --- | ---: |
| h/5-r |19/200|
| h1/5-r |2977/48600|
| eta_L/5-r |817/48600|
| h1(1/10-Delta)-2r |76721/3839400|
| (h1-h0)/5-r |1337/48600|

Hence a common actual wrong/absent-slot gap is

    G=817/48600>0.                                (FR4)

In particular H differs from P,A,B, the wrong-root15 alternative
is included, and all divisions in the marked packing proof are
valid. The original85/91 numerical cutoff was one sufficient way
to make these general guards positive. Equations(FR2)--(FR4)
prove them directly on the new domain, including its endpoint.
No old small-r theorem is simply invoked outside its hypothesis.

## 2. Reuse the r=0 heavy floors and reprove their positive-r price

The original162 fixed-support slab has Delta<=1/18 and z<=4/5,
with the forced first-beta condition, all deficit and late factors,
and every actual carrier mixture. Equations(FR2)--(FR3) put the
new sources inside this slab. Its existing r=0 floors remain

    m0 =1193878489939499612/259995953549870913375,
    m16=1088704788427803234124/300295326350100904948125.

For a fixed original branch let vmax be its largest derivative.
The marked dual coefficients stay nonnegative because
3/5-18(13/1215)=11/27>0. The general marker proof91 therefore
holds with price at most

    max(1,hbar/(5G))*vmax,
    hbar=122/243, hbar/(5G)=4880/817<65/9.         (FR5)

Keep162's fixed source supports, chosen branch coordinate and
selected deep shift. Only the non-H Q caps and the H correction
change with r. The root0 pre-cap increases by at most r/h and the
root1 pre-cap by at most r/h1. Their weighted payment is at most

    vmax*r*(h0/h+1)<=(13/9)*vmax*r.               (FR6)

Here h>=1/2 and h0<=2/9 hold on the whole slab. The negative
coefficient correction can only reduce this payment. The H
correction loses at most18(13/1215)*vmax*r, which is smaller.
No first-label residue or carrier is identified with another.

Use the same actual common residual as91:

    epsilon=rho-(r+r1)/5>=0,
    Di=(13/9)*max_branch vmax,
    Pi=(65/9)*max_branch vmax.

Since Pi>=5Di and Pi dominates(FR5),

    Di*r+Pi*epsilon
        <=Pi*r/5+Pi*(rho-(r+r1)/5)<=Pi*rho.       (FR7)

Thus both heavy costs obey the absolute bounds

    integral f_i <= C_i*S-m_i+P_i*rho,
    P0 =12491905/792792,
    P16=18197065/1459458.                         (FR8)

These replace the original heavy bounds. Their m_i are not added
as extra gains on top of an already optimized source margin.
The positive-r transport is proved here; the162 r=0 scan is reused
without extrapolating its former positive-r wrapper.

## 3. Enlarge the actual Q caps and reconstruct the complete heads

The uniform source operator134 remains valid after replacing its
rbar, Q-cap increments and common packing gap. With t=1/26 use

    rbar=1/200,
    v0=min(1/20,t/4+2rbar)=51/2600,
    v1=min(1/10,t/4+rbar/(161/486))=10343/418600.   (FR9)

These follow from the general cap formulas r/h<=2rbar and
r/h1<=rbar/h1min. The exact P/A/B exclusions remain. The three
group budgets use157's unchanged shared-source increments

    ((3+delta)*t/72, delta/36, t/12).

The source ratios, mean prices and complete tail coefficients
depend on delta, not on the old artificial r cutoff. Their domain
proofs reduce to positivity throughout[0,delta] of

    1-4x, 6-49x-70x^2, 42-35x^2,
    3x^2-23x+3, 2-7x-x^2.                        (FR10)

Each is decreasing and positive at delta=1/27. The root/cell and
first-label conditions used152 for shallow indicators and165 for
the joint pure-five block are consequently retained. Their actual
finite transport is evaluated using(FR4) and(FR9).

The new common defect simplex has the three vertices

    (q5,q15)=(0,0), (R/G,0), (0,R/G),
    R/G=243/4085<1/5.                            (FR11)

The corresponding residual is R-G(q5+q15). Every cost keeps that
one shared residual; no separate maximization grants additional
copies of its budget. The fresh original-head calculation uses
all12500 original layouts and ten positive-seven alternatives at
all three vertices, for each of26 independent objectives:
five denominator costs, H2,11 mean costs and9 quadratic costs.
It evaluates9,750,000 original heads and includes312 independent
exact rational LP comparisons. The complete selected-tail support
is rebuilt at the new parameters. No old head maximum is reused
as if its source domain were unchanged.

The other28 simple costs, both retained raw81 controllers, both
heavy costs(FR8), and the complete square use the same parameters.
The improved pure-five contribution replaces exactly its original
positive block. The resulting complete values include

    H1<=53180958548918201/98667384385701600,
    Q<=15912444113680496293/2960021531571048000.    (FR12)

## 4. Keep the actual S coefficient to close the complete comparison

Set A=53/360 and cE=1-1/614922 as in166. Its unchanged signed
assembly gives a numerator endpoint N, denominator endpoint d
and coefficient M of S-A. The new exact calculation gives

    N=36.23018387804461...,
    d=0.07561636093255815...>0,
    M=68.84786878598906... .                      (FR13)

For every actual S>=A, the same52 numerator and original survival
denominator satisfy the signed comparison at

    K=C0+N/d
     =12845377191256541150604967537085275240035849379390875157
       /25653522195632914867478663012682640991194533828000000
     =500.7256739756091971... .                   (FR14)

The remaining S coefficient is

    (K-C0)cE-M=410.2828975308059...>0.             (FR15)

Thus no replacement S=A has discarded an unfavorable mass term.
The helper verifies that the original indices are exactly0,...,51,
each included once, and that the denominator remains positive.
The margin below509 is8.2743260243908... .

For a global consumer, the useful consequence is precise: when
sigma<=1/27 but the source lies outside(FR1), necessarily
rho>1/1000. The old alternative r>1/520 can no longer force the
weaker residual threshold1/2600. Other source regions still need
their own complete bounds and a global splice.

The [helper](../frontier/full_slot_radius_source_comparison.py),
[complete certificate](../certificates/source_norms/full_slot_radius_source_comparison.json)
and [new original heads](../certificates/source_norms/full_slot_radius_source_heads.json)
retain the exact inputs, source guards,52-cost inventory and full
tail supports. Replay the canonical calculation with

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/full_slot_radius_source_comparison.py --check
```

Adding `--scan` independently recomputes every original head.
Neither check is Lean kernel verification.
