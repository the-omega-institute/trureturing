[Index](../../marked_head_profile.md) · [Common raw source](209-the-selected-indicators-share-one-raw-source.md) · [Complete extra deletions](../109-the-mean-and-all-hinges-share-one-original-test.md) · [All-selected policy](211-all-four-selected-labels-can-be-retained-above-the-first-hinge.md) · [Complete survival consumer](214-the-all-selected-policy-improves-survival-and-linear-costs.md)

# The survivor and extra deletions share the complete head

The complete comparison is

    K<=619937409355809660861838141342732760903504048694361/1503089929211069119080830448406185843896918427120
      =412.441995191330892261512732191790321881295... .

It improves214 by0.389175199770910214621038093315231318896221..., keeping the full
214 denominator. The face comparison remains9.44199519133089226151273219179032188129484...
above403. This is a statement about the two full saturated faces,
not the complete global comparison.

The two complete heavy-cost tests can retain the actual survivor measure
and two complete extra forbidden-deletion measures inside the same LP
as the original raw source. The resulting interface constrains where
survival mass can be placed, while keeping every original selected
residue independent. It refines the density bound mu<=w*Lambda used
in209/211.

The domain is both complete actual saturated K faces, with r=rho=0,
raw mass1/4 and survivor mass53/360. All conclusions are ordinary
source inequalities supported by exact rational certificates. No
claim of an actual common optimizer, actual-family attainment, Lean
verification, an off-face extension or unrestricted Erdos7 resolution
is made.

## 1. Three measures belong to the same source

Use the original25 rectangles indexed by ternary cell c and first-five
slot s. The four selected test events retain original labels25,27,75,81.
For their membership mask M, define

    x_(c,s,M)=Lambda(rectangle(c,s) intersect mask M),
    y_(c,s,M)=mu(rectangle(c,s) intersect mask M).

All400 x variables and25 independent residue-projection mixture
variables keep exactly209's original containing constraints. The
400 new y variables satisfy

    0<=y_(c,s,M)<=w_(c,s)*x_(c,s,M),
    sum y=53/360, sum x=1/4.                         (RD1)

The four selected survivor caps, proved on the whole face in75, give

    sum_(M contains j) y_(c,s,M)<=c_j,
    (c_25,c_27,c_75,c_81)=(2/125,7/270,4/375,7/810).  (RD2)

These are constraints on one measure mu. They are not four independent
choices of survivor mass. Original residues embed by their own point
masses in the four independent projection simplexes, exactly as in209.

The density w has already subtracted only the four complete forbidden
cofactor families3,9,5,15. At saturation the actual deleted measure
equals the full virtual deleted measure. As75/109 prove, the following
two collections have distinct original cofactors from these four and
from each other:

- pure3^a, a>=3, at every positive seven depth;
- 5^b and3*5^b, b>=2, at every positive seven depth.

Let e3_(c,s) and e5_(c,s) be their projected deletion masses in each
rectangle. They need not be supported on disjoint old-coordinate
rectangles. Equality of the actual and virtual deleted measures,
not an assumption about projected disjointness, gives

    e3_(c,s)+e5_(c,s)
      <=sum_M[w_(c,s)*x_(c,s,M)-y_(c,s,M)].         (RD3)

All these variables are nonnegative. No additional independent copy
of the raw source or of the residual is introduced.

## 2. The complete deletions impose exact row and column constraints

Let

    q=(0,1/5,1/5,3/20,1/5),
    eta=(1/18,1/9,1/9,1/9,1/9), ROOT=(0,0,1,1,1).

75's complete pure-three deletion is supported on root0, with exact
five-coordinate marginal q/90. Its forbidden27 subfamily lies in
cell1 and has marginal q/135. Hence

    e3_(c,s)=0 for c>=2,
    e3_(0,s)+e3_(1,s)=q_s/90,
    e3_(1,s)>=q_s/135.                              (RD4)

This does not require every deeper pure-three forbidden label to
lie in cell1. The lower bound uses only the forced27 subfamily.

109's complete deep-five deletion has ternary marginal
[eta(T)+eta(T intersect root1)]/100. Thus

    sum_s e5_(c,s)=eta_c*(1+1_(c>=2))/100.         (RD5)

The denominator100 includes exactly b>=2 and every positive seven
depth. The already subtracted b=1 families remain excluded.
Together(RD3)--(RD5) imply109's original mean credit, but also
constrain how deletions can interact with every higher hinge. There
is no separate subtraction of the mean credit from the new LP value.

This containing LP has875 nonnegative variables,581 inequalities
and16 equalities:400 raw,400 survivor,25 projection-mixture and50
extra-deletion variables. The extra measures are aggregated only
over rectangles; no unsupported selected-mask constraints on them
are imposed. Forgetting their finer geometry is an enlargement of
the actual feasible set.

## 3. Retain the survivor inside each hinge

Keep211's head B=1+I3+I9+I5+I15+I45 and its policy

    v_1=B, v_t=B+|M| for2<=t<=8.

Retain204's complete two-depth seven bridge g_t, with independent
21,35,63,105,147,245 projections and every unit7^e. For a nonnegative
coefficient vector a_t the new common-measure objective is

    sum_(c,s,M) sum_t a_t*
      [y_(c,s,M)*(v_t-t)_+ +x_(c,s,M)*g_t(v_t)].  (RD6)

The old hinge uses mu itself. The seven increment still uses the
same raw source Lambda. This separation follows directly from the
original pointwise bridge before the old hinge was enlarged using
mu<=w*Lambda. No estimate subtracts a deletion credit from the seven
increment or from a separately paid tail.

The complete omitted cap sum is

    T=a1*(163/1800+2669/88200)
       +sum_(t>=2)a_t*(19/648+2669/88200).         (RD7)

Every omitted original test label remains paid in exactly the same
assigned cap as211; every retained selected label has been removed
from its corresponding cap series. Therefore a feasible dual bound
U for(RD6) proves

    integral_mu sum_t a_t*(A-t)_+<=U+T.          (RD8)

For an original cost f, add f(1)*53/360 after checking its exact
hinge expansion and complete eventual affine tail. The consumer
checks both heavy functions on all positive integer loads through
their finite transitions and their full affine continuation.

## 4. A rational certificate bounds every independent configuration

Write the containing system as Ax<=b, Ex=d, x>=0. Each stored dual
has nonnegative inequality prices u and unrestricted equality prices
v, and satisfies every one of875 rational column inequalities

    A^T u+E^T v>=objective.

Its value b.u+d.v bounds(RD6) by weak duality, including constraints
with negative right sides and nonunit equality masses. Numerical
optimization proposes prices; the canonical checker uses only exact
rational arithmetic and does not require numerical optimality.

The proposal program repairs equality prices for deletion and
projection columns, then the zero-deletion and survivor-link rows,
and finally the raw cell-cap rows. The final column check, rather
than the optimizer's status, certifies each bound. Survivor-link
repairs can decrease raw-column slack; the last raw-cap repair pays
for that effect.

Each heavy scan accounts for all62,500,000 independent head and
seven-projection choices. Earlier complete two-, four-, six-projection
and matching209 bounds remain valid pruning alternatives, including
their original mean credit. Their mean credit is not transferred to
(RD8). Every pruned branch has an upper at most the final maximum;
every newly evaluated branch has a checked feasible dual.

Both source orientations and all first-beta cells follow by transporting
the whole source, survivor and deletion system together. The exact
complete cap sums justify the inherited finite-prefix and diagonal
limit arguments at arbitrary exponent heights.

## 5. Preserve the complete consumer

The consumer starts from214's entire52-cost vector and denominator.
It substitutes only the two complete heavy bounds, then applies
the existing whole-load majorants. Every other numerator improvement,
the signed actual mass, complete square, independent AP11/AP13 tests,
and full count remainder remain.

The two complete heavy bounds are

    cost0<=50840091137478544987478150943049729867/8989204096414656907392600000000000000
      =5.65568326096368308081352690083331486314178...;
    layout=(1, 4, 2, 1, 2, 4, 2),
    projections=(1, 2, 4, 1, 2, 1, 2).

    cost16<=191539875988371705831891325475326378141/42377676454526239706279400000000000000
      =4.51982958985269881819307497699668625782052...;
    layout=(1, 3, 2, 1, 2, 3, 2),
    projections=(1, 2, 3, 1, 2, 1, 2).

The numerator is

    N=29894132520911657484902144445014487457619490077/899459402319086713567427260296000000000000000
      =33.2356662722467133217727535735332547962156... .

Each scan uses65 feasible-dual evaluations, with64 distinct new
duals. All128 stored duals are checked in every875 column. The
complete scans also evaluate1,149,263 and1,169,863 original capacity
LPs, respectively; certified pruning accounts for all remaining
containing branches. Controller tuples identify maxima of the
certified upper operators, not attainable actual covering families.

The [helper](../../frontier/transport/retained_deletion_heavy_comparison.py),
[proposal program](../../frontier/transport/propose_retained_deletion_duals.py) and
[certificate](../../certificates/source_norms/retained-transport/retained_deletion_heavy_comparison.json)
provide the complete system, exact duals, branch accounting and full
consumer.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/retained_deletion_heavy_comparison.py --check
```
