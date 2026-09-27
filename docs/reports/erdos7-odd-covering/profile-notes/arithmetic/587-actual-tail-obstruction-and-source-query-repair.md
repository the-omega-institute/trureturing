# An actual tail obstruction and a source-norm repair

[Report586](586-joint-clipping-retains-loss-query-correlation.md)'s small-tail condition is not automatic for every admissible
actual PA source in its fixed-pure3, shallow two-phase slice. The
149-original family below has, under one explicitly fixed source nu,

    E_nu(W-16/3)_+
      =428853838918/5843456994375
      =0.0733904329801385...
      >tau_star=0.05574466163241126... .                    (AT1)

Every original numerical modulus and residue is fixed, all source
and ternary overlaps are realized together, and the source is an
actual instance of [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md). Thus AT1 is an arithmetic counterexample
to automatic satisfaction of that particular tail gate under the
given source. It does not assert that another allowed selection or
source could not satisfy the gate.

Keeping the actual source query norm instead of replacing it by B
repairs this example and gives a general all-height sufficient test:

    R_Q(nu)<1461204049288174906748586781
              /302451810663922521463738800
            =4.831196236123152... .                       (AT2)

Under the same fixed-pure3 and shallow two-phase hypotheses, AT2 needs
no additional pointwise reserve or damage-tail assumption. It is a
consumer of Report586's joint loss/query formula, not a new kernel
construction. The final continuation includes only originals
supported on `P union{23,29}`, where `P={3,5,7,11,13,17,19}`.

## 1. One explicit selected source

Write `Q=(5,7,11,13,17,19)`. At each prime cofactor q select
phases0 and1, and select no phases at other cofactors. Realize phase0
as the Q-only original `0 mod q`. Realize phase1 as an exponent-one
original with ternary phase2 and Q phase1, fixing its unique residue
modulo3q by CRT. These are12 shallow originals. Include the two pure3
originals `1 mod3` and `3 mod9`.

The actual PA source nu is the product of Haar conditioned on the
first q-digits `2,...,q-1`, with conditional higher digits still Haar.
Its q-coordinate survivor Haar mass is

    s_q=(q-2)/q.

There are no selected mixed-Q classes. The5/7 stage is the direct
product restriction; each later row has density q/(q-2) below its
existing PA cap, so all later caps are inactive. Normalizing the
actual final measure therefore gives exactly this product law. The
complete q-root2 cylinder is preserved at every higher q-height.

## 2. Fixed deep originals with cyclic ternary phases

Use the following45 distinct numerical Q cofactors, in the displayed
order, indexed by i=0,...,44:

    5,7,11,13,35,25,17,19,55,65,49,85,77,95,91,
    175,125,119,133,245,143,121,385,275,455,187,325,
    169,209,221,595,247,425,665,475,343,715,605,323,
    289,539,875,625,361,935.

Let t_0,...,t_44 be the increasing list of residues t modulo81 with
`t mod3 !=1` and `t mod9 !=3`. These are precisely the45 depth4
cylinders surviving the two pure3 originals. At cofactor d_i, add
three originals, all with Q phase2:

| ternary exponent | ternary phase |
|---:|---|
|4|t_i|
|5|t_((i+1) mod45)|
|6|t_((i+2) mod45)+81|

Each pair of coprime ternary and Q conditions determines one residue
modulo `3^e d_i` by CRT. The135 deep originals and14 preceding
originals give149 distinct odd nonunit numerical moduli. At every
cofactor the selected phases contain all actual projections through
ternary exponent3. The deep phases are not reselected on separate
branches or source events.

## 3. Exact actual-union computation

For each q, let v_q be the q-adic valuation of `x_q-2`, truncated at
the largest exponent of q appearing in the45 cofactors. Those six
cutoffs are

    (4,3,2,2,2,2),

so there are exactly1620 valuation cells. Under the actual product
source their coordinate probabilities are

    Pr(v_q=0)=1-1/(q s_q),
    Pr(v_q=n)=(q-1)/(s_q q^(n+1)),  1<=n<h_q,
    Pr(v_q=h_q)=1/(s_q q^h_q).

These are exact finite-cell probabilities, not a truncation error:
the final cell includes the complete higher tail. A deep original
with cofactor d is incident exactly when every valuation dominates
the corresponding exponent in d.

For every one of these actual cells, take the ordinary set union of
all incident ternary cylinders modulo729. Let M be its cardinality.
All its points lie in the45 pure3-surviving cylinders, and actual
overlaps are counted only once. Since both weighted branch losses
have the same raw Haar coefficient54,

    W=54M/729=2M/27,
    (W-16/3)_+=(2/27)(M-72)_+.

Summing against the exact cell probabilities gives AT1. The
independent producer reconstructs all original CRT residues and every
one of the1620 actual masks; it does not replace this union by an
additive load or combine incompatible marginal summaries.

## 4. The source has a much smaller actual query norm

For every q-power modulus q^h, the largest source cylinder has mass
`1/(s_q q^h)`: the Haar-density upper bound proves this, and the
untouched root2 cylinder attains it. Independence and complete
geometric tails therefore give

    R=R_Q(nu)=product_(q in Q)[1+1/(s_q(q-1))]-1
      =214267985/147806208
      =1.4496548412905634... .                             (AT3)

This is the complete all-height query norm. The example violates Report586's
small-tail target while having R far below the conservative supplier
bound `B=5.003067549838209...`. It therefore does not obstruct a
joint certificate retaining actual source cost.

## 5. Retaining R gives an all-height source-only condition

Here the family is any finite actual P-supported family of distinct
odd nonunit numerical moduli, with one globally fixed residue per
modulus, pure3 originals exactly `1 mod3` and `3 mod9`, and at most
two selected phases per nonunit Q cofactor containing all projections
through ternary exponent3. Use Report586's notation: `X=12(1-c_A)`, `V=18(1-c_B)`, `W=X+V`,
`T=(W-z)_+`, `U=min(X,(z-V)_+)`, `D=30-z`, and the one supported
submeasure eta with Q marginal `(1-T/D)nu`. Write `tau_z=E T` and
`s=1-tau_z/D`. Keep the same universal hinges

    B=432040125182653876501/86355045355449035400,
    K2=B-2,
    K3=12019840537595758779003/5715264751774801992890.

At each original height, joint A/B numerical uniqueness gives one
legal partial query layout. Thus the actual mean bound is `E W<=R`,
not merely B. In particular `E U<=R-tau_z`. Inserting this into the
second-hinge bound for U and Report586 CJ6 gives

    R_P(eta)<=1+2R+[zK2-3-3tau_z]/D.                      (AT4)

The term `-3R/D` in the root/deep coefficient cancels the `3R/D`
from `E U+R_Q(U nu)`. Replacing that latter R by B before combining
would lose precisely this improvement.

Take z=3 and D=27. The same-source full third-hinge contract and the
actual joint-height mixture give `tau_3<=K3`. With `G=566/49`, AT4
then yields

    Gs-R_P(eta)
      >=G-1-2R-[3K2-3+(G-3)tau_3]/27
      >=2(R_crit-R),                                    (AT5)

where

    R_crit=[G-1-(3K2-3+(G-3)K3)/27]/2

is exactly the threshold in AT2. In particular s is positive, since
`K3<27`, and `mu=eta/s` has `R_P(mu)<G` whenever R<R_crit.

The remaining originals supported on `P union{23,29}` may touch23
or29 with arbitrary fixed phases and arbitrary finite heights.
The same raw density and extension count as Report586 give

    H(full survivor)>=(49 alpha_min/5544)(R_crit-R),
    alpha_min=7575003978548161/73724315753088000.           (AT6)

For the original source AT3, this is

    1871277599635695698864969031197
      /609366447121640655085948108800000
      =0.003070857623478824...>0.

No small-damage-tail assumption is used here, and no source is changed
between the counterexample and this repair. This is not a claim of
new bare noncoverage for that finite family or an optimal choice among
all possible supported laws.

For selected Q families containing only pure-prime-power classes, the
same elementary product bound gives an automatic instance of AT2.
Each coordinate survivor has mass at least `(q-3)/(q-1)`; the later
PA caps are inactive and the actual source is a product. Its complete
prime-power query sum is at most `1/(q-3)`, so

    R_Q(nu)<=product_(q in Q)(q-2)/(q-3)-1
            =47063/28672<R_crit.

No product-source search of this kind can reach the remaining
high-query region; that region requires actual mixed-Q selected
constraints. This is a direct product estimate, not a separate new
kernel theorem.

## 6. What remains

For z=3 the actual sufficient joint condition is

    2R+((G-3)/27)tau_3
      <G-1-(3K2-3)/27.                                  (AT7)

The new source-only test uses `tau_3<=K3` to satisfy this when
R<R_crit. The remaining question is whether every actual family in
the stated slice admits one selected source, or another supported
law, satisfying a complete continuation certificate. The present
construction does not settle the high-query part `R>=R_crit`, nor
remove the fixed pure3, shallow two-phase or prime-support conditions.

[Report571](571-joint-residual-laws-retain-conditional-and-query-incidence.md)
JB7--JB10 already shows why positive deleted mass alone does not force
a positive actual-query debit. That obstruction is not counted again
as a new general result here.

The [exact producer](../../frontier/cover-geometry/automatic_tail_actual.py)
and [data](../../frontier/cover-geometry/automatic_tail_actual.json)
retain the actual original residues and source. The exact actual-union
and source calculations are separate from the
general deductions AT4--AT7. The producer checks the finite149-original
counterexample with complete coordinate/query tails. All63 named checks
pass, including the full1620 actual valuation cells and the exact
source-only margin identities. The ordinary
proofs carry the all-family and all-height source-only implication.
No new Lean verification is claimed.

Run with Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/automatic_tail_actual.py

## 7. High actual query cost requires a substantial mixed19 loss

The remaining region R_Q(nu)>=R_crit has a further necessary
condition from the existing one-row cap estimate. Let

    S17=lambda_<19(1),  nu17=lambda_<19/S17,
    d=Delta19/S17,  S=S17(1-d).

The actual prefix before19 is precisely the original PA construction
on the selected family supported on Q without19: originals involving19
do not alter earlier kernels. The omitted19 calculation in
[Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md)
NC9 and its exact data therefore give

    R_Q_without19(nu17)<=B17
       =2274605369898493/588022615198334
       =3.868227702656116... .

This concerns the stopped-prefix law. The earlier marginal after
the final19 reweighting need not equal nu17.

The current row has mass at most one and density at most9/5.
For each nonunit label d0 without19, its final raw query mass is at
most S17 q_d0(nu17). For each label19^e d0 with e>=1, including
d0=1, it is at most (9/5)19^(-e)S17 q_d0(nu17). Summing all query
heights and then normalizing ONCE gives

    R_Q(nu)<=A/(1-d),
    A=(11B17+1)/10
      =25608681684081757/5880226151983340
      =4.355050472921728... .                            (AT8)

The unit appears only in the positive19-exponent sum. The same-source
mass bound ensures d<1. Consequently

    R_Q(nu)>=R_crit  implies
    d>=d_min=1-A/R_crit
      =42340905997086165193203264671190758157847
         /429610513200413970577603014236563262811427
      =0.09855649407102397... .                          (AT9)

Thus at least this fraction of the actual incoming prefix mass must
be lost in the final19 row. It cannot be supplied by pure19 constraints
alone. Let s_pure be the Haar mass surviving all selected pure19-power
classes. At most two classes at each numerical19^e give

    s_pure>=1-2 sum_(e>=1)19^(-e)=8/9.

For a prefix h, let v19(h) be the Haar mass of the actual incident
mixed19 forbidden UNION inside that pure survivor. Every actual
overlap is included once. Then g19=s_pure-v19, so

    1-min(1,(9/5)g19)
       =(9/5)[v19-(s_pure-5/9)]_+
       <=(9/5)[v19-1/3]_+.

AT9 therefore forces

    E_nu17(v19-1/3)_+ >= (5/9)d_min
      =211704529985430825966016323355953790789235
         /3866494618803725735198427128129069365302843
      =0.05475360781723554... .                          (AT10)

This is a direct use of the old stopped-prefix and cap bounds, not
a new source mechanism. It rules out the high-query region whenever
the actual mixed19 union is everywhere at most1/3, but does not
exclude the general mixed case.

[Report588](588-query-prefix-incidence-strengthens-actual-source-debits.md)
weights final-row loss by the maximizing query's earlier-only count
(n19-2)_+. AT9 controls unweighted loss. The missing step is a useful
joint bound relating where that loss occurs to those fixed query
prefix events and the actual ternary damage. No independence or
favorable correlation of these quantities has been established.
