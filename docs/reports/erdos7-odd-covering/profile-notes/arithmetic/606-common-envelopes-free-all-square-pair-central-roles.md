# Common envelopes free all square-pair central roles

Keep the actual pure source, central15 phase, star phases and new9q/25q
phases of [Report604](604-fixed-pair-activation-admits-ten-central-square-stars.md).
For four choices of the squarefree pair roles, every central phase at all
80 square-pair labels may now be arbitrary and globally fixed. The complete
ten-prime survivor has Haar mass greater than1/6500.

After source-null and missing roles are padded into the retained roots,
there are20 central activation profiles, each with64 canonical choices.
Each primary pattern admits all64^20=2^120 padded role assignments. This
covers completely arbitrary actual secondary central residues, together
with arbitrary outside components and
all other original phases and finite heights permitted below. The proof
bounds their common actual-source construction; it does not enumerate a
sample and infer a universal result.

The unrestricted120-label pair-role problem remains open for this method:
the squarefree primary roles still belong to the four listed patterns.
No additional9q^2/25q^2, support-four augmentation or exterior branch
extension is included here. This is ordinary mathematics with exact
rational certificates, not new Lean verification.

## Fixed and free parts of the original family

Use P={3,5,7,11,13,17,19,23,29,31} and V={7,11,13,17,19}. All numerical
moduli are distinct, each may be absent or present once, and every residue
is globally fixed.

Retain Report604's exact restrictions on the pure3/pure5 inventory and
on central15, all existing star labels and all ten new9q/25q labels.
In particular the permitted pure3/pure5 originals are a subset of

    2 mod3, 7 mod9, 4 mod27, 13 mod81, 40 mod243, 121 mod729;
    4 mod5, 2 mod25.

The central15 component is0 mod15. Set
j_7=1,j_11=2,j_13=j_17=j_19=3. The central components of3q and3q^2 are
0 mod3, those of5q and5q^2 are j_q mod5, and15q has point(0,j_q).
The new9q component is1 mod9 and the new25q component is12 mod25.
All their q-components are arbitrary. Other pure powers are unrestricted.

For each q<r in V there are twelve retained pair labels

    3^a5^b q^e r^f,
    (a,b) in{0,1}^2, (e,f) in{(1,1),(2,1),(1,2)}.      (PE1)

Call the exponent type(1,1) primary. Number the ten outside pairs
lexicographically by h=0,...,9. Select one of these four primary tables:

|Primary pattern|Row mod3|Column mod5|Point(mod3,mod5)|
|---|---:|---:|---|
|concentrated00|0|0|(0,0)|
|concentrated12|1|2|(1,2)|
|cyclic|h mod2|2h mod4|((h+1) mod2,(h+1) mod4)|
|separated|1|2|(0,h mod4)|

The row specifies the central component of3qr, the column that of5qr,
and the point that of15qr. The qr label has no central component.
Every outside component remains arbitrary.

For each of the other20 outside exponent types, the actual residues of
its3-,5- and15-multiples are completely arbitrary. Thus the actual row
may be any residue mod3, the column any residue mod5, and the point any
of the15 residue pairs. All choices are made once for the family.

The chosen pure source only uses rows{0,1} and columns{0,1,2,3}. An actual
row2, column4 or point outside that retained rectangle has zero central
source mass. For upper estimates only, retain every active actual role
and pad every null or missing role by one fixed role in the retained
rectangle. For example, use row0, column0 or point(0,0) whenever padding
is needed. This dominates the original activation on every source cell.
It does not change any original residue or substitute a new actual event.
The padding is fixed globally and is independent of all later queries.

Each padded profile now has2*4*8=64 possibilities. Proving the bound for
all64^20 padded assignments covers every actual residue assignment at
the80 square-pair labels, as well as missing slots. The number64^20 counts
these canonical padded profiles, not all actual residue choices: when
all four labels of a type are present, there are3*5*15=225 actual central
profiles before padding. No equality between roles at different numerical
labels is required.

Every other mixed original on the first seven primes obeys Report598's
inventory condition: some exponent at least3, or both central exponents
at most1, or at least five prime divisors. All originals touching23,29
or31 are unrestricted. The retained inventory still has156 labels; no
new numerical label or original height is introduced by freeing these
roles. Pure3/pure5 remain subject to their explicit finite inventory.

## A uniform strict region on the same source

Use the actual central source of Report604, indexed by leaves l=3i+t and
m=5j+s. Its masses and shared density references are

    w=(81,81,81,81,41,0)/365, d3=729/365;
    v_10=0, v_11=v_12=v_13=v_14=1/16,
    all other v_m=1/20;
    d5=(5/4,5/4,25/16,5/4).                         (PE2)

At q in V set r_q=1/(q-1), a_q=1/[q(q-2)]. The conservative star factors
b_q(l,m)>0 are exactly Report604 FA7. Delete the central root cell(0,0).
There are105 remaining leaf cells. The old product pure source still
has full density at most D=3458/405.

For edge e={q,r}, write

    p_e=r_q r_r,
    s_e=a_q r_r+r_q a_r,
    kappa_e=p_e+s_e.

The primary activation alpha_e(i,j) is fixed by its chosen row, column
and point. Its value is1+row+column+point. For the two free types write
their analogous globally fixed padded profiles alpha_e,1 and alpha_e,2. Then

    beta_e=p_e alpha_e
             +a_q r_r alpha_e,1+r_q a_r alpha_e,2,
    kappa_e<=beta_e<=4kappa_e.                       (PE3)

As in Report597, beta is a padded upper cap for the actual pair union,
not its exact probability. Absent or source-null originals may be given
arbitrary fixed padding roles; the estimates remain upper bounds.

For each unmasked leaf put u_e=beta_e/(b_q b_r). In the whole box
0<=beta_e<=4kappa_e, the shared-coordinate graph has the polynomial

    Z_A(u)=1-sum_(e in A)u_e
                +sum_(e,f in A, disjoint, unordered)u_e u_f.

At the upper corner beta=4kappa, exact evaluation over all105 cells gives

    min Z_all=31820206188505/126963499999921>0,
    max_e sum_(f disjoint e)u_f
      <=6053127/13633361<1.                         (PE4)

Each coordinate derivative of every induced polynomial is negative
throughout the box. Zeroing omitted coordinates therefore increases the
polynomial, proving strict positivity of every induced polynomial for
every actual role assignment. This establishes the necessary strict
region uniformly; it does not presume that the upper corner is a
realizable global phase layout.

## Monotone query grids for every outside support

For any actual family, construct its actual conditional pair-survivor
submeasure by Report597 PS9--PS11, using that family's own beta. Define

    G_T=1_(central cell survives) product_(q notin T)b_q,
    H_T(beta)=G_T Z_(edges disjoint T)(u).            (PE5)

H_empty(beta) is the exact mass grid of the deliberately thinned chosen
submeasure. H_T(beta) is its query upper grid, at all outside heights.
The conditional laws and all original phases are those of that same family.

If e intersects T, H_T is independent of beta_e. Otherwise its derivative is

    d H_T/d beta_e
      =-G_(T union e)
          [1-sum_(f disjoint e and T)u_f]<0          (PE6)

on every unmasked cell throughout the box in PE4. At a masked cell every
grid is zero. Thus H_T is decreasing in each beta coordinate for every
outside support T, including the empty support used for mass.

For the20 free role choices only the elementary bound1<=alpha<=4 is needed.
With the primary roles held fixed, define comparison caps

    beta_e^- = p_e alpha_e+s_e,
    beta_e^+ = p_e alpha_e+4s_e.                     (PE7)

Every one of the64^20 padded assignments, including the padding of each
actual family, satisfies

    beta^-<=beta_actual<=beta^+<=4kappa,
    H_T(beta^+)<=H_T(beta_actual)<=H_T(beta^-)
    for every T.                                  (PE8)

The endpoint vectors need not be globally realizable. They are comparison
grids bounding the one actual measure of each original family. Using a
lower bound for its mass and upper bounds for its query probabilities
simultaneously does not combine different source laws.

## One fixed thinning matrix covers all20 free choices

For each of the four primary patterns choose the stored dyadic matrix
0<=theta(l,m)<=1. It is constant on the fourteen nonzero blocks formed by

    row classes: {0,1,2}, {3}, {4};
    column classes: {0,...,4}, {5,...,9}, {11,13,14}, {12}, {15,...,19},

after omitting the masked first-row/first-column block. Row5 and column10
have zero source mass and receive zero theta. No optimality assertion is
needed: these are explicit sufficient witnesses.

The same theta multiplies the actual mass grid and all actual query
grids. In particular it is fixed before any of the20 free roles is chosen.
Let L,W and the central screens S be Report604's complete512-entry
remaining-original and nonunit-query arrays. They retain the same source
masses, density references and analytic sums over all exponent heights.
Since screens are maxima of positive linear functionals, PE8 implies a
uniform continuation gate lower bound

    K_box(theta)=
      (1-c)sum_(l,m)w_l v_m theta(l,m)H_empty(beta^+)
      -sum_((e3,e5),T)[(1-c)L+cW]
                    S_(e3,e5)(theta H_T(beta^-)),
    c=1084133/201247200.                            (PE9)

To verify its direction, begin with the actual family's chosen measure.
Its pair-survivor mass is at least the first sum by PE8. Every remaining
original debit and every weighted query debit is at most the corresponding
screen at beta^- by PE8. Restricting this same measure by all remaining
originals therefore has gate at least PE9. The unit query is accounted
for by the factor1-c; the nonunit array W excludes it.

The argument is uniform over all64^20 padded assignments and all unspecified
outside phases. It neither selects a different beta for a query nor replaces
a global role assignment by independently maximizing each central cell.
Only comparison inequalities are taken pointwise.

## Four exact certificates and the head conclusion

Direct rational evaluation of the four fixed dyadic matrices gives:

|Primary pattern|Uniform gate lower bound, decimal display only|
|---|---:|
|concentrated00|0.008617643741990958...|
|concentrated12|0.010293727705276567...|
|cyclic|0.008318716722642390...|
|separated|0.008848738537744870...|

Each exact fraction is strictly greater than1/125. The existing23,29,31
continuation is reconstructed on each resulting actual source, with the
same controls2/5,9/20,1/2 and density multiplier200/33. Restricting the
extended law to its complete head survivor yields

    H_P(U)>=alpha K_box,
    alpha=33/(200D)=2673/138320,
    alpha/125>1/6500.                              (PE10)

This proves the asserted noncoverage class. The fixed pure and star
conditions and four primary-role patterns remain part of its hypotheses.
This theorem does not assert positivity for every primary layout, and
failure of a coarse envelope elsewhere would not be an actual covering
example or an impossibility result for the exact beta construction.

## Reproducible certificate and reuse

The [producer](../../frontier/cover-geometry/arbitrary_square_pair_roles.py)
and [data](../../frontier/cover-geometry/arbitrary_square_pair_roles.json)
use only the Python standard library. They fingerprint Report604's data
and producer, reuse its source, complete coefficients, selector definitions
and star factors, and rebuild the new primary weights, uncertainty envelopes,
strict-region inequalities and exact common-theta gates. The inherited six
fixed-pattern evaluation is not rerun.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_square_pair_roles.py

All34 named predicates, evaluated19680 times, pass with explicit failure
branches active under-O. The four fourteen-entry integer vectors and their
expanded120-entry matrices are retained. A separate pure-rational replay
checks the endpoint grids and complete gate fractions. No floating optimizer
or exploratory phase sample is a proof input.

The finite arithmetic checks the displayed constants and witnesses. The
all-layout guarantee is PE3--PE9: a uniform strict box and monotonicity place
every actual globally fixed role assignment between the same comparison
grids, while preserving that family's one actual source throughout.

[Report608](608-one-common-thinning-frees-every-central-pair-role.md)
removes the four-pattern restriction: one common thinning witness and64
exhaustive branch certificates admit arbitrary central roles at all120
retained pair labels. The pure-source and star hypotheses remain fixed;
the retained numerical inventory and permitted heights are unchanged.
