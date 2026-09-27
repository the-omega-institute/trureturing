# Joint anchor budgets close five split patterns with finite prefix agreement

Let P={3,5,7,11,13,17,19}, and choose any p in{7,11,13,17,19}.
Consider a finite family of congruence classes a_i modulo m_i with pairwise
distinct odd numerical moduli greater than1, supported on P union{23,29}.
Suppose there are two fixed references A,B and one fixed prefix c_q modulo
q^4 for every q in P minus{3,5,p}, satisfying:

- A and B differ modulo3, modulo5 and modulo p.
- For every complete original later label m_i=d_i*23^j*29^k, j+k>0,
  choose one fixed selector sigma_i in{A,B}. At each q in{3,5,p}, its
  actual residue obeys a_i=sigma_i modulo q^v_q(d_i). The same selector
  must work at all three coordinates.
- At every other old prime q, its actual residue obeys
  a_i=c_q modulo q^min(4,v_q(d_i)). Its deeper digits may be arbitrary
  and need not come from either of two global reference paths.

Then the family does not cover the integers. Original old-only classes,
all finite heights and all23/29 phases are arbitrary. Each complete label
keeps one fixed selector across the three split coordinates and all tested
points. Labels with the same d but different(j,k) may choose differently.
For d=1 every old condition is vacuous. No selected shallow class is
required to have been originally present.

In particular this includes two global old references which split at3,5,p
and agree through only min(4,H_q) at each other old prime, where H_q is the
largest later queried exponent and is0 if no later label queries q. They
may separate at deeper queried digits. The theorem also allows the deeper
residues at those four primes to vary independently with each original
numerical label, without any global two-path representation there.

The proof strengthens the source lower bound in
[report515](515-actual-anchor-reserves-close-the-fixed-mixed-chart.md),
transfers the row geometry of
[report516](516-three-first-root-splits-with-four-common-prefixes-do-not-cover.md)
to five choices of p, and controls the region affected by replacing deep
reference digits. Each step keeps one actual original family and one
completed source. These are ordinary mathematical deductions and exact
finite computations, with no new Lean verification. Arbitrary unrelated
old residues, arbitrary prime support and unrestricted Erdős#7 remain
outside this result.

The source construction and mixed-anchor formulas are Michael Schroeder's
*Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1,
Sections6,8--9. The [library entry](../../../../../Library/Arith/schroeder2026nine.md)
records attribution, archive identity and the local arbitrary-height
verification boundary. The new lower is an exact prefix consequence of
those formulas, not a new construction attributed to this project.

## Both the reserve and the losses retain the same actual holes

Choose the completed-and-charged old source nu of reports466/467, in its
actual order3,5,7,11,13,17,19. At7,11,13,17,19 its full-history conditional
caps are respectively

    3/2,5/3,3/2,2,9/5.                                  (J1)

The seven nonworst coarse source types retain report491's direct mass
separation. For the worst type(2,4,1), normalize the selected six cylinders
simultaneously to

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.

Their complement A6 has221 cells modulo675. The selected45/75 phases
(r,s) lie in the same17-by33 legal domain as report515. That report refunds
their overlaps in the basic reserve while retaining basic loss bounds
which release the two holes. Retaining the holes in both places gives

    nu(1)>=M=12604673809/675000000000
             =0.018673590828148148...                    (J2)

for all561 actual phase pairs. This replaces the weaker m7+c45+c75
lower. Its credits must not be added a second time. It leaves the source
kernels, conditional caps and original-family support unchanged.

Here is the joint budget giving J2. Normalize r by a single tree map
preserving the six anchors. Its signature is

    (r mod3,1[r=4 mod9],1[r=2 mod5],1[r=1 mod5]).

The eight least legal representatives are4,7,8,11,16,22,31,34. Apply the
same map to s, whose new projections are d modulo3 and k modulo5. There
are seven choices(d,k), with d in{1,2}, k in{1,2,3,4}, excluding(2,2).
Thus561 actual pairs are represented by56 triples(r,d,k).

These are actual simultaneous tree maps. At3 the second-digit branches
inside root2 may permute; the selected9 branch and27 leaf stay fixed.
At5 roots0,1,2 stay fixed, roots3,4 may interchange, and a child permutation
inside the selected75 root sends its leaf to a canonical child. In root1
that permutation fixes the selected25 child. Legal75 phases avoid that
child. Every selected cylinder and both actual phases are transported by
one map, together with the complete source and references. The lower
bound uses no later-reference coordinates, so their movement poses no
extra hypothesis. The consumer checks all561 finite maps, their prefix
consistency, each of the six fixed cylinders and both class images.

Put

    K_r={x mod135:x avoids0(3),1(9),4(27),0(5),2(15),r(45)},
    B={x in K_r:x=d mod3,x=k mod5},
    D_h=1[h=1]/5+t_h.

The higher pure5 budget and its overlap e with the selected75 child obey

    t_h>=0, sum_h t_h=1/20, 0<=e<=t_k.

The remaining relative quinary mass at x is

    1-D_(x mod5)-(1/5-e)1_B(x).

Its five joint vertices are(t,e)=((1/20)e_j,0), j=1,2,3,4, and
((1/20)e_k,1/20). Their coefficients20(t_j-e1[j=k]) and20e are
nonnegative and sum to1. Use these same coefficients in the reserve and
all stage-loss bounds.

In135-cell units the source's mixed reserve specializes to

    R=135/4+9D_2+gamma45+(3-gamma45)D_(r mod5)
         +9/5-|B|(1/5-e),
    gamma45=1[r=4 mod9].                                (J3)

The15 and45 classes are disjoint. The75 charge is evaluated after
removing45, since B is defined on K_r; their possible overlap is counted
once. The five-vertex quinary zero-atom numerator is

    16-4*1[x=1 mod5]-1[x=j mod5]-(4-i)1_B(x),

where i=0 at the first four vertices and(j,i)=(k,1) at the last. The
ternary zero numerator is4. The same nonnegative weights enter the
ordinary geometry maximum and its complete infinite-depth comparison.

For every vertex the consumer evaluates the five ordinary loss bounds
through19, at thresholds(2,4,4,8,8), and rounds each upward by less
than10^-10 cell units. It computes

    lower_vertex=(R-sum_(q=7,11,13,17,19) LossUpper_q)/135.

The minimum over all280 vertices is J2. Convexity of the geometry
maximum, positive expectations and the exact remainder bounds make the
ledger at least the same convex combination of vertex ledgers. No
vertex is optimized separately for different stages. Positive3/5 depths
beyond the finite geometry range and all multiplier tails are paid by
the full linear load and exact zeroth and first moments.

The source's compatible-screening lemma licenses these bounds on the
same prescribed charged process. At7 the ordinary inventory dominates
the selected charged contributions; later ordinary bounds release
first-hit savings, and at11 they release the prescribed165 residue.
Retaining45/75 holes strengthens that ordinary screen. No alternative
source is substituted, and no actual kernel is reordered.

## The existing row constraints transfer by their numerical labels

First impose agreement through every queried depth at the four primes
other than3,5,p. Present the exponent coordinates in the order

    (3,5,p,q1,q2,q3,q4), q1<q2<q3<q4.

The numerical label attached to an exponent vector e is

    d_p(e)=3^e0*5^e1*p^e2*product_j qj^e(2+j).

Unique factorization identifies these label sets bijectively as p changes.
For a signed split profile s, the two reference boxes have exponent lengths
max(1,s_i) and max(1,-s_i) at the first three coordinates, and the same
lengths s_i at the remaining four. Their full membership masks and every
intersection are preserved by this identification. In particular,

    Q(s)=(product_(i<3)max(1,s_i)
          +product_(i<3)max(1,-s_i)-1)*product_(i>=3)s_i.

For any finite collection of tested profiles and nonnegative weights w,

    N(w)=sum_e max(w dot mask_A(e),w dot mask_B(e))       (J4)

is identical under the label bijection. This maximum is taken once per
whole original label. It never gives different points independent
selector choices.

The later fibre budgets charge23^-j29^-k, with no factor1/d: at a fixed
old point, matching a cofactor is a zero/one activation. Thus the ordinary
pairs, triples, four-point certificates, binary cliques, finite-height
zero-only pairs and signed order rows of report509 consume the same J4,
axis capacities22/28 and mixed scale616. The strict finite-height factor
(1-23^-J)(1-29^-K) is also unchanged. All existing rows remain valid in
every role order. This transfers their validity, not their old numerical
weights or the physical source law.

For the true split prime p use the comparison probability

    J_p(0)=1-2C_p/p,
    J_p(+f)=J_p(-f)=C_p*(p-1)/p^f, f>=2.

For each true common prime q use

    J_q(1)=1-C_q/q,
    J_q(f)=C_q*(q-1)/q^f, f>=2.                          (J5)

Compare the actual kernels backwards in their unchanged natural order,
using their full-history caps and upwardness of the zero-support event.
Only after obtaining this independent product comparator is its written
order changed. Each actual prime, its cap and its complete geometric tail
stay together. Swapping actual conditional kernels would be unjustified.

## Three price vectors close all220 reference charts

The44 actual3/5 reference orbits of report516 remain available: their tree
maps affect none of the other primes. For each p and reference representative
rho, integrate the initial paired shells exactly on A6 and use J5 at the
remaining coordinates. Enlarging the actual initial source to A6 gives a
valid nonnegative upper comparator even though J2 retained both45/75 holes
on the lower side.

There are23408 profiles with Q<=38, of which3332 with Q<=19 are safe and
20076 are middle profiles. For their exact weights w_i, the complete
remaining mass is

    overflow=221/675-sum_(all23408 profiles)w_i.

This includes every infinite tail. With nonnegative rational row prices y
on the inherited valid constraints Az<=b, the upper is

    U=overflow+y dot b+sum_(middle i)max(w_i-(A^T y)_i,0). (J6)

Negative child loads from the order rows are kept before taking the
positive part. For every actual family, nu({s=0})<=U.

The consumer uses report516's existing reference26 price vector and two
additional vectors on the same row matrix. It checks all5*44 reference
charts, with a deterministic price selection. Each A6 bound covers all561
actual45/75 pairs because J2 is uniform and the upper released both holes.
This covers123420 representative phase cases. No optimizer is needed to
consume the rational prices, and no new geometric row is asserted.

The guaranteed worst-type source separation in each role is:

| Third first-root split p | Minimum M-U across44 representatives |
| --- | ---: |
| 7 | 0.00018393362529277194... |
| 11 | 0.001241097637999085... |
| 13 | 0.0004719829308... |
| 17 | 0.0005054947102... |
| 19 | 0.001340585173... |

Exact fractions, chosen prices and minimizing references are retained in
the result JSON. All five margins exceed1/6000. These are lower bounds for
source mass on nonzero fibres, not uniform lower bounds for the positive
values of s(x).

## Deep reference separation changes only a controlled region

Report491's seven nonworst types have direct source separation

    Delta=0.0006371421680321602...,

stored as uniform_nonworst_margin_own_source in its exact result. It is
the minimum of m_t-B_t over the actual source types and their tested
patterns. Q<=19 implies positive later-fibre survival. Thus for the
fully common comparison family the source mass on positive fibres is
at least delta_p=min(Delta, the p-row margin above), for every completion
type. This uses the direct source bound, without reversing a Haar result.

Now allow the arbitrary per-label deep residues in the opening theorem.
Let H_q be the largest later queried q exponent, or0 if none is queried.
For each of the four common-prefix coordinates choose one extension c*_q
through H_q, once. Finite CRT constructs A*,B* which retain A,B at all
queried3,5,p coordinates and both equal c*_q at the other coordinates.
For each original later label retain its same selector sigma_i and23/29
phases, replacing its old residue by the selected A* or B* modulo d_i.
The modified family has exactly the same numerical labels; its old-only
family and source nu are literally unchanged. Its references meet the
full-common hypotheses just proved. These are comparison references; the
original deeper residues need not be globally representable by two paths.

Let

    E=union_(q notin{3,5,p},H_q>4){x:x_q=c_q mod q^4}.

Every changed later class has some such q exponent greater than4. Both
its original and modified old cylinder lie in the same q^4 cylinder,
because both match c_q through that prefix. It is inactive in both fibres
outside E. Unchanged classes have identical activations and phases.
Consequently the two complete later survivor sets agree at every old
point outside E, simultaneously for every new-coordinate point.

If the original family covered, finite CRT would make its later survival
zero at every old point outside its old-only covered set, hence on the
support of nu. The modified family's positive-fibre event would then lie
inside E. The source's initial3/5 mass is at most3/8. Its kernels normalize
before deletion, and survivors are never renormalized. At stage q the
conditional mass of one q^4 cylinder is at most C_q/q^4; previous live mass
is at most3/8 and subsequent subprobability operations cannot increase it.
Therefore

    nu(E)<=(3/8)*sum_(q notin{3,5,p}) C_q/q^4=:epsilon_p. (J7)

This uses full-history caps of the actual source, not retrospective
conditioning or independence of its final coordinates. Omitting unqueried
or unchanged coordinates only improves the bound.

| p | Exceptional source mass upper epsilon_p |
| --- | ---: |
| 7 | 0.00007654232532905394... |
| 11 | 0.00026813136879189406... |
| 13 | 0.00029112502119088606... |
| 17 | 0.00030183993221123326... |
| 19 | 0.00030564019148577654... |

The exact consumer checks delta_p-epsilon_p>1/10000 for every p.
The modified positive-fibre event has source mass at least delta_p and at
most epsilon_p, a contradiction. This proves the original-family theorem.
More general finite depths h_q suffice whenever

    (3/8)*sum_(q:H_q>h_q) C_q/q^h_q < delta_p,            (J8)

with every original later residue matching c_q through min(h_q,v_q(d_i))
at those coordinates. Depth4 is one
uniform sufficient choice; it is not asserted to be optimal.

Apply the inherited source reductions to the full-reference comparison
family when using its source separation. The missing-shallow-class and
deleted3/5-root reductions are inherited
from reports491/516. Choose one old completion first. Insert a selected
pure class only if its numerical label is absent; remove later classes
already contained in it and inactive on the source. Only now-unused
reference coordinates need relocation. The exact-zero event on nu is
unchanged. Simultaneous tree normalization preserves every prefix depth,
so the new finite-prefix assumption survives these reductions. This
justifies using the source inequalities with the original quantifiers.

## Reproduction and remaining boundary

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_anchor_prefix_lower.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_single_split_source_bound.py

The lower consumer carries576 explicit geometry batches and61920 distinct
integer queries with source identities and the source's MIT notice. It
reconstructs the prescribed queries, all280 vertex ledgers and all561
phase transports, paying all infinite-depth remainders. The upper consumer
pins the resulting lower and inherited reference/row data, recalculates
physical-prime weights and all signed residuals, and checks the final
finite-prefix perturbation inequalities. Default execution compares the
retained outputs; --output writes them.

Integer geometry values inherit the pinned source evaluation and its
finite-verification boundary; hashes identify inputs and do not establish
those maxima by themselves. Same-source screening, interpolation,
label transfer, tree transport and the reference-replacement argument are
ordinary mathematical proofs. No source verifier or Lean build is claimed
by these standard-library consumers.

The original finite family has a finite period, so noncoverage gives
positive natural density for that family. The proof supplies no uniform
positive Haar-density floor and no fixed arbitrary-prime-tail extension.
Exact-zero rows may allow positive survival values tending to zero with
height. Additional early first-root splits, residues without the declared common
prefixes or the shared selector at3,5,p, and arbitrary prime supports still
require new arguments.
