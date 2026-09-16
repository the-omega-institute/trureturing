# Exact supported laws for the finite 5040 odd head

For a family F of distinct nonunit moduli dividing Q, write S_F for the
uncovered residues modulo Q. For a probability law mu supported on S_F,
let

    Gamma_Q(mu)=max_test E_mu[(sum_{d|Q} 1_{x=a_d mod d})^2],

where the test residues a_d are chosen independently of the forbidden
residues of F and independently for each d, and the divisor1 contributes1.
Then

    sup_{F, moduli|45} inf_{mu supported on S_F} Gamma_45(mu)
      =22570/3361.

For every F with distinct nonunit moduli dividing 315, there exists a
supported law satisfying

    Gamma_315(mu)<=198583/15619 <12.715.

The 315 bound is constructive but is not asserted minimax-optimal.
The 45 result uses simultaneous original-assignment and complete independent
test-layout optimization; no assumption of coherent test centres is made.

## Completion, pruning and symmetry

Adding missing forbidden classes only shrinks the survivor set. A law
supported on the smaller survivor set is also supported on the original
set, with exactly the same test-layout moment. Likewise, if a forbidden
class is wholly redundant under already selected classes, replacing it
with a class through a currently surviving point enlarges the forbidden
union. These are valid monotonicity reductions for the existential-law
claim. They do not assert monotonicity of uniform-survivor averages.

Complete the 45 head with one original class for each of3,9,5,15,45.
By ternary tree automorphisms and quinary point permutations normalize
the pure classes to0 mod3,4 mod9,0 mod5. If pure9 was redundant inside
the forbidden3 root, replace it by an effective class first. The remaining
ternary leaves are short-root{1,7} and long-root{2,5,8}; the quinary
columns are{1,2,3,4}.

Make the15 class effective if necessary. It deletes one short or long
root at one column, normalized to column1. Make the45 class effective
if necessary. Under the stabilizer there are exactly three positions:

* in the same ternary root and a different column;
* in the other ternary root and the same column;
* in the other ternary root and a different column.

Thus there are six cases: two15-root types times three45-point types.
The stabilizer permutes the two short leaves, the three long leaves,
and the four columns. All these maps preserve every divisor-cylinder
family, so they preserve Gamma. The verifier checks all140 normalized
active assignments, proves the six orbits disjoint and exhaustive, and
finds orbit sizes24,12,36,36,8,24. The survivor sizes are17 for the short
15-root cases and16 for the long15-root cases.

For a fixed survivor set, an empty test cylinder can be replaced by a
nonempty cylinder of the same modulus. Its indicator only increases on
S, so the squared nonnegative complete load does not decrease. Hence it
suffices to enumerate nonempty test cylinders independently for the five
moduli. There are4760 layouts per short-root case and4480 per long-root
case,27720 in total. This includes incompatible and noncoherent layouts.

## Exact primal and dual witnesses

Each certificate row contains a rational supported probability mu and a
rational probability distribution lambda over valid complete test layouts.
The standard-library verifier checks every effective test layout and proves

    E_mu L_a^2 <= G for every a,
    sum_a lambda_a L_a(x)^2 >= G for every x in S.

The second inequality implies max_a E_nu L_a^2>=G for every supported
probability nu. Thus the two witnesses prove exact minimax equality.
Floating LP output is used only to discover a rational active basis; it
is not a verification input. The six exact minimax values are:

|15 root|45 point orbit|Exact Gamma45|
|---|---|---|
|short|same root|96103805/14524696|
|short|other root, same column|378110/57721|
|short|other root, other column|8717065/1336253|
|long|same root|151515/22868|
|long|other root, same column|22570/3361|
|long|other root, other column|172125/25943|

The largest is 22570/3361. The corresponding actual forbidden family
therefore proves sharpness of the universal 45 constant, as well as the
upper bound for every45 family.

## Prime7 extension retaining the selected head law

For each canonical case use its certified law mu45 and define

    R45=sum_{d in{3,9,5,15,45}} max_a mu45(x=a mod d).

Remove the pure7 class and let U6 be uniform on the six remaining 7 residues.
Write nu=mu45 x U6. Any complete 315 test load has the form

    L(x,z)=A(x)+sum_{d|45} 1_{x=b_d mod d}1_{z=c_d mod7},

where A is a complete 45 test load. Ignore any terms whose7 label is the
removed pure7 residue. Group the others by active7 colour as B_z(x), and
complete B=sum_z B_z to a complete 45 test load if any terms are absent.
Because B_z>=0, sum_z B_z^2 <= B^2. Thus

    E_nu L^2
      <= E_mu A^2 +(1/3)E_mu AB +(1/6)E_mu B^2
      <= (3/2)Gamma45(mu),

where Cauchy-Schwarz bounds E_mu AB by Gamma45(mu). This argument permits
independent old test residues for the0 and1 powers of7 and arbitrary7
colours; it does not assume product or coherent test layouts.

Each original mixed 7 class has exactly one original old divisor label
among3,9,5,15,45. Its nu-mass is at most one sixth of the corresponding
cylinder cap, so their union has mass M<=R45/6. Condition nu once on the
actual complete 315 survivors. For every complete test load L>=1,

    E_nu[L^2 | good]
      <= (E_nu L^2-M)/(1-M)
      <= 1+((3/2)Gamma45(mu)-1)/(1-R45/6).

This is a law on the actual original survivors, common to every test
layout. Completing and pruning the original 45 head at the start may only
shrink the final survivor set, so the law remains valid for the original
315 family, including missing or redundant original classes.

The exact pairs(R45, lifted bound) for the six laws are

    10069783/7262348, 844794679/67008610;
    74384/57721, 1664303/135971;
    1750389/1336253, 25567732/2089043;
    59395/45736, 2667875/215021;
    4547/3361, 198583/15619;
    103658/77829, 4543717/363316.

All R45 are below6. The largest lifted bound is198583/15619, attained
among these candidate laws by the long-root/same-column case. This does
not assert that the actual315 minimax value is that bound.

## Exact verification and scope

The [standard-library verifier](../docs/reports/erdos7-odd-covering/verify_finite_head_geometry.py)
reads the [fixed rational certificate](../docs/reports/erdos7-odd-covering/finite_head_geometry_certificate.json),
reconstructs the six actual survivor sets, and checks all 140 normalized
assignments, all 27720 independent test layouts, the primal and dual
probabilities, the same-law hinge profiles and all six prime-7 lifts.
`python3 -I -O docs/reports/erdos7-odd-covering/verify_finite_head_geometry.py`
passes using integer and rational arithmetic only. No optimization solver
or floating-point input is required for verification.

The repository's finite-head density and marked truncation bounds are in
[the Erdős #7 dossier](erdos-7-odd-covering-systems.md), (CM9)--(CM13).
The finite minimax statement was not found among those statements or in
the inspected public Hough minimum-modulus source
(DOI 10.4007/annals.2015.181.1.6). No literature-priority claim is made.
The symmetry reductions, probability-law construction and prime-7 lift
above are ordinary proofs with exact certificates; they are not
end-to-end Lean theorems. These results do not establish a continuation
from prime 11.
