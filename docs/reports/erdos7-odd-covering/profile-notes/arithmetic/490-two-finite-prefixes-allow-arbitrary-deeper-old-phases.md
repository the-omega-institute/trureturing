# Two finite prefixes allow arbitrary deeper old phases

Only finite old prefixes need to lie at the two first-root-separated centres;
every deeper old residue may vary independently with the full original label.
There is no bound on the number of distinct deeper old phases. This extends
[report489](489-independent-centre-choices-across-all-seven-first-roots.md)'s
exact two-centre conclusion while retaining its original Haar bound and
large-prime continuation.

Let P={3,5,7,11,13,17,19}, set

    (h3,h5,h7,h11,h13,h17,h19)=(23,16,13,11,10,9,9),
    D=product_(p in P)p^hp,

and fix integers A,B with A!=B mod p for every p in P. Consider any finite
original family of congruence classes c_m mod m, with pairwise distinct odd
numerical moduli greater than one, supported on P union{23,29}. For each
complete original later label m=d23^j29^k, j+k>0, require a fixed choice
sigma_m in{A,B} such that

    c_m=sigma_m mod gcd(d,D).                                (P1)

Every full label makes its choice once. Its remaining old digits, its23/29
phases and all finite heights are arbitrary. Old-only original classes are
also arbitrary. Then the original survivor set has normalized Haar mass

    H(U_original)>1/1000000000.                              (P2)

Any finite set of additional support primes greater than100000000000 may be
included, with arbitrary phases, heights and joint support on tail-touching
classes. Only the head-only subfamily must satisfy P1. The enlarged family
has distorted survivor mass greater than1/2000000000, not a Haar bound of
that size. Both families are therefore noncovering.

The proof is an ordinary finite-carrier set comparison and exact arithmetic,
not new Lean certification or an unrestricted Erdős#7 result. It inherits
report489's actual-source theorem and its attributed Schroeder inputs; see
the [library entry](../../../../../Library/Arith/schroeder2026nine.md) for the
source edition, archive identity and verification boundary. This is a new
application of the existing phase/cylinder comparison method, not a claim
of a new general continuity theorem.

## One reference family on the same finite Haar carrier

Keep every original old-only class. For each later full numerical label m,
form exactly one reference class by CRT, specifying

    cbar_m=sigma_m mod d,
    cbar_m=c_m mod 23^j29^k.                                 (P3)

The two CRT factors are coprime, so this determines one residue modulo m.
Every original numerical label remains distinct and appears once; all new
coordinate phases and the one fixed selector per full label are preserved.
The reference family satisfies report489's exact two-centre hypothesis.

Work on one finite CRT carrier resolving all original moduli and every
prefix p^hp. Uniform lifting of the original or reference period preserves
its Haar survivor fraction. There is no law selected separately for each
test, and no identification of either survivor set with an auxiliary
comparison support.

Report489's full uniform quantitative bound is

    H(U_reference)>=a=(m7-Umax)/49896
      =1.171290574577427e-9... >11/10000000000.               (P4)

This stronger a applies to every completed source type. The worst type gives
P4 directly; the other seven have the larger bound1/400000, and the same-source
deleted-root reduction preserves the lower bound by survivor inclusion.
The present argument uses this actual original-family Haar conclusion,
not the auxiliary product measure used to prove it.

## All changed classes are confined to one fixed prefix neighbourhood

For p in P and sigma in{A,B}, let

    E_(p,sigma)={x:x_p=sigma mod p^hp},
    E=union_(p,sigma)E_(p,sigma).                             (P5)

Fix x outside E and one original later label, and write e=vp(d). If some
e>=hp, neither its actual nor reference class is active at x: P1 and P3
force any active point into E_(p,sigma_m). If all e<hp, P1 fixes every old
coordinate of c_m modulo d to sigma_m, so its actual old residue already
equals the reference residue. The23/29 residues agree by P3. Thus the two
class indicators agree at x in either case.

Old-only classes were unchanged. Applying this argument to every fixed full
label gives the exact set relation

    U_original symmetric_difference U_reference subset E.   (P6)

In particular U_reference minus E is a subset of U_original. There is no
assertion of a global covered-set inclusion between the two families.

Since A and B differ in the first digit at every old prime and hp>=1, the
two p-cylinders are disjoint. Under this one full Haar carrier the different
prime coordinates are independent. Hence

    H(E)=delta(h)=1-product_(p in P)(1-2/p^hp)
      <=sum_(p in P)2/p^hp.                                  (P7)

Independence in P7 is only that of full CRT Haar. No independence of the
source-conditioned survivor law is used. This common neighbourhood charges
all changed labels together; its cost is not multiplied by the number of
classes, their heights or their distinct deeper phases.

For arbitrary positive prefix heights the general quantitative conclusion is

    H(U_original)>=a-delta(h).                               (P8)

For the displayed heights, exact rational arithmetic gives

    sum_p 2/p^hp=9.957419448418714e-11... <1/10000000000,
    delta(h)=9.957419448004546e-11...,
    a-delta(h)=1.0717163800973814e-9... >1/1000000000.         (P9)

This proves P2 at every original finite height. Nothing in the argument
chooses a new phase after observing x.

## The allowed old residues need not fit any two complete centres

For any N choose t with3^t>=N and let d=D*3^t. At distinct full labels
d23^j choose N different old residues A+iD modulo d,0<=i<N, and at one
further label choose B mod d. Each of the first N residues has the same
required A prefix modulo D; the last has the B prefix. All23-coordinate
phases can be fixed arbitrarily by CRT.

There are at least N distinct old residues at the same old cofactor d, so
for N>2 no two complete old centres can represent this family. The B prefix
also prevents replacing P1 by a single common prefix. This exhibits the
scope difference from the exact two-centre premise and from report480's
single-prefix theorem; it is not a separate covering counterexample.

## Large-prime continuation and verification

After proving P2, take Haar restricted to the complete actual original head
survivor set as a new unnormalized seed. Its density is at most one and its
mass is greater than10^-9. Resolve all extra head digits queried by any
tail-touching original class by uniform lifting, without adding its head
projection as a new head exclusion.

The same Chapter33 calculation as report489 applies with

    B=100000000000, ell=23, c=1059/1057,
    M2=14003665/540672,
    tau7=c^7/B * [B/(B-3)]^2
      *sum_(j=0,...,7)7!/[(7-j)!ell^j].

It retains

    1/1000000000-M2*tau7
      =6.314001148070581e-10... >1/2000000000.                (P10)

Each original tail label is assigned once to its last exposed outside prime,
with its full earlier cofactor and fixed phase. The analytic prime-product
estimate and conditional continuation are inherited ordinary inputs.

The [standard-library consumer](../../frontier/cover-geometry/two_finite_prefix_phase_freedom.py)
reads the pinned exact report489 result and reconstructs the
[result data](../../frontier/cover-geometry/two_finite_prefix_phase_freedom.json).
It checks P4, all seven cylinder charges, their exact union measure, P9,
the nonworst lower-bound comparison and P10 using rational numbers.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_finite_prefix_phase_freedom.py

Default execution compares the adjacent result; --output writes a
reconstruction. Checks remain active under -O. The CRT construction and
P6 are ordinary arguments above; the prior pair certificates and Lean are
not rerun. The remaining shallow two-prefix restriction is substantial:
arbitrary unrelated shallow residues and unrestricted Erdős#7 remain open.
