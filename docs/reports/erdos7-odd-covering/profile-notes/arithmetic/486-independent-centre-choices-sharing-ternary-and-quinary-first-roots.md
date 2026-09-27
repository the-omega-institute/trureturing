# Independent centre choices sharing ternary and quinary first roots

Let P={3,5,7,11,13,17,19}. Consider a finite family of congruence classes with
pairwise distinct odd numerical moduli m>1 supported on P union{23,29}. For
a later modulus m=d23^j29^k, j+k>0, let d denote its P-supported cofactor.
Suppose there are two fixed integer centres a,b such that:

* a=b mod3 and a=b mod5;
* at7,11,13,17,19 they agree through every exponent queried by the original
  later cofactors;
* each complete original later numerical label independently has old residue
  a mod d or b mod d, with its choice fixed throughout the family.

The centres may separate at any subsequent depth at3 and5. Old-only classes,
new-coordinate phases and all finite heights are arbitrary. No original
shallow-anchor assumption is imposed. The original survivor set has normalized
Haar mass greater than1/200000000, so an integer remains uncovered.

Any finite set of further support primes greater than10000000000 may also be
added. The centre restriction concerns only the head-only subfamily; phases,
heights and joint support of all classes touching the additional primes are
arbitrary. The continuation below retains distorted mass greater than
1/1000000000. This is not a Haar bound for the enlarged family.

This complements [report485](485-independent-centre-choices-across-ternary-and-quinary-first-roots.md),
which treats different first digits at both3 and5. Here both first digits
agree, and the later disagreements can occur independently at arbitrary
depths. The mixed situations in which exactly one first digit differs are
outside this statement unless another prior theorem applies. Unrestricted
Erdős#7 remains unresolved.

The deductions and rational certificates below are ordinary mathematics;
no new Lean certification or literature priority is claimed.

## Fixed original labels and a single complete source

Use the same fixed-completion conditional source as
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md),
with completion as in report466. Its attribution to Michael Schroeder's
*Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1, and
arbitrary-height limits remain in the
[library entry](../../../../../Library/Arith/schroeder2026nine.md).
The averaged compactness law is not substituted for the conditional source.

Fix one actual complete source nu. It avoids all original old-only classes
and satisfies

    nu <= (27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5),
    m7=7235955529/450000000000,
    m_other=5891133457/225000000000.

Every cap holds at every complete earlier history. Its mass is at least m7
on the worst coarse type(2,4,1), and at least m_other on each of the other
seven types. These bounds retain the same32 source vertices and continuous
budget interpolation as reports467 and485. Completion enlarges only the old
covered union; all original later labels, phases and centre choices remain
fixed.

Let h3,h5 be the shared prefix depths of the two reference paths. Both are
at least1. Every extension beyond the finite original queried prefixes is
fixed once. In particular a common extension can be used when two finite
queried prefixes agree; this is a statement about their unused reference
digits, not a requirement that two different integers be equal in one
p-adic field. Infinity denotes coincident reference paths.

The source may have countably many pure exclusions. Finite pure-prefix
comparisons below enlarge only its upper comparison, with explicit error;
they never receive the complete source's mass lower bound. All original
families and every later finite augmentation remain finite.

## Matching cofactor inventories and the pair inequality

For an old point x outside the null reference paths, let A_x and B_x be the
finite sets of old exponent vectors matching the two centres, including
the all-zero vector. Each is a seven-coordinate divisor box. Define

    Q_x=|A_x union B_x|,
    N_xy=sum_d max(1_Ax(d)+1_Ay(d),1_Bx(d)+1_By(d)).             (S1)

The sum is over the finite union of the four inventories. It is the largest
sum of active inventories at x and y allowed by choosing one globally fixed
centre for each complete label. The actual fixed selector can only decrease
it. This prevents centre choices from adapting to a point or support branch.

The union load can also be written

    Q_x=[A3*A5+B3*B5-min(A3,B3)*min(A5,B5)] product(f),          (S2)

where A3,B3,A5,B5 are the corresponding valuation factors v_p+1, and f
contains the five common-coordinate factors. The union intersection is
retained; separate coordinatewise maxima are not multiplied.

For Q_x<=19, the original23/29 fibre survivor mass s(x) has

    s(x)>=(1-19/22)(1-19/28)-19/616=1/77.                       (S3)

For two arbitrary profiles,
[report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)'s
individual axis and mixed-budget optimization gives

    s(x)+s(y)>=K(Q_x,Q_y,N_xy)/616.                            (S4)

Its exact rectangle-boundary calculation has at most28 rational candidates.
The checker reconstructs the literal seven-coordinate inventories for every
used edge, recomputes S1 and applies the existing canonical optimizer. It
checks max(Q_x,Q_y)+1<=N_xy<=Q_x+Q_y. The extra1 comes from the unit label,
which is compatible at both points.

Increasing any of Q_x,Q_y,N_xy enlarges the feasible deletion region and
does not change the survivor objective function, so K is nonincreasing
in those capacity bounds. This is the same K used in S4, not a different
relaxation.

## Which upward closure permits each comparison

Fix0<kappa<=16 and let T={x:s(x)<kappa/1232} on the actual old live set.
S3 excludes Q<=19. S4 excludes every pair in T with K>=kappa. This concerns
the full theoretical threshold graph, before selecting any sparse dual edges.

For the joint six-anchor calculation below, hold the complete3/5 profile
fixed and close T's profile image upward only in the five common-coordinate
factors. Both cofactor boxes then enlarge. The associated Q and N increase,
so antitonicity preserves absence of every threshold edge.

For the generic pure comparison, also close upward in each of the3/5 joint
valuation pairs, ordered componentwise among the pairs realizable by those
same fixed two paths at the same h3,h5. Global A/B labels remain unchanged.
Increasing either joint pair again enlarges both cofactor boxes. This extra
closure is necessary: closure in only the last five coordinates would not
justify subtracting pure mass at a minimal3/5 profile.

A collision of ancestor profiles causes no exception. At an identical profile
N=2Q and K(Q,Q,2Q)=0 for Q>=20. All Q>=39 profiles may also be added without
introducing threshold edges, by S1's lower bound on N and the zero witness
K(20,39,40)=0. Denote the resulting upward support by U. It excludes Q<20
and avoids the full threshold graph. Infinite valuations are null under
both Haar and nu by the density cap.

At each common later prime p, a normalized conditional kernel with density
at most Cp is dominated on increasing payoffs by the positive probability

    Jp(f=1)=1-Cp/p,
    Jp(f=t)=Cp(p-1)/p^t, t>=2.                                (S5)

For an increasing valuation payoff g this is the inequality

    E_K g <= g(0)+Cp E_H[g-g(0)]=E_Jp g.

Apply it backwards at every complete earlier history, extending kernels
by Haar on any added histories and releasing deletion indicators only on
the upper side. This produces a fixed product comparison after the initial
3/5 measure. It does not make the actual source independent or Markovian.

## Positive pure comparisons and their finite releases

For two paths at prime p sharing h>=1 digits, the Haar joint valuation atoms
are

    (j,j), j<h:      (p-1)/p^(j+1),
    (h,h):          (p-2)/p^(h+1),
    (j,h),(h,j),j>h: (p-1)/p^(j+1) each.                       (S6)

Their baseline valuation pair(0,0) is minimal. The completed disjoint pure3
and pure5 exclusions have masses1/2 and1/4. For any nonnegative increasing
payoff, removing these masses costs at least the mass times its baseline
payoff. Subtracting them entirely at that baseline therefore gives positive
upper comparison measures Jpure_3,Jpure_5, with baseline weights

    2/3-1/2=1/6,  4/5-1/4=11/20,

and total masses1/2,3/4. This is an inequality valid for all positions of
the selected pure cylinders, not a relocation of original classes. Positive
integration preserves monotonicity, so the two comparisons apply successively.
Release all mixed initial exclusions only on the upper side. The ideal
product comparison has total mass3/8.

For an explicit finite upper comparison, retain pure3 through H3=12 and
pure5 through H5=8. The released tails have exact masses

    epsilon3=1/(2*3^12), epsilon5=1/(4*5^8),
    epsilon=epsilon3+epsilon5=1312691/830376562500.              (S7)

The finite retained integral is bounded by Jpure_p plus epsilon_p at its
baseline. For a payoff in[0,1], the product error is at most

    (3/4)epsilon3+(1/2)epsilon5+epsilon3 epsilon5
       <=epsilon3+epsilon5.

Every generic upper bound below pays the full epsilon. The actual complete
source nu and its lower bound stay unchanged throughout.

## Four generic depth regimes

Retain every realizable full profile with20<=Q<=38. A local joint pair list
from S6 and the five common factors reconstructs the profile universe.
Each reference cell has its full geometric tail; every omitted Q>=39 point
is paid with payoff1.

For exact vertex masses w_v and nonnegative edge multipliers lambda_e, put
c_v=sum_(e incident v)lambda_e. The edge-free support U satisfies

    comparison_mass(U)
      <=w_free+sum_e lambda_e+sum_v max(0,w_v-c_v).             (S8)

This follows from z_i+z_j<=1 on each certified edge and z_v<=1. It is an
upper certificate, with no claim of dual optimality or realization of every
abstract independent support. Sparse edges are used after the full-graph
upward-closure argument.

Three certificates treat exact depths(1,2),(1,3),(2,1). For h3=1 and all
h5>=4, including infinity, let C5 be the common depth4 quinary cylinder.
Its Haar mass is1/625 and its ideal product-comparison mass is1/1250.
Outside C5 both quinary valuations are equal and less than4. Those shells
and their matching inventories are identical for every h5>=4.

Use max(1_U,1_C5) as an increasing upper payoff. This union need not be
edge-free: C5 may contain Q<20 points and positive-K pairs. Pay C5 in full,
and apply S8 only to U outside C5. The exact free mass is

    w_free=3/8-comparison_mass(outside C5 and Q<39).            (S9)

It counts all C5 and the remaining overflow once each. Vertex masses inside
C5 are zero, and no dual edge touches C5. This separate cylinder payment is
in addition to S7's released pure tails. The listed profile count uses the
h5=4 reference universe; its paid-cylinder vertices have zero weight.

The checker obtains the following upper bounds on nu(T), including epsilon:

| Depths(h3,h5) | Profiles | Positive edges | Upper after pure release |
| --- | ---: | ---: | ---: |
| (1,2) | 4378 | 836 | 0.015548254795812032... |
| (1,3) | 4163 | 680 | 0.015360040688306646... |
| (2,1) | 4378 | 837 | 0.014368322138422148... |
| (1,h5>=4), including infinity | 4051 | 473 | 0.015805247351526632... |

Each certificate has minimum used K=1/3, so T={s<1/3696}. Every displayed
upper is strictly below m7. The worst of their exact Haar bounds is

    (m7-U_worst)/49896
      =0.000000005504525894438874... >1/200000000.              (S10)

Decimals are for orientation; the full fractions are retained and compared
exactly. These generic bounds already work for any coarse source because
its mass is at least m7.

## The remaining shallow split uses the joint six-anchor measure

Only h3=h5=1 remains beyond the previously known deeper-prefix boxes. For
any nonworst source,
[report485](485-independent-centre-choices-across-ternary-and-quinary-first-roots.md)'s
all-depth nonworst argument gives original Haar mass greater than1/1000000.
It remains to treat the worst source.

First handle a shared first root inside a selected pure3 or pure5 exclusion.
Add that one selected class modulo p to the original finite family only if
its numerical modulus is absent. If present, completion retains it. Both
centres lie in the root, so every later class with p dividing d is now
redundant and can be removed without changing the augmented covered union.

Choose two integer centres by finite CRT that agree at p through all remaining
queried depths, while retaining each centre's queried prefixes at every
other coordinate. Their residues on all surviving later labels are unchanged.
Only the other one of3 or5 can now differ, and its first digit still agrees.
[Report478](478-independent-center-choices-with-one-varying-old-coordinate.md)
therefore gives Haar mass greater than1/15592500. Equivalently, the deleted3
case can force a common3 prefix of length3 and use report479, and the deleted5
case is report483's shared ternary-root branch. All these bounds exceed
1/200000000. The augmented family is finite, its removed classes are redundant,
and its survivors are contained in the original survivors.

We may now assume both shared first roots survive. Normalize the worst source
simultaneously with both references and the original later queries, as in
reports477 and485. The source avoids

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.

Rooted prime-prefix bijections preserve Haar, shared depths and congruence
cylinders. Release all further initial exclusions only on the upper side.
The resulting initial set is the joint measure

    A6=(R1 times V5) union(R2 times W5),
    R1={x mod27:x=1 mod3,x!=1 mod9,x!=4 mod27},
    R2={x mod27:x=2 mod3},
    V5={y mod25:y!=0 mod5,y!=1 mod25},
    W5={y in V5:y!=2 mod5},
    H(A6)=221/675.                                            (S11)

No45/75 phase is prescribed. Its two marginals are not multiplied in place
of the mixed joint constraint.

For a shared surviving ternary root and distinct second digits, there are
108 ordered pairs of prefixes modulo27. At5 there are80 ordered pairs of
prefixes modulo25 sharing a nonzero first root and differing at the second
digit. The product gives8640 configurations, including references lying inside
the selected9,27 or25 cylinder. Exact cell-by-cell shell distributions give
55 complete initial weight classes. The unobserved reference digits do not
change the geometric masses.

Close upward only in the five common later coordinates, as justified above.
There are560 possible local3/5 types capable of Q<=38, yielding4863 full
profiles of load20 through38. One1213-edge certificate serves every weight
class, with minimum used K=8/15. Thus T={s<1/2310}. Its complete overflow is

    221/675-comparison_mass(Q<39).

For every class the checker verifies conservation of its BAD mass, recalculates
all unpaid vertex mass in S8 and obtains

    U11=0.015311322303938224... <m7,
    H(original survivors)>=(m7-U11)*(8/15)/16632
      =0.000000024645787128982888... >1/200000000.               (S12)

No finite pure-release error is needed in S12: it uses the literal finite
six-anchor upper set, without crediting any deeper pure exclusion.

## Exhaustive depth coverage and the original conclusion

The following regimes exhaust h3,h5>=1:

* (1,1), handled by S11--S12 and the source/deleted-root cases;
* (1,2),(1,3),(1,h5>=4), handled by three generic certificates;
* (2,1), handled by the fourth generic certificate;
* h3>=2,h5>=2 or h3>=3,h5>=1, handled by
  [report479](479-independent-center-choices-with-simultaneous-coordinate-splits.md).

The last two alternatives include every remaining infinite-depth case.
Report479 permits simultaneous later splits at the other five coordinates,
so the common-coordinate hypothesis here satisfies its stronger conditions.
Its original Haar bound is greater than1/3222450. The inherited nonworst and
deleted-root bounds, the new joint bound and every generic bound including S7
are all strictly greater than1/200000000.

For each new certificate, the transfer uses the same actual source. Outside
T, s>=kappa/1232, so

    H(original survivors)>=(nu(1)-nu(T))*kappa/16632.           (S13)

Taking the minimum of the applicable routes proves the opening statement.
Positive Haar mass gives a nonempty cell in the original finite CRT period
and hence an uncovered integer. At no stage are original label choices
reselected by the point or profile.

## A large-prime continuation with the stronger seed

Restrict Haar to the full original head survivor set. Its mass is greater
than1/200000000 and its density at most1. Resolve any additional head digits
queried by later classes without adding their projections as head exclusions.
Apply the existing Chapter33 continuation with

    M2=14003665/540672,
    B=10000000000, ell=20,
    c=(2ell^2+1)/(2ell^2-1)=801/799,
    tau7=(c^7/B)(B/(B-3))^2
           sum_(j=0,...,7)7!/[(7-j)!ell^j].                   (S14)

The inherited analytic estimate requires B>=286,ell>=4 and3^ell<=B. All three
hold. Exact arithmetic verifies

    M2*tau7=0.000000003920370059069986...,
    1/200000000-M2*tau7
      =0.0000000010796299409300137... >1/1000000000.             (S15)

Every tail-touching original class is assigned once to its last exposed
outside prime, retaining its full earlier cofactor and original fixed phase.
The resulting positive distorted mass proves noncoverage. S15 is not a Haar
lower bound for the enlarged family.

## Verification and boundary

The [standalone checker](../../frontier/cover-geometry/shared_first_root_centres.py)
reads the [five certificates](../../frontier/cover-geometry/shared_first_root_centres_certificate.json)
and reconstructs the [exact result](../../frontier/cover-geometry/shared_first_root_centres.json).
Run from any working directory, using the full path if needed:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/shared_first_root_centres.py
```

Default execution compares the adjacent result without writing it;
`--output PATH` writes the reconstruction. The checker imports only the standard
library and the existing canonical pair/source verifier. It checks4039 edge
occurrences and168 distinct capacity triples, all five reconstructed profile
universes, the8640 joint configurations and55 classes, all geometric overflow,
the explicit finite pure-release error, the separately paid depth4 cylinder,
32 retained source vertices, inherited numerical-result identities, and the
Haar and tail arithmetic. No scratch graph or solver is imported.

The source construction, continuous-budget interpolation, simultaneous
normalization, report481's pair theorem and antitonicity, the two upward-closure
arguments, pure baseline comparison, finite deleted-root reduction, prior478,
479 and485 routes, and inherited analytic tail estimate remain ordinary
mathematical inputs or deductions. Their producers and Lean are not rerun.
The statement still requires common first digits at both3 and5 and common
queried coordinates at7,11,13,17,19. Arbitrary unrelated old residues and
unrestricted Erdős#7 remain unresolved.
