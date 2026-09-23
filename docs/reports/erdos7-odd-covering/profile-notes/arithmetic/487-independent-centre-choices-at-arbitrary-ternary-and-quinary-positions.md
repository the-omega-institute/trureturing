# Independent centre choices at arbitrary ternary and quinary positions

Let P={3,5,7,11,13,17,19}. Consider a finite original family of congruence
classes with pairwise distinct odd numerical moduli m>1 supported on
P union{23,29}. Write each later modulus as d23^j29^k, j+k>0, with d
P-supported. Suppose two fixed integer centres a,b satisfy:

* at7,11,13,17,19 they agree through every exponent queried by the original
  later cofactors;
* each complete original later numerical label independently has old residue
  a mod d or b mod d, with its choice fixed throughout the original family.

There is no restriction on how the two centres agree or differ at3 and5.
Old-only classes, all23/29 phases, and all finite exponent heights are
arbitrary. No original shallow-anchor assumption is imposed. The actual
original survivor set has normalized Haar mass greater than1/80000000000.
In particular an integer remains uncovered.

Any finite set of further support primes greater than10000000000000 may
also be added. The centre condition applies only to the head-only subfamily;
all classes touching a further prime have arbitrary phases, heights and
joint support. The inherited continuation retains distorted mass greater
than1/125000000000, not a Haar bound of that size.

The new work closes the two mixed first-root regimes. Together with
[report485](485-independent-centre-choices-across-ternary-and-quinary-first-roots.md)
and [report486](486-independent-centre-choices-sharing-ternary-and-quinary-first-roots.md),
it permits arbitrary simultaneous disagreements in these two old coordinates.
It does not permit arbitrary disagreements in the other five coordinates
or independently unrelated old residues. Unrestricted Erdős#7 remains open.
The proofs and rational certificates are ordinary mathematics, not new Lean
certification or a literature-priority claim.

## One original family, one conditional source, and one global selector

Use the fixed-completion conditional process from
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
Its attribution to Michael Schroeder's *Nine Prime Divisors in Odd Distinct
Covering Systems*, edition1.0.1, and arbitrary-height verification boundary
remain in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).
The averaged completion law is not substituted for this conditional process.

Fix one actual complete source nu. Completion enlarges the old covered union,
so nu avoids all original old-only classes. Every later original label,
phase and choice between the two centres is unchanged. The source satisfies

    nu <= (27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5),
    m7=7235955529/450000000000,
    m_other=5891133457/225000000000.                         (M1)

The normalized caps hold at every complete earlier history. The source has
mass at least m7 on its worst coarse type(2,4,1), and at least m_other on
each other coarse type, retaining the32 source vertices and the same-budget
interpolation. Report485's all-depth comparison already gives original Haar
mass greater than1/1000000 on the seven nonworst types, for arbitrary3/5
separation depths. Only the worst type needs the new joint-anchor argument.

Let h3,h5 be the shared-prefix depths of the two fixed reference paths.
Zero means different first digits. Coincident paths have infinite depth.
Extensions of the finite queried reference prefixes are chosen once; this
does not require two different integers to be equal in a p-adic field.
The global A/B centre labels cannot be exchanged separately by coordinate,
point, fibre, or profile.

## Literal inventory bounds and independent support

For an old point x outside the null reference paths, let A_x,B_x be its two
matching old-cofactor inventories, including the unit. They are finite
seven-coordinate exponent boxes. Define

    Q_x=|A_x union B_x|,
    N_xy=sum_d max(1_Ax(d)+1_Ay(d),1_Bx(d)+1_By(d)).          (M2)

For each fixed new exponent pair(j,k), the same original selector applies
at x and y. Thus N_xy bounds their joint active inventory. It is a safe
upper capacity for the fixed selector, not permission to reselect phases.
Write the local3/5 factors as A3,A5,B3,B5 and the common five factors as f.
Then

    Q=[A3*A5+B3*B5-min(A3,B3)*min(A5,B5)] product(f).         (M3)

Let s(x) be the Haar survivor mass of the actual original23/29 fibre.
The existing axis and cross-class bounds give

    Q_x<=19 ==> s(x)>=1/77,
    s(x)+s(y)>=K(Q_x,Q_y,N_xy)/616.                         (M4)

Here K is exactly the individual-capacity rectangle optimizer of
[report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md).
Enlarging any of its three capacity bounds enlarges its feasible deletion
domain without changing the objective function, so K is nonincreasing.
The unit label supplies max(Q_x,Q_y)+1<=N_xy<=Q_x+Q_y.

Fix kappa with0<kappa<=16 and let T={x:s(x)<kappa/1232} on the actual old
live set. Its profile image excludes Q<=19 and contains no pair with
K>=kappa. This argument does not assume that s is constant on a profile:
if two profiles occurred in T, actual witnessing points would contradict M4.

Take upward closure under the FULL theoretical relation before selecting
sparse certificate edges. For a joint-anchor comparison, freeze the entire
3/5 profile and raise only the five common factors. For a pure comparison,
also raise each feasible3/5 joint valuation pair componentwise, for the same
fixed paths and separation depths. Both boxes grow, hence Q and N grow;
antitonicity preserves absence of all threshold edges. If ancestors coincide,
K(Q,Q,2Q)=0 for Q>=20. All Q>=39 profiles can be added without an edge, using
the witness K(20,39,40)=0 and the lower bound on N.

Denote this enlarged support by U. At each remaining prime p, reverse
integration of the actual conditional kernel on an increasing payoff is
bounded by the fixed positive comparison

    Jp(f=1)=1-Cp/p,
    Jp(f=t)=Cp(p-1)/p^t, t>=2.                              (M5)

Indeed E_K g<=g(0)+Cp E_H[g-g(0)]. Extend kernels by Haar on added histories
and release original deletion indicators only on the upper side. The result
is an auxiliary product comparison after the initial3/5 measure. No actual
independence of the source is asserted.

## Clique certificates for the low-survivor support

If C is a finite clique in the threshold graph K>=kappa, its indicator
variables for U satisfy

    sum_(v in C) z_v<=1.                                   (M6)

Every pair in C is checked; being a triangle in a drawn sparse graph is not
accepted without the three literal inventory inequalities. For nonnegative
clique multipliers lambda_C, let c_v=sum_(C containing v)lambda_C. Then

    comparison_mass(U)
      <=w_free+sum_C lambda_C+sum_v max(0,w_v-c_v).           (M7)

Multiply M6 by lambda_C, sum, and bound any unpaid vertex contribution by
its full mass. Edges are two-vertex cliques. The new(h3,h5)=(1,0) certificate
also uses346 triangles. M7 holds for the actual upward support; it does not
claim that every abstract sparse-graph independent set is realizable.

Any separately paid common-depth cylinder C_p is treated by the increasing
upper payoff max(1_U,1_Cp). That union need not be independent. Its cylinder
mass is paid in full, and the clique inequalities apply only to U outside
C_p. No certified row touches the cylinder. The exact free mass is

    total_comparison_mass
      -comparison_mass(outside C_p and Q<39).               (M8)

Thus all cylinder mass and the remaining overflow are counted once.

## The joint six-anchor calculations

Assume that every relevant first root survives the selected pure3 and pure5
classes. The finite reductions for excluded roots are given below. Normalize
the source, both references, and every original query simultaneously. Rooted
prime-prefix bijections preserve numerical labels, cylinders and shared
depths. The initial upper set is

    A6=(R1 times V5) union(R2 times W5),
    R1={x mod27:x=1 mod3,x!=1 mod9,x!=4 mod27},
    R2={x mod27:x=2 mod3},
    V5={y mod25:y!=0 mod5,y!=1 mod25},
    W5={y in V5:y!=2 mod5},
    H(A6)=221/675.                                         (M9)

It retains the joint mod15 exclusion. Its marginal measures are not
multiplied instead. Further initial exclusions are released only for an
upper bound; no45/75 phases or deeper pure exclusions are credited here.

For h3=0,h5>=1, one global exchange of A/B makes A lie in ternary root2 and
B in root1. The81 ordered prefixes modulo27, combined with80 quinary pairs
at h5=1, give6480 configurations and20 exact weight classes. At h5>=2 the
two references share one of20 nonzero prefixes modulo25, giving1620
configurations and16 classes. Their deeper shell law depends only on h5,
not on the particular deeper digits.

For h3=1,h5=0, there are108 ternary ordered prefix pairs in surviving common
roots and300 quinary ordered pairs in different nonzero roots. All32400
configurations give121 exact weight classes. Both A/B orientations occur.

The consumer obtains each weight by literal initial-cell integration and the
geometric shells within reference cells. A shared prefix of depth h has
joint valuation atoms

    (j,j),j<h: (p-1)/p^(j+1),
    (h,h): (p-2)/p^(h+1),
    (j,h),(h,j),j>h: (p-1)/p^(j+1) each.                    (M10)

It retains every possible profile with20<=Q<=38 and accounts for the full
geometric overflow. The new joint bounds are:

| h3 | h5 | Configurations/classes | Profiles | Clique rows | U |
| ---: | --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 6480/20 | 6377 | 1916 | 0.015326848926142387... |
| 0 | 2 | 1620/16 | 5397 | 1375 | 0.01460812499208575... |
| 0 | 3 | 1620/16 | 4982 | 1137 | 0.014511297942943603... |
| 0 | >=4, including infinity | 1620/16 | 4758 | 848 | 0.015020760170470437... |
| 1 | 0 | 32400/121 | 6377 | 2156 | 0.015884425761179852... |

The last row contains346 triangles and1810 edges; it checks2702 distinct
pair inequalities. Take kappa=1/3 for every row. All U are strictly below m7.
In the fourth row pay the entire common5^4 cylinder. Outside it both5
valuations coincide and are less than4, independently of every deeper split.
The3/5 profile is fixed during the later-five comparison, so M8 applies
uniformly even at infinite h5. No claim that the cylinder is graph-free is
needed. These joint calculations do not use a finite pure-release credit.

## The remaining opposite mixed depths use positive pure comparisons

Now h3>=2 and h5=0. The minimal joint valuation pair is(0,0) at both primes.
Subtract the completed disjoint pure3 mass1/2 and pure5 mass1/4 at this
minimal payoff. Nonnegative increasing payoffs give positive upper measures
with respective baseline weights

    2/3-1/2=1/6,
    3/5-1/4=7/20.                                         (M11)

Their total masses are1/2 and3/4; the ideal product has mass3/8. All actual
positions of the pure classes are covered by this inequality. No exclusion
is physically moved, and all mixed initial exclusions are released above.
The required upward closure includes the feasible3/5 joint valuation orders,
not only the last five coordinates.

For a finite upper comparison retain pure3 through12 and pure5 through8.
The released tails are paid by

    epsilon=1/(2*3^12)+1/(4*5^8)
           =1312691/830376562500.                          (M12)

As in report486, the exact product error is no greater than this sum for
payoffs in[0,1]. The original complete source and its mass lower bound are
unchanged; no finite truncation inherits that lower bound. All the following
U values include epsilon:

| h3 | h5 | Profiles | Edge rows | Minimum K | U after release |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 0 | 5397 | 1801 | 8/15 | 0.016051048726480707... |
| 3 | 0 | 4982 | 1437 | 1/3 | 0.014916459047309299... |
| 4 | 0 | 4758 | 1249 | 1/3 | 0.01465590753367749... |
| 5 | 0 | 4607 | 1170 | 1/3 | 0.01467137630375099... |
| >=6, including infinity | 0 | 4526 | 944 | 8/15 | 0.015353088969556497... |

Use each row's minimum K as kappa. For the last row, pay the entire common
3^6 cylinder, whose ideal product mass is(3/4)3^(-6)=1/972. Outside it the
ternary valuations coincide and are below6, independently of deeper splits.
M8 pays this cylinder in addition to the finite pure-tail error M12.
The cylinder may contain positive edges or Q<20 points. All sparse rows are
outside it. These generic bounds apply at every reference position and on
every source type, since every source has mass at least m7.

## Finite excluded-root reductions and exhaustive coverage

For joint-anchor cases, suppose one centre's first root is the selected
pure-p root, p=3 or5. Add that one class modulo p to the original finite
family if its numerical modulus is absent; otherwise completion retains
the original class. Remove every later class contained in it. This leaves
the augmented covered union unchanged.

If just one centre is in this root, every surviving label assigned to it
has p-free old cofactor. Change only its now-unused p-coordinate to agree
with the other centre through all needed depths. If both centres are in
the root, every surviving later cofactor is p-free, and both p-coordinates
may be chosen equal. Finite CRT realizes these changes while preserving
each centre's other queried coordinates and all surviving original phases.

The remaining centres differ only at the other exceptional coordinate.
[Report484](484-independent-centre-choices-with-one-arbitrary-old-coordinate.md)
therefore gives original Haar mass greater than1/80000000000 for this finite
augmented family. Its survivors are contained in the original survivors.
No finite-family theorem is applied to the countable auxiliary completion.

All h3,h5 in the nonnegative integers union{infinity} are now covered:

* h3=h5=0: report485;
* h3,h5>=1: report486;
* h3=0,h5>=1: the four joint rows above, with the excluded-root and nonworst
  reductions;
* h3>=1,h5=0: the remaining joint row and five pure rows, with the same
  reductions where needed.

For each new row, outside T the actual fibre has s>=kappa/1232. Therefore

    H(original survivors)>=(nu(1)-nu(T))*kappa/16632.        (M13)

The denominator includes the original density cap27/2. Every new row gives
a Haar lower bound greater than1/2000000000; the least new value is

    0.0000000009252027922029506... .                        (M14)

Full fractions are retained and compared exactly. The inherited485 and
excluded-root floors give the weaker uniform1/80000000000 across every
case. A positive cell in the original finite CRT period gives an uncovered
integer. All numerical labels and original selectors have remained fixed.

## Tail continuation and exact replay

Restrict unnormalized Haar to the full original head survivor set, with
mass greater than1/80000000000 and density at most1. Resolve any extra head
digits needed by later classes without adding their projected exclusions.
Chapter33's existing estimate applies with

    B=10^13, ell=27, 3^ell<=B,
    c=(2ell^2+1)/(2ell^2-1)=1459/1457,
    M2=product_(p in P union{23,29})p(p+1)/(p-1)^2
      =14003665/540672,
    tau7=(c^7/B)(B/(B-3))^2
          sum_(j=0,...,7)7!/[(7-j)!ell^j].                  (M15)

Exact arithmetic gives1/80000000000-M2*tau7>1/125000000000. Each tail-touching
original class is charged once at its last exposed outside prime, with all
earlier exponents and its original phase retained. This proves the stated
distorted-mass continuation under the inherited analytic prime-product bound.

The [standalone consumer](../../frontier/cover-geometry/mixed_first_root_centres.py)
reads [ten sparse certificates](../../frontier/cover-geometry/mixed_first_root_centres_certificate.json)
and compares the reconstructed [exact result](../../frontier/cover-geometry/mixed_first_root_centres.json).

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_first_root_centres.py
```

Default execution reads adjacent inputs and writes nothing; `--output PATH`
writes the reconstructed result. The consumer regenerates all profile
universes, all actual shallow reference classes and geometric masses. It
checks14033 clique rows, including346 triangles, and14579 distinct pair edges
counted separately by regime, using313 distinct capacity triples. It checks
all pure releases, deep-cylinder payments, inherited result identities,
original Haar conversions and tail arithmetic. Its imports use only the
standard library and the existing canonical pair/source validator; no
scratch producer, graph or optimizer is imported.

The completed source construction, continuous-budget interpolation, full
threshold-graph upward closure, clique-support reasoning, positive pure
comparison, finite excluded-root reductions, prior485/486 scope and analytic
tail estimate remain ordinary mathematical arguments or attributed inputs.
No new Lean certification is asserted. The five common old-coordinate
conditions remain essential to the present statement.
