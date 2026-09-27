# All split/common patterns after the 3/5 first-root split force the same six shallow classes

This is an ordinary source argument with exact rational arithmetic, not a new
Lean theorem or an unrestricted Erdős#7 settlement. It extends
[report488](488-all-seven-first-root-splits-force-six-shallow-moduli.md) from
five additional first-root splits to all32 choices of split/common status at
7,11,13,17,19. The two required first-root splits at3 and5 remain assumptions.

## Statement on the original finite family

Let P={3,5,7,11,13,17,19}. Consider one finite family of congruence classes
with pairwise distinct odd numerical moduli greater than1, supported on
P union{23,29}. Original old-only classes and all finite heights and23/29
phases are arbitrary. Each complete original later label

    m=d*23^j*29^k, j+k>0,

has its old residue fixed to one of two global references A or B modulo d.
The choice belongs to the complete original numerical label; it may depend
on(j,k), but never on the tested point, coordinate or subsequent estimate.
Assume A and B differ modulo3 and modulo5. Fix any subset

    S subset{7,11,13,17,19}.

At each p in S the references differ modulo p. At each remaining p they
agree modulo p^H_p, where H_p is the largest old p-exponent queried by any
original later class. If H_p=0 this agreement imposes no condition. These
are finite queried-prefix conditions, not equality of two distinct integers
as p-adic numbers. Extend the unused reference digits once, with a common
path at each p outside S union{3,5}. Such extensions do not change any
original later residue or selector. The conclusions below hold uniformly
for all32 subsets S and all original finite heights.

If the original six shallow numerical labels3,5,9,15,25,27 are not all present
with actual classes which admit a simultaneous prime-prefix relabeling to

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15,             (M1)

the ORIGINAL full head survivor set has Haar mass strictly greater than
1/2000000. In particular this family is not a cover. Presence of M1 is only
a necessary condition left by this result; it does not assert a cover exists.
The more general sufficient condition for the same lower bound is existence
of a legal old-only completion of any coarse type other than(2,4,1).

One may also include arbitrary original classes touching any finite set of
further primes greater than100000000. Their phases, finite exponents and
joint prime occurrences are unrestricted. The head-only subfamily must
satisfy the preceding hypotheses. The inherited tail construction retains
distorted survivor mass greater than1/20000000. This last bound is not a Haar
bound of that size. Intermediate prime supports other than the stated head
and primes above the cutoff are not included.

## One completed source, with its own mass and geometry

Use the inherited selected old completion and complete conditional process
of reports467/488. The source is Michael Schroeder, Nine Prime Divisors in
Odd Distinct Covering Systems, edition1.0.1; retain the [library entry](../../../../../Library/Arith/schroeder2026nine.md)'s
attribution, archive identity and arbitrary-height verification boundary. Completion only enlarges the old covered set. No original later
label or selector is replaced by a favorable new one.

The normalized selected six cylinders for coarse type

    t=(alpha,beta,gamma), alpha in{1,2}, beta in{2,4}, gamma in{1,2},

are

    0 mod3, 1 mod9, beta mod27,
    0 mod5, gamma mod25, alpha mod15.                           (M2)

There are six cylinders and eight possible coarse types. Normalize every
original class, the two references and the source simultaneously. Globally
exchange A/B once to place A in ternary root2 and B in root1. In this first
step suppose both references avoid the selected pure3 and5 roots; a finite
same-source reduction below removes this restriction.

Write

    R_r={x mod27:x=r mod3,x!=1 mod9,x!=beta},
    V_r={y mod25:y!=0 mod5,y!=gamma,
                         not(r=alpha and y=alpha mod5)}.

The enlarged joint initial Haar chart is

    A_t=(R_1 times V_1) union(R_2 times V_2).                    (M3)

The script verifies M3 against the literal complement of M2 at all675
residues. It does not form an independent product of3 and5 marginals.
The actual source nu_t satisfies, on its own complete process,

    nu_t(1)>=m_t,
    nu_t <= (27/2) H_old,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).                  (M4)

The conditional caps hold at every full earlier history of the normalized
construction kernels. They do not describe retrospective conditioning on
final survival. The mass m_t is the minimum of that type's four retained
vertices of the common pure5 budget; the existing concavity controls the
continuous budget. The initial chart is an upper enlargement of this same
source, not a different measure to which m_t is transferred.

## Literal divisor inventory for split and common coordinates

For x outside the null reference paths, at each split coordinate let

    a_p=vp(x_p-A_p)+1, b_p=vp(x_p-B_p)+1.

Its factor pair is(1,1),(f,1),or(1,f), f>=2. At a common coordinate the pair
is(f_p,f_p), where f_p=vp(x_p-A_p)+1. Define

    a=product_(p in{3,5} union S) a_p,
    b=product_(p in{3,5} union S) b_p,
    c=product_(p in P \ ({3,5} union S)) f_p.

The two labelled old divisor boxes have sizes ac and bc. Their intersection
has size c, since all split-coordinate exponents in the intersection must
be zero, whereas all common exponents remain available. Thus their union is

    Q=c(a+b-1).                                                (M5)

This is an upper inventory for the actual original cofactors, with their
original globally fixed selectors. At every fixed new exponent pair there
are at most Q active original old numerical labels. No class may choose
its centre separately at different points to attain this upper bound.
Reference paths have Haar measure zero and also nu_t-measure zero by M4.
Assigning them to BAD does not alter any mass estimate.

Set BAD={Q>=20}. On its complement, the actual original23/29 fibre survivor
fraction s(x) obeys the established two-prime union bound

    s(x)>=(1-19/22)(1-19/28)-19/616=1/77.                       (M6)

The d=1 old cofactor is retained, including for mixed new-prime classes.
The selected source is supported outside every original old-only class.

## Full-history comparison and exact infinite-tail evaluation

At a split prime p>=7 use the positive auxiliary probability law

    J_p(1,1)=1-2C_p/p,
    J_p(f,1)=J_p(1,f)=C_p(p-1)/p^f, f>=2.                     (M7)

At a common prime use the diagonal probability law

    J_p(1,1)=1-C_p/p,
    J_p(f,f)=C_p(p-1)/p^f, f>=2.                              (M8)

All baselines are nonnegative and the geometric tails make each law sum to1.
For any increasing local payoff h, its minimum is h_0 at(1,1), and the
actual normalized kernel K_p with Haar density at most C_p satisfies

    E_Kp h=h_0+E_Kp(h-h_0)
          <=h_0+C_p E_H(h-h_0)=E_Jp h.

The BAD indicator is increasing in each paired factor. Reverse integration
against fixed future J laws preserves this monotonicity. Release extra
selected exclusions on the upper side; extend newly admitted histories by
Haar where needed. Applying the last inequality at each full earlier history
therefore proves

    nu_t(BAD)<=B_t,S(A3,B3,A5,B5),                             (M9)

where B is the mass under H restricted to M3 and the five auxiliary laws.
The factorization belongs only to this upper comparator. No independence
or Markov assertion about the actual complete source is made.

The consumer evaluates the GOOD probability by backward rational recursion.
Its state(a,b,c) is the current split-A, split-B and common product. It is
absorbing BAD as soon as c(a+b-1)>19. At a split prime it multiplies a or b
by f; at a common prime it multiplies c by f. Only factors that can remain
GOOD are retained. This is exact because every later factor is at least1.
After integrating the joint initial3/5 shell law, BAD is the full chart mass
minus GOOD. Every initial and later infinite geometric tail is therefore
paid; no finite-source support assumption is made.

A separate forward calculation instead constructs a distribution of the
three later multipliers, then integrates it against the initial shell law.
The backward and forward constructions agree on every scalar bound and
reference multiplicity. An independent reconstruction from literal CRT
cells and cylinder-intersection differences checks the anchor partition.

Each coarse type has24300 ordered shallow reference configurations. Their
exact weight signatures give30,66,20,44,66,30,44,20 classes in lexicographic
type order. For each of32 subsets the script checks all320 classes, with
276 belonging to the seven nonworst types. Consequently the claimed bound
checks8832 nonworst classes representing5443200 ordered configurations.
Unqueried deeper reference digits do not change the exact shell laws.

The largest BAD over S and shallow references for each nonworst source is:

| Type | Classes per subset | Maximum BAD20, display only | Own source lower mass |
| --- | ---: | ---: | --- |
| (1,2,1) | 30 | 0.025730767024606603 | 3553359811/90000000000 |
| (1,2,2) | 66 | 0.025472584372440942 | 41366399129/1350000000000 |
| (1,4,1) | 20 | 0.025789481522897933 | 22645899553/675000000000 |
| (1,4,2) | 44 | 0.025545673196412284 | 5891133457/225000000000 |
| (2,2,1) | 66 | 0.025350197175025523 | 7360457957/270000000000 |
| (2,2,2) | 30 | 0.025622410300335880 | 6790631/175781250 |
| (2,4,2) | 20 | 0.025573455421369710 | 11886359579/450000000000 |

Every bound is compared to its OWN source mass before taking a minimum.
The smallest reserve is type(1,4,2), S={11,13}, references(2,7,3,4):

    Delta=25389916561652657732698099354371465892842880496100838122817322996942725616568398683241621
          /39849687927688826533580707419103065240382866617170573342124515914768315030926953125000000000
         =0.0006371421680321602... .

This gives uniformly on all nonworst types and all32 subsets

    nu_t(GOOD)>=m_t-B_t,S>=Delta,
    H(original head survivors)>=Delta/[(27/2)*77]
                               =6.129313785783166e-7...
                               >1/2000000.                  (M10)

The source with the largest BAD is different from the source attaining
Delta. M10 does not mix independently optimized source quantities.

The script retains the worst type(2,4,1) too, without claiming it passes.
For S={7}, all44 of its fractions agree with an independent backward
recursion. Many such worst-type scalar bounds fail; this does not refute
noncoverage. The present theorem leaves that source type unresolved except
where other separately established results apply.

## Deleted3/5 roots: a finite reduction preserving the SAME subset S

Fix the same completed old family and same source just used. At p=3 or5,
if a reference lies in the selected pure first root C_p, insert that selected
class into the original family only if numerical modulus p is absent. If
p was already present, completion retained its actual class, so there is no
duplicate modulus. At most one reference lies in C_p because these two
coordinates have first-root splits.

Delete every later original class choosing that reference whose old
cofactor is divisible by p. Such classes are contained in C_p and redundant
in the augmented union. Every remaining later label choosing that reference
is p-free. Replace its unused p-coordinate with a first digit outside C_p
and different from the other reference's digit. At3 the third-root argument
gives exactly one such surviving digit; at5 at least three are available.

Keep all other original queried reference prefixes. At every split prime
also keep at least the first digit even if no original query uses it. At
nonsplit primes keep the common original queried prefixes and choose a fixed
common extension. Thus every p in S remains first-root split and every other
later p remains common through the relevant original heights. Finite CRT
realizes all retained original queried prefixes by two fixed integer
representatives. Infinite common path extensions are only auxiliary charts;
they are not a demand that these two distinct integers coincide p-adically.

If both3 and5 require replacement, make both redundant deletions first,
then one CRT choice. Every remaining later numerical label preserves its
actual old residue and its original global selector. The selected old
completion already contains the added roots, so the same source, coarse
type, caps and lower mass still apply. No favorable source is substituted.
The augmented union contains the original union, and deleting redundant
classes leaves it unchanged. Thus its survivor set is contained in the
original survivor set. Apply M10 to the augmented family to get M10 for the
original family, now without the surviving-root restriction.

## Missing or redundant shallow classes force a nonworst completion

This step concerns only the old-only family and is independent of S. The
source's Lemma2.2 completes selected moduli in increasing numerical order.
A missing class can be placed at any residue avoiding previously selected
proper-divisor classes. If a present class meets a selected proper-divisor
class, it is contained in it, so that present class is redundant and can
be moved to a free residue while only enlarging the covered union.
The relevant selected proper-divisor lists are

    9:{3}; 15:{3,5}; 25:{5}; 27:{3,9}.

Other selected moduli create no additional forbidden choice at these steps.
A nonworst completion is obtained by any of the following free choices:

* Missing15: choose its ternary root to match selected9, and a quinary root
  outside selected5. Then alpha=1.
* Missing27: choose the surviving ternary root different from selected9.
  Then beta=2.
* Missing25: place it in selected15's quinary root. Then gamma=alpha, which
  also excludes(2,4,1).
* Missing3 or5 with15 present: insert that pure root to contain the original
 15 class. At step15 this now-redundant class can be moved to alpha=1.
* Missing9 with15 present: if15 is already redundant under selected3 or5,
  choose any free9 and then move15 to alpha=1. Otherwise choose9 in the
  original15 ternary root. This root survives selected3;15 is then retained
  with alpha=1.

If several shallow labels are absent, first use an applicable15,27,25 case;
otherwise the3,5,9 cases have15 present as required. Continue all later
selected choices under Lemma2.2 before constructing the source. No original
later class, old residue or selector changes during this completion.

The same freedom applies when an original shallow class is present but
redundant: move15 for alpha=1,27 for beta=2, or25 for gamma=alpha. If9 lies
inside selected3, move9 into original15's surviving ternary root unless15
is itself already redundant, in which case move15 instead. Hence if no
nonworst completion is available, all six original labels must be present
and their actual classes retained. Their normalized type must be(2,4,1),
which says: the15 ternary root differs from9's,27 shares9's ternary root
but uses another depth-two child, and25 has a quinary root distinct from
both5 and15. Simultaneous prime-prefix permutations carry precisely this
layout to M1; a further child permutation puts25 at1 mod25 without moving
5 or15.

All original queries and both references undergo the same prefix relabeling.
Such relabeling preserves equality of queried prefixes and inequality of
first roots. It therefore preserves every given split/common subset S.
The source completion argument and the deleted-root reduction are separate:
choose the nonworst completed family first, construct its own source, and
then reduce any reference lying in its deleted3/5 root. No mass or cap is
transferred between completions. This proves the opening necessary-layout
statement uniformly over all32 S.

## Tail continuation, with an explicit change of seed

Use unnormalized Haar restricted to the FULL ORIGINAL head survivors as
new seed. It has mass greater than1/2000000 and density at most1. Lift it
uniformly to all head heights appearing in the original tail-touching
labels; this adds no projected exclusions. Do not normalize this seed and
do not retain27/2 as its density cap.

[Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)'s
inherited analytic estimate applies with

    B=100000000, ell=16, 3^ell=43046721<=B,
    c=(2ell^2+1)/(2ell^2-1)=513/511,
    M2=product_(p in P union{23,29}) p(p+1)/(p-1)^2
      =14003665/540672,
    tau7=c^7/B*[B/(B-3)]^2
           *sum_(j=0,...,7) 7!/[(7-j)! ell^j].

The exact tail loss bound is

    M2*tau7=477215784096120508930940488250478515625
             /1074580189805606506781993092717995070110826496
            =4.440950881315332e-7... .

Consequently

    1/2000000-M2*tau7
      =938661106354417882188375907945609678600207
         /16790315465712601668468642073718672970481664000000
      =5.590491186846679e-8... >1/20000000.                    (M11)

Each tail-touching original numerical label is charged once at its last
exposed tail prime. Earlier exponents, all phases and full earlier histories
are retained. Normalized cap2 kernels preserve the full earlier measure;
finally delete the actual union. The number of such primes and their
simultaneous occurrences in one original modulus are arbitrary but finite.
The head split/common constraint is not imposed on these tail classes.
Positive remaining distorted mass gives an uncovered original finite CRT
residue, hence an uncovered integer. The prime-product analytic premise
is inherited, not proved by the exact rational evaluation M11.

## Verification and remaining scope

The [consumer](../../frontier/cover-geometry/mixed_split_common_source_types.py)
reconstructs the [exact result](../../frontier/cover-geometry/mixed_split_common_source_types.json)
using the standard library and adjacent canonical source/anchor helpers.
It imports no scratch producer, optimizer or saved multiplier graph.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_common_source_types.py

Default execution compares the adjacent result; --output writes a
reconstruction. Explicit exceptions keep checks active under -O. The exact
checks cover32 source vertices, eight literal joint anchors and their320
weight classes, all32 split/common subsets,10240 scalar bounds including
all8832 nonworst inequalities, and the strict Haar/tail conversions.
Decimals in the table are displays; all comparisons use rational values.

The fixed actual source, continuous-budget interpolation, complete-history
comparison, legal completion, finite deleted-root transport and analytic
tail estimate remain ordinary arguments or inherited inputs. Lean and source
producers are not rerun. The complete worst source type, a positive common
prefix followed by separation, unrelated old residues and unrestricted
Erdős#7 remain outside this theorem. Separately proved endpoints do not
supply the missing mixed worst-source cases.
