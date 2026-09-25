# Staged payment admits every two-parent entry from prime37

Keep the head-only original restrictions of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md)
and the private-branch decomposition of
[Report600](600-two-head-coordinates-admit-unbounded-large-prime-entries.md).
Every Type II entry prime may now be any q>=37, with any two distinct
head parents. In particular, entries37,41,43,47 may all use a parent
pair containing3. The proportion of complete head configurations
admitting a simultaneous avoiding extension is greater than1/65000.

There is no bound on the finite number of entries, private blocks,
their depth, or original heights. All original numerical moduli remain
distinct and all residues remain globally fixed. The result transports
to any ten ordered odd head primes that are the ten smallest primes
in the family. It retains Report600's disjoint private interiors and
its restrictions on originals crossing the head/private boundary.

The improvement pays blockers on two different boundaries of one
construction. Blockers depending only on the first seven head
coordinates are removed before the three remaining head primes are
processed. The other blockers are paid afterward. No source is
optimized separately for different queries or original phases.

This is ordinary mathematics with exact rational certificates, not
new Lean verification or a resolution of unrestricted Erdős #7.

## Original family and the two blocker groups

First use the reference head

    P0={3,5,7,11,13,17,19}, P1={23,29,31}, P=P0 union P1.

Pure powers and all head originals touching P1 are unrestricted.
A mixed original supported on P0 must have some exponent at least
three, or exponents at most one at3 and5, or at least five prime
divisors. These are exactly Report598's conditions.

Type I branches meet P in one prime and obey Report599's ordinary
block-tree conditions. A Type II branch has one entry prime q and
two declared head parents p,r. Its head-touching originals are

    p^a r^b q^e, a,b>=0, a+b>0, e>=1.

Behind q its private original family is an allowed ordinary block
tree rooted at q. There is no deeper contact with P. All private
interiors are pairwise disjoint, and no additional original joins
different private interiors. Parent pairs may coincide or overlap.
The private blocks and separate components have exactly the scopes
specified in Report600: at most twelve vertices, simple cycles, or
oriented larger blocks with k>=4 children and smallest child
s>=k(k+3)+3.

Let V_q be the actual private entry domain of Report600, including
pure-q originals and the entire private block tree. Let B_q be the
set of complete parent pairs having no avoiding entry word in V_q
after imposing that branch's head-touching originals. Both objects
come from the same original family at its full resolving heights.

Call B_q early when both parents lie in P0, and late otherwise.
An early blocker is a set on P0 alone; its definition does not use
the eventual P1 coordinates. A late parent pair, in increasing
order, is coordinatewise at least(3,23).

## One complete-label fee for each actual blocker

For a reference pair a<b let d_1,d_2,... be the increasing nonunit
a,b-smooth labels. Define

    C_(a,b)=a/(a-1) b/(b-1),
    T_(a,b)(N)=C_(a,b)-1-sum_(j<=N)1/d_j,
    F_(a,b)(q)=min_(0<=N<q-3) T_(a,b)(N)/(q-3-N).
                                                        (SP1)

Report600's actual parent-label conditioning proves

    (H_p times H_r)(B_q)<=F_(a,b)(q)              (SP2)

whenever the actual ordered pair(p,r) is coordinatewise at least(a,b).
The selected reference exponent patterns are used on the actual
parents. Each selected parent label retains every original q-height;
no child exponent, original residue or numerical identity is merged.

Put

    S35=sum_(q>=37 prime)F_(3,5)(q),
    S323=sum_(q>=37 prime)F_(3,23)(q).

The exact finite calculations and analytic tails below establish

    S35<1/2600, S323<1/125000.                    (SP3)

These bounds pay any finite subset of entries. Although the early
and late groups have disjoint entry primes, it is harmless to bound
each group by its entire positive series. No simultaneous worst-case
attainment or independence of blocker events is assumed.

## Remove early blockers on the seven-coordinate query law

At every finite resolving height, Report598 supplies one actual
submeasure eta on P0, supported on its head-only survivor, with

    eta<=rho=product_(p in P0)rho_p,
    eta(1)-c Gamma_Q(eta)>=K,
    c=1084133/201247200,
    K=26345885990886052732242307711
       /9055182074115772514304000000000.          (SP4)

Gamma_Q is the complete squared-query moment with the unit query
included and one globally fixed layout per maximization. Original
and query heights are not truncated. The underlying coordinate laws
satisfy

    rho_3<=2H_3,
    rho_p<=p/(p-2)H_p for p>=5,
    rho<=D H_(P0), D=3458/405.                   (SP5)

Consequently every pair marginal of rho on P0 is bounded by
(10/3) times product Haar: the largest coordinate-density product
is2*(5/3). The pair marginal of eta need not be independent.

Let E be the union of the early blockers, pulled back to P0, and
delta=eta(E). By SP2, eta<=rho and one union bound,

    delta<=(10/3)S35<1/780.                      (SP6)

Restrict eta'=eta outside E. Every complete query load L is at
least1, so for this same query layout

    integral L^2 d eta'<=integral L^2 d eta-delta.

Taking the maximum over the unchanged set of layouts gives

    Gamma_Q(eta')<=Gamma_Q(eta)-delta,
    eta'(1)-c Gamma_Q(eta')
      >=K-(1-c)delta>K-(1-c)/780>0.              (SP7)

This restriction lemma applies to any event E. It does not require
E to be one original cylinder or one of the labels in the old
head theorem. Here E is determined at the full finite heights of
the actual private branches and parent words. Choose the resolving
height before applying SP4; higher query heights retain the same
restriction and estimate.

## Continue the same restricted source and pay late blockers

Apply the existing23,29,31 capped-deletion construction to eta',
with the unchanged controls2/5,9/20,1/2. All original classes
assigned to these three head primes remain unrestricted. The
construction is performed afresh on eta'; it does not reuse kernels
chosen for an earlier, differently normalized source.

Each extension retains its seven-coordinate starting word, so the
extended physical law still avoids E. Restrict it to the complete
head survivor to obtain a submeasure supported outside E and every
head original. The continuation estimate and its density multiplier
200/33 then give an actual set U_* of complete head words, all
early-good, with

    H_P(U_*)>=33/(200D)[K-(1-c)(10/3)S35]
      >33/(200D)[K-(1-c)/780]
      =14799217832760926534994307711
       /468579418066477236879360000000000
      >1/32000.                                 (SP8)

Now take mu=H_P restricted to U_*. This is one unnormalized actual
measure with mu<=H_P. Its joint marginal on any parent pair is
therefore dominated by product Haar on that pair. Pay every late
blocker using SP2 with reference(3,23), for total loss at most S323.

Pay Type I branches by Report599's unchanged total fee2^-17.
Private descendants of Type II entries have already been incorporated
in their V_q and are not charged again. On this same mu, one union
bound leaves

    H_P(U_ext)>1/32000-1/125000-2^-17
      =31991/2048000000>1/65000.                 (SP9)

Choose one complete head word in U_ext. Every early branch has an
avoiding entry extension because it avoided E; every late branch
has one because its full pair blocker was deleted. Each selected
entry word extends through its private domain V_q. The Type I
branches also extend. Their private interiors are disjoint and have
no additional cross-branch originals, so all witnesses glue.
Separate components use their ordinary block-domain induction.
CRT supplies an integer avoiding the entire original family.

If Q_off is the product of all original prime powers outside the
head, including separate components, the full survivor density is
greater than1/(65000 Q_off). The head bound1/65000 is not asserted
as a uniform full-density bound.

## Transport the extension predicate while leaving private primes fixed

For ten arbitrary ordered actual odd head primes, use Report592's
finite digitwise shifted injections on the ten head coordinates
only, from the reference primes3,...,31. Leave every outside prime
coordinate unchanged. Outside primes are at least37, and the numeric
minimum-child conditions of private blocks consequently stay intact.

For each fixed injection, a target original pulls back either to the
empty set or to one cylinder with the same exponent vector and prime
support. Distinct numerical moduli remain distinct. The head-only
restriction and every declared branch interface are preserved; an
empty pullback only removes a constraint. In particular the actual
private V_q is unchanged, since no private coordinate is transported.

Every extendible source head word maps to an extendible target head
word: keep its avoiding private witness, and use the defining
pullback relation for each original. Hence the inverse image of the
target extension set contains the source extension set. The source
extension set has Haar mass greater than1/65000 by SP9 for every
fixed injection.

For each source head word, averaging its independently shifted
digit images gives uniform target-head Haar. Averaging the preceding
set inclusion transfers the same head lower bound. This transports
the extension predicate itself; it does not assert that the complete
query moment or its optimizing law is invariant under injection.

## Exact fee sums and the unbounded tail

For each of(3,5) and(3,23), the producer evaluates SP1 exactly at
all152 primes37<=q<=967. It enumerates the smallest parent labels
by a priority queue and independently verifies that prefix by an
exponent grid. All148 existing(3,5) rows from Report600 agree.

For n>=22 and odd q in

    2n^2+3<=q<=2(n+1)^2+1,

choose the parent rectangle0<=i,j<n, excluding the unit. Its
N=n^2-1 labels have reciprocal remainder

    T<=C_(a,b)(a^-n+b^-n-(ab)^-n)
      <=2 C_(a,b)3^-n,
    q-3-N>=n^2+1.

The N smallest labels have no larger remainder. There are2n+1
odd integers in the interval. Since(2n+1)/(n^2+1)<=3/n, summing
the geometric series gives

    sum_(q>=971 prime)F_(a,b)(q)
      <=9 C_(a,b)/(22*3^22).                     (SP10)

This is5/204558018192 for(3,5) and23/1125069100056 for(3,23).
Together with the exact finite rows, the respective total upper
bounds are approximately0.000384043178344069 and0.00000768707935452530,
strictly below the rational thresholds in SP3. The producer retains
the exact fractions; displayed decimals are not the proof inputs.

The [producer](../../frontier/cover-geometry/staged_two_parent_attachment.py)
and [data](../../frontier/cover-geometry/staged_two_parent_attachment.json)
check the inherited source fingerprints, all finite parent-tail
identities, the infinite-tail constants, pair-density bound and
the simultaneous positive reserve. No inherited full head scan is
repeated. The source, restriction, continuation and transport
arguments above supply the mathematical quantifiers beyond these
arithmetic checks.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/staged_two_parent_attachment.py

The remaining413 low-support central-square labels, originals
joining private branches, and recursively shared two-coordinate
separators remain outside this theorem. The choice of an earlier
payment boundary removes an entry-prime restriction; it does not
remove those joint-constraint gaps.
