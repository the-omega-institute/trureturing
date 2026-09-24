# Fresh-prime root transport and two-copy reduction

A concrete conditional construction leads to a legal counterexample to
unrestricted Erdős #7: suppose a finite odd cover has s distinct classes
of modulus p, for an odd prime p and 2<=s<p, with all other moduli distinct and
greater than one. Put t=p−s>0. If an odd prime q divides no input modulus,
q != p, and q <= t+2, a finite cover with pairwise distinct odd moduli
greater than one can be constructed. The input has no height bound.

This is a sufficient condition, not an exhibited odd covering. No input
satisfying it is supplied. The result combines Harrington–Sun–Wong (HSW)
Lemma 5.4, a root-branch restriction, and a prime-flat extension of their
Theorem 3.2. The [source note](../../../../../Library/Arith/harrington2021oddcovering.md)
identifies the inspected primary version and the authors' original scopes.
The arguments below are ordinary proofs, not Lean verification.

The quantitative sections also give a common all-depth law for arbitrary
two-copy families on at most six odd primes excluding3. The
[direct capped construction](#a-direct-capped-law-improves-the-two-copy-query-and-density-bounds)
has a [joint pure-anchor estimate](#retaining-the-actual-pure-anchor-masses)
with query bound5.149795473527814... and density below88, both under one
law. Its source comparison and verification limits are specified below.

## 1. Replace one digit and retain the complete remaining coordinates

Let C be the original cover and M its period. Remove any non-p class
contained in one of the s pure-p classes. Denote the t remaining first
p digits by U. All p-free classes remain. For k=min(q,t), choose distinct
sigma(0),...,sigma(k−1) in U and distinct q digits beta(0),...,beta(k−1).

Keep every original p-free class unchanged. Retain a p-divisible class
a mod p^alpha r only if xi=a mod p equals some sigma(j). Here alpha>=1,
p does not divide r, and p^alpha r != p; r=1 is allowed when alpha>=2.
Replace it by the unique class of modulus

    q p^(alpha−1) r

with CRT conditions

    x = beta(j)       mod q,
    x = (a−xi)/p      mod p^(alpha−1),
    x = a             mod r.

All factors are pairwise coprime. The second condition removes only the
lowest p digit; retaining a itself as the high-digit residue would be
incorrect. Add one pure-q class for every q digit outside beta's image.

For an output integer x in branch beta(j), construct one original integer
y by prescribing y=sigma(j)+p x modulo the full original p power and
y=x modulo the full p-free part of M. Its original covering label is
neither a removed pure-p class nor a class in a discarded branch. If that
label is p-free, it covers x unchanged. Otherwise its transported CRT
class covers x. The added pure-q classes cover the remaining branches.
This proves whole coverage using the same original witness for every
membership test, rather than independent marginal choices.

Fresh q separates transported classes from unchanged p-free classes.
Within transported classes, (alpha−1,r) determines the unique original
modulus p^alpha r. No transported class has modulus q, since the original
modulus p was excluded. Thus the only possible repeated modulus is q,
used max(q−t,0) times. All moduli remain odd and nonunit. The q height is
one, the old p height decreases by at least one, and other heights do not
increase. Original primes may disappear upon branch deletion.

For q>=t this is HSW Lemma 5.4, pages 16–17, written with literal CRT
residues. For q<t the same proof selects q complete original root
branches; this selection is an additional elementary consequence. It
does not assume equal branch laws or identical inserted modulus sets.

If q<=t+1, there is at most one pure-q class, so the output is already
distinct. If q=t+2, the output is q-flat with exactly two pure-q classes;
the next construction removes their duplication.

### Retaining the digits of an already present q

For the direct q<=t+1 conclusion, freshness can be replaced by this
specific input condition: q!=p and every original modulus divisible by
q is also divisible by p. Thus every retained p-free label is q-free.
The original q height may be arbitrary.

Write a selected original modulus as p^alpha q^beta r, with alpha>=1,
beta>=0 and gcd(r,pq)=1. Instead of discarding its q digits, shift them
one position upward and put the new root b in the lowest position:

    x = (a−xi)/p            mod p^(alpha−1),
    x = b+q(a mod q^beta)   mod q^(beta+1),
    x = a                  mod r.

This is one class of modulus q m/p. Keep the p-free classes unchanged
and add the same q−k pure-q closing classes as before. If the original
period is p^H q^K R, with gcd(R,pq)=1, use the full output carrier
p^(H−1) q^(K+1) R, even when the natural output period is smaller.
On new root b, one original witness has old p coordinate xi+p x,
old q coordinate floor(x/q) modulo q^K, and unchanged R coordinate.
Here floor(x/q) uses a representative of x modulo q^(K+1). This is a
bijection from that new-root fibre onto the old xi-root fibre, and it
preserves the whole original event vector. The retained p-free classes
are unaffected precisely because they contain no q factor.

The modulus map m -> q m/p is injective on transported labels, and the
q factor separates them from all retained p-free labels. Again none
has modulus q, since the original modulus p is excluded. Consequently
q<=t+1 gives a distinct odd cover, with no fresh-prime requirement under
this additional input condition. The original q digits have been kept
as higher digits; original exponents and labels have not been identified.
This is a direct CRT extension, not a literal HSW lemma or a novelty claim.

When q=t+2 and q already occurred, the output need not be q-flat: an
old q^beta factor becomes q^(beta+1). The two-copy closing argument
below therefore cannot be applied without a separate premise. Precisely,
the output is q-flat if and only if every retained transported label
has beta=0. If all old q labels are deleted, that condition does hold;
presence in the original prime support alone does not decide it.

The input condition has a concrete role. A p-free original class
a mod q^beta r, beta>=1, pulls back on the k selected new roots to k
different classes of the same modulus q^(beta+1)r. For k>1, this alone
violates modulus distinctness. Even for k=1 it can collide with the
transport of an original class of modulus p q^beta r. This is an
obstruction to dropping the condition in this particular construction,
not a proof that every possible use of an old q must fail.

## 2. Two repeated prime classes with a prime-flat input

Assume a finite odd cover has exactly two distinct pure-p classes, all
other moduli distinct and nonunit, and no modulus divisible by p^2.
A permutation of first p digits sends the pure-p classes to 0 and 1.
On p-divisible classes this permutation changes only that digit; the
p-free coordinates remain fixed. It is a bijection of the whole CRT
period and preserves every modulus and covering membership.

Delete classes contained in those two pure branches. Write the remaining
p-free classes as a_j mod m_j, and the others as r_i mod p b_i, with
p not dividing b_i, b_i>1, and xi_i=r_i mod p in {2,...,p−1}.
The b_i are pairwise distinct, but may equal an m_j. For each xi, the
m_j classes and the b_i classes with xi_i=xi cover the p-free coordinate.

Choose a fresh odd prime ell. Output these four families:

1. p^h mod p^(h+1), for 0<=h<=ell−2.
2. c_j mod p^j ell, for 0<=j<=ell−1, where c_j=0 mod p^j and c_j=j mod ell.
3. Every original p-free class a_j mod m_j.
4. For every i and 0<=h<=ell−2, the class of modulus p^(h+1)b_i
   with residues xi_i p^h mod p^(h+1) and r_i mod b_i.

For x not divisible by p^(ell−1), let h<ell−1 be its p valuation. Its
first nonzero p digit is either 1, covered by family 1, or xi>=2. The
original restricted cover then supplies a label in family 3 or 4.
If p^(ell−1) divides x, family 2 with j=x mod ell covers x, since j<=ell−1.
This includes zero and does not assign it a finite valuation.

The four modulus types cannot collide: pure p; divisible by fresh ell;
p-free and ell-free; or positive p height with nonunit p-free, ell-free
cofactor b_i. In the last family (h,b_i) is unique. All output moduli
are odd and nonunit. If R is the lcm of the surviving m_j and b_i, the
output period is exactly p^(ell−1) ell R.

HSW Theorem 3.2, pages 7–8, states this implication for square-free input.
Its construction and the proof above use only p-flatness; other prime
heights can be arbitrary. This weaker sufficient premise is separately
justified here, not attributed as the theorem's literal statement. The
CRT families also explicitly include all endpoint indices and zero.

## 3. A finite search target and why known multiplicity bounds are insufficient

For p=3, a prime-flat input to section 2 exists exactly when some finite
period Q coprime to 6 admits a cover with at most two residues for each
nonunit divisor d of Q. Repeated identical residues may be removed.

Forward, restrict the input to x=3k+2. Each original modulus d or 3d
becomes one class mod d; no other 3 heights occur. Thus each d has at
most two residual residues. Backward, for one or two chosen residues
c mod d, put the first at 3c+2 mod d and the second, if present, at
3c+2 mod 3d. Add 0 and 1 mod 3. Original moduli are distinct except for
3, and the resulting cover is 3-flat. Section 2 applies.

For fixed Q this is a finite covering problem, with a choice of at most
two residues per nonunit divisor and a constraint at every point of
Z/QZ. There is no bound on Q here and no reduction from an arbitrary
hypothetical odd distinct cover to this restricted search target.

The inspected HSW constructions with p=7,t=3 (Figure 11) and p=11,t=4
(Figure 18) contain primes 3 and 5. Their p>=23,t=5 construction (Figure
23 and its subtrees) contains 3,5,7. In each case every odd prime <=t+2
is already in the input support. The reported p=3,t=1 case has only 3
as a candidate, which is its original root. None supplies the fresh
prime required above. The cited p=5,t=2 multiplicity bound alone does
not certify that 3 is absent. Nor does the reported double-3 cover
certify the absence of modulus factors 9; its specific earlier modulus
list is not inferred from that multiplicity statement.

### A two-copy seed coprime to 6 must use 5 or 7

A finite collection with moduli greater than one, each numerical modulus
used at most twice, cannot cover if its period Q is coprime to 210.
Consequently the coprime-to-6 search target above must have 5 or 7 as
a prime factor. This statement permits arbitrary prime-power heights.
The multiplicity bound counts labels per modulus, not the covering
multiplicity at an integer.

Use the unions B_i, fibre fractions alpha_i and common distorted laws P_i
of [BBMST](../../../../../Library/Arith/balister2018covering.md),
arXiv:1811.03547v1. Their measure construction, earlier-marginal
preservation, one-step mass loss (Lemma 3.3), and cylinder domination
(Lemma 3.4) depend on the actual unions and work with repeated labels.
For a label lambda in stage i, write d_lambda=m_lambda p_i^j_lambda.
The union bound gives

    alpha_i(x) <= sum_lambda p_i^(−j_lambda)
                    1[x=a_lambda mod m_lambda].

Expand its kth power over ordered original labels. Each compatible
intersection is one cylinder modulo lcm(m_1,...,m_k), bounded under the
same P_(i−1) by nu(lcm)/lcm, where
nu(d)=prod_(p_j|d)(1−delta_j)^(-1). There are at most 2^k label tuples
for each tuple of numerical moduli. Thus the proof of Lemma 3.6(15)
acquires one leading factor 2^k; no label independence is assumed.
Lemma 3.7 then gives the second-moment bound

    E_(i−1)[alpha_i^2] <= 4/(p_i−1)^2
      prod_(j<i, p_j|Q) [1+(3p_j−1)/((1−delta_j)(p_j−1)^2)].

The geometric sums over exponents retain all finite original heights.
Section 6 explicitly allows all-prime indexing, including absent primes,
and any initial constant kappa satisfying this moment bound. Since
gcd(Q,210)=1, its first four bad sets are empty: mu_4=1, kappa=4, f_4=4,
where mu_i=1−sum_(j<=i) P_j(B_j). Padding absent factors with the positive
Euler factors only enlarges the bound.

Set delta_i=1/4 for 5<=i<=39. Write

    a_i=(3p_i−1)/(p_i−1)^2,  b_i=1/[4(p_i−1)^2],  F_4=4,
    F_i=F_(i−1)(1+4a_i/3)/(1−16b_i F_(i−1)/3).

The [exact rational checker](../../frontier/cover-geometry/multiplicity_two_sieve.py)
checks all 35 denominators are positive. Lemma 6.2 then implies mu_i>0
and f_i<=F_i throughout. At p_39=167 it verifies

    F_39 < 59319/400 = 148.2975
         < 39(log39+loglog39−3)^2.

For the second strict inequality, the positive series
log x=2 sum_(j>=0) z^(2j+1)/(2j+1), z=(x−1)/(x+1), gives
log39>183/50 using 100 terms and log(183/50)>129/100 using 20 terms.
Both lower comparisons are checked rationally. The squared expression
is increasing on these positive arguments. No rounded Table 1 value
or floating-point decision is used.

Theorem 6.1 now continues every remaining stage with delta_i=1/2,
preserving positive mu and proving noncoverage. If Q ends before prime
167, append empty stages; the same positivity argument applies. This
uses the theorem through its stated moment hypothesis and the labelled
extension just proved. It is not a quotation of the distinct-modulus
scope of BBMST Theorem 7.1. The checker certifies the rational endpoint;
the measure transport and unrestricted tail are ordinary mathematical
arguments using the cited lemmas, not program or Lean certification.

### A quantitative common law for six-prime two-copy families

Let Q be a set of at most six odd primes, with 3 not in Q. Take any
finite family of nonunit Q-supported numerical moduli, each used at
most twice, with arbitrary fixed residues and arbitrary finite heights.
Let V be its complete survivor set in X_Q=product_(q in Q) Z_q, and
let H_Q be Haar probability. There is one probability nu with

    nu(V)=1,
    (1/10) H_Q|V <= nu <= Lambda2 H_Q,
    R_Q(nu):=sum_(d>1,Q-supported) max_a nu(a mod d)
             <=33748/3375<10,
    Lambda2=3037500000000/7235955529<420.                 (TC1)

In particular H_Q(V)>=1/Lambda2>1/420. The same law controls every
query depth and has full support on V. The multiplicity bound concerns
the input numerical labels, not the number of classes containing a point.
There is no bound on the number of moduli or on their prime-power heights.

The input is split once into two families A and B, each with distinct
numerical moduli; a modulus used only once can go in either family.
Write V_A for the A-survivor and V=V_A intersect V_B. The split and all
residues are fixed before the construction or any query. This result
uses the uniform seven-prime common law of
[report467](../arithmetic/467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md),
whose source attribution and verification limits remain in force. It is
an ordinary quantitative deduction, not new Lean verification or a
claim of literature priority. The root transport above alone does not
supply its common-law query estimate.
The qualitative noncoverage conclusion also follows from the earlier
prime-flat construction with a fresh prime at least43 and report467's
prime-gap theorem. The added result here is the simultaneous quantitative
query and density control on the original two-copy survivor.

For each integer H>=1, use the disjoint ternary cylinders

    A_i=(3^(i-1)-1) mod3^i,
    T_i=(2*3^(i-1)-1) mod3^i,  1<=i<=H,
    Z_H=(-1) mod3^H,   W_H=union_(i=1..H) T_i.

Together the A_i, T_i and Z_H partition Z_3. Keep each class of A at
its original modulus d. Add the pure class A_i at modulus3^i. For
each B-class b_d mod d and each i=1,...,H, add the CRT class with
modulus3^i d, ternary residue T_i and Q-residue b_d. Every new numerical
modulus is odd, greater than one and distinct: the pure labels, 3-free
labels and pairs(i,d) are separate, and 3 does not divide d. There are
|A|+H(1+|B|) original labels on at most seven primes. This is a finite
actual family for each H, even though H will later tend to infinity.

Its complete survivor is exactly

    U_H=(W_H times V) disjoint-union (Z_H times V_A).       (TC2)

On T_i, precisely the B-copy at level i is active; on Z_H none is
active. In both cases the original A-classes remain. Thus, with
h=H_Q(V) and h_A=H_Q(V_A),

    H_(3,Q)(U_H)=((1-3^-H)/2)h+3^-H h_A.                 (TC3)

Report467 gives, for each of these actual finite families, a single
all-depth law mu_H supported on U_H with

    R_(3,Q)(mu_H)<=C=70871/3375,
    (1/5) H_(3,Q)|U_H <= mu_H <= Lambda H_(3,Q),
    Lambda=6075000000000/7235955529.

These are simultaneous properties of the same law. Let z_H be its
mass on Z_H times V_A, and let eta_H be the Q-marginal of its restriction
to W_H times V. Each of the H queries (-1)mod3^i contains Z_H, so

    z_H<=min(C/H,Lambda*3^-H),    eta_H(1)=1-z_H,
    ((1-3^-H)/10) H_Q|V <= eta_H
          <= (Lambda/2)(1-3^-H) H_Q.                    (TC4)

The exponential bound on z_H is the same law's Haar-density bound on
Z_H times V_A; it does not require a separate source.

The query gain comes from the actual partition W_H, without a product
assumption on mu_H. For each fixed Q-supported d, including d=1, choose
a phase a attaining max_a eta_H(a mod d). At ternary exponent zero,
the corresponding mu_H cylinder has at least this mass. At positive
exponents choose the H cylinders T_i, joined to that same Q-phase.
They partition the restricted mass over a mod d. Consequently

    sum_(i>=0) max_(c mod3^i d) mu_H(c mod3^i d)
         >=2 max_a eta_H(a mod d).

The labels 3^i d are unique as(i,d) varies. Summing nonnegative terms,
and writing R_Q also for the homogeneous functional on subprobabilities,
gives

    1+C >=1+R_(3,Q)(mu_H)
          >=2[eta_H(1)+R_Q(eta_H)].                    (TC5)

Only the query phases are selected separately, as allowed in R; every
term is measured under the same mu_H. No independently maximizing
conditional laws or marginal products occur in this inequality.

Already H=16 gives a finite transfer below the clean targets. With
delta=Lambda*3^-16<1, normalize eta_16 once to get a probability on V.
Its query bound is at most(1+C)/[2(1-delta)]-1<10, and its density cap
is at most Lambda(1-3^-16)/[2(1-delta)]<420. Thus crossing these two
targets does not require the limiting construction. The limit below
also gives the sharper exact constants and lower density in(TC1).

Take a weakly convergent subsequence of the eta_H on the compact
space X_Q. Their masses tend to one by(TC4), so the limit nu is a
probability. V is clopen because the input family is finite; hence
nu(V)=1. The measure bounds in(TC4) pass to each finite cylinder
algebra and then to Borel sets, giving the two bounds in(TC1).
For every finite set of query labels, the sum of cylinder maxima is
continuous in these finite marginals. Applying(TC5), passing to the
limit and then exhausting all Q-supported labels yields

    R_Q(nu)<=(C-1)/2=33748/3375.

Thus the law, its support, its density bounds and all queries survive
one common limit. There is no assumption that the separately chosen
mu_H were already projectively compatible. In particular V cannot be
empty: otherwise eta_H(1)=0 would contradict(TC4) for H>C. Alternatively,
(TC3) and the common density upper bound already imply h>=2/Lambda by
letting H grow. This avoids using an assumed nonempty two-copy survivor
as an input to the construction.

For Q={5,7,11,13,17,19}, retain nu and append Haar coordinates23 and29.
Any additional finite family with distinct full numerical labels,
supported on Q union{23,29} and touching23 or29, has total forbidden
probability at most

    (1+R_Q(nu))[(23/22)(29/28)-1]
       <=(37123/3375)(51/616).

All later residues and heights are arbitrary; the old Q-only family
still has multiplicity at most two. The remaining probability is at
least61909/693000>5/56. Its full Haar survivor mass is greater than
1/4704, since the same product law has density at most Lambda2<420.
The unit old cofactor is included in37123/3375. This is a quantitative
continuation for the stated multiplicity class, not a claim that an
unrestricted original seven-prime family reduces to two Q-phases per
cofactor. Arbitrary ternary prefixes can activate more than two such
phases; the unrestricted seven-prime target565/51 remains open.

The same actual construction transfers a lower certificate back to
that target. Suppose, for a particular nonempty two-copy survivor V,
every probability supported on V has R_Q>=r, with r>=0. The stronger
upper bound(PA1) below rules out r>=6 on at most six odd support primes
excluding3; the conditional transfer remains valid. Put a=1+2r. For ANY probability mu on the
actual U_H in(TC2), let z be its Z_H mass and eta its restricted
W_H marginal. The spine queries give R_(3,Q)(mu)>=Hz. Keeping the
unit query's additional mass z in the argument for(TC5) gives

    1+R_(3,Q)(mu)>=z+2[eta(1)+R_Q(eta)]
                  >=z+2(1-z)(1+r),
    R_(3,Q)(mu)>=a(1-z).

For z=1 the last inequality is trivial; otherwise normalize eta once
and apply the assumed cofactor lower bound. Both inequalities concern
the same mu. Minimizing max(Hz,a(1-z)) over0<=z<=1 proves

    R_*(U_H)>=aH/(H+a),                                (TC6)

where R_* is the infimum over all supported probabilities. The argument
does not use the particular upper-bound laws from report467.
If r>257/51, any integer H>(565/51)a/(a-565/51) therefore produces an
actual distinct seven-prime family with R_*(U_H)>565/51. In particular,
an actual two-copy cofactor certificate r>=6 would suffice at H=75:

    R_*(U_75)>=975/88=565/51+5/4488.

A cofactor lower certificate can use finitely many fixed query labels
and phase weights, but it must hold throughout that family's complete
actual V. A desired abstract support or one chosen law with large R
does not meet the premise. The r>=6 example is excluded by(PA1).
Finding an actual cofactor lower certificate with257/51<r<=B_pure,
or a uniform bound ruling out that remaining interval, remains open.
Even a successful(TC6) counterexample
would refute the intermediate query target, not settle Erdős#7.

The [partial-comb checker](../../frontier/cover-geometry/two_copy_comb_transfer.py)
constructs the actual distinct CRT labels for supplied A,B and H,
compares their full survivor mask with(TC2), and verifies(TC3) and the
displayed rational constants. Its [retained controls](../../frontier/cover-geometry/two_copy_comb_transfer.json)
exercise different phases, missing labels and higher cofactor powers.
The arbitrary-height common-law deduction is the proof above; finite
controls do not prove its universal quantifiers. Default execution
checks the retained controls; `--input PATH --height H` checks another
finite two-list input within an explicit period cap. No source geometry
or Lean build is rerun.

## 4. Reciprocal mass is transported, not automatically decreased

After deleting pure-covered classes in section 1, let A be the reciprocal
sum of p-free labels and S that of the remaining p-divisible labels.
For q>=t, all t branches are retained, and the exact labelled excesses are

    H_in  = A + S − t/p,
    H_new = A + (p/q)S − t/q
          = (p/q)H_in + (1−p/q)A.

For q<t, use the actual selected-branch mass S_selected:

    H_new = A + (p/q)S_selected − 1.

More generally, put h_xi=A+p S_xi−1, where S_xi is the original
p-divisible reciprocal mass in the selected nonpure root xi. Each
restricted source is a whole cover, so h_xi>=0, and

    H_new = ((q−k)/q) A + (1/q) sum_(selected xi) h_xi.

This is the disintegration over the actual retained root branches.
If H_in is measured before deleting pure-covered redundant labels of
total mass D, replace H_in by H_in−D in the q>=t identity.

Neither formula supplies uniform strict descent. For section 2 put
A=sum_j 1/m_j and B=sum_i 1/b_i after deletion. Then

    H_out + 1 = A + (1+B)(1−p^(−(ell−1)))/(p−1)
                  + p(1−p^(−ell))/(ell(p−1)).

Writing H_0=2/p+A+B/p−1, as fresh ell tends to infinity,

    H_out -> (p H_0−A)/(p−1).

The t=p−2 restricted branch covers imply (p−2)A+B>=p−2, so this limit
is at least A/(p−1). It is not a general excess contraction. These
constructions do not supply an upper bound contradicting the early
original-overlap requirement in [report 347](347-original-overlap-leakage-gives-a-uniform-reciprocal-gap.md).
The new labels, prime buckets and division-minimal classes must all be
recomputed before applying that result; no killed-source transport is
asserted.

## 5. Reproducible construction checks

The [prime-flat constructor](../../frontier/cover-geometry/p_flat_constructor.py) implements
section 2 with an odd-only default and an explicit even-fixture option.
It checks the complete input and output periods, root normalization,
literal CRT conditions, original-label provenance, modulus distinctness,
the exact reciprocal identity, the output period and zero coverage.
Its finite-period cap rejects oversized inputs instead of claiming to
have checked them. The general quantifiers come from the proof above.

The retained validation fixtures use even cofactors, including higher
powers of 2 and removable redundant classes. They exercise the transport
without pretending to supply the unknown odd input. Invalid input
coverage, duplicate moduli, nonfresh primes, non-flat input and even
input through the odd-only interface are rejected.

The [fresh-root constructor](../../frontier/cover-geometry/fresh_root_constructor.py)
implements section 1 and checks every original event bit against its
transported event on a single common carrier, including conditional
fibre bijections and the complete joint event histogram. It retains
that carrier even when deleting a high branch reduces the natural
output period. Its scope includes q<t, q=t, q=t+1, q=t+2 and q>t+2;
only the displayed sufficient range promises at most two pure-q classes.

The [composition check](../../frontier/cover-geometry/fresh_root_composition_check.py)
runs both constructions on one actual even-cofactor input: periods
56 -> 40 -> 600, ending with 14 distinct moduli and exact reciprocal
excess 443/600. Copy it with its two sibling programs to reproduce it
outside the repository.

The installed prime-flat checks pass five fixtures, 25,356 complete
period points and seven rejection cases. The fresh-root checks pass
eleven fixtures, 85,938 input/output/common-carrier points, 11,626
conditional-source points and nine rejection cases. These include a
retained p^8 label, unequal p heights, an absent original p factor, and
nonzero deleted pure-root mass. The absent-factor case distinguishes
the auxiliary CRT root from the original prime support. All three
entrypoints pass under Python's isolated, no-site, optimized mode;
checks use explicit exceptions rather than optimization-sensitive asserts.

The [old-q memory constructor](../../frontier/cover-geometry/old_q_memory_construct.py)
checks the additional support condition and preserves the complete
conditional source law after shifting the old q digits. Its five
fixtures check 198,428 input/output/common-carrier points, 46,200
conditional-source points and 600,432 original event coordinates;
eleven invalid inputs are rejected. One two-copy output retains q^3
and is correctly ineligible for the prime-flat closer. Another deletes
all old q labels and remains eligible despite q appearing in the
original period. These are also complete even-cofactor fixtures.

The multiplicity-two endpoint program checks 35 rational continuation
steps and the two positive-series logarithm bounds. A separate
implementation also verifies 24 actual distortion stages on twelve
labelled families, including squared prime factors and identical-event
duplicates: 246,840 stage-period points and 1,920 ordered original-label
pairs. Those finite families do not replace the general moment proof.
All five retained entrypoints run from physically copied files in a
path containing spaces, with cwd `/` and flags `-I -S -O`; their output
is identical to the corresponding unoptimized run. No new Lean
declaration, build, deposit or freeze is claimed.

## A direct capped law improves the two-copy query and density bounds

For the same finite two-copy inputs as(TC1), there is one probability nu
on the complete actual survivor V satisfying, at every query depth,

    H_Q|V <= nu <= D H_Q,
    R_Q(nu) <= B,
    B=4202355486461552318913516091708511
      /454292557570043338374301941417550
      =9.250328706548595... <10,
    D=2432902419851904000/12671604668586341
      =191.99639536444926... <192.                       (CP1)

In particular H_Q(V)>1/192. Every nonunit numerical input label may
occur at most twice, with arbitrary fixed residues and arbitrary finite
heights. The query sum still uses one maximum per numerical query label.
The bound B is greater than37/4; rounding it down to9.25 is invalid.
These are simultaneous bounds for the direct law constructed below.
They improve(TC1)'s quantitative interface without using its comb limit.
The actual-family lower-certificate transfer(TC6) remains valid. The
joint pure-anchor estimate below further improves this same direct law
and excludes the proposed cofactor lower target6.

The proof applies the existing
[conditional convex comparison](../../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound),
source Proposition `prop:comparison`, to a fixed completed probability
process. That proposition allows arbitrary coordinate supports and
separately labelled phases. The actual subprobability construction,
two-copy charge and resulting constants below are ordinary mathematical
deductions. The source attribution and local verification boundary
remain in force; this is not new Lean verification or a claim of
literature priority.

### Actual survivors and a normalized comparison process

First take Q={5,7,11,13,17,19}. At the5/7 anchor start with Haar
restricted to the complete actual survivor V57. The two pure inventories
have surviving Haar product at least

    (1-2/(5-1))(1-2/(7-1))=1/3.

The mixed inventory has original Haar union mass at most
2/[(5-1)(7-1)]=1/12. Thus the initial subprobability lambda0 has mass
at least1/4 and density at most1. There is no normalization of the pure
survivors before this subtraction.

Assign each later original to its largest prime q. For every full old
history x, let G_q(x) be the q-adic set avoiding exactly these originals,
including the pure-q classes. Put g=H_q(G_q(x)) and use row density

    k_q(x,y)=min(C_q,1/g)*1_(y in G_q(x))  if g>0,
    k_q(x,y)=0                            if g=0,
    s_q(x)=integral k_q(x,y)dH_q(y)=min(1,C_q*g).         (CP2)

Use thresholds t=(2,2,4,4) and caps

    C_q=(q-1)/(q-1-2t_q)=(5/3,3/2,2,9/5).

Iterating these rows from lambda0 defines one subprobability lambda.
All rows use the fixed original phases. On a complete actual survivor,
every surviving row density is at least1. Consequently

    H_Q|V <= lambda <=9 H_Q,
    lambda is supported exactly on V.                  (CP3)

For comparison only, complete every row to a normalized row by

    ktilde=k+(1-s)(C-k)/(C-s).

Here C>1 and s<=1, so the denominator is positive. The added density
has integral1-s, and k<=ktilde<=C. Start this comparison process from
full independent5/7 Haar. Its prefix laws dominate the actual prefix
subprobabilities by positivity, and its coordinate cylinder probabilities
conditional on the entire preceding history are bounded by C_p/p^e.
This is one fixed comparison law before all queries. Its extra mass may
lie on forbidden points; it is never normalized as an actual survivor
or used to assert preservation of live-prefix marginals.

The cited comparison therefore gives, for every finite complete old
query L including the unit label and every t>=1,

    integral (L-t)_+ d lambda_old <= E(M_old-t)_+,
    M_old=product_(old p) N_p,
    Pr(N_p=1)=1-C_p/p,
    Pr(N_p=n)=C_p*(p-1)/p^n, n>=2,                     (CP4)

with C5=C7=1. Independence belongs only to the auxiliary N_p. Completing
finite exponent inventories by nonnegative terms is legitimate since
their full mean is product_p(1+C_p/(p-1))<infinity.

### Charge both original copies without duplicating final queries

For each current q exponent e, split its originals once into two slots,
each with at most one original for every old numerical cofactor d.
Complete each slot to an old query L_(e,j), including d=1 for pure-q
originals. Missing phases are introduced only into this upper bound;
neither the actual family nor the kernel is changed. All original
phases remain attached to their own full labels q^e d.

The actual forbidden fibre fraction b=1-g obeys

    b <= sum_(e>=1,j=1,2) q^(-e)L_(e,j).

The weights beta_(e,j)=(q-1)/(2q^e) sum to1. Since
1-s=C_q*(b-2t_q/(q-1))_+, Jensen followed by(CP4) gives the absolute
mass loss at this stage:

    lambda_old(1)-lambda_new(1)
      <= [2/(q-1-2t_q)] E(M_old-t_q)_+.                (CP5)

The same comparison process dominates the actual prefix in each use.
There is no intermediate normalization, no assumed product survivor
law and no separate query-dependent source choice. The factor two in
(CP5) pays original multiplicity; final query labels are not doubled.

Every hinge is computed with its entire upper tail:

    E(M-t)_+=EM-t+sum_(m<t)(t-m)Pr(M=m).

Only the below-threshold probabilities need finite enumeration. The four
exact charges are

| q | t_q | Mass-loss upper bound |
| --- | --- | --- |
| 11 | 2 | 121/2520 |
| 13 | 2 | 2243/31680 |
| 17 | 4 | 333667517919/9170313152000 |
| 19 | 4 | 4318028797945659/90107497031552000 |

Subtracting their sum from1/4 yields

    lambda(1)>=alpha
      =12671604668586341/270322491094656000 >3/64.       (CP6)

For the final product, EM=4851/2048 and

    Phi=E(M-6)_+
      =643630899537111875680668794873587
       /3230464203494254131772080313600000.

For every complete query L, use L-1<=5+(L-6)_+ to obtain

    lambda(L-1)<=5*lambda(1)+Phi.

Normalize this same lambda once. Then B=5+Phi/alpha and D=9/alpha
give(CP1). The lower density follows from(CP3) and lambda(1)<=1.
Maximizing each label in a finite query inventory, then exhausting those
inventories, establishes the all-depth bound for this one nu. The
actual kernels depend on only finitely many original digits and leave
Haar tails. The law is defined on the full adic product directly; no
query-specific finite-period laws or new limit construction are needed.

### Larger actual primes and later23/29 classes

For any six odd primes excluding3, order them as p1<...<p6. Then
p_i is at least the corresponding reference prime5,7,11,13,17,19.
Use the same thresholds at positions3,...,6 and the actual caps
C_i=(p_i-1)/(p_i-1-2t_i). These are at most the reference caps.
The actual anchor mass is at least1/4, each coefficient in(CP5) is no
larger, and all auxiliary tails C_i/p_i^e are bounded by the reference
tails. Increasing hinges and products are therefore dominated by the
same reference expectations. The density product is at most9. This
proves(CP1) with the unchanged constants. Pad a smaller support with
unused odd primes excluding3 and project the constructed law back;
support, both density inequalities and the query upper bound survive.

For the reference six primes, add any finite family of distinct full
labels supported on Q union{23,29}, each touching23 or29, with one fixed
arbitrary residue per new label. Tensor nu with23/29 Haar. A union bound
under this same law gives remaining probability at least

    1-(1+B)*[(23/22)(29/28)-1]
      =2491480306913842230405369189634217
       /16461424439008629202268823289012400 >3/20.

Its density is at most D<192, so the full actual Haar survivor has mass
greater than1/1280. Old Q-only labels retain the permitted multiplicity
two. This improves the earlier(TC5) continuation reserve for the same
class of inputs; it supplies neither an unrestricted seven-prime query
bound below565/51 nor a resolution of Erdős#7.

The [exact budget consumer](../../frontier/cover-geometry/two_copy_capped_query.py)
and [rational data](../../frontier/cover-geometry/two_copy_capped_query.json)
compute(CP5)–(CP6), the complete final hinge, both bounds in(CP1), and
the continuation reserve. The program accepts four alternative stage
thresholds and a query threshold, rejecting invalid caps or a schedule
without a positive certified mass. The query-threshold limit64 bounds
this calculator's finite work, not the theorem's original heights.
It does not enumerate original families or rerun source geometry.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_copy_capped_query.py
```

## Retaining the actual pure-anchor masses

The same direct law in(CP2)–(CP3), with the same stage thresholds and
caps, satisfies the stronger simultaneous bounds

    H_Q|V <= nu <= D_pure H_Q,
    R_Q(nu)<=B_pure,
    B_pure=28165018706892770299/5469152872511772242
          =5.149795473527814... <103/20<6,
    D_pure=663518841777792000/7575003978548161
          =87.59320043353472... <88.                   (PA1)

This holds for arbitrary finite two-copy inputs on at most six odd
support primes excluding3. No original modulus or phase is changed.
The improvement retains two actual pure-union masses in the comparison
instead of replacing the anchor comparison carrier by full Haar.
The kernel and its normalization are the same as in(CP1); this is a
stronger estimate on that law, with the same ordinary source-comparison
premise and no additional Lean verification.

### One joint anchor parameter for all charges and queries

For the reference first primes5,7 let u and v be the actual Haar masses
of their respective pure forbidden unions. Thus

    0<=u<=1/2,  0<=v<=1/3,
    w5=1-u, w7=1-v.

The initial full57 survivor restriction is dominated by the product
of these actual pure-survivor Haar restrictions, of total mass w5*w7.
Its own mass is at least w5*w7-1/12. For comparison, normalize each
pure-survivor restriction: its conditional cylinder bounds are
1/(w_p*p^e). Apply the same completed later kernels and the same
conditional comparison as in(CP4), then multiply by w5*w7.

Equivalently, each initial auxiliary coordinate has unnormalized masses

    pi_p(1)=w_p-1/p,
    pi_p(n)=(p-1)/p^n, n>=2,
    sum_n pi_p(n)=w_p,
    sum_n n*pi_p(n)=w_p+1/(p-1).                       (PA2)

These masses are nonnegative throughout the stated rectangle. The later
auxiliary coordinate probabilities remain exactly those of(CP4).
For their product M the total comparison mass is w5*w7, so its hinge is

    F_t(u,v)=integral (M-t)_+ d pi
       =integral M d pi-t*w5*w7
          +sum_(m<t)(t-m)pi(M=m).                     (PA3)

The subtraction is t*w5*w7, not t. Every geometric upper tail remains
in the full first moment. The earlier absolute stage charge(CP5) now
uses the corresponding prefix F_(t_q)(u,v). Consequently define

    alpha(u,v)=w5*w7-1/12
       -sum_q [2/(q-1-2t_q)] F_(t_q)^old(u,v),
    Phi(u,v)=F_3^final(u,v).                           (PA4)

The actual final lambda obeys lambda(1)>=alpha(u,v) and
lambda(L-1)<=2*lambda(1)+Phi(u,v) for every complete query L.
Both use the same actual pair(u,v), the same originals and the same
law. There is no independent selection of a denominator or numerator
at different anchor parameters.

### Four endpoints certify the entire parameter rectangle

For these fixed thresholds and caps, the auxiliary atom masses are
affine in each of u,v, and integration against the fixed hinge payoff
preserves this separate affinity. This does not assert that taking the
positive part of an arbitrary affine expression preserves affinity.
Thus each function in(PA3)–(PA4) is affine in u with v fixed and affine
in v with u fixed. All four corner alpha values are positive. Their minimum
and the maximum of2+Phi/alpha are both attained at(u,v)=(1/2,1/3), where

    alpha_pure=7575003978548161/73724315753088000,
    Phi_pure=22496082952171/69510823782400.              (PA5)

The four exact query bounds are

| u | v | 2+Phi(u,v)/alpha(u,v) |
| --- | --- | --- |
| 0 | 0 | 128000709329279979373/46421374761426808734 |
| 0 | 1/3 | 66583813686862230349/21826129079333125342 |
| 1/2 | 0 | 58202896526211567323/15699892412092326034 |
| 1/2 | 1/3 | 28165018706892770299/5469152872511772242 |

For completeness, the interpolation certificate is the four nonnegative
corner values of (B_pure-2)*alpha-Phi. Multilinear interpolation preserves
this inequality throughout the rectangle, as well as
alpha>=alpha_pure>0. Normalize the actual lambda once and use its raw
density bound9 to obtain(PA1), with D_pure=9/alpha_pure.
The lower density and all-depth argument are unchanged from(CP3)–(CP6).

For larger actual primes, their two pure masses lie within this same
rectangle. The actual mixed-anchor Haar bound is at most1/12, and their
positive-depth auxiliary tails are no larger than the reference tails,
with the same w5,w7 total masses. The later caps and charge coefficients
are no larger either. The earlier ordered-prime domination and padding
argument therefore proves(PA1) for the stated arbitrary support.

### Consequences for actual lower certificates and continuation

Since every actual V in this class admits a law with R<=B_pure<6,
no such V can have R>=6 for every supported law. This excludes the
specific cofactor premise used in the H=75 example of(TC6); it does not
invalidate that conditional inequality or refute Erdős#7.
The remaining interval for a successful(TC6) cofactor certificate is

    257/51 < r <= B_pure,
    B_pure-257/51
      =30843665816005819055/278926796498100384342>0.

Even at this upper endpoint, the strict(TC6) crossing requires

    H>3491654251175798175460/6168733163201163811
      =566.024523804...,

so H>=567 is necessary for that certificate. This bounds what(TC6)
alone can certify; it is not an upper bound on an actual comb's R_*.

For the reference six primes, arbitrary additional distinct full labels
touching23 or29 retain probability at least

    1-(1+B_pure)*51/616
      =1653655418917620031481/3368998169467251701072
      >49/100.

Together with the same-law density cap below88, this gives full Haar
survivor mass greater than49/8800>1/180. The original fixed phases,
full labels and permitted old multiplicity two are retained.

The existing [consumer](../../frontier/cover-geometry/two_copy_capped_query.py)
with `--joint-anchor` computes the four full prefix ledgers, their exact
tail hinges and the common bounds in
[these data](../../frontier/cover-geometry/two_copy_pure_anchor.json).
It is a numerical consumer of(PA2)–(PA4); the interpolation and actual
source comparison are the ordinary proof above. The earlier default
calculation remains available and keeps its original output contract.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_copy_capped_query.py --joint-anchor
```

## Necessary query carriers and actual pure labels for the remaining lower target

Let T=257/51. Consider a finite actual two-copy family supported within a
declared query-prime carrier Q of at most six odd primes excluding3,
and its complete actual survivor V. A lower certificate means

    R_Q(nu)>=r>T for every probability nu supported on V.       (NC1)

Queries include every nonunit Q-smooth numerical label, including labels
using primes absent from the original family. The following are necessary
conditions for(NC1); they do not construct such a certificate.

### The declared query carrier must be the first six primes excluding3

Apply the PA construction to Q23={5,7,11,13,17,23}, with the same
thresholds(2,2,4,4). The last cap becomes11/7 and the raw density cap
becomes55/7. All four corner masses are positive. The minimum mass and
maximum paired query ratio occur at(u,v)=(1/2,1/3), giving one law with

    alpha23=57867788809484161/516070210271616000,
    R_Q23(nu)<=B23=12527664922219194437/2661918285236271406
                   =4.706254505144301...,
    nu<=D23 H_Q23,
    D23=4054837366419840000/57867788809484161<71,
    T-B23=45202088272542835055/135757832547049841706>0. (NC2)

These four corners use only retained PA moments. Subtract the old
prefix hinge at4 divided by7 from the mass through17. For the final
query hinge, remove the N19 factor, whose mean and masses at1,2 are
11/10,86/95,162/1805; insert N23 with corresponding values
15/14,150/161,242/3703. The product mass W=w5*w7 stays unchanged, so
the new hinge remains mean-3W+2*pi(M=1)+pi(M=2).
The separate-affinity argument of(PA4)–(PA5) proves(NC2) throughout
the anchor rectangle. The actual law and original phases obey the
same conditional-comparison proof as before.

Any six-element Q other than{5,7,11,13,17,19} has sorted vector at
least(5,7,11,13,17,23). Ordered-prime domination gives R_Q<=B23.
If Q has at most five elements, extend it to six elements containing23,
apply this bound to the same family with free added coordinates, and
project back to the entire declared Q. Its cylinder probabilities are
preserved and its query sum can only decrease. Hence(NC1) requires

    Q={5,7,11,13,17,19}.                              (NC3)

If Q is defined as the original family's minimal prime support, this
also determines that support. For a fixed ambient Q, however,(NC3)
alone does not force every prime to occur in an original. Removing an
unused prime from the query carrier changes R_Q and cannot be used to
deduce an ambient query bound without paying for its queries.

### Actual pure-union deficits must lie in a strict joint region

For the remaining reference carrier, let u,v be the actual pure-5 and
pure-7 union masses used in(PA2), and put d5=1/2-u,d7=1/3-v.
The four stored PA corners give exactly

    G=(T-2)*alpha-Phi=-c+A*d5+B*d7+C*d5*d7,
    c=6168733163201163811/542935350932041267200,
    A=44887686823492905683/27146767546602063360,
    B=20281636668601030051/20313907687933516800,
    C=585035299774741193/203139076879335168.           (NC4)

All four coefficients are positive. If G>=0, the existing supported
law has R_Q<=T, contradicting(NC1). Thus that lower certificate requires

    0<=d5<c/A=6168733163201163811/897753736469858113660,
    0<=d7<(c-A*d5)/(B+C*d5),                         (NC5)

and in particular d5<0.006871297676195501... and
d7<c/B=67856064795212801921/5962801180568702834994
=0.011379897256400057.... The two separate cutoffs are weaker than
the joint inequality. Even G<0 only means this PA estimate does not
exclude the lower target; it is not a sufficient condition for(NC1).

### Missing numerical slots and overlap both consume the deficit

Let n_(p,e) in{0,1,2} count the actual pure classes at modulus p^e.
With O_p their reciprocal-density sum minus their actual union mass,

    d_p=sum_(e>=1)(2-n_(p,e))*p^(-e)+O_p,  O_p>=0.   (NC6)

The absent slots beyond the last original exponent are included only
in this nonnegative budget identity. A missing slot at exponent e
costs at least p^(-e). Since1/125>c/A and1/49>c/B,(NC1) therefore
requires exactly two actual classes at each numerical modulus

    5,25,125;  7,49.                                 (NC7)

The six listed5-power cylinders must be pairwise disjoint within the
5 coordinate; the four listed7-power cylinders must be pairwise
disjoint within the7 coordinate. Indeed, same-coordinate prime-power
cylinders are nested or disjoint. An overlap among the listed cylinders
costs at least1/125 or1/49 in O_p, already contradicting(NC5).
There is no claim of disjointness across the two prime coordinates.

If every pure-5 exponent is at most3 and every pure-7 exponent is at
most2, the absent tails give d5>=1/250 and d7>=1/147. Thus

    G>=142559617481812957/67164742018133760000>0.       (NC8)

Consequently(NC1) also requires a pure-5 exponent at least4 or a
pure-7 exponent at least3. This does not force the particular adjacent
numerical labels625 or343: a higher exponent can satisfy this height
requirement while either adjacent label remains absent.

### Every remaining prime must occur in an actual original

The distinction after(NC3) can be resolved for(NC1). Suppose some
p in{11,13,17,19} divides no original modulus, while the declared Q
remains{5,7,11,13,17,19}. Then the actual full survivor factors as
V=V0 times Z_p. On Q0=Q minus{p}, run the actual CP/PA construction
with that row omitted, keeping the thresholds and caps attached to
each retained numerical prime. The anchor is still the complete
actual5/7 survivor. All fixed phases and old-history conditional
kernels remain those of this one actual family.

Let F_t^old,p and F_t^final,p be the comparison hinges with auxiliary
N_p omitted. Write W=w5*w7 and define

    alpha_p=W-1/12
      -sum_(q in{11,13,17,19} minus{p})
          [2/(q-1-2t_q)] F_(t_q)^old,p,
    Phi_p=F_3^final,p,
    B_p=max_(four corners)(2+Phi_p/alpha_p).

Each corner alpha_p is positive, and alpha_p and Phi_p are separately
affine in u,v. The same paired-ratio interpolation therefore yields
one supported law nu0 with R_Q0(nu0)<=B_p, retaining the full upper
tails of all query depths. Before the single normalization, the actual
subprobability has density at most9/C_p.

Tensor this law with Haar on the genuinely free coordinate p.
For every numerical label d=d0*p^e, its maximum cylinder mass is
p^(-e) times the maximum nu0 mass at d0. Summing these nonnegative
terms, including the unit label, proves

    1+R_Q(nu0 tensor H_p)=p/(p-1)*(1+R_Q0(nu0)).      (NC9)

Thus the absent coordinate's full query contribution is paid, with
the following exact all-depth bounds under this one law:

| Absent original prime p | Ambient upper A_p=p/(p-1)*(1+B_p)-1 |
| --- | --- |
| 11 | 1149041533527211729/323118077234730780 <3.557 |
| 13 | 7868920623067191/2107622446128616 <3.734 |
| 17 | 60876513409633145/15274538565725856 <3.986 |
| 19 | 14601841547756567/3528135691190004 <4.139 |

Every A_p<T, contradicting(NC1). These bounds apply even if other
primes are also unused. Together with(NC7), they imply that(NC1)
requires every prime in{5,7,11,13,17,19} to divide at least one actual
original modulus. The family's minimal prime support therefore equals
the declared query carrier, not merely a subset of it.           (NC10)

The new corner hinges are recovered from the retained PA moments.
For an auxiliary factor, put a_j=C*(p-1)/p^j for j=2,3 and
a_1=1-C/p. Removing that factor gives
mean'=mean/(1+C/(p-1)), P1'=P1/a_1 and
Pj'=(Pj-P1'*a_j)/a_1 for j=2,3. This last formula is used only for
the prime product indices2,3. The needed old-prefix P3 is recovered
from F4-mean+4W-3P1-2P2. These operations omit the absent row and
recompute the remaining charges without enumerating original families.

The [deficit consumer](../../frontier/cover-geometry/two_copy_pure_deficit.py)
and [exact results](../../frontier/cover-geometry/two_copy_pure_deficit.json)
calculate(NC2),(NC4)–(NC10) from the retained PA ledger. The input is
bound to that ledger's SHA-256; an alternate input must have the same
bytes. The actual-label implications and carrier transport are the
ordinary arguments above, with no additional Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_copy_pure_deficit.py
```

## A lower witness must retain an almost untouched pure-5 root

Let A5 be the actual union of pure-5 original cylinders and put

    m5=max_(r mod5) H5((r mod5) minus A5).

If m5<=24/125, the unchanged CP/PA actual law has the sharper bounds

    R_Q(nu)<=B_root=1827949258812195759/365819281957539530
                   =4.996864159348399...<5<257/51,
    H_Q|V<=nu<=D_root H_Q,
    D_root=8617127815296000/101334981151673<86.         (RC1)

This applies to arbitrary finite two-copy originals on the reference
Q, without assuming the necessary conditions(NC7). The kernel and
normalization remain those of(CP2)–(CP3); only the auxiliary comparison
retains a smaller actual first-level cylinder cap.

### Retain the actual root cap in every charge and query

Set sigma=1/125. The normalized actual pure-5 survivor measure has
first-level cylinder probabilities at most(1/5-sigma)/w5 and, at each
depth e>=2, at most1/(w5*5^e). These are valid decreasing bounds in
[0,1]. The conditional-comparison proposition cited in(CP4) permits
different deterministic bounds at different exponents and phases.
Completing the exponent inventory therefore replaces(PA2) for5 by

    pi5_sigma(1)=w5-1/5+sigma,
    pi5_sigma(2)=4/25-sigma,
    pi5_sigma(n)=4/5^n, n>=3,
    integral1=w5, integral N5=w5+1/4-sigma.           (RC2)

The7 factor and all later factors stay unchanged. Every atom in(RC2)
is nonnegative throughout the PA rectangle. Moving sigma mass from
N5=2 to N5=1 decreases each old-prefix hinge and the final hinge.
For the same actual u,v, define alpha_sigma and Phi_sigma by(PA4)
with these modified hinges. The actual law still satisfies

    lambda(1)>=alpha_sigma,
    lambda(L-1)<=2*lambda(1)+Phi_sigma.

Both bounds use the same refined comparison. The functions remain
separately affine in u,v, and all four corner masses are positive.
The smallest mass and largest paired query ratio are at(1/2,1/3):

    alpha_sigma=101334981151673/957458646144000,
    Phi_sigma=64424439965747/203116043520000,
    T-B_root=790143263665675501/18656783379834516030>0. (RC3)

Four-corner interpolation proves(RC1), using the unchanged raw density
cap9. Some envelope endpoints need not be realizable by an actual
pure family with this cap; the interpolation bounds the entire
rectangle, including every actual admissible pair.

### Necessary actual layout

Consequently(NC1) requires m5>24/125. There is a residue r0 mod5 with

    H5(A5 intersect(r0 mod5))<1/125.                  (RC4)

This is the actual union mass of all pure-5 originals in that root,
including arbitrarily high exponents. By(NC7), r0 is one of the three
roots not deleted at modulus5, and none of the four listed modulus25
or125 cylinders can lie in it: each would cost at least1/125.
Higher pure-5 classes can still occur in this root, with total union
mass below that threshold. The root need not be entirely free of
originals, and(RC4) is not sufficient for a lower certificate.

The [root-cap consumer](../../frontier/cover-geometry/two_copy_root_cap.py)
and [four-corner data](../../frontier/cover-geometry/two_copy_root_cap.json)
use the pinned PA ledger. For the remaining multiplier N, the exact
hinge correction is sigma times

    integral((2N-t)_+-(N-t)_+)
      =integral N-sum_(n<t)(min(2n,t)-n)*pi(N=n).

The full mean retains every high tail. A direct modified low-atom
convolution checks the same four new corner budgets. The source
comparison and(RC4) are ordinary proofs, without new Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_copy_root_cap.py
```

## Constant-cap tuning has an exact certificate optimum

Fix the unrefined pure-anchor measures(PA2), the mixed-anchor charge1/12,
and the four later primes11,13,17,19. Allow arbitrary finite constants
C_p>=1 in the same actual capped kernels, with

    t_p=(p-1)*(1-1/C_p)/2.

Changing a cap changes that actual kernel; the optimization compares
the resulting certificates. At C_p=1, complete each comparison row
directly to Haar density1, including the case s=C_p=1 where the
fractional completion formula would have denominator zero.

For the comparison, use the valid auxiliary tails

    Pr(N_p>=k)=min(C_p/p^(k-1),1), k>=2.              (CT1)

When C_p<=p these are exactly the probabilities in(CP4). For C_p>p,
the minimum in(CT1) is essential; the expression1-C_p/p is not a
probability. The conditional-comparison source permits these fixed
cylinder bounds. Every finite C_p gives a finite full first moment.

For a final real query threshold h>=1, consider the certificate

    alpha=W-1/12-sum_p [2C_p/(p-1)]F_(t_p)^old,
    B_h=h-1+F_h^final/alpha,  W=w5*w7.                (CT2)

Require alpha>0 throughout the pure-mass rectangle. The minimum over
such uniformly admissible constant-cap schedules and query thresholds
of the worst-case certificate B_h is exactly

    B_pure=28165018706892770299/5469152872511772242
          =5.149795473527814...>257/51.               (CT3)

This optimizes the specified comparison certificate. It is not an
optimum over supported actual laws, nor does it include the refined
root cap(RC2) or stronger estimates on the same kernels.

### A common corner and integer stage thresholds suffice

After dividing the two anchor measures by their masses, their tails
are1/(w_p*p^(k-1)) for k>=2. Thus decreasing either w_p increases every normalized
hinge, while alpha/W=1-1/(12W) minus the normalized nonnegative charges
decreases. The final hinge divided by W increases. Wherever alpha>0,
the query ratio therefore has the same worst corner(1/2,1/3) for every
schedule. Positivity there is equivalent to uniform admissibility.

First remove large caps without using a negative auxiliary atom. Put
b=(p-1)/2. For C_p>=b, the associated t_p is in[b-1,b). Holding every
other cap fixed, integer-valued M_old gives the current charge derivative
under the raw old-prefix measure:

    integral (M_old/b-1)*1_{M_old>=b}>0.

The strict sign follows from the full unbounded positive tail. The
tails(CT1) increase with C_p, so every later charge and the final hinge
are nondecreasing in C_p. Thus alpha decreases and B_h increases on
its feasible interval. Lowering C_p to b preserves feasibility and
cannot worsen the bound, even when the starting cap exceeded p.
Apply this separately to each coordinate.

Now1<=C_p<=b<p, so its auxiliary measure is affine in C_p. On a cell
between consecutive integer t_p values, write

    F_(t_p)^old=A-t_p D.

Since t_p=b*(1-1/C_p), the current charge is
C_p*(A/b-D)+D. Each later charge and the final hinge is also affine
in this one C_p, with the other parameters fixed. Hence alpha and
F_h^final are affine, and their ratio is fractional-linear on alpha>0.
The final hinge is strictly positive for every finite h. A boundary
where alpha approaches zero cannot improve the ratio. Therefore one
feasible cell endpoint, corresponding to an integer threshold, is at
least as good. Round the four coordinates successively at their common
worst anchor corner. All stage thresholds can thus be chosen in

    {0,...,4} times{0,...,5} times{0,...,7} times{0,...,8}.
                                                               (CT4)

For a fixed rounded schedule, B_h is affine between consecutive integer
h because M is integer-valued. Round h to an integer endpoint. Since
B_h>=h-1 and(PA1) supplies B_pure<6, any improvement has an integer
representative with h<=6.

### Exact finite grid

Two disjoint exact computations cover all2160 schedules in(CT4), each
testing integer query thresholds1 through8:

| Stage grid | Schedules | Uniformly positive | Best query certificate |
| --- | ---: | ---: | --- |
| All four thresholds positive | 1120 | 700 | B_pure, at(2,2,4,4), h=3 |
| At least one threshold zero | 1040 | 299 | 8.183084551002553..., at(0,2,4,4), h=6 |

The second row's exact grid minimum is
356233588829209201520069278190553/43532922898317742452872218559650.
Both programs retain every tail through the full geometric first
moment and convolve only the finite atoms below each hinge threshold.
Threshold zero has C=1 and its hinge equals the full mean.

The [positive-grid program](../../frontier/cover-geometry/two_copy_positive_cap_grid.py)
and [result](../../frontier/cover-geometry/two_copy_positive_cap_grid.json),
and the [zero-containing grid program](../../frontier/cover-geometry/two_copy_zero_cap_grid.py)
and [result](../../frontier/cover-geometry/two_copy_zero_cap_grid.json),
are the completed exact calculations used here. The rounding argument
extends their finite arithmetic conclusion to(CT3). This is an ordinary
proof with exact computational evidence, without Lean verification.

[Report537](../arithmetic/537-two-copy-lower-witnesses-require-nested-pure-five-prefixes.md) strengthens NC/RC using actual root and cell probabilities: both25 originals must share one surviving5-root, and both125 originals must share a live25-cell inside it. Three exact positive-mass same-law kernel comparisons exclude the other layouts. The remaining nested geometry still permits disjoint mixed-prefix packing approaching the full raw1/12 charge, so a uniform overlap rebate cannot close its query gap.
