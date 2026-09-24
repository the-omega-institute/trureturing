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
every probability supported on V has R_Q>=r, with r>=0. No such example
with r>=6 is supplied here. Put a=1+2r. For ANY probability mu on the
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
does not meet the premise. Finding such a cofactor family, or a uniform
bound ruling it out, remains open. Even a successful(TC6) counterexample
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
