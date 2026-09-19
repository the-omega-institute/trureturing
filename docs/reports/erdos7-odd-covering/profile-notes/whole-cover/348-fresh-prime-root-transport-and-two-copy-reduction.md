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

The [exact rational checker](../../frontier/whole-cover/multiplicity_two_sieve.py)
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

The [prime-flat constructor](../../frontier/whole-cover/p_flat_constructor.py) implements
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

The [fresh-root constructor](../../frontier/whole-cover/fresh_root_constructor.py)
implements section 1 and checks every original event bit against its
transported event on a single common carrier, including conditional
fibre bijections and the complete joint event histogram. It retains
that carrier even when deleting a high branch reduces the natural
output period. Its scope includes q<t, q=t, q=t+1, q=t+2 and q>t+2;
only the displayed sufficient range promises at most two pure-q classes.

The [composition check](../../frontier/whole-cover/fresh_root_composition_check.py)
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

The [old-q memory constructor](../../frontier/whole-cover/old_q_memory_construct.py)
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
