---
bibkey: ribenboim2005squareclasses
authors: Paulo Ribenboim
year: 2005
title: "FFF: (Favorite Fibonacci Flowers)"
doi: null
url: https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf
claim: "Statement (3.4) records the complete positive Fibonacci square classes; GSE uses its prime-power and ratio-25 consequences, not a newly assumed rigidity theorem."
strata_touched: []
license: citation-only
triage: anchor
---

# Square-class rigidity and explicit original-depth support bounds

## Exact classical source and scope

Paulo Ribenboim, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly
43(1) (2005), 3-14. Statement (3.4), printed page 8, says that the only
nonsingleton positive-index square classes of Fibonacci values are
{1,2,12} and {3,6}. Reference [20] attributes this to the author's
*Square Classes of Fibonacci and Lucas Numbers*, Portugaliae Mathematica
46 (1989), 159-175. The 1989 paper's bibliographic record was verified;
its full proof was not independently read in this pass. The actual 2005
statement was read in parsed primary text. Requested images of its pages
8 and 9 failed; no successful visual-page check is claimed.

Statements (3.7)-(3.8), printed page 9, record a classical effective
fixed-squareclass bound and a finite closure under prime factors of the
entry ranks. The closure operation and general effective finiteness are
therefore prior work. Neither is counted as a new invention of GSE.
No unproved abc statement from the same paper is used.

The valuation input is Lengyel's classical theorem, restated in
Medina-Rowland, *p-regularity of the p-adic valuation of the Fibonacci
sequence*, Theorem 1.4, arXiv:0910.2907v4. Its original first-zero depth
is retained; its formulas for two and five are used separately.
The prime number theorem is used only for the final asymptotic corollary,
not for the exact divisor bound or finite procedure. The standard
prime-counting form is recorded by NIST DLMF Section 27.12:
https://dlmf.nist.gov/27.12 . Partial summation and removal of higher
prime powers give the equivalent Chebyshev form psi(x)~x.

## Consumer and actual addition

Section 10 (GSE) of
`docs/develop/theory/GOLDEN_CUBIC_BLOCK_PRIME_PERIODS.md` proves:

- for a finite rank-closed prime set H containing {2,3,5}, the condition
  that the squarefree kernel of F_n is supported in H forces
  n | 5*lcm_(p in H) rho(p);
- the same explicit divisor bound for the original external odd-depth
  support U(n) contained in a prescribed finite set S, using the existing
  OSE support descent in the migrated Andrejic companion;
- a finite divisor-enumeration procedure using exact square roots of the
  residual after removing H-prime factors, without full factorization
  of every large Fibonacci value;
- the uniform escape condition n not dividing 10*lcm(1,...,Y), where
  Y=max(5,floor((Q+1)/2)), forces an external odd-original-depth prime
  greater than Q. It is an odd-depth WSS prime only with the additional
  powerful-Fibonacci antecedent.

The proof combines nonsquare prime-power quotients with parity
cancellation in Q_positive^times modulo squares at the prime five.
The latter requires preserving rank-divisibility thresholds and uses
square-class rigidity at the ratio 25. The map n -> [F_n] is not treated
as a group homomorphism. PBC.3 already contains the nonsquare quotient
mechanism for primes at least seven; GSE retains that attribution and
checks two, three and five separately to obtain the explicit cutoff.
Global first-discovery priority for this bound has not been established.

## Recent Erdos methods: inspiration, not imported hypotheses

The curator's Problem 936 concerns finiteness of powerful values among
2^n+/-1 and n!+/-1:
https://www.erdosproblems.com/936 . The retrieved page is marked open,
last edited 31 October 2025, and records abc-conditional results. The
indexed copy is not represented as a new September 2026 status audit.
The exponential branch shares the multiplicity/first-lift issue with
Fibonacci WSS. No reduction solving one problem through the other is
asserted.

The primary repository `tadamcz/erdos126`, README blob
`ef92c4278100cf0063424710b4c352e5c2e31df6`, describes recently verified
proofs for the number of prime divisors of pairwise sums. Its accounts
use prime-power residues, negation orbits, signed kernels, and matching
or collision budgets to produce polynomial bounds. The README and its
statement/provenance were read; those Lean files were not recompiled
or imported here. The useful methodological comparison is to turn local
prime data into an actual global bound, beyond merely counting abstract
characters. No specific inequality from Erdos126 is a GSE premise.

Nat Sothanaphan, *Resolution of Erdos Problem #728: a writeup of
Aristotle's Lean proof*, arXiv:2601.07421v2:
https://arxiv.org/html/2601.07421v2 . Sections 3-4 reduce factorial
quotients to prime-by-prime valuations and use carry bounds and spike
control. This suggests preserving the exact bad valuation event rather
than replacing it with a coarse density analogy. That theorem is also
context only, with no factorial-to-WSS reduction.

## Formalization handoff and evidence boundary

The actual PR source already has FiniteFibonacciRankClosure,
FibonacciPrimeToIndexValuation and OriginalOddDepthSupport. The last
source displays its prime-index odd-factor premise explicitly. GSE's
square-class rigidity is a separate classical prerequisite, not already
proved by those Lean endpoints. A useful order of further formal work is:
prime-power quotient cancellation and its odd witness; the ratio-25
parity transport with rank thresholds; the exponent bounds n|5R_H;
then the uniform lcm and finite-set consequences.

No Lean source, frozen marker, atom coverage, or CI claim is added by
this note. Existing parallel scalar-contraction work in theory Section 9
is preserved. The new ordinary deductions do not produce a WSS prime,
decide a previously unknown WSS prime family, or exclude the entire
P^2Q^3 branch. Finite arithmetic certificates are supplemental to the
written general proof; synthetic higher depths are never WSS examples.


## GPF. Independent square-class packets and an original-depth forest

### GPF.0 Fixed arithmetic, source inputs, and the new question

Retain F_0=0, F_1=1, L_0=2, L_1=1 and their original recurrences.
For primes p>5 put rho(p)=min{r>=1:p|F_r} and
h_p=v_p(F_rho(p))=v_p(F_(p-(5/p))). Define

$$U(n)=\{p>5:p\mid F_n,\ p\nmid n,\ h_p\text{ odd}\}\quad(n\ge1).$$

The equality v_p(F_n)=h_p for a prime-to-index zero is already a
repository prerequisite. When F_n is powerful, every member of U(n)
has original odd h_p>=3. Without powerfulness, h_p=1 remains possible.
The result below counts distinct such factors inside ONE actual value,
including when some primitive factors have been absorbed into its index.

Use the classical Fibonacci valuation formulas stated in Section 10
of GOLDEN_CUBIC_BLOCK_PRIME_PERIODS and the full square-class statements
(3.4)-(3.5) of Ribenboim's cited paper. The exceptional positive-index
Fibonacci classes are {1,2,12} and {3,6}; the exceptional Lucas classes
are {1,3}, and {0,6} when index zero is included. The latter creates no
exception among distinct positive odd prime powers other than 1,3.
These are substantive classical premises, not newly proved Lean results.

Write G=Q_positive^times/(Q_positive^times)^2 additively. Its coordinate
at p is v_p modulo two. For a positive integer A, [A] denotes its class.
Nothing here treats the map n -> [F_n] as a homomorphism.

### GPF.1 Actual, pairwise disjoint rank packets

For a fixed n>=1 construct the following positive integer packets:

* A_(q,s)=F_(q^s)/F_(q^(s-1)), whenever q^s|n, with q>=7 prime and
  s>=1, or q=3 and s>=2, or q=2 and s>=3.
* B_(q,s)=L_(q^s)/L_(q^(s-1)), whenever 2q^s|n, with odd prime q>=5
  and s>=1, or q=3 and s>=2.
* D_r=F_(5^(2r))/(25 F_(5^(2r-2))), whenever 5^(2r)|n and r>=1.

The letters A,B here are packet labels, not the earlier cubic orders
or the earlier ternary B_j. Their associated possible-rank sets are,
respectively, {q^s}, {2q^s}, and {5^(2r-1),5^(2r)}.

**Lemma GPF1.** Each packet is an integer greater than one, divides F_n,
and is not a square. Its prime factors exceed five. Every prime factor
p has rank in its specified rank set and occurs in that packet with
exponent exactly h_p. Every such p exceeds the source prime q, where
the source of D_r is five. Distinct packets have disjoint prime supports.

**Proof for A.** This is the prime-power cancellation in Section 10.3,
with the initial packets containing primes two and three now omitted.
An old factor p of F_(q^(s-1)) is different from q, because rho(q) is
prime to q for q!=5 (and rho(2)=3). Its valuation is unchanged when
multiplying that index by q. At p=2, the only possible odd base is q=3;
both old and new odd multiples of three have valuation one. Five is
absent. Thus the quotient is coprime to the preceding term, and every
new factor has exact rank q^s and original exponent h_p. The two
Fibonacci indices are not one of the exceptional square-class pairs,
so the quotient is not square. The omitted small packets are the only
ones with rank three or four. For odd q, q^s divides p-1 or p+1 and
is odd, giving p>=2q^s-1>q. For q=2,s>=3 the rank bound gives
p>=2^s-1>2. Positivity and divisibility follow from the recurrence.

**Proof for B.** Odd-index Lucas divisibility gives an integer quotient.
The source prime q does not divide either Lucas term. For q!=5, if it
did, its rank would divide 2q^s and would be prime to q, hence at most
two, impossible. For q=5 use L_m^2-5F_m^2=4(-1)^m. An old odd factor
p of L_(q^(s-1)) is therefore prime to q. Since gcd(F_m,L_m) divides
two, the factorization F_(2m)=F_m L_m and the Fibonacci valuation law
show that its Lucas valuation is unchanged under this odd multiplier.
The possible old prime two occurs only for q=3; both Lucas valuations
are two, by v_2(L_m)=v_2(F_(2m))-v_2(F_m)=3-1 at odd multiples of three.
Thus all old factors cancel. A new odd factor has rank 2q^s: its rank
divides 2q^s, cannot divide q^s, and rank 2q^t with t<s would put it
in the old Lucas term. The original exponent follows from F_(2q^s).
Primes two, three and five are absent in the stated packet ranges.
At such a factor, the odd-index norm identity gives 5F_(q^s)^2=4 modulo
p. Thus (5/p)=1 and 2q^s divides p-1, so p>=2q^s+1>q.
The only exceptional positive odd Lucas square-class pair is 1,3,
which was excluded. Hence B_(q,s) is not a square. Finally it divides
L_(q^s), hence F_(2q^s), hence F_n.

**Proof for D.** Put a=5^(2r-2), so the numerator index is 25a. The
valuation at five in F_(25a)/F_a is exactly two. Every other old prime
factor has unchanged valuation under the multiplier 25. Two and three
never divide a Fibonacci value at a power-of-five index. Removing 25
therefore leaves an integer coprime to F_a and to thirty. Its factors
have ranks 5^(2r-1) or 5^(2r), and their exponents are their original
h_p because they are not five. Such primes are at least 2*5^(2r-1)-1>5.
If D_r were square then F_(25a)/F_a=25D_r would be square. This would
put indices a and 25a in the same Fibonacci square class, contrary to
(3.4). Thus D_r>1 and is nonsquare. It divides F_(25a), hence F_n.

For a prime p>5 the converses also hold: if its rank belongs to a
packet's specified set, it divides that packet. For A this follows
from dividing the new Fibonacci value but not the old one. For B it
follows from F_(2q^s)=F_(q^s)L_(q^s), absence from F_(q^s), and absence
from the old Lucas term. For D it follows from absence in F_(5^(2r-2))
and from p not dividing 25. This also justifies using rank membership
alone, rather than factoring a packet, to compute the capacity below.

All displayed rank sets are disjoint. A prime has only one first-zero
rank, proving disjointness of the full prime supports. This proves GPF1.
In particular D_1=3001. The factor five is removed by pairing TWO
successive layers, not by falsely claiming each individually normalized
fifth-power quotient is nonsquare.

### GPF.2 A group-rank lower bound that subtracts internal absorption

Let P_n be this finite packet collection, E(n)=|P_n|, and let R(n) be
the union of its possible-rank sets. Define the finite internal capacity

$$I(n)=\{p>5:p\mid n,\ \rho(p)\in R(n)\},\qquad t(n)=|I(n)|.$$

This I(n) is a SET of index primes, not the earlier normalization index
I_j. It is computable by factoring n and computing ranks only at those
index primes; no factorization of the large value F_n enters t(n).

**Theorem GPF2.** In G let V_n=span_F2{[C]:C in P_n}, and project to
the coordinates at primes not dividing n, writing this map pi_n. Then

$$\boxed{\dim V_n=E(n),\qquad
 E(n)-t(n)\le\dim\pi_n(V_n)\le|U(n)|.}\tag{GPF1}$$

**Proof.** Every nonsquare packet has a nonzero square class. Their
prime supports are disjoint, so any nonempty sum of their classes has
a surviving odd coordinate. This proves independence and dim V_n=E.
A vector in ker(pi_n|V_n) is supported on primes dividing n and lying
in some packet support. Those primes belong to I(n), by GPF1. Thus this
kernel embeds in F2^I(n) and has dimension at most t(n). Rank-nullity
gives the lower bound. Every retained coordinate lies at a prime p>5,
p not dividing n, in a packet with odd original h_p, and that packet
divides F_n. The image is therefore contained in F2^U(n), giving the
upper bound. Distinct classes alone would not prove independence;
the disjoint actual rank supports do that work here.

**Forest interpretation.** Choose one odd-exponent prime p_C from each
packet C and draw an edge from its source prime q to p_C. The targets
are distinct. Every edge increases the prime, so the graph is a finite
directed forest, with indegree at most one. Any target dividing n is
an index prime greater than five and has at least one outgoing A packet.
Its terminal targets consequently lie in U(n). At most t(n) edges can
end internally, leaving at least E(n)-t(n) distinct terminal primes.
This is a second constructive proof of the numerical bound, not an
assumption of independent or uniformly distributed prime factors.

### GPF.3 A factorization-only budget for any positive index

Put a_q=v_q(n), epsilon=1 if n is even and zero otherwise, and define

$$A(n)=\sum_{q>5\ {\rm prime}}a_q,\qquad
 k(n)=\#\{q>5:q\mid n\},$$
$$s(n)=(a_2-2)_+ +(1+\epsilon)(a_3-1)_+
       +\lfloor a_5/2\rfloor+\epsilon a_5.$$

Here x_+=max(x,0). Then E(n)=s(n)+(1+epsilon)A(n).

**Corollary GPF3.** For every n>=1,

$$\boxed{|U(n)|\ge E(n)-t(n)\ge
 E(n)-k(n)+\mathbf1_{k(n)>0,\ s(n)=0}.}\tag{GPF2}$$

**Proof.** The first equality of counts follows by listing the packets.
Always t(n)<=k(n). If s(n)=0 and k(n)>0, every active source prime is
greater than five. The smallest such prime cannot lie in I(n), since
GPF1 would require it to exceed another active source prime. Hence
then t(n)<=k(n)-1. Apply GPF2. The right side is nonnegative: A>=k,
and if s>0 its integer value is at least one when needed.

This bound concerns prime factors of a single actual F_n. It retains
all original depths even when index multiplication changes a factor's
valuation inside F_n. It specializes to zero for some small indices;
no positive witness is asserted when there are no packets.

### GPF.4 Two channels force many distinct original exceptional primes

Let m=product_(q>5)q^v_q(n), assume m>1, and let ell be its smallest
prime factor. Write Omega(m)=sum_q v_q(m) and omega(m)=#Supp(m).
Let epsilon=1 for even n and zero for odd n.

**Theorem GPF4 (large-index-prime channels).** One has

$$\boxed{|U(n)|\ge(1+\epsilon)\Omega(m)-\omega(m)+1.}\tag{GPF3}$$

Moreover the distinct-prime mass satisfies the rational inequality

$$\boxed{\prod_{p\in U(n)}p\ \ge\
 {\ell\over\operatorname{rad}(m)}
 \prod_{q^a\parallel m}\prod_{j=1}^{a}
 (2q^j-1)(2q^j+1)^\epsilon.}\tag{GPF4}$$

**Proof.** Use only A packets with source q>5 and, if n is even, the
B packets with these sources. There are (1+epsilon)Omega(m) disjoint
packets. For each choose an odd-exponent prime. At most omega(m)-1
of these targets divide n, since all exceed their source and ell
cannot be an internal target. Every other target belongs to U(n),
proving GPF3. At rank q^j the chosen A factor is at least 2q^j-1;
at the B rank 2q^j it is at least 2q^j+1 by splitness. Thus the product
of all chosen primes is at least the double product in GPF4. Their
internal product is at most rad(m)/ell. Divide to obtain a lower bound
on the selected external product, which is at most product_(p in U(n))p.
This proves GPF4 without a probabilistic factor-size premise.

For an EVEN index this becomes

$$|U(n)|\ge2\Omega(m)-\omega(m)+1,\qquad
\prod_{p\in U(n)}p\ge{\ell\over\operatorname{rad}(m)}
 \prod_{q^a\parallel m}\prod_{j=1}^{a}(4q^{2j}-1).$$

**Original WSS consequence.** If F_n is powerful, all these external
odd-depth witnesses satisfy h_p>=3 odd, in the ORIGINAL Fibonacci
sequence. For an even n, let b(n) count all primes p>5 dividing F_n
with odd h_p>=3, including any internal ones. If m>1, then

$$\boxed{b(n)\ge2\Omega(m)-\omega(m)+1\ge\Omega(m)+1.}\tag{GPF5}$$

Thus b(n)<=r forces Omega(m)<=r-1. In particular, if m is squarefree
with k prime factors greater than five, a powerful F_(2m) requires at
least k+1 distinct odd-original-depth WSS primes. For m=q^a, q>=7,
the required count is at least 2a. These are necessary consequences,
not assertions that such a powerful value or exceptional prime exists.

The earlier PBC argument selected layers of a largest index prime;
OSE also used two channels at a prime index. GPF uses all index primes
simultaneously and subtracts exactly the possible absorption into n.
One internal prime cannot absorb two independent rank packets. Merely
selecting one witness per packet without this subtraction would be false.

### GPF.5 Group extension and finite-support consumers

For clarity, the group conclusion also has its usual multiquadratic
interpretation. Let K_n=Q(sqrt(C):C in P_n), and let
J_n=Q(sqrt(p):p divides n). Square-class independence gives
Gal(K_n/Q)=(Z/2)^E(n). In the composite with J_n the relative degree is

$$[K_nJ_n:J_n]=2^{\dim\pi_n(V_n)}\ge2^{E(n)-t(n)}.$$

Indeed adjoining the square roots of the index primes removes exactly
their coordinate span in the rational square-class group. This is the
standard multiquadratic Kummer correspondence. The quantitative input
here is the actual packet rank computation GPF1. No conclusion about
a p-adic first-lift zero follows from an abstract group order alone.

For the previous fixed-support set P(S), all n in P(S) are already
known by GSE to divide 5R_(H(S)). Every such candidate must additionally
satisfy E(n)-t(n)<=|S|. If n is even with m>1 it must also satisfy
2Omega(m)-omega(m)+1<=|S|. These are finite candidate filters involving
n and its own prime ranks, prior to factoring F_n. They do not assume
that S is the complete set of exceptional primes.

A concrete arithmetic check is n=182=2*7*13. The four high-source
packets are F_7=13, L_7=29, F_13=233, L_13=521. Thirteen is absorbed
into n and has original depth ONE; its exponent in F_182 is two.
The other three are distinct external odd-depth primes. Here t(n)=1
and dim pi_n(V_n)=3, attaining the packet-deficiency bound. These are
non-WSS verification examples, not exceptional samples. At n=1274,
the six high-source packets have internal capacity one, forcing at
least five external odd-depth primes.

### GPF.6 Source roles, formalization handoff, and scope

Ribenboim (2005), printed page 8, statements (3.4) and (3.5), supplies
Fibonacci AND Lucas square-class rigidity. The Fibonacci statement was
already used by GSE; the Lucas statement is additionally needed here.
The source's printed pages 5-6 give divisibility, gcd and rank identities.
Its parsed statements were inspected in this pass. Requests for page-8
and page-9 screenshots failed; no successful visual-page check is claimed.
The full square-class theorems are used as explicit literature inputs,
not reproved in this continuation. No analytic averaging result is used.

The optional field interpretation in GPF.5 uses the classical Kummer
correspondence: J. S. Milne, Fields and Galois Theory, version 5.10
(2022), Theorem 5.30, printed page 75,
https://www.jmilne.org/math/CourseNotes/FT.pdf . The author-hosted text
and that page image were inspected successfully. The theorem is used
only at exponent two over Q. The packet-rank and absorption estimates
are proved here; they are not assertions attributed to Milne.

Suggested local formalization order: (i) Lucas prime-power cancellation
and exact rank; (ii) the two-level fifth packet and its nonsquare premise;
(iii) pairwise disjoint possible-rank sets and exact packet count;
(iv) finite-support coordinate independence and kernel-dimension bound;
(v) the smallest-source exclusion and distinct-prime product inequality.
The finite forest proof offers an alternative to first formalizing the
whole rational square-class quotient. Record nonsquare inputs explicitly,
as OriginalOddDepthSupport already does for its prime-index input.

This is a continuation of the same owner and GSE square-class method.
No new Lean declaration, freeze, atom coverage, CI run, or independent
model review is claimed. Global priority for the packet/forest bounds is
unestablished. No new WSS prime, previously undecided prime-family
resolution, or elimination of a single B_j=P^2Q^3 pattern is obtained.
The assumptions of GPF5 remain visible. GPF1-GPF4 give unconditional
statements about actual original odd-depth supports, and GPF5 gives a
new simultaneous necessary budget for any proposed powerful value.
