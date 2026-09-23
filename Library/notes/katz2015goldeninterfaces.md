---
bibkey: katz2015goldeninterfaces
authors: Nicholas M. Katz
year: 2015
title: Wieferich past and future
doi: 10.1090/conm/632/12632
claim: Katz's torus equidistribution conjecture has an exact fixed-golden specialization; macroscopic equidistribution alone does not force a WSS zero.
strata_touched: []
license: citation-only
triage: anchor
---

# Original WSS arithmetic across geometric realizations

## Verified locator

Nicholas M. Katz, *Wieferich past and future*, Contemporary Mathematics 632
(2015), 253-270, DOI 10.1090/conm/632/12632.
Author-hosted paper:
https://web.math.princeton.edu/~nmk/wieferich42.pdf

## 1. The geometric equidistribution conjecture

Source scope: Sections 2-6, including Conjectures 3.1, 4.7 and 6.1,
the Lie-algebra exact sequence, and Section 5's lattice warning.

Conjecture 4.7 concerns a torus over Z[1/N], a point generating a Zariski-dense
cyclic subgroup, and an integral Lie lattice. It predicts Haar-equidistribution
of the Wieferich fractions in the compact real torus of that lattice.
Conjecture 6.1 gives a framed formulation. Section 5 cautions that an arbitrary
change of lattice is not an automatic equidistribution-preserving operation.

CG.1 and CG.7 choose the norm-one torus of O=Z[phi], the SAME point
u=phi/(1-phi)=-phi^2, and Lie lattice Z*sqrt(5). For p>5, N_p=p-(5/p),
and original q_p=F_(N_p)/p mod p, the computed defect is

`(u^N_p-1)/p = (5/p)*q_p*sqrt(5) mod p`.

Hence the actual Katz fraction is c_p/p, where c_p is the least nonnegative
residue of (5/p)*q_p. Its zero set is exactly the original WSS set. The point
is nontorsion and therefore Zariski dense in this one-dimensional torus.
This is a specialization of an existing conjecture, not a randomness theorem.

CG.7 proves that even prime-denominator equidistribution need not hit zero.
Its artificial countermodel is not a Fibonacci sequence or a refutation of
Katz. The exact Fourier zero-counting identity is recorded separately. Its
full nonconstant-frequency error would need a genuinely new estimate on the
log-log scale; no such estimate is supplied. Fixed-frequency macroscopic
cancellation is not silently strengthened to shrinking-target control.

## 2. p-rationality and actual local geometry

Zakariae Bouazzaoui, *Fibonacci Sequences And Real Quadratic p-Rational Fields*,
arXiv:1902.04795.
https://arxiv.org/abs/1902.04795
https://arxiv.org/pdf/1902.04795

Source scope: Corollary 2.2, Remark 2.3, Proposition 3.2 and Theorem 3.4,
with their discriminant and class-number conditions. For the fixed
field Q(sqrt(5)), class number one and p>5 give: p is WSS iff the field is not
p-rational. Corollary 2.2 also relates this to divisibility of L(2-p,chi_5).
Nonvanishing of a p-adic logarithm is weaker than initial valuation exactly
one and cannot settle WSS. In the split case O/pO is a product of fields;
CG.2-CG.4 use its norm-one group, not a falsely cyclic full
unit group.

CG.2-CG.4 prove their local formulas directly. Exactly one of the p lifts of
a norm-one residue preserves the N_p return. The derivative U_(N_p)'(1) is
-2/5 modulo p, always nonzero. The unique Hensel root a_p in 1+p Z_p has
v_p(a_p-1)=h_p and first displacement (5/2)q_p. Varying the coefficient to
this root does not produce a WSS prime for the fixed coefficient one.
The local orbit closure has index p^(h_p-1) in the principal norm-one group.
These are complete local descriptions retaining the unknown actual h_p.

Rigoberto Florez, Robinson A. Higuita and Alexander Ramirez,
*The Resultant, the Discriminant, and the Derivative of Generalized Fibonacci
Polynomials*, Journal of Integer Sequences 22 (2019), Article 19.4.4.
https://cs.uwaterloo.ca/journals/JIS/VOL22/Florez/florez23.html

The paper provides classical polynomial-derivative context. CG.4
proves its displayed identity; no unverified theorem number or first-discovery
claim is used.

## 3. An exact integral-basis transfer

Lenny Jones, *A new condition for k-Wall-Sun-Sun primes*, arXiv:2302.10357v4,
revised July 15, 2023; author PDF dated July 18, 2023.
https://arxiv.org/abs/2302.10357
https://arxiv.org/pdf/2302.10357

Source scope: the definition of polynomial monogenicity, Theorem 1.1,
Proposition 2.5 and the index-criterion argument. At k=1 the
hypotheses hold, giving

`p is WSS iff X^(2p)-X^p-1 is non-monogenic`.

For a root theta_p with theta_p^p=phi, K_p=Q(theta_p) contains the original
fixed golden field. Non-monogenic here concerns the SPECIFIED power basis:
Z[theta_p] is not the full ring of integers. It does not assert that no other
generator of K_p has a power integral basis. The displayed polynomial
discriminant has absolute value 5^p p^(2p), and equals the square of that
index times disc(K_p). Its p-divisibility, and the reduction to
(X^2-X-1)^p mod p, occur for every p and alone do not decide the index.
No new global index constraint is proved here.

## 4. Arithmetic derivatives and cohomology

Alexandru Buium and Santiago R. Simanca, *Arithmetic partial differential
equations*, arXiv:math/0605107v2.
https://arxiv.org/abs/math/0605107

The abstract describes Fermat-quotient operators and usual derivations on
arithmetic groups; the full technical development is outside this note's
source scope. CG.6
defines delta_p(x)=(sigma_p(x)-x^p)/p on the unramified golden algebra,
proves its multiplication law, and computes its value at phi as a unit
multiple of original q_p. No arithmetic Ricci-flow theorem or WSS existence
result is attributed to this paper.

Gebhard Boeckle, David-A. Guiraud, Sudesh Kalyanswamy and Chandrashekhar Khare,
*Wieferich Primes and a mod p Leopoldt Conjecture*, arXiv:1805.00131v2.
https://arxiv.org/abs/1805.00131

The primary introduction and real-quadratic discussion connect regulator
congruences with Galois representations, cohomology and deformation theory.
No statistical hypothesis there is used as a proved golden-unit theorem.

## 5. The actual three-manifold bridge and its limit

CG.5 uses A=[[1,1],[1,0]], B=A^2 and S=2A-I. For every positive EVEN n,
it proves B^n-I=F_n S A^n and computes the actual integer cokernel with Smith
factors F_n and 5F_n. Abelianizing the actual torus mapping-torus group gives
H1=Z plus that cokernel. At n=p-(5/p), its p-primary torsion is (Z/p^h_p)^2.
This is a literal continuous three-manifold realization of the original WSS
depth. No new bound on that depth follows merely from real hyperbolicity,
entropy, or the topological identification.

## 6. Related results and boundaries

Nic Fellini and M. Ram Murty, *Wieferich primes in number fields and the
conjectures of Ankeny-Artin-Chowla and Mordell*, arXiv:2508.08472v2.
https://arxiv.org/html/2508.08472v2

Theorem 1.2 gives conditional non-Wieferich infinitude under number-field abc.
Theorem 1.3 instead assumes finitely many super-Wieferich primes. Neither is
an unconditional WSS-existence theorem. The same source reports AAC and
Mordell counterexamples in VARYING quadratic fields; they are not fixed-golden
WSS examples. The Pell-height route remains conditional and
points primarily toward non-WSS results.

The p-rational and integral-basis formulations are established transfers, not
additional independent problems counted on top of WSS. The remaining
arithmetic obligation is a constraint on actual original q_p/h_p, a WSS
witness, or a new global distribution theorem. Rephrasing the same unknown
in multiple spaces does not supply such a result.

## 7. Predictive spacetime completion and the original square-level drift

The WSS owner's SJC section reads Katz's Section 4 exact Lie-kernel sequence
on printed page 3 together with the actual repository task-quotient theory.
The relevant repository inputs are
`docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md`, Sections 1-3,
at inspected dev b603c498c3cdc76478bfb37c2e3c4ea29edb86ed, and the draft
`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md`, Section 2,
at candidate commit29c5504b11a1685c220e0ad2a9705a987fc6cff4 in PR8891.
The former distinguishes update closure from task sufficiency and requires
actual joint images. The latter's automatic symplectic and thermal results
require their stated positive-energy hypotheses. Their interpretation as a
physical model is not an arithmetic premise.

SJC keeps v=phi^2 and its prime-to-p residue order r, which is different from
the Fibonacci rank. The full preimage of the residue orbit modulo p^2 has
canonical multiplicative coordinates (j,z) in Z/r x F_p. The fixed update
is exactly (j,z) mapping to (j+1,z-q_p). A fiber rephasing adds a telescoping
difference to this drift and preserves its cycle sum -r*q_p. The torsion
section is a group section only: characteristic p^2 prevents a unital ring
section of the reduction map or its replacement by characteristic-p dual
numbers. The fixed polynomial X^2-3X+1 selects the actual lift among p
comparison lifts; choosing the zero-drift lift is not a WSS construction.

Two exact delayed traces have matrix [[2,1],[3,4]], determinant five, and
recover the entire state modulo every p^a for p>5. The returned trace alone
has zero first-order defect; the next trace reads -5r*q_p after division by p.
These are ordinary finite-ring proofs, not extra Lean conclusions of the
existing trace-Gram source. The real flow generating multiplication by v
is symplectic but has indefinite quadratic energy, so positive Gibbs and
positive-energy compression cannot be imported from PR8891 without new
hypotheses.

This is a task-relative completion of information discarded by reduction.
The integers with the usual absolute-value metric are already complete;
the p-adic topology has its own completion Z_p. The integer WSS formula
itself requires no new arithmetic or set-theoretic axiom. The drift and its
higher precision remain the actual q_p and h_p. No new prime-family
existence, exclusion, or cross-prime equidistribution follows from this
choice of coordinates.

## 8. Cyclotomic norm calibration

Tyler Ross, Zhongyan Shen and Tianxin Cai, *The p-adic Valuations of Mobius
Duals of Lucas Sequences*, arXiv:2512.03481v1.
https://arxiv.org/html/2512.03481v1

The Introduction, Theorem 2.2(c), and Proposition 3.2 give the precise source
scope used for calibration. The regular Lucas-sequence cyclotomic and
entry-point valuations are explicitly credited there to Carmichael and
classical valuation theory; the paper extends them to irregular sequences.
No new integer WSS example is supplied by these statements.

SJC independently derives, for the prime-to-p period r of phi^2, the integer
G_r=Psi_r(3), where Psi_r is the real r-cyclotomic polynomial, and proves
v_p(G_r)=h_p using the canonical torsion trace. Its elementary height bound
is 1<G_r<5^(EulerPhi(r)/2). This is a classical cyclotomic-norm interface,
not a claimed new WSS family. This unramified-at-p coefficient field of
conductor r must not be confused with the ramified p-power coefficient
fields used for the conditional Maass families in SGN and HCR.

## 9. The published squarefree criterion and the stronger norm estimate

The complete primary HTML of Ross-Shen-Cai was rechecked, including its
conclusion, Corollary 5.1. That corollary explicitly states equivalence
between absence of WSS primes and squarefreeness of every Fibonacci Mobius
dual M_n^F except n=6. The WSS owner's SJC.9 proves the exact change of
index between that source and its own norm: G_r=M_(iota(r))^F, where
r odd gives iota(r)=2r, r=2 modulo4 gives iota(r)=r/2, and4|r gives
iota(r)=r. Thus the source's exceptional index6 is G_3=4. The resulting
squarefree characterization is cited prior work, not a new discovery.

SJC.9 also records all prime valuations, including the small primes2,3,5.
For p>5 an inherited factor at r=r_p*p^a has valuation exactly one;
only the primitive r=r_p factor can have the initial depth h_p. Consequently
any repeated prime divisor of G_r for r>=4 is an original WSS prime,
without an additional coprimality assumption on that divisor and r.

SJC.10 is a separate elementary estimate for the actual positive norm.
Writing R=rad(r), s=r/R and a=phi^(-2s), the Mobius logarithm is shown to
have sign -mu(R) and magnitude less than -log(1-a). This yields the uniform
bound phi^(EulerPhi(r)-1)<G_r<phi^(EulerPhi(r)+1) and the exact integer
upper bound B(r)=L_(EulerPhi(r))-1 for mu(R)=1, or L_(EulerPhi(r)+1)
for mu(R)=-1. The latter upper bound is attained at every odd prime index.
This signed estimate is proved in the dossier rather than attributed to
Ross-Shen-Cai or Katz; its independent priority has not been established.

SJC.11 deduces the quotient-independent implication p^2>B(r_p) => q_p!=0
and the joint depth budget for primes having the same actual period r.
It does not prove that a new unbounded prime family satisfies this condition.
The fixed113 example demonstrates an improvement over the former height
bound, not a newly discovered non-WSS prime. No WSS existence, complete
squarefreeness theorem, spectral nonvanishing or Lean certification follows
from the size estimate. The remaining obligation is stated in SJC.12.

## 10. SIC dimension towers and a fixed-field obstruction

Gary McConnell, *Some new infinite families of non-p-rational real quadratic
fields*, arXiv:2406.14632v1, June 20, 2024.
https://arxiv.org/abs/2406.14632
https://arxiv.org/html/2406.14632v1

The exact source scope is Theorems 2.1-2.2, definition (2.1), and Lemma 3.3.
The construction originates in SIC-POVM questions but constructs real
quadratic fields with a varying squarefree discriminant parameter D. It
does not construct a WSS prime in a fixed preselected golden field.

TBN.1 in the existing WSS owner imposes that fixed-field condition. It
proves D(d)=5 for a square dimension d>=4 only at d=4, using the golden
Pell classification and L_(2n)=L_n^2-2*(-1)^n. DCE.4 subsequently extends
the exclusion to EVERY pure odd-prime-power seed p^a with a>=2. The odd
index case uses the published D=3 Lebesgue-Nagell theorem; the even case
uses coprime factors L_n-1 and L_n+1. This excludes construction inputs,
not the rational prime p from the original WSS set.

TBN.2-TBN.6 use the actual companion blocks
B_j=L_(2*3^j)+1=Psi_(3^(j+1))(3), j>=1. Every prime factor is split,
has Fibonacci rank2*3^(j+1), and occurs with its original h_p. Different
blocks are coprime. The product modulo4 and5 and modulo3^(j+2) gives the
three simultaneous balances. These specialize the existing GP3 strategy
to a different Lucas block, not the earlier L_(3^j)^2+1 block.

The classical regular valuation source has also appeared as Ross-Shen-Cai,
*The p-adic Valuations of Mobius Duals of Lucas Sequences*, The Fibonacci
Quarterly, published online July 21, 2026, DOI10.1080/00150517.2026.2656703:
https://www.tandfonline.com/doi/full/10.1080/00150517.2026.2656703
The publisher metadata and abstract were checked; the detailed theorem
locators above refer to the separately read primary arXiv version. No
claim that its full journal text was inspected is made here.

## 11. Global perfect-power input and actual common-depth exclusion

The dedicated source note `Library/notes/bugeaud2006lebesguenagell.md`
records the published theorem and the exact D=3 table locator. DCE.1-DCE.2
uses that external theorem to prove

`gcd{h_p:p|L_(3^j)^2+3}=1` for every j>=1.

The factor exponents are the actual h_p by TBN3. The conclusion excludes
every common-divisor depth pattern, including common odd divisors beyond
three. For every fixed integer e>=2 it produces infinitely many distinct
split primes of ranks2*3^s whose depths are not divisible by e. This does
not choose between depth one and a larger depth in any unknown prime.

DCE.3 strengthens the coverage budget uniformly in H: all depths at least
H>=2 require at least two prime factors and total multiplicity at least
2H+1. Equality gives two depths H,H+1. The smallest all-WSS pattern must
therefore be P^2 Q^3, with Q=19 modulo40 and the displayed ternary class
for P. The fourth fixed block has an actual factor with h_p<=4 by an exact
size comparison, without factoring that block. It is not a newly found
non-WSS prime or a proof that every block has a simple factor.

No novelty is claimed for the external exponential theorem or its formal
instantiation. The new ordinary deductions narrow block-depth patterns;
heterogeneous depths such as2,3 remain unexcluded. The existing Scribe
reference records this arithmetic context without changing the Lean
trace-image theorem, its formulas, or its certification status.
