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
