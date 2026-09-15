---
bibkey: katz2015goldeninterfaces
authors: Nicholas M. Katz
year: 2015
title: Wieferich past and future
doi: 10.1090/conm/632/12632
claim: Katz's torus Wieferich equidistribution conjecture has an exact fixed-golden specialization; its macroscopic conclusion alone does not imply a WSS zero.
license: citation-only
triage: anchor
---

# Original WSS arithmetic across geometric realizations

## 1. Primary geometric conjecture and exact specialization

Nicholas M. Katz, *Wieferich past and future*, Contemporary Mathematics 632
(2015), 253-270, DOI 10.1090/conm/632/12632.
Author-hosted paper, reached through the actual author bibliography:
https://web.math.princeton.edu/~nmk/wieferich42.pdf

Read Sections 2-6 in the full parsed primary PDF, including Conjectures 3.1,
4.7 and 6.1, the Lie-algebra exact sequence and the lattice warning in
Section 5. Screenshot attempts for pages 6 and 7 failed with internal errors;
no successful visual inspection of those pages is claimed. The argument below
uses the retrieved mathematical text, not a diagram or unparsed table.

Conjecture 4.7 concerns a torus over Z[1/N], a point whose cyclic subgroup is
Zariski dense in the generic fibre, and a chosen integral Lie lattice. Its
Wieferich fractions are predicted to be Haar-equidistributed in the compact
real torus of that lattice. Conjecture 6.1 supplies a framed formulation.
The lattice choice matters: Section 5 includes a counterexample to an
unrestricted abstract change-of-lattice inference.

In the existing WSS document, new CG.1 and CG.7 choose the norm-one torus of
O=Z[phi], the SAME unit u=phi/(1-phi)=-phi^2, and Lie lattice Z*sqrt(5).
For p>5, N_p=p-(5/p), and the ORIGINAL quotient q_p=F_(N_p)/p mod p, the
actual first defect is

`(u^N_p-1)/p = (5/p)*q_p*sqrt(5) mod p`.

Thus the precise Katz fraction in this framing is c_p/p, with
c_p the least nonnegative residue of (5/p)*q_p. It has zero exactly at the
original WSS primes. The torus point is nontorsion and hence Zariski dense in
this one-dimensional torus. This is an explicit specialization of a published
conjecture, not a theorem that the resulting prime-indexed sequence is random.
In particular, sign changes or division by constants modulo p must not be
assumed to preserve equidistribution without checking the chosen framing.

## 2. Smooth local geometry and p-adic logarithms

Zakariae Bouazzaoui, *Fibonacci Sequences And Real Quadratic p-Rational Fields*,
arXiv:1902.04795.
https://arxiv.org/abs/1902.04795
https://arxiv.org/pdf/1902.04795

Read Corollary 2.2, Remark 2.3, Proposition 3.2 and Theorem 3.4 in the primary
PDF text. The source includes the class-number/discriminant conditions. For
the fixed field Q(sqrt(5)), class number one and p>5 give the exact bridge:
p is WSS iff the field is not p-rational. Equivalently the normalized local
unit regulator has an extra p-divisibility; Corollary 2.2 also connects this
to divisibility of L(2-p,chi_5). Ordinary nonvanishing of the p-adic logarithm
is weaker than valuation exactly one and cannot settle WSS.

The split algebra O/pO is a PRODUCT of two fields, not a field or a cyclic
unit group. The new local calculations explicitly treat split and inert
norm-one groups separately and do not reuse any imprecise split-case wording.

CG.2-CG.4 give elementary local calculations with their own proofs. The p
norm-preserving lifts of one reduction contain exactly one N_p-return lift.
The Fibonacci polynomial U_(N_p) has derivative -2/5 at X=1 modulo p, always
nonzero. Its unique Hensel root a_p in 1+p Z_p satisfies
`v_p(a_p-1)=h_p` and `(a_p-1)/p=(5/2)q_p mod p`.
Changing X to this root changes the recurrence parameter. It does not produce
a classical WSS prime at the fixed parameter X=1.

The principal norm-one p-adic group has logarithm p Z_p sqrt(5). The closure
of the actual cyclic return orbit has index p^(h_p-1). This is a precise
continuous/nonarchimedean interpretation, but its formula still contains the
unknown initial depth h_p. No new constraint across different primes follows
from the local classification alone.

Polynomial-derivative context: Rigoberto Florez, Robinson A. Higuita and
Antara Mukherjee? The bibliographic author list is deliberately NOT inferred
from memory here; use the primary entry for the exact names:
*The resultant, discriminant, and derivative of generalized Fibonacci
polynomials*, Journal of Integer Sequences 22 (2019), Article 19.4.4,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Florez/florez23.html .
The derivative mechanism is classical; no first-discovery claim is made for
its fixed-golden specialization. The displayed identity is proved in CG.4
rather than justified by a guessed theorem number.

## 3. A proved integral-basis transfer that preserves the original problem

Lenny Jones, *A new condition for k-Wall-Sun-Sun primes*, arXiv:2302.10357v4,
revised July 15, 2023; author PDF dated July 18, 2023.
https://arxiv.org/abs/2302.10357
https://arxiv.org/pdf/2302.10357

Read the definition of polynomial monogenicity, Theorem 1.1, Proposition 2.5
and the relevant index-criterion proof in the primary PDF text. At k=1 the
hypotheses are satisfied. The theorem gives:

`p is WSS iff X^(2p)-X^p-1 is non-monogenic`.

Here theta_p is a root, K_p=Q(theta_p), and monogenic means the SPECIFIED
power basis 1,theta_p,...,theta_p^(2p-1) equals the integer ring basis.
It is not a claim that K_p admits no other monogenic generator. Choose
 theta_p^p=phi, so the fixed original quadratic field sits in the extension.
Changing this extension with p is a valid exact encoding because the theorem
supplies the equivalence; it is not an unrelated varying fundamental unit.

The polynomial discriminant has absolute value 5^p p^(2p), but it equals
`[O_(K_p):Z[theta_p]]^2 * disc(K_p)`. Its displayed p-divisibility is present
for every p and does not by itself show an index defect. Likewise, reduction
of the polynomial to (X^2-X-1)^p mod p is automatic. One needs the integral
maximality/index information at the next order, not only a repeated mod-p root.
No independent global index restriction was proved in this increment.

## 4. Arithmetic differential and Galois-cohomological context

Alexandru Buium and Santiago Simanca, *Arithmetic partial differential
equations*, arXiv:math/0605107.
https://arxiv.org/abs/math/0605107

The primary abstract was read, not the full technical development. It studies
Fermat-quotient operators together with usual derivations on arithmetic groups.
CG.6 uses an explicitly defined operator
`delta_p(x)=(sigma_p(x)-x^p)/p` on the unramified golden p-adic algebra and
proves its multiplication law. Its value at phi is a unit multiple of the
original q_p. No arithmetic Ricci-flow theorem or application to WSS existence
is attributed to this paper.

Gebhard Boeckle, David-Alexandre Guiraud, Sudesh Kalyanswamy and Chandrashekhar
Khare, *Wieferich Primes and a mod p Leopoldt Conjecture*, arXiv:1805.00131.
https://arxiv.org/abs/1805.00131

The primary paper's introductory and real-quadratic discussion was inspected.
It links regulator congruences to Galois representations, cohomology and
Wieferich-type questions. No conjectural statistical input in that paper is
used as a proved vanishing or nonvanishing theorem for the original golden unit.

## 5. Genuine three-dimensional and macroscopic-statistical boundaries

CG.5 uses the actual integer matrix A=[[1,1],[1,0]], B=A^2 and S=2A-I.
For every positive EVEN n it proves B^n-I=F_n S A^n, computes the actual
cokernel with Smith factors F_n and 5F_n, and then computes the first homology
of the torus mapping torus from its semidirect-product fundamental group.
At n=p-(5/p) the p-primary torsion is (Z/p^h_p)^2. This is a literal
three-manifold interface to classical WSS, but it is not a new divisibility
bound. Real hyperbolic eigenvalues or entropy do not determine this next
p-adic digit from the displayed formula.

CG.7 constructs a prime-denominator sequence that is equidistributed in
R/Z but never hits zero. This is a logical countermodel to the assertion
that ordinary equidistribution alone implies a WSS prime, not a counterexample
to Katz's conjecture. Its proof uses classical irrational-rotation
equidistribution and uniform continuity, and is not counted as a newly solved
external problem. The exact Fourier identity for WSS zero counting is also
stated. An o(log log X) bound for its full nonconstant-frequency term would
force an asymptotic, but no such estimate is supplied. A fixed-frequency
macroscopic result is not silently upgraded to that shrinking-target scale.

## 6. Current adjacent open problems and accounting

Nic Fellini and M. Ram Murty, *Wieferich primes in number fields and the
conjectures of Ankeny-Artin-Chowla and Mordell*, arXiv:2508.08472v2.
https://arxiv.org/html/2508.08472v2

Theorem 1.2 gives conditional non-Wieferich infinitude under number-field abc.
Theorem 1.3 instead assumes finitely many super-Wieferich primes. These are
published conditional directions, not unconditional WSS existence results.
The same source records counterexamples to AAC and Mordell in VARYING real
quadratic fields; those must not be mislabeled as fixed-golden WSS examples.

Bounded current searches found no verified resolution of classical WSS
existence, Katz's general torus equidistribution conjecture, or its particular
fixed-golden specialization. This is not an exhaustive status/priority
certificate. The index and p-rational formulations are known exact transfers,
not additional independent open problems counted on top of WSS.

For a new result to count toward the current objective, it must impose a
previously unavailable restriction on actual h_p or q_p in the fixed field,
produce an actual WSS witness, or prove a genuinely global distribution result
with its precise scale and arithmetic family retained. Changing the local
parameter, assuming randomness, or importing a conjectural height inequality
does not satisfy that requirement by itself.

## 7. Repository, execution and write-back scope

Read actual dev 15e0a49477cda321e7d344ee62996bf18e34e838, the actual
GoldenApparition.lean source, and the current #7895 head d4813880. The
existing PH appendix is preserved byte-for-byte. The historical problem-card
Gap/Route paragraphs are not a fresh audit of all current frozen sources.
CG.1-CG.8 are appended ordinary proofs; no new bind-only Lean/Scribe wrapper,
CI file, registry, admission marker or frozen state is introduced.

Executed exact diagnostics: 300 primes 5<p<=2000 for the parameter derivative,
predicted Hensel lift, exact Katz coordinate and arithmetic-derivative relation;
1151 parameter lifts and 1151 norm-one lifts exhaustively checked at primes
through 101; 150 even-index actual matrix factorizations and integer Smith
calculations. These test formulas, not the existence of a WSS prime or a new
search bound. No statistical equidistribution, p-adic analytic kernel proof,
Lean elaboration, C# compilation, independent-model review or novelty approval
was executed. New external open problems solved: zero.
