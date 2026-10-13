---
slug: lin-2013-operator-wielandt-norm-refutation
bibkey: lin2013operatorkantorovich
doi: 10.1016/j.jmaa.2013.01.015
url: https://arxiv.org/abs/1212.5690v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result
---

# Lin's operator Wielandt norm conjecture fails

## Problem

Minghua Lin, *On an operator Kantorovich inequality for positive linear maps*, J. Math. Anal. Appl. 402 (2013), 127–132; arXiv:1212.5690v1, §3, pp. 6–7.

§3, p. 6, Theorem 3.1 states verbatim:

> Theorem 3.1. [3] Let 0 < m ≤ A ≤ M and let X, Y be two partial isometries on H whose final spaces are orthogonal to each other. Then for every 2-positive linear map Φ, Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX) ≤ ((M−m)/(M+m))² Φ(X*AX).

§3, pp. 6–7, immediately before Conjecture 3.4:

> Despite the invalidity of (3.6), there is some evidence that the following assertion could be true. We have been unable to prove (or disprove) it.

§3, p. 7, Conjecture 3.4 states verbatim:

> Conjecture 3.4. Under the same condition as in Theorem 3.1. Then for every 2-positive linear map Φ, ‖Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX)Φ(X*AX)⁻¹‖ ≤ ((M−m)/(M+m))².

§3, p. 6, defines 2-positivity verbatim:

> Let Φ be a unital positive linear map between C*-algebras. We say that Φ is 2-positive if whenever the 2 × 2 operator matrix [[A, B],[B*, C]] is positive, then so is [[Φ(A), Φ(B)],[Φ(B*), Φ(C)]].

P. Zhang, *Remarks on an operator Wielandt inequality*, arXiv:1506.00737, describes Conjecture 3.4 as still open.

## Motivation

The order inequality in Theorem 3.1 suggests a corresponding product norm bound. Multiplication by an inverse can produce a non-normal similarity, so the order estimate does not automatically control the Euclidean operator norm.

## Gap

Conjecture 3.4 asserts the product norm estimate for every unital 2-positive map and orthogonal-range partial isometries. A finite-dimensional counterexample with invertible compressed images disproves this assertion. Preregistration: issue #16004.

## Route

Take $n=k=4$, $m=1/25$, $M=13$, and

$$
A=\begin{pmatrix}9&0&2&0\\0&2&1&0\\2&1&1&0\\0&0&0&1\end{pmatrix},\quad
X=P=\operatorname{diag}(1,1,0,0),\quad
Y=\begin{pmatrix}0&0&0&0\\0&0&0&0\\1&0&0&0\\0&1&0&0\end{pmatrix}.
$$

The complex-linear map $\Phi(Z)=PZP^*+YZY^*$ is unital and 2-positive. The two ranges are orthogonal and both $P,Y$ are partial isometries. Exact positive diagonal congruences certify $mI\le A\le MI$:

$$
A-mI=L\operatorname{diag}(224/25,49/25,33/9800,24/25)L^*,\quad
L=\begin{pmatrix}1&0&0&0\\0&1&0&0\\25/112&25/49&1&0\\0&0&0&1\end{pmatrix},
$$

$$
MI-A=U\operatorname{diag}(4,11,120/11,12)U^*,\quad
U=\begin{pmatrix}1&0&0&0\\0&1&0&0\\-1/2&-1/11&1&0\\0&0&0&1\end{pmatrix}.
$$

The compressed images are $\Phi(Y^*AY)=I$ and $D=\Phi(X^*AX)=\operatorname{diag}(9,2,9,2)$, with determinants 1 and 324. Their inverses are $I$ and $\operatorname{diag}(1/9,1/2,1/9,1/2)$.

For any positive block matrix $M_0$, its entrywise image under $\Phi$ equals $K_1M_0K_1^*+K_2M_0K_2^*$, where $K_1=\operatorname{diag}(P,P)$ and $K_2=\operatorname{diag}(Y,Y)$. Both summands are positive semidefinite. Also $PP^*+YY^*=I$, proving unitality.

## Falsifier

The product in Conjecture 3.4 is

$$
T=\operatorname{diag}(G,G),\qquad
G=\begin{pmatrix}4/9&1\\2/9&1/2\end{pmatrix}.
$$

For the unit vector $e_2$ (index 1 in `Fin 4`),

$$
\|Te_2\|^2=5/4>\left(\frac{26244}{26569}\right)^2,
\qquad \left(\frac{M-m}{M+m}\right)^2=\frac{26244}{26569}<1.
$$

Thus the asserted Euclidean operator norm bound fails with both inverses genuine.

## Evidence

`D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.lean` exposes only `IsPartialIsometry`, `IsUnitalTwoPositive`, `NormLE`, `claim`, and `result`; all witness data and helpers are private. `claim : Prop` contains all the source hypotheses and requires determinant units for both inverses. `result : ¬ claim` checks the two LDL* certificates, partial isometries, orthogonality, unital 2-positivity, images, determinants, inverses, product and squared norm. Its axiom closure is `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or additional axiom. Parameter-family and symmetrization reasoning below is not separately formalized.

## Triage

### What the settlement shows

1. **Proved (Lean) — Conjecture 3.4 fails.** The displayed $4\times4$ instance satisfies every hypothesis and violates the norm bound.

2. **Reasoning (exact mathematics, not separately formalized) — an unbounded family.** For $a\ge0$, put

   $$
   F_a=\begin{pmatrix}1&a&a&0\\0&-1&1&0\\0&0&1&0\\0&0&0&1\end{pmatrix},\qquad A_a=F_aF_a^{\mathsf T}.
   $$

   $F_a$ is invertible, so $A_a$ is positive definite. With the same $X,Y,\Phi$, the product consists of two identical blocks

   $$
   G_a=\begin{pmatrix}a^2/(1+2a^2)&a/2\\a/(1+2a^2)&1/2\end{pmatrix}.
   $$

   Hence $\|T_a\|\ge\|T_ae_2\|=\sqrt{a^2/4+1/4}\ge a/2\to\infty$. Every conjectured constant is below 1. This excludes any replacement that stays uniformly below 1. The condition number of $A_a$ varies with $a$; this family does not exclude all bounds depending on that condition number.

3. **Reasoning (exact mathematics, not separately formalized) — non-normal similarity.** Write $C=\Phi(X^*AY)$, $E=\Phi(Y^*AY)$, $D=\Phi(X^*AX)$, and $H=CE^{-1}C^*$. Theorem 3.1 gives $0\le H\le qD$ with $q=((M-m)/(M+m))^2$. Therefore $K=D^{-1/2}HD^{-1/2}$ has $0\le K\le qI$, but $\Gamma=HD^{-1}=D^{1/2}KD^{-1/2}$ is a non-normal similarity. Order controls $K$, whereas the product norm can be amplified by the similarity. In this instance $E=I$. A bound $\|\Gamma\|\le q\sqrt{\kappa(D)}$ follows from submultiplicativity, so condition-number-dependent bounds are not excluded.

4. **Consequences (logical reasoning, not separately formalized) — conditional applications.** Lin's Proposition 3.5 and the results in Zhang 2015 that assume Conjecture 3.4 retain their conditional logical form. The conjecture cannot supply their hypothesis in general; this counterexample alone does not refute their conclusions.

5. **Reasoning and open boundary — symmetrization.** For the literal $\Gamma=T$, the symmetric part $(\Gamma+\Gamma^*)/2$ has Rayleigh quotient $13/12>1$ on $(1,1,0,0)/\sqrt2$. Its absolute value has the same operator norm, so the literal quantity $\tfrac12|\Gamma+\Gamma^*|$ also violates the conjectured constant. This calculation is not separately formalized. Whether a distinct symmetrized assertion with Zhang's precise parameters and hypotheses admits that constant remains open here; identification and resolution of that variant are outside this Lean theorem.

## ASSUMED-UNVERIFIED

The exact parameter family, the similarity interpretation, and consequences for Lin's Proposition 3.5 and Zhang's conditional results are not additional Lean conclusions. The precise relation to Zhang's symmetrized variants is unresolved here.
