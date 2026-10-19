---
slug: czerwinska-franco-merino-2026-radial-convexity-matrix-monotonicity
bibkey: czerwinska2026radial
doi: 10.48550/arXiv.2610.17393
url: https://arxiv.org/abs/2610.17393
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result
---

# Czerwińska–Franco–Merino: radial convexity and matrix monotonicity

## Problem

M. M. Czerwińska, J. A. Franco and A. Merino, *Towards a Characterization of Matrix Monotonicity via Radial Convexity*, arXiv:2610.17393v1, §4, Conjecture 4.10. See [czerwinska2026radial](../Library/Eigenstructure/czerwinska2026radial.md).

> Let f : (0, ∞) → R. Then f is radially convex of order n (with respect to the Frobenius norm) if and only if f is matrix monotone of degree n.

arXiv:2610.17393v1, §4, directly after Conjecture 4.10, verbatim:

> By Proposition 3.9, matrix monotonicity of degree n implies radial convexity of order n. Thus, it remains to prove the converse implication. The next theorem establishes the conjecture for n = 2.

The matrices are complex Hermitian positive definite, and the order is Loewner order. Radial convexity requires both endpoint distance inequalities for every ordered triple $A\preceq C\preceq B$. Matrix monotonicity allows either of the two uniform order directions. The universal assertion quantifies over every $n\ge1$ and every real function on the positive half-line.

## Motivation

The conjecture proposes that metric growth along ordered intervals characterizes preservation of the matrix order. The external problem and explicit degree-three candidate are preregistered in [issue #19013](https://github.com/the-omega-institute/trureturing/issues/19013).

arXiv:2610.17393v1, §1, verbatim:

> In degree 3, we show that radial convexity already provides the principal minor conditions required for matrix monotonicity, leaving the sign of the determinant of the Loewner matrix as the remaining obstruction.

## Gap

Endpoint distance growth depends on a positive composition of the derivative with a full increment. It need not require the derivative itself to preserve every positive direction. Three spectral nodes allow a small negative resolvent component to violate matrix monotonicity while retaining both endpoint derivative inequalities.

## Route

Set $\varepsilon=1/20000$ and

$$
f(t)=\frac{t+1}{t+3}+\frac{t+1}{2t+4}-\varepsilon\frac{t+1}{3t+5}.
$$

The order-preserving Cayley map $h(A)=I-2(A+I)^{-1}$ takes the positive cone into $-I\prec X\prec I$ and identifies $f(A)$ with $g(h(A))$, where $g=R_2+R_3-\varepsilon R_4$ and $R_s(X)=(sI-X)^{-1}$.

At either endpoint of $U\preceq V$, write the resolvent increment as $R_s(C)Z_sR_s(C)$ with $(V-U)/3\preceq Z_s\preceq3(V-U)$. Three-node spectral interpolation bounds the sum of the two mixed quadratic forms by $54$ times the three unmixed forms. Expanding the sandwich derivative leaves the positive coefficient $1/3-324\varepsilon=4757/15000$. Trace self-adjointness and differentiation of squared Frobenius distances along segments yield both radial inequalities. The argument includes singular increments and repeated eigenvalues.

## Falsifier

For the same scalar function, take

$$
A=\operatorname{diag}(1/3,1,3),\quad
B=\tfrac1{25}\begin{pmatrix}11&4&8\\4&31&12\\8&12&99\end{pmatrix}.
$$

Both are positive definite and $B-A=(2/75)ww^*$ with $w=(2,3,6)^T$. At $v=(-35,48,-15)^T$,

$$
v^*(f(B)-f(A))v=-\frac2{111549375}<0,
\qquad (f(B)-f(A))_{00}=\frac{1833242113439}{80513884788750}>0.
$$

The first sign excludes the increasing direction and the second excludes the decreasing direction. Exact rational inverse tables certify both signs.

## Evidence

`D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result : ¬ conjecture` targets the full conjecture. The proof combines global order-three radial convexity with the exact same function's failure of both monotonicity directions. Continuous functional calculus identifies the rational expression on every positive definite matrix, and the Frobenius norm is the Euclidean norm of all matrix entries.

## Triage

**REFUTED — Conjecture 4.10 at $n=3$.** The displayed function satisfies the full radial property on the positive cone and neither monotonicity direction.

**COMPUTED — the remaining Loewner-determinant obstruction named in §1 is real at $n=3$.** For the displayed function and nodes $x=(1/3,1,3)$, the Loewner matrix has entries

$$
L_{ij}=\frac{2}{(x_i+3)(x_j+3)}
+\frac{2}{(2x_i+4)(2x_j+4)}
-\frac{2\varepsilon}{(3x_i+5)(3x_j+5)},
\qquad \det L=-\frac{1}{175032900000000}<0.
$$

This formula includes $L_{ii}=f'(x_i)$. Exact rational arithmetic gives positive diagonal entries and positive principal minors of size two. Thus the Loewner-determinant sign can fail while radial convexity holds. The determinant and minor calculations are not Lean theorems here; the Lean result proves the full degree-three radial property together with failure of both matrix-monotonicity directions.

**LITERATURE — the differentiable $n=2$ case is true by the paper's Theorem 4.11.** Its regularity hypotheses are retained; this counterexample does not affect that result.

**OPEN — failure of the equivalence at every $n\ge3$.** Direct sum with a positive scalar block propagates the finite nonmonotonicity obstruction, since functional calculus acts blockwise and the negative quadratic form persists on a vector supported on the first three coordinates. It does not prove the radial property for arbitrary matrices in the larger cone. The three-node estimate does not supply that missing implication.

**OPEN — a characterization of radial convexity.** The counterexample separates it from same-degree matrix monotonicity without supplying a replacement characterization.

## ASSUMED-UNVERIFIED

The offline implementation uses the supplied source and preregistration. No independent current online literature search, absence of subsequent settlements, or worldwide priority is asserted. The paper's order-two theorem is contextual literature, and the higher-dimensional direct-sum argument is not formalized here.
