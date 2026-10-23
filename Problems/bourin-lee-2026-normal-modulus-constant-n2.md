---
slug: bourin-lee-2026-normal-modulus-constant-n2
bibkey: bourinlee2026symmetricmodulus
doi: 10.1090/proc/17861
url: https://arxiv.org/abs/2602.19607v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result
---

# The normal-modulus triangle constant in dimension two

## Problem

J.-C. Bourin and E.-Y. Lee, *Triangle inequalities for the operator symmetric modulus*, arXiv:2602.19607v1, §4, Corollary 4.2, state verbatim:

> Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest possible one.

The following paragraph asks verbatim:

> However, contrarily to the Schur version (4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 (what is the best constant for n = 2 ?).

Here $|X|=(X^*X)^{1/2}$ is the positive modulus and the inequality uses positive-semidefinite order. The article is in press in *Proceedings of the American Mathematical Society*, doi:10.1090/proc/17861; the quotations and locators refer to the arXiv version.

## Motivation

Corollary 4.2 provides a uniform upper bound. The question is whether dimension two permits a smaller constant, with the unitary allowed to depend on the two normal matrices.

## Gap

The paper proves sharpness only for $n\ge3$ and asks for the best constant when $n=2$. The source's upper bound applies also to $n=2$, but its stated sharpness result does not settle that case.

## Route

Refute the existence of a real $c<1/4$ that works for every pair of normal complex $2\times2$ matrices. Use

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
M=\frac1{25}\begin{pmatrix}9&-12\\-12&16\end{pmatrix},\qquad B=-M.
$$

$M$ is the orthogonal projection onto $(3,-4)/5$. Both $A$ and $B$ are Hermitian and hence normal. The explicit positive matrices satisfying the modulus square identities are

$$
P_A=A,\qquad P_B=M,\qquad
A+B=\frac1{25}\begin{pmatrix}16&12\\12&-16\end{pmatrix},\qquad
P_S=\frac45 I.
$$

Put $D=P_A+P_B=A+M$ and $x=(1,2)$. The spectral calculation gives eigenvalues $2/5$ and $8/5$ for $D$, with $Dx=(2/5)x$. The Lean proof uses quadratic forms and positive-semidefinite certificates directly, rather than an eigenvalue theorem.

## Falsifier

The witness satisfies

$$
x^*Dx=2,\qquad x^*P_Sx=4,\qquad 0\le D\le\frac85 I,\qquad x^*x=5.
$$

For any unitary $V$, write $q=x^*VDV^*x$. Then $0\le q\le8$. The proposed inequality would give $4\le2+cq$. For $c\ge0$ it implies $4\le2+8c$, hence $c\ge1/4$. For $c<0$, $cq\le0$ already contradicts $4\le2+cq$. Thus the same displayed pair defeats every unitary for every $c<1/4$.

## Evidence

The public declarations in `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.lean` are `IsModulus`, `IsNormalMatrix`, `claim`, and `result`. The matrices `A`, `M`, `B`, `PS`, `D`, the vector `x`, and all supporting lemmas are private.

`IsModulus X P` means `P.PosSemidef ∧ P * P = Xᴴ * X`. `IsNormalMatrix X` means `Xᴴ * X = X * Xᴴ`. The modulus predicate pins positivity and the square identity; uniqueness of the positive square root is not invoked.

`claim` asserts that there exists a real $c<1/4$ such that, for every normal pair $A,B$ and every $P_A,P_B,P_S$ satisfying the three modulus predicates, there exists $V ∈ Matrix.unitaryGroup (Fin 2) ℂ$ for which

$$
P_A+P_B+cV(P_A+P_B)V^*-P_S\succeq0.
$$

The real scalar is cast to $\mathbb C$ in the matrix scalar multiplication. The theorem `D5.S3.Quantum.Matrix.NormalModulusTriangleConstant.result` has type `¬ claim`.

`modulus_A`, `modulus_M`, and `modulus_PS` check the three modulus predicates. `normal_A` and `normal_B` check normality. `d_pos`, `d_quad`, `ps_quad`, and `d_upper` prove positivity, the two quadratic-form values, and the upper certificate. `conjugation_quad` rewrites conjugation as evaluation on $V^*x$ for every matrix $V$. The proof of `result` uses these facts and unitarity to bound that quadratic form between zero and eight, and treats nonnegative and negative $c$ separately.

The module's axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. The general upper bound at $c=1/4$ is a source result, not a theorem in this module.

## Triage

### What the settlement shows

1. **Proved (Lean) — the lower bound.** For every real $c<1/4$, the displayed $2\times2$ Hermitian pair defeats every unitary $V$ in the proposed normal-modulus triangle inequality.

2. **Computed (source consequence, not formalized here) — the attained best constant.** Corollary 4.2 gives the upper bound at $c=1/4$ for every dimension. Combined with the Lean lower bound, it yields the attained best constant $1/4$ for $n=2$.

3. **Computed (exact mathematical reasoning) — the mechanism.** The sum $A+B$ is of reflection type: $(A+B)^2=(16/25)I$, so its modulus is the scalar matrix $(4/5)I$. Against this isotropic modulus, $D$ has spectral endpoints $2/5$ and $8/5$. Testing its lower eigenvector gives the ratio $((4/5)-(2/5))/(8/5)=1/4$; the same ratio governs the Schur version (4.1). The module proves the explicit square identities and quadratic-form bounds, but does not formalize the comparison with (4.1).

4. **Open — other positive maps in small dimensions.** Whether $1/4$ is sharp in Theorem 4.1 for other positive maps $\Phi$ between small dimensions is not settled by this pair and the normal-matrix result.

5. **Open — equality cases.** A classification of equality cases in the source inequalities is not established by the lower-bound proof.

## ASSUMED-UNVERIFIED

The journal version's text is unverified. The quotations and their locators bind to arXiv:2602.19607v1, §4; no exhaustive literature or priority claim is established.

The characterization “the positive square root is unique” is quoted, not proved or used by the Lean module. The proof checks positivity and the square identity for each displayed modulus. The general upper bound from Corollary 4.2 and the comparison with the Schur version (4.1) are not formalized here.
