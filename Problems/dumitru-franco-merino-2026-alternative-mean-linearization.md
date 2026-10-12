---
slug: dumitru-franco-merino-2026-alternative-mean-linearization
bibkey: dumitrufrancomerino2026alternative
doi: 10.48550/arXiv.2606.25150
url: https://arxiv.org/abs/2606.25150v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/AlternativeMeanLinearization.result
---

# Characterizing rigid alternative means

## Problem

R. Dumitru, J. Franco, and A. Merino, *On The Linearization of Alternative Means*, arXiv:2606.25150v1, §1, ask in the supplied verbatim text:

> Question : Can we characterize all functions f : (0, ∞) → (0, ∞) such that Aσ̂_f B is linearizable if and only if AB = BA and |Spec(A⁻¹♯B)| ≤ 2 ?

Remark 4.4 restates this question. Definition 2.3 specifies $A\widehat\sigma_fB=f(Y)Af(Y)$ with $Y=A^{-1}\sharp B$, for continuous positive $f$ with $f(1)=1$. Remark 2.2 calls a mean linearizable when it equals $aA+bB$ for real $a,b$.

## Motivation

The geometric mean of $A^{-1}$ and $B$ is the positive definite solution of $YAY=B$. Its spectrum is the natural scalar parameter for the alternative mean. A characterization distinguishes the functions for which linearizability detects both matrix commutation and a spectrum of size at most two.

## Gap

Remark 4.3 gives a sufficient condition: $f^2$ increasing and strictly concave, and $x\mapsto f(x)/x$ injective. The Question asks for all functions, so the necessary conditions and their sufficiency must both be established. The theorem here settles the question for $D=\mathbb C$.

## Route

Put $g(s)=f(\sqrt{s})^2$. The characterization is that $f$ and $x\mapsto f(x)/x$ are injective on $(0,\infty)$ and $g$ is strictly convex or strictly concave there.

For a positive definite pair, diagonalize $Y=A^{-1}\sharp B=U\operatorname{diag}(t_i)U^*$ and put $C=U^*AU$. Linearizability gives

$$
(f(t_i)f(t_j)-a-bt_it_j)C_{ij}=0.
$$

Since $C_{ii}>0$, each graph point $(t_i^2,g(t_i^2))$ lies on the same affine line. Strict convexity or concavity excludes three distinct points. For two distinct spectral values $x,y$, set $u=f(x)$ and $v=f(y)$. The diagonal equations imply

$$
uv-a-bxy=-\frac{(u-v)(yu-xv)}{x+y}.
$$

Both factors in the numerator are nonzero by the two injectivity conditions, so $C_{ij}=0$ between distinct eigenspaces. This proves $AY=YA$ and $AB=BA$. Conversely, $AB=BA$ implies $AY=YA$ by functional calculus. On at most two positive spectral values, interpolate $f(t)^2=a+bt^2$; then $f(Y)Af(Y)=aA+bB$.

## Falsifier

Failure of either injectivity condition is detected in dimension two. Take

$$
A=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
Y=\operatorname{diag}(x,y),\qquad B=YAY,
\qquad x,y>0,\quad x\ne y.
$$

If $f(x)=f(y)=c$, the mean is $c^2A$. If $f(x)/x=f(y)/y=c$, it is $c^2B$. Both means are linearizable, whereas $(AB-BA)_{12}=2(y^2-x^2)\ne0$.

If three points $(s,g(s)),(t,g(t)),(u,g(u))$, with $0<s<t<u$, are collinear, take $A=I$ and $B=\operatorname{diag}(s,t,u)$. The mean is $\operatorname{diag}(g(s),g(t),g(u))=aI+bB$, but $Y=\operatorname{diag}(\sqrt{s},\sqrt{t},\sqrt{u})$ has three spectral values. Thus adjacent slopes never agree. Their difference is continuous and nonzero on the convex domain $0<s<t<u$, hence has constant sign. The slope criteria give strict convexity or strict concavity of $g$.

## Evidence

Settlement: **Proved (Lean, $D=\mathbb C$)**. The public declarations in `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.lean` are `gmInv`, `altMean`, `Linearizable`, `Rigid`, and `result`. Every supporting declaration is private.

The theorem `D5.S3.Quantum.Matrix.AlternativeMeanLinearization.result` states the characterization for every real function continuous and positive on $(0,\infty)$ and normalized at 1. `Rigid` quantifies over every finite dimension and every pair of complex positive definite matrices. Matrix functions use Mathlib's continuous functional calculus, and the spectrum is the real spectrum of the Hermitian matrix $Y$.

The proof establishes positivity, the Riccati identity and uniqueness for the specified geometric mean, spectral reduction, the off-diagonal identity, interpolation on spectra of size at most two, all three necessity constructions, and the global slope-sign argument. The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom.

## Triage

1. **Proved (Lean, $D=\mathbb C$) — the characterization.** The three scalar conditions are necessary and sufficient for the equivalence in the Question, uniformly in matrix size.

2. **Reasoning, not formalized — other scalar fields.** The proof works verbatim over $\mathbb R$ and over the quaternions, using the corresponding spectral theorem for positive definite self-adjoint matrices. The spectral values, interpolation coefficients, and off-diagonal factors are real, so they commute with quaternionic entries. These extensions are not assertions of the Lean theorem.

3. **Reasoning, not formalized — relation to Remark 4.3.** If $f^2$ is increasing and strictly concave, positivity makes $f$ injective and composition with the increasing strictly concave square root makes $g$ strictly concave. The separate injectivity assumption on $f(x)/x$ is exactly the second condition. The characterization strictly contains this sufficient class: the Wasserstein function $f(x)=(1+x)/2$ satisfies both injectivity conditions and has $g(s)=(1+\sqrt{s})^2/4$ strictly concave, while $f(x)^2$ is strictly convex. Indeed, $f(x)/x=1/2+1/(2x)$ is strictly decreasing, and $g''(s)=-1/(8s^{3/2})<0$. In contrast, $f(x)=x$ has constant quotient and gives the always-linearizable mean $B$, so it fails the equivalence.

4. **Reasoning, not formalized — dependence on dimension.** If the equivalence is required only in dimension two, only the two injectivity conditions are needed: the spectrum already has at most two values, and the same off-diagonal identity proves commutation. In dimension one every function works, because matrices commute, the spectrum has at most one value, and the scalar mean is a real multiple of $A$.

5. **Open — other mean families.** Analogous characterization questions for the other mean families mentioned in the paper remain outside this theorem.

## ASSUMED-UNVERIFIED

The supplied quotations and locators bind to arXiv:2606.25150v1; their agreement with the author text is ASSUMED-UNVERIFIED. No exhaustive literature or priority claim is established. The real and quaternionic extensions, the comparison with Remark 4.3, the Wasserstein example, and the statements restricted to dimensions one and two are mathematical reasoning and are not separately formalized here.
