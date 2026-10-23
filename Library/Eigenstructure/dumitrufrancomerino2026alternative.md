---
bibkey: dumitrufrancomerino2026alternative
authors: R. Dumitru; J. Franco; A. Merino
year: 2026
title: "On The Linearization of Alternative Means"
doi: 10.48550/arXiv.2606.25150
url: https://arxiv.org/abs/2606.25150v1
claim: "Can we characterize all functions f : (0, ∞) → (0, ∞) such that Aσ̂_f B is linearizable if and only if AB = BA and |Spec(A⁻¹♯B)| ≤ 2 ?"
strata_touched:
  - D5/S3/Quantum/Matrix/AlternativeMeanLinearization
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2606.25150v1>.
- DOI: https://doi.org/10.48550/arXiv.2606.25150

R. Dumitru, J. Franco, and A. Merino, *On The Linearization of Alternative Means*, arXiv:2606.25150v1, §1, Remark 2.2, Definition 2.3, and Remarks 4.3–4.4.

## Question and definitions

The Question in §1 (p. 3), restated as a problem in Remark 4.4, reads:

> Question : Can we characterize all functions f : (0 , ∞) → (0 , ∞) such that Aσ̂_f B is linearizable if and only if AB = BA and |Spec(A⁻¹♯B)| ≤ 2 ?

Definition 2.3 (p. 5) reads:

> Let f : (0 , ∞) → (0 , ∞) be a continuous function such that f(1) = 1. The alternative mean associated with f is the binary operation σ̂_f : P_n(D) × P_n(D) → P_n(D) defined by Aσ̂_f B = f(A⁻¹♯B) A f(A⁻¹♯B), (A , B ∈ P_n(D)).

Remark 2.2 (p. 4), items (1) and (2), reads in part:

> (1) Let σ be a Kubo-Ando mean on P_n(D). For two matrices A , B ∈ P_n(D), we say that AσB is linearizable if there exists a , b ∈ R such that AσB = aA + bB.
>
> (2) We denote by ♯ the geometric mean, i.e. the Kubo-ando mean corresponding to f(x) = √x. In particular, A♯B = A^{1/2}(A^{−1/2}BA^{−1/2})^{1/2}A^{1/2}, (A , B ∈ P_n(D)).

Remark 4.3 (p. 11) reads:

> The proof of Theorem 4.2 shows that the operator monotonicity assumption can be weakened. Indeed, the spectral part only uses that f² is increasing and strictly concave, while the commutativity part uses that the function x ↦ f(x)/x is injective on (0 , ∞). Therefore, the conclusion of Theorem 4.2 remains valid for any continuous function f : (0 , ∞) → (0 , ∞), with f(1) = 1, and satisfying these two conditions.

The geometric mean is

$$
A\sharp B=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2}.
$$

Applying this to $A^{-1}$ gives

$$
Y=A^{-1}\sharp B=A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2},
\qquad YAY=B,
$$

where the last equality is equation (1). Positive definiteness makes $Y$ the unique positive definite solution of that equation.

## Repository-derived result

For complex positive definite matrices in every finite dimension, the companion theorem characterizes the functions in the Question. Let $f$ be continuous and positive on $(0,\infty)$ with $f(1)=1$, and set $g(s)=f(\sqrt{s})^2$. The required equivalence holds for every dimension and every pair of positive definite matrices exactly when

1. $f$ is injective on $(0,\infty)$;
2. $x\mapsto f(x)/x$ is injective on $(0,\infty)$;
3. $g$ is strictly convex or strictly concave on $(0,\infty)$.

Diagonalizing $Y$ and writing $C=U^*AU$ turns linearizability into

$$
(f(t_i)f(t_j)-a-bt_it_j)C_{ij}=0.
$$

The positive diagonal entries imply $g(t_i^2)=a+bt_i^2$. Strict convexity or concavity permits at most two distinct eigenvalues. For distinct $x,y$, writing $u=f(x)$ and $v=f(y)$, the diagonal equations give

$$
uv-a-bxy=-\frac{(u-v)(yu-xv)}{x+y}.
$$

The two injectivity conditions make this nonzero, forcing the corresponding entries of $C$ to vanish. Thus $A$ commutes with $Y$ and hence with $B=YAY$. Conversely, commutation of $A$ and $B$ implies commutation of $A$ and $Y$ through the continuous functional calculus. Two spectral values permit interpolation of $f(t)^2$ by $a+bt^2$, proving linearizability.

Necessity uses $A=\begin{pmatrix}2&1\\1&2\end{pmatrix}$ and $Y=\operatorname{diag}(x,y)$ for each injectivity condition. A collinear triple in the graph of $g$ gives a linearizable diagonal pair in dimension three with three spectral values. Continuity then makes the nonzero adjacent-slope difference have constant sign on the connected domain $0<s<t<u$, yielding strict convexity or strict concavity.

## Neighboring references

Remark 4.3 supplies a sufficient condition rather than this full characterization. Questions about other mean families mentioned in the source are not settled by the companion theorem.

## ASSUMED-UNVERIFIED

No exhaustive literature or priority claim is established. The formal theorem concerns complex matrices; real and quaternionic extensions are mathematical reasoning rather than formal results of this module.
