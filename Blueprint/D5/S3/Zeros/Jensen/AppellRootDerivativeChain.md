# Appell Root Derivative Chain

## Abstract

A strict polynomial operator budget controls the derivative chain at an actual root.

**Theorem 1.1 (Conditional polynomial operator estimate).**

$$\begin{aligned}\forall q\in \mathbb{N}, \forall P\in \mathbb{C}[X], \forall b\in \mathbb{C}, \forall s\in \mathbb{C}, \forall a\in \mathbb{R}, \forall g\in (\mathbb{N}\to \mathbb{C}), \\1\le q \Rightarrow \operatorname{natDegree}(P)=q \Rightarrow P(b)=0 \Rightarrow s\neq 0 \Rightarrow 0< a \Rightarrow \\s^{2} P^{(2)}-X P^{(1)}+q P=\sum_{2\le m< q} g_{m} P^{(m+1)} \Rightarrow \\\frac{\Vert b\Vert }{\Vert s\Vert ^{2} a}+\frac{q}{\Vert s\Vert ^{2} a^{2}}+\sum_{2\le m< q} \frac{\Vert g_{m}\Vert  a^{m-1}}{\Vert s\Vert ^{2}}<1 \Rightarrow \\P^{(1)}(b)\neq 0\land (\forall m\in \mathbb{N}, 1\le m \Rightarrow m\le q \Rightarrow \Vert \frac{P^{(m)}(b)}{P^{(1)}(b)}\Vert \le a^{m-1})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/AppellRootDerivativeChain.actual_root_derivative_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P is a complex polynomial of natural degree q. The point b is an actual root, s is a nonzero complex number, a is a positive real number, and g is an arbitrary sequence of complex coefficients. P^(m) denotes the m-fold polynomial derivative, with P^(0)=P. The operator equation is equality of polynomials, not merely equality at b. Every sum ranges over the natural indices 2 <= m < q. Norms are complex absolute values, and the row inequality is real.

Differentiate the operator equation k times and evaluate at b. The product rule gives s^2 P^(k+2)(b) = b P^(k+1)(b) - (q-k) P^(k)(b) + sum g_m P^(k+m+1)(b), for k+2 <= q. Derivatives above q vanish. The top derivative is the nonzero constant q! times the leading coefficient; monicity is unnecessary.

The finite sequence |P^(j)(b)|/a^j, for 0 <= j <= q, has a positive attained maximum M. Its zeroth entry is zero. If an index k+2 attains M, the differentiated equation and triangle inequality bound that entry by B M, where B is the displayed row budget. Since B < 1, this is impossible. The maximizing index is therefore one, giving a nonzero first derivative and all displayed ratios. For q=1 the higher-index range and coefficient sum are empty.

This is the polynomial implication used in LC359--LC361 of the repository's Romik analytic note. For its Appell specialization, P=R_(q,t)=M_t(partial_z) z^q, s^2=v chi', and a=8 sqrt(q)/|s|. The g_m are ordinary coefficients of the logarithmic remainder; in the cumulant convention g_m=kappa_(m+1)/m!. The actual source ODE and its coefficient and root-location budgets must be established separately. This theorem supplies no global node signs, RH or Robin conclusion, and makes no claim of literature originality.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/AppellRootDerivativeChain.actual_root_derivative_chain`
