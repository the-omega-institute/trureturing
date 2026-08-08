# Equality in Gibbs' Inequality

## Abstract

Equality in finite Gibbs' inequality characterizes identical probability distributions.

**Theorem 1.1 (Zero relative entropy characterizes equal distributions).**

$$\begin{gathered}\forall I\ [\operatorname{Fintype}(I)],\\\forall p, q: I\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \land \\((\forall i, 0\le q(i)) \land \sum_{i}q(i)=1) \land \\(\forall i, q(i)=0 \Rightarrow p(i)=0) \Rightarrow\\D(p\Vert q)=0 \Leftrightarrow p=q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite alphabet. Let p and q be nonnegative normalized real mass functions, and assume discrete absolute continuity: q(i) = 0 implies p(i) = 0. The divergence D is the real-valued finite klDivergence introduced in ClassicalDPI. Equality p = q is equality of functions and hence asserts p(i) = q(i) at every letter i.

Normalization rewrites D(p||q) as the finite sum of q(i) klFun(p(i)/q(i)). Every summand is nonnegative. If their sum is zero, the finite nonnegative-sum criterion makes every summand zero. Where q(i) is positive, Mathlib's unique-zero theorem for klFun gives p(i)/q(i) = 1 and therefore p(i) = q(i). Where q(i) is zero, absolute continuity gives the same conclusion directly.

Conversely, if p and q agree pointwise, every defining summand of the divergence vanishes. Thus D(p||q) = 0 if and only if p = q. The proof uses the previously established Gibbs nonnegativity theorem and the strict zero characterization already supplied by Mathlib; it introduces neither a new divergence nor a second strict-convexity proof.

## References

- Truth anchor: `D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
