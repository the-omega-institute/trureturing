# Monotonicity with Finitely Many Exceptional Values

## Abstract

Continuity and nonnegative derivatives outside finitely many values imply interval monotonicity.

**Theorem 1.1 (Nonnegative derivatives away from exceptional values).**

$$\forall (f : \mathbb{R} \to \mathbb{R}), \forall (a : \mathbb{R}), \forall (b : \mathbb{R}), \forall (S : \operatorname{Set}(\mathbb{R})), (\operatorname{Finite}(S)) \Rightarrow (\operatorname{ContinuousOn}(f, \operatorname{Icc}(a, b))) \Rightarrow (\forall (t : \mathbb{R}), (t \in \operatorname{Ioo}(a, b)) \Rightarrow (\neg (\operatorname{f}(t) \in S)) \Rightarrow \exists (r : \mathbb{R}), \operatorname{HasDerivAt}(f, r, t) \land 0 \leq r) \Rightarrow \operatorname{MonotoneOn}(f, \operatorname{Icc}(a, b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity.monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a real-valued function continuous on the closed interval [a,b], and let S be a finite set of real values. At every interior point t for which f(t) is outside S, assume there is a real r such that HasDerivAt f r t and r is nonnegative. Then f is nondecreasing on [a,b]: whenever x and y belong to this interval and x is at most y, f(x) is at most f(y). The endpoints a and b are arbitrary; a reversed interval is empty, and a singleton interval also satisfies the conclusion.

The finiteness assumption concerns values, not domain points. The preimage of S can be infinite, and the derivative condition imposes no requirement there. For example, f(x) = max(0,x) on [-1,1] has S = {0} and preimage [-1,0]. It is continuous, has derivative 1 wherever its value is outside S, and is monotone, although it is not differentiable at zero. This illustrates the criterion without requiring a finite exceptional set of inputs.

Suppose instead that x is at most y but f(y) is strictly below f(x). Finiteness of S gives levels u and v strictly between f(y) and f(x), with u below v and with the entire open value interval (u,v) disjoint from S. The finite-set induction constructs such a gap by retaining a smaller interval on one side of each additional exceptional value.

Continuity and the intermediate value theorem make the level-u set in [x,y] nonempty. This level set is compact, so it has a first point c. Within [x,c], the level-v set is likewise nonempty and compact; let d be its last point. Then x is at most d, d is strictly below c, c is at most y, f(d) = v and f(c) = u. If an interior point of (d,c) had value at most u, the intermediate value theorem would give an earlier level-u crossing, contradicting the choice of c. If it had value at least v, it would give a later level-v crossing before c, contradicting the choice of d. Thus all interior values lie strictly in (u,v).

Every point of (d,c) is therefore an interior point of [a,b] whose value avoids S. Its nonnegative HasDerivAt witness gives differentiability and a nonnegative value of deriv. The mean-value monotonicity theorem, monotoneOn_of_deriv_nonneg, applies on [d,c] and yields f(d) at most f(c). This says v is at most u, contradicting the chosen gap. Equivalently, the descending secant would force a negative derivative by the mean value theorem.

An intended application is to a weighted extended-angle scalar function. Such an application must supply continuity, a finite set of exceptional angle values, and the nonnegative native derivative at every interior point avoiding those values. The native derivative formula and the right-inverse identity needed for that application remain unproved by this generic lemma. The conclusion here is the stated interval criterion; native and source-global monotonicity require those additional mathematical steps.

## References

- Truth anchor: `D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity.monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values`
