# Linear functionals on pointwise convergence

## Abstract

Linear functionals on pointwise convergence

A continuous linear functional on a space of continuous linear maps with pointwise convergence is a finite sum of evaluations against continuous dual vectors. The finite set of input vectors arises from a basic neighborhood of zero. The source E is an additive commutative group with a topology and a module structure over an arbitrary normed field K1; the target F is a normed additive commutative group with a normed space structure over an RCLike field K.

**Theorem 1.1 (exists_finset_sum_eq).**

$$\forall \{K 1 : Type u_1\} \{K : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [RCLike.\{u_2\} K ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [NormedAddCommGroup.\{u_4\} F] [NormedSpace.\{u_2, u_4\} K F] (\phi : StrongDual.\{u_2, max u_4 u_3\} K (PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F)), \exists (s : Finset.\{u_3\} E) (g : E \to StrongDual.\{u_2, u_4\} K F), \forall (T : PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F), Eq.\{u_2 + 1\} (\phi T) (\sum x \in s, (g x) (T x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/LocallyConvex/PointwiseConvergence.exists_finset_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Seminorm.bound_of_continuous bounds phi by finitely many evaluations, so phi factors through the finite-coordinate linear map Phi:T mapped to (T x) on a finite set s. The norm bound makes this factor well defined on range(Phi). Module.Dual.exists_continuous_extension_of_le_seminorm extends it to all of the finite product; decomposing that extension by ContinuousLinearMap.sum_comp_single yields one continuous functional on F per coordinate and the required finite sum.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/LocallyConvex/PointwiseConvergence.exists_finset_sum_eq`
