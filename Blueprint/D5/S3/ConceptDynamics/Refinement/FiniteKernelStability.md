# Finite Kernel Stability

## Abstract

Finite predictive kernel chains stabilize within their class-count budget.

**Theorem 1.1 (Finite predictive kernels stabilize).**

$$\begin{gathered}\forall X, O, F: X \to X, q: X \to O,\\(\forall m, E(m+1) \subseteq E(m)) \land\\(\forall r, E(N+r) = E(N)) \land\\(\forall m < N, E(m+1) \neq E(m)) \land\\c(0) = \lvert O \rvert \land\\N \leq c(N) - c(0) \leq \lvert X \rvert - c(0) \land\\(x, y) \in E(N) \iff (\forall k, q(F^{k}(x)) = q(F^{k}(y))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/FiniteKernelStability.finite_kernel_chain_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite nonempty state space, let F update its states, and let q map X surjectively onto the initial readout classes O. Write E_m for the kernel of the prediction word through depth m, c_m for its number of classes, and N for the least depth where two consecutive kernels agree.

The kernels form a decreasing chain. At N the chain becomes permanently constant, while every transition before N is strict. Consequently the number N of strict refinements is at most c_N minus c_0, and that class gain is at most the unused finite-state budget card(X) minus c_0. Surjectivity identifies c_0 with card(O).

Equality at the finite depth N is equivalent to equality of every future readout. Thus all distinctions visible in the infinite future have appeared after a finite, system-dependent depth.

The proof directly applies the repository's exact finite observation refinement bound and permanent partition-stability theorem. The new declaration is only the thin kernel-chain wrapper required by this source statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/FiniteKernelStability.finite_kernel_chain_stability`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../../Observer/Separation/FiniteObservationRefinementBound.md)
