# Passive Memory No-Backreaction

## Abstract

Passive triangular memory stores order without changing scalar spectral invariants.

**Theorem 1.1 (The adjacent-swap defect is explicitly off-diagonal).**

$$\forall F, v, L_{p}, L_{q}: \mathbb{C},\\{}\operatorname{memoryHolonomy}(F, v, L_{p}, L_{q}) = \begin{pmatrix}0&(L_{q} - L_{p})(F - 1)v\\0&0\end{pmatrix}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex memory update F, injection scale v, and readouts Lp and Lq, reversing the two prime-memory factors produces the displayed matrix with only its upper-right entry potentially nonzero.

The formula identifies the defect exactly as (Lq - Lp)(F - 1)v. It does not assert that every adjacent swap is nontrivial, since that scalar can vanish.

**Theorem 1.2 (The adjacent-swap defect has zero trace).**

$$\forall F, v, L_{p}, L_{q}: \mathbb{C},\\{}\operatorname{tr}(\operatorname{memoryHolonomy}(F, v, L_{p}, L_{q})) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex choice of F, v, Lp, and Lq, the trace of the adjacent-swap memory holonomy is zero. This follows from the zero diagonal in the explicit defect matrix.

Trace blindness is only a scalar invariant statement. It does not make the holonomy matrix zero or rule out a nonzero off-diagonal record of order.

**Theorem 1.3 (The adjacent-swap defect has zero determinant).**

$$\forall F, v, L_{p}, L_{q}: \mathbb{C},\\{}\operatorname{det}(\operatorname{memoryHolonomy}(F, v, L_{p}, L_{q})) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_det_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex choice of F, v, Lp, and Lq, the determinant of the adjacent-swap memory holonomy is zero. The explicit defect is strictly upper triangular.

A zero determinant records singularity, not equality with the zero matrix. The theorem therefore remains compatible with a nonzero off-diagonal order defect.

**Theorem 1.4 (Changing the passive injection preserves trace).**

$$\forall F, L, B_{1}, B_{2}: \mathbb{C},\\{}\operatorname{tr}(\operatorname{passiveMemoryMatrix}(F, B_{1}, L)) = \operatorname{tr}(\operatorname{passiveMemoryMatrix}(F, B_{2}, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_trace_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed complex diagonal entries F and L, replacing injection B1 by B2 leaves the trace of the passive memory matrix unchanged. Only the upper-right entry varies.

The equality is restricted to changes of the injection coordinate. It makes no invariance claim when either diagonal entry F or L is changed.

**Theorem 1.5 (Changing the passive injection preserves determinant).**

$$\forall F, L, B_{1}, B_{2}: \mathbb{C},\\{}\operatorname{det}(\operatorname{passiveMemoryMatrix}(F, B_{1}, L)) = \operatorname{det}(\operatorname{passiveMemoryMatrix}(F, B_{2}, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_det_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed complex diagonal entries F and L, replacing injection B1 by B2 leaves the determinant of the passive memory matrix unchanged. The determinant depends only on the diagonal.

This is an injection-blind scalar invariant, not an equality of the two matrices. Distinct upper-right entries can still encode different memory data.

**Theorem 1.6 (Changing the passive injection preserves the characteristic polynomial).**

$$\forall F, L, B_{1}, B_{2}: \mathbb{C},\\{}\operatorname{charpoly}(\operatorname{passiveMemoryMatrix}(F, B_{1}, L)) = \operatorname{charpoly}(\operatorname{passiveMemoryMatrix}(F, B_{2}, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_charpoly_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed complex diagonal entries F and L, the passive memory matrices with injections B1 and B2 have the same characteristic polynomial. Their scalar spectral roots therefore agree.

The result does not say that the matrices, their off-diagonal memory entries, or their products are equal. It isolates the lack of spectral backreaction for this triangular lift.

**Theorem 1.7 (A concrete pair of passive memory matrices does not commute).**

$$\forall M, N: \operatorname{MemoryMatrix},\\{}(M = \operatorname{passiveMemoryMatrix}(2, 1, 2) \land N = \operatorname{passiveMemoryMatrix}(2, 2, 3)) \Rightarrow\\{}M\,N \neq N\,M.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_order_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two matrices fixed by the displayed premises are precisely the passive lifts with parameters (2, 1, 2) and (2, 2, 3). Their products differ, giving a concrete order-sensitive witness.

This establishes existence of noncommuting passive memory steps, not noncommutativity for every parameter choice. Together with the invariance results, it separates stored order from scalar spectral change in this example.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_det_zero`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_formula`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.memory_holonomy_trace_zero`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_charpoly_invariant`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_det_invariant`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_order_witness`
- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.passive_memory_trace_invariant`
