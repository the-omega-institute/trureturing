# Central Cycle Realizations

## Abstract

The normalized product around the cycle is a central Hermitian involution K.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Definition 1.1 (pathWord).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\\forall (A : \mathbb{N} \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{pathWord} (R : = R) (A : = A) (k : = k) : R) = (((\operatorname{List} . \operatorname{range} k) . \operatorname{map} A) . \operatorname{prod})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.pathWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pathWord.

**Definition 1.2 (loopSign).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\(\operatorname{loopSign} (n : = n) : \mathbb{C}) = (((- 1))^{n})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.loopSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines loopSign.

**Definition 1.3 (normalizedLoop).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (n : \mathbb{N}),\\\forall (A : \mathbb{N} \to R),\\\forall (B : R),\\(\operatorname{normalizedLoop} (R : = R) (n : = n) (A : = A) (B : = B) : R) = (\operatorname{loopSign} n \cdot (\operatorname{pathWord} A (2 \cdot n + 1) \cdot B))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.normalizedLoop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines normalizedLoop.

**Lemma 1.4 (central relabel parent).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (B : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (t : \mathbb{R}),\\\forall (v_{0} : \operatorname{Fin} m),\\\forall (K : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(K . \operatorname{IsHermitian}) \to\\(K \cdot K = 1) \to\\(\forall v , K \cdot A v = A v \cdot K) \to\\(\forall v , B v = \operatorname{if} v = v_{0} \operatorname{then} K \cdot A v \operatorname{else} A v) \to\\(\forall v , (A v) . \operatorname{trace} = 0) \to\\(\forall v , (B v) . \operatorname{trace} = 0) \to\\(\operatorname{JM} B t) \to\\\operatorname{JM} A t\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.central_relabel_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This central relabel parent identity is used in the CentralCycleRealizations construction.

**Lemma 1.5 (natural cycle adj).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\(2 \leq M) \to\\\forall (u : \operatorname{Fin} M),\\\forall (v : \operatorname{Fin} M),\\(\operatorname{SimpleGraph} . \operatorname{cycleGraph} M) . \operatorname{Adj} u v \iff u . \operatorname{val} + 1 = v . \operatorname{val} \lor v . \operatorname{val} + 1 = u . \operatorname{val} \lor (u . \operatorname{val} = 0 \land v . \operatorname{val} + 1 = M) \lor (v . \operatorname{val} = 0 \land u . \operatorname{val} + 1 = M)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.natural_cycle_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This natural cycle adj identity is used in the CentralCycleRealizations construction.

**Definition 1.6 (cyclePrefix).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (M : \mathbb{N}),\\\forall (A : \operatorname{Fin} M \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (k : \mathbb{N}),\\(\operatorname{cyclePrefix} (d : = d) (M : = M) (A : = A) (k : = k) : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) = (\operatorname{if} k + 1 < M \operatorname{then} A \langle k , \cdot \rangle \operatorname{else} 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.cyclePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines cyclePrefix.

**Lemma 1.7 (realization cycle loop).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(1 \leq n) \to\\\forall (A : \operatorname{Fin} (2 \cdot n + 2) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{cycleGraph} (2 \cdot n + 2)) A) \to\\\operatorname{let} K : = \operatorname{normalizedLoop} n (\operatorname{cyclePrefix} A) (A \langle 2 \cdot n + 1 , \cdot \rangle) ; K . \operatorname{IsHermitian} \land K \cdot K = 1 \land (\forall j , K \cdot A j = A j \cdot K) \land K \cdot A \langle 2 \cdot n + 1 , \cdot \rangle = \operatorname{loopSign} n \cdot \operatorname{pathWord} (\operatorname{cyclePrefix} A) (2 \cdot n + 1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.realization_cycle_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This realization cycle loop identity is used in the CentralCycleRealizations construction.

**Lemma 1.8 (cycle majorana extension).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(1 \leq n) \to\\\forall (A : \operatorname{Fin} (2 \cdot n + 2) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{cycleGraph} (2 \cdot n + 2)) A) \to\\\operatorname{let} P : = \operatorname{cyclePrefix} A ; \operatorname{let} K : = \operatorname{normalizedLoop} n P (A \langle 2 \cdot n + 1 , \cdot \rangle) ; \operatorname{let} g : = \operatorname{pathMajorana} (\operatorname{liftPath} P) (\operatorname{liftSeed} d) ; (\forall k , k \leq 2 \cdot n + 1 \to g k \cdot g k = 1) \land (\forall k , k \leq 2 \cdot n + 1 \to \operatorname{star} (g k) = g k) \land (\forall j , j \leq 2 \cdot n + 1 \to \forall i , i < j \to g i \cdot g j = - (g j \cdot g i)) \land (\forall k , k < 2 \cdot n + 1 \to \operatorname{Complex} . I \cdot (g k \cdot g (k + 1)) = \operatorname{liftPath} P k) \land (- \operatorname{Complex} . I) \cdot (g (2 \cdot n + 1) \cdot g 0) = (K \cdot A \langle 2 \cdot n + 1 , \cdot \rangle) (\operatorname{Matrix}.\operatorname{kronecker}) \operatorname{qubitZ}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.cycle_majorana_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized product around the cycle is a central Hermitian involution K. It corrects the closing observable before the path extension. The last equation retains K explicitly and verifies the antiperiodic closing bond; no irreducibility or fixed central-sector assumption is imposed.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.central_relabel_parent`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.cyclePrefix`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.cycle_majorana_extension`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.loopSign`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.natural_cycle_adj`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.normalizedLoop`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.pathWord`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.realization_cycle_loop`
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations](CliffordPathRealizations.md)
