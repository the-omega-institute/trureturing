# Clifford Path Realizations

## Abstract

One qubit ancilla gives a seed that anticommutes with the first path generator and commutes with all subsequent generators.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Definition 1.1 (Realization).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (G : \operatorname{SimpleGraph} (\operatorname{Fin} m)),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\operatorname{Realization} (m : = m) (d : = d) (G : = G) (A : = A) \iff (1 \leq d \land (\forall (v : \operatorname{Fin} m) , (A v) . \operatorname{IsHermitian}) \land (\forall (v : \operatorname{Fin} m) , A v \cdot A v = 1) \land (\forall (u v : \operatorname{Fin} m) , u \neq v \to G . \operatorname{Adj} u v \to A u \cdot A v = - (A v \cdot A u)) \land (\forall (u v : \operatorname{Fin} m) , u \neq v \to \neg G . \operatorname{Adj} u v \to A u \cdot A v = A v \cdot A u))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.Realization` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

McNulty, Definition 1, p. 3: "The anti-commutativity graph G = (V,E) of a set of observables 𝒜 is defined by {v,v′} ∈ E ⇔ A_v A_v′ = −A_v′ A_v, so that adjacent vertices correspond to anti-commuting observables, and non-adjacent vertices correspond to commuting ones." The carrier is Matrix (Fin d) (Fin d) ℂ with 1 ≤ d. Every observable is Hermitian and squares to the identity. Vertices are zero-indexed; the graph is Mathlib's pathGraph or cycleGraph.

**Definition 1.2 (noisyObservable).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (eta : \mathbb{R}),\\\forall (v : \operatorname{Fin} m),\\(\operatorname{noisyObservable} (m : = m) (d : = d) (A : = A) (eta : = eta) (v : = v) : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) = ((eta : \mathbb{C}) \cdot A v + ((A v) . \operatorname{trace} / (d : \mathbb{C}) \cdot (1 - (eta : \mathbb{C}))) \cdot 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.noisyObservable` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

McNulty, Eq. (9), p. 3: "A_v^η = η A_v + (tr[A_v]/d)(1−η) 𝟙". The matrix expression retains the trace term. The definition uses TomiyamaDiagonalKPositivity.phi d (1−η) 0 at A v; expanding its scalar coefficients gives this expression.

**Definition 1.3 (effect).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (eta : \mathbb{R}),\\\forall (v : \operatorname{Fin} m),\\\forall (s : \operatorname{Bool}),\\(\operatorname{effect} (m : = m) (d : = d) (A : = A) (eta : = eta) (v : = v) (s : = s) : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) = ((1 / 2 : \mathbb{C}) \cdot (1 + (\operatorname{if} s \operatorname{then} (1 : \mathbb{C}) \operatorname{else} - 1) \cdot \operatorname{noisyObservable} A eta v))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.effect` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

McNulty, Eq. (3), p. 2: "M_v(±) = ½(𝟙 ± A_v)." The noisy binary effect replaces A_v by noisyObservable A η v. Bool true denotes +1 and false denotes −1.

**Definition 1.4 (JM).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (eta : \mathbb{R}),\\\operatorname{JM} (m : = m) (d : = d) (A : = A) (eta : = eta) \iff (\exists (E : (\operatorname{Fin} m \to \operatorname{Bool}) \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) , (\forall (a : \operatorname{Fin} m \to \operatorname{Bool}) , (E a) . \operatorname{PosSemidef}) \land (\sum a : \operatorname{Fin} m \to \operatorname{Bool} , E a = 1) \land (\forall (v : \operatorname{Fin} m) (s : \operatorname{Bool}) , (\sum a \in \operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (\operatorname{fun} (a : \operatorname{Fin} m \to \operatorname{Bool}) \mapsto a v = s) , E a) = \operatorname{effect} A eta v s))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.JM` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

McNulty, Section II.C, p. 3: "A collection of measurements are jointly measurable if there exists a parent POVM such that each measurement can be recovered as one of its marginals, or equivalently, if their statistics can be obtained from the parent after classical post-processing [47, 48]." E is indexed by every Boolean assignment. Each E a is positive semidefinite, the total is the identity, and both sign marginals equal the noisy effects exactly.

**Definition 1.5 (visibility).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\(\operatorname{visibility} (n : = n) : \mathbb{R}) = ((2 / (2 \cdot (n : \mathbb{R}) + 2)) \cdot ((\operatorname{Real} . \operatorname{sin} (\operatorname{Real} . \operatorname{pi} / (2 \cdot (n : \mathbb{R}) + 2))))^{-1})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.visibility` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

The candidate threshold is (2/(2n+2)) csc(π/(2n+2)); every division in this formula is real division. It is shared by the two consecutive path sizes and the next even cycle.

**Lemma 1.6 (signed product).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (a : R),\\\forall (b : R),\\\forall (x : R),\\\forall (s : \mathbb{C}),\\\forall (t : \mathbb{C}),\\(a \cdot x = s \cdot (x \cdot a)) \to\\(b \cdot x = t \cdot (x \cdot b)) \to\\(a \cdot b) \cdot x = (s \cdot t) \cdot (x \cdot (a \cdot b))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.signed_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This signed product identity is used in the CliffordPathRealizations construction.

**Definition 1.7 (generatorSign).**

$$\begin{aligned}\forall (k : \mathbb{N}),\\\forall (j : \mathbb{N}),\\(\operatorname{generatorSign} (k : = k) (j : = j) : \mathbb{C}) = (\operatorname{if} k + 1 = j \lor j + 1 = k \operatorname{then} - 1 \operatorname{else} 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.generatorSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines generatorSign.

**Definition 1.8 (prefixSign).**

$$\begin{aligned}\forall (k : \mathbb{N}),\\\forall (j : \mathbb{N}),\\(\operatorname{prefixSign} (k : = k) (j : = j) : \mathbb{C}) = (\operatorname{if} j + 1 = k \lor j = k \operatorname{then} - 1 \operatorname{else} 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.prefixSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines prefixSign.

**Lemma 1.9 (prefixSign zero).**

$$\begin{aligned}\forall (j : \mathbb{N}),\\\operatorname{prefixSign} 0 j = \operatorname{if} j = 0 \operatorname{then} - 1 \operatorname{else} 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.prefixSign_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This prefixSign zero identity is used in the CliffordPathRealizations construction.

**Definition 1.10 (pathMajorana).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (A : \mathbb{N} \to R),\\\forall (q : R),\\\forall (k : \mathbb{N}) , (\operatorname{pathMajorana} A q 0 = q) \land (\operatorname{pathMajorana} A q (k + 1) = - \operatorname{Complex} . I \cdot (\operatorname{pathMajorana} A q k \cdot A k))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.pathMajorana` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pathMajorana.

**Lemma 1.11 (anticommuting trace zero).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (A : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (B : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(B \cdot B = 1) \to\\(A \cdot B = - (B \cdot A)) \to\\A . \operatorname{trace} = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.anticommuting_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This anticommuting trace zero identity is used in the CliffordPathRealizations construction.

**Lemma 1.12 (noisy eq of trace zero).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\forall v , (A v) . \operatorname{trace} = 0) \to\\\forall (t : \mathbb{R}),\\\forall (v : \operatorname{Fin} m),\\\operatorname{noisyObservable} A t v = (t : \mathbb{C}) \cdot A v\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.noisy_eq_of_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This noisy eq of trace zero identity is used in the CliffordPathRealizations construction.

**Definition 1.13 (outcomeSign).**

$$\begin{aligned}\forall (b : \operatorname{Bool}),\\(\operatorname{outcomeSign} (b : = b) : \mathbb{C}) = (\operatorname{if} b \operatorname{then} 1 \operatorname{else} - 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.outcomeSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines outcomeSign.

**Lemma 1.14 (parent signed marginal).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (t : \mathbb{R}),\\(\forall v , (A v) . \operatorname{trace} = 0) \to\\\forall (E : (\operatorname{Fin} m \to \operatorname{Bool}) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\forall v s , (\sum a \in \operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (\operatorname{fun} a \mapsto a v = s) , E a) = \operatorname{effect} A t v s) \to\\\forall (v : \operatorname{Fin} m),\\(\sum a , \operatorname{outcomeSign} (a v) \cdot E a) = (t : \mathbb{C}) \cdot A v\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.parent_signed_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This parent signed marginal identity is used in the CliffordPathRealizations construction.

**Definition 1.15 (weightedHamiltonian).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (w : \operatorname{Fin} m \to \mathbb{R}),\\\forall (a : \operatorname{Fin} m \to \operatorname{Bool}),\\(\operatorname{weightedHamiltonian} (m : = m) (d : = d) (A : = A) (w : = w) (a : = a) : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) = (\sum v , (\operatorname{outcomeSign} (a v) \cdot (w v : \mathbb{C})) \cdot A v)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines weightedHamiltonian.

**Lemma 1.16 (weighted trace bound).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(0 < d) \to\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (w : \operatorname{Fin} m \to \mathbb{R}),\\\forall (t : \mathbb{R}),\\\forall (c : \mathbb{R}),\\(\forall v , (A v) . \operatorname{trace} = 0) \to\\(\forall v , A v \cdot A v = 1) \to\\(\operatorname{JM} A t) \to\\(\forall a , ((c : \mathbb{C}) \cdot (1 : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})) - \operatorname{weightedHamiltonian} A w a) . \operatorname{PosSemidef}) \to\\t \cdot (\sum v , w v) \leq c\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weighted_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This weighted trace bound identity is used in the CliffordPathRealizations construction.

**Lemma 1.17 (path realization trace zero).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(2 \leq m) \to\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{pathGraph} m) A) \to\\\forall (v : \operatorname{Fin} m),\\(A v) . \operatorname{trace} = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.path_realization_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This path realization trace zero identity is used in the CliffordPathRealizations construction.

**Lemma 1.18 (cycle realization trace zero).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(2 \leq m) \to\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{cycleGraph} m) A) \to\\\forall (v : \operatorname{Fin} m),\\(A v) . \operatorname{trace} = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.cycle_realization_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This cycle realization trace zero identity is used in the CliffordPathRealizations construction.

**Definition 1.19 (liftPath).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (A : \mathbb{N} \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (k : \mathbb{N}),\\(\operatorname{liftPath} (d : = d) (A : = A) (k : = k) : \operatorname{Matrix} (\operatorname{Fin} d \times \operatorname{Fin} 2) (\operatorname{Fin} d \times \operatorname{Fin} 2) \mathbb{C}) = (A k (\operatorname{Matrix}.\operatorname{kronecker}) (\operatorname{if} k = 0 \operatorname{then} \operatorname{qubitZ} \operatorname{else} 1))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines liftPath.

**Definition 1.20 (liftSeed).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\(\operatorname{liftSeed} (d : = d) : \operatorname{Matrix} (\operatorname{Fin} d \times \operatorname{Fin} 2) (\operatorname{Fin} d \times \operatorname{Fin} 2) \mathbb{C}) = ((1 : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})) (\operatorname{Matrix}.\operatorname{kronecker}) \operatorname{qubitX})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines liftSeed.

**Lemma 1.21 (liftSeed square).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\operatorname{liftSeed} d \cdot \operatorname{liftSeed} d = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This liftSeed square identity is used in the CliffordPathRealizations construction.

**Lemma 1.22 (liftSeed relation).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (A : \mathbb{N} \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (j : \mathbb{N}),\\\operatorname{liftSeed} d \cdot \operatorname{liftPath} A j = \operatorname{prefixSign} 0 j \cdot (\operatorname{liftPath} A j \cdot \operatorname{liftSeed} d)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This liftSeed relation identity is used in the CliffordPathRealizations construction.

**Lemma 1.23 (arbitrary path majorana extension).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (m : \mathbb{N}),\\\forall (A : \mathbb{N} \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\forall k , k < m \to A k \cdot A k = 1) \to\\(\forall k , k < m \to (A k) . \operatorname{IsHermitian}) \to\\(\forall k j , k < m \to j < m \to A k \cdot A j = \operatorname{generatorSign} k j \cdot (A j \cdot A k)) \to\\\operatorname{let} g : = \operatorname{pathMajorana} (\operatorname{liftPath} A) (\operatorname{liftSeed} d) ; (\forall k , k \leq m \to g k \cdot g k = 1) \land (\forall k , k \leq m \to \operatorname{star} (g k) = g k) \land (\forall j , j \leq m \to \forall i , i < j \to g i \cdot g j = - (g j \cdot g i)) \land (\forall k , k < m \to \operatorname{Complex} . I \cdot (g k \cdot g (k + 1)) = \operatorname{liftPath} A k)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.arbitrary_path_majorana_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One qubit ancilla gives a seed that anticommutes with the first path generator and commutes with all subsequent generators. The recursive Majorana family is Hermitian, squares to the identity, anticommutes pairwise, and has the exact consecutive bonds shown.

**Definition 1.24 (totalPath).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (m : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (k : \mathbb{N}),\\(\operatorname{totalPath} (d : = d) (m : = m) (A : = A) (k : = k) : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) = (\operatorname{if} \operatorname{hk} : k < m \operatorname{then} A \langle k , \operatorname{hk} \rangle \operatorname{else} 1)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.totalPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines totalPath.

**Lemma 1.25 (realization majoranas).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (m : \mathbb{N}),\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{pathGraph} m) A) \to\\\operatorname{let} g : = \operatorname{pathMajorana} (\operatorname{liftPath} (\operatorname{totalPath} A)) (\operatorname{liftSeed} d) ; (\forall k , k \leq m \to g k \cdot g k = 1) \land (\forall k , k \leq m \to \operatorname{star} (g k) = g k) \land (\forall j , j \leq m \to \forall i , i < j \to g i \cdot g j = - (g j \cdot g i)) \land (\forall k , k < m \to \operatorname{Complex} . I \cdot (g k \cdot g (k + 1)) = \operatorname{liftPath} (\operatorname{totalPath} A) k)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.realization_majoranas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This realization majoranas identity is used in the CliffordPathRealizations construction.

**Lemma 1.26 (labeled parent suffices).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (Omega : \operatorname{Type}),\\{}[\operatorname{Fintype} Omega] ,\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (t : \mathbb{R}),\\\forall (\operatorname{label} : Omega \to \operatorname{Fin} m \to \operatorname{Bool}),\\\forall (P : Omega \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\forall \omega , (P \omega) . \operatorname{PosSemidef}) \to\\(\sum \omega , P \omega = 1) \to\\(\forall v , \sum \omega , \operatorname{outcomeSign} (\operatorname{label} \omega v) \cdot P \omega = \operatorname{noisyObservable} A t v) \to\\\operatorname{JM} A t\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.labeled_parent_suffices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This labeled parent suffices identity is used in the CliffordPathRealizations construction.

**Definition 1.27 (qubitV).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{DecidableEq} \iota] ,\\(\operatorname{qubitV} (\iota : = \iota) : \operatorname{Matrix} (\iota \times \operatorname{Fin} 2) \iota \mathbb{C}) = ((1 : \operatorname{Matrix} (\iota \times \operatorname{Fin} 2) (\iota \times \operatorname{Fin} 2) \mathbb{C}) . \operatorname{submatrix} \operatorname{id} (\operatorname{fun} v \mapsto (v , 0)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines qubitV.

**Lemma 1.28 (qubitV isometry).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\(\operatorname{qubitV} (\iota : = \iota)) . \operatorname{conjTranspose} \cdot (\operatorname{qubitV} (\iota : = \iota)) = (1 : \operatorname{Matrix} \iota \iota \mathbb{C})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This qubitV isometry identity is used in the CliffordPathRealizations construction.

**Lemma 1.29 (qubitV compress).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (A : \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (D : \operatorname{Matrix} (\operatorname{Fin} 2) (\operatorname{Fin} 2) \mathbb{C}),\\(\operatorname{qubitV} (\iota : = \iota)) . \operatorname{conjTranspose} \cdot (A (\operatorname{Matrix}.\operatorname{kronecker}) D) \cdot (\operatorname{qubitV} (\iota : = \iota)) = D 0 0 \cdot A\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV_compress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This qubitV compress identity is used in the CliffordPathRealizations construction.

**Lemma 1.30 (compressed parent).**

$$\begin{aligned}\forall (m : \mathbb{N}),\\\forall (d : \mathbb{N}),\\\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (A : \operatorname{Fin} m \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\\forall (B : \operatorname{Fin} m \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (t : \mathbb{R}),\\\forall (V : \operatorname{Matrix} \iota (\operatorname{Fin} d) \mathbb{C}),\\(V . \operatorname{conjTranspose} \cdot V = 1) \to\\(\forall v , (A v) . \operatorname{trace} = 0) \to\\(\forall v , V . \operatorname{conjTranspose} \cdot B v \cdot V = A v) \to\\\forall (E : (\operatorname{Fin} m \to \operatorname{Bool}) \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall a , (E a) . \operatorname{PosSemidef}) \to\\(\sum a , E a = 1) \to\\(\forall v , \sum a , \operatorname{outcomeSign} (a v) \cdot E a = (t : \mathbb{C}) \cdot B v) \to\\\operatorname{JM} A t\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.compressed_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This compressed parent identity is used in the CliffordPathRealizations construction.

**Definition 1.31 (paddedMajoranas).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (m : \mathbb{N}),\\\forall (g : \mathbb{N} \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (j : \operatorname{Fin} (m + 2)),\\(\operatorname{paddedMajoranas} (\iota : = \iota) (m : = m) (g : = g) (j : = j) : \operatorname{Matrix} (\iota \times \operatorname{Fin} 2) (\iota \times \operatorname{Fin} 2) \mathbb{C}) = (\operatorname{if} j . \operatorname{val} = 0 \operatorname{then} (1 : \operatorname{Matrix} \iota \iota \mathbb{C}) (\operatorname{Matrix}.\operatorname{kronecker}) \operatorname{qubitX} \operatorname{else} g (j . \operatorname{val} - 1) (\operatorname{Matrix}.\operatorname{kronecker}) \operatorname{qubitZ})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines paddedMajoranas.

**Lemma 1.32 (paddedMajoranas relations).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (m : \mathbb{N}),\\\forall (g : \mathbb{N} \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall k , k \leq m \to g k \cdot g k = 1) \to\\(\forall k , k \leq m \to \operatorname{star} (g k) = g k) \to\\(\forall k l , k \leq m \to l \leq m \to k \neq l \to g k \cdot g l = - (g l \cdot g k)) \to\\(\forall j , \operatorname{paddedMajoranas} (m : = m) g j \cdot \operatorname{paddedMajoranas} g j = 1) \land (\forall j , \operatorname{star} (\operatorname{paddedMajoranas} (m : = m) g j) = \operatorname{paddedMajoranas} g j) \land (\forall j k , j \neq k \to \operatorname{paddedMajoranas} (m : = m) g j \cdot \operatorname{paddedMajoranas} g k = - (\operatorname{paddedMajoranas} g k \cdot \operatorname{paddedMajoranas} g j))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This paddedMajoranas relations identity is used in the CliffordPathRealizations construction.

**Lemma 1.33 (paddedMajoranas bond).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (m : \mathbb{N}),\\\forall (g : \mathbb{N} \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (j : \operatorname{Fin} (m + 2)),\\(0 < j . \operatorname{val}) \to\\\forall (\operatorname{hnext} : j . \operatorname{val} + 1 < m + 2),\\\operatorname{Complex} . I \cdot (\operatorname{paddedMajoranas} g j \cdot \operatorname{paddedMajoranas} g \langle j . \operatorname{val} + 1 , \operatorname{hnext} \rangle) = (\operatorname{Complex} . I \cdot (g (j . \operatorname{val} - 1) \cdot g j . \operatorname{val})) (\operatorname{Matrix}.\operatorname{kronecker}) (1 : \operatorname{Matrix} (\operatorname{Fin} 2) (\operatorname{Fin} 2) \mathbb{C})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas_bond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This paddedMajoranas bond identity is used in the CliffordPathRealizations construction.

**Definition 1.34 (Quadratic).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\\forall (g : \operatorname{Fin} M \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (C : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}),\\(\operatorname{Quadratic} (M : = M) (\iota : = \iota) (g : = g) (C : = C) : \operatorname{Matrix} \iota \iota \mathbb{C}) = (\sum j , \sum k , C j k \cdot (g j \cdot g k))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.Quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines Quadratic.

**Lemma 1.35 (quadratic bound of positive split).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (g : \operatorname{Fin} M \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\\forall (P : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}),\\\forall (Q : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}),\\\forall (K : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}),\\(P . \operatorname{PosSemidef}) \to\\(Q . \operatorname{PosSemidef}) \to\\(K = P - Q) \to\\(P . \operatorname{trace} \cdot (1 : \operatorname{Matrix} \iota \iota \mathbb{C}) - (1 / 2 : \mathbb{C}) \cdot \operatorname{Quadratic} g K) . \operatorname{PosSemidef}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.quadratic_bound_of_positive_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This quadratic bound of positive split identity is used in the CliffordPathRealizations construction.

**Lemma 1.36 (sum fin next).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (S : \operatorname{Type}),\\{}[\operatorname{AddCommMonoid} S] ,\\\forall (j : \operatorname{Fin} M),\\\forall (f : \operatorname{Fin} M \to S),\\(\sum k , \operatorname{if} j . \operatorname{val} + 1 = k . \operatorname{val} \operatorname{then} f k \operatorname{else} 0) = \operatorname{if} h : j . \operatorname{val} + 1 < M \operatorname{then} f \langle j . \operatorname{val} + 1 , h \rangle \operatorname{else} 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.sum_fin_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This sum fin next identity is used in the CliffordPathRealizations construction.

**Lemma 1.37 (sum fin prev).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (S : \operatorname{Type}),\\{}[\operatorname{AddCommMonoid} S] ,\\\forall (j : \operatorname{Fin} M),\\\forall (f : \operatorname{Fin} M \to S),\\(\sum k , \operatorname{if} k . \operatorname{val} + 1 = j . \operatorname{val} \operatorname{then} f k \operatorname{else} 0) = \operatorname{if} h : 0 < j . \operatorname{val} \operatorname{then} f \langle j . \operatorname{val} - 1 , \operatorname{by} \operatorname{omega} \rangle \operatorname{else} 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.sum_fin_prev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The previous-index sum selects the preceding coordinate when it exists, and is zero at the left endpoint.

**Definition 1.38 (tridiagonal).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (d : \operatorname{Fin} M \to \mathbb{C}),\\\forall (w : \operatorname{Fin} M \to \mathbb{C}),\\(\operatorname{tridiagonal} (M : = M) (d : = d) (w : = w) : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}) = (\operatorname{Matrix} . \operatorname{diagonal} d + \operatorname{Matrix} . \operatorname{of} (\operatorname{fun} j k : \operatorname{Fin} M \mapsto \operatorname{if} j . \operatorname{val} + 1 = k . \operatorname{val} \operatorname{then} w j \operatorname{else} 0) + \operatorname{Matrix} . \operatorname{transpose} (\operatorname{Matrix} . \operatorname{of} (\operatorname{fun} j k : \operatorname{Fin} M \mapsto \operatorname{if} j . \operatorname{val} + 1 = k . \operatorname{val} \operatorname{then} w j \operatorname{else} 0)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.tridiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines tridiagonal.

**Lemma 1.39 (tridiagonal mul apply).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (N : \mathbb{N}),\\\forall (d : \operatorname{Fin} M \to \mathbb{C}),\\\forall (w : \operatorname{Fin} M \to \mathbb{C}),\\\forall (F : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} N) \mathbb{C}),\\\forall (j : \operatorname{Fin} M),\\\forall (r : \operatorname{Fin} N),\\(\operatorname{tridiagonal} M d w \cdot F) j r = d j \cdot F j r + (\operatorname{if} h : j . \operatorname{val} + 1 < M \operatorname{then} w j \cdot F \langle j . \operatorname{val} + 1 , h \rangle r \operatorname{else} 0) + (\operatorname{if} 0 < j . \operatorname{val} \operatorname{then} w \langle j . \operatorname{val} - 1 , \cdot \rangle \cdot F \langle j . \operatorname{val} - 1 , \cdot \rangle r \operatorname{else} 0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.tridiagonal_mul_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This tridiagonal mul apply identity is used in the CliffordPathRealizations construction.

**Lemma 1.40 (mul tridiagonal apply).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (N : \mathbb{N}),\\\forall (d : \operatorname{Fin} M \to \mathbb{C}),\\\forall (w : \operatorname{Fin} M \to \mathbb{C}),\\\forall (F : \operatorname{Matrix} (\operatorname{Fin} N) (\operatorname{Fin} M) \mathbb{C}),\\\forall (j : \operatorname{Fin} N),\\\forall (r : \operatorname{Fin} M),\\(F \cdot \operatorname{tridiagonal} M d w) j r = F j r \cdot d r + (\operatorname{if} h : r . \operatorname{val} + 1 < M \operatorname{then} F j \langle r . \operatorname{val} + 1 , h \rangle \cdot w r \operatorname{else} 0) + (\operatorname{if} 0 < r . \operatorname{val} \operatorname{then} F j \langle r . \operatorname{val} - 1 , \cdot \rangle \cdot w \langle r . \operatorname{val} - 1 , \cdot \rangle \operatorname{else} 0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.mul_tridiagonal_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This mul tridiagonal apply identity is used in the CliffordPathRealizations construction.

**Definition 1.41 (edgeVector).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (r : \operatorname{Fin} M),\\\forall (j : \operatorname{Fin} M),\\(\operatorname{edgeVector} (M : = M) (r : = r) (j : = j) : \mathbb{C}) = ((\operatorname{Pi} . \operatorname{single} r (1 : \mathbb{C}) : \operatorname{Fin} M \to \mathbb{C}) j - (\operatorname{if} r . \operatorname{val} + 1 = j . \operatorname{val} \operatorname{then} 1 \operatorname{else} 0))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.edgeVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines edgeVector.

**Definition 1.42 (weightedLap).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (b : \operatorname{Fin} M \to \mathbb{R}),\\(\operatorname{weightedLap} (M : = M) (b : = b) : \operatorname{Matrix} (\operatorname{Fin} M) (\operatorname{Fin} M) \mathbb{C}) = (\sum r , (b r : \mathbb{C}) \cdot \operatorname{Matrix} . \operatorname{vecMulVec} (\operatorname{edgeVector} M r) (\operatorname{star} (\operatorname{edgeVector} M r)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines weightedLap.

**Lemma 1.43 (weightedLap psd).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (b : \operatorname{Fin} M \to \mathbb{R}),\\(\forall r , 0 \leq b r) \to\\(\operatorname{weightedLap} M b) . \operatorname{PosSemidef}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This weightedLap psd identity is used in the CliffordPathRealizations construction.

**Lemma 1.44 (weightedLap apply).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\\forall (b : \operatorname{Fin} M \to \mathbb{R}),\\\forall (j : \operatorname{Fin} M),\\\forall (k : \operatorname{Fin} M),\\\operatorname{weightedLap} M b j k = (\operatorname{if} j = k \operatorname{then} ((b j : \mathbb{C}) + (\operatorname{if} 0 < j . \operatorname{val} \operatorname{then} (b \langle j . \operatorname{val} - 1 , \cdot \rangle : \mathbb{C}) \operatorname{else} 0)) \operatorname{else} 0) - (\operatorname{if} j . \operatorname{val} + 1 = k . \operatorname{val} \operatorname{then} (b j : \mathbb{C}) \operatorname{else} 0) - (\operatorname{if} k . \operatorname{val} + 1 = j . \operatorname{val} \operatorname{then} (b k : \mathbb{C}) \operatorname{else} 0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This weightedLap apply identity is used in the CliffordPathRealizations construction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.JM`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.Quadratic`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.Realization`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.anticommuting_trace_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.arbitrary_path_majorana_extension`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.compressed_parent`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.cycle_realization_trace_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.edgeVector`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.effect`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.generatorSign`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.labeled_parent_suffices`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftPath`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed_relation`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.liftSeed_square`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.mul_tridiagonal_apply`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.noisyObservable`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.noisy_eq_of_trace_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.outcomeSign`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas_bond`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.paddedMajoranas_relations`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.parent_signed_marginal`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.pathMajorana`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.path_realization_trace_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.prefixSign`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.prefixSign_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.quadratic_bound_of_positive_split`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV_compress`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.qubitV_isometry`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.realization_majoranas`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.signed_product`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.sum_fin_next`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.sum_fin_prev`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.totalPath`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.tridiagonal`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.tridiagonal_mul_apply`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.visibility`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedHamiltonian`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap_apply`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weightedLap_psd`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations.weighted_trace_bound`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../QuantumChannels/TomiyamaDiagonalKPositivity.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](../../../QuantumBounds/MerminMeasurementDependence/Model.md)
