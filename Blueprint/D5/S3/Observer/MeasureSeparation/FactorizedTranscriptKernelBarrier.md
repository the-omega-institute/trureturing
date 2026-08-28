# Factorized Transcript Kernel Barrier

## Abstract

Factorized transcript laws and every finite repetition agree on interface fibers.

**Definition 1.1 (Transcript kernels).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.TranscriptKernel`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.TranscriptKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A transcript kernel is a state-indexed family of probability laws. The state needs no measurable structure because the source imposes none.

**Definition 1.2 (Factorization through an interface).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.KernelFactorsThrough`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.KernelFactorsThrough` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law family factors when it is the composite of the interface with a probability-law family on the interface codomain.

**Definition 1.3 (Repeated transcript kernels).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.RepeatedTranscriptKernel`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.RepeatedTranscriptKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A length-n transcript kernel returns a joint probability law on Fin n coordinates, so correlated repetitions are included.

**Definition 1.4 (Independent repetition).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.iidRepetition`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.iidRepetition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical finite product of one state-conditioned law gives every iid sample size, including the empty product.

**Definition 1.5 (Exact law identification).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.IdentifiesTarget`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.IdentifiesTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact law identification requires the target to agree whenever the complete transcript laws agree.

**Theorem 1.6 (Factorized laws agree on interface fibers).**

$$\forall X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), q \in X \to B, K \in X \to \operatorname{ProbabilityMeasure}\left(Y\right), x \in X, y \in X,\; \left(\operatorname{KernelFactorsThrough}\left(q, K\right) \land q\left(x\right) = q\left(y\right)\right) \Rightarrow K\left(x\right) = K\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_transcript_kernel_eq_on_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the named factorization turns equal interface values into equal arguments of the reduced law family.

**Theorem 1.7 (Independent repetition preserves factorization).**

$$\forall X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), q \in X \to B, K \in X \to \operatorname{ProbabilityMeasure}\left(Y\right), n \in \operatorname{Nat}\left(\right),\; \operatorname{KernelFactorsThrough}\left(q, K\right) \Rightarrow \operatorname{KernelFactorsThrough}\left(q, \operatorname{iidRepetition}\left(n, K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.iid_repetition_preserves_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the finite probability-product constructor to the reduced law family. The construction works uniformly at every natural sample count.

**Theorem 1.8 (Correlated repeated laws agree on fibers).**

$$\forall X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), n \in \operatorname{Nat}\left(\right), q \in X \to B, Kn \in X \to \operatorname{ProbabilityMeasure}\left(\operatorname{Fin}\left(n\right) \to Y\right), x \in X, y \in X,\; \left(\operatorname{KernelFactorsThrough}\left(q, Kn\right) \land q\left(x\right) = q\left(y\right)\right) \Rightarrow Kn\left(x\right) = Kn\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_repeated_kernel_eq_on_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No coordinate independence is used: equality follows from factorization of the whole joint transcript law.

**Theorem 1.9 (Repeated laws cannot identify a fiber-varying target).**

$$\forall X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), A \in \operatorname{Type}\left(\right), n \in \operatorname{Nat}\left(\right), q \in X \to B, Kn \in X \to \operatorname{ProbabilityMeasure}\left(\operatorname{Fin}\left(n\right) \to Y\right), T \in X \to A, x \in X, y \in X,\; \left(\operatorname{KernelFactorsThrough}\left(q, Kn\right) \land \left(q\left(x\right) = q\left(y\right) \land T\left(x\right) \ne T\left(y\right)\right)\right) \Rightarrow \left(\neg \operatorname{IdentifiesTarget}\left(Kn, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_repeated_kernel_cannot_identify_fiber_varying_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two same-fiber states have the same joint transcript law. If their target values differ, exact identification contradicts that equality.

**Definition 1.10 (The constant Boolean interface).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanInterface`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanInterface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The concrete interface sends both Boolean states to the sole Unit value.

**Definition 1.11 (The varying Boolean target).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanTarget`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The concrete target is the Boolean identity and therefore varies in the one interface fiber.

**Definition 1.12 (The constant point-mass transcript law).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.constantBooleanTranscriptKernel`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.constantBooleanTranscriptKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At either Boolean state, the observation law is the point mass on Unit.

**Definition 1.13 (The state-recording point-mass law).**

Lean statement: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.distinguishingBooleanTranscriptKernel`

*Formalization.* `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.distinguishingBooleanTranscriptKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This audit kernel assigns each Boolean state its own Dirac probability law.

**Theorem 1.14 (No finite repetition identifies the Boolean target).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \neg \operatorname{IdentifiesTarget}\left(\operatorname{iidRepetition}\left(n, constantBooleanTranscriptKernel\right), booleanTarget\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.boolean_target_not_identified_by_any_iid_repetition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, the iid product remains constant on the two Boolean states while the identity target separates them. This explicitly includes n equal to zero.

**Theorem 1.15 (Factorization cannot be deleted).**

$$\exists q \in Bool \to Unit, K \in Bool \to \operatorname{ProbabilityMeasure}\left(Bool\right), x \in Bool, y \in Bool,\; q\left(x\right) = q\left(y\right) \land \left(K\left(x\right) \ne K\left(y\right) \land \left(\neg \operatorname{KernelFactorsThrough}\left(q, K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.transcript_factorization_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the constant interface, distinct Boolean Dirac laws violate the fiber conclusion and cannot factor through that interface.

**Theorem 1.16 (The same-fiber premise cannot be deleted).**

$$\exists q \in Bool \to Bool, K \in Bool \to \operatorname{ProbabilityMeasure}\left(Bool\right), x \in Bool, y \in Bool,\; \operatorname{KernelFactorsThrough}\left(q, K\right) \land \left(q\left(x\right) \ne q\left(y\right) \land K\left(x\right) \ne K\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.same_fiber_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity interface admits the state-recording Dirac law as a factorized kernel, but its two different fibers have unequal laws.

**Theorem 1.17 (Target variation is required for nonidentification).**

$$\exists q \in Bool \to Unit, K \in Bool \to \operatorname{ProbabilityMeasure}\left(Unit\right), T \in Bool \to Unit,\; \operatorname{KernelFactorsThrough}\left(q, K\right) \land \left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{IdentifiesTarget}\left(\operatorname{iidRepetition}\left(n, K\right), T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.fiber_variation_is_necessary_for_nonidentification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant Unit-valued target is identified under every iid repetition of the constant factorized kernel.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.IdentifiesTarget`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.KernelFactorsThrough`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.RepeatedTranscriptKernel`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.TranscriptKernel`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanInterface`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.booleanTarget`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.boolean_target_not_identified_by_any_iid_repetition`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.constantBooleanTranscriptKernel`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.distinguishingBooleanTranscriptKernel`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_repeated_kernel_cannot_identify_fiber_varying_target`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_repeated_kernel_eq_on_fiber`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.factorized_transcript_kernel_eq_on_fiber`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.fiber_variation_is_necessary_for_nonidentification`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.iidRepetition`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.iid_repetition_preserves_factorization`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.same_fiber_is_necessary`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.transcript_factorization_is_necessary`
