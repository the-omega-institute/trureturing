# A Luders image without ambient Sob sum closure

## Abstract

A two-outcome qubit Luders instrument maps an effect to a sub-observable whose double is still a sub-observable but is outside the image of effects. This proves Gudder's conjecture after Theorem 3.1 and answers the arbitrary Luders question in Example 3 negatively.

**Definition 1.1 (Finite sub-observables).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{IsSubObservable}\left(A\right) \Leftrightarrow ((\forall (x: \operatorname{Fin}\left(n\right)), \operatorname{Matrix}.\operatorname{PosSemidef}\left(A\left(x\right)\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(1 - \sum_{x: \operatorname{Fin}\left(n\right)} A\left(x\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersSubObservableClosure.IsSubObservable` (`✓ std3`).

*Citation.* Stanley Gudder (2023). *Dual Quantum Instruments and Sub-observables*. URL: <https://arxiv.org/abs/2302.12243v1>.

*Commentary.*

Section 2, p. 3: "If Δ ↦ A(Δ) is countably additive but A(Ω_A) need not be I, then A is called a sub-observable." Here H is Fin d → ℂ, the outcomes are Fin n with all events, and A(Δ) is the sum of A x over x in Δ. Each outcome is positive semidefinite and the total is at most the identity.

**Definition 1.2 (Sob effect algebras).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (U: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)), \operatorname{IsSobEffectAlgebra}\left(U\right) \Leftrightarrow ((\forall (A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (A \in U) \Rightarrow (\operatorname{IsSubObservable}\left(A\right))) \land (\exists (Z: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (Z \in U) \land (((\operatorname{IsSubObservable}\left(Z\right)) \land (\sum_{x: \operatorname{Fin}\left(n\right)} Z\left(x\right) = 1)) \land ((\forall (A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (A \in U) \Rightarrow (Z - A \in U)) \land (\forall (A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (A \in U) \Rightarrow (\forall (B: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (B \in U) \Rightarrow ((\operatorname{IsSubObservable}\left(A + B\right)) \Rightarrow (A + B \in U))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersSubObservableClosure.IsSobEffectAlgebra` (`✓ std3`).

*Citation.* Stanley Gudder (2023). *Dual Quantum Instruments and Sub-observables*. URL: <https://arxiv.org/abs/2302.12243v1>.

*Commentary.*

Section 3, p. 11: "Let U ⊆ Sob(H) and assume that all elements of U have the same outcome set (Ω, F). We call U a Sob effect algebra if: (S1) there exists an observable Z ∈ U, (S2) if A ∈ U then A′ = Z − A ∈ U, (S3) if A, B ∈ U and A + B ∈ Sob(H), then A + B ∈ U." The same Z occurs in (S1) and (S2). In the finite representation, an observable is a sub-observable whose total is 1; addition and subtraction are pointwise on outcome values.

**Definition 1.3 (The image of effects under a Luders instrument).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (K: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{ludersImage}\left(K\right) = \{A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \mid \exists (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(a\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(1 - a\right))) \land (A = \operatorname{fun} (x: \operatorname{Fin}\left(n\right)) \mapsto K\left(x\right) \cdot a \cdot K\left(x\right))\}$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersSubObservableClosure.ludersImage` (`✓ std3`).

*Citation.* Stanley Gudder (2023). *Dual Quantum Instruments and Sub-observables*. URL: <https://arxiv.org/abs/2302.12243v1>.

*Commentary.*

Section 2, pp. 4–5: "The dual instrument satisfies L*_x(b) = a_x^(1/2) b a_x^(1/2) for all x ∈ Ω_A, b ∈ E(H)." The matrices K x are the positive square roots of the instrument's effects. The image consists of families A for which one effect a simultaneously gives A x = K x * a * K x at every outcome x.

**Definition 1.4 (Universal closure for Luders images).**

$$claim \Leftrightarrow (\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (K: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (x: \operatorname{Fin}\left(n\right)), \operatorname{Matrix}.\operatorname{PosSemidef}\left(K\left(x\right)\right)) \Rightarrow ((\sum_{x: \operatorname{Fin}\left(n\right)} K\left(x\right) \cdot K\left(x\right) = 1) \Rightarrow (\operatorname{IsSobEffectAlgebra}\left(\operatorname{ludersImage}\left(K\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim` (`✓ std3`).

*Citation.* Stanley Gudder (2023). *Dual Quantum Instruments and Sub-observables*. URL: <https://arxiv.org/abs/2302.12243v1>.

*Commentary.*

After Theorem 3.1, p. 11: "If I ∈ In(H) and U_I = {I*_a : a ∈ E(H)}, then we conjecture that U need not be a Sob effect algebra." Example 3, p. 14: "If L_x(ρ) = a_x ∘ ρ is an arbitrary Lüders instrument, we do not know whether U_L is a Sob effect algebra. However, in the case where a_x are projections (we then call L sharp) we can show that it is." The displayed assertion is universal Sob closure for finite Luders instruments: d is the Hilbert-space dimension, n is the number of outcomes, K x is positive semidefinite, and the sum of K x * K x is 1. Its negation gives a finite counterexample to that closure and therefore proves the existential conjecture.

**Theorem 1.5 (An unsharp qubit image violates (S3)).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LudersSubObservableClosure.result` (`✓ std3`). ∎

*Resolves.* `Problems/gudder-2023-sob-effect-algebra-luders` (proved) by `D5/S3/Quantum/Measurement/LudersSubObservableClosure.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gudder-2023-sob-effect-algebra-luders","declaration_gid":"D5/S3/Quantum/Measurement/LudersSubObservableClosure.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stanley Gudder (2023). *Dual Quantum Instruments and Sub-observables*. URL: <https://arxiv.org/abs/2302.12243v1>.

*Commentary.*

Take K_0 = diag(4/5, 3/5), K_1 = diag(3/5, 4/5), E = (1/400)[[151, 50], [50, 151]] and A x = K x * E * K x. Writing Pplus = Matrix.vecMulVec (1, 1) (star (1, 1)) and Pminus = Matrix.vecMulVec (1, −1) (star (1, −1)), E = (201/800) Pplus + (101/800) Pminus and 1 − E = (199/800) Pplus + (299/800) Pminus show that E is an effect. Each doubled outcome is positive semidefinite; the complement of their total is (1/400) Pplus + (97/400) Pminus. Hence A + A is a sub-observable. If A + A had an effect preimage, its outcome 0 and invertibility of K_0 would force the preimage E + E. The quadratic form of 1 − (E + E) on (1, 1) is −1/100, contradicting positivity. Thus (S3) fails. The summed map contracts off-diagonal entries by 24/25, while the individual invertible outcome fixes the preimage. Example 3's closure for projection effects survives, and no assertion about every unsharp instrument follows.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/LudersSubObservableClosure.IsSobEffectAlgebra`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersSubObservableClosure.IsSubObservable`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersSubObservableClosure.ludersImage`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersSubObservableClosure.result`
- Dependency: [D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity](../../../S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.md)
- Dependency: [D5/S3/Quantum/Bogoliubov/HardyBlockConservation](../Bogoliubov/HardyBlockConservation.md)
