/- GID: D5/S3/QuantumChannels/UnitaryKrausMixingInvariance
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/UnitaryKrausMixingInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A column-orthogonal change of Kraus generators leaves the induced channel invariant. -/

import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT
Repository layer:
* `D5/S3/Quantum/FiniteDimensional.lean` supplies qubit matrix-algebra and Born-weight facts,
  but no change-of-Kraus-family invariance theorem.
* `D5/S3/Quantum/Measurements/FiniteKrausInstrumentBornMarginal.lean` proves the Born marginal
  of one fixed finite Kraus instrument, not invariance under mixing its branch generators.
* Searches for `Kraus`, `unitary mixing`, `observer gauge`, `conjTranspose U * U`, and the
  component orthogonality sum found no repository theorem with the statement below.
Mathlib layer:
* `star_sum` and `star_smul` distribute the adjoint through the finite linear combination.
* `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_comm`, and `Finset.sum_smul` rearrange the
  finite expansion; `smul_mul_assoc` and `smul_mul_smul_comm` collect its scalar coefficients.
Verdict: no exact library theorem was found; prove the finite matrix identity directly.
-/

namespace D5.S3.QuantumChannels.UnitaryKrausMixingInvariance

universe u v w

/-- Mix a finite family of Kraus generators by a complex coefficient matrix. -/
noncomputable def unitaryKrausMixing
    {ι : Type u} {κ : Type v} {n : Type w} [Fintype ι]
    (U : Matrix κ ι ℂ) (S : ι → Matrix n n ℂ) (k : κ) : Matrix n n ℂ :=
  ∑ j, U k j • S j

/-- A column-orthogonal change of finite Kraus generators leaves their sandwich-sum map
unchanged.  The component hypothesis is the exact finite-dimensional content of the observer
change being unitary; rectangular isometries are allowed, so redundant branch labels are covered. -/
theorem unitary_kraus_mixing_invariance
    {ι : Type u} {κ : Type v} {n : Type w} [Fintype ι] [Fintype κ] [Fintype n]
    [DecidableEq ι]
    (U : Matrix κ ι ℂ) (S : ι → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hU : ∀ i j, ∑ k, U k i * star (U k j) = if i = j then 1 else 0) :
    ∑ k, unitaryKrausMixing U S k * X * star (unitaryKrausMixing U S k) =
      ∑ j, S j * X * star (S j) := by
  classical
  unfold unitaryKrausMixing
  calc
    ∑ k, (∑ j, U k j • S j) * X * star (∑ j, U k j • S j) =
        ∑ k, ∑ i, ∑ j,
          (U k i * star (U k j)) • (S i * X * star (S j)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (star (U k j)) (U k i)]
    _ = ∑ i, ∑ j, (∑ k, U k i * star (U k j)) •
        (S i * X * star (S j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_smul]
    _ = ∑ i, ∑ j, (if i = j then (1 : ℂ) else 0) • (S i * X * star (S j)) := by
      simp_rw [hU]
    _ = ∑ j, S j * X * star (S j) := by
      simp

#print axioms unitary_kraus_mixing_invariance

end D5.S3.QuantumChannels.UnitaryKrausMixingInvariance
