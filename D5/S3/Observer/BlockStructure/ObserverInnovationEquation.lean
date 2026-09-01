/- GID: D5/S3/Observer/BlockStructure/ObserverInnovationEquation
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/ObserverInnovationEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strict Gram floor drop identifies the unique innovation zero. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/- Library-search audit trail (2026-08-29):
   * Repository searches for observer innovations, unique Schur roots, Gram spectral floors,
     and the expanded block formula found no exact theorem on the source carrier.
   * `CertifiedStickyMatrix.certified_sticky_matrix` and
     `ExactStickyReduction.exact_sticky_reduction` provide related Schur-energy implications,
     but neither constructs the feature Gram matrices or identifies the unique spectral root.
   * Pinned Mathlib supplies the canonical `Matrix.gram`,
     `Matrix.PosDef.fromBlocks₁₁`, and `Matrix.det_fromBlocks₁₁`; the proof applies these
     directly. No pinned interlacing or packaged innovation-root theorem was found. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace D5.S3.Observer.BlockStructure.ObserverInnovationEquation

open Matrix

/-- If adjoining one feature strictly lowers the spectral floor of its Gram matrix,
the new floor is the unique zero below the old floor of the constructed innovation
Schur complement. The floor hypotheses are the positive-definite and
positive-semidefinite threshold characterizations of the two least eigenvalues. -/
theorem observer_innovation_equation
    {K V ι : Type*}
    [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [Fintype ι] [DecidableEq ι]
    (feature : Sum ι Unit → V)
    (alphaOld alphaNew : ℝ)
    (hOldFloor : ∀ a : ℝ,
      (Matrix.gram K (feature ∘ Sum.inl) -
        (a : K) • (1 : Matrix ι ι K)).PosDef ↔ a < alphaOld)
    (hFullFloorSemi : ∀ a : ℝ,
      (Matrix.gram K feature -
        (a : K) • (1 : Matrix (Sum ι Unit) (Sum ι Unit) K)).PosSemidef ↔
          a ≤ alphaNew)
    (hFullFloorDef : ∀ a : ℝ,
      (Matrix.gram K feature -
        (a : K) • (1 : Matrix (Sum ι Unit) (Sum ι Unit) K)).PosDef ↔
          a < alphaNew)
    (hDrop : alphaNew < alphaOld) :
    let oldGram := Matrix.gram K (feature ∘ Sum.inl)
    let coupling : Matrix ι Unit K := fun i _ =>
      ⟪feature (Sum.inl i), feature (Sum.inr ())⟫_K
    let innovation := fun a : ℝ =>
      ⟪feature (Sum.inr ()), feature (Sum.inr ())⟫_K - (a : K) -
        (couplingᴴ *
          (oldGram - (a : K) • (1 : Matrix ι ι K))⁻¹ * coupling) () ()
    innovation alphaNew = 0 ∧
      ∀ a : ℝ, a < alphaOld → innovation a = 0 → a = alphaNew := by
  dsimp only
  let oldGram := Matrix.gram K (feature ∘ Sum.inl)
  let coupling : Matrix ι Unit K := fun i _ =>
    ⟪feature (Sum.inl i), feature (Sum.inr ())⟫_K
  let diagonal : Matrix Unit Unit K := fun _ _ =>
    ⟪feature (Sum.inr ()), feature (Sum.inr ())⟫_K
  let oldShift := fun a : ℝ =>
    oldGram - (a : K) • (1 : Matrix ι ι K)
  let fullShift := fun a : ℝ =>
    Matrix.gram K feature -
      (a : K) • (1 : Matrix (Sum ι Unit) (Sum ι Unit) K)
  have hBlock (a : ℝ) :
      fullShift a = Matrix.fromBlocks (oldShift a) coupling couplingᴴ
        (diagonal - (a : K) • (1 : Matrix Unit Unit K)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [fullShift, oldShift, oldGram, Matrix.gram_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    · rcases j with ⟨⟩
      rw [Matrix.fromBlocks_apply₁₂]
      simp [fullShift, oldShift, coupling, Matrix.gram_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    · rcases i with ⟨⟩
      rw [Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
      simp [fullShift, oldShift, coupling, Matrix.gram_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, inner_conj_symm]
    · rcases i with ⟨⟩
      rcases j with ⟨⟩
      rw [Matrix.fromBlocks_apply₂₂]
      change
        (Matrix.gram K feature -
          (a : K) • (1 : Matrix (Sum ι Unit) (Sum ι Unit) K))
            (Sum.inr ()) (Sum.inr ()) =
          (diagonal - (a : K) • (1 : Matrix Unit Unit K)) () ()
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, Matrix.one_apply_eq]
      simp [diagonal, Matrix.gram_apply]
  have hOld (a : ℝ) (ha : a < alphaOld) : (oldShift a).PosDef := by
    exact (hOldFloor a).2 ha
  have hDetFactor (a : ℝ) (ha : a < alphaOld) :
      (fullShift a).det = (oldShift a).det *
        (diagonal - (a : K) • (1 : Matrix Unit Unit K) -
          couplingᴴ * (oldShift a)⁻¹ * coupling).det := by
    have hPos := hOld a ha
    letI : Invertible (oldShift a) := hPos.isUnit.invertible
    rw [hBlock a, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hInnovationEq (a : ℝ) :
      (diagonal - (a : K) • (1 : Matrix Unit Unit K) -
        couplingᴴ * (oldShift a)⁻¹ * coupling).det =
      ⟪feature (Sum.inr ()), feature (Sum.inr ())⟫_K - (a : K) -
        (couplingᴴ *
          (oldGram - (a : K) • (1 : Matrix ι ι K))⁻¹ * coupling) () () := by
    rw [Matrix.det_unique, Matrix.sub_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply_eq]
    simp [diagonal, oldShift, oldGram, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  constructor
  · have hOldNew := hOld alphaNew hDrop
    have hFullSemi : (fullShift alphaNew).PosSemidef := by
      exact (hFullFloorSemi alphaNew).2 le_rfl
    have hFullNotDef : ¬(fullShift alphaNew).PosDef := by
      rw [hFullFloorDef alphaNew]
      exact lt_irrefl _
    have hFullDetZero : (fullShift alphaNew).det = 0 := by
      rw [← not_ne_iff]
      intro hne
      exact hFullNotDef (hFullSemi.posDef_iff_det_ne_zero.2 hne)
    have hOldDetNe : (oldShift alphaNew).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 hOldNew.isUnit).ne_zero
    have hFactor := hDetFactor alphaNew hDrop
    rw [hFactor, mul_eq_zero] at hFullDetZero
    exact (hInnovationEq alphaNew).symm.trans
      (hFullDetZero.resolve_left hOldDetNe)
  · intro a ha hInnovation
    have hOldA := hOld a ha
    have hSchurZero :
        diagonal - (a : K) • (1 : Matrix Unit Unit K) -
          couplingᴴ * (oldShift a)⁻¹ * coupling = 0 := by
      have hDetZero :
          (diagonal - (a : K) • (1 : Matrix Unit Unit K) -
            couplingᴴ * (oldShift a)⁻¹ * coupling).det = 0 :=
        (hInnovationEq a).trans hInnovation
      ext i j
      simpa [Matrix.det_unique, Subsingleton.elim i (),
        Subsingleton.elim j ()] using hDetZero
    have hSchurSemi :
        (diagonal - (a : K) • (1 : Matrix Unit Unit K) -
          couplingᴴ * (oldShift a)⁻¹ * coupling).PosSemidef := by
      rw [hSchurZero]
      exact Matrix.PosSemidef.zero
    letI : Invertible (oldShift a) := hOldA.isUnit.invertible
    have hFullSemi : (fullShift a).PosSemidef := by
      rw [hBlock a, Matrix.PosDef.fromBlocks₁₁ coupling
        (diagonal - (a : K) • (1 : Matrix Unit Unit K)) hOldA]
      exact hSchurSemi
    have haLe : a ≤ alphaNew := (hFullFloorSemi a).1 hFullSemi
    have hSchurDetZero :
        (diagonal - (a : K) • (1 : Matrix Unit Unit K) -
          couplingᴴ * (oldShift a)⁻¹ * coupling).det = 0 :=
      (hInnovationEq a).trans hInnovation
    have hFullDetZero : (fullShift a).det = 0 := by
      rw [hDetFactor a ha, hSchurDetZero, mul_zero]
    have hNotLt : ¬a < alphaNew := by
      intro hlt
      have hDef := (hFullFloorDef a).2 hlt
      exact ((Matrix.isUnit_iff_isUnit_det _).1 hDef.isUnit).ne_zero
        hFullDetZero
    exact le_antisymm haLe (le_of_not_gt hNotLt)

#print axioms observer_innovation_equation

end D5.S3.Observer.BlockStructure.ObserverInnovationEquation
