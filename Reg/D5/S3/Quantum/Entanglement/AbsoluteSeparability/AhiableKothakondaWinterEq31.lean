import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31

abbrev signature : Signature where
  Params := Σ m : ℕ, Σ n : ℕ, Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  State p := Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p ρ => p.2.2 * ρ * star p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m n : ℕ, ∀ (_hm : 2 ≤ m) (_hmn : m ≤ n),
    ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      ∀ hρ : ρ.PosSemidef, ρ.trace = 1 →
      (let D := m * n
       let hD : m ≤ D := Nat.le_mul_of_pos_right m (by omega)
       let lamb : Fin D → ℝ := fun i =>
         hρ.isHermitian.eigenvalues₀ (Fin.cast (by simp [D]) i)
       2 * lamb ⟨D - 1, by omega⟩ +
           ∑ k : Fin (m - 1), lamb ⟨D - k.val - 2, by omega⟩ ≥
         ∑ k : Fin (m - 1), lamb ⟨k.val, by omega⟩) →
      ∀ U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        U ∈ Matrix.unitaryGroup (Fin m × Fin n) ℂ →
          separableCone (R.readout () ⟨m, ⟨n, U⟩⟩ ρ)

private abbrev Index := Fin 2 × Fin 2

private def mixed : Matrix Index Index ℂ := (1 / 4 : ℝ) • 1

private theorem mixed_psd : mixed.PosSemidef :=
  PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

private theorem mixed_eigenvalues (h : mixed.IsHermitian) (i : Index) :
    h.eigenvalues i = 1 / 4 := by
  have he := h.eigenvalues_mem_spectrum_real i
  have hm : mixed = algebraMap ℝ (Matrix Index Index ℂ) (1 / 4) := by
    simp [mixed, Algebra.algebraMap_eq_smul_one]
  have hs : spectrum ℝ mixed = {(1 / 4 : ℝ)} := by
    rw [hm, spectrum.scalar_eq]
  rw [hs] at he
  simpa using he

private theorem mixed_eigenvalues₀ (h : mixed.IsHermitian)
    (i : Fin (Fintype.card Index)) : h.eigenvalues₀ i = 1 / 4 := by
  simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
    mixed_eigenvalues h ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : trace mixed = 1 := by
    norm_num [mixed, trace_smul]
  have hs := h 2 2 (by decide) (by decide) mixed mixed_psd ht
    (by dsimp; simp only [mixed_eigenvalues₀]; norm_num)
    1 (one_mem _)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, ⟨1, 1⟩⟩, 0, 1, ?_⟩
    intro h
    change
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) * 0 * star 1 =
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) * 1 * star 1 at h
    simp only [star_one, one_mul, mul_one] at h
    exact zero_ne_one h

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31
    definition := some { owner :=
      `D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31, name :=
      `D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31.claim, path :=
      #[] }
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31
