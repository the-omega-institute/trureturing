import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.OddSquareGreenMass
import Reg.Support.DependentFamily

/-! Full-family audit of the odd-square inverse-mass estimate. -/

namespace Reg.D5.S3.Quantum.Dynamics.OddSquareGreenMass

open _root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open Lean Elab Command

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def mass (t : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ l : Fin q, ∑ d : Fin (q - l.val),
    ((lowerBlock t (2 * q + 1))⁻¹
      ⟨l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
      ⟨l.val, by have := l.isLt; omega⟩ +
    (lowerBlock t (2 * q + 1))⁻¹
      ⟨q + l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
      ⟨q + l.val + 1, by have := l.isLt; omega⟩)

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q t => mass t q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ → ℝ) (q : ℕ),
    (∀ i, 0 < t i) → (∀ i, t i ≤ 1) →
    (∀ i < 2 * q, t (i + (2 * q + 1)) = t i) →
      (q : ℝ) * (q + 1) ≤ R.readout () q t

private theorem actual_law : arena.Law actual := by
  intro t q ht hu hp
  exact odd_square_inverse_paired_mass t q ht hu hp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) 1 (by intro i; norm_num)
    (by intro i; norm_num) (by intro i hi; rfl)
  norm_num [rejected, realize] at hh

private theorem mass_const (c : ℝ) (hc : c ≠ 0) : mass (fun _ => c) 1 = 2 / c := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if j.val ≤ i.val then 1 / c else 0
  have he : (lowerBlock (fun _ => c) 3)⁻¹ = A := by
    apply Matrix.inv_eq_right_inv
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [lowerBlock, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.of_apply, A, hc]
  norm_num [mass, he, Fin.sum_univ_succ, A]
  ring

private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i

private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, (fun _ => 1), (fun _ => (1 / 2 : ℝ)), ?_⟩
  change mass (fun _ => 1) 1 ≠ mass (fun _ => (1 / 2 : ℝ)) 1
  rw [mass_const 1 (by norm_num), mass_const (1 / 2) (by norm_num)]
  norm_num

def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.odd_square_inverse_paired_mass)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.OddSquareGreenMass.odd_square_inverse_paired_mass.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OddSquareGreenMass.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t => mass t q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.OddSquareGreenMass
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration


namespace PositiveEntry
abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => greenEntry t p.1 p.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ → ℝ), (∀ i, 0 < t i) → ∀ l d : ℕ, 0 < R.readout () (l,d) t
private theorem actual_law : arena.Law actual := by
  exact entry_pos
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) (by intro i; norm_num) 0 0
  norm_num [rejected, realize] at hh
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(0,0), (fun _ => 1), (fun _ => 2), ?_⟩
  norm_num [actual, realize, greenEntry]
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.entry_pos)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.OddSquareGreenMass.entry_pos.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OddSquareGreenMass.PositiveEntry.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => greenEntry t p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.OddSquareGreenMass
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PositiveEntry

namespace BlockInverse
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p) (Fin p) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n t => greenMatrix t n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ → ℝ), (∀ i, 0 < t i) → ∀ n : ℕ, (lowerBlock t n)⁻¹ = R.readout () n t
private theorem actual_law : arena.Law actual := by
  exact block_inverse
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) (by intro i; norm_num) 1
  change (lowerBlock (fun _ => 1) 1)⁻¹ = 0 at hh
  rw [block_inverse _ (by intro i; norm_num)] at hh
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) hh
  norm_num [greenMatrix, greenEntry] at he
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, (fun _ => 1), (fun _ => 2), ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) h
  norm_num [actual, realize, greenMatrix, greenEntry] at he
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.block_inverse)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.OddSquareGreenMass.block_inverse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OddSquareGreenMass.BlockInverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n t => greenMatrix t n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.OddSquareGreenMass
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end BlockInverse

end
end Reg.D5.S3.Quantum.Dynamics.OddSquareGreenMass
