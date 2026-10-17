import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Hiai.SpectralNonconcavity
import Reg.Support.DependentFamily


open _root_.D5.S3.Quantum.Hiai.SpectralNonconcavity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Reg.D5.S3.Quantum.Hiai.SpectralNonconcavity

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ α ↦ decide (0 < α)) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α p : ℝ), R.readout () () α = true → α < 1 → α ≠ 1 / 2 → 0 < p →
    ∃ τ s ell : ℝ, WitnessGeometry τ s ell ∧
      (α < 1 / 2 → spectralTrace α p (diagonalState τ) (balancedState s) <
        (1 - ell) * spectralTrace α p (diagonalState (s ^ (2 : ℕ))) (balancedState s) +
          ell * spectralTrace α p (diagonalState (1 - s ^ (2 : ℕ))) (balancedState s)) ∧
      (1 / 2 < α → spectralTrace α p (balancedState s) (diagonalState τ) <
        (1 - ell) * spectralTrace α p (balancedState s) (diagonalState (s ^ (2 : ℕ))) +
          ell * spectralTrace α p (balancedState s) (diagonalState (1 - s ^ (2 : ℕ))))

private lemma zero_order (A B : Mat) (hA : Density A) (hB : Density B) :
    spectralTrace 0 1 A B = 1 := by
  have hL : IsStrictlyPositive (nativeMean 1 A B) := by
    exact _root_.D5.S3.Quantum.Hiai.PsiMeanTraceConcavity.mean_strict
      (hB.1.isStrictlyPositive.rpow B 1).posDef
      (hA.1.isStrictlyPositive.rpow A (-1)).posDef (1 / 2)
  unfold spectralTrace
  simp only [CFC.rpow_zero _ hL.nonneg, one_mul, mul_one, one_div_one,
    CFC.rpow_one A hA.1.posSemidef.nonneg, hA.2.1, Complex.one_re]

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨τ, s, ell, hg, hlo, _⟩ := law 0 1 rfl (by norm_num) (by norm_num) (by norm_num)
  rcases hg with ⟨_, _, _, _, _, _, _, hd0, hd1, hdτ, hb, _⟩
  have bad := hlo (by norm_num)
  rw [zero_order _ _ hdτ hb, zero_order _ _ hd0 hb, zero_order _ _ hd1 hb] at bad
  linarith

noncomputable def evidence : Registration arena (type_of% (@off_midpoint_violation)) where
  actual := actual
  bridge := by
    constructor
    · intro source α p hα hα1 hαne hp
      exact source α p (of_decide_eq_true hα) hα1 hαne hp
    · intro law α p hα hα1 hαne hp
      exact law α p (decide_eq_true hα) hα1 hαne hp
  variation := ⟨by
    intro α p hα hα1 hαne hp
    exact off_midpoint_violation α p (of_decide_eq_true hα) hα1 hαne hp,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by
      norm_num [actual, realize]⟩

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.off_midpoint_violation)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.off_midpoint_violation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Quantum.Hiai.SpectralNonconcavity
