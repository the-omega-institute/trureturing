import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Spectral
open _root_.D5.S3.Zeros.CriticalPoints.SchurMomentInequality
open _root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo (B)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n p => (((n : ℝ) + 1) ^ p + n - 1) / n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∀ j, b j ≠ 0) (p : ℝ) (hp : 1 ≤ p),
    let S := ((B b).charpoly.roots.map (fun μ => ‖μ‖ ^ p)).sum
    let M := R.readout () n p * ∑ j, ‖b j‖ ^ p
    S ≤ M ∧ (1 < p → S = M → ∀ i j, b i = b j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (by norm_num : 0 < 1) (fun _ => 1) (by intro j; norm_num)
    1 (by norm_num)).1
  change ((B (fun _ : Fin 1 => (1 : ℂ))).charpoly.roots.map
    (fun μ => ‖μ‖ ^ (1 : ℝ))).sum ≤ (-1 : ℝ) * ∑ _j : Fin 1, ‖(1 : ℂ)‖ ^ (1 : ℝ) at hh
  simp only [Fin.sum_univ_one, norm_one, Real.one_rpow, mul_one] at hh
  have hn : 0 ≤ ((B (fun _ : Fin 1 => (1 : ℂ))).charpoly.roots.map
      (fun μ => ‖μ‖ ^ (1 : ℝ))).sum := Multiset.sum_nonneg (by
    intro x hx
    obtain ⟨μ, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.rpow_nonneg (norm_nonneg _) _)
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [actual, realize, Real.rpow_two]
def source_registration : Registration arena (type_of% @spectral_bound_and_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_bound_and_rigidity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectral_bound_and_rigidity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Spectral.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Spectral.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n p => (((n : ℝ) + 1) ^ p + n - 1) / n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Spectral

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Reciprocal
open _root_.D5.S3.Zeros.CriticalPoints.SchurMomentNormalization
open _root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo (P B J)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ p => p + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) (p : ℝ),
    ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
    ((B (fun j => (z j)⁻¹)).charpoly.roots.map
      (fun μ => ‖μ‖ ^ R.readout () () p)).sum
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ : Fin 1 => (1 : ℂ)) (by intro j; norm_num) 1
  have htrue := reciprocal_moment (fun _ : Fin 1 => (1 : ℂ)) (by intro j; norm_num) 1
  have hB : B (fun _ : Fin 1 => (1 : ℂ)⁻¹) = Matrix.diagonal (fun _ : Fin 1 => (2 : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [B, J, Matrix.mul_apply]
  rw [htrue, hB] at hh
  norm_num [rejected, realize, Matrix.charpoly_diagonal, Fin.prod_univ_one,
    Polynomial.roots_X_sub_C, Real.rpow_two] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def source_registration : Registration arena (type_of% @reciprocal_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reciprocal_moment, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reciprocal_moment) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Reciprocal.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Reciprocal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Reciprocal
