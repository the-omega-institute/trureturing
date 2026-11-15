import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
open _root_.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace GreenCharge
abbrev signature : Signature where
  Params := ℝ × ℕ
  State _ := ℕ → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => _root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.greenEntry (fun i => p.1 ^ (a i)) 0 p.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℝ), rho ≠ 0 → ∀ (a : ℕ → ℤ) (q : ℕ), R.readout () (rho,q) a = rho ^ (-alternatingCharge a (2*q+1))
private theorem actual_law : arena.Law actual := by
  exact green_charge
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num) (fun _ => 0) 0
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
  refine ⟨(2,0), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, _root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.greenEntry]
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.green_charge)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.green_charge.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.GreenCharge.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => _root_.D5.S3.Quantum.Dynamics.OddSquareGreenMass.greenEntry (fun i => p.1 ^ (a i)) 0 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GreenCharge

namespace GapLimit
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ rho => gap rho) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℝ), 0 < rho → rho < 1 → Filter.Tendsto (R.readout () () rho) Filter.atTop (nhds 0)
private theorem actual_law : arena.Law actual := by
  exact gap_tendsto_zero
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1/2) (by norm_num) (by norm_num)
  rw [Metric.tendsto_atTop] at hh
  obtain ⟨J,hJ⟩ := hh (1/2) (by norm_num)
  have hb := hJ J le_rfl
  norm_num [rejected, realize, Real.dist_eq] at hb
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private lemma gap_first (rho : ℝ) : gap rho 1 = rho^2 := by
  have hL : _root_.D5.S1.Words.TribonacciAlignedWindows.L 1 = 2 := by decide
  have hW : _root_.D5.S1.Words.TribonacciAlignedWindows.W 0 = 0 := rfl
  have hH : (openPath (hopping rho) 1).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [openPath, hopping]
  have habs : ∀ i : Fin 2, |hH.eigenvalues i| = rho^2 := by
    intro i
    have hs := hH.eigenvalues_mem_spectrum_real i
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      not_not] at hs
    change (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (hH.eigenvalues i) -
      openPath (hopping rho) 1).det = 0 at hs
    rw [Matrix.det_fin_two] at hs
    simp [Matrix.algebraMap_eq_diagonal, Matrix.sub_apply, openPath, hopping, hW,
      _root_.D5.S1.Words.TribonacciPrefixRefutation.weight] at hs
    have hre : hH.eigenvalues i * hH.eigenvalues i - rho^2 * rho^2 = 0 := by
      exact_mod_cast hs
    have hsq := sq_abs (hH.eigenvalues i)
    nlinarith [abs_nonneg (hH.eigenvalues i), sq_nonneg rho]
  unfold gap
  rw [dite_eq_left (by omega : 1 ≤ 1)]
  apply le_antisymm
  · exact le_trans (Finset.min'_le _ _ (Finset.mem_image.mpr
      ⟨(0 : Fin 2), Finset.mem_univ _, rfl⟩)) (le_of_eq (habs 0))
  · apply Finset.le_min'
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact le_of_eq (habs i).symm
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1/2, 1/3, ?_⟩
  change gap (1/2) ≠ gap (1/3)
  intro h
  have he := congrFun h 1
  rw [gap_first, gap_first] at he
  norm_num at he

def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.gap_tendsto_zero)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.gap_tendsto_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap.GapLimit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => gap rho) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GapLimit

end
end Reg.D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
