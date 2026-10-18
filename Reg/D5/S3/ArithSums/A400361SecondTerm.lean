import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.A400361SecondTerm
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.A400361SecondTerm
open LeanInformationAudit Filter Topology
open scoped Asymptotics

noncomputable section
namespace Reg.D5.S3.ArithSums.A400361SecondTerm

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ d => coefficientTerm d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Both original conjuncts remain, with the selected positive-series observation varied. -/
def arena : Arena where
  signature := signature
  Law R := Summable (fun j : ℕ => R.readout () () (j + 1)) ∧
    (fun N : ℕ => residual N) =o[atTop] (fun N : ℕ => (N : ℝ)^2)

private theorem coefficient_one : coefficientTerm 1 = 1 := by
  have hm := (hasDerivAt_id (1 : ℝ)).mul Real.hasDerivAt_Gamma_one
  have he : (fun s : ℝ => Real.Gamma (s + 1)) =ᶠ[𝓝 (1 : ℝ)]
      (fun s => s * Real.Gamma s) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with s hs
    exact Real.Gamma_add_one hs
  have hd0 : HasDerivAt Real.Gamma (deriv Real.Gamma 2) ((1 : ℝ) + 1) := by
    convert (Real.hasDerivAt_Gamma_of_pos (by norm_num : (0 : ℝ) < 2)).differentiableAt.hasDerivAt using 1 <;> norm_num
  have hg : HasDerivAt (fun s : ℝ => s + 1) 1 1 := (hasDerivAt_id 1).add_const 1
  have hd := hd0.comp (h := fun s : ℝ => s + 1) 1 hg
  have hu := hd.unique (hm.congr_of_eventuallyEq he)
  have hv : deriv Real.Gamma 2 = 1 - Real.eulerMascheroniConstant := by
    simpa only [Real.Gamma_one, one_mul, mul_one, id_eq, ← sub_eq_add_neg] using hu
  norm_num [coefficientTerm, realDigamma, hv, Real.Gamma_nat_eq_factorial]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := h.1
  have hz : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  norm_num at hz

def registration : Registration arena originalClaim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    have hex : ∃ j : ℕ, coefficientTerm (j + 1) ≠ coefficientTerm 1 := by
      by_contra h
      have hf : (fun j : ℕ => coefficientTerm (j + 1)) = (fun _ => (1 : ℝ)) := by
        funext j
        have he : coefficientTerm (j + 1) = coefficientTerm 1 := by
          by_contra hn
          exact h ⟨j, hn⟩
        rw [he, coefficient_one]
      have ht := result.1.tendsto_atTop_zero
      rw [hf] at ht
      have hz : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
      norm_num at hz
    obtain ⟨j, hj⟩ := hex
    exact ⟨(), j + 1, 1, hj⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400361SecondTerm.result)
    (type_of% (realize signature (fun _ _ d => coefficientTerm d) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400361SecondTerm.coefficient_information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400361SecondTerm.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => coefficientTerm d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400361SecondTerm
    definition := some {
      owner := `D5.S3.ArithSums.A400361SecondTerm
      name := `D5.S3.ArithSums.A400361SecondTerm.originalClaim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ArithSums.A400361SecondTerm
