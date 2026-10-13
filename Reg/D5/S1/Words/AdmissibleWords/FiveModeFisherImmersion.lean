/- Vary the actual square-root chart while preserving its geometric premises. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion

open _root_.D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
open _root_.D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ContDiff

/-- Vary the actual square-root chart; keep its affine probability law, domain,
    differential and Fisher pairing fixed. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 4 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 5 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := IsOpen chartDomain ∧
    (∀ q, q ∈ chartDomain ↔ simplexLaw q ∈ openSimplex) ∧
    (∀ p ∈ openSimplex, ∃! q, q ∈ chartDomain ∧ simplexLaw q = p) ∧
    ContDiffOn ℝ ∞ (R.readout () ()) chartDomain ∧
    ∀ q ∈ chartDomain,
      HasFDerivAt (R.readout () ()) (squareRootDerivative q) q ∧
      Function.Injective (squareRootDerivative q) ∧
      ∑ s, R.readout () () q s ^ 2 = 4 ∧
      (∀ u v, ∑ s, squareRootDerivative q u s * squareRootDerivative q v s =
        fisher (simplexLaw q) (tangentLift u) (tangentLift v)) ∧
      ∀ u : Fin 4 → ℝ, u ≠ 0 →
        0 < fisher (simplexLaw q) (tangentLift u) (tangentLift u)

def actual : Realization signature :=
  realize signature (fun _ _ q => squareRootChart q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hq : (fun _ : Fin 4 => (1 / 5 : ℝ)) ∈ chartDomain := by
    intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · norm_num [simplexLaw, tangentLift, Fin.sum_univ_succ]
    · norm_num [simplexLaw, tangentLift]
  have hsphere := (h.2.2.2.2 _ hq).2.2.1
  change (∑ _s : Fin 5, (0 : ℝ) ^ 2) = 4 at hsphere
  norm_num at hsphere

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨(), 0, (fun _ => 1), ?_⟩
  intro heq
  have hs := congrFun heq 0
  change squareRootChart 0 0 = squareRootChart (fun _ => 1) 0 at hs
  have hneg : Real.sqrt (-3 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
  norm_num [squareRootChart, simplexLaw, tangentLift, Fin.sum_univ_succ, hneg] at hs

def family : Registration arena (type_of% five_mode_fisher_chart_immersion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨five_mode_fisher_chart_immersion, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    five_mode_fisher_chart_immersion
    (type_of% (realize signature (fun _ _ q => squareRootChart q) (fun e => nomatch e)))
    Unit Unit where
  unitName :=
    `D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion.five_mode_fisher_chart_immersion.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => squareRootChart q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
