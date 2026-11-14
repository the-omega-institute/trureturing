import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
import Reg.Support.DependentFamily

/-! Dependent-family audit of the complete native marked-count comparison. -/

open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => |d|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M q s : ℕ} {r : ℝ},
    1 ≤ q → q < M → 0 < r → r < 1 → compensation M q r < 1 →
    ∀ (S : Support M q) (m : Fin q → Fin M), Function.Injective m →
      (∀ j, m j ∈ S.val) → ∀ E : Set ((Fin q ⊕ Fin q) → ℕ),
      R.readout () ()
        ((∑ o : Obs M s .path, if nativeCounts m o ∈ E then probability r .path S o else 0) -
         (∑ o : Fin s → Option (Fin q ⊕ Fin q),
           if referenceCounts o ∈ E then referenceWeight M r o else 0)) ≤
          8*(s:ℝ)*(rho M q)^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Support 2 1 := ⟨{0}, by simp⟩
  let m : Fin 1 → Fin 2 := fun _ => 0
  have hm : Function.Injective m := fun i j _ => Subsingleton.elim i j
  have hms : ∀ j, m j ∈ S.val := by intro j; simp [m, S]
  have hc : compensation 2 1 (1/4) < 1 := by norm_num [compensation]
  have hh := h (s := 0) (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2)
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1) hc S m hm hms Set.univ
  change (1 : ℝ) ≤ 8*(0 : ℝ)*(rho 2 1)^2 at hh
  norm_num at hh

def family : Registration arena (type_of% @native_joint_count_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_joint_count_comparison, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0:ℝ), (1:ℝ), ?_⟩
    change |(0:ℝ)| ≠ |(1:ℝ)|
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_joint_count_comparison) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison.unit
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => |d|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
end
