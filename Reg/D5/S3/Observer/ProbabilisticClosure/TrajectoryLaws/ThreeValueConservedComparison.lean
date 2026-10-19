import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Fin 3 → ℝ, Fin 3 → ℝ
  State _ := Fin 3 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => ∑ i, p.1 i * |p.2 i - w i|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f := ∀
    (pi : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (u v : Fin 3 → ℝ)
    (hp : ∀ i, 0 < pi i) (hpsum : ∑ i, pi i = 1)
    (hB : ∀ i j, 0 ≤ B i j) (hrow : ∀ i, ∑ j, B i j = 1)
    (hbal : ∀ i j, pi i * B i j = pi j * B j i)
    (hu : ∀ i, (1 : ℝ) / 3 ≤ u i ∧ u i ≤ 2 / 5)
    (hv : ∀ i, (1 : ℝ) / 3 ≤ v i ∧ v i ≤ 2 / 5)
    (t : ℝ) (ht : 0 < t),
    ∃ (T : ConstantSuspensionSeparator.StationaryTable (Fin 3)) (w : Fin 3 → ℝ)
      (Ah : Fin 3 → Fin 3 → ℝ) (vh tauh : Fin 3 → ℝ),
      T.pi = pi ∧ Ah = (fun i j => if i = j then 1 else 0) ∧ vh = v ∧ tauh = pi ∧
      (∀ i, (1 : ℝ) / 3 ≤ w i ∧ w i ≤ 2 / 5) ∧
      (∀ i, (1 : ℝ) / 3 ≤ vh i ∧ vh i ≤ 2 / 5) ∧
      (∀ i j, 0 ≤ T.C i j) ∧ (∀ i, ∑ j, T.C i j = 1) ∧
      (∀ i j, pi i * T.C i j = pi j * T.C j i) ∧
      (∀ j, ∑ i, pi i * T.C i j = pi j) ∧
      (∀ i j, 0 < T.C i j → w i = w j) ∧
      f.readout () ⟨pi, u⟩ w ≤ t ∧
      (∑ i, pi i * ((1 / 2 : ℝ) * ∑ j, |B i j - T.C i j|)) ≤
        2 * ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * B i j * (u i - u j)^2) / t^2 ∧
      ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * T.C i j * (w i - w j)^2) = 0

private theorem source_bridge :
    (type_of% (@three_value_conserved_comparison)) ↔ arena.Law actual := Iff.rfl

private theorem actual_law : arena.Law actual := three_value_conserved_comparison

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let pi : Fin 3 → ℝ := fun _ => 1/3
  let B : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0
  let u : Fin 3 → ℝ := fun _ => 1/3
  have hp : ∀ i, 0 < pi i := by intro i; norm_num [pi]
  have hpsum : ∑ i, pi i = 1 := by norm_num [pi, Fin.sum_univ_succ]
  have hB : ∀ i j, 0 ≤ B i j := by intro i j; dsimp [B]; split_ifs <;> norm_num
  have hrow : ∀ i, ∑ j, B i j = 1 := by intro i; simp [B]
  have hbal : ∀ i j, pi i * B i j = pi j * B j i := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [B, h, Ne.symm h]
  have hu : ∀ i, (1 : ℝ)/3 ≤ u i ∧ u i ≤ 2/5 := by intro i; norm_num [u]
  obtain ⟨T,w,Ah,vh,tauh,hpi,hA,hv,htau,hw,hvh,hn,hr,hba,hs,hsp,hm,hq,hz⟩ :=
    law pi B u u hp hpsum hB hrow hbal hu hu (1/2) (by norm_num)
  norm_num [rejected, realize] at hm

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨fun _ => 1/3, fun _ => 1/3⟩,
    (fun _ => 1/3), (fun _ => 2/5), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def record : Registration arena (type_of% (@three_value_conserved_comparison)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact False.elim (h (@Subsingleton.elim Unit _ other role))
    · intro e; exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@three_value_conserved_comparison) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison.record
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p w => ∑ i, p.1 i * |p.2 i - w i|) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent, partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms record
#print axioms registration
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
