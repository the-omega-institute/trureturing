import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.FiniteNegativeRegression
import Reg.Support.DependentFamily

/-! Real comparison in the finite negative dependence statements. -/

namespace Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression

open _root_.D5.S3.Analytic.Probability
open _root_.D5.S3.Analytic.Probability.FiniteNegativeRegression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open Finset hiding expect
open scoped Classical

noncomputable section
universe u v

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

private def strict : Realization signature :=
  realize signature (fun _ _ a b => a < b) (fun e => nomatch e)

private theorem cmp_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) ((congrFun h 0).mp le_rfl)

private abbrev lowerArena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} {C : ι → Type v} [∀ i, Fintype (C i)] [Fintype ι]
    [∀ i, LinearOrder (C i)] (p : PMF (∀ i, C i)), FullNRD p → marginalProduct p < 81 →
    ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ)
    (g : (∀ j : J, C j) → ℝ), Monotone f → Monotone g →
      r.readout () () (cov p (f ∘ project I) (g ∘ project J)) 0

private abbrev upperArena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} {C : ι → Type v} [∀ i, Fintype (C i)] [Fintype ι]
    [∀ i, LinearOrder (C i)] (p : PMF (∀ i, C i)),
    (∀ (I J : Finset ι), Disjoint I J → ∀ U : Set (∀ i : I, C i), IsUpperSet U →
      ∀ (a b : ∀ j : J, C j), a ≤ b →
        0 < mass p (project J) a → 0 < mass p (project J) b →
        FiniteNegativeRegression.cond p (project J) b (event U ∘ project I) ≤
          FiniteNegativeRegression.cond p (project J) a (event U ∘ project I)) →
    ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ), Monotone f →
    ∀ (a b : ∀ j : J, C j), a ≤ b →
      0 < mass p (project J) a → 0 < mass p (project J) b →
        r.readout () () (FiniteNegativeRegression.cond p (project J) b (f ∘ project I))
          (FiniteNegativeRegression.cond p (project J) a (f ∘ project I))

private abbrev EmptyIndex := ULift.{u} Empty
private abbrev UnitFactor := ULift.{v} (Fin 1)
private def atom : EmptyIndex.{u} → UnitFactor.{v} := fun i => nomatch i.down
private def pointLaw : PMF (EmptyIndex.{u} → UnitFactor.{v}) := PMF.pure atom

private theorem pointNRD : FullNRD pointLaw.{u,v} := by
  intro I J hd f hf a b hab ha hb
  rw [Subsingleton.elim a b]

private theorem lower_strict_fails : ¬ lowerArena.{u,v}.Law strict := by
  intro h
  have hsize : marginalProduct pointLaw.{u,v} < 81 := by
    simp [marginalProduct]
  have hfalse := h pointLaw pointNRD hsize ∅ ∅ (by simp) (fun _ => 0) (fun _ => 0)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  simpa [strict, realize, cov, expect] using hfalse

private theorem upper_strict_fails : ¬ upperArena.{u,v}.Law strict := by
  intro h
  let J : Finset EmptyIndex.{u} := ∅
  let a := project J atom.{u,v}
  have hp : 0 < mass pointLaw (project J) a := by
    have hproj (x : EmptyIndex.{u} → UnitFactor.{v}) : project J x = a :=
      Subsingleton.elim _ _
    have hmass (x : EmptyIndex.{u} → UnitFactor.{v}) : (pointLaw x).toReal = 1 := by
      rw [Subsingleton.elim x atom]
      simp [pointLaw]
    simp [mass, fiberSum, hproj, hmass]
  have hfalse := h pointLaw (fun _ _ _ _ _ x y _ _ _ => by rw [Subsingleton.elim x y])
    ∅ J (by simp) (fun _ => 0) (fun _ _ _ => le_rfl) a a le_rfl hp hp
  exact (lt_irrefl _) hfalse

def lowerRealization :
    Registration lowerArena.{u,v} (type_of% @na_of_fullNRD_of_marginalProduct_lt_81.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@na_of_fullNRD_of_marginalProduct_lt_81.{u,v}, strict, lower_strict_fails⟩
  sensitivity := ⟨fun i => ⟨strict, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, lower_strict_fails⟩, fun e => nomatch e⟩
  dependence := cmp_dependence

def upperRealization :
    Registration upperArena.{u,v} (type_of% @fullNRD_of_upper.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fullNRD_of_upper.{u,v}, strict, upper_strict_fails⟩
  sensitivity := ⟨fun i => ⟨strict, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, upper_strict_fails⟩, fun e => nomatch e⟩
  dependence := cmp_dependence

def lowerRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@na_of_fullNRD_of_marginalProduct_lt_81.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression.lowerUnit
  realizationName := `Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression.lowerRealization
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerRealization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.FiniteNegativeRegression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def upperRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fullNRD_of_upper.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression.upperUnit
  realizationName := `Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression.upperRealization
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperRealization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.FiniteNegativeRegression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Analytic.Probability.FiniteNegativeRegression
