import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
import Mathlib.Tactic.NormNum
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open _root_.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
namespace Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => ENNReal.ofReal (2 * t)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original equivalence and every diameter clause, with one bound selected. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ {X : Type u} {A : Type v} {Y : Type w} [Nonempty X] [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (ε : ℝ) (_hε : 0 ≤ ε)
    (s : ℕ) (_hs : 1 ≤ s),
    (HasFinitePredictor F o ε s ↔ HasFiniteInvariantCover F o ε s) ∧
      (∀ (I : Type) (C : I → Set X) (δ : A → I → I) (y : I → Y),
        IsInvariantCover F o ε C δ y →
          ∀ i x, x ∈ C i → ∀ x', x' ∈ C i →
            futureDistance F o x x' ≤ obs.readout () () ε)

theorem positiveLaw : arena.{u,v,w}.Law actual :=
  @finite_predictor_iff_forward_invariant_cover.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let F : ULift.{v} Unit → ULift.{u} Bool → ULift.{u} Bool := fun _ x => x
  let o : ULift.{u} Bool → ULift.{w} ℝ := fun x => ⟨if x.down then 2 else 0⟩
  let C : Unit → Set (ULift.{u} Bool) := fun _ => Set.univ
  let δ : ULift.{v} Unit → Unit → Unit := fun _ _ => ()
  let y : Unit → ULift.{w} ℝ := fun _ => ⟨1⟩
  have hc : IsInvariantCover F o 1 C δ y := by
    constructor
    · intro i; exact ⟨⟨false⟩, Set.mem_univ _⟩
    · intro x; exact ⟨(), Set.mem_univ _⟩
    · intro a i x hx; exact Set.mem_univ _
    · intro i
      apply iSup_le
      rintro ⟨⟨x⟩, hx⟩
      apply (edist_le_ofReal (by norm_num : (0 : ℝ) ≤ 1)).2
      cases x <;> norm_num [o, y, ULift.dist_eq, Real.dist_eq]
  have hd := (h F o 1 (by norm_num) 1 (by norm_num)).2
    Unit C δ y hc () ⟨false⟩ (Set.mem_univ _) ⟨true⟩ (Set.mem_univ _)
  have he : edist (o ⟨false⟩) (o ⟨true⟩) ≤ 0 :=
    (le_iSup (fun word : List (ULift.{v} Unit) =>
      edist (o (runWord F word ⟨false⟩)) (o (runWord F word ⟨true⟩))) []).trans hd
  have heq := congrArg ULift.down (edist_le_zero.mp he)
  norm_num [o] at heq

theorem sensitivity : Sensitivity arena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u,v,w} (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => ENNReal.ofReal (2 * t)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "MetricGeometry") "ForwardInvariantPredictorCover") "finite_predictor_iff_forward_invariant_cover") "Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover/Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => ENNReal.ofReal (2 * t)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
