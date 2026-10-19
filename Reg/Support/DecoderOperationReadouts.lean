import Reg.Support.DecoderOperationTraceCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

abbrev Params : Type (max (u_1 + 1) (max (u_2 + 1) (u_3 + 1))) :=
  Σ C : Type u_1, Σ I : Type u_2, Σ O : Type u_3, Σ _ : C → Op C I O, ℕ → Option I

abbrev relationSignature : Signature where
  Params := Params.{u_1,u_2,u_3}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev traceSignature : Signature where
  Params := Params.{u_1,u_2,u_3}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → List p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def stepActual : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def traceActual : Realization traceSignature.{u_1,u_2,u_3} :=
  realize traceSignature (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def runActual : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def stepRejected : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def traceRejected : Realization traceSignature.{u_1,u_2,u_3} :=
  realize traceSignature (fun _ _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def runRejected : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ _ _ _ => False) (fun (e : Empty) _ => Empty.elim e)

abbrev stepArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    (action : C → Op C I O) (input : ℕ → Option I),
    Relator.RightUnique (R.readout () ⟨C, I, O, action, input⟩)

abbrev traceArena : Arena where
  signature := traceSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {vertices : List C}
    (_h : R.readout () ⟨C, I, O, action, input⟩ s t vertices),
    Relation.ReflTransGen (Step action input) s t

abbrev runClosureArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t : Frame C O},
    R.readout () ⟨C, I, O, action, input⟩ s t ↔
      Relation.ReflTransGen (Step action input) s t

abbrev runTransArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input t z),
    R.readout () ⟨C, I, O, action, input⟩ s z

abbrev runComparableArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input s z),
    R.readout () ⟨C, I, O, action, input⟩ t z ∨ Run action input z t

/-- These inhabited fibers witness global variation; the Laws quantify over all fibers. -/
private def sampleFrame (n : ℕ) : Frame (ULift.{u_1} Unit) (ULift.{u_3} Unit) :=
  ⟨⟨()⟩, n, []⟩

private def idleAction : ULift.{u_1} Unit →
    Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit) :=
  fun c => .internal c []

private def sampleParams : Params.{u_1,u_2,u_3} :=
  ⟨ULift.{u_1} Unit, ULift.{u_2} Unit, ULift.{u_3} Unit, idleAction, fun _ => none⟩

private theorem no_run_back
    (action : ULift.{u_1} Unit → Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit))
    (input : ℕ → Option (ULift.{u_2} Unit)) :
    ¬ Run action input (sampleFrame 1) (sampleFrame 0) := by
  intro h
  have bound := (run_mono h).1
  change 1 ≤ 0 at bound
  omega

theorem step_rejected_law : ¬ stepArena.{u_1,u_2,u_3}.Law stepRejected.{u_1,u_2,u_3} := by
  intro h
  have unique := h idleAction.{u_1,u_2,u_3} (fun _ => none)
  have equal : sampleFrame.{u_1,u_3} 0 = sampleFrame.{u_1,u_3} 1 :=
    unique (a := sampleFrame 0) True.intro True.intro
  have impossible : (0 : ℕ) = 1 := congrArg Frame.acquired equal
  omega

theorem trace_rejected_law : ¬ traceArena.{u_1,u_2,u_3}.Law traceRejected.{u_1,u_2,u_3} := by
  intro h
  have closure := h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 1) (t := sampleFrame 0) (vertices := []) True.intro
  exact no_run_back _ _ (run_closure.mpr closure)

theorem run_closure_rejected_law : ¬ runClosureArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  exact (h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0)).mpr .refl

theorem run_trans_rejected_law : ¬ runTransArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  exact h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0) (z := sampleFrame 0)
    ⟨_, .refl⟩ ⟨_, .refl⟩

theorem run_comparable_rejected_law : ¬ runComparableArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  let action : ULift.{u_1} Unit →
      Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit) :=
    fun _ => .acquire (fun _ => some (⟨()⟩, []))
  let input : ℕ → Option (ULift.{u_2} Unit) := fun _ => some ⟨()⟩
  have edge : Step action input (sampleFrame 0) (sampleFrame 1) :=
    Step.acquire (action := action) (input := input)
      ⟨()⟩ ⟨()⟩ 0 [] [] (fun _ => some (⟨()⟩, [])) ⟨()⟩ rfl rfl rfl
  have forward : Run action input (sampleFrame 0) (sampleFrame 1) :=
    ⟨_, Trace.refl.tail edge⟩
  rcases h (action := action) (input := input)
      (s := sampleFrame 0) (t := sampleFrame 0) (z := sampleFrame 1)
      ⟨_, .refl⟩ forward with impossible | backward
  · exact impossible
  · exact no_run_back action input backward

theorem run_dependence : ObservationalDependence relationSignature.{u_1,u_2,u_3} runActual.{u_1,u_2,u_3} := by
  intro i
  refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
  intro h
  have equal : Run idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
      Run idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
    congrFun h (sampleFrame 0)
  exact no_run_back _ _ (equal.mp ⟨_, Trace.refl⟩)

def stepRegistration : Registration stepArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@step_unique.{u_1,u_2,u_3}, stepRejected, step_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨stepRejected, ?_, rfl, step_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
    intro h
    have edge : Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) :=
      Step.internal (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
        ⟨()⟩ ⟨()⟩ 0 [] [] rfl
    have equal : Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
        Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
      congrFun h (sampleFrame 0)
    exact no_run_back _ _ ⟨_, Trace.refl.tail (equal.mp edge)⟩

def traceRegistration : Registration traceArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    traceSignature.{u_1,u_2,u_3}
    (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@trace_closure.{u_1,u_2,u_3}, traceRejected, trace_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨traceRejected, ?_, rfl, trace_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
    intro h
    have equal : Trace idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) [⟨()⟩] =
        Trace idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) [⟨()⟩] :=
      congrFun (congrFun h (sampleFrame 0)) [⟨()⟩]
    exact no_run_back _ _ ⟨_, equal.mp Trace.refl⟩

def runClosureRegistration : Registration runClosureArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_closure.{u_1,u_2,u_3}, runRejected, run_closure_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_closure_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runTransRegistration : Registration runTransArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_trans.{u_1,u_2,u_3}, runRejected, run_trans_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_trans_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runComparableRegistration : Registration runComparableArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_comparable.{u_1,u_2,u_3}, runRejected, run_comparable_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_comparable_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ z => compose C z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => c0 + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (model : Model) (execution : List Return),
      LegalWord .G0 .G0 (sourcePrefix j model execution) ∧
      (∀ p, source j model execution ((observedPrefix j model execution).length + p) =
        address (tailPrefix j) p) ∧
      (∀ p, coordinate (sourcePrefix j model execution)
          ((observedPrefix j model execution).length + p) = coordinate (tailPrefix j) p) ∧
      coordinate (externalWord j execution ++ anchor j model ++ tailPrefix j) 0 =
        c0 + sign j * execute j execution (initial j model) ∧
      (observedPrefix j model execution).length = observationOffset model + listWeight execution ∧
      (history model execution).length = observationOffset model + listWeight execution ∧
      (∀ D, r.readout () () (c0 + sign j * D) = c0 + sign j * (chi * D)) ∧
      (∀ D, compose (block j) (c0 + sign j * D) =
        c0 + sign j * (aSide j + rho * D)) ∧
      (∀ (a : Return) D, compose (returnWord j a) (c0 + sign j * D) =
        c0 + sign j * returnMap j a D) ∧
      (∀ (xs : List Return) D, compose (externalWord j xs) (c0 + sign j * D) =
        c0 + sign j * execute j xs D) ∧
      compose (tailPrefix j) 0 = c0 + sign j * xSide j

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .high .original []).2.2.2.2.2.2.1 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), c0, c0 + 1, ?_⟩
    have hc := (paired_source_reconstruction .high .original []).2.2.2.2.2.2.1
    have hc0 := hc 0
    have hc1 := hc 1
    simp only [sign, mul_zero, add_zero, one_mul, mul_one] at hc0 hc1
    have gp : 0 < g := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      dsimp [g, t]
      nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    have cp : 0 < chi := pow_pos gp 20
    change compose C c0 ≠ compose C (c0 + 1)
    rw [hc0, hc1]
    exact ne_of_lt (lt_add_of_pos_right c0 cp)

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.LiteralBranchReadout
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Label) (fun _ => ℝ → ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ l => branch l) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)

/-- The actual branch functions distinguish two legal label states at zero. -/
theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), Label.L0, Label.L2, ?_⟩
  intro heq
  have h := congrFun heq (0 : ℝ)
  norm_num [actual, realize, branch, shift] at h

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.LiteralBranchReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => List Label) (fun _ => ℝ → ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ w => compose w) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), [], [Label.L2], ?_⟩
  intro heq
  have h := congrFun heq (0 : ℝ)
  norm_num [actual, realize, compose, branch, shift] at h

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r :=     (∀ (s e : Guard) (w : List Label) (z : ℝ), LegalWord s e w → InSupport e z →
      InSupport s (compose w z)) ∧
    (∀ (left B right : List Label) (p : ℕ), p ≤ B.length →
      coordinate (left ++ B ++ right) (left.length + p) =
        compose (B.drop p) c0 + (-g) ^ (B.length - p) * (coordinate right 0 - c0)) ∧
    (∀ (w : List Label) (n p : ℕ), coordinate (w ++ List.replicate n Label.L0) p =
      coordinate w p) ∧
    (∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y) ∧
    (∀ (w v : List Label) (z : ℝ), r.readout () () (w ++ v) z = compose w (compose v z))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have h := h.2.2.2.2 [] [] 0
  norm_num [rejected, realize, compose] at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.LiteralBranchReadout

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s e : Guard) (w : List Label) (hw : LegalWord s e w),
    ∃ path : ℕ → Guard, path 0 = s ∧
      (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (coordinate w p)) ∧
      (∀ p, coordinate w p = r.readout () () (address w p) (coordinate w (p + 1)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨path, hpath0, hedges, hsupp, hrec⟩ := h .G0 .G0 [] rfl
  have h := hrec 0
  norm_num [LiteralBranchReadout.rejected, realize, coordinate, compose] at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_address_path) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_address_path, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204

