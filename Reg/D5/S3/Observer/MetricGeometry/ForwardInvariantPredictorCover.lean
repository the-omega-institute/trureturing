import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.observationFact0, `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover


noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
      Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.actual)
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"finite_predictor_iff_forward_invariant_cover\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.arena.{u_1, u_2, u_3}
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.actual)
  Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.observation0.{u_1, u_2, u_3} : {X : Type u_1} →
  {A : Type u_2} →
    {Y : Type u_3} →
      [Nonempty.{u_1 + 1} X] →
        [inst : MetricSpace.{u_3} Y] →
          (F : A → X → X) →
            (o : X → Y) →
              (ε : Real) →
                (hε :
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε) →
                  (s : Nat) →
                    (_hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s) →
                      (I : Type) →
                        (C : I → Set.{u_1} X) →
                          (δ : A → I → I) →
                            (y : I → Y) →
                              @D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.IsInvariantCover.{u_1, u_2,
                                      u_3, 0}
                                  X A Y I inst F o ε C δ y →
                                (i : I) →
                                  (x : X) →
                                    @Membership.mem.{u_1, u_1} X (Set.{u_1} X) (@Set.instMembership.{u_1} X) (C i) x →
                                      (x' : X) →
                                        @Membership.mem.{u_1, u_1} X (Set.{u_1} X) (@Set.instMembership.{u_1} X) (C i)
                                            x' →
                                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0,
                                              0, 0, 0, 0}
                                            Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.signature
                                            PUnit.unit.{1} PUnit.unit.{1} :=
  fun {X : Type u_1} {A : Type u_2} {Y : Type u_3} [Nonempty.{u_1 + 1} X] [MetricSpace.{u_3} Y] (F : A → X → X)
    (o : X → Y) (ε : Real)
    (hε : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (s : Nat) (_hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s)
    (I : Type) (C : I → Set.{u_1} X) (δ : A → I → I) (y : I → Y)
    (a :
      @D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.IsInvariantCover.{u_1, u_2, u_3, 0} X A Y I inst_1 F
        o ε C δ y)
    (i : I) (x : X) (a_1 : @Membership.mem.{u_1, u_1} X (Set.{u_1} X) (@Set.instMembership.{u_1} X) (C i) x) (x' : X)
    (a_2 : @Membership.mem.{u_1, u_1} X (Set.{u_1} X) (@Set.instMembership.{u_1} X) (C i) x') =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.signature
    Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.actual PUnit.unit.{1} PUnit.unit.{1} ε

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"finite_predictor_iff_forward_invariant_cover\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"finite_predictor_iff_forward_invariant_cover\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ForwardInvariantPredictorCover\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, declaration := `Reg.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
