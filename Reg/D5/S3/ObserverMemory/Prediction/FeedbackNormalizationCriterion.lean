import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
universe u v

@[reducible] def signature : Signature where
  Params := ℕ
  State T := Fin T → ℝ
  Role := ULift.{u} Unit
  finiteRole := ⟨{⟨()⟩}, fun x => by
    have hx : x = ⟨()⟩ := Subsingleton.elim _ _
    simp only [hx, Finset.mem_singleton]⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := ULift.{v} Empty
  finiteAnchor := ⟨∅, fun x => nomatch x.down⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ f => ∏ t, f t) (fun e => nomatch e.down)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e.down)

@[reducible] def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀
    (T : ℕ) (hT : 1 ≤ T)
    (A : Fin T → Type u) (Y : Fin T → Type v)
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, DecidableEq (A t)]
    [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (hP : ∀ y a, 0 ≤ P y a)
    (hPsum : ∀ a, ∑ y, P y a = 1),
    List.TFAE [
      ∀ f : (t : Fin T) → Prefix Y t.val → A t, feedbackMass P f = 1,
      ∀ n, 1 ≤ n → n < T →
        ∀ (u : Prefix A n)
          (v w : (i : {i : Fin T // n ≤ i.val}) → A i.1)
          (E : Set (Prefix Y n)),
          feedbackMass P (singleCutSwitch n u v w E) = 1,
      ∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
        (∀ i, i.val < n → a i = b i) →
          prefixMarginal P n x a = prefixMarginal P n x b,
      ∃ q : (t : Fin T) → Prefix A (t.val + 1) → Prefix Y t.val → Y t → ℝ,
        (∀ t a x y, 0 ≤ q t a x y) ∧
        (∀ t a x, ∑ y, q t a x y = 1) ∧
        ∀ y a, P y a = R.readout ⟨()⟩ T (fun t => q t (restrictPrefix a (t.val + 1))
          (restrictPrefix y t.val) (y t))]

theorem actual_law : arena.Law actual := by
  exact feedback_normalization_prefix_causality_sequential_kernels

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have hcase := h 1 (by omega) (fun _ => ULift.{u} Unit) (fun _ => ULift.{v} Unit)
    (fun _ _ => (1 : ℝ)) (by intros; norm_num) (by intro a; simp)
  have hfirst : ∀ f : (t : Fin 1) → Prefix (fun _ => ULift.{v} Unit) t.val →
      ULift.{u} Unit, feedbackMass (fun _ _ => (1 : ℝ)) f = 1 := by
    intro f
    simp [feedbackMass]
  have hfourth := (List.TFAE.out hcase 0 3).mp hfirst
  obtain ⟨q, _, _, hfactor⟩ := hfourth
  have impossible := hfactor (fun _ => ⟨()⟩) (fun _ => ⟨()⟩)
  norm_num [rejected, realize] at impossible

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i.down⟩
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∏ _t : Fin 1, (0 : ℝ)) ≠ ∏ _t : Fin 1, (1 : ℝ)
    norm_num

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels.{u_1, u_2}) (type_of% (realize.{0, 0, u_1, 0, u_2} signature.{u_1, u_2} (fun _ _ f => ∏ t, f t) (fun e => nomatch e.down))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Prediction") "FeedbackNormalizationCriterion") "feedback_normalization_prefix_causality_sequential_kernels") "Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion/Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u_1, 0, u_2} signature.{u_1, u_2} (fun _ _ f => ∏ t, f t) (fun e => nomatch e.down)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "body", "arg", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.anchorEnumeration }


end Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion


noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, u_2} :=
  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, u_2} :=
  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, u_2}
  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u_1, 0, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, u_2}
      Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
      Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.actual.{u_1, u_2})
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"feedback_normalization_prefix_causality_sequential_kernels\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u_1, 0, u_2}
  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.arena.{u_1, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.actual.{u_1, u_2})
  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.roleEnumeration.{u_1} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_1, 0} Unit) where
  values := [@ULift.up.{u_1, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.anchorEnumeration.{u_2} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_2, 0} Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.observation0.{u_1, u_2} : (T : Nat) →
  (hT : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) T) →
    (A : Fin T → Type u_1) →
      (Y : Fin T → Type u_2) →
        [(t : Fin T) → Fintype.{u_1} (A t)] →
          [∀ (t : Fin T), Nonempty.{u_1 + 1} (A t)] →
            [(t : Fin T) → DecidableEq.{u_1 + 1} (A t)] →
              [inst : (t : Fin T) → Fintype.{u_2} (Y t)] →
                [∀ (t : Fin T), Nonempty.{u_2 + 1} (Y t)] →
                  [(t : Fin T) → DecidableEq.{u_2 + 1} (Y t)] →
                    (P : ((t : Fin T) → Y t) → ((t : Fin T) → A t) → Real) →
                      (hP :
                          ∀ (y : (t : Fin T) → Y t) (a : (t : Fin T) → A t),
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (P y a)) →
                        (hPsum :
                            ∀ (a : (t : Fin T) → A t),
                              @Eq.{1} Real
                                (@Finset.sum.{u_2, 0} ((t : Fin T) → Y t) Real Real.instAddCommMonoid
                                  (@Finset.univ.{u_2} ((t : Fin T) → Y t)
                                    (@Pi.instFintype.{0, u_2} (Fin T) Y (instDecidableEqFin T) (Fin.fintype T) inst))
                                  fun (y : (t : Fin T) → Y t) => P y a)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                          (q :
                              (t : Fin T) →
                                @D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.Prefix.{u_1} T A
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val T t)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                  @D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.Prefix.{u_2} T Y
                                      (@Fin.val T t) →
                                    Y t → Real) →
                            (y : (t : Fin T) → Y t) →
                              (a : (t : Fin T) → A t) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u_1, 0,
                                    u_2}
                                  Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.signature.{u_1,
                                    u_2}
                                  (@ULift.up.{u_1, 0} Unit Unit.unit) T :=
  fun (T : Nat) (hT : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) T)
    (A : Fin T → Type u_1) (Y : Fin T → Type u_2) [(t : Fin T) → Fintype.{u_1} (A t)]
    [∀ (t : Fin T), Nonempty.{u_1 + 1} (A t)] [(t : Fin T) → DecidableEq.{u_1 + 1} (A t)]
    [(t : Fin T) → Fintype.{u_2} (Y t)] [∀ (t : Fin T), Nonempty.{u_2 + 1} (Y t)]
    [(t : Fin T) → DecidableEq.{u_2 + 1} (Y t)] (P : ((t : Fin T) → Y t) → ((t : Fin T) → A t) → Real)
    (hP :
      ∀ (y : (t : Fin T) → Y t) (a : (t : Fin T) → A t),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (P y a))
    (hPsum :
      ∀ (a : (t : Fin T) → A t),
        @Eq.{1} Real
          (@Finset.sum.{u_2, 0} ((t : Fin T) → Y t) Real Real.instAddCommMonoid
            (@Finset.univ.{u_2} ((t : Fin T) → Y t)
              (@Pi.instFintype.{0, u_2} (Fin T) Y (instDecidableEqFin T) (Fin.fintype T) inst_3))
            fun (y : (t : Fin T) → Y t) => P y a)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (q :
      (t : Fin T) →
        @D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.Prefix.{u_1} T A
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val T t)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          @D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.Prefix.{u_2} T Y (@Fin.val T t) → Y t → Real)
    (y : (t : Fin T) → Y t) (a : (t : Fin T) → A t) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u_1, 0, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.signature.{u_1, u_2}
    Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.actual.{u_1, u_2}
    (@ULift.up.{u_1, 0} Unit Unit.unit) T fun (t : Fin T) =>
    q t
      (@D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.restrictPrefix.{u_1} T A a
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val T t)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.restrictPrefix.{u_2} T Y y (@Fin.val T t)) (y t)

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"feedback_normalization_prefix_causality_sequential_kernels\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .function, .argument, .argument, .body, .argument, .argument, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"feedback_normalization_prefix_causality_sequential_kernels\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2}).actual (Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Prediction\",\"FeedbackNormalizationCriterion\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion, declaration := `Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
