import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal
noncomputable section
universe u

/-- The actual observation is the complete finite prefix of the infinite path. -/
abbrev signature : Signature where
  Params := (_ : Type u) × ℕ
  State p := ℕ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2 + 1) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α]
    (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] [IsProbabilityMeasure ν]
    [MeasurableSingletonClass α] (n : ℕ) (w : Fin (n + 1) → α),
    ((Kernel.trajMeasure (X := fun _ => α) ν
        (fun n => κ.comap (fun u : Iic n → α => u ⟨n, mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _))).map (R.readout () ⟨α, n⟩)) {w}
      = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ}

def actual : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
    (i : Fin (p.2 + 1)) => x i.1) (fun e => nomatch e)

/-- Repeating the initial state loses the transition recorded by a two-state prefix. -/
def rejected : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
    (_ : Fin (p.2 + 1)) => x 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  let w : Fin 2 → ULift.{u} Bool := ![a, b]
  have hab : a ≠ b := by decide
  have hfibre : (fun (x : ℕ → ULift.{u} Bool) (_ : Fin 2) => x 0) ⁻¹' {w} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    exact hab (h0.symm.trans h1)
  have hh := h (Measure.dirac a) (Kernel.const _ (Measure.dirac b)) 1 w
  dsimp only [rejected, realize] at hh
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w), hfibre] at hh
  simpa [w, a, b, Kernel.const_apply] using hh

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro α m ν κ hκ hν hs n w
    exact markov_chain_law_map_prefix_apply_singleton ν κ n w,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 0⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro h
    have hh := congrArg (fun f => (f 0).down) h
    cases hh

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} signature.{u}
    (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
      (i : Fin (p.2 + 1)) => x i.1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "ProbabilisticClosure") "TrajectoryLaws") "MarkovPrefixMass") "markov_chain_law_map_prefix_apply_singleton") "Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass/Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} signature.{u}
    (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
      (i : Fin (p.2 + 1)) => x i.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, definition := none, coordinates := #[0, 7], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "body"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.observationFact0, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass


noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
      Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
      Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.actual.{u})
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u})

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"markov_chain_law_map_prefix_apply_singleton\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u + 1, u, 0, u, 0}
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.arena.{u}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.actual.{u})
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u})

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.observation0.{u} : {α : Type u} →
  [inst : MeasurableSpace.{u} α] →
    (ν : @MeasureTheory.Measure.{u} α inst) →
      (κ : @ProbabilityTheory.Kernel.{u, u} α α inst inst) →
        [@ProbabilityTheory.IsMarkovKernel.{u, u} α α inst inst κ] →
          [@MeasureTheory.IsProbabilityMeasure.{u} α inst ν] →
            [@MeasurableSingletonClass.{u} α inst] →
              (n : Nat) →
                (w :
                    Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      α) →
                  (x : (n : Nat) → α) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
                      Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.signature.{u}
                      PUnit.unit.{1} (@Sigma.mk.{u + 1, 0} (Type u) (fun (x : Type u) => Nat) α n) :=
  fun {α : Type u} [MeasurableSpace.{u} α] (ν : @MeasureTheory.Measure.{u} α inst)
    (κ : @ProbabilityTheory.Kernel.{u, u} α α inst inst) [@ProbabilityTheory.IsMarkovKernel.{u, u} α α inst inst κ]
    [@MeasureTheory.IsProbabilityMeasure.{u} α inst ν] [@MeasurableSingletonClass.{u} α inst] (n : Nat)
    (w :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        α)
    (x : (n : Nat) → α) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.signature.{u}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.actual.{u} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, 0} (Type u) (fun (x : Type u) => Nat) α n) x

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"markov_chain_law_map_prefix_apply_singleton\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"body\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .function, .argument, .body], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"markov_chain_law_map_prefix_apply_singleton\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u}).actual (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u}).variation.2.choose (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u}).variation.1 (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"MarkovPrefixMass\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
