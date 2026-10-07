import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset MeasureTheory Preorder ProbabilityTheory
open ProbabilityTheory.Kernel
noncomputable section
universe u v

/-- Coordinates retain the sample type, every dependent time type, and the process. -/
abbrev signature : Signature where
  Params := (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (n : ℕ) → p.2.1 n
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {Ω : Type v} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}
    [∀ n, IsMarkovKernel (κ n)] {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
    [IsFiniteMeasure P] {Y : (n : ℕ) → Ω → X n}
    (hY_meas : ∀ n, Measurable (Y n)) (h0 : HasLaw (Y 0) μ₀ P)
    (h_condDistrib : ∀ n, HasCondDistrib (Y (n + 1))
      (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P),
    HasLaw (R.readout () ⟨Ω, X, Y⟩) (trajMeasure μ₀ κ) P

def actual : Realization signature.{u,v} :=
  realize signature (fun (_ : Unit)
    (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
    (ω : p.1) (n : ℕ) => p.2.2 n ω) (fun e => nomatch e)

/-- This intervention erases the sample while preserving all dependent output types. -/
def rejected : Realization signature.{u,v} :=
  realize signature (fun (_ : Unit)
    (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
    (ω : p.1) (n : ℕ) => Classical.choice (show Nonempty (p.2.1 n) from ⟨p.2.2 n ω⟩))
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u,v} := by
  intro h
  let Ω := ULift.{v} Unit
  let B := ULift.{u} Bool
  let b : B := Classical.choice (inferInstance : Nonempty B)
  let c : B := ⟨!b.down⟩
  let P : Measure Ω := Measure.dirac ⟨()⟩
  let Y : (n : ℕ) → Ω → B := fun _ _ => c
  let κ : (n : ℕ) → Kernel (Iic n → B) B :=
    fun _ => Kernel.const _ (Measure.dirac c)
  have hc : b ≠ c := by
    intro heq
    have hh := congrArg ULift.down heq
    change b.down = !b.down at hh
    have hn : ∀ z : Bool, z ≠ !z := by decide
    exact hn b.down hh
  have hY : ∀ n, Measurable (Y n) := by intro n; exact measurable_const
  have h0 : HasLaw (Y 0) (Measure.dirac c) P := hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hcond : ∀ n, HasCondDistrib (Y (n + 1))
      (fun ω => fun i : Iic n => Y i ω) (κ n) P := by
    intro n
    constructor
    · change AEMeasurable (fun _ : Ω => ((fun _ : Iic n => c), c)) P
      exact measurable_const.aemeasurable
    · simp [Y, P, κ, Measure.map_const, Measure.compProd_const, Measure.dirac_prod_dirac]
  have hbad := h hY h0 hcond
  have hgood := has_law_traj_measure hY h0 hcond
  have heq := hbad.map_eq.trans hgood.map_eq.symm
  change P.map (fun _ : Ω => fun _ : ℕ => b) =
    P.map (fun _ : Ω => fun _ : ℕ => c) at heq
  have hmass := congrArg (fun μ : Measure (ℕ → B) => μ {fun _ => c}) heq
  have hpath : (fun _ : ℕ => b) ≠ (fun _ : ℕ => c) := fun h => hc (congrFun h 0)
  simpa [P, Measure.map_const, hpath, Ne.symm hpath] using hmass

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨has_law_traj_measure,
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
    refine ⟨⟨ULift.{v} Bool, (fun _ => ULift.{u} Bool),
      (fun _ ω => ⟨ω.down⟩)⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have hh := congrArg (fun f => (f 0).down) h
    cases hh

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.has_law_traj_measure.{u, v}) (type_of% (realize.{max (u + 1) (v + 1), v, 0, u, 0} signature.{u, v}
    (fun (_ : Unit)
      (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
      (ω : p.1) (n : ℕ) => p.2.2 n ω) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "ProbabilisticClosure") "TrajectoryLaws") "HasLawTrajectory") "has_law_traj_measure") "Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory/Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1), v, 0, u, 0} signature.{u, v}
    (fun (_ : Unit)
      (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
      (ω : p.1) (n : ℕ) => p.2.2 n ω) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, definition := none, coordinates := #[0, 3, 10], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.has_law_traj_measure, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.observationFact0, `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory


noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), v, 0, u, 0} :=
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.arena.{u, v}
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), v, 0, u, 0} :=
  Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.arena.{u, v}
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence


noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u + 1) (v + 1), v, 0, u, 0} (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.arena.) (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).actual

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"has_law_traj_measure\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.has_law_traj_measure, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).bridge

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.observation0.{u, v} : {Ω : Type v} →
  {mΩ : MeasurableSpace.{v} Ω} →
    {P : @MeasureTheory.Measure.{v} Ω mΩ} →
      {X : Nat → Type u} →
        [inst : (n : Nat) → MeasurableSpace.{u} (X n)] →
          {κ :
              (n : Nat) →
                @ProbabilityTheory.Kernel.{u, u}
                  ((i :
                      @Subtype.{1} Nat fun (x : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                          (@Finset.Iic.{0} Nat Nat.instPreorder
                            (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                              Nat.instLocallyFiniteOrder Nat.instOrderBot)
                            n)
                          x) →
                    X
                      (@Subtype.val.{1} Nat
                        (fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Finset.Iic.{0} Nat Nat.instPreorder
                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                              n)
                            x)
                        i))
                  (X
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@MeasurableSpace.pi.{0, u}
                    (@Subtype.{1} Nat fun (x : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                        (@Finset.Iic.{0} Nat Nat.instPreorder
                          (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                            Nat.instLocallyFiniteOrder Nat.instOrderBot)
                          n)
                        x)
                    (fun
                        (i :
                          @Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                n)
                              x) =>
                      X
                        (@Subtype.val.{1} Nat
                          (fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                n)
                              x)
                          i))
                    fun
                      (a :
                        @Subtype.{1} Nat fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Finset.Iic.{0} Nat Nat.instPreorder
                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                              n)
                            x) =>
                    inst
                      (@Subtype.val.{1} Nat
                        (fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Finset.Iic.{0} Nat Nat.instPreorder
                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                              n)
                            x)
                        a))
                  (inst
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
            [∀ (n : Nat),
                  @ProbabilityTheory.IsMarkovKernel.{u, u}
                    ((i :
                        @Subtype.{1} Nat fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Finset.Iic.{0} Nat Nat.instPreorder
                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                              n)
                            x) →
                      X
                        (@Subtype.val.{1} Nat
                          (fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                n)
                              x)
                          i))
                    (X
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@MeasurableSpace.pi.{0, u}
                      (@Subtype.{1} Nat fun (x : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                          (@Finset.Iic.{0} Nat Nat.instPreorder
                            (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                              Nat.instLocallyFiniteOrder Nat.instOrderBot)
                            n)
                          x)
                      (fun
                          (i :
                            @Subtype.{1} Nat fun (x : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                (@Finset.Iic.{0} Nat Nat.instPreorder
                                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                    Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                  n)
                                x) =>
                        X
                          (@Subtype.val.{1} Nat
                            (fun (x : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                (@Finset.Iic.{0} Nat Nat.instPreorder
                                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                    Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                  n)
                                x)
                            i))
                      fun
                        (a :
                          @Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                n)
                              x) =>
                      inst
                        (@Subtype.val.{1} Nat
                          (fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                n)
                              x)
                          a))
                    (inst
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (κ n)] →
              {μ₀ :
                  @MeasureTheory.Measure.{u} (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))} →
                [@MeasureTheory.IsProbabilityMeasure.{u}
                      (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) μ₀] →
                  [@MeasureTheory.IsFiniteMeasure.{v} Ω mΩ P] →
                    {Y : (n : Nat) → Ω → X n} →
                      (hY_meas : ∀ (n : Nat), @Measurable.{v, u} Ω (X n) mΩ (inst n) (Y n)) →
                        (h0 :
                            @ProbabilityTheory.HasLaw.{v, u} Ω
                              (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) mΩ
                              (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (Y (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) μ₀ P) →
                          (h_condDistrib :
                              ∀ (n : Nat),
                                @ProbabilityTheory.HasCondDistrib.{v, u, u} Ω
                                  ((i :
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Finset.Iic.{0} Nat Nat.instPreorder
                                            (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                              Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                            n)
                                          x) →
                                    X
                                      (@Subtype.val.{1} Nat
                                        (fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Finset.Iic.{0} Nat Nat.instPreorder
                                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                              n)
                                            x)
                                        i))
                                  (X
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  mΩ
                                  (@MeasurableSpace.pi.{0, u}
                                    (@Subtype.{1} Nat fun (x : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (@Finset.Iic.{0} Nat Nat.instPreorder
                                          (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                            Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                          n)
                                        x)
                                    (fun
                                        (i :
                                          @Subtype.{1} Nat fun (x : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                                n)
                                              x) =>
                                      X
                                        (@Subtype.val.{1} Nat
                                          (fun (x : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (@Finset.Iic.{0} Nat Nat.instPreorder
                                                (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                  Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                                n)
                                              x)
                                          i))
                                    fun
                                      (a :
                                        @Subtype.{1} Nat fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Finset.Iic.{0} Nat Nat.instPreorder
                                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                              n)
                                            x) =>
                                    inst
                                      (@Subtype.val.{1} Nat
                                        (fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Finset.Iic.{0} Nat Nat.instPreorder
                                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                              n)
                                            x)
                                        a))
                                  (inst
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (Y
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (fun (ω : Ω)
                                      (i :
                                        @Subtype.{1} Nat fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Finset.Iic.{0} Nat Nat.instPreorder
                                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                              n)
                                            x) =>
                                    Y
                                      (@Subtype.val.{1} Nat
                                        (fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Finset.Iic.{0} Nat Nat.instPreorder
                                              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                                                Nat.instLocallyFiniteOrder Nat.instOrderBot)
                                              n)
                                            x)
                                        i)
                                      ω)
                                  (κ n) P) →
                            (ω : Ω) →
                              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u + 1)
                                    (v + 1),
                                  v, 0, u, 0}
                                Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.signature.{u, v}
                                PUnit.unit.{1}
                                (@Sigma.mk.{v + 1, max (max u v) (u + 1)} (Type v)
                                  (fun (Ω : Type v) =>
                                    @Sigma.{u + 1, max u v} (Nat → Type u) fun (X : Nat → Type u) =>
                                      (n : Nat) → Ω → X n)
                                  Ω
                                  (@Sigma.mk.{u + 1, max u v} (Nat → Type u)
                                    (fun (X : Nat → Type u) => (n : Nat) → Ω → X n) X Y)) :=
  fun {Ω : Type v} {mΩ : MeasurableSpace.{v} Ω} {P : @MeasureTheory.Measure.{v} Ω mΩ} {X : Nat → Type u}
    [(n : Nat) → MeasurableSpace.{u} (X n)]
    {κ :
      (n : Nat) →
        @ProbabilityTheory.Kernel.{u, u}
          ((i :
              @Subtype.{1} Nat fun (x : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Iic.{0} Nat Nat.instPreorder
                    (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      Nat.instOrderBot)
                    n)
                  x) →
            X
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                i))
          (X
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@MeasurableSpace.pi.{0, u}
            (@Subtype.{1} Nat fun (x : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (@Finset.Iic.{0} Nat Nat.instPreorder
                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    Nat.instOrderBot)
                  n)
                x)
            (fun
                (i :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x) =>
              X
                (@Subtype.val.{1} Nat
                  (fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x)
                  i))
            fun
              (a :
                @Subtype.{1} Nat fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x) =>
            inst
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                a))
          (inst
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
    [∀ (n : Nat),
        @ProbabilityTheory.IsMarkovKernel.{u, u}
          ((i :
              @Subtype.{1} Nat fun (x : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Iic.{0} Nat Nat.instPreorder
                    (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      Nat.instOrderBot)
                    n)
                  x) →
            X
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                i))
          (X
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@MeasurableSpace.pi.{0, u}
            (@Subtype.{1} Nat fun (x : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (@Finset.Iic.{0} Nat Nat.instPreorder
                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    Nat.instOrderBot)
                  n)
                x)
            (fun
                (i :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x) =>
              X
                (@Subtype.val.{1} Nat
                  (fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x)
                  i))
            fun
              (a :
                @Subtype.{1} Nat fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x) =>
            inst
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                a))
          (inst
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (κ n)]
    {μ₀ :
      @MeasureTheory.Measure.{u} (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))}
    [@MeasureTheory.IsProbabilityMeasure.{u} (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) μ₀]
    [@MeasureTheory.IsFiniteMeasure.{v} Ω mΩ P] {Y : (n : Nat) → Ω → X n}
    (hY_meas : ∀ (n : Nat), @Measurable.{v, u} Ω (X n) mΩ (inst n) (Y n))
    (h0 :
      @ProbabilityTheory.HasLaw.{v, u} Ω (X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) mΩ
        (inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Y (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) μ₀ P)
    (h_condDistrib :
      ∀ (n : Nat),
        @ProbabilityTheory.HasCondDistrib.{v, u, u} Ω
          ((i :
              @Subtype.{1} Nat fun (x : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Iic.{0} Nat Nat.instPreorder
                    (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      Nat.instOrderBot)
                    n)
                  x) →
            X
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                i))
          (X
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          mΩ
          (@MeasurableSpace.pi.{0, u}
            (@Subtype.{1} Nat fun (x : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (@Finset.Iic.{0} Nat Nat.instPreorder
                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    Nat.instOrderBot)
                  n)
                x)
            (fun
                (i :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x) =>
              X
                (@Subtype.val.{1} Nat
                  (fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Finset.Iic.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          Nat.instOrderBot)
                        n)
                      x)
                  i))
            fun
              (a :
                @Subtype.{1} Nat fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x) =>
            inst
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                a))
          (inst
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Y
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun (ω : Ω)
              (i :
                @Subtype.{1} Nat fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x) =>
            Y
              (@Subtype.val.{1} Nat
                (fun (x : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.Iic.{0} Nat Nat.instPreorder
                      (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        Nat.instOrderBot)
                      n)
                    x)
                i)
              ω)
          (κ n) P)
    (ω : Ω) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u + 1) (v + 1), v, 0, u, 0}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.signature.{u, v}
    Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.actual.{u, v} PUnit.unit.{1}
    (@Sigma.mk.{v + 1, max (max u v) (u + 1)} (Type v)
      (fun (Ω : Type v) => @Sigma.{u + 1, max u v} (Nat → Type u) fun (X : Nat → Type u) => (n : Nat) → Ω → X n) Ω
      (@Sigma.mk.{u + 1, max u v} (Nat → Type u) (fun (X : Nat → Type u) => (n : Nat) → Ω → X n) X Y))
    ω

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"has_law_traj_measure\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"function\",\"argument\",\"body\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.has_law_traj_measure, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .function, .argument, .body], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"has_law_traj_measure\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.has_law_traj_measure, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).actual (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).variation.2.choose (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).variation.1 (Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1.descriptorFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"ProbabilisticClosure\",\"TrajectoryLaws\",\"HasLawTrajectory\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory, declaration := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))
