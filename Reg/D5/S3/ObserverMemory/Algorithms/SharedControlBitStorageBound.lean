import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
open Function Set LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound

@[reducible] def signature : Signature where
  Params := Σ _ : ℕ, Type
  State p := (((Fin p.1 → ZMod 2) × ZMod 2) → p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (((Fin p.1 → ZMod 2) × ZMod 2) → p.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ u _ => u 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (hd : 2 ≤ d) {α β : Type} [Finite α] [Finite β]
    (u : ((Fin d → ZMod 2) × ZMod 2) → α)
    (v : ((Fin d → ZMod 2) × ZMod 2) → β)
    (hu : DynamicallyClosed u) (hv : DynamicallyClosed v)
    (hjoint : Injective (fun z => (u z, v z))),
    (∃ H : Submodule (ZMod 2) ((Fin d → ZMod 2) × ZMod 2),
      (∀ z z', u z = u z' ↔ z - z' ∈ H) ∧
        (H ≤ LinearMap.range
            (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)) ∨ H = ⊤)) ∧
    (∀ H : Submodule (ZMod 2) ((Fin d → ZMod 2) × ZMod 2),
      (H ≤ LinearMap.range
          (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)) ∨ H = ⊤) →
        DynamicallyClosed H.mkQ ∧
          ∀ z z', H.mkQ z = H.mkQ z' ↔ z - z' ∈ H) ∧
    ((¬Injective (R.readout () ⟨d, α⟩ u) ∧ ¬Injective v) →
      2 ^ (d + 2) ≤ (Set.range u).ncard * (Set.range v).ncard) ∧
    ∀ h : ℕ, 1 ≤ h → ∀ hupper : h ≤ d - 1,
      let hle : h ≤ d := hupper.trans (Nat.sub_le d 1)
      DynamicallyClosed (suffixCode hle) ∧
        DynamicallyClosed (prefixCode hle) ∧
        Injective (fun z => (suffixCode hle z, prefixCode hle z)) ∧
        (Set.range (suffixCode hle)).ncard *
            (Set.range (prefixCode hle)).ncard = 2 ^ (d + 2)



theorem actual_law : arena.Law actual := by
  intro d hd α β _ _ u v hu hv hjoint
  simpa [actual, realize] using
    (shared_control_bit_storage_bound d hd u v hu hv hjoint)

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let V := (Fin 2 → ZMod 2) × ZMod 2
  let u : V → V := id
  let v : V → Unit := fun _ => ()
  have hu : DynamicallyClosed u := by
    intro f hf
    exact ⟨f, rfl⟩
  have hv : DynamicallyClosed v := by
    intro f hf
    exact ⟨id, rfl⟩
  have hjoint : Injective (fun z => (u z, v z)) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hcollapsed : ¬Injective (rejected.readout () ⟨2, V⟩ u) := by
    intro hinjective
    let x : V := (0, 0)
    let y : V := (Pi.single (0 : Fin 2) 1, 0)
    have hxy : rejected.readout () ⟨2, V⟩ u x =
        rejected.readout () ⟨2, V⟩ u y := rfl
    have heq := hinjective hxy
    have hcoordinate := congrArg (fun z : V => z.1 (0 : Fin 2)) heq
    simp [x, y] at hcoordinate
  have hvNoninjective : ¬Injective v := by
    intro hinjective
    let x : V := (0, 0)
    let y : V := (Pi.single (0 : Fin 2) 1, 0)
    have hxy : v x = v y := rfl
    have heq : x = y := @hinjective x y hxy
    have hcoordinate := congrArg (fun z : V => z.1 (0 : Fin 2)) heq
    simp [x, y] at hcoordinate
  have huRange : Set.range u = Set.univ := Set.range_eq_univ.mpr surjective_id
  have hvRange : Set.range v = Set.univ := Set.range_eq_univ.mpr (by
    intro value
    cases value
    exact ⟨0, rfl⟩)
  have lower := (law 2 (by decide) u v hu hv hjoint).2.2.1
    ⟨hcollapsed, hvNoninjective⟩
  rw [huRange, hvRange, Set.ncard_univ, Set.ncard_univ] at lower
  norm_num [V, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card] at lower

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Bool⟩, (fun _ => false), (fun _ => true), ?_⟩
  intro heq
  have hvalue := congrFun heq (0, 0)
  simp [actual, realize] at hvalue

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ _ u => u) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Algorithms") "SharedControlBitStorageBound") "shared_control_bit_storage_bound") "Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound/Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ _ u => u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, definition := none, coordinates := #[0, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "domain", "fn", "arg", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound


noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0} (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena) (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).actual

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"shared_control_bit_storage_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).bridge

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.observation0 : (d : Nat) →
  (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d) →
    {α β : Type} →
      [Finite.{1} α] →
        [Finite.{1} β] →
          (u :
              Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                α) →
            (v :
                Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                  β) →
              (hu : @D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.DynamicallyClosed.{0} d α u) →
                (hv : @D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.DynamicallyClosed.{0} d β v) →
                  (hjoint :
                      @Function.Injective.{1, 1}
                        (Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (Prod.{0, 0} α β)
                        fun
                          (z :
                            Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                        @Prod.mk.{0, 0} α β (u z) (v z)) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                      Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.signature PUnit.unit.{1}
                      (@Sigma.mk.{0, 1} Nat (fun (x : Nat) => Type) d α) :=
  fun (d : Nat) (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
    {α β : Type} [Finite.{1} α] [Finite.{1} β]
    (u :
      Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        α)
    (v :
      Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        β)
    (hu : @D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.DynamicallyClosed.{0} d α u)
    (hv : @D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.DynamicallyClosed.{0} d β v)
    (hjoint :
      @Function.Injective.{1, 1}
        (Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Prod.{0, 0} α β)
        fun
          (z :
            Prod.{0, 0} (Fin d → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
        @Prod.mk.{0, 0} α β (u z) (v z)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.signature
    Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 1} Nat (fun (x : Nat) => Type) d α) u

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"shared_control_bit_storage_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"domain\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument, .domain, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"shared_control_bit_storage_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).actual (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).variation.2.choose (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).variation.1 (Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"Algorithms\",\"SharedControlBitStorageBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound, declaration := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
