import D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
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

run_cmd do
  let root := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
  let sourceName := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound ++
    `shared_control_bit_storage_bound
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := "sha256:0784cf503dfe5b78a65875009000f173bf6ffa84e7614fb47b4041a701fe3e3e"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

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

register_information_theorem shared_control_bit_storage_bound in arena
  readout via (realize signature (fun _ _ u => u) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "fn", "arg", "domain", "fn",
        "arg", "arg", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
