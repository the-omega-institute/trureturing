import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54

open _root_.D5.S3.Combinatorics.Graph.LeapGroups.LeapGroup
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv Set MulAction Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54
open _root_.D5.S3.Combinatorics.Graph.Hypercube

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => cubeParity x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ n : ℕ, 3 ≤ n → Odd n → leapGroup (prism n) = ⊤) ∧
    (∀ (n : ℕ), 4 ≤ n → ∀ h : 2 ∣ n,
      leapGroup (prism n) =
        MulAction.stabilizer (Perm (ZMod 2 × ZMod n))
          ({{x | prismParity h x = 0}, {x | prismParity h x = 1}} :
            Set (Set (ZMod 2 × ZMod n)))) ∧
    (∀ n : ℕ, 1 ≤ n →
      leapGroup (hypercube n) =
        MulAction.stabilizer (Perm (Fin n → Bool))
          ({{x | r.readout () n x = 0}, {x | cubeParity x = 1}} :
            Set (Set (Fin n → Bool))))

private def a (_ : Fin 1) : Bool := true
private def b (_ : Fin 1) : Bool := false

private theorem weights : cubeParity a = 1 ∧ cubeParity b = 0 := by
  constructor <;> simp [cubeParity, a, b]

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, a, b, ?_⟩
  change cubeParity a ≠ cubeParity b
  rw [weights.1, weights.2]
  exact one_ne_zero

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let f : Perm (Fin 1 → Bool) := swap a b
  have hf : IsHop (hypercube 1) f := by
    intro x
    have hx : x = a ∨ x = b := by
      cases he : x 0
      · right
        funext i
        rw [Subsingleton.elim i 0]
        exact he
      · left
        funext i
        rw [Subsingleton.elim i 0]
        exact he
    change (hypercube 1).Adj x (swap a b x)
    rcases hx with rfl | rfl
    · rw [swap_apply_left]
      change hammingDist a b = 1
      decide
    · rw [swap_apply_right]
      change hammingDist b a = 1
      decide
  have hm : f ∈ leapGroup (hypercube 1) := Subgroup.subset_closure hf
  rw [bad.2.2 1 (by decide)] at hm
  rw [MulAction.mem_stabilizer_iff] at hm
  let S : Set (Fin 1 → Bool) := {x | cubeParity x = 1}
  have hs : S ∈ ({{x | rejected.readout () 1 x = 0}, S} : Set (Set (Fin 1 → Bool))) :=
    Set.mem_insert_of_mem _ (Set.mem_singleton S)
  have hsm : f • S ∈ ({{x | rejected.readout () 1 x = 0}, S} : Set (Set (Fin 1 → Bool))) := by
    rw [← hm]
    exact Set.mem_smul_set.mpr ⟨_, hs, rfl⟩
  have hmem : b ∈ f • S := Set.mem_smul_set.mpr ⟨a, weights.1, swap_apply_left a b⟩
  rcases Set.mem_insert_iff.mp hsm with h | h
  · rw [h] at hmem
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hmem
  · rw [Set.mem_singleton_iff.mp h] at hmem
    exact zero_ne_one (weights.2.symm.trans hmem)

def sourceRecord : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def resultRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54.resultRegistrationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54.sourceRecord
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cubeParity x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "arg", "arg", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.LeapGroups.SchachnerUdellQuestion54
