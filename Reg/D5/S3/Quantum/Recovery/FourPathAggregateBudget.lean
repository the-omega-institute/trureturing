import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathAggregateBudget
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FourPathAggregateBudget
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e _ => nomatch e)

abbrev distance_arena : Arena where
  signature := signature
  Law obs := ∀ {J : Type*} [Fintype J] (p q δ : J → ℝ),
    (hp : ∀ j, 0 ≤ p j) → (hq : ∀ j, 0 ≤ q j) →
    (hδ : ∀ j, min (p j) (q j) ≤ 1600 * δ j) →
    (obs.readout () () true = true) ∧
      (∑ j, min (p j) (q j) ≤ 1600 * ∑ j, δ j)

abbrev distance_claim : Prop := ∀ {J : Type*} [Fintype J] (p q δ : J → ℝ),
    (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ q j) →
    (∀ j, min (p j) (q j) ≤ 1600 * δ j) →
    ∑ j, min (p j) (q j) ≤ 1600 * ∑ j, δ j

theorem distance_actual_law : distance_arena.Law actual := by
  intro J inst p q δ hp hq hδ
  exact ⟨rfl, certificate_distance_budget p q δ hp hq hδ⟩

theorem distance_rejected_law : ¬ distance_arena.Law rejected := by
  intro h
  let J := ULift Unit
  have hh := h (J := J) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (by intro j; simp) (by intro j; simp) (by intro j; norm_num)
  exact Bool.false_ne_true (by simpa [rejected, realize] using hh.1)

def distance_source_registration : Registration distance_arena distance_claim where
  actual := actual
  bridge := by
    constructor
    · intro h J inst p q δ hp hq hδ
      exact ⟨rfl, h p q δ hp hq hδ⟩
    · intro h J inst p q δ hp hq hδ
      exact (h p q δ hp hq hδ).2
  variation := ⟨distance_actual_law, ⟨rejected, distance_rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, distance_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), False, True, ?_⟩
    simp [actual, realize]

def distance_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathAggregateBudget.certificate_distance_budget)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.certificate_distance_budget.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.distance_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨distance_arena⟩
  objectArena := .source ⟨distance_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source distance_arena ⟨distance_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev quartic_arena : Arena where
  signature := signature
  Law obs := ∀ {J : Type*} [Fintype J] (p q δ : J → ℝ),
    (hp : ∀ j, 0 ≤ p j) → (hq : ∀ j, 0 ≤ q j) →
    (hsumP : ∑ j, p j = 1) → (hsumQ : ∑ j, q j = 1) →
    (hδ : ∀ j, min (p j) (q j) ≤ 1600 * δ j) →
    (obs.readout () () true = true) ∧
      (∑ j, (min (p j) (q j)) ^ 2 ≤ 1600 * ∑ j, δ j)

abbrev quartic_claim : Prop := ∀ {J : Type*} [Fintype J] (p q δ : J → ℝ),
    (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ q j) →
    (∑ j, p j = 1) → (∑ j, q j = 1) →
    (∀ j, min (p j) (q j) ≤ 1600 * δ j) →
    ∑ j, (min (p j) (q j)) ^ 2 ≤ 1600 * ∑ j, δ j

theorem quartic_actual_law : quartic_arena.Law actual := by
  intro J inst p q δ hp hq hsumP hsumQ hδ
  exact ⟨rfl, quartic_distance_budget p q δ hp hq hsumP hsumQ hδ⟩

theorem quartic_rejected_law : ¬ quartic_arena.Law rejected := by
  intro h
  let J := ULift Unit
  have hh := h (J := J) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (by intro j; simp) (by intro j; simp) (by simp) (by simp) (by intro j; norm_num)
  exact Bool.false_ne_true (by simpa [rejected, realize] using hh.1)

def quartic_source_registration : Registration quartic_arena quartic_claim where
  actual := actual
  bridge := by
    constructor
    · intro h J inst p q δ hp hq hsumP hsumQ hδ
      exact ⟨rfl, h p q δ hp hq hsumP hsumQ hδ⟩
    · intro h J inst p q δ hp hq hsumP hsumQ hδ
      exact (h p q δ hp hq hsumP hsumQ hδ).2
  variation := ⟨quartic_actual_law, ⟨rejected, quartic_rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, quartic_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), False, True, ?_⟩
    simp [actual, realize]

def quartic_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathAggregateBudget.quartic_distance_budget)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.quartic_distance_budget.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.quartic_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨quartic_arena⟩
  objectArena := .source ⟨quartic_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quartic_arena ⟨quartic_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev root_arena : Arena where
  signature := signature
  Law obs := ∀ (S_cert S_tr M X ε : ℝ),
    (hcert : 0 ≤ S_cert) → (htr : 0 ≤ S_tr) → (heps : 0 ≤ ε) →
    (hM : M ≤ 1600 * S_cert) →
    (hX : X ≤ 4 * S_tr + 9 * M) →
    (hbudget : S_cert + S_tr ≤ 8 * ε) →
    (obs.readout () () true = true) ∧
      (2 * Real.sqrt X ≤ 480 * Real.sqrt 2 * Real.sqrt ε)

abbrev root_claim : Prop := ∀ (S_cert S_tr M X ε : ℝ),
    (0 ≤ S_cert) → (0 ≤ S_tr) → (0 ≤ ε) →
    (M ≤ 1600 * S_cert) →
    (X ≤ 4 * S_tr + 9 * M) →
    (S_cert + S_tr ≤ 8 * ε) →
    2 * Real.sqrt X ≤ 480 * Real.sqrt 2 * Real.sqrt ε

theorem root_actual_law : root_arena.Law actual := by
  intro S_cert S_tr M X ε hcert htr heps hM hX hbudget
  exact ⟨rfl, square_root_budget S_cert S_tr M X ε hcert htr heps hM hX hbudget⟩

theorem root_rejected_law : ¬ root_arena.Law rejected := by
  intro h
  have hh := h 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact Bool.false_ne_true (by simpa [rejected, realize] using hh.1)

def root_source_registration : Registration root_arena root_claim where
  actual := actual
  bridge := by
    constructor
    · intro h S_cert S_tr M X ε hcert htr heps hM hX hbudget
      exact ⟨rfl, h S_cert S_tr M X ε hcert htr heps hM hX hbudget⟩
    · intro h S_cert S_tr M X ε hcert htr heps hM hX hbudget
      exact (h S_cert S_tr M X ε hcert htr heps hM hX hbudget).2
  variation := ⟨root_actual_law, ⟨rejected, root_rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, root_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), False, True, ?_⟩
    simp [actual, realize]

def root_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathAggregateBudget.square_root_budget)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.square_root_budget.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget.root_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨root_arena⟩
  objectArena := .source ⟨root_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source root_arena ⟨root_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms distance_source_registration
#print axioms distance_registration
#print axioms quartic_source_registration
#print axioms quartic_registration
#print axioms root_source_registration
#print axioms root_registration

end Reg.D5.S3.Quantum.Recovery.FourPathAggregateBudget
