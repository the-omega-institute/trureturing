import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.HughesBlockExchange
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.HughesBlockExchange

open _root_.D5.S1.Words.HughesBlockExchange
open _root_.D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open _root_.D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : List α, List α
  State p := List p.1
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := WithTop Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (α : Type u) (u v w z : List α) (E : BlockCut α)
    (M : List Side) (r : Nat), u ≠ [] → v ≠ [] →
    w = original E → z = successor E → IsMinimumMask u v w M r →
    1 < r → Admissible E M →
    c E u v = ((r - 1 : Nat) : WithTop Nat) ∧
    R.readout false ⟨α,u,v⟩ z = min ((r - 1 : Nat) : WithTop Nat) (b E u v) ∧
    (R.readout true ⟨α,u,v⟩ z = ((r - 1 : Nat) : WithTop Nat) ↔
      ((r - 1 : Nat) : WithTop Nat) ≤ b E u v)

private def su : List (ULift.{u} (Fin 3)) := [⟨0⟩,⟨0⟩]
private def sv : List (ULift.{u} (Fin 3)) := [⟨1⟩]
private def cut : BlockCut (ULift.{u} (Fin 3)) := ⟨[],[⟨0⟩],[⟨1⟩],[⟨0⟩]⟩
private def mask : List Side := [.first,.second,.first]

private theorem count_length (N : List Side) :
    N.count .first + N.count .second = N.length := by
  induction N with
  | nil => rfl
  | cons q N ih => cases q <;> simp_all <;> omega

private theorem sample_min : IsMinimumMask su.{u} sv (original cut) mask 2 := by
  refine ⟨by unfold ValidMask ValidTwoSchedule; decide,by decide,?_⟩
  intro N hN
  have hl := count_length N
  have hcounts := hN.1
  simp only [ValidTwoSchedule,su,sv,List.length_cons,List.length_nil] at hcounts
  have hlen : N.length = 3 := by omega
  obtain ⟨a,b,c,hshape⟩ := List.length_eq_three.mp hlen
  subst N
  cases a <;> cases b <;> cases c <;>
    simp_all [ValidMask,ValidTwoSchedule,evaluateTwo,annotateTwo,annotateTwoFrom,
      readTwo,su,sv,original,cut,rho,List.splitBy,List.splitBy.loop]

private theorem sample_admissible : Admissible cut.{u} mask := by
  refine ⟨by decide,by decide,⟨[],[.first],[.second],[.first]⟩,?_,rfl,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · decide
  · exact Or.inl ⟨rfl,rfl,rfl⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (ULift.{u} (Fin 3)) su sv (original cut) (successor cut) cut mask 2
    (by decide) (by decide) rfl rfl sample_min (by omega) sample_admissible
  have hle := min_le_left (1 : WithTop Nat) (b cut su sv)
  have hdeg := he.2.1
  change (⊤ : WithTop Nat) = min 1 (b cut su sv) at hdeg
  rw [← hdeg] at hle
  simpa using hle

private theorem sample_b : b cut.{u} su sv = ⊤ := by
  classical
  have hempty : ¬ ∃ n : Nat, ∃ N,
      (ValidMask su.{u} sv (successor cut) N ∧ ¬ Commuting cut N) ∧ rho N = n := by
    rintro ⟨n,N,⟨hN,hC⟩,_⟩
    have hl := count_length N
    have hc := hN.1
    simp only [ValidTwoSchedule,su,sv,List.length_cons,List.length_nil] at hc
    have hlen : N.length = 3 := by omega
    obtain ⟨a,b,c,hshape⟩ := List.length_eq_three.mp hlen
    subst N
    cases a <;> cases b <;> cases c
    all_goals
      first
      | exact hC ⟨rfl,rfl⟩
      | simp_all [ValidMask,ValidTwoSchedule,evaluateTwo,annotateTwo,annotateTwoFrom,
          readTwo,su,sv,successor,cut]
  exact dif_neg hempty

private def perturbed (i : Bool) : Realization signature.{u} :=
  realize signature (fun j p z => if j = i then ⊤ else degree p.2.1 p.2.2 z)
    (fun e => Empty.elim e)

private theorem perturbed_law (i : Bool) : ¬ arena.{u}.Law (perturbed i) := by
  intro h
  have he := h (ULift.{u} (Fin 3)) su sv (original cut) (successor cut) cut mask 2
    (by decide) (by decide) rfl rfl sample_min (by omega) sample_admissible
  cases i
  · have hle := min_le_left (1 : WithTop Nat) (b cut su sv)
    have hdeg := he.2.1
    change (⊤ : WithTop Nat) = min 1 (b cut su sv) at hdeg
    rw [← hdeg] at hle
    simpa using hle
  · have hiff := he.2.2
    change ((⊤ : WithTop Nat) = 1 ↔ (1 : WithTop Nat) ≤ b cut su sv) at hiff
    rw [sample_b] at hiff
    simpa using hiff

private theorem mapM_nil {α β : Type*} (xs : List α) (f : α → Option β)
    (h : xs.mapM f = some []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      simp only [List.mapM_cons] at h
      cases hf : f a <;> cases hx : xs.mapM f <;> simp [hf,hx] at h

private theorem empty_degree : degree su.{u} sv [] = ⊤ := by
  classical
  have hempty : ¬ ∃ n : Nat, ∃ N, ValidMask su.{u} sv [] N ∧ rho N = n := by
    rintro ⟨n,N,hN,_⟩
    have ha := mapM_nil (annotateTwo N) (readTwo su sv) hN.2
    have he : N = [] := by
      cases N with
      | nil => rfl
      | cons q N => cases q <;> simp [annotateTwo,annotateTwoFrom] at ha
    subst N
    have hc := hN.1.1
    simp [su] at hc
  simp only [degree,minRuns,dif_neg hempty]

private theorem sample_finite : degree su.{u} sv (successor cut) ≠ ⊤ := by
  have he := result (ULift.{u} (Fin 3)) su sv (original cut) (successor cut) cut mask 2
    (by decide) (by decide) rfl rfl sample_min (by omega) sample_admissible
  have hle := min_le_left (1 : WithTop Nat) (b cut su sv)
  have hdeg : degree su sv (successor cut) = min 1 (b cut su sv) := by
    simpa using he.2.1
  rw [← hdeg] at hle
  intro htop
  rw [htop] at hle
  simpa using hle

def source_registration : Registration arena.{u} (type_of% (@result.{u})) where
  actual := realize signature.{u}
    (fun _ p z => degree p.2.1 p.2.2 z) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨result,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨perturbed i,?_,rfl,perturbed_law i⟩
      intro j hj
      funext p z
      change degree p.2.1 p.2.2 z =
        (if j = i then (⊤ : WithTop Nat) else degree p.2.1 p.2.2 z)
      exact (if_neg hj).symm
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 3),su,sv⟩,successor cut,[],?_⟩
    change degree su sv (successor cut) ≠ degree su sv []
    rw [empty_degree]
    exact sample_finite

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S1.Words.HughesBlockExchange.result.__information_unit
  realizationName := `Reg.D5.S1.Words.HughesBlockExchange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p z => degree p.2.1 p.2.2 z) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.HughesBlockExchange
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","arg","fn","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","arg","arg","fn","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end
end Reg.D5.S1.Words.HughesBlockExchange
