import D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation

open _root_.D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
open _root_.D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (R)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => List ℕ)
    (fun _ => Multiset ℕ → Option ℕ → Polynomial ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ rows => count rows) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ),
    (∑ c, α c) = n →
    (f.readout () () (List.ofFn lam)
      (((List.finRange k).flatMap
        (fun c => List.replicate (α c) (c.val + 1))) : Multiset ℕ) none).map
          (Nat.castRingHom ℝ) = R lam α

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 0) (k := 0) Fin.elim0 Fin.elim0 (by simp)
  rw [← count_eq_R (n := 0) (k := 0) Fin.elim0 Fin.elim0 (by simp)] at he
  norm_num [rejected, realize, count] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), [], [1], ?_⟩
  intro he
  have h := congrFun (congrFun he (0 : Multiset ℕ)) none
  norm_num [actual, realize, count] at h

def family : Registration arena (type_of% (@count_eq_R)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_eq_R, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_eq_R) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation.count_eq_R.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rows => count rows) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
