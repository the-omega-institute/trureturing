import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source-family bridges for bounded prime stripping and support recognition. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace specification

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ pk m => strip pk.2 pk.1 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p m : ℕ}, ∀ k : ℕ, (¬p ^ (k + 1) ∣ m) ↔
    0 < R.readout () (p, k) m ∧ R.readout () (p, k) m ≤ m ∧
      ¬p ∣ R.readout () (p, k) m ∧
      ∃ e ≤ k, m = p ^ e * R.readout () (p, k) m

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := ((h (p := 2) (m := 1) 1).mp (by decide)).1
  exact (Nat.lt_irrefl 0) hh

def family : Registration arena (type_of% (@strip_spec)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strip_spec, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(2, 1), 1, 3, ?_⟩
    change strip 1 2 1 ≠ strip 1 2 3
    decide

end specification

namespace strip_factored_iff

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ pk m => strip pk.2 pk.1 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p m : ℕ}, (p.Prime ∨ p ≤ 1) → ∀ (k : ℕ) (s : Finset ℕ),
    (p ≤ 1 ∨ p ∈ s ∨ m = 0 ∨ ¬p ^ (k + 1) ∣ m) →
      (R.readout () (p, k) m ∈ Nat.factoredNumbers s ↔
        m ∈ Nat.factoredNumbers (insert p s))

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hx : (1 : ℕ) ∈ Nat.factoredNumbers (insert 2 (∅ : Finset ℕ)) := by
    refine ⟨by decide, ?_⟩
    intro p hp
    rw [Nat.primeFactorsList_one] at hp
    exact (List.not_mem_nil hp).elim
  have hh := (h (p := 2) (m := 1) (Or.inl Nat.prime_two) 0 ∅
    (Or.inr (Or.inr (Or.inr (by decide))))).mpr hx
  change (0 : ℕ) ∈ Nat.factoredNumbers ∅ at hh
  exact hh.1 rfl

def family : Registration arena (type_of% (@strip_factored_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strip_factored_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(2, 1), 1, 3, ?_⟩
    change strip 1 2 1 ≠ strip 1 2 3
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strip_factored_iff) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.strip_factored_iff)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ pk m => strip pk.2 pk.1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end strip_factored_iff

namespace isSmooth_iff

abbrev signature : Signature where
  Params := List ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ps m => isSmooth ps m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ps : List ℕ}, (∀ p ∈ ps, p.Prime ∨ p ≤ 1) → ∀ {m : ℕ},
    (m = 0 ∨ ∀ p ∈ ps, p.Prime → ¬p ^ 65 ∣ m) →
    (R.readout () ps m = true ↔ m ∈ Nat.factoredNumbers ps.toFinset)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hx : (1 : ℕ) ∈ Nat.factoredNumbers ([] : List ℕ).toFinset := by simp
  have hh := (h (ps := []) (by simp) (m := 1) (Or.inr (by simp))).mpr hx
  exact Bool.false_ne_true hh

def family : Registration arena (type_of% (@isSmooth_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨isSmooth_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], 0, 1, ?_⟩
    change isSmooth [] 0 ≠ isSmooth [] 1
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isSmooth_iff) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.isSmooth_iff)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ps m => isSmooth ps m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end isSmooth_iff

namespace specification

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strip_spec) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.strip_spec)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ pk m => strip pk.2 pk.1 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end specification

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
