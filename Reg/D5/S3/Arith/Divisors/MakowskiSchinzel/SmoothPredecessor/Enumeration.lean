import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete weighted prime-power fold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

abbrev signature : Signature where
  Params := ℕ × (ℕ → ℕ) × ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a c => powSum a.1 a.2.1 a.2.2.1 a.2.2.2 c)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (f : ℕ → ℕ) {p X c : ℕ},
    R.readout () (n, f, p, X) c =
      (∑ e ∈ range n, if c * p ^ e ≤ X then f (c * p ^ e) else 0) ↔
        n ≤ 1 ∨ 1 ≤ p ∨ c ≤ X ∨ f 0 = 0

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h 0 id (p := 1) (X := 0) (c := 0)).mpr (Or.inl (by decide))
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@powSum_eq_sum_range)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨powSum_eq_sum_range, rejected, rejected_law⟩
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
    refine ⟨(1, id, 1, 1), 0, 1, ?_⟩
    norm_num [actual, realize, powSum]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@powSum_eq_sum_range) (Realization signature)
    (ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.powSum_eq_sum_range.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ a c => powSum a.1 a.2.1 a.2.2.1 a.2.2.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev smoothSignature : Signature where
  Params := (ℕ → ℕ) × List ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def smoothActual : Realization smoothSignature :=
  realize smoothSignature (fun _ a c => smoothSum a.1 a.2.1 a.2.2 c)
    (fun e => nomatch e)

def smoothRejected : Realization smoothSignature :=
  realize smoothSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev smoothArena : Arena where
  signature := smoothSignature
  Law R := ∀ (w : ℕ → ℕ) (ps : List ℕ), (∀ p ∈ ps, p.Prime) → ps.Nodup →
    ∀ {X c : ℕ}, (0 < c ∨ w 0 = 0) → (ps = [] → c ≤ X ∨ w c = 0) →
    (c = 0 ∨ ∀ p ∈ ps, X < c * p ^ 64) →
    R.readout () (w, ps, X) c = ∑ m ∈ factoredMultiples ps.toFinset X c, w m

private theorem smoothRejected_law : ¬smoothArena.Law smoothRejected := by
  intro h
  have hh := h (fun _ => 1) [] (by simp) (by simp)
    (X := 1) (c := 1) (Or.inl (by decide)) (fun _ => Or.inl le_rfl) (by simp)
  have hset : factoredMultiples ∅ 1 1 = {1} := by decide +kernel
  change 0 = ∑ m ∈ factoredMultiples ∅ 1 1, 1 at hh
  rw [hset, sum_singleton] at hh
  exact Nat.zero_ne_one hh

def smoothFamily : Registration smoothArena (type_of% (@smoothSum_eq_sum)) where
  actual := smoothActual
  bridge := Iff.rfl
  variation := ⟨smoothSum_eq_sum, smoothRejected, smoothRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨smoothRejected, ?_, rfl, smoothRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(id, [], 1), 0, 1, ?_⟩
    norm_num [smoothActual, realize, smoothSum]

def smoothAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smoothSum_eq_sum) (Realization smoothSignature)
    ((ℕ → ℕ) → List ℕ → ℕ → ℕ → ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.smoothSum_eq_sum.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration.smoothFamily
  realizationSource := none
  generated := false
  arena := .source ⟨smoothArena⟩
  objectArena := .source ⟨smoothArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source smoothArena ⟨smoothFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize smoothSignature
    (fun _ a c => smoothSum a.1 a.2.1 a.2.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev partitionSignature : Signature where
  Params := (ℕ → ℕ) × ℕ × Finset ℕ × ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def partitionActual : Realization partitionSignature :=
  realize partitionSignature (fun _ a c =>
    ∑ e ∈ range a.2.1,
      ∑ m ∈ factoredMultiples a.2.2.1 a.2.2.2.2 (c * a.2.2.2.1 ^ e), a.1 m)
    (fun e => nomatch e)

def partitionRejected : Realization partitionSignature :=
  realize partitionSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev partitionArena : Arena where
  signature := partitionSignature
  Law R := ∀ (w : ℕ → ℕ) (N : ℕ) {s : Finset ℕ} {p X c : ℕ}, p.Prime → p ∉ s →
    (c = 0 ∨ X < c * p ^ N) →
    R.readout () (w, N, s, p, X) c = ∑ m ∈ factoredMultiples (insert p s) X c, w m

private theorem partitionRejected_law : ¬partitionArena.Law partitionRejected := by
  intro h
  have hh := h (fun _ => 0) 64 (s := ∅) (p := 2) (X := 0) (c := 1)
    Nat.prime_two (by simp) (Or.inr (by decide))
  norm_num [partitionRejected, realize] at hh

set_option maxHeartbeats 2000000 in
/-- Preserve the complete weighted branch sum while checking the source-family obligations. -/
def partitionFamily : Registration partitionArena
    (type_of% (@sum_factoredMultiples_insert)) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨sum_factoredMultiples_insert, partitionRejected, partitionRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨partitionRejected, ?_, ?_, partitionRejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨((fun _ => 1), 64, ∅, 2, 1), 0, 1, ?_⟩
    change (∑ e ∈ range 64, ∑ m ∈ factoredMultiples ∅ 1 (0 * 2 ^ e), 1) ≠
      ∑ e ∈ range 64, ∑ m ∈ factoredMultiples ∅ 1 (1 * 2 ^ e), 1
    have hset0 : factoredMultiples ∅ 1 0 = ∅ := by decide +kernel
    have hz : (∑ e ∈ range 64, ∑ m ∈ factoredMultiples ∅ 1 (0 * 2 ^ e), 1) = 0 := by
      simp only [zero_mul, hset0, sum_empty, sum_const_zero]
    have hone := sum_factoredMultiples_insert (fun _ => 1) 64
      (s := ∅) (p := 2) (X := 1) (c := 1)
      Nat.prime_two (by simp) (Or.inr (by decide))
    have hset1 : factoredMultiples (insert 2 ∅) 1 1 = {1} := by decide +kernel
    rw [hset1, sum_singleton] at hone
    rw [hz, hone]
    exact Nat.zero_ne_one

set_option maxHeartbeats 2000000 in
/-- The source selection includes all parameters of the weighted branch partition. -/
def partitionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_factoredMultiples_insert) (Realization partitionSignature)
    (Finset ℕ → ℕ → ℕ → Finset ℕ) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.sum_factoredMultiples_insert.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration.partitionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨partitionArena⟩
  objectArena := .source ⟨partitionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source partitionArena ⟨partitionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize partitionSignature (fun _ a c =>
    ∑ e ∈ range a.2.1,
      ∑ m ∈ factoredMultiples a.2.2.1 a.2.2.2.2 (c * a.2.2.2.1 ^ e), a.1 m)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
