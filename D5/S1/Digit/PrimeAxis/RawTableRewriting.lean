/- GID: D5/S1/Digit/PrimeAxis/RawTableRewriting
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/RawTableRewriting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A decreasing lexicographic triple terminates raw table carries and makes their legal words finite. -/

import D5.S1.Digit.PrimeAxis.ChargedTableNormalization
import D5.S1.Digit.CarryStepConfluence
import Mathlib.Order.WellFounded
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace D5.S1.Digit.PrimeAxis.RawTableRewriting

open D5.S1.Digit D5.S1.Deficit D5.S0.Conventions
open D5.S1.Digit.PrimeAxis.ChargedTableNormalization

/-- A finitely supported family of prime rows, each with finitely supported natural multiplicities. -/
abbrev RawTable := PrimeAxis →₀ RawDigits

/-- The sum of multiplicities in a row against an index weight. -/
def rowMoment (w : ℕ → ℕ) (r : RawDigits) : ℕ := r.sum fun j n => n * w j

/-- The sum of a row moment over all prime rows. -/
def moment (w : ℕ → ℕ) (t : RawTable) : ℕ := t.sum fun _ r => rowMoment w r

/-- The total Fibonacci weight of the table. -/
def V (t : RawTable) : ℕ := moment wValue t

/-- The total number of tokens in the table, counted with multiplicity. -/
def C (t : RawTable) : ℕ := moment (fun _ => 1) t

/-- The sum of token indices in the table. -/
def I (t : RawTable) : ℕ := moment id t

/-- The sum of squared token indices in the table. -/
def S (t : RawTable) : ℕ := moment (fun j => j^2) t

/-- One directed carry in one prime row, with its charge left unspecified. -/
def Reduces (t u : RawTable) : Prop := ∃ p z, TableStep t u p z

/-- The finite set of indices whose Fibonacci weights do not exceed the given value. -/
def weightIndices (v : ℕ) : Finset ℕ :=
  (Finset.range (v+1)).filter fun j => wValue j ≤ v

/-- The token count, index sum, and bounded complementary square sum. -/
def triple (v J : ℕ) (t : RawTable) : ℕ × ℕ × ℕ := (C t, I t, v*J^2-S t)

/-- The strict lexicographic order on three natural numbers. -/
def TripleLt : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

/-- A finite table sequence with one directed carry between each pair of consecutive states. -/
structure FiniteExecution where
  /-- The number of steps. -/
  length : ℕ
  /-- The tables at successive times. -/
  states : Fin (length+1) → RawTable
  /-- Every consecutive pair is related by a directed carry. -/
  legal : ∀ i : Fin length,
    Reduces (states ⟨i.val, by omega⟩) (states ⟨i.val+1, by omega⟩)

/-- The final table of a finite execution. -/
def FiniteExecution.last (e : FiniteExecution) : RawTable := e.states ⟨e.length, by omega⟩

/-- A table from which no directed table carry is possible. -/
def Irreducible (t : RawTable) : Prop := ∀ u, ¬ Reduces t u

/-- A finite or infinite sequence of actual directed table carries. -/
abbrev Execution := FiniteExecution ⊕ {f : ℕ → RawTable // ∀ n, Reduces (f n) (f (n+1))}

/-- A sequence is maximal when it is infinite or its final table allows no further carry. -/
def Maximal : Execution → Prop
  | .inl e => Irreducible e.last
  | .inr _ => True

/-- The four directed row carries, with a natural index for either variable rule. -/
inductive RuleKind where
  /-- Combine tokens at adjacent indices. -/
  | adjacent : ℕ → RuleKind
  /-- Carry two tokens at index zero. -/
  | doubleZero : RuleKind
  /-- Split two tokens at index one. -/
  | doubleOne : RuleKind
  /-- Split two tokens at an index of at least two. -/
  | doubleSucc : ℕ → RuleKind
  deriving DecidableEq

/-- A directed row carry together with its selected prime. -/
abbrev Rule := PrimeAxis × RuleKind

/-- The multiplicities required to perform a directed row carry. -/
noncomputable def lhs : RuleKind → RawDigits
  | .adjacent j => Finsupp.single j 1 + Finsupp.single (j+1) 1
  | .doubleZero => Finsupp.single 0 2
  | .doubleOne => Finsupp.single 1 2
  | .doubleSucc j => Finsupp.single (j+2) 2

/-- The multiplicities produced by a directed row carry. -/
noncomputable def rhs : RuleKind → RawDigits
  | .adjacent j => Finsupp.single (j+2) 1
  | .doubleZero => Finsupp.single 1 1
  | .doubleOne => Finsupp.single 0 1 + Finsupp.single 2 1
  | .doubleSucc j => Finsupp.single j 1 + Finsupp.single (j+3) 1

/-- The signed charge of a directed row carry. -/
def ruleCharge : RuleKind → ℤ
  | .adjacent _ => 0
  | .doubleZero => 1
  | .doubleOne => -1
  | .doubleSucc _ => 0

/-- A rule is enabled when its required multiplicities are present in the selected row. -/
def Enabled (t : RawTable) (a : Rule) : Prop := lhs a.2 ≤ t a.1

/-- Subtract the required multiplicities, add the produced ones, and preserve every other row. -/
noncomputable def applyRule (t : RawTable) (a : Rule) : RawTable :=
  t.update a.1 (t a.1 - lhs a.2 + rhs a.2)

/-- A rule word is legal when each rule is enabled after all its predecessors have been applied. -/
def LegalWord : RawTable → List Rule → Prop
  | _, [] => True
  | t, a::w => Enabled t a ∧ LegalWord (applyRule t a) w

/-- The tables with the same Fibonacci value at every prime as the given table. -/
def rowFiber (t : RawTable) : Set RawTable :=
  {u | ∀ p, rawValue (u p) = rawValue (t p)}

/-- An index required by the left side of a row carry. -/
def pivot : RuleKind → ℕ
  | .adjacent j => j
  | .doubleZero => 0
  | .doubleOne => 1
  | .doubleSucc j => j+2

/-- A finite set containing every rule enabled at the given table. -/
def ruleCandidates (t : RawTable) : Finset Rule :=
  t.support.product
    (((Finset.range (V t+1)).image RuleKind.adjacent ∪
      (Finset.range (V t+1)).image RuleKind.doubleSucc) ∪
      {RuleKind.doubleZero, RuleKind.doubleOne})

/-- The coefficientwise bound with the given prime support and uniform index and multiplicity bounds. -/
noncomputable def box (t : RawTable) : RawTable :=
  ∑ p ∈ t.support, Finsupp.single p
    (∑ j ∈ Finset.range (V t+1), Finsupp.single j (V t))

/-- The exact changes in token count, index sum, and square sum for the four directed carries. -/
def RuleEffect (t u : RawTable) : RuleKind → Prop
  | .adjacent _ => C u + 1 = C t
  | .doubleZero => C u + 1 = C t
  | .doubleOne => C u = C t ∧ I u = I t ∧ S u = S t + 2
  | .doubleSucc _ => C u = C t ∧ I u + 1 = I t

set_option maxHeartbeats 1600000 in
/-- Every directed table execution terminates. For positive initial value, the largest
admissible Fibonacci index bounds every reachable token and makes the triple
`(C, I, V * J^2 - S)` strictly decrease. Maximal executions end at the unique
rowwise canonical table, with at most one token per index and no adjacent tokens. -/
theorem table_rewriting_terminates :
    WellFounded (fun u t : RawTable => Reduces t u) ∧
    (¬ ∃ f : ℕ → RawTable, ∀ n, Reduces (f n) (f (n+1))) ∧
    WellFounded TripleLt ∧
    (∀ t : RawTable, C t ≤ V t) ∧
    (∀ t : RawTable, V t = 0 ↔ t = 0 ∧ ∀ u p z, ¬ TableStep t u p z) ∧
    (∀ t : RawTable, 0 < V t →
      ∃ J : ℕ, wValue J ≤ V t ∧
        (∀ j, wValue j ≤ V t → j ≤ J) ∧
        ∀ u charge, TablePath t u charge →
          (∀ p j, u p j ≠ 0 → wValue j ≤ V t ∧ j ≤ J) ∧
          S u ≤ V t * J^2 ∧
          ∀ v p z, TableStep u v p z →
            S v ≤ V t * J^2 ∧
            TripleLt (triple (V t) J v) (triple (V t) J u)) ∧
    (∀ t u p z, TableStep t u p z →
      ∃ a : Rule, a.1 = p ∧ Enabled t a ∧ applyRule t a = u ∧ RuleEffect t u a.2) ∧
    (∀ e : Execution, Maximal e →
      ∃ finite : FiniteExecution, e = .inl finite ∧ Irreducible finite.last) ∧
    (∀ t : RawTable, Irreducible t ↔ ∀ p, CanonicalRaw (t p)) ∧
    (∀ t u c, TablePath t u c → Irreducible u →
      (∀ p j, u p j ≤ 1) ∧ (∀ p j, u p j = 1 → u p (j+1) = 0) ∧
      u = rowNormalize t ∧
      ∀ v d, TablePath t v d → Irreducible v → v = u) := by
  classical
  have rowMoment_add (w : ℕ → ℕ) (r s : RawDigits) :
      rowMoment w (r+s) = rowMoment w r + rowMoment w s := by
    classical
    simp [rowMoment, Finsupp.sum_add_index, add_mul]
  have moment_balance (w : ℕ → ℕ) {t u : RawTable} {p : PrimeAxis} {z : ℤ}
      (h : TableStep t u p z) :
      moment w u + rowMoment w (t p) = moment w t + rowMoment w (u p) := by
    classical
    have hu : u = t.update p (u p) := by
      ext q j
      by_cases hq : q = p
      · subst q; simp
      · simp [Finsupp.update_apply, hq, h.2 q hq]
    unfold moment
    conv_lhs => rw [hu]
    exact Finsupp.sum_update_add t p (u p) (fun _ r => rowMoment w r)
      (by simp [rowMoment]) (fun _ a b => rowMoment_add w a b)
  have weight_pos (j : ℕ) : 0 < wValue j := Nat.fib_pos.mpr (by omega)
  have coefficient_value_le (t : RawTable) (p : PrimeAxis) (j : ℕ) :
      t p j * wValue j ≤ V t := by
    have h₁ := Finsupp.single_le_sum (t p)
      (g := fun j n => n * wValue j) (fun _ _ => Nat.zero_le _) j
    have h₂ := Finsupp.single_eval_le_sum t
      (g := fun r => rowMoment wValue r) (by simp [rowMoment]) (fun _ => Nat.zero_le _) p
    simpa [rowMoment, V, moment] using
      (show t p j * wValue j ≤ (t p).sum (fun j n => n * wValue j) from by
        simpa using h₁).trans h₂
  have token_bound (t : RawTable) : C t ≤ V t := by
    apply Finsupp.sum_le_sum
    intro p hp
    apply Finsupp.sum_le_sum
    intro j hj
    simpa using Nat.mul_le_mul_left (t p j) (weight_pos j)
  have value_zero_iff (t : RawTable) : V t = 0 ↔ t = 0 := by
    constructor
    · intro ht
      ext p j
      have h := coefficient_value_le t p j
      have hw := weight_pos j
      rw [ht] at h
      simpa using (show t p j = 0 by nlinarith)
    · rintro rfl
      simp [V, moment]
  have charged_source_ne_zero {a b : RawDigits} {z : ℤ}
      (h : ChargedCarryStep a b z) : a ≠ 0 := by
    cases h with
    | adjacent rest j =>
        intro he
        have := congrArg (fun r : RawDigits => r j) he
        simp at this
    | double_zero rest =>
        intro he
        have := congrArg (fun r : RawDigits => r 0) he
        simp at this
    | double_one rest =>
        intro he
        have := congrArg (fun r : RawDigits => r 1) he
        simp at this
    | double_succ rest j =>
        intro he
        have := congrArg (fun r : RawDigits => r (j+2)) he
        simp at this
  have zero_table_clause (t : RawTable) :
      V t = 0 ↔ t = 0 ∧ ∀ u p z, ¬ TableStep t u p z := by
    constructor
    · intro ht
      have hz := (value_zero_iff t).mp ht
      refine ⟨hz, ?_⟩
      intro u p z h
      exact charged_source_ne_zero h.1 (by simp [hz])
    · intro ht
      exact (value_zero_iff t).mpr ht.1
  have path_value (t u : RawTable) (charge : PrimeAxis →₀ ℤ)
      (h : TablePath t u charge) : V t = V u := by
    classical
    have hrow (p : PrimeAxis) : rawValue (t p) = rawValue (u p) :=
      rawValue_reflTransGen (tablePath_project h p).toReflTransGen
    change t.sum (fun _ r => rawValue r) = u.sum (fun _ r => rawValue r)
    rw [Finsupp.sum_of_support_subset t Finset.subset_union_left _
        (show ∀ p ∈ t.support ∪ u.support, rawValue 0 = 0 from by simp [rawValue]),
      Finsupp.sum_of_support_subset u Finset.subset_union_right _
        (show ∀ p ∈ t.support ∪ u.support, rawValue 0 = 0 from by simp [rawValue])]
    exact Finset.sum_congr rfl (fun p _ => hrow p)
  have mem_weightIndices (j v : ℕ) : j ∈ weightIndices v ↔ wValue j ≤ v := by
    have hi : j ≤ wValue j := Nat.fib_add_two_strictMono.id_le j
    simp only [weightIndices, Finset.mem_filter, Finset.mem_range]
    omega
  have reachable_index_bound (t : RawTable) (ht : 0 < V t) :
      ∃ J : ℕ, wValue J ≤ V t ∧
        (∀ j, wValue j ≤ V t → j ≤ J) ∧
        ∀ u charge, TablePath t u charge → ∀ p j,
          u p j ≠ 0 → wValue j ≤ V t ∧ j ≤ J := by
    have hn : (weightIndices (V t)).Nonempty := by
      refine ⟨0, (mem_weightIndices 0 (V t)).mpr ?_⟩
      simpa only [wValue_zero] using (show 1 ≤ V t by omega)
    let J := (weightIndices (V t)).max' hn
    have hJ : wValue J ≤ V t :=
      (mem_weightIndices J (V t)).mp (Finset.max'_mem _ hn)
    have hmax (j : ℕ) (hj : wValue j ≤ V t) : j ≤ J :=
      Finset.le_max' _ _ ((mem_weightIndices j (V t)).mpr hj)
    refine ⟨J, hJ, hmax, ?_⟩
    intro u charge h p j hj
    have hv := path_value t u charge h
    have hc := coefficient_value_le u p j
    have hw : wValue j ≤ V t := by
      have hm := Nat.mul_le_mul_right (wValue j) (show 1 ≤ u p j by omega)
      simp only [one_mul] at hm
      omega
    exact ⟨hw, hmax j hw⟩
  have square_bound (t : RawTable) (J : ℕ)
      (hb : ∀ p j, t p j ≠ 0 → j ≤ J) : S t ≤ V t * J^2 := by
    calc
      S t = ∑ p ∈ t.support, ∑ j ∈ (t p).support, t p j * j^2 := rfl
      _ ≤ ∑ p ∈ t.support, ∑ j ∈ (t p).support, t p j * J^2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hb p j (Finsupp.mem_support_iff.mp hj)) 2)
      _ = C t * J^2 := by
        simp [C, moment, rowMoment, Finsupp.sum, Finset.sum_mul]
      _ ≤ V t * J^2 := Nat.mul_le_mul_right _ (token_bound t)
  have triple_step {t u : RawTable} {p : PrimeAxis} {z : ℤ} (v J : ℕ)
      (h : TableStep t u p z) (hs : S u ≤ v*J^2) :
      TripleLt (triple v J u) (triple v J t) := by
    have hc := moment_balance (fun _ => 1) h
    have hi := moment_balance id h
    have hq := moment_balance (fun j => j^2) h
    change C u + _ = C t + _ at hc
    change I u + _ = I t + _ at hi
    change S u + _ = S t + _ at hq
    rcases h with ⟨hstep, hrest⟩
    generalize ha : t p = a at hstep hc hi hq
    generalize hb : u p = b at hstep hc hi hq
    cases hstep with
    | adjacent rest j =>
        simp [rowMoment, Finsupp.sum_add_index] at hc
        exact Prod.Lex.left _ _ (by omega)
    | double_zero rest =>
        simp [rowMoment, Finsupp.sum_add_index] at hc
        exact Prod.Lex.left _ _ (by omega)
    | double_one rest =>
        simp [rowMoment, Finsupp.sum_add_index, add_mul] at hc hi hq
        have hC : C u = C t := by omega
        have hI : I u = I t := by omega
        unfold triple TripleLt
        rw [hC, hI]
        exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    | double_succ rest j =>
        simp [rowMoment, Finsupp.sum_add_index, add_mul] at hc hi
        have hC : C u = C t := by omega
        unfold triple TripleLt
        rw [hC]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  have exact_triple_clause (t : RawTable) (ht : 0 < V t) :
      ∃ J : ℕ, wValue J ≤ V t ∧
        (∀ j, wValue j ≤ V t → j ≤ J) ∧
        ∀ u charge, TablePath t u charge →
          S u ≤ V t * J^2 ∧
          ∀ v p z, TableStep u v p z →
            S v ≤ V t * J^2 ∧
            TripleLt (triple (V t) J v) (triple (V t) J u) := by
    obtain ⟨J, hJ, hmax, hbound⟩ := reachable_index_bound t ht
    refine ⟨J, hJ, hmax, ?_⟩
    intro u charge hu
    have hs : S u ≤ V t * J^2 := by
      rw [path_value t u charge hu]
      exact square_bound u J (fun p j hj => (hbound u charge hu p j hj).2)
    refine ⟨hs, ?_⟩
    intro v p z huv
    have hv := TablePath.tail hu huv
    have hsv : S v ≤ V t * J^2 := by
      rw [path_value t v _ hv]
      exact square_bound v J (fun q j hj => (hbound v _ hv q j hj).2)
    exact ⟨hsv, triple_step (V t) J huv hsv⟩
  have triple_wellFounded : WellFounded TripleLt :=
    Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  have no_infinite_table_path :
      ¬ ∃ f : ℕ → RawTable, ∀ n, Reduces (f n) (f (n+1)) := by
    rintro ⟨f, h⟩
    by_cases hz : V (f 0) = 0
    · obtain ⟨p, z, hs⟩ := h 0
      exact (zero_table_clause (f 0)).mp hz |>.2 (f 1) p z hs
    · have ht : 0 < V (f 0) := Nat.pos_of_ne_zero hz
      obtain ⟨J, _, hmax, _⟩ := reachable_index_bound (f 0) ht
      have hadj (n : ℕ) : V (f n) = V (f (n+1)) := by
        obtain ⟨p, z, hs⟩ := h n
        exact path_value _ _ _ (TablePath.tail (TablePath.refl _) hs)
      have hv (n : ℕ) : V (f 0) = V (f n) :=
        Nat.rel_of_forall_rel_succ_of_le Eq hadj (Nat.zero_le n)
      have hbound (n : ℕ) : S (f n) ≤ V (f 0) * J^2 := by
        rw [hv n]
        apply square_bound (f n) J
        intro p j hj
        apply hmax j
        have hc := coefficient_value_le (f n) p j
        have hm := Nat.mul_le_mul_right (wValue j) (Nat.pos_of_ne_zero hj)
        have he := hv n
        omega
      apply (wellFounded_iff_isEmpty_descending_chain.mp triple_wellFounded).false
      refine ⟨fun n => triple (V (f 0)) J (f n), ?_⟩
      intro n
      obtain ⟨p, z, hs⟩ := h n
      exact triple_step (V (f 0)) J hs (hbound (n+1))
  have table_strong_termination : WellFounded (fun u t : RawTable => Reduces t u) := by
    apply wellFounded_iff_isEmpty_descending_chain.mpr
    exact ⟨fun h => no_infinite_table_path ⟨h.1, h.2⟩⟩
  have maximal_execution_clause (e : Execution) (he : Maximal e) :
      ∃ finite : FiniteExecution, e = .inl finite ∧ Irreducible finite.last := by
    cases e with
    | inl finite => exact ⟨finite, rfl, he⟩
    | inr infinite => exact False.elim (no_infinite_table_path ⟨infinite.1, infinite.2⟩)
  have canonical_no_charged_step {r s : RawDigits} {z : ℤ}
      (hr : CanonicalRaw r) (h : ChargedCarryStep r s z) : False := by
    cases h with
    | adjacent rest j =>
        have hb := hr.1 j
        have hn := hr.2 j
        simp at hb hn
        have h0 : rest j = 0 := by omega
        simp [h0] at hn
    | double_zero rest =>
        have hb := hr.1 0
        simp at hb
    | double_one rest =>
        have hb := hr.1 1
        simp at hb
    | double_succ rest j =>
        have hb := hr.1 (j+2)
        simp at hb
  have irreducible_iff_canonical (t : RawTable) :
      Irreducible t ↔ ∀ p, CanonicalRaw (t p) := by
    constructor
    · intro ht p
      by_contra hn
      have lift {a b : RawDigits} (h : CarryStep a b) : ∃ z, ChargedCarryStep a b z := by
        cases h with
        | adjacent rest j => exact ⟨0, ChargedCarryStep.adjacent rest j⟩
        | double_zero rest => exact ⟨1, ChargedCarryStep.double_zero rest⟩
        | double_one rest => exact ⟨-1, ChargedCarryStep.double_one rest⟩
        | double_succ rest j => exact ⟨0, ChargedCarryStep.double_succ rest j⟩
      obtain ⟨z, hz⟩ := lift (carryPass_step hn)
      apply ht (t.update p (carryPass (t p)))
      refine ⟨p, z, ?_, ?_⟩
      · simpa using hz
      · intro q hq
        simp [Finsupp.update_apply, hq]
    · intro ht u hu
      obtain ⟨p, z, hs⟩ := hu
      exact canonical_no_charged_step (ht p) hs.1
  have irreducible_unique_clause (t u : RawTable) (c : PrimeAxis →₀ ℤ)
      (hu : TablePath t u c) (hi : Irreducible u) :
      (∀ p j, u p j ≤ 1) ∧ (∀ p j, u p j = 1 → u p (j+1) = 0) ∧
      u = rowNormalize t ∧
      ∀ v d, TablePath t v d → Irreducible v → v = u := by
    have hcan := (irreducible_iff_canonical u).mp hi
    have he : u = rowNormalize t := by
      ext p j
      have hp := reachable_canonical_eq_normalize
        (tablePath_project hu p).toReflTransGen (hcan p)
      exact congrArg (fun r : RawDigits => r j) hp
    refine ⟨fun p => (hcan p).1, fun p => (hcan p).2, he, ?_⟩
    intro v d hv hvi
    rw [he]
    ext p j
    have hp := reachable_canonical_eq_normalize
      (tablePath_project hv p).toReflTransGen ((irreducible_iff_canonical v).mp hvi p)
    exact congrArg (fun r : RawDigits => r j) hp
  have rule_sound {t : RawTable} {a : Rule} (ha : Enabled t a) :
      TableStep t (applyRule t a) a.1 (ruleCharge a.2) := by
    classical
    obtain ⟨p, k⟩ := a
    have hr : t p - lhs k + lhs k = t p := tsub_add_cancel_of_le ha
    have hc : ChargedCarryStep (t p) (t p - lhs k + rhs k) (ruleCharge k) := by
      cases k with
      | adjacent j =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.adjacent (t p - lhs (.adjacent j)) j
      | doubleZero =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, hr] using
            ChargedCarryStep.double_zero (t p - lhs .doubleZero)
      | doubleOne =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.double_one (t p - lhs .doubleOne)
      | doubleSucc j =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.double_succ (t p - lhs (.doubleSucc j)) j
    refine ⟨?_, ?_⟩
    · simpa [applyRule] using hc
    · intro q hq
      simp [applyRule, Finsupp.update_apply, hq]
  have rule_effects (t : RawTable) (a : Rule) (ha : Enabled t a) :
      RuleEffect t (applyRule t a) a.2 := by
    classical
    obtain ⟨p,k⟩ := a
    have h := rule_sound ha
    have hc := moment_balance (fun _ => 1) h
    have hi := moment_balance id h
    have hq := moment_balance (fun j => j^2) h
    change C (applyRule t (p,k)) + _ = C t + _ at hc
    change I (applyRule t (p,k)) + _ = I t + _ at hi
    change S (applyRule t (p,k)) + _ = S t + _ at hq
    let rest := t p - lhs k
    have hr : t p = rest + lhs k := (tsub_add_cancel_of_le ha).symm
    have hu : (applyRule t (p,k)) p = rest + rhs k := by simp [applyRule, rest]
    rw [hr, hu] at hc hi hq
    cases k <;>
      simp [lhs, rhs, rowMoment, Finsupp.sum_add_index, add_mul] at hc hi hq <;>
      simp only [RuleEffect] <;> omega
  have effects : ∀ t u p z, TableStep t u p z →
      ∃ a : Rule, a.1 = p ∧ Enabled t a ∧ applyRule t a = u ∧ RuleEffect t u a.2 := by
    intro u v p z h
    -- The rule-choice equality retains the selected row; prove it without erasing p.
    have hd : ∃ k rest, u p = rest + lhs k ∧ v p = rest + rhs k := by
      have hc := h.1
      generalize he : u p = x at hc
      generalize hf : v p = y at hc
      cases hc with
      | adjacent rest j => exact ⟨.adjacent j, rest, by simp [lhs, add_assoc], by simp [rhs]⟩
      | double_zero rest => exact ⟨.doubleZero, rest, rfl, rfl⟩
      | double_one rest => exact ⟨.doubleOne, rest, rfl, by simp [rhs, add_assoc]⟩
      | double_succ rest j => exact ⟨.doubleSucc j, rest, rfl, by simp [rhs, add_assoc]⟩
    obtain ⟨k, rest, he, hf⟩ := hd
    have hen : Enabled u (p,k) := by
      change lhs k ≤ u p
      rw [he]
      intro j
      simp only [Finsupp.add_apply]
      omega
    have hout : applyRule u (p,k) = v := by
      ext q j
      by_cases hq : q = p
      · subst q
        simpa [applyRule, he] using congrArg (fun r : RawDigits => r j) hf.symm
      · simp [applyRule, Finsupp.update_apply, hq, h.2 q hq]
    exact ⟨(p,k), rfl, hen, hout, hout ▸ rule_effects u (p,k) hen⟩
  refine ⟨table_strong_termination, no_infinite_table_path, triple_wellFounded,
    token_bound, zero_table_clause, ?_, effects, maximal_execution_clause,
    irreducible_iff_canonical, irreducible_unique_clause⟩
  intro t ht
  obtain ⟨J, hJ, hmax, hb⟩ := reachable_index_bound t ht
  refine ⟨J, hJ, hmax, ?_⟩
  intro u charge hu
  have hs : S u ≤ V t * J^2 := by
    rw [path_value t u charge hu]
    exact square_bound u J (fun p j hj => (hb u charge hu p j hj).2)
  refine ⟨hb u charge hu, hs, ?_⟩
  intro v p z huv
  have hv := TablePath.tail hu huv
  have hsv : S v ≤ V t * J^2 := by
    rw [path_value t v _ hv]
    exact square_bound v J (fun p j hj => (hb v _ hv p j hj).2)
  exact ⟨hsv, triple_step (V t) J huv hsv⟩

set_option maxHeartbeats 1600000 in
/-- At every raw table the row-value fiber, enabled rules, and all legal finite rule words
are finite. The labelled rules describe exactly the directed table steps, including their
selected prime and signed charge. -/
theorem finite_legal_words (t : RawTable) :
    (rowFiber t).Finite ∧ {a : Rule | Enabled t a}.Finite ∧
    {w : List Rule | LegalWord t w}.Finite ∧
    (∀ u p z, TableStep t u p z ↔
      ∃ k : RuleKind, Enabled t (p,k) ∧ applyRule t (p,k) = u ∧ ruleCharge k = z) := by
  classical
  have weight_pos (j : ℕ) : 0 < wValue j := Nat.fib_pos.mpr (by omega)
  have coefficient_value_le (t : RawTable) (p : PrimeAxis) (j : ℕ) :
      t p j * wValue j ≤ V t := by
    have h₁ := Finsupp.single_le_sum (t p)
      (g := fun j n => n * wValue j) (fun _ _ => Nat.zero_le _) j
    have h₂ := Finsupp.single_eval_le_sum t
      (g := fun r => rowMoment wValue r) (by simp [rowMoment]) (fun _ => Nat.zero_le _) p
    simpa [rowMoment, V, moment] using
      (show t p j * wValue j ≤ (t p).sum (fun j n => n * wValue j) from by
        simpa using h₁).trans h₂
  have rule_sound {t : RawTable} {a : Rule} (ha : Enabled t a) :
      TableStep t (applyRule t a) a.1 (ruleCharge a.2) := by
    classical
    obtain ⟨p, k⟩ := a
    have hr : t p - lhs k + lhs k = t p := tsub_add_cancel_of_le ha
    have hc : ChargedCarryStep (t p) (t p - lhs k + rhs k) (ruleCharge k) := by
      cases k with
      | adjacent j =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.adjacent (t p - lhs (.adjacent j)) j
      | doubleZero =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, hr] using
            ChargedCarryStep.double_zero (t p - lhs .doubleZero)
      | doubleOne =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.double_one (t p - lhs .doubleOne)
      | doubleSucc j =>
          simp only [lhs] at hr
          simpa only [lhs, rhs, ruleCharge, add_assoc, hr] using
            ChargedCarryStep.double_succ (t p - lhs (.doubleSucc j)) j
    refine ⟨?_, ?_⟩
    · simpa [applyRule] using hc
    · intro q hq
      simp [applyRule, Finsupp.update_apply, hq]
  have enabled_bounds {t : RawTable} {a : Rule} (ha : Enabled t a) :
      a.1 ∈ t.support ∧ pivot a.2 ≤ V t := by
    have hl : 0 < lhs a.2 (pivot a.2) := by
      rcases a with ⟨p, k⟩
      cases k <;> simp [lhs, pivot]
    have hp : 0 < t a.1 (pivot a.2) := lt_of_lt_of_le hl (ha _)
    have hr : t a.1 ≠ 0 := by
      intro hzero
      simp [hzero] at hp
    have hi : pivot a.2 ≤ wValue (pivot a.2) := Nat.fib_add_two_strictMono.id_le _
    have hv := coefficient_value_le t a.1 (pivot a.2)
    have hw := Nat.mul_le_mul_right (wValue (pivot a.2)) hp
    exact ⟨Finsupp.mem_support_iff.mpr hr, by omega⟩
  have enabled_finite (t : RawTable) : {a : Rule | Enabled t a}.Finite := by
    apply (ruleCandidates t).finite_toSet.subset
    intro a ha
    obtain ⟨hp, hi⟩ := enabled_bounds ha
    obtain ⟨p, k⟩ := a
    cases k with
    | adjacent j =>
        simp only [pivot] at hi
        simp [ruleCandidates, hp, show j ≤ V t by omega]
    | doubleZero => simp [ruleCandidates, hp]
    | doubleOne => simp [ruleCandidates, hp]
    | doubleSucc j =>
        simp only [pivot] at hi
        simp [ruleCandidates, hp, show j ≤ V t by omega]
  have fiber_finite (t : RawTable) : (rowFiber t).Finite := by
    classical
    apply (Set.finite_Iic (box t)).subset
    intro u hu
    have hval : V u = V t := by
      change u.sum (fun _ r => rawValue r) = t.sum (fun _ r => rawValue r)
      exact Finsupp.sum_congr_of_eq_on_union (fun p _ => hu p)
        (by simp [rawValue]) (by simp [rawValue])
    change u ≤ box t
    intro p j
    by_cases hz : u p j = 0
    · simp [hz]
    have hw := weight_pos j
    have hn : 0 < u p j := Nat.pos_of_ne_zero hz
    have hin := Finsupp.single_le_sum (u p)
      (g := fun k n => n*wValue k) (fun _ _ => Nat.zero_le _) j
    have hin' : u p j * wValue j ≤ rawValue (u p) := by simpa [rawValue] using hin
    have hp : p ∈ t.support := by
      apply Finsupp.mem_support_iff.mpr
      intro hp0
      have he := hu p
      rw [hp0] at he
      change rawValue (u p) = 0 at he
      have hpos := Nat.mul_pos hn hw
      omega
    have htotal := coefficient_value_le u p j
    rw [hval] at htotal
    have hcoef : u p j ≤ V t := by
      have := Nat.mul_le_mul_left (u p j) hw
      omega
    have hj : j < V t+1 := by
      have := Nat.mul_le_mul_right (wValue j) hn
      have hi : j ≤ wValue j := Nat.fib_add_two_strictMono.id_le j
      omega
    simpa [box, Finsupp.finsetSum_apply, Finsupp.single_apply, hp, hj] using hcoef
  have charged_actual_step_iff {t u : RawTable} {p : PrimeAxis} {z : ℤ} :
      TableStep t u p z ↔
        ∃ k : RuleKind, Enabled t (p,k) ∧ applyRule t (p,k) = u ∧ ruleCharge k = z := by
    constructor
    · intro h
      have hd : ∃ k rest, t p = rest + lhs k ∧ u p = rest + rhs k ∧ ruleCharge k = z := by
        have hc := h.1
        generalize he : t p = x at hc
        generalize hf : u p = y at hc
        cases hc with
        | adjacent rest j =>
            exact ⟨.adjacent j, rest, by simp [lhs, add_assoc], by simp [rhs], rfl⟩
        | double_zero rest => exact ⟨.doubleZero, rest, rfl, rfl, rfl⟩
        | double_one rest => exact ⟨.doubleOne, rest, rfl, by simp [rhs, add_assoc], rfl⟩
        | double_succ rest j =>
            exact ⟨.doubleSucc j, rest, rfl, by simp [rhs, add_assoc], rfl⟩
      obtain ⟨k, rest, he, hf, hz⟩ := hd
      refine ⟨k, ?_, ?_, hz⟩
      · change lhs k ≤ t p
        rw [he]
        intro j
        simp only [Finsupp.add_apply]
        omega
      · ext q j
        by_cases hq : q = p
        · subst q
          simpa [applyRule, he] using congrArg (fun r : RawDigits => r j) hf.symm
        · simp [applyRule, Finsupp.update_apply, hq, h.2 q hq]
    · rintro ⟨k, hk, rfl, rfl⟩
      exact rule_sound hk
  have finite_legal_words (t : RawTable) : {w : List Rule | LegalWord t w}.Finite := by
    classical
    induction t using table_rewriting_terminates.1.induction with
    | h t ih =>
        have ht : ∀ a ∈ {a : Rule | Enabled t a},
            {w : List Rule | LegalWord (applyRule t a) w}.Finite := by
          intro a ha
          exact ih (applyRule t a) ⟨a.1, ruleCharge a.2, rule_sound ha⟩
        have hall := (Set.finite_singleton ([] : List Rule)).union
          ((enabled_finite t).biUnion fun a ha => (ht a ha).image (List.cons a))
        apply hall.subset
        intro w hw
        cases w with
        | nil => exact Or.inl rfl
        | cons a w =>
            exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
              ⟨hw.1, ⟨w, hw.2, rfl⟩⟩⟩)
  exact ⟨fiber_finite t, enabled_finite t, finite_legal_words t,
    fun _ _ _ => charged_actual_step_iff⟩

end D5.S1.Digit.PrimeAxis.RawTableRewriting
