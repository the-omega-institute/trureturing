/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.row_bijective,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.transfer_table,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.values_zero,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.values_step,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_identity,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_step,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_step_two,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_terminal,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_one_terminal
   digest: The literal rooted binary king-strip counts satisfy Hardin's seventh-order recurrence. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Rooted three-column binary rectangles and their boundary transfer. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
open scoped BigOperators

/-- Rooted binary rectangles with the prescribed number of unequal king neighbours. -/
def Admissible {n : ℕ} (A : Fin n × Fin 3 → Fin 2) : Prop :=
  (∀ i : Fin n, i.val = 0 → A (i, 0) = 0) ∧
  ∀ p : Fin n × Fin 3,
    (Finset.univ.filter (fun q : Fin n × Fin 3 =>
      q ≠ p ∧ q.1.val ≤ p.1.val + 1 ∧ p.1.val ≤ q.1.val + 1 ∧
      q.2.val ≤ p.2.val + 1 ∧ p.2.val ≤ q.2.val + 1 ∧ A q ≠ A p)).card ∈
        ({0, 1, 2, 5} : Finset ℕ)

/-- The integer cardinality of the original labelled arrays. -/
noncomputable def a (n : ℕ) : ℤ :=
  (Nat.card {A : Fin n × Fin 3 → Fin 2 // Admissible A} : ℤ)

/-- The empirical formula of OEIS A303956, with its original strict threshold. -/
def claim : Prop := ∀ n : ℕ, 8 < n →
  a n = a (n-1) + 2*a (n-2) + 3*a (n-3) + 2*a (n-4) -
    2*a (n-5) - 6*a (n-6) - 4*a (n-7)

private def row : Fin 8 → Fin 3 → Fin 2 :=
  ![![0,0,0], ![1,0,0], ![0,1,0], ![1,1,0],
    ![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]]

private def across (b c : Fin 3 → Fin 2) (j : Fin 3) : ℕ :=
  ∑ l : Fin 3, if l.val ≤ j.val+1 ∧ j.val ≤ l.val+1 ∧ c l ≠ b j then 1 else 0

private def horizontal (b : Fin 3 → Fin 2) (j : Fin 3) : ℕ :=
  ∑ l : Fin 3, if l ≠ j ∧ l.val ≤ j.val+1 ∧ j.val ≤ l.val+1 ∧ b l ≠ b j then 1 else 0

private def optional (b : Fin 3 → Fin 2) (c : Option (Fin 3 → Fin 2)) (j : Fin 3) : ℕ :=
  match c with | none => 0 | some c => across b c j

private def Local (a : Option (Fin 3 → Fin 2)) (b : Fin 3 → Fin 2)
    (c : Option (Fin 3 → Fin 2)) : Prop :=
  ∀ j, horizontal b j + optional b a j + optional b c j ∈ ({0,1,2,5} : Finset ℕ)

private def L (a : Option (Fin 8)) (b : Fin 8) (c : Option (Fin 8)) : Prop :=
  Local (a.map row) (row b) (c.map row)

private instance (a : Option (Fin 8)) (b : Fin 8) (c : Option (Fin 8)) : Decidable (L a b c) :=
  inferInstanceAs (Decidable (∀ j, _))

private def T : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℤ :=
  fun s t => if t.1 = s.2 ∧ L (some s.1) s.2 (some t.2) then 1 else 0

private def v : (Fin 8 × Fin 8) → ℤ :=
  fun s => if row s.1 0 = 0 ∧ L none s.1 (some s.2) then 1 else 0

private def t : (Fin 8 × Fin 8) → ℤ :=
  fun s => if L (some s.1) s.2 none then 1 else 0

private def headRow {n : ℕ} (f : Fin n → Fin 3 → Fin 2) : Option (Fin 3 → Fin 2) :=
  if h : 0 < n then some (f ⟨0,h⟩) else none

private def aboveRow {n : ℕ} (a : Option (Fin 3 → Fin 2))
    (f : Fin n → Fin 3 → Fin 2) (i : Fin n) : Option (Fin 3 → Fin 2) :=
  if h : i.val = 0 then a else some (f ⟨i.val-1, by omega⟩)

private def belowRow {n : ℕ} (f : Fin n → Fin 3 → Fin 2) (i : Fin n) : Option (Fin 3 → Fin 2) :=
  if h : i.val+1 < n then some (f ⟨i.val+1,h⟩) else none

private def AllLocal {n : ℕ} (a : Option (Fin 3 → Fin 2))
    (f : Fin n → Fin 3 → Fin 2) : Prop :=
  ∀ i, Local (aboveRow a f i) (f i) (belowRow f i)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem row_bijective : Function.Bijective row := by decide +kernel

private noncomputable def rowEquiv : Fin 8 ≃ (Fin 3 → Fin 2) :=
  Equiv.ofBijective row row_bijective

private theorem allLocal_cons {n : ℕ} (a : Option (Fin 3 → Fin 2))
    (b : Fin 3 → Fin 2) (f : Fin n → Fin 3 → Fin 2) :
    AllLocal a (Fin.cons b f) ↔ Local a b (headRow f) ∧ AllLocal (some b) f := by
  have hz : belowRow (Fin.cons b f) 0 = headRow f := by
    by_cases h : 0 < n
    · simp only [belowRow, headRow, Fin.val_zero, show 0+1 < n+1 from by omega,
        h, ↓reduceDIte]
      rfl
    · simp [belowRow, headRow, h, show ¬0+1 < n+1 from by omega]
  have ha (i : Fin n) : aboveRow a (Fin.cons b f) i.succ = aboveRow (some b) f i := by
    simp only [aboveRow, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceDIte, Nat.add_sub_cancel]
    by_cases h : i.val = 0
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte]
      congr 1
      have he : (⟨i.val, by omega⟩ : Fin (n+1)) =
          (⟨i.val-1, by omega⟩ : Fin n).succ := by apply Fin.ext; simp; omega
      rw [he, Fin.cons_succ]
  have hb (i : Fin n) : belowRow (Fin.cons b f) i.succ = belowRow f i := by
    simp only [belowRow, Fin.val_succ, Nat.add_lt_add_iff_right]
    split_ifs with h
    · rfl
    · rfl
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [AllLocal, aboveRow, Fin.val_zero, ↓reduceDIte, Fin.cons_zero, hz] using h 0
    · intro i
      simpa only [ha, hb, Fin.cons_succ] using h i.succ
  · rintro ⟨h, hf⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [aboveRow, Fin.val_zero, ↓reduceDIte, Fin.cons_zero, hz] using h
    · simpa only [ha, hb, Fin.cons_succ] using hf j

private theorem native_split {n : ℕ} (f : Fin n → Fin 3 → Fin 2) (i : Fin n) (j : Fin 3) :
    (Finset.univ.filter (fun q : Fin n × Fin 3 =>
      q ≠ (i,j) ∧ q.1.val ≤ i.val+1 ∧ i.val ≤ q.1.val+1 ∧
      q.2.val ≤ j.val+1 ∧ j.val ≤ q.2.val+1 ∧ f q.1 q.2 ≠ f i j)).card =
      horizontal (f i) j + optional (f i) (aboveRow none f i) j +
        optional (f i) (belowRow f i) j := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have splitRow (r : Fin n) :
      (∑ l : Fin 3, if (r,l) ≠ (i,j) ∧ r.val ≤ i.val+1 ∧ i.val ≤ r.val+1 ∧
        l.val ≤ j.val+1 ∧ j.val ≤ l.val+1 ∧ f r l ≠ f i j then 1 else 0) =
      (if r = i then horizontal (f i) j else 0) +
      (if r.val+1 = i.val then across (f i) (f r) j else 0) +
      (if i.val+1 = r.val then across (f i) (f r) j else 0) := by
    by_cases he : r = i
    · subst r
      simp [horizontal]
    · have hval : r.val ≠ i.val := fun h => he (Fin.ext h)
      by_cases hp : r.val+1 = i.val
      · have hn : i.val+1 ≠ r.val := by omega
        have hr : r.val ≤ i.val+1 := by omega
        have hi : i.val ≤ r.val+1 := by omega
        simp [he, hp, hn, across, hr, hi]
      · by_cases hn : i.val+1 = r.val
        · have hr : r.val ≤ i.val+1 := by omega
          have hi : i.val ≤ r.val+1 := by omega
          simp [he, hp, hn, across, hr, hi]
        · have hfar : ¬ (r.val ≤ i.val+1 ∧ i.val ≤ r.val+1) := by omega
          simp only [he, hp, hn, ite_false, add_zero, horizontal, across]
          apply Finset.sum_eq_zero
          intro l _
          split_ifs with h
          · exact False.elim (hfar ⟨h.2.1,h.2.2.1⟩)
          · rfl
  simp_rw [splitRow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  · congr 1
    by_cases h : i.val = 0
    · have hz (r : Fin n) : r.val+1 ≠ i.val := by omega
      simp [aboveRow, h, optional, hz]
    · let p : Fin n := ⟨i.val-1, by omega⟩
      have he (r : Fin n) : r.val+1 = i.val ↔ r = p := by
        simp only [Fin.ext_iff, p]; omega
      simp_rw [he]
      simp [aboveRow, h, optional, p]
  · by_cases h : i.val+1 < n
    · let p : Fin n := ⟨i.val+1,h⟩
      have he (r : Fin n) : i.val+1 = r.val ↔ r = p := by
        simp only [Fin.ext_iff, p]; omega
      simp_rw [he]
      simp [belowRow, h, optional, p]
    · have he (r : Fin n) : i.val+1 ≠ r.val := by omega
      simp [belowRow, h, optional, he]

private theorem admissible_iff_local {n : ℕ} (f : Fin n → Fin 3 → Fin 2) :
    Admissible (fun p => f p.1 p.2) ↔
      (∀ i : Fin n, i.val = 0 → f i 0 = 0) ∧ AllLocal none f := by
  simp only [Admissible, AllLocal, Local]
  simp_rw [native_split]
  simp only [Prod.forall]

private def TailGood : {k : ℕ} → Fin 8 → Fin 8 → (Fin k → Fin 8) → Prop
  | 0, a, b, _ => L (some a) b none
  | k+1, a, b, f => L (some a) b (some (f 0)) ∧ TailGood b (f 0) (Fin.tail f)

private instance {k : ℕ} (a b : Fin 8) (f : Fin k → Fin 8) : Decidable (TailGood a b f) := by
  induction k generalizing a b with
  | zero => exact inferInstanceAs (Decidable (L _ _ _))
  | succ k ih => exact instDecidableAnd

private theorem local_iff_tail {k : ℕ} (a b : Fin 8) (f : Fin k → Fin 8) :
    AllLocal (some (row a)) (fun i => row ((Fin.cons b f : Fin (k+1) → Fin 8) i)) ↔
      TailGood a b f := by
  induction k generalizing a b with
  | zero =>
    simp only [TailGood]
    rw [show (fun i => row ((Fin.cons b f : Fin 1 → Fin 8) i)) =
      Fin.cons (row b) (fun i => row (f i)) from Fin.comp_cons row b f, allLocal_cons]
    simp [AllLocal, headRow, L]
  | succ k ih =>
    rw [show (fun i => row ((Fin.cons b f : Fin (k+2) → Fin 8) i)) =
      Fin.cons (row b) (fun i => row (f i)) from Fin.comp_cons row b f, allLocal_cons]
    have hf : (fun i => row (f i)) =
        (fun i => row ((Fin.cons (f 0) (Fin.tail f) : Fin (k+1) → Fin 8) i)) := by
      rw [Fin.cons_self_tail]
    rw [hf, ih]
    rfl

private noncomputable def arrayCodingEquiv (k : ℕ) :
    (Fin (k+2) × Fin 3 → Fin 2) ≃ Fin 8 × (Fin 8 × (Fin k → Fin 8)) :=
  (Equiv.curry _ _ _).trans ((Equiv.piCongrRight fun _ => rowEquiv.symm).trans
    ((Fin.consEquiv fun _ : Fin (k+2) => Fin 8).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin 8))
        (Fin.consEquiv fun _ : Fin (k+1) => Fin 8).symm)))

private theorem admissible_coding (k : ℕ) (b c : Fin 8) (f : Fin k → Fin 8) :
    Admissible ((arrayCodingEquiv k).symm (b,c,f)) ↔
      (row b 0 = 0 ∧ L none b (some c)) ∧ TailGood b c f := by
  change Admissible (fun p => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → Fin 8) p.1) p.2) ↔ _
  rw [admissible_iff_local (fun i => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → Fin 8) i))]
  have hr : (∀ i : Fin (k+2), i.val = 0 →
      row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → Fin 8) i) 0 = 0) ↔ row b 0 = 0 := by
    constructor
    · intro h; exact h 0 rfl
    · intro h i hi
      have he : i = 0 := Fin.ext hi
      subst i; exact h
  rw [hr]
  rw [show (fun i => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → Fin 8) i)) =
    Fin.cons (row b) (fun i => row ((Fin.cons c f : Fin (k+1) → Fin 8) i)) from
      Fin.comp_cons row b (Fin.cons c f), allLocal_cons, local_iff_tail]
  simp only [headRow, Nat.zero_lt_succ, ↓reduceDIte, Fin.cons_zero]
  change (row b 0 = 0 ∧ L none b (some c) ∧ TailGood b c f) ↔ _
  exact and_assoc.symm

private theorem count_rows (k : ℕ) :
    a (k+2) = ∑ b : Fin 8, ∑ c : Fin 8, ∑ f : Fin k → Fin 8,
      if (row b 0 = 0 ∧ L none b (some c)) ∧ TailGood b c f then 1 else 0 := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [← (arrayCodingEquiv k).symm.sum_comp]
  simp only [Fintype.sum_prod_type, admissible_coding, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private def next (s : Fin 8 × Fin 8) (c : Fin 8) : Fin 8 × Fin 8 := (s.2,c)
private def cost (s : Fin 8 × Fin 8) (c : Fin 8) : ℤ :=
  if L (some s.1) s.2 (some c) then 1 else 0

private theorem aggregate_transition (s u : Fin 8 × Fin 8) :
    (∑ c : Fin 8, if next s c = u then cost s c else 0) = T s u := by
  rw [Finset.sum_eq_single u.2]
  · have he : next s u.2 = u ↔ u.1 = s.2 := by
      cases u; simp [next, eq_comm]
    simp only [he, cost, T]
    split_ifs <;> simp_all
  · intro c _ hc
    have hn : next s c ≠ u := fun h => hc (congrArg Prod.snd h)
    simp [hn]
  · simp

private theorem contribution_sum {k : ℕ} (a b : Fin 8) (f : Fin k → Fin 8) :
    (∑ u : Fin 8 × Fin 8,
      D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution
        next cost u (a,b) (List.ofFn f) * t u) =
      if TailGood a b f then 1 else 0 := by
  classical
  induction k generalizing a b with
  | zero =>
    simp only [List.ofFn_zero, D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  | succ k ih =>
    rw [List.ofFn_succ]
    simp only [D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution,
      mul_assoc, ← Finset.mul_sum]
    rw [ih]
    change (if L (some a) b (some (f 0)) then 1 else 0) *
      (if TailGood b (f 0) (Fin.tail f) then 1 else 0) =
      if L (some a) b (some (f 0)) ∧ TailGood b (f 0) (Fin.tail f) then 1 else 0
    split_ifs <;> simp_all

private theorem count_eq_power (k : ℕ) :
    a (k+2) = dotProduct (Matrix.vecMul v (T^k)) t := by
  classical
  have hm : (Matrix.of fun s u => ∑ label : Fin 8,
      if next s label = u then cost s label else 0) = T := by
    ext s u; exact aggregate_transition s u
  have hw (b c : Fin 8) : dotProduct ((T^k) (b,c)) t =
      ∑ f : Fin k → Fin 8, if TailGood b c f then 1 else 0 := by
    unfold dotProduct
    rw [← hm]
    simp_rw [← D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.weighted_walks_eq_pow]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [contribution_sum]
  rw [count_rows]
  have hd : dotProduct (Matrix.vecMul v (T^k)) t =
      ∑ s : Fin 8 × Fin 8, v s * dotProduct ((T^k) s) t := by
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [hd]
  simp only [Fintype.sum_prod_type, hw]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  unfold v
  by_cases h : row b 0 = 0 ∧ L none b (some c)
  · simp [h]
  · simp [h]

private def incoming (s : Fin 8 × Fin 8) : Finset (Fin 8 × Fin 8) :=
  (![![{(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (6,0)}, {(0,0), (1,0), (2,0), (4,0)}, {(0,0), (1,0), (2,0), (4,0)}, {(0,0)}, {(0,0), (1,0), (2,0), (4,0)}, {(0,0)}, {(0,0)}, {}], ![{(0,1), (4,1)}, {(7,1)}, {}, {(3,1), (5,1)}, {(0,1)}, {(3,1)}, {}, {(1,1)}], ![{}, {}, {}, {}, {}, {}, {}, {(7,2)}], ![{(3,3)}, {(1,3), (2,3)}, {(1,3)}, {(0,3)}, {}, {}, {(7,3)}, {(6,3), (7,3)}], ![{(0,4), (1,4)}, {(0,4)}, {}, {}, {(7,4)}, {(6,4)}, {(5,4), (6,4)}, {(4,4)}], ![{(0,5)}, {}, {}, {}, {}, {}, {}, {}], ![{(6,6)}, {}, {(4,6)}, {(7,6)}, {(2,6), (4,6)}, {}, {(0,6)}, {(3,6), (7,6)}], ![{}, {(7,7)}, {(7,7)}, {(3,7), (5,7), (6,7), (7,7)}, {(7,7)}, {(3,7), (5,7), (6,7), (7,7)}, {(3,7), (5,7), (6,7), (7,7)}, {(1,7), (2,7), (3,7), (4,7), (5,7), (6,7), (7,7)}]]) s.1 s.2

private theorem transfer_table (s u : Fin 8 × Fin 8) :
    T s u = if s ∈ incoming u then 1 else 0 := by
  rcases s with ⟨a,b⟩
  rcases u with ⟨c,d⟩
  revert a b c d
  decide +kernel

private def step (w : (Fin 8 × Fin 8) → ℤ) : (Fin 8 × Fin 8) → ℤ :=
  fun u => ∑ s ∈ incoming u, w s

private theorem step_eq_vecMul (w : (Fin 8 × Fin 8) → ℤ) : step w = Matrix.vecMul w T := by
  funext u
  simp [step, Matrix.vecMul, dotProduct, transfer_table]

private def values (j : Fin 8) (s : Fin 8 × Fin 8) : ℤ :=
  (![![![1, 1, 1, 1, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0]], ![![2, 2, 2, 1, 2, 1, 1, 0], ![1, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0]], ![![6, 4, 4, 2, 4, 2, 2, 0], ![3, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![3, 2, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![15, 12, 12, 6, 12, 6, 6, 0], ![6, 0, 0, 0, 4, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 2, 0, 0, 0, 0], ![6, 4, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 2, 0], ![0, 1, 1, 1, 1, 1, 1, 1]], ![![31, 27, 27, 15, 27, 15, 15, 0], ![16, 1, 0, 0, 12, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, 0, 6, 0, 0, 1, 1], ![16, 12, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 6, 1], ![0, 1, 1, 1, 1, 1, 1, 1]], ![![73, 63, 63, 31, 63, 31, 31, 0], ![39, 1, 0, 0, 27, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![6, 0, 0, 15, 0, 0, 1, 2], ![39, 27, 0, 0, 1, 0, 0, 1], ![15, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 1, 0, 0, 15, 2], ![0, 1, 1, 3, 1, 3, 3, 4]], ![![178, 151, 151, 73, 151, 73, 73, 0], ![90, 1, 0, 0, 63, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![15, 0, 0, 31, 0, 0, 3, 4], ![90, 63, 0, 0, 1, 0, 0, 1], ![31, 0, 0, 0, 0, 0, 0, 0], ![15, 0, 0, 3, 0, 0, 31, 4], ![0, 4, 4, 8, 4, 8, 8, 11]], ![![419, 358, 358, 178, 358, 178, 178, 0], ![214, 4, 0, 0, 151, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 4], ![31, 0, 0, 73, 0, 0, 8, 11], ![214, 151, 0, 0, 4, 0, 0, 1], ![73, 0, 0, 0, 0, 0, 0, 0], ![31, 0, 0, 8, 0, 0, 73, 11], ![0, 11, 11, 19, 11, 19, 19, 22]]]) j s.1 s.2

private def r (s : Fin 8 × Fin 8) : ℤ :=
  (![![0, 0, 0, 0, 0, 0, 0, 0], ![-2, -2, 0, 0, 0, 0, 0, -2], ![4, 0, 0, 0, 0, 0, 0, -2], ![-2, 0, 0, -2, 0, 0, 0, 0], ![-2, 0, 4, 0, 2, 0, 0, 4], ![-2, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 4, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]) s.1 s.2
private def rOne (s : Fin 8 × Fin 8) : ℤ :=
  (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -2], ![0, 0, 0, 0, 0, 0, 0, 0], ![-2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]) s.1 s.2

private theorem values_zero : values 0 = v := by decide +kernel
private theorem values_step (j : Fin 7) : step (values j.castSucc) = values j.succ := by
  fin_cases j <;> decide +kernel

private theorem values_power (j : Fin 8) : values j = Matrix.vecMul v (T^j.val) := by
  have h (k : ℕ) (hk : k < 8) : values ⟨k,hk⟩ = Matrix.vecMul v (T^k) := by
    induction k with
    | zero => simpa using values_zero
    | succ k ih =>
      let j : Fin 7 := ⟨k,by omega⟩
      have hstep := values_step j
      have hj : j.castSucc = (⟨k,by omega⟩ : Fin 8) := Fin.ext rfl
      have hs : j.succ = (⟨k+1,hk⟩ : Fin 8) := Fin.ext rfl
      rw [step_eq_vecMul, hj, hs] at hstep
      rw [← hstep, ih (by omega), Matrix.vecMul_vecMul, ← pow_succ]
  exact h j.val j.isLt

private theorem residual_identity :
    (4:ℤ) • values 0 + (6:ℤ) • values 1 + (2:ℤ) • values 2 -
      (2:ℤ) • values 3 - (3:ℤ) • values 4 - (2:ℤ) • values 5 - values 6 + values 7 = r := by
  decide +kernel

private theorem residual_step : step r = rOne := by decide +kernel
private theorem residual_step_two : step rOne = 0 := by decide +kernel
private theorem residual_terminal : dotProduct r t = 0 := by decide +kernel
private theorem residual_one_terminal : dotProduct rOne t = 0 := by decide +kernel

private theorem residual_invisible (m : ℕ) : dotProduct (Matrix.vecMul r (T^m)) t = 0 := by
  have hr : Matrix.vecMul r T = rOne := by rw [← step_eq_vecMul, residual_step]
  have hrOne : Matrix.vecMul rOne T = 0 := by rw [← step_eq_vecMul, residual_step_two]
  cases m with
  | zero => simpa using residual_terminal
  | succ m =>
    cases m with
    | zero => simpa [hr] using residual_one_terminal
    | succ k =>
      have hz : Matrix.vecMul r (T^2) = 0 := by
        rw [show (2:ℕ) = 1+1 from rfl, pow_add, pow_one,
          ← Matrix.vecMul_vecMul, hr, hrOne]
      rw [show k+1+1 = 2+k from by omega, pow_add, ← Matrix.vecMul_vecMul, hz]
      simp

private theorem shifted_recurrence (m : ℕ) :
    4*a (m+2) + 6*a (m+3) + 2*a (m+4) - 2*a (m+5) - 3*a (m+6) -
      2*a (m+7) - a (m+8) + a (m+9) = 0 := by
  have hf (j : Fin 8) :
      dotProduct (Matrix.vecMul (values j) (T^m)) t = a (m+j.val+2) := by
    rw [values_power, Matrix.vecMul_vecMul, ← pow_add, add_comm j.val m, count_eq_power]
  have h := congrArg (fun w => dotProduct (Matrix.vecMul w (T^m)) t) residual_identity
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul,
    add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul, hf,
    residual_invisible] at h
  norm_num [Nat.add_assoc] at h
  exact h

/-- Hardin's full empirical recurrence for the independently defined native counts. -/
theorem result : claim := by
  intro n hn
  have h := shifted_recurrence (n-9)
  have h2 : n-9+2 = n-7 := by omega
  have h3 : n-9+3 = n-6 := by omega
  have h4 : n-9+4 = n-5 := by omega
  have h5 : n-9+5 = n-4 := by omega
  have h6 : n-9+6 = n-3 := by omega
  have h7 : n-9+7 = n-2 := by omega
  have h8 : n-9+8 = n-1 := by omega
  have h9 : n-9+9 = n := by omega
  rw [h2,h3,h4,h5,h6,h7,h8,h9] at h
  linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
