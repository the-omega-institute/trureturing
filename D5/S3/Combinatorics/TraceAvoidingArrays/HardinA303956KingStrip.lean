/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
