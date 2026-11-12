/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA202330
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Four-column binary arrays with increasing two-bit windows. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Bit values are embedded before any arithmetic. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Both adjacent comparisons between two-bit windows of a four-bit row. -/
def horizontal (r : Fin 4 → Bool) : Prop :=
  ∀ j : Fin 2, 2 * bit (r ⟨j.val, by omega⟩) + bit (r ⟨j.val+1, by omega⟩) ≤
    2 * bit (r ⟨j.val+1, by omega⟩) + bit (r ⟨j.val+2, by omega⟩)

instance (r : Fin 4 → Bool) : Decidable (horizontal r) := by
  unfold horizontal
  infer_instance

/-- Labeled arrays with open boundaries and the original window comparisons. -/
def valid {n : ℕ} (a : Fin (n+1) → Fin 4 → Bool) : Prop :=
  (∀ i, horizontal (a i)) ∧
  ∀ i : ℕ, ∀ hi : i+2 < n+1, ∀ j : Fin 4,
    2 * bit (a ⟨i, by omega⟩ j) + bit (a ⟨i+1, by omega⟩ j) ≤
      2 * bit (a ⟨i+1, by omega⟩ j) + bit (a ⟨i+2, hi⟩ j)

noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {a : Fin (n+1) → Fin 4 → Bool // valid a}

/-- OFFSET 1,1: the formal series has zero constant coefficient. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (count n : ℚ))

def claim : Prop :=
  (∀ n : ℕ, 1 ≤ n → 12 * (count n : ℤ) =
    (n : ℤ)^4 + 16*(n : ℤ)^3 + 83*(n : ℤ)^2 + 176*(n : ℤ) + 156) ∧
  (let X : PowerSeries ℚ := PowerSeries.X
   generatingSeries = X*(36-98*X+112*X^2-61*X^3+13*X^4) * ((1-X)^5)⁻¹) ∧
  (∀ n : ℕ, 6 ≤ n → (count n : ℤ) =
    5*(count (n-1) : ℤ) - 10*(count (n-2) : ℤ) + 10*(count (n-3) : ℤ) -
      5*(count (n-4) : ℤ) + (count (n-5) : ℤ))

private def row : Fin 6 → Fin 4 → Bool :=
  ![![false,false,false,false], ![false,false,false,true],
    ![false,false,true,false], ![false,false,true,true],
    ![false,true,true,true], ![true,true,true,true]]

private def rowMap (i : Fin 6) : {r : Fin 4 → Bool // horizontal r} :=
  ⟨row i, by revert i; decide⟩

private noncomputable def rowEquiv : Fin 6 ≃ {r : Fin 4 → Bool // horizontal r} :=
  Equiv.ofBijective rowMap (by constructor <;> decide)

private def Q (a b c : Fin 6) : Prop :=
  ∀ j : Fin 4, 2*bit (row a j) + bit (row b j) ≤
    2*bit (row b j) + bit (row c j)

private instance (a b c : Fin 6) : Decidable (Q a b c) := by
  unfold Q
  infer_instance

private def T : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℤ :=
  fun s t => if t.1 = s.2 ∧ Q s.1 s.2 t.2 then 1 else 0

private theorem decoded_good {n : ℕ} (w : Fin (n+1) → Fin 6) :
    valid (fun i => row (w i)) ↔ good (fun _ _ => True) Q (List.ofFn w) := by
  rw [good_iff_local]
  have get (i : ℕ) (hi : i < n+1) :
      (List.ofFn w).getD i default = w ⟨i,hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hr (i : Fin 6) : horizontal (row i) := (rowMap i).property
  simp only [valid, hr, implies_true, true_and, List.length_ofFn]
  constructor
  · intro h i hi
    simpa only [get i (by omega), get (i+1) (by omega), get (i+2) hi, Q] using h i hi
  · intro h i hi
    simpa only [get i (by omega), get (i+1) (by omega), get (i+2) hi, Q] using h i hi

private noncomputable def arrayEquiv (n : ℕ) :
    {a : Fin (n+1) → Fin 4 → Bool // valid a} ≃
      {w : Fin (n+1) → Fin 6 // good (fun _ _ => True) Q (List.ofFn w)} where
  toFun a := by
    let w : Fin (n+1) → Fin 6 := fun i => rowEquiv.symm ⟨a.val i, a.property.1 i⟩
    have hw (i) : row (w i) = a.val i :=
      congrArg Subtype.val (rowEquiv.apply_symm_apply ⟨a.val i, a.property.1 i⟩)
    exact ⟨w, (decoded_good w).mp (by simpa only [hw] using a.property)⟩
  invFun w := ⟨fun i => row (w.val i), (decoded_good w.val).mpr w.property⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (rowEquiv.apply_symm_apply ⟨a.val i, a.property.1 i⟩)
  right_inv w := by
    apply Subtype.ext
    funext i
    exact rowEquiv.symm_apply_apply (w.val i)

private theorem count_transfer (m : ℕ) :
    (count (m+1) : ℤ) = dotProduct (1 : Fin 6 × Fin 6 → ℤ)
      ((T^m).mulVec (1 : Fin 6 × Fin 6 → ℤ)) := by
  have hc := Nat.card_congr (arrayEquiv (m+1))
  rw [count, hc]
  apply cardMatrix (fun _ _ => True) Q (fun a b => (a,b)) T 1
  · intro a b _ s
    rcases s with ⟨d,c⟩
    simp only [T, Prod.mk.injEq, true_and]
    rw [show (∑ r : Fin 6, if Q a b r ∧ b = d ∧ r = c then (1 : ℤ) else 0) =
      (if b = d ∧ Q a b c then 1 else 0) by
        simp only [and_assoc, and_left_comm, and_comm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]]
    by_cases h : d = b <;> simp_all
  · intro s
    rcases s with ⟨a,b⟩
    simp only [Prod.mk.injEq, true_and]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private def V (m : ℤ) : Fin 6 × Fin 6 → ℤ :=
  fun s => if s = (0,0) then m^4+12*m^3+41*m^2+54*m+48
    else if s.2 = 1 ∧ (s.1 = 0 ∨ s.1 = 1) ∨
      s.2 = 2 ∧ (s.1 = 0 ∨ s.1 = 2) then 2*(m+1)*(m+2)*(m+6)
    else if s.2 = 3 ∧ s.1 ≤ 3 then 6*(m+1)*(m+4)
    else if s.2 = 4 ∧ s.1 ≤ 4 then 12*(m+2)
    else if s.2 = 5 then 12 else 0

private theorem vector_base :
    (12 : ℤ) • ((T^2).mulVec (1 : Fin 6 × Fin 6 → ℤ)) = V 2 := by
  decide

private theorem vector_step (m : ℤ) : T.mulVec (V m) = V (m+1) := by
  ext ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ] <;>
    norm_num [T, Q, row, bit, V, Fin.forall_fin_succ] <;> ring

private theorem vector_power (k : ℕ) :
    (12 : ℤ) • ((T^(k+2)).mulVec (1 : Fin 6 × Fin 6 → ℤ)) = V (k+2) := by
  induction k with
  | zero => simpa using vector_base
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega, pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_smul, ih, vector_step]
    push_cast
    ring_nf

private theorem vector_sum (m : ℤ) :
    (∑ s : Fin 6 × Fin 6, V m s) =
      (m+1)^4+16*(m+1)^3+83*(m+1)^2+176*(m+1)+156 := by
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, V]
  ring

private theorem quartic (n : ℕ) (hn : 1 ≤ n) :
    12*(count n : ℤ) =
      (n : ℤ)^4+16*(n : ℤ)^3+83*(n : ℤ)^2+176*(n : ℤ)+156 := by
  rcases n with _ | n
  · omega
  rw [count_transfer]
  rcases n with _ | n
  · norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]
  rcases n with _ | k
  · simp only [pow_one, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ]
    norm_num [T, Q, row, bit, Fin.forall_fin_succ]
  have h := congrArg (fun w : Fin 6 × Fin 6 → ℤ => ∑ s, w s) (vector_power k)
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, vector_sum] at h
  simp only [dotProduct, Pi.one_apply, one_mul]
  convert h using 1 <;> push_cast <;> ring

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (count n : ℤ) = 5*(count (n-1) : ℤ)-10*(count (n-2) : ℤ)+
      10*(count (n-3) : ℤ)-5*(count (n-4) : ℤ)+(count (n-5) : ℤ) := by
  have h0 := quartic n (by omega)
  have h1 := quartic (n-1) (by omega)
  have h2 := quartic (n-2) (by omega)
  have h3 := quartic (n-3) (by omega)
  have h4 := quartic (n-4) (by omega)
  have h5 := quartic (n-5) (by omega)
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n),
    Nat.cast_sub (by omega : 5 ≤ n)] at h1 h2 h3 h4 h5
  have h : 12*((count n : ℤ) - (5*(count (n-1) : ℤ)-10*(count (n-2) : ℤ)+
      10*(count (n-3) : ℤ)-5*(count (n-4) : ℤ)+(count (n-5) : ℤ))) = 0 := by
    linear_combination h0-5*h1+10*h2-10*h3+5*h4-h5
  linarith

private theorem series_formula :
    generatingSeries = (let X : PowerSeries ℚ := PowerSeries.X
      X*(36-98*X+112*X^2-61*X^3+13*X^4)*((1-X)^5)⁻¹) := by
  let X : PowerSeries ℚ := PowerSeries.X
  have hb (k : ℕ) (hk : 1 ≤ k) : 12*(count k : ℚ) =
      (k : ℚ)^4+16*(k : ℚ)^3+83*(k : ℚ)^2+176*(k : ℚ)+156 := by
    exact_mod_cast quartic k hk
  have h1 : (count 1 : ℚ) = 36 := by have h := hb 1 (by omega); norm_num at h; linarith
  have h2 : (count 2 : ℚ) = 82 := by have h := hb 2 (by omega); norm_num at h; linarith
  have h3 : (count 3 : ℚ) = 162 := by have h := hb 3 (by omega); norm_num at h; linarith
  have h4 : (count 4 : ℚ) = 289 := by have h := hb 4 (by omega); norm_num at h; linarith
  have h5 : (count 5 : ℚ) = 478 := by have h := hb 5 (by omega); norm_num at h; linarith
  have hp : generatingSeries * (1-X)^5 = X*(36-98*X+112*X^2-61*X^3+13*X^4) := by
    have he : generatingSeries * (1-X)^5 = generatingSeries -
        5*(generatingSeries*X^1)+10*(generatingSeries*X^2)-
        10*(generatingSeries*X^3)+5*(generatingSeries*X^4)-generatingSeries*X^5 := by ring
    rw [he]
    have he' : X*(36-98*X+112*X^2-61*X^3+13*X^4) =
        36*X^1-98*X^2+112*X^3-61*X^4+13*X^5 := by ring
    rw [he']
    apply PowerSeries.ext
    intro n
    simp only [map_sub, map_add, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      generatingSeries, PowerSeries.coeff_mk, X]
    by_cases hn : n < 6
    · interval_cases n <;> norm_num [h1,h2,h3,h4,h5]
    · have hr : (count n : ℚ) = 5*(count (n-1) : ℚ)-10*(count (n-2) : ℚ)+
          10*(count (n-3) : ℚ)-5*(count (n-4) : ℚ)+(count (n-5) : ℚ) := by
        exact_mod_cast recurrence n (by omega)
      simp only [ite_eq_left (by omega : 1 ≤ n), ite_eq_left (by omega : 2 ≤ n),
        ite_eq_left (by omega : 3 ≤ n), ite_eq_left (by omega : 4 ≤ n), ite_eq_left (by omega : 5 ≤ n),
        ite_eq_right (by omega : n ≠ 0), ite_eq_right (by omega : n ≠ 1),
        ite_eq_right (by omega : n ≠ 2), ite_eq_right (by omega : n ≠ 3),
        ite_eq_right (by omega : n ≠ 4), ite_eq_right (by omega : n ≠ 5),
        ite_eq_right (by omega : n-1 ≠ 0), ite_eq_right (by omega : n-2 ≠ 0),
        ite_eq_right (by omega : n-3 ≠ 0), ite_eq_right (by omega : n-4 ≠ 0),
        ite_eq_right (by omega : n-5 ≠ 0)]
      linarith
  change generatingSeries = X*(36-98*X+112*X^2-61*X^3+13*X^4)*((1-X)^5)⁻¹
  calc
    generatingSeries = (generatingSeries*(1-X)^5)*((1-X)^5)⁻¹ := by
      rw [mul_assoc, PowerSeries.mul_inv_cancel _ (by norm_num [X]), mul_one]
    _ = _ := by rw [hp]

/-- The full native-array quartic, formal generating function and signed recurrence. -/
theorem result : claim := ⟨quartic, series_formula, recurrence⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA202330
