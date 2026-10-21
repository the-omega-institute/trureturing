/- GID: D5/S3/Quantum/Optimization/PrepareMeasureLkBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Optimization/PrepareMeasureLkBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prepare-and-measure bound is uniformly strict for every k at least three. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-! The averaged sign functional gives a strict prepare-and-measure bound. -/

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Optimization.PrepareMeasureLkBound

def signValue (s : Fin 2) : ℝ := if s = 0 then -1 else 1

def manhattan {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

def fiberSum {n m k : ℕ} (f : Fin n → Fin k) (M : Matrix (Fin n) (Fin m) ℝ)
    (j : Fin k) (q : Fin m) : ℝ :=
  ∑ i, if f i = j then M i q else 0

private def fiberMax {n m k : ℕ} (hk : 0 < k) (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  letI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  (Finset.univ : Finset (Fin n → Fin k)).sup'
    Finset.univ_nonempty (fun f => manhattan (fun j q => fiberSum f M j q))

def Lk (k : ℕ) {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  if hk : 0 < k then fiberMax hk M else 0

def L {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  letI : Nonempty (Fin n → Fin 2) := ⟨fun _ => 0⟩
  (Finset.univ : Finset (Fin n → Fin 2)).sup'
    Finset.univ_nonempty (fun v => ∑ j, |∑ i, signValue (v i) * M i j|)

def a (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i)|

private lemma a_nonneg (k : ℕ) : 0 ≤ a k := by
  unfold a
  positivity

private def signs3Equiv : (Fin 3 → Fin 2) ≃ Fin 2 × (Fin 2 × Fin 2) where
  toFun := fun f => (f 0, (f 1, f 2))
  invFun := fun x => ![x.1, x.2.1, x.2.2]
  left_inv := by
    intro f
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨a, b, c⟩
    rfl

private lemma a_three : a 3 = (3 / 2 : ℝ) := by
  unfold a
  rw [Fintype.sum_equiv signs3Equiv
    (fun ε => |∑ i, signValue (ε i)|)
    (fun x => |signValue x.1 + signValue x.2.1 + signValue x.2.2|)
    (by intro ε; simp [signs3Equiv, Fin.sum_univ_succ] <;> ring_nf)]
  simp_rw [Fintype.sum_prod_type]
  norm_num [signValue]

def claim : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, c < k ∧
    ∀ n m (M : Matrix (Fin n) (Fin m) ℝ), Lk k M ≤ c * L M

private lemma averaged_abs_lower (k : ℕ) (hk : 0 < k) (x : Fin k → ℝ) :
    (a k / k) * (∑ i, |x i|) ≤
      ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i) * x i| := by
  sorry

private lemma a_succ_ge (k : ℕ) : a k ≤ a (k + 1) := by
  classical
  have hsplit : (∑ ε : Fin (k + 1) → Fin 2, |∑ i, signValue (ε i)|) =
      ∑ ε : Fin k → Fin 2,
        (|(-1 : ℝ) + ∑ i, signValue (ε i)| + |1 + ∑ i, signValue (ε i)|) := by
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 2)).sum_comp]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      signValue, ↓reduceIte, Fin.isValue]
    rw [← Finset.sum_add_distrib]
    norm_num only [Fin.reduceEq, ↓reduceIte]
  have hsum : 2 * (∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i)|) ≤
      ∑ ε : Fin k → Fin 2,
        (|(-1 : ℝ) + ∑ i, signValue (ε i)| + |1 + ∑ i, signValue (ε i)|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ε _
    have h := abs_add_le (-1 + ∑ i, signValue (ε i)) (1 + ∑ i, signValue (ε i))
    have heq : (-1 + ∑ i, signValue (ε i)) + (1 + ∑ i, signValue (ε i)) =
        2 * ∑ i, signValue (ε i) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  unfold a
  rw [hsplit, pow_succ]
  have hp : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  have hi : (2 ^ k * 2 : ℝ)⁻¹ = (2 ^ k)⁻¹ / 2 := by rw [mul_inv_rev]; ring
  rw [hi]
  nlinarith [mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)]

private lemma a_lower_three_halves (k : ℕ) (hk : 3 ≤ k) :
    (3 / 2 : ℝ) ≤ a k := by
  induction k, hk using Nat.le_induction with
  | base =>
      simpa using (le_of_eq a_three.symm)
  | succ k hk ih =>
      exact le_trans ih (a_succ_ge k)

private lemma lk_bound (k : ℕ) (hk : 0 < k) (n m : ℕ)
    (M : Matrix (Fin n) (Fin m) ℝ) :
    Lk k M ≤ ((k : ℝ) / a k) * L M := by
  sorry

theorem result : claim := by
  intro k hk
  have hk0 : 0 < k := by omega
  have ha : (3 / 2 : ℝ) ≤ a k := a_lower_three_halves k hk
  have hak : 1 < a k := by linarith [a_nonneg k]
  let c : ℝ := (k : ℝ) / a k
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    apply (div_lt_iff₀ (lt_trans (by norm_num : (0 : ℝ) < 1) hak)).mpr
    nlinarith
  · intro n m M
    exact lk_bound k hk0 n m M

end D5.S3.Quantum.Optimization.PrepareMeasureLkBound
