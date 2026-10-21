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
import Mathlib.Basic.Sign.Basic
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

private lemma sign_correlation (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (∑ ε : Fin k → Fin 2,
      (SignType.sign (∑ j, signValue (ε j)) : ℝ) * signValue (ε i)) =
      (∑ ε : Fin k → Fin 2, |∑ j, signValue (ε j)|) / k := by
  classical
  let S (ε : Fin k → Fin 2) : ℝ := ∑ j, signValue (ε j)
  let σ (ε : Fin k → Fin 2) : SignType := SignType.sign (S ε)
  let T (j : Fin k) : ℝ := ∑ ε : Fin k → Fin 2, (σ ε : ℝ) * signValue (ε j)
  have hsymm (j l : Fin k) : T j = T l := by
    let e : (Fin k → Fin 2) ≃ (Fin k → Fin 2) :=
      { toFun := fun ε t => ε (Equiv.swap j l t)
        invFun := fun ε t => ε (Equiv.swap j l t)
        left_inv := by intro ε; funext t; simp only [Equiv.swap_apply_self]
        right_inv := by intro ε; funext t; simp only [Equiv.swap_apply_self] }
    have hS (ε : Fin k → Fin 2) : S (e ε) = S ε :=
      Equiv.sum_comp (Equiv.swap j l) (fun t => signValue (ε t))
    calc
      T j = ∑ ε : Fin k → Fin 2, (σ (e ε) : ℝ) * signValue (e ε j) :=
        (e.sum_comp (fun ε => (σ ε : ℝ) * signValue (ε j))).symm
      _ = T l := by
        apply Finset.sum_congr rfl
        intro ε _
        have hσ : σ (e ε) = σ ε := congrArg SignType.sign (hS ε)
        rw [hσ]
        change (σ ε : ℝ) * signValue (ε (Equiv.swap j l j)) = _
        rw [Equiv.swap_apply_left]
  have htotal : (k : ℝ) * T i = ∑ ε : Fin k → Fin 2, |S ε| := by
    calc
      (k : ℝ) * T i = ∑ j : Fin k, T j := by
        calc
          (k : ℝ) * T i = ∑ _ : Fin k, T i := by simp
          _ = ∑ j : Fin k, T j := Finset.sum_congr rfl (fun j _ => hsymm i j)
      _ = ∑ ε : Fin k → Fin 2, (σ ε : ℝ) * S ε := by
        dsimp only [T, S]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ ε : Fin k → Fin 2, |S ε| := by
        apply Finset.sum_congr rfl
        intro ε _
        exact sign_mul_self (S ε)
  change T i = (∑ ε : Fin k → Fin 2, |S ε|) / k
  exact (eq_div_iff (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)).mpr
    ((mul_comm (T i) k).trans htotal)

private lemma averaged_abs_nonneg (k : ℕ) (hk : 0 < k) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (a k / k) * (∑ i, |x i|) ≤
      ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i) * x i| := by
  classical
  let σ (ε : Fin k → Fin 2) : SignType := SignType.sign (∑ i, signValue (ε i))
  have hpoint (ε : Fin k → Fin 2) :
      (σ ε : ℝ) * (∑ i, signValue (ε i) * x i) ≤ |∑ i, signValue (ε i) * x i| := by
    calc
      _ ≤ |(σ ε : ℝ) * (∑ i, signValue (ε i) * x i)| := le_abs_self _
      _ ≤ _ := by
        rw [abs_mul]
        have hσ : |(σ ε : ℝ)| ≤ 1 := by cases σ ε <;> norm_num [SignType.cast]
        exact mul_le_of_le_one_left (abs_nonneg _) hσ
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => hpoint ε)
  have hexpand :
      (∑ ε : Fin k → Fin 2, (σ ε : ℝ) * ∑ i, signValue (ε i) * x i) =
        ((∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i)|) / k) * ∑ i, |x i| := by
    calc
      _ = ∑ ε : Fin k → Fin 2, ∑ i : Fin k, (σ ε : ℝ) *
          (signValue (ε i) * x i) := by simp only [Finset.mul_sum]
      _ = ∑ i : Fin k, ∑ ε : Fin k → Fin 2, (σ ε : ℝ) *
          (signValue (ε i) * x i) := Finset.sum_comm
      _ = ∑ i : Fin k, x i *
          (∑ ε : Fin k → Fin 2, (σ ε : ℝ) * signValue (ε i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ε _
        ring
      _ = ∑ i : Fin k, x i *
          ((∑ ε : Fin k → Fin 2, |∑ j, signValue (ε j)|) / k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (∑ ε : Fin k → Fin 2, (σ ε : ℝ) * signValue (ε i)) =
          (∑ ε : Fin k → Fin 2, |∑ j, signValue (ε j)|) / k from
            sign_correlation k hk i]
      _ = _ := by
        rw [← Finset.sum_mul, mul_comm]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => (abs_of_nonneg (hx i)).symm)
  rw [hexpand] at hsum
  have h := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k))
  unfold a
  convert h using 1 <;> ring

private lemma averaged_abs_lower (k : ℕ) (hk : 0 < k) (x : Fin k → ℝ) :
    (a k / k) * (∑ i, |x i|) ≤
      ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i) * x i| := by
  classical
  let e : (Fin k → Fin 2) ≃ (Fin k → Fin 2) :=
    Equiv.piCongrRight (fun i =>
      if x i < 0 then Equiv.swap (0 : Fin 2) 1 else Equiv.refl (Fin 2))
  have hflip (s : Fin 2) : signValue (Equiv.swap (0 : Fin 2) 1 s) = -signValue s := by
    fin_cases s <;> norm_num [signValue]
  have hcoord (ε : Fin k → Fin 2) (i : Fin k) :
      signValue (e ε i) * x i = signValue (ε i) * |x i| := by
    change signValue ((if x i < 0 then Equiv.swap (0 : Fin 2) 1 else
      Equiv.refl (Fin 2)) (ε i)) * x i = _
    by_cases hi : x i < 0
    · rw [ite_eq_left hi, hflip, abs_of_neg hi]
      ring
    · rw [ite_eq_right hi, Equiv.refl_apply, abs_of_nonneg (le_of_not_gt hi)]
  have hsum : (∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i) * x i|) =
      ∑ ε : Fin k → Fin 2, |∑ i, signValue (ε i) * (|x i|)| := by
    calc
      _ = ∑ ε : Fin k → Fin 2, |∑ i, signValue (e ε i) * x i| :=
        (e.sum_comp (fun ε => |∑ i, signValue (ε i) * x i|)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ε _
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hcoord ε i)
  rw [hsum]
  have h := averaged_abs_nonneg k hk (fun i => |x i|) (fun i => abs_nonneg (x i))
  simpa only [abs_abs] using h

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
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a k := by
    unfold a
    apply mul_pos (inv_pos.mpr (pow_pos (by norm_num) k))
    apply Finset.sum_pos'
    · exact fun ε _ => abs_nonneg _
    · refine ⟨fun _ => 1, Finset.mem_univ _, ?_⟩
      have hone : signValue (1 : Fin 2) = 1 := by norm_num [signValue]
      simpa only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] using hkR
  unfold Lk
  rw [dite_eq_left hk]
  unfold fiberMax
  apply Finset.sup'_le
  intro f _
  have hfiber (ε : Fin k → Fin 2) (q : Fin m) :
      (∑ j, signValue (ε j) * fiberSum f M j q) =
        ∑ i, signValue (ε (f i)) * M i q := by
    unfold fiberSum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hrow (ε : Fin k → Fin 2) :
      (∑ q, |∑ j, signValue (ε j) * fiberSum f M j q|) ≤ L M := by
    simp_rw [hfiber]
    exact Finset.le_sup' (fun v : Fin n → Fin 2 =>
      ∑ q, |∑ i, signValue (v i) * M i q|) (Finset.mem_univ (fun i => ε (f i)))
  have havg : (a k / k) * manhattan (fun j q => fiberSum f M j q) ≤ L M := by
    calc
      _ = ∑ q : Fin m, (a k / k) * ∑ j : Fin k, |fiberSum f M j q| := by
        unfold manhattan
        rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ q : Fin m, ((2 : ℝ) ^ k)⁻¹ *
          ∑ ε : Fin k → Fin 2, |∑ j, signValue (ε j) * fiberSum f M j q| :=
        Finset.sum_le_sum (fun q _ => averaged_abs_lower k hk (fun j => fiberSum f M j q))
      _ = ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Fin 2,
          ∑ q : Fin m, |∑ j, signValue (ε j) * fiberSum f M j q| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((2 : ℝ) ^ k)⁻¹ * ∑ _ : Fin k → Fin 2, L M :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ε _ => hrow ε))
          (by positivity)
      _ = L M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos (by norm_num) k)), one_mul]
  have h := (le_div_iff₀ (div_pos ha hkR)).mpr ((mul_comm _ _).trans_le havg)
  calc
    manhattan (fun j q => fiberSum f M j q) ≤ L M / (a k / k) := h
    _ = ((k : ℝ) / a k) * L M := by rw [div_div_eq_mul_div]; ring

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
