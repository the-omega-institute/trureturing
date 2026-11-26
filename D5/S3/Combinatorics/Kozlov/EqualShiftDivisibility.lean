/- GID: D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Kozlov/EqualShiftDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: The equal-shift Kozlov lattice deficit has roots zero and minus one. -/

import D5.S3.Combinatorics.Kozlov.MatrixPowerPolynomial
import D5.S3.Combinatorics.Kozlov.TransferEndpoints
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

open Polynomial
open scoped Polynomial

namespace D5.S3.Combinatorics.Kozlov

def AgreesOnPositiveRanks (P : ℚ[X]) (count : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → P.eval (r : ℚ) = (count r : ℚ)

private theorem positive_ranks_unique {P Q : ℚ[X]} {count : ℕ → ℕ}
    (hP : AgreesOnPositiveRanks P count) (hQ : AgreesOnPositiveRanks Q count) :
    P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun r : ℕ => ((r + 1 : ℕ) : ℚ)) := by
    intro a b h
    change ((a + 1 : ℕ) : ℚ) = ((b + 1 : ℕ) : ℚ) at h
    have hab : a + 1 = b + 1 := by exact_mod_cast h
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨r, rfl⟩
  exact (hP _ (by omega)).trans (hQ _ (by omega)).symm

private noncomputable def continuation {n : ℕ} (hn : 1 ≤ n) (T : Matrix (Fin n) (Fin n) ℕ) : ℚ[X] :=
  (powerPolynomial (T.map (Nat.castRingHom ℚ)) (firstState hn) (lastState hn)).comp (X + 1)

private theorem continuation_eval {n : ℕ} (hn : 1 ≤ n) {T : Matrix (Fin n) (Fin n) ℕ}
    (hT : (∀ i j, j < i → T i j = 0) ∧ (∀ i, T i i = 1))
    (x : ℚ) (m : ℕ) (hx : x + 1 = (m : ℚ)) :
    (continuation hn T).eval x = ((T ^ m) (firstState hn) (lastState hn) : ℚ) := by
  have hlow : ∀ i j, j < i → T.map (Nat.castRingHom ℚ) i j = 0 := by
    intro i j hij
    simp [hT.1 _ _ hij]
  have hdiag : ∀ i, T.map (Nat.castRingHom ℚ) i i = 1 := by
    intro i
    simp [hT.2]
  rw [continuation, eval_comp, eval_add, eval_X, eval_one, hx,
    powerPolynomial_eval hlow hdiag, ← Matrix.map_pow]
  rfl

private theorem proper_continuation {n : ℕ} (hn : 1 ≤ n) :
    AgreesOnPositiveRanks (continuation hn (properTransfer hn))
      (fun r => (properSumset n r).ncard) := by
  intro r hr
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [continuation_eval hn (properTransfer_unitriangular hn) _ (k + 2) (by
    push_cast
    ring)]
  exact_mod_cast (proper_count_as_entry hn k).symm

private theorem lattice_continuation {n : ℕ} (hn : 1 ≤ n) :
    AgreesOnPositiveRanks (continuation hn (latticeTransfer hn))
      (fun r => (dilateLattice n r).ncard) := by
  intro r hr
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [continuation_eval hn (latticeTransfer_unitriangular hn) _ (k + 2) (by
    push_cast
    ring)]
  exact_mod_cast (lattice_count_as_entry hn k).symm

theorem equal_shift_count_polynomials_exist (n : ℕ) (hn : 1 ≤ n) :
    ∃ A L : ℚ[X],
      AgreesOnPositiveRanks A (fun r => (properSumset n r).ncard) ∧
      AgreesOnPositiveRanks L (fun r => (dilateLattice n r).ncard) :=
  ⟨_, _, proper_continuation hn, lattice_continuation hn⟩

private theorem paired_endpoints {n : ℕ} (hn : 1 ≤ n) (A L : ℚ[X])
    (hA : AgreesOnPositiveRanks A (fun r => (properSumset n r).ncard))
    (hL : AgreesOnPositiveRanks L (fun r => (dilateLattice n r).ncard)) :
    L.eval 0 = 1 ∧ A.eval 0 = 1 ∧
      L.eval (-1) = (if n = 1 then 1 else 0) ∧ A.eval (-1) = (if n = 1 then 1 else 0) := by
  have eh := firstState_eq_lastState_iff hn
  rw [positive_ranks_unique hA (proper_continuation hn),
      positive_ranks_unique hL (lattice_continuation hn)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [continuation_eval hn (latticeTransfer_unitriangular hn) 0 1 (by norm_num), pow_one]
    have hh := transfer_last_column hn (latticeVectors hn)
      (fun _ hf => normalized_one_bounded hn ((mem_latticeVectors hn).mp hf))
      (fun _ hf => normalized_one_fixed hn ((mem_latticeVectors hn).mp hf))
      (fun _ hk => skeleton_mem_latticeVectors hn hk)
      (fun _ hf => lattice_terminal hn hf) (firstState hn)
    change latticeTransfer hn (firstState hn) (lastState hn) = 1 at hh
    rw [hh, Nat.cast_one]
  · rw [continuation_eval hn (properTransfer_unitriangular hn) 0 1 (by norm_num), pow_one]
    have hh := transfer_last_column hn (properVectors n)
      (fun _ hf => SnF_bounded (mem_properVectors.mp hf))
      (fun _ hf => SnF_fixed hn (mem_properVectors.mp hf))
      (fun _ hk => mem_properVectors.mpr (skeleton_mem_SnF hk))
      (fun _ hf => SnF_terminal (mem_properVectors.mp hf)) (firstState hn)
    change properTransfer hn (firstState hn) (lastState hn) = 1 at hh
    rw [hh, Nat.cast_one]
  · rw [continuation_eval hn (latticeTransfer_unitriangular hn) (-1) 0 (by norm_num), pow_zero]
    simp [Matrix.one_apply, eh]
  · rw [continuation_eval hn (properTransfer_unitriangular hn) (-1) 0 (by norm_num), pow_zero]
    simp [Matrix.one_apply, eh]

/-- Snellman's equal-shift question, with both interpolants specified by their literal counts. -/
theorem equal_shift_kozlov_deficiency_divisible (n : ℕ) (hn : 1 ≤ n) (A L : ℚ[X])
    (hA : AgreesOnPositiveRanks A (fun r => (properSumset n r).ncard))
    (hL : AgreesOnPositiveRanks L (fun r => (dilateLattice n r).ncard)) :
    X * (X + 1) ∣ L - A := by
  obtain ⟨hL0, hA0, hLm, hAm⟩ := paired_endpoints hn A L hA hL
  have h0 : (L - A).eval 0 = 0 := by simp [hL0, hA0]
  have hm : (L - A).eval (-1) = 0 := by simp [hLm, hAm]
  have hX : X ∣ L - A := Polynomial.X_dvd_iff.mpr (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact h0)
  obtain ⟨Q, hQ⟩ := hX
  have hQm : Q.eval (-1) = 0 := by simpa [hQ] using hm
  have hfactor : X + 1 ∣ Q := by
    rw [show (X : ℚ[X]) + 1 = X - C (-1) by simp,
      Polynomial.dvd_iff_isRoot]
    exact hQm
  obtain ⟨R, hR⟩ := hfactor
  exact ⟨R, by rw [hQ, hR, mul_assoc]⟩

end D5.S3.Combinatorics.Kozlov
