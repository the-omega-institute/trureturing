import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Group

compile_only_with_mathlib

/-!
Omega original.

Rooted reconstruction and retractions of finite path powers.
-/

namespace SimpleGraph.BanachPathPower

private def pathGauge {n : ℕ} {H : Type*} [Group H] (g : Fin n → Fin n → H) : ℕ → H
  | 0 => 1
  | i + 1 => if hi : i + 1 < n then pathGauge g i * g ⟨i, by omega⟩ ⟨i + 1, hi⟩ else 1

theorem pathPower_small_group_upper_bound {n k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2)
    {H : Type*} [Group H] [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]
    (g : Fin n → Fin n → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, (pathPower n k).Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, (pathPower n k).Adj a b → (pathPower n k).Adj b c →
      (pathPower n k).Adj a c → Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ p : Fin n → H, ∀ a b, (pathPower n k).Adj a b →
      Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ ((k : ℝ) - 1) * ε := by
  let p (v : Fin n) := pathGauge g v.val
  have hnext (a b : Fin n) (h : b.val = a.val + 1) : p b = p a * g a b := by
    have hi : a.val + 1 < n := h ▸ b.isLt
    unfold p
    rw [h, pathGauge, dite_eq_left hi]
    congr 1
    congr 1
    exact Fin.ext h.symm
  have fit (a b : Fin n) (h : (pathPower n k).Adj a b) (hab : a.val < b.val) :
      Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ ((k : ℝ) - 1) * ε := by
    by_cases he : b.val = a.val + 1
    · rw [hnext a b he]
      simp only [← mul_assoc, inv_mul_cancel, one_mul, _root_.dist_self]
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
      exact mul_nonneg (sub_nonneg.mpr hkr) hε
    · have h₂ : b.val = a.val + 2 := by have := h.2.2; omega
      have hK : k = 2 := by have := h.2.2; omega
      let m : Fin n := ⟨a.val + 1, by have := b.isLt; omega⟩
      have h₁ : (pathPower n k).Adj a m :=
        ⟨fun he => by have := congrArg Fin.val he; dsimp [m] at this; omega,
          by dsimp [m]; omega, by dsimp [m]; omega⟩
      have h₂m : (pathPower n k).Adj m b :=
        ⟨fun he => by have := congrArg Fin.val he; dsimp [m] at this; omega,
          by dsimp [m]; omega, by dsimp [m]; omega⟩
      rw [hnext m b (by dsimp [m]; omega), hnext a m rfl]
      have heq : (p a)⁻¹ * (p a * g a m * g m b) = g a m * g m b := by group
      rw [heq, _root_.dist_comm]
      simpa [hK, show (2 : ℝ) - 1 = 1 by norm_num] using htri a m b h₁ h₂m h
  refine ⟨p, fun a b h => ?_⟩
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · exact fit a b h hab
  · exact (h.1 (Fin.ext hab)).elim
  · have hr := fit b a h.symm hab
    rw [hrev a b h] at hr
    rw [← dist_inv_inv (g a b) ((p a)⁻¹ * p b)]
    simpa only [mul_inv_rev, inv_inv] using hr

end SimpleGraph.BanachPathPower

