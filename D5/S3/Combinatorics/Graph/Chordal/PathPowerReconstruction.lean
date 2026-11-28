/- GID: D5/S3/Combinatorics/Graph/Chordal/PathPowerReconstruction
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consecutive-edge integration gives the group reconstruction bounds for path powers of width one and two. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalPath49Metric
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


namespace SimpleGraph.BanachPathPower

/-- A uniform bound for bi-invariant group gains on all finite paths of the given width. -/
def GroupUniformBound (k : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (H : Type) [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] (g : Fin n → Fin n → H),
    (∀ a b, (pathPower n k).Adj a b → g b a = (g a b)⁻¹) →
    (∀ a b c, (pathPower n k).Adj a b → (pathPower n k).Adj b c →
      (pathPower n k).Adj a c → Dist.dist (g a b * g b c) (g a c) ≤ 1) →
    ∃ p : Fin n → H, ∀ a b, (pathPower n k).Adj a b →
      Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ C

theorem triangle_power_lower (C : ℝ) (hC : GroupUniformBound 2 C) : 1 ≤ C := by
  let := ChordalPath49.cayleyMetric
  let := ChordalPath49.cayley_left
  let := ChordalPath49.cayley_right
  let f : ℕ → ℕ → ChordalPath49.H := fun i j => if i = 0 ∧ j = 2 then 2 else 0
  let g (i j : Fin 3) := Multiplicative.ofAdd (ChordalPath49.skew f i j)
  have hrev (a b : Fin 3) (ha : (pathPower 3 2).Adj a b) : g b a = (g a b)⁻¹ :=
    ChordalPath49.skew_rev f ha.ne
  have htri (a b c : Fin 3) (hab : (pathPower 3 2).Adj a b) (hbc : (pathPower 3 2).Adj b c)
      (hac : (pathPower 3 2).Adj a c) : Dist.dist (g a b * g b c) (g a c) ≤ 1 := by
    have ht (i j l : ℕ) (hij : i < j) (hjl : j < l) (hil : l ≤ i + 2) :
        f i j + f j l - f i l ∈ ChordalPath49.alphabet := by
      have h₁ : j = i + 1 := by omega
      have h₂ : l = i + 2 := by omega
      rw [h₁, h₂]
      by_cases h₀ : i = 0
      · subst i; decide
      · simp [f, h₀, ChordalPath49.alphabet]
    change Dist.dist (Multiplicative.ofAdd (ChordalPath49.skew f a b + ChordalPath49.skew f b c))
      (Multiplicative.ofAdd (ChordalPath49.skew f a c)) ≤ 1
    simpa only [Nat.cast_one] using (ChordalPath49.word_iff_distance 1 _ _).2
      ((ChordalPath49.wordBudget_one_iff _).2 (ChordalPath49.skew_triangles f ht hab hbc hac))
  obtain ⟨p, hp⟩ := hC.2 3 ChordalPath49.M g hrev htri
  by_contra! hlt
  have hz (a b : Fin 3) (hab : (pathPower 3 2).Adj a b) : g a b = (p a)⁻¹ * p b := by
    have hq := (hp a b hab).trans_lt hlt
    change (GroupWordMetric.length ChordalPath49.letters_generate ((g a b)⁻¹ * ((p a)⁻¹ * p b)) : ℝ) < 1 at hq
    have hq' : GroupWordMetric.length ChordalPath49.letters_generate
        ((g a b)⁻¹ * ((p a)⁻¹ * p b)) < 1 := by exact_mod_cast hq
    have hz' : GroupWordMetric.length ChordalPath49.letters_generate
        ((g a b)⁻¹ * ((p a)⁻¹ * p b)) = 0 := by omega
    have he := GroupWordMetric.eq_one_of_length_zero ChordalPath49.letters_generate hz'
    exact inv_mul_eq_one.mp he
  have hab : (pathPower 3 2).Adj 0 1 := ⟨by decide, by decide, by decide⟩
  have hbc : (pathPower 3 2).Adj 1 2 := ⟨by decide, by decide, by decide⟩
  have hac : (pathPower 3 2).Adj 0 2 := ⟨by decide, by decide, by decide⟩
  have he : g 0 1 * g 1 2 = g 0 2 := by rw [hz _ _ hab, hz _ _ hbc, hz _ _ hac]; group
  have hne : g 0 1 * g 1 2 ≠ g 0 2 := by decide
  exact hne he

end SimpleGraph.BanachPathPower
