import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

compile_only_with_mathlib

/-! Omega original.

Periodic gains on power paths convert a uniform edge fit into a common
enclosing ball for an arbitrary finite family.
-/

namespace SimpleGraph.BanachPathPower

open Finset

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private def phase (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k :=
  ⟨i % k, Nat.mod_lt i hk⟩

private theorem phase_repeat (k : ℕ) (hk : 0 < k) (a : Fin k) (j : ℕ) :
    phase k hk (a.val + j * k) = a := by
  apply Fin.ext
  simp [phase, Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

private def forward (k : ℕ) (hk : 0 < k) (u : Fin k → E) (i j : ℕ) : E :=
  if j = i + k then (2 : ℝ) • u (phase k hk i) else u (phase k hk i)

private def periodicGain {n k : ℕ} (hk : 0 < k) (u : Fin k → E)
    (a b : Fin n) : E :=
  if a < b then forward k hk u a b
  else if b < a then -forward k hk u b a else 0

private theorem gain_forward {n k : ℕ} (hk : 0 < k) (u : Fin k → E)
    {a b : Fin n} (h : a < b) : periodicGain hk u a b = forward k hk u a b := by
  simp [periodicGain, h]

private theorem gain_skew {n k : ℕ} (hk : 0 < k) (u : Fin k → E) (a b : Fin n) :
    periodicGain hk u b a = -periodicGain hk u a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [periodicGain, h, not_lt_of_gt h]
  · simp [periodicGain]
  · simp [periodicGain, h, not_lt_of_gt h]

private theorem gain_triangle {n k : ℕ} (hk : 0 < k) (u : Fin k → E) {D : ℝ}
    (h₁ : ∀ a, ‖u a‖ ≤ D) (h₂ : ∀ a b, ‖u a - u b‖ ≤ D)
    (a b c : Fin n) (hab : (pathPower n k).Adj a b)
    (hbc : (pathPower n k).Adj b c) (hac : (pathPower n k).Adj a c) :
    ‖periodicGain hk u a b + periodicGain hk u b c - periodicGain hk u a c‖ ≤ D := by
  let g := periodicGain (n := n) hk u
  have inv (x y : Fin n) : g y x = -g x y := gain_skew hk u x y
  have ordered (x y z : Fin n) (hxy : x < y) (hyz : y < z)
      (hxz : (pathPower n k).Adj x z) : ‖g x y + g y z - g x z‖ ≤ D := by
    have hxy' : x.val < y.val := hxy
    have hyz' : y.val < z.val := hyz
    have hspan := hxz.2.2
    change ‖periodicGain hk u x y + periodicGain hk u y z - periodicGain hk u x z‖ ≤ D
    rw [gain_forward hk u hxy, gain_forward hk u hyz, gain_forward hk u (hxy.trans hyz)]
    simp only [forward, ite_eq_right (show y.val ≠ x.val + k by omega),
      ite_eq_right (show z.val ≠ y.val + k by omega)]
    split_ifs with he
    · rw [two_smul, show u (phase k hk x) + u (phase k hk y) -
          (u (phase k hk x) + u (phase k hk x)) = u (phase k hk y) - u (phase k hk x) by abel]
      exact h₂ _ _
    · rw [add_comm, add_sub_cancel_right]
      exact h₁ _
  have swapFirst (x y z : Fin n) :
      ‖g y x + g x z - g y z‖ = ‖g x y + g y z - g x z‖ := by
    rw [inv x y, ← norm_neg (g x y + g y z - g x z)]
    congr 1
    abel
  have swapLast (x y z : Fin n) :
      ‖g x z + g z y - g x y‖ = ‖g x y + g y z - g x z‖ := by
    rw [inv y z, ← norm_neg (g x y + g y z - g x z)]
    congr 1
    abel
  change ‖g a b + g b c - g a c‖ ≤ D
  rcases lt_or_gt_of_ne hab.ne with hab' | hba'
  · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
    · exact ordered a b c hab' hbc' hac
    · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
      · rw [← swapLast a b c]
        exact ordered a c b hac' hcb' hab
      · rw [← swapLast a b c, ← swapFirst a c b]
        exact ordered c a b hca' hab' hbc.symm
  · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
    · rw [swapFirst b a c]
      exact ordered b a c hba' hac' hbc
    · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
      · rw [swapFirst b a c, ← swapLast b a c]
        exact ordered b c a hbc' hca' hab.symm
      · rw [swapFirst b a c, ← swapLast b a c, ← swapFirst b c a]
        exact ordered c b a hcb' hba' hac.symm

private def memberAt {k M : ℕ} (a : Fin k) {j : ℕ} (h : j ≤ M) :
    Fin (k * (M + 1)) :=
  ⟨a.val + j * k, by
    have hm := Nat.mul_le_mul_right k h
    rw [Nat.mul_succ]
    nlinarith [a.isLt]⟩

private theorem phase_edge {k M : ℕ} (a : Fin k) {j : ℕ} (h : j + 1 ≤ M) :
    (pathPower (k * (M + 1)) k).Adj (memberAt a (by omega : j ≤ M)) (memberAt a h) := by
  have hk := a.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have := congrArg Fin.val he
    simp only [memberAt, Nat.add_mul, Nat.one_mul] at this
    omega
  · dsimp [memberAt]
    rw [Nat.add_mul]
    omega
  · dsimp [memberAt]
    rw [Nat.add_mul]
    omega

private theorem row_edge {k M : ℕ} {a b : Fin k} (hab : a < b) {j : ℕ} (h : j ≤ M) :
    (pathPower (k * (M + 1)) k).Adj (memberAt a h) (memberAt b h) := by
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have := congrArg Fin.val he
    simp only [memberAt] at this
    omega
  · dsimp [memberAt]
    omega
  · dsimp [memberAt]
    omega

/-- On a finite power path, fitting the periodic gains yields a single ball
around the doubled target family with an explicit finite-size correction. -/
theorem exists_gain_for_doubled_radius {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (u : Fin k → E) (D : ℝ) (h₁ : ∀ a, ‖u a‖ ≤ D) (h₂ : ∀ a b, ‖u a - u b‖ ≤ D) :
    ∃ g : Fin (k * (M + 1)) → Fin (k * (M + 1)) → E,
      (∀ a b, g b a = -g a b) ∧
      (∀ a b c, (pathPower (k * (M + 1)) k).Adj a b →
        (pathPower (k * (M + 1)) k).Adj b c →
        (pathPower (k * (M + 1)) k).Adj a c → ‖g a b + g b c - g a c‖ ≤ D) ∧
      ∀ (p : Fin (k * (M + 1)) → E) (R : ℝ), 0 ≤ R →
        (∀ a b, (pathPower (k * (M + 1)) k).Adj a b → ‖g a b - (p b - p a)‖ ≤ R) →
        ∃ y : E, ∀ a, ‖(2 : ℝ) • u a - y‖ ≤ R + 2 * R / M * ((k - 1 : ℕ) : ℝ) / k := by
  let g := periodicGain (n := k * (M + 1)) hk u
  refine ⟨g, gain_skew hk u, gain_triangle hk u h₁ h₂, ?_⟩
  intro p R hR hp
  let q (a : Fin k) := (M : ℝ)⁻¹ • (p (memberAt a (le_refl M)) -
    p (memberAt a (Nat.zero_le M)))
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have long {a : Fin k} {j : ℕ} (hj : j + 1 ≤ M) :
      g (memberAt a (by omega : j ≤ M)) (memberAt a hj) = (2 : ℝ) • u a := by
    have he : (memberAt a hj).val =
        (memberAt a (by omega : j ≤ M)).val + k := by simp [memberAt, Nat.add_mul, Nat.add_assoc]
    have hlt : memberAt a (by omega : j ≤ M) < memberAt a hj := by
      change (memberAt a (by omega : j ≤ M)).val < (memberAt a hj).val
      omega
    change periodicGain hk u _ _ = _
    rw [gain_forward hk u hlt, forward, ite_eq_left he]
    simp [memberAt, phase_repeat]
  have along (a : Fin k) : ‖(2 : ℝ) • u a - q a‖ ≤ R := by
    have step (j : ℕ) (hj : j ≤ M) :
        ‖(j : ℝ) • ((2 : ℝ) • u a) -
          (p (memberAt a hj) - p (memberAt a (Nat.zero_le M)))‖ ≤ (j : ℝ) * R := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hj' : j ≤ M := by omega
        have h := hp _ _ (phase_edge a hj)
        rw [long hj] at h
        push_cast
        rw [add_smul, one_smul, show
            (j : ℝ) • ((2 : ℝ) • u a) + (2 : ℝ) • u a -
                (p (memberAt a hj) - p (memberAt a (Nat.zero_le M))) =
              ((j : ℝ) • ((2 : ℝ) • u a) -
                (p (memberAt a hj') - p (memberAt a (Nat.zero_le M)))) +
              ((2 : ℝ) • u a - (p (memberAt a hj) - p (memberAt a hj'))) by abel]
        exact (norm_add_le _ _).trans (by linarith [ih hj'])
    have he :
        (2 : ℝ) • u a - q a = (M : ℝ)⁻¹ • ((M : ℝ) • ((2 : ℝ) • u a) -
          (p (memberAt a (le_refl M)) - p (memberAt a (Nat.zero_le M)))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hMR.ne', one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ)⁻¹)]
    calc
      _ ≤ (M : ℝ)⁻¹ * ((M : ℝ) * R) :=
        mul_le_mul_of_nonneg_left (step M le_rfl) (by positivity)
      _ = R := by rw [← mul_assoc, inv_mul_cancel₀ hMR.ne', one_mul]
  have short {a b : Fin k} (hab : a < b) {j : ℕ} (hj : j ≤ M) :
      g (memberAt a hj) (memberAt b hj) = u a := by
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    have hlt : memberAt a hj < memberAt b hj := by
      change (memberAt a hj).val < (memberAt b hj).val
      dsimp [memberAt]
      omega
    change periodicGain hk u _ _ = _
    rw [gain_forward hk u hlt, forward,
      ite_eq_right (show (memberAt b hj).val ≠ (memberAt a hj).val + k by dsimp [memberAt]; omega)]
    simp [memberAt, phase_repeat]
  have compare {a b : Fin k} (hab : a < b) : ‖q a - q b‖ ≤ 2 * R / M := by
    have hs := hp _ _ (row_edge hab (Nat.zero_le M))
    have ht := hp _ _ (row_edge hab (le_refl M))
    rw [short hab (Nat.zero_le M)] at hs
    rw [short hab (le_refl M)] at ht
    dsimp [q]
    rw [← smul_sub, show
        p (memberAt a (le_refl M)) - p (memberAt a (Nat.zero_le M)) -
          (p (memberAt b (le_refl M)) - p (memberAt b (Nat.zero_le M))) =
        (u a - (p (memberAt b (le_refl M)) - p (memberAt a (le_refl M)))) -
          (u a - (p (memberAt b (Nat.zero_le M)) - p (memberAt a (Nat.zero_le M)))) by abel,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ)⁻¹)]
    rw [div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_sub_le _ _).trans (by linarith)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let y : E := (k : ℝ)⁻¹ • ∑ b : Fin k, q b
  refine ⟨y, fun a => ?_⟩
  have he : q a - y = (k : ℝ)⁻¹ • ∑ b ∈ univ.erase a, (q a - q b) := by
    have hs : (∑ b ∈ univ.erase a, (q a - q b)) = ∑ b : Fin k, (q a - q b) := by
      simpa using sum_erase_add (univ : Finset (Fin k)) (fun b => q a - q b) (mem_univ a)
    rw [hs, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_sub, smul_smul, inv_mul_cancel₀ hkr.ne', one_smul]
  have hb (b : Fin k) (hne : b ≠ a) : ‖q a - q b‖ ≤ 2 * R / M := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [norm_sub_rev]
      exact compare h
    · exact compare h
  have hc : ‖q a - y‖ ≤ 2 * R / M * ((k - 1 : ℕ) : ℝ) / k := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)⁻¹)]
    calc
      _ ≤ (k : ℝ)⁻¹ * ∑ b ∈ univ.erase a, ‖q a - q b‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (k : ℝ)⁻¹ * ∑ b ∈ univ.erase a, (2 * R / M) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun b h => hb b (mem_erase.mp h).1) (by positivity)
      _ = _ := by simp only [sum_const, card_erase_of_mem (mem_univ a), card_univ,
          Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]; ring
  rw [show (2 : ℝ) • u a - y = ((2 : ℝ) • u a - q a) + (q a - y) by abel]
  exact (norm_add_le _ _).trans (add_le_add (along a) hc)

theorem clique_card_le_width_add_one {n k : ℕ} {s : Finset (Fin n)}
    (hc : (pathPower n k).IsClique (s : Set (Fin n))) : s.card ≤ k + 1 := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha, hm⟩ := Finset.exists_min_image s Fin.val hs
    have hsub : s.image Fin.val ⊆ Finset.Icc a.val (a.val + k) := by
      intro i hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
      refine Finset.mem_Icc.mpr ⟨hm b hb, ?_⟩
      by_cases he : a = b
      · simp [he]
      · exact (hc ha hb he).2.2
    rw [← s.card_image_of_injective Fin.val_injective]
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end SimpleGraph.BanachPathPower
