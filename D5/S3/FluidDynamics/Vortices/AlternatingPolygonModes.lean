/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Folded Fourier modes and collision multiplicities of the actual polygon Jacobian. -/


import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Folded Fourier multiplicities and two-dimensional restrictions. -/


noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes

open InverseChordCirculant AlternatingPolygonSpectrum

def fold (m : ℕ) (q : ZMod (2 * m)) : ℕ := min q.val (2 * m - q.val)

def ell (m : ℕ) (q : ZMod (2 * m)) : ℝ := -((m : ℝ) - q.val) ^ 2 / 2

theorem fold_le (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) : fold m q ≤ m := by
  have hq := ZMod.val_lt q
  unfold fold
  omega

theorem ell_fold (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    ell m q = -((m : ℝ) - fold m q) ^ 2 / 2 := by
  have hq := ZMod.val_lt q
  by_cases h : q.val ≤ m
  · have hf : fold m q = q.val := by unfold fold; omega
    rw [hf]
    rfl
  · have hf : fold m q = 2 * m - q.val := by unfold fold; omega
    rw [hf, Nat.cast_sub (by omega : q.val ≤ 2 * m)]
    unfold ell
    push_cast
    ring

theorem ell_shift (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    ell m (q + m) = -(fold m q : ℝ) ^ 2 / 2 := by
  have hm : 0 < m := by
    have := NeZero.ne (2 * m)
    omega
  have hq := ZMod.val_lt q
  have hmv : (m : ZMod (2 * m)).val = m := ZMod.val_natCast_of_lt (by omega)
  by_cases h : q.val < m
  · have hv : (q + m).val = q.val + m := by
      rw [ZMod.val_add, hmv, Nat.mod_eq_of_lt (by omega)]
    have hf : fold m q = q.val := by unfold fold; omega
    simp only [ell, hv, hf, Nat.cast_add]
    ring
  · have hv : (q + m).val = q.val - m := by
      rw [ZMod.val_add_of_le (by rw [hmv]; omega), hmv]
      omega
    have hf : fold m q = 2 * m - q.val := by unfold fold; omega
    rw [ell, hv, hf, Nat.cast_sub (by omega : m ≤ q.val),
      Nat.cast_sub (by omega : q.val ≤ 2 * m)]
    push_cast
    ring

theorem mode_product (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    ell m q * (ell m (q + m) + 1) = gamma m q := by
  rw [ell_fold, ell_shift]
  change -((m : ℝ) - fold m q) ^ 2 / 2 * (-(fold m q : ℝ) ^ 2 / 2 + 1) =
    ((m : ℝ) - fold m q) ^ 2 * ((fold m q : ℝ) ^ 2 - 2) / 4
  ring

theorem ell_add_one_ne_zero (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    ell m q + 1 ≠ 0 := by
  rw [ell_fold]
  have hle := fold_le m q
  let n := m - fold m q
  have hn : (n : ℝ) = (m : ℝ) - fold m q := Nat.cast_sub hle
  rw [← hn]
  intro h
  have hs : (n : ℝ) ^ 2 = 2 := by linarith
  have hlt : n < 2 := by
    by_contra hlt
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    nlinarith
  interval_cases n <;> norm_num at hs

theorem gamma_zero_iff (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    gamma m q = 0 ↔ fold m q = m := by
  rw [← mode_product, mul_eq_zero, or_iff_left (ell_add_one_ne_zero m (q + m))]
  rw [ell_fold]
  constructor
  · intro h
    have hsq : ((m : ℝ) - fold m q) ^ 2 = 0 := by linarith
    have he : (m : ℝ) = fold m q := sub_eq_zero.mp ((sq_eq_zero_iff).mp hsq)
    exact_mod_cast he.symm
  · intro h
    simp [h]

/-- Folding retains exactly the pair of opposite cyclic labels. -/
theorem fold_eq_iff (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m))
    {r : ℕ} (hr : r ≤ m) :
    fold m q = r ↔ q.val = r ∨ q.val = 2 * m - r := by
  have hq := ZMod.val_lt q
  unfold fold
  omega

private theorem fold_natCast (m : ℕ) [NeZero (2 * m)] {r : ℕ} (hr : r ≤ m) :
    fold m (r : ZMod (2 * m)) = r := by
  have hm : 0 < m := by have := NeZero.ne (2 * m); omega
  rw [fold, ZMod.val_natCast_of_lt (by omega)]
  omega

private theorem fold_neg (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    fold m (-q) = fold m q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [fold, ZMod.neg_val, ite_eq_right hq]
    have hv := ZMod.val_lt q
    have hpos : 0 < q.val := by
      by_contra h
      have hzero : q.val = 0 := by omega
      exact hq ((ZMod.val_eq_zero q).mp hzero)
    unfold fold
    omega

/-- End labels occur once; every interior folded label occurs twice. -/
theorem fold_fibre_card (m : ℕ) [NeZero (2 * m)] {r : ℕ} (hr : r ≤ m) :
    (Finset.univ.filter (fun q : ZMod (2 * m) => fold m q = r)).card =
      if r = 0 ∨ r = m then 1 else 2 := by
  classical
  have hm : 0 < m := by have := NeZero.ne (2 * m); omega
  have hv : (r : ZMod (2 * m)).val = r := ZMod.val_natCast_of_lt (by omega)
  have hf : Finset.univ.filter (fun q : ZMod (2 * m) => fold m q = r) =
      {(r : ZMod (2 * m)), -(r : ZMod (2 * m))} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases (fold_eq_iff m q hr).mp h with h | h
      · left
        exact ZMod.val_injective _ (h.trans hv.symm)
      · right
        by_cases hr0 : r = 0
        · subst r
          have := ZMod.val_lt q
          omega
        · apply ZMod.val_injective _
          rw [ZMod.neg_val, ite_eq_right (by
            intro he
            have := congrArg ZMod.val he
            simp [hv] at this
            exact hr0 this), hv]
          exact h
    · rintro (rfl | rfl)
      · exact fold_natCast m hr
      · rw [fold_neg]
        exact fold_natCast m hr
  rw [hf]
  have heq : (r : ZMod (2 * m)) = -(r : ZMod (2 * m)) ↔ r = 0 ∨ r = m := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · rw [← (ZMod.val_injective (2 * m)).eq_iff, ZMod.neg_val, ite_eq_right (by
        intro he
        have := congrArg ZMod.val he
        simp [hv] at this
        exact hr0 this), hv]
      omega
  by_cases h : r = 0 ∨ r = m
  · rw [ite_eq_left h, ← heq.mpr h]
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton]
  · rw [ite_eq_right h]
    exact Finset.card_pair (heq.not.mpr h)

private theorem prod_fold {A : Type*} [CommMonoid A] (m : ℕ) [NeZero (2 * m)]
    (g : ℕ → A) :
    (∏ q : ZMod (2 * m), g (fold m q)) =
      ∏ r ∈ Finset.range (m + 1), g r ^ (if r = 0 ∨ r = m then 1 else 2) := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ)
    (t := Finset.range (m + 1)) (g := fold m)
    (fun q _ => Finset.mem_range.mpr (by have := fold_le m q; omega)) g]
  apply Finset.prod_congr rfl
  intro r hr
  rw [Finset.prod_const, fold_fibre_card m (by simpa using Finset.mem_range.mp hr)]

/-- Folded mode factors, with endpoint multiplicity one and interior
multiplicity two. This identity includes the separate small polygons. -/
theorem charpoly_folded (m : ℕ) (hm : 1 ≤ m) :
    (jacobian (2 * m)).charpoly =
      X ^ 2 * (X ^ 2 + C ((m : ℝ) ^ 2 / 2)) *
        ∏ r ∈ Finset.Ico 1 m,
          (X ^ 2 - C (((m : ℝ) - r) ^ 2 * ((r : ℝ) ^ 2 - 2) / 4)) ^ 2 := by
  classical
  have : NeZero (2 * m) := ⟨by omega⟩
  let g : ℕ → ℝ[X] := fun r =>
    X ^ 2 - C (((m : ℝ) - r) ^ 2 * ((r : ℝ) ^ 2 - 2) / 4)
  have hg : ∀ q : ZMod (2 * m), X ^ 2 - C (gamma m q) = g (fold m q) :=
    fun q => rfl
  rw [charpoly_mode_product m hm]
  simp_rw [hg]
  rw [prod_fold, Finset.prod_range_succ, Finset.range_eq_Ico,
    Finset.prod_eq_prod_Ico_succ_bot (by omega : 0 < m)]
  have hmid : (∏ r ∈ Finset.Ico 1 m, g r ^ (if r = 0 ∨ r = m then 1 else 2)) =
      ∏ r ∈ Finset.Ico 1 m, g r ^ 2 := by
    apply Finset.prod_congr rfl
    intro r hr
    have hr := Finset.mem_Ico.mp hr
    simp [show ¬(r = 0 ∨ r = m) by omega]
  rw [hmid]
  have h0 : g 0 = X ^ 2 + C ((m : ℝ) ^ 2 / 2) := by
    dsimp [g]
    simp only [Nat.cast_zero, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub]
    rw [show (m : ℝ) ^ 2 * -2 / 4 = -((m : ℝ) ^ 2 / 2) by ring, map_neg,
      sub_neg_eq_add]
  have hm' : g m = X ^ 2 := by simp [g]
  simp only [or_true, true_or, ite_true, pow_one, h0, hm']
  change (X ^ 2 + C ((m : ℝ) ^ 2 / 2)) *
      (∏ r ∈ Finset.Ico 1 m, g r ^ 2) * X ^ 2 =
    X ^ 2 * (X ^ 2 + C ((m : ℝ) ^ 2 / 2)) *
      (∏ r ∈ Finset.Ico 1 m, g r ^ 2)
  ring

/-- The complete normalized polynomial at every m >= 3. -/
theorem charpoly_factored (m : ℕ) (hm : 3 ≤ m) :
    (jacobian (2 * m)).charpoly =
      X ^ 2 * (X ^ 2 + C ((m : ℝ) ^ 2 / 2)) *
        (X ^ 2 + C (((m : ℝ) - 1) ^ 2 / 4)) ^ 2 *
          ∏ r ∈ Finset.Ico 2 m,
            (X ^ 2 - C (((m : ℝ) - r) ^ 2 * ((r : ℝ) ^ 2 - 2) / 4)) ^ 2 := by
  rw [charpoly_folded m (by omega),
    Finset.prod_eq_prod_Ico_succ_bot (by omega : 1 < m)]
  norm_num only [Nat.cast_one, one_pow, show 1 + 1 = 2 from rfl]
  rw [show ((m : ℝ) - 1) ^ 2 * -1 / 4 = -(((m : ℝ) - 1) ^ 2 / 4) by ring,
    map_neg, sub_neg_eq_add]
  ring

/-- Dipole polynomial, derived separately from the all-mode identity. -/
theorem dipole_charpoly :
    (jacobian 2).charpoly = X ^ 2 * (X ^ 2 + C (1 / 2 : ℝ)) := by
  simpa using charpoly_folded 1 (by omega)

/-- The square constants follow from the actual Cartesian derivative. They
are not the constants printed in BK arXiv v2 Eq. (12). -/
theorem square_charpoly :
    (jacobian 4).charpoly = X ^ 2 * (X ^ 2 + C (2 : ℝ)) *
      (X ^ 2 + C (1 / 4 : ℝ)) ^ 2 := by
  have h := charpoly_folded 2 (by omega)
  norm_num [Finset.prod_Ico_succ_top] at h ⊢
  exact h

theorem neutral_denominator_ne_zero (m : ℕ) : (1 : ℝ) - (m : ℝ) ^ 2 / 2 ≠ 0 := by
  intro h
  have hs : (m : ℝ) ^ 2 = 2 := by linarith
  have hlt : m < 2 := by
    by_contra hlt
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    nlinarith
  interval_cases m <;> norm_num at hs

/-- The direct sum of the two-dimensional Fourier restrictions. -/
def pairedOperator {Q : Type*} (α β : Q → ℂ) : Module.End ℂ (Q → ℂ × ℂ) where
  toFun v q := (α q * (v q).2, β q * (v q).1)
  map_add' v w := by
    ext q <;> simp [mul_add]
  map_smul' c v := by
    ext q <;> simp [mul_left_comm]

private lemma paired_kernel_square {Q : Type*} (α β : Q → ℂ) {μ : ℂ} (hμ : μ ≠ 0)
    (v : Q → ℂ × ℂ)
    (h : (pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ)))
      ((pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ))) v) = 0) :
    (pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ))) v = 0 := by
  funext q
  have h₁ := congrArg (fun w : Q → ℂ × ℂ => (w q).1) h
  have h₂ := congrArg (fun w : Q → ℂ × ℂ => (w q).2) h
  change α q * (β q * (v q).1 - μ * (v q).2) -
    μ * (α q * (v q).2 - μ * (v q).1) = 0 at h₁
  change β q * (α q * (v q).2 - μ * (v q).1) -
    μ * (β q * (v q).1 - μ * (v q).2) = 0 at h₂
  change (α q * (v q).2 - μ * (v q).1,
    β q * (v q).1 - μ * (v q).2) = (0, 0)
  by_cases hγ : α q * β q = μ ^ 2
  · apply Prod.ext
    · apply (mul_eq_zero.mp (show (2 * μ) *
        (α q * (v q).2 - μ * (v q).1) = 0 by
          linear_combination -h₁ + (v q).1 * hγ)).resolve_left
      exact mul_ne_zero (by norm_num) hμ
    · apply (mul_eq_zero.mp (show (2 * μ) *
        (β q * (v q).1 - μ * (v q).2) = 0 by
          linear_combination -h₂ + (v q).2 * hγ)).resolve_left
      exact mul_ne_zero (by norm_num) hμ
  · have hγ' : α q * β q - μ ^ 2 ≠ 0 := sub_ne_zero.mpr hγ
    apply Prod.ext
    · apply (mul_eq_zero.mp (show (α q * β q - μ ^ 2) *
        (α q * (v q).2 - μ * (v q).1) = 0 by
          linear_combination α q * h₂ + μ * h₁)).resolve_left hγ'
    · apply (mul_eq_zero.mp (show (α q * β q - μ ^ 2) *
        (β q * (v q).1 - μ * (v q).2) = 0 by
          linear_combination β q * h₁ + μ * h₂)).resolve_left hγ'

/-- No two-dimensional off-diagonal restriction has a nontrivial nonzero
Jordan chain. This controls generalized eigenspaces, not just polynomial roots. -/
theorem paired_nonzero_semisimple {Q : Type*} (α β : Q → ℂ) {μ : ℂ} (hμ : μ ≠ 0) :
    (pairedOperator α β).maxGenEigenspace μ =
      (pairedOperator α β).eigenspace μ := by
  apply le_antisymm
  · intro v hv
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
    rw [Module.End.mem_eigenspace_iff]
    suffices (pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ))) v = 0 by
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, sub_eq_zero] using this
    have hpow : ∀ n : ℕ, ∀ v : Q → ℂ × ℂ,
        ((pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ))) ^ n) v = 0 →
        (pairedOperator α β - μ • (1 : Module.End ℂ (Q → ℂ × ℂ))) v = 0 := by
      intro n
      induction n with
      | zero =>
        intro v hv
        have hv : v = 0 := by simpa only [pow_zero, Module.End.one_apply] using hv
        rw [hv, map_zero]
      | succ n ih =>
        intro v hv
        apply paired_kernel_square α β hμ v
        apply ih
        simpa only [pow_succ, Module.End.mul_apply] using hv
    exact hpow n v hn
  · exact Module.End.eigenspace_le_maxGenEigenspace

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes
