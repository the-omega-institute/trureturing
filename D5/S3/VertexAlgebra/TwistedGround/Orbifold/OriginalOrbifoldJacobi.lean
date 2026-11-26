/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered Borcherds identities for the original fixed and negative twisted modes. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

/-! Ordered coefficient Jacobi laws on the original two-sector orbifold carrier.

The all-fixed case follows from the fixed lattice vertex algebra. The identities
with three twisted states and with two twisted sources acting on a fixed state
remain to be established for the assembled field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution HalfFock.LatticeHalfFockParityField
open OriginalOrbifoldField OriginalOrbifoldTranslation
open OriginalFourMChargeCoset (originalI)
open MixedIntertwiner (originalRightCoefficient original_mixed_jacobi)
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private finsum_range offset_cutoff from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
open private epsilon_add epsilon_nat sign_square from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
open private rightTerm from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew

section Divided

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem choose_cast (n : ℤ) (j : ℕ) :
    integerBinomial n j = Ring.choose (n : ℂ) j :=
  Ring.map_choose (Int.castRingHom ℂ) n j

private theorem choose_step (n : ℤ) (j : ℕ) :
    ((j : ℂ) + 1) * integerBinomial n (j + 1) =
      integerBinomial n j * ((n : ℂ) - j) := by
  have h := Ring.choose_smul_choose (n : ℂ) (Nat.le_succ j)
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_succ,
    show j.succ - j = 1 by omega, Ring.choose_one_right, choose_cast] using h

private theorem divided_zero (S : Module.End ℂ W) (v : W) :
    dividedTranslation S 0 v = v := by
  simp [dividedTranslation]

private theorem divided_succ (S : Module.End ℂ W) (j : ℕ) (v : W) :
    ((j : ℂ) + 1) • dividedTranslation S (j + 1) v =
      S (dividedTranslation S j v) := by
  simp only [dividedTranslation, LinearMap.smul_apply, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_succ, pow_succ', Module.End.mul_apply, map_smul, smul_smul]
  congr 1
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

private theorem divided_succ_right (S : Module.End ℂ W) (j : ℕ) (v : W) :
    ((j : ℂ) + 1) • dividedTranslation S (j + 1) v =
      dividedTranslation S j (S v) := by
  rw [divided_succ]
  simp only [dividedTranslation, LinearMap.smul_apply, map_smul]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', pow_succ]

private theorem divided_state_of_step (μ : Modes W) (S : Module.End ℂ W)
    (step : ∀ n v, μ n (S v) = -(n : ℂ) • μ (n - 1) v) :
    DividedStateTranslation μ S := by
  intro j
  induction j with
  | zero => intro n v; simp [divided_zero, choose_cast]
  | succ j ih =>
    intro n v
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    apply (smul_right_inj hj).mp
    rw [← map_smul, divided_succ_right, ih, step]
    simp only [smul_smul, Nat.cast_succ, pow_succ]
    rw [show n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) by omega]
    push_cast
    congr 1
    rw [show ((j : ℂ) + 1) * ((-1 : ℂ)^j * -1 * integerBinomial n (j + 1)) =
        -((-1 : ℂ)^j) * (((j : ℂ) + 1) * integerBinomial n (j + 1)) by ring,
      choose_step]
    ring

private theorem divided_mode_of_step (μ : Modes W) (S : Module.End ℂ W) (a : W)
    (step : ∀ n v, μ n a (S v) = S (μ n a v) + (n : ℂ) • μ (n - 1) a v) :
    DividedModeTranslation μ S a := by
  intro n h
  induction h with
  | zero => intro v; simp [divided_zero, choose_cast]
  | succ h ih =>
    intro v
    have hh : (h : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero h
    apply (smul_right_inj hh).mp
    rw [← map_smul, divided_succ_right, ih]
    simp only [step, map_add, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    let f := fun t : ℕ =>
      integerBinomial n t • dividedTranslation S (h + 1 - t) (μ (n - t) a v)
    change _ = ∑ t ∈ Finset.range (h + 2), ((h : ℂ) + 1) • f t
    have first :
        (∑ t ∈ Finset.range (h + 1),
          integerBinomial n t • dividedTranslation S (h - t) (S (μ (n - t) a v))) =
        ∑ t ∈ Finset.range (h + 2), ((h + 1 - t : ℕ) : ℂ) • f t := by
      rw [Finset.sum_range_succ (fun t => ((h + 1 - t : ℕ) : ℂ) • f t) (h + 1)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      rw [← divided_succ_right, show h - t + 1 = h + 1 - t by omega]
      simp only [f, smul_smul]
      rw [← show ((h + 1 - t : ℕ) : ℂ) = ((h - t : ℕ) : ℂ) + 1 by
        rw [← Nat.cast_succ]; congr 1; omega, mul_comm]
    have second :
        (∑ t ∈ Finset.range (h + 1),
          integerBinomial n t • ((n - (t : ℤ) : ℤ) : ℂ) •
            dividedTranslation S (h - t) (μ (n - t - 1) a v)) =
        ∑ t ∈ Finset.range (h + 2), (t : ℂ) • f t := by
      rw [Finset.sum_range_succ' (fun t => (t : ℂ) • f t) (h + 1)]
      simp only [Nat.cast_zero, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [f, smul_smul, Nat.cast_succ, Int.cast_sub, Int.cast_natCast]
      rw [choose_step, show h + 1 - (t + 1) = h - t by omega,
        show n - ((t : ℤ) + 1) = n - t - 1 by omega]
    rw [first, second, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← add_smul, Nat.cast_sub (by have := Finset.mem_range.mp ht; omega), Nat.cast_succ]
    congr 1
    ring

end Divided

variable {D : LatticeData} {hu : IsUnit D.G.det}
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

local notation "μ" => modesOfStateField (Y D hu hD)
local notation "τ" => T D hu

/-- The literal orbifold mode map has divided state translation. -/
theorem divided_state_translation (h24 : D.rank = 24) : DividedStateTranslation μ τ :=
  divided_state_of_step μ τ (Y_translation D hu hD h24)

/-- Divided translation through any literal orbifold mode, on its second input. -/
theorem divided_mode_translation (h24 : D.rank = 24) (a : Carrier D hu) :
    DividedModeTranslation μ τ a := by
  apply divided_mode_of_step
  intro n v
  have h := LinearMap.congr_fun (Y_covariance D hu hD h24 n a) v
  change τ (μ n a v) - μ n a (τ v) = -(n : ℂ) • μ (n - 1) a v at h
  calc
    μ n a (τ v) = τ (μ n a v) - (τ (μ n a v) - μ n a (τ v)) := by
      rw [sub_sub_cancel]
    _ = _ := by rw [h, neg_smul, sub_neg_eq_add]

section Skew

private theorem translation_diagonal (l : ℕ) :
    (∑ j ∈ Finset.range (l + 1), (-1 : ℂ)^(l - j) * (j.factorial : ℂ)⁻¹ *
      ((l - j).factorial : ℂ)⁻¹) = if l = 0 then 1 else 0 := by
  have binomial (j : ℕ) (hj : j ≤ l) :
      (j.factorial : ℂ)⁻¹ * ((l - j).factorial : ℂ)⁻¹ =
        (l.choose (l - j) : ℂ) * (l.factorial : ℂ)⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial j (l - j)
    rw [Nat.add_sub_of_le hj] at h
    have hc : (l.choose (l - j) : ℂ) * (j.factorial : ℂ) *
        ((l - j).factorial : ℂ) = (l.factorial : ℂ) := by exact_mod_cast h
    have h₁ : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have h₂ : ((l - j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (l - j)
    have h₃ : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
    field_simp
    linear_combination -hc
  simp_rw [mul_assoc]
  trans ∑ j ∈ Finset.range (l + 1),
      ((-1 : ℂ)^(l - j) * (l.choose (l - j) : ℂ)) * (l.factorial : ℂ)⁻¹
  · apply Finset.sum_congr rfl
    intro j hj
    rw [binomial j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_assoc]
  rw [← Finset.sum_mul]
  have hrev := Finset.sum_range_reflect
    (fun j => (-1 : ℂ)^j * (l.choose j : ℂ)) (l + 1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [show (∑ j ∈ Finset.range (l + 1), (-1 : ℂ)^(l - j) * (l.choose (l - j) : ℂ)) =
      ∑ j ∈ Finset.range (l + 1), (-1 : ℂ)^j * (l.choose j : ℂ) by
    convert hrev using 2]
  have h := Int.alternating_sum_range_choose (n := l)
  have hc := congrArg (Int.cast : ℤ → ℂ) h
  cases l with
  | zero => simp
  | succ l =>
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, Nat.succ_ne_zero, ite_false, Int.cast_zero] at hc ⊢
    rw [hc, zero_mul]

private theorem skew_reverse {W : Type*} [AddCommGroup W] [Module ℂ W]
    (μ' : Modes W) (trunc : LowerTruncated μ') (S : Module.End ℂ W) {a b : W}
    (skew : SkewAt μ' S a b) : SkewAt μ' S b a := by
  intro n
  obtain ⟨N, tail⟩ := offset_cutoff μ' trunc b a n
  have inner (j : ℕ) :
      μ' (n + j) a b = ∑ k ∈ Finset.range (N - j),
        epsilon (n + j + k + 1) • dividedTranslation S k (μ' (n + j + k) b a) := by
    rw [skew, finsum_range (N := N - j)]
    intro k hk
    rw [show n + (j : ℤ) + k = n + ((j + k : ℕ) : ℤ) by push_cast; ring,
      tail (j + k) (by omega), map_zero, smul_zero]
  rw [finsum_range (N := N)]
  swap
  · intro j hj
    rw [inner j, Nat.sub_eq_zero_of_le hj, Finset.range_zero, Finset.sum_empty,
      map_zero, smul_zero]
  symm
  calc
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (N - j),
        ((-1 : ℂ)^k * (j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹) •
          (S^(j+k)) (μ' (n + ((j+k : ℕ) : ℤ)) b a) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner j, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hs : epsilon (n + j + k + 1) = epsilon (n + j + 1) * (-1 : ℂ)^k := by
        rw [show n + (j : ℤ) + k + 1 = (n + j + 1) + k by omega, epsilon_add, epsilon_nat]
      simp only [dividedTranslation, LinearMap.smul_apply, map_smul, smul_smul,
        pow_add S, Module.End.mul_apply, Nat.cast_add]
      rw [hs, add_assoc n (j : ℤ) (k : ℤ)]
      congr 1
      calc
        _ = (epsilon (n + j + 1) * epsilon (n + j + 1)) *
            ((-1 : ℂ)^k * (j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹) := by ac_rfl
        _ = _ := by rw [sign_square, one_mul]
    _ = ∑ l ∈ Finset.range N,
        (if l = 0 then (1 : ℂ) else 0) • (S^l) (μ' (n + l) b a) := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro l hl
      rw [← translation_diagonal, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    _ = _ := by
      by_cases hN : N = 0
      · simpa [hN] using (tail 0 (by omega)).symm
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro j _ hj
          simp [hj]
        · exact fun h => False.elim (h (Finset.mem_range.mpr (Nat.pos_of_ne_zero hN)))

end Skew

local notation "V₀" => FixedCarrier D
local notation "M₀" => paritySpace D hu (-1)
local notation "vIn" => (LinearMap.inl ℂ V₀ M₀)
local notation "mIn" => (LinearMap.inr ℂ V₀ M₀)

private theorem mode_vv (n : ℤ) (a b : V₀) :
    μ n (vIn a) (vIn b) = vIn (fixedMode D a n b) := by
  change ((Y D hu hD (a, 0))[[n]]) (b, 0) = _
  rw [Y_fixed_ncoeff_apply, map_zero]
  rfl

private theorem mode_vm (n : ℤ) (a : V₀) (u : M₀) :
    μ n (vIn a) (mIn u) = mIn (((fixedParitySlice D hu (-1) a)[[n]]) u) := by
  change ((Y D hu hD (a, 0))[[n]]) (0, u) = _
  rw [Y_fixed_ncoeff_apply, map_zero]
  rfl

private theorem mode_mv (n : ℤ) (u : M₀) (a : V₀) :
    μ n (mIn u) (vIn a) = mIn (originalRightCoefficient D hu n u a) := by
  change ((Y D hu hD (0, u))[[n]]) (a, 0) = _
  rw [Y_ncoeff_apply]
  simp only [Prod.fst, Prod.snd, fixedMode, map_zero, LinearMap.zero_apply, zero_add, add_zero]
  rfl

private theorem mode_mm (n : ℤ) (u v : M₀) :
    μ n (mIn u) (mIn v) = vIn (originalI D hu hD n u v) := by
  change ((Y D hu hD (0, u))[[n]]) (0, v) = _
  rw [Y_ncoeff_apply]
  simp only [Prod.fst, Prod.snd, fixedMode, map_zero, LinearMap.zero_apply, zero_add, add_zero]
  rfl

private theorem truncation : LowerTruncated μ :=
  lowerTruncated_modesOfStateField (Y D hu hD)

private theorem pow_m (j : ℕ) (u : M₀) :
    (τ ^ j) ((mIn u : Carrier D hu)) = mIn ((MixedIntertwiner.translation D hu ^ j) u) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    change (fixedTranslation D 0, _) = ((0 : V₀), _)
    rw [map_zero]
    rfl

private theorem smul_v (z : ℂ) (v : V₀) :
    z • (vIn v : Carrier D hu) = vIn (z • v) :=
  (map_smul (vIn : V₀ →ₗ[ℂ] Carrier D hu) z v).symm

private theorem smul_m (z : ℂ) (u : M₀) :
    z • (mIn u : Carrier D hu) = mIn (z • u) :=
  (map_smul (mIn : M₀ →ₗ[ℂ] Carrier D hu) z u).symm

private theorem sum_v (f : ℕ → V₀) :
    vIn (∑ᶠ j, f j) = ∑ᶠ j, (vIn (f j) : Carrier D hu) :=
  (vIn : V₀ →ₗ[ℂ] Carrier D hu).toAddMonoidHom.map_finsum_of_injective
    LinearMap.inl_injective f

private theorem sum_m (f : ℕ → M₀) :
    mIn (∑ᶠ j, f j) = ∑ᶠ j, (mIn (f j) : Carrier D hu) :=
  (mIn : M₀ →ₗ[ℂ] Carrier D hu).toAddMonoidHom.map_finsum_of_injective
    LinearMap.inr_injective f

/-- Twisted-fixed skew is the original right coefficient. -/
theorem skew_mv (u : M₀) (a : V₀) : SkewAt μ τ (mIn u) (vIn a) := by
  intro n
  simp only [mode_mv, mode_vm, dividedTranslation, LinearMap.smul_apply, pow_m, smul_m, smul_smul]
  change mIn (∑ᶠ j, rightTerm D hu n u a j) = _
  rw [sum_m]
  apply finsum_congr
  intro j
  rfl

/-- Fixed-twisted skew follows by finite involution of the signed translation. -/
theorem skew_vm (a : V₀) (u : M₀) : SkewAt μ τ (vIn a) (mIn u) :=
  skew_reverse μ (truncation hD) τ (skew_mv hD u a)

/-- The verified fixed-fixed-twisted law for the literal orbifold field. -/
theorem defect_vvm (a b : V₀) (u : M₀) (p q r : ℤ) :
    defect μ (vIn a) (vIn b) (mIn u) p q r = 0 :=
  (defect_eq_zero_iff_borcherds μ (truncation hD) _ _ _ _ _ _).2
    (Y_borcherds_vvm D hu hD a b u p q r)

/-- The original mixed coefficient Jacobi law for the fixed-twisted-twisted order. -/
theorem defect_vmm (h24 : D.rank = 24) (a : V₀) (u v : M₀) (p q r : ℤ) :
    defect μ (vIn a) (mIn u) (mIn v) p q r = 0 := by
  have h := original_mixed_jacobi D hu hD h24 p q r a u v
  have secondFinite : Function.HasFiniteSupport (fun j : ℕ =>
      ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
        originalI D hu hD (q + r - j) u (((fixedParitySlice D hu (-1) a)[[p+j]]) v)) := by
    obtain ⟨N, tail⟩ := offset_cutoff μ (truncation hD) (vIn a) (mIn v) p
    apply (Finset.range N).finite_toSet.subset
    intro j hj
    refine Finset.mem_range.mpr (lt_of_not_ge fun hn => hj ?_)
    have hz := tail j hn
    rw [mode_vm] at hz
    have hm := LinearMap.inr_injective (hz.trans (map_zero (mIn : M₀ →ₗ[ℂ] Carrier D hu)).symm)
    dsimp only
    rw [hm, map_zero, smul_zero]
  have hzero := congrArg (vIn : V₀ →ₗ[ℂ] Carrier D hu) (sub_eq_zero.mpr h.symm)
  unfold defect product iterate
  simp only [mode_vm, mode_mm, mode_vv, smul_v, ← sum_v, ← map_sub]
  simp only [choose_cast, epsilon, smul_finsum' _ secondFinite, smul_smul, mul_comm ((-1 : ℂ)^r)]
  exact hzero.trans (map_zero _)

/-- Moving the third input of VVM to the middle uses the three mixed skew instances. -/
theorem defect_vmv (h24 : D.rank = 24) (a b : V₀) (u : M₀) (p q r : ℤ) :
    defect μ (vIn a) (mIn u) (vIn b) p q r = 0 := by
  have law := (defect_swap_last μ (truncation hD) (vIn a) (mIn u) (vIn b)
    p q r (divided_mode_translation hD h24 _) (skew_mv hD u b)
    (fun i => by rw [mode_vm]; exact skew_mv hD _ b)
    (fun i => by rw [mode_vv]; exact skew_mv hD u _)).2
  rw [law]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [defect_vvm hD a b u, map_zero]

/-- Moving the twisted input of VMV to the first position. -/
theorem defect_mvv (h24 : D.rank = 24) (u : M₀) (a b : V₀) (p q r : ℤ) :
    defect μ (mIn u) (vIn a) (vIn b) p q r = 0 := by
  rw [defect_swap_first μ (truncation hD) (skew_mv hD u a)
    (divided_state_translation hD h24), defect_vmv hD h24 a b u, smul_zero]

/-- Moving the fixed input of VMM to the middle. -/
theorem defect_mvm (h24 : D.rank = 24) (u : M₀) (a : V₀) (v : M₀) (p q r : ℤ) :
    defect μ (mIn u) (vIn a) (mIn v) p q r = 0 := by
  rw [defect_swap_first μ (truncation hD) (skew_mv hD u a)
    (divided_state_translation hD h24), defect_vmm hD h24 a u v, smul_zero]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
