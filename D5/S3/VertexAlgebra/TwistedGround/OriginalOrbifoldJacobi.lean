/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered Borcherds identities for the original fixed and negative twisted modes. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

/-! Ordered coefficient Jacobi laws on the original two-sector orbifold carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldJacobi

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution HalfFock.LatticeHalfFockParityField
open OriginalOrbifoldField OriginalOrbifoldTranslation
open OriginalFourMChargeCoset (originalI originalJacobi)
open private jacobiLeftTerm jacobiFirstTerm jacobiSecondTerm from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
open MixedIntertwiner (originalRightCoefficient original_mixed_jacobi)
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private support_subset_range finsum_range offset_cutoff from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
open private epsilon_add epsilon_nat sign_square from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
open private rightTerm from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

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
  rw [Y_twisted_ncoeff_apply, map_zero]
  rfl

private theorem mode_mm (n : ℤ) (u v : M₀) :
    μ n (mIn u) (mIn v) = vIn (originalI D hu hD n u v) := by
  change ((Y D hu hD (0, u))[[n]]) (0, v) = _
  rw [Y_twisted_ncoeff_apply, map_zero]
  rfl

private theorem truncation : LowerTruncated μ :=
  lowerTruncated_modesOfStateField (Y D hu hD)

private theorem pow_v (j : ℕ) (a : V₀) :
    (τ ^ j) ((vIn a : Carrier D hu)) = vIn ((fixedTranslation D ^ j) a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    change (_, MixedIntertwiner.translation D hu 0) = (_, (0 : M₀))
    rw [map_zero]
    rfl

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

/-- Fixed-fixed skew transports the actual fixed vertex algebra skew identity. -/
theorem skew_vv (a b : V₀) : SkewAt μ τ (vIn a) (vIn b) := by
  intro n
  have h := (StateField.SkewSymmetry.skew_symmetry (fixed_actualVertexAlgebra D) a b).1 n
  change _ ∧ ((fixedY D a)[[n]]) b = _ at h
  simp only [mode_vv, dividedTranslation, LinearMap.smul_apply, pow_v, smul_v, smul_smul]
  have fixedCoeff (x y : V₀) (k : ℤ) : fixedMode D x k y = ((fixedY D x)[[k]]) y :=
    (LinearMap.congr_fun (fixedField_ncoeff D x k) y).symm
  rw [fixedCoeff, h.2, sum_v]
  apply finsum_congr
  intro j
  rw [fixedCoeff, div_eq_mul_inv]
  rfl


/-- The fixed-only identity is the fixed vertex algebra law. -/
theorem defect_vvv (a b c : V₀) (p q r : ℤ) :
    defect μ (vIn a) (vIn b) (vIn c) p q r = 0 := by
  let ν := modesOfStateField (fixedY D)
  have fixed := (defect_eq_zero_iff_borcherds ν (lowerTruncated_modesOfStateField (fixedY D))
    a b c p q r).2 (fixed_borcherds D a b c p q r)
  have coeff (n : ℤ) (x y : V₀) : fixedMode D x n y = ν n x y :=
    (LinearMap.congr_fun (fixedField_ncoeff D x n) y).symm
  unfold defect product iterate at fixed ⊢
  simpa only [mode_vv, coeff, smul_v, ← sum_v, ← map_sub, map_zero]
    using congrArg (vIn : V₀ →ₗ[ℂ] Carrier D hu) fixed

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


/-- The exact remaining three-twisted coefficient law, at every integer index. -/
def OriginalMMM : Prop :=
  ∀ (p q r : ℤ) (u v w : M₀), originalJacobi D hu hD p q r u v w

/-- Joint faithfulness of the original fixed-sector modes on the negative sector. -/
def FixedActionFaithful (D : LatticeData) (hu : IsUnit D.G.det) : Prop :=
  ∀ a : FixedCarrier D,
    (∀ (n : ℤ) (u : paritySpace D hu (-1)), ((fixedParitySlice D hu (-1) a)[[n]]) u = 0) →
    a = 0

/-- The literal three-twisted defect vanishes exactly when the original coefficient law holds. -/
theorem defect_mmm_iff (u v w : M₀) (p q r : ℤ) :
    defect μ (mIn u) (mIn v) (mIn w) p q r = 0 ↔
      originalJacobi D hu hD p q r u v w := by
  unfold defect product iterate originalJacobi jacobiLeftTerm jacobiFirstTerm jacobiSecondTerm
  simp only [mode_mm, mode_mv, mode_vm, smul_m, ← sum_m, ← map_sub, choose_cast,
    zpow_natCast, epsilon]
  rw [smul_finsum]
  simp only [smul_smul, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  have sign (j : ℕ) :
      (-1 : ℂ)^r * ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) =
        ((-1 : ℂ)^j * (-1 : ℂ)^r) * Ring.choose (r : ℂ) j := by ac_rfl
  simp only [sign, mixedMode]
  rw [← map_zero (mIn : M₀ →ₗ[ℂ] Carrier D hu), LinearMap.inr_injective.eq_iff,
    sub_eq_zero, eq_comm]
  rfl

private theorem product_swap (a b c : Carrier D hu) (p q r : ℤ) :
    product μ a b c p q r - epsilon r • product μ b a c q p r =
      epsilon (r + 1) • (product μ b a c q p r - epsilon r • product μ a b c p q r) := by
  have sign : epsilon (r + 1) = -epsilon r := by
    rw [epsilon_add]
    simp [epsilon]
  rw [sign, smul_sub, neg_smul, smul_smul, neg_mul, sign_square, neg_smul, one_smul]
  abel

set_option maxHeartbeats 900000 in
-- Elaborating the summed mode action uses the concrete mixed-carrier linear maps.
/-- Comparing the two ordered MMM iterates on the faithful twisted sector gives MM skew. -/
theorem skew_mm (h24 : D.rank = 24) (mmm : OriginalMMM (hu := hu) hD)
    (faithful : FixedActionFaithful D hu) (u v : M₀) : SkewAt μ τ (mIn u) (mIn v) := by
  intro r
  let c := fun j : ℕ => originalI D hu hD (r + j) v u
  let f := fun j : ℕ => epsilon (r + j + 1) • dividedTranslation (fixedTranslation D) j (c j)
  have embed (j : ℕ) :
      epsilon (r + j + 1) • dividedTranslation τ j (μ (r + j) (mIn v) (mIn u)) =
        vIn (f j) := by
    simp only [mode_mm, dividedTranslation, LinearMap.smul_apply, pow_v, smul_v, f, c]
  simp_rw [embed, ← sum_v]
  rw [mode_mm]
  apply congrArg (vIn : V₀ →ₗ[ℂ] Carrier D hu)
  apply sub_eq_zero.mp
  apply faithful
  intro q w
  obtain ⟨N, tail⟩ := offset_cutoff μ (truncation hD) (mIn v) (mIn u) r
  have finite : Function.HasFiniteSupport f := by
    apply (Finset.range N).finite_toSet.subset
    apply support_subset_range
    intro j hj
    have h := tail j hj
    rw [mode_mm] at h
    have hz := LinearMap.inl_injective (h.trans (map_zero (vIn : V₀ →ₗ[ℂ] Carrier D hu)).symm)
    simp only [f, c, hz, map_zero, smul_zero]
  have finiteIn : Function.HasFiniteSupport (fun j => (vIn (f j) : Carrier D hu)) :=
    finite.subset (Function.support_comp_subset (map_zero (vIn : V₀ →ₗ[ℂ] Carrier D hu)) f)
  have lhs : iterate μ (mIn u) (mIn v) (mIn w) 0 q r =
      μ q (μ r (mIn u) (mIn v)) (mIn w) := by
    unfold iterate
    rw [finsum_eq_single _ 0]
    · simp [choose_cast]
    · intro j hj
      simp [choose_cast, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  have first := sub_eq_zero.mp ((defect_mmm_iff hD u v w 0 q r).2 (mmm 0 q r u v w))
  have second := sub_eq_zero.mp ((defect_mmm_iff hD v u w q 0 r).2 (mmm q 0 r v u w))
  have exchange : μ q (μ r (mIn u) (mIn v)) (mIn w) =
      epsilon (r+1) • iterate μ (mIn v) (mIn u) (mIn w) q 0 r := by
    rw [← lhs, ← first, ← second, product_swap]
  let eval := (μ q).flip (mIn w)
  have evaluated : μ q (vIn (∑ᶠ j, f j)) (mIn w) =
      epsilon (r+1) • iterate μ (mIn v) (mIn u) (mIn w) q 0 r := by
    change eval (vIn (∑ᶠ j, f j)) = _
    rw [sum_v, map_finsum eval finiteIn, iterate, smul_finsum]
    apply finsum_congr
    intro j
    simp only [eval, LinearMap.flip_apply, ← embed,
      map_smul, smul_smul, add_zero]
    have hs : epsilon (r + j + 1) = epsilon (r+1) * (-1 : ℂ)^j := by
      rw [show r + (j : ℤ) + 1 = (r + 1) + j by omega, epsilon_add, epsilon_nat]
    rw [hs, divided_state_translation hD h24 j q _, LinearMap.smul_apply, smul_smul,
      mul_assoc, ← mul_assoc ((-1 : ℂ)^j), ← mul_pow]
    norm_num
  rw [mode_mm] at exchange
  apply (LinearMap.inr_injective : Function.Injective (mIn : M₀ →ₗ[ℂ] Carrier D hu))
  rw [← mode_vm hD, map_sub, map_sub, LinearMap.sub_apply, exchange.trans evaluated.symm,
    sub_self, map_zero]

/-- MMV follows from MVM after the fixed action detects the MM skew identity. -/
theorem defect_mmv (h24 : D.rank = 24) (mmm : OriginalMMM (hu := hu) hD)
    (faithful : FixedActionFaithful D hu) (u v : M₀) (a : V₀) (p q r : ℤ) :
    defect μ (mIn u) (mIn v) (vIn a) p q r = 0 := by
  have law := (defect_swap_last μ (truncation hD) (mIn u) (mIn v) (vIn a)
    p q r (divided_mode_translation hD h24 _) (skew_mv hD v a)
    (fun i => by rw [mode_mm]; exact skew_vv hD _ a)
    (fun i => by rw [mode_mv]; exact skew_mm hD h24 mmm faithful v _)).2
  rw [law]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [defect_mvm hD h24 u a v, map_zero]


section Additivity

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  (μ' : Modes W) (trunc : LowerTruncated μ')

include trunc

private theorem product_finite (a b c : W) (p q r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ => (((-1 : ℂ)^i) * integerBinomial r i) •
      μ' (p + r - i) a (μ' (q + i) b c)) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ' trunc b c q
  apply (Finset.range N).finite_toSet.subset (support_subset_range ?_)
  intro i hi
  simp only [tail i hi, map_zero, smul_zero]

private theorem iterate_finite (a b c : W) (p q r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      integerBinomial p i • μ' (p + q - i) (μ' (r + i) a b) c) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ' trunc a b r
  apply (Finset.range N).finite_toSet.subset (support_subset_range ?_)
  intro i hi
  simp only [tail i hi, map_zero, LinearMap.zero_apply, smul_zero]

private theorem defect_add_first (a a' b c : W) (p q r : ℤ) :
    defect μ' (a + a') b c p q r = defect μ' a b c p q r + defect μ' a' b c p q r := by
  simp only [defect, product, iterate, map_add, LinearMap.add_apply, smul_add,
    finsum_add_distrib (product_finite μ' trunc a b c p q r) (product_finite μ' trunc a' b c p q r),
    finsum_add_distrib (product_finite μ' trunc b a c q p r) (product_finite μ' trunc b a' c q p r),
    finsum_add_distrib (iterate_finite μ' trunc a b c p q r) (iterate_finite μ' trunc a' b c p q r)]
  abel

private theorem defect_add_second (a b b' c : W) (p q r : ℤ) :
    defect μ' a (b + b') c p q r = defect μ' a b c p q r + defect μ' a b' c p q r := by
  simp only [defect, product, iterate, map_add, LinearMap.add_apply, smul_add,
    finsum_add_distrib (product_finite μ' trunc a b c p q r) (product_finite μ' trunc a b' c p q r),
    finsum_add_distrib (product_finite μ' trunc b a c q p r) (product_finite μ' trunc b' a c q p r),
    finsum_add_distrib (iterate_finite μ' trunc a b c p q r) (iterate_finite μ' trunc a b' c p q r)]
  abel

private theorem defect_add_third (a b c c' : W) (p q r : ℤ) :
    defect μ' a b (c + c') p q r = defect μ' a b c p q r + defect μ' a b c' p q r := by
  simp only [defect, product, iterate, map_add, smul_add,
    finsum_add_distrib (product_finite μ' trunc a b c p q r) (product_finite μ' trunc a b c' p q r),
    finsum_add_distrib (product_finite μ' trunc b a c q p r) (product_finite μ' trunc b a c' q p r),
    finsum_add_distrib (iterate_finite μ' trunc a b c p q r) (iterate_finite μ' trunc a b c' p q r)]
  abel

end Additivity

set_option maxHeartbeats 900000 in
-- Expanding the three carrier sums generates all eight ordered sector cases.
/-- The literal MMM identity and faithful fixed action imply all ordered identities. -/
theorem defect_all (h24 : D.rank = 24) (mmm : OriginalMMM (hu := hu) hD)
    (faithful : FixedActionFaithful D hu) (a b c : Carrier D hu) (p q r : ℤ) :
    defect μ a b c p q r = 0 := by
  have split (x : Carrier D hu) : x = vIn x.1 + mIn x.2 := by
    ext <;> simp
  conv_lhs =>
    arg 2
    rw [split a]
  conv_lhs =>
    arg 3
    rw [split b]
  conv_lhs =>
    arg 4
    rw [split c]
  simp only [defect_add_first μ (truncation hD), defect_add_second μ (truncation hD),
    defect_add_third μ (truncation hD), defect_vvv hD, defect_vvm hD, defect_vmv hD h24,
    defect_mvv hD h24, defect_vmm hD h24, defect_mvm hD h24, defect_mmv hD h24 mmm faithful,
    fun u v w p q r => (defect_mmm_iff hD u v w p q r).2 (mmm p q r u v w), add_zero]

#print axioms divided_state_translation
#print axioms divided_mode_translation
#print axioms skew_mv
#print axioms skew_vm
#print axioms skew_vv
#print axioms defect_vvv
#print axioms defect_vvm
#print axioms defect_vmv
#print axioms defect_mvv
#print axioms defect_vmm
#print axioms defect_mvm
#print axioms defect_mmm_iff
#print axioms skew_mm
#print axioms defect_mmv
#print axioms defect_all

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldJacobi
