/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient translation for the original fixed and negative twisted field. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldField
import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceModeTransport

/-! Translation of the original sector coefficients and their assembled field. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation

open LatticeGeneratingFieldLocality LatticeInvolution LatticeHalfFockCorrectedField
open HalfFock.LatticeHalfFockParityField OriginalOrbifoldField MixedIntertwiner
open OriginalFourMChargeCoset (originalI)
open StateFieldResidueReconstruction (integerBinomial)
open private fixedY_ncoeff from D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldField
open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private actual_translation_commutator raising translation_val from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private mixedMode mixed_mode_tail from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private rightTerm rightTerm_finite from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew

/-- The two actual sector translations act diagonally on the assembled carrier. -/
def T (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (OriginalOrbifoldField.Carrier D hu) :=
  ((fixedTranslation D).comp (LinearMap.fst ℂ _ _)).prod
    ((MixedIntertwiner.translation D hu).comp (LinearMap.snd ℂ _ _))

@[simp] theorem T_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (a : OriginalOrbifoldField.Carrier D hu) :
    T D hu a = (fixedTranslation D a.1, MixedIntertwiner.translation D hu a.2) := rfl

theorem T_vacuum (D : LatticeData) (hu : IsUnit D.G.det) :
    T D hu (vacuumState D hu) = 0 := by
  rw [T_apply, vacuumState]
  exact Prod.ext (by
    apply Subtype.ext
    exact LatticeAllStateField.translation_kills_vacuum D) (map_zero _)

private def stress (D : LatticeData) : FixedCarrier D :=
  ⟨LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D),
    (mem_fixedSpace D _).mpr
      (theta_omega_fixed D (HalfFockSpectralFiberSource.actualInverse D))⟩

private theorem stress_fixed_mode (D : LatticeData) (hu : IsUnit D.G.det) :
    fixedMode D (stress D) 0 = fixedTranslation D := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ((LatticeAllStateField.Y D (stress D).val)[[0]]) a.val =
    LatticeSugawaraConformal.translation D a.val
  have h := LatticeActualConformalState.omega_modes D
    (HalfFockSpectralFiberSource.actualInverse D) (-1)
  change (LatticeAllStateField.Y D (stress D).val)[[0]] = _ at h
  rw [h, LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D _
    (HalfFockSpectralFiberSource.actualInverse_left D hu)
    (HalfFockSpectralFiberSource.actualInverse_right D hu)]

private theorem stress_twisted_mode (D : LatticeData) (hu : IsUnit D.G.det) :
    (fixedParitySlice D hu (-1) (stress D))[[0]] = MixedIntertwiner.translation D hu :=
  rfl

private theorem zero_choose_finsum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → V) : (∑ᶠ j : ℕ, Ring.choose (0 : ℂ) j • f j) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]

private theorem zero_choose (j : ℕ) :
    integerBinomial 0 j = Ring.choose (0 : ℂ) j := by
  simpa [integerBinomial] using Ring.map_choose (Int.castRingHom ℂ) (0 : ℤ) j

private theorem zero_signed_choose (j : ℕ) :
    (-1 : ℂ)^j * Ring.choose (0 : ℂ) j = Ring.choose (0 : ℂ) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp [Ring.choose_zero_pos ℂ hj]

set_option maxHeartbeats 1000000 in
-- Comparing the fixed field and its mode requires reducing the subtype linear maps.
/-- Translation covariance of the original fixed-to-fixed block. -/
theorem vv_covariance (D : LatticeData) (n : ℤ) (a b : FixedCarrier D) :
    fixedTranslation D (fixedMode D a n b) - fixedMode D a n (fixedTranslation D b) =
      -(n : ℂ) • fixedMode D a (n-1) b := by
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, fixedY_ncoeff]
    using LinearMap.congr_fun (fixed_covariance D a n) b

set_option maxHeartbeats 1000000 in
-- Simplifying Borcherds at zero involves nested applications of the fixed field.
/-- Input translation of the fixed-to-fixed block, from its zero stress mode. -/
theorem vv_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (a b : FixedCarrier D) :
    fixedMode D (fixedTranslation D a) n b = -(n : ℂ) • fixedMode D a (n-1) b := by
  have h := (fixed_borcherds D (stress D) a b 0 n 0).2.2.2
  dsimp only at h
  simp only [zero_choose, zero_signed_choose, zero_choose_finsum,
    StateFieldResidueReconstruction.epsilon,
    zpow_zero, one_smul, Nat.cast_zero, zero_add, add_zero, sub_zero,
    fixedY_ncoeff, stress_fixed_mode D hu] at h
  exact h.trans (vv_covariance D n a b)

/-- Input translation of the actual fixed-source field on the negative sector. -/
theorem vm_translation (D : LatticeData) (hu : IsUnit D.G.det) (n : ℤ)
    (a : FixedCarrier D) (u : paritySpace D hu (-1)) :
    ((fixedParitySlice D hu (-1) (fixedTranslation D a))[[n]]) u =
      -(n : ℂ) • ((fixedParitySlice D hu (-1) a)[[n-1]]) u := by
  apply Subtype.ext
  change (correctedField D hu (LatticeSugawaraConformal.translation D a.val)).coeff
      (2*(-n-1)) u.val = -(n : ℂ) • (correctedField D hu a.val).coeff (2*(-(n-1)-1)) u.val
  rw [LatticeHalfFockOriginalTranslation.correctedField_translation_physical,
    show (2*(-n-1)+2 : ℤ) = 2*(-(n-1)-1) by ring]
  congr 1
  push_cast
  ring

/-- Translation covariance of the actual fixed-source field on the negative sector. -/
theorem vm_covariance (D : LatticeData) (hu : IsUnit D.G.det) (n : ℤ)
    (a : FixedCarrier D) (u : paritySpace D hu (-1)) :
    MixedIntertwiner.translation D hu (((fixedParitySlice D hu (-1) a)[[n]]) u) -
      ((fixedParitySlice D hu (-1) a)[[n]]) (MixedIntertwiner.translation D hu u) =
        -(n : ℂ) • ((fixedParitySlice D hu (-1) a)[[n-1]]) u := by
  apply Subtype.ext
  rw [Submodule.coe_sub, translation_val, Submodule.coe_smul]
  change raising D hu ((correctedField D hu a.val).coeff (2*(-n-1)) u.val) -
    (correctedField D hu a.val).coeff (2*(-n-1))
    (MixedIntertwiner.translation D hu u).val =
    -(n : ℂ) • (correctedField D hu a.val).coeff (2*(-(n-1)-1)) u.val
  rw [translation_val]
  have h := actual_translation_commutator D hu a.val (-n-1) u.val
  rw [show (2*(-n-1)+2 : ℤ) = 2*(-(n-1)-1) by ring,
    show ((-n-1 : ℤ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at h
  exact h

/-- The grade-wise inverse pairing carries input translation to the actual
twisted-to-fixed block. -/
theorem mm_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (n : ℤ) (u v : paritySpace D hu (-1)) :
    originalI D hu hD n (MixedIntertwiner.translation D hu u) v =
      -(n : ℂ) • originalI D hu hD (n-1) u v := by
  unfold originalI
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    normalizedCoefficient_translation D hu h24, map_smul]

/-- Zero-mode mixed Jacobi gives covariance of the original twisted-to-fixed block. -/
theorem mm_covariance (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (n : ℤ) (u v : paritySpace D hu (-1)) :
    fixedTranslation D (originalI D hu hD n u v) -
      originalI D hu hD n u (MixedIntertwiner.translation D hu v) =
        -(n : ℂ) • originalI D hu hD (n-1) u v := by
  have h := original_mixed_jacobi D hu hD h24 0 n 0 (stress D) u v
  simp only [Int.cast_zero, zpow_zero, mul_one, zero_signed_choose, zero_choose_finsum,
    Nat.cast_zero, zero_add, add_zero, sub_zero, stress_fixed_mode D hu, stress_twisted_mode] at h
  exact h.symm.trans (mm_translation D hu hD h24 n u v)

private theorem rightTerm_raise (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (u : paritySpace D hu (-1)) (a : FixedCarrier D) (j : ℕ) :
    MixedIntertwiner.translation D hu (rightTerm D hu n u a j) =
      ((j + 1 : ℕ) : ℂ) • rightTerm D hu (n-1) u a (j+1) := by
  let t := MixedIntertwiner.translation D hu
  have raise (x : paritySpace D hu (-1)) : t ((t ^ j) x) = (t ^ (j+1)) x := by
    rw [pow_succ', Module.End.mul_apply]
  simp only [rightTerm, map_smul, Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul, smul_smul]
  rw [show n - 1 + ((j : ℤ) + 1) = n + (j : ℤ) by omega]
  rw [show MixedIntertwiner.translation D hu
    ((MixedIntertwiner.translation D hu ^ j) (mixedMode D hu (n + (j : ℤ)) a u)) = _ from
      raise (mixedMode D hu (n + (j : ℤ)) a u)]
  congr 1
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  rw [mul_inv_rev]
  field_simp

private theorem rightTerm_fixed_input (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (u : paritySpace D hu (-1)) (a : FixedCarrier D) (j : ℕ) :
    rightTerm D hu n u (fixedTranslation D a) j =
      ((n : ℂ) + (j : ℂ)) • rightTerm D hu (n-1) u a j := by
  have h : mixedMode D hu (n + (j : ℤ)) (fixedTranslation D a) u =
      -((n + (j : ℤ) : ℤ) : ℂ) • mixedMode D hu (n + (j : ℤ) - 1) a u :=
    vm_translation D hu _ a u
  simp only [rightTerm, h, map_smul, smul_smul]
  rw [show n + (j : ℤ) - 1 = n - 1 + (j : ℤ) by omega]
  congr 1
  rw [show n + (j : ℤ) + 1 = (n - 1 + (j : ℤ) + 1) + 1 by omega,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  push_cast
  ring

private theorem finsum_succ_of_tail {V : Type*} [AddCommMonoid V] (f : ℕ → V) (N : ℕ)
    (h0 : f 0 = 0) (hN : ∀ j, N ≤ j → f j = 0) :
    (∑ᶠ j, f (j+1)) = ∑ᶠ j, f j := by
  have range_sum (g : ℕ → V) (hg : ∀ j, N ≤ j → g j = 0) :
      (∑ᶠ j, g j) = ∑ j ∈ Finset.range N, g j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge fun h => hj (hg j h))
  rw [range_sum (fun j => f (j+1)) (fun j hj => hN (j+1) (by omega)), range_sum f hN]
  have h := Finset.sum_range_succ' f N
  rw [Finset.sum_range_succ, h0, hN N le_rfl, add_zero, add_zero] at h
  exact h.symm

/-- The fixed-to-negative input derivative gives covariance of the original right field. -/
theorem mv_covariance (D : LatticeData) (hu : IsUnit D.G.det) (n : ℤ)
    (u : paritySpace D hu (-1)) (a : FixedCarrier D) :
    MixedIntertwiner.translation D hu (originalRightCoefficient D hu n u a) -
      originalRightCoefficient D hu n u (fixedTranslation D a) =
        -(n : ℂ) • originalRightCoefficient D hu (n-1) u a := by
  let b := rightTerm D hu (n-1) u a
  let f := fun j : ℕ => (j : ℂ) • b j
  obtain ⟨N, hN⟩ := mixed_mode_tail D hu (n-1) a u
  have shift : (∑ᶠ j, f (j+1)) = ∑ᶠ j, f j := by
    apply finsum_succ_of_tail f N
    · simp [f]
    · intro j hj
      simp only [f, b, rightTerm, hN j hj, map_zero, smul_zero]
  have hb : Function.HasFiniteSupport b := rightTerm_finite D hu (n-1) u a
  have hf : Function.HasFiniteSupport f :=
    hb.subset (Function.support_smul_subset_right (fun j : ℕ => (j : ℂ)) b)
  have hn : Function.HasFiniteSupport (fun j => (n : ℂ) • b j) :=
    hb.subset (Function.support_smul_subset_right (fun _ => (n : ℂ)) b)
  change MixedIntertwiner.translation D hu (∑ᶠ j, rightTerm D hu n u a j) -
    (∑ᶠ j, rightTerm D hu n u (fixedTranslation D a) j) = -(n : ℂ) • ∑ᶠ j, b j
  rw [map_finsum _ (rightTerm_finite D hu n u a)]
  simp_rw [rightTerm_raise, rightTerm_fixed_input]
  change (∑ᶠ j, f (j+1)) - (∑ᶠ j : ℕ, ((n : ℂ) + (j : ℂ)) • b j) =
    -(n : ℂ) • ∑ᶠ j, b j
  rw [shift]
  simp_rw [add_smul]
  rw [finsum_add_distrib hn hf, ← smul_finsum' (n : ℂ) hb, neg_smul]
  abel

/-- The mixed commutator carries input translation through the original right sum. -/
theorem mv_translation (D : LatticeData) (hu : IsUnit D.G.det) (n : ℤ)
    (u : paritySpace D hu (-1)) (a : FixedCarrier D) :
    originalRightCoefficient D hu n (MixedIntertwiner.translation D hu u) a =
      -(n : ℂ) • originalRightCoefficient D hu (n-1) u a := by
  let t := MixedIntertwiner.translation D hu
  rw [← mv_covariance D hu n u a]
  change (∑ᶠ j, rightTerm D hu n (t u) a j) =
    t (∑ᶠ j, rightTerm D hu n u a j) - ∑ᶠ j, rightTerm D hu n u (fixedTranslation D a) j
  have hA := rightTerm_finite D hu n u a
  have hB := rightTerm_finite D hu n u (fixedTranslation D a)
  have htA : Function.HasFiniteSupport (fun j => t (rightTerm D hu n u a j)) :=
    hA.subset (Function.support_comp_subset (map_zero t) _)
  rw [map_finsum t hA, ← finsum_sub_distrib htA hB]
  apply finsum_congr
  intro j
  have commute (x : paritySpace D hu (-1)) : t ((t ^ j) x) = (t ^ j) (t x) := calc
    _ = (t ^ (j + 1)) x := by rw [pow_succ', Module.End.mul_apply]
    _ = _ := by rw [pow_succ, Module.End.mul_apply]
  have h : mixedMode D hu (n + (j : ℤ)) a (t u) =
      t (mixedMode D hu (n + (j : ℤ)) a u) -
        mixedMode D hu (n + (j : ℤ)) (fixedTranslation D a) u := by
    have hc : t (mixedMode D hu (n + (j : ℤ)) a u) -
          mixedMode D hu (n + (j : ℤ)) a (t u) =
        -((n + (j : ℤ) : ℤ) : ℂ) • mixedMode D hu (n + (j : ℤ) - 1) a u :=
      vm_covariance D hu _ a u
    have hd : mixedMode D hu (n + (j : ℤ)) (fixedTranslation D a) u =
        -((n + (j : ℤ) : ℤ) : ℂ) • mixedMode D hu (n + (j : ℤ) - 1) a u :=
      vm_translation D hu _ a u
    rw [hd, ← hc]
    abel
  dsimp only [rightTerm]
  rw [h, map_sub, smul_sub, map_smul, commute]

/-- The assembled field on the translated state has the coefficient of its derivative. -/
theorem Y_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (n : ℤ) (a : OriginalOrbifoldField.Carrier D hu) :
    (Y D hu hD (T D hu a))[[n]] = -(n : ℂ) • (Y D hu hD a)[[n-1]] := by
  apply LinearMap.ext
  intro b
  simp only [LinearMap.smul_apply, T_apply, Y_ncoeff_apply, vv_translation D hu,
    mm_translation D hu hD h24, vm_translation, mv_translation, Prod.smul_mk, smul_add]

/-- The commutator with the diagonal translation is the same derivative coefficient. -/
theorem Y_covariance (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (n : ℤ) (a : OriginalOrbifoldField.Carrier D hu) :
    T D hu * (Y D hu hD a)[[n]] - (Y D hu hD a)[[n]] * T D hu =
      -(n : ℂ) • (Y D hu hD a)[[n-1]] := by
  apply LinearMap.ext
  intro b
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    T_apply, Y_ncoeff_apply]
  apply Prod.ext
  · simp only [Prod.fst_sub, Prod.smul_fst, map_add, smul_add]
    rw [← vv_covariance, ← mm_covariance D hu hD h24]
    abel
  · simp only [Prod.snd_sub, Prod.smul_snd, map_add, smul_add]
    rw [← vm_covariance, ← mv_covariance]
    abel

#print axioms T
#print axioms T_apply
#print axioms T_vacuum
#print axioms vv_covariance
#print axioms vv_translation
#print axioms vm_translation
#print axioms vm_covariance
#print axioms mm_translation
#print axioms mm_covariance
#print axioms mv_covariance
#print axioms mv_translation
#print axioms Y_translation
#print axioms Y_covariance

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation
