/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed monomial multiplication for native formal series. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentFiber
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
/-! Native monomial multiplication is a signed coefficient translation. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.SupportedFinalCovariance
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open SupportedChannelSeries ThreeFieldFinalLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The two colliding native coordinates, with a fixed signed spectator. -/
def finalSlice {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (z : ℤ) : MvPowerSeries (Fin 2) R :=
  fun d => signedExtend P ![(d 0 : ℤ), (d 1 : ℤ), z]

private theorem finalSlice_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (a b : ℕ) (z : ℤ) :
    MvPowerSeries.coeff (powerIndex a b) (finalSlice P z) =
      signedExtend P ![(a : ℤ), (b : ℤ), z] := by
  simp [MvPowerSeries.coeff_apply, finalSlice, powerIndex]

private theorem finalSlice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℤ) :
    extend (finalSlice P z) x y = signedExtend P ![x, y, z] := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [extend, if_pos ⟨hx, hy⟩, finalSlice_coeff]
      simp [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]
    · have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i := fun h => hy (h 1)
      simp [extend, signedExtend, hy, hn]
  · have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i := fun h => hx (h 0)
    simp [extend, signedExtend, hx, hn]

private theorem native_nat {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℕ) :
    signedExtend P ![(x : ℤ), (y : ℤ), (z : ℤ)] =
      MvPowerSeries.coeff (index3 x y z) P := by
  have hn : ∀ i : Fin 3,
      0 ≤ (![(x : ℤ), (y : ℤ), (z : ℤ)] : Fin 3 → ℤ) i := by
    intro i
    fin_cases i <;> simp
  rw [signedExtend, if_pos hn]
  congr 1
  ext i
  fin_cases i <;> simp [signedIndex, index3]

private theorem finalSlice_collision {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℤ) :
    extend (collision (finalSlice P z)) x y =
      signedExtend (finalCollision P) ![x, y, z] := by
  classical
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [extend, if_pos ⟨hx, hy⟩, collision_coeff]
      simp_rw [finalSlice_coeff]
      by_cases hz : 0 ≤ z
      · have ee : (![x, y, z] : Fin 3 → ℤ) =
            ![(x.toNat : ℤ), (y.toNat : ℤ), (z.toNat : ℤ)] := by
          funext i
          fin_cases i <;> simp [Int.toNat_of_nonneg hx,
            Int.toNat_of_nonneg hy, Int.toNat_of_nonneg hz]
        rw [ee, native_nat, finalCollision_coeff]
        apply Finset.sum_congr rfl
        intro d hd
        apply congrArg (fun v : R => ((x.toNat + d).choose x.toNat : ℂ) • v)
        change signedExtend P ![((x.toNat + d : ℕ) : ℤ),
          ((y.toNat - d : ℕ) : ℤ), z] = _
        simpa only [Int.toNat_of_nonneg hz] using
          (native_nat P (x.toNat + d) (y.toNat - d) z.toNat)
      · have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i := fun h => hz (h 2)
        rw [signedExtend, if_neg hn]
        apply Finset.sum_eq_zero
        intro d hd
        change _ • signedExtend P ![((x.toNat + d : ℕ) : ℤ),
          ((y.toNat - d : ℕ) : ℤ), z] = 0
        have hn' : ¬ ∀ i : Fin 3, 0 ≤
            (![((x.toNat + d : ℕ) : ℤ), ((y.toNat - d : ℕ) : ℤ), z] : Fin 3 → ℤ) i :=
          fun h => hz (h 2)
        rw [signedExtend, if_neg hn', smul_zero]
    · have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i := fun h => hy (h 1)
      simp [extend, signedExtend, hy, hn]
  · have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i := fun h => hx (h 0)
    simp [extend, signedExtend, hx, hn]

/-- The existing signed collision theorem at N=A=B=0, in final coordinates.
All signed targets and negative spectator coefficients are included. -/
theorem signed_final_transform {R : Type*} [CommRing R] [Algebra ℂ R]
    (M : ℤ → ℤ → ℤ → R) (P : MvPowerSeries (Fin 3) R)
    (common : ∀ b s z : ℤ, M b s z = signedExtend P ![s, b, z])
    (x y z : ℤ) :
    (∑ i ∈ Finset.range (y.toNat + 1),
      (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) • M (y - i) (x + i) z) =
      signedExtend (finalCollision P) ![x, y, z] := by
  have lower (s b : ℤ) (hb : b < -(0 : ℤ)) : M b s z = 0 := by
    rw [common]
    apply if_neg
    intro h
    have := h 1
    change 0 ≤ b at this
    omega
  have matchNative (s b : ℤ) :
      clear 0 (fun s b => M b s z) (s - (0 : ℤ)) (b - (0 : ℤ)) =
        extend (finalSlice P z) s b := by
    simpa [clear, finalSlice_extend] using common b s z
  have signed := signed_cleared_collision (fun s b => M b s z)
    0 0 0 lower (finalSlice P z) matchNative x y
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
        M (y - i) (x + i) z) =
      ∑ i ∈ Finset.range (y.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) • M (y - i) (x + i) z := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have hiy : y < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    change _ • M (y - (i : ℤ)) (x + (i : ℤ)) z = 0
    rw [lower _ _ (by omega), smul_zero]
  rw [← finiteSum]
  have signedEq :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
        M (y - i) (x + i) z) = extend (collision (finalSlice P z)) x y := by
    simpa only [Nat.cast_zero, zero_sub, sub_zero] using signed.2
  exact signedEq.trans (finalSlice_collision P x y z)


def signedExtension {R : Type*} [CommRing R] [Algebra ℂ R] :
    MvPowerSeries (Fin 3) R →ₗ[ℂ] Distribution 3 R where
  toFun := signedExtend
  map_add' P Q := by
    funext e
    by_cases he : ∀ i, 0 ≤ e i <;> simp [signedExtend, he] <;> rfl
  map_smul' c P := by
    funext e
    by_cases he : ∀ i, 0 ≤ e i <;> simp [signedExtend, he] <;> rfl

private theorem signed_monomial_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (d : Fin 3 →₀ ℕ) (e : Exponent 3) :
    signedExtend (MvPowerSeries.monomial d 1 * P) e =
      signedExtend P (fun i => e i - d i) := by
  classical
  by_cases he : ∀ i, 0 ≤ e i
  · rw [signedExtend, if_pos he]
    change MvPowerSeries.coeff (signedIndex e) (MvPowerSeries.monomial d 1 * P) = _
    rw [mul_comm, MvPowerSeries.coeff_mul_monomial]
    by_cases hd : d ≤ signedIndex e
    · rw [if_pos hd, mul_one, signedExtend,
        if_pos (show ∀ i, 0 ≤ e i - d i by
          intro i
          have hi := hd i
          change d i ≤ (e i).toNat at hi
          have := Int.toNat_of_nonneg (he i)
          omega)]
      apply congrArg P
      ext i
      change (e i).toNat - d i = (e i - d i).toNat
      have hi := hd i
      change d i ≤ (e i).toNat at hi
      omega
    · rw [if_neg hd]
      symm
      apply if_neg
      intro hs
      apply hd
      intro i
      change d i ≤ (e i).toNat
      have hi : 0 ≤ e i - (d i : ℤ) := hs i
      have hei := he i
      omega
  · have hs : ¬ ∀ i, 0 ≤ e i - d i := by
      intro hs
      apply he
      intro i
      have hi : 0 ≤ e i - (d i : ℤ) := hs i
      omega
    simp only [signedExtend, if_neg he, if_neg hs]

/-- A native nonnegative monomial is an actual signed translation. -/
theorem signed_X_pow_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (i : Fin 3) (n : ℕ) (e : Exponent 3) :
    signedExtend (MvPowerSeries.X i ^ n * P) e =
      signedExtend P (e - n • Pi.single i 1) := by
  rw [MvPowerSeries.X_pow_eq, signed_monomial_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp [nsmul_eq_mul]
  · simp [Pi.single_apply, h, Ne.symm h, Finsupp.single_eq_of_ne h]

theorem signed_extra_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (A B : ℕ) (x y z : ℤ) :
    signedExtend (((MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ A *
      MvPowerSeries.X 1 ^ B) * P) ![x, y, z] =
      ∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
        signedExtend P ![x - h, y - B - A + h, z] := by
  classical
  have expand : (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) ^ A =
      ∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
        (MvPowerSeries.X 0 ^ h * MvPowerSeries.X 1 ^ (A - h)) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro h hh
    simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
  rw [expand]
  simp only [Finset.sum_mul, smul_mul_assoc]
  change signedExtension (∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
    (((MvPowerSeries.X 0 ^ h * MvPowerSeries.X 1 ^ (A - h)) *
      MvPowerSeries.X 1 ^ B) * P)) ![x, y, z] = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro h hh
  have hhA : h ≤ A := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun v : R => (A.choose h : ℂ) • v)
  change signedExtend _ _ = _
  rw [mul_assoc, mul_assoc, signed_X_pow_mul, signed_X_pow_mul, signed_X_pow_mul]
  apply congrArg (signedExtend P)
  funext i
  fin_cases i <;> simp [nsmul_eq_mul, Nat.cast_sub hhA, Pi.single_apply, Matrix.vecHead, Matrix.vecTail] <;> omega

/-- Removing y^B is a signed translation. Removing (x+y)^A uses the existing
finite supported inverse, with the SAME genuine x support bound on both sides.
This theorem has no unrestricted-polynomial cancellation premise. -/
theorem remove_supported_extra {R : Type*} [CommRing R] [Algebra ℂ R]
    (G H : ℤ → ℤ → ℤ → R) (A B U : ℕ)
    (lowerG : ∀ x y z : ℤ, x < -(U : ℤ) → G x y z = 0)
    (lowerH : ∀ x y z : ℤ, x < -(U : ℤ) → H x y z = 0)
    (extra : ∀ x y z : ℤ,
      (∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
        G (x - h) (y - B - A + h) z) =
      ∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
        H (x - h) (y - B - A + h) z)
    (x y z : ℤ) : G x y z = H x y z := by
  have cleared (s q : ℤ) :
      positiveClear A (fun s q => G s q z) s q =
      positiveClear A (fun s q => H s q z) s q := by
    have h := extra s (q + B + A) z
    simpa only [positiveClear, show q + B + A - B - A = q by omega,
      sub_add_eq_sub_sub, add_sub_cancel_right] using h
  by_cases hx : 0 ≤ x + U
  · rw [supported_positive_reconstruction (fun s q => G s q z) A U
        (fun s q hs => lowerG s q z hs) x y hx,
      supported_positive_reconstruction (fun s q => H s q z) A U
        (fun s q hs => lowerH s q z hs) x y hx]
    apply Finset.sum_congr rfl
    intro j hj
    rw [cleared]
  · rw [lowerG x y z (by omega), lowerH x y z (by omega)]

end
end D5.S3.VertexAlgebra.SupportedFinalCovariance
