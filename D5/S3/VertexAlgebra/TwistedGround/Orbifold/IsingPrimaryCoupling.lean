/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ward and null-vector selection for original two-twisted Ising primary coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsingHighestWeight
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSourceModeTransport
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

/-! For a norm-four Ising axis, the original mixed Jacobi law determines the
detected coefficients with an odd input descended by mode minus one or minus
two. The actual odd null laws then restrict the three primary weights. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeInvolution (FixedCarrier fixedMode)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.NormFourFirstGradeSpectrum (normFourFixedSource)
open MixedIntertwiner (original_mixed_jacobi)
open OriginalFourMChargeCoset (originalI)
open private originalI_tail from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
open scoped BigOperators VertexOperator

variable {D : LatticeData} {hu : IsUnit D.G.det}
  {hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))}
  {a : Charge D} {s : ℂ}

local notation "Odd" => paritySpace D hu (-1)
local notation "𝑒" => normFourFixedSource D a s
local notation "𝒜" => (fun m : ℤ => fixedMode D 𝑒 (m + 1))
local notation "ℬ" => oddAxisMode D hu a s
local notation "𝓘" => originalI D hu hD

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) := (paritySpace D hu (-1)).addCommGroup

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    Module ℂ (paritySpace D hu (-1)) := (paritySpace D hu (-1)).module

local instance (D : LatticeData) :
    AddCommGroup (FixedCarrier D) := (LatticeInvolution.fixedSpace D).addCommGroup

local instance (D : LatticeData) :
    Module ℂ (FixedCarrier D) := (LatticeInvolution.fixedSpace D).module

private theorem isingFinsumChooseZero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → V) :
    (∑ᶠ j : ℕ, Ring.choose (0 : ℂ) j • f j) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp only [Ring.choose_zero_right, one_smul]
  · intro j hj
    rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), zero_smul]

private theorem isingSignedChooseZero (j : ℕ) :
    (-1 : ℂ)^j * Ring.choose (0 : ℂ) j = Ring.choose (0 : ℂ) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, one_mul]
  · rw [Ring.choose_zero_pos ℂ hj, mul_zero]

private theorem isingFinsumChooseOne {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → V) :
    (∑ᶠ j : ℕ, Ring.choose (1 : ℂ) j • f j) = f 0 + f 1 := by
  have tail (j : ℕ) (hj : 2 ≤ j) : Ring.choose (1 : ℂ) j • f j = 0 := by
    have hzero : Ring.choose (1 : ℂ) j = 0 := by
      rw [← Nat.cast_one, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show 1 < j by omega),
        Nat.cast_zero]
    rw [hzero, zero_smul]
  have support : Function.support (fun j => Ring.choose (1 : ℂ) j • f j) ⊆
      Finset.range 2 := fun j hj =>
    Finset.mem_range.mpr (lt_of_not_ge fun hj' => hj (tail j hj'))
  rw [finsum_eq_sum_of_support_subset _ support]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Ring.choose_zero_right, Ring.choose_one_right, one_smul]

private theorem isingSignedChooseNegOne (j : ℕ) :
    (-1 : ℂ)^j * Ring.choose (-1 : ℂ) j = 1 := by
  have hc : StateFieldResidueReconstruction.integerBinomial (-1) j =
      Ring.choose (-1 : ℂ) j := by
    simpa [StateFieldResidueReconstruction.integerBinomial] using
      Ring.map_choose (Int.castRingHom ℂ) (-1 : ℤ) j
  simpa only [hc] using LatticeActualStateFieldCalculus.minus_one_binomial j

variable (h24 : D.rank = 24) (ell : FixedCarrier D →ₗ[ℂ] ℂ) {h3 : ℂ}
variable (ell0 : ∀ z : FixedCarrier D,
    ell (fixedMode D (normFourFixedSource D a s) 1 z) = h3 * ell z)
variable (ellNeg : ∀ k : ℤ, k < 0 → ∀ z : FixedCarrier D,
    ell (fixedMode D (normFourFixedSource D a s) (k + 1) z) = 0)

include h24 ell0 in
private theorem isingWardOne (n : ℤ) (x y : Odd) {hx hy : ℂ}
    (hx0 : ℬ 0 x = hx • x) (hy0 : ℬ 0 y = hy • y) :
    ell (𝓘 (n + 1) (ℬ (-1) x) y) = (h3 - hx - hy) * ell (𝓘 n x y) := by
  have h := original_mixed_jacobi D hu hD h24 1 n 0 𝑒 x y
  simp only [Int.cast_one, Int.cast_zero, zpow_zero, mul_one,
    isingSignedChooseZero, isingFinsumChooseZero, isingFinsumChooseOne,
    Nat.cast_zero, Nat.cast_one, zero_add, add_zero, sub_zero,
    show (1 : ℤ) + n = n + 1 by omega,
    show n + 1 - 1 = n by omega] at h
  change 𝓘 (n + 1) (ℬ (-1) x) y + 𝓘 n (ℬ 0 x) y =
    𝒜 0 (𝓘 n x y) - 𝓘 n x (ℬ 0 y) at h
  have paired := congrArg (fun z : FixedCarrier D => ell z) h
  have hz := ell0 (𝓘 n x y)
  simp only [map_add, map_sub, show (0 : ℤ) + 1 = 1 by decide, hz, hx0, hy0,
    map_smul, LinearMap.smul_apply, smul_eq_mul] at paired
  linear_combination paired

include h24 ellNeg in
private theorem isingWardSwap (n : ℤ) (x y : Odd) :
    ell (𝓘 n (ℬ (-1) x) y) = -ell (𝓘 n x (ℬ (-1) y)) := by
  have h := original_mixed_jacobi D hu hD h24 0 n 0 𝑒 x y
  simp only [Int.cast_zero, zpow_zero, mul_one, isingSignedChooseZero,
    isingFinsumChooseZero, Nat.cast_zero, zero_add, add_zero, sub_zero] at h
  change 𝓘 n (ℬ (-1) x) y = 𝒜 (-1) (𝓘 n x y) - 𝓘 n x (ℬ (-1) y) at h
  have paired := congrArg (fun z : FixedCarrier D => ell z) h
  have hz := ellNeg (-1) (by decide) (𝓘 n x y)
  simpa only [map_sub, hz, zero_sub] using paired

include h24 ell0 ellNeg in
private theorem isingWardTwo (n : ℤ) (x y : Odd) {hx hy : ℂ}
    (hx0 : ℬ 0 x = hx • x) (hy0 : ℬ 0 y = hy • y)
    (hyPos : ∀ k : ℤ, 0 < k → ℬ k y = 0) :
    ell (𝓘 (n + 2) (ℬ (-2) x) y) = (hx + 2 * hy - h3) * ell (𝓘 n x y) := by
  let first (j : ℕ) : FixedCarrier D :=
    fixedMode D 𝑒 (-1 - (j : ℤ)) (𝓘 (n + 2 + (j : ℤ)) x y)
  let second (j : ℕ) : FixedCarrier D :=
    (-1 : ℂ) • 𝓘 (n + 1 - (j : ℤ)) x
      (((fixedParitySlice D hu (-1) 𝑒)[[(j : ℤ)]]) y)
  have h := original_mixed_jacobi D hu hD h24 0 (n + 2) (-1) 𝑒 x y
  have hcast : ((-1 : ℤ) : ℂ) = -1 := by norm_num
  have hsign : (-1 : ℂ)^(-1 : ℤ) = -1 := by norm_num [zpow_neg_one]
  simp only [Int.cast_zero, hcast, hsign, isingFinsumChooseZero,
    isingSignedChooseNegOne, one_mul, one_smul, Nat.cast_zero, zero_add, add_zero,
    sub_zero, show n + 2 + (-1 : ℤ) = n + 1 by omega] at h
  change 𝓘 (n + 2) (ℬ (-2) x) y =
    (∑ᶠ j : ℕ, first j) - (∑ᶠ j : ℕ, second j) at h
  have finiteFirst : Function.HasFiniteSupport first := by
    obtain ⟨N, hN⟩ := originalI_tail D hu hD x y (n + 2)
    apply (Finset.range N).finite_toSet.subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hlt
    exact hj (by simp only [first, hN j (by omega), map_zero])
  have zeroFirst (j : ℕ) : ell (first j) = 0 := by
    dsimp only [first]
    rw [show (-1 : ℤ) - (j : ℤ) = (-2 - (j : ℤ)) + 1 by omega]
    exact ellNeg (-2 - (j : ℤ)) (by omega) (𝓘 (n + 2 + (j : ℤ)) x y)
  have pairedFirst : ell (∑ᶠ j : ℕ, first j) = 0 := calc
    _ = ∑ᶠ j : ℕ, ell (first j) := map_finsum ell finiteFirst
    _ = ∑ᶠ _ : ℕ, (0 : ℂ) := finsum_congr zeroFirst
    _ = 0 := finsum_zero
  have tailSecond (j : ℕ) (hj : 2 ≤ j) : second j = 0 := by
    have hyj : ((fixedParitySlice D hu (-1) 𝑒)[[(j : ℤ)]]) y = 0 := by
      simpa only [oddAxisMode, show (j : ℤ) - 1 + 1 = (j : ℤ) by omega] using
        hyPos ((j : ℤ) - 1) (by omega)
    simp only [second, hyj, map_zero, smul_zero]
  have secondEval : (∑ᶠ j : ℕ, second j) =
      (-1 : ℂ) • 𝓘 (n + 1) x (ℬ (-1) y) +
      (-1 : ℂ) • 𝓘 n x (ℬ 0 y) := by
    have support : Function.support second ⊆ Finset.range 2 := fun j hj =>
      Finset.mem_range.mpr (lt_of_not_ge fun hj' => hj (tailSecond j hj'))
    rw [finsum_eq_sum_of_support_subset _ support]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, second,
      Nat.cast_zero, Nat.cast_one, sub_zero, show n + 1 - 1 = n by omega]
    rfl
  rw [secondEval] at h
  have paired := congrArg (fun z : FixedCarrier D => ell z) h
  simp only [map_sub, pairedFirst, map_add, hy0, map_smul, smul_eq_mul] at paired
  have swap := isingWardSwap (hD := hD) (a := a) (s := s) h24 ell ellNeg (n + 1) x y
  have one := isingWardOne (hD := hD) h24 ell ell0 n x y hx0 hy0
  linear_combination paired + swap - one

include h24 ell0 ellNeg in
/-- A nonzero original two-twisted coefficient detected by a dual Ising
primary has its three weights in the Ising primary table. -/
theorem originalI_ising_primary_selection (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (n : ℤ) (u v : Odd) {h1 h2 : ℂ}
    (hu0 : ℬ 0 u = h1 • u) (hv0 : ℬ 0 v = h2 • v)
    (huPos : ∀ k : ℤ, 0 < k → ℬ k u = 0)
    (hvPos : ∀ k : ℤ, 0 < k → ℬ k v = 0)
    (wh1 : h1 = 0 ∨ h1 = 1/2 ∨ h1 = 1/16)
    (wh2 : h2 = 0 ∨ h2 = 1/2 ∨ h2 = 1/16)
    (wh3 : h3 = 0 ∨ h3 = 1/2 ∨ h3 = 1/16)
    (hne : ell (𝓘 n u v) ≠ 0) :
    (h1 = 0 ∧ h3 = h2) ∨ (h2 = 0 ∧ h3 = h1) ∨
    (h1 = 1/2 ∧ h2 = 1/2 ∧ h3 = 0) ∨
    (((h1 = 1/2 ∧ h2 = 1/16) ∨ (h1 = 1/16 ∧ h2 = 1/2)) ∧ h3 = 1/16) ∨
    (h1 = 1/16 ∧ h2 = 1/16 ∧ (h3 = 0 ∨ h3 = 1/2)) := by
  let c := ell (𝓘 n u v)
  let δ := h3 - h1 - h2
  change c ≠ 0 at hne
  have first : ell (𝓘 (n + 1) (ℬ (-1) u) v) = δ * c :=
    isingWardOne h24 ell ell0 n u v hu0 hv0
  have descend : ℬ 0 (ℬ (-1) u) = (h1 + 1) • ℬ (-1) u := by
    have hop := LinearMap.congr_fun (odd_virasoro D hu a s ha hs 0 (-1)) u
    have hcomm : ℬ 0 (ℬ (-1) u) - ℬ (-1) (ℬ 0 u) = ℬ (-1) u := by
      simpa [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        LinearMap.add_apply] using hop
    rw [hu0, map_smul] at hcomm
    calc
      _ = (ℬ 0 (ℬ (-1) u) - h1 • ℬ (-1) u) + h1 • ℬ (-1) u :=
        (sub_add_cancel _ _).symm
      _ = _ := by rw [hcomm, add_smul, one_smul, add_comm]
  have twice : ell (𝓘 (n + 2) (ℬ (-1) (ℬ (-1) u)) v) = (δ - 1) * δ * c := by
    have step := isingWardOne (hD := hD) h24 ell ell0 (n + 1) (ℬ (-1) u) v descend hv0
    rw [show n + 1 + 1 = n + 2 by omega, first] at step
    dsimp only [δ, c] at step ⊢
    linear_combination step
  have second := isingWardTwo (hD := hD) h24 ell ell0 ellNeg n u v hu0 hv0 hvPos
  have fromLevelTwo (q : ℂ) (hnull : ℬ (-2) u = q • ℬ (-1) (ℬ (-1) u)) :
      h1 + 2 * h2 - h3 = q * (δ - 1) * δ := by
    have paired := second
    simp only [hnull, map_smul, LinearMap.smul_apply, smul_eq_mul, twice] at paired
    have hprod : (h1 + 2 * h2 - h3 - q * (δ - 1) * δ) * c = 0 := by
      dsimp only [c] at paired ⊢
      linear_combination -paired
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)
  rcases wh1 with h | h | h
  · have hx : ℬ 0 u = 0 := by simpa only [h, zero_smul] using hu0
    have hnull := highest_weight_zero_level_one u ha hs hx huPos
    have paired := first
    simp only [hnull, map_zero, LinearMap.zero_apply] at paired
    have p : δ = 0 := (mul_eq_zero.mp paired.symm).resolve_right hne
    rcases wh2 with hy | hy | hy <;> rcases wh3 with hz | hz | hz <;>
      (norm_num [δ, h, hy, hz] at p <;> norm_num [h, hy, hz])
  · have hx : ℬ 0 u = (1/2 : ℂ) • u := by simpa only [h] using hu0
    have p := fromLevelTwo (3/4) (highest_weight_half_level_two u ha hs hx huPos)
    rcases wh2 with hy | hy | hy <;> rcases wh3 with hz | hz | hz <;>
      (norm_num [δ, h, hy, hz] at p <;> norm_num [h, hy, hz])
  · have hx : ℬ 0 u = (1/16 : ℂ) • u := by simpa only [h] using hu0
    have p := fromLevelTwo (4/3) (highest_weight_sixteenth_level_two u ha hs hx huPos)
    rcases wh2 with hy | hy | hy <;> rcases wh3 with hz | hz | hz <;>
      (norm_num [δ, h, hy, hz] at p <;> norm_num [h, hy, hz])

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing
