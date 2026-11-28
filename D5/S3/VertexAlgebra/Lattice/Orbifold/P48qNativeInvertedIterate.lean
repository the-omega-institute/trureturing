/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeInvertedIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeInvertedIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite inversion coefficients of the actual untwisted P48q source iterate. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSourceMobius
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeAllStateField (Y)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qNativeSourceMobius (sourceLOne_dividedAd_modes)
open P48qTwistedChargeAction (lattice)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (integerBinomial)

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

-- Left multiplication is the sum of the adjoint and right multiplication.
-- The binomial coefficient converts the total factorial to the two factorials.
private theorem dividedTranslation_apply_end {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T A : Module.End ℂ V) (b : V) (r : ℕ) :
    dividedTranslation T r (A b) =
      ∑ j ∈ Finset.range (r + 1),
        (dividedTranslation (LieAlgebra.ad ℂ (Module.End ℂ V) T) (r - j) A)
          (dividedTranslation T j b) := by
  let right : Module.End ℂ (Module.End ℂ V) := LinearMap.mulRight ℂ T
  let ad : Module.End ℂ (Module.End ℂ V) := LieAlgebra.ad ℂ (Module.End ℂ V) T
  have hAd : ad = LinearMap.mulLeft ℂ T - right := by
    apply LinearMap.ext
    intro X
    simp only [ad, right, LieAlgebra.ad_apply, Ring.lie_def, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  have hCommute : Commute right ad := by
    rw [hAd]
    exact (LinearMap.commute_mulLeft_right (R := ℂ) T T).symm.sub_right (Commute.refl right)
  have hSplit : right + ad = LinearMap.mulLeft ℂ T := by
    rw [add_comm right ad, hAd, sub_add_cancel]
  have expansion := LinearMap.congr_fun (hCommute.add_pow r) A
  rw [hSplit] at expansion
  have evaluated := LinearMap.congr_fun expansion b
  simp only [right, ad, LinearMap.pow_mulLeft, LinearMap.pow_mulRight,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply,
    Module.End.natCast_apply, LinearMap.sum_apply, ← Nat.cast_smul_eq_nsmul ℂ,
    map_smul, LinearMap.smul_apply] at evaluated
  simp only [dividedTranslation, LinearMap.smul_apply]
  rw [evaluated, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hFactorial (k : ℕ) : (k.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [map_smul, smul_smul]
  rw [Nat.cast_choose ℂ hjr]
  congr 1
  field_simp [hFactorial] <;> ring

private theorem dividedTranslation_mode_of_dividedAd {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Module.End ℂ V) (T : Module.End ℂ W)
    (mode : ℤ → V →ₗ[ℂ] Module.End ℂ W) (a : V) (b : W) (d m : ℤ)
    (expand : ∀ n : ℕ,
      dividedTranslation (LieAlgebra.ad ℂ (Module.End ℂ W) T) n (mode m a) =
        ∑ i ∈ Finset.range (n + 1),
          ((i.factorial : ℂ)⁻¹ * integerBinomial (2 * d - m - (i : ℤ) - 2) (n - i)) •
            mode (m + (n : ℤ) - (i : ℤ)) ((S ^ i) a)) (r : ℕ) :
    dividedTranslation T r (mode m a b) =
      ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r - i + 1),
        integerBinomial (2 * d - m - (i : ℤ) - 2) (r - i - j) •
          mode (m + (r : ℤ) - (i : ℤ) - (j : ℤ)) (dividedTranslation S i a)
            (dividedTranslation T j b) := by
  let term := fun i j : ℕ =>
    integerBinomial (2 * d - m - (i : ℤ) - 2) (r - i - j) •
      mode (m + (r : ℤ) - (i : ℤ) - (j : ℤ)) (dividedTranslation S i a)
        (dividedTranslation T j b)
  change _ = ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r - i + 1), term i j
  rw [dividedTranslation_apply_end T (mode m a) b r]
  calc
    _ = ∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (r - j + 1), term i j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have expansion := LinearMap.congr_fun (expand (r - j))
        (dividedTranslation T j b)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply] at expansion
      rw [expansion]
      apply Finset.sum_congr rfl
      intro i _
      have hMode : m + ((r - j : ℕ) : ℤ) - (i : ℤ) =
          m + (r : ℤ) - (i : ℤ) - (j : ℤ) := by omega
      have hOrder : r - j - i = r - i - j := by omega
      dsimp only [term]
      rw [hMode, hOrder,
        show dividedTranslation S i a = (i.factorial : ℂ)⁻¹ • (S ^ i) a from rfl]
      simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
    _ = _ := by
      apply Finset.sum_comm' (f := fun j i => term i j)
      intro j i
      simp only [Finset.mem_range]
      omega

/-- Finite inversion of the actual `m`th source iterate at divided order `r`.
For `b` of weight `e`, this is the coefficient of
`x^(-m-1) y^(r-2*(d+e-m-1))` after removing `(-1)^(d+e-m-1)` from
`C(y)Y(a,x)b = Y(C(y+x)a, (y+x)^(-1)-y^(-1)) C(y)b`.
On the right the mode is `q = m + n`, where `n` is the order in `x/y`
and `i + j + n = r`. The relative sign gives the scalar
`(-1)^n choose(i-2*d+m+n+1,n) = choose(2*d-m-i-2,n)` by negative binomial
reflection. The finite vector identity holds for arbitrary `b`. -/
theorem sourceLOne_divided_inverted_iterate (a b : Carrier lattice) (d : ℤ)
    (ha : L₀ a = (d : ℂ) • a) (m : ℤ) (r : ℕ) :
    dividedTranslation L₁ r (((Y lattice a)[[m]]) b) =
      ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r - i + 1),
        integerBinomial (2 * d - m - (i : ℤ) - 2) (r - i - j) •
          ((Y lattice (dividedTranslation L₁ i a))[[m + (r : ℤ) - (i : ℤ) - (j : ℤ)]])
            (dividedTranslation L₁ j b) := by
  let mode (q : ℤ) : Carrier lattice →ₗ[ℂ] Module.End ℂ (Carrier lattice) :=
    (LinearMap.proj q).comp (VertexOperator.ncoeff.comp (Y lattice))
  exact dividedTranslation_mode_of_dividedAd L₁ L₁ mode a b d m
    (sourceLOne_dividedAd_modes a d ha m) r

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate
