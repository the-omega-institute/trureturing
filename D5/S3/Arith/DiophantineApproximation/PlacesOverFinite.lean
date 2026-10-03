/- GID: D5/S3/Arith/DiophantineApproximation/PlacesOverFinite
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/PlacesOverFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An absolute value above a finite place is a positive power of a finite place upstairs. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Data.NNReal.Basic
import Mathlib.RingTheory.Valuation.Integral

-- Used only inside proofs.

public section

open IsDedekindDomain NumberField

namespace NumberField.FinitePlace

variable {F : Type*} [Field F] [NumberField F]

end NumberField.FinitePlace

namespace AbsoluteValue

section Ideal

variable {F : Type*} [Field F] {w : AbsoluteValue F ℝ}

/-- The algebraic integers of absolute value less than one, as an ideal of `𝓞 F`. It is the prime
that the classification below attaches to `w`. -/
def integerLtIdeal (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) : Ideal (𝓞 F) where
  carrier := {y : 𝓞 F | w (y : F) < 1}
  add_mem' {a b} ha hb := by
    have ha' : w (a : F) < 1 := ha
    have hb' : w (b : F) < 1 := hb
    change w ((a + b : 𝓞 F) : F) < 1
    refine lt_of_le_of_lt ?_ (max_lt ha' hb')
    push_cast
    exact hna (a : F) (b : F)
  zero_mem' := by change w ((0 : 𝓞 F) : F) < 1; simp
  smul_mem' c y hy := by
    have hy' : w (y : F) < 1 := hy
    change w ((c • y : 𝓞 F) : F) < 1
    rw [smul_eq_mul]
    push_cast
    rw [map_mul]
    calc w (c : F) * w (y : F) ≤ 1 * w (y : F) :=
          mul_le_mul_of_nonneg_right (hle c) (w.nonneg _)
      _ < 1 := by rw [one_mul]; exact hy'

theorem isPrime_integerLtIdeal (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) : (w.integerLtIdeal hna hle).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : 𝓞 F) ∈ w.integerLtIdeal hna hle := htop ▸ Submodule.mem_top
    change w (1 : F) < 1 at h1
    simp at h1
  · intro a b hab
    change w ((a * b : 𝓞 F) : F) < 1 at hab
    push_cast at hab
    rw [map_mul] at hab
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    change ¬ w (a : F) < 1 at ha
    change ¬ w (b : F) < 1 at hb
    have ha1 : (1 : ℝ) ≤ w (a : F) := le_of_not_gt ha
    have hb1 : (1 : ℝ) ≤ w (b : F) := le_of_not_gt hb
    nlinarith [w.nonneg (a : F), w.nonneg (b : F)]

end Ideal

variable {F : Type*} [Field F] [NumberField F] {w : AbsoluteValue F ℝ}

set_option maxHeartbeats 1000000 in
/-- **Ostrowski's theorem at a finite place**, for a number field: a nonarchimedean absolute value
that is at most `1` on the ring of integers and less than `1` somewhere on it is a positive real
power of the absolute value of a finite place. -/
theorem exists_heightOneSpectrum_rpow_eq (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) (hnt : ∃ y : 𝓞 F, y ≠ 0 ∧ w (y : F) < 1) :
    ∃ (P : HeightOneSpectrum (𝓞 F)) (t : ℝ), 0 < t ∧
      ∀ y : F, w y = FinitePlace.mk P y ^ t := by
  obtain ⟨y₀, hy₀0, hy₀1⟩ := hnt
  have hIbot : w.integerLtIdeal hna hle ≠ ⊥ := by
    intro h
    have hmem : y₀ ∈ w.integerLtIdeal hna hle := hy₀1
    rw [h, Ideal.mem_bot] at hmem
    exact hy₀0 hmem
  set P : HeightOneSpectrum (𝓞 F) :=
    ⟨w.integerLtIdeal hna hle, isPrime_integerLtIdeal hna hle, hIbot⟩ with hPdef
  have hmemP : ∀ y : 𝓞 F, y ∈ P.asIdeal ↔ w (y : F) < 1 := fun _ => Iff.rfl
  have himp : ∀ x : F, (FinitePlace.mk P).1 x < 1 → w x < 1 := by
    intro x hx
    have hx' : FinitePlace.mk P x < 1 := hx
    obtain ⟨n, d, hnd⟩ :=
      P.exists_primeCompl_mul_eq_of_integer x (((fun P x ↦ (show NumberField.FinitePlace.mk P x ≤ 1 ↔ P.valuation F x ≤ 1 from by
      rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding,
        HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_le_coe]
      exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal P))) P x).mp hx'.le)
    have hd_notin : (d : 𝓞 F) ∉ P.asIdeal := d.2
    have hwd1 : w ((d : 𝓞 F) : F) = 1 :=
      le_antisymm (hle d) (le_of_not_gt fun h => hd_notin ((hmemP _).mpr h))
    have hWd1 : FinitePlace.mk P ((d : 𝓞 F) : F) = 1 :=
      ((show NumberField.FinitePlace.mk P ((d : 𝓞 F) : F) = 1 ↔ (d : 𝓞 F) ∉ P.asIdeal from by
      rw [NumberField.FinitePlace.mk_apply]
      exact NumberField.FinitePlace.norm_eq_one_iff_notMem F P (d : 𝓞 F))).mpr hd_notin
    have hWn : FinitePlace.mk P ((n : 𝓞 F) : F) < 1 := by
      have h1 : FinitePlace.mk P x * FinitePlace.mk P ((d : 𝓞 F) : F)
          = FinitePlace.mk P ((n : 𝓞 F) : F) := by
        rw [← map_mul]; exact congrArg (FinitePlace.mk P) hnd
      rw [hWd1, mul_one] at h1
      rw [← h1]
      exact hx'
    have hwn : w ((n : 𝓞 F) : F) < 1 :=
      (hmemP _).mp (((show NumberField.FinitePlace.mk P (n : F) < 1 ↔ n ∈ P.asIdeal from by
      rw [NumberField.FinitePlace.mk_apply]
      exact NumberField.FinitePlace.norm_lt_one_iff_mem F P n)).mp hWn)
    have hxd : w x * w ((d : 𝓞 F) : F) = w ((n : 𝓞 F) : F) := by
      rw [← map_mul]; exact congrArg w hnd
    rw [hwd1, mul_one] at hxd
    rw [hxd]
    exact hwn
  have hWnt : (FinitePlace.mk P).1.IsNontrivial := by
    refine ⟨(y₀ : F), by simpa using hy₀0, ?_⟩
    exact ne_of_lt (((show NumberField.FinitePlace.mk P (y₀ : F) < 1 ↔ y₀ ∈ P.asIdeal from by
      rw [NumberField.FinitePlace.mk_apply]
      exact NumberField.FinitePlace.norm_lt_one_iff_mem F P y₀)).mpr ((hmemP _).mpr hy₀1))
  obtain ⟨t, ht, hfun⟩ := isEquiv_iff_exists_rpow_eq.mp (isEquiv_of_lt_one_imp hWnt himp)
  exact ⟨P, t, ht, fun y => (congrFun hfun y).symm⟩

end AbsoluteValue

namespace AbsoluteValue

end AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 0.1, the nonarchimedean half, with the exponent named.** An absolute value of `F`
lying over a finite place `v` of `K` is the `(e f)⁻¹`-th power of the finite place of a prime
`𝔓` of `𝓞 F` above the prime of `v`, with `e` and `f` the ramification index and the inertia
degree of `𝔓`. -/
theorem exists_finitePlace_rpow_inv_eq_of_liesOver (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal.LiesOver v.maximalIdeal.asIdeal ∧
      ∀ y : F, w y = FinitePlace.mk P y ^
        (((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹ := by
  have hres : ∀ y : K, w (algebraMap K F y) = v y :=
    fun y ↦ congrArg (fun a : AbsoluteValue K ℝ ↦ a y)
      (AbsoluteValue.LiesOver.comp_eq w v.1)
  have hint : ∀ n : ℤ, w ((n : ℤ) : F) ≤ 1 := by
    intro n
    rw [← map_intCast (algebraMap K F) n, hres]
    exact by
      rw [← v.norm_embedding_eq, FinitePlace.norm_embedding]
      exact HeightOneSpectrum.adicAbv_intCast_le_one K v.maximalIdeal n
  have hna : IsNonarchimedean (w : F → ℝ) := by
    letI : NormedField F := w.toNormedField
    letI : IsUltrametricDist F :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
        change w (n : F) ≤ 1
        simpa only [Int.cast_natCast] using hint (n : ℤ)
    intro x y
    exact IsUltrametricDist.norm_add_le_max x y
  have hle : ∀ y : 𝓞 F, w (y : F) ≤ 1 := by
    let vv : Valuation F NNReal :=
      { toFun := fun x ↦ ⟨w x, w.nonneg x⟩
        map_zero' := by apply Subtype.ext; exact w.map_zero
        map_one' := by apply Subtype.ext; exact w.map_one
        map_mul' := fun x z ↦ by apply Subtype.ext; exact w.map_mul x z
        map_add_le_max' := fun x z ↦ by
          change w (x + z) ≤ max (w x) (w z)
          exact hna x z }
    intro y
    have hy : IsIntegral vv.integer (y : F) := (RingOfIntegers.isIntegral_coe y).tower_top
    have hbound : vv (y : F) ≤ 1 :=
      (Valuation.integer.integers vv).isIntegral_iff_v_le_one.mp hy
    exact hbound
  have hcoe : ∀ u : 𝓞 K,
      ((algebraMap (𝓞 K) (𝓞 F) u : 𝓞 F) : F) = algebraMap K F ((u : 𝓞 K) : K) := by
    intro u
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 F) F, ← IsScalarTower.algebraMap_apply (𝓞 K) K F]
  have hvmem : ∀ u : 𝓞 K, u ∈ v.maximalIdeal.asIdeal ↔ v ((u : 𝓞 K) : K) < 1 := by
    intro u
    rw [← v.norm_embedding_eq, RingOfIntegers.coe_eq_algebraMap]
    exact (FinitePlace.norm_lt_one_iff_mem K v.maximalIdeal u).symm
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
  have hzK0 : ((z : 𝓞 K) : K) ≠ 0 := fun h => hz0 (by exact_mod_cast h)
  have hvz : v ((z : 𝓞 K) : K) < 1 := (hvmem z).mp hzmem
  have hzF0 : algebraMap (𝓞 K) (𝓞 F) z ≠ 0 := fun h => hz0 <|
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))).mp h
  have hwzF : w ((algebraMap (𝓞 K) (𝓞 F) z : 𝓞 F) : F) < 1 := by
    rw [hcoe z, hres]; exact hvz
  obtain ⟨P, t, ht, hPt⟩ :=
    AbsoluteValue.exists_heightOneSpectrum_rpow_eq hna hle ⟨_, hzF0, hwzF⟩
  have hmem : ∀ y : 𝓞 F, y ∈ P.asIdeal ↔ w (y : F) < 1 := by
    intro y
    rw [hPt, Real.rpow_lt_one_iff' (by positivity) ht, FinitePlace.mk_apply]
    exact (FinitePlace.norm_lt_one_iff_mem F P y).symm
  have hover : P.asIdeal.LiesOver v.maximalIdeal.asIdeal := by
    refine ⟨?_⟩
    ext u
    rw [Ideal.under_def, Ideal.mem_comap, hmem, hcoe u, hres, ← hvmem u]
  refine ⟨P, hover, ?_⟩
  set e := P.asIdeal.ramificationIdx (𝓞 K) with he
  set f := P.asIdeal.inertiaDeg (𝓞 K) with hf
  have hef : 0 < e * f :=
    Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
  letI : P.asIdeal.LiesOver v.maximalIdeal.asIdeal := hover
  have hloc : ∀ u : K,
      FinitePlace.mk P (algebraMap K F u) = FinitePlace.mk v.maximalIdeal u ^ (e * f) := by
    intro u
    change FinitePlace.mk P (algebraMap K F u) =
      FinitePlace.mk v.maximalIdeal u ^
        (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K))
    by_cases hu : u = 0
    · rw [hu, map_zero, map_zero, map_zero, zero_pow]
      exact (mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K))
        (P.asIdeal.inertiaDeg_pos (𝓞 K))).ne'
    simp_rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def]
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver F v.maximalIdeal, map_pow,
      WithZeroMulInt.toNNReal_neg_apply _ (by simpa),
      WithZeroMulInt.toNNReal_neg_apply _ (by simpa),
      ← Ideal.absNorm_pow_inertiaDeg v.maximalIdeal.1 P.1]
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.maximalIdeal.asIdeal P.asIdeal
      v.maximalIdeal.ne_bot]
    simp only [Nat.cast_pow, Nat.cast_mul, NNReal.coe_zpow, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hb0 : 0 < FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) := FinitePlace.pos_iff.mpr hzK0
  have hb1 : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) < 1 := by
    rw [FinitePlace.mk_maximalIdeal]; exact hvz
  have hkey : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^ (((e * f : ℕ) : ℝ) * t)
      = FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^ (1 : ℝ) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast, Real.rpow_one, ← hloc ((z : 𝓞 K) : K), ← hPt,
      hres, FinitePlace.mk_maximalIdeal]
  have htef : ((e * f : ℕ) : ℝ) * t = 1 := (Real.rpow_right_inj hb0 hb1.ne).mp hkey
  have ht' : t = (((e * f : ℕ) : ℝ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact htef)
  intro y
  rw [hPt y, ht']

end NumberField

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

end NumberField
