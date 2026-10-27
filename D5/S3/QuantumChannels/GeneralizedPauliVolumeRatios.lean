/- GID: D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/GeneralizedPauliVolumeRatios
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Generalized Pauli channel regions have three explicit volume ratios. -/

import D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Volumes of the source eigenvalue regions for generalized Pauli channels. -/

noncomputable section

namespace D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

def boxRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {x | ∀ i, -1 / ((d : ℝ) - 1) ≤ x i ∧ x i ≤ 1}

def cpRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {x | -1 / ((d : ℝ) - 1) ≤ ∑ i, x i ∧ ∀ j, ∑ i, x i ≤ 1 + (d : ℝ) * x j}

def generatorRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  cpRegion d ∩ {x | ∀ i, 0 ≤ x i}

def ebRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  generatorRegion d ∩ {x | ∑ i, x i ≤ 1}

def channelVolume (d : ℕ) (s : Set (Fin (d + 1) → ℝ)) : ℝ :=
  (Real.sqrt ((d : ℝ) - 1) / (d : ℝ)) ^ (d + 1) * (volume s).toReal

private def standardRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1}

private def affineSimplex (d : ℕ) (c : ℝ) : Set (Fin (d + 1) → ℝ) :=
  (fun t i => 1 + c * (t i - ∑ j, t j)) '' standardRegion (d + 1)

private lemma standard_volume (n : ℕ) :
    volume (standardRegion n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  change volume
    (D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexCoords (n + 1)) = _
  rw [D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_volume]
  rw [one_div, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  norm_cast

private lemma affine_simplex_volume (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    volume (affineSimplex d c) =
      ENNReal.ofReal ((d : ℝ) * c ^ (d + 1) / ((d + 1).factorial : ℝ)) := by
  classical
  let a : Matrix (Fin (d + 1)) (Fin 1) ℝ := Matrix.of (fun _ _ => 1)
  let b : Matrix (Fin 1) (Fin (d + 1)) ℝ := Matrix.of (fun _ _ => 1)
  have hprod : a * b = Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext i j
    simp only [Matrix.mul_apply, a, b, Matrix.of_apply, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul]
  have hdet : Matrix.det ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) -
      Matrix.of (fun _ _ => 1)) = -(d : ℝ) := by
    rw [← hprod, Matrix.det_one_sub_mul_comm, Matrix.det_unique]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, a, b, Matrix.of_apply, one_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_one]
    ring
  let f := Matrix.toLin' (c • ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) -
    Matrix.of (fun _ _ => 1)))
  have hf (t : Fin (d + 1) → ℝ) : f t = fun i => c * (t i - ∑ j, t j) := by
    change Matrix.toLin' _ t = _
    rw [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.mulVec_apply_eq_sum, Matrix.of_apply,
      one_mul]
  have hdetf : LinearMap.det f = c ^ (d + 1) * -(d : ℝ) := by
    dsimp only [f]
    rw [LinearMap.det_toLin', Matrix.det_smul, hdet, Fintype.card_fin]
  have himage : affineSimplex d c = (fun y : Fin (d + 1) → ℝ => (fun _ => 1) + y) ''
      (f '' standardRegion (d + 1)) := by
    rw [image_image]
    apply congrArg (fun g => g '' standardRegion (d + 1))
    funext t
    rw [hf]
    rfl
  rw [himage, image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap,
    hdetf, standard_volume]
  rw [abs_mul, abs_of_pos (pow_pos hc _), abs_neg, abs_of_nonneg (Nat.cast_nonneg d),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private lemma affine_sum (d : ℕ) (c : ℝ) (t : Fin (d + 1) → ℝ) :
    (∑ i, (1 + c * (t i - ∑ j, t j))) =
      (d : ℝ) + 1 - c * (d : ℝ) * ∑ j, t j := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  ring

private lemma affine_simplex_iff (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (x : Fin (d + 1) → ℝ) :
    x ∈ affineSimplex d c ↔
      (d : ℝ) + 1 - c * d ≤ ∑ i, x i ∧ ∀ j, ∑ i, x i ≤ 1 + (d : ℝ) * x j := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hden : 0 < c * (d : ℝ) := mul_pos hc hdpos
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 at ht
    rw [affine_sum]
    constructor
    · nlinarith [mul_nonneg hden.le (sub_nonneg.mpr ht.2)]
    · intro j
      nlinarith [mul_nonneg hden.le (ht.1 j)]
  · intro hx
    let t : Fin (d + 1) → ℝ := fun i =>
      ((d : ℝ) * x i - ∑ j, x j + 1) / (c * (d : ℝ))
    have hsum : ∑ i, t i = ((d : ℝ) + 1 - ∑ j, x j) / (c * (d : ℝ)) := by
      dsimp only [t]
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (by linarith [hx.2 i]) hden.le
    · rw [hsum]
      exact (div_le_one hden).mpr (by linarith [hx.1])
    · funext i
      change 1 + c * (t i - ∑ j, t j) = x i
      rw [hsum]
      dsimp only [t]
      field_simp
      <;> ring

private lemma cp_eq_affine (d : ℕ) (hd : 2 ≤ d) :
    cpRegion d = affineSimplex d ((d : ℝ) / ((d : ℝ) - 1)) := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn : (d : ℝ) - 1 ≠ 0 := by linarith
  have heq : (d : ℝ) + 1 - (d : ℝ) / ((d : ℝ) - 1) * d =
      -1 / ((d : ℝ) - 1) := by
    field_simp
    <;> ring
  ext x
  rw [affine_simplex_iff d hd _ (div_pos (by linarith) (by linarith)), heq]
  rfl

private lemma generator_eq_union (d : ℕ) (hd : 2 ≤ d) :
    generatorRegion d = standardRegion (d + 1) ∪ affineSimplex d 1 := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlo : -1 / ((d : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by norm_num) (by linarith)
  ext x
  rw [mem_union, affine_simplex_iff d hd 1 zero_lt_one]
  change ((-1 / ((d : ℝ) - 1) ≤ ∑ i, x i ∧
    ∀ j, ∑ i, x i ≤ 1 + (d : ℝ) * x j) ∧ (∀ i, 0 ≤ x i)) ↔
    ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1) ∨
      ((d : ℝ) + 1 - 1 * d ≤ ∑ i, x i ∧ ∀ j, ∑ i, x i ≤ 1 + (d : ℝ) * x j)
  constructor
  · intro hx
    by_cases hs : ∑ i, x i ≤ 1
    · exact Or.inl ⟨hx.2, hs⟩
    · exact Or.inr ⟨by linarith, hx.1.2⟩
  · rintro (hx | hx)
    · exact ⟨⟨hlo.trans (Finset.sum_nonneg (fun i _ => hx.1 i)),
        fun j => le_trans hx.2 (by nlinarith [hx.1 j])⟩, hx.1⟩
    · refine ⟨⟨by linarith [hx.1], hx.2⟩, fun j => ?_⟩
      nlinarith [hx.2 j, hx.1]

private lemma simplex_overlap_null (d : ℕ) (hd : 2 ≤ d) :
    volume (standardRegion (d + 1) ∩ affineSimplex d 1) = 0 := by
  classical
  let f : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hf (x : Fin (d + 1) → ℝ) : f x = ∑ i, x i := by
    simp only [f, LinearMap.sum_apply, LinearMap.proj_apply]
  let a : AffineSubspace ℝ (Fin (d + 1) → ℝ) :=
    AffineSubspace.mk' (Pi.single (0 : Fin (d + 1)) (1 : ℝ)) (LinearMap.ker f)
  have ha : (a : Set (Fin (d + 1) → ℝ)) = {x | ∑ i, x i = 1} := by
    ext x
    change x ∈ AffineSubspace.mk' _ _ ↔ _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    change f (x - Pi.single 0 1) = 0 ↔ ∑ i, x i = 1
    rw [map_sub, hf, hf]
    simp only [Fintype.sum_pi_single', sub_eq_zero]
  have hproper : a ≠ ⊤ := by
    intro h
    have hz : (0 : Fin (d + 1) → ℝ) ∈ (a : Set (Fin (d + 1) → ℝ)) := by
      rw [h]
      trivial
    rw [ha] at hz
    simpa only [mem_ofPred_eq, Pi.zero_apply, Finset.sum_const_zero, zero_ne_one] using hz
  have hnull : volume {x : Fin (d + 1) → ℝ | ∑ i, x i = 1} = 0 := by
    rw [← ha]
    exact Measure.addHaar_affineSubspace volume a hproper
  apply measure_mono_null _ hnull
  intro x hx
  have hlo := ((affine_simplex_iff d hd 1 zero_lt_one x).mp hx.2).1
  change ∑ i, x i = 1
  linarith [hx.1.2]

private lemma generator_volume (d : ℕ) (hd : 2 ≤ d) :
    volume (generatorRegion d) =
      ENNReal.ofReal (((d : ℝ) + 1) / ((d + 1).factorial : ℝ)) := by
  have hs := standard_volume (d + 1)
  have hq := affine_simplex_volume d hd 1 zero_lt_one
  have hu := generator_eq_union d hd
  have hn := simplex_overlap_null d hd
  have hmeas : MeasurableSet (standardRegion (d + 1)) := by
    change MeasurableSet ({x : Fin (d + 1) → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
    apply MeasurableSet.inter
    · have hm (i : Fin (d + 1)) : MeasurableSet {x : Fin (d + 1) → ℝ | 0 ≤ x i} :=
        measurableSet_le measurable_const (measurable_pi_apply i)
      simpa only [setOf_forall] using MeasurableSet.iInter hm
    · exact measurableSet_le (by fun_prop) measurable_const
  have hadd := measure_union_add_inter' (μ := volume) hmeas (affineSimplex d 1)
  rw [hn, add_zero] at hadd
  rw [hu, hadd, hs, hq]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [one_pow, mul_one]
  ring

private lemma eb_eq_standard (d : ℕ) (hd : 2 ≤ d) :
    ebRegion d = standardRegion (d + 1) := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlo : -1 / ((d : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by norm_num) (by linarith)
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.2, hx.2⟩
  · intro hx
    refine ⟨⟨⟨hlo.trans (Finset.sum_nonneg (fun i _ => hx.1 i)), ?_⟩, hx.1⟩, hx.2⟩
    intro j
    exact hx.2.trans (by nlinarith [hx.1 j])

private lemma box_volume (d : ℕ) (hd : 2 ≤ d) :
    volume (boxRegion d) = ENNReal.ofReal (((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1)) := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn : (d : ℝ) - 1 ≠ 0 := by linarith
  have hwidth : 1 - -1 / ((d : ℝ) - 1) = (d : ℝ) / ((d : ℝ) - 1) := by
    field_simp [hdn]
    <;> ring
  have hset : boxRegion d = Icc (fun _ => -1 / ((d : ℝ) - 1)) (fun _ => 1) := by
    ext x
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
      fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hset, Real.volume_Icc_pi]
  simp only [hwidth, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (div_nonneg (Nat.cast_nonneg d) (by linarith))]

private lemma ratios_from_volumes (d : ℕ) (hd : 2 ≤ d)
    (hp : volume (boxRegion d) =
      ENNReal.ofReal (((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1)))
    (hc : volume (cpRegion d) =
      ENNReal.ofReal ((d : ℝ) * ((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1) /
        ((d + 1).factorial : ℝ)))
    (hg : volume (generatorRegion d) =
      ENNReal.ofReal (((d : ℝ) + 1) / ((d + 1).factorial : ℝ)))
    (he : volume (ebRegion d) = ENNReal.ofReal (1 / ((d + 1).factorial : ℝ))) :
    channelVolume d (cpRegion d) / channelVolume d (boxRegion d) =
        (d : ℝ) / ((d + 1).factorial : ℝ) ∧
    channelVolume d (generatorRegion d) / channelVolume d (cpRegion d) =
        (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) / (d : ℝ)) ^ d ∧
    channelVolume d (ebRegion d) / channelVolume d (generatorRegion d) =
        1 / ((d : ℝ) + 1) := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdmpos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hfpos : (0 : ℝ) < ((d + 1).factorial : ℝ) := by positivity
  have hlpos : (0 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := div_pos hdpos hdmpos
  have hw : (Real.sqrt ((d : ℝ) - 1) / (d : ℝ)) ^ (d + 1) ≠ 0 :=
    ne_of_gt (pow_pos (div_pos (Real.sqrt_pos.mpr hdmpos) hdpos) _)
  simp only [channelVolume, hp, hc, hg, he,
    ENNReal.toReal_ofReal (le_of_lt (pow_pos hlpos (d + 1))),
    ENNReal.toReal_ofReal (le_of_lt (div_pos (mul_pos hdpos (pow_pos hlpos _)) hfpos)),
    ENNReal.toReal_ofReal (le_of_lt (div_pos (by linarith : (0 : ℝ) < (d : ℝ) + 1) hfpos)),
    ENNReal.toReal_ofReal (le_of_lt (div_pos zero_lt_one hfpos))]
  constructor
  · field_simp [hw, hlpos.ne', hfpos.ne']
  · constructor
    · simp only [div_pow, pow_succ]
      field_simp [hw, hdpos.ne', hdmpos.ne', hfpos.ne']
      <;> ring
    · field_simp [hw, hfpos.ne']


theorem result : ∀ d : ℕ, 2 ≤ d →
    channelVolume d (cpRegion d) / channelVolume d (boxRegion d) =
        (d : ℝ) / ((d + 1).factorial : ℝ) ∧
    channelVolume d (generatorRegion d) / channelVolume d (cpRegion d) =
        (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) / (d : ℝ)) ^ d ∧
    channelVolume d (ebRegion d) / channelVolume d (generatorRegion d) =
        1 / ((d : ℝ) + 1) := by
  intro d hd
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply ratios_from_volumes d hd (box_volume d hd)
  · rw [cp_eq_affine d hd]
    exact affine_simplex_volume d hd _ (div_pos (by positivity) (by linarith))
  · exact generator_volume d hd
  · rw [eb_eq_standard d hd]
    exact standard_volume (d + 1)

end D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios
