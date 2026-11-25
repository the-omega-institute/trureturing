/- GID: D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Basic]
   utility: none
   digest: Uniform signed power generator comparison and positive Kelvin gap. -/

import D5.S1.Words.Patterns.Separable.OccupiedComparison
import D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
import D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
import D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The exact compensated integer generator is approximated by the real
signed Mellin integral. The quantitative Kelvin gap then gives a uniform
one-sided estimate with the same error constant. -/

open Set MeasureTheory
open scoped BigOperators

namespace D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator

open OccupiedComparison OccupiedKernelWeightReplacement
open OccupiedMellinInterior OccupiedMellinFloors OccupiedMellinKelvin

private theorem sample_eq_two_rays (β : ℝ) {s : ℝ} (hs : 0 < s) :
    sample β 0 s = signedKernel β (1 + s) + signedKernel β (1 - s) := by
  unfold sample signedKernel
  rw [show 1 - (1 + s) = -s by ring, show 1 - (1 - s) = s by ring, abs_neg,
    abs_of_pos hs, abs_of_pos (by linarith : 0 < 1 + s)]
  simp only [zero_add, Real.one_rpow, mul_one]
  ring

private theorem split_signed_at_one (β : ℝ) (h : Integrable (signedKernel β)) :
    (∫ y, signedKernel β y) =
      (∫ y in Set.Ioi (1 : ℝ), signedKernel β y) + (∫ y in Set.Iio (1 : ℝ), signedKernel β y) := by
  have hd : Disjoint (Set.Ioi (1 : ℝ)) (Set.Iio 1) := by
    refine Set.disjoint_left.mpr fun y h₁ h₂ => ?_
    exact (not_lt_of_ge (Set.mem_Ioi.mp h₁).le) (Set.mem_Iio.mp h₂)
  have hae : (Set.univ : Set ℝ) =ᵐ[volume] Set.Ioi (1 : ℝ) ∪ Set.Iio 1 := by
    filter_upwards [volume.ae_ne (1 : ℝ)] with y hy
    exact propext (iff_of_true trivial ((lt_or_gt_of_ne hy).elim Or.inr Or.inl))
  rw [← setIntegral_univ, setIntegral_congr_set hae,
    setIntegral_union hd measurableSet_Iio h.integrableOn h.integrableOn]

/-- Exact identification of the unshifted paired mesh integral with the whole
signed Mellin kernel. Both affine rays are handled as measure-preserving maps;
their missing point y = 1 is volume-null. -/
private theorem halfline_sample_eq_J (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    IntegrableOn (sample β 0) (Set.Ioi (0 : ℝ)) ∧
    (∫ s in Set.Ioi (0 : ℝ), sample β 0 s) = J β := by
  unfold J
  have hg := signed_mellin_cancellation_and_gap.1 β hβ hβ'
  let ePlus := Homeomorph.addLeft (1 : ℝ)
  let eMinus := (Homeomorph.neg ℝ).trans ePlus
  have hp : MeasurePreserving ePlus volume volume :=
    measurePreserving_add_left (volume : Measure ℝ) 1
  have hm : MeasurePreserving eMinus volume volume :=
    hp.comp (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpSet : ePlus ⁻¹' Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext x
    change 1 < 1 + x ↔ 0 < x
    constructor <;> intro h <;> linarith
  have hmSet : eMinus ⁻¹' Set.Iio (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext x
    change 1 + (-x) < 1 ↔ 0 < x
    constructor <;> intro h <;> linarith
  have hpI : IntegrableOn (fun s => signedKernel β (1 + s)) (Set.Ioi (0 : ℝ)) := by
    rw [← hpSet]
    exact (hp.integrableOn_comp_preimage ePlus.measurableEmbedding).mpr hg.integrableOn
  have hmI : IntegrableOn (fun s => signedKernel β (1 - s)) (Set.Ioi (0 : ℝ)) := by
    rw [← hmSet]
    have hi := (hm.integrableOn_comp_preimage eMinus.measurableEmbedding).mpr
      (hg.integrableOn (s := Set.Iio (1 : ℝ)))
    change IntegrableOn (fun s => signedKernel β (1 + (-s))) (eMinus ⁻¹' Set.Iio (1 : ℝ)) at hi
    simpa only [sub_eq_add_neg] using hi
  have he : Set.EqOn (sample β 0) (fun s => signedKernel β (1 + s) + signedKernel β (1 - s))
      (Set.Ioi (0 : ℝ)) := fun _ hs => sample_eq_two_rays β hs
  refine ⟨(integrableOn_congr_fun he measurableSet_Ioi).mpr (hpI.add hmI), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add hpI hmI, split_signed_at_one β hg]
  have hpEq := hp.setIntegral_preimage_emb ePlus.measurableEmbedding (signedKernel β) (Set.Ioi 1)
  have hmEq := hm.setIntegral_preimage_emb eMinus.measurableEmbedding (signedKernel β) (Set.Iio 1)
  rw [hpSet] at hpEq
  rw [hmSet] at hmEq
  change (∫ s in Set.Ioi (0 : ℝ), signedKernel β (1 + s)) = _ at hpEq
  change (∫ s in Set.Ioi (0 : ℝ), signedKernel β (1 + (-s))) = _ at hmEq
  rw [hpEq]
  have hmEq' : (∫ s in Set.Ioi (0 : ℝ), signedKernel β (1 - s)) =
      ∫ y in Set.Iio (1 : ℝ), signedKernel β y := by
    simpa only [sub_eq_add_neg] using hmEq
  rw [hmEq']

/-- Shifted inverse-power profile on integer positions. -/
noncomputable def powerProfile (β : ℝ) (z : ℤ) : ℝ :=
  (2 + |(z : ℝ)|) ^ (-β)

/-- Compensated linear generator with the exact production weights, including
the singleton correction. A positive jump of size i + 1 uses kernelWeight i. -/
noncomputable def actualGenerator (u : ℤ → ℝ) (z : ℤ) : ℝ :=
  ∑' i : ℕ, kernelWeight i * (u (z + (i + 1 : ℕ)) + u (z - (i + 1 : ℕ)) - 2 * u z)

private theorem generator_eq_tsum (β : ℝ) (n : ℕ) :
    actualGenerator (powerProfile β) (n : ℤ) =
      ∑' i : ℕ, kernelWeight i * secondDiff β (n : ℝ) ((i + 1 : ℕ) : ℝ) := by
  unfold actualGenerator powerProfile secondDiff
  push_cast
  rfl

private theorem homogeneous_weight {x : ℝ} (hx : 0 < x) :
    1 / (x * Real.sqrt x) = x ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  calc
    _ = (1 : ℝ) / (x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ)) := by rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add hx, one_div, ← Real.rpow_neg hx.le]
      norm_num

private theorem normalized_error {β N E r : ℝ} (hn : 1 ≤ N) (hE : 0 ≤ E)
    (h : |r| ≤ 298 * E * N ^ (-β - 3 / 2)) :
    |N ^ (β + 1 / 2) * r| ≤ 298 * E * N ^ (-(1 / 80 : ℝ)) := by
  have hN : 0 < N := by linarith
  have hg := Real.rpow_nonneg hN.le (β + 1 / 2)
  rw [abs_mul, abs_of_nonneg hg]
  calc
    _ ≤ N ^ (β + 1 / 2) * (298 * E * N ^ (-β - 3 / 2)) := mul_le_mul_of_nonneg_left h hg
    _ = (298 * E) * N ^ (-(1 : ℝ)) := by
      calc
        _ = (298 * E) * (N ^ (β + 1 / 2) * N ^ (-β - 3 / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hN]
          congr 2
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn (by norm_num)) (by positivity)

/-- The actual compensated generator comparison is uniform to the
Kelvin integral, with one strictly positive leading coefficient. -/
private theorem actual_comparison :
    ∃ A > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ β : ℝ, 1 / 2 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 4 ^ 20 ≤ n →
        |(n : ℝ) ^ (β + (1 / 2 : ℝ)) * actualGenerator (powerProfile β) (n : ℤ) -
          A * J β| ≤ C * (n : ℝ) ^ (-(1 / 80 : ℝ)) := by
  obtain ⟨A,hA,E,hE,hw⟩ := actual_global_weight_replacement
  refine ⟨A,hA,1232 * A + 298 * E,by positivity,?_⟩
  intro β hβ hβ' n hn
  have hN1 : 1 ≤ n := (by norm_num : (1 : ℕ) ≤ 4 ^ 20).trans hn
  have hn0 : 0 < n := by omega
  let N := (n : ℝ)
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn0
  have hNr : 1 ≤ N := by dsimp only [N]; exact_mod_cast hN1
  let Q (i : ℕ) := ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * secondDiff β N ((i + 1 : ℕ) : ℝ)
  let U (i : ℕ) := actualWeightError A (i + 1) * secondDiff β N ((i + 1 : ℕ) : ℝ)
  let G := N ^ (β + (1 / 2 : ℝ))
  let S := N ^ (β + (3 / 2 : ℝ))
  let L := J β
  have hS : 0 < S := Real.rpow_pos_of_pos hN _
  have heq (i : ℕ) : sample β (2 / N) (((i + 1 : ℕ) : ℝ) / N) = S * Q i := by
    have hi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    rw [OccupiedKernelWeightReplacement.sample_eq_lattice hN hi]
  obtain ⟨hab,_,hme⟩ := global_mesh_rate (by linarith) hβ' n hn
  have hk := (halfline_sample_eq_J β (by linarith) (by linarith)).2
  change Summable fun i : ℕ => |sample β (2 / N) (((i + 1 : ℕ) : ℝ) / N)| at hab
  simp only [heq, abs_mul, abs_of_pos hS] at hab
  have hNorm : Summable fun i : ℕ => ‖Q i‖ := by
    have h := hab.mul_left S⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hS.ne', one_mul, Real.norm_eq_abs] using h
  have hQ := hNorm.of_norm
  have hSG : S / N = G := by
    dsimp only [S, G]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one N, ← Real.rpow_add hN]
    congr 1
    ring
  have hMesh : |L - G * (∑' i, Q i)| ≤ 1232 * N ^ (-(1 / 80 : ℝ)) := by
    change |(∫ s in Ioi (0 : ℝ), sample β 0 s) -
      (∑' i : ℕ, sample β (2 / N) (((i + 1 : ℕ) : ℝ) / N)) / N| ≤ _ at hme
    simp only [hk, heq, tsum_mul_left] at hme
    have he : (S * (∑' i, Q i)) / N = G * (∑' i, Q i) := by rw [← hSG]; ring
    rw [he] at hme
    exact hme
  obtain ⟨hUabs,hUb⟩ := hw β hβ hβ' n hn0
  change Summable (fun i : ℕ => |U i|) at hUabs
  change (∑' i : ℕ, |U i|) ≤ 298 * E * N ^ (-β - 3 / 2) at hUb
  have hUnorm : Summable (fun i : ℕ => ‖U i‖) := by
    simpa only [Real.norm_eq_abs] using hUabs
  have hUa := hUnorm.of_norm
  have hUb' : |∑' i : ℕ, U i| ≤ 298 * E * N ^ (-β - 3 / 2) :=
    (by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hUnorm :
      |∑' i : ℕ, U i| ≤ ∑' i : ℕ, |U i|).trans hUb
  have hUscaled : |G * (∑' i : ℕ, U i)| ≤ 298 * E * N ^ (-(1 / 80 : ℝ)) :=
    normalized_error hNr hE hUb'
  have hgen : actualGenerator (powerProfile β) (n : ℤ) =
      A * (∑' i : ℕ, Q i) + ∑' i : ℕ, U i := by
    rw [generator_eq_tsum, ← tsum_mul_left, ← (hQ.mul_left A).tsum_add hUa]
    apply tsum_congr
    intro i
    have hp : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    dsimp only [Q, U, actualWeightError]
    rw [Nat.add_sub_cancel]
    have hw : A / (((i + 1 : ℕ) : ℝ) * Real.sqrt ((i + 1 : ℕ) : ℝ)) =
      A * ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [← homogeneous_weight hp]; ring
    rw [hw]
    ring
  have hM : |A * (G * (∑' i : ℕ, Q i) - L)| ≤ 1232 * A * N ^ (-(1 / 80 : ℝ)) := by
    rw [abs_mul, abs_of_pos hA, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hMesh hA.le).trans_eq (by ring)
  change |G * actualGenerator (powerProfile β) (n : ℤ) - A * L| ≤ _
  rw [hgen]
  have ha :
      G * (A * (∑' i : ℕ, Q i)+∑' i : ℕ, U i) - A * L =
        A * (G * (∑' i : ℕ, Q i) - L) + G * (∑' i : ℕ, U i) := by ring
  rw [ha]
  exact ((abs_add_le _ _).trans (add_le_add hM hUscaled)).trans_eq (by ring)

/-- One fixed leading coefficient and error constant control both the signed
discrepancy and the lower bound obtained from the Kelvin gap. -/
theorem actual_generator_power_comparison :
    ∃ A > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ β : ℝ, 1 / 2 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 4 ^ 20 ≤ n →
        |(n : ℝ) ^ (β + 1 / 2) * actualGenerator (powerProfile β) (n : ℤ) - A * J β| ≤
          C * (n : ℝ) ^ (-(1 / 80 : ℝ)) ∧
        A * (gapCoefficient * (β - 1 / 2)) - C * (n : ℝ) ^ (-(1 / 80 : ℝ)) ≤
          (n : ℝ) ^ (β + 1 / 2) * actualGenerator (powerProfile β) (n : ℤ) := by
  obtain ⟨A, hA, C, hC, H⟩ := actual_comparison
  refine ⟨A, hA, C, hC, ?_⟩
  intro β hβ hβ' n hn
  have hb := H β hβ hβ' n hn
  refine ⟨hb, ?_⟩
  have hg := signed_mellin_cancellation_and_gap.2.2.2 β hβ (by linarith)
  have hk := mul_le_mul_of_nonneg_left hg hA.le
  have he := (abs_le.mp hb).1
  linarith only [hk, he]

end D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
