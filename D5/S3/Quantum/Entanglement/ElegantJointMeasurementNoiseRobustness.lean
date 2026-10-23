/- GID: D5/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseRobustness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseRobustness
   mirror-E: none(waiver:physical-noise-bound-consumer)
   anchors: []
   utility: none
   digest: An actual positive EJM inflation score excludes a strict physical noise box. -/

import D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
import D5.S3.Quantum.Entanglement.EJMInflationScore

/-
admission_basis: escape-witness
positive_score_physical_noise_box: proof_shape: content; escape_witness:
the actual 16 triangle contractions are perturbed by their genuine noisy
head marginals in ABC or BAC order, while all 16 singleton blocks still
cancel. Coefficient amplitudes and the physical L1 estimate control the
full local expectation. Actual coefficient positivity is an explicit premise.
Source-bound registration for the certificate consumer remains under issue #16309.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseRobustness

open D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
open D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJMWightedCancellation
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation
open D5.S3.Quantum.Entanglement.TriangleInflationSoundness
open scoped BigOperators

private def tripleEquiv : (Fin 3 → Fin 4) ≃ Fin 4 × (Fin 4 × Fin 4) where
  toFun h := (h 0, h 1, h 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv h := by ext j; fin_cases j <;> rfl
  right_inv a := rfl

private theorem sum_triples (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ h : Fin 3 → Fin 4, f (h 0) (h 1) (h 2)) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, f a b c := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv tripleEquiv (fun h => f (h 0) (h 1) (h 2))
      (fun a => f a.1 a.2.1 a.2.2) (fun _ => rfl))

private def headProbability (p : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (i : Fin 16) (h : Fin 3 → Fin 4) : ℝ :=
  if spec.party (lhsTriangle i 0) = 0 then p (h 0) (h 1) (h 2)
  else p (h 1) (h 0) (h 2)

private theorem noise_head_l1 (x y z : ℝ) (i : Fin 16) :
    (∑ h : Fin 3 → Fin 4,
      |headProbability (ejmProbability x y z) i h -
        ejmDistribution (h 0) (h 1) (h 2)|) = l1Deviation x y z := by
  have hideal : ∀ a b c,
      ejmDistribution a b c = ejmProbability 1 1 1 a b c := by
    intro a b c
    rw [ejm_noise_probability]
    simp only [ejmDistribution, ejmNumerator, ejmNoiseTable]
    by_cases he : a = b ∧ b = c
    · rw [if_pos he, if_pos he]
      norm_num
    · rw [if_neg he, if_neg he]
      by_cases hd : a ≠ b ∧ b ≠ c ∧ c ≠ a
      · rw [if_pos hd, if_neg hd.1, if_neg hd.2.1, if_neg hd.2.2]
        norm_num
      · rw [if_neg hd]
        by_cases hab : a = b
        · rw [if_pos hab]
          norm_num
        · rw [if_neg hab]
          by_cases hbc : b = c
          · rw [if_pos hbc]
            norm_num
          · rw [if_neg hbc]
            have hca : c = a := by
              by_contra hh
              exact hd ⟨hab, hbc, hh⟩
            rw [if_pos hca]
            norm_num
  have hswap : ∀ a b c, ejmDistribution a b c = ejmDistribution b a c := by
    intro a b c
    exact congrArg (fun t : ℝ => t / 256) (ejmNumerator_swap_ab a b c).symm
  unfold headProbability
  split_ifs with hi
  · simp_rw [hideal]
    exact sum_triples (fun a b c =>
      |ejmProbability x y z a b c - ejmProbability 1 1 1 a b c|)
  · rw [sum_triples (fun a b c =>
      |ejmProbability x y z b a c - ejmDistribution a b c|)]
    calc
      _ = ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          |ejmProbability x y z b a c - ejmProbability 1 1 1 b a c| := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        rw [hswap a b c, hideal]
      _ = _ := by rw [Finset.sum_comm]; rfl

private theorem headProbability_mass (R : ResponseModel)
    (p : Fin 4 → Fin 4 → Fin 4 → ℝ) (hp : Represents R p)
    (i : Fin 16) (o : Node → Fin 4) :
    marginalMass spec R (nodeRange (triangleHead i)) o =
      headProbability p i (o ∘ triangleHead i) := by
  rw [triangle_head_mass_of_represents R p hp i o]
  unfold headProbability triangleHead triangleA triangleB triangleC
  split_ifs <;> rfl

private theorem actual_triangle_expectation_le (F : (Fin 10 → Fin 4) → ℤ)
    (R : ResponseModel) (x y z amp : ℝ)
    (hp : Represents R (ejmProbability x y z))
    (hamp : ∀ e, |(F e : ℝ)| ≤ amp) (i : Fin 16) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (triangleBlock F i o : ℝ)) ≤
      256 * amp * l1Deviation x y z := by
  classical
  let p := ejmProbability x y z
  let centered := fun o : Node → Fin 4 =>
    256 * (F (o ∘ lhsTriangle i) : ℝ) -
      ∑ h : Fin 3 → Fin 4,
        (256 * headProbability p i h) * (F (Fin.append h (o ∘ triangleTail i)) : ℝ)
  have hzero : (∑ o, inflationMass spec R o * centered o) = 0 := by
    have h := inflation_centered_fin_expectation (m := 3) (n := 7) spec R
      (lhsTriangle i) (triangle_injective i)
      (fun h => 256 * headProbability p i h) 256 256 (-1)
      (fun e => (F e : ℝ)) (by norm_num) (triangle_support_disjoint i)
      (fun o => by
        change marginalMass spec R (nodeRange (triangleHead i)) o =
          256 * headProbability p i (o ∘ triangleHead i) / 256
        rw [headProbability_mass R p hp i o]
        ring)
    simpa [centered, triangleTail, Function.comp_def, sub_eq_add_neg] using h
  have hnum : ∀ a b c,
      (ejmIntNumerator a b c : ℝ) = 256 * ejmDistribution a b c := by
    intro a b c
    simp only [ejmIntNumerator, ejmDistribution, ejmNumerator]
    split_ifs <;> norm_num
  have hpoint : ∀ o : Node → Fin 4,
      (triangleBlock F i o : ℝ) ≤ centered o + 256 * amp * l1Deviation x y z := by
    intro o
    have hterm : (∑ h : Fin 3 → Fin 4,
        (headProbability p i h - ejmDistribution (h 0) (h 1) (h 2)) *
          (F (Fin.append h (o ∘ triangleTail i)) : ℝ)) ≤ amp * l1Deviation x y z := by
      calc
        _ ≤ ∑ h : Fin 3 → Fin 4,
            |headProbability p i h - ejmDistribution (h 0) (h 1) (h 2)| * amp := by
          apply Finset.sum_le_sum
          intro h _
          exact (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hamp _) (abs_nonneg _))
        _ = _ := by rw [← Finset.sum_mul, noise_head_l1]; ring
    have hdiff : (triangleBlock F i o : ℝ) = centered o +
        256 * (∑ h : Fin 3 → Fin 4,
          (headProbability p i h - ejmDistribution (h 0) (h 1) (h 2)) *
            (F (Fin.append h (o ∘ triangleTail i)) : ℝ)) := by
      simp only [triangleBlock, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
        Int.cast_sum, hnum, centered, sub_mul,
        Finset.sum_sub_distrib, mul_assoc]
      simp only [← Finset.mul_sum]
      ring
    rw [hdiff]
    nlinarith
  calc
    _ ≤ ∑ o : Node → Fin 4, inflationMass spec R o *
        (centered o + 256 * amp * l1Deviation x y z) :=
      Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left (hpoint o)
        (inflationMass_nonnegative spec R o))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        hzero, inflationMass_normalized, zero_add, one_mul]

/-- The actual coefficient score has a controlled local expectation on the
physical independent-source noisy law. The singleton terms cancel exactly. -/
theorem physical_score_expectation_le (F1 : (Fin 10 → Fin 4) → ℤ)
    (F2 : (Fin 9 → Fin 4) → ℤ) (R : ResponseModel) (x y z amp : ℝ)
    (hp : Represents R (ejmProbability x y z))
    (hamp : ∀ e, |(F1 e : ℝ)| ≤ amp) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (score F1 F2 o : ℝ)) ≤
      4096 * amp * l1Deviation x y z := by
  classical
  have hsingle := singleton_block_expectation_zero_of_uniform F2 R
    (ejmProbability x y z) hp (ejm_noise_marginal_A x y z) (ejm_noise_marginal_B x y z)
  calc
    _ = ∑ i : Fin 16, ∑ o : Node → Fin 4,
        inflationMass spec R o * (triangleBlock F1 i o : ℝ) := by
      simp only [score, Int.cast_add, Int.cast_sum, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm, Finset.sum_comm (f := fun o i =>
        inflationMass spec R o * (singletonBlock F2 i o : ℝ))]
      simp only [hsingle, Finset.sum_const_zero, add_zero]
    _ ≤ ∑ _ : Fin 16, 256 * amp * l1Deviation x y z :=
      Finset.sum_le_sum (fun i _ => actual_triangle_expectation_le F1 R x y z amp hp hamp i)
    _ = _ := by simp; ring

/-- A true positive margin of the actual coefficient score excludes the
physical noisy triangle whenever its visibility deficits lie below the margin. -/
theorem positive_score_excludes_physical_noise (F1 : (Fin 10 → Fin 4) → ℤ)
    (F2 : (Fin 9 → Fin 4) → ℤ) (x y z amp margin : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hamp0 : 0 ≤ amp)
    (hamp : ∀ e, |(F1 e : ℝ)| ≤ amp)
    (hpositive : ∀ o : Node → Fin 4, margin ≤ (score F1 F2 o : ℝ))
    (hnoise : 8192 * amp * ((1 - x) + (1 - y) + (1 - z)) < margin) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      (ejmProbability x y z) := by
  intro hlocal
  obtain ⟨R, hp⟩ := isTriangleLocal_responseModel (ejmProbability x y z) hlocal
  have hlower : margin ≤ ∑ o : Node → Fin 4,
      inflationMass spec R o * (score F1 F2 o : ℝ) := by
    calc
      _ = ∑ o : Node → Fin 4, inflationMass spec R o * margin := by
        rw [← Finset.sum_mul, inflationMass_normalized, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun o _ =>
        mul_le_mul_of_nonneg_left (hpositive o) (inflationMass_nonnegative spec R o))
  have hupper := physical_score_expectation_le F1 F2 R x y z amp hp hamp
  have hl1 := mul_le_mul_of_nonneg_left (ejm_noise_l1_bound x y z hx hy hz)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hamp0)
  nlinarith

def noiseBoxRadius (margin amp : ℝ) : ℝ := min (1 / 2) (margin / (24576 * amp))

/-- A positive global score margin and an amplitude bound give an explicit
strict source-noise box about the ideal physical EJM triangle. -/
theorem positive_score_physical_noise_box (F1 : (Fin 10 → Fin 4) → ℤ)
    (F2 : (Fin 9 → Fin 4) → ℤ) (amp margin : ℝ)
    (hamp0 : 0 < amp) (hmargin : 0 < margin)
    (hamp : ∀ e, |(F1 e : ℝ)| ≤ amp)
    (hpositive : ∀ o : Node → Fin 4, margin ≤ (score F1 F2 o : ℝ)) :
    0 < noiseBoxRadius margin amp ∧ ∀ x y z : ℝ,
      x ∈ Set.Ioc (1 - noiseBoxRadius margin amp) 1 →
      y ∈ Set.Ioc (1 - noiseBoxRadius margin amp) 1 →
      z ∈ Set.Ioc (1 - noiseBoxRadius margin amp) 1 →
      ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
        (ejmProbability x y z) := by
  have hden : 0 < 24576 * amp := mul_pos (by norm_num) hamp0
  have hrad : 0 < noiseBoxRadius margin amp :=
    lt_min (by norm_num) (div_pos hmargin hden)
  refine ⟨hrad, ?_⟩
  intro x y z hx hy hz
  have hhalf : noiseBoxRadius margin amp ≤ 1 / 2 := min_le_left _ _
  have hfrac : noiseBoxRadius margin amp ≤ margin / (24576 * amp) := min_le_right _ _
  have hprod : 24576 * amp * noiseBoxRadius margin amp ≤ margin := by
    nlinarith [(le_div_iff₀ hden).mp hfrac]
  apply positive_score_excludes_physical_noise F1 F2 x y z amp margin
    ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩
    ⟨by linarith [hz.1], hz.2⟩ (le_of_lt hamp0) hamp hpositive
  have hsum : (1 - x) + (1 - y) + (1 - z) < 3 * noiseBoxRadius margin amp := by
    linarith [hx.1, hy.1, hz.1]
  have hstrict := mul_lt_mul_of_pos_left hsum (mul_pos (by norm_num : (0 : ℝ) < 8192) hamp0)
  nlinarith

#print axioms physical_score_expectation_le
#print axioms positive_score_excludes_physical_noise
#print axioms positive_score_physical_noise_box

end D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseRobustness
