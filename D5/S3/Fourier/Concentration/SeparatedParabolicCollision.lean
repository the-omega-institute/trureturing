/- GID: D5/S3/Fourier/Concentration/SeparatedParabolicCollision
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/SeparatedParabolicCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separated parabolic weights attain the collision variance limit. -/

import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
import D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

/-! Exact finite collision mass and its normalized limit on separated integer points. -/

open Finset Filter
open scoped Topology

noncomputable section

namespace D5.S3.Fourier.Concentration.SeparatedParabolicCollision

open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

/-- Finite parabolic weights have exact second moment and collision mass below unit resolution. -/
theorem separated_parabolic_collision (n : ℕ) (hn : 0 < n) (η : ℝ)
    (hη : 0 ≤ η) (hη' : η < 1) :
    let mass := fun m : ℕ => (m : ℝ) * (4 * (m : ℝ)^2 - 1) / 3
    let c := fun k : ℤ => (n : ℝ)^2 - (k : ℝ)^2
    let W := mass n
    (∀ k ∈ latticeInterval n, 0 ≤ c k) ∧
    0 < W ∧
    (∑ k ∈ latticeInterval n, c k) = W ∧
    (∑ k ∈ latticeInterval n, c k * (k : ℝ)^2) = W * ((n : ℝ)^2 - 1)/5 ∧
    nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η =
      W * (4 * (n : ℝ)^2 + 1)/5 := by
  intro mass c W
  have hW : normalizer n ((n : ℝ)^2) = W := by
    rw [normalizer_formula]
    dsimp [W, mass]
    ring
  have hsum : (∑ k ∈ latticeInterval n, c k) = W := hW
  have hp : 0 < W := hW ▸ normalizer_pos n hn le_rfl
  have hm0 := lower_moment_difference n ((n : ℝ)^2)
  rw [hW, sub_self, mul_zero, sub_eq_zero] at hm0
  have hm : (∑ k ∈ latticeInterval n, c k * (k : ℝ)^2) = W * ((n : ℝ)^2 - 1)/5 := by
    unfold momentNumerator at hm0
    dsimp [c]
    simp_rw [mul_comm ((n : ℝ)^2 - (_ : ℝ)^2)]
    rw [hm0]
    ring
  refine ⟨fun k hk => sub_nonneg.mpr ((sq_le_iff_mem k n).mpr hk), hp, hsum, hm, ?_⟩
  calc
    _ = ∑ k ∈ latticeInterval n, c k ^ 2 := by
      unfold nearCollisionMass
      simp_rw [int_near_eq _ _ hη hη']
      apply sum_congr rfl
      intro k hk
      simp [hk, pow_two]
    _ = (n : ℝ)^2 * (∑ k ∈ latticeInterval n, c k) -
        ∑ k ∈ latticeInterval n, c k * (k : ℝ)^2 := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k hk
      dsimp [c]
      ring
    _ = _ := by rw [hsum, hm]; ring

/-- With a resolution strictly below the lattice spacing, the normalized ratio approaches the
limiting collision coefficient while the resolution divided by the standard deviation vanishes. -/
theorem parabolic_collision_ratio_limit :
    let V := fun n : ℕ => ((n : ℝ)^2 - 1)/5
    let η := fun n : ℕ => (n : ℝ)/((n : ℝ)+1)
    let W := fun n : ℕ => (n : ℝ) * (4 * (n : ℝ)^2 - 1)/3
    let E := fun n : ℕ => nearCollisionMass (latticeInterval n)
      (fun k : ℤ => (k : ℝ)) (fun k => (n : ℝ)^2 - (k : ℝ)^2) (η n)
    Tendsto (fun n => η n / Real.sqrt (V n)) atTop (𝓝 0) ∧
    Tendsto (fun n => E n * Real.sqrt (V n) / (W n ^ 2 * η n)) atTop
      (𝓝 (3 / (5 * Real.sqrt 5))) := by
  intro V η W E
  let t := fun n : ℕ => (n : ℝ)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hs : Tendsto (fun n => Real.sqrt (1 - t n ^ 2)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (ht.pow 2) (a := (1 : ℝ)))
    simpa [Function.comp_def] using h
  have hplus : Tendsto (fun n => 1+t n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add ht (a := (1 : ℝ)))
  have htop : Tendsto (fun n => 4+t n^2) atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.add (ht.pow 2) (a := (4 : ℝ)))
  have hbot : Tendsto (fun n => 4-t n^2) atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.sub (ht.pow 2) (a := (4 : ℝ)))
  have hsmall : Tendsto (fun n => Real.sqrt 5 * t n / ((1+t n)*Real.sqrt (1-t n^2)))
      atTop (𝓝 0) := by
    convert (ht.const_mul (Real.sqrt 5)).div (hplus.mul hs) (by norm_num) using 1 <;> simp
  have hratio : Tendsto (fun n => (3/(5*Real.sqrt 5)) *
      ((4+t n^2)/(4-t n^2)) * Real.sqrt (1-t n^2) * (1+t n))
      atTop (𝓝 (3/(5*Real.sqrt 5))) := by
    convert (((htop.div hbot (by norm_num)).const_mul (3/(5*Real.sqrt 5))).mul hs).mul hplus using 1 <;> norm_num
  have heq (n : ℕ) (hn : 2 ≤ n) :
      Real.sqrt (V n) = (n : ℝ) * Real.sqrt (1-t n^2) / Real.sqrt 5 := by
    have hn0 : 0 < (n : ℝ) := by positivity
    have hs0 : 0 ≤ 1-t n^2 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have ht1 : 0 ≤ t n ∧ t n ≤ 1 := by
        dsimp [t]
        exact ⟨inv_nonneg.mpr hn0.le, inv_le_one_of_one_le₀ hn1⟩
      nlinarith [mul_nonneg ht1.1 (sub_nonneg.mpr ht1.2)]
    have hV : V n = (n : ℝ)^2 * (1-t n^2) / 5 := by
      dsimp [V, t]
      field_simp
    rw [hV, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hn0.le]
  constructor
  · apply hsmall.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [heq n hn]
    dsimp [η, t]
    field_simp
  · apply hratio.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn' : 0 < n := by omega
    have hn0 : 0 < (n : ℝ) := by positivity
    have hη0 : 0 ≤ η n := by dsimp [η]; positivity
    have hη1 : η n < 1 := by
      dsimp [η]
      exact (div_lt_one (by positivity)).mpr (by linarith)
    have hc := (separated_parabolic_collision n hn' (η n) hη0 hη1).2.2.2.2
    change E n = _ at hc
    rw [hc, heq n hn]
    dsimp [W, η, t]
    have h4 : (4 * (n : ℝ)^2-1) ≠ 0 := by
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    field_simp [hn0.ne', h4]
    <;> ring

#print axioms separated_parabolic_collision
#print axioms parabolic_collision_ratio_limit

end D5.S3.Fourier.Concentration.SeparatedParabolicCollision
