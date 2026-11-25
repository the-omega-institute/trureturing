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
    :
    let mass := fun m : ℕ => (m : ℝ) * (4 * (m : ℝ)^2 - 1) / 3
    let c := fun k : ℤ => (n : ℝ)^2 - (k : ℝ)^2
    let W := mass n
    (∀ k ∈ latticeInterval n, 0 ≤ c k) ∧
    0 < W ∧
    (∑ k ∈ latticeInterval n, c k) = W ∧
    (∑ k ∈ latticeInterval n, c k * (k : ℝ)^2) = W * ((n : ℝ)^2 - 1)/5 ∧
    (nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η =
      W * (4 * (n : ℝ)^2 + 1)/5 ↔ 0 ≤ η ∧ (n = 1 ∨ η < 1)) := by
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
  have hc : ∀ k ∈ latticeInterval n, 0 ≤ c k :=
    fun k hk => sub_nonneg.mpr ((sq_le_iff_mem k n).mpr hk)
  have hdiag : (∑ k ∈ latticeInterval n, c k ^ 2) = W * (4 * (n : ℝ)^2 + 1)/5 := by
    calc
      _ = (n : ℝ)^2 * (∑ k ∈ latticeInterval n, c k) -
          ∑ k ∈ latticeInterval n, c k * (k : ℝ)^2 := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro k hk
        dsimp [c]
        ring
      _ = _ := by rw [hsum, hm]; ring
  refine ⟨hc, hp, hsum, hm, ?_⟩
  have htarget : 0 < W * (4 * (n : ℝ)^2 + 1)/5 := by positivity
  have hn0 (hη : η < 0) :
      nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η = 0 := by
    unfold nearCollisionMass
    simp only [show ∀ i j : ℤ, ¬ |(i : ℝ) - (j : ℝ)| ≤ η from
      fun i j h => not_lt_of_ge ((abs_nonneg _).trans h) hη, ite_false, sum_const_zero]
  have hsmall (hη : 0 ≤ η) (hη' : η < 1) :
      nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η =
        W * (4 * (n : ℝ)^2 + 1)/5 := by
    unfold nearCollisionMass
    simp_rw [int_near_eq _ _ hη hη']
    rw [← hdiag]
    apply sum_congr rfl
    intro k hk
    simp [hk, pow_two]
  have hone (he : n = 1) (hη : 0 ≤ η) :
      nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η =
        W * (4 * (n : ℝ)^2 + 1)/5 := by
    subst n
    have hset : latticeInterval 1 = {(-1 : ℤ), 0, 1} := by decide
    dsimp [W, mass, c]
    rw [hset]
    unfold nearCollisionMass
    norm_num [hη, Finset.sum_insert, Finset.sum_singleton]
  have hlarge (hn2 : 2 ≤ n) (hη : 1 ≤ η) :
      W * (4 * (n : ℝ)^2 + 1)/5 <
        nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η := by
    rw [← hdiag]
    unfold nearCollisionMass
    let s := latticeInterval n
    have hzero : (0 : ℤ) ∈ s := by
      dsimp [s]
      apply (sq_le_iff_mem _ _).mp
      norm_num
    have hone : (1 : ℤ) ∈ s := by
      dsimp [s]
      apply (sq_le_iff_mem _ _).mp
      have h : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      norm_num
      nlinarith
    have hrow (i : ℤ) (hi : i ∈ s) :
        c i ^ 2 ≤ ∑ j ∈ s, if |(i : ℝ) - (j : ℝ)| ≤ η then c i * c j else 0 := by
      calc
        _ = ∑ j ∈ s, if i = j then c i * c j else 0 := by
          simp [hi, pow_two]
        _ ≤ _ := by
          apply sum_le_sum
          intro j hj
          by_cases hij : i = j
          · subst j
            simp [show 0 ≤ η by linarith]
          · simp only [hij, ite_false]
            split_ifs
            · exact mul_nonneg (hc i hi) (hc j hj)
            · exact le_rfl
    apply sum_lt_sum (fun i hi => hrow i hi)
    refine ⟨0, hzero, ?_⟩
    calc
      _ = ∑ j ∈ s, if (0 : ℤ) = j then c 0 * c j else 0 := by
        simp [hzero, pow_two]
      _ < _ := by
        apply sum_lt_sum
        · intro j hj
          by_cases hj0 : (0 : ℤ) = j
          · subst j
            simp [show 0 ≤ η by linarith]
          · simp only [hj0, ite_false]
            split_ifs
            · exact mul_nonneg (hc 0 hzero) (hc j hj)
            · exact le_rfl
        · refine ⟨1, hone, ?_⟩
          have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          have hc0 : 0 < c 0 := by dsimp [c]; norm_num; nlinarith
          have hc1 : 0 < c 1 := by dsimp [c]; norm_num; nlinarith
          simpa [hη] using mul_pos hc0 hc1
  constructor
  · intro h
    have hη : 0 ≤ η := by
      by_contra! hneg
      rw [hn0 hneg] at h
      linarith
    refine ⟨hη, ?_⟩
    by_contra! hh
    have hn2 : 2 ≤ n := by omega
    exact (ne_of_gt (hlarge hn2 hh.2)) h
  · rintro ⟨hη, he | he⟩
    · exact hone he hη
    · exact hsmall hη he

/-- With a resolution strictly below the lattice spacing, the normalized ratio approaches the
limiting collision coefficient while the resolution divided by the standard deviation vanishes. -/
theorem parabolic_collision_ratio_limit (η : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hη : ∀ᶠ n in atTop, 0 < η n ∧ η n < 1) (hlim : Tendsto η atTop (𝓝 L)) :
    let V := fun n : ℕ => ((n : ℝ)^2 - 1)/5
    let W := fun n : ℕ => (n : ℝ) * (4 * (n : ℝ)^2 - 1)/3
    let E := fun n : ℕ => nearCollisionMass (latticeInterval n)
      (fun k : ℤ => (k : ℝ)) (fun k => (n : ℝ)^2 - (k : ℝ)^2) (η n)
    Tendsto (fun n => η n / Real.sqrt (V n)) atTop (𝓝 0) ∧
    Tendsto (fun n => E n * Real.sqrt (V n) / (W n ^ 2 * η n)) atTop
      (𝓝 (3 / (5 * Real.sqrt 5 * L))) := by
  intro V W E
  let t := fun n : ℕ => (n : ℝ)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hs : Tendsto (fun n => Real.sqrt (1 - t n ^ 2)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (ht.pow 2) (a := (1 : ℝ)))
    simpa [Function.comp_def] using h
  have htop : Tendsto (fun n => 4+t n^2) atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.add (ht.pow 2) (a := (4 : ℝ)))
  have hbot : Tendsto (fun n => 4-t n^2) atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.sub (ht.pow 2) (a := (4 : ℝ)))
  have hsmall : Tendsto (fun n => Real.sqrt 5 * t n * η n / Real.sqrt (1-t n^2))
      atTop (𝓝 0) := by
    convert ((ht.const_mul (Real.sqrt 5)).mul hlim).div hs (by norm_num) using 1 <;> simp
  have hratio : Tendsto (fun n => ((3/(5*Real.sqrt 5)) *
      ((4+t n^2)/(4-t n^2)) * Real.sqrt (1-t n^2)) / η n)
      atTop (𝓝 (3/(5*Real.sqrt 5*L))) := by
    convert (((htop.div hbot (by norm_num)).const_mul (3/(5*Real.sqrt 5))).mul hs).div
      hlim hL.ne' using 1 <;> simp [div_div]
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
    dsimp [t]
    field_simp
  · apply hratio.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ), hη] with n hn hηn
    have hn' : 0 < n := by omega
    have hn0 : 0 < (n : ℝ) := by positivity
    have hc := (separated_parabolic_collision n hn' (η n)).2.2.2.2.mpr
      ⟨hηn.1.le, Or.inr hηn.2⟩
    change E n = _ at hc
    rw [hc, heq n hn]
    dsimp [W, t]
    have h4 : (4 * (n : ℝ)^2-1) ≠ 0 := by
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    field_simp [hn0.ne', h4, hηn.1.ne']

#print axioms separated_parabolic_collision
#print axioms parabolic_collision_ratio_limit

end D5.S3.Fourier.Concentration.SeparatedParabolicCollision
