/- GID: D5/S3/Fourier/Concentration/FejerCollisionSecants
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FejerCollisionSecants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Secants of the triangular collision ramp bound and recover closed collision bands. -/

import D5.S3.Fourier.Concentration.FejerCollisionVariance

/-! Positive-part increments distinguish the closed collision band from its outer shell. -/

open Finset MeasureTheory
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

noncomputable section

namespace D5.S3.Fourier.Concentration.FejerCollisionSecants

/-- The triangular collision moment multiplied by the band radius. -/
def rampCollisionMass {I : Type*} (s : Finset I) (x c : I → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, c i*c j * max 0 (r-|x i-x j|)

private theorem ramp_left_le (r d δ : ℝ) (hδ : 0 < δ) :
    max 0 (r-d)-max 0 (r-δ-d) ≤ if d≤r then δ else 0 := by
  split_ifs with hd
  · rw [max_eq_right (sub_nonneg.mpr hd)]
    linarith [le_max_right (0:ℝ) (r-δ-d)]
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    simp

private theorem ramp_right_ge (r d δ : ℝ) (hδ : 0 < δ) :
    (if d≤r then δ else 0) ≤ max 0 (r+δ-d)-max 0 (r-d) := by
  split_ifs with hd
  · rw [max_eq_right (by linarith),max_eq_right (sub_nonneg.mpr hd)]
    linarith
  · rw [show max 0 (r-d) = 0 by exact max_eq_left (by linarith)]
    simp

private theorem ramp_right_eq (r d δ : ℝ) (hδ : 0 < δ)
    (hgap : d≤r ∨ r+δ≤d) :
    max 0 (r+δ-d)-max 0 (r-d) = if d≤r then δ else 0 := by
  rcases hgap with hd | hd
  · rw [ite_eq_left hd,max_eq_right (by linarith),max_eq_right (sub_nonneg.mpr hd)]
    ring
  · rw [ite_eq_right (by linarith),max_eq_left (by linarith),max_eq_left (by linarith),sub_zero]

/-- Left and right increments of the ramp bracket the closed-band collision mass. -/
theorem collision_ramp_secants {I : Type*} (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    let ramp := fun z : ℝ × ℝ => max 0 (z.1-z.2)
    let L := fun t => ∑ i ∈ s, ∑ j ∈ s, c i*c j*ramp (t,|x i-x j|)
    L r-L (r-δ) ≤ δ*nearCollisionMass s x c r ∧
      δ*nearCollisionMass s x c r ≤ L (r+δ)-L r := by
  intro ramp L
  change rampCollisionMass s x c r-rampCollisionMass s x c (r-δ) ≤ δ*nearCollisionMass s x c r ∧
      δ*nearCollisionMass s x c r ≤ rampCollisionMass s x c (r+δ)-rampCollisionMass s x c r
  unfold rampCollisionMass nearCollisionMass
  simp_rw [← sum_sub_distrib,← mul_sub,mul_sum]
  constructor
  · apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_left (ramp_left_le r |x i-x j| δ hδ)
      (mul_nonneg (hc i hi) (hc j hj))
    simpa only [mul_ite,ite_mul,mul_zero,zero_mul,mul_comm δ] using h
  · apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_left (ramp_right_ge r |x i-x j| δ hδ)
      (mul_nonneg (hc i hi) (hc j hj))
    simpa only [mul_ite,ite_mul,mul_zero,zero_mul,mul_comm δ] using h

/-- Finiteness gives a nonzero interval on which the right quotient is exact, even for signed weights. -/
theorem collision_ramp_exact_right {I : Type*} (s : Finset I) (x c : I → ℝ) (r : ℝ) :
    let ramp := fun z : ℝ × ℝ => max 0 (z.1-z.2)
    let L := fun t => ∑ i ∈ s, ∑ j ∈ s, c i*c j*ramp (t,|x i-x j|)
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      L (r+δ)-L r = δ*nearCollisionMass s x c r := by
  intro ramp L
  classical
  let outer := (s ×ˢ s).filter (fun ij => r < |x ij.1-x ij.2|)
  let gaps := outer.image (fun ij => |x ij.1-x ij.2|-r)
  let D := insert (1:ℝ) gaps
  have hD : D.Nonempty := ⟨1,mem_insert_self _ _⟩
  let δ₀ := D.min' hD
  have hδ₀ : 0 < δ₀ := by
    have hm := D.min'_mem hD
    change δ₀ ∈ insert (1:ℝ) gaps at hm
    rcases mem_insert.mp hm with he | hg
    · rw [he]; norm_num
    · obtain ⟨ij,hij,he⟩ := mem_image.mp hg
      rw [← he]
      exact sub_pos.mpr (mem_filter.mp hij).2
  refine ⟨δ₀,hδ₀,?_⟩
  intro δ hδ hδle
  change rampCollisionMass s x c (r+δ)-rampCollisionMass s x c r =
    δ*nearCollisionMass s x c r
  unfold rampCollisionMass nearCollisionMass
  simp_rw [← sum_sub_distrib,← mul_sub,mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hgap : |x i-x j|≤r ∨ r+δ≤|x i-x j| := by
    by_cases hd : |x i-x j|≤r
    · exact Or.inl hd
    · right
      have hm : |x i-x j|-r ∈ D := mem_insert_of_mem
        (mem_image.mpr ⟨(i,j),mem_filter.mpr ⟨mem_product.mpr ⟨hi,hj⟩,lt_of_not_ge hd⟩,rfl⟩)
      have hmin : δ₀ ≤ |x i-x j|-r := D.min'_le _ hm
      linarith
  have h := congrArg (fun v : ℝ => c i*c j*v) (ramp_right_eq r |x i-x j| δ hδ hgap)
  simpa only [mul_ite,ite_mul,mul_zero,zero_mul,mul_comm δ] using h

#print axioms collision_ramp_secants
#print axioms collision_ramp_exact_right

end D5.S3.Fourier.Concentration.FejerCollisionSecants
