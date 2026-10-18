/- GID: D5/S3/Estimation/DataProcessing/UniformIidStrictPeakSharpness
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/UniformIidStrictPeakSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform ordered letter laws attain both determinant signs and approach the sharp lower surface. -/

import D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false
namespace D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
open scoped BigOperators
open Filter Topology Set
open IidStrictPeakSource FiniteIidStrictPeakLower
noncomputable section

/-- The law of one uniformly sampled ordered letter. -/
def uniform (q : ℕ) : Fin q → ℝ := fun _ => 1/(q : ℝ)

/-- The determinant is evaluated on the actual product-source pushforward. -/
def uniformDeterminant (q : ℕ) : ℝ :=
  modeLaw (uniform q) 0*modeLaw (uniform q) 3-
    modeLaw (uniform q) 1*modeLaw (uniform q) 2

/-- Determinants of independently specified finite ordered source laws. -/
def finiteDeterminants : Set ℝ := {d | ∃ (q : ℕ) (p : Fin q → ℝ),
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
  d = modeLaw p 0*modeLaw p 3-modeLaw p 1*modeLaw p 2}

private theorem power_sums (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 ∧
    (∑ i ∈ Finset.range n, (i : ℝ)^2) = (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 ∧
    (∑ i ∈ Finset.range n, (i : ℝ)^3) = ((n:ℝ)*((n:ℝ)-1))^2/4 ∧
    (∑ i ∈ Finset.range n, (i : ℝ)^4) =
      (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)*(3*(n:ℝ)^2-3*(n:ℝ)-1)/30 := by
  have h1 := sum_range_pow n 1
  have h2 := sum_range_pow n 2
  have h3 := sum_range_pow n 3
  have h4 := sum_range_pow n 4
  norm_num [Finset.sum_range_succ,bernoulli,Nat.choose] at h1 h2 h3 h4
  have r1 := congrArg (fun x : ℚ => (x : ℝ)) h1
  have r2 := congrArg (fun x : ℚ => (x : ℝ)) h2
  have r3 := congrArg (fun x : ℚ => (x : ℝ)) h3
  have r4 := congrArg (fun x : ℚ => (x : ℝ)) h4
  push_cast at r1 r2 r3 r4
  norm_num at r1 r2 r3 r4
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [r1,r2,r3,r4]

private theorem uniform_lower (q : ℕ) (i : Fin q) :
    lowerMass (uniform q) i = (i.val:ℝ)/(q:ℝ) := by
  classical
  have hf : lowerMass (uniform q) i =
      ∑ a ∈ Finset.univ.filter (fun a : Fin q => a < i), 1/(q:ℝ) := by
    unfold lowerMass uniform
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [hf]
  have he : Finset.univ.filter (fun j : Fin q => j < i) = Finset.Iio i := by
    ext j; simp
  rw [he,Finset.sum_const,Fin.card_Iio]
  simp [nsmul_eq_mul,div_eq_mul_inv]

private theorem upper_index_sum (q : ℕ) (c : Fin q) :
    (∑ b : Fin q, if c < b then (b.val:ℝ) else 0) =
      ((q:ℝ)*((q:ℝ)-1)-(c.val:ℝ)*((c.val:ℝ)+1))/2 := by
  have he : (∑ b : Fin q, if c < b then (b.val:ℝ) else 0) =
      ∑ b ∈ Finset.range q, if c.val < b then (b:ℝ) else 0 := by
    exact (Finset.sum_range (n := q) (fun b : ℕ => if c.val < b then (b : ℝ) else 0)).symm
  rw [he,← Finset.sum_filter]
  have hf : (Finset.range q).filter (fun b => c.val < b) = Finset.Ico (c.val+1) q := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [hf,Finset.sum_Ico_eq_sub _ (by omega)]
  rw [(power_sums q).1,(power_sums (c.val+1)).1]
  push_cast
  ring

private theorem uniform_wing (q : ℕ) (c : Fin q) :
    wingMass (uniform q) c =
      ((q:ℝ)*((q:ℝ)-1)-(c.val:ℝ)*((c.val:ℝ)+1))/(2*(q:ℝ)^2) := by
  unfold wingMass
  simp_rw [uniform_lower]
  have he (b : Fin q) : (if c < b then uniform q b*((b.val:ℝ)/(q:ℝ)) else 0) =
      (1/(q:ℝ)^2)*(if c < b then (b.val:ℝ) else 0) := by
    split_ifs <;> simp [uniform,div_eq_mul_inv,pow_two,mul_assoc,mul_comm,mul_left_comm]
  simp_rw [he]
  rw [← Finset.mul_sum,upper_index_sum]
  ring

private theorem uniform_formulas (q : ℕ) (hq : 0 < q) :
    modeLaw (uniform q) 1+modeLaw (uniform q) 3 =
      ((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2) ∧
    modeLaw (uniform q) 3 =
      (((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2))*
        (2*(q:ℝ)^2-2*(q:ℝ)+1)/(5*(q:ℝ)^2) ∧
    uniformDeterminant q =
      -((q:ℝ)-1)*(2*(q:ℝ)-1)*
        (2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1)/(180*(q:ℝ)^6) := by
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hp : ∀ i, 0 ≤ uniform q i := by intro i; unfold uniform; positivity
  have hs : ∑ i, uniform q i = 1 := by simp [uniform,hq0]
  obtain ⟨_,_,_,hx,_,_,hj,_,hd⟩ := iid_peak_source (uniform q) hp hs
  have hX : modeLaw (uniform q) 1+modeLaw (uniform q) 3 =
      ((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2) := by
    rw [hx]
    simp_rw [uniform_lower]
    have he (b : Fin q) : uniform q b*((b.val:ℝ)/(q:ℝ))^2 =
        (1/(q:ℝ)^3)*(b.val:ℝ)^2 := by unfold uniform; field_simp
    simp_rw [he]
    rw [← Finset.mul_sum,← (Finset.sum_range (n := q) (fun b : ℕ => (b : ℝ)^2)),
      (power_sums q).2.1]
    field_simp <;> ring
  have hK : modeLaw (uniform q) 3 =
      (((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2))*
        (2*(q:ℝ)^2-2*(q:ℝ)+1)/(5*(q:ℝ)^2) := by
    rw [hj]
    simp_rw [uniform_wing]
    have he (c : Fin q) : uniform q c*
        (((q:ℝ)*((q:ℝ)-1)-(c.val:ℝ)*((c.val:ℝ)+1))/(2*(q:ℝ)^2))^2 =
        (1/(4*(q:ℝ)^5))*(((q:ℝ)*((q:ℝ)-1))^2-
          2*((q:ℝ)*((q:ℝ)-1))*((c.val:ℝ)^2+(c.val:ℝ))+
          (c.val:ℝ)^4+2*(c.val:ℝ)^3+(c.val:ℝ)^2) := by
      unfold uniform
      field_simp
      ring
    simp_rw [he]
    rw [← Finset.mul_sum,← (Finset.sum_range (n := q) (fun c : ℕ =>
      ((q:ℝ)*((q:ℝ)-1))^2-2*((q:ℝ)*((q:ℝ)-1))*((c:ℝ)^2+(c:ℝ))+
      (c:ℝ)^4+2*(c:ℝ)^3+(c:ℝ)^2))]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [(power_sums q).1,(power_sums q).2.1,(power_sums q).2.2.1,(power_sums q).2.2.2]
    field_simp <;> ring
  refine ⟨hX,hK,?_⟩
  unfold uniformDeterminant
  rw [hd,← hx,← hj,hX,hK]
  field_simp
  ring

/-- Uniform finite sources realize the exact formulas, both determinant signs,
and the continuous sharp endpoint as a limit of their actual source laws. -/
theorem uniform_peak_sharpness :
    (∀ q : ℕ, 0 < q →
      modeLaw (uniform q) 1+modeLaw (uniform q) 3 =
        ((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2) ∧
      modeLaw (uniform q) 3 =
        (((q:ℝ)-1)*(2*(q:ℝ)-1)/(6*(q:ℝ)^2))*
          (2*(q:ℝ)^2-2*(q:ℝ)+1)/(5*(q:ℝ)^2) ∧
      uniformDeterminant q =
        -((q:ℝ)-1)*(2*(q:ℝ)-1)*
          (2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1)/(180*(q:ℝ)^6)) ∧
    (∀ q : ℕ, 2 ≤ q → q ≤ 5 → 0 < uniformDeterminant q) ∧
    (∀ q : ℕ, 6 ≤ q → uniformDeterminant q < 0) ∧
    Tendsto uniformDeterminant atTop (𝓝 (-1/45 : ℝ)) ∧
    IsGLB finiteDeterminants (-1/45) ∧ (-1/45 : ℝ) ∉ finiteDeterminants := by
  refine ⟨uniform_formulas,?_,?_,?_⟩
  · intro q hq2 hq5
    rw [(uniform_formulas q (by omega)).2.2]
    interval_cases q <;> norm_num
  · intro q hq
    rw [(uniform_formulas q (by omega)).2.2]
    have hqr : (6 : ℝ) ≤ q := by exact_mod_cast hq
    have hP : 0 < 2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1 := by
      have he : 2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1 =
          2*((q:ℝ)-6)^4+35*((q:ℝ)-6)^3+207*((q:ℝ)-6)^2+427*((q:ℝ)-6)+79 := by ring
      rw [he]
      positivity
    apply div_neg_of_neg_of_pos
    · have : 0 < ((q:ℝ)-1)*(2*(q:ℝ)-1)*
          (2*(q:ℝ)^4-13*(q:ℝ)^3+9*(q:ℝ)^2-5*(q:ℝ)+1) :=
        mul_pos (mul_pos (by linarith) (by linarith)) hP
      nlinarith
    · positivity
  · let f := fun t : ℝ => -1/45+(8/45)*t-(59/180)*t^2+(5/18)*t^3-
        (13/90)*t^4+(2/45)*t^5-(1/180)*t^6
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hinv : Tendsto (fun q : ℕ => 1/(q:ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div,Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have ht := hf.continuousAt.tendsto.comp hinv
    have heq : uniformDeterminant =ᶠ[atTop] fun q => f (1/(q:ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with q hq
      rw [(uniform_formulas q (by omega)).2.2]
      have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
      dsimp [f]
      field_simp
      ring
    have hf0 : f 0 = (-1/45 : ℝ) := by norm_num [f]
    rw [hf0] at ht
    have hlim : Tendsto uniformDeterminant atTop (𝓝 (-1/45 : ℝ)) :=
      ht.congr' heq.symm
    have hstrict : ∀ d ∈ finiteDeterminants, (-1/45 : ℝ) < d := by
      rintro d ⟨q,p,hp,hs,rfl⟩
      exact (finite_iid_lower_surface p hp hs).2.2.2.2.2.1
    refine ⟨hlim,⟨fun d hd => (hstrict d hd).le,?_⟩,?_⟩
    · intro b hb
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop 1] with q hq
      apply hb
      refine ⟨q,uniform q,?_,?_,rfl⟩
      · intro i; unfold uniform; positivity
      · have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
        simp [uniform,hq0]
    · intro h
      exact (lt_irrefl (-1/45 : ℝ)) (hstrict _ h)

#print axioms uniform_peak_sharpness
end
end D5.S3.Estimation.DataProcessing.UniformIidStrictPeakSharpness
