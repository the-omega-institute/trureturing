/- GID: D5/S3/Fourier/Concentration/FiniteCollisionVariance
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteCollisionVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-resolution collision mass has a variance lower bound. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

namespace D5.S3.Fourier.Concentration.FiniteCollisionVariance

private def exponentialSum {I : Type*} (s : Finset I) (x c : I → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, c i * Real.exp (x i * t)

private theorem exponentialSum_deriv {I : Type*} (s : Finset I) (x c : I → ℝ) (t : ℝ) :
    HasDerivAt (exponentialSum s x c)
      (exponentialSum s x (fun i => c i * x i) t) t := by
  unfold exponentialSum
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := (((hasDerivAt_id t).const_mul (x i)).exp).const_mul (c i)
  convert h using 1 <;> simp only [id_eq, mul_one] <;> ring

private theorem exponentialSum_pow {J : Type*} [Fintype J] [DecidableEq J]
    (x w : J → ℝ) (p : ℕ) (t : ℝ) :
    exponentialSum univ x w t ^ p =
      exponentialSum (piAntidiag univ p) (monomialFrequency x) (monomialWeight w) t := by
  unfold exponentialSum
  rw [sum_pow_eq_sum_piAntidiag]
  apply sum_congr rfl
  intro m _
  unfold monomialWeight monomialFrequency
  rw [mul_assoc, sum_mul, Real.exp_sum]
  congr 1
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

private theorem sum_monomialWeight {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) :
    (∑ m ∈ piAntidiag univ p, monomialWeight w m) = (∑ j, w j) ^ p := by
  have h := exponentialSum_pow (fun _ => 0 : J → ℝ) w p 0
  simpa [exponentialSum] using h.symm

private theorem centered_second_moment {J : Type*} [Fintype J] [DecidableEq J]
    (x w : J → ℝ) (p : ℕ) (hcenter : ∑ j, w j * x j = 0) :
    (∑ m ∈ piAntidiag univ p, monomialWeight w m * monomialFrequency x m ^ 2) =
      (p : ℝ) * (∑ j, w j) ^ (p - 1) * ∑ j, w j * x j ^ 2 := by
  let s := piAntidiag (univ : Finset J) p
  let freq := monomialFrequency x
  let coeff := monomialWeight w
  let A := exponentialSum univ x w
  let B := exponentialSum univ x (fun j => w j * x j)
  let C := exponentialSum univ x (fun j => w j * x j * x j)
  let D := exponentialSum s freq (fun m => coeff m * freq m)
  have hpow (t : ℝ) : A t ^ p = exponentialSum s freq coeff t :=
    exponentialSum_pow x w p t
  have hfirst : D = fun t => (p : ℝ) * A t ^ (p - 1) * B t := by
    funext t
    have hleft := (exponentialSum_deriv (univ : Finset J) x w t).pow p
    have hright := exponentialSum_deriv s freq coeff t
    have heq : (fun t => A t ^ p) = exponentialSum s freq coeff := funext hpow
    change HasDerivAt (fun t => A t ^ p) _ t at hleft
    rw [heq] at hleft
    exact hright.unique hleft
  have hB0 : B 0 = 0 := by simpa [B, exponentialSum] using hcenter
  have hL := exponentialSum_deriv s freq (fun m => coeff m * freq m) 0
  change HasDerivAt D _ 0 at hL
  rw [hfirst] at hL
  have hA := ((exponentialSum_deriv (univ : Finset J) x w 0).pow (p - 1)).const_mul (p : ℝ)
  have hB := exponentialSum_deriv (univ : Finset J) x (fun j => w j * x j) 0
  change HasDerivAt _ (C 0) 0 at hB
  have hR := hA.mul hB
  change HasDerivAt (fun t => (p : ℝ) * A t ^ (p - 1) * B t)
    (_ * B 0 + (p : ℝ) * A 0 ^ (p - 1) * C 0) 0 at hR
  have h := hL.unique hR
  simpa [hB0, A, C, exponentialSum, s, coeff, freq, pow_two, mul_assoc] using h

private theorem interval_mass_sq_le {I : Type*} (s : Finset I) (x c : I → ℝ)
    {a d η : ℝ} (hd : 0 ≤ d) (hη : 0 < η) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ a + d) :
    (∑ i ∈ s, c i) ^ 2 ≤ (1 + d / η) * nearCollisionMass s x c η := by
  let b (i : I) : ℤ := ⌊(x i - a) / η⌋
  let bins := s.image b
  let mass (k : ℤ) := ∑ i ∈ s with b i = k, c i
  have hdiag : (∑ k ∈ bins, mass k ^ 2) ≤ nearCollisionMass s x c η := by
    apply sum_bin_mass_sq_le_nearCollisionMass s x c b η hc
    intro i _ j _ hb
    have hii := Int.floor_le ((x i - a) / η)
    have his := Int.lt_floor_add_one ((x i - a) / η)
    have hjj := Int.floor_le ((x j - a) / η)
    have hjs := Int.lt_floor_add_one ((x j - a) / η)
    change (b i : ℝ) ≤ _ at hii
    change _ < (b i : ℝ) + 1 at his
    change (b j : ℝ) ≤ _ at hjj
    change _ < (b j : ℝ) + 1 at hjs
    rw [← hb] at hjj hjs
    have hdiff : |(x i - a) / η - (x j - a) / η| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hη, div_le_iff₀ hη,
      one_mul] at hdiff
    exact hdiff
  have hsubset : bins ⊆ Icc (0 : ℤ) ⌊d / η⌋ := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
    exact mem_Icc.2 ⟨Int.floor_nonneg.2 (div_nonneg (sub_nonneg.2 (hx i hi).1) hη.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith [(hx i hi).2]) hη.le)⟩
  have hcard : (bins.card : ℝ) ≤ 1 + d / η := by
    have h := card_le_card hsubset
    rw [Int.card_Icc, sub_zero] at h
    have hb : 0 ≤ ⌊d / η⌋ + 1 :=
      (Int.floor_nonneg.2 (div_nonneg hd hη.le)).trans (by omega)
    have ht : ((⌊d / η⌋ + 1).toNat : ℝ) = (⌊d / η⌋ : ℝ) + 1 := by
      exact_mod_cast Int.toNat_of_nonneg hb
    have hc' : (bins.card : ℝ) ≤ ((⌊d / η⌋ + 1).toNat : ℝ) := by exact_mod_cast h
    rw [ht] at hc'
    linarith [Int.floor_le (d / η)]
  have hsum : (∑ k ∈ bins, mass k) = ∑ i ∈ s, c i :=
    sum_fiberwise_of_maps_to (fun _ hi => mem_image_of_mem b hi) _
  have hnonneg : 0 ≤ ∑ k ∈ bins, mass k ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ = (∑ k ∈ bins, mass k) ^ 2 := by rw [hsum]
    _ ≤ (bins.card : ℝ) * ∑ k ∈ bins, mass k ^ 2 := by
      simpa [mul_comm] using sum_mul_sq_le_sq_mul_sq bins (fun _ => (1 : ℝ)) mass
    _ ≤ (1 + d / η) * nearCollisionMass s x c η :=
      mul_le_mul hcard hdiag hnonneg (by positivity)

private theorem nearCollisionMass_mono {I : Type*} {s u : Finset I} (x c : I → ℝ)
    (η : ℝ) (hu : u ⊆ s) (hc : ∀ i ∈ s, 0 ≤ c i) :
    nearCollisionMass u x c η ≤ nearCollisionMass s x c η := by
  classical
  unfold nearCollisionMass
  have hnonneg (i j : I) (hi : i ∈ s) (hj : j ∈ s) :
      0 ≤ if |x i - x j| ≤ η then c i * c j else 0 := by
    split_ifs
    · exact mul_nonneg (hc i hi) (hc j hj)
    · exact le_rfl
  calc
    _ ≤ ∑ i ∈ u, ∑ j ∈ s, if |x i - x j| ≤ η then c i * c j else 0 := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum_of_subset_of_nonneg hu fun j hj _ => hnonneg i j (hu hi) hj
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hu
      (fun i hi _ => sum_nonneg fun j hj => hnonneg i j hi hj)

private theorem central_mass {I : Type*} (s : Finset I) (x c : I → ℝ)
    (a V : ℝ) (hV : 0 ≤ V) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hm : ∑ i ∈ s, c i * (x i - a) ^ 2 ≤ V * ∑ i ∈ s, c i) :
    3 / 4 * (∑ i ∈ s, c i) ≤ ∑ i ∈ s with |x i - a| ≤ 2 * √V, c i := by
  classical
  let R : ℝ := 2 * √V
  let inside := s.filter (fun i => |x i - a| ≤ R)
  let outside := s.filter (fun i => ¬ |x i - a| ≤ R)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hout : outside ⊆ s := filter_subset _ _
  have hsplit : (∑ i ∈ inside, c i) + (∑ i ∈ outside, c i) = ∑ i ∈ s, c i :=
    sum_filter_add_sum_filter_not s (fun i => |x i - a| ≤ R) c
  have hmoment :
      (∑ i ∈ outside, c i * (x i - a) ^ 2) ≤ V * ∑ i ∈ s, c i :=
    (sum_le_sum_of_subset_of_nonneg hout (fun i hi _ => mul_nonneg (hc i hi) (sq_nonneg _))).trans hm
  have hB : (∑ i ∈ outside, c i) ≤ (∑ i ∈ s, c i) / 4 := by
    rcases hV.eq_or_lt with hzero | hpos
    · have hz : V = 0 := hzero.symm
      have hweights (i : I) (hi : i ∈ outside) : c i = 0 := by
        have hj : R < |x i - a| := lt_of_not_ge (mem_filter.1 hi).2
        have hx : x i - a ≠ 0 := by
          intro he
          rw [he, abs_zero] at hj
          exact (not_lt_of_ge hR) hj
        have hsingle := single_le_sum
          (f := fun j => c j * (x j - a) ^ 2)
          (fun j hj => mul_nonneg (hc j (hout hj)) (sq_nonneg _)) hi
        have hle : c i * (x i - a) ^ 2 ≤ 0 := by
          simpa [hz] using hsingle.trans hmoment
        have heq := le_antisymm hle (mul_nonneg (hc i (hout hi)) (sq_nonneg _))
        exact (mul_eq_zero.mp heq).resolve_right (pow_ne_zero _ hx)
      rw [sum_eq_zero hweights]
      exact div_nonneg (sum_nonneg hc) (by norm_num)
    · have hsq : R ^ 2 = 4 * V := by
        dsimp [R]
        rw [mul_pow, Real.sq_sqrt hV]
        norm_num
      have hbound : R ^ 2 * (∑ i ∈ outside, c i) ≤
          ∑ i ∈ outside, c i * (x i - a) ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun i hi => ?_
        have hle : R ≤ |x i - a| := (lt_of_not_ge (mem_filter.1 hi).2).le
        have hle2 := pow_le_pow_left₀ hR hle 2
        rw [sq_abs] at hle2
        rw [mul_comm (R ^ 2)]
        exact mul_le_mul_of_nonneg_left hle2 (hc i (hout hi))
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      apply (le_of_mul_le_mul_left ?_ hpos)
      have hk := hbound.trans hmoment
      rw [hsq] at hk
      convert hk using 1
      ring
  change _ ≤ ∑ i ∈ inside, c i
  linarith

private theorem collision_lower_of_second_moment {I : Type*} (s : Finset I) (x c : I → ℝ)
    (a : ℝ) {V η : ℝ} (hV : 0 ≤ V) (hη : 0 < η) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hm : ∑ i ∈ s, c i * (x i - a) ^ 2 ≤ V * ∑ i ∈ s, c i) :
    (9 / 16 : ℝ) * (∑ i ∈ s, c i) ^ 2 ≤
      (1 + 4 * √V / η) * nearCollisionMass s x c η := by
  let R : ℝ := 2 * √V
  let u := s.filter (fun i => |x i - a| ≤ R)
  have hu : u ⊆ s := filter_subset _ _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hin (i : I) (hi : i ∈ u) : a - R ≤ x i ∧ x i ≤ (a - R) + 2 * R := by
    have hb := abs_le.mp (mem_filter.mp hi).2
    constructor <;> linarith [hb.1, hb.2]
  have hcentral := central_mass s x c a V hV hc hm
  have hconst : 2 * R = 4 * √V := by dsimp [R]; ring
  calc
    _ = (3 / 4 * (∑ i ∈ s, c i)) ^ 2 := by ring
    _ ≤ (∑ i ∈ u, c i) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (sum_nonneg hc)) hcentral 2
    _ ≤ (1 + 2 * R / η) * nearCollisionMass u x c η :=
      interval_mass_sq_le u x c (mul_nonneg (by norm_num) hR) hη (fun i hi => hc i (hu hi)) hin
    _ ≤ (1 + 4 * √V / η) * nearCollisionMass s x c η := by
      rw [hconst]
      exact mul_le_mul_of_nonneg_left (nearCollisionMass_mono x c η hu hc) (by positivity)

private theorem monomialFrequency_sub_const {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) (a : ℝ) {p : ℕ} {m : J → ℕ} (hm : m ∈ piAntidiag univ p) :
    monomialFrequency (fun j => g j - a) m = monomialFrequency g m - (p : ℝ) * a := by
  have hp : ∑ j, (m j : ℝ) = (p : ℝ) := by exact_mod_cast (mem_piAntidiag.mp hm).1
  simp only [monomialFrequency, mul_sub, sum_sub_distrib, ← sum_mul, hp]

/-- Every positive-resolution moment certificate pays for a central interval of the p-fold score. -/
theorem tailCollisionMass_lower_variance {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hW : 0 < ∑ j, w j) {p : ℕ} (hp : 0 < p)
    {η : ℝ} (hη : 0 < η) :
    let W := ∑ j, w j
    let μ := (∑ j, w j * g j) / W
    let V := (∑ j, w j * (g j - μ) ^ 2) / W
    (9 / 16 : ℝ) * W ^ (2 * p) ≤
      (1 + 4 * √((p : ℝ) * V) / η) * tailCollisionMass g w p η := by
  classical
  intro W μ V
  let x : J → ℝ := fun j => g j - μ
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  have hc (m : J → ℕ) (_ : m ∈ s) : 0 ≤ c m := monomialWeight_nonneg w hw m
  have hV : 0 ≤ V := div_nonneg (sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)) hW.le
  have hcenter : ∑ j, w j * x j = 0 := by
    simp only [x, mul_sub, sum_sub_distrib, ← sum_mul]
    change (∑ j, w j * g j) - W * ((∑ j, w j * g j) / W) = 0
    rw [mul_comm W, div_mul_cancel₀ _ hW.ne', sub_self]
  have hsum : ∑ m ∈ s, c m = W ^ p := sum_monomialWeight w p
  have hVmul : V * W = ∑ j, w j * x j ^ 2 := div_mul_cancel₀ _ hW.ne'
  have hpow : W ^ (p - 1) * W = W ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp]
  have hsecond : ∑ m ∈ s, c m * (monomialFrequency x m - 0) ^ 2 ≤
      ((p : ℝ) * V) * ∑ m ∈ s, c m := by
    rw [hsum]
    simp only [sub_zero]
    rw [centered_second_moment x w p hcenter, ← hVmul, ← hpow]
    change (p : ℝ) * W ^ (p - 1) * (V * W) ≤ (p : ℝ) * V * (W ^ (p - 1) * W)
    exact le_of_eq (by ring)
  have hcollision : nearCollisionMass s (monomialFrequency x) c η = tailCollisionMass g w p η := by
    unfold nearCollisionMass tailCollisionMass
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    change (if |monomialFrequency x m - monomialFrequency x n| ≤ η then c m * c n else 0) =
      (if |monomialFrequency g m - monomialFrequency g n| ≤ η then c m * c n else 0)
    rw [monomialFrequency_sub_const g μ hm, monomialFrequency_sub_const g μ hn,
      sub_sub_sub_cancel_right]
  have h := collision_lower_of_second_moment s (monomialFrequency x) c 0
    (mul_nonneg (Nat.cast_nonneg p) hV) hη hc hsecond
  rw [hsum, hcollision, ← pow_mul, mul_comm p 2] at h
  exact h

#print axioms tailCollisionMass_lower_variance

end D5.S3.Fourier.Concentration.FiniteCollisionVariance
