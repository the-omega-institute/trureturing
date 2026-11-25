/- GID: D5/S3/Fourier/Concentration/OccupationDiagonalFloor
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/OccupationDiagonalFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multinomial occupation concentration gives a dimension-sensitive diagonal lower bound. -/

import D5.S3.Fourier.Concentration.FiniteCollisionVariance
import D5.S3.Fourier.Concentration.FejerCollisionVariance

open Finset MeasureTheory
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.FiniteCollisionVariance
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Analytic.Fourier.AngularFejerKernel

noncomputable section

namespace D5.S3.Fourier.Concentration.OccupationDiagonalFloor

private lemma coordinate_second_moment {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (hW : ∑ j,w j = 1) (p : ℕ) (j : J) :
    (∑ m ∈ piAntidiag univ p, monomialWeight w m * ((m j:ℝ)-(p:ℝ)*w j)^2) = (p:ℝ)*(w j-(w j)^2) := by
  let x : J → ℝ := fun i => (if i=j then 1 else 0)-w j
  have hcenter : ∑ i,w i*x i=0 := by
    simp only [x,mul_sub,sum_sub_distrib,← sum_mul,hW]
    simp [mul_ite]
  have hmoment := centered_second_moment x w p hcenter
  rw [hW,one_pow,mul_one] at hmoment
  have hx (m : J → ℕ) (hm : m ∈ piAntidiag univ p) :
      monomialFrequency x m = (m j:ℝ)-(p:ℝ)*w j := by
    unfold monomialFrequency x
    simp only [mul_sub,sum_sub_distrib,← sum_mul,← Nat.cast_sum,(mem_piAntidiag.mp hm).1]
    simp [mul_ite]
  have hc : ∑ i,w i*x i^2 = w j-(w j)^2 := by
    have he (i : J) : x i^2 = (if i=j then 1 else 0) - 2*(if i=j then 1 else 0)*w j+(w j)^2 := by
      by_cases hi : i=j <;> simp [x,hi]; ring
    simp_rw [he,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
    rw [← sum_mul,hW,one_mul]
    have heq : (∑ i, w i*(2*(if i=j then 1 else 0)*w j)) = 2*(w j)^2 := by
      simp [mul_ite]
      ring
    rw [heq]
    simp [mul_ite]
    ring
  calc
    _ = ∑ m ∈ piAntidiag univ p, monomialWeight w m * monomialFrequency x m ^ 2 := by
      apply sum_congr rfl
      intro m hm
      rw [hx m hm]
    _ = (p:ℝ)*(∑ i,w i*x i^2) := hmoment
    _ = (p:ℝ)*(w j-(w j)^2) := by rw [hc]

private lemma int_interval_card (a r : ℝ) (hr : 0 ≤ r) :
    ((Icc ⌈a-r⌉ ⌊a+r⌋ : Finset ℤ).card : ℝ) ≤ 1+2*r := by
  rw [Int.card_Icc]
  by_cases h : 0 ≤ ⌊a+r⌋+1-⌈a-r⌉
  · have he : (((⌊a+r⌋+1-⌈a-r⌉ : ℤ).toNat : ℕ):ℝ) =
        (⌊a+r⌋:ℝ)+1-(⌈a-r⌉:ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [he]
    linarith [Int.floor_le (a+r),Int.le_ceil (a-r)]
  · rw [Int.toNat_of_nonpos (le_of_not_ge h)]
    push_cast
    linarith

/-- The actual multinomial occupation diagonal retains an inverse square-root volume lower bound. -/
theorem occupation_diagonal_lower {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (hw : ∀ j, 0≤w j) (hW : ∑ j,w j=1) (j0 : J) (p : ℕ)
    (r : {j : J // j ≠ j0} → ℝ) (hr : ∀ j, 0 < r j) :
    let width := fun x : ℝ => 1+2*x
    let v := ∑ j : {j : J // j ≠ j0}, (p:ℝ)*(w j.1-(w j.1)^2)/(r j)^2
    (max 0 (1-v))^2 ≤ (∏ j,width (r j))*diagonal w p := by
  intro width v
  classical
  let K := {j : J // j ≠ j0}
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let e := fun m : J → ℕ => ∑ j : K, ((m j.1:ℝ)-(p:ℝ)*w j.1)^2/(r j)^2
  let good := s.filter (fun m => e m ≤ 1)
  let bad := s.filter (fun m => ¬ e m ≤ 1)
  have hc (m : J → ℕ) : 0 ≤ c m := monomialWeight_nonneg w hw m
  have hmass : ∑ m ∈ s,c m = 1 := by
    dsimp [s,c]
    rw [sum_monomialWeight,hW,one_pow]
  have hmoment : ∑ m ∈ s,c m*e m = v := by
    dsimp [e,s,c,v]
    simp_rw [mul_sum,← mul_div_assoc]
    rw [sum_comm]
    simp_rw [← sum_div,coordinate_second_moment w hW p]
    rfl
  have hbad : ∑ m ∈ bad,c m ≤ v := by
    calc
      _ ≤ ∑ m ∈ bad,c m*e m := by
        apply sum_le_sum
        intro m hm
        exact le_mul_of_one_le_right (hc m) (le_of_lt (lt_of_not_ge (mem_filter.mp hm).2))
      _ ≤ ∑ m ∈ s,c m*e m := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro m _ _
        exact mul_nonneg (hc m) (sum_nonneg fun _ _ => by positivity)
      _ = v := hmoment
  have hgood : max 0 (1-v) ≤ ∑ m ∈ good,c m := by
    apply max_le (sum_nonneg fun m _ => hc m)
    have hs := sum_filter_add_sum_filter_not s (fun m => e m ≤ 1) c
    change (∑ m ∈ good,c m)+(∑ m ∈ bad,c m)=_ at hs
    rw [hmass] at hs
    linarith
  let coord : (J → ℕ) → K → ℤ := fun m j => (m j.1:ℤ)
  let box : Finset (K → ℤ) := Fintype.piFinset
    (fun j : K => Icc ⌈(p:ℝ)*w j.1-r j⌉ ⌊(p:ℝ)*w j.1+r j⌋)
  have hinj : Set.InjOn coord ↑good := by
    intro m hm l hl heq
    have hm' := (mem_piAntidiag.mp (mem_filter.mp (show m ∈ good from hm)).1).1
    have hl' := (mem_piAntidiag.mp (mem_filter.mp (show l ∈ good from hl)).1).1
    have hagree (j : J) (hj : j ≠ j0) : m j = l j := by
      have h := congrFun heq (⟨j,hj⟩ : K)
      change (m j : ℤ) = (l j : ℤ) at h
      exact_mod_cast h
    have hsum : ∑ j ∈ univ.erase j0,m j = ∑ j ∈ univ.erase j0,l j :=
      sum_congr rfl fun j hj => hagree j (mem_erase.mp hj).1
    have hm0 := sum_erase_add (s := (univ : Finset J)) m (mem_univ j0)
    have hl0 := sum_erase_add (s := (univ : Finset J)) l (mem_univ j0)
    rw [hm'] at hm0
    rw [hl'] at hl0
    rw [hsum] at hm0
    have h0 : m j0 = l j0 := by omega
    funext j
    by_cases hj : j=j0
    · simpa [hj] using h0
    · exact hagree j hj
  have hbox : good.image coord ⊆ box := by
    intro y hy
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hy
    apply Fintype.mem_piFinset.mpr
    intro j
    have hh := (mem_filter.mp hm).2
    have hcoord : ((m j.1:ℝ)-(p:ℝ)*w j.1)^2/(r j)^2 ≤ 1 := by
      exact (single_le_sum (f := fun i : K => ((m i.1:ℝ)-(p:ℝ)*w i.1)^2/(r i)^2)
        (fun i _ => by positivity) (mem_univ j)).trans hh
    have hsq : ((m j.1:ℝ)-(p:ℝ)*w j.1)^2 ≤ (r j)^2 :=
      (div_le_one (sq_pos_of_pos (hr j))).mp hcoord
    have habs : |(m j.1:ℝ)-(p:ℝ)*w j.1| ≤ r j := by
      apply (sq_le_sq₀ (abs_nonneg _) (hr j).le).mp
      rw [sq_abs]
      exact hsq
    have hh := abs_le.mp habs
    apply mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      dsimp [coord]
      push_cast
      linarith only [hh.1]
    · apply Int.le_floor.mpr
      dsimp [coord]
      push_cast
      linarith only [hh.2]
  have hcard : (good.card:ℝ) ≤ ∏ j : K, width (r j) := by
    have h := card_le_card hbox
    rw [card_image_of_injOn hinj] at h
    calc
      _ ≤ (box.card:ℝ) := by exact_mod_cast h
      _ = ∏ j : K, ((Icc ⌈(p:ℝ)*w j.1-r j⌉ ⌊(p:ℝ)*w j.1+r j⌋ : Finset ℤ).card:ℝ) := by
        dsimp [box]
        rw [Fintype.card_piFinset,Nat.cast_prod]
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by positivity)
        (fun j _ => int_interval_card ((p:ℝ)*w j.1) (r j) (hr j).le)
  have hsquare := sum_mul_sq_le_sq_mul_sq good (fun _ => (1:ℝ)) c
  have hsquare' : (∑ m ∈ good,c m)^2 ≤ (good.card:ℝ)*∑ m ∈ good,c m^2 := by
    simpa [mul_comm] using hsquare
  have hdiag : ∑ m ∈ good,c m^2 ≤ diagonal w p := by
    unfold diagonal
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hsmall := (sq_le_sq₀ (le_max_left 0 (1-v))
    (sum_nonneg fun m _ => hc m)).mpr hgood
  have hwid : 0≤∏ j : K,width (r j) := prod_nonneg fun j _ => add_nonneg zero_le_one (mul_nonneg (by norm_num) (hr j).le)
  exact hsmall.trans (hsquare'.trans (mul_le_mul hcard hdiag
    (sum_nonneg fun _ _ => sq_nonneg _) hwid))

/-- Every positive-resolution Fejer moment contains the dimension-sensitive diagonal floor. -/
theorem fejer_occupation_floor {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0≤w j) (hW : ∑ j,w j=1) (j0 : J) (p : ℕ)
    (r : {j : J // j ≠ j0} → ℝ) (hr : ∀ j, 0 < r j) (η : ℝ) (hη : 0 < η) :
    let kernel := fun z : ℝ × ℝ => K z.1 z.2
    let v := ∑ j : {j : J // j ≠ j0}, (p:ℝ)*(w j.1-(w j.1)^2)/(r j)^2
    (max 0 (1-v))^2 ≤ (∏ j : {j : J // j ≠ j0},(1+2*r j))*(∫ t : ℝ,kernel (η,t)*‖complexScore g w t‖^(2*p)) := by
  intro kernel v
  have hfloor := occupation_diagonal_lower w hw hW j0 p r hr
  have hdiag : diagonal w p ≤ ∫ t : ℝ,K η t*‖complexScore g w t‖^(2*p) := by
    rw [(fejer_collision_comparison g w p hη).1]
    unfold diagonal
    apply sum_le_sum
    intro m hm
    calc
      monomialWeight w m^2 =
          monomialWeight w m*monomialWeight w m*phi η (monomialFrequency g m-monomialFrequency g m) := by
        simp [phi,pow_two]
      _ ≤ ∑ l ∈ piAntidiag univ p,
          monomialWeight w m*monomialWeight w l*phi η (monomialFrequency g m-monomialFrequency g l) :=
        single_le_sum (f := fun l => monomialWeight w m*monomialWeight w l*
          phi η (monomialFrequency g m-monomialFrequency g l))
          (fun l _ => mul_nonneg (mul_nonneg (monomialWeight_nonneg w hw m)
          (monomialWeight_nonneg w hw l)) (by unfold phi; exact le_max_left _ _)) hm
  have hprod : 0 ≤ ∏ j : {j : J // j ≠ j0},(1+2*r j) :=
    prod_nonneg fun j _ => add_nonneg zero_le_one (mul_nonneg (by norm_num) (hr j).le)
  exact hfloor.trans (mul_le_mul_of_nonneg_left hdiag hprod)

#print axioms occupation_diagonal_lower
#print axioms fejer_occupation_floor

end D5.S3.Fourier.Concentration.OccupationDiagonalFloor
