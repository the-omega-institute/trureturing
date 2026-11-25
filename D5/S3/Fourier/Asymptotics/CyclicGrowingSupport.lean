/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingSupport
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cyclic optimizer support in growing windows away from rear activation thresholds. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits

import D5.S3.Fourier.Asymptotics.CyclicEventualSupport

/-! Exact cyclic support from critical-scale boundary estimates and the finite complement certificate. -/


open Finset Matrix Filter
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicEventualSupport
open D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
open D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open Asymptotics

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingSupport

noncomputable section

set_option autoImplicit false

private theorem sample_int_cast {q : ℕ} [NeZero q] (j : ℤ) :
    sample (j : ZMod q) = Real.cos ((j : ℝ) * mesh q) := by
  let i : ZMod q := j
  have hzero : ((j - i.valMinAbs : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_sub, ZMod.coe_valMinAbs]
    exact sub_self i
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hr : (j : ℝ) - (i.valMinAbs : ℝ) = (q : ℝ)*k := by exact_mod_cast hk
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have he : (j : ℝ)*mesh q = (i.valMinAbs : ℝ)*mesh q + (k : ℝ)*(2*Real.pi) := by
    have hj : (j : ℝ) = (i.valMinAbs : ℝ) + (q : ℝ)*k := by linarith only [hr]
    rw [hj]
    unfold mesh
    field_simp [hq]
    <;> ring
  rw [sample, centeredAngle_eq_mesh, he, Real.cos_add_int_mul_two_pi]

private theorem rear_sample {q : ℕ} [NeZero q] (j : ℤ) :
    sample (((q / 2 : ℕ) : ℤ) + j : ZMod q) =
      -Real.cos (((j : ℝ) - (q % 2 : ℕ)/2) * mesh q) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hk : (2 : ℝ) * (q/2 : ℕ) + (q%2 : ℕ) = q := by
    exact_mod_cast (show 2*(q/2) + q%2 = q by omega)
  rw [← Int.cast_add, sample_int_cast, Int.cast_add, Int.cast_natCast]
  have he : (((q / 2 : ℕ) : ℝ) + j)*mesh q =
      Real.pi + ((j : ℝ) - (q%2 : ℕ)/2)*mesh q := by
    have hhalf : ((q/2 : ℕ) : ℝ) = (q : ℝ)/2 - ((q%2 : ℕ) : ℝ)/2 := by linarith only [hk]
    rw [hhalf]
    unfold mesh
    field_simp [hq]
    <;> ring
  rw [he, Real.cos_add]
  simp

private theorem cast_eq_of_small_diff {q : ℕ} {x y : ℤ}
    (hsmall : |x-y| < (q : ℤ)) (hcast : (x : ZMod q) = (y : ZMod q)) : x = y := by
  have hd : (q : ℤ) ∣ x-y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, hcast, sub_self]
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hsmall)


def frontSites (q n : ℕ) : Finset (ZMod q) :=
  (Icc (-(n : ℤ)) (n : ℤ)).image (fun j : ℤ => (j : ZMod q))

def rearOffsets (q l : ℕ) : Finset ℤ :=
  Icc (-(l : ℤ)) ((l : ℤ) + (q % 2 : ℕ))

def rearSites (q l : ℕ) : Finset (ZMod q) :=
  (rearOffsets q l).image (fun j : ℤ => ((((q/2 : ℕ) : ℤ) + j : ℤ) : ZMod q))

private theorem front_mem {q n : ℕ} [NeZero q] (hq : 2*n < q) (i : ZMod q) :
    i ∈ frontSites q n ↔ i.valMinAbs.natAbs ≤ n := by
  constructor
  · intro hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
    have ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hj
    have hrep : i.valMinAbs = j := (ZMod.valMinAbs_spec i j).mpr
      ⟨hji.symm, by constructor <;> omega⟩
    rw [hrep]
    omega
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨i.valMinAbs, Finset.mem_Icc.mpr ⟨?_,?_⟩, ZMod.coe_valMinAbs i⟩
    all_goals omega

private theorem rear_mem {q l : ℕ} [NeZero q] (hq : l+1 < q/2) (i : ZMod q) :
    i ∈ rearSites q l ↔ q/2-l ≤ i.valMinAbs.natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  constructor
  · intro hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
    have ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hj
    have hnonneg : 0 ≤ ((q/2 : ℕ) : ℤ) + j := by omega
    have hlt : ((q/2 : ℕ) : ℤ) + j < (q : ℤ) := by omega
    have hval : (i.val : ℤ) = (q/2 : ℕ) + j := by
      rw [← hji, ZMod.val_intCast, Int.emod_eq_of_lt hnonneg hlt]
    omega
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨(i.val : ℤ) - (q/2 : ℕ), Finset.mem_Icc.mpr ⟨?_,?_⟩, ?_⟩
    · omega
    · omega
    · rw [show (((q/2 : ℕ) : ℤ) + ((i.val : ℤ) - (q/2 : ℕ))) = i.val by ring,
        Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem two_sites_disjoint {q n l : ℕ} [NeZero q] (h : n+l+2 ≤ q/2) :
    Disjoint (frontSites q n) (rearSites q l) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  have hf := (front_mem (by omega : 2*n < q) i).mp hi
  have hb := (rear_mem (by omega : l+1 < q/2) i).mp hj
  omega


private theorem cos_index_antitone {q a b : ℕ} [NeZero q] (hab : a ≤ b)
    (hb : b ≤ q/2) : Real.cos ((b : ℝ)*mesh q) ≤ Real.cos ((a : ℝ)*mesh q) := by
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · exact mul_nonneg (Nat.cast_nonneg _) mesh_pos.le
  · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hb) mesh_pos.le).trans half_mesh_le_pi
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) mesh_pos.le

private theorem rear_cosine_identity {q l : ℕ} [NeZero q] (hl : l ≤ q/2) :
    Real.cos ((↑(q/2-l) : ℝ)*mesh q) =
      -Real.cos (((l : ℝ) + ((q%2 : ℕ) : ℝ)/2)*mesh q) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hhalf : (2 : ℝ)*((q/2 : ℕ) : ℝ)+((q%2 : ℕ) : ℝ)=q := by
    exact_mod_cast (show 2*(q/2)+q%2=q by omega)
  have he : ((↑(q/2-l) : ℝ)*mesh q) =
      Real.pi-((l : ℝ)+((q%2 : ℕ) : ℝ)/2)*mesh q := by
    rw [Nat.cast_sub hl]
    have hk : ((q/2 : ℕ) : ℝ) = (q : ℝ)/2-((q%2 : ℕ) : ℝ)/2 := by linarith
    rw [hk]
    unfold mesh
    field_simp [hq]
    <;> ring
  rw [he, Real.cos_pi_sub]

private theorem front_sample_lower {q n l : ℕ} [NeZero q] (h : n+l+2 ≤ q/2)
    {i : ZMod q} (hi : i ∈ frontSites q n) :
    Real.cos ((n : ℝ)*mesh q) ≤ sample i := by
  rw [sample_eq_abs]
  exact cos_index_antitone ((front_mem (by omega : 2*n<q) i).mp hi) (by omega)

private theorem rear_sample_upper {q n l : ℕ} [NeZero q] (h : n+l+2 ≤ q/2)
    {i : ZMod q} (hi : i ∈ rearSites q l) :
    sample i ≤ -Real.cos (((l : ℝ)+((q%2 : ℕ) : ℝ)/2)*mesh q) := by
  rw [sample_eq_abs, ← rear_cosine_identity (by omega : l ≤ q/2)]
  exact cos_index_antitone ((rear_mem (by omega : l+1<q/2) i).mp hi)
    (ZMod.natAbs_valMinAbs_le i)

private theorem complement_sample_between {q n l : ℕ} [NeZero q] (h : n+l+2 ≤ q/2)
    {i : ZMod q} (hf : i ∉ frontSites q n) (hr : i ∉ rearSites q l) :
    -Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q) ≤ sample i ∧
      sample i ≤ Real.cos (((n : ℝ)+1)*mesh q) := by
  have hf' := mt (front_mem (by omega : 2*n<q) i).mpr hf
  have hr' := mt (rear_mem (by omega : l+1<q/2) i).mpr hr
  rw [sample_eq_abs]
  constructor
  · rw [← show Real.cos ((↑(q/2-(l+1)) : ℝ)*mesh q) =
        -Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q) by
      simpa only [Nat.cast_add,Nat.cast_one] using rear_cosine_identity (by omega : l+1 ≤ q/2)]
    exact cos_index_antitone (by omega : i.valMinAbs.natAbs ≤ q/2-(l+1)) (by omega)
  · rw [← Nat.cast_one, ← Nat.cast_add]
    exact cos_index_antitone (by omega : n+1 ≤ i.valMinAbs.natAbs)
      (ZMod.natAbs_valMinAbs_le i)



def rearRealOffsets (q l : ℕ) : Finset ℝ :=
  (rearOffsets q l).image fun j : ℤ => (j : ℝ) - ((q%2 : ℕ) : ℝ)/2

private def siteF {q : ℕ} (i : ZMod q) : ℝ := (1+sample i)/2
private def siteW {q : ℕ} (i : ZMod q) : ℝ := 1-siteF i
private def siteX {q : ℕ} (n : ℕ) (i : ZMod q) : ℝ :=
  (1-sample i^2)/((n : ℝ)*mesh q)^2

private theorem front_features_match {q n : ℕ} [NeZero q] (hn : 0<n) (j : ℤ) :
    let u := (n : ℝ)*mesh q
    let x := (j : ℝ)/n
    siteF (j : ZMod q) = frontFeatures u x 0 ∧
      siteX n (j : ZMod q) = frontFeatures u x 1 := by
  intro u x
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hu : u ≠ 0 := mul_ne_zero hn0 mesh_pos.ne'
  have he : x*u = (j : ℝ)*mesh q := by
    dsimp [x,u]
    field_simp [hn0]
  constructor
  · change (1+sample (j : ZMod q))/2 = (1+Real.cos (x*u))/2
    rw [he,sample_int_cast]
  · change (1-sample (j : ZMod q)^2)/u^2 =
      if u=0 then x^2 else (1-Real.cos (x*u)^2)/u^2
    rw [if_neg hu, he,sample_int_cast]

private theorem rear_moment_eq {h : ℝ} (hh : h ≠ 0) (r : ℝ) :
    rearMoment h r = (1-Real.cos (r*h)^2)/h^2 := by
  rw [← Real.sin_sq]
  by_cases hr : r=0
  · simp [hr,rearMoment]
  · rw [rearMoment, Real.sinc_of_ne_zero (mul_ne_zero hr hh)]
    field_simp [hr,hh]
    <;> ring

set_option maxHeartbeats 400000 in
private theorem rear_features_match {q n : ℕ} [NeZero q] (hn : 0<n) (j : ℤ) :
    let i : ZMod q := (((q/2 : ℕ) : ℤ)+j : ℤ)
    let r := (j : ℝ)-((q%2 : ℕ) : ℝ)/2
    siteF i = 1-rearWeight (mesh q) r ∧ siteW i = rearWeight (mesh q) r ∧
      siteX n i = rearMoment (mesh q) r/(n : ℝ)^2 := by
  intro i r
  have hi : sample i = -Real.cos (r*mesh q) := by
    simpa only [i,r,Int.cast_add] using rear_sample (q := q) j
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : mesh q ≠ 0 := mesh_pos.ne'
  refine ⟨?_,?_,?_⟩
  · unfold siteF rearWeight
    rw [hi]
    ring
  · unfold siteW siteF rearWeight
    rw [hi]
    ring
  · unfold siteX
    rw [hi,neg_sq,rear_moment_eq hh]
    field_simp [hh,hn0]
    <;> ring


private theorem sum_two_windows {q n l : ℕ} [NeZero q] (h : n+l+2 ≤ q/2)
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ i ∈ frontSites q n ∪ rearSites q l, f i) =
      (∑ j ∈ latticeInterval n, f (j : ZMod q)) +
      (∑ j ∈ rearOffsets q l, f ((((q/2 : ℕ) : ℤ)+j : ℤ) : ZMod q)) := by
  classical
  rw [sum_union (two_sites_disjoint h)]
  congr 1
  · unfold frontSites latticeInterval
    apply sum_image
    intro x hx y hy he
    apply cast_eq_of_small_diff _ he
    obtain ⟨hx₁,hx₂⟩ := mem_Icc.mp hx
    obtain ⟨hy₁,hy₂⟩ := mem_Icc.mp hy
    rw [abs_lt]
    constructor <;> omega
  · unfold rearSites
    apply sum_image
    intro x hx y hy he
    have he' : ((q/2 : ℕ) : ℤ)+x = ((q/2 : ℕ) : ℤ)+y := by
      apply cast_eq_of_small_diff _ he
      have ⟨hx₁,hx₂⟩ := mem_Icc.mp hx
      have ⟨hy₁,hy₂⟩ := mem_Icc.mp hy
      rw [abs_lt]
      constructor <;> omega
    omega

private def signedSiteValue {q : ℕ} (n : ℕ) (a : Fin 3 → ℝ) (i : ZMod q) : ℝ :=
  coefficientRow n (siteF i) (siteX n i) (siteW i) ⬝ᵥ a

def windowLaw {q : ℕ} (n l : ℕ) (a : Fin 3 → ℝ) (i : ZMod q) : ℝ :=
  if i ∈ frontSites q n ∪ rearSites q l then signedSiteValue n a i else 0

private theorem cyclic_readout {q n l : ℕ} [NeZero q] (hn : 0<n)
    (h : n+l+2 ≤ q/2) (a : Fin 3 → ℝ) :
    (∑ i : ZMod q, windowLaw n l a i • momentRow n (siteF i) (siteX n i) (siteW i)) =
      coupledMoments (rearRealOffsets q l) n (mesh q) a := by
  classical
  rw [← sum_subset (subset_univ (frontSites q n ∪ rearSites q l)) (by
    intro i _ hi
    simp [windowLaw,hi])]
  have he :
      (∑ i ∈ frontSites q n ∪ rearSites q l,
        windowLaw n l a i • momentRow n (siteF i) (siteX n i) (siteW i)) =
      ∑ i ∈ frontSites q n ∪ rearSites q l,
        signedSiteValue n a i • momentRow n (siteF i) (siteX n i) (siteW i) := by
    apply sum_congr rfl
    intro i hi
    simp only [windowLaw,hi,ite_true]
  rw [he, sum_two_windows h]
  unfold coupledMoments
  dsimp only
  congr 1
  · apply sum_congr rfl
    intro j _
    obtain ⟨hf,hx⟩ := front_features_match (q := q) hn j
    unfold signedSiteValue siteW
    rw [hf,hx]
  · unfold rearRealOffsets
    rw [sum_image]
    · apply sum_congr rfl
      intro j _
      obtain ⟨hf,hw,hx⟩ := rear_features_match (q := q) hn j
      unfold signedSiteValue
      rw [hf,hw,hx]
    · intro j hj k hk hEq
      have hReal : (j : ℝ) = (k : ℝ) := by linarith
      exact_mod_cast hReal



private theorem moments_from_scaled_rows {q n : ℕ} [NeZero q] (hn : 0<n)
    (m : ℝ) (v : ZMod q → ℝ)
    (hrows : (∑ i : ZMod q, v i • momentRow n (siteF i) (siteX n i) (siteW i)) =
      ![1-m*(mesh q)^2, m/(n : ℝ)^2, 3*(n : ℝ)^3*m*(mesh q)^2/4]) :
    (∑ i, v i) = 1 ∧ cosineMoment 1 v = 1-2*m*(mesh q)^2 ∧
      cosineMoment 2 v = 1-2*m*(mesh q)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : mesh q ≠ 0 := mesh_pos.ne'
  have hf := congrFun hrows (0 : Fin 3)
  have hx := congrFun hrows (1 : Fin 3)
  have hw2 := congrFun hrows (2 : Fin 3)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, momentRow,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hf hx hw2
  change (∑ i, v i*siteF i) = 1-m*(mesh q)^2 at hf
  change (∑ i, v i*siteX n i) = m/(n : ℝ)^2 at hx
  change (∑ i, v i*((n : ℝ)^3*siteW i^2)) = 3*(n : ℝ)^3*m*(mesh q)^2/4 at hw2
  have hW2 : (∑ i, v i*siteW i^2) = 3*m*(mesh q)^2/4 := by
    apply (mul_left_cancel₀ (pow_ne_zero 3 hn0))
    calc
      (n : ℝ)^3*(∑ i, v i*siteW i^2) = ∑ i, v i*((n : ℝ)^3*siteW i^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hw2]; ring
  have hX : (∑ i, v i*(1-sample i^2)) = m*(mesh q)^2 := by
    have hx' : (∑ i, v i*(1-sample i^2))/((n : ℝ)*mesh q)^2 = m/(n : ℝ)^2 := by
      simpa only [siteX, mul_div_assoc, sum_div] using hx
    have h := (div_eq_iff (pow_ne_zero 2 (mul_ne_zero hn0 hh))).mp hx'
    rw [h]
    field_simp [hn0]
    <;> ring
  have hidentity (i : ZMod q) : siteW i = siteW i^2+(1-sample i^2)/4 := by
    unfold siteW siteF
    ring
  have hw : (∑ i, v i*siteW i) = m*(mesh q)^2 := by
    calc
      _ = (∑ i, v i*siteW i^2)+(∑ i, v i*(1-sample i^2))/4 := by
        rw [sum_div, ← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        nth_rw 1 [hidentity i]
        ring
      _ = _ := by rw [hW2,hX]; ring
  have hmass : (∑ i,v i)=1 := by
    calc
      _ = (∑ i,v i*siteF i)+(∑ i,v i*siteW i) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        unfold siteW
        ring
      _ = _ := by rw [hf,hw]; ring
  have hd : (∑ i,v i*(1-sample i)) = 2*m*(mesh q)^2 := by
    calc
      _ = 2*(∑ i,v i*siteW i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        unfold siteW siteF
        ring
      _ = _ := by rw [hw]; ring
  obtain ⟨h1,h2⟩ := sum_sample_deficits hmass
  exact ⟨hmass,by linarith only [hd,h1],by linarith only [hX,h2]⟩



private def fitPolynomial (n : ℕ) (h : ℝ) (a : Fin 3 → ℝ) (c : ℝ) : ℝ :=
  a 0/n + (a 2/(2*(n : ℝ)^3)-a 0/(2*n))*(1-c) +
    (a 1/(n : ℝ)^3)*((1-c^2)/h^2)

private theorem signed_site_eq_poly {q n : ℕ} [NeZero q] (hn : 0<n)
    (a : Fin 3 → ℝ) (i : ZMod q) :
    signedSiteValue n a i = fitPolynomial n (mesh q) a (sample i) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : mesh q ≠ 0 := mesh_pos.ne'
  simp only [signedSiteValue, coefficientRow, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change siteF i / n*a 0+siteX n i/n*a 1+siteW i/(n : ℝ)^3*a 2 = _
  simp only [siteF,siteX,siteW,fitPolynomial]
  field_simp [hn0,hh]
  <;> ring

private theorem window_signs {q n l : ℕ} [NeZero q] (hn : 0<n)
    (h : n+l+2 ≤ q/2) (a : Fin 3 → ℝ) (hc : a 1 ≤ 0)
    (hposF : 0 < fitPolynomial n (mesh q) a (Real.cos ((n : ℝ)*mesh q)))
    (hnegF : fitPolynomial n (mesh q) a (Real.cos (((n : ℝ)+1)*mesh q)) ≤ 0)
    (hposR : 0 < fitPolynomial n (mesh q) a
      (-Real.cos (((l : ℝ)+((q%2 : ℕ) : ℝ)/2)*mesh q)))
    (hnegR : fitPolynomial n (mesh q) a
      (-Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q)) ≤ 0) :
    (∀ i ∈ frontSites q n ∪ rearSites q l, 0 < signedSiteValue n a i) ∧
    ∀ i ∉ frontSites q n ∪ rearSites q l, signedSiteValue n a i ≤ 0 := by
  let s := (mesh q)^2
  let A := a 0/n
  let B := a 2/(2*(n : ℝ)^3)-a 0/(2*n)
  let G := a 1/(n : ℝ)^3
  have hs : 0 < s := sq_pos_of_pos mesh_pos
  have hg : G ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (by positivity)
  have convex_bound {lo hi c : ℝ} (hlo : lo ≤ c) (hhi : c ≤ hi)
      (hl : fitPolynomial n (mesh q) a lo ≤ 0)
      (hh : fitPolynomial n (mesh q) a hi ≤ 0) :
      fitPolynomial n (mesh q) a c ≤ 0 :=
    dualValue_nonpos_of_between (a := A) (b := B) hs hg hlo hhi hl hh
  have hfront_order : Real.cos (((n : ℝ)+1)*mesh q) ≤ Real.cos ((n : ℝ)*mesh q) := by
    rw [← Nat.cast_one,← Nat.cast_add]
    exact cos_index_antitone (by omega : n≤n+1) (by omega)
  have hrear_order : -Real.cos (((l : ℝ)+((q%2 : ℕ) : ℝ)/2)*mesh q) ≤
      -Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q) := by
    rw [← rear_cosine_identity (by omega : l ≤ q/2)]
    rw [← show Real.cos ((↑(q/2-(l+1)) : ℝ)*mesh q) =
        -Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q) by
      simpa only [Nat.cast_add,Nat.cast_one] using rear_cosine_identity (by omega : l+1 ≤ q/2)]
    exact cos_index_antitone (by omega : q/2-(l+1)≤q/2-l) (by omega)
  constructor
  · intro i hi
    rw [signed_site_eq_poly hn]
    rcases mem_union.mp hi with hf | hr
    · by_contra! hz
      exact (not_le_of_gt hposF) (convex_bound hfront_order
        (front_sample_lower h hf) hnegF hz)
    · by_contra! hz
      exact (not_le_of_gt hposR) (convex_bound (rear_sample_upper h hr)
        hrear_order hz hnegR)
  · intro i hi
    rw [signed_site_eq_poly hn]
    obtain ⟨hf,hr⟩ := not_or.mp (mt mem_union.mpr hi)
    obtain ⟨hlo,hhi⟩ := complement_sample_between h hf hr
    exact convex_bound hlo hhi hnegR hnegF

private theorem window_optimizer {q n l : ℕ} [NeZero q] (hn : 0<n)
    (h : n+l+2 ≤ q/2) (m : ℝ) (a : Fin 3 → ℝ) (hc : a 1 ≤ 0)
    (hb : a 2 ≤ a 0*(n : ℝ)^2)
    (hrows : coupledMoments (rearRealOffsets q l) n (mesh q) a =
      ![1-m*(mesh q)^2, m/(n : ℝ)^2, 3*(n : ℝ)^3*m*(mesh q)^2/4])
    (hposF : 0 < fitPolynomial n (mesh q) a (Real.cos ((n : ℝ)*mesh q)))
    (hnegF : fitPolynomial n (mesh q) a (Real.cos (((n : ℝ)+1)*mesh q)) ≤ 0)
    (hposR : 0 < fitPolynomial n (mesh q) a
      (-Real.cos (((l : ℝ)+((q%2 : ℕ) : ℝ)/2)*mesh q)))
    (hnegR : fitPolynomial n (mesh q) a
      (-Real.cos (((l : ℝ)+1+((q%2 : ℕ) : ℝ)/2)*mesh q)) ≤ 0) :
    let v : ZMod q → ℝ := windowLaw n l a
    let threshold := 1-2*m*(mesh q)^2
    cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible q threshold ∧
      (∀ w ∈ feasible q threshold, w ≠ v → energy v < energy w) ∧
      (∀ w ∈ feasible q threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
      ∀ w ∈ feasible q threshold, IsMinOn energy (feasible q threshold) w →
        ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites q n ∪ rearSites q l := by
  intro v threshold
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  let s := (mesh q)^2
  let A := a 0/n
  let B := a 2/(2*(n : ℝ)^3)-a 0/(2*n)
  let G := a 1/(n : ℝ)^3
  have hB : B ≤ 0 := by
    dsimp [B]
    rw [sub_nonpos,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hb (show 0≤2*(n : ℝ) by positivity)]
  have hG : G ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (by positivity)
  have hs : 0<s := sq_pos_of_pos mesh_pos
  obtain ⟨hp,ho⟩ := window_signs hn h a hc hposF hnegF hposR hnegR
  have hrow : (∑ i : ZMod q, v i • momentRow n (siteF i) (siteX n i) (siteW i)) =
      ![1-m*(mesh q)^2, m/(n : ℝ)^2, 3*(n : ℝ)^3*m*(mesh q)^2/4] := by
    rw [show v=windowLaw n l a from rfl,cyclic_readout hn h,hrows]
  obtain ⟨hm,h1,h2⟩ := moments_from_scaled_rows hn m v hrow
  have hv : v = fun i : ZMod q =>
      if i ∈ frontSites q n ∪ rearSites q l then fitPolynomial n (mesh q) a (sample i) else 0 := by
    funext i
    simp only [v,windowLaw,signed_site_eq_poly hn]
  have hpos : ∀ i ∈ frontSites q n ∪ rearSites q l,
      0 < fitPolynomial n (mesh q) a (sample i) := by
    intro i hi
    rw [← signed_site_eq_poly hn]
    exact hp i hi
  have hneg : ∀ i ∉ frontSites q n ∪ rearSites q l,
      fitPolynomial n (mesh q) a (sample i) ≤ 0 := by
    intro i hi
    rw [← signed_site_eq_poly hn]
    exact ho i hi
  rw [hv] at hm h1 h2 ⊢
  exact ⟨h1,h2,exact_support_of_dual_nonpos (a := A) hs hB hG hpos hneg hm h1 h2⟩



private theorem boundary_poly_eq {n : ℕ} (hn : 0<n) {h : ℝ} (hh : h≠0)
    (S : Finset ℝ) (offset : ℝ) :
    boundaryValue S n h offset =
      fitPolynomial n h (coefficientFit S n h) (Real.cos (((n : ℝ)+offset)*h)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hu : (n : ℝ)*h ≠ 0 := mul_ne_zero hn0 hh
  let c := Real.cos (((n : ℝ)+offset)*h)
  have he : (((n : ℝ)+offset)/n)*((n : ℝ)*h) = ((n : ℝ)+offset)*h := by
    field_simp [hn0]
  unfold boundaryValue
  simp only [frontFeatures, Matrix.cons_val_zero, Matrix.cons_val_one, if_neg hu, he]
  change coefficientRow n ((1+c)/2) ((1-c^2)/((n : ℝ)*h)^2) (1-(1+c)/2)
    ⬝ᵥ coefficientFit S n h = fitPolynomial n h (coefficientFit S n h) c
  simp only [coefficientRow,dotProduct,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change ((1+c)/2)/n*coefficientFit S n h 0 +
    ((1-c^2)/((n : ℝ)*h)^2)/n*coefficientFit S n h 1 +
    ((1-(1+c)/2)/(n : ℝ)^3)*coefficientFit S n h 2 = _
  unfold fitPolynomial
  field_simp [hn0,hh]
  <;> ring

private theorem rear_poly_eq {n : ℕ} (hn : 0<n) {h : ℝ} (hh : h≠0)
    (S : Finset ℝ) (r : ℝ) :
    rearValue S n h r =
      fitPolynomial n h (coefficientFit S n h) (-Real.cos (r*h)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let c := Real.cos (r*h)
  unfold rearValue
  rw [rear_moment_eq hh]
  simp only [rearWeight,coefficientRow,dotProduct,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change (1-(1+c)/2)/n*coefficientFit S n h 0+
    ((1-c^2)/h^2/(n : ℝ)^2)/n*coefficientFit S n h 1+
    ((1+c)/2)/(n : ℝ)^3*coefficientFit S n h 2 = _
  change _ = fitPolynomial n h (coefficientFit S n h) (-c)
  unfold fitPolynomial
  field_simp [hn0,hh]
  <;> ring

private theorem eventually_wide_cycle (q : ℕ → ℕ) (hq : ∀ n, q n≠0)
    (hU : Tendsto (fun n : ℕ => (n : ℝ)*mesh (q n)) atTop (𝓝 0))
    (l : ℕ) : ∀ᶠ n in atTop, n+l+2 ≤ q n/2 := by
  have hp := hU.eventually (gt_mem_nhds (show (0:ℝ)<Real.pi/2 by positivity))
  filter_upwards [hp,eventually_ge_atTop (l+2)] with n hn hn'
  have hqR : (0:ℝ)<q n := by exact_mod_cast Nat.pos_of_ne_zero (hq n)
  unfold mesh at hn
  have he : (n : ℝ) * (2*Real.pi/(q n : ℝ)) = (2*(n : ℝ)*Real.pi)/(q n : ℝ) := by ring
  rw [he, div_lt_iff₀ hqR] at hn
  have hlt : (4:ℝ)*n < q n := by
    by_contra! hbad
    have he := mul_le_mul_of_nonneg_right hbad Real.pi_pos.le
    nlinarith only [hn,he]
  have hlt' : 4*n < q n := by exact_mod_cast hlt
  omega

private theorem rear_offsets_nonempty (e l : ℕ) : (rearRealOffsets e l).Nonempty := by
  refine ⟨-((e%2 : ℕ) : ℝ)/2, Finset.mem_image.mpr ⟨0,?_,?_⟩⟩
  · exact mem_Icc.mpr ⟨by omega,by omega⟩
  · norm_num <;> ring


private theorem eventual_strict_window_support
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (hpar : ∀ᶠ n in atTop, q n % 2 = e) {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (mesh (q n))^2) atTop (𝓝 K))
    (hposR : 3*((l : ℝ)+(e : ℝ)/2)^2/4 < limitCoefficients (rearRealOffsets e l) K 2)
    (hnegR : limitCoefficients (rearRealOffsets e l) K 2 < 3*((l : ℝ)+1+(e : ℝ)/2)^2/4) :
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let v : ZMod (q n) → ℝ := windowLaw n l (coefficientFit (rearRealOffsets e l) n (mesh (q n)))
      let threshold := 1-2*budget n*(mesh (q n))^2
      cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) l := by
  obtain ⟨j,hj⟩ := hpar.exists
  have he : e < 2 := by rw [← hj]; omega
  let h := fun n => mesh (q n)
  let S := rearRealOffsets e l
  have hS : S.Nonempty := rear_offsets_nonempty e l
  have hB := hK.isBigO_one ℝ
  obtain ⟨_,hU,hscale⟩ := critical_bound_mesh_limits hB
  have hwide := eventually_wide_cycle q hq hU l
  let a := fun n => coefficientFit S n (h n)
  have ha := coefficient_tendsto hK S hS
  have hA : Tendsto (fun n => a n 0) atTop (𝓝 (3/4)) := tendsto_pi_nhds.1 ha 0
  have hC : Tendsto (fun n => a n 1) atTop (𝓝 (-3/4)) := tendsto_pi_nhds.1 ha 1
  have hBr : Tendsto (fun n => a n 2) atTop (𝓝 (limitCoefficients S K 2)) :=
    tendsto_pi_nhds.1 ha 2
  have hnAt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hnAt
  have hBrDiv : Tendsto (fun n : ℕ => a n 2/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,zero_pow (by decide : 2≠0),mul_zero] using hBr.mul (hi.pow 2)
  have hCneg := hC.eventually (gt_mem_nhds (by norm_num : (-3/4 : ℝ)<0))
  have hApos := hA.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<3/4))
  have hBsmall := hBrDiv.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hF0 := scaled_boundary_value hB S hS 0
  have hF1 := scaled_boundary_value hB S hS 1
  have hF0pos : ∀ᶠ n : ℕ in atTop, 0<(n : ℝ)^2*boundaryValue S n (h n) 0 :=
    hF0.eventually (lt_mem_nhds (by norm_num))
  have hF1neg : ∀ᶠ n : ℕ in atTop, (n : ℝ)^2*boundaryValue S n (h n) 1<0 :=
    hF1.eventually (gt_mem_nhds (by norm_num))
  let r0 := (l : ℝ)+(e : ℝ)/2
  let r1 := (l : ℝ)+1+(e : ℝ)/2
  have hR0 := scaled_rear_value hK S hS r0
  have hR1 := scaled_rear_value hK S hS r1
  have hR0pos : ∀ᶠ n : ℕ in atTop, 0<(n : ℝ)^3*rearValue S n (h n) r0 :=
    hR0.eventually (lt_mem_nhds (by dsimp [r0,S]; linarith only [hposR]))
  have hR1neg : ∀ᶠ n : ℕ in atTop, (n : ℝ)^3*rearValue S n (h n) r1<0 :=
    hR1.eventually (gt_mem_nhds (by dsimp [r1,S]; linarith only [hnegR]))
  have hdet := coupledMatrix_eventually_det_ne_zero hscale hS
  filter_upwards [hwide,hpar,eventually_ge_atTop (1:ℕ),hCneg,hApos,hBsmall,hF0pos,hF1neg,
    hR0pos,hR1neg,hdet] with n hnwide hnpar hn hc ha0 hb hf0 hf1 hr0 hr1 hd
  letI : NeZero (q n) := ⟨hq n⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hn0 : (n : ℝ)≠0 := hnR.ne'
  have hh : h n≠0 := mesh_pos.ne'
  have hBineq : a n 2 ≤ a n 0*(n : ℝ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hnR)).mp
    exact le_of_lt (lt_trans hb ha0)
  have hS_eq : rearRealOffsets (q n) l = S := by
    change rearRealOffsets (q n) l = rearRealOffsets e l
    simp only [rearRealOffsets, rearOffsets, hnpar, Nat.mod_eq_of_lt he]
  have hrows : coupledMoments (rearRealOffsets (q n) l) n (mesh (q n)) (a n) =
      ![1-budget n*(mesh (q n))^2, budget n/(n : ℝ)^2,
        3*(n : ℝ)^3*budget n*(mesh (q n))^2/4] := by
    rw [hS_eq]
    rw [← coupledMomentMatrix_mulVec S n hn (h n) (a n)]
    change coupledMomentMatrix S n (h n) *ᵥ
      ((coupledMomentMatrix S n (h n))⁻¹ *ᵥ target n (h n)) = _
    change (coupledMomentMatrix S n (h n)).det ≠ 0 at hd
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),one_mulVec] <;> rfl
  have hpF : 0<fitPolynomial n (h n) (a n) (Real.cos ((n : ℝ)*h n)) := by
    have hpos : 0<boundaryValue S n (h n) 0 :=
      pos_of_mul_pos_right hf0 (sq_nonneg _)
    rw [boundary_poly_eq hn hh S,add_zero] at hpos
    exact hpos
  have hnF : fitPolynomial n (h n) (a n) (Real.cos (((n : ℝ)+1)*h n))≤0 := by
    have hneg : boundaryValue S n (h n) 1<0 :=
      neg_of_mul_neg_right hf1 (sq_nonneg _)
    rw [boundary_poly_eq hn hh S] at hneg
    exact hneg.le
  have hpR : 0<fitPolynomial n (h n) (a n)
      (-Real.cos (((l : ℝ)+((q n%2 : ℕ):ℝ)/2)*h n)) := by
    have hpos : 0<rearValue S n (h n) r0 :=
      pos_of_mul_pos_right hr0 (by positivity)
    rw [rear_poly_eq hn hh S] at hpos
    rw [hnpar]
    exact hpos
  have hnR' : fitPolynomial n (h n) (a n)
      (-Real.cos (((l : ℝ)+1+((q n%2 : ℕ):ℝ)/2)*h n))≤0 := by
    have hneg : rearValue S n (h n) r1<0 :=
      neg_of_mul_neg_right hr1 (by positivity)
    rw [rear_poly_eq hn hh S] at hneg
    rw [hnpar]
    exact hneg.le
  exact window_optimizer hn hnwide (budget n) (a n) hc.le hBineq hrows
    hpF hnF hpR hnR'


private theorem sum_lattice_linear (l : ℕ) :
    (∑ j ∈ latticeInterval l, (j : ℝ)) = 0 := by
  induction l with
  | zero => simp [latticeInterval]
  | succ l ih =>
    unfold latticeInterval at *
    rw [show ((l+1:ℕ):ℤ) = (l:ℤ)+1 by norm_num,
      Finset.sum_Icc_succ_eq_add_endpoints]
    push_cast
    rw [ih]
    ring

private theorem rear_offset_card (e l : ℕ) (he : e<2) :
    ((rearRealOffsets e l).card : ℝ) = 2*(l : ℝ)+1+e := by
  unfold rearRealOffsets
  rw [card_image_of_injective]
  · unfold rearOffsets
    rw [Nat.mod_eq_of_lt he]
    have h := Int.card_Icc_of_le (a := -(l:ℤ)) (b := (l:ℤ)+(e:ℤ)) (by omega)
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hr
    linarith
  · intro j k h
    have hr : (j:ℝ)=(k:ℝ) := by linarith
    exact_mod_cast hr

private theorem rear_square_sum_even (l : ℕ) :
    (∑ r ∈ rearRealOffsets 0 l,r^2) = (l : ℝ)*(l+1)*(2*l+1)/3 := by
  unfold rearRealOffsets
  rw [sum_image]
  · have hh := sum_lattice_square l
    simpa [rearOffsets,latticeInterval] using hh
  · intro j hj k hk h
    have hr : (j:ℝ)=(k:ℝ) := by linarith
    exact_mod_cast hr

private theorem rear_square_sum_odd (l : ℕ) :
    (∑ r ∈ rearRealOffsets 1 l,r^2) =
      ((l:ℝ)+1)*(4*((l:ℝ)+1)^2-1)/6 := by
  unfold rearRealOffsets
  rw [sum_image]
  · have hset : rearOffsets 1 l = insert ((l:ℤ)+1) (latticeInterval l) := by
      ext j
      simp [rearOffsets,latticeInterval]
      omega
    rw [hset,sum_insert (by simp [latticeInterval]),show 1%2=1 by decide]
    push_cast
    have hsum : (∑ j ∈ latticeInterval l, ((j:ℝ)-1/2)^2) =
        (∑ j ∈ latticeInterval l, (j:ℝ)^2) -
        (∑ j ∈ latticeInterval l, (j:ℝ)) + ((latticeInterval l).card : ℝ)/4 := by
      calc
        _ = ∑ j ∈ latticeInterval l, ((j:ℝ)^2-(j:ℝ)+1/4) := by
          apply sum_congr rfl; intro j _; ring
        _ = _ := by
          rw [sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul]
          ring
    rw [hsum,sum_lattice_square,sum_lattice_linear,card_latticeInterval]
    ring
  · intro j hj k hk h
    have hr : (j:ℝ)=(k:ℝ) := by linarith
    exact_mod_cast hr


def rearThreshold (e l : ℕ) : ℝ :=
  if e=0 then (l : ℝ)*(2*l-1)*(2*l+1)/4
  else (l : ℝ)*(l+1/2)*(l+1)

private theorem threshold_equiv (e l : ℕ) (he : e<2) (K : ℝ) :
    (3*((l : ℝ)+(e : ℝ)/2)^2/4 < limitCoefficients (rearRealOffsets e l) K 2 ∧
      limitCoefficients (rearRealOffsets e l) K 2 < 3*((l : ℝ)+1+(e : ℝ)/2)^2/4) ↔
      rearThreshold e l < 3*K/20 ∧ 3*K/20 < rearThreshold e (l+1) := by
  let S := rearRealOffsets e l
  have hc : (0:ℝ)<S.card := by exact_mod_cast (rear_offsets_nonempty e l).card_pos
  have hCard := rear_offset_card e l he
  change (3*((l : ℝ)+(e : ℝ)/2)^2/4 <
        (3*K/20+3*(∑ r∈S,r^2)/4)/(S.card : ℝ) ∧
      (3*K/20+3*(∑ r∈S,r^2)/4)/(S.card : ℝ) <
        3*((l : ℝ)+1+(e : ℝ)/2)^2/4) ↔ _
  rw [lt_div_iff₀ hc,div_lt_iff₀ hc]
  have hlow : 3*((l : ℝ)+(e : ℝ)/2)^2/4*(S.card : ℝ) -
      3*(∑ r∈S,r^2)/4 = rearThreshold e l := by
    change _ = _
    dsimp only [S]
    rw [hCard]
    interval_cases e <;> simp only [Nat.cast_zero,Nat.cast_one,add_zero,zero_div,
      rearThreshold,if_pos rfl,if_neg (by decide : (1:ℕ)≠0),ite_true,ite_false]
    · rw [rear_square_sum_even]; ring
    · rw [rear_square_sum_odd]; ring
  have hhigh : 3*((l : ℝ)+1+(e : ℝ)/2)^2/4*(S.card : ℝ) -
      3*(∑ r∈S,r^2)/4 = rearThreshold e (l+1) := by
    dsimp only [S]
    rw [hCard]
    interval_cases e <;> simp only [Nat.cast_zero,Nat.cast_one,add_zero,zero_div,
      rearThreshold,if_pos rfl,if_neg (by decide : (1:ℕ)≠0),Nat.cast_add,ite_true,ite_false]
    · rw [rear_square_sum_even]; ring
    · rw [rear_square_sum_odd]; ring
  constructor
  · intro h
    exact ⟨by linarith only [h.1,hlow],by linarith only [h.2,hhigh]⟩
  · intro h
    exact ⟨by linarith only [h.1,hlow],by linarith only [h.2,hhigh]⟩

private theorem rearThreshold_strictMono (e : ℕ) (he : e<2) :
    StrictMono (rearThreshold e) := by
  apply strictMono_nat_of_lt_succ
  intro l
  interval_cases e <;> simp only [rearThreshold,if_pos rfl,
    if_neg (by decide : (1:ℕ)≠0),Nat.cast_add,Nat.cast_one,ite_true,ite_false]
  all_goals nlinarith only [sq_nonneg (l : ℝ), Nat.cast_nonneg (α := ℝ) l]

private theorem rearThreshold_ge_index (e l : ℕ) (he : e<2) (hl : 0<l) :
    (l : ℝ)/2 ≤ rearThreshold e l := by
  have hlr : (1:ℝ)≤l := by exact_mod_cast hl
  have h1 := mul_nonneg (sub_nonneg.mpr hlr) (sq_nonneg (l:ℝ))
  interval_cases e <;> simp only [rearThreshold,if_pos rfl,
    if_neg (by decide : (1:ℕ)≠0),ite_true,ite_false]
  all_goals nlinarith only [h1,hlr,sq_nonneg (l:ℝ)]

private theorem strict_threshold_index (e : ℕ) (he : e<2) {Q : ℝ} (hQ : 0<Q)
    (hneq : ∀ l, Q≠rearThreshold e l) :
    ∃! l : ℕ, rearThreshold e l < Q ∧ Q < rearThreshold e (l+1) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2*Q)
  have hkpos : 0<k := by
    by_contra! hn
    have hk0 : k=0 := by omega
    rw [hk0,Nat.cast_zero] at hk
    linarith
  have hex : ∃ k, Q < rearThreshold e k :=
    ⟨k,by linarith only [hk,rearThreshold_ge_index e k he hkpos]⟩
  let k0 := Nat.find hex
  have hk0 : 0<k0 := by
    by_contra! hn
    have hz : k0=0 := by omega
    have hx := Nat.find_spec hex
    change Q<rearThreshold e k0 at hx
    rw [hz] at hx
    simp [rearThreshold] at hx
    linarith
  let l := k0-1
  have hnext : l+1=k0 := by omega
  have hup : Q<rearThreshold e (l+1) := by rw [hnext]; exact Nat.find_spec hex
  have hlo : rearThreshold e l<Q := by
    apply lt_of_le_of_ne _ (Ne.symm (hneq l))
    by_contra! hh
    have hle : k0≤l := Nat.find_min' hex hh
    omega
  refine ⟨l,⟨hlo,hup⟩,?_⟩
  intro j hj
  have hm := rearThreshold_strictMono e he
  by_contra! hne
  rcases lt_or_gt_of_ne hne with hjl | hlj
  · have hh : rearThreshold e (j+1)≤rearThreshold e l := hm.monotone (by omega)
    linarith only [hj.2,hlo,hh]
  · have hh : rearThreshold e (l+1)≤rearThreshold e j := hm.monotone (by omega)
    linarith only [hup,hj.1,hh]


/-- Away from exact rear thresholds, the growing cyclic problem has one eventual support window. -/
theorem eventual_strict_support_away_from_thresholds
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e : ℕ)
    (hpar : ∀ᶠ n in atTop, q n % 2 = e) {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (mesh (q n))^2) atTop (𝓝 K))
    (hneq : ∀ l, 3*K/20 ≠ rearThreshold e l) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    ∃! l : ℕ, rearThreshold e l < 3*K/20 ∧ 3*K/20 < rearThreshold e (l+1) ∧
      ∀ᶠ n : ℕ in atTop,
        letI : NeZero (q n) := ⟨hq n⟩
        let v : ZMod (q n) → ℝ :=
          windowLaw n l (readout ((rearRealOffsets e l,n),mesh (q n)))
        let threshold := 1-2*budget n*(mesh (q n))^2
        cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
        v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) l := by
  dsimp only
  obtain ⟨j,hj⟩ := hpar.exists
  have he : e<2 := by rw [← hj]; omega
  have hKnonneg : 0 ≤ K := ge_of_tendsto hK (Eventually.of_forall fun _ => by positivity)
  have hkne : K ≠ 0 := by
    intro hz
    have h := hneq 0
    simp [hz,rearThreshold] at h
  have hKpos : 0 < K := lt_of_le_of_ne hKnonneg hkne.symm
  obtain ⟨l,hl,hu⟩ := strict_threshold_index e he (by positivity : 0<3*K/20) hneq
  obtain ⟨hpos,hneg⟩ := (threshold_equiv e l he K).mpr hl
  refine ⟨l,⟨hl.1,hl.2,eventual_strict_window_support q hq e l hpar hK hpos hneg⟩,?_⟩
  intro j hj
  exact hu j ⟨hj.1,hj.2.1⟩

end

end D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
