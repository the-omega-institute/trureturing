/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact adjacent-window support selection at a growing rear activation threshold. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! A determinant ratio compares the two adjacent signed fits. -/

open Finset Matrix Filter Asymptotics
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder
open D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact

noncomputable section

set_option autoImplicit false

private theorem rank_one_score {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : 0<M.det) (u r b x y : ι → ℝ)
    (hx : M *ᵥ x=b) (hy : (M+vecMulVec u r)*ᵥ y=b) :
    M.det*(r ⬝ᵥ x) = (M+vecMulVec u r).det*(r ⬝ᵥ y) := by
  have hu := isUnit_iff_ne_zero.mpr hM.ne'
  have hMr : M *ᵥ (M⁻¹ *ᵥ u) = u := by
    rw [mulVec_mulVec,mul_nonsing_inv _ hu,one_mulVec]
  have houter : vecMulVec u r *ᵥ y = (r ⬝ᵥ y) • u := by
    ext i
    simp [vecMulVec_mulVec,mul_comm]
  rw [add_mulVec,houter,← hx] at hy
  have hxy : x = y+(r ⬝ᵥ y) • (M⁻¹ *ᵥ u) := by
    have he : M *ᵥ x = M *ᵥ (y+(r ⬝ᵥ y) • (M⁻¹ *ᵥ u)) := by
      rw [mulVec_add,mulVec_smul,hMr]
      exact hy.symm
    have hh := congrArg (fun z => M⁻¹ *ᵥ z) he
    simpa only [mulVec_mulVec,nonsing_inv_mul _ hu,one_mulVec] using hh
  have hd := det_add_replicateCol_mul_replicateRow (ι:=Unit) hu u r
  rw [← vecMulVec_eq Unit,Matrix.mul_assoc,← replicateCol_mulVec] at hd
  have hscalar : (1+replicateRow Unit r*replicateCol Unit (M⁻¹ *ᵥ u)).det =
      1+r ⬝ᵥ (M⁻¹ *ᵥ u) := by
    rw [det_unique]
    simp [Matrix.add_apply]
  have hd' : (M+vecMulVec u r).det=M.det*(1+r ⬝ᵥ (M⁻¹ *ᵥ u)) := by
    rw [hscalar] at hd
    exact hd
  rw [hd',hxy,dotProduct_add,dotProduct_smul]
  ring

private theorem adjacent_offsets (e l : ℕ) (he : e<2) :
    let R := (l:ℝ)+1+(e:ℝ)/2
    rearRealOffsets e (l+1) = insert R (insert (-R) (rearRealOffsets e l)) := by
  intro R
  have hmod : e%2=e := Nat.mod_eq_of_lt he
  have hset : rearOffsets e (l+1) =
      insert ((l:ℤ)+1+e) (insert (-(l:ℤ)-1) (rearOffsets e l)) := by
    ext j
    simp only [rearOffsets,hmod,Nat.cast_add,Nat.cast_one,mem_Icc,mem_insert]
    omega
  rw [rearRealOffsets,hset,Finset.image_insert,Finset.image_insert]
  change insert ((((l:ℤ)+1+e:ℤ):ℝ)-((e%2:ℕ):ℝ)/2)
      (insert ((((-(l:ℤ)-1):ℤ):ℝ)-((e%2:ℕ):ℝ)/2) (rearRealOffsets e l)) = _
  congr 1
  all_goals simp [R,hmod] <;> ring

private theorem outside_offsets (e l : ℕ) (he : e<2) :
    let R := (l:ℝ)+1+(e:ℝ)/2
    R ∉ rearRealOffsets e l ∧ -R ∉ rearRealOffsets e l ∧ R≠-R := by
  intro R
  have hmod : e%2=e := Nat.mod_eq_of_lt he
  have hR : 0<R := by dsimp [R]; positivity
  refine ⟨?_,?_,by linarith⟩
  · intro h
    obtain ⟨j,hj,hjr⟩ := mem_image.mp h
    have hb := (mem_Icc.mp hj).2
    simp only [rearOffsets,hmod] at hb
    have hb' : (j:ℝ)≤(l:ℝ)+(e:ℝ) := by exact_mod_cast hb
    simp only [hmod] at hjr
    dsimp [R] at hjr
    linarith
  · intro h
    obtain ⟨j,hj,hjr⟩ := mem_image.mp h
    have hb := (mem_Icc.mp hj).1
    have hb' : -(l:ℝ)≤(j:ℝ) := by exact_mod_cast hb
    simp only [hmod] at hjr
    dsimp [R] at hjr
    linarith


private theorem rear_matrix_neg (n h r : ℝ) : rearMatrix n h (-r)=rearMatrix n h r := by
  have hw : rearWeight h (-r)=rearWeight h r := by simp [rearWeight,neg_mul,Real.cos_neg]
  have hx : rearMoment h (-r)=rearMoment h r := by simp [rearMoment,neg_mul,Real.sinc_neg]
  simp only [rearMatrix,hw,hx]

private theorem adjacent_matrix (e l n : ℕ) (he : e<2) (h : ℝ) :
    let R := (l:ℝ)+1+(e:ℝ)/2
    coupledMomentMatrix (rearRealOffsets e (l+1)) n h =
      coupledMomentMatrix (rearRealOffsets e l) n h + (2:ℝ) • rearMatrix n h R := by
  intro R
  obtain ⟨hp,hm,hne⟩ := outside_offsets e l he
  change R ∉ rearRealOffsets e l at hp
  change -R ∉ rearRealOffsets e l at hm
  have hnot : R ∉ insert (-R) (rearRealOffsets e l) := by
    change R≠-R at hne
    simp only [mem_insert,not_or]
    exact ⟨hne,hp⟩
  rw [adjacent_offsets e l he]
  unfold coupledMomentMatrix
  change frontMatrix n ((n:ℝ)*h)+∑ r∈insert R (insert (-R) (rearRealOffsets e l)),rearMatrix n h r = _
  rw [sum_insert hnot,sum_insert hm,rear_matrix_neg]
  module

private theorem eventually_det_pos {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    ∀ᶠ n : ℕ in atTop, 0<(coupledMomentMatrix S n (h n)).det := by
  have ht := continuous_id.matrix_det.continuousAt.tendsto.comp
    (coupledMatrix_tendsto (critical_bound_mesh_limits (hK.isBigO_one ℝ)).2.2 S)
  change Tendsto (fun n => (coupledMomentMatrix S n (h n)).det) atTop
    (𝓝 (!![(2:ℝ),2/3,0;2/3,2/5,0;0,∑ r∈S,r^2,(S.card:ℝ)]).det) at ht
  rw [coupledLimit_det] at ht
  have hc : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  exact ht.eventually (lt_mem_nhds (by positivity))

/-- Adding the antipodal pair preserves the boundary score up to the positive determinant ratio. -/
theorem adjacent_fit_score {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (e l : ℕ) (he : e<2) :
    let R := (l:ℝ)+1+(e:ℝ)/2
    let S := rearRealOffsets e l
    let T := rearRealOffsets e (l+1)
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      rearValue state.1.1.1 state.1.1.2 state.1.2 state.2
    ∀ᶠ n : ℕ in atTop,
      0<(coupledMomentMatrix S n (h n)).det ∧
      0<(coupledMomentMatrix T n (h n)).det ∧
      (coupledMomentMatrix S n (h n)).det*readout (((S,n),h n),R) =
      (coupledMomentMatrix T n (h n)).det*readout (((T,n),h n),R) := by
  dsimp only
  let R := (l:ℝ)+1+(e:ℝ)/2
  let S := rearRealOffsets e l
  let T := rearRealOffsets e (l+1)
  have hS := rear_offsets_nonempty e l
  have hT := rear_offsets_nonempty e (l+1)
  filter_upwards [eventually_det_pos hK S hS,eventually_det_pos hK T hT,
    eventually_ge_atTop (1:ℕ)] with n hnS hnT hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  let M := coupledMomentMatrix S n (h n)
  let N := coupledMomentMatrix T n (h n)
  let w := rearWeight (h n) R
  let X := rearMoment (h n) R/(n:ℝ)^2
  let r := coefficientRow n (1-w) X w
  let u := (2:ℝ) • momentRow n (1-w) X w
  have hN : N=M+vecMulVec u r := by
    change coupledMomentMatrix T n (h n)=coupledMomentMatrix S n (h n)+vecMulVec u r
    rw [adjacent_matrix e l n he (h n)]
    rw [rearMatrix_outer hn0]
    congr 1
    ext i j
    simp [u,r,w,X,vecMulVec_apply]
    ring
  let x := coefficientFit S n (h n)
  let y := coefficientFit T n (h n)
  have hx : M *ᵥ x=target n (h n) := by
    change M *ᵥ M⁻¹ *ᵥ target n (h n)=_
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hnS.ne'),one_mulVec]
  have hy : N *ᵥ y=target n (h n) := by
    change N *ᵥ N⁻¹ *ᵥ target n (h n)=_
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hnT.ne'),one_mulVec]
  have heq := rank_one_score hnS u r (target n (h n)) x y hx (hN ▸ hy)
  rw [← hN] at heq
  exact ⟨hnS,hnT,heq⟩



/-- The exact finite sign chooses the adjacent support at every sufficiently large radius. -/
theorem eventual_support_at_leading_threshold
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (hpar : ∀ᶠ n in atTop, q n % 2 = e) {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (q n))^2) atTop (𝓝 K))
    (hcrit : 3*K/20=rearThreshold e (l+1)) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    let R := (l:ℝ)+1+(e:ℝ)/2
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let k := if 0<rearValue (rearRealOffsets e l) n (mesh (q n)) R then l+1 else l
      let v : ZMod (q n) → ℝ := windowLaw n k (readout ((rearRealOffsets e k,n),mesh (q n)))
      let threshold := 1-2*budget n*(mesh (q n))^2
      cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) k := by
  obtain ⟨j,hj⟩ := hpar.exists
  have he : e < 2 := by rw [← hj]; omega
  let h := fun n => mesh (q n)
  let R := (l:ℝ)+1+(e:ℝ)/2
  let S := rearRealOffsets e l
  let T := rearRealOffsets e (l+1)
  have hmono := rearThreshold_strictMono e he
  have hlow : rearThreshold e l < 3*K/20 := hcrit ▸ hmono (Nat.lt_succ_self l)
  have hhigh : 3*K/20 < rearThreshold e (l+2) := hcrit ▸ hmono (Nat.lt_succ_self (l+1))
  obtain ⟨hS0,_⟩ := rear_threshold_endpoints e l he
  obtain ⟨_,hT1⟩ := rear_threshold_endpoints e (l+1) he
  have hSpos := leading_boundary_pos hK S (rear_offsets_nonempty e l)
    ((l:ℝ)+(e:ℝ)/2) (hS0.trans_lt hlow)
  have hTneg := leading_boundary_neg hK T (rear_offsets_nonempty e (l+1))
    (((l+1:ℕ):ℝ)+1+(e:ℝ)/2) (hhigh.trans_eq hT1.symm)
  have hscore := adjacent_fit_score hK e l he
  have hSmall := eventual_window_support_of_point_signs q hq e l hpar hK
  have hLarge := eventual_window_support_of_point_signs q hq e (l+1) hpar hK
  filter_upwards [eventually_ge_atTop (1:ℕ),hSpos,hTneg,hscore,hSmall,hLarge]
    with n hn hs ht ⟨hdS,hdT,heq⟩ hcS hcT
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hp : 0<rearValue S n (h n) R
  · have hlarge : 0<rearValue T n (h n) R := by
      apply pos_of_mul_pos_right _ hdT.le
      change 0 < (coupledMomentMatrix T n (h n)).det * rearValue T n (h n) R
      rw [← heq]
      exact mul_pos hdS hp
    have hpos : 0<(n:ℝ)^3*rearValue T n (h n) (((l+1:ℕ):ℝ)+(e:ℝ)/2) := by
      simpa only [Nat.cast_add,Nat.cast_one,R] using mul_pos (pow_pos hnR 3) hlarge
    dsimp only
    rw [ite_eq_left hp]
    exact hcT hpos ht.le
  · have hnonpos : (n:ℝ)^3*rearValue S n (h n) R≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hp)
    dsimp only
    rw [ite_eq_right hp]
    exact hcS hs hnonpos


end

end D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact
