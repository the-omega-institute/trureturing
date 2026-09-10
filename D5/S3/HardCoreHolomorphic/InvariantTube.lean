/- GID: D5/S3/HardCoreHolomorphic/InvariantTube
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/InvariantTube
   mirror-E: none(waiver:uniform-analytic-invariant-neighborhood)
   anchors: []
   digest: Integrating the actual complex differential gives one invariant tube for every certified row. -/

import D5.S3.HardCoreHolomorphic.RowTubeBounds
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.InvariantTube
open scoped BigOperators
open D5.S3.HardCoreHolomorphic.AffineChart
open D5.S3.HardCoreHolomorphic.TypedJacobian
open D5.S3.HardCoreHolomorphic.TubeEstimates
open D5.S3.HardCoreHolomorphic.RowTubeBounds

variable {ι : Type*} [DecidableEq ι]

/-- The real centers are mapped to the correct real parent center, for every
pruning set including the leaf and activity zero. -/
theorem row_at_centers (s : Finset ι) (a0 b0 : ℝ) (a b r : ι → ℝ)
    (hc0 : CoeffBound a0 b0) (hc : ∀ j ∈ s, CoeffBound (a j) (b j))
    (hr : ∀ j ∈ s, 20/71 ≤ r j ∧ r j ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51/20) :
    let y : ℝ := (1+lam*∏ j ∈ s, r j)⁻¹
    (20/71 ≤ y ∧ y ≤ 1) ∧
    rowMap s a0 b0 (fun j => a j) (fun j => b j) lam
      (fun j => center (a j) (b j) (r j)) = center a0 b0 y := by
  let P : ℝ := ∏ j ∈ s, r j
  have hp : 0 ≤ P ∧ P ≤ 1 := by
    refine ⟨Finset.prod_nonneg (fun j hj => by linarith [(hr j hj).1]), ?_⟩
    have h := Finset.prod_le_prod (fun j hj => show 0 ≤ r j by linarith [(hr j hj).1])
      (fun j hj => (hr j hj).2)
    simpa using h
  have hA : 0 ≤ lam*P ∧ lam*P ≤ 51/20 :=
    ⟨mul_nonneg hlam.1 hp.1,
      (mul_le_mul_of_nonneg_left hp.2 hlam.1).trans (by simpa using hlam.2)⟩
  have hD : 0 < 1+lam*P := by linarith [hA.1]
  have hy : 20/71 ≤ (1+lam*P)⁻¹ ∧ (1+lam*P)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    constructor
    · apply (le_div_iff₀ hD).mpr; nlinarith [hA.2]
    · apply (div_le_iff₀ hD).mpr; linarith [hA.1]
  have hprod : messageProduct s (fun j => (a j:ℂ)) (fun j => (b j:ℂ))
      (fun j => center (a j) (b j) (r j)) = (P:ℂ) := by
    dsimp [messageProduct, P]
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro j hj
    apply inverse_center
    · rcases hc j hj with ⟨ha,hc,hb⟩; linarith
    · linarith [(hr j hj).1]
    · rcases hc j hj with ⟨ha,hc,hb⟩
      nlinarith [mul_le_mul_of_nonneg_left (hr j hj).2 ha]
  have hb0 : 0 < b0 := by rcases hc0 with ⟨ha,hc,hb⟩; linarith
  have hH : 0 < b0-a0+b0*(lam*P) := by
    rcases hc0 with ⟨ha,hc,hb⟩
    nlinarith [mul_nonneg hb0.le hA.1]
  refine ⟨hy, ?_⟩
  dsimp only [rowMap, logArgument]
  rw [hprod]
  have hid : b0/(1+lam*P)⁻¹-a0 = b0-a0+b0*(lam*P) := by
    rw [div_inv_eq_mul]; ring
  dsimp only [center]
  rw [hid]
  push_cast
  rw [Complex.ofReal_log hH.le]
  push_cast
  ring

/-- The actual complex Jacobian retains a strict margin on the entire tube.
The real-row value at the chosen real anchor suffices for this local comparison. -/
theorem jacobian_tube_sum (s : Finset ι) (hs : s.card ≤ 4)
    (a0 b0 : ℝ) (a b r : ι → ℝ)
    (hc0 : CoeffBound a0 b0) (hc : ∀ j ∈ s, CoeffBound (a j) (b j))
    (hr : ∀ j ∈ s, 1/4 ≤ r j ∧ r j ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 3)
    (hreal : (∑ j ∈ s, ‖((-(lam*(∏ k ∈ s, r k)*(b j-a j*r j)) /
      (b0-a0+b0*lam*(∏ k ∈ s, r k)):ℝ):ℂ)‖) ≤ 999/1000)
    (z : ℂ) (hz : ‖z-(lam:ℂ)‖ ≤ epsilon)
    (m : ι → ℂ) (hm : ∀ j ∈ s, ‖m j-center (a j) (b j) (r j)‖ ≤ delta) :
    (∑ j ∈ s, ‖jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) z m j‖) < 1999/2000 := by
  have h := row_tube_bounds s hs a0 b0 a b hc0 hc r hr lam hlam z hz m hm
  have hd := h.2.2.2.2
  have hn : (s.card:ℝ) ≤ 4 := by exact_mod_cast hs
  have hb : (∑ j ∈ s, ‖jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) z m j‖) ≤
      (999/1000:ℝ)+s.card*(10^11*delta) := by
    calc
      _ ≤ ∑ j ∈ s, (‖((-(lam*(∏ k ∈ s, r k)*(b j-a j*r j)) /
            (b0-a0+b0*lam*(∏ k ∈ s, r k)):ℝ):ℂ)‖+10^11*delta) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := norm_le_norm_sub_add
          (jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) z m j)
          (((-(lam*(∏ k ∈ s, r k)*(b j-a j*r j)) /
            (b0-a0+b0*lam*(∏ k ∈ s, r k)):ℝ):ℂ))
        linarith [hd j hj]
      _ ≤ _ := by simpa [Finset.sum_add_distrib] using add_le_add_right hreal (s.card*(10^11*delta))
  have hw : (999/1000:ℝ)+10^12*delta < 1999/2000 := by norm_num [delta]
  have hdpos : 0 ≤ delta := by norm_num [delta]
  nlinarith

/-- Uniform stability is derived by integrating the true differential along
straight message/activity segments. There is no supplied complex Lipschitz or
complex-invariance premise. -/
theorem row_tube_stability (s : Finset ι) (hs : s.card ≤ 4)
    (a0 b0 : ℝ) (a b r : ι → ℝ)
    (hc0 : CoeffBound a0 b0) (hc : ∀ j ∈ s, CoeffBound (a j) (b j))
    (hr : ∀ j ∈ s, 1/4 ≤ r j ∧ r j ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 3)
    (hreal : (∑ j ∈ s, ‖((-(lam*(∏ k ∈ s, r k)*(b j-a j*r j)) /
      (b0-a0+b0*lam*(∏ k ∈ s, r k)):ℝ):ℂ)‖) ≤ 999/1000)
    (z : ℂ) (hz : ‖z-(lam:ℂ)‖ ≤ epsilon)
    (m : ι → ℂ) (hm : ∀ j ∈ s, ‖m j-center (a j) (b j) (r j)‖ ≤ delta) :
    ‖rowMap s a0 b0 (fun j => a j) (fun j => b j) z m -
      rowMap s a0 b0 (fun j => a j) (fun j => b j) lam
        (fun j => center (a j) (b j) (r j))‖ < delta := by
  let dz := z-(lam:ℂ)
  let dm := fun j => m j-center (a j) (b j) (r j)
  let zt := fun t : ℂ => (lam:ℂ)+t*dz
  let mt := fun j (t:ℂ) => center (a j) (b j) (r j)+t*dm j
  let f := fun t : ℂ => rowMap s a0 b0 (fun j => a j) (fun j => b j) (zt t) (fun j => mt j t)
  let df := fun t : ℂ => activityEntry s a0 b0 (fun j => a j) (fun j => b j) (zt t)
      (fun j => mt j t)*dz + ∑ j ∈ s,
        jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) (zt t) (fun j => mt j t) j*dm j
  have hzp (t:ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖zt t-(lam:ℂ)‖ ≤ epsilon := by
    dsimp [zt]; rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg dz)).trans (by simpa [dz] using hz)
  have hmp (t:ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j) (hj : j ∈ s) :
      ‖mt j t-center (a j) (b j) (r j)‖ ≤ delta := by
    dsimp [mt]; rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (dm j))).trans (by simpa [dm] using hm j hj)
  have hb0 : (b0:ℂ) ≠ 0 := by
    have h : 0 < b0 := by rcases hc0 with ⟨ha,hc,hb⟩; linarith
    exact_mod_cast ne_of_gt h
  have hf (t:ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun u:ℝ => f u) (df t) t := by
    have htube := row_tube_bounds s hs a0 b0 a b hc0 hc r hr lam hlam
      (zt t) (hzp t ht) (fun j => mt j t) (hmp t ht)
    have hslit : logArgument s a0 b0 (fun j => a j) (fun j => b j)
        (zt t) (fun j => mt j t) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le (by norm_num) htube.2.1))
    have h := rowMap_hasDerivAt s a0 b0 (fun j => a j) (fun j => b j) zt mt t dz dm hb0
      (by simpa [zt] using ((hasDerivAt_id (t:ℂ)).mul_const dz).const_add (lam:ℂ))
      (fun j _ => by
        simpa [mt] using ((hasDerivAt_id (t:ℂ)).mul_const (dm j)).const_add
          (center (a j) (b j) (r j))) htube.1 hslit
    exact h.comp_ofReal
  have hdf (t:ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖df t‖ ≤ (1999/2000:ℝ)*delta+10000*epsilon := by
    have htube := row_tube_bounds s hs a0 b0 a b hc0 hc r hr lam hlam
      (zt t) (hzp t ht) (fun j => mt j t) (hmp t ht)
    have hjac := jacobian_tube_sum s hs a0 b0 a b r hc0 hc hr lam hlam hreal
      (zt t) (hzp t ht) (fun j => mt j t) (hmp t ht)
    dsimp [df]
    calc
      _ ≤ ‖activityEntry s a0 b0 (fun j => a j) (fun j => b j) (zt t) (fun j => mt j t)‖*‖dz‖+
          ∑ j ∈ s, ‖jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) (zt t) (fun j => mt j t) j‖*‖dm j‖ :=
        (norm_add_le _ _).trans (add_le_add (by rw [norm_mul]) (by
          simpa only [norm_mul] using norm_sum_le s (fun j =>
            jacobianEntry s a0 b0 (fun k => a k) (fun k => b k)
              (zt t) (fun k => mt k t) j * dm j)))
      _ ≤ 10000*epsilon+(∑ j ∈ s, ‖jacobianEntry s a0 b0 (fun j => a j) (fun j => b j)
          (zt t) (fun j => mt j t) j‖)*delta := by
        apply add_le_add
        · exact mul_le_mul htube.2.2.2.1 hz (norm_nonneg _) (by norm_num)
        · rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hm j hj) (norm_nonneg _))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hjac.le width_arithmetic.1.le]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf t ht).hasDerivWithinAt) hdf (convex_Icc (0:ℝ) 1)
    (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1:ℝ) ∈ Set.Icc 0 1)
  have hfinal : ‖f 1-f 0‖ ≤ (1999/2000:ℝ)*delta+10000*epsilon := by simpa using hmv
  have hw : (1999/2000:ℝ)*delta+10000*epsilon < delta := by norm_num [delta,epsilon]
  simpa [f,zt,mt,dz,dm] using hfinal.trans_lt hw

#print axioms row_at_centers
#print axioms jacobian_tube_sum
#print axioms row_tube_stability
end D5.S3.HardCoreHolomorphic.InvariantTube
