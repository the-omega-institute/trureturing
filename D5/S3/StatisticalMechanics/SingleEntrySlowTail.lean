/- GID: D5/S3/StatisticalMechanics/SingleEntrySlowTail
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntrySlowTail
   mirror-E: none(waiver:conditional-single-entry-slow-tail)
   anchors: []
   utility: none
   digest: A slower input mode transfers its exact coefficient to the association residual. -/

import D5.S3.StatisticalMechanics.SingleEntryFiveState
import D5.S3.StatisticalMechanics.SingleEntrySecularRoot

/-! # Exact association tails from an independently supplied input tail

The differential equation, input asymptotic and joint-occupancy equilibrium
are separate premises. This module does not identify a generator eigenvalue
or supply its residue. It proves the analytic transfer needed after those
spectral and equilibrium bridges have been established for the same chain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter

namespace D5.S3.StatisticalMechanics.SingleEntrySlowTail

private theorem upper_barrier (y g : ℝ → ℝ) (c B T t : ℝ)
    (hT : 0 ≤ T) (ht : T ≤ t)
    (hy : ∀ u, 0 ≤ u → HasDerivAt y (-c * y u + g u) u)
    (hg : ∀ u, T ≤ u → g u ≤ c * B) :
    y t ≤ B + Real.exp (-c * (t - T)) * (y T - B) := by
  let H := fun u => Real.exp (c * u) * (y u - B)
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt H (Real.exp (c * u) * (g u - c * B)) u := by
    convert (((hasDerivAt_id u).const_mul c).exp.mul
      ((hy u hu).sub_const B)) using 1 <;>
      first | rfl | (dsimp [H]; ring)
  have hm : AntitoneOn H (Icc T t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro u hu
      exact (hd u (hT.trans hu.1)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hd u (hT.trans hu.1.le)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u (hT.trans hu.1.le)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hg u hu.1.le))
  have hh := hm (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  have he : Real.exp (c * t) * Real.exp (-c * (t - T)) = Real.exp (c * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh' : Real.exp (c * t) *
      (y t - (B + Real.exp (-c * (t - T)) * (y T - B))) ≤ 0 := by
    dsimp [H] at hh
    have he' : Real.exp (c * T) * (y T - B) =
        Real.exp (c * t) * (Real.exp (-c * (t - T)) * (y T - B)) := by
      rw [← mul_assoc, he]
    rw [he'] at hh
    nlinarith only [hh]
  apply sub_nonpos.mp
  exact nonpos_of_mul_nonpos_right hh' (Real.exp_pos (c * t))

private theorem lower_barrier (y g : ℝ → ℝ) (c B T t : ℝ)
    (hT : 0 ≤ T) (ht : T ≤ t)
    (hy : ∀ u, 0 ≤ u → HasDerivAt y (-c * y u + g u) u)
    (hg : ∀ u, T ≤ u → c * B ≤ g u) :
    B + Real.exp (-c * (t - T)) * (y T - B) ≤ y t := by
  have hh := upper_barrier (fun u => -y u) (fun u => -g u) c (-B) T t hT ht
    (by
      intro u hu
      convert (hy u hu).neg using 1
      ring)
    (by intro u hu; linarith [hg u hu])
  linarith

private theorem barrier_tendsto (c B T yT : ℝ) (hc : 0 < c) :
    Tendsto (fun t => B + Real.exp (-c * (t - T)) * (yT - B)) atTop (nhds B) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-c * (t - T))) atTop (nhds 0) := by
    have hshift : Tendsto (fun t : ℝ => t - T) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
    have ht : Tendsto (fun t : ℝ => c * (t - T)) atTop atTop :=
      hshift.const_mul_atTop hc
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  simpa using (he.mul_const (yT - B)).const_add B

private theorem stable_forcing_limit (y g : ℝ → ℝ) (c L : ℝ) (hc : 0 < c)
    (hy : ∀ u, 0 ≤ u → HasDerivAt y (-c * y u + g u) u)
    (hg : Tendsto g atTop (nhds L)) :
    Tendsto y atTop (nhds (L / c)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let B := (a + L / c) / 2
    have haB : a < B := by dsimp [B]; linarith
    have hBL : c * B < L := by
      have hB : B < L / c := by dsimp [B]; linarith
      simpa only [mul_comm] using (lt_div_iff₀ hc).mp hB
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hg.eventually (Ioi_mem_nhds hBL))
    let T := max T₀ 0
    have hT : 0 ≤ T := le_max_right _ _
    have hforce : ∀ u, T ≤ u → c * B ≤ g u := by
      intro u hu
      exact (hT₀ u ((le_max_left _ _).trans hu)).le
    have he := (barrier_tendsto c B T (y T) hc).eventually (Ioi_mem_nhds haB)
    filter_upwards [eventually_ge_atTop T, he] with t ht he
    exact lt_of_lt_of_le he (lower_barrier y g c B T t hT ht hy hforce)
  · intro b hb
    let B := (b + L / c) / 2
    have hBb : B < b := by dsimp [B]; linarith
    have hLB : L < c * B := by
      have hB : L / c < B := by dsimp [B]; linarith
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp hB
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hg.eventually (Iio_mem_nhds hLB))
    let T := max T₀ 0
    have hT : 0 ≤ T := le_max_right _ _
    have hforce : ∀ u, T ≤ u → g u ≤ c * B := by
      intro u hu
      exact (hT₀ u ((le_max_left _ _).trans hu)).le
    have he := (barrier_tendsto c B T (y T) hc).eventually (Iio_mem_nhds hBb)
    filter_upwards [eventually_ge_atTop T, he] with t ht he
    exact lt_of_le_of_lt (upper_barrier y g c B T t hT ht hy hforce) he

/-- An independently established slow net-input tail and joint equilibrium
force the exact association tail. The hypotheses concern the actual three
functions of one common time variable; no limit of the association is assumed. -/
theorem association_tail_from_input_tail (D f K : ℝ → ℝ)
    (s l theta rInf qi qj slope : ℝ)
    (hslow : l < s) (htheta : 0 < theta) (hr : 0 < rInf)
    (hqi : 0 < qi) (hqj : 0 < qj) (hslope : slope < 0)
    (hD : ∀ t, 0 ≤ t → HasDerivAt D (-s * D t + f t * K t) t)
    (hf : Tendsto (fun t => Real.exp (l * t) * f t) atTop (nhds (-theta / slope)))
    (hK : Tendsto K atTop (nhds (rInf * qi * qj))) :
    Tendsto (fun t => Real.exp (l * t) * D t) atTop
      (nhds (-theta * rInf * qi * qj / ((s - l) * slope))) ∧
      0 < -theta * rInf * qi * qj / ((s - l) * slope) := by
  let y := fun t => Real.exp (l * t) * D t
  let g := fun t => (Real.exp (l * t) * f t) * K t
  have hy : ∀ t, 0 ≤ t → HasDerivAt y (-(s - l) * y t + g t) t := by
    intro t ht
    convert (((hasDerivAt_id t).const_mul l).exp.mul (hD t ht)) using 1 <;>
      first | rfl | (dsimp [y, g]; ring)
  have hg : Tendsto g atTop (nhds ((-theta / slope) * (rInf * qi * qj))) := hf.mul hK
  have heq : (-theta / slope) * (rInf * qi * qj) / (s - l) =
      -theta * rInf * qi * qj / ((s - l) * slope) := by
    field_simp
  constructor
  · rw [← heq]
    exact stable_forcing_limit y g (s - l) _ (sub_pos.mpr hslow) hy hg
  · exact div_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos htheta) hr) hqi) hqj)
      (mul_neg_of_pos_of_neg (sub_pos.mpr hslow) hslope)

#print axioms association_tail_from_input_tail

end D5.S3.StatisticalMechanics.SingleEntrySlowTail
