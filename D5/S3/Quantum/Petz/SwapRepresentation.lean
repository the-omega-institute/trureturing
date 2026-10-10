/- GID: D5/S3/Quantum/Petz/SwapRepresentation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real swap representation and signed-density first-partial difference for the symmetric Petz kernel. -/

import D5.S3.Quantum.PositiveResolvent.SwapDifferentiation
import D5.S3.Quantum.Petz.KernelSmoothness
import D5.S3.Quantum.Petz.PDoubleStieltjes
import D5.S3.Quantum.Petz.SymmetricStieltjesSwap

namespace D5.S3.Quantum.Petz.SwapRepresentation

open Set MeasureTheory Filter
open scoped Topology
open D5.S3.Quantum.Petz.SymmetricKernel
open D5.S3.Quantum.Petz.KernelSmoothness
open D5.S3.Quantum.PositiveResolvent.SwapDifferentiation
open D5.S3.Quantum.PositiveResolvent.EulerResolvent
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.Petz.DoubleStieltjes
open D5.S3.Quantum.Petz.DoubleStieltjesMarginals
open D5.S3.Quantum.Petz.DoubleStieltjesRepresentations
open D5.S3.Quantum.Petz.PDoubleStieltjes
open D5.S3.Quantum.Petz.SymmetricStieltjesSwap

/-- The derivative consequence of a locally proved fixed-density representation. -/
private theorem hs1_sub_of_fixed_density {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    {d : ℝ → ℝ} (hd : Measurable d)
    (hi : IntegrableOn (fun s => (1 / (x+s) + 1 / (y+s)) * d s) (Ioi 0))
    (hrep : ∀ᶠ h in 𝓝 (0 : ℝ),
      (∫ s in Ioi (0 : ℝ), (1 / (x+h+s) + 1 / (y-h+s)) * d s) = -hs (x+h) (y-h) z) :
    IntegrableOn (fun s => (x+y+2*s) / ((x+s)^2*(y+s)^2) * d s) (Ioi 0) ∧
      hs1 x y z - hs1 y x z = (y-x) *
        ∫ s in Ioi (0 : ℝ), (x+y+2*s) / ((x+s)^2*(y+s)^2) * d s := by
  obtain ⟨hint, hderiv⟩ := signed_swap_hasDerivAt hx hy hd hi
  have hf := (hs_differentiableAt hx hy hz).hasFDerivAt
  let L := fderiv ℝ (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) (x,y,z)
  have hf0 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) L
      (x+0, y-0, z) := by simpa only [add_zero, sub_zero] using hf
  have hp := hf0.comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).const_add x).prodMk
      (((hasDerivAt_const (0 : ℝ) y).sub (hasDerivAt_id (0 : ℝ))).prodMk
        (hasDerivAt_const (0 : ℝ) z)))
  have hp : HasDerivAt (fun h => hs (x+h) (y-h) z) (L (1,-1,0)) 0 := by
    simpa only [Function.comp_def, id_eq, add_zero, sub_zero, zero_sub, Pi.sub_apply] using hp
  have h1 := hf.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z)))
  have h1 : hs1 x y z = L (1,0,0) := by
    simpa only [hs1, Function.comp_def, id_eq] using h1.deriv
  have h2 := hf.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z)))
  have h2 : hs1 y x z = L (0,1,0) := by
    rw [← hs1_swap hx hy hz]
    simpa only [Function.comp_def, id_eq] using h2.deriv
  have hv : ((1,-1,0) : ℝ × ℝ × ℝ) = (1,0,0) - (0,1,0) := by ext <;> norm_num
  have hl : L (1,-1,0) = hs1 x y z - hs1 y x z := by rw [hv, map_sub, ← h1, ← h2]
  rw [hl] at hp
  have hrepeq : (fun h => ∫ s in Ioi (0 : ℝ),
      (1 / (x+h+s) + 1 / (y-h+s)) * d s) =ᶠ[𝓝 (0 : ℝ)]
      (fun h => -hs (x+h) (y-h) z) := hrep
  have hsame := hderiv.congr_of_eventuallyEq hrepeq.symm
  have he := hp.neg.unique hsame
  refine ⟨hint, ?_⟩
  linarith only [he]

private lemma moving_nodes_ne (x y z : ℝ) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), x+y+s ≠ z := by
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (z-(x+y)))] with s hs
  intro h
  apply hs
  linarith

private theorem Q_swap {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s => (1/(x+s)+1/(y+s))*rQ (x+y+s) z s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (1/(x+s)+1/(y+s))*rQ (x+y+s) z s) =
        D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference.Q x y z := by
  have hq := Q_double_stieltjes hx hy z
  have h := symmetric_stieltjes_swap (A z) (A_measurable z)
    (fun s t _ _ => (A_pos z s t).le) (fun s t _ _ => A_symm z s t) hx hy hq.1
  have he : (fun s => (1/(x+s)+1/(y+s)) *
      (∫ t in Ioi (0 : ℝ), A z s t/(x+y+s+t))) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => (1/(x+s)+1/(y+s))*rQ (x+y+s) z s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, moving_nodes_ne x y z] with s hs hn
    change 0 < s at hs
    rw [(A_marginal_eq_rQ hs (add_pos (add_pos hx hy) hs) hz hn).2]
  refine ⟨h.1.congr he, ?_⟩
  rw [← integral_congr_ae he, ← h.2, hq.2]

private theorem P_swap {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s => (1/(x+s)+1/(y+s))*rP (x+y+s) z s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (1/(x+s)+1/(y+s))*rP (x+y+s) z s) = P x y z := by
  obtain ⟨hd, hb, hp⟩ := P_double_stieltjes hx hy hz
  have h := symmetric_stieltjes_swap (B z) (B_measurable z)
    (fun s t hs ht => (B_pos hz hs ht).le) (fun s t _ _ => B_symm z s t) hx hy hb
  let d := fun s : ℝ => E s z/((x+s)*(y+s))
  let b := fun s : ℝ => (1/(x+s)+1/(y+s)) *
    (∫ t in Ioi (0 : ℝ), B z s t/(x+y+s+t))
  have he : (fun s => d s+b s) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => (1/(x+s)+1/(y+s))*rP (x+y+s) z s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, moving_nodes_ne x y z] with s hs hn
    change 0 < s at hs
    rw [(rP_marginal hs (add_pos (add_pos hx hy) hs) hz hn).2]
    dsimp [d,b]
    have hxs : x+s ≠ 0 := (add_pos hx hs).ne'
    have hys : y+s ≠ 0 := (add_pos hy hs).ne'
    have hc : x+y+s+s ≠ 0 := by positivity
    field_simp [hxs,hys,hc]
    <;> ring
  refine ⟨(hd.add h.1).congr he, ?_⟩
  rw [← integral_congr_ae he, integral_add hd h.1, ← h.2]
  exact hp.symm

/-- Source formula (15), with absolute integrability and all positive parameter coincidences. -/
theorem swap_representation {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s => (1/(x+s)+1/(y+s))*rho (x+y+s) z s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (1/(x+s)+1/(y+s))*rho (x+y+s) z s) = -hs x y z := by
  have hq := Q_swap hx hy hz
  have hp := P_swap hx hy hz
  have he : (fun s => (2*((1/(x+s)+1/(y+s))*rQ (x+y+s) z s) -
      (1/(x+s)+1/(y+s))*rP (x+y+s) z s)/6) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => (1/(x+s)+1/(y+s))*rho (x+y+s) z s) := by
    filter_upwards [moving_nodes_ne x y z] with s hn
    simp only [rho, if_neg hn]
    ring
  refine ⟨((hq.1.const_mul 2).sub hp.1 |>.div_const 6).congr he, ?_⟩
  rw [← integral_congr_ae he, integral_div,
    integral_sub (hq.1.const_mul 2) hp.1, integral_const_mul, hq.2, hp.2]
  unfold hs
  ring

/-- Source formula (16) without a sign hypothesis on the Stieltjes density. -/
theorem hs1_sub_swap_integral {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s => (x+y+2*s)/((x+s)^2*(y+s)^2)*rho (x+y+s) z s) (Ioi 0) ∧
      hs1 x y z - hs1 y x z = (y-x) *
        ∫ s in Ioi (0 : ℝ), (x+y+2*s)/((x+s)^2*(y+s)^2)*rho (x+y+s) z s := by
  have hd : Measurable (fun s => rho (x+y+s) z s) := by
    unfold rho
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
    · unfold rQ rP
      fun_prop
  have hi := (swap_representation hx hy hz).1
  apply hs1_sub_of_fixed_density hx hy hz hd hi
  filter_upwards [eventually_gt_nhds (show -x < (0 : ℝ) by linarith),
    eventually_lt_nhds hy] with h hlo hhi
  have ha : 0 < x+h := by linarith
  have hb : 0 < y-h := by linarith
  have hrep := (swap_representation ha hb hz).2
  have hc : x+h+(y-h) = x+y := by ring
  simpa only [hc] using hrep

end D5.S3.Quantum.Petz.SwapRepresentation
