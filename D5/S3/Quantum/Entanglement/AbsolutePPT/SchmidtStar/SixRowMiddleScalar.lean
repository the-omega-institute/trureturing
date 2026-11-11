/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict
   digest: Source-faithful scalar premises imply the strict six-row middle bound. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleScalar
noncomputable section

open SixRowMiddlePolynomial SixRowMiddleCertificate

/-- Only scalar premises consumed on [1/5,3/10]; physical APPT suppliers are separate. -/
structure Hyp6 (r H D a q : ℝ) : Prop where
  H_nonneg : 0 ≤ H
  D_nonneg : 0 ≤ D
  q_nonneg : 0 ≤ q
  mass : 0 ≤ slack r H D
  q_box : q ≤ D
  q_mass : q ≤ D^2
  tail_cap : q ≤ max 2 (2*D/3)
  head_sq : a ≤ H^2
  head_cap : a ≤ (cn r/den r)*H
  head_box : a ≤ (H-cn r/den r)^2+(cn r/den r)^2
  coupled : a+2*r*H+15*r^2 ≤ (2-q/2)^2
  variance : (5/7)*(a-H^2/15)+(q-D^2/21) ≤ 4*slack r H D-(slack r H D)^2/3

private theorem necessary_nonneg (r H D a q : ℝ) (h : Hyp6 r H D a q)
    (hr : r ≤ 3/10) (hWT : T138 r ≤ W r H D a q) :
    Necessary (10*(r-1/5)) (H/3) (D/3) (q/2) := by
  have ha0 : a0 r H D q ≤ a := by
    dsimp only [a0]
    dsimp only [W] at hWT
    linarith only [hWT]
  have hd : 0 < den r := by dsimp only [den]; linarith only [hr]
  have hcap := mul_le_mul_of_nonneg_left h.head_cap (le_of_lt hd)
  have hcap_id : den r*((cn r/den r)*H) = cn r*H := by
    field_simp [ne_of_gt hd] <;> ring
  rw [hcap_id] at hcap
  have hcap0 := mul_le_mul_of_nonneg_left ha0 (le_of_lt hd)
  have hbox := mul_le_mul_of_nonneg_left h.head_box (sq_nonneg (den r))
  have hbox_id : (den r)^2*((H-cn r/den r)^2+(cn r/den r)^2) =
      (den r*H-cn r)^2+(cn r)^2 := by
    field_simp [ne_of_gt hd] <;> ring
  rw [hbox_id] at hbox
  have hbox0 := mul_le_mul_of_nonneg_left ha0 (sq_nonneg (den r))
  constructor
  · rw [mass_identity]; exact h.mass
  · rw [qbox_identity]; exact sub_nonneg.mpr h.q_box
  · rw [qmass_identity]; exact sub_nonneg.mpr h.q_mass
  · rw [headsq_identity]; linarith only [h.head_sq, ha0]
  · rw [headcap_identity]; linarith only [hcap, hcap0]
  · rw [headbox_identity]; linarith only [hbox, hbox0]
  · rw [coupled_identity]; linarith only [h.coupled, ha0]
  · rw [variance_identity]; nlinarith only [h.variance, ha0]

/-- Strict scalar middle bound; this is a supplier, not the full APPT threshold theorem. -/
theorem middle_strict (r H D a q : ℝ) (h : Hyp6 r H D a q)
    (hrl : 1/5 ≤ r) (hru : r ≤ 3/10) : W r H D a q < T138 r := by
  by_contra hn
  have hWT : T138 r ≤ W r H D a q := le_of_not_gt hn
  have hm := h.mass
  dsimp only [slack] at hm
  have hH : H ≤ 3 := by linarith only [hm, h.D_nonneg, hrl]
  have hD : D ≤ 3 := by linarith only [hm, h.H_nonneg, hrl]
  have hq : q ≤ 2 := h.tail_cap.trans (max_le (le_refl _) (by linarith only [hD]))
  exact closed_box_exclusion (10*(r-1/5)) (H/3) (D/3) (q/2)
    (by linarith only [hrl]) (by linarith only [hru])
    (by linarith only [h.H_nonneg]) (by linarith only [hH])
    (by linarith only [h.D_nonneg]) (by linarith only [hD])
    (by linarith only [h.q_nonneg]) (by linarith only [hq])
    (necessary_nonneg r H D a q h hru hWT)

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleScalar
