/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertTetrahedronGeometryFaces
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Face energy bounds for four Hilbert candidates at low radius. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.HilbertTetrahedronGeometryContacts
import D5.S3.Combinatorics.Graph.Chordal.HilbertGeometry.HilbertTetrahedronGeometryRows

compile_only_with_mathlib

/-! Omega original.

 The low-radius face estimate, including a candidate inside the sphere. -/

open scoped BigOperators

namespace HilbertTetrahedronGeometry

noncomputable section

lemma sum_face (f : Fin 4 → ℝ) (k : Fin 4) :
    ∑ i ∈ Finset.univ.erase k, f i = ∑ i : Fin 3, f (k.succAbove i) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
  have h := Fin.sum_univ_succAbove f k
  linarith

lemma face_energy_triple (D : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, D i i=0) (hs : ∀ i j, D i j=D j i) (k : Fin 4) :
    faceEnergy D k = D (k.succAbove 0) (k.succAbove 1)+
      D (k.succAbove 0) (k.succAbove 2)+D (k.succAbove 1) (k.succAbove 2) := by
  unfold faceEnergy
  rw [sum_face]
  simp_rw [sum_face]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, hd, add_zero, zero_add]
  rw [hs (k.succAbove 1) (k.succAbove 0), hs (k.succAbove 2) (k.succAbove 0),
    hs (k.succAbove 2) (k.succAbove 1)]
  ring

namespace FourContactRows

variable {D : Fin 4 → Fin 4 → ℝ} {w : Fin 4 → ℝ} {q B : ℝ}
variable (h : FourContactRows D w q B)
include h

/-- The face row estimate before eliminating the omitted barycentric weight. -/
theorem face_weighted (k : Fin 4) :
    4*(2*q-w k*B) ≤ (1-w k)*faceEnergy D k := by
  let f : Fin 3 → Fin 4 := k.succAbove
  have hs : w (f 0)+w (f 1)+w (f 2)+w k=1 := by
    have hh := Fin.sum_univ_succAbove w k
    rw [h.w_sum] at hh
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, add_zero] at hh
    dsimp [f]
    linarith
  have hrow (i : Fin 3) : 2*q-w k*B ≤ ∑ j : Fin 3, w (f j)*D (f i) (f j) := by
    have hr := h.row (f i)
    rw [Fin.sum_univ_succAbove _ k] at hr
    have hb := mul_le_mul_of_nonneg_left (h.diam (f i) k) (h.w_nonneg k)
    change w k*D (f i) k + ∑ j : Fin 3, w (f j)*D (f i) (f j) = 2*q at hr
    linarith
  have hr0 := hrow 0
  have hr1 := hrow 1
  have hr2 := hrow 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, h.diag, mul_zero, add_zero, zero_add] at hr0 hr1 hr2
  rw [h.symm (f 1) (f 0)] at hr1
  rw [h.symm (f 2) (f 0), h.symm (f 2) (f 1)] at hr2
  have hface := face_energy_triple D h.diag h.symm k
  change faceEnergy D k=D (f 0) (f 1)+D (f 0) (f 2)+D (f 1) (f 2) at hface
  by_cases hL : 0 ≤ 2*q-w k*B
  · have hw := weighted_rows (h.w_nonneg (f 0)) (h.w_nonneg (f 1)) (h.w_nonneg (f 2))
      (h.nonneg (f 0) (f 1)) (h.nonneg (f 0) (f 2)) (h.nonneg (f 1) (f 2)) hL hr0 hr1 hr2
    rw [← hface] at hw
    have hsum : w (f 0)+w (f 1)+w (f 2)=1-w k := by linarith
    rw [hsum] at hw
    exact hw
  · have hn : 0 ≤ faceEnergy D k := by
      rw [hface]
      exact add_nonneg (add_nonneg (h.nonneg _ _) (h.nonneg _ _)) (h.nonneg _ _)
    have hsum : 0 ≤ 1-w k := by linarith [h.w_nonneg (f 0), h.w_nonneg (f 1), h.w_nonneg (f 2)]
    have hp := mul_nonneg hsum hn
    linarith

/-- Sharp low-radius spherical face inequality (10).  The case `q<B/4`
is included: its lower bound is nonpositive. -/
theorem low_face (hB : 0 < B) (hq : 0 < q) (hhalf : 2*q ≤ B) (k : Fin 4) :
    8*B*q-2*B^2 ≤ q*faceEnergy D k := by
  have hface : 0 ≤ faceEnergy D k := by
    unfold faceEnergy
    exact div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => h.nonneg i j))) (by norm_num)
  by_cases hquarter : B ≤ 4*q
  · have hw := h.face_weighted k
    have hwb := h.weight_bound k
    have hwk : 0 < 1-w k := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hw hq.le
    have hp : 0 ≤ (B-2*q)*(B*(1-w k)-2*q) :=
      mul_nonneg (by linarith) (by nlinarith)
    apply le_of_mul_le_mul_left (a := 1-w k) _ hwk
    nlinarith only [hm, hp]
  · have hp := mul_nonneg hq.le hface
    have hneg : 8*B*q-2*B^2 ≤ 0 := by nlinarith
    exact hneg.trans hp

theorem supporting_face (k : Fin 4) (hk : w k=0) : 8*q ≤ faceEnergy D k := by
  have hh := h.face_weighted k
  simp only [hk, zero_mul, sub_zero, one_mul] at hh
  linarith

end FourContactRows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace CandidateData

variable {p : Fin 4 → E} (t : CandidateData p)

def faceSlack (k : Fin 4) : ℝ := ∑ i ∈ Finset.univ.erase k, t.slack i

lemma face_slack_nonneg (k : Fin 4) : 0 ≤ t.faceSlack k :=
  Finset.sum_nonneg (fun i _ => t.slack_nonneg i)

lemma adjusted_face (k : Fin 4) :
    faceEnergy t.adjusted k = faceEnergy (fun i j => ‖p i-p j‖^2) k+2*t.faceSlack k := by
  rw [face_energy_triple _ t.adjusted_self t.adjusted_symm,
    face_energy_triple _ (by simp) (fun i j => by rw [norm_sub_rev])]
  have h01 : k.succAbove (0 : Fin 3) ≠ k.succAbove 1 := k.succAbove_right_injective.ne (by decide)
  have h02 : k.succAbove (0 : Fin 3) ≠ k.succAbove 2 := k.succAbove_right_injective.ne (by decide)
  have h12 : k.succAbove (1 : Fin 3) ≠ k.succAbove 2 := k.succAbove_right_injective.ne (by decide)
  simp only [adjusted, h01, h02, h12, ite_false]
  unfold faceSlack
  rw [sum_face]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, add_zero]
  ring

lemma face_norm_sum (k : Fin 4) :
    ∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2 = 3*t.q-t.faceSlack k := by
  have h : ∑ i ∈ Finset.univ.erase k, (‖p i-t.c‖^2+t.slack i) = 3*t.q := by
    simp [t.slack_eq]
  rw [Finset.sum_add_distrib] at h
  change (∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2)+t.faceSlack k = 3*t.q at h
  linarith

lemma adjusted_rows {B : ℝ} (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) :
    FourContactRows t.adjusted t.w t.q (B+∑ i, t.slack i) := by
  have hB : 0 ≤ B := by simpa using hdiam 0 0
  refine ⟨t.w_nonneg, t.w_sum, t.adjusted_self, t.adjusted_symm, t.adjusted_nonneg, ?_, t.adjusted_weighted_row⟩
  intro i j
  by_cases hij : i=j
  · subst j
    rw [t.adjusted_self]
    exact add_nonneg hB (Finset.sum_nonneg (fun i _ => t.slack_nonneg i))
  · have hp : t.slack i+t.slack j ≤ ∑ k, t.slack k := by
      have hs : (∑ k ∈ ({i,j} : Finset (Fin 4)), t.slack k) ≤ ∑ k, t.slack k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => t.slack_nonneg k)
      simpa [Finset.sum_pair hij] using hs
    simp only [adjusted, hij, ite_false]
    linarith [hdiam i j]

/-- Interior-safe face estimate (35).  `faceSlack k` is the total squared
radial slack in the selected face; at most one term is nonzero. -/
theorem low_radius_face {B : ℝ} (hB : 0 < B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hlo : B/4 < t.q) (hhi : t.q ≤ B/3)
    (k : Fin 4) :
    8*B*t.q+6*t.faceSlack k*t.q-2*(B+t.faceSlack k)^2 ≤
      t.q*faceEnergy (fun i j => ‖p i-p j‖^2) k := by
  have hq : 0 < t.q := by linarith
  have hrows := t.adjusted_rows hdiam
  have hface := t.adjusted_face k
  by_cases hk : t.slack k=0
  · have htotal : ∑ i, t.slack i=t.faceSlack k := by
      unfold faceSlack
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hk, sub_zero]
    rw [htotal] at hrows
    have hh := hrows.low_face (by linarith [t.face_slack_nonneg k]) hq
      (by linarith [t.face_slack_nonneg k]) k
    rw [hface] at hh
    nlinarith only [hh]
  · have hkpos : 0 < t.slack k := lt_of_le_of_ne (t.slack_nonneg k) (Ne.symm hk)
    have hs (i : Fin 4) (hi : i≠k) : t.slack i=0 := by
      by_contra hn
      have hipos : 0 < t.slack i := lt_of_le_of_ne (t.slack_nonneg i) (Ne.symm hn)
      exact hi (t.slack_unique hB.le hdiam hlo hipos hkpos)
    have hδ : t.faceSlack k=0 := by
      unfold faceSlack
      exact Finset.sum_eq_zero (fun i hi => hs i (Finset.mem_erase.mp hi).1)
    have hh := hrows.supporting_face k (t.weight_zero_of_slack_pos hkpos)
    rw [hface, hδ] at hh
    rw [hδ]
    nlinarith [sq_nonneg (2*t.q-B)]

/-- Above `B/4`, the total interior slack is at most the squared radius. -/
theorem total_slack_le {B : ℝ} (hB : 0 ≤ B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/4 < t.q) :
    (∑ i, t.slack i) ≤ t.q := by
  by_cases he : ∃ i, 0 < t.slack i
  · obtain ⟨i, hi⟩ := he
    have hs : ∑ j, t.slack j=t.slack i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_contra hn
        have hj : 0 < t.slack j := lt_of_le_of_ne (t.slack_nonneg j) (Ne.symm hn)
        exact hji (t.slack_unique hB hdiam hq hj hi)
      · simp
    rw [hs]
    exact t.slack_le i
  · have hz : ∀ i, t.slack i=0 := by
      intro i
      have hn : ¬0 < t.slack i := fun hi => he ⟨i,hi⟩
      linarith [t.slack_nonneg i]
    simp only [hz, Finset.sum_const_zero]
    exact t.q_nonneg

theorem face_slack_le {B : ℝ} (hB : 0 ≤ B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/4 < t.q) (k : Fin 4) :
    t.faceSlack k ≤ t.q := by
  apply le_trans _ (t.total_slack_le hB hdiam hq)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => t.slack_nonneg i)

/-- The scalar reduction (36), with all denominators cleared. -/
theorem low_face_reduction {q B δ T S : ℝ} (hq : 0 < q) (hT : 0 < T)
    (hδ : 0 ≤ δ) (hTdef : T=3*q-δ)
    (hface : 8*B*q+6*δ*q-2*(B+δ)^2 ≤ q*S) :
    8*B*T-6*B^2 ≤ T*S := by
  have hidentity : q*(T*S-(8*B*T-6*B^2)) =
      T*(q*S-(8*B*q+6*δ*q-2*(B+δ)^2))+2*δ*(B-T)^2 := by
    rw [hTdef]
    ring
  have hp : 0 ≤ T*(q*S-(8*B*q+6*δ*q-2*(B+δ)^2)) :=
    mul_nonneg hT.le (by linarith)
  have hrest : 0 ≤ 2*δ*(B-T)^2 := by positivity
  have hprod : 0 ≤ q*(T*S-(8*B*T-6*B^2)) := by rw [hidentity]; positivity
  have hh := nonneg_of_mul_nonneg_right hprod hq
  linarith

/-- The geometry needed by the lower-radius closure algebra, expressed solely
in the actual face radial energy `T`. This is (36), including interior points. -/
theorem low_radius_face_geometry {B : ℝ} (hB : 0 < B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hlo : B/4 < t.q) (hhi : t.q ≤ B/3)
    (k : Fin 4) :
    let T := ∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2
    0 < T ∧ T ≤ B ∧ 8*B*T-6*B^2 ≤ T*faceEnergy (fun i j => ‖p i-p j‖^2) k := by
  dsimp only
  let T := ∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2
  have hTdef : T=3*t.q-t.faceSlack k := t.face_norm_sum k
  have hq : 0 < t.q := by linarith
  have hδlo := t.face_slack_nonneg k
  have hδhi := t.face_slack_le hB.le hdiam hlo k
  have hT : 0 < T := by linarith
  have hTB : T ≤ B := by linarith
  refine ⟨hT, hTB, ?_⟩
  exact low_face_reduction hq hT hδlo hTdef (t.low_radius_face hB hdiam hlo hhi k)

/-- Divided form of (36), for direct use with the antitone face allowance. -/
theorem low_radius_face_geometry_div {B : ℝ} (hB : 0 < B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hlo : B/4 < t.q) (hhi : t.q ≤ B/3)
    (k : Fin 4) :
    let T := ∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2
    8*B-6*B^2/T ≤ faceEnergy (fun i j => ‖p i-p j‖^2) k := by
  have hh := t.low_radius_face_geometry hB hdiam hlo hhi k
  dsimp only at hh ⊢
  apply le_of_mul_le_mul_right _ hh.1
  have he : (8*B-6*B^2/(∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2))*
      (∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2) =
      8*B*(∑ i ∈ Finset.univ.erase k, ‖p i-t.c‖^2)-6*B^2 := by
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hh.1)]
  rw [he]
  nlinarith only [hh.2.2]

theorem three_face_geometry {p : Fin 3 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/4 < t.q) :
    8*t.q ≤ ‖p 0-p 1‖^2+‖p 0-p 2‖^2+‖p 1-p 2‖^2 := by
  have hs (i : Fin 3) : t.slack i=0 := by
    linarith [t.slack_eq i, t.three_contacts hB hdiam hq i]
  have r0 := t.weighted_row 0
  have r1 := t.weighted_row 1
  have r2 := t.weighted_row 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, sub_self, norm_zero, zero_pow (by decide : 2≠0), mul_zero,
    add_zero, zero_add, hs, sub_zero] at r0 r1 r2
  rw [norm_sub_rev (p 1) (p 0)] at r1
  rw [norm_sub_rev (p 2) (p 0), norm_sub_rev (p 2) (p 1)] at r2
  have hh := weighted_rows (t.w_nonneg 0) (t.w_nonneg 1) (t.w_nonneg 2)
    (sq_nonneg ‖p 0-p 1‖) (sq_nonneg ‖p 0-p 2‖) (sq_nonneg ‖p 1-p 2‖)
    (by linarith [t.q_nonneg] : 0 ≤ 2*t.q) r0.ge r1.ge r2.ge
  have hsum := t.w_sum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, add_zero] at hsum
  have hsum' : t.w 0+t.w 1+t.w 2=1 := by linarith
  rw [hsum', one_mul] at hh
  linarith

end CandidateData
end
end HilbertTetrahedronGeometry
