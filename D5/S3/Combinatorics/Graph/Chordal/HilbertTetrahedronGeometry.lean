/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertTetrahedronGeometry
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert centers, contact slack and adjusted pair distances. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.FiniteHilbertJung
import Mathlib.Tactic.FinCases

compile_only_with_mathlib

/-! Omega original.

 Finite Hilbert center weights, contact slack, and scalar adjusted distances.
No completeness or finite-dimensionality is imposed on the ambient space. -/

open scoped BigOperators InnerProductSpace

namespace HilbertTetrahedronGeometry

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- A variance-maximizing center, with complementary nonnegative contact slack. -/
structure CandidateData (p : ι → E) where
  c : E
  q : ℝ
  w : ι → ℝ
  slack : ι → ℝ
  q_nonneg : 0 ≤ q
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  center_eq : FiniteHilbertJung.center p w = c
  slack_eq : ∀ i, ‖p i-c‖^2 + slack i = q
  slack_nonneg : ∀ i, 0 ≤ slack i
  complementary : ∀ i, w i * slack i = 0

/-- Candidate weights exist for every nonempty finite family. -/
theorem exists_candidate_data [Nonempty ι] (p : ι → E) : Nonempty (CandidateData p) := by
  obtain ⟨w, hw, hsum, hball, hcontact⟩ := FiniteHilbertJung.exists_variance_center p
  refine ⟨{
    c := FiniteHilbertJung.center p w
    q := FiniteHilbertJung.variance p w
    w := w
    slack := fun i => FiniteHilbertJung.variance p w - ‖p i-FiniteHilbertJung.center p w‖^2
    q_nonneg := (sq_nonneg _).trans (hball (Classical.arbitrary ι))
    w_nonneg := hw
    w_sum := hsum
    center_eq := rfl
    slack_eq := fun i => by ring
    slack_nonneg := fun i => sub_nonneg.mpr (hball i)
    complementary := ?_ }⟩
  intro i
  by_cases h : w i = 0
  · simp [h]
  · rw [hcontact i (lt_of_le_of_ne (hw i) (Ne.symm h)), sub_self, mul_zero]

namespace CandidateData

variable {p : ι → E} (t : CandidateData p)

lemma centered_sum : ∑ i, t.w i • (p i-t.c) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, t.w_sum, one_smul]
  change FiniteHilbertJung.center p t.w-t.c = 0
  rw [t.center_eq, sub_self]

lemma norm_sq_le (i : ι) : ‖p i-t.c‖^2 ≤ t.q := by
  linarith [t.slack_eq i, t.slack_nonneg i]

lemma slack_le (i : ι) : t.slack i ≤ t.q := by
  linarith [t.slack_eq i, sq_nonneg ‖p i-t.c‖]

lemma contact_of_pos {i : ι} (h : 0 < t.w i) : ‖p i-t.c‖^2 = t.q := by
  have hz := (mul_eq_zero.mp (t.complementary i)).resolve_left h.ne'
  linarith [t.slack_eq i]

lemma weight_zero_of_slack_pos {i : ι} (h : 0 < t.slack i) : t.w i = 0 :=
  (mul_eq_zero.mp (t.complementary i)).resolve_right h.ne'

lemma variance_eq : FiniteHilbertJung.variance p t.w = t.q := by
  have hsum : ∑ i, t.w i * ‖p i-t.c‖^2 = t.q := by
    calc
      _ = ∑ i, t.w i*t.q := Finset.sum_congr rfl (fun i _ => by
        have h := t.slack_eq i
        have hzero := t.complementary i
        nlinarith only [congrArg (fun x => t.w i*x) h, hzero])
      _ = _ := by rw [← Finset.sum_mul, t.w_sum, one_mul]
  rw [FiniteHilbertJung.weighted_sq p t.w t.w_sum t.c, t.center_eq] at hsum
  simpa using hsum

/-- The original row has exactly the deficit of its own contact slack. -/
theorem weighted_row (i : ι) :
    ∑ j, t.w j * ‖p i-p j‖^2 = 2*t.q-t.slack i := by
  have h := FiniteHilbertJung.weighted_sq p t.w t.w_sum (p i)
  simp_rw [norm_sub_rev (p i)]
  rw [h, t.variance_eq, t.center_eq, norm_sub_rev]
  linarith [t.slack_eq i]

/-- Scalar distances of the lifted spherical configuration. -/
def adjusted [DecidableEq ι] (i j : ι) : ℝ :=
  if i=j then 0 else ‖p i-p j‖^2+t.slack i+t.slack j

@[simp] lemma adjusted_self [DecidableEq ι] (i : ι) : t.adjusted i i = 0 := by
  simp [adjusted]

lemma adjusted_symm [DecidableEq ι] (i j : ι) : t.adjusted i j = t.adjusted j i := by
  by_cases h : i=j
  · subst j; rfl
  · simp only [adjusted, h, Ne.symm h, ite_false, norm_sub_rev (p j)]
    ring

lemma adjusted_nonneg [DecidableEq ι] (i j : ι) : 0 ≤ t.adjusted i j := by
  unfold adjusted
  split_ifs
  · exact le_rfl
  · exact add_nonneg (add_nonneg (sq_nonneg _) (t.slack_nonneg i)) (t.slack_nonneg j)

/-- Complementarity makes the adjusted rows exactly constant, even at an
interior candidate. This is the scalar replacement for a Hilbert direct sum. -/
theorem adjusted_weighted_row [DecidableEq ι] (i : ι) :
    ∑ j, t.w j*t.adjusted i j = 2*t.q := by
  have hpoint (j : ι) : t.w j*t.adjusted i j =
      t.w j*(‖p i-p j‖^2+t.slack i+t.slack j) := by
    by_cases hij : i=j
    · subst j
      simp only [adjusted_self, mul_zero, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_add]
      nlinarith [t.complementary i]
    · simp [adjusted, hij]
  simp_rw [hpoint, mul_add, Finset.sum_add_distrib]
  rw [t.weighted_row, ← Finset.sum_mul, t.w_sum, one_mul]
  have hz : ∑ j, t.w j*t.slack j = 0 := by simp [t.complementary]
  rw [hz]
  ring

/-- The weighted pair budget, retaining the sum of squared center weights. -/
theorem pair_budget {B : ℝ} (_hB : 0 ≤ B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) :
    2*t.q ≤ (1-∑ i, t.w i^2)*B := by
  classical
  have hsum : ∑ i, ∑ j, t.w i*t.w j*‖p i-p j‖^2 ≤
      (1-∑ i, t.w i^2)*B := by
    calc
      _ ≤ ∑ i, ∑ j, (t.w i*t.w j-if i=j then t.w i^2 else 0)*B := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases hij : i=j
        · subst j; simp [pow_two]
        · simp only [hij, ite_false, sub_zero]
          exact mul_le_mul_of_nonneg_left (hdiam i j)
            (mul_nonneg (t.w_nonneg i) (t.w_nonneg j))
      _ = _ := by
        simp [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, t.w_sum, mul_assoc]
  rw [FiniteHilbertJung.pair_sq p t.w t.w_sum, t.variance_eq] at hsum
  exact hsum

/-- A support of cardinality `k` gives the exact finite Jung squared bound. -/
theorem support_bound {B : ℝ} (hB : 0 ≤ B)
    (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B)
    (K : Finset ι) (hzero : ∀ i, i ∉ K → t.w i = 0) :
    2*(K.card : ℝ)*t.q ≤ ((K.card : ℝ)-1)*B := by
  classical
  have hsum : ∑ i ∈ K, t.w i = 1 := by
    rw [← t.w_sum]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)
  have hsq : ∑ i ∈ K, t.w i^2 = ∑ i, t.w i^2 := by
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hzero i hi]; ring)
  have hcs := sq_sum_le_card_mul_sum_sq (s := K) (f := t.w)
  rw [hsum, hsq, one_pow] at hcs
  have hpair := t.pair_budget hB hdiam
  have hmul := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg K.card : (0:ℝ) ≤ K.card)
  have hBmul := mul_le_mul_of_nonneg_left hcs hB
  nlinarith

/-- Above the three-point Jung threshold every candidate has positive weight,
and therefore every candidate is a contact point. -/
theorem four_weights_pos {p : Fin 4 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/3 < t.q)
    (i : Fin 4) : 0 < t.w i := by
  classical
  by_contra hn
  have hw : t.w i = 0 := by linarith [t.w_nonneg i]
  have h := t.support_bound hB hdiam (Finset.univ.erase i) (by
    intro j hj
    have : j=i := by simpa using hj
    simpa [this] using hw)
  have hc : (Finset.univ.erase i).card = 3 := by simp
  rw [hc] at h
  norm_num at h
  linarith

theorem four_contacts {p : Fin 4 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/3 < t.q)
    (i : Fin 4) : ‖p i-t.c‖^2 = t.q :=
  t.contact_of_pos (t.four_weights_pos hB hdiam hq i)

/-- The four-point Jung bound, in squared and denominator-free form. -/
theorem four_radius_bound {p : Fin 4 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) : 8*t.q ≤ 3*B := by
  have hh := t.support_bound hB hdiam Finset.univ (by simp)
  norm_num at hh
  exact hh

/-- Above the two-point threshold, each of three candidates is a contact. -/
theorem three_contacts {p : Fin 3 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/4 < t.q)
    (i : Fin 3) : ‖p i-t.c‖^2 = t.q := by
  classical
  apply t.contact_of_pos
  by_contra hn
  have hw : t.w i=0 := by linarith [t.w_nonneg i]
  have hh := t.support_bound hB hdiam (Finset.univ.erase i) (by
    intro j hj
    have : j=i := by simpa using hj
    simpa [this] using hw)
  have hc : (Finset.univ.erase i).card=2 := by simp
  rw [hc] at hh
  norm_num at hh
  linarith

/-- Above the two-point Jung threshold at most one candidate is interior. -/
theorem slack_unique {p : Fin 4 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/4 < t.q)
    {i j : Fin 4} (hi : 0 < t.slack i) (hj : 0 < t.slack j) : i=j := by
  classical
  by_contra hij
  have h := t.support_bound hB hdiam ((Finset.univ.erase i).erase j) (by
    intro k hk
    have : k=j ∨ k=i := by
      by_cases hkj : k=j
      · exact Or.inl hkj
      · exact Or.inr (by simpa [hkj] using hk)
    rcases this with rfl | rfl
    · exact t.weight_zero_of_slack_pos hj
    · exact t.weight_zero_of_slack_pos hi)
  have hc : ((Finset.univ.erase i).erase j).card = 2 := by simp [Ne.symm hij]
  rw [hc] at h
  norm_num at h
  linarith

end CandidateData
end
end HilbertTetrahedronGeometry
