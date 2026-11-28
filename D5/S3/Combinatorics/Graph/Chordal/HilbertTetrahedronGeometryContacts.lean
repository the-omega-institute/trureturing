/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertTetrahedronGeometryContacts
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Total, edge and face contact estimates for four Hilbert candidates. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.HilbertTetrahedronGeometry

compile_only_with_mathlib

/-! Omega original.

 Sharp total, edge, and face estimates above the three-contact threshold. -/

open scoped BigOperators

namespace HilbertTetrahedronGeometry

noncomputable section

def edgeEnergy (D : Fin 4 → Fin 4 → ℝ) : ℝ := (∑ i, ∑ j, D i j)/2

def faceEnergy (D : Fin 4 → Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  (∑ i ∈ Finset.univ.erase k, ∑ j ∈ Finset.univ.erase k, D i j)/2

/-- Scalar spherical data.  The geometry enters only through constant weighted
rows, nonnegative weights, and the diameter bound. -/
structure FourContactRows (D : Fin 4 → Fin 4 → ℝ) (w : Fin 4 → ℝ) (q B : ℝ) : Prop where
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  diag : ∀ i, D i i = 0
  symm : ∀ i j, D i j = D j i
  nonneg : ∀ i j, 0 ≤ D i j
  diam : ∀ i j, D i j ≤ B
  row : ∀ i, ∑ j, w j*D i j = 2*q

namespace FourContactRows

variable {D : Fin 4 → Fin 4 → ℝ} {w : Fin 4 → ℝ} {q B : ℝ}
variable (h : FourContactRows D w q B)
include h

lemma weight_bound (i : Fin 4) : B*w i ≤ B-2*q := by
  have hr : ∑ j, w j*D i j ≤ ∑ j, w j*(B-if j=i then B else 0) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (h.w_nonneg j)
    by_cases hj : j=i
    · subst j; simp [h.diag]
    · simp [hj, h.diam i j]
  rw [h.row] at hr
  simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.w_sum, mul_ite] at hr
  linarith

lemma pair_weight_bound (i j : Fin 4) (hij : i≠j) :
    4*q-B ≤ B*(w i+w j) := by
  classical
  let K := (Finset.univ.erase i).erase j
  have hc : K.card = 2 := by simp [K, Ne.symm hij]
  have hs : ∑ k ∈ K, w k = 1-w i-w j := by
    dsimp [K]
    rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hij]), Finset.sum_erase_eq_sub (by simp), h.w_sum]
  have hb : ∑ k ∈ K, B*w k ≤ ∑ _k ∈ K, (B-2*q) :=
    Finset.sum_le_sum (fun k _ => h.weight_bound k)
  rw [← Finset.mul_sum, hs] at hb
  simp only [Finset.sum_const, hc, nsmul_eq_mul] at hb
  norm_num at hb
  nlinarith only [hb]

def deficit (_h : FourContactRows D w q B) (i j : Fin 4) : ℝ := if i=j then 0 else B-D i j

lemma deficit_nonneg (i j : Fin 4) : 0 ≤ h.deficit i j := by
  unfold deficit
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (h.diam i j)

lemma deficit_symm (i j : Fin 4) : h.deficit i j = h.deficit j i := by
  by_cases hij : i=j
  · subst j; rfl
  · simp [deficit, hij, Ne.symm hij, h.symm i j]

lemma deficit_eq (i j : Fin 4) : h.deficit i j = B-D i j-(if i=j then B else 0) := by
  by_cases hij : i=j
  · subst j; simp [deficit, h.diag]
  · simp [deficit, hij]

lemma deficit_row (i : Fin 4) :
    ∑ j, w j*h.deficit i j = B*(1-w i)-2*q := by
  simp_rw [h.deficit_eq, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, h.w_sum, one_mul, h.row]
  simp [mul_ite, Finset.sum_ite_eq]
  ring

lemma deficit_sum : ∑ i, ∑ j, h.deficit i j = 12*B-2*edgeEnergy D := by
  simp_rw [h.deficit_eq, Finset.sum_sub_distrib]
  simp [edgeEnergy, Finset.sum_ite_eq]
  ring

lemma weighted_deficit_sum :
    ∑ i, ∑ j, (w i+w j)*h.deficit i j = 2*(3*B-8*q) := by
  have hs : ∑ i, ∑ j, w j*h.deficit i j = 3*B-8*q := by
    simp_rw [h.deficit_row, mul_sub, Finset.sum_sub_distrib]
    simp [← Finset.mul_sum, h.w_sum]
    ring
  have he : ∑ i, ∑ j, w i*h.deficit i j = ∑ i, ∑ j, w j*h.deficit i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [h.deficit_symm]))
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [he, hs]
  ring

/-- Total energy inequality (6), with the positive denominator cleared. -/
theorem total_energy : B*(32*q-9*B) ≤ edgeEnergy D*(4*q-B) := by
  have hm : (4*q-B)*(∑ i, ∑ j, h.deficit i j) ≤
      B*(∑ i, ∑ j, (w i+w j)*h.deficit i j) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i=j
    · subst j; simp [deficit]
    · have hh := mul_le_mul_of_nonneg_right (h.pair_weight_bound i j hij) (h.deficit_nonneg i j)
      nlinarith only [hh]
  rw [h.deficit_sum, h.weighted_deficit_sum] at hm
  nlinarith only [hm]

lemma deficit_pair_le (i j : Fin 4) (hij : i≠j) :
    2*h.deficit i j ≤ ∑ a, ∑ b, h.deficit a b := by
  have hi : h.deficit i j ≤ ∑ b, h.deficit i b :=
    Finset.single_le_sum (fun b _ => h.deficit_nonneg i b) (Finset.mem_univ j)
  have hj : h.deficit j i ≤ ∑ b, h.deficit j b :=
    Finset.single_le_sum (fun b _ => h.deficit_nonneg j b) (Finset.mem_univ i)
  have hsub : (∑ a ∈ ({i,j} : Finset (Fin 4)), ∑ b, h.deficit a b) ≤
      ∑ a, ∑ b, h.deficit a b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => Finset.sum_nonneg (fun b _ => h.deficit_nonneg a b))
  rw [Finset.sum_pair hij] at hsub
  rw [h.deficit_symm j i] at hj
  linarith

/-- Individual edge inequality (7), including a denominator-free interface. -/
theorem individual_edge (hq : B/3 < q) (hB : 0 < B) (i j : Fin 4) (hij : i≠j) :
    4*B*(3*q-B) ≤ D i j*(4*q-B) := by
  have hp : 0 ≤ 4*q-B := by linarith
  have hpair := mul_le_mul_of_nonneg_left (h.deficit_pair_le i j hij) hp
  rw [h.deficit_sum] at hpair
  have ht := h.total_energy
  simp only [deficit, hij, ite_false] at hpair
  nlinarith only [hpair, ht]

end FourContactRows

lemma face_energy_identity (D : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, D i i=0) (hs : ∀ i j, D i j=D j i) (k : Fin 4) :
    faceEnergy D k = edgeEnergy D-∑ i, D k i := by
  unfold faceEnergy edgeEnergy
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
  rw [Finset.sum_sub_distrib]
  simp_rw [← hs k]
  rw [hd]
  ring

namespace FourContactRows

variable {D : Fin 4 → Fin 4 → ℝ} {w : Fin 4 → ℝ} {q B : ℝ}
variable (h : FourContactRows D w q B)
include h

/-- Face inequality (9), again with its denominator cleared. -/
theorem high_face (hq : B/3 < q) (hB : 0 < B) (k : Fin 4) :
    5*B*(4*q-B)-B^2 ≤ faceEnergy D k*(4*q-B) := by
  have hrow : ∑ i, D k i ≤ 3*B := by
    calc
      _ = ∑ i ∈ Finset.univ.erase k, D k i := by simp [Finset.sum_erase_eq_sub, h.diag]
      _ ≤ ∑ _i ∈ Finset.univ.erase k, B := Finset.sum_le_sum (fun i _ => h.diam k i)
      _ = _ := by simp
  have he := face_energy_identity D h.diag h.symm k
  have hm := mul_le_mul_of_nonneg_right hrow (by linarith : 0 ≤ 4*q-B)
  have ht := h.total_energy
  rw [he]
  nlinarith only [hm, ht]

end FourContactRows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every high-radius candidate family supplies spherical row data directly. -/
theorem CandidateData.contact_rows {p : Fin 4 → E} (t : CandidateData p) {B : ℝ}
    (hB : 0 ≤ B) (hdiam : ∀ i j, ‖p i-p j‖^2 ≤ B) (hq : B/3 < t.q) :
    FourContactRows (fun i j => ‖p i-p j‖^2) t.w t.q B := by
  refine ⟨t.w_nonneg, t.w_sum, by simp, ?_, fun i j => sq_nonneg _, hdiam, ?_⟩
  · intro i j; rw [norm_sub_rev]
  · intro i
    have hs : t.slack i=0 := by linarith [t.slack_eq i, t.four_contacts hB hdiam hq i]
    rw [t.weighted_row, hs, sub_zero]

end
end HilbertTetrahedronGeometry
