/- GID: D5/S3/Combinatorics/Graph/LegalWords/ActivityInnovations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/ActivityInnovations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive path activities have orthogonal innovations with explicit variances. -/

import D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open InhomogeneousMarkovCompletion ActivityMeanCorrespondence

noncomputable section

/-- The centered next bit after subtracting its linear prediction from the current bit. -/
def edgeResidual (u v : ℝ) (a b : Bool) : ℝ :=
  ((if b then 1 else 0) - v) + v / (1 - u) * ((if a then 1 else 0) - u)

/-- The first centered bit followed by the successive prediction residuals. -/
def innovation {N : ℕ} (u : ℕ → ℝ) (b : Fin (N + 1) → Bool) : Fin (N + 1) → ℝ :=
  Fin.cases ((if b 0 then 1 else 0) - u 0)
    (fun i => edgeResidual (u i.val) (u (i.val + 1)) (b i.castSucc) (b i.succ))

private theorem cylinder_expect (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (m : ℕ) (hm : m ≤ n) (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ v, cylinder n P m hm v * F v) =
      ∑ b, P b * F (initialSegment m hm b) := by
  unfold cylinder
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [mul_ite]

private theorem extension_expect (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (K : ℕ → Bool → Bool → ℝ)
    (hrec : ∀ (m : ℕ) (hm : m < n) (v : Fin (m + 1) → Bool) (b : Bool),
      cylinder n P (m + 1) (by omega) (Fin.snoc v b) =
        cylinder n P m (by omega) v * K m (v (Fin.last m)) b)
    (m : ℕ) (hm : m < n) (F : (Fin (m + 1) → Bool) → ℝ)
    (G : Bool → Bool → ℝ) :
    (∑ b, P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) =
    ∑ v, cylinder n P m (by omega) v * F v *
      ∑ a : Bool, K m (v (Fin.last m)) a * G (v (Fin.last m)) a := by
  let H : (Fin (m + 2) → Bool) → ℝ := fun v =>
    F (Fin.init v) * G (v (Fin.last m).castSucc) (v (Fin.last (m + 1)))
  have hh := cylinder_expect n P (m + 1) (by omega) H
  have he : (∑ b, P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) =
      ∑ v, cylinder n P (m + 1) (by omega) v * H v := by
    rw [hh]
    apply Finset.sum_congr rfl
    intro b _
    change P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩) =
      P b * (F (initialSegment m (by omega) b) *
        G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩))
    ring
  rw [he, ← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 2) => Bool),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  change (∑ a : Bool, cylinder n P (m + 1) (by omega) (Fin.snoc v a) * H (Fin.snoc v a)) = _
  simp only [hrec m hm, H, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem kernel_occupied (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P)
    (K : ℕ → Bool → Bool → ℝ)
    (hrec : ∀ (m : ℕ) (hm : m < n) (v : Fin (m + 1) → Bool) (b : Bool),
      cylinder n P (m + 1) (by omega) (Fin.snoc v b) =
        cylinder n P m (by omega) v * K m (v (Fin.last m)) b)
    (m : ℕ) (hm : m < n) :
    K m true true = 0 ∧ K m false true = u (m + 1) / (1 - u m) := by
  let I : Fin (n + 1) := ⟨m, by omega⟩
  let J : Fin (n + 1) := ⟨m + 1, by omega⟩
  have hfirst : (∑ v, cylinder n P m (by omega) v *
      if v (Fin.last m) then 1 else 0) = u m := by
    rw [cylinder_expect]
    exact hmean I
  have hvac : (∑ v, cylinder n P m (by omega) v *
      if v (Fin.last m) then 0 else 1) = 1 - u m := by
    rw [cylinder_expect]
    have htotal : (∑ b, P b * if b I then 1 else 0) +
        (∑ b, P b * if b I then 0 else 1) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hP.2.1 using 1
      apply Finset.sum_congr rfl
      intro b _
      cases b I <;> simp
    change (∑ b, P b * if b I then 0 else 1) = _
    rw [hmean I] at htotal
    linarith
  have hzero : (∑ b, P b * (if b I then 1 else 0) * (if b J then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    by_cases hi : b I = true
    · by_cases hj : b J = true
      · have hb : ¬ Adm (n + 1) b := by
          intro ha
          have ha' := (adm_iff_no_adjacent_true _ b).mp ha I J (by rfl)
          simp [hi, hj] at ha'
        simp [hP.2.2 b hb]
      · simp [hj]
    · simp [hi]
  have h11 := extension_expect n P K hrec m hm (fun _ => 1)
    (fun a b => (if a then 1 else 0) * (if b then 1 else 0))
  simp only [mul_one, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, mul_zero, mul_one, add_zero] at h11
  have h11r : (∑ v, cylinder n P m (by omega) v *
      (K m (v (Fin.last m)) true * if v (Fin.last m) then 1 else 0)) =
      u m * K m true true := by
    rw [← hfirst, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    cases v (Fin.last m) <;> simp
  rw [h11r] at h11
  have hz : K m true true = 0 := by
    have he : u m * K m true true = 0 := h11.symm.trans (by simpa only [mul_assoc] using hzero)
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hu.1 m (by omega)).1)
  refine ⟨hz, ?_⟩
  have hnext := extension_expect n P K hrec m hm (fun _ => 1)
    (fun _ b => if b then 1 else 0)
  simp only [mul_one, Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false, mul_zero,
    add_zero] at hnext
  have hr : (∑ v, cylinder n P m (by omega) v * K m (v (Fin.last m)) true) =
      (1 - u m) * K m false true := by
    rw [← hvac, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    cases v (Fin.last m) <;> simp [hz]
  rw [hr] at hnext
  have hmnext := hmean J
  change (∑ b, P b * if b J then 1 else 0) = _ at hnext
  rw [hmnext] at hnext
  exact (eq_div_iff (ne_of_gt (sub_pos.mpr (hu.1 m (by omega)).2))).2 (by linarith)

private theorem residual_row_zero (u v : ℝ) (hu : u < 1)
    (K : Bool → Bool → ℝ) (hrows : ∀ a, (∑ b : Bool, K a b) = 1)
    (h11 : K true true = 0) (h01 : K false true = v / (1 - u)) (a : Bool) :
    (∑ b : Bool, K a b * edgeResidual u v a b) = 0 := by
  have hden : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  have ht := hrows true
  have hf := hrows false
  simp only [Fintype.sum_bool] at ht hf
  have h00 : K false false = 1 - v / (1 - u) := by rw [h01] at hf; linarith
  have h10 : K true false = 1 := by rw [h11] at ht; linarith
  cases a <;> simp [Fintype.sum_bool, edgeResidual, h11, h01, h00, h10]
  all_goals field_simp [hden] <;> ring

private theorem past_residual_zero (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P)
    (m : ℕ) (hm : m < n) (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ b, P b * F (initialSegment m (by omega) b) *
      edgeResidual (u m) (u (m + 1)) (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) = 0 := by
  obtain ⟨K, _, hrows, hrec⟩ := hM
  rw [extension_expect n P K hrec m hm F]
  apply Finset.sum_eq_zero
  intro v _
  have hk := kernel_occupied u n hu P hP hmean K hrec m hm
  rw [residual_row_zero (u m) (u (m + 1)) (hu.1 m (by omega)).2
    (K m) (hrows m hm) hk.1 hk.2]
  exact mul_zero _


private theorem centered_variance (u : ℕ → ℝ) (n : ℕ)
    (P : (Fin (n + 1) → Bool) → ℝ) (hP : LegalLaw n P) (hmean : Means u n P)
    (i : Fin (n + 1)) :
    (∑ b, P b * ((if b i then 1 else 0) - u i.val) ^ 2) =
      u i.val * (1 - u i.val) := by
  calc
    _ = (1 - 2 * u i.val) * (∑ b, P b * if b i then 1 else 0) +
        u i.val ^ 2 * ∑ b, P b := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      cases b i <;> norm_num <;> ring
    _ = _ := by rw [hmean i, hP.2.1]; ring

private theorem edge_variance (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P)
    (m : ℕ) (hm : m < n) :
    (∑ b, P b * edgeResidual (u m) (u (m + 1))
      (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩) ^ 2) =
      u (m + 1) * seam u m / (1 - u m) := by
  let I : Fin (n + 1) := ⟨m, by omega⟩
  let J : Fin (n + 1) := ⟨m + 1, by omega⟩
  let a : ℝ := u (m + 1) / (1 - u m)
  have hz := past_residual_zero u n hu P hP hmean hM m hm
    (fun v => (if v (Fin.last m) then 1 else 0) - u m)
  have hvI := centered_variance u n P hP hmean I
  have hvJ := centered_variance u n P hP hmean J
  have he : (∑ b, P b * edgeResidual (u m) (u (m + 1)) (b I) (b J) ^ 2) =
      (∑ b, P b * ((if b J then 1 else 0) - u (m + 1)) ^ 2) -
      a ^ 2 * (∑ b, P b * ((if b I then 1 else 0) - u m) ^ 2) +
      2 * a * (∑ b, P b * ((if b I then 1 else 0) - u m) *
        edgeResidual (u m) (u (m + 1)) (b I) (b J)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [edgeResidual, a]
    ring
  change (∑ b, P b * ((if b I then 1 else 0) - u m) *
    edgeResidual (u m) (u (m + 1)) (b I) (b J)) = 0 at hz
  change (∑ b, P b * ((if b I then 1 else 0) - u m) ^ 2) = _ at hvI
  change (∑ b, P b * ((if b J then 1 else 0) - u (m + 1)) ^ 2) = _ at hvJ
  change (∑ b, P b * edgeResidual (u m) (u (m + 1)) (b I) (b J) ^ 2) = _
  rw [he, hvI, hvJ, hz]
  dsimp [I, J, a, seam]
  field_simp [ne_of_gt (sub_pos.mpr (hu.1 m (by omega)).2)]
  ring

private theorem innovation_prefix (u : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n)
    (b : Fin (n + 1) → Bool) (i : Fin (m + 1)) :
    innovation u (initialSegment m hm b) i =
      innovation u b ⟨i.val, by omega⟩ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

private theorem innovations_orthogonal (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P) :
    ∀ i j : Fin (n + 1), i ≠ j →
      (∑ b, P b * innovation u b i * innovation u b j) = 0 := by
  have ordered (i j : Fin (n + 1)) (hij : i < j) :
      (∑ b, P b * innovation u b i * innovation u b j) = 0 := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij))
    have hi : i.val < j.val + 1 := by exact hij
    let I : Fin (j.val + 1) := ⟨i.val, hi⟩
    have h := past_residual_zero u n hu P hP hmean hM j.val j.isLt
      (fun v => innovation u v I)
    simp only [innovation_prefix] at h
    exact h
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · convert ordered j i h using 1
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- Positive activities give orthogonal successive residuals and their exact squared norms. -/
theorem orthogonal_innovations (n : ℕ) (w : Fin (n + 2) → ℝ) (hw : ∀ i, 0 < w i) :
    (∀ i j : Fin (n + 2), i ≠ j →
      (∑ b, law w b * innovation (meansOf w) b i * innovation (meansOf w) b j) = 0) ∧
    (∑ b, law w b * innovation (meansOf w) b 0 ^ 2) =
      meansOf w 0 * (1 - meansOf w 0) ∧
    (∀ i : Fin (n + 1),
      (∑ b, law w b * innovation (meansOf w) b i.succ ^ 2) =
        meansOf w (i.val + 1) * seam (meansOf w) i.val / (1 - meansOf w i.val)) := by
  have h := positive_activity_means n w hw
  have hc := activity_mean_correspondence (meansOf w) n h.1
  have he : law w = completion (meansOf w) n := by
    exact (congrArg law ((hc.2.2.2.2 w hw).mp h.2)).trans hc.2.1
  have hm := unique_markov_completion (meansOf w) n h.1
  have hl : LegalLaw (n + 1) (law w) := by simpa only [he] using hm.1
  have hM : Markov (n + 1) (law w) := by simpa only [he] using hm.2.2.1
  refine ⟨innovations_orthogonal (meansOf w) (n + 1) h.1 (law w) hl h.2 hM, ?_, ?_⟩
  · exact centered_variance (meansOf w) (n + 1) (law w) hl h.2 0
  · intro i
    exact edge_variance (meansOf w) (n + 1) h.1 (law w) hl h.2 hM i.val i.isLt

#print axioms orthogonal_innovations

end
end D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations
