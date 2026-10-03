/- GID: D5/S3/Quantum/Magic/WignerSimplexNearestEdge
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/WignerSimplexNearestEdge
   mirror-E: none(waiver:explicit-universal-convex-construction)
   anchors: []
   utility: none
   digest: Construct a nearest edge-polytope point in four-coordinate L1 geometry. -/
/-
proof_shape: nearest_edge_point: content
escape_witness: face_triangle and positive_minimum_mixture give explicit convex coefficients;
  nearest_edge_point transfers the negative minimum to a maximum coordinate with exact L1 error.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import Mathlib
set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Magic.WignerSimplexNearestEdge
def edgeVertex (i j : Fin 4) (k : Fin 4) : ℝ := if k = i ∨ k = j then 1/2 else 0
def freeEdges : Set (Fin 4 → ℝ) := {w | ∃ i j : Fin 4, i ≠ j ∧ w = edgeVertex i j}
private theorem face_triangle (f : Fin 4 → ℝ) (j : Fin 4) (hsum : ∑ i, f i = 1) (hz : f j = 0) (hcap : ∀ i, f i ≤ 1/2) : f ∈ convexHull ℝ freeEdges := by
  let v : Fin 3 → Fin 4 → ℝ :=
    ![edgeVertex (j.succAbove 1) (j.succAbove 2),edgeVertex (j.succAbove 2) (j.succAbove 0),
      edgeVertex (j.succAbove 0) (j.succAbove 1)]
  let w : Fin 3 → ℝ :=
    ![1-2*f (j.succAbove 0),1-2*f (j.succAbove 1),1-2*f (j.succAbove 2)]
  apply mem_convexHull_of_exists_fintype (w := w) (z := v)
  · intro i; fin_cases i <;> dsimp [w] <;>
      linarith [hcap (j.succAbove 0),hcap (j.succAbove 1),hcap (j.succAbove 2)]
  · fin_cases j <;>
      norm_num [w,Fin.succAbove,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.lt_def,Fin.sum_univ_three,Fin.sum_univ_four,Fin.succ, Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
        at hz hsum ⊢ <;>
      try simp only [show (⟨2,by decide⟩ : Fin 4) = 2 from rfl, show (⟨3,by decide⟩ : Fin 4) = 3 from rfl] at *
    all_goals linarith
  · intro i; fin_cases i <;> dsimp [v]
    all_goals refine ⟨_,_,?_,rfl⟩; fin_cases j <;> decide
  · ext k
    fin_cases j <;> fin_cases k <;>
      norm_num [w,v,Fin.succAbove,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.lt_def,edgeVertex,Fin.sum_univ_three,Fin.sum_univ_four, Pi.smul_apply,smul_eq_mul,Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.head_cons,Matrix.tail_cons] at hz hsum ⊢ <;>
      try simp only [show (⟨2,by decide⟩ : Fin 4) = 2 from rfl, show (⟨3,by decide⟩ : Fin 4) = 3 from rfl] at *
    all_goals linarith
private theorem positive_minimum_mixture (f : Fin 4 → ℝ) (j : Fin 4) (hsum : ∑ i, f i = 1) (hj : 0 ≤ f j) (hcap : ∀ i, f i + f j ≤ 1/2) : f ∈ convexHull ℝ freeEdges := by
  let v : Fin 5 → Fin 4 → ℝ :=
    ![edgeVertex (j.succAbove 1) (j.succAbove 2),edgeVertex (j.succAbove 2) (j.succAbove 0),
      edgeVertex (j.succAbove 0) (j.succAbove 1),edgeVertex j (j.succAbove 0),
      edgeVertex (j.succAbove 1) (j.succAbove 2)]
  let w : Fin 5 → ℝ :=
    ![1-2*(f (j.succAbove 0)+f j),1-2*(f (j.succAbove 1)+f j),
      1-2*(f (j.succAbove 2)+f j),2*f j,2*f j]
  apply mem_convexHull_of_exists_fintype (w := w) (z := v)
  · intro i; fin_cases i <;> dsimp [w] <;>
      linarith [hcap (j.succAbove 0),hcap (j.succAbove 1),hcap (j.succAbove 2)]
  · fin_cases j <;>
      norm_num [w,Fin.succAbove,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.lt_def,Fin.sum_univ_succ,Fin.sum_univ_four,Fin.succ, Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four, Matrix.head_cons,Matrix.tail_cons] at hsum ⊢ <;>
      try simp only [show (⟨2,by decide⟩ : Fin 4) = 2 from rfl, show (⟨3,by decide⟩ : Fin 4) = 3 from rfl] at *
    all_goals linarith
  · intro i; fin_cases i <;> dsimp [v]
    all_goals refine ⟨_,_,?_,rfl⟩; fin_cases j <;> decide
  · ext k
    fin_cases j <;> fin_cases k <;>
      norm_num [w,v,Fin.succAbove,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Fin.lt_def,edgeVertex,Fin.sum_univ_succ,Fin.sum_univ_four,Fin.succ, Pi.smul_apply,smul_eq_mul,Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hsum ⊢ <;>
      try simp only [show (⟨2,by decide⟩ : Fin 4) = 2 from rfl, show (⟨3,by decide⟩ : Fin 4) = 3 from rfl] at *
    all_goals linarith
theorem nearest_edge_point (w : Fin 4 → ℝ) (j k : Fin 4) (hsum : ∑ i, w i = 1) (hmin : ∀ i, w j ≤ w i) (hmax : ∀ i, w i ≤ w k) (hpair : ∀ i l : Fin 4, i ≠ l → 0 ≤ w i + w l ∧ w i + w l ≤ 1) (hone : ∀ i l : Fin 4, w i < 0 → w l < 0 → i = l) (hcap : ∀ i, w i + w j ≤ 1/2) : ∃ f ∈ convexHull ℝ freeEdges, ‖WithLp.toLp 1 (w-f)‖ = ‖WithLp.toLp 1 w‖ - 1 := by
  classical
  by_cases hj : 0 ≤ w j
  · have hn (i : Fin 4) : 0 ≤ w i := hj.trans (hmin i)
    refine ⟨w,positive_minimum_mixture w j hsum hj hcap,?_⟩; have hnorm : ‖WithLp.toLp 1 w‖ = 1 := by simpa only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply,abs_of_nonneg (hn _)] using hsum
    rw [hnorm]; simp [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply]
  · have hjneg : w j < 0 := lt_of_not_ge hj
    have hjk : j ≠ k := by
      intro heq; subst k; have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmax i); simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hsum] at hs; norm_num at hs; linarith
    have hn (i : Fin 4) (hij : i ≠ j) : 0 ≤ w i := by
      by_contra! hi
      exact hij (hone i j hi hjneg)
    let f (i : Fin 4) := w i + (if i = j then -w j else 0) +
      (if i = k then w j else 0)
    have hfj : f j = 0 := by simp [f,hjk]
    have hfk : f k = w k+w j := by simp [f,Ne.symm hjk]
    have hfi (i : Fin 4) (hij : i ≠ j) (hik : i ≠ k) : f i = w i := by simp [f,hij,hik]
    have hsumf : ∑ i, f i = 1 := by
      simp [f,Finset.sum_add_distrib,hsum]
    have hcapf (i : Fin 4) : f i ≤ 1/2 := by
      by_cases hij : i = j
      · subst i; rw [hfj]; norm_num
      by_cases hik : i = k
      · subst i; rw [hfk]; exact hcap k
      rw [hfi i hij hik]; have hp := (hpair i k hik).2; linarith [hmax i]
    have hfree := face_triangle f j hsumf hfj hcapf; refine ⟨f,hfree,?_⟩; have herr (i : Fin 4) : |w i-f i| = (if i = j then -w j else 0) + (if i = k then -w j else 0) := by
      by_cases hij : i = j
      · subst i
        simp only [hfj,sub_zero,if_pos rfl,if_neg hjk,add_zero]
        exact abs_of_neg hjneg
      by_cases hik : i = k
      · subst i
        rw [hfk]; simp [Ne.symm hjk,abs_of_neg hjneg]
      rw [hfi i hij hik]; simp [hij,hik]
    have habs (i : Fin 4) : |w i| = w i + (if i = j then -2*w j else 0) := by
      by_cases hij : i = j
      · subst i; rw [abs_of_neg hjneg]; simp; ring
      · simp [hij,abs_of_nonneg (hn i hij)]
    simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply,Pi.sub_apply]; simp_rw [herr,habs]; simp [Finset.sum_add_distrib,hsum]; ring
#print axioms nearest_edge_point
end D5.S3.Quantum.Magic.WignerSimplexNearestEdge
