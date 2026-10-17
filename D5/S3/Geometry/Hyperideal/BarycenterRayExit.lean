/- GID: D5/S3/Geometry/Hyperideal/BarycenterRayExit
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/BarycenterRayExit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every non-barycentric point of the common cut body reaches an original support trace. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import D5.S3.Geometry.Hyperideal.SupportRatioExit
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.SupportRatioExit
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.BarycenterRayExit

private def row (l : Fin 6 → ℝ) (i : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  ∑ j, lengthGram l i j * x j

private lemma row_line (l : Fin 6 → ℝ) (i : Fin 4)
    (a x : Fin 4 → ℝ) (u : ℝ) :
    row l i (fun j => a j + u * (x j - a j)) =
      row l i a + u * (row l i x - row l i a) := by
  simp only [row, Fin.sum_univ_succ]
  ring

/-- Every point different from the common barycenter has an explicit
support-ratio extension to one of the eight original supporting traces. -/
theorem barycenter_ray_exit (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (x : Fin 4 → ℝ) (hx : x ∈ cutBody l)
    (hxb : x ≠ fun _ : Fin 4 => (1 : ℝ) / 4) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      let y : Fin 4 → ℝ := fun j => 1 / 4 + (x j - 1 / 4) / t
      y ∈ cutBody l ∧
      ((∃ i, y i = 0) ∨ (∃ i, (∑ j, lengthGram l i j * y j) = 0)) ∧
      x = (1 - t) • (fun _ : Fin 4 => (1 : ℝ) / 4) + t • y := by
  classical
  let b : Fin 4 → ℝ := fun _ => 1 / 4
  let L : (Fin 4 ⊕ Fin 4) → (Fin 4 → ℝ) → ℝ :=
    Sum.elim (fun i v => -v i) (row l)
  have hsumx := hx.1.2
  have hsumx' : x 0 + x 1 + x 2 + x 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsumx
  have hsmall : ∃ i, x i < (1 : ℝ) / 4 := by
    by_contra hn
    push_neg at hn
    have hx0 := hn 0
    have hx1 := hn 1
    have hx2 := hn 2
    have hx3 := hn 3
    apply hxb
    funext i
    fin_cases i <;> dsimp <;> linarith [hsumx']
  have hline (r : Fin 4 ⊕ Fin 4) (u : ℝ) :
      L r (fun j => b j + u * (x j - b j)) =
        L r b + u * (L r x - L r b) := by
    cases r with
    | inl i => dsimp [L]; ring
    | inr i => exact row_line l i b x u
  have hb (r : Fin 4 ⊕ Fin 4) : L r b < 0 := by
    cases r with
    | inl i => norm_num [L, b]
    | inr i => exact (shared_radial_body l hl).2.2.1 i
  have hLx (r : Fin 4 ⊕ Fin 4) : L r x ≤ 0 := by
    cases r with
    | inl i => exact neg_nonpos.mpr (hx.1.1 i)
    | inr i => exact hx.2 i
  obtain ⟨i, hi⟩ := hsmall
  have hgrowth : ∃ r ∈ (Finset.univ : Finset (Fin 4 ⊕ Fin 4)), L r b < L r x :=
    ⟨Sum.inl i, Finset.mem_univ _, neg_lt_neg hi⟩
  obtain ⟨r, _, t, ht, ht1, _, _, hLy, hry, hxy⟩ :=
    support_ratio_exit Finset.univ L b x hline (fun r _ => hb r)
      (by intro r hr; exact (hr (Finset.mem_univ r)).elim) hLx hgrowth
  let y : Fin 4 → ℝ := fun j => 1 / 4 + (x j - 1 / 4) / t
  have hysum : ∑ j, y j = 1 := by
    have hconst : (∑ _ : Fin 4, (1 : ℝ) / 4) = 1 := by norm_num
    have hdiff : (∑ j : Fin 4, (x j - (1 : ℝ) / 4)) = 0 := by
      rw [Finset.sum_sub_distrib, hsumx, hconst]
      ring
    have hscaled : (∑ j : Fin 4, (x j - (1 : ℝ) / 4) / t) = 0 := by
      rw [← Finset.sum_div, hdiff]
      simp
    dsimp [y]
    rw [Finset.sum_add_distrib, hconst, hscaled]
    norm_num
  refine ⟨t, ht, ht1, ?_⟩
  change y ∈ cutBody l ∧ _ ∧ _
  refine ⟨⟨⟨?_, hysum⟩, ?_⟩, ?_, hxy⟩
  · intro j
    exact neg_nonpos.mp (hLy (Sum.inl j))
  · intro j
    exact hLy (Sum.inr j)
  · cases r with
    | inl j => exact Or.inl ⟨j, neg_eq_zero.mp hry⟩
    | inr j => exact Or.inr ⟨j, hry⟩

#print axioms barycenter_ray_exit

end D5.S3.Geometry.Hyperideal.BarycenterRayExit
