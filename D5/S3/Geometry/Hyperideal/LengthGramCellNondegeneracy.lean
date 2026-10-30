/- GID: D5/S3/Geometry/Hyperideal/LengthGramCellNondegeneracy
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramCellNondegeneracy
   mirror-E: none(waiver:cfmp-cell-nondegeneracy)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: The twenty original coefficient cells are nondegenerate affine simplices. -/

import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import D5.S3.Geometry.Hyperideal.SupportAffineIndependent
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.SupportAffineIndependent
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramCellNondegeneracy

abbrev V := Fin 4 → ℝ

private lemma endpoint_support_zero_iff (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    support l f (endpoint l i j) = 0 ↔ incident f i j := by
  obtain ⟨_, hi, hj, hz, hr, ho⟩ := (cut_body_polytope l hl).2.2.2 i j hij
  constructor
  · intro h
    cases f with
    | inl k =>
        by_cases hki : k = i
        · subst k
          have : endpoint l i j i ≠ 0 := ne_of_gt hi
          simpa [support] using (this (by simpa [support] using h))
        · by_cases hkj : k = j
          · subst k
            have : endpoint l i j j ≠ 0 := ne_of_gt hj
            simpa [support] using (this (by simpa [support] using h))
          · exact ⟨hki, hkj⟩
    | inr k =>
        by_cases hki : k = i
        · simpa [incident] using hki
        · exfalso
          exact (ne_of_lt (ho k hki) (by simpa [support] using h))
  · intro h
    cases f with
    | inl k =>
        rcases h with ⟨hki, hkj⟩
        simpa [support] using congrArg Neg.neg (hz k hki hkj)
    | inr k =>
        have hki : k = i := h
        subst k
        simpa [support] using hr

private lemma barycenter_support_ne (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) : support l f barycenter ≠ 0 := by
  cases f with
  | inl k => norm_num [support, barycenter]
  | inr k =>
      have h := (shared_radial_body l hl).2.2.1 k
      exact ne_of_lt (by simpa [support, barycenter] using h)

private lemma endpoint_ne (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i j k m : Fin 4} (hij : i ≠ j) (hkm : k ≠ m)
    (hpq : (i, j) ≠ (k, m)) : endpoint l i j ≠ endpoint l k m := by
  intro h
  apply hpq
  have hinj := (cut_body_polytope l hl).2.2.1
  have hsub : (⟨(i, j), hij⟩ : EndpointLabel) = ⟨(k, m), hkm⟩ := by
    apply hinj
    simpa using h
  exact congrArg Subtype.val hsub

private lemma endpoint_eq_false (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i j k m : Fin 4} (h : endpoint l i j = endpoint l k m)
    (hij : i ≠ j) (hkm : k ≠ m) (hpq : (i, j) ≠ (k, m)) : False := by
  exact endpoint_ne l hl hij hkm hpq h

/-- Every one of the twenty original four-point cells is an affine simplex.

The proof uses the literal facet and ridge support table from
`LengthGramSideTrace`: the first support isolates the barycenter, the second
isolates the first endpoint, and the last two endpoints are distinct by the
ordered endpoint classification. -/
theorem vertices_affine_independent (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (n : Fin 20) : AffineIndependent ℝ (vertices l n) := by
  have hfacet (j : Fin 3) :
      support l (facet n) (vertices l n j.succ) = 0 := by
    fin_cases n <;> fin_cases j <;>
      simp [vertices, facet] <;>
      first
      | exact (endpoint_support_zero_iff l hl _ _ _ (by decide)).2 (by decide)
  have hridge_zero (j : Fin 2) :
      support l (ridge n) (vertices l n (j.succ.succ)) = 0 := by
    fin_cases n <;> fin_cases j <;>
      simp [vertices, ridge] <;>
      first
      | exact (endpoint_support_zero_iff l hl _ _ _ (by decide)).2 (by decide)
  have hridge_ne :
      support l (ridge n) (vertices l n 1) ≠ 0 := by
    fin_cases n <;>
      simp [vertices, ridge] <;>
      first
      | intro h
        have hz := (endpoint_support_zero_iff l hl _ _ _ (by decide)).mp h
        simpa [incident] using hz
  have hlast : vertices l n 2 ≠ vertices l n 3 := by
    fin_cases n <;> intro h <;>
      apply endpoint_eq_false l hl (by simpa [vertices] using h) (by decide) (by decide) (by decide)
  apply support_affine_independent (vertices l n)
    (support l (facet n)) (support l (ridge n))
  · have hzero : vertices l n 0 = barycenter := by
      fin_cases n <;> rfl
    simpa only [hzero] using (barycenter_support_ne l hl (facet n))
  · exact hfacet
  · exact hridge_ne
  · exact hridge_zero 0
  · exact hridge_zero 1
  · exact hlast

#print axioms vertices_affine_independent

end D5.S3.Geometry.Hyperideal.LengthGramCellNondegeneracy
