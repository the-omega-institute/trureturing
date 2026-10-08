/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureSelectors
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureSelectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DiscreteInt

/-!
The concrete bounded-coefficient tensor square for the measure comparison.
For every light profinite test space S and every uniformly finite-range family
of integer coordinates, construct the map P tensor Z[S] -> P by selecting
finite points in the convergent sequence. This works for empty, finite and
infinite S. The uniform bound is essential; no bound is imposed on the number
of coordinates. New proofs, Apache-2.0, following the construction in
Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

/-- Keep the n-th finite point if its coefficient is k, and collapse it otherwise. -/
def coefficientSelectorFun (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (k : ℤ) : NinfTensor S → ℕ∪{∞}
  | (∞, _) => ∞
  | (OnePoint.some n, s) => if c n s = k then (n : ℕ∪{∞}) else ∞

@[simp] theorem coefficientSelectorFun_infty (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (s : S) :
    coefficientSelectorFun S c k (∞, s) = ∞ := rfl

@[simp] theorem coefficientSelectorFun_nat (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (n : ℕ) (s : S) :
    coefficientSelectorFun S c k ((n : ℕ∪{∞}), s) =
      if c n s = k then (n : ℕ∪{∞}) else ∞ := rfl

theorem coefficientSelectorFun_fiber (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (n : ℕ) :
    coefficientSelectorFun S c k ⁻¹' {(n : ℕ∪{∞})} =
      {x : NinfTensor S | x.1 = (n : ℕ∪{∞}) ∧ c n x.2 = k} := by
  ext ⟨a, s⟩
  cases a using OnePoint.rec
  · simp [coefficientSelectorFun]
  · rename_i m
    simp only [Set.mem_preimage, Set.mem_singleton_iff, coefficientSelectorFun,
      Set.mem_ofPred_eq]
    split_ifs <;> simp_all <;> grind

theorem coefficientSelectorFun_fiber_clopen (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (n : ℕ) :
    IsClopen (coefficientSelectorFun S c k ⁻¹' {(n : ℕ∪{∞})}) := by
  rw [coefficientSelectorFun_fiber]
  have hsingleton : IsClopen {(n : ℕ∪{∞})} := by
    constructor
    · exact isClosed_singleton
    · exact (OnePoint.isOpen_iff_of_notMem (by simp)).2 (isOpen_discrete _)
  exact (hsingleton.preimage continuous_fst).inter
    ((isClopen_discrete ({k} : Set ℤ)).preimage ((c n).continuous.comp continuous_snd))

/-- Continuity at infinity uses only preservation of the finite index: every
output is either the input index or infinity. No convergence of c_n is needed. -/
theorem coefficientSelectorFun_continuous (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    Continuous (coefficientSelectorFun S c k) := by
  rw [continuous_def]
  intro U hU
  by_cases hInf : (∞ : ℕ∪{∞}) ∈ U
  · rw [← isClosed_compl_iff]
    have hfinite : (((↑) : ℕ → ℕ∪{∞}) ⁻¹' U)ᶜ.Finite := by
      have h := (OnePoint.isOpen_iff_of_mem hInf).1 hU
      simpa only [isClosed_discrete, isCompact_iff_finite, true_and] using h
    have heq : (coefficientSelectorFun S c k ⁻¹' U)ᶜ =
        ⋃ n ∈ (((↑) : ℕ → ℕ∪{∞}) ⁻¹' U)ᶜ,
          coefficientSelectorFun S c k ⁻¹' {(n : ℕ∪{∞})} := by
      ext ⟨a, s⟩
      cases a using OnePoint.rec
      · simp [coefficientSelectorFun, hInf]
      · rename_i m
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion,
          Set.mem_singleton_iff, coefficientSelectorFun]
        split_ifs <;> simp_all
    rw [heq]
    exact hfinite.isClosed_biUnion fun n _ =>
      (coefficientSelectorFun_fiber_clopen S c k n).isClosed
  · have heq : coefficientSelectorFun S c k ⁻¹' U =
        ⋃ n ∈ ((↑) : ℕ → ℕ∪{∞}) ⁻¹' U,
          coefficientSelectorFun S c k ⁻¹' {(n : ℕ∪{∞})} := by
      ext ⟨a, s⟩
      cases a using OnePoint.rec
      · simp [coefficientSelectorFun, hInf]
      · rename_i m
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
          coefficientSelectorFun]
        split_ifs <;> simp_all
    rw [heq]
    exact isOpen_biUnion fun n _ => (coefficientSelectorFun_fiber_clopen S c k n).isOpen

/-- The actual continuous selector, hence an honest light-profinite morphism. -/
def coefficientSelector (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (k : ℤ) : NinfTensor S ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨coefficientSelectorFun S c k,
    coefficientSelectorFun_continuous S c k⟩

end LightCondensed.Solid
