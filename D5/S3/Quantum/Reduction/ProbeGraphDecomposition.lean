/- GID: D5/S3/Quantum/Reduction/ProbeGraphDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/ProbeGraphDecomposition
   mirror-E: none(waiver:finite-dimensional-argument)
   anchors: []
   utility: none
   digest: An arbitrary family of unit probes in finite dimension has finitely many orthogonal nonorthogonality components. -/

import D5.S3.Quantum.Reduction.ProbeComponentRigidity

/-!
# Arbitrary probe families in finite dimension

Taking the quotient of the nonorthogonality relation does not restrict the
index family. Representatives from distinct classes are orthonormal, so the
number of classes is finite. Their actual spans are orthogonal and jointly
span exactly the original probe span.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace D5.S3.Quantum.Reduction.ProbeGraphDecomposition
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Reduction.ProbeComponentRigidity
variable {d J : Type*} [Fintype d] [DecidableEq d]

/-- Connected components of the original arbitrary index family. -/
def Component (v : J → d → ℂ) :=
  Quotient (Relation.EqvGen.setoid (fun i j => star (v i) ⬝ᵥ v j ≠ 0))

/-- Class of an original probe index. -/
def component (v : J → d → ℂ) (j : J) : Component v := Quotient.mk _ j

/-- The actual component span in the finite Hilbert space. -/
def hilbertComponent (v : J → d → ℂ) (c : Component v) :
    Submodule ℂ (EuclideanSpace ℂ d) :=
  Submodule.span ℂ {x | ∃ j, component v j = c ∧ WithLp.toLp 2 (v j) = x}

private theorem representatives_orthonormal (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1) :
    Orthonormal ℂ (fun c : Component v => WithLp.toLp 2 (v c.out)) := by
  classical
  rw [orthonormal_iff_ite]
  intro c e
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  split_ifs with h
  · subst e; exact hv c.out
  · by_contra hn
    have he : c = e := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq e]
      exact Quotient.sound (Relation.EqvGen.rel _ _ hn)
    exact h he

/-- Finite dimensionality proves finiteness of components, even for an
    infinite or otherwise arbitrary probe family. -/
theorem components_finite (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1) : Finite (Component v) :=
  (representatives_orthonormal v hv).linearIndependent.finite

/-- Distinct graph components span orthogonal Hilbert subspaces. -/
theorem components_orthogonal (v : J → d → ℂ) :
    Pairwise (fun c e : Component v =>
      Submodule.IsOrtho (hilbertComponent v c) (hilbertComponent v e)) := by
  intro c e hce
  rw [hilbertComponent, hilbertComponent, Submodule.isOrtho_span]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  by_contra h
  apply hce
  exact hi.symm.trans ((Quotient.sound (Relation.EqvGen.rel _ _ h)).trans hj)

/-- The orthogonal component spans exhaust the space whenever the original
    family spans it; no finite-family replacement is assumed. -/
theorem components_span (v : J → d → ℂ)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    (⨆ c : Component v, hilbertComponent v c) = ⊤ := by
  let E := (WithLp.linearEquiv 2 ℂ (d → ℂ)).symm
  have hs : Submodule.span ℂ (Set.range (fun j => WithLp.toLp 2 (v j))) = ⊤ := by
    have h := congrArg (fun S : Submodule ℂ (d → ℂ) => S.map E.toLinearMap) hspan
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective,
      E, LinearEquiv.coe_toLinearMap, WithLp.coe_symm_linearEquiv] using h
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact (le_iSup (fun c => hilbertComponent v c) (component v j))
    (Submodule.subset_span ⟨j, rfl, rfl⟩)

#print axioms components_finite
#print axioms components_orthogonal
#print axioms components_span
end D5.S3.Quantum.Reduction.ProbeGraphDecomposition
