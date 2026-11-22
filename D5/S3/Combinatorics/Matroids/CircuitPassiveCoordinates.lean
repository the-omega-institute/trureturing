/- GID: D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitPassiveCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Weighted vector insertion preserves the subset of zero-weight indices. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

/-! Splitting the weighted insertion equations by their passive indices. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates

open Finset
open UniformCircuitResidueForms
open Set.powersetCard (ofFinEmbEquiv)
open AlternatingMap
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

set_option autoImplicit false

variable {I M N : Type*} [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
variable {d : ℕ}

/-- Keep exactly the form coefficients whose intersection with A is S. -/
noncomputable def project (b : Module.Basis I ℤ M) (A S : Finset I) :
    (M [⋀^Fin d]→ₗ[ℤ] N) →ₗ[ℤ] (M [⋀^Fin d]→ₗ[ℤ] N) :=
  let basis := basisFormEquiv (n := d) (N := N) b
  let mask : (Set.powersetCard I d → N) →ₗ[ℤ] (Set.powersetCard I d → N) :=
    { toFun f F := if F.val ∩ A = S then f F else 0
      map_add' f g := by funext F; by_cases h : F.val ∩ A = S <;> simp [h]
      map_smul' t f := by funext F; by_cases h : F.val ∩ A = S <;> simp [h] }
  basis.toLinearMap.comp (mask.comp basis.symm.toLinearMap)

private lemma project_coordinate (b : Module.Basis I ℤ M) (A S F : Finset I)
    (f : M [⋀^Fin d]→ₗ[ℤ] N) :
    formCoordinates b (project b A S f) F =
      if F ∩ A = S then formCoordinates b f F else 0 := by
  by_cases hd : F.card = d
  · simp [formCoordinates, hd, project]
  · simp [formCoordinates, hd]

/-- When the weights vanish on A, inserting the weighted vector commutes
with projecting to each fixed intersection with A. -/
theorem insertion_project [Fintype I] (b : Module.Basis I ℤ M) (A S : Finset I)
    (weight : I → ℕ) (hweight : ∀ i ∈ A, weight i = 0)
    (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :
    (project b A S f).curryLeft (∑ i, weight i • b i) =
      project b A S (f.curryLeft (∑ i, weight i • b i)) := by
  apply (basisFormEquiv b).symm.injective
  funext T
  let e := ofFinEmbEquiv.symm T
  have he : (ofFinEmbEquiv e).val = T.val := congrArg Subtype.val (ofFinEmbEquiv.apply_symm_apply T)
  have ht (g : M [⋀^Fin d]→ₗ[ℤ] N) :
      (basisFormEquiv b).symm g T = formCoordinates b g T.val := by
    rw [formCoordinates, dite_eq_left (show T.val.card = d from T.prop)]
  rw [ht, ht, project_coordinate, ← ht]
  rw [← ht, basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
  rw [curryLeft_weighted_basis b _ weight e, curryLeft_weighted_basis b f weight e, he]
  have hface (i : I) (hi : i ∉ A) : insert i T.val ∩ A = T.val ∩ A := by
    ext j
    by_cases hj : j ∈ A
    · have hne : j ≠ i := fun he => hi (he ▸ hj)
      simp [hj, hne]
    · simp [hj]
  by_cases hs : T.val ∩ A = S
  · rw [ite_eq_left hs]
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp [hweight i hi]
    · rw [project_coordinate, hface i hi, ite_eq_left hs]
  · rw [ite_eq_right hs]
    apply sum_eq_zero
    intro i _
    by_cases hi : i ∈ A
    · simp [hweight i hi]
    · rw [project_coordinate, hface i hi, ite_eq_right hs, nsmul_zero, smul_zero]

end D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates
