/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charge-homogeneous restrictions of actual lattice fields and mixed sector operators. -/

import D5.S3.VertexAlgebra.LatticeActualStateDerivative

/-
Classical neutral Heisenberg sectors inside the ordinary untwisted lattice
vertex algebra. The fields and creation series are those of Bakalov--Kac,
math/0402315v1, section 4.1. Nested normal products and residue identities
retain the Matsuo--Nagatomo and Scott Carnahan attributions of their suppliers.

proof_shape: charge_homogeneity: content
admission_basis: escape-witness
escape_witness: The charge support invariant survives both nested normal
branches for every oscillator word, then the full polynomial linear extension.
It is consumed by the actual mixed-carrier restriction laws.
utility is none: these are unrestricted algebraic statements, not finite
certified instances, bounded enumerations, checkers or numerical reductions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- A separately charge-labelled oscillator carrier. -/
@[reducible] def Sector (D : LatticeData) (_δ : Charge D) := Oscillator D

instance (D : LatticeData) (δ : Charge D) : CommRing (Sector D δ) :=
  inferInstanceAs (CommRing (Oscillator D))
instance (D : LatticeData) (δ : Charge D) : Algebra ℂ (Sector D δ) :=
  inferInstanceAs (Algebra ℂ (Oscillator D))

def inclusion (D : LatticeData) (δ : Charge D) : Sector D δ →ₗ[ℂ] Carrier D :=
  Finsupp.lsingle δ

def projection (D : LatticeData) (δ : Charge D) : Carrier D →ₗ[ℂ] Sector D δ :=
  Finsupp.lapply δ

private def chargeSpace (D : LatticeData) (δ : Charge D) : Submodule ℂ (Carrier D) :=
  LinearMap.range (Finsupp.lsingle δ)

private theorem chargeSpace_single (D : LatticeData) (δ : Charge D) (v : Oscillator D) :
    Finsupp.single δ v ∈ chargeSpace D δ := ⟨v, rfl⟩

private theorem word_charge (D : LatticeData) (α β : Charge D)
    (w : List (Index D)) (n : ℤ) (v : Oscillator D) :
    ((wordField D α w)[[n]]) (Finsupp.single β v) ∈ chargeSpace D (α + β) := by
  classical
  have neutral (x : Index D) (m : ℤ) (δ : Charge D) (p : Oscillator D) :
      ((dividedDerivative x.2 (neutralField D x.1))[[m]]) (Finsupp.single δ p)
        ∈ chargeSpace D δ := by
    change Ring.choose (-m - 1 + x.2) x.2 •
      HVertexOperator.coeff (neutralField D x.1) (-m - 1 + x.2)
        (Finsupp.single δ p) ∈ _
    rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff, neutralMode_single]
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact (chargeSpace D δ).smul_mem _ (chargeSpace_single D δ _)
  induction w generalizing n β v with
  | nil =>
    rw [wordField, actualField, VertexOperator.ncoeff_of_coeff,
      (actual_creation_coefficient_transport D α α).2.2.1]
    exact (chargeSpace D (α + β)).smul_mem _ (chargeSpace_single D (α + β) _)
  | cons x tail ih =>
    rw [wordField, (normalMinusOne _ _).2]
    apply (chargeSpace D (α + β)).add_mem
    · apply finsum_induction _ (chargeSpace D (α + β)).zero_mem
        (fun _ _ => (chargeSpace D (α + β)).add_mem)
      intro j
      obtain ⟨p, hp⟩ := ih (β := β) (n := n + j) (v := v)
      rw [← hp]
      exact neutral x _ _ _
    · apply finsum_induction _ (chargeSpace D (α + β)).zero_mem
        (fun _ _ => (chargeSpace D (α + β)).add_mem)
      intro j
      obtain ⟨p, hp⟩ := neutral x j β v
      rw [← hp]
      exact ih (β := β) (n := _) (v := p)

/-- Every coefficient of the original all-state field has the sum charge.
There is no nonsingularity or nonzero-charge hypothesis. -/
theorem charge_homogeneity (D : LatticeData) (α β : Charge D)
    (u v : Oscillator D) (n : ℤ) :
    ((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v) =
      Finsupp.single (α + β)
        ((((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v)) (α + β)) := by
  classical
  have h : ((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v)
      ∈ chargeSpace D (α + β) := by
    rw [Y_single, polynomialField, Module.Basis.constr_apply]
    simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      LinearMap.sum_apply, LinearMap.smul_apply]
    apply Submodule.sum_mem
    intro e he
    exact (chargeSpace D (α + β)).smul_mem _ (word_charge D α β _ n v)
  obtain ⟨p, hp⟩ := h
  change Finsupp.single (α + β) p = _ at hp
  rw [← hp, Finsupp.single_eq_same]

/-- The actual heterogeneous coefficient: the target is labelled by α+β. -/
def canonical (D : LatticeData) (α β : Charge D) :
    Sector D α →ₗ[ℂ] (ℤ → (Sector D β →ₗ[ℂ] Sector D (α + β))) where
  toFun u n := (projection D (α + β)).comp
    ((((Y D (inclusion D α u))[[n]])).comp (inclusion D β))
  map_add' u v := by ext n w; simp [inclusion, projection]
  map_smul' c u := by ext n w; simp [inclusion, projection]

/-- Restriction loses no coefficient information. -/
theorem inclusion_canonical (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) (n : ℤ) :
    inclusion D (α + β) (canonical D α β u n v) =
      ((Y D (inclusion D α u))[[n]]) (inclusion D β v) :=
  (charge_homogeneity D α β u v n).symm

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
