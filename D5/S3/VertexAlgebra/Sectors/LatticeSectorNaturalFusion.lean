/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorNaturalFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorNaturalFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural actual Hom-to-intertwiner fusion for finite neutral-sector sums. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFiniteSumLaws

/-!
The forward representing map is actual postcomposition with J. The inverse
uses the proven normalized ground classification on matching components and
the proven zero theorem on every other component. Naturality is with respect
to all linear maps commuting with all neutral modes. Coherent associativity,
braiding, full charged lattice modules and CFT are not asserted here.
Classical Heisenberg/lattice attribution: Bakalov--Kac and Matsuo--Nagatomo;
imported residue and Sugawara suppliers retain Carnahan and Kytölä credits.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators
noncomputable section
namespace FiniteSectorObject
variable (D : LatticeData)

/-- Each matrix block of an actual module map is itself an actual sector map. -/
def block {M N : FiniteSectorObject D} (g : Hom D M N) (j : Fin N.size) (i : Fin M.size) :
    SectorHom D (M.charge i) (N.charge j) :=
  ⟨(LinearMap.proj j).comp (g.val.comp (LinearMap.single ℂ _ i)), by
    intro a n v
    have ins : (LinearMap.single ℂ (fun k => Sector D (M.charge k)) i)
        (action D (M.charge i) a n v) =
        mode D M a n ((LinearMap.single ℂ _ i) v) := by
      funext k
      by_cases h : k = i
      · subst k; simp [mode]
      · simp [mode, LinearMap.single_apply, Pi.single_apply, h]
    have h := congrFun (g.property a n ((LinearMap.single ℂ _ i) v)) j
    rw [← ins] at h
    exact h⟩

private theorem blocks_apply {M N : FiniteSectorObject D} (g : Hom D M N)
    (x : M.States D) (j : Fin N.size) :
    (g.val x) j = ∑ i, (block D g j i).val (x i) := by
  have e : x = ∑ i, (LinearMap.single ℂ (fun k => Sector D (M.charge k)) i) (x i) :=
    (LinearMap.sum_single_apply (fun k => Sector D (M.charge k)) x).symm
  conv_lhs => rw [e]
  simp [block, map_sum, Finset.sum_apply]

/-- Actual postcomposition on the full finite-sum IO space. -/
def intertwinerPost (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N) :
    Intertwiners D α β M →ₗ[ℂ] Intertwiners D α β N where
  toFun I j := ∑ i, post D H hHG hGH α β (M.charge i) (N.charge j) (block D g j i) (I i)
  map_add' I K := by funext j; simp [Finset.sum_add_distrib]
  map_smul' c I := by funext j; simp [Finset.smul_sum]

/-- The matrix-block definition agrees with postcomposition on every coefficient. -/
theorem intertwinerPost_coefficients (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (I : Intertwiners D α β M) (u : Sector D α) (v : Sector D β) (n : ℤ) :
    coefficients D α β N (intertwinerPost D H hHG hGH α β g I) u n v =
      g.val (coefficients D α β M I u n v) := by
  funext j
  rw [blocks_apply]
  simp [coefficients, intertwinerPost, post, postCoefficients, Finset.sum_apply]

/-- Ordinary module postcomposition on the Hom side. -/
def incomingPost (δ : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N) :
    Incoming D δ M →ₗ[ℂ] Incoming D δ N where
  toFun f := ⟨g.val.comp f.val, by intro a n v; simp only [LinearMap.comp_apply,
    f.property a n v, g.property a n (f.val v)]⟩
  map_add' f k := by apply Subtype.ext; ext v; simp
  map_smul' c f := by apply Subtype.ext; ext v; simp

private theorem coefficients_injective (α β : Charge D) (M : FiniteSectorObject D) :
    Function.Injective (coefficients D α β M) := by
  intro I K h
  funext i
  apply Subtype.ext; apply LinearMap.ext; intro u; funext n
  apply LinearMap.ext; intro v
  exact congrArg (fun F => (F u n v) i) h

/-- Naturality for every actual neutral-module morphism in the explicit category. -/
theorem universal_natural (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (f : Incoming D (α + β) M) :
    universal D H hHG hGH α β N (incomingPost D (α + β) g f) =
      intertwinerPost D H hHG hGH α β g (universal D H hHG hGH α β M f) := by
  apply coefficients_injective D α β N
  apply LinearMap.ext; intro u; funext n
  apply LinearMap.ext; intro v
  rw [universal_coefficients, intertwinerPost_coefficients, universal_coefficients]
  rfl

/-- The explicitly constructed inverse is natural as well. -/
theorem universal_inverse_natural (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (I : Intertwiners D α β M) :
    (universal D H hHG hGH α β N).symm (intertwinerPost D H hHG hGH α β g I) =
      incomingPost D (α + β) g ((universal D H hHG hGH α β M).symm I) := by
  apply (universal D H hHG hGH α β N).injective
  rw [LinearEquiv.apply_symm_apply, universal_natural, LinearEquiv.apply_symm_apply]

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
