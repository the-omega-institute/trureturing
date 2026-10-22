/- GID: D5/S3/VertexAlgebra/LatticeSectorMultiplicityFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSectorMultiplicityFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual categorical sector representation with arbitrary finite-dimensional multiplicities. -/

import D5.S3.VertexAlgebra.LatticeSectorFullFusion

/-!
Finite-dimensional multiplicities are arbitrary complex vector spaces. The
coordinate equivalence intertwines the actual tensor multiplicity actions.
A single sector is an object of the explicit category, and its actual
categorical Hom space represents the entire lawful mixed-field space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators TensorProduct
noncomputable section
namespace FiniteSectorObject
variable (D : LatticeData)

/-- The actual neutral action on arbitrary tensor multiplicity spaces. -/
def multiplicityMode (s : ℕ) (δ : Fin s → Charge D)
    (V : Fin s → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (a : Sector D 0) (n : ℤ) :
    Module.End ℂ ((i : Fin s) → Sector D (δ i) ⊗[ℂ] V i) :=
  LinearMap.pi fun i => (TensorProduct.map (action D (δ i) a n) (LinearMap.id)).comp (LinearMap.proj i)

/-- Basis coordinates preserve every actual neutral mode, not just vector spaces. -/
theorem multiplicityCoordinates_mode (s : ℕ) (δ : Fin s → Charge D)
    (V : Fin s → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, Module.Finite ℂ (V i)] (a : Sector D 0) (n : ℤ)
    (x : (i : Fin s) → Sector D (δ i) ⊗[ℂ] V i) :
    multiplicityCoordinates D s δ V (multiplicityMode D s δ V a n x) =
      mode D (withMultiplicities D s δ V) a n (multiplicityCoordinates D s δ V x) := by
  let e (i : Fin s) : Sector D (δ i) ⊗[ℂ] V i ≃ₗ[ℂ]
      (Fin (Module.finrank ℂ (V i)) → Sector D (δ i)) :=
    (TensorProduct.congr (LinearEquiv.refl ℂ _) (Module.finBasis ℂ (V i)).equivFun).trans
      (TensorProduct.piScalarRight ℂ ℂ _ _)
  have nat (i : Fin s) (y : Sector D (δ i) ⊗[ℂ] V i) :
      e i (TensorProduct.map (action D (δ i) a n) LinearMap.id y) =
        fun k => action D (δ i) a n (e i y k) := by
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    | add y z hy hz =>
      simp only [map_add, hy, hz]
      funext k
      simp
  funext j
  let t := (Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (V i)))).symm j
  exact congrFun (nat t.1 (x t.1)) t.2

/-- One actual labelled oscillator sector as an object of the explicit category. -/
abbrev sectorObject (δ : Charge D) : FiniteSectorObject D := ⟨1, fun _ => δ⟩

private def sectorInto (δ : Charge D) : Sector D δ →ₗ[ℂ] (sectorObject D δ).States D where
  toFun x _ := x
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Categorical Hom from the sector object is the full actual module-Hom space. -/
def sectorHomEquiv (δ : Charge D) (M : FiniteSectorObject D) :
    Hom D (sectorObject D δ) M ≃ₗ[ℂ] Incoming D δ M where
  toFun f := ⟨f.val.comp (sectorInto D δ), by
    intro a n x
    exact f.property a n (sectorInto D δ x)⟩
  invFun f := ⟨f.val.comp (LinearMap.proj 0), by
    intro a n x
    exact f.property a n (x 0)⟩
  left_inv f := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    change f.val (fun _ => x 0) = f.val x
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i; rfl
  right_inv f := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

/-- The genuine category-level representing fusion equivalence, with explicit inverses. -/
def categoryUniversal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) :
    Hom D (sectorObject D (α + β)) M ≃ₗ[ℂ] FullIO D α β M :=
  (sectorHomEquiv D (α + β) M).trans (fullUniversal D H hHG hGH α β M)

/-- Naturality is actual category composition against full IO postcomposition. -/
theorem categoryUniversal_natural (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (f : Hom D (sectorObject D (α + β)) M) :
    categoryUniversal D H hHG hGH α β N (compose D g f) =
      fullPost D H hHG hGH α β g (categoryUniversal D H hHG hGH α β M f) := by
  exact fullUniversal_natural D H hHG hGH α β g (sectorHomEquiv D (α + β) M f)

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
