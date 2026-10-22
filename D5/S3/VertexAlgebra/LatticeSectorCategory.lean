/- GID: D5/S3/VertexAlgebra/LatticeSectorCategory
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSectorCategory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit finite-sum category of actual neutral Heisenberg sectors. -/

import D5.S3.VertexAlgebra.LatticeSectorUniversalComponent
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Free

/-!
Finite coordinate presentations permit arbitrary finite-dimensional complex
multiplicities. Charges may repeat and each object chooses its own finite
list; no global finite charge set is fixed. The neutral action and translation
are the actual restricted operators, component by component. The tensor
products below describe multiplicities only, not the fusion object.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators TensorProduct
noncomputable section

/-- An arbitrary finite charge list, allowing zero multiplicities and repeats. -/
structure FiniteSectorObject (D : LatticeData) where
  size : ℕ
  charge : Fin size → Charge D

namespace FiniteSectorObject
variable (D : LatticeData)

abbrev States (M : FiniteSectorObject D) := (i : Fin M.size) → Sector D (M.charge i)

def mode (M : FiniteSectorObject D) (a : Sector D 0) (n : ℤ) :
    Module.End ℂ (M.States D) := LinearMap.pi fun i =>
      (action D (M.charge i) a n).comp (LinearMap.proj i)

def translation (M : FiniteSectorObject D) : Module.End ℂ (M.States D) :=
  LinearMap.pi fun i => (sectorT D (M.charge i)).comp (LinearMap.proj i)

/-- Full actual-module morphisms, not just maps preserving charge labels. -/
def homSpace (M N : FiniteSectorObject D) : Submodule ℂ (M.States D →ₗ[ℂ] N.States D) where
  carrier := {f | ∀ a n x, f (mode D M a n x) = mode D N a n (f x)}
  zero_mem' := by intro a n x; simp
  add_mem' := by intro f g hf hg a n x; simp [hf a n x, hg a n x]
  smul_mem' := by intro c f hf a n x; simp [hf a n x]

abbrev Hom (M N : FiniteSectorObject D) := homSpace D M N

def identity (M : FiniteSectorObject D) : Hom D M M := ⟨LinearMap.id, by intro a n x; rfl⟩

def compose {M N P : FiniteSectorObject D} (g : Hom D N P) (f : Hom D M N) : Hom D M P :=
  ⟨g.val.comp f.val, by intro a n x; exact (congrArg g.val (f.property a n x)).trans (g.property a n (f.val x))⟩

instance : CategoryTheory.Category (FiniteSectorObject D) where
  Hom := fun M N => ↥(Hom D M N)
  id := identity D
  comp f g := compose D g f
  id_comp f := by apply Subtype.ext; rfl
  comp_id f := by apply Subtype.ext; rfl
  assoc f g h := by apply Subtype.ext; rfl

/-- Actual module maps from one labelled oscillator sector to a finite sum. -/
def incomingSpace (δ : Charge D) (M : FiniteSectorObject D) :
    Submodule ℂ (Sector D δ →ₗ[ℂ] M.States D) where
  carrier := {f | ∀ a n x, f (action D δ a n x) = mode D M a n (f x)}
  zero_mem' := by intro a n x; simp
  add_mem' := by intro f g hf hg a n x; simp [hf a n x, hg a n x]
  smul_mem' := by intro c f hf a n x; simp [hf a n x]

abbrev Incoming (δ : Charge D) (M : FiniteSectorObject D) := incomingSpace D δ M

/-- Coordinates identify actual incoming module maps with sector module maps. -/
def incomingEquiv (δ : Charge D) (M : FiniteSectorObject D) :
    Incoming D δ M ≃ₗ[ℂ] ((i : Fin M.size) → SectorHom D δ (M.charge i)) where
  toFun f i := ⟨(LinearMap.proj i).comp f.val, by
    intro a n x
    exact congrFun (f.property a n x) i⟩
  invFun f := ⟨LinearMap.pi fun i => (f i).val, by
    intro a n x; funext i; exact (f i).property a n x⟩
  left_inv f := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  right_inv f := by funext i; apply Subtype.ext; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/-- IO into a finite sum, expressed by its uniquely determined coordinates. -/
abbrev Intertwiners (α β : Charge D) (M : FiniteSectorObject D) :=
  (i : Fin M.size) → IO D α β (M.charge i)

/-- The representing equivalence; forward evaluation is actual postcomposition. -/
def universal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) :
    Incoming D (α + β) M ≃ₗ[ℂ] Intertwiners D α β M :=
  (incomingEquiv D (α + β) M).trans
    (LinearEquiv.piCongrRight fun i => componentUniversal D H hHG hGH α β (M.charge i))

/-- Coefficients are genuine maps to the full finite-sum carrier. -/
def coefficients (α β : Charge D) (M : FiniteSectorObject D)
    (I : Intertwiners D α β M) :
    Sector D α →ₗ[ℂ] (ℤ → (Sector D β →ₗ[ℂ] M.States D)) where
  toFun u n := LinearMap.pi fun i => (I i).val u n
  map_add' u v := by funext n; apply LinearMap.ext; intro w; funext i; simp
  map_smul' c u := by funext n; apply LinearMap.ext; intro w; funext i; simp

/-- The forward universal map is postcomposition with J on every state and mode. -/
theorem universal_coefficients (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) (f : Incoming D (α + β) M)
    (u : Sector D α) (v : Sector D β) (n : ℤ) :
    coefficients D α β M (universal D H hHG hGH α β M f) u n v =
      f.val (canonical D α β u n v) := rfl

/-- Finite multiplicities are implemented by repeated charge slots. -/
def withMultiplicities (s : ℕ) (δ : Fin s → Charge D)
    (V : Fin s → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, Module.Finite ℂ (V i)] : FiniteSectorObject D where
  size := Fintype.card (Σ i, Fin (Module.finrank ℂ (V i)))
  charge j := δ ((Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (V i)))).symm j).1

/-- Arbitrary finite-dimensional multiplicities have these actual coordinate carriers. -/
def multiplicityCoordinates (s : ℕ) (δ : Fin s → Charge D)
    (V : Fin s → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, Module.Finite ℂ (V i)] :
    ((i : Fin s) → Sector D (δ i) ⊗[ℂ] V i) ≃ₗ[ℂ]
      (withMultiplicities D s δ V).States D :=
  (LinearEquiv.piCongrRight fun i =>
    (TensorProduct.congr (LinearEquiv.refl ℂ (Sector D (δ i))) (Module.finBasis ℂ (V i)).equivFun).trans
      (TensorProduct.piScalarRight ℂ ℂ (Sector D (δ i)) (Fin (Module.finrank ℂ (V i))))) |>.trans
  (LinearEquiv.piCurry ℂ (fun i (_ : Fin (Module.finrank ℂ (V i))) => Oscillator D)).symm |>.trans
  (LinearEquiv.piCongrLeft' ℂ (fun _ => Oscillator D)
    (Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (V i)))))

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
