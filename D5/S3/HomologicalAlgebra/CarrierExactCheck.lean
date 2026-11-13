import D5.S3.HomologicalAlgebra.AcyclicCarrier
import Mathlib.Data.ZMod.Basic
noncomputable section
open CategoryTheory Module
open D5.S3.HomologicalAlgebra.AcyclicCarrier
universe u v w
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ}
variable {I : ℕ → Type w} {B : ∀ n, Basis (I n) R (C.X n)}
example
    (A : ∀ n, I n → ∀ m, Submodule R (D.X m))
    (boundary : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z ∈ A n b m)
    (nest : ∀ n (b : I (n + 1)) (c : I n),
      (B n).repr ((C.d (n + 1) n).hom (B (n + 1) b)) c ≠ 0 →
      ∀ m, A n c m ≤ A (n + 1) b m)
    (epsilon : D.X 0 →ₗ[R] R)
    (epsilon_d : epsilon.comp (D.d 1 0).hom = 0)
    (acyc0 : ∀ n b (z : D.X 0), z ∈ A n b 0 → epsilon z = 0 →
      ∃ y ∈ A n b 1, (D.d 1 0).hom y = z)
    (acyc : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z = 0 → ∃ y ∈ A n b (m + 2), (D.d (m + 2) (m + 1)).hom y = z)
    (f g : C ⟶ D)
    (augmentation : epsilon.comp (f.f 0).hom = epsilon.comp (g.f 0).hom)
    (fc : ∀ n b, (f.f n).hom (B n b) ∈ A n b n)
    (gc : ∀ n b, (g.f n).hom (B n b) ∈ A n b n) :
    ∃ H : Homotopy f g, ∀ n b, (H.hom n (n + 1)).hom (B n b) ∈ A n b (n + 1) := by
  exact exists_homotopy (B := B) A boundary nest epsilon epsilon_d acyc0 acyc f g augmentation fc gc

end

noncomputable section
open CategoryTheory Module
open D5.S3.HomologicalAlgebra.AcyclicCarrier
variable {C D : ChainComplex (ModuleCat.{v} (ZMod 2)) ℕ}
variable {I : ℕ → Type w} {B : ∀ n, Basis (I n) (ZMod 2) (C.X n)}
example
    (A : ∀ n, I n → ∀ m, Submodule (ZMod 2) (D.X m))
    (boundary : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z ∈ A n b m)
    (nest : ∀ n (b : I (n + 1)) (c : I n),
      (B n).repr ((C.d (n + 1) n).hom (B (n + 1) b)) c ≠ 0 →
      ∀ m, A n c m ≤ A (n + 1) b m)
    (epsilon : D.X 0 →ₗ[ZMod 2] ZMod 2)
    (epsilon_d : epsilon.comp (D.d 1 0).hom = 0)
    (acyc0 : ∀ n b (z : D.X 0), z ∈ A n b 0 → epsilon z = 0 →
      ∃ y ∈ A n b 1, (D.d 1 0).hom y = z)
    (acyc : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z = 0 → ∃ y ∈ A n b (m + 2), (D.d (m + 2) (m + 1)).hom y = z)
    (f g : C ⟶ D)
    (augmentation : epsilon.comp (f.f 0).hom = epsilon.comp (g.f 0).hom)
    (fc : ∀ n b, (f.f n).hom (B n b) ∈ A n b n)
    (gc : ∀ n b, (g.f n).hom (B n b) ∈ A n b n) :
    ∃ H : Homotopy f g, ∀ n b, (H.hom n (n + 1)).hom (B n b) ∈ A n b (n + 1) := by
  exact exists_homotopy (B := B) A boundary nest epsilon epsilon_d acyc0 acyc f g augmentation fc gc

set_option pp.universes true in
#check @exists_homotopy
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.Carried.face
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.Carried.sub
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.basis_exists_lift
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.exists_carried_primitive
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.exists_carried_primitive0
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.Carried.comp_left
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.Carried.d_comp
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.exists_sequence
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.CarrierData.exists_carried_homotopy
#print axioms D5.S3.HomologicalAlgebra.AcyclicCarrier.exists_homotopy
