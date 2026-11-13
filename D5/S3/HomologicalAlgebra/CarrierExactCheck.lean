import D5.S3.HomologicalAlgebra.AcyclicCarrier
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Basic
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

namespace NonzeroFixture
open CategoryTheory Module
abbrev delta (n : ℕ) : ModuleCat.of (ZMod 2) (ZMod 2) ⟶ ModuleCat.of (ZMod 2) (ZMod 2) :=
  if n % 2 = 0 then 𝟙 _ else 0
abbrev disk : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of (ZMod 2) (ZMod 2)) delta (by
    intro n
    by_cases h : n % 2 = 0
    · have hn : (n + 1) % 2 ≠ 0 := by omega
      simp [delta, h, hn]
    · simp [delta, h])
abbrev beta (n : ℕ) : Basis Unit (ZMod 2) (disk.X n) := Basis.singleton Unit (ZMod 2)
example : ∃ H : Homotopy (𝟙 disk) (0 : disk ⟶ disk),
    (∀ n b, (H.hom n (n+1)).hom (beta n b) ∈ (⊤ : Submodule (ZMod 2) (disk.X (n+1)))) ∧
    H.hom 0 1 ≠ 0 := by
  obtain ⟨H, hH⟩ := exists_homotopy (B := beta)
    (fun _ _ _ => ⊤) (by intros; trivial) (by intros; exact le_rfl)
    (0 : disk.X 0 →ₗ[ZMod 2] ZMod 2) (by simp)
    (by
      intro n b z hz he
      exact ⟨z, by trivial, by simp [disk, ChainComplex.of.d, delta]⟩)
    (by
      intro n b m z hz hc
      by_cases hm : m % 2 = 0
      · have hz0 : z = 0 := by simpa [disk, delta, hm] using hc
        exact ⟨0, by trivial, by simp [hz0]⟩
      · have hm' : (m+1) % 2 = 0 := by omega
        exact ⟨z, by trivial, by simpa [disk, ChainComplex.of.d, delta, hm']⟩)
    (𝟙 disk) 0 (by simp) (by intros; trivial) (by intros; trivial)
  refine ⟨H, hH, ?_⟩
  intro hzero
  have he := H.comm 0
  rw [Homotopy.dNext_zero_chainComplex (P := disk) (Q := disk) H.hom,
    Homotopy.prevD_chainComplex (P := disk) (Q := disk) H.hom 0] at he
  rw [hzero] at he
  have hbad := congrArg (fun k : disk.X 0 ⟶ disk.X 0 => k.hom (1 : ZMod 2)) he
  simpa using hbad
end NonzeroFixture
