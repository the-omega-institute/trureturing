/- GID: D5/S3/Geometry/KozakiKakeiMatching
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two oriented cyclic matchings of the even frieze level equation. -/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace D5.S3.Geometry.KozakiKakei
open scoped BigOperators

abbrev K := RatFunc ℂ
abbrev Col (m : ℕ) := Fin (2 * m)
abbrev Chart (R : Type*) (m : ℕ) := Matrix (Fin 2) (Col m) R

def first {m : ℕ} (hm : 2 ≤ m) : Col m := ⟨0, by omega⟩
def second {m : ℕ} (hm : 2 ≤ m) : Col m := ⟨1, by omega⟩
def third {m : ℕ} (hm : 2 ≤ m) : Col m := ⟨2, by omega⟩

def last {m : ℕ} (hm : 2 ≤ m) : Col m := ⟨2 * m - 1, by omega⟩

def oddVertex {m : ℕ} (p : Fin m × Bool) : Col m :=
  ⟨2 * p.1.val + (if p.2 then 1 else 0), by have := p.1.isLt; split <;> omega⟩

def evenVertex {m : ℕ} (p : Fin m × Bool) : Col m :=
  ⟨if p.1.val = 0 then (if p.2 then 2 * m - 1 else 0)
    else 2 * p.1.val - (if p.2 then 0 else 1), by
      have h := p.1.isLt
      rcases p with ⟨i, b⟩
      cases b <;> simp_all <;> split <;> omega⟩

private theorem oddVertex_bijective (m : ℕ) :
    Function.Bijective (@oddVertex m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [Nat.mul_comm]⟩
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have h' := congrArg Fin.val h
  cases b <;> cases c <;> simp [oddVertex] at h' ⊢ <;> omega

private theorem evenVertex_bijective (m : ℕ) :
    Function.Bijective (@evenVertex m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [Nat.mul_comm]⟩
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hi := i.isLt
  have hj := j.isLt
  have h' := congrArg Fin.val h
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0 <;>
    cases b <;> cases c <;> simp [evenVertex, hi0, hj0] at h' ⊢ <;> omega

noncomputable def oddMatching (m : ℕ) : Fin m × Bool ≃ Col m :=
  Equiv.ofBijective _ (oddVertex_bijective m)

noncomputable def evenMatching (m : ℕ) : Fin m × Bool ≃ Col m :=
  Equiv.ofBijective _ (evenVertex_bijective m)

def minor {m : ℕ} {R : Type*} [CommRing R] (Z : Chart R m) (i j : Col m) : R :=
  Z 0 i * Z 1 j - Z 1 i * Z 0 j

def Admissible {m : ℕ} {R : Type*} [CommRing R] (Z : Chart R m) : Prop :=
  ∀ i j, i ≠ j → minor Z i j ≠ 0

def reorder {m : ℕ} {R : Type*} (σ : Equiv.Perm (Col m)) (Z : Chart R m) : Chart R m :=
  fun a i => Z a (σ i)

def oddProduct {m : ℕ} {R : Type*} [CommRing R] (Z : Chart R m) : R :=
  ∏ i : Fin m, minor Z (oddVertex (i, false)) (oddVertex (i, true))

def evenProduct {m : ℕ} {R : Type*} [CommRing R] (Z : Chart R m) : R :=
  ∏ i : Fin m, minor Z (evenVertex (i, false)) (evenVertex (i, true))

def PreservesLevel {m : ℕ} (σ : Equiv.Perm (Col m)) : Prop :=
  ∀ Z : Chart K m, Admissible Z → evenProduct Z = oddProduct Z →
    evenProduct (reorder σ Z) = oddProduct (reorder σ Z)

def Normalized {m : ℕ} (hm : 2 ≤ m) (Z : Chart K m) : Prop :=
  Admissible Z ∧
    Z 0 (first hm) = 0 ∧ Z 1 (first hm) = -1 ∧
    Z 0 (second hm) = 1 ∧ Z 1 (second hm) = 0 ∧
    Z 0 (third hm) = 1 ∧ Z 1 (third hm) = 1 ∧
    (∀ (i : Col m) (hi : i.val + 1 < 2 * m), minor Z i ⟨i.val + 1, hi⟩ = 1) ∧
    minor Z (first hm) (last hm) = 1

def MatEquivalent {m : ℕ} (W Z : Chart K m) : Prop :=
  ∃ (L : (Matrix (Fin 2) (Fin 2) K)ˣ) (d : Col m → Kˣ),
    W = (L.val * Z) * Matrix.diagonal (fun i => (d i).val)

def Allowable {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Col m)) : Prop :=
  ∀ Z : Chart K m, Normalized hm Z →
    ∃! W, Normalized hm W ∧ MatEquivalent W (reorder σ Z)

def Dihedral {m : ℕ} (σ : Equiv.Perm (Col m)) : Prop :=
  ∃ a : Col m, (∀ i, σ i = a + i) ∨ (∀ i, σ i = a - i)

def affine {R : Type*} [CommRing R] {m : ℕ} (t : Col m → R) : Chart R m :=
  fun a i => if a = 0 then 1 else t i

theorem minor_affine {R : Type*} [CommRing R] {m : ℕ} (t : Col m → R) (i j : Col m) :
    minor (affine t) i j = t j - t i := by
  simp [minor, affine]

open MvPolynomial

noncomputable def diff {V : Type*} (i j : V) : MvPolynomial V ℂ := X j - X i

noncomputable def matchingPolynomial {m : ℕ} (M : Fin m × Bool ≃ Col m) :
    MvPolynomial (Col m) ℂ :=
  ∏ i : Fin m, diff (M (i, false)) (M (i, true))

noncomputable def F (m : ℕ) : MvPolynomial (Col m) ℂ :=
  matchingPolynomial (evenMatching m) - matchingPolynomial (oddMatching m)

theorem eval_matchingPolynomial {m : ℕ} (M : Fin m × Bool ≃ Col m) (t : Col m → ℂ) :
    eval t (matchingPolynomial M) = ∏ i : Fin m, (t (M (i, true)) - t (M (i, false))) := by
  simp [matchingPolynomial, diff, map_prod]

theorem eval_F {m : ℕ} (t : Col m → ℂ) :
    eval t (F m) = evenProduct (affine t) - oddProduct (affine t) := by
  simp only [F, map_sub, eval_matchingPolynomial, evenProduct, oddProduct, minor_affine]
  rfl

theorem affine_constants_admissible {m : ℕ} {t : Col m → ℂ}
    (ht : Function.Injective t) : Admissible (affine (RatFunc.C ∘ t)) := by
  intro i j hij
  rw [minor_affine]
  exact sub_ne_zero.mpr (RatFunc.C_injective.ne (ht.ne hij.symm))

theorem constant_matrix_implication {m : ℕ} {σ : Equiv.Perm (Col m)}
    (hp : PreservesLevel σ) (t : Col m → ℂ) (ht : Function.Injective t)
    (hF : eval t (F m) = 0) : eval t (rename σ (F m)) = 0 := by
  rw [eval_F, sub_eq_zero] at hF
  have evenC (u : Col m → ℂ) :
      evenProduct (affine (RatFunc.C ∘ u)) = RatFunc.C (evenProduct (affine u)) := by
    simp [evenProduct, minor_affine, map_prod]
  have oddC (u : Col m → ℂ) :
      oddProduct (affine (RatFunc.C ∘ u)) = RatFunc.C (oddProduct (affine u)) := by
    simp [oddProduct, minor_affine, map_prod]
  have h := hp _ (affine_constants_admissible ht) (by rw [evenC, oddC, hF])
  change evenProduct (affine (RatFunc.C ∘ (t ∘ σ))) =
    oddProduct (affine (RatFunc.C ∘ (t ∘ σ))) at h
  rw [evenC, oddC] at h
  rw [eval_rename, eval_F, sub_eq_zero]
  exact RatFunc.C_injective h

end D5.S3.Geometry.KozakiKakei
