/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic moment sums and their canonical pairing expressions are defined. -/

import Mathlib

/-! Finite quadratic moment definitions used by the cubic and fourth-order expansions. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing A] [Algebra ℝ A]

/-- The unweighted sum of a coefficient function. -/
def indexSum (f : ι → ℝ) : ℝ := ∑ d, f d

/-- A moment of finite coefficient sums under a linear functional. -/
def quadraticFamilyMoment (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) {k : ℕ}
    (f : Fin k → ι → ℝ) : ℝ :=
  ℓ (∏ i, ∑ d, f i d • Y d)

/-- The ordered distinct-index moment. -/
def distinctIndexMoment (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) {k : ℕ}
    (f : Fin k → ι → ℝ) : ℝ :=
  ∑ x : Fin k → ι with Function.Injective x,
    (∏ i, f i (x i)) * ℓ (∏ i, Y (x i))

/-- The three products of second moments. -/
def perfectPairingSum (B : (ι → ℝ) → (ι → ℝ) → ℝ)
    (f g h q : ι → ℝ) : ℝ :=
  B f g * B h q + B f h * B g q + B f q * B g h

/-- The six choices of a repeated pair and two singleton indices. -/
def repeatedPairSum (C : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ)
    (f g h q : ι → ℝ) : ℝ :=
  C (f*g) h q + C (f*h) g q + C (f*q) g h +
  C (g*h) f q + C (g*q) f h + C (h*q) f g

/-- The three pairings of two two-fold coefficient products. -/
def pairPairSum (B : (ι → ℝ) → (ι → ℝ) → ℝ)
    (f g h q : ι → ℝ) : ℝ :=
  B (f*g) (h*q) + B (f*h) (g*q) + B (f*q) (g*h)

/-- The four choices of a singleton in a three-fold coefficient product. -/
def tripleSingletonSum (B : (ι → ℝ) → (ι → ℝ) → ℝ)
    (f g h q : ι → ℝ) : ℝ :=
  B (g*h*q) f + B (f*h*q) g + B (f*g*q) h + B (f*g*h) q

omit [DecidableEq ι] in
/-- Expand a product of weighted sums as a sum over all ordered index tuples. -/
lemma quadraticFamilyMoment_eq_tuple_sum (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) {k : ℕ}
    (f : Fin k → ι → ℝ) :
    quadraticFamilyMoment ℓ Y f = ∑ x : Fin k → ι, (∏ i, f i (x i)) * ℓ (∏ i, Y (x i)) := by
  unfold quadraticFamilyMoment
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_smul, map_smul, smul_eq_mul]

/-- Permuting tuple positions preserves the sum over ordered injective tuples. -/
lemma sum_perm {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : (Fin n → ι) → ℝ) :
    (∑ x : Fin n → ι with Function.Injective x, F (x ∘ e)) =
      ∑ x : Fin n → ι with Function.Injective x, F x := by
  apply Finset.sum_bij (fun x _ => x ∘ e)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      ((Finset.mem_filter.mp hx).2.comp e.injective)
  · intro x hx y hy h
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  · intro y hy
    refine ⟨y ∘ e.symm, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        ((Finset.mem_filter.mp hy).2.comp e.symm.injective)
    · funext i; simp
  · intro x hx; rfl

/-- The ordered distinct-index second moment is symmetric in its two coefficient functions. -/
lemma distinctIndexMoment_pair_comm (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (f g : ι → ℝ) : distinctIndexMoment ℓ Y ![f, g] = distinctIndexMoment ℓ Y ![g, f] := by
  classical
  unfold distinctIndexMoment
  rw [← sum_perm (Equiv.swap 0 1)
    (fun x : Fin 2 → ι => (∏ i, (![g, f] : Fin 2 → ι → ℝ) i (x i)) *
      ℓ (∏ i, Y (x i)))]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Fin.prod_univ_two, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_comm (Y (x 1)) (Y (x 0))]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
