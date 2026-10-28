/- GID: D5/S3/FiniteGroups/HeadleyCoordinateKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyCoordinateKernel
   mirror-E: none(waiver:coordinate-kernel)
   anchors: []
   utility: none
   digest: Doubled coordinates, their index-four kernel, and strict exponent decrease. -/

import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! Coordinate kernels for the strict two-primary induction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyCoordinateKernel
open Function

/-- Cyclic two-primary coordinates, allowing zero exponents. -/
abbrev Coordinates {r : ℕ} (e : Fin r → ℕ) := ∀ i, ZMod (2 ^ e i)

/-- Reduction of one positive coordinate modulo two. -/
def reduction (a : ℕ) (ha : 0 < a) : ZMod (2 ^ a) →+ ZMod 2 :=
  (ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt ha)) (ZMod 2)).toAddMonoidHom

private theorem reduction_surjective (a : ℕ) (ha : 0 < a) :
    Surjective (reduction a ha) := by
  exact ZMod.castHom_surjective (dvd_pow_self 2 (Nat.ne_of_gt ha))

/-- Reduction kills precisely the doubled elements, including a=1. -/
theorem reduction_kernel_eq_doubled (a : ℕ) (ha : 0 < a) :
    (reduction a ha).ker = (nsmulAddMonoidHom (α := ZMod (2 ^ a)) 2).range := by
  ext x
  constructor
  · intro hx
    have hv : (x.val : ZMod 2) = 0 := by
      change (ZMod.cast x : ZMod 2) = 0 at hx
      rw [ZMod.cast_eq_val] at hx
      exact hx
    obtain ⟨k, hk⟩ := ZMod.natCast_eq_zero_iff_even.mp hv
    refine ⟨(k : ZMod (2 ^ a)), ?_⟩
    change 2 • (k : ZMod (2 ^ a)) = x
    rw [two_nsmul, ← Nat.cast_add, ← hk, ZMod.natCast_zmod_val]
  · rintro ⟨y, rfl⟩
    change reduction a ha (2 • y) = 0
    rw [map_nsmul, two_nsmul]
    exact CharTwo.add_self_eq_zero _

private theorem reduction_kernel_card (a : ℕ) (ha : 0 < a) :
    Nat.card (reduction a ha).ker = 2 ^ (a - 1) := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective (reduction_surjective a ha)
  have hp : 2 ^ a = 2 ^ (a - 1) * 2 := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
  simp only [Nat.card_zmod] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2) (h.trans hp)

/-- The literal kernel is a cyclic factor with exponent lowered by one. -/
noncomputable def reductionKernelEquiv (a : ℕ) (ha : 0 < a) :
    (reduction a ha).ker ≃+ ZMod (2 ^ (a - 1)) :=
  (zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic (reduction a ha).ker)).symm.trans
    (ZMod.ringEquivCongr (reduction_kernel_card a ha)).toAddEquiv

/-- Additive splitting supplied by the original dependent-function equivalence. -/
def splitAt {ι : Type*} [DecidableEq ι] (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (i : ι) : (∀ k, A k) ≃+ A i × (∀ k : {k // k ≠ i}, A k) :=
  { Equiv.piSplitAt i A with map_add' := fun _ _ => rfl }

/-- Two selected coordinates and the unrestricted remaining coordinates. -/
def splitTwo {ι : Type*} [DecidableEq ι] (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (i j : ι) (hji : j ≠ i) :
    (∀ k, A k) ≃+ (A i × A j) ×
      (∀ k : {k : {k // k ≠ i} // k ≠ ⟨j, hji⟩}, A k.val.val) :=
  ((splitAt A i).trans
    (AddEquiv.prodCongr (AddEquiv.refl _)
      (splitAt (fun k : {k // k ≠ i} => A k.val) ⟨j, hji⟩))).trans
        (AddEquiv.prodAssoc).symm

/-- Product kernels use the original kernel identity and subgroup equivalence. -/
def productKernelEquiv {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] (f : A →+ C) (g : B →+ D) :
    (f.prodMap g).ker ≃+ f.ker × g.ker :=
  (AddEquiv.addSubgroupCongr (AddMonoidHom.ker_prodMap f g)).trans
    (AddSubgroup.prodEquiv _ _)

/-- Ignoring a factor leaves that whole factor in the kernel. -/
def projectionKernelEquiv {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) :
    (f.comp (AddMonoidHom.fst A C)).ker ≃+ f.ker × C where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Exactly the selected exponents are lowered. -/
def lower {r : ℕ} (e : Fin r → ℕ) (i j : Fin r) : Fin r → ℕ :=
  fun k => e k - if k = i ∨ k = j then 1 else 0

/-- The induction measure decreases by exactly two. -/
theorem lower_sum_add_two {r : ℕ} (e : Fin r → ℕ) (i j : Fin r)
    (hij : i ≠ j) (hi : 0 < e i) (hj : 0 < e j) :
    (∑ k, lower e i j k) + 2 = ∑ k, e k := by
  have hpoint (k : Fin r) : e k = lower e i j k +
      (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [lower, true_or, ite_true, hij, ite_false]
      omega
    · by_cases hkj : k = j
      · subst k
        simp only [lower, or_true, ite_true, hki, ite_false]
        omega
      · simp [lower, hki, hkj]
  calc
    (∑ k, lower e i j k) + 2 =
        ∑ k, (lower e i j k + (if k = i then 1 else 0) +
          (if k = j then 1 else 0)) := by simp [Finset.sum_add_distrib]
    _ = ∑ k, e k := Finset.sum_congr rfl (fun k _ => (hpoint k).symm)

end D5.S3.FiniteGroups.HeadleyCoordinateKernel
