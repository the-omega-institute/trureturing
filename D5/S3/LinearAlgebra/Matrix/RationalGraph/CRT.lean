/- GID: D5/S3/LinearAlgebra/Matrix/RationalGraph/CRT
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chinese remainder factorization of a matrix congruence index -/

import OmegaBuild.Commands
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Omega original.

# Chinese remainder factorization of a matrix congruence index

The additive subgroup of integer vectors sent to zero modulo a product of
pairwise coprime moduli has index equal to the product of the individual indices.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators

namespace Omega.RationalMatrixGraph.CRT

noncomputable section

/-- Entrywise reduction of an integer matrix modulo `d`. -/
def reduceMatrix {m n : Type*} (d : ℕ) (A : Matrix m n ℤ) : Matrix m n (ZMod d) :=
  A.map (Int.castRingHom (ZMod d))

/-- Coordinatewise reduction of an integer vector modulo `d`. -/
def reduceVec (n : Type*) (d : ℕ) : (n → ℤ) →+ (n → ZMod d) where
  toFun v i := v i
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

theorem reduceVec_surj (n : Type*) (d : ℕ) : Function.Surjective (reduceVec n d) := by
  intro v
  choose a ha using fun i : n => ZMod.intCast_surjective (v i)
  exact ⟨a, funext ha⟩

/-- The integer vectors whose image under `A` vanishes modulo `d`. -/
def graphKernel {n : Type*} [Fintype n] (d : ℕ) (A : Matrix n n ℤ) :
    AddSubgroup (n → ℤ) :=
  (((reduceMatrix d A).mulVecLin).toAddMonoidHom.comp (reduceVec n d)).ker

theorem graphKernel_mem {n : Type*} [Fintype n] (d : ℕ)
    (A : Matrix n n ℤ) (v : n → ℤ) :
    v ∈ graphKernel d A ↔ ∀ i, (d : ℤ) ∣ (A *ᵥ v) i := by
  unfold graphKernel
  rw [AddMonoidHom.mem_ker]
  have hmap (i : n) :
      (((reduceMatrix d A).mulVecLin).toAddMonoidHom.comp (reduceVec n d)) v i =
        ((A *ᵥ v) i : ZMod d) :=
    (RingHom.map_mulVec (Int.castRingHom (ZMod d)) A v i).symm
  constructor
  · intro h i
    have hi := congrFun h i
    rw [hmap] at hi
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
  · intro h
    ext i
    rw [hmap]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h i)

/-- The index counts the image of the matrix over `ZMod d`. -/
theorem kernel_card {n : Type*} [Fintype n] (d : ℕ) (A : Matrix n n ℤ) :
    (graphKernel d A).index = Nat.card (LinearMap.range (reduceMatrix d A).mulVecLin) := by
  let f := (reduceMatrix d A).mulVecLin.toAddMonoidHom
  let g := f.comp (reduceVec n d)
  have hr : g.range = f.range := by
    change (f.comp (reduceVec n d)).range = f.range
    rw [AddMonoidHom.range_comp, AddMonoidHom.range_eq_top.mpr (reduceVec_surj n d),
      AddSubgroup.map_top]
  change Nat.card ((n → ℤ) ⧸ g.ker) = Nat.card f.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hr]

/-- The Chinese remainder equivalence acts coordinatewise on integer matrices
and factors their images into the independent images at each coprime modulus. -/
def rangeEquiv {n ι : Type*} [Fintype n] [Fintype ι] (d : ι → ℕ)
    (hc : Pairwise (Function.onFun Nat.Coprime d)) (A : Matrix n n ℤ) :
    LinearMap.range (reduceMatrix (∏ i, d i) A).mulVecLin ≃
      ∀ i, LinearMap.range (reduceMatrix (d i) A).mulVecLin := by
  classical
  let e := ZMod.prodEquivPi d hc
  let D := ∏ i, d i
  let T := (reduceMatrix D A).mulVecLin
  let Tᵢ (i : ι) := (reduceMatrix (d i) A).mulVecLin
  have hmap (x : n → ZMod D) (i : ι) (j : n) :
      e (T x j) i = Tᵢ i (fun k => e (x k) i) j := by
    let f := (Pi.evalRingHom (fun i => ZMod (d i)) i).comp e.toRingHom
    have hmat : (reduceMatrix D A).map f = reduceMatrix (d i) A := by
      ext j k
      change f ((A j k : ℤ) : ZMod D) = ((A j k : ℤ) : ZMod (d i))
      exact map_intCast f _
    change f (((reduceMatrix D A) *ᵥ x) j) = _
    rw [RingHom.map_mulVec, hmat]
    rfl
  let F : LinearMap.range T → ∀ i, LinearMap.range (Tᵢ i) := fun x i =>
    ⟨fun j => e (x.val j) i, by
      obtain ⟨y, hy⟩ := x.property
      refine ⟨fun k => e (y k) i, ?_⟩
      funext j
      rw [← hmap y i j, hy]⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y h
    apply Subtype.ext
    funext j
    apply e.injective
    funext i
    exact congrArg (fun f : ∀ i, LinearMap.range (Tᵢ i) => (f i).val j) h
  · intro y
    choose x hx using fun i => (y i).property
    let z : n → ZMod D := fun j => e.symm (fun i => x i j)
    refine ⟨⟨T z, ⟨z, rfl⟩⟩, ?_⟩
    funext i
    apply Subtype.ext
    funext j
    change e (T z j) i = (y i).val j
    rw [hmap]
    have he : (fun k => e (z k) i) = x i := by
      funext k
      simp [z]
    rw [he, hx i]

/-- The congruence index for a product of pairwise coprime moduli factors. -/
theorem index_prod {n ι : Type*} [Fintype n] [Fintype ι] (d : ι → ℕ)
    (hc : Pairwise (Function.onFun Nat.Coprime d)) (A : Matrix n n ℤ) :
    (graphKernel (∏ i, d i) A).index = ∏ i, (graphKernel (d i) A).index := by
  simp_rw [kernel_card]
  rw [Nat.card_congr (rangeEquiv d hc A), Nat.card_pi]

end

end Omega.RationalMatrixGraph.CRT
