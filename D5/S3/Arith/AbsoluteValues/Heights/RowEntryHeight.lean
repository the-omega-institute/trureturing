/- GID: D5/S3/Arith/AbsoluteValues/Heights/RowEntryHeight
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/RowEntryHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Arakelov height of a finite span is bounded by the product of its generators' heights. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.Hadamard
public import D5.S3.Arith.AbsoluteValues.Heights.Duality
import all D5.S3.Arith.AbsoluteValues.Heights.Duality
public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Fintype.Order
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Data.Real.Pointwise
import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
import all Mathlib.NumberTheory.Height.Basic

-- Used only inside proofs: the finiteness of the support of the finite-place factor of a height.

public section

open Finset Matrix Module NumberField Real

namespace exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- **The nonarchimedean half.** At a nonarchimedean absolute value the largest maximal minor of a
family of `k` vectors is at most the product of the largest entries of the vectors: the Leibniz
formula writes each minor as a sum of products of one entry from each vector, a sum is no larger
than its largest term, and the permutation is a bijection of the rows. -/
theorem iSup_plucker_le_prod {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (X : Fin k → (ι → K)) :
    (⨆ s : Set.powersetCard ι k, v (plucker k X s)) ≤ ∏ i, ⨆ j, v (X i j) := by
  have nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp)))
  have hnn : ∀ i, (0 : ℝ) ≤ ⨆ j, v (X i j) := fun i ↦ Real.iSup_nonneg fun j ↦ v.nonneg _
  refine Real.iSup_le (fun s ↦ ?_) (Finset.prod_nonneg fun i _ ↦ hnn i)
  rw [nativeSource18, Matrix.det_apply']
  refine (hv.apply_sum_le_sup Finset.univ_nonempty).trans (Finset.sup'_le _ _ fun σ _ ↦ ?_)
  rw [map_mul]
  have h1 : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [h1, one_mul, map_prod]
  calc ∏ i, v (Matrix.of (fun i j ↦ X i (Set.powersetCard.ofFinEmbEquiv.symm s j)) (σ i) i)
      ≤ ∏ i, ⨆ j, v (X (σ i) j) :=
        Finset.prod_le_prod₀ (fun i _ ↦ v.nonneg _) fun i _ ↦ Finite.le_ciSup_of_le _ le_rfl
    _ = ∏ i, ⨆ j, v (X i j) := Equiv.prod_comp σ fun i ↦ ⨆ j, v (X i j)

end exteriorPower

namespace Matrix

open exteriorPower

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

omit [NumberField K] in
/-- **The archimedean half.** At an infinite place the local factor of the tuple of maximal minors
is the Gram determinant of the rows read through the embedding, and the bound is Hadamard's
inequality in its Hermitian form — which covers a real place as well, the embedding there landing
in `ℝ`. -/
theorem sum_sq_plucker_row_le_prod (v : InfinitePlace K) (A : Matrix (Fin m) ι K) :
    ∑ s : Set.powersetCard ι m, v (plucker m A.row s) ^ 2 ≤ ∏ i, ∑ j, v (A i j) ^ 2 := by
  have hcomplex (s : Set.powersetCard ι m) :
      exteriorPower.plucker m (A.map v.embedding).row s =
        (Matrix.of fun i j ↦ (A.map v.embedding).row i
          (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp
  have hfield (s : Set.powersetCard ι m) :
      exteriorPower.plucker m A.row s =
        (Matrix.of fun i j ↦ A.row i
          (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp
  have hmap (s : Set.powersetCard ι m) :
      exteriorPower.plucker m (A.map v.embedding).row s =
        v.embedding (exteriorPower.plucker m A.row s) := by
    classical
    rw [hcomplex, hfield, RingHom.map_det]
    rfl
  have h := Matrix.sum_sq_norm_plucker_row_le_prod (A.map v.embedding)
  simp_rw [hmap] at h
  simpa only [Matrix.map_apply, InfinitePlace.norm_embedding_eq] using h

/-- **The Arakelov height of the tuple of maximal minors is at most the product of the Arakelov
heights of the rows.** This is Bombieri–Gubler 2.9.8: the two local bounds above, assembled over
all places. No hypothesis is needed — if the minors all vanish the left-hand side is the junk
value `1`, and every factor on the right is at least `1`. -/
theorem arakelovMulHeight_plucker_row_le_prod (A : Matrix (Fin m) ι K) :
    NumberField.arakelovMulHeight (plucker m A.row)
      ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
  have nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  have nativeSource13 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · simp [NumberField.arakelovMulHeight]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
    have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
    rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
    refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ ?_)
      (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
    have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
      le_trans (le_of_eq (by simp [hi']))
        (Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (mem_univ i))
    exact Real.one_le_rpow h1 (by positivity))))
  classical
  rcases eq_or_ne (plucker m A.row) 0 with h0 | h0
  · rw [h0, (show NumberField.arakelovMulHeight (0 : Set.powersetCard ι m → K) = 1 from by
      simp [NumberField.arakelovMulHeight])]
    exact Finset.one_le_prod₀ fun _ _ ↦ nativeSource13 _
  have hrow : ∀ i, A i ≠ 0 := by
    intro i hi
    apply h0
    funext s
    rw [Pi.zero_apply]
    have hdet : plucker m A.row s =
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
      classical
      rw [exteriorPower.plucker, Module.Basis.equivFun_apply,
        exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
        Set.powersetCard.ofFinEmbEquiv_symm_apply]
      rfl
    rw [hdet]
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ ?_
    rw [Matrix.submatrix_apply]
    exact congrFun hi _
  have hfinp : (fun v : FinitePlace K ↦
      ⨆ s : Set.powersetCard ι m, v (plucker m A.row s)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal h0
  have hfini : ∀ i, (fun v : FinitePlace K ↦ ⨆ j, v (A i j)).HasFiniteMulSupport :=
    fun i ↦ Height.hasFiniteMulSupport_iSup_nonarchAbsVal (hrow i)
  have hexp : (∏ i, NumberField.arakelovMulHeight (A i))
      = (∏ i, ∏ v : InfinitePlace K, (∑ j, v (A i j) ^ 2) ^ (v.mult / 2 : ℝ))
        * ∏ i, ∏ᶠ v : FinitePlace K, ⨆ j, v (A i j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by
      simp only [NumberField.arakelovMulHeight, if_neg (hrow i)]
  rw [NumberField.arakelovMulHeight, if_neg h0, hexp]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · rw [Finset.prod_comm]
    refine Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_
    rw [Real.finsetProd_rpow _ _ (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity) _]
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun s _ ↦ by positivity)
      (sum_sq_plucker_row_le_prod v A) (by positivity)
  · rw [← finprod_prod_comm Finset.univ (fun (v : FinitePlace K) i ↦ ⨆ j, v (A i j))
      fun i _ ↦ hfini i]
    refine finprod_le_finprod₀ hfinp (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
      (Function.HasFiniteMulSupport.prod hfini Finset.univ) fun v ↦ ?_
    exact iSup_plucker_le_prod (NumberField.FinitePlace.add_le v) A.row
  · exact _root_.finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  · positivity

/-- **The Arakelov height of the row space is at most the product of the Arakelov heights of the
rows.** The rows must be independent for the row space to have the minors of `A` as its Plücker
coordinates; that is the only role of the hypothesis. -/
theorem arakelovMulHeight_span_range_row_le_prod {A : Matrix (Fin m) ι K}
    (hA : LinearIndependent K A.row) :
    (Submodule.span K (Set.range A.row)).arakelovMulHeight
      ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
  have nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp)))
  have nativeSource19 := (open Module Submodule exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) => (show exteriorPower.plucker m A.row s =
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det from by
    classical
    rw [nativeSource18, Set.powersetCard.ofFinEmbEquiv_symm_apply]
    rfl)))
  have nativeSource20 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (c : R) (v w : Fin k → (ι → R)) => (show exteriorPower.plucker k v = c • exteriorPower.plucker k w ↔ exteriorPower.ιMulti R k v = c • exteriorPower.ιMulti R k w from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker, ← map_smul]
    exact (LinearEquiv.injective _).eq_iff)))
  have nativeSource21 := (open Module in (fun {k : ℕ} (s : Set.powersetCard (Fin k) k) => (show ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) from by
    classical
    have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm)))
  have nativeSource22 := (open Module in (fun {E : Type _} [instSource2 : AddCommGroup E] [instSource3 : Module K E] {k : ℕ} {v : Fin k → E} (hv : LinearIndependent K v) => (show exteriorPower.ιMulti K k v ≠ 0 from by
    classical
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h)))
  have nativeSource23 := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b b' : Module.Basis (Fin k) K V) => (show ∃ c : K, exteriorPower.plucker k (fun i ↦ ((b' i : ι → K))) = c • exteriorPower.plucker k fun i ↦ ((b i : ι → K)) from by
    classical
    have h1 : Module.finrank K (⋀[K]^k V) = 1 := by rw [exteriorPower.finrank_eq, hV, Nat.choose_self]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (exteriorPower.ιMulti K k ⇑b)
      (nativeSource22 b.linearIndependent)).1 h1 (exteriorPower.ιMulti K k ⇑b')
    refine ⟨c, (nativeSource20 ..).2 ?_⟩
    have := congrArg (exteriorPower.map k V.subtype) hc
    rwa [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, eq_comm] at this)))
  have nativeSource24 := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b : Module.Basis (Fin k) K V)
      (hb : exteriorPower.plucker k (fun i ↦ ((b i : ι → K))) ≠ 0) => (show Submodule.pluckerPoint V hV = Projectivization.mk K (exteriorPower.plucker k fun i ↦ ((b i : ι → K))) hb from by
    classical
    obtain ⟨c, hc⟩ := nativeSource23 hV b (Module.finBasisOfFinrankEq K V hV)
    refine ((Projectivization.mk_eq_mk_iff' K _ _ _ hb).2 ⟨c, hc.symm⟩))))
  have nativeSource27 := (open Module in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show exteriorPower.plucker k v ≠ 0 from by
    classical
    intro h
    apply nativeSource22 hv
    apply (((Pi.basisFun K ι).exteriorPower k).equivFun).injective
    simpa only [exteriorPower.plucker, map_zero] using h)))
  have nativeSource28 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v)
      (hV : Module.finrank K (Submodule.span K (Set.range v)) = k) => (show Submodule.pluckerPoint (Submodule.span K (Set.range v)) hV =
        Projectivization.mk K (exteriorPower.plucker k v) (nativeSource27 hv) from by
    classical
    have hfun : (fun i ↦ ((Module.Basis.span hv i : ι → K))) = v :=
      funext fun i ↦ congrArg Subtype.val (Module.Basis.span_apply hv i)
    rw [nativeSource24 hV (Module.Basis.span hv) (by rw [hfun]; exact nativeSource27 hv)]
    simp only [hfun])))
  have nativeSource29 := (open Module exteriorPower Submodule in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (exteriorPower.plucker k v) from by
    classical
    have hV : finrank K (span K (Set.range v)) = k :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin k)
    rw [(show (span K (Set.range v)).arakelovMulHeight =
        Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hV) from by
          exact Eq.rec (motive := fun (r : ℕ) (hr : finrank K (span K (Set.range v)) = r) ↦
            (span K (Set.range v)).arakelovMulHeight = Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hr))
            rfl hV), nativeSource28 hv hV]
    rfl)))
  have nativeSource30 := (open Module Submodule exteriorPower in (fun {A : Matrix (Fin m) ι K} (hA : LinearIndependent K A.row) => (show (Submodule.span K (Set.range A.row)).arakelovMulHeight =
        NumberField.arakelovMulHeight fun s : Set.powersetCard ι m ↦
          (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det from by
    classical
    rw [nativeSource29 hA]
    exact congrArg _ (funext (nativeSource19 A)))))
  rw [nativeSource30 hA]
  refine le_trans (le_of_eq ?_) (arakelovMulHeight_plucker_row_le_prod A)
  exact congrArg _ (funext fun s ↦ (nativeSource19 A s).symm)


end Matrix

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **2.9.8 for an arbitrary finite family.** The height of the span is at most the product of the
Arakelov heights of the generators, whatever the index type and whatever their dependences. This
is the form Layer 5.6 consumes, its generators being indexed by a product rather than by
`Fin m`. -/
theorem arakelovMulHeight_span_range_le_prod {μ : Type*} [Fintype μ] (v : μ → (ι → K)) :
    (Submodule.span K (Set.range v)).arakelovMulHeight
      ≤ ∏ i, NumberField.arakelovMulHeight (v i) := by
  have hFin {m : ℕ} (A : Matrix (Fin m) ι K) :
      (Submodule.span K (Set.range A.row)).arakelovMulHeight
        ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
    have nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
      classical
      rcases eq_or_ne x 0 with rfl | hx
      · rw [smul_zero]
      have hcx : c • x ≠ 0 := by simp [hc, hx]
      have hFinite :
          (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
            = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
        have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
          obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
          exact Finset.prod_pos fun v _ ↦ pow_pos
            ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
        have h := Height.mulHeight_smul_eq_mulHeight x hc
        rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
        have hSupInfinite (v : NumberField.InfinitePlace K) :
            (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
        have hSupFinite (v : NumberField.FinitePlace K) :
            (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
        simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
        exact mul_left_cancel₀ hA.ne' (by linear_combination h)
      have harch (v : NumberField.InfinitePlace K) :
          (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
            = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
        have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
        have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
          rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
            ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
          congr 1
          push_cast
          ring
        rw [hsum, Real.mul_rpow (by positivity) (by positivity),
          hPower]
      rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
      simp only [harch, Finset.prod_mul_distrib]
      rw [mul_right_comm, hFinite, mul_comm])))
    have nativeSource13 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
      classical
      rcases eq_or_ne x 0 with rfl | hx
      · simp [NumberField.arakelovMulHeight]
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
      have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
      have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
      rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
      refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ ?_)
        (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
      have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
        le_trans (le_of_eq (by simp [hi']))
          (Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (mem_univ i))
      exact Real.one_le_rpow h1 (by positivity))))
    have nativeSource16 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 < NumberField.arakelovMulHeight x from by
      classical
      exact (
        zero_lt_one.trans_le <| nativeSource13 x
      ))))
    have nativeSource43 := (open Module Submodule exteriorPower in (fun {K : Type _} [instSource1 : Field K] {ι : Type _} [instSource3 : Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι K) => (show ∃ (R : ℕ) (f : Fin R → Fin m), A.rank = R ∧
          LinearIndependent K (A.submatrix f id).row ∧
          Submodule.span K (Set.range (A.submatrix f id).row) = Submodule.span K (Set.range A.row) from by
      classical
      classical
      obtain ⟨b, -, -, hsp, hind⟩ :=
        exists_linearIndepOn_extension (K := K) (v := A.row) (linearIndepOn_empty K A.row)
          (Set.empty_subset (Set.univ : Set (Fin m)))
      set s : Finset (Fin m) := b.toFinset with hs
      set R : ℕ := s.card with hR
      set E : Fin R ≃ ↥b :=
        (s.orderIsoOfFin hR.symm).toEquiv.trans (Equiv.subtypeEquivRight fun x ↦ Set.mem_toFinset)
        with hE
      have hindB : LinearIndependent K (A.submatrix (fun i ↦ (E i : Fin m)) id).row :=
        hind.comp E E.injective
      have hrange : Set.range (fun i : Fin R ↦ ((E i : Fin m))) = b := by
        rw [show (fun i : Fin R ↦ ((E i : Fin m))) = Subtype.val ∘ E from rfl,
          Set.range_comp, E.range_eq_univ, Set.image_univ, Subtype.range_coe]
      have himg : Set.range (A.submatrix (fun i ↦ (E i : Fin m)) id).row = A.row '' b := by
        rw [show (A.submatrix (fun i ↦ (E i : Fin m)) id).row
            = A.row ∘ (fun i : Fin R ↦ ((E i : Fin m))) from rfl, Set.range_comp, hrange]
      have hspanB : Submodule.span K (Set.range (A.submatrix (fun i ↦ (E i : Fin m)) id).row)
          = Submodule.span K (Set.range A.row) := by
        rw [himg]
        refine le_antisymm (Submodule.span_mono ?_) (span_le.2 ?_)
        · rintro _ ⟨x, -, rfl⟩
          exact ⟨x, rfl⟩
        · rw [← Set.image_univ]
          exact hsp
      refine ⟨R, fun i ↦ (E i : Fin m), ?_, hindB, hspanB⟩
      rw [Matrix.rank_eq_finrank_span_row, ← hspanB, finrank_span_eq_card hindB, Fintype.card_fin])))
    classical
    obtain ⟨R, f, hR, hind, hspan⟩ := nativeSource43 A
    have hinj : Function.Injective f := fun a b hab ↦
      hind.injective (funext fun j ↦ by simp [Matrix.submatrix_apply, hab])
    rw [← hspan]
    refine (Matrix.arakelovMulHeight_span_range_row_le_prod hind).trans ?_
    calc ∏ i : Fin R, NumberField.arakelovMulHeight ((A.submatrix f id) i)
        = ∏ i : Fin R, NumberField.arakelovMulHeight (A (f i)) := rfl
      _ = ∏ i ∈ Finset.univ.image f, NumberField.arakelovMulHeight (A i) :=
          (Finset.prod_image (f := fun i ↦ NumberField.arakelovMulHeight (A i))
            hinj.injOn).symm
      _ ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
          rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image f))]
          exact le_mul_of_one_le_left
            (Finset.prod_nonneg fun i _ ↦ (nativeSource16 _).le)
            (Finset.one_le_prod₀ fun i _ ↦ nativeSource13 _)
  let e : Fin (Fintype.card μ) ≃ μ := (Fintype.equivFin μ).symm
  have hrange :
      Set.range (Matrix.of fun l ↦ v (e l) : Matrix (Fin (Fintype.card μ)) ι K).row
        = Set.range v := by
    rw [show (Matrix.of fun l ↦ v (e l) : Matrix (Fin (Fintype.card μ)) ι K).row = v ∘ e from rfl,
      Set.range_comp, e.range_eq_univ, Set.image_univ]
  rw [← hrange]
  exact (hFin _).trans
    (le_of_eq (Equiv.prod_comp e fun i ↦ NumberField.arakelovMulHeight (v i)))

end Submodule

end
