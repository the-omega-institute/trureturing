/- GID: D5/S3/Arith/AbsoluteValues/Heights/RestrictScalars
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/RestrictScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restriction of scalars gives a power bound for Arakelov height of a subspace span. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.ArakelovHeightExtension

public section

open Finset Matrix Module NumberField Real exteriorPower

namespace Matrix

section Defs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ι : Type*} [Fintype ι] {m r : ℕ}

/-- **Restriction of scalars for a linear system.** Writing each entry of `A` in the `K`-basis `e`
of `F` turns the `M × N` system over `F` into an `r M × N` system over `K` with the same
`K`-rational solutions. The rows are indexed by `Fin m × Fin r`: the row `(i, t)` is the `t`-th
coordinate of the `i`-th row of `A`. -/
@[expose] noncomputable def restrictScalars (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) :
    Matrix (Fin m × Fin r) ι K :=
  Matrix.of fun p j ↦ e.repr (A p.1 j) p.2

/-- The `K`-linear map `x ↦ A x` on `K`-rational vectors, for `A` a matrix over `F`. Its kernel is
the object Layer 5.6 is about, and it mentions no basis of `F / K`. -/
@[expose] noncomputable def mulVecRestrict (A : Matrix (Fin m) ι F) :
    (ι → K) →ₗ[K] (Fin m → F) :=
  (LinearMap.restrictScalars K A.mulVecLin).comp ((Algebra.linearMap K F).compLeft ι)

end Defs

section Rank

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **The `K`-rank of the restricted system is at most `r` times the `F`-rank of `A`.** The image
of `K ^ N` under `A` lies in the `F`-column space of `A`, an `F`-space of dimension `rank A`,
which as a `K`-space has dimension `r · rank A`. The crude bound `r M` — one for each row of
`Matrix.restrictScalars` — is what `Matrix.rank_le_card_height` gives and is strictly weaker
whenever `A` is not of full rank. -/
theorem finrank_range_mulVecRestrict_le (A : Matrix (Fin m) ι F) :
    finrank K (LinearMap.range (mulVecRestrict (K := K) A)) ≤ finrank K F * A.rank := by
  have hle : LinearMap.range (mulVecRestrict (K := K) A)
      ≤ (LinearMap.range A.mulVecLin).restrictScalars K := by
    rintro _ ⟨x, rfl⟩
    exact ⟨fun j ↦ algebraMap K F (x j), rfl⟩
  refine (Submodule.finrank_mono hle).trans (le_of_eq ?_)
  exact (Module.finrank_mul_finrank K F ↥(LinearMap.range A.mulVecLin)).symm

end Rank

section Conjugate

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
variable {ι : Type*} [Fintype ι] {m r : ℕ}

/-- **The matrix of conjugates**: the row `(i, u)` is the `u`-th conjugate of the `i`-th row of
`A`. This is Bombieri–Gubler's `Ã`. -/
@[expose] def conjugate (σ : Fin r → (F →ₐ[K] L)) (A : Matrix (Fin m) ι F) :
    Matrix (Fin m × Fin r) ι L :=
  Matrix.of fun p j ↦ σ p.2 (A p.1 j)

/-- The matrix of the embeddings on a basis, `(σ_u (e t))`. Its determinant is a square root of
the discriminant of `F / K` in that basis, so it is invertible. -/
@[expose] noncomputable def embMatrix (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L)) :
    Matrix (Fin r) (Fin r) L :=
  Matrix.of fun u t ↦ σ u (e t)

/-- `m` copies of `Matrix.embMatrix` down the diagonal: Bombieri–Gubler's `Ω`. -/
@[expose] noncomputable def blockEmbMatrix (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (m : ℕ) : Matrix (Fin m × Fin r) (Fin m × Fin r) L :=
  Matrix.of fun p q ↦ if p.1 = q.1 then embMatrix e σ p.2 q.2 else 0

omit [Fintype ι] in
/-- **Bombieri–Gubler's (2.30):** the matrix of conjugates is the block matrix of embeddings times
the restriction of scalars. -/
theorem conjugate_eq_blockEmbMatrix_mul (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (A : Matrix (Fin m) ι F) :
    conjugate σ A = blockEmbMatrix e σ m * (restrictScalars e A).map (algebraMap K L) := by
  ext p j
  have hbasis : σ p.2 (A p.1 j)
      = ∑ t, σ p.2 (e t) * algebraMap K L (e.repr (A p.1 j) t) := by
    conv_lhs => rw [← e.sum_repr (A p.1 j)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ ↦ by rw [map_smul, Algebra.smul_def, mul_comm]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [blockEmbMatrix, Matrix.of_apply, ite_mul, zero_mul, Matrix.map_apply,
    Matrix.restrictScalars, Matrix.of_apply, conjugate, embMatrix]
  rw [Finset.sum_eq_single p.1 (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simpa using hbasis

omit [Fintype ι] in
/-- **The conjugates and the restriction of scalars have the same row space over `L`.** -/
theorem span_range_row_conjugate (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (hM : IsUnit (embMatrix e σ).det) (A : Matrix (Fin m) ι F) :
    Submodule.span L (Set.range (conjugate σ A).row)
      = Submodule.span L (Set.range ((restrictScalars e A).map (algebraMap K L)).row) := by
  have nativeSource47 := (open Module Submodule exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} {n : Type _} [instSource5 : Fintype n] [instSource6 : DecidableEq n] (U : Matrix n n R) (A : Matrix n ι R) => (show Submodule.span R (Set.range (U * A).row) ≤ Submodule.span R (Set.range A.row) from by
    classical
    rw [← range_vecMulLinear A, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨U.row i, rfl⟩)))
  have nativeSource48 := (open Module Submodule exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} {n : Type _} [instSource5 : Fintype n] [instSource6 : DecidableEq n] {U : Matrix n n R} (hU : IsUnit U.det)
      (A : Matrix n ι R) => (show Submodule.span R (Set.range (U * A).row) = Submodule.span R (Set.range A.row) from by
    classical
    refine le_antisymm (nativeSource47 U A) ?_
    calc Submodule.span R (Set.range A.row)
        = Submodule.span R (Set.range (U⁻¹ * (U * A)).row) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul U hU, Matrix.one_mul]
      _ ≤ Submodule.span R (Set.range (U * A).row) := nativeSource47 _ _)))
  rw [conjugate_eq_blockEmbMatrix_mul e]
  have hdet : (blockEmbMatrix e σ m).det = (embMatrix e σ).det ^ m := by
    have h : blockEmbMatrix e σ m
        = (Matrix.blockDiagonal fun _ : Fin m ↦ embMatrix e σ).submatrix
            (Equiv.prodComm (Fin m) (Fin r)) (Equiv.prodComm (Fin m) (Fin r)) := by
      ext p q
      simp [blockEmbMatrix, Matrix.blockDiagonal_apply, Equiv.prodComm]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  exact nativeSource48 (by rw [hdet]; exact hM.pow m) _

end Conjugate

end Matrix

namespace Submodule

section BaseChange

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- The image of a `K`-span lies in the `L`-span of the image. -/
theorem comp_algebraMap_mem_span {μ : Type*} {v : μ → (ι → K)} {x : ι → K}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    (algebraMap K L ∘ x) ∈ Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨l, rfl⟩ := hy; exact Submodule.subset_span ⟨l, rfl⟩
  | zero =>
      rw [show (algebraMap K L ∘ (0 : ι → K)) = 0 from funext fun j ↦ by simp]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [show (algebraMap K L ∘ (y + z))
        = (algebraMap K L ∘ y) + (algebraMap K L ∘ z) from funext fun j ↦ by simp]
      exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [show (algebraMap K L ∘ (c • y))
        = algebraMap K L c • (algebraMap K L ∘ y) from funext fun j ↦ by simp [Algebra.smul_def]]
      exact Submodule.smul_mem _ _ hy

/-- **Base change of a span.** Two families with the same `K`-span have the same `L`-span after
base change, so the base change of a subspace may be computed from any family that spans it. -/
theorem span_range_comp_algebraMap_eq {μ ν : Type*} {v : μ → (ι → K)} {w : ν → (ι → K)}
    (h : Submodule.span K (Set.range v) = Submodule.span K (Set.range w)) :
    Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)
      = Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ w l) := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_le] <;> rintro _ ⟨l, rfl⟩
  · exact comp_algebraMap_mem_span (h ▸ Submodule.subset_span ⟨l, rfl⟩)
  · exact comp_algebraMap_mem_span (h ▸ Submodule.subset_span ⟨l, rfl⟩)

end BaseChange

section Height

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Base change does not change the absolute Arakelov height of a subspace.** The Plücker point
of the base change is the image of the Plücker point, by `exteriorPower.plucker_comp_ringHom`, and
the absolute height of a tuple is invariant under an embedding. -/
theorem arakelovMulHeight_span_range_comp_algebraMap_rpow {v : Fin k → (ι → K)}
    (hv : LinearIndependent K v) :
    (Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)).arakelovMulHeight
        ^ (finrank ℚ L : ℝ)⁻¹
      = (Submodule.span K (Set.range v)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
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
    refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod fun v _ ↦ ?_)
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
  have nativeSource20 := (open Module in (fun (k : ℕ) (c : K) (v w : Fin k → (ι → K)) => (show exteriorPower.plucker k v = c • exteriorPower.plucker k w ↔ exteriorPower.ιMulti K k v = c • exteriorPower.ιMulti K k w from by
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
    intro hp
    apply nativeSource22 hv
    rw [exteriorPower.plucker] at hp
    exact (map_eq_zero_iff _ (LinearEquiv.injective _)).mp hp)))
  have nativeSource28 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v)
      (hV : Module.finrank K (Submodule.span K (Set.range v)) = k) => (show Submodule.pluckerPoint (Submodule.span K (Set.range v)) hV =
        Projectivization.mk K (exteriorPower.plucker k v) (nativeSource27 hv) from by
    classical
    have hfun : (fun i ↦ ((Module.Basis.span hv i : ι → K))) = v :=
      funext fun i ↦ congrArg Subtype.val (Module.Basis.span_apply hv i)
    rw [nativeSource24 hV (Module.Basis.span hv) (by rw [hfun]; exact nativeSource27 hv)]
    simp only [hfun])))
  have nativeSource29 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (exteriorPower.plucker k v) from by
    classical
    have hV : finrank K (span K (Set.range v)) = k :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin k)
    rw [(show (span K (Set.range v)).arakelovMulHeight =
        Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hV) from by
          exact Eq.rec (motive := fun (r : ℕ) (hr : finrank K (span K (Set.range v)) = r) ↦
            (span K (Set.range v)).arakelovMulHeight = Projectivization.projectiveArakelovMulHeight ((span K (Set.range v)).pluckerPoint hr))
            rfl hV), nativeSource28 hv hV]
    rfl)))
  have nativeSource20L := (open Module in (fun (k : ℕ) (c : L) (v w : Fin k → (ι → L)) => (show exteriorPower.plucker k v = c • exteriorPower.plucker k w ↔ exteriorPower.ιMulti L k v = c • exteriorPower.ιMulti L k w from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker, ← map_smul]
    exact (LinearEquiv.injective _).eq_iff)))
  have nativeSource22L := (open Module in (fun {E : Type _} [instSource2 : AddCommGroup E] [instSource3 : Module L E] {k : ℕ} {v : Fin k → E} (hv : LinearIndependent L v) => (show exteriorPower.ιMulti L k v ≠ 0 from by
    classical
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h)))
  have nativeSource23L := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule L (ι → L)} (hV : Module.finrank L V = k) (b b' : Module.Basis (Fin k) L V) => (show ∃ c : L, exteriorPower.plucker k (fun i ↦ ((b' i : ι → L))) = c • exteriorPower.plucker k fun i ↦ ((b i : ι → L)) from by
    classical
    have h1 : Module.finrank L (⋀[L]^k V) = 1 := by rw [exteriorPower.finrank_eq, hV, Nat.choose_self]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (exteriorPower.ιMulti L k ⇑b)
      (nativeSource22L b.linearIndependent)).1 h1 (exteriorPower.ιMulti L k ⇑b')
    refine ⟨c, (nativeSource20L ..).2 ?_⟩
    have := congrArg (exteriorPower.map k V.subtype) hc
    rwa [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, eq_comm] at this)))
  have nativeSource24L := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule L (ι → L)} (hV : Module.finrank L V = k) (b : Module.Basis (Fin k) L V)
      (hb : exteriorPower.plucker k (fun i ↦ ((b i : ι → L))) ≠ 0) => (show Submodule.pluckerPoint V hV = Projectivization.mk L (exteriorPower.plucker k fun i ↦ ((b i : ι → L))) hb from by
    classical
    obtain ⟨c, hc⟩ := nativeSource23L hV b (Module.finBasisOfFinrankEq L V hV)
    refine ((Projectivization.mk_eq_mk_iff' L _ _ _ hb).2 ⟨c, hc.symm⟩))))
  have nativeSource27L := (open Module in (fun {k : ℕ} {v : Fin k → (ι → L)} (hv : LinearIndependent L v) => (show exteriorPower.plucker k v ≠ 0 from by
    classical
    intro hp
    apply nativeSource22L hv
    rw [exteriorPower.plucker] at hp
    exact (map_eq_zero_iff _ (LinearEquiv.injective _)).mp hp)))
  have nativeSource28L := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → L)} (hv : LinearIndependent L v)
      (hV : Module.finrank L (Submodule.span L (Set.range v)) = k) => (show Submodule.pluckerPoint (Submodule.span L (Set.range v)) hV =
        Projectivization.mk L (exteriorPower.plucker k v) (nativeSource27L hv) from by
    classical
    have hfun : (fun i ↦ ((Module.Basis.span hv i : ι → L))) = v :=
      funext fun i ↦ congrArg Subtype.val (Module.Basis.span_apply hv i)
    rw [nativeSource24L hV (Module.Basis.span hv) (by rw [hfun]; exact nativeSource27L hv)]
    simp only [hfun])))
  have nativeSource29L := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → L)} (hv : LinearIndependent L v) => (show (span L (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (exteriorPower.plucker k v) from by
    classical
    have hV : finrank L (span L (Set.range v)) = k :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin k)
    rw [(show (span L (Set.range v)).arakelovMulHeight =
        Projectivization.projectiveArakelovMulHeight ((span L (Set.range v)).pluckerPoint hV) from by
          exact Eq.rec (motive := fun (r : ℕ) (hr : finrank L (span L (Set.range v)) = r) ↦
            (span L (Set.range v)).arakelovMulHeight = Projectivization.projectiveArakelovMulHeight ((span L (Set.range v)).pluckerPoint hr))
            rfl hV), nativeSource28L hv hV]
    rfl)))
  have nativeSource109 := (open Function IntermediateField Module in (fun (x : Set.powersetCard ι k → K) => (show NumberField.arakelovMulHeight (algebraMap K L ∘ x) ^ ((Module.finrank ℚ L : ℝ))⁻¹
        = NumberField.arakelovMulHeight x ^ ((Module.finrank ℚ K : ℝ))⁻¹ from by
    classical
    letI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
    letI : IsTorsionFree ℚ K := Module.Free.instIsTorsionFree ℚ K
    letI : Module.Free K L := Module.Free.of_divisionRing K L
    letI : IsTorsionFree K L := Module.Free.instIsTorsionFree K L
    have : IsScalarTower ℚ K L :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
    have hmul : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
    have hkey : NumberField.arakelovMulHeight x ^ Module.finrank K L =
        NumberField.arakelovMulHeight (algebraMap K L ∘ x) :=
      NumberField.arakelovMulHeight_pow_finrank (K := K) (L := L) x
    rw [← hkey, ← hmul]
    rw [← Real.rpow_natCast (NumberField.arakelovMulHeight x) (Module.finrank K L), ← Real.rpow_mul ((nativeSource16 x).le)]
    congr 1
    have hm' : ((Module.finrank ℚ K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := K)).ne'
    have hn' : ((Module.finrank K L) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := K) (M := L)).ne'
    push_cast
    field_simp)))
  have nativeSource151 (k : ℕ) (v : Fin k → (ι → K)) :
      exteriorPower.plucker k (fun l ↦ algebraMap K L ∘ v l) =
        algebraMap K L ∘ exteriorPower.plucker k v := by
    classical
    funext t
    simp only [Function.comp_apply, exteriorPower.plucker, Module.Basis.equivFun_apply,
      exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    rw [RingHom.map_det]
    rfl
  have hp : plucker k (fun l ↦ algebraMap K L ∘ v l) = algebraMap K L ∘ plucker k v :=
    nativeSource151 k v
  have hind : LinearIndependent L (fun l ↦ algebraMap K L ∘ v l) := by
    by_contra hcon
    letI : Module.Free L (⋀[L]^k (ι → L)) := Module.Free.of_divisionRing L (⋀[L]^k (ι → L))
    letI : IsTorsionFree L (⋀[L]^k (ι → L)) := Module.Free.instIsTorsionFree L (⋀[L]^k (ι → L))
    have hιZero : exteriorPower.ιMulti L k (fun l ↦ algebraMap K L ∘ v l) = 0 :=
      AlternatingMap.map_linearDependent _ _ hcon
    have h0 : plucker k (fun l ↦ algebraMap K L ∘ v l) = 0 := by
      rw [exteriorPower.plucker, hιZero, map_zero]
    rw [hp] at h0
    exact nativeSource27 hv (funext fun s ↦ FaithfulSMul.algebraMap_injective K L
      (by simpa using congrFun h0 s))
  rw [nativeSource29L hind, nativeSource29 hv, hp]
  exact nativeSource109 (plucker k v)

end Height

end Submodule

namespace Matrix

section Relative

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [NumberField K] [NumberField F] [NumberField L] [Algebra K F] [Algebra K L]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m r : ℕ}

set_option maxHeartbeats 4000000 in
/-- **2.9.8 over a finite extension, with the conjugates given.** -/
theorem arakelovMulHeight_span_restrictScalars_rpow_le
    (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L)) (hM : IsUnit (embMatrix e σ).det)
    (A : Matrix (Fin m) ι F) :
    (Submodule.span K (Set.range (restrictScalars e A).row)).arakelovMulHeight
        ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
  have hnonnegF (x : ι → F) : 0 ≤ NumberField.arakelovMulHeight x := by
    classical
    unfold NumberField.arakelovMulHeight
    split_ifs
    · norm_num
    · exact mul_nonneg
        (Finset.prod_nonneg fun v _ =>
          Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _)
        (finprod_nonneg fun v => Real.iSup_nonneg fun i => apply_nonneg _ _)
  have hnonnegL (x : ι → L) : 0 ≤ NumberField.arakelovMulHeight x := by
    classical
    unfold NumberField.arakelovMulHeight
    split_ifs
    · norm_num
    · exact mul_nonneg
        (Finset.prod_nonneg fun v _ =>
          Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _)
        (finprod_nonneg fun v => Real.iSup_nonneg fun i => apply_nonneg _ _)
  have nativeSource109 := (open Function IntermediateField Module in (fun (f : F →+* L) (x : ι → F) => (show NumberField.arakelovMulHeight (f ∘ x) ^ ((Module.finrank ℚ L : ℝ))⁻¹
        = NumberField.arakelovMulHeight x ^ ((Module.finrank ℚ F : ℝ))⁻¹ from by
    classical
    letI : Module.Free ℚ F := Module.Free.of_divisionRing ℚ F
    letI : IsTorsionFree ℚ F := Module.Free.instIsTorsionFree ℚ F
    let : Algebra F L := f.toAlgebra
    letI : Module.Free F L := Module.Free.of_divisionRing F L
    letI : IsTorsionFree F L := Module.Free.instIsTorsionFree F L
    have : IsScalarTower ℚ F L :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Module.Finite F L := Module.Finite.of_restrictScalars_finite ℚ F L
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ F L
    have hkey : NumberField.arakelovMulHeight x ^ Module.finrank F L = NumberField.arakelovMulHeight (f ∘ x) := by
      simpa [RingHom.algebraMap_toAlgebra] using
        NumberField.arakelovMulHeight_pow_finrank (K := F) (L := L) x
    rw [← hkey, ← hmul]
    rw [← Real.rpow_natCast (NumberField.arakelovMulHeight x) (Module.finrank F L), ← Real.rpow_mul (hnonnegF x)]
    congr 1
    have hm' : ((Module.finrank ℚ F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := F)).ne'
    have hn' : ((Module.finrank F L) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := F) (M := L)).ne'
    push_cast
    field_simp)))
  have hspanNonneg (V : Submodule L (ι → L)) : 0 ≤ V.arakelovMulHeight := by
    let p := V.pluckerPoint rfl
    change 0 ≤ Projectivization.projectiveArakelovMulHeight p
    rw [← p.mk_rep, (fun {x : _ → _} hx ↦
      (show Projectivization.projectiveArakelovMulHeight
        (Projectivization.mk _ x hx) = NumberField.arakelovMulHeight x from rfl))]
    classical
    unfold NumberField.arakelovMulHeight
    split_ifs
    · norm_num
    · exact mul_nonneg
        (Finset.prod_nonneg fun v _ =>
          Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _)
        (finprod_nonneg fun v => Real.iSup_nonneg fun i => apply_nonneg _ _)
  set B := restrictScalars e A with hBdef
  set W := Submodule.span K (Set.range B.row) with hWdef
  set b := Module.finBasis K W with hbdef
  set v : Fin (finrank K W) → (ι → K) := fun l ↦ ((b l : ι → K)) with hvdef
  have hvind : LinearIndependent K v := by
    change LinearIndependent K (W.subtype ∘ ⇑b)
    exact b.linearIndependent.map' W.subtype W.ker_subtype
  have hvspan : Submodule.span K (Set.range v) = W := by
    change Submodule.span K (Set.range (W.subtype ∘ ⇑b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hbc : Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)
      = Submodule.span L (Set.range (B.map (algebraMap K L)).row) :=
    Submodule.span_range_comp_algebraMap_eq (v := v) (w := B.row) (by rw [hvspan])
  calc W.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹
      = (Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)).arakelovMulHeight
          ^ (finrank ℚ L : ℝ)⁻¹ := by
        rw [Submodule.arakelovMulHeight_span_range_comp_algebraMap_rpow hvind, hvspan]
    _ = (Submodule.span L (Set.range (conjugate σ A).row)).arakelovMulHeight
          ^ (finrank ℚ L : ℝ)⁻¹ := by rw [hbc, span_range_row_conjugate e σ hM]
    _ ≤ (∏ p, NumberField.arakelovMulHeight (conjugate σ A p)) ^ (finrank ℚ L : ℝ)⁻¹ :=
        Real.rpow_le_rpow (hspanNonneg _)
          (Submodule.arakelovMulHeight_span_range_le_prod _) (by positivity)
    _ = ∏ p, NumberField.arakelovMulHeight (conjugate σ A p) ^ (finrank ℚ L : ℝ)⁻¹ :=
        (Real.finsetProd_rpow _ _ (fun p _ ↦ hnonnegL _) _).symm
    _ = ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        have hstep : ∀ t : Fin r,
            NumberField.arakelovMulHeight (conjugate σ A (i, t)) ^ (finrank ℚ L : ℝ)⁻¹
              = NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹ := fun t ↦
          nativeSource109 (σ t).toRingHom (A i)
        rw [Finset.prod_congr rfl fun t _ ↦ hstep t, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

end Relative

section Exists

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m r : ℕ}

open IntermediateField in
/-- **2.9.8 over a finite extension** (Bombieri–Gubler, inside the proof of Theorem 2.9.19): the
absolute Arakelov height of the row space of the restricted system is at most the product of the
`r`-th powers of the absolute Arakelov heights of the rows of `A`. The field carrying the
conjugates is constructed in the proof. -/
theorem arakelovMulHeight_span_restrictScalars_rpow_le'
    (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) :
    (Submodule.span K (Set.range (restrictScalars e A).row)).arakelovMulHeight
        ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
  classical
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hcard : Fintype.card (F →ₐ[K] AlgebraicClosure K) = r := by
    rw [AlgHom.card K F (AlgebraicClosure K), Module.finrank_eq_card_basis e, Fintype.card_fin]
  let τ : Fin r ≃ (F →ₐ[K] AlgebraicClosure K) := (Fintype.equivFinOfCardEq hcard).symm
  have hfr : ∀ i : Fin r, FiniteDimensional K ↥((τ i).fieldRange) := fun i ↦
    (AlgEquiv.ofInjectiveField (τ i)).toLinearEquiv.finiteDimensional
  let L : IntermediateField K (AlgebraicClosure K) := ⨆ i : Fin r, (τ i).fieldRange
  have : FiniteDimensional K ↥L := inferInstance
  have : IsScalarTower ℚ K ↥L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ ↥L := Module.Finite.trans K ↥L
  have : NumberField ↥L := ⟨⟩
  let σ : Fin r → (F →ₐ[K] ↥L) := fun i ↦ (τ i).codRestrict L.toSubalgebra
    (fun x ↦ le_iSup (fun i : Fin r ↦ ((τ i).fieldRange : IntermediateField K _)) i ⟨x, rfl⟩)
  have hσ : ∀ i x, algebraMap ↥L (AlgebraicClosure K) (σ i x) = τ i x := fun i x ↦ rfl
  have hdet : (embMatrix e τ).det ≠ 0 := by
    have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K (AlgebraicClosure K) (⇑e) τ
    have hd : Algebra.discr K (⇑e) ≠ 0 := Algebra.discr_not_zero_of_basis K e
    have ht : embMatrix e τ
        = (Algebra.embeddingsMatrixReindex K (AlgebraicClosure K) (⇑e) τ)ᵀ := by
      ext u t
      simp [embMatrix, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [ht, Matrix.det_transpose]
    intro h0
    rw [h0] at h2
    exact hd ((map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).1
      (by simpa using h2))
  have hM : IsUnit (embMatrix e σ).det := by
    have hmap : (embMatrix e σ).map (algebraMap ↥L (AlgebraicClosure K)) = embMatrix e τ := by
      ext u t
      simp [embMatrix, hσ]
    have hval : algebraMap ↥L (AlgebraicClosure K) (embMatrix e σ).det = (embMatrix e τ).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
    refine isUnit_iff_ne_zero.2 fun h0 ↦ hdet ?_
    rw [← hval, h0, map_zero]
  exact arakelovMulHeight_span_restrictScalars_rpow_le e σ hM A

end Exists

end Matrix

end
