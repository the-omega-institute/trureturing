/- GID: D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/WeightedCycleKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Cyclic first-order transport has a one-dimensional kernel precisely when its edge product is one. -/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
open scoped BigOperators Fin.NatCast Classical
open Matrix Module
universe u
variable {K : Type u} [Field K]

/-- Partial product along the cyclic order, before closing the last edge. -/
def initialProduct {n : ℕ} (r : Fin (n + 1) → K) (k : ℕ) : K :=
  ∏ j ∈ Finset.range k, r (j : Fin (n + 1))

/-- The linear transport defect around a labelled cycle. -/
def transport {n : ℕ} (r : Fin (n + 1) → K) :
    (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun x i := x (finRotate (n + 1) i) - r i * x i
  map_add' x y := by ext i; simp; ring
  map_smul' c x := by ext i; simp; ring

private theorem prefix_succ {n : ℕ} (r : Fin (n + 1) → K) (k : ℕ) :
    initialProduct r (k + 1) = initialProduct r k * r (k : Fin (n + 1)) := by
  exact Finset.prod_range_succ _ _

private theorem coordinate {n : ℕ} (r : Fin (n + 1) → K)
    (x : Fin (n + 1) → K) (hx : transport r x = 0) :
    ∀ k ≤ n, x (k : Fin (n + 1)) = initialProduct r k * x 0 := by
  intro k hk
  induction k with
  | zero => simp [initialProduct]
  | succ k ih =>
    have h := congrFun hx (k : Fin (n + 1))
    change x (finRotate (n + 1) (k : Fin (n + 1))) -
      r (k : Fin (n + 1)) * x (k : Fin (n + 1)) = 0 at h
    rw [finRotate_apply] at h
    have he : ((k : Fin (n + 1)) + 1) = ((k + 1 : ℕ) : Fin (n + 1)) := by
      simp
    rw [he] at h
    rw [sub_eq_zero] at h
    rw [h, ih (by omega), prefix_succ]
    ring

private theorem prefix_full {n : ℕ} (r : Fin (n + 1) → K) :
    initialProduct r (n + 1) = ∏ i, r i := by
  simpa [initialProduct] using (Fin.prod_univ_eq_prod_range (fun j : ℕ => r (j : Fin (n + 1))) (n + 1)).symm

private theorem closing {n : ℕ} (r : Fin (n + 1) → K)
    (x : Fin (n + 1) → K) (hx : transport r x = 0) :
    x 0 = (∏ i, r i) * x 0 := by
  have h := congrFun hx (Fin.last n)
  change x (finRotate (n + 1) (Fin.last n)) - r (Fin.last n) * x (Fin.last n) = 0 at h
  rw [finRotate_last, sub_eq_zero] at h
  have he : (n : Fin (n + 1)) = Fin.last n := by ext; simp
  rw [← he, coordinate r x hx n le_rfl] at h
  rw [← prefix_full, prefix_succ]
  convert h using 1 <;> ring

private theorem prefix_solution {n : ℕ} (r : Fin (n + 1) → K)
    (hr : ∏ i, r i = 1) : transport r (fun i => initialProduct r i.val) = 0 := by
  ext i
  change initialProduct r (finRotate (n + 1) i).val - r i * initialProduct r i.val = 0
  by_cases hi : i = Fin.last n
  · subst i
    rw [finRotate_last]
    have h := prefix_full r
    rw [hr, prefix_succ] at h
    simp only [Fin.val_zero, Fin.val_last, initialProduct, Finset.range_zero, Finset.prod_empty]
    have he : (n : Fin (n + 1)) = Fin.last n := by ext; simp
    rw [he] at h
    change 1 - r (Fin.last n) * initialProduct r n = 0
    rw [mul_comm, h, sub_self]
  · rw [coe_finRotate_of_ne_last hi, prefix_succ]
    simp [mul_comm]

/-- A cyclic transport equation has nullity one exactly when its holonomy is one.
The entries of r need not be nonzero. -/
theorem transport_nullity {n : ℕ} (r : Fin (n + 1) → K) :
    finrank K (LinearMap.ker (transport r)) = if ∏ i, r i = 1 then 1 else 0 := by
  classical
  let ev : LinearMap.ker (transport r) →ₗ[K] K :=
    (LinearMap.proj 0).comp (LinearMap.ker (transport r)).subtype
  have hinj : Function.Injective ev := by
    intro x y h
    apply Subtype.ext
    funext i
    have hxi := coordinate r x x.property i.val (by omega)
    have hyi := coordinate r y y.property i.val (by omega)
    simp only [Fin.cast_val_eq_self] at hxi hyi
    change x.val 0 = y.val 0 at h
    rw [hxi, hyi, h]
  have hle : finrank K (LinearMap.ker (transport r)) ≤ 1 := by
    simpa using ev.finrank_le_finrank_of_injective hinj
  split_ifs with hr
  · have hpos : 0 < finrank K (LinearMap.ker (transport r)) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      refine ⟨⟨fun i => initialProduct r i.val, prefix_solution r hr⟩, ?_⟩
      intro h
      have h0 := congrArg (fun x : LinearMap.ker (transport r) => x.val 0) h
      simpa [initialProduct] using h0
    omega
  · have hk : LinearMap.ker (transport r) = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      change x = 0
      have hc := closing r x hx
      have hz : x 0 = 0 := by
        have hm : ((∏ i, r i) - 1) * x 0 = 0 := by
          rw [sub_mul, one_mul, ← hc, sub_self]
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hr)
      ext i
      have hh := coordinate r x hx i.val (by omega)
      simpa [hz] using hh
    simp [hk]

/-- Two nonzero edge families between consecutive parity classes of an even cycle. -/
def cyclicBidiagonal {n : ℕ} (a b : Fin (n + 1) → K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => (if j = i then a i else 0) +
    (if j = finRotate (n + 1) i then b i else 0)

private theorem bidiagonal_mulVec {n : ℕ} (a b x : Fin (n + 1) → K) (i : Fin (n + 1)) :
    ((cyclicBidiagonal a b) *ᵥ x) i = a i * x i + b i * x (finRotate (n + 1) i) := by
  classical
  simp [Matrix.mulVec, dotProduct, cyclicBidiagonal, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq']

private theorem bidiagonal_kernel {n : ℕ} [CharP K 2]
    (a b : Fin (n + 1) → K) (hb : ∀ i, b i ≠ 0) :
    LinearMap.ker (cyclicBidiagonal a b).mulVecLin =
      LinearMap.ker (transport (fun i => a i / b i)) := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  apply forall_congr'
  intro i
  rw [bidiagonal_mulVec]
  change a i * x i + b i * x (finRotate (n + 1) i) = 0 ↔
    x (finRotate (n + 1) i) - (a i / b i) * x i = 0
  rw [CharTwo.add_eq_zero, sub_eq_zero]
  constructor
  · intro h
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hb i)).mpr
    simpa only [mul_comm] using h.symm
  · intro h
    rw [h]
    field_simp [hb i]

private theorem bidiagonal_rank {n : ℕ} [CharP K 2]
    (a b : Fin (n + 1) → K) (hb : ∀ i, b i ≠ 0) :
    (cyclicBidiagonal a b).rank = if ∏ i, a i = ∏ i, b i then n else n + 1 := by
  classical
  have h := (cyclicBidiagonal a b).mulVecLin.finrank_range_add_finrank_ker
  change (cyclicBidiagonal a b).rank + _ = _ at h
  rw [bidiagonal_kernel a b hb, transport_nullity, Module.finrank_pi] at h
  have hprod : (∏ i, a i / b i) = 1 ↔ (∏ i, a i) = ∏ i, b i := by
    rw [Finset.prod_div_distrib, div_eq_one_iff_eq]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  rw [hprod, Fintype.card_fin] at h
  split_ifs at h ⊢ <;> omega

private def offDiagonalKernelEquiv {n : Type*} [Fintype n] (B : Matrix n n K) :
    LinearMap.ker (Matrix.fromBlocks 0 B Bᵀ 0).mulVecLin ≃ₗ[K]
      LinearMap.ker Bᵀ.mulVecLin × LinearMap.ker B.mulVecLin where
  toFun x :=
    (⟨x.val ∘ Sum.inl, by
      change Bᵀ *ᵥ (x.val ∘ Sum.inl) = 0
      have h : (Matrix.fromBlocks 0 B Bᵀ 0) *ᵥ x.val = 0 := x.property
      rw [Matrix.fromBlocks_mulVec] at h
      ext i
      simpa only [Matrix.zero_mulVec, zero_add, add_zero, Function.comp_def,
        Sum.elim_inr, Pi.zero_apply] using congrFun h (Sum.inr i)⟩,
     ⟨x.val ∘ Sum.inr, by
      change B *ᵥ (x.val ∘ Sum.inr) = 0
      have h : (Matrix.fromBlocks 0 B Bᵀ 0) *ᵥ x.val = 0 := x.property
      rw [Matrix.fromBlocks_mulVec] at h
      ext i
      simpa only [Matrix.zero_mulVec, zero_add, add_zero, Function.comp_def,
        Sum.elim_inl, Pi.zero_apply] using congrFun h (Sum.inl i)⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val, by
    change (Matrix.fromBlocks 0 B Bᵀ 0) *ᵥ Sum.elim x.1.val x.2.val = 0
    rw [Matrix.fromBlocks_mulVec]
    ext (i | i)
    · simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        Matrix.zero_mulVec, zero_add, add_zero, Pi.zero_apply] using
        congrFun (show B *ᵥ x.2.val = 0 from x.2.property) i
    · simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        Matrix.zero_mulVec, zero_add, add_zero, Pi.zero_apply] using
        congrFun (show Bᵀ *ᵥ x.1.val = 0 from x.1.property) i⟩
  left_inv x := by ext (i | i) <;> rfl
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' c x := rfl

private theorem offDiagonal_rank {n : Type*} [Fintype n] (B : Matrix n n K) :
    (Matrix.fromBlocks 0 B Bᵀ 0).rank = 2 * B.rank := by
  have h := (Matrix.fromBlocks 0 B Bᵀ 0).mulVecLin.finrank_range_add_finrank_ker
  change (Matrix.fromBlocks 0 B Bᵀ 0).rank + _ = _ at h
  have hk := (offDiagonalKernelEquiv B).finrank_eq
  rw [Module.finrank_prod] at hk
  rw [hk, Module.finrank_pi, Fintype.card_sum] at h
  have hb := B.mulVecLin.finrank_range_add_finrank_ker
  have hbt := Bᵀ.mulVecLin.finrank_range_add_finrank_ker
  change B.rank + _ = _ at hb
  change Bᵀ.rank + _ = _ at hbt
  rw [Module.finrank_pi] at hb hbt
  rw [Matrix.rank_transpose] at hbt
  omega

/-- The rank dichotomy on the two parity classes uses the actual two matching products. -/
theorem cyclic_bipartite_rank {n : ℕ} [CharP K 2]
    (a b : Fin (n + 1) → K) (hb : ∀ i, b i ≠ 0) :
    (Matrix.fromBlocks 0 (cyclicBidiagonal a b) (cyclicBidiagonal a b)ᵀ 0).rank =
      if ∏ i, a i = ∏ i, b i then 2 * n else 2 * (n + 1) := by
  rw [offDiagonal_rank, bidiagonal_rank a b hb]
  split_ifs <;> rfl

#print axioms transport_nullity
#print axioms cyclic_bipartite_rank

end D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
