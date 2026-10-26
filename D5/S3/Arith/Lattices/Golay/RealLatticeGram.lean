/- GID: D5/S3/Arith/Lattices/Golay/RealLatticeGram
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/RealLatticeGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An even positive selfdual real lattice yields integral charge coordinates and a unimodular Gram form. -/

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality



open scoped BigOperators

namespace LinearMap.BilinForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A selfdual integer span has an integral Gram matrix with unit determinant.
The integer inverse is obtained from the coordinates of the bilinear dual basis. -/
theorem selfdual_span_gram_isUnit_det
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (B : LinearMap.BilinForm K (Fin n → K))
    (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (b : Module.Basis (Fin n) K (Fin n → K))
    (hself : B.dualSubmodule (Submodule.span ℤ (Set.range b)) =
      Submodule.span ℤ (Set.range b))
    (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, (G i j : K) = B (b i) (b j)) :
    IsUnit G.det := by
  classical
  let d : Module.Basis (Fin n) K (Fin n → K) := B.dualBasis hB b
  have hd (j : Fin n) : d j ∈ Submodule.span ℤ (Set.range b) := by
    rw [← hself, B.dualSubmodule_span_of_basis hB b]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hcoord (i j : Fin n) : ∃ z : ℤ, (z : K) = b.repr (d j) i := by
    exact (b.mem_span_iff_repr_mem ℤ (d j)).mp (hd j) i
  let H : Matrix (Fin n) (Fin n) ℤ := fun i j => Classical.choose (hcoord i j)
  have hH (i j : Fin n) : (H i j : K) = b.repr (d j) i :=
    Classical.choose_spec (hcoord i j)
  have hexpand (j : Fin n) : (∑ k, (H k j : K) • b k) = d j := by
    simpa only [hH] using b.sum_repr (d j)
  have hGH (i j : Fin n) :
      (∑ k, (G i k : K) * (H k j : K)) = if i = j then 1 else 0 := by
    calc
      _ = ∑ k, B (b i) ((H k j : K) • b k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hG i k, B.smul_right, mul_comm]
      _ = B (b i) (∑ k, (H k j : K) • b k) := by rw [map_sum]
      _ = B (b i) (d j) := by rw [hexpand j]
      _ = if i = j then 1 else 0 := B.apply_dualBasis_right hB hSymm b i j
  have hinv : G * H = 1 := by
    ext i j
    apply (Int.cast_injective (α := K))
    simpa only [Matrix.mul_apply, Matrix.one_apply, Int.cast_sum, Int.cast_mul,
      apply_ite, Int.cast_one, Int.cast_zero] using hGH i j
  exact Matrix.isUnit_det_of_right_inverse hinv

end LinearMap.BilinForm

namespace D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

/-- Realize a positive even selfdual real lattice by its integral Gram matrix
and its actual integer charge coordinates. The chosen integer basis is extended
over ℝ; the same form `B` supplies every pairing, without a normalization change.
There is no positive-rank hypothesis, so the statement also includes `n = 0`.
Concrete lattice membership, evenness and selfduality must be proved separately
before this construction can be applied to the real image of the Leech lattice. -/
theorem exists_latticeData_of_real_selfdual
    {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (B : LinearMap.BilinForm ℝ (Fin n → ℝ))
    (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < B x x)
    (hself : B.dualSubmodule L = L)
    (heven : ∀ x : L, ∃ z : ℤ, B (x : Fin n → ℝ) (x : Fin n → ℝ) =
      (2 : ℝ) * (z : ℝ)) :
    ∃ (D : LatticeData) (b : Module.Basis (Fin D.rank) ℤ L)
      (e : Charge D ≃ₗ[ℤ] L),
      D.rank = n ∧
      IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      e = b.equivFun.symm ∧
      (∀ i j, (D.G i j : ℝ) =
        B ((Module.Basis.ofZLatticeBasis (K := ℝ) (L := L) (b := b)) i)
          ((Module.Basis.ofZLatticeBasis (K := ℝ) (L := L) (b := b)) j)) ∧
      (∀ a : Charge D, (e a : Fin n → ℝ) =
        (Module.Basis.ofZLatticeBasis (K := ℝ) (L := L) (b := b)).equivFun.symm
          (fun i => (a i : ℝ))) ∧
      (∀ a c : Charge D, (bilinear D a c : ℝ) =
        B (e a : Fin n → ℝ) (e c : Fin n → ℝ)) := by
  classical
  let b : Module.Basis (Fin n) ℤ L := IsZLattice.basis L
  let bR : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
    Module.Basis.ofZLatticeBasis (K := ℝ) (L := L) (b := b)
  have hbR (i : Fin n) : bR i = (b i : Fin n → ℝ) := by
    exact Module.Basis.ofZLatticeBasis_apply (K := ℝ) (L := L) (b := b) i
  have hspan : Submodule.span ℤ (Set.range bR) = L := by
    exact Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := b)
  have hintegral (i j : Fin n) :
      ∃ z : ℤ, (z : ℝ) = B (bR i) (bR j) := by
    have hi : bR i ∈ B.dualSubmodule L := by
      rw [hself, hbR i]
      exact (b i).property
    have hj : bR j ∈ L := by
      rw [hbR j]
      exact (b j).property
    simpa using (Submodule.mem_one.mp
      ((B.mem_dualSubmodule.mp hi) (bR j) hj))
  let G : Matrix (Fin n) (Fin n) ℤ :=
    fun i j => Classical.choose (hintegral i j)
  have hG (i j : Fin n) : (G i j : ℝ) = B (bR i) (bR j) :=
    Classical.choose_spec (hintegral i j)
  have hunit : IsUnit G.det :=
    B.selfdual_span_gram_isUnit_det hB hSymm bR
      (by rw [hspan]; exact hself) G hG
  have hsym (i j : Fin n) : G i j = G j i := by
    apply (Int.cast_injective (α := ℝ))
    rw [hG i j, hG j i]
    exact hSymm.eq _ _
  have hevenG (i : Fin n) : Even (G i i) := by
    obtain ⟨z, hz⟩ := heven (b i)
    refine ⟨z, ?_⟩
    apply (Int.cast_injective (α := ℝ))
    calc
      (G i i : ℝ) = B (bR i) (bR i) := hG i i
      _ = (2 : ℝ) * (z : ℝ) := by simpa only [hbR] using hz
      _ = ((z + z : ℤ) : ℝ) := by simp only [Int.cast_add, two_mul]
  have hexpand (u v : Fin n → ℝ) :
      B (∑ i, u i • bR i) (∑ j, v j • bR j) =
        ∑ i, ∑ j, u i * (G i j : ℝ) * v j := by
    calc
      _ = ∑ i, B (u i • bR i) (∑ j, v j • bR j) :=
        LinearMap.map_sum₂ B Finset.univ (fun i => u i • bR i) _
      _ = ∑ i, ∑ j, B (u i • bR i) (v j • bR j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact map_sum (B (u i • bR i)) _ _
      _ = ∑ i, ∑ j, u i * (G i j : ℝ) * v j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [B.smul_left, B.smul_right, ← hG i j]
        ring
  have hpairR (u v : Fin n → ℝ) :
      B (bR.equivFun.symm u) (bR.equivFun.symm v) =
        ∑ i, ∑ j, u i * (G i j : ℝ) * v j := by
    simpa only [Module.Basis.equivFun_symm_apply] using hexpand u v
  have hposG : (G.map (Int.castRingHom ℝ)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j
      simpa using congrArg (fun z : ℤ => (z : ℝ)) (hsym j i)
    · intro u hu
      have hne : bR.equivFun.symm u ≠ 0 := by
        intro hz
        apply hu
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using
          congrArg bR.equivFun hz
      have hp := hpos (bR.equivFun.symm u) hne
      rw [hpairR u u] at hp
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hp
  let e : (Fin n → ℤ) ≃ₗ[ℤ] L := b.equivFun.symm
  have heR (a : Fin n → ℤ) : (e a : Fin n → ℝ) =
      bR.equivFun.symm (fun i => (a i : ℝ)) := by
    calc
      (e a : Fin n → ℝ) = L.subtype (b.equivFun.symm a) := rfl
      _ = ∑ i, L.subtype (a i • b i) := by
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      _ = ∑ i, (a i : ℝ) • bR i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        change a i • (b i : Fin n → ℝ) = (a i : ℝ) • bR i
        rw [hbR i]
        exact (Int.cast_smul_eq_zsmul ℝ (a i) (b i : Fin n → ℝ)).symm
      _ = bR.equivFun.symm (fun i => (a i : ℝ)) :=
        (bR.equivFun_symm_apply _).symm
  let D : LatticeData := {
    rank := n
    G := G
    symmetric := hsym
    even_diagonal := hevenG }
  refine ⟨D, b, e, rfl, hunit, hposG, rfl, hG, heR, ?_⟩
  intro a c
  change ((∑ i, ∑ j, a i * G i j * c j : ℤ) : ℝ) =
    B (e a : Fin n → ℝ) (e c : Fin n → ℝ)
  rw [heR a, heR c, hpairR]
  simp only [Int.cast_sum, Int.cast_mul]
  rfl

end D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

#print axioms LinearMap.BilinForm.selfdual_span_gram_isUnit_det
#print axioms D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.exists_latticeData_of_real_selfdual
