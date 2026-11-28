/- GID: D5/S3/HilbertOperators/BlecherNoAnticommutingPair
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/BlecherNoAnticommutingPair
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim; result=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result; claim=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim
   digest: A finite symmetric operator algebra excludes nonzero anticommuting products. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.LinearCombination

/-! A symmetric operator algebra answering the question in Blecher, Example 5.5
(arXiv:2509.17673v2). Its multiplication is the unconjugated outer product of
the row coordinates, with the product in a two-sided annihilator. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

noncomputable section
namespace D5.S3.HilbertOperators.BlecherNoAnticommutingPair

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-- The necessity of a nonzero anticommuting product in a noncommutative symmetric
matrix algebra, at ambient size sixteen. -/
def claim : Prop :=
  ∀ A : Submodule ℂ (Matrix (Fin 16) (Fin 16) ℂ),
    (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) →
    (∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) →
    (∀ k (x : Matrix (Fin k) (Fin k) (Matrix (Fin 16) (Fin 16) ℂ)),
      (∀ i j, x i j ∈ A) →
      ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖) →
    ∃ x ∈ A, ∃ y ∈ A, x * y = -(y * x) ∧ x * y ≠ 0

private abbrev Coordinates := (Fin 2 → ℂ) × Matrix (Fin 2) (Fin 2) ℂ

-- The entries of I, D₁, P₁₂ and R₁₂, in row-major order.
private def probes (t : Fin 4) : Fin 4 → ℂ :=
  ![![1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 1, 1, 0], ![0, -1, 1, 0]] t

private def block (t : Fin 4) (x : Coordinates) : Matrix (Fin 4) (Fin 4) ℂ :=
  let r := x.1
  let z := x.2
  let j := probes t
  !![0, r 0, r 1, j 0 * z 0 0 + j 1 * z 0 1 + j 2 * z 1 0 + j 3 * z 1 1;
     0, 0, 0, j 0 * r 0 + j 1 * r 1;
     0, 0, 0, j 2 * r 0 + j 3 * r 1;
     0, 0, 0, 0]

private def blockMap (t : Fin 4) : Coordinates →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := block t
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [block, mul_add] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [block] <;> ring

private lemma block_mul (t : Fin 4) (x y : Coordinates) :
    block t x * block t y = block t (0, vecMulVec x.1 y.1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec_apply]
  ring

private def flipBlock (t : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  let j := probes t
  !![0, 0, 0, 1; 0, j 0, j 1, 0; 0, j 2, j 3, 0; 1, 0, 0, 0]

private lemma flipBlock_unitary (t : Fin 4) :
    flipBlock t ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := by
  constructor <;> ext i j <;> fin_cases t <;> fin_cases i <;> fin_cases j <;>
    simp [flipBlock, probes, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma flipBlock_transpose (t : Fin 4) (x : Coordinates) :
    flipBlock t * (block t x)ᵀ * flipBlock t = block t x := by
  ext i j
  fin_cases t <;> fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ];
      simp [flipBlock, block, probes])

private def index : Fin 4 × Fin 4 ≃ Fin 16 := finProdFinEquiv

private def assembled : Coordinates →ₗ[ℂ] Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ where
  toFun x := blockDiagonal fun t => blockMap t x
  map_add' x y := by
    rw [← blockDiagonal_add]
    congr
    funext t
    exact map_add (blockMap t) x y
  map_smul' c x := by
    ext i j
    by_cases h : i.2 = j.2
    · simp [blockDiagonal_apply, h, Matrix.smul_apply]
    · simp [blockDiagonal_apply, h, Matrix.smul_apply]

private def representation : Coordinates →ₗ[ℂ] Matrix (Fin 16) (Fin 16) ℂ :=
  (reindexAlgEquiv ℂ ℂ index).toLinearMap.comp assembled

private lemma representation_mul (x y : Coordinates) :
    representation x * representation y = representation (0, vecMulVec x.1 y.1) := by
  change reindexAlgEquiv ℂ ℂ index (blockDiagonal fun t => block t x) *
    reindexAlgEquiv ℂ ℂ index (blockDiagonal fun t => block t y) = _
  rw [← map_mul, ← blockDiagonal_mul]
  simp only [block_mul]
  rfl

private lemma representation_injective : Function.Injective representation := by
  intro x y h
  have blocks (t i j : Fin 4) : block t x i j = block t y i j := by
    have h' : (blockDiagonal fun t => block t x) = (blockDiagonal fun t => block t y) :=
      (reindexAlgEquiv ℂ ℂ index).injective h
    simpa only [blockDiagonal_apply_eq] using
      congrArg (fun a : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ => a (i,t) (j,t)) h'
  apply Prod.ext
  · funext i
    fin_cases i
    · exact blocks 0 0 1
    · exact blocks 0 0 2
  · have hI := blocks 0 0 3
    have hD := blocks 1 0 3
    have hP := blocks 2 0 3
    have hR := blocks 3 0 3
    simp [block, probes] at hI hD hP hR
    ext i j
    fin_cases i <;> fin_cases j
    · change x.2 0 0 = y.2 0 0
      linear_combination (hI - hD) / 2
    · change x.2 0 1 = y.2 0 1
      linear_combination (hP - hR) / 2
    · change x.2 1 0 = y.2 1 0
      linear_combination (hP + hR) / 2
    · change x.2 1 1 = y.2 1 1
      linear_combination (hI + hD) / 2

private def flip : Matrix (Fin 16) (Fin 16) ℂ :=
  reindexAlgEquiv ℂ ℂ index (blockDiagonal flipBlock)

private lemma flip_unitary : flip ∈ unitary (Matrix (Fin 16) (Fin 16) ℂ) := by
  have hstar (M : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :
      star (reindexAlgEquiv ℂ ℂ index M) = reindexAlgEquiv ℂ ℂ index (star M) := rfl
  constructor <;>
    simp only [flip, hstar, ← map_mul, ← map_one (reindexAlgEquiv ℂ ℂ index)]
  all_goals
    apply congrArg (reindexAlgEquiv ℂ ℂ index)
    simp only [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    rw [← blockDiagonal_one]
    congr
    funext t
    first | exact (flipBlock_unitary t).1 | exact (flipBlock_unitary t).2

private lemma flip_transpose (x : Coordinates) :
    flip * (representation x)ᵀ * flip = representation x := by
  have htranspose (M : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :
      (reindexAlgEquiv ℂ ℂ index M)ᵀ = reindexAlgEquiv ℂ ℂ index (Mᵀ) := rfl
  change reindexAlgEquiv ℂ ℂ index (blockDiagonal flipBlock) *
    (reindexAlgEquiv ℂ ℂ index (blockDiagonal fun t => block t x))ᵀ *
    reindexAlgEquiv ℂ ℂ index (blockDiagonal flipBlock) = _
  rw [htranspose, ← map_mul, ← map_mul, blockDiagonal_transpose,
    ← blockDiagonal_mul, ← blockDiagonal_mul]
  simp only [flipBlock_transpose]
  rfl

private lemma amplified_norm (k : ℕ)
    (x : Matrix (Fin k) (Fin k) (Matrix (Fin 16) (Fin 16) ℂ))
    (hx : ∀ i j, x i j ∈ LinearMap.range representation) :
    ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖ := by
  let W := compRingEquiv (Fin k) (Fin 16) ℂ
  let D : Matrix (Fin k) (Fin k) (Matrix (Fin 16) (Fin 16) ℂ) := diagonal fun _ => flip
  have hD : W D ∈ unitary (Matrix (Fin k × Fin 16) (Fin k × Fin 16) ℂ) := by
    have hstar : star (W D) = W (diagonal fun _ => star flip) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      by_cases h : i = j
      · subst j
        simp [W, D, Matrix.star_apply, comp_apply]
      · simp [W, D, Matrix.star_apply, comp_apply, h, Ne.symm h]
    constructor <;> rw [hstar, ← map_mul, ← map_one W] <;> congr 1 <;>
      simp [D, diagonal_mul_diagonal, flip_unitary.1, flip_unitary.2, ← Matrix.diagonal_one]
  have hflip : W D * W (of (fun i j => (x i j)ᵀ)) * W D = W x := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Matrix.ext
    intro i j
    rw [mul_diagonal, diagonal_mul]
    obtain ⟨z, hz⟩ := hx i j
    change flip * (x i j)ᵀ * flip = x i j
    rw [← hz, flip_transpose]
  change ‖W (of (fun i j => (x i j)ᵀ))‖ = ‖W x‖
  rw [← hflip, CStarRing.norm_mul_mem_unitary _ hD, CStarRing.norm_mem_unitary_mul _ hD]

private lemma outer_eq_neg_swapped {r s : Fin 2 → ℂ}
    (h : vecMulVec r s = -(vecMulVec s r)) : vecMulVec r s = 0 := by
  by_cases hr : r = 0
  · simp [hr]
  have ⟨i, hi⟩ : ∃ i, r i ≠ 0 := Function.ne_iff.mp hr
  have entry (i j : Fin 2) : r i * s j = -(s i * r j) :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) h
  have hdiag : (2 : ℂ) * (r i * s i) = 0 := by
    linear_combination entry i i
  have hsi : s i = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hdiag).resolve_left (by norm_num))).resolve_left hi
  have hs : s = 0 := by
    funext j
    exact (mul_eq_zero.mp (by simpa [hsi] using entry i j)).resolve_left hi
  simp [hs]

private lemma faithfulCounterexample :
    ∃ ρ : Coordinates →ₗ[ℂ] Matrix (Fin 16) (Fin 16) ℂ,
      Function.Injective ρ ∧
      (∀ x y, ρ x * ρ y = ρ (0, vecMulVec x.1 y.1)) ∧
      (∃ x ∈ LinearMap.range ρ, ∃ y ∈ LinearMap.range ρ, x * y ≠ y * x) ∧
      (∀ x ∈ LinearMap.range ρ, ∀ y ∈ LinearMap.range ρ, x * y = -(y * x) → x * y = 0) ∧
      (∀ k (x : Matrix (Fin k) (Fin k) (Matrix (Fin 16) (Fin 16) ℂ)),
        (∀ i j, x i j ∈ LinearMap.range ρ) →
        ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖) := by
  refine ⟨representation, representation_injective, representation_mul, ?_, ?_, amplified_norm⟩
  · let x : Coordinates := (![1, 0], 0)
    let y : Coordinates := (![0, 1], 0)
    refine ⟨representation x, ⟨x, rfl⟩, representation y, ⟨y, rfl⟩, ?_⟩
    intro h
    rw [representation_mul, representation_mul] at h
    have h' := congrArg (fun z : Coordinates => z.2 0 1) (representation_injective h)
    norm_num [x, y, vecMulVec_apply] at h'
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    rw [representation_mul, representation_mul, ← map_neg] at h
    have h' := congrArg Prod.snd (representation_injective h)
    rw [representation_mul, outer_eq_neg_swapped h']
    exact map_zero representation

/-- A noncommutative symmetric operator algebra in sixteen dimensions whose
anticommuting pairs all have zero product. -/
theorem result : ¬ claim := by
  intro necessity
  obtain ⟨ρ, _, hmul, hnc, hzero, hnorm⟩ := faithfulCounterexample
  have hclosed : ∀ x ∈ LinearMap.range ρ, ∀ y ∈ LinearMap.range ρ,
      x * y ∈ LinearMap.range ρ := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨_, (hmul x y).symm⟩
  obtain ⟨x, hx, y, hy, hxy, hnonzero⟩ := necessity _ hclosed hnc hnorm
  exact hnonzero (hzero x hx y hy hxy)

end D5.S3.HilbertOperators.BlecherNoAnticommutingPair
