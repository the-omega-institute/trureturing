/- GID: D5/S3/Quantum/Foundation/ComplexLocalTomography
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ComplexLocalTomography
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Dyson dimension gaps, product tomography, and two-particle exchange symmetry. -/

module

public import OmegaBuild.Commands
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-! Product tests on bipartite matrices and exchange of two identical factors. -/

compile_only_with_mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace D5.S3.Quantum.Foundation.ComplexLocalTomography

open Matrix
open scoped ComplexOrder Kronecker Matrix

/-- The diagonal contribution plus the off-diagonal contribution at index `β`. -/
def dysonDim {K : Type*} [Field K] (β d : K) : K :=
  d + (β / 2) * d * (d - 1)

/-- The bipartite dimension gap factors into one index term and four size terms. -/
theorem dyson_bipartite_dimension_gap {K : Type*} [Field K] [CharZero K]
    (β d₁ d₂ : K) :
    dysonDim β (d₁ * d₂) - dysonDim β d₁ * dysonDim β d₂ =
      (β * (2 - β) / 4) * d₁ * d₂ * (d₁ - 1) * (d₂ - 1) := by
  unfold dysonDim
  field_simp
  ring

/-- In nontrivial local dimensions the dimension count is multiplicative exactly at
the classical and complex indices. -/
theorem dyson_local_tomography_iff {K : Type*} [Field K] [CharZero K]
    (β : K) (d₁ d₂ : ℕ) (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) :
    dysonDim β ((d₁ : K) * (d₂ : K)) = dysonDim β (d₁ : K) * dysonDim β (d₂ : K) ↔
      β = 0 ∨ β = 2 := by
  have hn (d : ℕ) (h : 2 ≤ d) : (d : K) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  have hm (d : ℕ) (h : 2 ≤ d) : (d : K) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show d ≠ 1 by omega)
  rw [← sub_eq_zero, dyson_bipartite_dimension_gap]
  simp [mul_eq_zero, hn d₁ h₁, hn d₂ h₂, hm d₁ h₁, hm d₂ h₂, sub_eq_zero, eq_comm (a := (2 : K))]

/-- The positive, zero, and negative ranges of the gap, with the exact real and
quaternionic gaps. -/
theorem dyson_sign_trichotomy (β : ℝ) (d₁ d₂ : ℕ) (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) :
    let gap := fun b : ℝ =>
      dysonDim b ((d₁ : ℝ) * (d₂ : ℝ)) - dysonDim b (d₁ : ℝ) * dysonDim b (d₂ : ℝ)
    (0 < gap β ↔ 0 < β ∧ β < 2) ∧
    (gap β = 0 ↔ β = 0 ∨ β = 2) ∧
    (gap β < 0 ↔ β < 0 ∨ 2 < β) ∧
    gap 1 = ((d₁ : ℝ) * ((d₁ : ℝ) - 1) / 2) * ((d₂ : ℝ) * ((d₂ : ℝ) - 1) / 2) ∧
    gap 4 = -2 * (d₁ : ℝ) * (d₂ : ℝ) * ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) := by
  dsimp only
  have hd₁ : (2 : ℝ) ≤ d₁ := by exact_mod_cast h₁
  have hd₂ : (2 : ℝ) ≤ d₂ := by exact_mod_cast h₂
  have hsize : 0 < (d₁ : ℝ) * (d₂ : ℝ) * ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
  simp_rw [dyson_bipartite_dimension_gap]
  have regroup :
      (β * (2 - β) / 4) * (d₁ : ℝ) * (d₂ : ℝ) * ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1) =
        (β * (2 - β) / 4) * ((d₁ : ℝ) * (d₂ : ℝ) * ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1)) := by
    ring
  rw [regroup]
  refine ⟨?_, ?_, ?_, by ring, by ring⟩
  · rw [mul_pos_iff_of_pos_right hsize, div_pos_iff_of_pos_right (by norm_num),
      mul_pos_iff]
    constructor
    · rintro (⟨hb, hc⟩ | ⟨hb, hc⟩) <;> (first | exact ⟨hb, by linarith⟩ | linarith)
    · rintro ⟨hb, hc⟩
      exact Or.inl ⟨hb, by linarith⟩
  · simp [mul_eq_zero, ne_of_gt hsize, sub_eq_zero, eq_comm (a := (2 : ℝ))]
  · rw [← zero_mul ((d₁ : ℝ) * (d₂ : ℝ) * ((d₁ : ℝ) - 1) * ((d₂ : ℝ) - 1)),
      mul_lt_mul_iff_of_pos_right hsize, div_lt_iff₀ (by norm_num)]
    simp only [zero_mul, mul_neg_iff]
    constructor
    · rintro (⟨_, hc⟩ | ⟨hb, _⟩)
      · exact Or.inr (by linarith)
      · exact Or.inl hb
    · rintro (hb | hb)
      · exact Or.inr ⟨hb, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩

private theorem trace_skew_mul_symmetric {ι : Type*} [Fintype ι]
    (S A : Matrix ι ι ℝ) (hS : Sᵀ = -S) (hA : Aᵀ = A) :
    (S * A).trace = 0 := by
  have h : (S * A).trace = -(S * A).trace := by
    calc
      (S * A).trace = ((S * A)ᵀ).trace := (trace_transpose _).symm
      _ = -(S * A).trace := by
        rw [transpose_mul, hS, hA, Matrix.mul_neg, trace_neg, trace_mul_comm A S]
  linarith

/-- A product of two real skew-symmetric factors is symmetric and invisible to
every product of symmetric tests. -/
theorem real_skew_kron_orthogonal_to_symmetric_products
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S₁ A : Matrix ι ι ℝ) (S₂ B : Matrix κ κ ℝ)
    (h₁ : S₁ᵀ = -S₁) (h₂ : S₂ᵀ = -S₂) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (S₁ ⊗ₖ S₂)ᵀ = S₁ ⊗ₖ S₂ ∧ ((S₁ ⊗ₖ S₂) * (A ⊗ₖ B)).trace = 0 := by
  constructor
  · change S₁ᵀ ⊗ₖ S₂ᵀ = S₁ ⊗ₖ S₂
    rw [h₁, h₂]
    ext ⟨i, k⟩ ⟨j, l⟩
    simp
  · rw [← mul_kronecker_mul, trace_kronecker,
      trace_skew_mul_symmetric S₁ A h₁ hA, trace_skew_mul_symmetric S₂ B h₂ hB, mul_zero]

/-- The two-rebit skew-tensor construction gives two orthogonal density matrices
with equal symmetric product statistics. -/
theorem two_rebit_hidden_orthogonal_states :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
    let W := J ⊗ₖ J
    let ρplus := (1 / 4 : ℝ) • (1 + W)
    let ρminus := (1 / 4 : ℝ) • (1 - W)
    Wᵀ = W ∧ W * W = 1 ∧ W.trace = 0 ∧ W ≠ 0 ∧ ρplus ≠ ρminus ∧
    ρplusᵀ = ρplus ∧ ρminusᵀ = ρminus ∧ ρplus.trace = 1 ∧ ρminus.trace = 1 ∧
    ρplus * ρminus = 0 ∧ ρplus * ρplus = (1 / 2 : ℝ) • ρplus ∧
    ρminus * ρminus = (1 / 2 : ℝ) • ρminus ∧
    ρplus.PosSemidef ∧ ρminus.PosSemidef ∧
    ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, Aᵀ = A → Bᵀ = B →
      (ρplus * (A ⊗ₖ B)).trace = (ρminus * (A ⊗ₖ B)).trace := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
  let W := J ⊗ₖ J
  let ρplus := (1 / 4 : ℝ) • (1 + W)
  let ρminus := (1 / 4 : ℝ) • (1 - W)
  have hJ : Jᵀ = -J := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [J]
  have hJJ : J * J = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have htrJ : J.trace = 0 := by norm_num [J, Matrix.trace, Fin.sum_univ_two]
  have hW : Wᵀ = W :=
    (real_skew_kron_orthogonal_to_symmetric_products J 0 J 0 hJ hJ (by simp) (by simp)).1
  have hWW : W * W = 1 := by
    change (J ⊗ₖ J) * (J ⊗ₖ J) = 1
    rw [← mul_kronecker_mul, hJJ]
    calc
      (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) ⊗ₖ (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) =
          (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext ⟨i, k⟩ ⟨j, l⟩
        simp
      _ = 1 := one_kronecker_one
  have htrW : W.trace = 0 := by simp [W, trace_kronecker, htrJ]
  have hwEntry : W (0, 0) (1, 1) = 1 := by norm_num [W, J]
  have hplus : ρplusᵀ = ρplus := by simp [ρplus, hW]
  have hminus : ρminusᵀ = ρminus := by simp [ρminus, hW]
  have hp : ρplus * ρplus = (1 / 2 : ℝ) • ρplus := by
    simp only [ρplus, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hWW]
    module
  have hm : ρminus * ρminus = (1 / 2 : ℝ) • ρminus := by
    simp only [ρminus, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hWW]
    module
  have posOfHalfSquare (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
      (hR : Rᵀ = R) (hRR : R * R = (1 / 2 : ℝ) • R) : R.PosSemidef := by
    have h := (posSemidef_conjTranspose_mul_self R).smul (show (0 : ℝ) ≤ 2 by norm_num)
    rw [conjTranspose_eq_transpose_of_trivial, hR, hRR, smul_smul] at h
    norm_num at h
    exact h
  have htrI : (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ).trace = 4 := by
    norm_num [trace_one, Fintype.card_prod]
  change Wᵀ = W ∧ W * W = 1 ∧ W.trace = 0 ∧ W ≠ 0 ∧ ρplus ≠ ρminus ∧ _
  refine ⟨hW, hWW, htrW, ?_, ?_, hplus, hminus, ?_, ?_, ?_, hp, hm,
    posOfHalfSquare ρplus hplus hp, posOfHalfSquare ρminus hminus hm, ?_⟩
  · intro h
    norm_num [h] at hwEntry
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ =>
      M (0, 0) (1, 1)) h
    norm_num [ρplus, ρminus, hwEntry, Matrix.one_apply] at he
  · change ((1 / 4 : ℝ) • (1 + W)).trace = 1
    rw [trace_smul, trace_add, htrI, htrW]
    norm_num
  · change ((1 / 4 : ℝ) • (1 - W)).trace = 1
    rw [trace_smul, trace_sub, htrI, htrW]
    norm_num
  · change ((1 / 4 : ℝ) • (1 + W)) * ((1 / 4 : ℝ) • (1 - W)) = 0
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hWW]
    module
  · intro A B hA hB
    have h := (real_skew_kron_orthogonal_to_symmetric_products J A J B hJ hJ hA hB).2
    change (W * (A ⊗ₖ B)).trace = 0 at h
    change (((1 / 4 : ℝ) • (1 + W)) * (A ⊗ₖ B)).trace =
      (((1 / 4 : ℝ) • (1 - W)) * (A ⊗ₖ B)).trace
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
      trace_smul, trace_add, trace_sub, h, add_zero, sub_zero]

/-- Hermitian factors suffice to separate all complex bipartite matrices by trace
pairing, including matrices that are themselves non-Hermitian. -/
theorem complex_local_tomography_iff {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (M₁ M₂ : Matrix (ι × κ) (ι × κ) ℂ) :
    (∀ (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), Aᴴ = A → Bᴴ = B →
      (M₁ * (A ⊗ₖ B)).trace = (M₂ * (A ⊗ₖ B)).trace) ↔ M₁ = M₂ := by
  classical
  constructor
  · intro h
    have right (A : Matrix ι ι ℂ) (hA : Aᴴ = A) (B : Matrix κ κ ℂ) :
        (M₁ * (A ⊗ₖ B)).trace = (M₂ * (A ⊗ₖ B)).trace := by
      have hR := h A (realPart B) hA (realPart B).property
      have hI := h A (imaginaryPart B) hA (imaginaryPart B).property
      rw [← realPart_add_I_smul_imaginaryPart B]
      simp only [kronecker_add, kronecker_smul, Matrix.mul_add, Matrix.mul_smul, trace_add,
        trace_smul, hR, hI]
    have both (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
        (M₁ * (A ⊗ₖ B)).trace = (M₂ * (A ⊗ₖ B)).trace := by
      have hR := right (realPart A) (realPart A).property B
      have hI := right (imaginaryPart A) (imaginaryPart A).property B
      rw [← realPart_add_I_smul_imaginaryPart A]
      simp only [add_kronecker, smul_kronecker, Matrix.mul_add, Matrix.mul_smul, trace_add,
        trace_smul, hR, hI]
    ext ⟨i, k⟩ ⟨j, l⟩
    simpa [single_kronecker_single, trace_mul_single] using
      both (single j i (1 : ℂ)) (single l k (1 : ℂ))
  · rintro rfl A B _ _
    rfl

/-- The extension of a product test to a scalar action on the dark summand. -/
def darkProductExt {ι κ γ : Type*} [Fintype ι] [Fintype κ] [DecidableEq γ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : Matrix ((ι × κ) ⊕ γ) ((ι × κ) ⊕ γ) ℂ :=
  fromBlocks (A ⊗ₖ B) 0 0
    (((A.trace / Fintype.card ι) * (B.trace / Fintype.card κ)) • (1 : Matrix γ γ ℂ))

private theorem trace_fromBlocks_diagonal {α γ : Type*} [Fintype α] [Fintype γ]
    (A : Matrix α α ℂ) (D : Matrix γ γ ℂ) :
    (fromBlocks A 0 0 D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- The unital extension keeps the visible pairing and assigns every dark basis
state the product statistics of the maximally mixed visible state. -/
theorem dark_sector_product_indistinguishable {ι κ γ : Type*}
    [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq ι] [DecidableEq κ] [DecidableEq γ]
    [Nonempty ι] [Nonempty κ] (x y : γ) (hxy : x ≠ y) :
    let E := fun z : γ => (single (Sum.inr z) (Sum.inr z) 1 :
      Matrix ((ι × κ) ⊕ γ) ((ι × κ) ⊕ γ) ℂ)
    darkProductExt (γ := γ) (1 : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ) = 1 ∧
    (∀ (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ),
      (darkProductExt (γ := γ) A B)ᴴ = darkProductExt Aᴴ Bᴴ) ∧
    (∀ (M : Matrix (ι × κ) (ι × κ) ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ),
      (fromBlocks M 0 0 (0 : Matrix γ γ ℂ) * darkProductExt A B).trace =
        (M * (A ⊗ₖ B)).trace) ∧
    E x ≠ E y ∧ (E x)ᴴ = E x ∧ (E y)ᴴ = E y ∧
    (E x).trace = 1 ∧ (E y).trace = 1 ∧ (E x).PosSemidef ∧ (E y).PosSemidef ∧
    E x * E y = 0 ∧
    ∀ (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ),
      (E x * darkProductExt A B).trace = (E y * darkProductExt A B).trace ∧
      (E x * darkProductExt A B).trace =
        (((Fintype.card ι : ℂ) * (Fintype.card κ : ℂ))⁻¹ •
          (1 : Matrix (ι × κ) (ι × κ) ℂ) * (A ⊗ₖ B)).trace := by
  dsimp only
  have hι : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hκ : (Fintype.card κ : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card κ ≠ 0)
  have psd (z : (ι × κ) ⊕ γ) :
      (single z z (1 : ℂ)).PosSemidef := by
    rw [← diagonal_single]
    exact PosSemidef.diagonal (fun i => by
      by_cases hi : i = z <;> simp [Pi.single_apply, hi])
  refine ⟨?_, ?_, ?_, ?_, by simp [conjTranspose_single], by simp [conjTranspose_single],
    trace_single_eq_same _ _, trace_single_eq_same _ _, psd _, psd _, ?_, ?_⟩
  · simp [darkProductExt, hι, hκ, fromBlocks_one]
  · intro A B
    simp [darkProductExt, fromBlocks_conjTranspose, conjTranspose_kronecker, conjTranspose_smul,
      trace_conjTranspose, star_mul, Complex.star_def, mul_comm]
  · intro M A B
    simp [darkProductExt, fromBlocks_multiply, trace_fromBlocks_diagonal]
  · intro h
    have he := congrArg (fun M : Matrix ((ι × κ) ⊕ γ) ((ι × κ) ⊕ γ) ℂ =>
      M (Sum.inr x) (Sum.inr x)) h
    simp [Matrix.single, Ne.symm hxy] at he
  · apply Matrix.single_mul_single_of_ne
    exact fun h => hxy (Sum.inr_injective h)
  · intro A B
    simp only [trace_single_mul, darkProductExt, fromBlocks_apply₂₂, Matrix.smul_apply,
      one_apply_eq, smul_eq_mul, mul_one, true_and, Matrix.smul_mul, Matrix.one_mul, trace_smul,
      trace_kronecker]
    field_simp

/-- The two exchange projections decompose the tensor square into its symmetric
and alternating parts. A repeated factor survives only in the symmetric part. -/
theorem two_particle_exchange_decomposition (ι : Type*) :
    let swap := fun (ψ : ι × ι → ℂ) (p : ι × ι) => ψ p.swap
    let Pplus := fun ψ => (1 / 2 : ℂ) • (ψ + swap ψ)
    let Pminus := fun ψ => (1 / 2 : ℂ) • (ψ - swap ψ)
    Pplus + Pminus = id ∧ Pplus ∘ Pminus = 0 ∧ Pminus ∘ Pplus = 0 ∧
    Pplus ∘ Pplus = Pplus ∧ Pminus ∘ Pminus = Pminus ∧
    swap ∘ Pplus = Pplus ∧ swap ∘ Pminus = -Pminus ∧
    ∀ v : ι → ℂ, v ≠ 0 →
      let ψ := fun p : ι × ι => v p.1 * v p.2
      Pminus ψ = 0 ∧ Pplus ψ = ψ ∧ ψ ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try
    (funext ψ p
     simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
       Pi.zero_apply, Prod.swap_swap, smul_eq_mul, id_eq]
     ring)
  intro v hv
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  refine ⟨?_, ?_, ?_⟩
  · funext (i, j)
    simp [mul_comm (v j) (v i)]
  · funext (i, j)
    simp only [Pi.smul_apply, Pi.add_apply, Prod.swap_prod_mk, smul_eq_mul, mul_comm (v j) (v i)]
    ring
  · obtain ⟨i, hi⟩ := hex
    intro h
    exact (mul_ne_zero hi hi) (congrFun h (i, i))

end D5.S3.Quantum.Foundation.ComplexLocalTomography
