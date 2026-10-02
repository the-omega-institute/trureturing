/- GID: D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Over all eigenbases the A-OTOC long-time average is least at the product basis. -/

/-
proof_shape: Idx, projA, projAc, ketBra, R0, R1, term, lta: definition (the block Hilbert space,
  the two Hilbert–Schmidt projections, the kernels and the long-time average of Eq. (6))
proof_shape: claim: definition (published conjecture, read over all eigenbases)
proof_shape: trD, trN: private definition (partial traces of one block of |φ_k⟩⟨φ_l|)
proof_shape: qf_le: content (the quadratic forms of both cross kernels are at most the
  identity, from unitarity of the eigenbasis and Cauchy–Schwarz in each block)
proof_shape: kernel_bounds: content (each cross trace is at most its diagonal, and the diagonal
  entries are bounded by the squared block weights)
proof_shape: lta_ge: content (the lower bound, from the per-block inequalities
  x(1-x)(M-1-x-x^2) >= 0 and superadditivity of 2x^2 - x^4 under the row and column weight
  constraints)
proof_shape: result: content (lta_ge together with the evaluation of the kernels at the
  product basis, carried out as local steps)
escape_witness: result (form (2) of §3.2: the lower bound and its attainment are produced by the
  Hilbert–Schmidt contraction, purity and per-block polynomial estimates and by the evaluation
  at the product basis; no existing statement gives them)
admission_basis: open-problem-resolution (issue #12247; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.AlgebraOTOCLongTimeMinimum

open Matrix
open scoped Kronecker BigOperators
open D5.S3.Quantum.Information.PartialTraceMutualInformation

variable {r : ℕ} (n d : Fin r → ℕ)

/-- The Hilbert space `⊕_J ℂ^{n_J} ⊗ ℂ^{d_J}` in its distinguished basis. -/
abbrev Idx := Σ J : Fin r, Fin (n J) × Fin (d J)

/-- `𝒫_𝒜(X) = ⊕_J (1/n_J) 𝟙_{n_J} ⊗ Tr_{n_J}(X_J)`: the Hilbert–Schmidt projection onto
`𝒜 = ⊕_J 𝟙_{n_J} ⊗ L(ℂ^{d_J})`. -/
noncomputable def projA (X : Matrix (Idx n d) (Idx n d) ℂ) : Matrix (Idx n d) (Idx n d) ℂ :=
  blockDiagonal' fun J => ((n J : ℂ)⁻¹) •
    ((1 : Matrix (Fin (n J)) (Fin (n J)) ℂ) ⊗ₖ partialTraceLeft (blockDiag' X J))

/-- `𝒫_{𝒜'}(X) = ⊕_J Tr_{d_J}(X_J) ⊗ (1/d_J) 𝟙_{d_J}`: the Hilbert–Schmidt projection onto
the commutant `𝒜' = ⊕_J L(ℂ^{n_J}) ⊗ 𝟙_{d_J}`. -/
noncomputable def projAc (X : Matrix (Idx n d) (Idx n d) ℂ) : Matrix (Idx n d) (Idx n d) ℂ :=
  blockDiagonal' fun J => ((d J : ℂ)⁻¹) •
    (partialTraceRight (blockDiag' X J) ⊗ₖ (1 : Matrix (Fin (d J)) (Fin (d J)) ℂ))

variable {n d}

/-- `|φ_k⟩⟨φ_l|` for the columns `φ_k` of `U`. -/
def ketBra (U : Matrix (Idx n d) (Idx n d) ℂ) (k l : Idx n d) : Matrix (Idx n d) (Idx n d) ℂ :=
  vecMulVec (fun i => U i k) (fun j => star (U j l))

/-- `R^{(0),𝒳}_{lk} = ‖𝒫_𝒳(|φ_k⟩⟨φ_l|)‖₂²`. -/
noncomputable def R0 (P : Matrix (Idx n d) (Idx n d) ℂ → Matrix (Idx n d) (Idx n d) ℂ)
    (U : Matrix (Idx n d) (Idx n d) ℂ) : Matrix (Idx n d) (Idx n d) ℝ :=
  fun l k => (trace ((P (ketBra U k l))ᴴ * P (ketBra U k l))).re

/-- `R^{(1),𝒳}_{kl} = ⟨𝒫_𝒳(Π_k), 𝒫_𝒳(Π_l)⟩`, a real number since both are Hermitian. -/
noncomputable def R1 (P : Matrix (Idx n d) (Idx n d) ℂ → Matrix (Idx n d) (Idx n d) ℂ)
    (U : Matrix (Idx n d) (Idx n d) ℂ) : Matrix (Idx n d) (Idx n d) ℝ :=
  fun k l => (trace ((P (ketBra U k k))ᴴ * P (ketBra U l l))).re

/-- One summand of Eq. (6): `Tr(R^{(0),𝒳} R^{(1),𝒳'}) - ½ Tr(R^{(0),𝒳}_D R^{(1),𝒳'}_D)`. -/
noncomputable def term (R0X R1X' : Matrix (Idx n d) (Idx n d) ℝ) : ℝ :=
  trace (R0X * R1X') - 1 / 2 * trace (diagonal (diag R0X) * diagonal (diag R1X'))

variable (n d)

/-- The long-time average of the `𝒜`-OTOC under the non-resonance condition, Eq. (6) of
arXiv:2312.13386, for the eigenbasis given by the columns of `U`. -/
noncomputable def lta (U : Matrix (Idx n d) (Idx n d) ℂ) : ℝ :=
  1 - 1 / ((∑ J, n J * d J : ℕ) : ℝ) *
    (term (R0 (projA n d) U) (R1 (projAc n d) U) + term (R0 (projAc n d) U) (R1 (projA n d) U))

/-- The conjecture of arXiv:2312.13386, Section IV: over all eigenbases, the least long-time
average is `1 - (Σ_J d_J + Σ_J n_J - d_𝒵) / d`. -/
def claim : Prop :=
  ∀ (r : ℕ) (n d : Fin r → ℕ), (∀ J, 0 < n J) → (∀ J, 0 < d J) →
    IsLeast (Set.range fun U : unitaryGroup (Idx n d) ℂ => lta n d U)
      (1 - (((∑ J, d J : ℕ) : ℝ) + ((∑ J, n J : ℕ) : ℝ) - r) / ((∑ J, n J * d J : ℕ) : ℝ))

section Proof

variable {n d}

/-- `Tr_{d_J}` of the `J` block of `|φ_k⟩⟨φ_l|`. -/
private def trD (U : Matrix (Idx n d) (Idx n d) ℂ) (J : Fin r) (k l : Idx n d) :
    Matrix (Fin (n J)) (Fin (n J)) ℂ :=
  fun a a' => ∑ b, U ⟨J, (a, b)⟩ k * star (U ⟨J, (a', b)⟩ l)

/-- `Tr_{n_J}` of the `J` block of `|φ_k⟩⟨φ_l|`. -/
private def trN (U : Matrix (Idx n d) (Idx n d) ℂ) (J : Fin r) (k l : Idx n d) :
    Matrix (Fin (d J)) (Fin (d J)) ℂ :=
  fun b b' => ∑ a, U ⟨J, (a, b)⟩ k * star (U ⟨J, (a, b')⟩ l)

/-- For a unitary `U`, the quadratic forms of both cross kernels are at most the identity. -/
private theorem qf_le (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J) (U : Matrix (Idx n d) (Idx n d) ℂ)
    (hU : star U * U = 1) (c : Idx n d → ℂ) :
    (∑ k, ∑ l, star (c k) * c l *
        ∑ J, ((d J : ℂ))⁻¹ * trace ((trD U J k k)ᴴ * trD U J l l)).re ≤ ∑ k, ‖c k‖ ^ 2 ∧
    (∑ k, ∑ l, star (c k) * c l *
        ∑ J, ((n J : ℂ))⁻¹ * trace ((trN U J k k)ᴴ * trN U J l l)).re ≤ ∑ k, ‖c k‖ ^ 2 := by
  have hfrob : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      (trace (Aᴴ * A)).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    intro m A
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  have hcs : ∀ (m : ℕ) (z : Fin m → ℂ), ‖∑ b, z b‖ ^ 2 ≤ m * ∑ b, ‖z b‖ ^ 2 := by
    intro m z
    calc ‖∑ b, z b‖ ^ 2 ≤ (∑ b, ‖z b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Finset.univ : Finset (Fin m)).card * ∑ b, ‖z b‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = m * ∑ b, ‖z b‖ ^ 2 := by simp
  have hblock : ∀ F : Idx n d → Idx n d → ℝ, (∀ i j, 0 ≤ F i j) →
      ∑ J, ∑ p : Fin (n J) × Fin (d J), ∑ q : Fin (n J) × Fin (d J), F ⟨J, p⟩ ⟨J, q⟩ ≤
        ∑ i, ∑ j, F i j := by
    intro F hF
    rw [Fintype.sum_sigma]
    refine Finset.sum_le_sum fun J _ => Finset.sum_le_sum fun p _ => ?_
    rw [Fintype.sum_sigma]
    exact Finset.single_le_sum (f := fun J' => ∑ q : Fin (n J') × Fin (d J'), F ⟨J, p⟩ ⟨J', q⟩)
      (fun J' _ => Finset.sum_nonneg fun q _ => hF _ _) (Finset.mem_univ J)
  have hunit : ∑ i, ∑ j, ‖∑ k, c k * U i k * star (U j k)‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
    have hU' : Uᴴ * U = 1 := by rwa [← star_eq_conjTranspose]
    set Ym : Matrix (Idx n d) (Idx n d) ℂ := U * diagonal c * Uᴴ with hYm
    have hYe : ∀ i j, Ym i j = ∑ k, c k * U i k * star (U j k) := by
      intro i j
      rw [hYm, mul_apply]
      simp only [mul_diagonal, conjTranspose_apply]
      exact Finset.sum_congr rfl fun k _ => by ring
    have htr : trace (Ymᴴ * Ym) = ∑ k, star (c k) * c k := by
      have : Ymᴴ * Ym = U * (diagonal (star c) * diagonal c) * Uᴴ := by
        simp only [hYm, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
      rw [this, trace_mul_cycle, hU', Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal]
      rfl
    have hn : ∀ z : ℂ, ‖z‖ ^ 2 = (star z * z).re := by
      intro z; rw [Complex.star_def, Complex.conj_mul']; norm_cast
    calc ∑ i, ∑ j, ‖∑ k, c k * U i k * star (U j k)‖ ^ 2
        = (∑ j, ∑ i, star (Ym i j) * Ym i j).re := by
          rw [Finset.sum_comm, Complex.re_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hYe, hn]
      _ = (trace (Ymᴴ * Ym)).re := by
          simp only [trace, diag, mul_apply, conjTranspose_apply]
      _ = ∑ k, ‖c k‖ ^ 2 := by
          rw [htr, Complex.re_sum]
          exact Finset.sum_congr rfl fun k _ => (hn _).symm
  set Y : Idx n d → Idx n d → ℂ := fun i j => ∑ k, c k * U i k * star (U j k) with hY
  constructor
  · set S : ∀ J, Matrix (Fin (n J)) (Fin (n J)) ℂ := fun J => ∑ k, c k • trD U J k k with hSdef
    have hS : ∀ J (y x : Fin (n J)), S J y x = ∑ b, Y ⟨J, (y, b)⟩ ⟨J, (x, b)⟩ := by
      intro J y x
      simp only [hSdef, hY, Matrix.sum_apply, Matrix.smul_apply, trD, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
    have hexp : ∀ J, trace ((S J)ᴴ * S J) =
        ∑ k, ∑ l, star (c k) * c l * trace ((trD U J k k)ᴴ * trD U J l l) := by
      intro J
      simp only [hSdef, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    have hL : ∑ k, ∑ l, star (c k) * c l *
        ∑ J, ((d J : ℂ))⁻¹ * trace ((trD U J k k)ᴴ * trD U J l l) =
        ∑ J, ((d J : ℂ))⁻¹ * trace ((S J)ᴴ * S J) := by
      simp only [hexp, Finset.mul_sum]
      calc _ = ∑ k, ∑ J, ∑ l, star (c k) * c l *
            (((d J : ℂ))⁻¹ * trace ((trD U J k k)ᴴ * trD U J l l)) :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
        _ = _ := Finset.sum_comm.trans (Finset.sum_congr rfl fun J _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    rw [hL, Complex.re_sum]
    calc ∑ J, (((d J : ℂ))⁻¹ * trace ((S J)ᴴ * S J)).re
        = ∑ J, ((d J : ℝ))⁻¹ * ∑ y, ∑ x, ‖S J y x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
            hfrob]
      _ ≤ ∑ J, ∑ y, ∑ x, ∑ b, ‖Y ⟨J, (y, b)⟩ ⟨J, (x, b)⟩‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => ?_
          have hJ : (0 : ℝ) < d J := by exact_mod_cast hd J
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hS]
          calc ((d J : ℝ))⁻¹ * ‖∑ b, Y ⟨J, (y, b)⟩ ⟨J, (x, b)⟩‖ ^ 2
              ≤ ((d J : ℝ))⁻¹ * (d J * ∑ b, ‖Y ⟨J, (y, b)⟩ ⟨J, (x, b)⟩‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (hcs _ _) (inv_nonneg.mpr hJ.le)
            _ = _ := by field_simp
      _ ≤ ∑ J, ∑ p : Fin (n J) × Fin (d J), ∑ q : Fin (n J) × Fin (d J),
            ‖Y ⟨J, p⟩ ⟨J, q⟩‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => ?_
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun x _ => ?_
          exact Finset.single_le_sum (f := fun b' => ‖Y ⟨J, (y, b)⟩ ⟨J, (x, b')⟩‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
      _ ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 := hblock (fun i j => ‖Y i j‖ ^ 2) fun _ _ => sq_nonneg _
      _ = ∑ k, ‖c k‖ ^ 2 := hunit
  · set S : ∀ J, Matrix (Fin (d J)) (Fin (d J)) ℂ := fun J => ∑ k, c k • trN U J k k with hSdef
    have hS : ∀ J (y x : Fin (d J)), S J y x = ∑ a, Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩ := by
      intro J y x
      simp only [hSdef, hY, Matrix.sum_apply, Matrix.smul_apply, trN, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
    have hexp : ∀ J, trace ((S J)ᴴ * S J) =
        ∑ k, ∑ l, star (c k) * c l * trace ((trN U J k k)ᴴ * trN U J l l) := by
      intro J
      simp only [hSdef, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    have hL : ∑ k, ∑ l, star (c k) * c l *
        ∑ J, ((n J : ℂ))⁻¹ * trace ((trN U J k k)ᴴ * trN U J l l) =
        ∑ J, ((n J : ℂ))⁻¹ * trace ((S J)ᴴ * S J) := by
      simp only [hexp, Finset.mul_sum]
      calc _ = ∑ k, ∑ J, ∑ l, star (c k) * c l *
            (((n J : ℂ))⁻¹ * trace ((trN U J k k)ᴴ * trN U J l l)) :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
        _ = _ := Finset.sum_comm.trans (Finset.sum_congr rfl fun J _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    rw [hL, Complex.re_sum]
    calc ∑ J, (((n J : ℂ))⁻¹ * trace ((S J)ᴴ * S J)).re
        = ∑ J, ((n J : ℝ))⁻¹ * ∑ y, ∑ x, ‖S J y x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
            hfrob]
      _ ≤ ∑ J, ∑ y, ∑ x, ∑ a, ‖Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => ?_
          have hJ : (0 : ℝ) < n J := by exact_mod_cast hn J
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hS]
          calc ((n J : ℝ))⁻¹ * ‖∑ a, Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩‖ ^ 2
              ≤ ((n J : ℝ))⁻¹ * (n J * ∑ a, ‖Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (hcs _ _) (inv_nonneg.mpr hJ.le)
            _ = _ := by field_simp
      _ ≤ ∑ J, ∑ p : Fin (n J) × Fin (d J), ∑ q : Fin (n J) × Fin (d J),
            ‖Y ⟨J, p⟩ ⟨J, q⟩‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => ?_
          simp only [Fintype.sum_prod_type]
          have e : ∑ y : Fin (d J), ∑ x : Fin (d J), ∑ a : Fin (n J),
                ‖Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩‖ ^ 2 =
              ∑ a : Fin (n J), ∑ y : Fin (d J), ∑ x : Fin (d J), ‖Y ⟨J, (a, y)⟩ ⟨J, (a, x)⟩‖ ^ 2 :=
            (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans Finset.sum_comm
          rw [e]
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun y _ => ?_
          exact Finset.single_le_sum
            (f := fun a' => ∑ x : Fin (d J), ‖Y ⟨J, (a, y)⟩ ⟨J, (a', x)⟩‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      _ ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 := hblock (fun i j => ‖Y i j‖ ^ 2) fun _ _ => sq_nonneg _
      _ = ∑ k, ‖c k‖ ^ 2 := hunit

/-- The two cross terms of Eq. (6) are bounded by their diagonals, and the diagonal entries by the
sector weights `q_{Jk} = ‖P_J φ_k‖²`. -/
private theorem kernel_bounds (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (U : Matrix (Idx n d) (Idx n d) ℂ) (hU : star U * U = 1) :
    trace (R0 (projA n d) U * R1 (projAc n d) U) ≤ ∑ k, R0 (projA n d) U k k ∧
    trace (R0 (projAc n d) U * R1 (projA n d) U) ≤ ∑ k, R0 (projAc n d) U k k ∧
    (∀ k, R0 (projA n d) U k k ≤
      ∑ J, (∑ p : Fin (n J) × Fin (d J), ‖U ⟨J, p⟩ k‖ ^ 2) ^ 2 / n J) ∧
    (∀ k, R0 (projAc n d) U k k ≤
      ∑ J, (∑ p : Fin (n J) × Fin (d J), ‖U ⟨J, p⟩ k‖ ^ 2) ^ 2 / d J) := by
  have hA : ∀ X Y : Matrix (Idx n d) (Idx n d) ℂ, trace ((projA n d X)ᴴ * projA n d Y) =
      ∑ J, ((n J : ℂ))⁻¹ *
        trace ((partialTraceLeft (blockDiag' X J))ᴴ * partialTraceLeft (blockDiag' Y J)) := by
    intro X Y
    simp only [projA, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, trace_blockDiagonal']
    refine Finset.sum_congr rfl fun J _ => ?_
    have hJ : (n J : ℂ) ≠ 0 := by exact_mod_cast (hn J).ne'
    rw [conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, ← mul_kronecker_mul, mul_one, trace_smul, trace_smul, trace_kronecker,
      trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    simp only [star_inv₀, star_natCast]
    field_simp
  have hA' : ∀ X Y : Matrix (Idx n d) (Idx n d) ℂ, trace ((projAc n d X)ᴴ * projAc n d Y) =
      ∑ J, ((d J : ℂ))⁻¹ *
        trace ((partialTraceRight (blockDiag' X J))ᴴ * partialTraceRight (blockDiag' Y J)) := by
    intro X Y
    simp only [projAc, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, trace_blockDiagonal']
    refine Finset.sum_congr rfl fun J _ => ?_
    have hJ : (d J : ℂ) ≠ 0 := by exact_mod_cast (hd J).ne'
    rw [conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, ← mul_kronecker_mul, mul_one, trace_smul, trace_smul, trace_kronecker,
      trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    simp only [star_inv₀, star_natCast]
    field_simp
  have reorder : ∀ {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
      (f : α → β → γ → δ → ℂ),
      (∑ i, ∑ j, ∑ x, ∑ y, f i j x y) = ∑ x, ∑ y, ∑ i, ∑ j, f i j x y := by
    intro α β γ δ _ _ _ _ f
    calc (∑ i, ∑ j, ∑ x, ∑ y, f i j x y) = ∑ i, ∑ x, ∑ j, ∑ y, f i j x y :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ y, ∑ j, f i j x y :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ x, ∑ i, ∑ y, ∑ j, f i j x y := Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ i, ∑ j, f i j x y := Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have hfrob : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      (trace (Aᴴ * A)).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    intro m A
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  refine ⟨?_, ?_, fun k => ?_, fun k => ?_⟩
  · have hherm : ∀ J k, (trD U J k k)ᴴ = trD U J k k := by
      intro J k
      ext a a'
      simp only [trD, conjTranspose_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hswap : ∀ J k l, trace ((trN U J k l)ᴴ * trN U J k l) =
        trace ((trD U J k k)ᴴ * trD U J l l) := by
      intro J k l
      simp only [trace, diag, mul_apply, conjTranspose_apply, trN, trD, star_sum, star_mul',
        star_star, Finset.sum_mul, Finset.mul_sum]
      refine (reorder _).trans ?_
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    set g : ∀ J, Idx n d → Idx n d → ℂ := fun J k l => trace ((trD U J k k)ᴴ * trD U J l l)
      with hg
    have hreal : ∀ J k l, star (g J k l) = g J k l := by
      intro J k l
      simp only [hg]
      rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hherm, hherm,
        trace_mul_comm]
    set h : Idx n d → Idx n d → ℂ := fun k l => ∑ J, ((d J : ℂ))⁻¹ * g J k l with hh
    have hhre : ∀ k l, ((h k l).re : ℂ) = h k l := by
      intro k l
      have : star (h k l) = h k l := by
        simp only [hh, star_sum, star_mul', star_inv₀, star_natCast, hreal]
      exact Complex.conj_eq_iff_re.mp (by rw [← Complex.star_def]; exact this)
    have hR0 : ∀ l k, R0 (projA n d) U l k = (∑ J, ((n J : ℂ))⁻¹ * g J k l).re := by
      intro l k
      simp only [R0, hA, hg]
      congr 1
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [show partialTraceLeft (blockDiag' (ketBra U k l) J) = trN U J k l from rfl, hswap]
    have hR1 : ∀ k l, R1 (projAc n d) U k l = (h k l).re := by
      intro k l
      simp only [R1, hA', hh, hg]
      rfl
    have him : ∀ k l, (h k l).im = 0 := by
      intro k l
      have := congrArg Complex.im (hhre k l)
      simpa using this.symm
    have hgexp : ∀ J k l, g J k l =
        ∑ x : Fin (n J), ∑ y : Fin (n J), star (trD U J k k y x) * trD U J l l y x := by
      intro J k l
      simp only [hg, trace, diag, mul_apply, conjTranspose_apply]
    have hgre : ∀ J k, (g J k k).re = ∑ x : Fin (n J), ∑ y : Fin (n J), ‖trD U J k k y x‖ ^ 2 := by
      intro J k
      rw [hgexp, Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Complex.star_def, Complex.conj_mul']; norm_cast
    have hmain : trace (R0 (projA n d) U * R1 (projAc n d) U) =
        ∑ J, ((n J : ℝ))⁻¹ * ∑ x : Fin (n J), ∑ y : Fin (n J),
          (∑ k, ∑ l, star (trD U J k k y x) * trD U J l l y x * h k l).re := by
      have e1 : trace (R0 (projA n d) U * R1 (projAc n d) U) =
          ∑ l, ∑ k, R0 (projA n d) U l k * R1 (projAc n d) U k l := by
        simp only [trace, diag, mul_apply]
      have e2 : ∀ k l, (∑ J, ((n J : ℂ))⁻¹ * g J k l).re * (h k l).re =
          ((∑ J, ((n J : ℂ))⁻¹ * g J k l) * h k l).re := by
        intro k l
        rw [Complex.mul_re, him]; ring
      have e3 : ∑ l, ∑ k, (∑ J, ((n J : ℂ))⁻¹ * g J k l) * h k l =
          ∑ J, ((n J : ℂ))⁻¹ * ∑ x : Fin (n J), ∑ y : Fin (n J),
            ∑ k, ∑ l, star (trD U J k k y x) * trD U J l l y x * h k l := by
        simp only [hgexp, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        calc _ = ∑ k, ∑ J, ∑ l, ∑ x : Fin (n J), ∑ y : Fin (n J),
              ((n J : ℂ))⁻¹ * (star (trD U J k k y x) * trD U J l l y x) * h k l :=
              Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = ∑ J, ∑ k, ∑ l, ∑ x : Fin (n J), ∑ y : Fin (n J),
              ((n J : ℂ))⁻¹ * (star (trD U J k k y x) * trD U J l l y x) * h k l :=
              Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun J _ => (reorder _).trans
              (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
                Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
      rw [e1]
      simp only [hR0, hR1, e2]
      calc ∑ l, ∑ k, ((∑ J, ((n J : ℂ))⁻¹ * g J k l) * h k l).re
          = (∑ l, ∑ k, (∑ J, ((n J : ℂ))⁻¹ * g J k l) * h k l).re := by
            simp only [Complex.re_sum]
        _ = (∑ J, ((n J : ℂ))⁻¹ * ∑ x : Fin (n J), ∑ y : Fin (n J),
            ∑ k, ∑ l, star (trD U J k k y x) * trD U J l l y x * h k l).re := by rw [e3]
        _ = _ := by
            simp only [Complex.re_sum]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
            simp only [Complex.re_sum]
    rw [hmain]
    calc ∑ J, ((n J : ℝ))⁻¹ * ∑ x : Fin (n J), ∑ y : Fin (n J),
          (∑ k, ∑ l, star (trD U J k k y x) * trD U J l l y x * h k l).re
        ≤ ∑ J, ((n J : ℝ))⁻¹ * ∑ x : Fin (n J), ∑ y : Fin (n J), ∑ k, ‖trD U J k k y x‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.mpr (Nat.cast_nonneg _))
          exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            (qf_le hn hd U hU (fun k => trD U J k k y x)).1
      _ = ∑ k, R0 (projA n d) U k k := by
          have e4 : ∀ k, R0 (projA n d) U k k = ∑ J, ((n J : ℝ))⁻¹ * (g J k k).re := by
            intro k
            rw [hR0, Complex.re_sum]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
          simp only [e4, hgre]
          symm
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  · have hherm : ∀ J k, (trN U J k k)ᴴ = trN U J k k := by
      intro J k
      ext a a'
      simp only [trN, conjTranspose_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hswap : ∀ J k l, trace ((trD U J k l)ᴴ * trD U J k l) =
        trace ((trN U J k k)ᴴ * trN U J l l) := by
      intro J k l
      simp only [trace, diag, mul_apply, conjTranspose_apply, trD, trN, star_sum, star_mul',
        star_star, Finset.sum_mul, Finset.mul_sum]
      refine (reorder _).trans ?_
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    set g : ∀ J, Idx n d → Idx n d → ℂ := fun J k l => trace ((trN U J k k)ᴴ * trN U J l l)
      with hg
    have hreal : ∀ J k l, star (g J k l) = g J k l := by
      intro J k l
      simp only [hg]
      rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hherm, hherm,
        trace_mul_comm]
    set h : Idx n d → Idx n d → ℂ := fun k l => ∑ J, ((n J : ℂ))⁻¹ * g J k l with hh
    have hhre : ∀ k l, ((h k l).re : ℂ) = h k l := by
      intro k l
      have : star (h k l) = h k l := by
        simp only [hh, star_sum, star_mul', star_inv₀, star_natCast, hreal]
      exact Complex.conj_eq_iff_re.mp (by rw [← Complex.star_def]; exact this)
    have hR0 : ∀ l k, R0 (projAc n d) U l k = (∑ J, ((d J : ℂ))⁻¹ * g J k l).re := by
      intro l k
      simp only [R0, hA', hg]
      congr 1
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [show partialTraceRight (blockDiag' (ketBra U k l) J) = trD U J k l from rfl, hswap]
    have hR1 : ∀ k l, R1 (projA n d) U k l = (h k l).re := by
      intro k l
      simp only [R1, hA, hh, hg]
      rfl
    have him : ∀ k l, (h k l).im = 0 := by
      intro k l
      have := congrArg Complex.im (hhre k l)
      simpa using this.symm
    have hgexp : ∀ J k l, g J k l =
        ∑ x : Fin (d J), ∑ y : Fin (d J), star (trN U J k k y x) * trN U J l l y x := by
      intro J k l
      simp only [hg, trace, diag, mul_apply, conjTranspose_apply]
    have hgre : ∀ J k, (g J k k).re = ∑ x : Fin (d J), ∑ y : Fin (d J), ‖trN U J k k y x‖ ^ 2 := by
      intro J k
      rw [hgexp, Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Complex.star_def, Complex.conj_mul']; norm_cast
    have hmain : trace (R0 (projAc n d) U * R1 (projA n d) U) =
        ∑ J, ((d J : ℝ))⁻¹ * ∑ x : Fin (d J), ∑ y : Fin (d J),
          (∑ k, ∑ l, star (trN U J k k y x) * trN U J l l y x * h k l).re := by
      have e1 : trace (R0 (projAc n d) U * R1 (projA n d) U) =
          ∑ l, ∑ k, R0 (projAc n d) U l k * R1 (projA n d) U k l := by
        simp only [trace, diag, mul_apply]
      have e2 : ∀ k l, (∑ J, ((d J : ℂ))⁻¹ * g J k l).re * (h k l).re =
          ((∑ J, ((d J : ℂ))⁻¹ * g J k l) * h k l).re := by
        intro k l
        rw [Complex.mul_re, him]; ring
      have e3 : ∑ l, ∑ k, (∑ J, ((d J : ℂ))⁻¹ * g J k l) * h k l =
          ∑ J, ((d J : ℂ))⁻¹ * ∑ x : Fin (d J), ∑ y : Fin (d J),
            ∑ k, ∑ l, star (trN U J k k y x) * trN U J l l y x * h k l := by
        simp only [hgexp, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        calc _ = ∑ k, ∑ J, ∑ l, ∑ x : Fin (d J), ∑ y : Fin (d J),
              ((d J : ℂ))⁻¹ * (star (trN U J k k y x) * trN U J l l y x) * h k l :=
              Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = ∑ J, ∑ k, ∑ l, ∑ x : Fin (d J), ∑ y : Fin (d J),
              ((d J : ℂ))⁻¹ * (star (trN U J k k y x) * trN U J l l y x) * h k l :=
              Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun J _ => (reorder _).trans
              (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
                Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
      rw [e1]
      simp only [hR0, hR1, e2]
      calc ∑ l, ∑ k, ((∑ J, ((d J : ℂ))⁻¹ * g J k l) * h k l).re
          = (∑ l, ∑ k, (∑ J, ((d J : ℂ))⁻¹ * g J k l) * h k l).re := by
            simp only [Complex.re_sum]
        _ = (∑ J, ((d J : ℂ))⁻¹ * ∑ x : Fin (d J), ∑ y : Fin (d J),
            ∑ k, ∑ l, star (trN U J k k y x) * trN U J l l y x * h k l).re := by rw [e3]
        _ = _ := by
            simp only [Complex.re_sum]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
            simp only [Complex.re_sum]
    rw [hmain]
    calc ∑ J, ((d J : ℝ))⁻¹ * ∑ x : Fin (d J), ∑ y : Fin (d J),
          (∑ k, ∑ l, star (trN U J k k y x) * trN U J l l y x * h k l).re
        ≤ ∑ J, ((d J : ℝ))⁻¹ * ∑ x : Fin (d J), ∑ y : Fin (d J), ∑ k, ‖trN U J k k y x‖ ^ 2 := by
          refine Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.mpr (Nat.cast_nonneg _))
          exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            (qf_le hn hd U hU (fun k => trN U J k k y x)).2
      _ = ∑ k, R0 (projAc n d) U k k := by
          have e4 : ∀ k, R0 (projAc n d) U k k = ∑ J, ((d J : ℝ))⁻¹ * (g J k k).re := by
            intro k
            rw [hR0, Complex.re_sum]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
          simp only [e4, hgre]
          symm
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  · have hR : R0 (projA n d) U k k =
        ∑ J, ((n J : ℝ))⁻¹ * ∑ x, ∑ y, ‖trN U J k k y x‖ ^ 2 := by
      simp only [R0, hA, Complex.re_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
        show partialTraceLeft (blockDiag' (ketBra U k k) J) = trN U J k k from rfl, hfrob,
        Finset.sum_comm]
    rw [hR]
    refine Finset.sum_le_sum fun J _ => ?_
    have hJ : (0 : ℝ) < n J := by exact_mod_cast hn J
    set A : Fin (d J) → ℝ := fun b => ∑ a : Fin (n J), ‖U ⟨J, (a, b)⟩ k‖ ^ 2 with hAdef
    have hq : ∑ p : Fin (n J) × Fin (d J), ‖U ⟨J, p⟩ k‖ ^ 2 = ∑ b, A b := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hpt : ∀ x y, ‖trN U J k k y x‖ ^ 2 ≤ A y * A x := by
      intro x y
      calc ‖trN U J k k y x‖ ^ 2
          ≤ (∑ a : Fin (n J), ‖U ⟨J, (a, y)⟩ k‖ * ‖U ⟨J, (a, x)⟩ k‖) ^ 2 := by
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun a _ => by rw [norm_mul, norm_star]
        _ ≤ A y * A x := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [hq, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hJ.le)
    calc ∑ x, ∑ y, ‖trN U J k k y x‖ ^ 2 ≤ ∑ x : Fin (d J), ∑ y : Fin (d J), A y * A x :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = (∑ b, A b) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.sum_comm]
  · have hR : R0 (projAc n d) U k k =
        ∑ J, ((d J : ℝ))⁻¹ * ∑ x, ∑ y, ‖trD U J k k y x‖ ^ 2 := by
      simp only [R0, hA', Complex.re_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
        show partialTraceRight (blockDiag' (ketBra U k k) J) = trD U J k k from rfl, hfrob,
        Finset.sum_comm]
    rw [hR]
    refine Finset.sum_le_sum fun J _ => ?_
    have hJ : (0 : ℝ) < d J := by exact_mod_cast hd J
    set A : Fin (n J) → ℝ := fun a => ∑ b : Fin (d J), ‖U ⟨J, (a, b)⟩ k‖ ^ 2 with hAdef
    have hq : ∑ p : Fin (n J) × Fin (d J), ‖U ⟨J, p⟩ k‖ ^ 2 = ∑ a, A a := by
      rw [Fintype.sum_prod_type]
    have hpt : ∀ x y, ‖trD U J k k y x‖ ^ 2 ≤ A y * A x := by
      intro x y
      calc ‖trD U J k k y x‖ ^ 2
          ≤ (∑ b : Fin (d J), ‖U ⟨J, (y, b)⟩ k‖ * ‖U ⟨J, (x, b)⟩ k‖) ^ 2 := by
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun b _ => by rw [norm_mul, norm_star]
        _ ≤ A y * A x := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [hq, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hJ.le)
    calc ∑ x, ∑ y, ‖trD U J k k y x‖ ^ 2 ≤ ∑ x : Fin (n J), ∑ y : Fin (n J), A y * A x :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = (∑ b, A b) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.sum_comm]

/-- The lower bound: every eigenbasis gives at least the conjectured value. -/
private theorem lta_ge (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (U : Matrix (Idx n d) (Idx n d) ℂ) (hU : U ∈ unitaryGroup (Idx n d) ℂ) :
    1 - (((∑ J, d J : ℕ) : ℝ) + ((∑ J, n J : ℕ) : ℝ) - r) / ((∑ J, n J * d J : ℕ) : ℝ) ≤
      lta n d U := by
  have hU1 : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hU2 : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  obtain ⟨h1, h2, h3, h4⟩ := kernel_bounds hn hd U hU1
  obtain ⟨q, hq⟩ : ∃ q : Fin r → Idx n d → ℝ,
      q = fun J k => ∑ p : Fin (n J) × Fin (d J), ‖U ⟨J, p⟩ k‖ ^ 2 := ⟨_, rfl⟩
  have h3' : ∀ k, R0 (projA n d) U k k ≤ ∑ J, q J k ^ 2 / n J := by
    intro k; rw [hq]; exact h3 k
  have h4' : ∀ k, R0 (projAc n d) U k k ≤ ∑ J, q J k ^ 2 / d J := by
    intro k; rw [hq]; exact h4 k
  have hcol : ∀ k, ∑ J, q J k = 1 := by
    intro k
    have e := congrArg Complex.re (congrFun (congrFun hU1 k) k)
    simp only [mul_apply, star_apply, one_apply_eq, Complex.re_sum, Complex.one_re] at e
    rw [hq]
    dsimp only
    rw [← e, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  have hrow : ∀ J, ∑ k, q J k = n J * d J := by
    intro J
    have e1 : ∀ p : Fin (n J) × Fin (d J), ∑ k, ‖U ⟨J, p⟩ k‖ ^ 2 = 1 := by
      intro p
      have e := congrArg Complex.re (congrFun (congrFun hU2 ⟨J, p⟩) ⟨J, p⟩)
      simp only [mul_apply, star_apply, one_apply_eq, Complex.re_sum, Complex.one_re] at e
      rw [← e]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.star_def, Complex.mul_conj']; norm_cast
    rw [hq]
    dsimp only
    rw [Finset.sum_comm]
    simp [e1]
  have hq0 : ∀ J k, 0 ≤ q J k := by
    intro J k; rw [hq]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : ∀ J k, q J k ≤ 1 := by
    intro J k
    rw [← hcol k]
    exact Finset.single_le_sum (fun J' _ => hq0 J' k) (Finset.mem_univ J)
  have hterm : ∀ A B : Matrix (Idx n d) (Idx n d) ℝ,
      term A B = trace (A * B) - 1 / 2 * ∑ k, A k k * B k k := by
    intro A B
    simp only [term, diagonal_mul_diagonal, trace_diagonal, diag_apply]
  have hF : term (R0 (projA n d) U) (R1 (projAc n d) U) +
      term (R0 (projAc n d) U) (R1 (projA n d) U) ≤
        ∑ k, (R0 (projA n d) U k k + R0 (projAc n d) U k k -
          R0 (projA n d) U k k * R0 (projAc n d) U k k) := by
    rw [hterm, hterm]
    have e1 : ∀ k, R1 (projAc n d) U k k = R0 (projAc n d) U k k := fun k => rfl
    have e2 : ∀ k, R1 (projA n d) U k k = R0 (projA n d) U k k := fun k => rfl
    simp only [e1, e2]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hc : ∑ k, R0 (projAc n d) U k k * R0 (projA n d) U k k =
        ∑ k, R0 (projA n d) U k k * R0 (projAc n d) U k k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  have hsq : ∀ J k, q J k ^ 2 ≤ q J k := fun J k => by nlinarith [hq0 J k, hq1 J k]
  have hrr1 : ∀ k, ∑ J, q J k ^ 2 / n J ≤ 1 := by
    intro k
    rw [← hcol k]
    refine Finset.sum_le_sum fun J _ => ?_
    have hJ : (1 : ℝ) ≤ n J := by exact_mod_cast hn J
    exact (div_le_self (sq_nonneg _) hJ).trans (hsq J k)
  have hww1 : ∀ k, ∑ J, q J k ^ 2 / d J ≤ 1 := by
    intro k
    rw [← hcol k]
    refine Finset.sum_le_sum fun J _ => ?_
    have hJ : (1 : ℝ) ≤ d J := by exact_mod_cast hd J
    exact (div_le_self (sq_nonneg _) hJ).trans (hsq J k)
  have hprod : ∀ k, ∑ J, q J k ^ 4 / (n J * d J) ≤
      (∑ J, q J k ^ 2 / n J) * ∑ J, q J k ^ 2 / d J := by
    intro k
    rw [Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun J _ => ?_
    have e : q J k ^ 4 / (n J * d J) = q J k ^ 2 / n J * (q J k ^ 2 / d J) := by
      rw [div_mul_div_comm]; ring
    rw [e]
    exact Finset.single_le_sum (f := fun J' => q J k ^ 2 / n J * (q J' k ^ 2 / d J'))
      (fun J' _ => mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))) (Finset.mem_univ J)
  have hk : ∀ k, R0 (projA n d) U k k + R0 (projAc n d) U k k -
      R0 (projA n d) U k k * R0 (projAc n d) U k k ≤
      ∑ J, (q J k ^ 2 / n J + q J k ^ 2 / d J - q J k ^ 4 / (n J * d J)) := by
    intro k
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hs := h3' k
    have ht := h4' k
    have hp := hprod k
    have hr := hrr1 k
    have hw := hww1 k
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr (ht.trans hw)),
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hr)]
  have hJ : ∀ J, ∑ k, (q J k ^ 2 / n J + q J k ^ 2 / d J - q J k ^ 4 / (n J * d J)) ≤
      (n J : ℝ) + d J - 1 := by
    intro J
    have hn0 : (0 : ℝ) < n J := by exact_mod_cast hn J
    have hd0 : (0 : ℝ) < d J := by exact_mod_cast hd J
    have e : ∀ k, q J k ^ 2 / n J + q J k ^ 2 / d J - q J k ^ 4 / (n J * d J) =
        (((n J : ℝ) + d J) * q J k ^ 2 - q J k ^ 4) / (n J * d J) := by
      intro k; field_simp; ring
    simp only [e]
    rcases Nat.lt_or_ge (n J + d J) 3 with hlt | hge
    · have hn1 : n J = 1 := by have := hn J; have := hd J; omega
      have hd1 : d J = 1 := by have := hn J; have := hd J; omega
      have hsum : ∑ k, q J k = 1 := by rw [hrow, hn1, hd1]; norm_num
      have hsup : ∀ s : Finset (Idx n d), ∑ k ∈ s, q J k ≤ 1 →
          ∑ k ∈ s, (2 * q J k ^ 2 - q J k ^ 4) ≤
            2 * (∑ k ∈ s, q J k) ^ 2 - (∑ k ∈ s, q J k) ^ 4 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert j s hj ih =>
          intro hs
          rw [Finset.sum_insert hj] at hs ⊢
          rw [Finset.sum_insert hj]
          have hS0 : 0 ≤ ∑ k ∈ s, q J k := Finset.sum_nonneg fun k _ => hq0 J k
          have hqj := hq0 J j
          have ih' := ih (by linarith)
          have key : 0 ≤ q J j * (∑ k ∈ s, q J k) *
              (4 - 4 * (q J j + ∑ k ∈ s, q J k) ^ 2 + 2 * q J j * ∑ k ∈ s, q J k) := by
            apply mul_nonneg (mul_nonneg hqj hS0)
            nlinarith
          nlinarith
      have hfin := hsup Finset.univ hsum.le
      rw [hsum] at hfin
      simp only [hn1, hd1, Nat.cast_one]
      norm_num at hfin ⊢
      linarith
    · have hM : (3 : ℝ) ≤ n J + d J := by exact_mod_cast hge
      have hterm' : ∀ k, (((n J : ℝ) + d J) * q J k ^ 2 - q J k ^ 4) / (n J * d J) ≤
          ((n J : ℝ) + d J - 1) * q J k / (n J * d J) := by
        intro k
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h0 := hq0 J k
        have h1' := hq1 J k
        have h2' : 0 ≤ q J k * (1 - q J k) * ((n J : ℝ) + d J - 1 - q J k - q J k ^ 2) := by
          apply mul_nonneg (mul_nonneg h0 (by linarith))
          nlinarith
        nlinarith
      calc ∑ k, (((n J : ℝ) + d J) * q J k ^ 2 - q J k ^ 4) / (n J * d J)
          ≤ ∑ k, ((n J : ℝ) + d J - 1) * q J k / (n J * d J) :=
            Finset.sum_le_sum fun k _ => hterm' k
        _ = ((n J : ℝ) + d J - 1) * (∑ k, q J k) / (n J * d J) := by
            rw [Finset.mul_sum, Finset.sum_div]
        _ = (n J : ℝ) + d J - 1 := by
            rw [hrow]; field_simp
  have hB : ∑ J, ((n J : ℝ) + d J - 1) =
      ((∑ J, d J : ℕ) : ℝ) + ((∑ J, n J : ℕ) : ℝ) - r := by
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hFB : term (R0 (projA n d) U) (R1 (projAc n d) U) +
      term (R0 (projAc n d) U) (R1 (projA n d) U) ≤
        ((∑ J, d J : ℕ) : ℝ) + ((∑ J, n J : ℕ) : ℝ) - r := by
    rw [← hB]
    refine hF.trans ((Finset.sum_le_sum fun k _ => hk k).trans ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun J _ => hJ J
  have hD : 0 ≤ 1 / ((∑ J, n J * d J : ℕ) : ℝ) := by positivity
  unfold lta
  rw [div_eq_mul_one_div, mul_comm]
  nlinarith [mul_le_mul_of_nonneg_left hFB hD]

end Proof

/-- The conjecture holds: over all eigenbases the least long-time average is
`1 - (Σ_J d_J + Σ_J n_J - d_𝒵) / d`, attained by the distinguished product basis. -/
theorem result : claim := by
  intro r n d hn hd
  have hone : lta n d (1 : Matrix (Idx n d) (Idx n d) ℂ) =
      1 - (((∑ J, d J : ℕ) : ℝ) + ((∑ J, n J : ℕ) : ℝ) - r) / ((∑ J, n J * d J : ℕ) : ℝ) := by
    have hA : ∀ X Y : Matrix (Idx n d) (Idx n d) ℂ, trace ((projA n d X)ᴴ * projA n d Y) =
        ∑ J, ((n J : ℂ))⁻¹ *
          trace ((partialTraceLeft (blockDiag' X J))ᴴ * partialTraceLeft (blockDiag' Y J)) := by
      intro X Y
      simp only [projA, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, trace_blockDiagonal']
      refine Finset.sum_congr rfl fun J _ => ?_
      have hJ : (n J : ℂ) ≠ 0 := by exact_mod_cast (hn J).ne'
      rw [conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, ← mul_kronecker_mul, mul_one, trace_smul, trace_smul, trace_kronecker,
        trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
      simp only [star_inv₀, star_natCast]
      field_simp
    have hA' : ∀ X Y : Matrix (Idx n d) (Idx n d) ℂ, trace ((projAc n d X)ᴴ * projAc n d Y) =
        ∑ J, ((d J : ℂ))⁻¹ *
          trace ((partialTraceRight (blockDiag' X J))ᴴ * partialTraceRight (blockDiag' Y J)) := by
      intro X Y
      simp only [projAc, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, trace_blockDiagonal']
      refine Finset.sum_congr rfl fun J _ => ?_
      have hJ : (d J : ℂ) ≠ 0 := by exact_mod_cast (hd J).ne'
      rw [conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, ← mul_kronecker_mul, mul_one, trace_smul, trace_smul, trace_kronecker,
        trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
      simp only [star_inv₀, star_natCast]
      field_simp
    have hN0 : ∀ J' (k l : Idx n d), (k.1 ≠ J' ∨ l.1 ≠ J') →
        trN (1 : Matrix (Idx n d) (Idx n d) ℂ) J' k l = 0 := by
      intro J' k l h
      ext b b'
      simp only [trN, one_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      rcases h with h | h
      · rw [if_neg (by rintro rfl; exact h rfl), zero_mul]
      · have hne : ¬ ((⟨J', (a, b')⟩ : Idx n d) = l) := by rintro rfl; exact h rfl
        simp [hne]
    have hD0 : ∀ J' (k l : Idx n d), (k.1 ≠ J' ∨ l.1 ≠ J') →
        trD (1 : Matrix (Idx n d) (Idx n d) ℂ) J' k l = 0 := by
      intro J' k l h
      ext a a'
      simp only [trD, one_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      rcases h with h | h
      · rw [if_neg (by rintro rfl; exact h rfl), zero_mul]
      · have hne : ¬ ((⟨J', (a', b)⟩ : Idx n d) = l) := by rintro rfl; exact h rfl
        simp [hne]
    have hNv : ∀ J (a0 a1 : Fin (n J)) (b0 b1 b b' : Fin (d J)),
        trN (1 : Matrix (Idx n d) (Idx n d) ℂ) J ⟨J, (a0, b0)⟩ ⟨J, (a1, b1)⟩ b b' =
          if b = b0 ∧ b' = b1 ∧ a0 = a1 then 1 else 0 := by
      intro J a0 a1 b0 b1 b b'
      simp only [trN, one_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq]
      rw [Finset.sum_eq_single a0 (fun x _ hx => by simp [hx]) (by simp)]
      by_cases h1 : b = b0 <;> by_cases h2 : b' = b1 <;> by_cases h3 : a0 = a1 <;>
        simp [h1, h2, h3]
    have hDv : ∀ J (a0 a1 a a' : Fin (n J)) (b0 b1 : Fin (d J)),
        trD (1 : Matrix (Idx n d) (Idx n d) ℂ) J ⟨J, (a0, b0)⟩ ⟨J, (a1, b1)⟩ a a' =
          if a = a0 ∧ a' = a1 ∧ b0 = b1 then 1 else 0 := by
      intro J a0 a1 a a' b0 b1
      simp only [trD, one_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq]
      rw [Finset.sum_eq_single b0 (fun x _ hx => by simp [hx]) (by simp)]
      by_cases h1 : a = a0 <;> by_cases h2 : a' = a1 <;> by_cases h3 : b0 = b1 <;>
        simp [h1, h2, h3]
    have hfrob : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
        (trace (Aᴴ * A)).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
      intro m A
      simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.conj_mul']; norm_cast
    have hnorm : ∀ c : Prop, [Decidable c] →
        ‖(if c then (1 : ℂ) else 0)‖ ^ 2 = if c then 1 else 0 := by
      intro c _; split_ifs <;> simp
    have hptN : ∀ (J : Fin r) (k l : Idx n d),
        partialTraceLeft (blockDiag' (ketBra (1 : Matrix (Idx n d) (Idx n d) ℂ) k l) J) =
          trN 1 J k l := fun _ _ _ => rfl
    have hptD : ∀ (J : Fin r) (k l : Idx n d),
        partialTraceRight (blockDiag' (ketBra (1 : Matrix (Idx n d) (Idx n d) ℂ) k l) J) =
          trD 1 J k l := fun _ _ _ => rfl
    have R0A_ne : ∀ k l : Idx n d, k.1 ≠ l.1 → R0 (projA n d) 1 l k = 0 := by
      intro k l h
      simp only [R0, hA, hptN]
      rw [Finset.sum_eq_zero fun J _ => ?_]
      · simp
      · by_cases hk : k.1 = J
        · rw [hN0 J k l (Or.inr (fun hl => h (hk.trans hl.symm)))]; simp
        · rw [hN0 J k l (Or.inl hk)]; simp
    have R0A_eq : ∀ J (a0 a1 : Fin (n J)) (b0 b1 : Fin (d J)),
        R0 (projA n d) 1 ⟨J, (a1, b1)⟩ ⟨J, (a0, b0)⟩ = if a0 = a1 then ((n J : ℝ))⁻¹ else 0 := by
      intro J a0 a1 b0 b1
      simp only [R0, hA, hptN]
      rw [Finset.sum_eq_single J (fun J' _ hJ' => by
        rw [hN0 J' _ _ (Or.inl (Ne.symm hJ'))]; simp) (by simp)]
      rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
        hfrob]
      simp only [hNv, hnorm]
      by_cases h : a0 = a1 <;> simp [h, ite_and, Finset.sum_ite_eq']
    have R0A'_ne : ∀ k l : Idx n d, k.1 ≠ l.1 → R0 (projAc n d) 1 l k = 0 := by
      intro k l h
      simp only [R0, hA', hptD]
      rw [Finset.sum_eq_zero fun J _ => ?_]
      · simp
      · by_cases hk : k.1 = J
        · rw [hD0 J k l (Or.inr (fun hl => h (hk.trans hl.symm)))]; simp
        · rw [hD0 J k l (Or.inl hk)]; simp
    have R0A'_eq : ∀ J (a0 a1 : Fin (n J)) (b0 b1 : Fin (d J)),
        R0 (projAc n d) 1 ⟨J, (a1, b1)⟩ ⟨J, (a0, b0)⟩ = if b0 = b1 then ((d J : ℝ))⁻¹ else 0 := by
      intro J a0 a1 b0 b1
      simp only [R0, hA', hptD]
      rw [Finset.sum_eq_single J (fun J' _ hJ' => by
        rw [hD0 J' _ _ (Or.inl (Ne.symm hJ'))]; simp) (by simp)]
      rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
        hfrob]
      simp only [hDv, hnorm]
      by_cases h : b0 = b1 <;> simp [h, ite_and, Finset.sum_ite_eq']
    have R1A'_eq : ∀ J (a0 a1 : Fin (n J)) (b0 b1 : Fin (d J)),
        R1 (projAc n d) 1 ⟨J, (a0, b0)⟩ ⟨J, (a1, b1)⟩ = if a0 = a1 then ((d J : ℝ))⁻¹ else 0 := by
      intro J a0 a1 b0 b1
      simp only [R1, hA', hptD]
      rw [Finset.sum_eq_single J (fun J' _ hJ' => by
        rw [hD0 J' _ _ (Or.inl (Ne.symm hJ'))]; simp) (by simp)]
      rw [show ((d J : ℂ))⁻¹ = (((d J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
      simp only [trace, diag, mul_apply, conjTranspose_apply, hDv, Complex.re_sum]
      by_cases hne : a0 = a1
      · subst hne
        simp only [ite_and]
        rw [Finset.sum_eq_single a0 (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [hx])
          (by simp)]
        rw [Finset.sum_eq_single a0 (fun y _ hy => by simp [hy]) (by simp)]
        simp
      · simp only [ite_and]
        rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_]
        · simp [hne]
        · split_ifs <;> first | (exfalso; subst_vars; exact hne rfl) | simp
    have R1A_eq : ∀ J (a0 a1 : Fin (n J)) (b0 b1 : Fin (d J)),
        R1 (projA n d) 1 ⟨J, (a0, b0)⟩ ⟨J, (a1, b1)⟩ = if b0 = b1 then ((n J : ℝ))⁻¹ else 0 := by
      intro J a0 a1 b0 b1
      simp only [R1, hA, hptN]
      rw [Finset.sum_eq_single J (fun J' _ hJ' => by
        rw [hN0 J' _ _ (Or.inl (Ne.symm hJ'))]; simp) (by simp)]
      rw [show ((n J : ℂ))⁻¹ = (((n J : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
      simp only [trace, diag, mul_apply, conjTranspose_apply, hNv, Complex.re_sum]
      by_cases hne : b0 = b1
      · subst hne
        simp only [ite_and]
        rw [Finset.sum_eq_single b0 (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [hx])
          (by simp)]
        rw [Finset.sum_eq_single b0 (fun y _ hy => by simp [hy]) (by simp)]
        simp
      · simp only [ite_and]
        rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_]
        · simp [hne]
        · split_ifs <;> first | (exfalso; subst_vars; exact hne rfl) | simp
    have hsum : ∀ f : Idx n d → Idx n d → ℝ, (∀ k l : Idx n d, k.1 ≠ l.1 → f k l = 0) →
        ∑ l, ∑ k, f k l =
          ∑ J, ∑ p : Fin (n J) × Fin (d J), ∑ p' : Fin (n J) × Fin (d J), f ⟨J, p'⟩ ⟨J, p⟩ := by
      intro f hf
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_eq_single J
        (fun J' _ hJ' => Finset.sum_eq_zero fun p' _ => hf _ _ hJ') (by simp)]
    have hn0 : ∀ J, (n J : ℝ) ≠ 0 := fun J => by have := hn J; positivity
    have hd0 : ∀ J, (d J : ℝ) ≠ 0 := fun J => by have := hd J; positivity
    have T1 : trace (R0 (projA n d) 1 * R1 (projAc n d) 1) = ((∑ J, d J : ℕ) : ℝ) := by
      have h : trace (R0 (projA n d) 1 * R1 (projAc n d) 1) =
          ∑ l, ∑ k, R0 (projA n d) 1 l k * R1 (projAc n d) 1 k l := by
        simp only [trace, diag, mul_apply]
      rw [h, hsum (fun k l => R0 (projA n d) 1 l k * R1 (projAc n d) 1 k l)
        (fun k l h => mul_eq_zero_of_left (R0A_ne k l h) _)]
      push_cast
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [Fintype.sum_prod_type, R0A_eq, R1A'_eq]
      simp [Finset.sum_ite_eq']
      field_simp [hn0 J, hd0 J]
    have T2 : trace (R0 (projAc n d) 1 * R1 (projA n d) 1) = ((∑ J, n J : ℕ) : ℝ) := by
      have h : trace (R0 (projAc n d) 1 * R1 (projA n d) 1) =
          ∑ l, ∑ k, R0 (projAc n d) 1 l k * R1 (projA n d) 1 k l := by
        simp only [trace, diag, mul_apply]
      rw [h, hsum (fun k l => R0 (projAc n d) 1 l k * R1 (projA n d) 1 k l)
        (fun k l h => mul_eq_zero_of_left (R0A'_ne k l h) _)]
      push_cast
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [Fintype.sum_prod_type, R0A'_eq, R1A_eq]
      simp [Finset.sum_ite_eq']
      field_simp [hn0 J, hd0 J]
    have D1 : trace (diagonal (diag (R0 (projA n d) 1)) * diagonal (diag (R1 (projAc n d) 1))) =
        (r : ℝ) := by
      rw [diagonal_mul_diagonal, trace_diagonal, Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type, diag, R0A_eq, R1A'_eq]
      calc _ = ∑ _ : Fin r, (1 : ℝ) := Finset.sum_congr rfl fun J _ => by
              simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              field_simp [hn0 J, hd0 J]
        _ = r := by simp
    have D2 : trace (diagonal (diag (R0 (projAc n d) 1)) * diagonal (diag (R1 (projA n d) 1))) =
        (r : ℝ) := by
      rw [diagonal_mul_diagonal, trace_diagonal, Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type, diag, R0A'_eq, R1A_eq]
      calc _ = ∑ _ : Fin r, (1 : ℝ) := Finset.sum_congr rfl fun J _ => by
              simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              field_simp [hn0 J, hd0 J]
        _ = r := by simp
    unfold lta term
    rw [T1, T2, D1, D2]
    ring
  refine ⟨⟨⟨1, one_mem _⟩, hone⟩, ?_⟩
  rintro _ ⟨U, rfl⟩
  exact lta_ge hn hd U U.2

end D5.S3.Quantum.Information.AlgebraOTOCLongTimeMinimum
