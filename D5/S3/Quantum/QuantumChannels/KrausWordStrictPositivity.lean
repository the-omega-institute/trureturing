/- GID: D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/KrausWordStrictPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full exact-length Kraus-word span implies strict positivity of the same iterate. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
The word convention puts the latest letter first:
`word K (m+1) w = K (w 0) * word K m (Fin.tail w)`.
Thus a word is `K(w 0) ... K(w(m-1))`; all exact-length words occur.

Admission basis: escape-witness. The content obligation is that full matrix span
forces a PSD matrix annihilating every transformed vector to vanish. The proof
constructs the annihilator submodule and tests all matrix units. The transformed
kernel equations come from PositiveBranchReachableResponse.weightedCP_kernel
with every weight equal to one. The proof consumes the
exact iterate expansion, which is proved by induction, not assumed. No trace
normalization, primitivity premise, or positivity premise about an iterate is used.

Source: Ekblad, arXiv:2504.21638v3, Section 4, the known inequality between
Wielength and the primitivity index. This is a formalization of that bridge,
not a resolution of Conjecture A or a claim about its global open status.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity

/-- Exact-length products; coordinate zero is the leftmost, latest Kraus factor. -/
def word {d g : ℕ} (K : Fin g → Matrix (Fin d) (Fin d) ℂ) :
    (m : ℕ) → (Fin m → Fin g) → Matrix (Fin d) (Fin d) ℂ
  | 0, _ => 1
  | m + 1, w => K (w 0) * word K m (Fin.tail w)

/-- The complex span of all words of exactly the specified length. -/
def wordSpan {d g : ℕ} (K : Fin g → Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    Submodule ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Submodule.span ℂ (Set.range (word K m))

/-- Iteration of the actual Kraus map is the Kraus sum over exact-length words. -/
theorem iterate_eq_word_sum {d g : ℕ}
    (K : Fin g → Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (MatrixMap.of_kraus K K)^[m] X =
      ∑ w : Fin m → Fin g, word K m w * X * (word K m w)ᴴ := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin g)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, word,
      Fin.cons_zero, Fin.tail_cons, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem sum_posDef_of_span {d : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hL : Submodule.span ℂ (Set.range L) = ⊤)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) (hne : X ≠ 0) :
    (∑ i, L i * X * (L i)ᴴ).PosDef := by
  classical
  have hY : (∑ i, L i * X * (L i)ᴴ).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same (L i))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hY.isHermitian
  intro v hv
  apply lt_of_le_of_ne' (hY.dotProduct_mulVec_nonneg v)
  intro hz
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hker :
      (D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.weightedCP
        (fun i => L (e i)) (fun _ => 1) X) *ᵥ v = 0 := by
    simp only [D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.weightedCP,
      LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_one, one_smul]
    rw [e.sum_comp (fun i => L i * X * (L i)ᴴ)]
    exact hY.dotProduct_mulVec_zero_iff.mp hz
  have each :=
    (D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.weightedCP_kernel
      (fun i => L (e i)) (fun _ => 1) (fun _ => zero_lt_one) hX v).mp hker
  let S : Submodule ℂ (Matrix (Fin d) (Fin d) ℂ) := {
    carrier := {A | X *ᵥ (Aᴴ *ᵥ v) = 0}
    zero_mem' := by simp
    add_mem' := by
      intro A B hA hB
      simp only [Set.mem_ofPred_eq] at hA hB ⊢
      simp [Matrix.conjTranspose_add, Matrix.add_mulVec, Matrix.mulVec_add, hA, hB]
    smul_mem' := by
      intro c A hA
      simp only [Set.mem_ofPred_eq] at hA ⊢
      simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, hA] }
  have hspan : Submodule.span ℂ (Set.range L) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change X *ᵥ ((L i)ᴴ *ᵥ v) = 0
    simpa only [e.apply_symm_apply] using each (e.symm i)
  have hall (A : Matrix (Fin d) (Fin d) ℂ) : X *ᵥ (Aᴴ *ᵥ v) = 0 := by
    exact hspan (hL ▸ Submodule.mem_top)
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  apply hne
  ext a b
  have hab := congrFun (hall (Matrix.single i b 1)) a
  simpa [Matrix.conjTranspose_single, Matrix.single_mulVec_eq,
    Matrix.mulVec_smul, Matrix.mulVec_single_one, hi] using hab

/-- Full exact-word span makes the same iterate send every nonzero PSD matrix
to a positive definite matrix, for all dimensions, alphabet sizes and lengths. -/
theorem iterate_posDef_of_wordSpan_eq_top {d g : ℕ}
    (K : Fin g → Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    (hspan : wordSpan K m = ⊤)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) (hne : X ≠ 0) :
    ((MatrixMap.of_kraus K K)^[m] X).PosDef := by
  rw [iterate_eq_word_sum]
  exact sum_posDef_of_span (word K m) hspan X hX hne

end D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
