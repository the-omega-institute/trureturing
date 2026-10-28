/- GID: D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every signalling channel has a pure product input with positive PDM negativity. -/

import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Matrix.Order

/-! # Pure product inputs detect signalling through PDM negativity -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity

variable {α β α₁ β₁ α₂ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
  [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]

/-- The input-transposed CJ convention of the source. -/
def cjMatrix (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  ∑ i, ∑ j, single j i (1 : ℂ) ⊗ₖ e (single i j 1)

/-- Trace out A₁ and B₂ from the two-time PDM of a pure product input. -/
def pdmBA (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) : Matrix (β₁ × α₂) (β₁ × α₂) ℂ :=
  let m := cjMatrix (matrixAction p.toCompletelyPositiveMap)
  let ρ := (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b)) ⊗ₖ
    (1 : Matrix (α₂ × β₂) (α₂ × β₂) ℂ)
  partialTraceLeft (((1 / 2 : ℂ) • (m * ρ + ρ * m)).submatrix
    (fun x : (α₁ × β₂) × (β₁ × α₂) => ((x.1.1, x.2.1), (x.2.2, x.1.2)))
    (fun x : (α₁ × β₂) × (β₁ × α₂) => ((x.1.1, x.2.1), (x.2.2, x.1.2))))

/-- The trace norm minus one, using the positive matrix square root. -/
def negativity (r : Matrix α α ℂ) : ℝ :=
  (trace (CFC.sqrt (r * rᴴ))).re - 1

/-- Failure of CPTP factorization through the input A marginal. -/
def IsSignallingBA (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) : Prop :=
  ¬ ∃ t : QuantumChannel α₁ α₂, ∀ x : Matrix (α₁ × β₁) (α₁ × β₁) ℂ,
    partialTraceRight (p.toCompletelyPositiveMap x) =
      matrixAction t.toCompletelyPositiveMap (partialTraceRight x)

private def marginalMap (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) :
    Matrix (α₁ × β₁) (α₁ × β₁) ℂ →ₗ[ℂ] Matrix α₂ α₂ ℂ where
  toFun x := partialTraceRight (matrixAction p.toCompletelyPositiveMap x)
  map_add' := by
    intro x y
    rw [map_add, partialTraceRight_add]
  map_smul' := by
    intro z x
    ext i j
    change (∑ k, matrixAction p.toCompletelyPositiveMap (z • x) (i, k) (j, k)) =
      z * ∑ k, matrixAction p.toCompletelyPositiveMap x (i, k) (j, k)
    rw [map_smul]
    exact Finset.mul_sum.symm

private def conditionalMap (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) : Matrix β₁ β₁ ℂ →ₗ[ℂ] Matrix α₂ α₂ ℂ where
  toFun x := partialTraceRight (matrixAction p.toCompletelyPositiveMap (vecMulVec a (star a) ⊗ₖ x))
  map_add' := by
    intro x y
    rw [Matrix.kronecker_add, map_add, partialTraceRight_add]
  map_smul' := by
    intro z x
    ext i j
    change (∑ k, matrixAction p.toCompletelyPositiveMap (vecMulVec a (star a) ⊗ₖ (z • x))
      (i, k) (j, k)) = z * ∑ k, p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ x) (i, k) (j, k)
    rw [Matrix.kronecker_smul, map_smul]
    exact Finset.mul_sum.symm

private def IsReplacement (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∃ σ : Matrix β β ℂ, ∀ x, e x = trace x • σ

private theorem cj_entry (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (i j : α) (r s : β) : cjMatrix e (i, r) (j, s) = e (single j i 1) r s := by
  unfold cjMatrix
  simp only [Matrix.sum_apply, kronecker_apply, single_apply, ite_and,
    ite_mul, one_mul, zero_mul]
  simp

private theorem map_expansion (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (x : Matrix α α ℂ) : e x = ∑ i, ∑ j, x i j • e (single i j 1) := by
  have hx : x = ∑ i, ∑ j, x i j • single i j (1 : ℂ) := by
    conv_lhs => rw [matrix_eq_sum_single x]
    simp only [smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]

private theorem conditional_entry (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (k l : β₁) (r s : α₂) :
    conditionalMap p a (single k l 1) r s =
      ∑ t : β₂, ∑ i : α₁, ∑ j : α₁,
        (a i * star (a j)) * p.toCompletelyPositiveMap
          (single (i, k) (j, l) 1) (r, t) (s, t) := by
  change (∑ t : β₂, p.toCompletelyPositiveMap
    (vecMulVec a (star a) ⊗ₖ single k l 1) (r, t) (s, t)) = _
  rw [map_expansion (matrixAction p.toCompletelyPositiveMap)]
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, kronecker_apply, vecMulVec_apply, Pi.star_apply, single_apply, ite_and,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

private theorem discard_channel : ∃ t : QuantumChannel (α × β) α,
    ∀ x : Matrix (α × β) (α × β) ℂ,
      matrixAction t.toCompletelyPositiveMap x = partialTraceRight x := by
  let k : β → Matrix α (α × β) ℂ := fun b i j => if i = j.1 ∧ b = j.2 then 1 else 0
  have hk : ∑ b, (k b)ᴴ * k b = 1 := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    dsimp [k]
    simp only [map_ite, star_one, star_zero, ite_and, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Matrix.one_apply, Prod.mk.injEq, ite_and]
    split_ifs <;> simp_all
  obtain ⟨t, ht⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel k hk
  refine ⟨t, fun x => ?_⟩
  rw [show matrixAction t.toCompletelyPositiveMap x = ∑ b, k b * x * (k b)ᴴ from ht x]
  unfold partialTraceRight
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  dsimp [k]
  simp only [map_ite, star_one, star_zero, ite_and, ite_mul, mul_ite,
    one_mul, mul_one, zero_mul, mul_zero]
  simp

private theorem mixed_append_channel [Nonempty β] : ∃ t : QuantumChannel α (α × β),
    ∀ x : Matrix α α ℂ, matrixAction t.toCompletelyPositiveMap x =
      x ⊗ₖ ((Fintype.card β : ℂ)⁻¹ • (1 : Matrix β β ℂ)) := by
  let q : ℂ := (Real.sqrt ((Fintype.card β : ℝ)⁻¹) : ℂ)
  have hq : star q = q := Complex.conj_ofReal _
  have hqq : q * q = (Fintype.card β : ℂ)⁻¹ := by
    dsimp [q]
    exact_mod_cast Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hd : (Fintype.card β : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := β)
  let k : β → Matrix (α × β) α ℂ := fun b i j => if i.1 = j ∧ i.2 = b then q else 0
  have hk : ∑ b, (k b)ᴴ * k b = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    dsimp [k]
    simp only [map_ite, hq, star_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hqq, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ hd
    · simp [hij, Matrix.one_apply_ne hij]
  obtain ⟨t, ht⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel k hk
  refine ⟨t, fun x => ?_⟩
  rw [show matrixAction t.toCompletelyPositiveMap x = ∑ b, k b * x * (k b)ᴴ from ht x]
  ext ⟨i, b⟩ ⟨j, c⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    kronecker_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  dsimp [k]
  simp only [map_ite, hq, star_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hbc : b = c
  · subst c
    simp only [ite_true, mul_one]
    calc q * x i j * q = (q * q) * x i j := by ring
      _ = _ := by rw [hqq]; ring
  · simp [hbc, hbc.symm]

private theorem pure_projectors_map_zero
    (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (he : ∀ a : α → ℂ, star a ⬝ᵥ a = 1 → e (vecMulVec a (star a)) = 0) : e = 0 := by
  have hh (x : Matrix α α ℂ) (hx : x.IsHermitian) : e x = 0 := by
    have hexp : x = ∑ i, (hx.eigenvalues i : ℂ) •
        vecMulVec (⇑(hx.eigenvectorBasis i)) (star ⇑(hx.eigenvectorBasis i)) := by
      ext j k
      conv_lhs => rw [hx.spectral_theorem, Unitary.conjStarAlgAut_apply,
        Matrix.mul_diagonal, Matrix.mul_apply]
      simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.star_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply,
        smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hu (i : α) : star ⇑(hx.eigenvectorBasis i) ⬝ᵥ ⇑(hx.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, hx.eigenvectorBasis.norm_eq_one]
      norm_num
    rw [hexp, map_sum]
    simp only [map_smul, he _ (hu _), smul_zero, Finset.sum_const_zero]
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
  rw [map_add, map_smul, hh _ (realPart x).property,
    hh _ (imaginaryPart x).property, smul_zero, add_zero]
  rfl

private theorem signalling_dichotomy [Nonempty α₁] [Nonempty β₁]
    [Nonempty α₂] [Nonempty β₂]
    (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) (hp : IsSignallingBA p) :
    ∃ a : α₁ → ℂ, star a ⬝ᵥ a = 1 ∧ ¬ IsReplacement (conditionalMap p a) := by
  classical
  by_contra hall
  have hreplace (a : α₁ → ℂ) (ha : star a ⬝ᵥ a = 1) :
      IsReplacement (conditionalMap p a) := by
    by_contra hn
    exact hall ⟨a, ha, hn⟩
  let μ : Matrix β₁ β₁ ℂ := (Fintype.card β₁ : ℂ)⁻¹ • 1
  have hμ : trace μ = 1 := by
    dsimp [μ]
    rw [trace_smul, trace_one, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := β₁))
  have ht : ∃ t : QuantumChannel α₁ α₂, ∀ y : Matrix α₁ α₁ ℂ,
      matrixAction t.toCompletelyPositiveMap y = marginalMap p (y ⊗ₖ μ) := by
    obtain ⟨a, ha⟩ := mixed_append_channel (α := α₁) (β := β₁)
    obtain ⟨d, hd⟩ := discard_channel (α := α₂) (β := β₂)
    refine ⟨d.comp (p.comp a), fun y => ?_⟩
    change CStarMatrix.ofMatrix.symm
      ((d.comp (p.comp a)).toCompletelyPositiveMap (CStarMatrix.ofMatrix y)) = _
    rw [QuantumChannel.comp_apply, QuantumChannel.comp_apply]
    change matrixAction d.toCompletelyPositiveMap
      (matrixAction p.toCompletelyPositiveMap (matrixAction a.toCompletelyPositiveMap y)) = _
    rw [ha, hd]
    rfl
  obtain ⟨t, ht⟩ := ht
  have hprod (y : Matrix α₁ α₁ ℂ) (x : Matrix β₁ β₁ ℂ) :
      marginalMap p (y ⊗ₖ x) = trace x • matrixAction t.toCompletelyPositiveMap y := by
    let f : Matrix α₁ α₁ ℂ →ₗ[ℂ] Matrix α₂ α₂ ℂ :=
      { toFun y := marginalMap p (y ⊗ₖ x)
        map_add' := by intro y z; rw [add_kronecker, map_add]
        map_smul' := by intro z y; rw [smul_kronecker, map_smul]; rfl }
    have hf : f - trace x • matrixAction t.toCompletelyPositiveMap = 0 := by
      apply pure_projectors_map_zero
      intro a ha
      change marginalMap p (vecMulVec a (star a) ⊗ₖ x) -
        trace x • matrixAction t.toCompletelyPositiveMap (vecMulVec a (star a)) = 0
      obtain ⟨σ, hσ⟩ := hreplace a ha
      have hσμ := hσ μ
      change marginalMap p (vecMulVec a (star a) ⊗ₖ μ) = trace μ • σ at hσμ
      rw [ht, hσμ, hμ, one_smul]
      exact sub_eq_zero.mpr (hσ x)
    have h := LinearMap.congr_fun hf y
    change marginalMap p (y ⊗ₖ x) -
      trace x • matrixAction t.toCompletelyPositiveMap y = 0 at h
    exact sub_eq_zero.mp h
  apply hp
  refine ⟨t, fun x => ?_⟩
  change marginalMap p x = matrixAction t.toCompletelyPositiveMap (partialTraceRight x)
  induction x using Matrix.induction_on' with
  | h_zero =>
    have hz : partialTraceRight (0 : Matrix (α₁ × β₁) (α₁ × β₁) ℂ) = 0 := by
      ext i j
      exact Finset.sum_const_zero
    rw [map_zero, hz, map_zero]
  | h_add x y hx hy => rw [map_add, partialTraceRight_add, map_add, hx, hy]
  | h_std_basis ik jl z =>
    obtain ⟨i, k⟩ := ik
    obtain ⟨j, l⟩ := jl
    have hk : single (i, k) (j, l) z = single i j z ⊗ₖ single k l (1 : ℂ) := by
      rw [single_kronecker_single, mul_one]
    rw [hk, hprod, partialTraceRight_kronecker, map_smul]

private theorem pdm_reduction (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) :
    pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ))) := by
  unfold pdmBA partialTraceLeft
  ext ⟨k, r⟩ ⟨l, s⟩
  simp only [submatrix_apply, Matrix.smul_apply, Matrix.add_apply, mul_apply, cj_entry,
    kronecker_apply, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type,
    one_apply, Prod.mk.injEq, ite_and, mul_ite, ite_mul, one_mul, mul_one,
    zero_mul, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [conditional_entry, Finset.mul_sum, Finset.sum_mul]
  sorry

private theorem basis_pair_units (i j : α) (hij : i ≠ j) (q : ℂ)
    (hq : star q = q) (hqq : q * q = 1 / 2) :
    star (q • (Pi.single i (1 : ℂ) + Pi.single j 1)) ⬝ᵥ
        (q • (Pi.single i (1 : ℂ) + Pi.single j 1)) = 1 ∧
    star (q • (Pi.single i (1 : ℂ) - Pi.single j 1)) ⬝ᵥ
        (q • (Pi.single i (1 : ℂ) - Pi.single j 1)) = 1 ∧
    star (q • (Pi.single i (1 : ℂ) + Pi.single j 1)) ⬝ᵥ
        (q • (Pi.single i (1 : ℂ) - Pi.single j 1)) = 0 := by
  simp only [star_smul, star_add, star_sub, Pi.star_single, star_one, hq,
    smul_dotProduct, dotProduct_smul, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, Pi.single_apply,
    hij, hij.symm, if_false, ite_true, mul_one, one_mul, mul_zero,
    smul_eq_mul, ← mul_assoc, hqq]
  norm_num

private theorem orthogonal_pair [Nonempty α]
    (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (he : ¬ IsReplacement e) :
    ∃ b c : α → ℂ, star b ⬝ᵥ b = 1 ∧ star c ⬝ᵥ c = 1 ∧
      star b ⬝ᵥ c = 0 ∧ e (vecMulVec c (star b)) ≠ 0 := by
  classical
  by_contra hpair
  apply he
  have hvan (b c : α → ℂ) (hb : star b ⬝ᵥ b = 1) (hc : star c ⬝ᵥ c = 1)
      (hbc : star b ⬝ᵥ c = 0) : e (vecMulVec c (star b)) = 0 := by
    by_contra hn
    exact hpair ⟨b, c, hb, hc, hbc, hn⟩
  have hoff (i j : α) (hij : i ≠ j) : e (single i j 1) = 0 := by
    have h := hvan (Pi.single j 1) (Pi.single i 1)
      (by simp only [Pi.star_single, star_one, single_dotProduct, Pi.single_eq_same,
        mul_one])
      (by simp only [Pi.star_single, star_one, single_dotProduct, Pi.single_eq_same,
        mul_one])
      (by simp only [Pi.star_single, star_one, single_dotProduct,
        Pi.single_eq_of_ne hij.symm, mul_zero])
    simpa only [Pi.star_single, star_one, ← single_eq_single_vecMulVec_single] using h
  have hdiag (i j : α) : e (single i i 1) = e (single j j 1) := by
    by_cases hij : i = j
    · rw [hij]
    let q : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    have hq : star q = q := Complex.conj_ofReal _
    have hqq : q * q = 1 / 2 := by
      dsimp [q]
      exact_mod_cast Real.mul_self_sqrt (by norm_num : 0 ≤ (1 / 2 : ℝ))
    obtain ⟨hb, hc, hbc⟩ := basis_pair_units i j hij q hq hqq
    have hz := hvan _ _ hb hc hbc
    simp only [star_smul, star_add, Pi.star_single, star_one, hq,
      smul_vecMulVec, vecMulVec_smul, smul_smul, hqq, sub_vecMulVec,
      vecMulVec_add, ← single_eq_single_vecMulVec_single, map_smul,
      map_sub, map_add, hoff i j hij, hoff j i hij.symm, add_zero, zero_add] at hz
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  let i := Classical.choice (inferInstance : Nonempty α)
  refine ⟨e (single i i 1), fun x => ?_⟩
  rw [map_expansion]
  have hsingle (k l : α) : e (single k l 1) =
      if k = l then e (single i i 1) else 0 := by
    split_ifs with hkl
    · subst l
      exact hdiag k i
    · exact hoff k l hkl
  simp only [hsingle, ite_smul, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  rfl

private theorem pdm_hermitian_trace (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) (ha : star a ⬝ᵥ a = 1)
    (hb : star b ⬝ᵥ b = 1) :
    (pdmBA p a b).IsHermitian ∧ trace (pdmBA p a b) = 1 := by
  sorry

private theorem negative_minor (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b c : β₁ → ℂ)
    (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) (hc : star c ⬝ᵥ c = 1)
    (hbc : star b ⬝ᵥ c = 0)
    (he : conditionalMap p a (vecMulVec c (star b)) ≠ 0)
    (hr : pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)))) :
    ¬ (pdmBA p a b).PosSemidef := by
  sorry

private theorem negativity_of_not_posSemidef (r : Matrix α α ℂ)
    (hr : r.IsHermitian) (ht : trace r = 1) (hn : ¬ r.PosSemidef) :
    0 < negativity r := by
  have hneg : (negPart r).PosSemidef := (CFC.negPart_nonneg r).posSemidef
  have hne : negPart r ≠ 0 := by
    intro hz
    exact hn ((CFC.negPart_eq_zero_iff r hr).mp hz).posSemidef
  have htr : 0 < (trace (negPart r)).re := by
    have hnonneg := Complex.nonneg_iff.mp hneg.trace_nonneg
    refine lt_of_le_of_ne hnonneg.1 ?_
    intro hz
    apply hne
    apply hneg.trace_eq_zero_iff.mp
    exact Complex.ext hz.symm hnonneg.2.symm
  have habs : CFC.abs r = CFC.sqrt (r * rᴴ) := by
    unfold CFC.abs
    rw [Matrix.star_eq_conjTranspose, hr.eq]
  have hh : CFC.abs r - r = negPart r + negPart r := by
    simpa only [two_smul] using CFC.abs_sub_self r hr
  have heq := congrArg (fun x : Matrix α α ℂ => (trace x).re) hh
  rw [habs, trace_sub, trace_add, ht, Complex.sub_re, Complex.add_re,
    Complex.one_re] at heq
  unfold negativity
  linarith only [heq, htr]

/-- A signalling channel admits a pure product input with strictly positive PDM negativity. -/
theorem result [Nonempty α₁] [Nonempty β₁] [Nonempty α₂] [Nonempty β₂]
    (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) (hp : IsSignallingBA p) :
    ∃ (a : α₁ → ℂ) (b : β₁ → ℂ), star a ⬝ᵥ a = 1 ∧ star b ⬝ᵥ b = 1 ∧
      0 < negativity (pdmBA p a b) := by
  obtain ⟨a, ha, he⟩ := signalling_dichotomy p hp
  obtain ⟨b, c, hb, hc, hbc, hcross⟩ := orthogonal_pair (conditionalMap p a) he
  obtain ⟨hr, ht⟩ := pdm_hermitian_trace p a b ha hb
  exact ⟨a, b, ha, hb, negativity_of_not_posSemidef _ hr ht
    (negative_minor p a b c ha hb hc hbc hcross (pdm_reduction p a b))⟩

end D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
