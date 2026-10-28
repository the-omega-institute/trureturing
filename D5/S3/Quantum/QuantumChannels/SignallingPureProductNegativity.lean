/- GID: D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every signalling channel has a pure product input with positive PDM negativity. -/

import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation

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
    partialTraceRight (matrixAction p.toCompletelyPositiveMap x) =
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
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

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
      (i, k) (j, k)) = z * ∑ k, matrixAction p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ x) (i, k) (j, k)
    rw [Matrix.kronecker_smul, map_smul]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

private def IsReplacement (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∃ σ : Matrix β β ℂ, ∀ x, e x = trace x • σ

private theorem cj_entry (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (i j : α) (r s : β) : cjMatrix e (i, r) (j, s) = e (single j i 1) r s := by
  change (∑ k, ∑ l, single l k (1 : ℂ) ⊗ₖ e (single k l 1))
    (i, r) (j, s) = _
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
        (a i * star (a j)) * matrixAction p.toCompletelyPositiveMap
          (single (i, k) (j, l) 1) (r, t) (s, t) := by
  change (∑ t : β₂, matrixAction p.toCompletelyPositiveMap
    (vecMulVec a (star a) ⊗ₖ single k l 1) (r, t) (s, t)) = _
  rw [map_expansion (matrixAction p.toCompletelyPositiveMap)]
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, kronecker_apply, vecMulVec_apply, Pi.star_apply, single_apply, ite_and,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

private theorem discard_channel : ∃ t : QuantumChannel (α × β) α,
    ∀ x : Matrix (α × β) (α × β) ℂ,
      matrixAction t.toCompletelyPositiveMap x = partialTraceRight x := by
  have star_ite (p : Prop) [Decidable p] (x y : ℂ) :
      star (if p then x else y) = if p then star x else star y := by
    split_ifs <;> rfl
  let k : β → Matrix α (α × β) ℂ := fun b i j => if i = j.1 ∧ b = j.2 then 1 else 0
  have hk : ∑ b, (k b)ᴴ * k b = 1 := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    dsimp [k]
    simp only [starRingEnd_apply, star_ite, star_one, star_zero, ite_and, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Matrix.one_apply, Prod.mk.injEq, ite_and]
  obtain ⟨t, ht⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel k hk
  refine ⟨t, fun x => ?_⟩
  rw [show matrixAction t.toCompletelyPositiveMap x = ∑ b, k b * x * (k b)ᴴ from ht x]
  unfold partialTraceRight
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  dsimp [k]
  simp only [starRingEnd_apply, star_ite, star_one, star_zero, ite_and, ite_mul, mul_ite,
    one_mul, mul_one, zero_mul, mul_zero]
  simp

private theorem mixed_append_channel [Nonempty β] : ∃ t : QuantumChannel α (α × β),
    ∀ x : Matrix α α ℂ, matrixAction t.toCompletelyPositiveMap x =
      x ⊗ₖ ((Fintype.card β : ℂ)⁻¹ • (1 : Matrix β β ℂ)) := by
  have star_ite (p : Prop) [Decidable p] (x y : ℂ) :
      star (if p then x else y) = if p then star x else star y := by
    split_ifs <;> rfl
  let q : ℂ := (Real.sqrt ((Fintype.card β : ℝ)⁻¹) : ℂ)
  have hq : star q = q := Complex.conj_ofReal _
  have hqq : q * q = (Fintype.card β : ℂ)⁻¹ := by
    dsimp [q]
    have h := congrArg Complex.ofReal (Real.mul_self_sqrt
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card β))))
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using h
  have hd : (Fintype.card β : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := β)
  let k : β → Matrix (α × β) α ℂ := fun b i j => if i.1 = j ∧ i.2 = b then q else 0
  have hk : ∑ b, (k b)ᴴ * k b = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type]
    dsimp [k]
    simp (config := { contextual := true }) only
      [starRingEnd_apply, star_ite, hq, star_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [Finset.sum_const_zero, Finset.sum_ite_irrel]
    try simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hqq, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ hd
    · simp [hij, Ne.symm hij]
  obtain ⟨t, ht⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel k hk
  refine ⟨t, fun x => ?_⟩
  rw [show matrixAction t.toCompletelyPositiveMap x = ∑ b, k b * x * (k b)ᴴ from ht x]
  ext ⟨i, b⟩ ⟨j, c⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    kronecker_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  dsimp [k]
  simp only [starRingEnd_apply, star_ite, hq, star_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hbc : b = c
  · subst c
    simp only [ite_true, mul_one]
    calc q * x i j * q = (q * q) * x i j := by ring
      _ = _ := by rw [hqq]; ring
  · simp [hbc, Ne.symm hbc]

private theorem pure_projectors_map_zero
    (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (he : ∀ a : α → ℂ, star a ⬝ᵥ a = 1 → e (vecMulVec a (star a)) = 0) : e = 0 := by
  have hh (x : Matrix α α ℂ) (hx : x.IsHermitian) : e x = 0 := by
    have hexp : x = ∑ i, (hx.eigenvalues i : ℂ) •
        vecMulVec (⇑(hx.eigenvectorBasis i)) (star ⇑(hx.eigenvectorBasis i)) := by
      ext j k
      conv_lhs => rw [hx.spectral_theorem, Unitary.conjStarAlgAut_apply,
        Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose]
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
    rw [hk, hprod]
    change _ = matrixAction t.toCompletelyPositiveMap
      (partialTraceRight (Matrix.kronecker (single i j z) (single k l 1)))
    rw [partialTraceRight_kronecker, map_smul]

private theorem pdm_reduction (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) :
    pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ))) := by
  generalize hn : cjMatrix (conditionalMap p a) = n
  unfold pdmBA partialTraceLeft
  generalize hm : cjMatrix (matrixAction p.toCompletelyPositiveMap) = m
  have hm_entry (i j : α₁ × β₁) (r s : α₂ × β₂) :
      m (i, r) (j, s) = matrixAction p.toCompletelyPositiveMap (single j i 1) r s := by
    rw [← hm, cj_entry]
  have hn_entry (i j : β₁) (r s : α₂) :
      n (i, r) (j, s) = conditionalMap p a (single j i 1) r s := by
    rw [← hn, cj_entry]
  ext ⟨k, r⟩ ⟨l, s⟩
  simp only [submatrix_apply, Matrix.smul_apply, Matrix.add_apply, mul_apply, ↓hm_entry, ↓hn_entry,
    kronecker_apply, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type,
    one_apply, Prod.mk.injEq, ite_and, mul_ite, ite_mul, one_mul, mul_one,
    zero_mul, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [conditional_entry, Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [smul_eq_mul]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1
  · simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      rw [Finset.sum_comm]
      arg 2; ext t
      arg 2; ext i
      rw [Finset.sum_comm]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2; ext t
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro z _
    ring
  · conv_lhs =>
      rw [Finset.sum_comm]
      arg 2; ext t
      rw [Finset.sum_comm]
      arg 2; ext i
      rw [Finset.sum_comm]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2; ext t
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro z _
    ring

private theorem basis_pair_units (i j : α) (hij : i ≠ j) (q : ℂ)
    (hq : star q = q) (hqq : q * q = 1 / 2) :
    star (q • ((Pi.single i 1 : α → ℂ) + (Pi.single j 1 : α → ℂ))) ⬝ᵥ
        (q • ((Pi.single i 1 : α → ℂ) + (Pi.single j 1 : α → ℂ))) = 1 ∧
    star (q • ((Pi.single i 1 : α → ℂ) - (Pi.single j 1 : α → ℂ))) ⬝ᵥ
        (q • ((Pi.single i 1 : α → ℂ) - (Pi.single j 1 : α → ℂ))) = 1 ∧
    star (q • ((Pi.single i 1 : α → ℂ) + (Pi.single j 1 : α → ℂ))) ⬝ᵥ
        (q • ((Pi.single i 1 : α → ℂ) - (Pi.single j 1 : α → ℂ))) = 0 := by
  simp only [star_smul, star_add, star_sub, Pi.star_single, star_one, hq,
    smul_dotProduct, dotProduct_smul, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, Pi.single_apply,
    hij, (Ne.symm hij), ite_false, ite_true, mul_one, mul_zero, smul_eq_mul]
  norm_num
  linear_combination 2 * hqq

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
    have h := hvan ((Pi.single j 1 : α → ℂ)) (Pi.single i 1)
      (by simp only [Pi.star_single, star_one, single_dotProduct, Pi.single_eq_same,
        mul_one])
      (by simp only [Pi.star_single, star_one, single_dotProduct, Pi.single_eq_same,
        mul_one])
      (by simp only [Pi.star_single, star_one, single_dotProduct,
        Pi.single_eq_of_ne (Ne.symm hij), mul_zero])
    simpa only [Pi.star_single, star_one, ← single_eq_single_vecMulVec_single] using h
  have hdiag (i j : α) : e (single i i 1) = e (single j j 1) := by
    by_cases hij : i = j
    · rw [hij]
    let q : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
    have hq : star q = q := Complex.conj_ofReal _
    have hqq : q * q = 1 / 2 := by
      dsimp [q]
      rw [← Complex.ofReal_mul]
      have h := congrArg Complex.ofReal (Real.mul_self_sqrt (by norm_num : 0 ≤ (1 / 2 : ℝ)))
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
      exact h
    obtain ⟨hb, hc, hbc⟩ := basis_pair_units i j hij q hq hqq
    have hz := hvan _ _ hb hc hbc
    simp only [star_smul, star_add, Pi.star_single, star_one, hq,
      smul_vecMulVec, vecMulVec_smul, smul_smul, hqq, sub_vecMulVec,
      vecMulVec_add, ← single_eq_single_vecMulVec_single, map_smul,
      map_sub, map_add, hoff i j hij, hoff j i (Ne.symm hij), add_zero, zero_add,
      sub_zero, zero_sub, smul_add, smul_neg, smul_smul, hqq] at hz
    have hz2 : (1 / 2 : ℂ) • (e (single i i 1) - e (single j j 1)) = 0 := by
      rw [smul_sub]
      exact hz
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz2).resolve_left (by norm_num))
  let i := Classical.choice (inferInstance : Nonempty α)
  refine ⟨e (single i i 1), fun x => ?_⟩
  rw [map_expansion]
  have hsingle (k l : α) : e (single k l 1) =
      if k = l then e (single i i 1) else 0 := by
    split_ifs with hkl
    · subst l
      exact hdiag k i
    · exact hoff k l hkl
  calc
    (∑ k, ∑ l, x k l • e (single k l 1)) =
        ∑ k, ∑ l, if k = l then x k l • e (single i i 1) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [hsingle k l]
      split_ifs <;> simp only [smul_zero]
    _ = _ := by
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← Finset.sum_smul]
      rfl

private theorem channel_adjoint (p : QuantumChannel α β) (x : Matrix α α ℂ) :
    matrixAction p.toCompletelyPositiveMap xᴴ = (matrixAction p.toCompletelyPositiveMap x)ᴴ := by
  have hm (y : Matrix α α ℂ) (hy : y.IsHermitian) :
      (matrixAction p.toCompletelyPositiveMap y).IsHermitian := by
    change IsSelfAdjoint (p.toCompletelyPositiveMap (CStarMatrix.ofMatrix y))
    exact (show IsSelfAdjoint (CStarMatrix.ofMatrix y) from hy).map'
      p.toCompletelyPositiveMap
  let y : Matrix α α ℂ := realPart x
  let z : Matrix α α ℂ := imaginaryPart x
  have hy : y.IsHermitian := (realPart x).property
  have hz : z.IsHermitian := (imaginaryPart x).property
  have hx : x = y + Complex.I • z := (realPart_add_I_smul_imaginaryPart x).symm
  rw [hx]
  simp only [conjTranspose_add, conjTranspose_smul, hy.eq, hz.eq, map_add,
    map_smul, (hm y hy).eq, (hm z hz).eq]

private theorem cj_hermitian (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (he : ∀ x, e xᴴ = (e x)ᴴ) : (cjMatrix e).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ⟨i, r⟩ ⟨j, s⟩
  rw [cj_entry, cj_entry]
  have h := congrArg (fun m : Matrix β β ℂ => m r s) (he (single i j 1))
  simpa only [conjTranspose_single, star_one, conjTranspose_apply] using h.symm

private theorem cj_pairing (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (x y : α → ℂ) (r s : β) :
    (∑ i, ∑ j, star (x i) * cjMatrix e (i, r) (j, s) * y j) =
      e (vecMulVec y (star x)) r s := by
  generalize hm : cjMatrix e = m
  have hm_entry (i j : α) (r s : β) : m (i, r) (j, s) = e (single j i 1) r s := by
    rw [← hm, cj_entry]
  rw [map_expansion e (vecMulVec y (star x))]
  simp only [↓hm_entry, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem tensor_pairing (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (x y : α → ℂ) (r s : β) :
    star (fun z : α × β => x z.1 * if z.2 = r then 1 else 0) ⬝ᵥ
      cjMatrix e *ᵥ (fun z : α × β => y z.1 * if z.2 = s then 1 else 0) =
      e (vecMulVec y (star x)) r s := by
  have star_ite (p : Prop) [Decidable p] (x y : ℂ) :
      star (if p then x else y) = if p then star x else star y := by
    split_ifs <;> rfl
  generalize hm : cjMatrix e = m
  change (∑ z : α × β, star (x z.1 * if z.2 = r then 1 else 0) *
    ∑ w : α × β, m z w * (y w.1 * if w.2 = s then 1 else 0)) = _
  simp only [Fintype.sum_prod_type, star_mul, star_ite, star_one, star_zero,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← hm, ← cj_pairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem projector_tensor (b x : α → ℂ) (s : β) :
    ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ
      (fun z : α × β => x z.1 * if z.2 = s then 1 else 0) =
    (star b ⬝ᵥ x) • (fun z : α × β => b z.1 * if z.2 = s then 1 else 0) := by
  funext ⟨i, r⟩
  change (∑ z : α × β, (b i * star (b z.1) * if r = z.2 then 1 else 0) *
    (x z.1 * if z.2 = s then 1 else 0)) =
    (∑ j, star (b j) * x j) * (b i * if r = s then 1 else 0)
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hrs : r = s
  · simp only [hrs, ite_true]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [hrs, ite_false, Finset.sum_const_zero]

private theorem cj_projector_trace (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (b : α → ℂ) :
    trace (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix β β ℂ)) * cjMatrix e) =
      trace (e (vecMulVec b (star b))) := by
  generalize hm : cjMatrix e = m
  have hm_entry (i j : α) (r s : β) : m (i, r) (j, s) = e (single j i 1) r s := by
    rw [← hm, cj_entry]
  change (∑ z : α × β, (((vecMulVec b (star b)) ⊗ₖ
    (1 : Matrix β β ℂ)) * m) z z) = ∑ r, e (vecMulVec b (star b)) r r
  simp only [Matrix.mul_apply, ↓hm_entry, kronecker_apply, vecMulVec_apply,
    Pi.star_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [map_expansion e (vecMulVec b (star b))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  rw [Finset.sum_comm]

private theorem pdm_hermitian_trace (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) (ha : star a ⬝ᵥ a = 1)
    (hb : star b ⬝ᵥ b = 1) :
    (pdmBA p a b).IsHermitian ∧ trace (pdmBA p a b) = 1 := by
  have hpa : (vecMulVec a (star a))ᴴ = vecMulVec a (star a) := by
    rw [conjTranspose_vecMulVec, star_star]
  have he (x : Matrix β₁ β₁ ℂ) :
      conditionalMap p a xᴴ = (conditionalMap p a x)ᴴ := by
    change partialTraceRight (matrixAction p.toCompletelyPositiveMap
      (vecMulVec a (star a) ⊗ₖ xᴴ)) =
      (partialTraceRight (matrixAction p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ x)))ᴴ
    have hinput : vecMulVec a (star a) ⊗ₖ xᴴ = (vecMulVec a (star a) ⊗ₖ x)ᴴ := by
      rw [conjTranspose_kronecker, hpa]
    rw [hinput, channel_adjoint]
    ext i j
    change (∑ t, star (matrixAction p.toCompletelyPositiveMap
      (vecMulVec a (star a) ⊗ₖ x) (j, t) (i, t))) =
      star (∑ t, matrixAction p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ x) (j, t) (i, t))
    exact (star_sum _ _).symm
  have hm := cj_hermitian (conditionalMap p a) he
  have hd : ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ))ᴴ =
      (vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_vecMulVec, star_star, conjTranspose_one]
  have ht : trace (conditionalMap p a (vecMulVec b (star b))) = 1 := by
    change trace (partialTraceRight (matrixAction p.toCompletelyPositiveMap
      (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b)))) = 1
    rw [trace_partialTraceRight]
    have hp := p.trace_preserving
      (CStarMatrix.ofMatrix (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b)))
    change trace (matrixAction p.toCompletelyPositiveMap
      (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b))) = _ at hp
    have hpraw : trace (matrixAction p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b))) =
        trace (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b)) := hp
    rw [hpraw, trace_kronecker, trace_vecMulVec, trace_vecMulVec,
      dotProduct_comm a (star a), dotProduct_comm b (star b), ha, hb, one_mul]
  constructor
  · rw [pdm_reduction]
    change ((1 / 2 : ℂ) • _)ᴴ = _
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
      conjTranspose_mul, hd, hm.eq, show star (1 / 2 : ℂ) = 1 / 2 by norm_num,
      add_comm]
  · rw [pdm_reduction, trace_smul, trace_add,
      trace_mul_comm (cjMatrix (conditionalMap p a)), cj_projector_trace, ht]
    norm_num

private theorem negative_minor (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b c : β₁ → ℂ)
    (hb : star b ⬝ᵥ b = 1) (hbc : star b ⬝ᵥ c = 0)
    (he : conditionalMap p a (vecMulVec c (star b)) ≠ 0)
    (hr : pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)))) :
    ¬ (pdmBA p a b).PosSemidef := by
  intro hpos
  obtain ⟨r, s, hrs⟩ : ∃ r s, conditionalMap p a (vecMulVec c (star b)) r s ≠ 0 := by
    by_contra hall
    apply he
    ext r s
    by_contra hn
    exact hall ⟨r, s, hn⟩
  let v : β₁ × α₂ → ℂ := fun z => c z.1 * if z.2 = s then 1 else 0
  let w : β₁ × α₂ → ℂ := fun z => b z.1 * if z.2 = r then 1 else 0
  let d := (vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)
  have hd : dᴴ = d := by
    dsimp [d]
    rw [conjTranspose_kronecker, conjTranspose_vecMulVec, star_star, conjTranspose_one]
  have hdv : d *ᵥ v = 0 := by
    change ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *ᵥ
      (fun z : β₁ × α₂ => c z.1 * if z.2 = s then 1 else 0) = 0
    rw [projector_tensor, hbc, zero_smul]
  have hdw : d *ᵥ w = w := by
    change ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *ᵥ
      (fun z : β₁ × α₂ => b z.1 * if z.2 = r then 1 else 0) = _
    rw [projector_tensor, hb, one_smul]
  have hvleft : star v ᵥ* d = 0 := by
    have h := congrArg star hdv
    rwa [star_mulVec, hd, star_zero] at h
  have hwleft : star w ᵥ* d = star w := by
    have h := congrArg star hdw
    rwa [star_mulVec, hd] at h
  have hquad : star v ⬝ᵥ (pdmBA p a b) *ᵥ v = 0 := by
    rw [hr]
    change star v ⬝ᵥ ((1 / 2 : ℂ) •
      (d * cjMatrix (conditionalMap p a) + cjMatrix (conditionalMap p a) * d)) *ᵥ v = 0
    rw [smul_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hdv,
      mulVec_zero, add_zero, dotProduct_smul, dotProduct_mulVec,
      hvleft, zero_dotProduct, smul_zero]
  have hkernel : (pdmBA p a b) *ᵥ v = 0 := hpos.dotProduct_mulVec_zero_iff.mp hquad
  have hzero : star w ⬝ᵥ (pdmBA p a b) *ᵥ v = 0 := by
    rw [hkernel, dotProduct_zero]
  rw [hr] at hzero
  change star w ⬝ᵥ ((1 / 2 : ℂ) •
    (d * cjMatrix (conditionalMap p a) + cjMatrix (conditionalMap p a) * d)) *ᵥ v = 0 at hzero
  rw [smul_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hdv,
    mulVec_zero, add_zero, dotProduct_smul, dotProduct_mulVec, hwleft] at hzero
  have hpair := tensor_pairing (conditionalMap p a) b c r s
  change star w ⬝ᵥ cjMatrix (conditionalMap p a) *ᵥ v = _ at hpair
  rw [hpair, smul_eq_mul] at hzero
  exact hrs ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

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
    (negative_minor p a b c hb hbc hcross (pdm_reduction p a b))⟩

end D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
