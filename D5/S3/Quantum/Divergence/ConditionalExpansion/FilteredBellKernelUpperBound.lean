/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Inverse environment marginal bounds finite conditional expansion. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap

/-!
# Kernel projection of a filtered isometry complement

For a Hermitian invertible filter `S` and a column isometry `U`, the kernel
of `S * (1 - U * Uᴴ) * S` is the column space of `Z = S⁻¹ * U`.
The projection onto that space has trace pairing with `S * U * Uᴴ * S`
equal to the trace of the inverse Gram matrix of `Z`.

For the normalized CPTP filter, the padded Bell pairs bound the
finite-reference conditional trace-distance expansion coefficient in
Hirche–George–Nuradha–Wilde, arXiv:2608.27171v1, §2.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped ComplexOrder Matrix

namespace FilteredBellKernelProjection

/-- The Gram matrix of the filtered columns is invertible. Its inverse gives
the orthogonal projection onto the kernel of the filtered complement. -/
theorem bell_kernel_projection
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : Matrix ι ι ℂ) (U : Matrix ι κ ℂ)
    (hS : S.IsHermitian) (hSunit : IsUnit S)
    (hU : Uᴴ * U = 1) :
    let Z := S⁻¹ * U
    let M := Zᴴ * Z
    let Q := Z * M⁻¹ * Zᴴ
    IsUnit M ∧ IsStarProjection Q ∧
      (∀ x : ι → ℂ, (S * (1 - U * Uᴴ) * S) *ᵥ x = 0 ↔ Q *ᵥ x = x) ∧
      (Matrix.trace (Q * (S * U * Uᴴ * S)) = Matrix.trace M⁻¹) := by
  intro Z M Q
  let : Invertible S := hSunit.invertible
  have hSZ : S * Z = U := Matrix.mul_inv_cancel_left_of_invertible S U
  have hUinj : Function.Injective U.mulVec := by
    intro x y hxy
    have h := congrArg (fun w => Uᴴ *ᵥ w) hxy
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using h
  have hZinj : Function.Injective Z.mulVec := by
    intro x y hxy
    apply hUinj
    have h := congrArg (fun w => S *ᵥ w) hxy
    simpa only [Matrix.mulVec_mulVec, hSZ] using h
  have hMpos : M.PosDef := Matrix.PosDef.conjTranspose_mul_self Z hZinj
  have hMunit : IsUnit M := hMpos.isUnit
  let : Invertible M := hMunit.invertible
  have hQherm : Q.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose Z hMpos.isHermitian.inv
  have hGram : Zᴴ * Z = M := rfl
  have hQZ : Q * Z = Z := by
    simp only [Q, Matrix.mul_assoc, hGram, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc
      Q * Q = (Q * Z) * M⁻¹ * Zᴴ := by
        change Q * (Z * M⁻¹ * Zᴴ) = _
        simp only [Matrix.mul_assoc]
      _ = Q := by rw [hQZ]
  let C : Matrix ι ι ℂ := 1 - U * Uᴴ
  let B := S * C * S
  have hCU : C * U = 0 := by
    simp only [C, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one,
      sub_self]
  have hBZ : B * Z = 0 := by
    calc
      B * Z = S * (C * (S * Z)) := by simp only [B, Matrix.mul_assoc]
      _ = 0 := by rw [hSZ, hCU, Matrix.mul_zero]
  have hBaction (x : ι → ℂ) : B *ᵥ x = S *ᵥ (C *ᵥ (S *ᵥ x)) := by
    simp only [B, ← Matrix.mulVec_mulVec]
  have hkernel (x : ι → ℂ) : B *ᵥ x = 0 ↔ ∃ v : κ → ℂ, Z *ᵥ v = x := by
    constructor
    · intro hx
      have hCx : C *ᵥ (S *ᵥ x) = 0 := by
        apply Matrix.mulVec_injective_of_invertible S
        rw [← hBaction, hx, Matrix.mulVec_zero]
      have hfix : U *ᵥ (Uᴴ *ᵥ (S *ᵥ x)) = S *ᵥ x := by
        have h := hCx
        simp only [C, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
          sub_eq_zero] at h
        exact h.symm
      refine ⟨Uᴴ *ᵥ (S *ᵥ x), ?_⟩
      change (S⁻¹ * U) *ᵥ (Uᴴ *ᵥ (S *ᵥ x)) = x
      rw [← Matrix.mulVec_mulVec, hfix, Matrix.mulVec_mulVec,
        Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    · rintro ⟨v, rfl⟩
      rw [Matrix.mulVec_mulVec, hBZ, Matrix.zero_mulVec]
  have hfixed (x : ι → ℂ) : Q *ᵥ x = x ↔ ∃ v : κ → ℂ, Z *ᵥ v = x := by
    constructor
    · intro hx
      refine ⟨M⁻¹ *ᵥ (Zᴴ *ᵥ x), ?_⟩
      simpa only [Q, ← Matrix.mulVec_mulVec] using hx
    · rintro ⟨v, rfl⟩
      rw [Matrix.mulVec_mulVec, hQZ]
  have hZS : Zᴴ * S = Uᴴ := by
    simpa only [Matrix.conjTranspose_mul, hS.eq] using
      congrArg Matrix.conjTranspose hSZ
  have htrace : Matrix.trace (Q * (S * U * Uᴴ * S)) = Matrix.trace M⁻¹ := by
    calc
      _ = Matrix.trace (Z * (M⁻¹ * (Zᴴ * (S * U * Uᴴ * S)))) := by
        simp only [Q, Matrix.mul_assoc]
      _ = Matrix.trace ((M⁻¹ * (Zᴴ * (S * U * Uᴴ * S))) * Z) :=
        Matrix.trace_mul_comm Z _
      _ = Matrix.trace (M⁻¹ * ((Zᴴ * S) * U * Uᴴ * (S * Z))) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace M⁻¹ := by
        rw [hZS, hSZ, hU, Matrix.one_mul, hU, Matrix.mul_one]
  exact ⟨hMunit, ⟨hQQ, hQherm.isSelfAdjoint⟩,
    fun x => (hkernel x).trans (hfixed x).symm, htrace⟩

end FilteredBellKernelProjection

open scoped CStarAlgebra MatrixOrder Kronecker Matrix.Norms.L2Operator

open RHLinalg (rtrace)
open D5.S3.Quantum.Divergence.ConditionalExpansion (exists_bell_kernel_ratio_le)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act amp gap ratios)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
  (bellProjector)
open FilteredChannelConditionalGap
  (filterAction filtered_channel_ratio_lower_bound)
open UnitaryReconstruction.LiuWildChoiObstruction (bell diagonalVector outer pairMatrix)
open private amp_filterAction from
  D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap

namespace FilteredBellKernelProjection

noncomputable section

variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]

private def bellColumns : Matrix (A × (A × E)) E ℂ :=
  fun i f => bell A (i.1, i.2.1) * (1 : Matrix E E ℂ) i.2.2 f

private theorem bellColumns_mul_adjoint :
    (bellColumns (A := A) (E := E)) * (bellColumns (A := A) (E := E))ᴴ =
      (bellProjector A ⊗ₖ (1 : Matrix E E ℂ)).reindex
        (Equiv.prodAssoc A A E) (Equiv.prodAssoc A A E) := by
  ext ⟨r, a, f⟩ ⟨s, b, g⟩
  by_cases h : f = g
  · subst g
    simp [bellColumns, bellProjector, outer, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, ite_mul, mul_ite]
  · simp [bellColumns, bellProjector, outer, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, ite_mul, mul_ite, h, Ne.symm h]

private theorem bell_compress [Nonempty A] (H : Matrix (A × E) (A × E) ℂ) :
    (bellColumns (A := A) (E := E))ᴴ * ((1 : Matrix A A ℂ) ⊗ₖ H) *
        bellColumns (A := A) (E := E) =
      (Fintype.card A : ℝ)⁻¹ • partialTraceLeft H := by
  let c : ℂ := (↑(Real.sqrt (Fintype.card A)) : ℂ)⁻¹
  have hcolumn (r a : A) (f g : E) :
      bellColumns (r, a, f) g = if r = a then if f = g then c else 0 else 0 := by
    by_cases h : r = a <;> simp [bellColumns, bell, diagonalVector, c, Matrix.one_apply, h, mul_ite]
  have hreal : star c * c = (Fintype.card A : ℂ)⁻¹ := by
    have hs : (↑(Real.sqrt (Fintype.card A)) : ℂ) ^ 2 = (Fintype.card A : ℂ) := by
      exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card A by positivity)
    simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← pow_two, inv_pow, hs]
  have hmul (r a : A) (f g : E) :
      (((1 : Matrix A A ℂ) ⊗ₖ H) * bellColumns (A := A) (E := E)) (r, a, f) g =
        H (a, f) (r, g) * c := by
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
      hcolumn, ite_mul, mul_ite]
  rw [Matrix.mul_assoc]
  ext f g
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Complex.real_smul,
    partialTraceLeft, Fintype.sum_prod_type, hcolumn, hmul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = star c * (H (r, f) (r, g) * c) := by
      simp [apply_ite, ite_mul, Finset.sum_ite_irrel]
    _ = _ := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast, ← hreal]
      ac_rfl

private theorem bellColumns_isometry [Nonempty A] :
    (bellColumns (A := A) (E := E))ᴴ * bellColumns (A := A) (E := E) = 1 := by
  have h := bell_compress (1 : Matrix (A × E) (A × E) ℂ)
  rw [Matrix.one_kronecker_one, Matrix.mul_one] at h
  rw [h]
  ext f g
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hfg : f = g
  · subst g
    simp [partialTraceLeft, Complex.real_smul, hd]
  · simp [partialTraceLeft, hfg]

/-- The orthogonal projection specified by a positive semidefinite matrix's kernel
is the complement of its spectral support. -/
private theorem kernel_projection_eq {n : Type} [Fintype n] [DecidableEq n]
    {B Q : Matrix n n ℂ} (hB : B.PosSemidef) (hQ : IsStarProjection Q)
    (hker : ∀ v, B *ᵥ v = 0 ↔ Q *ᵥ v = v) :
    Q = 1 - spectralSupport B := by
  let P := 1 - spectralSupport B
  obtain ⟨hRadj, _, hSadj, _, _, _, hSB, _⟩ := spectral_sqrt_normalization B hB
  obtain ⟨_, hWR, _, _⟩ := spectral_sqrt_inverse_products B hB
  have hP : P.IsHermitian := by
    change (1 - spectralSupport B)ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hSadj]
  have hBP : B * P = 0 := by
    have hBS : B * spectralSupport B = B := by
      simpa only [Matrix.conjTranspose_mul, hSadj, hB.isHermitian.eq] using
        congrArg Matrix.conjTranspose hSB
    simp [P, Matrix.mul_sub, hBS]
  have hpker (v : n → ℂ) : B *ᵥ v = 0 ↔ P *ᵥ v = v := by
    constructor
    · intro hv
      have hRv : CFC.sqrt B *ᵥ v = 0 := by
        apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt B) v).mp
        rwa [hRadj, CFC.sqrt_mul_sqrt_self B hB.nonneg]
      have hSv : spectralSupport B *ᵥ v = 0 := by
        rw [← hWR, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_zero]
      simp [P, Matrix.sub_mulVec, hSv]
    · intro hv
      conv_lhs => rw [← hv]
      rw [Matrix.mulVec_mulVec, hBP, Matrix.zero_mulVec]
  have hPQ : P * Q = Q := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec]
    apply (hpker _).mp
    apply (hker _).mpr
    rw [Matrix.mulVec_mulVec, hQ.isIdempotentElem]
  have hQP : Q * P = P := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec]
    apply (hker _).mp
    rw [Matrix.mulVec_mulVec, hBP, Matrix.zero_mulVec]
  have hQadj : Qᴴ = Q := hQ.isSelfAdjoint.star_eq
  simpa only [Matrix.conjTranspose_mul, hQadj, hP.eq, hQP] using
    congrArg Matrix.conjTranspose hPQ.symm

private theorem filtered_bell_kernel_weight [Nonempty A] [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (hG : G.PosDef)
    (N : QuantumChannel A (A × E)) (hN : ∀ X, act N X = filterAction G X) :
    let P := bellProjector A
    let B := amp N (1 - P)
    rtrace ((1 - spectralSupport B) * amp N P) =
      rtrace (((Fintype.card A : ℝ)⁻¹ • partialTraceLeft G⁻¹)⁻¹) / Fintype.card E := by
  intro P B
  let a : ℝ := (Fintype.card E : ℝ)⁻¹
  let U : Matrix (A × (A × E)) E ℂ := bellColumns
  let S := (1 : Matrix A A ℂ) ⊗ₖ CFC.sqrt G
  let W := (1 : Matrix A A ℂ) ⊗ₖ G
  let Z := S⁻¹ * U
  let M := Zᴴ * Z
  let Q := Z * M⁻¹ * Zᴴ
  have hU : Uᴴ * U = 1 := bellColumns_isometry
  have hP : U * Uᴴ = (P ⊗ₖ (1 : Matrix E E ℂ)).reindex
        (Equiv.prodAssoc A A E) (Equiv.prodAssoc A A E) :=
    bellColumns_mul_adjoint
  have hS : S.IsHermitian :=
    (Matrix.PosSemidef.one.kronecker (CFC.sqrt_nonneg G).posSemidef).isHermitian
  have hSS : S * S = W := by
    simp only [S, W, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  have hW : W.PosDef := Matrix.PosDef.one.kronecker hG
  have hSunit : IsUnit S := isUnit_mul_self_iff.mp (hSS ▸ hW.isUnit)
  obtain ⟨_, hQ, hker, hweight⟩ := bell_kernel_projection S U hS hSunit hU
  change IsStarProjection Q at hQ
  change ∀ v, (S * (1 - U * Uᴴ) * S) *ᵥ v = 0 ↔ Q *ᵥ v = v at hker
  change trace (Q * (S * U * Uᴴ * S)) = trace M⁻¹ at hweight
  have hM : M = (Fintype.card A : ℝ)⁻¹ • partialTraceLeft G⁻¹ := by
    have hWinv : W⁻¹ = (1 : Matrix A A ℂ) ⊗ₖ G⁻¹ := by
      simp [W, Matrix.inv_kronecker]
    calc
      M = Uᴴ * (S⁻¹ * S⁻¹) * U := by
        simp only [M, Z, Matrix.conjTranspose_mul, hS.inv.eq, Matrix.mul_assoc]
      _ = Uᴴ * W⁻¹ * U := by rw [← hSS, Matrix.mul_inv_rev]
      _ = _ := by rw [hWinv]; exact bell_compress _
  have hX : amp N P = a • (S * U * Uᴴ * S) := by
    rw [amp_filterAction G N hN, ← hP]
    simp only [S, a, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hB : B = a • (S * (1 - U * Uᴴ) * S) := by
    change amp N (1 - P) = _
    rw [amp_filterAction G N hN]
    have hsub : (((1 - P) ⊗ₖ (1 : Matrix E E ℂ)).reindex
        (Equiv.prodAssoc A A E) (Equiv.prodAssoc A A E)) = 1 - U * Uᴴ := by
      rw [hP]
      change (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A A E))
          ((1 - P) ⊗ₖ (1 : Matrix E E ℂ)) =
        1 - (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A A E))
          (P ⊗ₖ (1 : Matrix E E ℂ))
      have hlin : (1 - P) ⊗ₖ (1 : Matrix E E ℂ) =
          1 - P ⊗ₖ (1 : Matrix E E ℂ) := by
        apply eq_sub_iff_add_eq.mpr
        rw [← Matrix.add_kronecker, sub_add_cancel, Matrix.one_kronecker_one]
      rw [hlin, map_sub, map_one]
    rw [hsub]
    simp only [S, a, Matrix.mul_smul, Matrix.smul_mul]
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hBpsd : B.PosSemidef := by
    rw [hB]
    apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hproj : IsStarProjection (U * Uᴴ) := by
      refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
      · calc
          _ = U * (Uᴴ * U) * Uᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hU, Matrix.mul_one]
      · change (U * Uᴴ)ᴴ = U * Uᴴ
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simpa only [hS.eq] using hproj.one_sub.nonneg.posSemidef.mul_mul_conjTranspose_same S
  have hkerB (v : A × (A × E) → ℂ) : B *ᵥ v = 0 ↔ Q *ᵥ v = v := by
    rw [hB, Matrix.smul_mulVec, smul_eq_zero, or_iff_right ha]
    exact hker v
  have hQeq : Q = 1 - spectralSupport B := kernel_projection_eq hBpsd hQ hkerB
  rw [← hQeq, hX, Matrix.mul_smul]
  change (trace (a • (Q * (S * U * Uᴴ * S)))).re = _
  rw [Matrix.trace_smul, Complex.smul_re, hweight, hM]
  simp only [smul_eq_mul, a, div_eq_mul_inv, rtrace, RCLike.re_to_complex, mul_comm]

/-- For a positive-definite normalized filter, the finite-reference conditional
trace-distance expansion infimum is at most the normalized trace of the
inverse of the filter's normalized inverse marginal over the input. -/
theorem filtered_channel_bell_upper_bound [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel A (A × E)) (hN : ∀ X, act N X = filterAction G X)
    (hd : 2 ≤ Fintype.card A) (γ : ℝ) (hγ : 1 ≤ γ) (orth : Bool) :
    sInf (ratios N γ orth) ≤
      rtrace (((Fintype.card A : ℝ)⁻¹ • partialTraceLeft G⁻¹)⁻¹) / Fintype.card E := by
  let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have hweight := filtered_bell_kernel_weight G hG N hN
  dsimp only at hweight
  have htransfer := D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.result
  unfold D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.claim at htransfer
  have hsets := htransfer A (A × E) N
  have hratios : ratios N γ orth = ratios N 1 true := by
    have h := (hsets.2 γ 1 hγ le_rfl).trans (hsets.1 1 le_rfl)
    cases orth
    · exact h
    · exact (hsets.1 γ hγ).symm.trans h
  have hbdd : BddBelow (ratios N γ orth) := by
    refine ⟨‖((Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹)‖⁻¹, ?_⟩
    exact fun _ hx => filtered_channel_ratio_lower_bound G hG hnorm N hN γ orth hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ρ, σ, horth, hgap, hratio⟩ := exists_bell_kernel_ratio_le N hd ε hε
  let x := gap 1 (amp N (pairMatrix ρ)) (amp N (pairMatrix σ)) /
    gap 1 (pairMatrix ρ) (pairMatrix σ)
  have hx : x ∈ ratios N γ orth := by
    rw [hratios]
    exact ⟨Option A, inferInstance, inferInstance, pairMatrix ρ, pairMatrix σ,
      density_posSemidef ρ, ρ.2.2, density_posSemidef σ, σ.2.2, fun _ => horth, hgap, rfl⟩
  rw [hweight] at hratio
  exact (csInf_le hbdd hx).trans hratio

/-- info: 'FilteredBellKernelProjection.bell_kernel_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bell_kernel_projection
/--
info: 'FilteredBellKernelProjection.filtered_channel_bell_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms filtered_channel_bell_upper_bound
end

end FilteredBellKernelProjection
