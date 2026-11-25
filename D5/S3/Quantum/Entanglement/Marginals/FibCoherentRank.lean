/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A residual determinant criterion for bounded rational rank at positive occupation. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity

/-! Rank transport across scalar Schur elimination and rational residual purity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Complex
open scoped ComplexOrder ComplexConjugate Matrix
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

namespace D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank

theorem assemble_rank {n : Type} [Fintype n]
    (b : ℝ) (hb : b ≠ 0) (v : n → ℂ) (T : Matrix n n ℂ) :
    (assemble b v T).rank = (T - correction b v).rank + 1 := by
  classical
  let P := pivot b
  let B := cross v
  let S := T - correction b v
  let : Invertible P := (pivot_isUnit hb).invertible
  have hS : T - Bᴴ * ⅟P * B = S := by
    rw [invOf_eq_nonsing_inv, correction_eq_schur b hb v]
  let U : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ := fromBlocks 1 (⅟P * B) 0 1
  let V : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ := fromBlocks 1 0 (Bᴴ * ⅟P) 1
  let D : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ := fromBlocks P 0 0 S
  have hU : IsUnit U := Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩
  have hV : IsUnit V := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩
  have h : assemble b v T = V * D * U := by
    simpa only [assemble, ← hS, V, D, U] using Matrix.fromBlocks_eq_of_invertible₁₁ P B Bᴴ T
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hV)]
  let e := LinearEquiv.sumArrowLequivProdArrow Unit n ℂ ℂ
  have hprod : P.mulVecLin.prodMap S.mulVecLin =
      (e : _ →ₗ[ℂ] _).comp (D.mulVecLin.comp (e.symm : _ →ₗ[ℂ] _)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change P.mulVec x.1 i = D.mulVec (e.symm x) (Sum.inl i)
      have he : (e.symm x) ∘ Sum.inl = x.1 := by funext j; rfl
      simp [D, fromBlocks_mulVec, he]
    · funext i
      change S.mulVec x.2 i = D.mulVec (e.symm x) (Sum.inr i)
      have he : (e.symm x) ∘ Sum.inr = x.2 := by funext j; rfl
      simp [D, fromBlocks_mulVec, he]
  have hrange := congrArg LinearMap.range hprod
  rw [LinearMap.range_prodMap, LinearMap.range_comp, LinearEquiv.range_comp] at hrange
  have hD : D.rank = P.rank + S.rank := by
    change Module.finrank ℂ D.mulVecLin.range =
      Module.finrank ℂ P.mulVecLin.range + Module.finrank ℂ S.mulVecLin.range
    rw [← LinearEquiv.finrank_map_eq e D.mulVecLin.range, ← hrange,
      (Submodule.prodEquiv P.mulVecLin.range S.mulVecLin.range).finrank_eq, Module.finrank_prod]
  have hP : P.rank = 1 := by
    simpa using Matrix.rank_of_isUnit P (pivot_isUnit hb)
  rw [hD, hP, add_comm]

private theorem rational_middleRow {u v w z : ℂ}
    (qu : RationalEntry u) (qv : RationalEntry v)
    (qw : RationalEntry w) (qz : RationalEntry z) (i : Bool × Bool) :
    RationalEntry (middleRow u v w z i) := by
  rcases i with ⟨i, j⟩
  cases i <;> cases j
  · exact qu
  · exact qw
  · exact qv
  · exact qz

private theorem rational_pivot_of_trace {b : ℝ} {L : Matrix Bool Bool ℂ}
    (ht : L.trace + (b : ℂ) = 1) (qL : ∀ i j, RationalEntry (L i j)) :
    RationalEntry (b : ℂ) := by
  rw [show (b : ℂ) = 1 - L.trace by linear_combination ht]
  exact rationalComplex.sub_mem rationalComplex.one_mem
    (rationalComplex.sum_mem fun i _ => qL i i)

private theorem rational_correction {n : Type*} {b : ℝ} {row : n → ℂ}
    (qb : RationalEntry (b : ℂ)) (qrow : ∀ i, RationalEntry (row i))
    (i j : n) : RationalEntry (correction b row i j) := by
  change RationalEntry ((↑b⁻¹ : ℂ) * (conj (row i) * row j))
  rw [Complex.ofReal_inv]
  exact rationalComplex.mul_mem (rationalComplex.inv_mem qb)
    (rationalComplex.mul_mem (rationalConjugate ⟨_, qrow i⟩).property (qrow j))

private theorem rational_original_assemble_iff {b : ℝ} {row : Bool × Bool → ℂ}
    {T : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (qb : RationalEntry (b : ℂ)) (qrow : ∀ i, RationalEntry (row i)) :
    (∀ i j, RationalEntry (original (assemble b row T) i j)) ↔
      ∀ i j, RationalEntry (T i j) := by
  constructor
  · intro h i j
    simpa only [original, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      assemble, Matrix.fromBlocks_apply₂₂] using h (wordEquiv (.inr i)) (wordEquiv (.inr j))
  · intro h i j
    change RationalEntry (assemble b row T (wordEquiv.symm i) (wordEquiv.symm j))
    cases wordEquiv.symm i <;> cases wordEquiv.symm j
    · rename_i a c
      cases a
      cases c
      exact qb
    · apply qrow
    · exact (rationalConjugate ⟨_, qrow _⟩).property
    · apply h

/-- At positive middle occupation the rational joint residual determines the
rational global rank, with one extra dimension for the middle singleton. -/
private theorem rational_rank_at_iff (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ) (k : ℕ)
    (hb : 0 < b) (ht : L.trace + (b : ℂ) = 1) (qL : ∀ i j, RationalEntry (L i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (qz : RationalEntry z) :
    let C := correction b (middleRow u v w z)
    (∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ρ.rank ≤ k + 1 ∧ ∀ i j, RationalEntry (ρ i j)) ↔
    (∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ, S.PosSemidef ∧
      partialTraceRight S = L - partialTraceRight C ∧
      partialTraceLeft S = R - partialTraceLeft C ∧ S.rank ≤ k ∧
      ∀ i j, RationalEntry (S i j)) := by
  dsimp only
  let row := middleRow u v w z
  let C := correction b row
  have qb := rational_pivot_of_trace ht qL
  have qr := rational_middleRow qu qv qw qz
  have qC := rational_correction qb qr
  have hrank (T : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
      (original (assemble b row T)).rank = (T - C).rank + 1 := by
    rw [original, Matrix.rank_submatrix, assemble_rank b hb.ne']
  constructor
  · rintro ⟨ρ, hρ, hdata, hr, hq⟩
    obtain ⟨T, rfl, hS, hTL, hTR⟩ := extension_blocks hρ hdata
    have qT := (rational_original_assemble_iff qb qr).mp hq
    rw [hrank] at hr
    refine ⟨T - C, hS, by rw [partialTraceRight_sub, hTL],
      by rw [partialTraceLeft_sub, hTR], Nat.le_of_add_le_add_right hr, ?_⟩
    exact fun i j => rationalComplex.sub_mem (qT i j) (qC i j)
  · rintro ⟨S, hS, hSL, hSR, hr, hq⟩
    change partialTraceRight S = L - partialTraceRight C at hSL
    change partialTraceLeft S = R - partialTraceLeft C at hSR
    let T := S + C
    have hT : T - C = S := add_sub_cancel_right _ _
    have hTL : partialTraceRight T = L := by
      rw [show T = S + C from rfl, partialTraceRight_add, hSL, sub_add_cancel]
    have hTR : partialTraceLeft T = R := by
      rw [show T = S + C from rfl, partialTraceLeft_add, hSR, sub_add_cancel]
    have hpos : (assemble b row T).PosSemidef :=
      (block_psd b row T).mpr ⟨hb.le, fun h => (hb.ne' h).elim, hT ▸ hS⟩
    refine ⟨original (assemble b row T), hpos.submatrix _, ⟨?_, ?_, ?_, rfl⟩,
      by simpa only [hrank, hT] using Nat.add_le_add_right hr 1,
      (rational_original_assemble_iff qb qr).mpr ?_⟩
    · rwa [trace_original, trace_assemble, ← trace_partialTraceRight T, hTL]
    · rw [left_read, hTL]
      rfl
    · rw [right_read, hTR]
      rfl
    · exact fun i j => rationalComplex.add_mem (hq i j) (qC i j)

theorem rankOneDensity_of_rank_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (ht : S.trace = 1) (hr : S.rank ≤ 1) :
    ∃ ψ : n → ℂ, S = rankOneDensity ψ := by
  let h := hS.isHermitian
  let U : Matrix n n ℂ := h.eigenvectorUnitary
  have hnz : h.eigenvalues ≠ 0 := fun he =>
    one_ne_zero (ht.symm.trans (by simp [h.eigenvalues_eq_zero_iff.mp he]))
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hnz
  have hc : Fintype.card {i // h.eigenvalues i ≠ 0} ≤ 1 := by
    rwa [← h.rank_eq_card_non_zero_eigs]
  let := Fintype.card_le_one_iff_subsingleton.mp hc
  have hdiag (i : n) : h.eigenvalues i = if i = j then h.eigenvalues j else 0 := by
    split_ifs with hij
    · rw [hij]
    · by_contra hi
      exact hij (congrArg Subtype.val (Subsingleton.elim
        (⟨i, hi⟩ : {i // h.eigenvalues i ≠ 0}) ⟨j, hj⟩))
  let c := Real.sqrt (h.eigenvalues j)
  let ψ : n → ℂ := fun i => (c : ℂ) * U i j
  have hsquare : c * c = h.eigenvalues j := Real.mul_self_sqrt (hS.eigenvalues_nonneg j)
  have hd : diagonal (RCLike.ofReal ∘ h.eigenvalues : n → ℂ) =
      diagonal (fun i => if i = j then (h.eigenvalues j : ℂ) else 0) := by
    congr 1
    funext i
    rw [Function.comp_apply, hdiag i]
    split_ifs <;> rfl
  refine ⟨ψ, ?_⟩
  rw [h.spectral_theorem, hd, Unitary.conjStarAlgAut_apply]
  change U * diagonal (fun i => if i = j then (h.eigenvalues j : ℂ) else 0) * Uᴴ =
    rankOneDensity ψ
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left rfl, if_true, rankOneDensity, vecMulVec_apply, Pi.star_apply, ψ,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    calc
      _ = ((↑c : ℂ) * ↑c) * (U i j * conj (U k j)) := by
        rw [← Complex.ofReal_mul, hsquare]
        ring
      _ = _ := by ring
  · intro l _ hlj
    simp [hlj]
  · simp

private theorem partialTraceRight_smul (c : ℂ) (S : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    partialTraceRight (c • S) = c • partialTraceRight S := by
  ext i j
  simp [partialTraceRight, mul_add]

private theorem partialTraceLeft_smul (c : ℂ) (S : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    partialTraceLeft (c • S) = c • partialTraceLeft S := by
  ext i j
  simp [partialTraceLeft, mul_add]

private theorem normSq_real_mul (t : ℝ) (z : ℂ) :
    (normSq ((t : ℂ) * z) : ℂ) = (t : ℂ)^2 * (normSq z : ℂ) := by
  rw [normSq_mul, normSq_ofReal, Complex.ofReal_mul, Complex.ofReal_mul, pow_two]

private theorem residual_rank_le_one_iff (X Y : Matrix Bool Bool ℂ)
    (ht : X.trace = Y.trace)
    (qX : ∀ i j, RationalEntry (X i j)) (qY : ∀ i j, RationalEntry (Y i j)) :
    (∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ, S.PosSemidef ∧
      partialTraceRight S = X ∧ partialTraceLeft S = Y ∧ S.rank ≤ 1 ∧
      ∀ i j, RationalEntry (S i j)) ↔
    X.PosSemidef ∧ Y.PosSemidef ∧ X.det = Y.det ∧
      ∃ z : ℂ, RationalEntry z ∧ (normSq z : ℂ) = X.det := by
  by_cases h0 : X.trace = 0
  · have hzL : partialTraceRight (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
      ext i j
      simp [partialTraceRight]
    have hzR : partialTraceLeft (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
      ext i j
      simp [partialTraceLeft]
    constructor
    · rintro ⟨S, hS, hSX, hSY, _, _⟩
      have hs0 : S.trace = 0 := by rw [← trace_partialTraceRight S, hSX, h0]
      have hs := hS.trace_eq_zero_iff.mp hs0
      rw [hs, hzL] at hSX
      rw [hs, hzR] at hSY
      rw [← hSX, ← hSY]
      exact ⟨.zero, .zero, rfl, 0, rationalComplex.zero_mem, by simp⟩
    · rintro ⟨hX, hY, _, _⟩
      have hx0 := hX.trace_eq_zero_iff.mp h0
      have hy0 := hY.trace_eq_zero_iff.mp (ht.symm.trans h0)
      exact ⟨0, .zero, hzL.trans hx0.symm, hzR.trans hy0.symm,
        by simp, fun _ _ => rationalComplex.zero_mem⟩
  let t := X.trace.re
  let X₁ := (↑t⁻¹ : ℂ) • X
  let Y₁ := (↑t⁻¹ : ℂ) • Y
  have qt : RationalEntry X.trace := rationalComplex.sum_mem fun i _ => qX i i
  have norm_data (hX : X.PosSemidef) :
      0 < t ∧ (t : ℂ) = X.trace ∧ X₁.trace = 1 ∧ Y₁.trace = 1 := by
    have h := Complex.nonneg_iff.mp hX.trace_nonneg
    have htC : (t : ℂ) = X.trace := Complex.ext rfl (by simpa using h.2)
    have htpos : 0 < t := lt_of_le_of_ne h.1 (fun hz => h0 (by simpa [← hz] using htC.symm))
    have hcancel : (↑t⁻¹ : ℂ) * X.trace = 1 := by
      rw [← htC, ← Complex.ofReal_mul, inv_mul_cancel₀ htpos.ne', Complex.ofReal_one]
    exact ⟨htpos, htC, by simpa [X₁, Matrix.trace_smul] using hcancel,
      by simpa [Y₁, Matrix.trace_smul, ← ht] using hcancel⟩
  have detX : X₁.det = (↑t⁻¹ : ℂ)^2 * X.det := by simp [X₁]
  have detY : Y₁.det = (↑t⁻¹ : ℂ)^2 * Y.det := by simp [Y₁]
  constructor
  · rintro ⟨S, hS, hSX, hSY, hr, qS⟩
    have hX := hSX ▸ partialTraceRight_posSemidef hS
    have hY := hSY ▸ partialTraceLeft_posSemidef hS
    obtain ⟨hp, htC, hX₁, _⟩ := norm_data hX
    let S₁ := (↑t⁻¹ : ℂ) • S
    have hi : (↑t⁻¹ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hp.ne')
    have hS₁ : S₁.PosSemidef := hS.smul (by exact_mod_cast (inv_nonneg.mpr hp.le))
    have hSX₁ : partialTraceRight S₁ = X₁ := by
      change partialTraceRight ((↑t⁻¹ : ℂ) • S) = _
      rw [partialTraceRight_smul, hSX]
    have hSY₁ : partialTraceLeft S₁ = Y₁ := by
      change partialTraceLeft ((↑t⁻¹ : ℂ) • S) = _
      rw [partialTraceLeft_smul, hSY]
    have ht₁ : S₁.trace = 1 := by rw [← trace_partialTraceRight S₁, hSX₁, hX₁]
    have hr₁ : S₁.rank ≤ 1 := by
      change (((↑t⁻¹ : ℂ) • S)).rank ≤ 1
      rwa [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hi)]
    obtain ⟨ψ, hψ⟩ := rankOneDensity_of_rank_le_one hS₁ ht₁ hr₁
    let M : Matrix Bool Bool ℂ := fun i j => ψ (i,j)
    rw [hψ, leftGram M] at hSX₁
    rw [hψ, rightGram M] at hSY₁
    have qS₁ (i j : Bool × Bool) :
        RationalEntry (rankOneDensity (Function.uncurry M) i j) := by
      change RationalEntry (rankOneDensity ψ i j)
      rw [← hψ]
      exact rationalComplex.mul_mem (by rw [Complex.ofReal_inv, htC]
                                        exact rationalComplex.inv_mem qt) (qS i j)
    obtain ⟨_, _, _, _, hd, _, _, z, qz, hz⟩ :=
      (RationalQubitPurity.rational_qubit_purity_iff X₁ Y₁).mp
        ⟨M, hX₁, hSX₁, hSY₁, qS₁⟩
    refine ⟨hX, hY, mul_left_cancel₀ (pow_ne_zero _ hi) (detX.symm.trans (hd.trans detY)),
      (t : ℂ) * z, rationalComplex.mul_mem (htC.symm ▸ qt) qz, ?_⟩
    rw [normSq_real_mul, hz, detX]
    have hone : (t : ℂ) * (↑t⁻¹ : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne', Complex.ofReal_one]
    rw [← mul_assoc, ← mul_pow, hone, one_pow, one_mul]
  · rintro ⟨hX, hY, hd, z, qz, hz⟩
    obtain ⟨hp, htC, htX, htY⟩ := norm_data hX
    have hi : 0 ≤ (↑t⁻¹ : ℂ) := by exact_mod_cast (inv_nonneg.mpr hp.le)
    have qtc : RationalEntry (t : ℂ) := htC.symm ▸ qt
    have qi : RationalEntry (↑t⁻¹ : ℂ) := by
      rw [Complex.ofReal_inv]
      exact rationalComplex.inv_mem qtc
    obtain ⟨M, _, hM, hMr, hq⟩ := (RationalQubitPurity.rational_qubit_purity_iff X₁ Y₁).mpr
      ⟨hX.smul hi, hY.smul hi, htX, htY, by rw [detX, detY, hd],
        fun i j => rationalComplex.mul_mem qi (qX i j),
        fun i j => rationalComplex.mul_mem qi (qY i j),
        (↑t⁻¹ : ℂ) * z, rationalComplex.mul_mem qi qz, by rw [normSq_real_mul, hz, detX]⟩
    let S := rankOneDensity (Function.uncurry M)
    have hS : S.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
    have hSr : S.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
    have htC' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    refine ⟨(t : ℂ) • S, hS.smul (by exact_mod_cast hp.le), ?_, ?_, ?_,
      fun i j => rationalComplex.mul_mem qtc (hq i j)⟩
    · change partialTraceRight ((t : ℂ) • rankOneDensity (fun p => M p.1 p.2)) = X
      rw [partialTraceRight_smul, leftGram, hM]
      change (t : ℂ) • ((↑t⁻¹ : ℂ) • X) = X
      rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ htC', one_smul]
    · change partialTraceLeft ((t : ℂ) • rankOneDensity (fun p => M p.1 p.2)) = Y
      rw [partialTraceLeft_smul, rightGram, hMr]
      change (t : ℂ) • ((↑t⁻¹ : ℂ) • Y) = Y
      rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ htC', one_smul]
    · rwa [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero htC')]

/-- With positive middle occupation and a fixed rational coupling, a rational state of
rank at most two exists exactly when the residual marginals are positive semidefinite and
their common determinant is a Gaussian norm. -/
theorem rational_rank_le_two_at_iff (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (hb : 0 < b) (ht : L.trace + (b : ℂ) = 1) (hr : R.trace = L.trace)
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (qz : RationalEntry z) :
    let C := correction b (middleRow u v w z)
    let X := L - partialTraceRight C
    let Y := R - partialTraceLeft C
    (∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j)) ↔
    X.PosSemidef ∧ Y.PosSemidef ∧ X.det = Y.det ∧
      ∃ a : ℂ, RationalEntry a ∧ (normSq a : ℂ) = X.det := by
  dsimp only
  have qC := rational_correction (rational_pivot_of_trace ht qL)
    (rational_middleRow qu qv qw qz)
  refine (rational_rank_at_iff b L R u v w z 1 hb ht qL qu qv qw qz).trans ?_
  apply residual_rank_le_one_iff
  · simp [Matrix.trace_sub, hr, trace_partialTraceRight, trace_partialTraceLeft]
  · exact fun i j => rationalComplex.sub_mem (qL i j)
      (rationalComplex.sum_mem fun k _ => qC (i,k) (j,k))
  · exact fun i j => rationalComplex.sub_mem (qR i j)
      (rationalComplex.sum_mem fun k _ => qC (k,i) (k,j))

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
