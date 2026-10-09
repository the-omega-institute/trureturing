/- GID: D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim; result=D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result; claim=D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim
   digest: A flagged qubit measurement refutes uniform trace-norm CMI contraction. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
noncomputable section

def localContraction {n n' : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin n') (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ρ ρ' : DensityState (Fin n), ρ ≠ ρ' ∧
    r = traceNorm ((of_kraus K K) (CStarMatrix.ofMatrix.symm ρ.1) -
      (of_kraus K K) (CStarMatrix.ofMatrix.symm ρ'.1)) /
      traceNorm (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm ρ'.1)}

def I1 {dA dB n : ℕ}
    (M : Matrix ((Fin dA × Fin dB) × Fin n) ((Fin dA × Fin dB) × Fin n) ℂ) : ℝ :=
  let AB := partialTraceRight M
  let A := partialTraceRight AB
  let B := partialTraceLeft AB
  let BC := partialTraceLeft (M.submatrix
    (fun x : Fin dA × (Fin dB × Fin n) => ((x.1, x.2.1), x.2.2))
    (fun x : Fin dA × (Fin dB × Fin n) => ((x.1, x.2.1), x.2.2)))
  traceNorm (M - (A ⊗ₖ BC).submatrix
    (fun x : (Fin dA × Fin dB) × Fin n => (x.1.1, (x.1.2, x.2)))
    (fun x : (Fin dA × Fin dB) × Fin n => (x.1.1, (x.1.2, x.2)))) -
    traceNorm (AB - A ⊗ₖ B)

def claim : Prop :=
  ∀ (n n' : ℕ),
  ∀ (ι : Type) [Fintype ι] (K : ι → Matrix (Fin n') (Fin n) ℂ),
  (∑ i, (K i)ᴴ * K i) = 1 → localContraction K < 1 →
  ∃ η : ℝ, η < 1 ∧ ∀ (dA dB : ℕ),
  ∀ ρ : DensityState ((Fin dA × Fin dB) × Fin n),
    I1 ((of_kraus
      (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i)
      (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i))
      (CStarMatrix.ofMatrix.symm ρ.1)) ≤ η * I1 (CStarMatrix.ofMatrix.symm ρ.1)

set_option maxRecDepth 4096

private theorem diagonal_norm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    traceNorm (diagonal (fun i => (d i : ℂ))) = ∑ i, |d i| := by
  have hp : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast abs_nonneg (d i)
  have hs : diagonal (fun i => ((|d i| : ℝ) : ℂ)) * diagonal (fun i => ((|d i| : ℝ) : ℂ)) =
      (diagonal (fun i => (d i : ℂ)))ᴴ * diagonal (fun i => (d i : ℂ)) := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show |d i| * |d i| = d i * d i from by nlinarith [sq_abs (d i)])
  unfold traceNorm
  rw [CFC.sqrt_unique hs hp.nonneg]
  simp only [trace_diagonal, map_sum]
  change (∑ i, Complex.re ((|d i| : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_re]

private def qubit (x : ℝ) (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), y; star y, -(x : ℂ)]

private theorem qubit_norm (x : ℝ) (y : ℂ) :
    traceNorm (qubit x y) = 2 * Real.sqrt (x^2 + Complex.normSq y) := by
  let r := Real.sqrt (x^2 + Complex.normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = x^2 + Complex.normSq y :=
    Real.sq_sqrt (add_nonneg (sq_nonneg x) (Complex.normSq_nonneg y))
  have hp : (diagonal (fun _ : Fin 2 => (r : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hr
  have hs : diagonal (fun _ : Fin 2 => (r : ℂ)) * diagonal (fun _ : Fin 2 => (r : ℂ)) =
      (qubit x y)ᴴ * qubit x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [qubit, mul_apply, conjTranspose_apply, Fin.sum_univ_two,
        of_apply, cons_val_zero, cons_val_one, diagonal_apply,
        Fin.zero_eta, Fin.mk_one, star_neg, star_star, Complex.star_def,
        Complex.conj_ofReal] <;>
      simp <;> apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;>
      nlinarith [show r^2 = x^2 + (y.re^2 + y.im^2) from by
        simpa [Complex.normSq_apply, pow_two] using hr2]
  unfold traceNorm
  rw [CFC.sqrt_unique hs hp.nonneg]
  simp [trace_diagonal, Fin.sum_univ_two, r]

private theorem lifted_term_apply {α : Type*} [Fintype α] [DecidableEq α]
    (K : Fin 4 → Matrix (Fin 4) (Fin 2) ℂ)
    (M : Matrix (α × Fin 2) (α × Fin 2) ℂ)
    (k : Fin 4) (p q : α × Fin 4) :
    (((1 : Matrix α α ℂ) ⊗ₖ K k) * M *
      ((1 : Matrix α α ℂ) ⊗ₖ K k)ᴴ) p q =
      ∑ e : Fin 2, ∑ f : Fin 2, K k p.2 e * M (p.1,e) (q.1,f) * star (K k q.2 f) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul]
  simp only [ite_mul, one_mul, zero_mul, mul_zero,
    apply_ite, star_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  rw [Finset.sum_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
-- The explicit finite matrix certificates require an enlarged elaboration budget.
theorem result : ¬ claim := by
  intro hclaim
  let s : ℂ := (Real.sqrt 2 : ℂ) / 2
  let K : Fin 4 → Matrix (Fin 4) (Fin 2) ℂ := fun k =>
    single k 0 (if k = 0 then s else if k = 1 then 0 else 1/2) +
    single k 1 (if k = 0 then 0 else if k = 1 then s else if k = 2 then 1/2 else -1/2)
  have hsq : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs : star s = s := by
    simp only [s, star_div₀, Complex.star_def, Complex.conj_ofReal, map_ofNat]
  have hs2 : s * s = 1/2 := by
    dsimp only [s]
    have hsq : (Real.sqrt 2 : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      s*s = (Real.sqrt 2 : ℂ)^2 / 4 := by dsimp only [s]; ring
      _ = 1/2 := by rw [hsq]; norm_num
  have hcomplete : (∑ k, (K k)ᴴ * K k) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [K, Matrix.sum_apply, Fin.sum_univ_two, Fin.sum_univ_four, mul_apply,
        conjTranspose_apply,
        single, of_apply, Matrix.add_apply, Fin.isValue] <;>
      simp [s, Prod.ext_iff, Fin.ext_iff, Complex.star_def] <;> ring_nf <;> norm_num [hsq]
  have hsr : s.im = 0 := by dsimp only [s]; norm_num
  have hsr2 : s.re^2 = 1/2 := by
    have h := congrArg Complex.re hs2
    simpa [Complex.mul_re, hsr, pow_two] using h
  have hact (x : ℝ) (y : ℂ) : (of_kraus K K) (qubit x y) =
      diagonal (fun k : Fin 4 =>
        if k = 0 then ((x/2 : ℝ) : ℂ) else if k = 1 then ((-x/2 : ℝ) : ℂ)
        else if k = 2 then ((y.re/2 : ℝ) : ℂ) else ((-y.re/2 : ℝ) : ℂ)) := by
    change (∑ k, K k * qubit x y * (K k)ᴴ) = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [K, qubit, Matrix.sum_apply, Fin.sum_univ_two, Fin.sum_univ_four, mul_apply,
        conjTranspose_apply, single, of_apply, Matrix.add_apply, diagonal_apply] <;>
      simp [hs, Prod.ext_iff, Fin.ext_iff] <;> apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, hsr] <;>
      ring_nf <;> simp only [hsr2] <;> ring
  have hnout (x : ℝ) (y : ℂ) :
      traceNorm ((of_kraus K K) (qubit x y)) = |x| + |y.re| := by
    rw [hact]
    change traceNorm (diagonal (fun k : Fin 4 => ((if k = 0 then x/2 else
      if k = 1 then -x/2 else if k = 2 then y.re/2 else -y.re/2 : ℝ) : ℂ))) = _
    rw [diagonal_norm]
    rw [Fin.sum_univ_four]
    norm_num [Fin.ext_iff, abs_div]
    ring
  have hpair (ρ ρ' : DensityState (Fin 2)) :
      traceNorm ((of_kraus K K) (CStarMatrix.ofMatrix.symm ρ.1) -
        (of_kraus K K) (CStarMatrix.ofMatrix.symm ρ'.1)) /
        traceNorm (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm ρ'.1) ≤
        1 / Real.sqrt 2 := by
    let D := CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm ρ'.1
    have hD : D.IsHermitian := (density_posSemidef ρ).isHermitian.sub
      (density_posSemidef ρ').isHermitian
    have ht : D.trace = 0 := by
      dsimp only [D]
      rw [trace_sub]
      rw [show trace (CStarMatrix.ofMatrix.symm ρ.1) = 1 from ρ.2.2,
        show trace (CStarMatrix.ofMatrix.symm ρ'.1) = 1 from ρ'.2.2, sub_self]
    let x := (D 0 0).re
    let y := D 0 1
    have h00 : D 0 0 = (x : ℂ) := (hD.coe_re_apply_self 0).symm
    have h11 : D 1 1 = -(x : ℂ) := by
      have hh : (x : ℂ) + D 1 1 = 0 := by simpa [trace, Fin.sum_univ_two, h00] using ht
      exact eq_neg_of_add_eq_zero_right hh
    have heq : D = qubit x y := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [qubit] <;>
        simp [h00, h11, ← hD.apply 1 0, y]
    change traceNorm ((of_kraus K K) (CStarMatrix.ofMatrix.symm ρ.1) -
      (of_kraus K K) (CStarMatrix.ofMatrix.symm ρ'.1)) / traceNorm D ≤ _
    rw [← map_sub]
    change traceNorm ((of_kraus K K) D) / traceNorm D ≤ _
    rw [heq, hnout, qubit_norm]
    let r := Real.sqrt (x^2 + Complex.normSq y)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r^2 = x^2 + (y.re^2 + y.im^2) := by
      dsimp only [r]
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg x) (Complex.normSq_nonneg y))]
      simp [Complex.normSq_apply, pow_two]
    have hsq2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hb : |x| + |y.re| ≤ Real.sqrt 2 * r := by
      nlinarith [sq_abs x, sq_abs y.re, sq_nonneg (|x|-|y.re|),
        sq_nonneg y.im, abs_nonneg x, abs_nonneg y.re, mul_nonneg hroot.le hr]
    change (|x| + |y.re|) / (2*r) ≤ _
    by_cases hz : r = 0
    · simp [hz, hroot.le]
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      apply (div_le_iff₀ (by positivity : 0 < 2*r)).mpr
      have hrr : 1 / Real.sqrt 2 * (2*r) = Real.sqrt 2 * r := by
        field_simp
        nlinarith [hsq2]
      rwa [hrr]
  have hcontraction : localContraction K ≤ 1 / Real.sqrt 2 := by
    let S := {r : ℝ | ∃ ρ ρ' : DensityState (Fin 2), ρ ≠ ρ' ∧
      r = traceNorm ((of_kraus K K) (CStarMatrix.ofMatrix.symm ρ.1) -
        (of_kraus K K) (CStarMatrix.ofMatrix.symm ρ'.1)) /
        traceNorm (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm ρ'.1)}
    have hu : ∀ r ∈ S, r ≤ 1 / Real.sqrt 2 := by
      rintro r ⟨ρ, ρ', hne, rfl⟩
      exact hpair ρ ρ'
    have hbounded : BddAbove S := ⟨1 / Real.sqrt 2, hu⟩
    change sSup S ≤ _
    by_cases hne : S.Nonempty
    · exact (csSup_le_iff hbounded hne).mpr hu
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hstrict : localContraction K < 1 := by
    apply hcontraction.trans_lt
    have hroot : 1 < Real.sqrt 2 := by
      have hsq2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    exact (div_lt_one (by positivity)).mpr hroot
  let v0 : ((Fin 2 × Fin 2) × Fin 2) → ℂ := fun p => if p.1.1 = 0 ∧ p.1.2 = p.2 then 1/2 else 0
  let v1 : ((Fin 2 × Fin 2) × Fin 2) → ℂ := fun p => if p.1.1 = 1 then
    if p.1.2 = 0 ∧ p.2 = 1 then 1/2 else if p.1.2 = 1 ∧ p.2 = 0 then -1/2 else 0
    else 0
  let w0 : ((Fin 2 × Fin 2) × Fin 2) → ℂ := fun p => if p.1.1 = 1 ∧ p.1.2 = p.2 then 1/2 else 0
  let w1 : ((Fin 2 × Fin 2) × Fin 2) → ℂ := fun p => if p.1.1 = 0 then
    if p.1.2 = 0 ∧ p.2 = 1 then 1/2 else if p.1.2 = 1 ∧ p.2 = 0 then -1/2 else 0
    else 0
  let M : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    vecMulVec v0 (star v0) + vecMulVec v1 (star v1)
  let W : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    vecMulVec w0 (star w0) + vecMulVec w1 (star w1)
  have hM : M.PosSemidef := (posSemidef_vecMulVec_self_star v0).add
    (posSemidef_vecMulVec_self_star v1)
  have hW : W.PosSemidef := (posSemidef_vecMulVec_self_star w0).add
    (posSemidef_vecMulVec_self_star w1)
  have htrM : M.trace = 1 := by
    change (∑ p : (Fin 2 × Fin 2) × Fin 2, M p p) = 1
    simp only [M, trace, Matrix.diag_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, v0, v1]
    norm_num [Prod.ext_iff, Fin.ext_iff]
  have htrW : W.trace = 1 := by
    change (∑ p : (Fin 2 × Fin 2) × Fin 2, W p p) = 1
    simp only [W, trace, Matrix.diag_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, w0, w1]
    norm_num [Prod.ext_iff, Fin.ext_iff]
  let R : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    (1/2 : ℂ) • M - (1/2 : ℂ) • W
  have hinSecond : partialTraceRight M -
      partialTraceRight (partialTraceRight M) ⊗ₖ
        partialTraceLeft (partialTraceRight M) = 0 := by
    ext ⟨a,b⟩ ⟨a',b'⟩
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp only [partialTraceRight, partialTraceLeft, M, Matrix.sub_apply,
        Matrix.zero_apply, Matrix.kroneckerMap_apply, Matrix.add_apply,
        vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.sum_univ_four, v0, v1] <;>
      simp [Prod.ext_iff, Fin.ext_iff] <;> norm_num
  have hinCenter : M -
      ((partialTraceRight (partialTraceRight M) ⊗ₖ
        partialTraceLeft (M.submatrix
          (fun p : Fin 2 × (Fin 2 × Fin 2) => ((p.1,p.2.1),p.2.2))
          (fun p : Fin 2 × (Fin 2 × Fin 2) => ((p.1,p.2.1),p.2.2)))).submatrix
          (fun p : ((Fin 2 × Fin 2) × Fin 2) => (p.1.1,(p.1.2,p.2)))
          (fun p : ((Fin 2 × Fin 2) × Fin 2) => (p.1.1,(p.1.2,p.2)))) = R := by
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      simp only [R, M, W, partialTraceRight, partialTraceLeft, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_four, v0, v1, w0, w1] <;>
      simp [Prod.ext_iff, Fin.ext_iff] <;> norm_num
  have hzero : traceNorm (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := by
    have ht := congrArg Complex.re (traceNorm_of_posSemidef
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).PosSemidef))
    simpa using ht
  have hinI : I1 M = traceNorm R := by
    simp only [I1, hinSecond, hinCenter, hzero, sub_zero]
  have hhalf : (0 : ℂ) ≤ 1/2 := by
    rw [Complex.le_def]
    norm_num
  have hnM : traceNorm ((1/2 : ℂ) • M) = 1/2 := by
    have ht := congrArg Complex.re (traceNorm_of_posSemidef (hM.smul hhalf))
    simpa [trace_smul, htrM] using ht
  have hnW : traceNorm ((1/2 : ℂ) • W) = 1/2 := by
    have ht := congrArg Complex.re (traceNorm_of_posSemidef (hW.smul hhalf))
    simpa [trace_smul, htrW] using ht
  have hinUpper : I1 M ≤ 1 := by
    rw [hinI]
    have ht := traceNorm_add_le ((1/2 : ℂ) • M) (-((1/2 : ℂ) • W))
    rw [traceNorm_neg, hnM, hnW] at ht
    change traceNorm R ≤ 1
    exact ht.trans_eq (by norm_num)
  let ui : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ := diagonal (fun p =>
    if (p.1.1 = 0 ∧ p.1.2 = p.2) ∨ (p.1.1 = 1 ∧ p.1.2 ≠ p.2) then 1 else -1)
  have hui : ui ∈ unitaryGroup ((Fin 2 × Fin 2) × Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      simp only [ui, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
        conjTranspose_apply, diagonal_apply, Matrix.one_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four] <;>
      simp [Prod.ext_iff, Fin.ext_iff] <;> norm_num
  have htri : (ui * R).trace.re = 1 := by
    simp only [ui, R, M, W, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_four, v0, v1, w0, w1]
    simp [Prod.ext_iff, Fin.ext_iff] <;> norm_num
  have hinLower : 1 ≤ I1 M := by
    rw [hinI]
    exact (traceNorm_eq_max_re_tr_U R).2 ⟨⟨ui,hui⟩, htri⟩
  let L : Fin 4 → Matrix ((Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2) × Fin 2) ℂ := fun k =>
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ K k
  let T : Matrix ((Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2) × Fin 4) ℂ := fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = q.2 then
      if p.2 = 0 then if p.1.2 = q.1.2 ∧ p.1.2 = p.1.1 then 1/8 else 0
      else if p.2 = 1 then if p.1.2 = q.1.2 ∧ p.1.2 ≠ p.1.1 then 1/8 else 0
      else if p.1.2 = q.1.2 then 1/16
      else if (p.2 = 2 ∧ p.1.1 = 0) ∨ (p.2 = 3 ∧ p.1.1 = 1) then 1/16 else -1/16
    else 0
  have houtput : (of_kraus L L) M = T := by
    change (∑ k, L k * M * (L k)ᴴ) = T
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    simp only [Matrix.sum_apply, L, lifted_term_apply]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      simp only [Fin.sum_univ_two, Fin.sum_univ_four, K, M, T, v0, v1,
        Matrix.single, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
        Pi.star_apply] <;>
      norm_num [Fin.ext_iff, starRingEnd_apply, hs] <;>
      ring_nf <;> norm_num [pow_two, hs2]
  let X : Matrix ((Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2) × Fin 4) ℂ := T - (1/16 : ℂ) • 1
  have houtSecond : partialTraceRight T -
      partialTraceRight (partialTraceRight T) ⊗ₖ
        partialTraceLeft (partialTraceRight T) = 0 := by
    ext ⟨a,b⟩ ⟨a',b'⟩
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp only [partialTraceRight, partialTraceLeft, T, Matrix.sub_apply,
        Matrix.zero_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_four] <;> norm_num [Fin.ext_iff]
  have houtAB : partialTraceRight T = (1/4 : ℂ) • 1 := by
    ext ⟨a,b⟩ ⟨a',b'⟩
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp only [partialTraceRight, T, Fin.sum_univ_four, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply] <;>
      norm_num [Prod.mk.injEq, Fin.ext_iff]
  have houtA : partialTraceRight (partialTraceRight T) = (1/2 : ℂ) • 1 := by
    rw [houtAB]
    ext a a'
    fin_cases a <;> fin_cases a' <;>
      norm_num [partialTraceRight, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        Fin.sum_univ_two, Prod.mk.injEq, Fin.ext_iff]
  have houtBC : partialTraceLeft (T.submatrix
      (fun p : Fin 2 × (Fin 2 × Fin 4) => ((p.1,p.2.1),p.2.2))
      (fun p : Fin 2 × (Fin 2 × Fin 4) => ((p.1,p.2.1),p.2.2))) =
      (1/8 : ℂ) • 1 := by
    ext ⟨b,c⟩ ⟨b',c'⟩
    change (∑ a : Fin 2, T ((a,b),c) ((a,b'),c')) =
      (1/8 : ℂ) * (if (b,c) = (b',c') then 1 else 0)
    fin_cases b <;> fin_cases c <;> fin_cases b' <;> fin_cases c' <;>
      simp only [T, Fin.sum_univ_two] <;>
      norm_num [Prod.mk.injEq, Fin.ext_iff]
  have houtCenter : T -
      ((partialTraceRight (partialTraceRight T) ⊗ₖ
        partialTraceLeft (T.submatrix
          (fun p : Fin 2 × (Fin 2 × Fin 4) => ((p.1,p.2.1),p.2.2))
          (fun p : Fin 2 × (Fin 2 × Fin 4) => ((p.1,p.2.1),p.2.2)))).submatrix
          (fun p : ((Fin 2 × Fin 2) × Fin 4) => (p.1.1,(p.1.2,p.2)))
          (fun p : ((Fin 2 × Fin 2) × Fin 4) => (p.1.1,(p.1.2,p.2)))) = X := by
    dsimp only [X]
    rw [houtA, houtBC]
    congr 1
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      norm_num [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply, Prod.mk.injEq, Fin.ext_iff]
  have houtI : I1 T = traceNorm X := by
    simp only [I1, houtSecond, houtCenter, hzero, sub_zero]
  have hXentry (p q : (Fin 2 × Fin 2) × Fin 4) :
      X p q = T p q - if p = q then (1/16 : ℂ) else 0 := by
    simp only [X, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp
  have hXstar : Xᴴ = X := by
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    simp only [conjTranspose_apply, hXentry, T]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      norm_num [Prod.mk.injEq, Fin.ext_iff, Complex.star_def]
  have hXsq : X * X = (1/256 : ℂ) • 1 := by
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    simp only [Matrix.mul_apply, hXentry, T, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
      norm_num [Prod.mk.injEq, Fin.ext_iff]
  let uo : Matrix ((Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2) × Fin 4) ℂ := (16 : ℂ) • X
  have huo : uo ∈ unitaryGroup ((Fin 2 × Fin 2) × Fin 4) ℂ := by
    rw [mem_unitaryGroup_iff]
    change ((16 : ℂ) • X) * (((16 : ℂ) • X)ᴴ) = 1
    rw [conjTranspose_smul, hXstar, smul_mul_smul_comm, hXsq, smul_smul]
    norm_num
  have htro : (uo * X).trace.re = 1 := by
    dsimp only [uo]
    rw [smul_mul, hXsq, smul_smul, trace_smul, trace_one]
    norm_num [Fintype.card_prod]
  have houtLower : 1 ≤ I1 T := by
    rw [houtI]
    exact (traceNorm_eq_max_re_tr_U X).2 ⟨⟨uo,huo⟩, htro⟩
  let ρ : DensityState ((Fin 2 × Fin 2) × Fin 2) := ⟨CStarMatrix.ofMatrix M,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg, htrM⟩
  obtain ⟨η, hη, hbound⟩ := hclaim 2 4 (Fin 4) K hcomplete hstrict
  have hb := hbound 2 2 ρ
  change I1 ((of_kraus L L) M) ≤ η * I1 M at hb
  rw [houtput] at hb
  have hpositive : 0 < I1 M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hinLower
  have hηnonneg : 0 ≤ η := by nlinarith
  have hscaled : η * I1 M ≤ η := by nlinarith
  linarith

end
end D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
