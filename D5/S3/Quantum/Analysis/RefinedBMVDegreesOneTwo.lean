/- GID: D5/S3/Quantum/Analysis/RefinedBMVDegreesOneTwo
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refined BMV product comparisons at first degrees one and two. -/

import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
import D5.S3.Quantum.Analysis.RefinedBMVUniformWords
import D5.S3.Quantum.Hiai.SupportPowerLimits

/-! # The first two degrees of the refined BMV comparison

The Araki–Lieb–Thirring step uses the compound three-lines argument from
`D5.S3.Quantum.Divergence.AlphaZAffine.Result`, specialized to interpolation
from the identity to a product of two positive definite matrices.
-/

noncomputable section

namespace RefinedBMV.DegreesOneTwo

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators
open D5.S3.Quantum.Hiai.SupportPowerLimits
open D5.S3.Quantum.Hiai.InverseMeanVariational (tracePower)

variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private def traceMoment (X : Matrix d d ℂ) (z : ℝ) : ℝ := tracePower z (Xᴴ * X)

section ThreeLinesParts
open NormedSpace Complex Set
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [StarRing E]
  [CStarRing E] [CompleteSpace E] [StarModule ℂ E]
local instance : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
private def expSandwich (H K X : E) (w : ℂ) : E :=
  exp (w • H) * X * exp (w • K)
private lemma imaginary_exp_unitary {H : E} (hH : IsSelfAdjoint H) (s : ℝ) :
    exp (((s : ℂ) * I) • H) ∈ unitary E := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  exact hH.smul_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff]
    simp)
omit [StarRing E] [CStarRing E] [StarModule ℂ E] in
private lemma expSandwich_split (H K X : E) (w : ℂ) :
    expSandwich H K X w = exp (((w.im : ℂ) * I) • H) *
      expSandwich H K X w.re * exp (((w.im : ℂ) * I) • K) := by
  have hsplitH : exp (w • H) =
      exp (((w.im : ℂ) * I) • H) * exp ((w.re : ℂ) • H) := by
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl H).smul_left _).smul_right _), ← add_smul]
    congr 2
    exact (Complex.re_add_im w).symm.trans (add_comm _ _)
  have hsplitK : exp (w • K) =
      exp ((w.re : ℂ) • K) * exp (((w.im : ℂ) * I) • K) := by
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl K).smul_left _).smul_right _), ← add_smul]
    rw [Complex.re_add_im]
  simp only [expSandwich, hsplitH, hsplitK, mul_assoc]
end ThreeLinesParts
section CompoundThreeLinesParts
open _root_.Matrix NormedSpace Complex Set
open scoped Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]
private lemma compound_differentiable (H K X : Matrix d d ℂ) (k : ℕ) :
    Differentiable ℂ (fun w : ℂ => compoundMatrix (expSandwich H K X w) k) := by
  unfold compoundMatrix
  simp only [Matrix.det_apply']
  unfold expSandwich Matrix.submatrix
  simp only [Matrix.of_apply]
  fun_prop
private lemma compound_norm_re {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (X : Matrix d d ℂ) (k : ℕ) (w : ℂ) :
    ‖compoundMatrix (expSandwich H K X w) k‖ =
      ‖compoundMatrix (expSandwich H K X w.re) k‖ := by
  rw [expSandwich_split, compoundMatrix_mul, compoundMatrix_mul]
  rw [CStarRing.norm_mul_mem_unitary _
      (compoundMatrix_unitary _ (imaginary_exp_unitary hK w.im) k),
    CStarRing.norm_mem_unitary_mul _
      (compoundMatrix_unitary _ (imaginary_exp_unitary hH w.im) k)]
private theorem compound_expSandwich_three_lines {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (X : Matrix d d ℂ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖compoundMatrix (expSandwich H K X (t : ℂ)) k‖ ≤
      ‖compoundMatrix X k‖ ^ (1 - t) *
        ‖compoundMatrix (expSandwich H K X 1) k‖ ^ t := by
  let F := fun w : ℂ => compoundMatrix (expSandwich H K X w) k
  have hd : Differentiable ℂ F := compound_differentiable H K X k
  have hc : Continuous (fun s : ℝ => ‖F (s : ℂ)‖) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm
  have hb : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image hc).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ M
    rw [compound_norm_re hH hK]
    exact hM (mem_image_of_mem _ hw)
  apply HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (by simpa [HadamardThreeLines.verticalClosedStrip] using ht) hd.diffContOnCl hb
  · intro w hw
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ _
    rw [compound_norm_re hH hK]
    have hw0 : w.re = 0 := hw
    simp [hw0, expSandwich]
  · intro w hw
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ _
    rw [compound_norm_re hH hK]
    have hw1 : w.re = 1 := hw
    simp [hw1]
end CompoundThreeLinesParts

section PowerInterpolationParts
open _root_.Matrix NormedSpace
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
local instance : NormedAlgebra ℚ (Matrix d d ℂ) := .restrictScalars ℚ ℂ _
private theorem exp_smul_log {A : Matrix d d ℂ} (hA : A.PosDef) (r : ℝ) :
    exp ((r : ℂ) • CFC.log A) = A ^ r := by
  have hlog : IsSelfAdjoint (CFC.log A) := IsSelfAdjoint.log
  have hscaled : IsSelfAdjoint (r • CFC.log A) := (IsSelfAdjoint.all r).smul hlog
  have hc : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono (fun x hx => (hA.isStrictlyPositive.spectrum_pos hx).ne')
  rw [Complex.coe_smul, ← CFC.real_exp_eq_normedSpace_exp hscaled, CFC.log,
    ← cfc_const_mul r Real.log A hc]
  calc
    cfc Real.exp (cfc (fun x : ℝ => r * Real.log x) A) =
        cfc (fun x : ℝ => Real.exp (r * Real.log x)) A :=
      (cfc_comp Real.exp (fun x : ℝ => r * Real.log x) A
        hA.isHermitian (by fun_prop) (continuousOn_const.mul hc)).symm
    _ = A ^ r := by
      rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
      apply cfc_congr
      intro x hx
      change Real.exp (r * Real.log x) = x ^ r
      rw [Real.rpow_def_of_pos (hA.isStrictlyPositive.spectrum_pos hx), mul_comm]
end PowerInterpolationParts

private theorem traceMoment_eq_sum_sorted (X : Matrix d d ℂ) {z : ℝ} (hz : 0 < z) :
    traceMoment X z = ∑ i, singularValuesSorted X i ^ (2 * z) := by
  have h := D5.S3.Quantum.Hiai.InverseMeanVariational.norm_rpow_gram X
    (r := 2 * z) (by positivity)
  rw [show 2 * z / 2 = z by ring,
    schattenNorm_rpow_eq_sum_singularValues X (p := 2 * z) (by positivity),
    sum_singularValues_rpow_eq_sum_sorted] at h
  exact h.symm

section Interpolation

open scoped Matrix.Norms.L2Operator
open NormedSpace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior

private theorem power_weak_log_majorization {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ Fintype.card d) :
    (∏ i : Fin k, singularValuesSorted (A ^ t * B ^ t) ⟨i.val, by omega⟩) ≤
      (∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩) ^ t := by
  have hn : 0 < Fintype.card {S : Finset d // S.card = k} := by
    simpa [Fintype.card_subtype] using Nat.choose_pos hk
  let : Nonempty {S : Finset d // S.card = k} := Fintype.card_pos_iff.mp hn
  have h := compound_expSandwich_three_lines
    (IsSelfAdjoint.log (a := A)) (IsSelfAdjoint.log (a := B)) (1 : Matrix d d ℂ) k ht
  have h₁ : expSandwich (CFC.log A) (CFC.log B) (1 : Matrix d d ℂ) 1 = A * B := by
    rw [← Complex.ofReal_one]
    simp only [expSandwich, exp_smul_log hA, exp_smul_log hB, mul_one,
      CFC.rpow_one _ hA.posSemidef.nonneg, CFC.rpow_one _ hB.posSemidef.nonneg]
  have ht' : expSandwich (CFC.log A) (CFC.log B) (1 : Matrix d d ℂ) (t : ℂ) =
      A ^ t * B ^ t := by
    simp only [expSandwich, exp_smul_log hA, exp_smul_log hB, mul_one]
  have hid : ‖compoundMatrix (1 : Matrix d d ℂ) k‖ = 1 :=
    CStarRing.norm_of_mem_unitary (compoundMatrix_unitary _ (by simp) k)
  rw [h₁, ht', hid, Real.one_rpow, one_mul] at h
  simpa only [complex_opNorm_sorted _ hn, ← prod_singularValuesSorted_eq_compoundSV _ k hk]
    using h

private theorem alt_posDef {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t z : ℝ}
    (ht : 0 < t) (ht₁ : t ≤ 1) (hz : 0 < z) :
    traceMoment (A ^ t * B ^ t) z ≤ traceMoment (A * B) (t * z) := by
  rw [traceMoment_eq_sum_sorted _ hz, traceMoment_eq_sum_sorted _ (mul_pos ht hz)]
  let x := singularValuesSorted (A ^ t * B ^ t)
  let y := fun i => singularValuesSorted (A * B) i ^ t
  have h := weak_log_maj_sum_rpow_le (x := x) (y := y)
    (singularValuesSorted_nonneg _)
    (fun i => Real.rpow_nonneg (singularValuesSorted_nonneg _ i) _)
    (singularValuesSorted_antitone _) (fun i j hij =>
      Real.rpow_le_rpow (singularValuesSorted_nonneg _ _)
        (singularValuesSorted_antitone _ hij) ht.le)
    (fun k hk => by
      dsimp [x, y]
      rw [Real.finsetProd_rpow _ _ (fun _ _ => singularValuesSorted_nonneg _ _) _]
      exact power_weak_log_majorization hA hB ⟨ht.le, ht₁⟩ k hk)
    (show 0 < 2 * z by positivity)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [y]
  rw [← Real.rpow_mul (singularValuesSorted_nonneg _ i)]
  congr 1
  ring

end Interpolation

open Filter Topology

omit [Fintype d] in
private lemma shift_tendsto (A : Matrix d d ℂ) :
    Tendsto (fun ε : ℝ => A + ε • (1 : Matrix d d ℂ))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 A) := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using tendsto_const_nhds.add (hε.smul_const (1 : Matrix d d ℂ))

private lemma tendsto_traceMoment {ι : Type*} {l : Filter ι}
    {F : ι → Matrix d d ℂ} {X : Matrix d d ℂ} {z : ℝ}
    (hz : 0 < z) (hF : Tendsto F l (𝓝 X)) :
    Tendsto (fun i => traceMoment (F i) z) l (𝓝 (traceMoment X z)) :=
  tendsto_tracePower hz (posSemidef_conjTranspose_mul_self X)
    (.of_forall fun i => posSemidef_conjTranspose_mul_self (F i))
    (((continuous_id.matrix_conjTranspose.continuousAt.tendsto).comp hF).mul hF)

private theorem alt {A B : Matrix d d ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t z : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (hz : 0 < z) :
    traceMoment (A ^ t * B ^ t) z ≤ traceMoment (A * B) (t * z) := by
  have hpd (X : Matrix d d ℂ) (hX : X.PosSemidef) :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, (X + ε • (1 : Matrix d d ℂ)).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (Matrix.PosDef.one.smul hε).posSemidef_add hX
  have hA' := hpd A hA
  have hB' := hpd B hB
  have hAt := tendsto_positive_rpow ht hA (hA'.mono fun _ h => h.posSemidef) (shift_tendsto A)
  have hBt := tendsto_positive_rpow ht hB (hB'.mono fun _ h => h.posSemidef) (shift_tendsto B)
  apply le_of_tendsto_of_tendsto (tendsto_traceMoment hz (hAt.mul hBt))
    (tendsto_traceMoment (mul_pos ht hz) ((shift_tendsto A).mul (shift_tendsto B)))
  filter_upwards [hA', hB'] with ε hAe hBe
  exact alt_posDef hAe hBe ht ht₁ hz

private lemma trace_cycle_power (X Y : Matrix d d ℂ) (k : ℕ) :
    trace ((X * Y) ^ k) = trace ((Y * X) ^ k) := by
  cases k with
  | zero => simp
  | succ k =>
    calc
      trace ((X * Y) ^ (k + 1)) = trace ((X * Y) ^ k * X * Y) := by
        rw [pow_succ, mul_assoc]
      _ = trace (X * (Y * X) ^ k * Y) := by rw [mul_pow_mul]
      _ = trace ((Y * X) ^ (k + 1)) := by
        rw [trace_mul_comm, ← mul_assoc, ← pow_succ']

private lemma moment_square_product {X Y : Matrix d d ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (k : ℕ) :
    traceMoment (X * Y) k = (trace ((X ^ 2 * Y ^ 2) ^ k)).re ∧
      (trace ((X ^ 2 * Y ^ 2) ^ k)).im = 0 := by
  have hGram := posSemidef_conjTranspose_mul_self (X * Y)
  have he : (X * Y)ᴴ * (X * Y) = Y * (X ^ 2 * Y) := by
    rw [conjTranspose_mul, hX.isHermitian.eq, hY.isHermitian.eq, pow_two]
    simp only [mul_assoc]
  have htrace : trace (((X * Y)ᴴ * (X * Y)) ^ k) =
      trace ((X ^ 2 * Y ^ 2) ^ k) := by
    rw [he, trace_cycle_power Y, mul_assoc, ← pow_two]
  constructor
  · unfold traceMoment tracePower
    rw [CFC.rpow_natCast _ _ hGram.nonneg, htrace]
  · rw [← htrace]
    exact (Complex.nonneg_iff.mp (hGram.pow k).trace_nonneg).2.symm

private lemma square_rpow {A : Matrix d d ℂ} (hA : A.PosSemidef) (r : ℝ) :
    (A ^ r) ^ (2 : ℕ) = A ^ (r * 2) := by
  rw [← CFC.rpow_natCast _ 2 CFC.rpow_nonneg, psd_nested_rpow hA]
  norm_num

private theorem alt_trace {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    {m n : ℕ} (hm : 0 < m) (htm : t * m = n) :
    trace (((A ^ t) ^ 2 * (B ^ t) ^ 2) ^ m) ≤ trace ((A ^ 2 * B ^ 2) ^ n) := by
  have h := alt hA hB ht ht₁ (show (0 : ℝ) < m by exact_mod_cast hm)
  rw [htm] at h
  have hleft := moment_square_product
    (X := A ^ t) (Y := B ^ t) CFC.rpow_nonneg.posSemidef CFC.rpow_nonneg.posSemidef m
  have hright := moment_square_product hA hB n
  rw [hleft.1, hright.1] at h
  exact Complex.le_def.mpr ⟨h, hleft.2.trans hright.2.symm⟩

private lemma square_nested_rpow {A : Matrix d d ℂ} (hA : A.PosSemidef) (r t : ℝ) :
    ((A ^ r) ^ t) ^ (2 : ℕ) = A ^ (r * t * 2) := by
  rw [psd_nested_rpow hA, square_rpow hA]

section WordMeans

open scoped Matrix.Norms.L2Operator

private theorem gap_rotate (A B : Matrix d d ℂ) (p q r : ℕ) :
    traceGaps43 A B (q, r, p) = traceGaps43 A B (p, q, r) := by
  simpa only [traceGaps43, mul_assoc] using
    trace_mul_comm (A ^ q * (B * (A ^ r * B))) (A ^ p * B)

/-- The one-copy word mean is the trace of its single cyclic representative. -/
private theorem wordMean_one (A B : Matrix d d ℂ) :
    DimThree.wordMean 1 A B = trace (A * B ^ 3) := by
  rw [DimThree.wordMean_eq_gaps_all,
    show DimThree.gaps 1 = [(0, 0, 1), (0, 1, 0), (1, 0, 0)] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gap_rotate A B 0 0 1, gap_rotate A B 1 0 0]
  simp only [traceGaps43, pow_zero, pow_one, one_mul, ← pow_two B, ← pow_succ' B 2]
  norm_num
  ring

/-- The two-copy word mean gives equal weight to the two cyclic orbits. -/
private theorem wordMean_two (A B : Matrix d d ℂ) :
    DimThree.wordMean 2 A B = (trace (A ^ 2 * B ^ 3) + trace (A * B * A * B ^ 2)) / 2 := by
  rw [DimThree.wordMean_eq_gaps_all,
    show DimThree.gaps 2 =
      [(0, 0, 2), (0, 1, 1), (0, 2, 0), (1, 0, 1), (1, 1, 0), (2, 0, 0)] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gap_rotate A B 0 0 2, gap_rotate A B 2 0 0, gap_rotate A B 1 0 1, gap_rotate A B 1 1 0]
  simp only [traceGaps43, pow_zero, pow_one, one_mul, mul_assoc, ← pow_two B, ← pow_succ' B 2]
  norm_num
  ring

omit [DecidableEq d] in
private theorem trace_le_gramMean (X Y : Matrix d d ℂ) (t : ℂ)
    (hXY : trace (Xᴴ * Y) = t) (hYX : trace (Yᴴ * X) = t) :
    t ≤ (trace (Xᴴ * X) + trace (Yᴴ * Y)) / 2 := by
  have h := (posSemidef_conjTranspose_mul_self (X - Y)).trace_nonneg
  have he : trace ((X - Y)ᴴ * (X - Y)) =
      2 * ((trace (Xᴴ * X) + trace (Yᴴ * Y)) / 2 - t) := by
    rw [conjTranspose_sub, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
      hXY, hYX]
    ring
  rw [he, Complex.nonneg_iff] at h
  rw [Complex.le_def]
  rcases h with ⟨hr, hi⟩
  norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im, Complex.normSq_ofNat] at hr hi ⊢
  constructor <;> linarith

private theorem trace_rotate_powers (A C : Matrix d d ℂ) (i j k l : ℕ) :
    trace ((C ^ i * A * C ^ j) * (C ^ k * A * C ^ l)) =
      trace (A * C ^ (j + k) * A * C ^ (l + i)) := by
  rw [pow_add, pow_add]
  calc
    _ = trace (C ^ i * (A * (C ^ j * C ^ k) * A * C ^ l)) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [trace_mul_comm]
      simp only [mul_assoc]

private theorem trace_swap_powers (A C : Matrix d d ℂ) (i j : ℕ) :
    trace (A * C ^ i * A * C ^ j) = trace (A * C ^ j * A * C ^ i) := by
  simpa only [mul_assoc] using trace_mul_comm (A * C ^ i) (A * C ^ j)

/-- The degree-two mean bounds the trace square involving the three-halves power.
Each comparison is the nonnegativity of the trace of a Gram matrix. -/
private theorem trace_rpow_mul_le_wordMean_two (A B : Matrix d d ℂ) (hA : A.IsHermitian)
    (hB : B.PosSemidef) :
    trace ((A * B ^ (3 / 2 : ℝ)) ^ 2) ≤ DimThree.wordMean 2 A B := by
  let C := B ^ (1 / 2 : ℝ)
  have hC : 0 ≤ C := CFC.rpow_nonneg
  have hCstar : Cᴴ = C := hC.posSemidef.isHermitian.eq
  have cPow (k : ℕ) : C ^ k = B ^ ((1 / 2 : ℝ) * k) := by
    rw [← CFC.rpow_natCast C k hC]
    exact CFC.rpow_rpow_of_exponent_nonneg B _ _ (by norm_num) (by positivity) hB.nonneg
  have cTwo : C ^ (2 : ℕ) = B := by
    rw [cPow, show (1 / 2 : ℝ) * ↑(2 : ℕ) = 1 by norm_num, CFC.rpow_one B hB.nonneg]
  have cThree : C ^ (3 : ℕ) = B ^ (3 / 2 : ℝ) := by
    rw [cPow]
    norm_num
  have hswap : trace (A * C ^ 4 * A * C ^ 2) = trace (A * C ^ 2 * A * C ^ 4) :=
    trace_swap_powers A C 4 2
  have hpow (i j : ℕ) : (C ^ i * A * C ^ j)ᴴ = C ^ j * A * C ^ i := by
    simp only [conjTranspose_mul, conjTranspose_pow, hCstar, hA.eq, mul_assoc]
  have hnormalize (i j k l : ℕ) :
      trace ((C ^ i * A * C ^ j)ᴴ * (C ^ k * A * C ^ l)) =
        trace (A * C ^ (i + k) * A * C ^ (l + j)) := by
    rw [hpow, trace_rotate_powers]
  have lower : trace (A * C ^ 3 * A * C ^ 3) ≤ trace (A * C ^ 2 * A * C ^ 4) := by
    have h := trace_le_gramMean (C ^ 2 * A * C ^ 1) (C ^ 1 * A * C ^ 2)
      (trace (A * C ^ 3 * A * C ^ 3))
      (by rw [hnormalize]) (by rw [hnormalize])
    rw [hnormalize, hnormalize] at h
    norm_num at h
    rw [hswap, add_self_div_two] at h
    exact h
  have upper : trace (A * C ^ 2 * A * C ^ 4) ≤
      (trace (A ^ 2 * C ^ 6) + trace (A * C ^ 2 * A * C ^ 4)) / 2 := by
    have h := trace_le_gramMean (C ^ 0 * A * C ^ 3) (C ^ 2 * A * C ^ 1)
      (trace (A * C ^ 2 * A * C ^ 4))
      (by rw [hnormalize]) (by rw [hnormalize])
    rw [hnormalize, hnormalize] at h
    norm_num at h
    rw [hswap] at h
    simpa only [pow_two A] using h
  rw [wordMean_two, ← cThree, ← cTwo, ← pow_mul, ← pow_mul, pow_two]
  simpa only [mul_assoc] using lower.trans upper

end WordMeans

/-- The refined BMV product comparison with one copy of `A` and three copies of `B`. -/
theorem product_bound_one (A B : Matrix d d ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (1 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 1 A B := by
  have h := alt_trace (A := A ^ (1 / 2 : ℝ)) (B := B ^ (3 / 2 : ℝ))
    CFC.rpow_nonneg.posSemidef CFC.rpow_nonneg.posSemidef
    (t := 1 / 3) (by norm_num) (by norm_num) (m := 3) (n := 1) (by norm_num) (by norm_num)
  rw [wordMean_one]
  rw [square_nested_rpow hA, square_nested_rpow hB, square_rpow hA, square_rpow hB,
    show (1 / 2 : ℝ) * (1 / 3) * 2 = 1 / 3 by norm_num,
    show (3 / 2 : ℝ) * (1 / 3) * 2 = 1 by norm_num,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    show (3 / 2 : ℝ) * 2 = ((3 : ℕ) : ℝ) by norm_num,
    CFC.rpow_one _ hA.nonneg, CFC.rpow_one _ hB.nonneg,
    CFC.rpow_natCast _ 3 hB.nonneg, pow_one] at h
  exact h

/-- The refined BMV product comparison with two copies of `A` and three copies of `B`. -/
theorem product_bound_two (A B : Matrix d d ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (2 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 2 A B := by
  have h := alt_trace (A := A ^ (1 / 2 : ℝ)) (B := B ^ (3 / 4 : ℝ))
    CFC.rpow_nonneg.posSemidef CFC.rpow_nonneg.posSemidef
    (t := 2 / 3) (by norm_num) (by norm_num) (m := 3) (n := 2) (by norm_num) (by norm_num)
  have h' : trace (((A ^ (2 / 3 : ℝ)) * B) ^ 3) ≤
      trace ((A * B ^ (3 / 2 : ℝ)) ^ 2) := by
    rw [square_nested_rpow hA, square_nested_rpow hB, square_rpow hA, square_rpow hB,
      show (1 / 2 : ℝ) * (2 / 3) * 2 = 2 / 3 by norm_num,
      show (3 / 4 : ℝ) * (2 / 3) * 2 = 1 by norm_num,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      show (3 / 4 : ℝ) * 2 = 3 / 2 by norm_num,
      CFC.rpow_one _ hA.nonneg, CFC.rpow_one _ hB.nonneg] at h
    exact h
  exact h'.trans (trace_rpow_mul_le_wordMean_two A B hA.isHermitian hB)

#print axioms product_bound_one
#print axioms product_bound_two

end RefinedBMV.DegreesOneTwo
