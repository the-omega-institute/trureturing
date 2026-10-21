/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The literal signed three-node arithmetic columns form a linear Hilbert-sum map with the original coefficient metric. -/

import D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail
import D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import D5.S3.Weil.ZetaBridge.ActualExplicit336
import D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
import D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
import D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteAlgebra
import D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace ComplexOrder Matrix
open D5.S3.Weil.ZetaBridge
open D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance 2000] InnerProductSpace.toInner

/-- Literal cropping of BOTH signed exterior columns. -/
private lemma actual_tail_crop (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) :
    pairedColumnTerm c (N + J) S v j = pairedColumnTerm c N S v (j + J) := by
  simp [pairedColumnTerm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The unscaled complete tail energy decreases with its cutoff. -/
private lemma actual_tail_crop_le (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (hs : Summable (pairedColumnTerm c N S v)) :
    (∑' j : ℕ, pairedColumnTerm c (N + J) S v j) ≤
      ∑' j : ℕ, pairedColumnTerm c N S v j := by
  simp_rw [actual_tail_crop]
  exact tsum_comp_le_tsum_of_inj hs
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i j h => Nat.add_right_cancel h)

/-- The coefficient-uniform lower estimate supplies summability at a later
cutoff; literal cropping recovers every original cutoff, including zero. -/
lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ)
    (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) :
    Summable (pairedColumnTerm c N S v) := by
  obtain ⟨_, _, M, hM⟩ :=
    ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower (by omega : 2 ≤ c) S hS
  have hbig : Summable (pairedColumnTerm c (N + M) S v) := by
    change Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((N + M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((N + M + j + 1 : ℕ) : ℤ))‖ ^ 2)
    exact (hM v (N + M) (by omega)).1
  have hshift : Summable (fun j : ℕ => pairedColumnTerm c N S v (j + M)) := by
    convert hbig using 1
    funext j
    exact (actual_tail_crop c N M S v j).symm
  exact Summable.comp_nat_add hshift

/-- Nonzero on the retained finite head implies positive COMPLETE actual
energy at every cutoff, by the uniform tail lower bound. -/
theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) :
    0 < ∑' j : ℕ, pairedColumnTerm c N S v j := by
  have hS : S.Nonempty := by obtain ⟨k, hk, _⟩ := hv; exact ⟨k, hk⟩
  obtain ⟨C, hC, M, hM⟩ :=
    ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower (by omega : 2 ≤ c) S hS
  have hmass : 0 < ∑ k ∈ S, ‖v k‖ ^ 2 := by
    obtain ⟨k, hk, hvk⟩ := hv
    exact (sq_pos_of_pos (norm_pos_iff.mpr hvk)).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (‖v j‖)) hk)
  let K := max N M
  have hNK : N ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have henc : C * (∑ k ∈ S, ‖v k‖ ^ 2) / ((K : ℝ) + 1) ^ (2 * S.card - 1) ≤
        ∑' j : ℕ, pairedColumnTerm c K S v j := by
    simpa only [pairedColumnTerm] using (hM v K hMK).2
  have hlo : 0 < C * (∑ k ∈ S, ‖v k‖ ^ 2) /
      ((K : ℝ) + 1) ^ (2 * S.card - 1) := by positivity
  have hpos : 0 < ∑' j : ℕ, pairedColumnTerm c K S v j := hlo.trans_le henc
  have hcrop := actual_tail_crop_le c N (K - N) S v
    (actual_tail_summable_all hc S hS N v)
  have hsum : N + (K - N) = K := by omega
  rw [hsum] at hcrop
  exact hpos.trans_le hcrop

/-- Exact kernel on the original finite coefficients, including an empty
head and the zero vector. This does not claim injectivity on all Z->C. -/
theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) :
    (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0 := by
  constructor
  · intro hz k hk
    by_contra hvk
    have hp := actual_finite_head_tail_pos hc S N v ⟨k, hk, hvk⟩
    exact hp.ne' hz
  · intro hv
    have hcol : ∀ m : ℤ, couplingColumn c S v m = 0 := by
      intro m
      unfold couplingColumn
      apply Finset.sum_eq_zero
      intro k hk
      rw [hv k hk, mul_zero]
    simp [pairedColumnTerm, hcol]


/-- The literal three-node source, retaining the signed integer labels. -/
def threeNodes (n : ℤ) : Finset ℤ := {-n, 0, n}

abbrev pairSpace := EuclideanSpace ℂ (Fin 2)
abbrev tailSpace : Type := ↥(lp (fun _ : ℕ => pairSpace) 2)

def pairedColumnVector (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) : pairSpace :=
  !₂[couplingColumn c S v ((N + j + 1 : ℕ) : ℤ),
    couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))]

private lemma pairedColumnVector_norm_sq (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) :
    ‖pairedColumnVector c N S v j‖ ^ 2 =
      pairedColumnTerm c N S v j := by
  simp only [pairedColumnVector, EuclideanSpace.norm_sq_eq]
  simp [pairedColumnTerm]

/-- Summability of the complete actual paired column at every cutoff. -/
private lemma source_summable_all {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (v : ℤ → ℂ) : Summable (pairedColumnTerm c N (threeNodes n) v) :=
  actual_tail_summable_all hc (threeNodes n)
    (by simp [threeNodes]) N v

/-- The genuine Hilbert-sum element of the two signed exterior columns. -/
def pairedColumnLp {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) (v : ℤ → ℂ) : tailSpace :=
  ⟨pairedColumnVector c N (threeNodes n) v, by
    change Memℓp (pairedColumnVector c N (threeNodes n) v) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
    simpa [Real.rpow_two, pairedColumnVector_norm_sq] using source_summable_all hc n N v⟩

private lemma couplingColumn_add (c : ℕ) (S : Finset ℤ) (v w : ℤ → ℂ) (m : ℤ) :
    couplingColumn c S (v + w) m =
      couplingColumn c S v m + couplingColumn c S w m := by
  classical
  simp [couplingColumn, Pi.add_apply, Finset.sum_add_distrib, mul_add]

private lemma couplingColumn_smul (c : ℕ) (S : Finset ℤ) (a : ℂ) (v : ℤ → ℂ) (m : ℤ) :
    couplingColumn c S (a • v) m = a • couplingColumn c S v m := by
  classical
  simp only [couplingColumn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private lemma pairedColumnVector_add (c N : ℕ) (S : Finset ℤ) (v w : ℤ → ℂ) (j : ℕ) :
    pairedColumnVector c N S (v + w) j =
      pairedColumnVector c N S v j + pairedColumnVector c N S w j := by
  ext i
  fin_cases i <;> simp [pairedColumnVector, couplingColumn_add]

private lemma pairedColumnVector_smul (c N : ℕ) (S : Finset ℤ) (a : ℂ) (v : ℤ → ℂ) (j : ℕ) :
    pairedColumnVector c N S (a • v) j =
      a • pairedColumnVector c N S v j := by
  ext i
  fin_cases i <;> simp [pairedColumnVector, couplingColumn_smul]

/-- The source operator is linear in the entire coefficient function. -/
def sourceColumnMap {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) :
    (ℤ → ℂ) →ₗ[ℂ] tailSpace :=
  { toFun := pairedColumnLp hc n N
    map_add' := by
      intro v w
      apply Subtype.ext
      funext j
      exact pairedColumnVector_add c N (threeNodes n) v w j
    map_smul' := by
      intro a v
      apply Subtype.ext
      funext j
      exact pairedColumnVector_smul c N (threeNodes n) a v j }

/-- The three normalized heads in the original integer coordinate order. -/
def singletonHead (k : ℤ) : ℤ → ℂ := Pi.single k 1

def headE (n : ℤ) : ℤ → ℂ :=
  (Real.sqrt 3 : ℂ)⁻¹ •
    (singletonHead (-n) + singletonHead 0 + singletonHead n)

def headO (n : ℤ) : ℤ → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (-singletonHead (-n) + singletonHead n)

def headS (n : ℤ) : ℤ → ℂ :=
  (Real.sqrt 6 : ℂ)⁻¹ •
    (singletonHead (-n) - 2 • singletonHead 0 + singletonHead n)

def normalizedHead (n : ℤ) : Fin 3 → (ℤ → ℂ) :=
  ![headE n, headO n, headS n]

def sourceHead (n : ℤ) (x : Fin 3 → ℂ) : ℤ → ℂ :=
  ∑ i, x i • normalizedHead n i

def sourceTailFamily {c : ℕ} (hc : 3 ≤ c) (N : ℕ) (n : ℤ) :
    Fin 3 → tailSpace :=
  fun i => pairedColumnLp hc n N (normalizedHead n i)

/-- The finite lp combination is exactly the source map at the literal head. -/
theorem source_linear_combination {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (x : Fin 3 → ℂ) :
    ∑ i, x i • sourceTailFamily hc N n i =
      sourceColumnMap hc n N (sourceHead n x) := by
  unfold sourceTailFamily sourceHead
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  rfl

/-- The lp norm square is the complete, untruncated pairedColumnTerm tsum. -/
private lemma pairedColumnLp_norm_sq_tsum {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (v : ℤ → ℂ) :
    ((‖pairedColumnLp hc n N v‖ ^ 2 : ℝ) : ℂ) =
      ((∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j : ℝ) : ℂ) := by
  have h : ‖pairedColumnLp hc n N v‖ ^ 2 =
      ∑' j : ℕ, ‖(pairedColumnLp hc n N v) j‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (pairedColumnLp hc n N v)
  exact congrArg (fun z : ℝ => (z : ℂ)) (h.trans
    (tsum_congr (fun j => pairedColumnVector_norm_sq c N (threeNodes n) v j)))

/-- Complete complex Gram quadratic form, with the source linearity step visible. -/
theorem actual_source_gram_tsum {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (x : Fin 3 → ℂ) :
    let G : Matrix (Fin 3) (Fin 3) ℂ :=
      Matrix.gram ℂ (sourceTailFamily hc N n)
    star x ⬝ᵥ (G *ᵥ x) =
      ((∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j : ℝ) : ℂ) := by
  dsimp
  calc
    star x ⬝ᵥ (Matrix.gram ℂ (sourceTailFamily hc N n) *ᵥ x) =
        ⟪∑ i, x i • sourceTailFamily hc N n i,
          ∑ i, x i • sourceTailFamily hc N n i⟫_ℂ :=
      Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ) (sourceTailFamily hc N n) x x
    _ = ⟪sourceColumnMap hc n N (sourceHead n x),
          sourceColumnMap hc n N (sourceHead n x)⟫_ℂ := by
      rw [source_linear_combination]
    _ = ((‖sourceColumnMap hc n N (sourceHead n x)‖ ^ 2 : ℝ) : ℂ) :=
      by
        simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using
          (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (sourceColumnMap hc n N (sourceHead n x)))
    _ = ((‖pairedColumnLp hc n N (sourceHead n x)‖ ^ 2 : ℝ) : ℂ) := by
      rfl
    _ = ((∑' j : ℕ, pairedColumnTerm c N (threeNodes n)
          (sourceHead n x) j : ℝ) : ℂ) :=
      pairedColumnLp_norm_sq_tsum hc n N (sourceHead n x)

/-- Finite Euclidean realization of the original three-node coefficient metric. -/
def nodeVector (n : ℤ) (v : ℤ → ℂ) : EuclideanSpace ℂ (Fin 3) :=
  !₂[v (-n), v 0, v n]

def coefficientInner (n : ℤ) (v w : ℤ → ℂ) : ℂ :=
  ⟪nodeVector n v, nodeVector n w⟫_ℂ

def coefficientGram (n : ℤ) (b : Fin 3 → (ℤ → ℂ)) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => coefficientInner n (b i) (b j)

private lemma coefficientInner_eq_original_sum {n : ℤ} (hn : n ≠ 0) (v w : ℤ → ℂ) :
    coefficientInner n v w =
      ∑ k ∈ threeNodes n, conj (v k) * w k := by
  classical
  have hn0 : (-n : ℤ) ≠ 0 := neg_ne_zero.mpr hn
  have hsep : (-n : ℤ) ≠ n := by
    intro h
    have : (2 : ℤ) * n = 0 := by linarith
    exact hn (by omega)
  have hsep' : (n : ℤ) ≠ -n := hsep.symm
  unfold coefficientInner nodeVector
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  simp [threeNodes, Fin.sum_univ_succ, hn, Ne.symm hn, hn0, hsep, hsep', ne_eq,
    sub_eq_add_neg] <;> ring

private lemma normalizedHead_nodeVector {n : ℤ} (hn : n ≠ 0) :
    nodeVector n (normalizedHead n 0) =
      !₂[(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 3 : ℂ)⁻¹] ∧
    nodeVector n (normalizedHead n 1) =
      !₂[-(Real.sqrt 2 : ℂ)⁻¹, 0, (Real.sqrt 2 : ℂ)⁻¹] ∧
    nodeVector n (normalizedHead n 2) =
      !₂[(Real.sqrt 6 : ℂ)⁻¹, -2 * (Real.sqrt 6 : ℂ)⁻¹,
        (Real.sqrt 6 : ℂ)⁻¹] := by
  have hn0 : (-n : ℤ) ≠ 0 := neg_ne_zero.mpr hn
  have hneq : (-n : ℤ) ≠ n := by
    intro h
    have : (2 : ℤ) * n = 0 := by linarith
    exact hn (by omega)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext i
    fin_cases i <;>
      simp [normalizedHead, nodeVector, headE, headO, headS, singletonHead,
        hn, hn0, hneq, hneq.symm, mul_comm]

/-- The three normalized heads are orthonormal in the original node metric.
The proof is a finite `Fin 3` computation, retaining all square-root factors. -/
theorem normalizedHead_coefficient_gram {n : ℤ} (hn : n ≠ 0) :
    coefficientGram n (normalizedHead n) = 1 := by
  classical
  rcases normalizedHead_nodeVector hn with ⟨hE, hO, hS⟩
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt (6 : ℝ)) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hc2 : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs2
  have hc3 : (Real.sqrt (3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs3
  have hc6 : (Real.sqrt (6 : ℝ) : ℂ) ^ 2 = 6 := by exact_mod_cast hs6
  have hi2 : ((Real.sqrt (2 : ℝ) : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    rw [inv_pow, hc2]
    norm_num
  have hi3 : ((Real.sqrt (3 : ℝ) : ℂ)⁻¹) ^ 2 = (1 / 3 : ℂ) := by
    rw [inv_pow, hc3]
    norm_num
  have hi6 : ((Real.sqrt (6 : ℝ) : ℂ)⁻¹) ^ 2 = (1 / 6 : ℂ) := by
    rw [inv_pow, hc6]
    norm_num
  have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change conj ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal 2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [coefficientGram, Matrix.of_apply, coefficientInner,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    simp [hE, hO, hS, Fin.sum_univ_succ, Complex.star_def, hconj2] <;>
      ring_nf <;> norm_num [hi2, hi3, hi6, hconj2]

lemma sourceHead_original_norm {n : ℤ} (hn : n ≠ 0) (x : Fin 3 → ℂ) :
    (∑ k ∈ threeNodes n, ‖sourceHead n x k‖ ^ 2) = ∑ i : Fin 3, ‖x i‖ ^ 2 := by
  have hlin : (∑ i, x i • nodeVector n (normalizedHead n i)) =
      nodeVector n (sourceHead n x) := by
    ext k
    fin_cases k <;> simp [nodeVector, sourceHead, Finset.sum_apply]
  have h := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ)
    (fun i : Fin 3 => nodeVector n (normalizedHead n i)) x x
  change star x ⬝ᵥ (coefficientGram n (normalizedHead n) *ᵥ x) =
    ⟪∑ i, x i • nodeVector n (normalizedHead n i),
      ∑ i, x i • nodeVector n (normalizedHead n i)⟫_ℂ at h
  rw [normalizedHead_coefficient_gram hn, Matrix.one_mulVec, hlin] at h
  change star x ⬝ᵥ x = coefficientInner n (sourceHead n x) (sourceHead n x) at h
  rw [coefficientInner_eq_original_sum hn] at h
  have hr := congrArg Complex.re h
  simpa only [dotProduct, Pi.star_apply, Complex.star_def, RCLike.conj_mul,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    Complex.ofReal_re] using hr.symm

/-- The retained literal node values determine the normalized coefficient vector. -/
private theorem sourceHead_eq_zero_of_retained_zero {n : ℤ} (hn : n ≠ 0)
    (x : Fin 3 → ℂ) (hx : ∀ k ∈ threeNodes n, sourceHead n x k = 0) : x = 0 := by
  have hmass := sourceHead_original_norm hn x
  have hzero : (∑ k ∈ threeNodes n, ‖sourceHead n x k‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [hx k hk]
  rw [hzero] at hmass
  funext i
  have hi : ‖x i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖x j‖)).mp hmass.symm i
      (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- Positive definiteness is on the retained three-dimensional source, at every cutoff. -/
theorem actual_gram_posDef {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) (N : ℕ) :
    (Matrix.gram ℂ (sourceTailFamily hc N n)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_gram ℂ _)
  intro x hx
  rw [actual_source_gram_tsum hc n N x]
  have hzero : (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j) ≠ 0 := by
    intro hz
    apply hx
    exact sourceHead_eq_zero_of_retained_zero hn x
      ((actual_finite_head_tail_zero_iff hc (threeNodes n) N
        (sourceHead n x)).mp hz)
  have hnonneg : 0 ≤ ∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j :=
    tsum_nonneg (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpos := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  exact (RCLike.ofReal_pos (K := ℂ)).mpr hpos

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge


noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open scoped Interval
open ActualThreeNodeSourceHeadBridge ActualPairedReciprocal ActualNodalCoercivity
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds
local notation "U₃" => ActualThreeNodeFiniteAlgebra.U
local notation "T₃" => ActualThreeNodeFiniteAlgebra.T
local notation "C₃" => ActualThreeNodeFiniteAlgebra.C
local notation "O₃" => ActualThreeNodeFiniteAlgebra.O

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteEnergy

lemma nodes_distinct {n : ℤ} (hn : n ≠ 0) :
    -n ≠ 0 ∧ -n ≠ n ∧ (0 : ℤ) ≠ n := by
  refine ⟨neg_ne_zero.mpr hn, ?_, Ne.symm hn⟩
  omega

lemma threeNodes_card {n : ℤ} (hn : n ≠ 0) : (threeNodes n).card = 3 := by
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  simp [threeNodes, hn, hm0, hmp, h0p]

lemma actual_symbol_zero (c : ℕ) : arithmeticBoundarySymbol c 0 = 0 := by
  have h := arithmetic_boundary_symbol_neg c 0
  simp only [neg_zero] at h
  linarith

/-- Exact D/P/Q of the literal signed set; there is no positivity assumption on n. -/
lemma actual_three_nodal {n : ℤ} (hn : n ≠ 0) (c : ℕ) (v : ℤ → ℂ) :
    D (threeNodes n) = X * (X ^ 2 - C ((n : ℂ) ^ 2)) ∧
    Q (threeNodes n) v =
      C (v (-n) + v 0 + v n) * X ^ 2 +
        C ((n : ℂ) * (v n - v (-n))) * X - C ((n : ℂ) ^ 2 * v 0) ∧
    P c (threeNodes n) v =
      C ((arithmeticBoundarySymbol c n : ℂ) * (v n - v (-n))) * X ^ 2 +
        C ((arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (v n + v (-n))) * X := by
  classical
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  have h0 := actual_symbol_zero c
  constructor
  · simp [D, threeNodes, Lagrange.nodal, hn, hm0, hmp, h0p]
    ring
  constructor
  · simp [Q, threeNodes, Lagrange.nodal, hn, hm0, hmp, hmp.symm, h0p,
      Finset.erase_insert_of_ne, hm0.symm, h0p.symm,
      map_add, map_sub, map_mul, map_pow]
    ring
  · simp [P, threeNodes, Lagrange.nodal, hn, hm0, hmp, hmp.symm, h0p,
      Finset.erase_insert_of_ne, hm0.symm, h0p.symm,
      arithmetic_boundary_symbol_neg, h0, map_add, map_sub, map_mul, map_pow]
    ring

/-- Unnormalized coordinates are used only inside the finite algebra. -/
def rawHead (n : ℤ) (p q s : ℂ) : ℤ → ℂ :=
  p • (singletonHead (-n) + singletonHead 0 + singletonHead n) +
  q • (-singletonHead (-n) + singletonHead n) +
  s • (singletonHead (-n) - 2 • singletonHead 0 + singletonHead n)

lemma rawHead_nodes {n : ℤ} (hn : n ≠ 0) (p q s : ℂ) :
    rawHead n p q s (-n) = p - q + s ∧
    rawHead n p q s 0 = p - 2 * s ∧
    rawHead n p q s n = p + q + s := by
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [rawHead, singletonHead, Pi.single_apply, hn, hm0, hmp, hmp.symm,
      h0p, h0p.symm, hm0.symm, smul_eq_mul] <;> ring

lemma sourceHead_eq_rawHead (n : ℤ) (x : Fin 3 → ℂ) :
    sourceHead n x = rawHead n (x 0 / (Real.sqrt 3 : ℂ))
      (x 1 / (Real.sqrt 2 : ℂ)) (x 2 / (Real.sqrt 6 : ℂ)) := by
  funext k
  simp [sourceHead, normalizedHead, headE, headO, headS, rawHead,
    Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  <;> ring

/-- These are evaluations of the genuine reciprocal polynomials, not premises. -/
def rawA (a r : ℝ) (p q s : ℂ) : ℂ[X] :=
  C (2 * (a : ℂ) * q) + C (2 * (a : ℂ) * (r : ℂ) * (p + s)) * X

def rawB (r : ℝ) (p q s : ℂ) : ℂ[X] :=
  C (3 * p) + C (2 * (r : ℂ) * q) * X +
    C ((r : ℂ) ^ 2 * (-p + 2 * s)) * X ^ 2

lemma reciprocal_three (N : ℕ) (b0 b1 b2 : ℂ) :
    reciprocalPolynomial 3 N (C b0 + C b1 * X + C b2 * X ^ 2) =
      C b2 + C (b1 / (N : ℂ)) * X + C (b0 / (N : ℂ) ^ 2) * X ^ 2 := by
  simp [reciprocalPolynomial, Finset.sum_range_succ, Polynomial.coeff_X]
  <;> ring

lemma actual_raw_reciprocals {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (p q s : ℂ) :
    reciprocalPolynomial 3 N (P c (threeNodes n) (rawHead n p q s)) =
      rawA (arithmeticBoundarySymbol c n) ((n : ℝ) / N) p q s ∧
    reciprocalPolynomial 3 N (Q (threeNodes n) (rawHead n p q s)) =
      rawB ((n : ℝ) / N) p q s := by
  rcases actual_three_nodal hn c (rawHead n p q s) with ⟨_hD, hQ, hP⟩
  rcases rawHead_nodes hn p q s with ⟨hm, hz, hp⟩
  simp only [hm, hz, hp] at hQ hP
  have hPc : P c (threeNodes n) (rawHead n p q s) =
      C 0 + C (2 * (arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (p + s)) * X +
        C (2 * (arithmeticBoundarySymbol c n : ℂ) * q) * X ^ 2 := by
    rw [hP]
    simp [map_add, map_sub, map_mul, map_neg, Polynomial.C_ofNat]
    ring
  have hQc : Q (threeNodes n) (rawHead n p q s) =
      C ((n : ℂ) ^ 2 * (-p + 2 * s)) + C (2 * (n : ℂ) * q) * X + C (3 * p) * X ^ 2 := by
    rw [hQ]
    simp [map_add, map_sub, map_mul, map_neg, Polynomial.C_ofNat]
    ring
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : 2 * (arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (p + s) / (N : ℂ) =
      2 * (arithmeticBoundarySymbol c n : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) * (p + s) := by
    push_cast
    field_simp [hnC] <;> ring
  have h2 : (2 * (n : ℂ) * q) / (N : ℂ) =
      2 * (((n : ℝ) / N : ℝ) : ℂ) * q := by
    push_cast
    field_simp [hnC] <;> ring
  have h3 : ((n : ℂ) ^ 2 * (-p + 2 * s)) / (N : ℂ) ^ 2 =
      (((n : ℝ) / N : ℝ) : ℂ) ^ 2 * (-p + 2 * s) := by
    push_cast
    field_simp [hnC] <;> ring
  constructor
  · rw [hPc, reciprocal_three, h1]
    simp [rawA]
  · rw [hQc, reciprocal_three, h2, h3]
    rfl

def mixed (p s : ℂ) : ℝ := (conj p * s).re

def rawIntegrand (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) : ℝ :=
  ‖value (rawA a r p q s) t + (g : ℂ) * value (rawB r p q s) t‖ ^ 2 +
  ‖value (rawA a r p q s) (-t) - (g : ℂ) * value (rawB r p q s) (-t)‖ ^ 2 +
  mu * (‖value (rawB r p q s) t‖ ^ 2 + ‖value (rawB r p q s) (-t)‖ ^ 2)

/-- The cancellation is exact for arbitrary complex p/q/s, including zero. -/
def quarticCoeffs (g mu a r : ℝ) (p q s : ℂ) : Fin 5 → ℝ :=
  ![18 * (g ^ 2 + mu) * ‖p‖ ^ 2 + 8 * a ^ 2 * ‖q‖ ^ 2,
    24 * g * a * r * (‖p‖ ^ 2 + mixed p s) + 16 * a * g * r * ‖q‖ ^ 2,
    (8 * a ^ 2 - 12 * (g ^ 2 + mu)) * r ^ 2 * ‖p‖ ^ 2 +
      8 * (g ^ 2 + mu) * r ^ 2 * ‖q‖ ^ 2 + 8 * a ^ 2 * r ^ 2 * ‖s‖ ^ 2 +
      (16 * a ^ 2 + 24 * (g ^ 2 + mu)) * r ^ 2 * mixed p s,
    8 * a * g * r ^ 3 * (-‖p‖ ^ 2 + 2 * ‖s‖ ^ 2 + mixed p s),
    2 * (g ^ 2 + mu) * r ^ 4 * (‖p‖ ^ 2 + 4 * ‖s‖ ^ 2 - 4 * mixed p s)]

lemma rawIntegrand_parity_pair (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :
    rawIntegrand g mu a r p q s t =
      2 * ‖value (rawA a r p 0 s) t + (g : ℂ) * value (rawB r p 0 s) t‖ ^ 2 +
      2 * ‖value (rawA a r 0 q 0) t + (g : ℂ) * value (rawB r 0 q 0) t‖ ^ 2 +
      2 * mu * (‖value (rawB r p 0 s) t‖ ^ 2 + ‖value (rawB r 0 q 0) t‖ ^ 2) := by
  unfold rawIntegrand
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [rawIntegrand, rawA, rawB, value,
    Complex.mul_re, Complex.mul_im, pow_two]
  <;> ring

lemma rawIntegrand_quartic (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :
    rawIntegrand g mu a r p q s t =
      ∑ i : Fin 5, quarticCoeffs g mu a r p q s i * t ^ (i : ℕ) := by
  rw [rawIntegrand_parity_pair]
  unfold quarticCoeffs
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [rawA, rawB, value, quarticCoeffs, mixed, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, pow_two]
  <;> ring

lemma integral_fin5_monomials (b : Fin 5 → ℝ) :
    (∫ t in (0 : ℝ)..1, ∑ i : Fin 5, b i * t ^ (i : ℕ)) =
      ∑ i : Fin 5, b i / (((i : ℕ) : ℝ) + 1) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [intervalIntegral.integral_const_mul, integral_pow, div_eq_mul_inv]
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ => b i * t ^ (i : ℕ))).intervalIntegrable 0 1

lemma raw_pairedEnergy (c : ℕ) (a r : ℝ) (p q s : ℂ) :
    pairedEnergy c (rawA a r p q s) (rawB r p q s) =
      U₃ (Real.pi / 4) (mean c) a r * ‖p‖ ^ 2 +
      2 * O₃ (Real.pi / 4) (mean c) a r * ‖q‖ ^ 2 +
      C₃ (Real.pi / 4) (mean c) a r * ‖s‖ ^ 2 +
      2 * T₃ (Real.pi / 4) (mean c) a r * mixed p s := by
  rw [pairedEnergy_integral]
  change (∫ t in (0 : ℝ)..1, rawIntegrand (Real.pi / 4) (mean c) a r p q s t) = _
  calc
    _ = ∫ t in (0 : ℝ)..1,
        ∑ i : Fin 5, quarticCoeffs (Real.pi / 4) (mean c) a r p q s i * t ^ (i : ℕ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact rawIntegrand_quartic _ _ _ _ _ _ _ _
    _ = ∑ i : Fin 5,
        quarticCoeffs (Real.pi / 4) (mean c) a r p q s i / (((i : ℕ) : ℝ) + 1) :=
      integral_fin5_monomials _
    _ = _ := by
      simp [quarticCoeffs, Fin.sum_univ_succ, ActualThreeNodeFiniteAlgebra.U,
        ActualThreeNodeFiniteAlgebra.T, ActualThreeNodeFiniteAlgebra.C,
        ActualThreeNodeFiniteAlgebra.O]
      <;> ring

lemma mixed_div_real (p s : ℂ) (u v : ℝ) :
    mixed (p / (u : ℂ)) (s / (v : ℂ)) = mixed p s / (u * v) := by
  simp [mixed, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.mul_im]
  <;> ring

lemma norm_div_sqrt_sq (p : ℂ) {d : ℝ} (hd : 0 ≤ d) :
    ‖p / (Real.sqrt d : ℂ)‖ ^ 2 = ‖p‖ ^ 2 / d := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd]

def finiteForm (g mu a r : ℝ) (x : Fin 3 → ℂ) : ℝ :=
  U₃ g mu a r / 3 * ‖x 0‖ ^ 2 + O₃ g mu a r * ‖x 1‖ ^ 2 +
    C₃ g mu a r / 6 * ‖x 2‖ ^ 2 +
    2 * (T₃ g mu a r / Real.sqrt 18) * mixed (x 0) (x 2)

def finiteMatrix (g mu a r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((U₃ g mu a r / 3 : ℝ) : ℂ), 0, ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ);
      0, (O₃ g mu a r : ℂ), 0;
      ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ), 0, ((C₃ g mu a r / 6 : ℝ) : ℂ)]

lemma finiteMatrix_form (g mu a r : ℝ) (x : Fin 3 → ℂ) :
    star x ⬝ᵥ (finiteMatrix g mu a r *ᵥ x) = (finiteForm g mu a r x : ℂ) := by
  apply Complex.ext
  all_goals
    simp [finiteMatrix, finiteForm, mixed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.star_apply, Complex.star_def, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring

lemma finiteMatrix_isHermitian (g mu a r : ℝ) :
    (finiteMatrix g mu a r).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteMatrix, Matrix.conjTranspose_apply]

/-- Physical finite-energy realization in the ORIGINAL orthonormal metric. -/
theorem actual_finite_energy_form {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (x : Fin 3 → ℂ) :
    pairedEnergy c
        (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))
        (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) =
      finiteForm (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
  rw [sourceHead_eq_rawHead]
  rcases actual_raw_reciprocals hn c N hN
      (x 0 / (Real.sqrt 3 : ℂ)) (x 1 / (Real.sqrt 2 : ℂ))
      (x 2 / (Real.sqrt 6 : ℂ)) with ⟨hA, hB⟩
  rw [hA, hB, raw_pairedEnergy]
  rw [norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 3),
    norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 2),
    norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 6), mixed_div_real]
  have hs : Real.sqrt (3 : ℝ) * Real.sqrt 6 = Real.sqrt 18 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hs]
  unfold finiteForm
  ring

theorem actual_finite_matrix_realization {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (x : Fin 3 → ℂ) :
    star x ⬝ᵥ (finiteMatrix (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) *ᵥ x) =
      (pairedEnergy c
        (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))
        (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) : ℂ) := by
  rw [finiteMatrix_form, actual_finite_energy_form hn c N hN]

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteEnergy


noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open ActualThreeNodeSourceHeadBridge ActualThreeNodeFiniteEnergy
open ActualPairedReciprocal ActualNodalCoercivity ActualNodalTailEnclosure
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSymmetricDenominator

/-- Exact single-source denominator. Its sign is retained until after norm square. -/
lemma actual_single_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)
    (hN : 0 < N) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) (hmS : m ∉ threeNodes n) :
    Real.pi ^ 2 * (1 - ((n : ℝ) / (m : ℝ)) ^ 2) ^ 2 *
        ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 /
        (m : ℝ) ^ 2 := by
  have hSne : (threeNodes n).Nonempty := by simp [threeNodes]
  have hmodel := actual_nodal_polynomial_model c (threeNodes n) hSne v
  have hP : (P c (threeNodes n) v).natDegree < 3 := by
    simpa only [threeNodes_card hn] using hmodel.1
  have hQ : (Q (threeNodes n) v).natDegree < 3 := by
    simpa only [threeNodes_card hn] using hmodel.2.1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hp := reciprocalPolynomial_exact (by norm_num : 1 ≤ 3) hN
    (P c (threeNodes n) v) hP (m : ℂ) hmC
  have hq := reciprocalPolynomial_exact (by norm_num : 1 ≤ 3) hN
    (Q (threeNodes n) v) hQ (m : ℂ) hmC
  have harg : (N : ℂ) / (m : ℂ) = (((N : ℝ) / m : ℝ) : ℂ) := by push_cast; rfl
  norm_num at hp hq
  rw [harg] at hp hq
  have hnum : (Real.pi : ℂ) * (D (threeNodes n)).eval (m : ℂ) *
      couplingColumn c (threeNodes n) v m =
      (m : ℂ) ^ 2 *
        (value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)) := by
    rw [hmodel.2.2 m hmS, ← hp, ← hq]
    unfold value
    ring
  have hd : (D (threeNodes n)).eval (m : ℂ) =
      (((m : ℝ) * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [(actual_three_nodal hn c v).1]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_C]
    push_cast <;> ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hnum
  rw [hd] at hnorm
  have hbase : Real.pi ^ 2 * ((m : ℝ) * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) ^ 2 *
      ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      (m : ℝ) ^ 4 *
        ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 := by
    simpa only [norm_mul, norm_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_intCast, sq_abs, ← pow_mul] using hnorm
  have hcancel : Real.pi ^ 2 * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) ^ 2 *
      ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      (m : ℝ) ^ 2 *
        ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hmr)
    nlinarith only [hbase]
  field_simp [hmr]
  nlinarith only [hcancel]

lemma threeNodes_radius (n : ℤ) :
    ∀ k ∈ threeNodes n, |(k : ℝ)| ≤ |(n : ℝ)| := by
  intro k hk
  simp only [threeNodes, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> simp

/-- Both genuine signs have the SAME squared denominator; neither is discarded. -/
lemma actual_pair_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)
    (hN : 0 < N) (hR : |(n : ℝ)| < (N : ℝ)) (v : ℤ → ℂ) (j : ℕ) :
    Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *
        pairedColumnTerm c N (threeNodes n) v j =
      pairedTerm c N
        (reciprocalPolynomial 3 N (P c (threeNodes n) v))
        (reciprocalPolynomial 3 N (Q (threeNodes n) v)) j := by
  let m : ℤ := ((N + j + 1 : ℕ) : ℤ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNm : (N : ℝ) < (m : ℝ) := by
    dsimp [m]
    exact_mod_cast (show N < N + j + 1 by omega)
  have hmp : (0 : ℝ) < m := hNr.trans hNm
  have hm0 : m ≠ 0 := by intro he; simpa [he] using hmp
  have hnot : m ∉ threeNodes n := by
    intro he
    have h := threeNodes_radius n m he
    rw [abs_of_pos hmp] at h
    linarith
  have hnotm : -m ∉ threeNodes n := by
    intro he
    have h := threeNodes_radius n (-m) he
    simp only [Int.cast_neg, abs_neg, abs_of_pos hmp] at h
    linarith
  have hp := actual_single_symmetric_denominator hn c N hN v m hm0 hnot
  have hm := actual_single_symmetric_denominator hn c N hN v (-m)
    (neg_ne_zero.mpr hm0) hnotm
  simp only [Int.cast_neg, div_neg, neg_sq] at hm
  have hs := congrArg₂ (fun x y : ℝ => x + y) hp hm
  convert hs using 1 <;>
    simp only [pairedColumnTerm, pairedTerm, m, Int.cast_natCast] <;> ring

lemma symmetric_factor_bounds {b N m : ℝ} (hN : 0 < N) (hR : |b| < N) (hNm : N < m) :
    0 < (1 - (b / N) ^ 2) ^ 2 ∧
      (1 - (b / N) ^ 2) ^ 2 ≤ (1 - (b / m) ^ 2) ^ 2 ∧
      (1 - (b / m) ^ 2) ^ 2 ≤ 1 := by
  have hm := hN.trans hNm
  have hratN : |b| / N < 1 := (div_lt_one hN).mpr hR
  have hratN0 : 0 ≤ |b| / N := div_nonneg (abs_nonneg _) hN.le
  have hratm0 : 0 ≤ |b| / m := div_nonneg (abs_nonneg _) hm.le
  have hrat : |b| / m ≤ |b| / N :=
    div_le_div_of_nonneg_left (abs_nonneg _) hN hNm.le
  have hsqN : (b / N) ^ 2 < 1 := by
    have hprod : 0 < (1 - |b| / N) * (1 + |b| / N) :=
      mul_pos (sub_pos.mpr hratN) (by linarith)
    have hs : (|b| / N) ^ 2 < 1 := by nlinarith only [hprod]
    simpa only [div_pow, sq_abs] using hs
  have hsq : (b / m) ^ 2 ≤ (b / N) ^ 2 := by
    simpa only [div_pow, sq_abs] using pow_le_pow_left₀ hratm0 hrat 2
  have hbaseN : 0 < 1 - (b / N) ^ 2 := sub_pos.mpr hsqN
  have hbasem : 0 ≤ 1 - (b / m) ^ 2 := by linarith
  refine ⟨sq_pos_of_pos hbaseN, pow_le_pow_left₀ hbaseN.le (by linarith) 2, ?_⟩
  simpa only [one_pow] using
    pow_le_pow_left₀ hbasem (by nlinarith [sq_nonneg (b / m)] : 1 - (b / m) ^ 2 ≤ 1) 2

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSymmetricDenominator


noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open ActualThreeNodeSourceHeadBridge ActualThreeNodeFiniteEnergy ActualThreeNodeSymmetricDenominator
open ActualPairedReciprocal ActualNodalCoercivity ActualNodalTailEnclosure
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFull336

def delta336 (c : ℕ) : ℝ := 9 * 336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3
def lower336 (c N : ℕ) : ℝ := 1 - delta336 c / N
def upper336 (c N : ℕ) (n : ℤ) : ℝ :=
  (1 + delta336 c / N) / (1 - ((n : ℝ) / N) ^ 2) ^ 2

def actualTailGram {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.gram ℂ (sourceTailFamily hc N n)

/-- Cutoff/radius conditions precede all vectors. The complete infinite tail is
compared multiplicatively, without dividing by head energy or vector mass. -/
theorem actual_full336_all_vector {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :
    ∀ x : Fin 3 → ℂ,
      lower336 c N * finiteForm (Real.pi / 4) (mean c)
          (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x ≤
        Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ∧
      Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ≤
        upper336 c N n * finiteForm (Real.pi / 4) (mean c)
          (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
  intro x
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let v := sourceHead n x
  let A := reciprocalPolynomial 3 N (P c (threeNodes n) v)
  let B := reciprocalPolynomial 3 N (Q (threeNodes n) v)
  let dN : ℝ := (1 - ((n : ℝ) / N) ^ 2) ^ 2
  have hdN : 0 < dN := (symmetric_factor_bounds hNr hR (lt_add_one (N : ℝ))).1
  have hpair := ActualExplicit336.actual_paired_symbol_bounds_explicit336
    hc (by norm_num : 1 ≤ 3) (by norm_num; exact hN9) A B
    (reciprocalPolynomial_degree (by norm_num) _) (reciprocalPolynomial_degree (by norm_num) _)
  have heps : (9 : ℝ) *
      (336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3) / N = delta336 c / N := by
    unfold delta336
    ring
  dsimp only at hpair
  norm_num only [Nat.cast_ofNat] at hpair
  rw [heps] at hpair
  have hcol : Summable (pairedColumnTerm c N (threeNodes n) v) :=
    ActualThreeNodeSourceHeadBridge.actual_tail_summable_all hc (threeNodes n)
      (by simp [threeNodes]) N v
  have hpoint (j : ℕ) : pairedTerm c N A B j ≤
        Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j ∧
      Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j ≤ pairedTerm c N A B j / dN := by
    have hNm : (N : ℝ) < (N + j + 1 : ℕ) := by
      exact_mod_cast (show N < N + j + 1 by omega)
    have hbounds := symmetric_factor_bounds hNr hR hNm
    have he := actual_pair_symmetric_denominator hn c N hN hR v j
    change Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *
      pairedColumnTerm c N (threeNodes n) v j = pairedTerm c N A B j at he
    have hnon : 0 ≤ Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j := by
      unfold pairedColumnTerm
      positivity
    constructor
    · have hh := mul_le_mul_of_nonneg_right hbounds.2.2 hnon
      nlinarith only [he, hh]
    · apply (le_div_iff₀ hdN).mpr
      have hh := mul_le_mul_of_nonneg_right hbounds.2.1 hnon
      nlinarith only [he, hh]
  have hsumlo : (∑' j : ℕ, pairedTerm c N A B j) ≤
      Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) := by
    rw [← hcol.tsum_mul_left (Real.pi ^ 2)]
    exact hpair.1.tsum_le_tsum (fun j => (hpoint j).1) (hcol.mul_left _)
  have hsumhi : Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) ≤
      (∑' j : ℕ, pairedTerm c N A B j) / dN := by
    rw [← hcol.tsum_mul_left (Real.pi ^ 2), ← tsum_div_const]
    exact (hcol.mul_left _).tsum_le_tsum (fun j => (hpoint j).2) (hpair.1.div_const dN)
  have hH : pairedEnergy c A B = finiteForm (Real.pi / 4) (mean c)
      (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
    have hm := actual_finite_matrix_realization hn c N hN x
    rw [finiteMatrix_form] at hm
    exact (Complex.ofReal_inj.mp hm).symm
  have hlow : lower336 c N * pairedEnergy c A B ≤
      (∑' j : ℕ, pairedTerm c N A B j) * N := by
    have hh := (div_le_iff₀ hNr).mp hpair.2.1
    simpa only [lower336] using hh
  have hupp : (∑' j : ℕ, pairedTerm c N A B j) * N ≤
      (1 + delta336 c / N) * pairedEnergy c A B := by
    have hh := (le_div_iff₀ hNr).mp hpair.2.2
    exact hh
  have hK : (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re =
      ∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j := by
    have hh := congrArg Complex.re (actual_source_gram_tsum hc n N x)
    simpa only [actualTailGram, Complex.ofReal_re] using hh
  simp only [hK, ← hH]
  constructor
  · exact hlow.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsumlo hNr.le])
  · calc
      Real.pi ^ 2 * N * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) =
          (Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j)) * N := by ring
      _ ≤ ((∑' j : ℕ, pairedTerm c N A B j) / dN) * N :=
        mul_le_mul_of_nonneg_right hsumhi hNr.le
      _ = ((∑' j : ℕ, pairedTerm c N A B j) * N) / dN := by ring
      _ ≤ ((1 + delta336 c / N) * pairedEnergy c A B) / dN :=
        div_le_div_of_nonneg_right hupp hdN.le
      _ = upper336 c N n * pairedEnergy c A B := by dsimp [upper336, dN]; ring

theorem actual_full336_loewner {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :
    let H := finiteMatrix (Real.pi / 4) (mean c)
      (arithmeticBoundarySymbol c n) ((n : ℝ) / N)
    let K := actualTailGram hc n N
    ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧
      (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef := by
  dsimp only
  have hK : (actualTailGram hc n N).IsHermitian := Matrix.isHermitian_gram _ _
  have hH := finiteMatrix_isHermitian (Real.pi / 4) (mean c)
    (arithmeticBoundarySymbol c n) ((n : ℝ) / N)
  have hreal (q : ℝ) : IsSelfAdjoint (q : ℂ) := by
    change star (q : ℂ) = (q : ℂ)
    simp
  have hsource (x : Fin 3 → ℂ) :
      star x ⬝ᵥ (actualTailGram hc n N *ᵥ x) =
        ((∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j : ℝ) : ℂ) :=
    actual_source_gram_tsum hc n N x
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hK.smul (hreal _)).sub (hH.smul (hreal _)))
    intro x
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, hsource, finiteMatrix_form]
    have hh := (actual_full336_all_vector hc hn N hN9 hR x).1
    rw [hsource x] at hh
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa [pow_two, Complex.mul_re, Complex.mul_im] using sub_nonneg.mpr hh
    · simp [pow_two, Complex.mul_im]
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hH.smul (hreal _)).sub (hK.smul (hreal _)))
    intro x
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, hsource, finiteMatrix_form]
    have hh := (actual_full336_all_vector hc hn N hN9 hR x).2
    rw [hsource x] at hh
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa [pow_two, Complex.mul_re, Complex.mul_im] using sub_nonneg.mpr hh
    · simp [pow_two, Complex.mul_im]

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFull336


namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
open ActualThreeNodeFiniteEnergy ActualThreeNodeFull336 ActualThreeNodeSymmetricDenominator
open PrimeSymbolResonance

/-- The actual sharp upper estimate transfers positive complete source energy
into strict positivity of the finite physical form at every exterior cutoff. -/
theorem actual_finite_energy_pos {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ))
    (x : Fin 3 → ℂ) (hx : x ≠ 0) :
    0 < finiteForm (Real.pi / 4) (mean c)
      (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have htail : 0 < ∑' j : ℕ,
      pairedColumnTerm c N (threeNodes n) (sourceHead n x) j := by
    have hp := (actual_gram_posDef hc hn N).dotProduct_mulVec_pos hx
    rw [actual_source_gram_tsum hc n N x] at hp
    exact (RCLike.ofReal_pos (K := ℂ)).mp hp
  have hK : (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re =
      ∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j := by
    simpa only [actualTailGram, Complex.ofReal_re] using
      congrArg Complex.re (actual_source_gram_tsum hc n N x)
  have hupper : Real.pi ^ 2 * (N : ℝ) *
      (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j) ≤
      upper336 c N n * finiteForm (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
    have hh := (Complex.nonneg_iff.mp
      ((actual_full336_loewner hc hn N hN9 hR).2.dotProduct_mulVec_nonneg x)).1
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, finiteMatrix_form, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hK] at hh
    exact sub_nonneg.mp hh
  have hleft : 0 < Real.pi ^ 2 * (N : ℝ) *
      (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j) := by
    exact mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) hNr) htail
  have hlog : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ c by omega))
  have hdelta : 0 ≤ delta336 c := by unfold delta336; positivity
  have hden : 0 < (1 - ((n : ℝ) / N) ^ 2) ^ 2 :=
    (symmetric_factor_bounds hNr hR (lt_add_one (N : ℝ))).1
  have hu : 0 < upper336 c N n := by
    unfold upper336
    exact div_pos (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hdelta hNr.le)) hden
  by_contra he
  have hnpos := mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt he)
  exact (not_lt_of_ge hnpos) (hleft.trans_le hupper)

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
