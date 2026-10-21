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

noncomputable section
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace ComplexOrder Matrix
open D5.S3.Weil.ZetaBridge
open D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

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
