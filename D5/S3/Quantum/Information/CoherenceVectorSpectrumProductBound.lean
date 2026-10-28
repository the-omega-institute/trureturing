/- GID: D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CoherenceVectorSpectrumProductBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coherence majorization bounds and the largest eigenvalue have product at least 1/d. -/

import D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
import D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
import Mathlib.Data.Fin.Tuple.Sort

/-! The coherence set of Alvarez–Losada–Portesi–Bosyk, Eqs. (11)–(12), and Conjecture 5. -/

set_option autoImplicit false
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
  (coherenceVector IsDecomposition)
open D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState)
open D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation (Majorizes)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

noncomputable section
namespace D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound

/-- The decreasing rearrangement of a finite real vector. -/
def decreasingRearrangement {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  x ∘ Tuple.sort (α := ℝᵒᵈ) x

/-- The set in Eq. (11): averages of decreasing pure-state squared-amplitude vectors. -/
def coherenceSet {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Set (Fin d → ℝ) :=
  {u | ∃ k p ψ, IsDecomposition ρ k p ψ ∧
    u = fun i => ∑ j, p j * decreasingRearrangement (coherenceVector (ψ j)) i}

/-- A decreasing probability vector majorizing every member of the source coherence set. -/
def IsMajorizationUpperBound {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ν : Fin d → ℝ) : Prop :=
  Antitone ν ∧ (∀ i, 0 ≤ ν i) ∧ (∑ i, ν i) = 1 ∧
    ∀ u ∈ coherenceSet ρ,
      Majorizes (List.ofFn ν) (List.ofFn (decreasingRearrangement u))

/-- The largest Hermitian eigenvalue; the value on non-Hermitian matrices is immaterial. -/
def maxEigenvalue {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  if h : ρ.IsHermitian then sSup (Set.range h.eigenvalues) else 0

private lemma column_ensemble {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsState ρ) :
    ∃ (p : Fin d → ℝ) (ψ : Fin d → Fin d → ℂ),
      IsDecomposition ρ d p ψ ∧
      (∀ j, p j = (ρ j j).re) ∧
      ∀ i j, p j * Complex.normSq (ψ j i) = Complex.normSq (CFC.sqrt ρ i j) := by
  classical
  let a := CFC.sqrt ρ
  let p : Fin d → ℝ := fun j => (ρ j j).re
  let ψ : Fin d → Fin d → ℂ := fun j i =>
    if p j = 0 then Pi.single (⟨0, hd⟩ : Fin d) 1 i else a i j / (Real.sqrt (p j) : ℂ)
  have ha : a.IsHermitian := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have haa : a * a = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hp (j : Fin d) : 0 ≤ p j := (Complex.nonneg_iff.mp hρ.1.diag_nonneg).1
  have hnorm (j : Fin d) : (∑ i, Complex.normSq (a i j)) = p j := by
    have h : aᴴ * a = ρ := by rw [ha.eq, haa]
    have he := congrArg (fun b : Matrix (Fin d) (Fin d) ℂ => (b j j).re) h
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using he
  have hzero (j : Fin d) (hz : p j = 0) (i : Fin d) : a i j = 0 := by
    have hs : (∑ i, Complex.normSq (a i j)) = 0 := (hnorm j).trans hz
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => Complex.normSq_nonneg (a i j))).mp hs
      i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  have hcol (i j : Fin d) : p j * Complex.normSq (ψ j i) = Complex.normSq (a i j) := by
    by_cases hz : p j = 0
    · rw [hz, zero_mul, hzero j hz i, Complex.normSq_zero]
    · have hsq : Real.sqrt (p j) * Real.sqrt (p j) = p j := Real.mul_self_sqrt (hp j)
      change p j * Complex.normSq (if p j = 0 then _ else _) = _
      rw [if_neg hz, Complex.normSq_div, Complex.normSq_ofReal, hsq,
        mul_div_cancel₀ _ hz]
  have hunit (j : Fin d) : (∑ i, Complex.normSq (ψ j i)) = 1 := by
    by_cases hz : p j = 0
    · change (∑ i, Complex.normSq (if p j = 0 then _ else _)) = 1
      simp only [hz, if_true, Pi.single_apply, apply_ite, Complex.normSq_one,
        Complex.normSq_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
        hcol i j)
      rw [← Finset.mul_sum, hnorm j] at hs
      exact (mul_left_cancel₀ hz (hs.trans (mul_one (p j)).symm))
  have houter (j : Fin d) (i k : Fin d) :
      (p j : ℂ) * (ψ j i * star (ψ j k)) = a i j * star (a k j) := by
    by_cases hz : p j = 0
    · rw [hz, Complex.ofReal_zero, zero_mul, hzero j hz i, zero_mul]
    · have hsq : (Real.sqrt (p j) : ℂ) * (Real.sqrt (p j) : ℂ) = (p j : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt (hp j)
      change (p j : ℂ) * ((if p j = 0 then _ else _) * star (if p j = 0 then _ else _)) = _
      rw [if_neg hz, if_neg hz, star_div₀, Complex.star_def, Complex.conj_ofReal,
        div_mul_div_comm, hsq, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hz)]
  refine ⟨p, ψ, ⟨hp, ?_, hunit, ?_⟩, fun _ => rfl, hcol⟩
  · have ht := congrArg Complex.re hρ.2
    simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using ht
  · rw [← haa, ← ha.eq]
    ext i k
    change (∑ j, a i j * star (a k j)) = ∑ j, (p j : ℂ) * (ψ j i * star (ψ j k))
    exact Finset.sum_congr rfl (fun j _ => (houter j i k).symm)

private lemma rearrangement_max {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) (i : Fin d) :
    x i ≤ decreasingRearrangement x ⟨0, hd⟩ := by
  have h := Tuple.monotone_sort (α := ℝᵒᵈ) x
    (show (⟨0, hd⟩ : Fin d) ≤ (Tuple.sort (α := ℝᵒᵈ) x).symm i from Fin.zero_le _)
  change x (Tuple.sort (α := ℝᵒᵈ) x ((Tuple.sort (α := ℝᵒᵈ) x).symm i)) ≤ _ at h
  rwa [Equiv.apply_symm_apply] at h

private lemma first_component_bound {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (ν : Fin d → ℝ)
    (hν : IsMajorizationUpperBound ρ ν)
    (p : Fin d → ℝ) (ψ : Fin d → Fin d → ℂ)
    (hdec : IsDecomposition ρ d p ψ)
    (hcol : ∀ i j, p j * Complex.normSq (ψ j i) = Complex.normSq (CFC.sqrt ρ i j)) :
    (∑ j, (CFC.sqrt ρ j j).re ^ 2) ≤ ν ⟨0, hd⟩ := by
  classical
  let u : Fin d → ℝ := fun i => ∑ j, p j * decreasingRearrangement (coherenceVector (ψ j)) i
  have hu : u ∈ coherenceSet ρ := ⟨d, p, ψ, hdec, rfl⟩
  have htake (x : Fin d → ℝ) : ((List.ofFn x).take 1).sum = x ⟨0, hd⟩ := by
    cases d with
    | zero => omega
    | succ n =>
      simp only [List.ofFn_succ, List.take_succ_cons, List.take_zero,
        List.sum_cons, List.sum_nil, add_zero]
  have hmaj := hν.2.2.2 u hu
  have hfirst := hmaj.1 1 (by omega) (by simpa only [List.length_ofFn] using hd)
  rw [htake, htake] at hfirst
  calc
    (∑ j, (CFC.sqrt ρ j j).re ^ 2) ≤ ∑ j, Complex.normSq (CFC.sqrt ρ j j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (CFC.sqrt ρ j j).im]
    _ = ∑ j, p j * Complex.normSq (ψ j j) :=
      Finset.sum_congr rfl (fun j _ => (hcol j j).symm)
    _ ≤ u ⟨0, hd⟩ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (rearrangement_max hd (coherenceVector (ψ j)) j)
        (hdec.1 j)
    _ ≤ decreasingRearrangement u ⟨0, hd⟩ := rearrangement_max hd u ⟨0, hd⟩
    _ ≤ ν ⟨0, hd⟩ := hfirst

private lemma diagonal_cauchy_schwarz {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (CFC.sqrt ρ).trace.re ^ 2 ≤ (d : ℝ) * ∑ j, (CFC.sqrt ρ j j).re ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun j => (CFC.sqrt ρ j j).re)
  change (∑ j, CFC.sqrt ρ j j).re ^ 2 ≤ _
  rw [Complex.re_sum]
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using h

private lemma trace_sqrt_spectral {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : IsState ρ) :
    (CFC.sqrt ρ).trace.re = ∑ i, Real.sqrt (hρ.1.isHermitian.eigenvalues i) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ ρ hρ.1.nonneg, hρ.1.isHermitian.cfc_eq,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, RCLike.ofReal_re, NNReal.coe_sqrt,
    Real.coe_toNNReal _ (hρ.1.eigenvalues_nonneg i)]

private lemma spectral_bound {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsState ρ) :
    0 < maxEigenvalue ρ ∧ 1 / Real.sqrt (maxEigenvalue ρ) ≤ (CFC.sqrt ρ).trace.re := by
  classical
  have hsum : (∑ i, hρ.1.isHermitian.eigenvalues i) = 1 := by
    have h := congrArg Complex.re hρ.1.isHermitian.trace_eq_sum_eigenvalues
    rw [hρ.2] at h
    simpa only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] using h.symm
  have hle (i : Fin d) : hρ.1.isHermitian.eigenvalues i ≤ maxEigenvalue ρ := by
    rw [maxEigenvalue, dif_pos hρ.1.isHermitian]
    exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
  have hl : 0 < maxEigenvalue ρ := by
    by_contra hn
    have hzero : ∀ i, hρ.1.isHermitian.eigenvalues i = 0 := by
      intro i
      exact le_antisymm ((hle i).trans (le_of_not_gt hn)) (hρ.1.eigenvalues_nonneg i)
    simp only [hzero, Finset.sum_const_zero] at hsum
    norm_num at hsum
  refine ⟨hl, ?_⟩
  rw [trace_sqrt_spectral ρ hρ]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hl)).mpr
  calc
    1 = ∑ i, hρ.1.isHermitian.eigenvalues i := hsum.symm
    _ ≤ ∑ i, Real.sqrt (hρ.1.isHermitian.eigenvalues i) *
        Real.sqrt (maxEigenvalue ρ) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = Real.sqrt (hρ.1.isHermitian.eigenvalues i) *
            Real.sqrt (hρ.1.isHermitian.eigenvalues i) :=
          (Real.mul_self_sqrt (hρ.1.eigenvalues_nonneg i)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle i)) (Real.sqrt_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

private lemma assemble_bound (d : ℕ) (hd : 1 ≤ d) (v l t s : ℝ)
    (hl : 0 < l) (ht : 1 / Real.sqrt l ≤ t)
    (hcs : t ^ 2 ≤ (d : ℝ) * s) (hv : s ≤ v) : 1 / (d : ℝ) ≤ v * l := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have htpos : 0 ≤ t := (le_of_lt (one_div_pos.mpr hsqrt)).trans ht
  have hsq : (1 / Real.sqrt l) ^ 2 ≤ t ^ 2 := sq_le_sq₀ (by positivity) htpos |>.mpr ht
  have hmul : 1 ≤ l * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq hl.le
    have heq : l * (1 / Real.sqrt l) ^ 2 = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt hl.le, mul_one_div_cancel hl.ne']
    rwa [heq] at h
  apply (div_le_iff₀ hdpos).mpr
  calc
    1 ≤ l * t ^ 2 := hmul
    _ ≤ l * ((d : ℝ) * s) := mul_le_mul_of_nonneg_left hcs hl.le
    _ ≤ l * ((d : ℝ) * v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hdpos.le) hl.le
    _ = v * l * (d : ℝ) := by ring

/-- Every majorization upper bound of the source coherence set satisfies the product bound.
The supremum ν(ρ) of Eq. (12) is such an upper bound, so this implies Conjecture 5, Eq. (20),
without constructing the majorization-lattice supremum. -/
theorem result (d : ℕ) (hd : 1 ≤ d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : IsState ρ) (ν : Fin d → ℝ) (hν : IsMajorizationUpperBound ρ ν) :
    1 / (d : ℝ) ≤ ν ⟨0, hd⟩ * maxEigenvalue ρ := by
  obtain ⟨p, ψ, hdec, _, hcol⟩ := column_ensemble hd ρ hρ
  obtain ⟨hl, ht⟩ := spectral_bound hd ρ hρ
  exact assemble_bound d hd _ _ _ _ hl ht (diagonal_cauchy_schwarz ρ)
    (first_component_bound hd ρ ν hν p ψ hdec hcol)

end D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
