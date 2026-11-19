/- GID: D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual complex orthogonality residual of real phase coordinates and its real derivative. -/

import D5.S3.Quantum.Tomography.Hadamard.BanicaCycleForestIncidence
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

open scoped BigOperators Topology
noncomputable section

namespace D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian

/-- Each unordered pair of distinct rows is represented once. -/
abbrev RowPairs (m : Type*) [LinearOrder m] := {e : m × m // e.1 < e.2}

variable {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m]

/-- The matrix obtained by multiplying each entry by a real phase. -/
def phaseMatrix (H : Matrix m n ℂ) (θ : m → n → ℝ) : Matrix m n ℂ :=
  fun s j => H s j * Complex.exp (Complex.I * (θ s j : ℂ))

/-- Orthogonality equations in independent upper-triangular row coordinates. -/
def phaseResidual (H : Matrix m n ℂ) (θ : m → n → ℝ) : RowPairs m → ℂ :=
  fun e => ∑ j, H e.1.1 j * star (H e.1.2 j) *
    Complex.exp (Complex.I * ((θ e.1.1 j - θ e.1.2 j : ℝ) : ℂ))

private def coordinate (s : m) (j : n) : (m → n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj s : (m → n → ℝ) →L[ℝ] (n → ℝ))

private def exponent (e : RowPairs m) (j : n) : (m → n → ℝ) →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp (coordinate e.1.1 j - coordinate e.1.2 j))

/-- The derivative of the phase residual at zero, as a real continuous linear map. -/
def phaseJacobian (H : Matrix m n ℂ) :
    (m → n → ℝ) →L[ℝ] (RowPairs m → ℂ) :=
  ContinuousLinearMap.pi fun e => ∑ j, (H e.1.1 j * star (H e.1.2 j)) • exponent e j

/-- The exponential phase equations are real analytic on the entire phase space. -/
theorem phase_residual_contDiff (H : Matrix m n ℂ) :
    ContDiff ℝ ⊤ (phaseResidual H) := by
  apply contDiff_pi.2
  intro e
  apply ContDiff.sum
  intro j _
  simpa [exponent, coordinate, ContinuousLinearMap.comp_apply] using
    (contDiff_const (c := H e.1.1 j * star (H e.1.2 j))).mul
      ((exponent e j).contDiff.cexp)

/-- The Frechet derivative is computed from the exponential equations themselves. -/
theorem phase_residual_hasFDerivAt_zero (H : Matrix m n ℂ) :
    HasFDerivAt (phaseResidual H) (phaseJacobian H) 0 := by
  apply hasFDerivAt_pi.2
  intro e
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (((exponent e j).hasFDerivAt : HasFDerivAt (exponent e j)
      (exponent e j) (0 : m → n → ℝ)).cexp).const_mul
      (H e.1.1 j * star (H e.1.2 j)))
  simpa [phaseResidual, phaseJacobian, exponent, coordinate,
    ContinuousLinearMap.comp_apply] using h

/-- In coordinates the derivative is i times the weighted row-phase difference. -/
theorem phase_jacobian_apply (H : Matrix m n ℂ) (η : m → n → ℝ) (e : RowPairs m) :
    phaseJacobian H η e = Complex.I * ∑ j,
      H e.1.1 j * star (H e.1.2 j) * ((η e.1.1 j - η e.1.2 j : ℝ) : ℂ) := by
  simp only [phaseJacobian, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, exponent, coordinate, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Additive row and column phases form the range of this linear map. -/
def rowColumnMap : ((m → ℝ) × (n → ℝ)) →ₗ[ℝ] (m → n → ℝ) where
  toFun x s j := x.1 s + x.2 j
  map_add' x y := by ext s j; simp; ring
  map_smul' r x := by ext s j; simp; ring

omit [LinearOrder m] in
/-- The dimension of the row-column phase space is at most the number of row
and column parameters. -/
theorem row_column_finrank_le :
    Module.finrank ℝ (LinearMap.range (rowColumnMap (m := m) (n := n))) ≤
      Fintype.card m + Fintype.card n := by
  simpa using LinearMap.finrank_range_le (rowColumnMap (m := m) (n := n))

/-- The Fourier matrix in additive-character coordinates. -/
def fourierMatrix (p : ℕ) [NeZero p] (S : Finset (ZMod p)) : Matrix S (ZMod p) ℂ :=
  fun s j => ZMod.stdAddChar (s.1 * j)

private theorem frequency_potentials {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S ≠ Finset.univ) (Y : S → S → ℂ) :
    ∃ R : ZMod p → S → ℂ, ∀ s t : S, s ≠ t →
      R (t.1 - s.1) s - R (t.1 - s.1) t = Y s t := by
  classical
  have hex (a : ZMod p) (ha : a ≠ 0) : ∃ r : S → ℂ,
      ∀ e : BanicaCycleForestIncidence.Edges S a,
        r e.1 - r ⟨e.1.1 + a, e.2⟩ = Y e.1 ⟨e.1.1 + a, e.2⟩ := by
    obtain ⟨r, hr⟩ := BanicaCycleForestIncidence.cycle_incidence_surjective S hS
      (Units.mk0 a ha) (fun e => Y e.1 ⟨e.1.1 + a, e.2⟩)
    exact ⟨r, fun e => congrFun hr e⟩
  let R : ZMod p → S → ℂ := fun a => if ha : a = 0 then 0 else Classical.choose (hex a ha)
  refine ⟨R, ?_⟩
  intro s t hst
  have ha : t.1 - s.1 ≠ 0 := sub_ne_zero.mpr (fun h => hst (Subtype.ext h.symm))
  have ht : s.1 + (t.1 - s.1) ∈ S := by simpa using t.2
  have hh := Classical.choose_spec (hex (t.1 - s.1) ha) ⟨s, ht⟩
  have he : (⟨s.1 + (t.1 - s.1), ht⟩ : S) = t := Subtype.ext (by ring)
  rw [he] at hh
  dsimp only [R]
  rw [dif_neg ha]
  exact hh

private theorem complex_fourier_differences {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S ≠ Finset.univ) (Y : S → S → ℂ) :
    ∃ η : S → ZMod p → ℂ, ∀ s t : S, s ≠ t →
      ZMod.dft (η s) (t.1 - s.1) - ZMod.dft (η t) (t.1 - s.1) = Y s t := by
  obtain ⟨R, hR⟩ := frequency_potentials S hS Y
  refine ⟨fun s => ZMod.dft.symm (fun a => R a s), ?_⟩
  intro s t hst
  simpa only [LinearEquiv.apply_symm_apply] using hR s t hst

private theorem star_standard_character {p : ℕ} [NeZero p] (x : ZMod p) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  exact (AddChar.map_neg_eq_conj _ _).symm

private theorem fourier_coefficient {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (s t : S) (j : ZMod p) :
    fourierMatrix p S s j * star (fourierMatrix p S t j) =
      ZMod.stdAddChar ((s.1 - t.1) * j) := by
  change ZMod.stdAddChar (s.1 * j) * star (ZMod.stdAddChar (t.1 * j)) = _
  rw [star_standard_character, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem fourier_difference_eq_sum {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (η : S → ZMod p → ℂ) (s t : S) :
    ZMod.dft (η s) (t.1 - s.1) - ZMod.dft (η t) (t.1 - s.1) =
      ∑ j, ZMod.stdAddChar ((s.1 - t.1) * j) * (η s j - η t j) := by
  rw [ZMod.dft_apply, ZMod.dft_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : -(j * (t.1 - s.1)) = (s.1 - t.1) * j := by ring
  simp only [smul_eq_mul]
  rw [he, mul_sub]

private theorem dft_realPart {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (a : ZMod p) :
    2 * ZMod.dft (fun j => ((f j).re : ℂ)) a =
      ZMod.dft f a + star (ZMod.dft f (-a)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, star_standard_character]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : -(-(j * -a)) = -(j * a) := by ring
  rw [he, Complex.re_eq_add_conj]
  simp only [Complex.star_def]
  ring

private theorem real_fourier_differences {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S ≠ Finset.univ) (Y : S → S → ℂ)
    (hY : ∀ s t, Y t s = -star (Y s t)) :
    ∃ η : S → ZMod p → ℝ, ∀ s t : S, s ≠ t →
      ZMod.dft (fun j => (η s j : ℂ)) (t.1 - s.1) -
        ZMod.dft (fun j => (η t j : ℂ)) (t.1 - s.1) = Y s t := by
  obtain ⟨η, hη⟩ := complex_fourier_differences S hS Y
  refine ⟨fun s j => (η s j).re, ?_⟩
  intro s t hst
  have hs := dft_realPart (η s) (t.1 - s.1)
  have ht := dft_realPart (η t) (t.1 - s.1)
  have hforward := hη s t hst
  have hreverse := hη t s hst.symm
  have hneg : s.1 - t.1 = -(t.1 - s.1) := by ring
  rw [hneg] at hreverse
  have htwice :
      2 * (ZMod.dft (fun j => ((η s j).re : ℂ)) (t.1 - s.1) -
        ZMod.dft (fun j => ((η t j).re : ℂ)) (t.1 - s.1)) = 2 * Y s t := by
    calc
      _ = (ZMod.dft (η s) (t.1 - s.1) - ZMod.dft (η t) (t.1 - s.1)) -
          star (ZMod.dft (η t) (-(t.1 - s.1)) -
            ZMod.dft (η s) (-(t.1 - s.1))) := by
        rw [star_sub]
        linear_combination hs - ht
      _ = Y s t - star (Y t s) := by rw [hforward, hreverse]
      _ = 2 * Y s t := by rw [hY]; simp; ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwice

/-- Every independent complex orthogonality equation can be prescribed by a real
phase velocity when at least one Fourier row has been removed. -/
theorem fourier_jacobian_surjective {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) [LinearOrder S] (hS : S ≠ Finset.univ) :
    Function.Surjective (phaseJacobian (fourierMatrix p S)) := by
  classical
  intro y
  let Y : S → S → ℂ := fun s t =>
    if h : s < t then -Complex.I * y ⟨(s, t), h⟩ else
      if h : t < s then -Complex.I * star (y ⟨(t, s), h⟩) else 0
  have hY (s t : S) : Y t s = -star (Y s t) := by
    by_cases hst : s < t
    · simp [Y, hst, not_lt_of_ge (le_of_lt hst), star_mul, Complex.star_def]
      ring
    · by_cases hts : t < s
      · simp [Y, hst, hts, star_mul, Complex.star_def]
        ring
      · simp [Y, hst, hts]
  obtain ⟨η, hη⟩ := real_fourier_differences S hS Y hY
  refine ⟨η, funext fun e => ?_⟩
  rw [phase_jacobian_apply]
  simp_rw [fourier_coefficient]
  simp only [Complex.ofReal_sub]
  rw [← fourier_difference_eq_sum S (fun s j => (η s j : ℂ)) e.1.1 e.1.2,
    hη e.1.1 e.1.2 (ne_of_lt e.2)]
  simp [Y, e.2, ← mul_assoc, Complex.I_mul_I]

/-- Twice the number of independent row pairs is m(m-1). -/
theorem row_pairs_card_twice :
    2 * Fintype.card (RowPairs m) = Fintype.card m * (Fintype.card m - 1) := by
  classical
  have hc : Fintype.card (RowPairs m) = (Fintype.card m).choose 2 := by
    rw [Fintype.card_subtype]
    exact Fintype.card_product_filter_lt
  rw [hc]
  have hh := Nat.descFactorial_eq_factorial_mul_choose (Fintype.card m) 2
  simpa [Nat.descFactorial_succ, Nat.factorial_succ, Nat.mul_comm] using hh.symm

/-- At a regular phase point the kernel dimension is the variable count minus
the real count of independent orthogonality equations. -/
theorem phase_jacobian_rank_nullity (H : Matrix m n ℂ)
    (hsurj : Function.Surjective (phaseJacobian H)) :
    Module.finrank ℝ (LinearMap.ker (phaseJacobian H).toLinearMap) +
      Fintype.card m * (Fintype.card m - 1) = Fintype.card m * Fintype.card n := by
  let L := (phaseJacobian H).toLinearMap
  have hrank := L.finrank_range_add_finrank_ker
  have hL : LinearMap.range L = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [hL] at hrank
  have hcod : Module.finrank ℝ (RowPairs m → ℂ) =
      Fintype.card m * (Fintype.card m - 1) := by
    rw [← row_pairs_card_twice (m := m)]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  have hdom : Module.finrank ℝ (m → n → ℝ) = Fintype.card m * Fintype.card n := by
    simp [Module.finrank_pi_fintype, Module.finrank_pi]
  simpa only [finrank_top, hcod, hdom, Nat.add_comm] using hrank

/-- A phase-space dimension exceeding the equation count and the row-column
parameter count supplies a genuine kernel direction outside the row-column space. -/
theorem phase_jacobian_kernel_nontrivial (H : Matrix m n ℂ)
    (hsurj : Function.Surjective (phaseJacobian H))
    (h : 2 * Fintype.card (RowPairs m) + Fintype.card m + Fintype.card n <
      Fintype.card m * Fintype.card n) :
    ∃ v : m → n → ℝ, phaseJacobian H v = 0 ∧
      v ∉ LinearMap.range (rowColumnMap (m := m) (n := n)) := by
  classical
  let L := (phaseJacobian H).toLinearMap
  have hrank := phase_jacobian_rank_nullity H hsurj
  rw [← row_pairs_card_twice (m := m)] at hrank
  by_contra hn
  have hle : LinearMap.ker L ≤ LinearMap.range (rowColumnMap (m := m) (n := n)) := by
    intro v hv
    by_contra hnot
    apply hn
    exact ⟨v, hv, hnot⟩
  have hker := Submodule.finrank_mono hle
  dsimp only [L] at hker
  have hrow := row_column_finrank_le (m := m) (n := n)
  omega

end D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
