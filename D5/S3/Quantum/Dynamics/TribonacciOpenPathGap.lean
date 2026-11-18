/- GID: D5/S3/Quantum/Dynamics/TribonacciOpenPathGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/TribonacciOpenPathGap
   mirror-E: none(waiver:finite-single-particle-spectrum)
   anchors: []
   utility: none
   digest: Positive Tribonacci open chains have minimum absolute eigenvalue tending to zero along every even iterate prefix. -/

import D5.S1.Words.TribonacciPrefixRefutation
import D5.S3.Quantum.Dynamics.OddSquareGreenMass
import D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact exponential Green entries connect literal positive-charge prefixes to finite open spectra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
open D5.S1.Words.TribonacciPrefixRefutation
open D5.S1.Words.TribonacciAlignedWindows
open D5.S3.Quantum.Dynamics.OddSquareGreenMass
open D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)

private lemma prefix_parity (n : ℕ) : prefixLength n % 2 = n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ho := four_odd (n+1) 2
    rw [Nat.odd_iff] at ho
    change ((D5.S1.Words.RankOneMorphismIterationBound.image sigma (4*(n+1)) 2 ++
      prefixWord n).length) % 2 = (n+1) % 2
    rw [List.length_append, Nat.add_mod, ho]
    change (1 + prefixLength n % 2) % 2 = _
    rw [ih]
    omega

private lemma prefix_odd_charge (n : ℕ) (hn : Odd n) : prefixCharge n = (n+1 : ℤ)*(n+2) := by
  rw [prefixCharge_closed, hn.neg_one_pow]
  ring

private lemma eventually_length (k : ℕ) : ∃ J : ℕ, 1 ≤ J ∧ ∀ j ≥ J, k ≤ N j := by
  refine ⟨k+2, by omega, ?_⟩
  intro j hj
  have hg := D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth (by omega : 2 ≤ 3) j
  change j+1 ≤ L j at hg
  unfold N
  omega

def alternatingCharge (a : ℕ → ℤ) (k : ℕ) : ℤ := ((List.range k).map a).alternatingSum

lemma green_charge (rho : ℝ) (hr : rho ≠ 0) (a : ℕ → ℤ) (q : ℕ) :
    greenEntry (fun i => rho ^ (a i)) 0 q = rho ^ (-alternatingCharge a (2*q+1)) := by
  induction q with
  | zero => simp [greenEntry, alternatingCharge]
  | succ q ih =>
    have hc : alternatingCharge a (2*(q+1)+1) = alternatingCharge a (2*q+1) - a (2*q+1) + a (2*(q+1)) := by
      have he : 2*(q+1)+1 = (2*q+1)+1+1 := by omega
      rw [he]
      simp only [alternatingCharge, List.range_succ, List.map_append, List.map_singleton,
        List.alternatingSum_append, List.length_map, List.length_range,
        List.alternatingSum_singleton]
      simp [pow_add, pow_mul]
      <;> ring_nf
    rw [greenEntry, ih, hc]
    simp only [Nat.zero_add]
    rw [← zpow_add₀ hr, ← zpow_sub₀ hr]
    congr 1
    ring


open D5.S3.Quantum.Dynamics.OddSquareGreenMass

def openPath (t : ℕ → ℝ) (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℂ :=
  fun i j => if i.val+1=j.val then (t i.val : ℂ)
    else if j.val+1=i.val then (t j.val : ℂ) else 0

private def signs (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := diagonal (fun i => (-1:ℝ)^i.val)

private def positiveBlock (t : ℕ → ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  signs m * lowerBlock t m * signs m

private def parity (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) :=
  Equiv.ofBijective (fun s => match s with
    | Sum.inl i => ⟨2*i.val, by omega⟩
    | Sum.inr i => ⟨2*i.val+1, by omega⟩) (by
      constructor
      · intro i j h
        cases i with
        | inl i => cases j with
          | inl j => congr 1; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega
          | inr j => have := congrArg Fin.val h; dsimp at this; omega
        | inr i => cases j with
          | inl j => have := congrArg Fin.val h; dsimp at this; omega
          | inr j => congr 1; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega
      · intro k
        by_cases h : k.val % 2 = 0
        · refine ⟨Sum.inl ⟨k.val/2, by have := k.isLt; omega⟩, ?_⟩
          apply Fin.ext; dsimp; omega
        · refine ⟨Sum.inr ⟨k.val/2, by have := k.isLt; omega⟩, ?_⟩
          apply Fin.ext; dsimp; omega)

private lemma signs_square (m : ℕ) : signs m * signs m = 1 := by
  rw [signs, diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j
    simp [← pow_add, ← two_mul, pow_mul]
  · simp [diagonal_apply, h]

private lemma lower_unit (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (m : ℕ) : IsUnit (lowerBlock t m) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp [lowerBlock, ht, ne_of_gt (ht (2*i.val))]
  · intro i j hij
    have hijv : i.val < j.val := hij
    have hne : i ≠ j := by intro e; subst j; omega
    simp [lowerBlock, diagonal_apply, hne, show ¬j.val+1=i.val by omega]

private lemma block_entry (t : ℕ → ℝ) (m : ℕ) (i j : Fin m) :
    positiveBlock t m i j = if i=j then t (2*i.val)
      else if j.val+1=i.val then t (2*j.val+1) else 0 := by
  simp only [positiveBlock, signs, diagonal_mul, mul_diagonal, lowerBlock,
    Matrix.sub_apply, diagonal_apply, of_apply]
  by_cases h : i=j
  · subst j
    simp only [ite_true, show ¬i.val+1=i.val by omega, ite_false, sub_zero]
    have hs : (-1:ℝ)^i.val * (-1:ℝ)^i.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc
      _ = t (2*i.val) * ((-1:ℝ)^i.val * (-1:ℝ)^i.val) := by ring
      _ = _ := by rw [hs, mul_one]
  · simp only [h, ite_false]
    by_cases hv : j.val+1=i.val
    · rw [ite_eq_left hv, ← hv, pow_succ]
      have hs : (-1:ℝ)^j.val * (-1:ℝ)^j.val = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      calc
        _ = t (2*j.val+1) * ((-1:ℝ)^j.val * (-1:ℝ)^j.val) := by ring
        _ = _ := by rw [hs, mul_one]
    · simp [hv]

private lemma parity_path (t : ℕ → ℝ) (m : ℕ) :
    (openPath t m).submatrix (parity m) (parity m) =
      (Matrix.fromBlocks 0 (positiveBlock t m) (positiveBlock t m)ᵀ 0).map Complex.ofRealHom := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j =>
      change openPath t m ⟨2*i.val, by omega⟩ ⟨2*j.val, by omega⟩ = _
      simp only [Fin.val_mk, openPath, Matrix.map_apply, fromBlocks_apply₁₁, fromBlocks_apply₂₂, Matrix.zero_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_zero, show ¬2*i.val+1=2*j.val by omega,
        show ¬2*j.val+1=2*i.val by omega, ite_false]
    | inr j =>
      change openPath t m ⟨2*i.val, by omega⟩ ⟨2*j.val+1, by omega⟩ = _
      simp only [Fin.val_mk, openPath,
        fromBlocks_apply₁₂, Matrix.map_apply, Complex.ofRealHom_eq_coe, block_entry]
      by_cases h : i=j
      · subst j; simp
      · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
        simp only [h, ite_false, show ¬2*i.val+1=2*j.val+1 by omega]
        by_cases hji : j.val+1=i.val
        · simp [hji, show 2*j.val+1+1=2*i.val by omega]
        · simp [hji, show ¬2*j.val+1+1=2*i.val by omega]
  | inr i => cases j with
    | inl j =>
      change openPath t m ⟨2*i.val+1, by omega⟩ ⟨2*j.val, by omega⟩ = _
      simp only [Fin.val_mk, openPath,
        fromBlocks_apply₂₁, Matrix.map_apply, transpose_apply, block_entry]
      by_cases h : j=i
      · subst j; simp [show ¬2*i.val+1+1=2*i.val by omega]
      · have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
        simp only [h, ite_false, show ¬2*j.val+1=2*i.val+1 by omega]
        by_cases hij : i.val+1=j.val
        · simp [hij, show 2*i.val+1+1=2*j.val by omega]
        · simp [hij, show ¬2*i.val+1+1=2*j.val by omega]
    | inr j =>
      change openPath t m ⟨2*i.val+1, by omega⟩ ⟨2*j.val+1, by omega⟩ = _
      simp only [Fin.val_mk, openPath, Matrix.map_apply, fromBlocks_apply₁₁, fromBlocks_apply₂₂, Matrix.zero_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_zero,
        show ¬(2*i.val+1)+1=2*j.val+1 by omega,
        show ¬(2*j.val+1)+1=2*i.val+1 by omega, ite_false]

open D5.S3.Quantum.Dynamics.OddSquareGreenMass

private def positiveGreen (t : ℕ → ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  signs m * greenMatrix t m * signs m

private lemma positive_inverse (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (m : ℕ) :
    positiveBlock t m * positiveGreen t m = 1 ∧
      positiveGreen t m * positiveBlock t m = 1 := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp (lower_unit t ht m)
  have hLG := Matrix.mul_nonsing_inv (lowerBlock t m) hunit
  have hGL := Matrix.nonsing_inv_mul (lowerBlock t m) hunit
  rw [block_inverse t ht m] at hLG hGL
  constructor
  · simp only [positiveBlock, positiveGreen]
    calc
      _ = signs m * lowerBlock t m * (signs m * signs m) * greenMatrix t m * signs m := by
        simp only [Matrix.mul_assoc]
      _ = signs m * (lowerBlock t m * greenMatrix t m) * signs m := by
        rw [signs_square]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hLG, Matrix.mul_one, signs_square]
  · simp only [positiveBlock, positiveGreen]
    calc
      _ = signs m * greenMatrix t m * (signs m * signs m) * lowerBlock t m * signs m := by
        simp only [Matrix.mul_assoc]
      _ = signs m * (greenMatrix t m * lowerBlock t m) * signs m := by
        rw [signs_square]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hGL, Matrix.mul_one, signs_square]

private lemma inverse_parity (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (m : ℕ) :
    ((openPath t m).submatrix (parity m) (parity m))⁻¹ =
      (fromBlocks 0 (positiveGreen t m)ᵀ (positiveGreen t m) 0).map Complex.ofRealHom := by
  apply Matrix.inv_eq_right_inv
  rw [parity_path, ← Matrix.map_mul (f := Complex.ofRealHom)]
  rcases positive_inverse t ht m with ⟨hCG,hGC⟩
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [← transpose_mul, hGC, transpose_one, hCG, fromBlocks_one]
  simp

private lemma path_unit (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (m : ℕ) : IsUnit (openPath t m) := by
  rw [← Matrix.isUnit_submatrix_equiv (parity m) (parity m)]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply Matrix.isUnit_det_of_right_inverse (B :=
    (fromBlocks 0 (positiveGreen t m)ᵀ (positiveGreen t m) 0).map Complex.ofRealHom)
  rw [parity_path, ← Matrix.map_mul (f := Complex.ofRealHom)]
  rcases positive_inverse t ht m with ⟨hCG,hGC⟩
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [← transpose_mul, hGC, transpose_one, hCG, fromBlocks_one]
  simp

private lemma inverse_entry (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (m q : ℕ) (hq : q < m) :
    ‖(openPath t m)⁻¹ ⟨2*q+1, by omega⟩ ⟨0, by omega⟩‖ = greenEntry t 0 q := by
  have he := congrArg (fun A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ =>
    A (Sum.inr ⟨q,hq⟩) (Sum.inl ⟨0,by omega⟩)) (inverse_parity t ht m)
  rw [Matrix.inv_submatrix_equiv] at he
  change (openPath t m)⁻¹ ⟨2*q+1, by omega⟩ ⟨0,by omega⟩ = _ at he
  rw [he]
  simp only [Matrix.map_apply, Complex.ofRealHom_eq_coe, fromBlocks_apply₂₁, positiveGreen, signs,
    diagonal_mul, mul_diagonal, greenMatrix, Nat.zero_le, ite_true,
    Nat.sub_zero, Fin.val_zero, pow_zero, mul_one]
  rw [Complex.norm_real, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  exact abs_of_pos (entry_pos t ht 0 q)

private lemma path_hermitian (t : ℕ → ℝ) (m : ℕ) : (openPath t m).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [openPath]
  by_cases h : i.val+1=j.val
  · have h' : ¬j.val+1=i.val := by omega
    simp [h,h']
  · by_cases h' : j.val+1=i.val <;> simp [h,h']

private lemma small_spectrum (t : ℕ → ℝ) (ht : ∀ i, 0 < t i)
    (m q : ℕ) (hq : q < m) :
    ∃ lam : ℝ, lam ∈ spectrum ℝ (openPath t m) ∧
      |lam| ≤ 1 / greenEntry t 0 q := by
  letI : Nonempty (Fin (2*m)) := ⟨⟨0, by omega⟩⟩
  have hh := path_hermitian t m
  have hu := path_unit t ht m
  let u : (Matrix (Fin (2*m)) (Fin (2*m)) ℂ)ˣ := hu.unit
  have heu : (u : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) = openPath t m := hu.unit_spec
  have hentry := D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone.entry_le_norm
    (openPath t m)⁻¹ ⟨2*q+1,by omega⟩ ⟨0,by omega⟩
  rw [inverse_entry t ht m q hq] at hentry
  have hpos : 0 < greenEntry t 0 q := entry_pos t ht 0 q
  have hn : 0 < ‖(openPath t m)⁻¹‖ := lt_of_lt_of_le hpos hentry
  have hs := CStarAlgebra.norm_or_neg_norm_mem_spectrum (openPath t m)⁻¹ hh.inv.isSelfAdjoint
  rcases hs with hs | hs
  · refine ⟨‖(openPath t m)⁻¹‖⁻¹, ?_, ?_⟩
    · have heinv : (↑u⁻¹ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) = (openPath t m)⁻¹ := by
        rw [Matrix.coe_units_inv, heu]
      rw [← heinv] at hs
      have hh := spectrum.inv₀_mem hs
      simpa [heu] using hh
    · rw [abs_inv, abs_of_pos hn, one_div]
      exact inv_le_inv₀ hn hpos |>.mpr hentry
  · refine ⟨(-‖(openPath t m)⁻¹‖)⁻¹, ?_, ?_⟩
    · have heinv : (↑u⁻¹ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) = (openPath t m)⁻¹ := by
        rw [Matrix.coe_units_inv, heu]
      rw [← heinv] at hs
      have hh := spectrum.inv₀_mem hs
      simpa [heu] using hh
    · rw [abs_inv, abs_neg, abs_of_pos hn, one_div]
      exact inv_le_inv₀ hn hpos |>.mpr hentry
open D5.S1.Words.TribonacciPrefixRefutation
open D5.S1.Words.TribonacciAlignedWindows
open D5.S3.Quantum.Dynamics.OddSquareGreenMass
open D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)

def hopping (rho : ℝ) (i : ℕ) : ℝ := rho ^ (weight (W i))

private theorem eventually_small_spectrum (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) :
    ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, 1 ≤ J ∧ ∀ j ≥ J,
      ∃ lam : ℝ, lam ∈ spectrum ℝ (openPath (hopping rho) (L j / 2)) ∧ |lam| < eps := by
  intro eps heps
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one heps hr1
  let n := 2*k+1
  have hn : Odd n := ⟨k, rfl⟩
  have hp := prefix_parity n
  have ho := hn
  rw [Nat.odd_iff] at ho
  have hlen : 2 * (prefixLength n / 2)+1 = prefixLength n := by omega
  let q := prefixLength n / 2
  have hcharge : alternatingCharge (fun i => weight (W i)) (2*q+1) = (n+1:ℤ)*(n+2) := by
    change alternatingCharge (fun i => weight (W i)) (2*(prefixLength n/2)+1) = _
    rw [hlen, ← prefix_odd_charge n hn]
    unfold alternatingCharge prefixCharge signedWordSum
    rw [← prefixWord_actual n]
    simp [factor, List.map_map, Function.comp_def]
  have hbound : 1 / greenEntry (hopping rho) 0 q = rho ^ ((n+1)*(n+2)) := by
    change 1 / greenEntry (fun i => rho ^ (weight (W i))) 0 q = _
    rw [green_charge rho (ne_of_gt hr), hcharge]
    simp only [_root_.zpow_neg, one_div, inv_inv]
    norm_cast
  obtain ⟨J,hJ,hJL⟩ := eventually_length (prefixLength n+1)
  refine ⟨J,hJ,?_⟩
  intro j hj
  have hnj := hJL j hj
  have hqm : q < L j / 2 := by
    unfold N at hnj
    dsimp [q]
    omega
  obtain ⟨lam,hlam,habs⟩ := small_spectrum (hopping rho)
    (fun i => zpow_pos hr _) (L j/2) q hqm
  refine ⟨lam,hlam,lt_of_le_of_lt habs ?_⟩
  rw [hbound]
  exact lt_of_le_of_lt (pow_le_pow_of_le_one hr.le hr1.le
    (show k ≤ (n+1)*(n+2) by dsimp [n]; nlinarith)) hk

open D5.S1.Words.TribonacciAlignedWindows

def absEigenvalues (rho : ℝ) (j : ℕ) : Finset ℝ :=
  Finset.univ.image (fun i => |(path_hermitian (hopping rho) (L j/2)).eigenvalues i|)

private lemma eigenvalues_nonempty (rho : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (absEigenvalues rho j).Nonempty := by
  have hg := D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth (by omega : 2 ≤ 3) j
  change j+1 ≤ L j at hg
  exact ⟨|(path_hermitian (hopping rho) (L j/2)).eigenvalues ⟨0,by omega⟩|,
    Finset.mem_image.mpr ⟨⟨0,by omega⟩, Finset.mem_univ _, rfl⟩⟩

def gap (rho : ℝ) (j : ℕ) : ℝ :=
  if hj : 1 ≤ j then (absEigenvalues rho j).min' (eigenvalues_nonempty rho j hj) else 0

private lemma gap_nonneg (rho : ℝ) (j : ℕ) : 0 ≤ gap rho j := by
  unfold gap
  split
  · apply Finset.le_min'
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact abs_nonneg _
  · exact le_rfl

private lemma gap_lt_iff (rho : ℝ) (j : ℕ) (hj : 1 ≤ j) (eps : ℝ) :
    gap rho j < eps ↔ ∃ lam : ℝ,
      lam ∈ spectrum ℝ (openPath (hopping rho) (L j/2)) ∧ |lam| < eps := by
  rw [gap, dite_eq_left hj]
  constructor
  · intro h
    have hm := Finset.min'_mem (absEigenvalues rho j) (eigenvalues_nonempty rho j hj)
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    refine ⟨(path_hermitian (hopping rho) (L j/2)).eigenvalues i,
      (path_hermitian (hopping rho) (L j/2)).eigenvalues_mem_spectrum_real i, ?_⟩
    rw [hi]
    exact h
  · rintro ⟨lam,hlam,hlt⟩
    rw [(path_hermitian (hopping rho) (L j/2)).spectrum_real_eq_range_eigenvalues] at hlam
    obtain ⟨i,rfl⟩ := hlam
    exact lt_of_le_of_lt (Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)) hlt

theorem gap_tendsto_zero (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) :
    Filter.Tendsto (gap rho) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨J,hJ,h⟩ := eventually_small_spectrum rho hr hr1 eps heps
  refine ⟨J,?_⟩
  intro j hj
  have hlt := (gap_lt_iff rho j (by omega) eps).mpr (h j hj)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (gap_nonneg rho j)] using hlt


end D5.S3.Quantum.Dynamics.TribonacciOpenPathGap
