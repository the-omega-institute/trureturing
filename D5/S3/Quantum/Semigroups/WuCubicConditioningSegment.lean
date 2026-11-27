import D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

/-! Spectral bounds on the Gibbs-weighted conditioning segment in the two-mode
cubic problem, in the range `1 ≤ r ≤ 6/5`. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Kronecker BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicConditioningSegment

open WuCubicOperatorBridge (Mat Occupation G)
open WuCubicHotInnerPartialTrace (Local gibbs reduce lift)
open private root rootValues sandwich_lift sqrt_rootScale_sq root_posDef
  trace_sandwich_pairing from D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
open private rootScale rootScale_pos rootRatio rootRatio_sq from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft isHermitian_kronecker)
open private spectral_sum_kronecker from D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The weighted trace in the embedded variable has the weight `d^(2/3)`.
The positive diagonal root is the one in `WuCubicHotInnerPartialTrace`,
whose sixth power is `gibbs r`. -/
def weightedTrace (r : ℝ) (M : Mat) : Local :=
  partialTraceLeft (((root r ^ 4) ⊗ₖ (1 : Local)) * M)

/-- The active factor of the actual embedded conditional expectation. -/
theorem conditioned_product {r : ℝ} (hr : 1 ≤ r) (X : Mat) :
    G r * lift (reduce r X) * G r =
      (root r ^ 2) ⊗ₖ weightedTrace r (G r * X * G r) := by
  rw [sandwich_lift hr]
  congr 1
  ext j k
  have hp := trace_sandwich_pairing hr X (Matrix.single k j 1)
  have hpair : ((root r * reduce r X * root r) * Matrix.single k j 1).trace =
      (root r * reduce r X * root r) j k := by simp [Matrix.trace_mul_single]
  rw [hpair] at hp
  symm
  calc
    _ = (partialTraceLeft (((root r ^ 4) ⊗ₖ (1 : Local)) * (G r * X * G r)) *
        Matrix.single k j 1).trace := by simp [weightedTrace, Matrix.trace_mul_single]
    _ = ((((root r ^ 4) ⊗ₖ (1 : Local)) * (G r * X * G r)) *
        ((1 : Local) ⊗ₖ Matrix.single k j 1)).trace := by
      rw [Matrix.trace_mul_one_kron_right]
      rfl
    _ = ((G r * X * G r) * ((root r ^ 4) ⊗ₖ Matrix.single k j 1)).trace := by
      rw [Matrix.trace_mul_cycle, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
      exact Matrix.trace_mul_comm _ _
    _ = _ := hp

private theorem weightedTrace_apply (r : ℝ) (M : Mat) (j k : Fin 2) :
    weightedTrace r M j k = ∑ i : Fin 2, (rootValues r i : ℂ) ^ 4 * M (i, j) (i, k) := by
  rw [weightedTrace, root, Matrix.diagonal_pow, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal]
  simp [partialTraceLeft, Matrix.diagonal_mul]

private theorem weightedTrace_psd {r : ℝ} {M : Mat} (hM : M.PosSemidef) :
    (weightedTrace r M).PosSemidef := by
  have heq : weightedTrace r M =
      ∑ i : Fin 2, (rootValues r i ^ 4) •
        M.submatrix (fun j => (i, j)) (fun j => (i, j)) := by
    ext j k
    simp [weightedTrace_apply, Matrix.sum_apply, RCLike.real_smul_eq_coe_mul, ← Complex.ofReal_pow]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun i _ => (hM.submatrix _).smul (by positivity))

private theorem weightedTrace_mono {r : ℝ} {A B : Mat} (h : A ≤ B) :
    weightedTrace r A ≤ weightedTrace r B := by
  rw [Matrix.le_iff] at h ⊢
  have heq : weightedTrace r (B - A) = weightedTrace r B - weightedTrace r A := by
    ext j k
    simp [weightedTrace_apply, mul_sub, Finset.sum_sub_distrib]
  rw [← heq]
  exact weightedTrace_psd h

private def traceWeight (r : ℝ) : ℝ := (root r ^ 4).trace.re

private theorem traceWeight_eq_sum (r : ℝ) :
    traceWeight r = ∑ i : Fin 2, rootValues r i ^ 4 := by
  rw [traceWeight, root, Matrix.diagonal_pow, Matrix.trace_diagonal, Complex.re_sum]
  simp [← Complex.ofReal_pow]

private theorem traceWeight_pos {r : ℝ} (hr : 1 ≤ r) : 0 < traceWeight r := by
  have h := Real.sqrt_pos.2 (rootScale_pos (zero_le_one.trans hr))
  have ht := Real.sqrt_pos.2 (zero_lt_one.trans_le hr)
  simp [traceWeight_eq_sum, rootValues, Fin.sum_univ_two, rootRatio]
  positivity

private theorem weightedTrace_scalar (r c : ℝ) :
    weightedTrace r (c • (1 : Mat)) = (c * traceWeight r) • (1 : Local) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [weightedTrace_apply, traceWeight_eq_sum,
      RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul,
      ← Complex.ofReal_pow, mul_comm]
    ring
  · simp [weightedTrace_apply, hjk]

/-- Expectation bounds for the weighted partial trace over the spectator. -/
theorem weightedTrace_bounds {r l L : ℝ} {M : Mat}
    (hlo : l • (1 : Mat) ≤ M) (hhi : M ≤ L • (1 : Mat)) :
    (l * (root r ^ 4).trace.re) • (1 : Local) ≤ weightedTrace r M ∧
      weightedTrace r M ≤ (L * (root r ^ 4).trace.re) • (1 : Local) := by
  exact ⟨weightedTrace_scalar r l ▸ weightedTrace_mono hlo,
    weightedTrace_scalar r L ▸ weightedTrace_mono hhi⟩

private theorem root_square {r : ℝ} (hr : 1 ≤ r) :
    root r ^ 2 = diagonal (fun i : Fin 2 =>
      (if i = 0 then (rootScale r : ℂ) else (r * rootScale r : ℂ))) := by
  rw [root, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp [rootValues, ← Complex.ofReal_pow, mul_pow,
    sqrt_rootScale_sq hr, rootRatio_sq (zero_le_one.trans hr), mul_comm]

private theorem root_square_bounds {r : ℝ} (hr : 1 ≤ r) :
    rootScale r • (1 : Local) ≤ root r ^ 2 ∧
      root r ^ 2 ≤ (r * rootScale r) • (1 : Local) := by
  have ha := rootScale_pos (zero_le_one.trans hr)
  have hle : rootScale r ≤ r * rootScale r := by nlinarith
  rw [root_square hr]
  have scalar (c : ℝ) : c • (1 : Local) = diagonal (fun _ : Fin 2 => (c : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij,
      RCLike.real_smul_eq_coe_mul]
  rw [scalar, scalar]
  constructor <;> apply Matrix.PosSemidef.diagonal_le_iff.mp <;>
    intro i <;> fin_cases i <;> simp <;>
    rw [← Complex.ofReal_mul] <;> exact Complex.real_le_real.mpr hle

private theorem root_square_trace {r : ℝ} (hr : 1 ≤ r) :
    (root r ^ 2).trace.re = (1 + r) * rootScale r := by
  rw [root_square hr, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp
  ring

private theorem max_eigenvalue {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ i : n, ∀ j, hA.eigenvalues j ≤ hA.eigenvalues i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

private theorem root_square_max {r : ℝ} (hr : 1 ≤ r) (h : (root r ^ 2).IsHermitian) :
    ∃ i : Fin 2, h.eigenvalues i = r * rootScale r := by
  obtain ⟨i, hi⟩ := max_eigenvalue h
  have hupper := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff h _).mpr
    (root_square_bounds hr).2 i
  have hbound := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff h _).mp hi
  have hd := Matrix.PosSemidef.diag_mono hbound (1 : Fin 2)
  have hd0 : (root r ^ 2).diag 1 = (r * rootScale r : ℂ) := by
    rw [root_square hr]
    simp
  rw [hd0] at hd
  have hd' : r * rootScale r ≤ h.eigenvalues i := by
    simp only [Matrix.diag_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      RCLike.real_smul_eq_coe_mul, mul_one] at hd
    rw [← Complex.ofReal_mul] at hd
    exact Complex.real_le_real.mp hd
  exact ⟨i, le_antisymm hupper hd'⟩

private theorem kron_eigenvalue_range {A B : Local} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Set.range (isHermitian_kronecker hA hB).eigenvalues =
      Set.range (fun p : Occupation => hA.eigenvalues p.1 * hB.eigenvalues p.2) := by
  ext x
  let g : ℝ → ℝ := fun y => if y = x then 1 else 0
  have heq := spectral_sum_kronecker hA hB g
  have heq' : ∑ c, g ((isHermitian_kronecker hA hB).eigenvalues c) =
      ∑ p : Occupation, g (hA.eigenvalues p.1 * hB.eigenvalues p.2) :=
    heq.trans (Fintype.sum_prod_type (fun p : Occupation => g (hA.eigenvalues p.1 * hB.eigenvalues p.2))).symm
  clear heq
  constructor
  · rintro ⟨i, hi⟩
    by_contra hn
    have hz : ∀ p : Occupation, g (hA.eigenvalues p.1 * hB.eigenvalues p.2) = 0 := by
      intro p
      have hne : hA.eigenvalues p.1 * hB.eigenvalues p.2 ≠ x :=
        fun he => hn ⟨p, he⟩
      simp [g, hne]
    have hpos : 1 ≤ ∑ j, g ((isHermitian_kronecker hA hB).eigenvalues j) := by
      simpa [g, hi] using
        (Finset.single_le_sum (f := fun j => g ((isHermitian_kronecker hA hB).eigenvalues j))
          (fun j _ => by simp [g]; split <;> norm_num) (Finset.mem_univ i))
    simp [hz] at heq'
    linarith
  · rintro ⟨p, hp⟩
    by_contra hn
    have hz : ∀ j, g ((isHermitian_kronecker hA hB).eigenvalues j) = 0 := by
      intro j
      have hne : (isHermitian_kronecker hA hB).eigenvalues j ≠ x :=
        fun he => hn ⟨j, he⟩
      simp [g, hne]
    have hpos : 1 ≤ ∑ q : Occupation, g (hA.eigenvalues q.1 * hB.eigenvalues q.2) := by
      simpa [g, hp] using
        (Finset.single_le_sum (f := fun q : Occupation => g (hA.eigenvalues q.1 * hB.eigenvalues q.2))
          (fun q _ => by simp [g]; split <;> norm_num) (Finset.mem_univ p))
    simp [hz] at heq'
    linarith

/-- The conditioned endpoint has an attained maximal eigenvalue. Its spectral
ratio is at least `5 * k / 6`, and its trace-to-maximum ratio is at least
`11 * (1 + k) / 6` in the entire temperature interval. -/
theorem conditioned_endpoint_of_ratio {r L k : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (X : Mat) (hL : 0 < L) (hk : 0 < k)
    (hlo : (k * L : ℝ) • (1 : Mat) ≤ G r * X * G r)
    (hup : G r * X * G r ≤ L • (1 : Mat)) :
    ∃ L0 : ℝ, 0 < L0 ∧
      ∃ h0 : (G r * lift (reduce r X) * G r).IsHermitian,
        (∃ i, h0.eigenvalues i = L0) ∧
        (5 / 6 * k * L0 : ℝ) • (1 : Mat) ≤ G r * lift (reduce r X) * G r ∧
        G r * lift (reduce r X) * G r ≤ L0 • (1 : Mat) ∧
        (11 / 6 * (1 + k) : ℝ) * L0 ≤ (G r * lift (reduce r X) * G r).trace.re := by
  rw [conditioned_product hr]
  let S := weightedTrace r (G r * X * G r)
  let a := rootScale r
  let t := traceWeight r
  have ha : 0 < a := rootScale_pos (zero_le_one.trans hr)
  have ht : 0 < t := traceWeight_pos hr
  obtain ⟨hslo, hsup⟩ := weightedTrace_bounds hlo hup
  change (k * L * t) • (1 : Local) ≤ S at hslo
  change S ≤ (L * t) • (1 : Local) at hsup
  have hSpsd : S.PosSemidef := Matrix.LE.le.posSemidef
    (le_trans (smul_nonneg (by positivity : 0 ≤ (k * L * t : ℝ)) (by simp)) hslo)
  let hS := hSpsd.isHermitian
  obtain ⟨j, hj⟩ := max_eigenvalue hS
  let b := hS.eigenvalues j
  have hbup : b ≤ L * t :=
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hS _).mpr hsup j
  have hslow (i : Fin 2) : k * L * t ≤ hS.eigenvalues i :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hS _).mpr hslo i
  have hb : 0 < b := lt_of_lt_of_le (by positivity) (hslow j)
  have hratio (i : Fin 2) : k * b ≤ hS.eigenvalues i := by
    nlinarith only [hslow i, mul_le_mul_of_nonneg_left hbup hk.le]
  have hB : (root r ^ 2).IsHermitian := ((root_posDef hr).posSemidef.pow 2).isHermitian
  have hBmin (i : Fin 2) : a ≤ hB.eigenvalues i :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hB _).mpr (root_square_bounds hr).1 i
  have hBmax (i : Fin 2) : hB.eigenvalues i ≤ r * a :=
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hB _).mpr (root_square_bounds hr).2 i
  let hK := isHermitian_kronecker hB hS
  let L0 := r * a * b
  have hL0 : 0 < L0 := by dsimp [L0]; positivity
  refine ⟨L0, hL0, hK, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := root_square_max hr hB
    have hm : L0 ∈ Set.range (fun p : Occupation => hB.eigenvalues p.1 * hS.eigenvalues p.2) :=
      ⟨(i, j), by simp [L0, a, b, hi]⟩
    rw [← kron_eigenvalue_range hB hS] at hm
    exact hm
  · apply (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hK _).mp
    intro i
    have hm : hK.eigenvalues i ∈ Set.range (fun p : Occupation =>
        hB.eigenvalues p.1 * hS.eigenvalues p.2) := by
      rw [← kron_eigenvalue_range hB hS]
      exact ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hm
    rw [← hp]
    have hprod := mul_le_mul (hBmin p.1) (hratio p.2) (by positivity : 0 ≤ k * b)
      (ha.le.trans (hBmin p.1))
    have hrb : (5 / 6 * k * r) ≤ k := by
      nlinarith only [mul_le_mul_of_nonneg_right
        (show (5 / 6 : ℝ) * r ≤ 1 by linarith) hk.le]
    have h := mul_le_mul_of_nonneg_right hrb (mul_nonneg ha.le hb.le)
    dsimp [L0]
    nlinarith only [hprod, h]
  · apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hK _).mp
    intro i
    have hm : hK.eigenvalues i ∈ Set.range (fun p : Occupation =>
        hB.eigenvalues p.1 * hS.eigenvalues p.2) := by
      rw [← kron_eigenvalue_range hB hS]
      exact ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hm
    rw [← hp]
    exact mul_le_mul (hBmax p.1) (hj p.2)
      ((mul_nonneg hk.le hb.le).trans (hratio p.2)) (by positivity)
  · have hsTrace : (1 + k) * b ≤ S.trace.re := by
      rw [hS.trace_eq_sum_eigenvalues, Complex.re_sum, Fin.sum_univ_two]
      change (1 + k) * b ≤ hS.eigenvalues 0 + hS.eigenvalues 1
      fin_cases j <;> dsimp [b] at * <;> nlinarith only [hratio 0, hratio 1]
    have hBtr : (root r ^ 2).trace.im = 0 := by
      rw [root_square hr, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp
    rw [Matrix.trace_kronecker, Complex.mul_re, hBtr, zero_mul, sub_zero, root_square_trace hr]
    have hh := mul_le_mul_of_nonneg_left hsTrace (by positivity : 0 ≤ (1 + r) * a)
    have hr' : (11 / 6 * (1 + k)) * r ≤ (1 + r) * (1 + k) := by
      nlinarith only [mul_le_mul_of_nonneg_right
        (show (11 / 6 : ℝ) * r ≤ 1 + r by linarith) (by positivity : 0 ≤ 1 + k)]
    have hh' := mul_le_mul_of_nonneg_right hr' (mul_nonneg ha.le hb.le)
    dsimp [L0]
    nlinarith only [hh, hh']

/-- The two-thirds input gives the endpoint ratios `5/9` and `55/18`. -/
theorem conditioned_endpoint {r L : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (X : Mat) (hL : 0 < L)
    (hlo : (2 / 3 * L : ℝ) • (1 : Mat) ≤ G r * X * G r)
    (hup : G r * X * G r ≤ L • (1 : Mat)) :
    ∃ L0 : ℝ, 0 < L0 ∧
      ∃ h0 : (G r * lift (reduce r X) * G r).IsHermitian,
        (∃ i, h0.eigenvalues i = L0) ∧
        (5 / 9 * L0 : ℝ) • (1 : Mat) ≤ G r * lift (reduce r X) * G r ∧
        G r * lift (reduce r X) * G r ≤ L0 • (1 : Mat) ∧
        (55 / 18 : ℝ) * L0 ≤ (G r * lift (reduce r X) * G r).trace.re := by
  simpa only [show (5 / 6 : ℝ) * (2 / 3) = 5 / 9 by norm_num,
    show (11 / 6 : ℝ) * (1 + 2 / 3) = 55 / 18 by norm_num] using
    conditioned_endpoint_of_ratio hr hhi X hL (k := 2 / 3) (by norm_num) hlo hup

private theorem original_trace_bound {M : Mat} {L k : ℝ} (hM : M.IsHermitian)
    (hlow : ∀ i, k * L ≤ hM.eigenvalues i)
    (hmax : ∃ i, hM.eigenvalues i = L) :
    (1 + 3 * k) * L ≤ M.trace.re := by
  obtain ⟨i, hi⟩ := hmax
  rw [hM.trace_eq_sum_eigenvalues, Complex.re_sum]
  change (1 + 3 * k) * L ≤ ∑ j, hM.eigenvalues j
  have hsum : (∑ j : Occupation, (k * L + if j = i then (1 - k) * L else 0)) ≤
      ∑ j, hM.eigenvalues j := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j = i
    · subst j
      simp [hi] <;> ring_nf <;> exact le_rfl
    · simpa [h] using hlow j
  rw [Finset.sum_add_distrib] at hsum
  simp [Fintype.card_prod] at hsum
  nlinarith only [hsum]

/-- Along the actual Gibbs-weighted conditioning segment an input spectral
ratio of at least `k > 0` gives a spectral ratio of at least `5 * k / 6`.
The trace-to-maximum ratio is bounded by the smaller of the two endpoint
bounds. The input and segment maxima are attained. -/
theorem conditioning_segment_bounds_of_ratio {r L s k : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (X : Mat) (hL : 0 < L) (hk : 0 < k) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hM : (G r * X * G r).IsHermitian)
    (hlow : ∀ i, k * L ≤ hM.eigenvalues i)
    (hup : ∀ i, hM.eigenvalues i ≤ L)
    (hmax : ∃ i, hM.eigenvalues i = L) :
    let Ms := (1 - s) • (G r * lift (reduce r X) * G r) + s • (G r * X * G r)
    ∃ Ls : ℝ, 0 < Ls ∧ ∃ hMs : Ms.PosDef,
      (∃ i, hMs.isHermitian.eigenvalues i = Ls) ∧
      (∀ i, 5 / 6 * k * Ls ≤ hMs.isHermitian.eigenvalues i ∧ hMs.isHermitian.eigenvalues i ≤ Ls) ∧
      min (1 + 3 * k) (11 / 6 * (1 + k)) * Ls ≤ Ms.trace.re := by
  dsimp only
  let M := G r * X * G r
  let M0 := G r * lift (reduce r X) * G r
  let Ms := (1 - s) • M0 + s • M
  have hMlo : (k * L : ℝ) • (1 : Mat) ≤ M :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hM _).mp hlow
  have hMhi : M ≤ L • (1 : Mat) :=
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hM _).mp hup
  obtain ⟨L0, hL0, hM0, _, hM0lo, hM0hi, hM0tr⟩ :=
    conditioned_endpoint_of_ratio hr hhi X hL hk hMlo hMhi
  have hMtr : (1 + 3 * k) * L ≤ M.trace.re := original_trace_bound hM hlow hmax
  have hMlo' : (5 / 6 * k * L : ℝ) • (1 : Mat) ≤ M :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hM _).mp
      (fun i => by nlinarith only [hlow i, mul_nonneg hk.le hL.le])
  let K := (1 - s) * L0 + s * L
  have hK : 0 < K := by
    dsimp [K]
    rcases eq_or_lt_of_le hs' with h | h
    · subst s
      simpa using hL
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) hL0)
        (mul_nonneg hs hL.le)
  have hs0 : 0 ≤ 1 - s := sub_nonneg.mpr hs'
  have hlowS : (5 / 6 * k * K : ℝ) • (1 : Mat) ≤ Ms := by
    have h := add_le_add (smul_le_smul_of_nonneg_left hM0lo hs0)
      (smul_le_smul_of_nonneg_left hMlo' hs)
    have hcoeff : (1 - s) * (5 / 6 * k * L0) + s * (5 / 6 * k * L) = 5 / 6 * k * K := by
      dsimp [K]
      ring
    simpa only [smul_smul, ← add_smul, hcoeff, Ms, M, M0] using h
  have hupS : Ms ≤ K • (1 : Mat) := by
    have h := add_le_add (smul_le_smul_of_nonneg_left hM0hi hs0)
      (smul_le_smul_of_nonneg_left hMhi hs)
    simpa only [smul_smul, ← add_smul, K, Ms, M, M0] using h
  let c := min (1 + 3 * k) (11 / 6 * (1 + k))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have htrace : c * K ≤ Ms.trace.re := by
    have h0 : c * L0 ≤ M0.trace.re :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le).trans hM0tr
    have h1 : c * L ≤ M.trace.re :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le).trans hMtr
    have a := mul_le_mul_of_nonneg_left h0 hs0
    have b := mul_le_mul_of_nonneg_left h1 hs
    have heq : Ms.trace.re = (1 - s) * M0.trace.re + s * M.trace.re := by
      simp [Ms, Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]
    rw [heq]
    dsimp [K]
    nlinarith only [a, b]
  have hMs : Ms.IsHermitian := (Matrix.LE.le.posSemidef
    (le_trans (smul_nonneg (by positivity : 0 ≤ (5 / 6 * k * K : ℝ))
      (by simp : (0 : Mat) ≤ 1)) hlowS)).isHermitian
  obtain ⟨i, hi⟩ := max_eigenvalue hMs
  let Ls := hMs.eigenvalues i
  have hLsK : Ls ≤ K :=
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hMs _).mpr hupS i
  have hloS (j : Occupation) : 5 / 6 * k * K ≤ hMs.eigenvalues j :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hMs _).mpr hlowS j
  have hLs : 0 < Ls := lt_of_lt_of_le (by positivity) (hloS i)
  have hMspos : Ms.PosDef := hMs.posDef_iff_eigenvalues_pos.mpr
    (fun j => lt_of_lt_of_le (by positivity) (hloS j))
  exact ⟨Ls, hLs, hMspos, ⟨i, rfl⟩,
    fun j => ⟨(mul_le_mul_of_nonneg_left hLsK (by positivity)).trans (hloS j), hi j⟩,
    (mul_le_mul_of_nonneg_left hLsK hc.le).trans htrace⟩

/-- For an input spectral ratio of at least two-thirds, every segment
eigenvalue is at least `5/9` of its attained maximum and the trace is at
least three times that maximum. -/
theorem conditioning_segment_bounds {r L s : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (X : Mat) (hL : 0 < L) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hM : (G r * X * G r).IsHermitian)
    (hlow : ∀ i, 2 / 3 * L ≤ hM.eigenvalues i)
    (hup : ∀ i, hM.eigenvalues i ≤ L)
    (hmax : ∃ i, hM.eigenvalues i = L) :
    let Ms := (1 - s) • (G r * lift (reduce r X) * G r) + s • (G r * X * G r)
    ∃ Ls : ℝ, 0 < Ls ∧ ∃ hMs : Ms.PosDef,
      (∃ i, hMs.isHermitian.eigenvalues i = Ls) ∧
      (∀ i, 5 / 9 * Ls ≤ hMs.isHermitian.eigenvalues i ∧ hMs.isHermitian.eigenvalues i ≤ Ls) ∧
      3 * Ls ≤ Ms.trace.re := by
  simpa only [show (5 / 6 : ℝ) * (2 / 3) = 5 / 9 by norm_num,
    show min (1 + 3 * (2 / 3 : ℝ)) (11 / 6 * (1 + 2 / 3)) = 3 by norm_num [min_def]] using
    conditioning_segment_bounds_of_ratio hr hhi X hL (k := 2 / 3)
      (by norm_num) hs hs' hM hlow hup hmax

/-- For an input spectral ratio of at least `63/100`, the segment satisfies
the wider curvature bounds `21/40` and `289/100` relative to its attained
maximal eigenvalue. -/
theorem conditioning_segment_bounds_wider {r L s : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (X : Mat) (hL : 0 < L) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hM : (G r * X * G r).IsHermitian)
    (hlow : ∀ i, 63 / 100 * L ≤ hM.eigenvalues i)
    (hup : ∀ i, hM.eigenvalues i ≤ L)
    (hmax : ∃ i, hM.eigenvalues i = L) :
    let Ms := (1 - s) • (G r * lift (reduce r X) * G r) + s • (G r * X * G r)
    ∃ Ls : ℝ, 0 < Ls ∧ ∃ hMs : Ms.PosDef,
      (∃ i, hMs.isHermitian.eigenvalues i = Ls) ∧
      (∀ i, 21 / 40 * Ls ≤ hMs.isHermitian.eigenvalues i ∧ hMs.isHermitian.eigenvalues i ≤ Ls) ∧
      289 / 100 * Ls ≤ Ms.trace.re := by
  simpa only [show (5 / 6 : ℝ) * (63 / 100) = 21 / 40 by norm_num,
    show min (1 + 3 * (63 / 100 : ℝ)) (11 / 6 * (1 + 63 / 100)) = 289 / 100 by
      norm_num [min_def]] using
    conditioning_segment_bounds_of_ratio hr hhi X hL (k := 63 / 100)
      (by norm_num) hs hs' hM hlow hup hmax

#print axioms conditioned_product
#print axioms weightedTrace_bounds
#print axioms conditioned_endpoint_of_ratio
#print axioms conditioned_endpoint
#print axioms conditioning_segment_bounds_of_ratio
#print axioms conditioning_segment_bounds
#print axioms conditioning_segment_bounds_wider

end D5.S3.Quantum.Semigroups.WuCubicConditioningSegment
