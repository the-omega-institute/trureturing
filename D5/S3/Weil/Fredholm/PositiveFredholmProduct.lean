/- GID: D5/S3/Weil/Fredholm/PositiveFredholmProduct
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive square-folded spectral factors form a convergent monotone product. -/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ZetaValues

/- Library-search audit trail (2026-09-01):
   * Repository searches for `Fredholm`, `traceClass`, `trace_class`,
     `HilbertSchmidt`, `Multipliable`, `tprod`, and the square-folded factor
     found no declaration for a countable Fredholm determinant or for the
     variable-multiplicity product below. The closest product modules prove
     convergence of different Euler or Weierstrass factors. The nearby
     `SinglePrimeThermalState` audit independently records that pinned Mathlib
     has no countable trace-class operator API.
   * Pinned Mathlib supplies `summable_sigma_of_nonneg` for expanding a
     multiplicity into the finite fiber `Fin (m i)`,
     `Real.summable_log_one_add_of_summable` and
     `Real.multipliable_of_summable_log` for the logarithmic product test, and
     `Real.rexp_tsum_eq_tprod` for its value. These results are reused rather
     than reproved.
   * `hasSum_zeta_two` supplies the exact Basel witness. The divergence
     witness is reduced by comparison to
     `Real.summable_one_div_nat_add_rpow` at exponent one.
   * The source's RH assertion and zero-density input are not proved here:
     the positive ordinates and their weighted square summability are explicit
     parameters. The operator, trace-class, and determinant layers are also
     not claimed because the required countable operator API is absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Fredholm.PositiveFredholmProduct

open scoped BigOperators

noncomputable section

/-- The square-folded spectral product, with natural-number multiplicities. -/
def positiveFredholmProduct {ι : Type*} (gamma : ι → ℝ) (m : ι → ℕ) (x : ℝ) : ℝ :=
  ∏' i, (1 + x / (gamma i) ^ 2) ^ (m i)

private theorem repeated_increment_summable {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2))
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun p : Σ i, Fin (m i) => x / (gamma p.1) ^ 2) := by
  apply (summable_sigma_of_nonneg (fun p => div_nonneg hx (sq_nonneg (gamma p.1)))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  refine (hsum.mul_left x).congr fun i => ?_
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The logarithms of the multiplicity-weighted factors are summable. -/
theorem positive_fredholm_log_summable {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2))
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun i => Real.log ((1 + x / (gamma i) ^ 2) ^ (m i))) := by
  have hExpanded := Real.summable_log_one_add_of_summable
    (repeated_increment_summable gamma m hsum hx)
  simpa [Real.log_pow] using hExpanded.sigma

private theorem positive_fredholm_factor_pos {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ) {x : ℝ} (hx : 0 ≤ x) (i : ι) :
    0 < (1 + x / (gamma i) ^ 2) ^ (m i) := by
  apply pow_pos
  have hquot : 0 ≤ x / (gamma i) ^ 2 := div_nonneg hx (sq_nonneg (gamma i))
  linarith

/-- Weighted square summability makes every nonnegative square-folded product
multipliable. The positivity assumption excludes the source's meaningless
zero ordinates, where real division would otherwise be totalized as zero. -/
theorem positive_fredholm_multipliable {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hpos : ∀ i, 0 < gamma i)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2))
    {x : ℝ} (hx : 0 ≤ x) :
    Multipliable (fun i => (1 + x / (gamma i) ^ 2) ^ (m i)) := by
  exact Real.multipliable_of_summable_log
    (fun i => by
      have hden : 0 < (gamma i) ^ 2 := sq_pos_of_pos (hpos i)
      apply pow_pos
      have hquot : 0 ≤ x / (gamma i) ^ 2 := div_nonneg hx hden.le
      linarith)
    (positive_fredholm_log_summable gamma m hsum hx)

/-- At zero the square-folded product is exactly one. -/
@[simp]
theorem positive_fredholm_zero {ι : Type*} (gamma : ι → ℝ) (m : ι → ℕ) :
    positiveFredholmProduct gamma m 0 = 1 := by
  simp [positiveFredholmProduct]

/-- Every convergent square-folded product is at least one on the nonnegative
axis. -/
theorem one_le_positive_fredholm {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2))
    {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ positiveFredholmProduct gamma m x := by
  have hlog := positive_fredholm_log_summable gamma m hsum hx
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (∑' i, Real.log ((1 + x / (gamma i) ^ 2) ^ (m i))) :=
      Real.exp_le_exp.mpr <| tsum_nonneg fun i => Real.log_nonneg <| one_le_pow₀ <| by
        have hquot : 0 ≤ x / (gamma i) ^ 2 := div_nonneg hx (sq_nonneg (gamma i))
        linarith
    _ = positiveFredholmProduct gamma m x :=
      Real.rexp_tsum_eq_tprod (positive_fredholm_factor_pos gamma m hx) hlog

/-- The square-folded product is monotone on the nonnegative axis. -/
theorem positive_fredholm_monotoneOn {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hpos : ∀ i, 0 < gamma i)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2)) :
    MonotoneOn (positiveFredholmProduct gamma m) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hlogX := positive_fredholm_log_summable gamma m hsum hx
  have hlogY := positive_fredholm_log_summable gamma m hsum hy
  unfold positiveFredholmProduct
  rw [
    ← Real.rexp_tsum_eq_tprod (positive_fredholm_factor_pos gamma m hx) hlogX,
    ← Real.rexp_tsum_eq_tprod (positive_fredholm_factor_pos gamma m hy) hlogY]
  apply Real.exp_le_exp.mpr
  refine hlogX.tsum_le_tsum (fun i => ?_) hlogY
  apply Real.strictMonoOn_log.monotoneOn
  · exact positive_fredholm_factor_pos gamma m hx i
  · exact positive_fredholm_factor_pos gamma m hy i
  · have hden : 0 < (gamma i) ^ 2 := sq_pos_of_pos (hpos i)
    have hquot : x / (gamma i) ^ 2 ≤ y / (gamma i) ^ 2 :=
      (div_le_div_iff_of_pos_right hden).2 hxy
    apply pow_le_pow_left₀
    · have : 0 ≤ x / (gamma i) ^ 2 := div_nonneg hx hden.le
      linarith
    · linarith

/-- Atom-level positive Fredholm completion at the spectral-product layer:
convergence, normalization, positivity, and monotonicity all follow from the
weighted reciprocal-square hypothesis. -/
theorem positive_fredholm_completion {ι : Type*}
    (gamma : ι → ℝ) (m : ι → ℕ)
    (hpos : ∀ i, 0 < gamma i)
    (hsum : Summable (fun i => (m i : ℝ) / (gamma i) ^ 2)) :
    (∀ x, 0 ≤ x → Multipliable (fun i => (1 + x / (gamma i) ^ 2) ^ (m i))) ∧
      positiveFredholmProduct gamma m 0 = 1 ∧
      (∀ x, 0 ≤ x → 1 ≤ positiveFredholmProduct gamma m x) ∧
      MonotoneOn (positiveFredholmProduct gamma m) (Set.Ici 0) := by
  exact ⟨fun _ hx => positive_fredholm_multipliable gamma m hpos hsum hx,
    positive_fredholm_zero gamma m,
    fun _ hx => one_le_positive_fredholm gamma m hsum hx,
    positive_fredholm_monotoneOn gamma m hpos hsum⟩

/-- Concrete positive ordinates for the nonempty Basel witness. -/
def unitSpectrum (i : ℕ) : ℝ := i + 1

/-- Unit multiplicity for the nonempty Basel witness. -/
def unitMultiplicity (_ : ℕ) : ℕ := 1

/-- The witness's weighted reciprocal-square series is exactly the Basel sum. -/
theorem unit_spectrum_weight_hasSum :
    HasSum (fun i => (unitMultiplicity i : ℝ) / (unitSpectrum i) ^ 2)
      (Real.pi ^ 2 / 6) := by
  have htail : (∑' i : ℕ, (1 : ℝ) / (((i + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 6 := by
    have hz := hasSum_zeta_two.tsum_eq
    rw [hasSum_zeta_two.summable.tsum_eq_zero_add] at hz
    simpa using hz
  have hs : Summable (fun i => (unitMultiplicity i : ℝ) / (unitSpectrum i) ^ 2) := by
    simpa [unitMultiplicity, unitSpectrum, Nat.cast_add, Nat.cast_one] using
      (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  rw [hs.hasSum_iff]
  simpa [unitMultiplicity, unitSpectrum, Nat.cast_add, Nat.cast_one] using htail

/-- The concrete Basel product converges at `x = 1`. -/
theorem unit_spectrum_product_one_multipliable :
    Multipliable (fun i : ℕ =>
      (1 + 1 / (unitSpectrum i) ^ 2) ^ (unitMultiplicity i)) := by
  apply positive_fredholm_multipliable unitSpectrum unitMultiplicity
  · intro i
    dsimp [unitSpectrum]
    positivity
  · exact unit_spectrum_weight_hasSum.summable
  · norm_num

/-- The concrete Basel product is normalized at `x = 0`. -/
theorem unit_spectrum_product_zero :
    positiveFredholmProduct unitSpectrum unitMultiplicity 0 = 1 := by
  exact positive_fredholm_zero unitSpectrum unitMultiplicity

/-- Natural multiplicities growing as `m i = i` violate the weighted
reciprocal-square hypothesis. -/
theorem growing_multiplicity_weight_not_summable :
    ¬Summable (fun i : ℕ => (i : ℝ) / ((i : ℝ) + 1) ^ 2) := by
  intro h
  have hshift : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) / ((((n + 1 : ℕ) : ℝ) + 1) ^ 2))) := by
    simpa [Function.comp_def] using
      h.comp_injective Nat.succ_injective
  have hharmonic : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (hshift.mul_left 2)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    have hden : 0 < (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    rw [hcast] at hden ⊢
    rw [div_le_iff₀ hden]
    field_simp
    nlinarith
  have hshiftedP : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (1 : ℝ)) := by
    refine hharmonic.congr fun n => ?_
    rw [Real.rpow_one, abs_of_pos (by positivity)]
    norm_num [Nat.cast_add]
    ring
  have hforbidden := (Real.summable_one_div_nat_add_rpow 2 1).1 hshiftedP
  norm_num at hforbidden

#print axioms positive_fredholm_completion
#print axioms unit_spectrum_weight_hasSum
#print axioms unit_spectrum_product_one_multipliable
#print axioms unit_spectrum_product_zero
#print axioms growing_multiplicity_weight_not_summable

end

end D5.S3.Weil.Fredholm.PositiveFredholmProduct
