/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal canonical occupation coefficients for scalar lattice sewing. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.FactorialFockMetric
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

/-! Literal factorial-coordinate sewing and occupation coefficients
of the original lattice fields.

proof_shape: canonical_sewing_summable: content
admission_basis: escape-witness
escape_witness: The actual finite word-field recurrence preserves complementary
row and factorial column bounds for arbitrary descendant words and signed modes.
Their product gives an ungrouped occupation majorant, before any cancellation
or energy-fibre grouping. Every private estimate is consumed by this theorem.
The factorial pairing is used only for coordinate resolution, not BPZ invariance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalOccupationSewing

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open LatticeAllStateField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FieldNormalProduct
open scoped BigOperators VertexOperator

noncomputable section

abbrev Occ (D : LatticeData) := Index D →₀ ℕ

def level (D : LatticeData) (d : Occ D) : ℕ :=
  LatticePositiveEnergy.oscillatorEnergy d

def b (D : LatticeData) (d : Occ D) : Oscillator D :=
  MvPolynomial.monomial d (1 : ℂ)

/-- The factorial coordinate-resolution form; no invariant BPZ property is asserted. -/
def H (D : LatticeData) (p t : Oscillator D) : ℂ :=
  FactorialFockMetric.inner p t

def A (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (d : Occ D) : ℂ :=
  H D p (canonical D α (β + γ) u (r + (level D d : ℤ)) (b D d)) *
    (H D (b D d) (canonical D β γ v (s - (level D d : ℤ)) w) /
      (FactorialFockMetric.weight d : ℂ))

def sewnTerm (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) : ℂ :=
  q ^ level D d * A D α β γ u v w p r s d

/-- The original exponential's factorial-free occupation numerator. -/
def creationCoordinate (D : LatticeData) (α : Charge D) (d : Occ D) : ℂ :=
  d.prod fun x n => ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) ^ n

private theorem creation_partial (D : LatticeData) (α : Charge D) (x : Index D)
    (t : ℤ) :
    pderiv x (creationCoeff D α t) =
      ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) •
        creationCoeff D α (t - (x.2 + 1 : ℕ)) := by
  classical
  have hlin (n : ℕ) :
      pderiv x (∑ j : Fin D.rank, (α j : ℂ) • (X (j,n) : Oscillator D)) =
        if x.2 = n then (α x.1 : ℂ) • (1 : Oscillator D) else 0 := by
    rcases x with ⟨i,k⟩
    by_cases h : k = n
    · subst n
      simp [map_sum, Derivation.map_smul, pderiv_X, Pi.single_apply, Prod.mk.injEq,
        eq_comm]
    · simp [map_sum, Derivation.map_smul, pderiv_X, Prod.mk.injEq, h, Ne.symm h]
  have hlog : seriesDerivation D (pderiv x) (creationSeries D α) =
      PowerSeries.C (((α x.1 : ℂ) / (x.2 + 1 : ℂ)) • (1 : Oscillator D)) *
        PowerSeries.X ^ (x.2 + 1) := by
    apply PowerSeries.ext
    intro n
    rw [series_coeff]
    cases n with
    | zero => simp [creationSeries]
    | succ n =>
      simp only [creationSeries, PowerSeries.coeff_mk,
        dite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        Derivation.map_smul, hlin, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases hx : x.2 = n
      · rw [ite_eq_left hx]
        simp [hx, div_eq_mul_inv, smul_smul, mul_comm]
      · rw [ite_eq_right hx]
        simp [Ne.symm hx]
  have hnat (n : ℕ) : pderiv x (PowerSeries.coeff n (creationExponential D α)) =
      if x.2 + 1 ≤ n then
        ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) •
          PowerSeries.coeff (n - (x.2 + 1)) (creationExponential D α) else 0 := by
    have h := congrArg (PowerSeries.coeff n)
      (actual_exponential_derivation D (pderiv x) α)
    rw [series_coeff, hlog, ← mul_assoc, PowerSeries.coeff_mul_X_pow'] at h
    rw [h]
    split_ifs
    · rw [PowerSeries.coeff_mul_C, mul_smul_comm, mul_one]
    · rfl
  by_cases ht : t < 0
  · rw [creationCoeff, dite_eq_left ht, map_zero, creationCoeff,
      dite_eq_left (show t - (x.2 + 1 : ℕ) < 0 by omega), smul_zero]
  · rw [creationCoeff, dite_eq_right ht, hnat]
    by_cases hx : x.2 + 1 ≤ t.toNat
    · rw [ite_eq_left hx, creationCoeff, dite_eq_right (by omega),
        show (t - (x.2 + 1 : ℕ)).toNat = t.toNat - (x.2 + 1) by omega]
    · rw [ite_eq_right hx, creationCoeff, dite_eq_left (by omega), smul_zero]

set_option maxHeartbeats 2000000 in
-- The occupation induction repeatedly extracts coefficients of the actual derivation law.
/-- Exact occupation coefficient of the original creation exponential.
The factorial is supplied by the original polynomial derivations, not postulated. -/
private theorem creation_coefficient_factorial (D : LatticeData) (α : Charge D)
    (d : Occ D) :
    (creationCoeff D α (level D d)).coeff d * (FactorialFockMetric.weight d : ℂ) =
      creationCoordinate D α d := by
  classical
  have hstep (e : Occ D) (x : Index D) :
      (creationCoeff D α (level D (e + Finsupp.single x 1))).coeff
          (e + Finsupp.single x 1) * (FactorialFockMetric.weight (e + Finsupp.single x 1) : ℂ) =
        ((creationCoeff D α (level D e)).coeff e * (FactorialFockMetric.weight e : ℂ)) *
          ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) := by
    have hlev : level D (e + Finsupp.single x 1) = level D e + (x.2 + 1) := by
      simp [level, LatticePositiveEnergy.oscillatorEnergy, map_add, Finsupp.weight_single]
    have he := congrArg (fun p : Oscillator D => p.coeff e)
      (creation_partial D α x (level D (e + Finsupp.single x 1)))
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_smul] at he
    have hidx : (level D (e + Finsupp.single x 1) : ℤ) - (x.2 + 1 : ℕ) =
        (level D e : ℤ) := by rw [hlev]; omega
    rw [hidx] at he
    rw [FactorialFockMetric.weight_add_single]
    push_cast
    calc
      _ = ((creationCoeff D α (level D (e + Finsupp.single x 1))).coeff
          (e + Finsupp.single x 1) * (e x + 1 : ℂ)) *
            (FactorialFockMetric.weight e : ℂ) := by ring
      _ = _ := by rw [he]; ring
  have hprod (e : Occ D) (x : Index D) :
      creationCoordinate D α (e + Finsupp.single x 1) =
        creationCoordinate D α e * ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) := by
    unfold creationCoordinate
    rw [Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _)]
    simp
  have haux : ∀ n : ℕ, ∀ d : Occ D, level D d = n →
      (creationCoeff D α (level D d)).coeff d * (FactorialFockMetric.weight d : ℂ) =
        creationCoordinate D α d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd
      by_cases hz : d = 0
      · subst d
        have hc := LatticeSugawaraConformal.exponential_constant D α
        simp [level, LatticePositiveEnergy.oscillatorEnergy, creationCoeff, hc,
          creationCoordinate, FactorialFockMetric.weight]
      · obtain ⟨x, hx⟩ : ∃ x : Index D, d x ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (Finsupp.ext h)
        let e := d - Finsupp.single x 1
        have hed : e + Finsupp.single x 1 = d :=
          Finsupp.sub_add_single_one_cancel hx
        have hlev : level D e + (x.2 + 1) = level D d := by
          rw [← hed]
          simp [level, LatticePositiveEnergy.oscillatorEnergy, map_add, Finsupp.weight_single]
        have hi := ih (level D e) (by omega) e rfl
        rw [← hed, hstep, hi, hprod]
  exact haux (level D d) d rfl

private theorem creation_coefficient_norm (D : LatticeData) (α : Charge D)
    (d : Occ D) :
    ‖(creationCoeff D α (level D d)).coeff d‖ =
      d.prod (fun x n => (‖(α x.1 : ℂ)‖ / (x.2 + 1 : ℝ)) ^ n / (n.factorial : ℝ)) := by
  classical
  have hw : (FactorialFockMetric.weight d : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (FactorialFockMetric.weight_pos d))
  have hn (n : ℕ) : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Complex.norm_natCast (n + 1))
  have h := congrArg norm (creation_coefficient_factorial D α d)
  simp only [norm_mul, Complex.norm_natCast] at h
  calc
    _ = ‖creationCoordinate D α d‖ / (FactorialFockMetric.weight d : ℝ) :=
      (eq_div_iff hw).mpr h
    _ = _ := by
      simp [creationCoordinate, FactorialFockMetric.weight, Finsupp.prod,
        norm_prod, norm_pow, Finset.prod_div_distrib, hn]

/-- A radial estimate for every literal creation occupation, with no energy cutoff.
The arbitrary descendant field estimate needed for scalar sewing is separate. -/
private theorem creation_radial_bound (D : LatticeData) (α : Charge D)
    (M B ρ : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hα : ∀ i, ‖(α i : ℂ)‖ ≤ M) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d : Occ D) :
    ‖(creationCoeff D α (level D d)).coeff d‖ * B ^ d.degree * ρ ^ level D d ≤
      Real.exp ((D.rank : ℝ) * M * B / (1 - ρ)) := by
  classical
  have hpow : ρ ^ level D d = d.prod (fun x n => (ρ ^ (x.2 + 1)) ^ n) := by
    simp only [level, LatticePositiveEnergy.oscillatorEnergy, Finsupp.weight_apply,
      Finsupp.sum, Finsupp.prod, nsmul_eq_mul, ← pow_mul,
      Finset.prod_pow_eq_pow_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x hx => Nat.mul_comm _ _)
  have hdegree : B ^ d.degree = d.prod (fun _ n => B ^ n) := by
    simp [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  let f : Index D → ℝ := fun x =>
    ‖(α x.1 : ℂ)‖ / (x.2 + 1 : ℝ) * B * ρ ^ (x.2 + 1)
  have hf (x : Index D) : 0 ≤ f x := by dsimp [f]; positivity
  have hprod : ‖(creationCoeff D α (level D d)).coeff d‖ * B ^ d.degree * ρ ^ level D d ≤
      Real.exp (∑ x ∈ d.support, f x) := by
    rw [creation_coefficient_norm, hdegree, hpow]
    change ((∏ x ∈ d.support,
        (‖(α x.1 : ℂ)‖ / (x.2 + 1 : ℝ)) ^ d x / ((d x).factorial : ℝ)) *
        (∏ x ∈ d.support, B ^ d x)) *
      (∏ x ∈ d.support, (ρ ^ (x.2 + 1)) ^ d x) ≤ _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro x hx
      positivity
    · intro x hx
      calc
        _ = (f x) ^ d x / ((d x).factorial : ℝ) := by
          simp only [f, mul_pow]
          ring
        _ ≤ Real.exp (f x) := Real.pow_div_factorial_le_exp (f x) (hf x) (d x)
  have hgeo := summable_geometric_of_lt_one hρ0 hρ1
  have hMB : 0 ≤ M * B := mul_nonneg hM hB
  have hs : Summable (fun x : Index D => (M * B) * ρ ^ x.2) := by
    exact (summable_prod_of_nonneg
      (fun x : Index D => mul_nonneg hMB (pow_nonneg hρ0 _))).2
      ⟨fun _ => hgeo.mul_left (M * B), Summable.of_finite⟩
  have hdom (x : Index D) : f x ≤ (M * B) * ρ ^ x.2 := by
    have hd : (1 : ℝ) ≤ x.2 + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le x.2)
    have hdiv : ‖(α x.1 : ℂ)‖ / (x.2 + 1 : ℝ) ≤ M :=
      (div_le_self (norm_nonneg _) hd).trans (hα x.1)
    have hp : ρ ^ (x.2 + 1) ≤ ρ ^ x.2 :=
      pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hdiv hB) hp (pow_nonneg hρ0 _) hMB
  have hsum : (∑ x ∈ d.support, f x) ≤ (D.rank : ℝ) * M * B / (1 - ρ) := by
    calc
      _ ≤ ∑ x ∈ d.support, (M * B) * ρ ^ x.2 := Finset.sum_le_sum (fun x hx => hdom x)
      _ ≤ ∑' x : Index D, (M * B) * ρ ^ x.2 :=
        hs.sum_le_tsum d.support (fun x hx => mul_nonneg hMB (pow_nonneg hρ0 _))
      _ = _ := by
        rw [hs.tsum_prod]
        simp [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1,
          div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  exact hprod.trans (Real.exp_le_exp.mpr hsum)

/-- The all-occupation creation seed is absolutely summable on the open disk.
This is an internal seed estimate, not the all-descendant canonical sewing theorem. -/
private theorem creation_occupation_summable (D : LatticeData) (α : Charge D)
    (B : ℝ) (hB : 0 ≤ B) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => B ^ d.degree * ‖q ^ level D d *
      (creationCoeff D α (level D d)).coeff d‖) := by
  obtain ⟨ρ, hqρ, hρ1⟩ := exists_between hq
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg q) hqρ
  let M : ℝ := ∑ i : Fin D.rank, ‖(α i : ℂ)‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hα (i : Fin D.rank) : ‖(α i : ℂ)‖ ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (α j : ℂ)) (Finset.mem_univ i)
  have hR0 : 0 ≤ ‖q‖ / ρ := div_nonneg (norm_nonneg q) hρ0.le
  have hR1 : ‖q‖ / ρ < 1 := (div_lt_one hρ0).mpr hqρ
  have hs : Summable (fun d : Occ D => (‖q‖ / ρ) ^ level D d) := by
    have hh := summable_norm_signed_integer_occupations (Fin D.rank)
        (q := ((‖q‖ / ρ : ℝ) : ℂ)) (by simpa [abs_of_nonneg hR0, abs_of_pos hρ0] using hR1)
    simpa [signedIntegerMonomial, integerEnergy,
      level, LatticePositiveEnergy.oscillatorEnergy, abs_of_nonneg hR0, abs_of_pos hρ0] using hh
  let C := Real.exp ((D.rank : ℝ) * M * B / (1 - ρ))
  refine (hs.mul_left C).of_nonneg_of_le (fun d => mul_nonneg (pow_nonneg hB _) (norm_nonneg _)) ?_
  intro d
  have hb := creation_radial_bound D α M B ρ hM hB hα hρ0.le hρ1 d
  rw [norm_mul, norm_pow]
  have hr : 0 < ρ ^ level D d := pow_pos hρ0 _
  calc
    _ = (‖(creationCoeff D α (level D d)).coeff d‖ * B ^ d.degree * ρ ^ level D d) *
        (‖q‖ / ρ) ^ level D d := by
      rw [div_pow]
      field_simp
      <;> ring
    _ ≤ C * (‖q‖ / ρ) ^ level D d :=
      mul_le_mul_of_nonneg_right hb (pow_nonneg hR0 _)

private theorem creation_coefficient_norm_le (D : LatticeData) (α : Charge D)
    (t : ℤ) (d : Occ D) :
    ‖(creationCoeff D α t).coeff d‖ ≤
      ‖(creationCoeff D α (level D d)).coeff d‖ := by
  by_cases ht : t < 0
  · simp [creationCoeff, ht]
  · by_cases he : t = (level D d : ℤ)
    · rw [he]
    · have hn : Finsupp.weight (oscillatorWeight D) d ≠ t.toNat := by
        change level D d ≠ t.toNat
        intro h
        apply he
        rw [h, Int.toNat_of_nonneg (not_lt.mp ht)]
      rw [((actual_creation_coefficient_transport D α α).1 t).coeff_eq_zero d hn]
      simpa only [norm_zero] using norm_nonneg ((creationCoeff D α (level D d)).coeff d)

/-- Projection of the original recursively normal-ordered word field. -/
private def wordMap (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (m : ℤ) : Oscillator D →ₗ[ℂ] Oscillator D :=
  (Finsupp.lapply (α + β)).comp
    (((wordField D α ω)[[m]]).comp (Finsupp.lsingle β))

private def wordCoeff (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (m : ℤ) (e d : Occ D) : ℂ :=
  (wordMap D α β ω m (b D d)).coeff e

/-- Finite contraction with the original creation coefficients. -/
private def creationContract (D : LatticeData) (α : Charge D) (t : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.linearCombination (Oscillator D) (fun n : ℕ => creationCoeff D α (t + n))).comp
    (((Polynomial.toFinsuppIsoLinear (Oscillator D)).trans
      (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D))).toLinearMap)

private theorem creationContract_apply (D : LatticeData) (α : Charge D) (t : ℤ)
    (P : Polynomial (Oscillator D)) :
    creationContract D α t P = ∑ j ∈ P.support, P.coeff j * creationCoeff D α (t + j) := by
  rfl

private theorem creationContract_monomial (D : LatticeData) (α : Charge D) (t : ℤ)
    (n : ℕ) (a : Oscillator D) :
    creationContract D α t (Polynomial.monomial n a) = a * creationCoeff D α (t + n) := by
  simp [creationContract, Finsupp.linearCombination_apply]

private theorem creationContract_C_mul (D : LatticeData) (α : Charge D) (t : ℤ)
    (a : Oscillator D) (P : Polynomial (Oscillator D)) :
    creationContract D α t (Polynomial.C a * P) = a * creationContract D α t P := by
  rw [← Polynomial.smul_eq_C_mul]
  exact map_smul (creationContract D α t) a P

private theorem creationContract_shift (D : LatticeData) (α : Charge D) (t : ℤ)
    (n : ℕ) (P : Polynomial (Oscillator D)) :
    creationContract D α t (Polynomial.X ^ n * P) = creationContract D α (t + n) P := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [mul_add, map_add, hp, hq]
  | monomial j a =>
    rw [Polynomial.X_pow_mul_monomial, creationContract_monomial,
      creationContract_monomial]
    congr 2
    omega

private theorem wordMap_nil (D : LatticeData) (α β : Charge D)
    (m : ℤ) (p : Oscillator D) :
    wordMap D α β [] m p = epsilon D α β •
      creationContract D α (-m - 1 - bilinear D α β) (translatedPolynomial D α p) := by
  change (((actualField D α)[[m]]) (Finsupp.single β p)) (α + β) = _
  rw [actualField, VertexOperator.ncoeff_of_coeff,
    (actual_creation_coefficient_transport D α α).2.2.1]
  simp only [rawSingle, Finsupp.smul_apply, Finsupp.single_eq_same,
    creationContract_apply, smul_eq_mul]

/-- The actual input multiplication/translation recurrence, uniformly in signed mode. -/
private theorem wordMap_nil_X (D : LatticeData) (α β : Charge D)
    (m : ℤ) (x : Index D) (p : Oscillator D) :
    wordMap D α β [] m (X x * p) =
      X x * wordMap D α β [] m p -
        (bilinear D α (unitCharge D x.1) : ℂ) •
          wordMap D α β [] (m - (x.2 + 1 : ℕ)) p := by
  have ht : translatedPolynomial D α (X x * p) =
      translationVariable D α x.1 x.2 * translatedPolynomial D α p := by
    simp [translatedPolynomial]
  rw [wordMap_nil, ht, translationVariable, sub_mul, map_sub,
    creationContract_C_mul, mul_assoc, creationContract_C_mul, creationContract_shift,
    wordMap_nil, wordMap_nil]
  rw [show -m - 1 - bilinear D α β + (x.2 + 1 : ℕ) =
    -(m - (x.2 + 1 : ℕ)) - 1 - bilinear D α β by omega]
  simp [smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]

private theorem derivative_mode (D : LatticeData) (x : Index D) (m : ℤ) :
    (dividedDerivative x.2 (neutralField D x.1))[[m]] =
      ((Ring.choose (-m - 1 + x.2) x.2 : ℤ) : ℂ) •
        neutralMode D x.1 (m - x.2) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-m - 1 + x.2) x.2 •
    HVertexOperator.coeff (neutralField D x.1) (-m - 1 + x.2) v = _
  rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff]
  rw [show -(-m - 1 + x.2) - 1 = m - x.2 by omega]
  simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

private theorem neutral_component (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (v : Carrier D) (δ : Charge D) :
    (neutralMode D i m v) δ = neutralPolynomialMode D i δ m (v δ) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw]
  | single β p =>
    by_cases h : β = δ
    · subst β; simp
    · simp [h]

private theorem negative_derivative_component (D : LatticeData) (x : Index D)
    (j : ℕ) (v : Carrier D) (δ : Charge D) :
    (((dividedDerivative x.2 (neutralField D x.1))[[-(j : ℤ) - 1]]) v) δ =
      ((j + x.2).choose x.2 : ℂ) •
        (X (x.1, j + x.2) * v δ) := by
  rw [derivative_mode, LinearMap.smul_apply, Finsupp.smul_apply, neutral_component]
  rw [show -(-(j : ℤ) - 1) - 1 + x.2 = ((j + x.2 : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  have ht : (-(j : ℤ) - 1 - x.2) < 0 := by omega
  rw [neutralPolynomialMode, ite_eq_left ht]
  change ((j + x.2).choose x.2 : ℂ) •
    (X (x.1, (-(-(j : ℤ) - 1 - x.2) - 1).toNat) * v δ) = _
  rw [show (-(-(j : ℤ) - 1 - x.2) - 1).toNat = j + x.2 by omega]

private theorem derivative_single (D : LatticeData) (x : Index D)
    (j : ℕ) (β : Charge D) (p : Oscillator D) :
    ((dividedDerivative x.2 (neutralField D x.1))[[j]]) (Finsupp.single β p) =
      ((Ring.choose (-(j : ℤ) - 1 + x.2) x.2 : ℤ) : ℂ) •
        Finsupp.single β (neutralPolynomialMode D x.1 β ((j : ℤ) - x.2) p) := by
  rw [derivative_mode, LinearMap.smul_apply, neutralMode_single]

private theorem negative_coefficient_vanish (D : LatticeData) (x : Index D)
    (j : ℕ) (e : Occ D) (p : Oscillator D) (hj : level D e ≤ j) :
    (X (x.1, j + x.2) * p).coeff e = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  split_ifs with h
  · have he := Finsupp.le_weight_of_ne_zero'
      (w := fun y : Index D => y.2 + 1) (Finsupp.mem_support_iff.mp h)
    change j + x.2 + 1 ≤ level D e at he
    omega
  · rfl

private theorem positive_derivative_vanish (D : LatticeData) (x : Index D)
    (j : ℕ) (β : Charge D) (d : Occ D) (hj : x.2 + level D d < j) :
    ((dividedDerivative x.2 (neutralField D x.1))[[j]]) (Finsupp.single β (b D d)) = 0 := by
  rw [derivative_single]
  have hm : 0 < (j : ℤ) - x.2 := by omega
  have hderiv (i : Fin D.rank) :
      pderiv (i, ((j : ℤ) - x.2 - 1).toNat) (b D d) = 0 := by
    have hz : d (i, ((j : ℤ) - x.2 - 1).toNat) = 0 := by
      by_contra hn
      have he := Finsupp.le_weight_of_ne_zero'
        (w := fun y : Index D => y.2 + 1) hn
      change ((j : ℤ) - x.2 - 1).toNat + 1 ≤ level D d at he
      have ht := Int.toNat_of_nonneg (show 0 ≤ (j : ℤ) - x.2 - 1 by omega)
      omega
    rw [b, pderiv_monomial, hz]
    simp
  have hz : neutralPolynomialMode D x.1 β ((j : ℤ) - x.2) (b D d) = 0 := by
    rw [neutralPolynomialMode, ite_eq_right (not_lt.mpr hm.le), ite_eq_right (ne_of_gt hm)]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe,
      hderiv, smul_zero, Finset.sum_const_zero]
  rw [hz, Finsupp.single_zero, smul_zero]

/-- Both original normal-product branches, with exact finite ranges.
The first range is forced by the output occupation and the second by the input.
No field truncation or growth premise is introduced. -/
private theorem wordCoeff_cons_finite (D : LatticeData) (α β : Charge D)
    (x : Index D) (ω : List (Index D)) (m : ℤ) (e d : Occ D) :
    wordCoeff D α β (x :: ω) m e d =
      (∑ j ∈ Finset.range (level D e),
        ((j + x.2).choose x.2 : ℂ) *
          (X (x.1, j + x.2) * wordMap D α β ω (m + j) (b D d)).coeff e) +
      ∑ j ∈ Finset.range (x.2 + level D d + 1),
        ((Ring.choose (-(j : ℤ) - 1 + x.2) x.2 : ℤ) : ℂ) *
          (wordMap D α β ω (m - j - 1)
            (neutralPolynomialMode D x.1 β ((j : ℤ) - x.2) (b D d))).coeff e := by
  classical
  let left := dividedDerivative x.2 (neutralField D x.1)
  let right := wordField D α ω
  let v := Finsupp.single β (b D d)
  have hf₁ : Function.HasFiniteSupport
      (fun j : ℕ => (left[[-(j : ℤ) - 1]]) ((right[[m + j]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (right v)).order - m).toNat, ?_⟩
    intro j hj
    contrapose! hj
    have hz : (right[[m + j]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  have hf₂ : Function.HasFiniteSupport
      (fun j : ℕ => (right[[m - j - 1]]) ((left[[j]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (left v)).order - 1).toNat, ?_⟩
    intro j hj
    contrapose! hj
    have hz : (left[[j]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  let extract : Carrier D →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ e).comp (Finsupp.lapply (α + β))
  change extract (((wordField D α (x :: ω))[[m]]) v) = _
  rw [wordField, (normalMinusOne _ _).2, map_add,
    map_finsum extract hf₁, map_finsum extract hf₂]
  congr 1
  · have heq (j : ℕ) :
        extract ((left[[-(j : ℤ) - 1]]) ((right[[m + j]]) v)) =
          ((j + x.2).choose x.2 : ℂ) *
          (X (x.1, j + x.2) * wordMap D α β ω (m + j) (b D d)).coeff e := by
      change (((left[[-(j : ℤ) - 1]]) ((right[[m + j]]) v)) (α + β)).coeff e = _
      rw [negative_derivative_component]
      rfl
    simp_rw [heq]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hn
    have hj' : level D e ≤ j := by simpa using hn
    exact hj (by dsimp only; rw [negative_coefficient_vanish D x j e _ hj', mul_zero])
  · have heq (j : ℕ) :
        extract ((right[[m - j - 1]]) ((left[[j]]) v)) =
          ((Ring.choose (-(j : ℤ) - 1 + x.2) x.2 : ℤ) : ℂ) *
          (wordMap D α β ω (m - j - 1)
            (neutralPolynomialMode D x.1 β ((j : ℤ) - x.2) (b D d))).coeff e := by
      change (((right[[m - j - 1]]) ((left[[j]]) v)) (α + β)).coeff e = _
      rw [derivative_single, map_smul, Finsupp.smul_apply, MvPolynomial.coeff_smul]
      rfl
    calc
      _ = ∑ j ∈ Finset.range (x.2 + level D d + 1),
          extract ((right[[m - j - 1]]) ((left[[j]]) v)) := by
        apply finsum_eq_sum_of_support_subset
        intro j hj
        by_contra hn
        have hj' : x.2 + level D d < j := by simpa using hn
        exact hj (by dsimp only; simp only [left, v,
          positive_derivative_vanish D x j β d hj', map_zero])
      _ = _ := Finset.sum_congr rfl (fun j hj => heq j)

private theorem wordCoeff_nil_add_single (D : LatticeData) (α β : Charge D)
    (m : ℤ) (x : Index D) (e d : Occ D) :
    wordCoeff D α β [] m e (d + Finsupp.single x 1) =
      (if x ∈ e.support then
        wordCoeff D α β [] m (e - Finsupp.single x 1) d else 0) -
      (bilinear D α (unitCharge D x.1) : ℂ) *
        wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) e d := by
  classical
  have hb : b D (d + Finsupp.single x 1) = X x * b D d := by
    simp [b, X, monomial_mul_monomial, add_comm]
  simp only [wordCoeff, hb, wordMap_nil_X, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_X_mul', MvPolynomial.coeff_smul, smul_eq_mul]

/-- A creation-seed row bound in every signed mode and every output occupation. -/
private theorem creation_row_bound (D : LatticeData) (α : Charge D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℤ) (e : Occ D),
      ‖(creationCoeff D α t).coeff e‖ ≤ C * (2 : ℝ) ^ level D e := by
  classical
  let M : ℝ := ∑ i : Fin D.rank, ‖(α i : ℂ)‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hα (i : Fin D.rank) : ‖(α i : ℂ)‖ ≤ M :=
    Finset.single_le_sum (fun j _ => norm_nonneg (α j : ℂ)) (Finset.mem_univ i)
  let C := Real.exp ((D.rank : ℝ) * M / (1 - (1 / 2 : ℝ)))
  refine ⟨C, (Real.exp_pos _).le, ?_⟩
  intro t e
  have hr := creation_radial_bound D α M 1 (1/2) hM (by norm_num) hα
    (by norm_num) (by norm_num) e
  simp only [one_pow, mul_one] at hr
  have hid : (1 / 2 : ℝ) ^ level D e * 2 ^ level D e = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ ≤ ‖(creationCoeff D α (level D e)).coeff e‖ := creation_coefficient_norm_le D α t e
    _ = (‖(creationCoeff D α (level D e)).coeff e‖ * (1/2 : ℝ) ^ level D e) *
          2 ^ level D e := by rw [mul_assoc, hid, mul_one]
    _ ≤ C * 2 ^ level D e := mul_le_mul_of_nonneg_right hr (by positivity)

/-- Complementary row seed for the actual creation-and-translation field.
The input occupation is unrestricted, and the mode is arbitrary. -/
private theorem ground_row_bound (D : LatticeData) (α β : Charge D) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m e d‖ ≤
        C * (2 : ℝ) ^ level D e * L ^ d.degree := by
  classical
  obtain ⟨C, hC, hbase⟩ := creation_row_bound D α
  let T : Fin D.rank → ℝ := fun i => ‖(bilinear D α (unitCharge D i) : ℂ)‖
  let L : ℝ := 1 + ∑ i : Fin D.rank, T i
  have hL : 1 ≤ L := by
    dsimp [L, T]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hTx (x : Index D) : 1 + T x.1 ≤ L := by
    dsimp [L]
    simpa only [T, add_comm] using add_le_add_left (Finset.single_le_sum
      (fun i _ => norm_nonneg (bilinear D α (unitCharge D i) : ℂ))
      (Finset.mem_univ x.1)) 1
  have hphase : ‖epsilon D α β‖ = 1 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  have hzero (e : Occ D) (m : ℤ) :
      ‖wordCoeff D α β [] m e 0‖ ≤ C * 2 ^ level D e := by
    have hh : wordCoeff D α β [] m e 0 =
        epsilon D α β * (creationCoeff D α (-m - 1 - bilinear D α β)).coeff e := by
      have hc : creationContract D α (-m - 1 - bilinear D α β) 1 =
          creationCoeff D α (-m - 1 - bilinear D α β) := by
        simpa using creationContract_monomial D α (-m - 1 - bilinear D α β) 0 (1 : Oscillator D)
      simp [wordCoeff, b, wordMap_nil, translatedPolynomial, hc]
    rw [hh, norm_mul, hphase, one_mul]
    exact hbase _ _
  refine ⟨C, L, hC, hL, ?_⟩
  have haux : ∀ n : ℕ, ∀ d : Occ D, d.degree = n → ∀ (e : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m e d‖ ≤ C * 2 ^ level D e * L ^ d.degree := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd e m
      by_cases hz : d = 0
      · subst d
        simpa using hzero e m
      · obtain ⟨x, hx⟩ : ∃ x : Index D, d x ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (Finsupp.ext h)
        let d' := d - Finsupp.single x 1
        have hadd : d' + Finsupp.single x 1 = d := Finsupp.sub_add_single_one_cancel hx
        have hdeg : d'.degree + 1 = d.degree := by
          rw [← hadd, map_add, Finsupp.degree_single]
        have hi (e' : Occ D) (m' : ℤ) := ih d'.degree (by omega) d' rfl e' m'
        let B : ℝ := C * 2 ^ level D e * L ^ d'.degree
        have hB : 0 ≤ B := by dsimp [B]; positivity
        have hleft : ‖if x ∈ e.support then
            wordCoeff D α β [] m (e - Finsupp.single x 1) d' else 0‖ ≤ B := by
          split_ifs with he
          · have hlev := Finsupp.weight_sub_single_add (w := fun y : Index D => y.2 + 1)
              (Finsupp.mem_support_iff.mp he)
            change level D (e - Finsupp.single x 1) + (x.2 + 1) = level D e at hlev
            have hp : (2 : ℝ) ^ level D (e - Finsupp.single x 1) ≤ 2 ^ level D e :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            exact (hi _ m).trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp hC) (pow_nonneg (by linarith) _))
          · simpa only [norm_zero] using hB
        rw [← hadd, wordCoeff_nil_add_single]
        calc
          _ ≤ ‖if x ∈ e.support then
              wordCoeff D α β [] m (e - Finsupp.single x 1) d' else 0‖ +
              ‖(bilinear D α (unitCharge D x.1) : ℂ) *
                wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) e d'‖ := norm_sub_le _ _
          _ ≤ B + T x.1 * B := by
            rw [norm_mul]
            exact add_le_add hleft (mul_le_mul_of_nonneg_left (hi e _) (norm_nonneg _))
          _ = (1 + T x.1) * B := by ring
          _ ≤ L * B := mul_le_mul_of_nonneg_right (hTx x) hB
          _ = C * 2 ^ level D e * L ^ (d' + Finsupp.single x 1).degree := by
            rw [map_add, Finsupp.degree_single, pow_succ]
            dsimp [B]
            ring
          _ ≤ _ := le_rfl
        all_goals exact le_rfl
  exact fun e d m => haux d.degree d rfl e m

private theorem signed_derivative_choose (j k : ℕ) :
    ((Ring.choose (-(j : ℤ) - 1 + k) k : ℤ) : ℂ) =
      (-1 : ℂ) ^ k * (j.choose k : ℂ) := by
  rw [show -(j : ℤ) - 1 + k = -((j : ℤ) + 1 - k) by ring,
    Ring.choose_neg]
  rw [show (j : ℤ) + 1 - k + k - 1 = (j : ℤ) by ring, Ring.choose_natCast]
  change (((Int.negOnePow (k : ℤ) : ℤ) * (j.choose k : ℤ) : ℤ) : ℂ) = _
  rw [Int.coe_negOnePow_natCast]
  push_cast
  rfl

/-- Every positive branch is a zero mode or lowers one actual input occupation.
The gap below the derivative order is zero, including its apparent negative modes. -/
private theorem wordMap_neutral_coefficient (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (i : Fin D.rank) (k j : ℕ) (m : ℤ) (e d : Occ D) :
    ((Ring.choose (-(j : ℤ) - 1 + k) k : ℤ) : ℂ) *
      (wordMap D α β ω m
        (neutralPolynomialMode D i β ((j : ℤ) - k) (b D d))).coeff e =
    (-1 : ℂ) ^ k * (j.choose k : ℂ) *
      (if j < k then 0 else if j = k then
        (bilinear D (unitCharge D i) β : ℂ) * wordCoeff D α β ω m e d
      else ((j : ℤ) - k : ℂ) *
        ∑ a : Fin D.rank, (D.G i a : ℂ) * (d (a, j - k - 1) : ℂ) *
          wordCoeff D α β ω m e (d - Finsupp.single (a, j - k - 1) 1)) := by
  classical
  rw [signed_derivative_choose]
  by_cases hlt : j < k
  · simp [hlt, Nat.choose_eq_zero_of_lt hlt]
  · rw [ite_eq_right hlt]
    by_cases heq : j = k
    · subst j
      simp [neutralPolynomialMode, wordCoeff, map_smul, MvPolynomial.coeff_smul]
    · rw [ite_eq_right heq]
      have hm : 0 < (j : ℤ) - k := by omega
      rw [neutralPolynomialMode, ite_eq_right (not_lt.mpr hm.le), ite_eq_right (ne_of_gt hm)]
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe,
        map_smul, map_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_sum,
        smul_eq_mul]
      congr 1
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hd : pderiv (a, ((j : ℤ) - k - 1).toNat) (b D d) =
          (d (a, j - k - 1) : ℂ) • b D (d - Finsupp.single (a, j - k - 1) 1) := by
        rw [show ((j : ℤ) - k - 1).toNat = j - k - 1 by omega]
        simp [b, pderiv_monomial, smul_monomial]
      rw [hd, map_smul, MvPolynomial.coeff_smul]
      simp only [wordCoeff, Int.cast_sub, Int.cast_natCast]
      ring

/-- A finite recurrence solely in literal word-field matrix coefficients.
All colours, both normal-product branches, and every signed mode are retained. -/
private theorem wordCoeff_cons (D : LatticeData) (α β : Charge D)
    (x : Index D) (ω : List (Index D)) (m : ℤ) (e d : Occ D) :
    wordCoeff D α β (x :: ω) m e d =
      (∑ j ∈ Finset.range (level D e),
        ((j + x.2).choose x.2 : ℂ) *
          if (x.1, j + x.2) ∈ e.support then
            wordCoeff D α β ω (m + j) (e - Finsupp.single (x.1, j + x.2) 1) d
          else 0) +
      ∑ j ∈ Finset.range (x.2 + level D d + 1),
        (-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
          (if j < x.2 then 0 else if j = x.2 then
            (bilinear D (unitCharge D x.1) β : ℂ) *
              wordCoeff D α β ω (m - j - 1) e d
          else ((j : ℤ) - x.2 : ℂ) *
            ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (d (a, j - x.2 - 1) : ℂ) *
              wordCoeff D α β ω (m - j - 1) e
                (d - Finsupp.single (a, j - x.2 - 1) 1)) := by
  classical
  rw [wordCoeff_cons_finite]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [MvPolynomial.coeff_X_mul']
    rfl
  · apply Finset.sum_congr rfl
    intro j hj
    exact wordMap_neutral_coefficient D α β ω x.1 x.2 j (m - j - 1) e d

private theorem occupation_sub_bounds (D : LatticeData) (d : Occ D) (x : Index D) :
    level D (d - Finsupp.single x 1) ≤ level D d ∧
      (d - Finsupp.single x 1).degree ≤ d.degree := by
  classical
  by_cases hx : d x = 0
  · have heq : d - Finsupp.single x 1 = d := by
      ext y
      by_cases hy : y = x
      · subst y; simp [Finsupp.sub_apply, hx]
      · simp [Finsupp.sub_apply, Finsupp.single_apply, hy]
    rw [heq]
    exact ⟨le_rfl, le_rfl⟩
  · have hh := Finsupp.sub_add_single_one_cancel hx
    have hl : level D (d - Finsupp.single x 1) + (x.2 + 1) = level D d := by
      simpa [level, LatticePositiveEnergy.oscillatorEnergy, map_add,
        Finsupp.weight_single] using congrArg (level D) hh
    have hd : (d - Finsupp.single x 1).degree + 1 = d.degree := by
      simpa [map_add, Finsupp.degree_single] using congrArg Finsupp.degree hh
    omega

private def rowWeight (D : LatticeData) (L : ℝ) (K : ℕ) (d : Occ D) : ℝ :=
  (1 + (level D d : ℝ)) ^ K * L ^ d.degree

private theorem rowWeight_nonneg (D : LatticeData) (L : ℝ) (hL : 1 ≤ L)
    (K : ℕ) (d : Occ D) : 0 ≤ rowWeight D L K d := by
  dsimp [rowWeight]
  positivity

private theorem rowWeight_sub_le (D : LatticeData) (L : ℝ) (hL : 1 ≤ L)
    (K : ℕ) (d : Occ D) (x : Index D) :
    rowWeight D L K (d - Finsupp.single x 1) ≤ rowWeight D L K d := by
  have hb := occupation_sub_bounds D d x
  dsimp [rowWeight]
  apply mul_le_mul
  · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hb.1 1) K
  · exact pow_le_pow_right₀ hL hb.2
  · positivity
  · positivity

private theorem rowWeight_grow (D : LatticeData) (L : ℝ) (hL : 1 ≤ L)
    (K t : ℕ) (d : Occ D) : rowWeight D L K d ≤ rowWeight D L (K + t) d := by
  dsimp [rowWeight]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by have hn := Nat.cast_nonneg (α := ℝ) (level D d); linarith) (Nat.le_add_right _ _))
    (pow_nonneg (by linarith) _)

/-- One actual normal-product insertion preserves the polynomial row envelope. -/
private theorem word_row_step (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (x : Index D) (L : ℝ) (hL : 1 ≤ L) (K : ℕ)
    (C : Occ D → ℝ) (hC : ∀ e, 0 ≤ C e)
    (hrow : ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β ω m e d‖ ≤ C e * rowWeight D L K d) (e : Occ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D α β (x :: ω) m e d‖ ≤
        B * rowWeight D L (K + (x.2 + 3)) d := by
  classical
  let Z : ℝ := ‖(bilinear D (unitCharge D x.1) β : ℂ)‖
  let G : ℝ := ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖
  let P : ℝ := (x.2 + 1 : ℝ) ^ x.2
  let F : ℝ := ∑ j ∈ Finset.range (level D e),
    ((j + x.2).choose x.2 : ℝ) *
      if (x.1, j + x.2) ∈ e.support then C (e - Finsupp.single (x.1, j + x.2) 1) else 0
  have hZ : 0 ≤ Z := norm_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs
    · exact hC _
    · exact le_rfl
  have hCe : 0 ≤ C e := hC e
  refine ⟨F + (x.2 + 1 : ℝ) * P * (Z + G) * C e, by positivity, ?_⟩
  intro d m
  let N : ℝ := 1 + (level D d : ℝ)
  have hN : 1 ≤ N := by dsimp [N]; have hn := Nat.cast_nonneg (α := ℝ) (level D d); linarith
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hW := rowWeight_nonneg D L hL K d
  have hb (a : Fin D.rank) (n : ℕ) (m' : ℤ) :
      ‖wordCoeff D α β ω m' e (d - Finsupp.single (a,n) 1)‖ ≤
        C e * rowWeight D L K d :=
    (hrow e _ m').trans (mul_le_mul_of_nonneg_left (rowWeight_sub_le D L hL K d (a,n)) (hC e))
  have hchoose (j : ℕ) (hj : j < x.2 + level D d + 1) :
      (j.choose x.2 : ℝ) ≤ P * N ^ x.2 := by
    have hjN : (j : ℝ) ≤ (x.2 + 1 : ℝ) * N := by
      have hj' : (j : ℝ) ≤ (x.2 : ℝ) + level D d := by exact_mod_cast (show j ≤ x.2 + level D d by omega)
      dsimp [N]
      nlinarith [Nat.cast_nonneg (α := ℝ) (level D d), Nat.cast_nonneg (α := ℝ) x.2]
    calc
      _ ≤ (j : ℝ) ^ x.2 := by exact_mod_cast Nat.choose_le_pow j x.2
      _ ≤ ((x.2 + 1 : ℝ) * N) ^ x.2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hjN x.2
      _ = _ := mul_pow _ _ _
  have hpos (j : ℕ) (hj : j < x.2 + level D d + 1) :
      ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
        (if j < x.2 then 0 else if j = x.2 then
          (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) e d
        else ((j : ℤ) - x.2 : ℂ) *
          ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (d (a, j - x.2 - 1) : ℂ) *
            wordCoeff D α β ω (m - j - 1) e (d - Finsupp.single (a, j - x.2 - 1) 1))‖ ≤
      P * (Z + G) * N ^ (x.2 + 2) * C e * rowWeight D L K d := by
    have hinner :
        ‖if j < x.2 then 0 else if j = x.2 then
          (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) e d
        else ((j : ℤ) - x.2 : ℂ) *
          ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (d (a, j - x.2 - 1) : ℂ) *
            wordCoeff D α β ω (m - j - 1) e (d - Finsupp.single (a, j - x.2 - 1) 1)‖ ≤
          (Z + G) * N ^ 2 * (C e * rowWeight D L K d) := by
      split_ifs with hlt heq
      · simp only [norm_zero]; positivity
      · rw [norm_mul]
        have hsq : 1 ≤ N ^ 2 := one_le_pow₀ hN
        calc
          _ ≤ Z * (C e * rowWeight D L K d) := mul_le_mul_of_nonneg_left (hrow e d _) hZ
          _ ≤ (Z + G) * N ^ 2 * (C e * rowWeight D L K d) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hCe hW)
            exact (le_add_of_nonneg_right hG).trans
              (le_mul_of_one_le_right (add_nonneg hZ hG) hsq)
      · have hm : 0 ≤ (j : ℤ) - x.2 := by omega
        have hjN : ‖((j : ℤ) - x.2 : ℂ)‖ ≤ N := by
          simp only [Int.cast_natCast]
          rw [← Nat.cast_sub (show x.2 ≤ j by omega), Complex.norm_natCast]
          dsimp [N]
          exact_mod_cast (show j - x.2 ≤ 1 + level D d by omega)
        have hdN (a : Fin D.rank) : (d (a, j - x.2 - 1) : ℝ) ≤ N := by
          have hh := Finsupp.le_weight (w := fun y : Index D => y.2 + 1)
            (s := (a, j - x.2 - 1)) (by omega) d
          change d (a, j - x.2 - 1) ≤ level D d at hh
          dsimp [N]
          exact_mod_cast (hh.trans (Nat.le_add_left _ _))
        rw [norm_mul]
        calc
          _ ≤ N * ∑ a : Fin D.rank,
              ‖(D.G x.1 a : ℂ)‖ * (d (a, j - x.2 - 1) : ℝ) *
                ‖wordCoeff D α β ω (m - j - 1) e (d - Finsupp.single (a, j - x.2 - 1) 1)‖ := by
            gcongr
            exact (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
          _ ≤ N * ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖ * N *
              (C e * rowWeight D L K d) := by
            gcongr with a
            · exact hdN a
            · exact hb a _ _
          _ = G * N ^ 2 * (C e * rowWeight D L K d) := by
            simp only [G, ← Finset.sum_mul]
            ring
          _ ≤ (Z + G) * N ^ 2 * (C e * rowWeight D L K d) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hZ) (pow_nonneg hN0 _))
              (mul_nonneg hCe hW)
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    calc
      _ ≤ (P * N ^ x.2) * ((Z + G) * N ^ 2 * (C e * rowWeight D L K d)) := by
        exact mul_le_mul (hchoose j hj) hinner (norm_nonneg _) (mul_nonneg hP (pow_nonneg hN0 _))
      _ = _ := by rw [pow_add]; ring
  rw [wordCoeff_cons]
  calc
    _ ≤ (∑ j ∈ Finset.range (level D e),
        ‖((j + x.2).choose x.2 : ℂ) *
          if (x.1, j + x.2) ∈ e.support then
            wordCoeff D α β ω (m + j) (e - Finsupp.single (x.1, j + x.2) 1) d else 0‖) +
      ∑ j ∈ Finset.range (x.2 + level D d + 1),
        ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
          (if j < x.2 then 0 else if j = x.2 then
            (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) e d
          else ((j : ℤ) - x.2 : ℂ) *
            ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (d (a, j - x.2 - 1) : ℂ) *
              wordCoeff D α β ω (m - j - 1) e (d - Finsupp.single (a, j - x.2 - 1) 1))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ F * rowWeight D L K d +
        (x.2 + level D d + 1 : ℕ) * (P * (Z + G) * N ^ (x.2 + 2) * C e * rowWeight D L K d) := by
      apply add_le_add
      · rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Complex.norm_natCast]
        split_ifs with he
        · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (hrow _ _ _) (Nat.cast_nonneg ((j + x.2).choose x.2) : (0 : ℝ) ≤ _)
        · simp
      · exact (Finset.sum_le_sum (fun j hj => hpos j (Finset.mem_range.mp hj))).trans (by simp)
    _ ≤ F * rowWeight D L (K + (x.2 + 3)) d +
        ((x.2 + 1 : ℝ) * N) * (P * (Z + G) * N ^ (x.2 + 2) * C e * rowWeight D L K d) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (rowWeight_grow D L hL K (x.2 + 3) d) hF
      · gcongr
        dsimp [N]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) (level D d), Nat.cast_nonneg (α := ℝ) x.2]
    _ = _ := by
      dsimp [rowWeight, N]
      rw [pow_add, pow_succ (1 + (level D d : ℝ)) (x.2 + 2)]
      ring

/-- Every actual descendant word has a row envelope uniform in all signed modes. -/
private theorem word_row_bound (D : LatticeData) (α β : Charge D) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ω : List (Index D), ∃ K : ℕ, ∀ e : Occ D,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Occ D) (m : ℤ),
        ‖wordCoeff D α β ω m e d‖ ≤ C * rowWeight D L K d := by
  classical
  obtain ⟨C₀, L, hC₀, hL, hbase⟩ := ground_row_bound D α β
  refine ⟨L, hL, ?_⟩
  intro ω
  induction ω with
  | nil =>
    refine ⟨0, fun e => ⟨C₀ * 2 ^ level D e, by positivity, ?_⟩⟩
    intro d m
    simpa [rowWeight, mul_assoc] using hbase e d m
  | cons x ω ih =>
    obtain ⟨K, hi⟩ := ih
    choose C hC hb using hi
    exact ⟨K + (x.2 + 3), fun e => word_row_step D α β ω x L hL K C hC hb e⟩

/-- The factorial occupation envelope for the complementary column estimate. -/
private def factorialEnvelope (D : LatticeData) (B : ℝ) (d : Occ D) : ℝ :=
  d.prod (fun x n => (B / (x.2 + 1 : ℝ)) ^ n) /
    (FactorialFockMetric.weight d : ℝ)

private theorem factorialEnvelope_nonneg (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (d : Occ D) : 0 ≤ factorialEnvelope D B d := by
  unfold factorialEnvelope
  apply div_nonneg
  · exact Finset.prod_nonneg (fun _ _ => pow_nonneg (div_nonneg hB (by positivity)) _)
  · exact Nat.cast_nonneg _

private theorem factorialEnvelope_add_single (D : LatticeData) (B : ℝ)
    (d : Occ D) (x : Index D) :
    factorialEnvelope D B (d + Finsupp.single x 1) * (d x + 1 : ℝ) =
      factorialEnvelope D B d * (B / (x.2 + 1 : ℝ)) := by
  classical
  have hw : (FactorialFockMetric.weight d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (FactorialFockMetric.weight_pos d)
  have hn : (d x + 1 : ℝ) ≠ 0 := by positivity
  unfold factorialEnvelope
  rw [Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _),
    FactorialFockMetric.weight_add_single]
  rw [Finsupp.prod_single_index (by simp)]
  simp only [pow_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem factorialEnvelope_sub_le (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (d : Occ D) (x : Index D) :
    factorialEnvelope D B (d - Finsupp.single x 1) ≤
      (1 + (level D d : ℝ)) * factorialEnvelope D B d := by
  classical
  have henv := factorialEnvelope_nonneg D B (by linarith) d
  by_cases hx : d x = 0
  · have heq : d - Finsupp.single x 1 = d := by
      ext y
      by_cases hy : y = x
      · subst y; simp [hx]
      · simp [hy]
    rw [heq]
    exact le_mul_of_one_le_left henv (by have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith)
  · let a := d - Finsupp.single x 1
    have hadd : a + Finsupp.single x 1 = d := Finsupp.sub_add_single_one_cancel hx
    have hd : a x + 1 = d x := by simpa using congrArg (fun c : Occ D => c x) hadd
    have hh := factorialEnvelope_add_single D B a x
    rw [hadd, show (a x + 1 : ℝ) = (d x : ℝ) by exact_mod_cast hd] at hh
    have hn : (x.2 + 1 : ℝ) ≠ 0 := by positivity
    have hrel : factorialEnvelope D B a * B =
        factorialEnvelope D B d * (d x : ℝ) * (x.2 + 1 : ℝ) := by
      have ht := congrArg (fun r : ℝ => r * (x.2 + 1 : ℝ)) hh
      field_simp at ht
      linarith
    have hlev : (d x : ℝ) * (x.2 + 1 : ℝ) ≤ (level D d : ℝ) := by
      have hs := Finset.single_le_sum (s := d.support)
        (f := fun y : Index D => d y * (y.2 + 1))
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)
      change d x * (x.2 + 1) ≤ level D d at hs
      exact_mod_cast hs
    calc
      _ ≤ factorialEnvelope D B a * B :=
        le_mul_of_one_le_right (factorialEnvelope_nonneg D B (by linarith) a) hB
      _ = _ := hrel
      _ ≤ (1 + (level D d : ℝ)) * factorialEnvelope D B d := by
        nlinarith

private theorem creation_factorialEnvelope (D : LatticeData) (α : Charge D)
    (B : ℝ) (hB : 0 ≤ B) (hα : ∀ i, ‖(α i : ℂ)‖ ≤ B) (t : ℤ) (d : Occ D) :
    ‖(creationCoeff D α t).coeff d‖ ≤ factorialEnvelope D B d := by
  classical
  apply (creation_coefficient_norm_le D α t d).trans
  rw [creation_coefficient_norm]
  unfold factorialEnvelope FactorialFockMetric.weight
  simp only [Finsupp.prod, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod₀
  · intro x hx; positivity
  · intro x hx
    gcongr
    exact hα x.1

/-- The actual translated field has the complementary factorial column envelope. -/
private theorem ground_column_bound (D : LatticeData) (α β : Charge D) :
    ∃ B L : ℝ, 1 ≤ B ∧ 1 ≤ L ∧ ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m d e‖ ≤
        L ^ e.degree * (1 + (level D d : ℝ)) ^ e.degree * factorialEnvelope D B d := by
  classical
  let B : ℝ := 1 + ∑ i : Fin D.rank, ‖(α i : ℂ)‖
  have hB : 1 ≤ B := by
    dsimp [B]
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun (i : Fin D.rank) _ => norm_nonneg (α i : ℂ))
    linarith
  have hα (i : Fin D.rank) : ‖(α i : ℂ)‖ ≤ B := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ => norm_nonneg (α j : ℂ)) (Finset.mem_univ i)
    dsimp [B]
    linarith
  let T : Fin D.rank → ℝ := fun i => ‖(bilinear D α (unitCharge D i) : ℂ)‖
  let L : ℝ := 1 + ∑ i : Fin D.rank, T i
  have hL : 1 ≤ L := by
    dsimp [L, T]
    have hh := Finset.sum_nonneg (s := Finset.univ)
      (fun (i : Fin D.rank) _ => norm_nonneg (bilinear D α (unitCharge D i) : ℂ))
    linarith
  have hTx (x : Index D) : 1 + T x.1 ≤ L := by
    have hh := Finset.single_le_sum (fun (i : Fin D.rank) _ =>
      norm_nonneg (bilinear D α (unitCharge D i) : ℂ)) (Finset.mem_univ x.1)
    dsimp [L, T]
    linarith
  have hphase : ‖epsilon D α β‖ = 1 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  have hzero (d : Occ D) (m : ℤ) :
      ‖wordCoeff D α β [] m d 0‖ ≤ factorialEnvelope D B d := by
    have hc : creationContract D α (-m - 1 - bilinear D α β) 1 =
        creationCoeff D α (-m - 1 - bilinear D α β) := by
      simpa using creationContract_monomial D α (-m - 1 - bilinear D α β) 0 (1 : Oscillator D)
    have hh : wordCoeff D α β [] m d 0 =
        epsilon D α β * (creationCoeff D α (-m - 1 - bilinear D α β)).coeff d := by
      simp [wordCoeff, b, wordMap_nil, translatedPolynomial, hc]
    rw [hh, norm_mul, hphase, one_mul]
    exact creation_factorialEnvelope D α B (by linarith) hα _ d
  refine ⟨B, L, hB, hL, ?_⟩
  have haux : ∀ n : ℕ, ∀ e : Occ D, e.degree = n → ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m d e‖ ≤
        L ^ e.degree * (1 + (level D d : ℝ)) ^ e.degree * factorialEnvelope D B d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he d m
      by_cases hz : e = 0
      · subst e
        simpa using hzero d m
      · obtain ⟨x, hx⟩ : ∃ x : Index D, e x ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (Finsupp.ext h)
        let e' := e - Finsupp.single x 1
        have hadd : e' + Finsupp.single x 1 = e := Finsupp.sub_add_single_one_cancel hx
        have hdeg : e'.degree + 1 = e.degree := by
          rw [← hadd, map_add, Finsupp.degree_single]
        have hi (d' : Occ D) (m' : ℤ) := ih e'.degree (by omega) e' rfl d' m'
        let N : ℝ := 1 + (level D d : ℝ)
        let V : ℝ := L ^ e'.degree * N ^ (e'.degree + 1) * factorialEnvelope D B d
        have hN : 1 ≤ N := by dsimp [N]; have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith
        have henv := factorialEnvelope_nonneg D B (by linarith) d
        have hV : 0 ≤ V := by dsimp [V]; positivity
        have hleft : ‖if x ∈ d.support then
            wordCoeff D α β [] m (d - Finsupp.single x 1) e' else 0‖ ≤ V := by
          split_ifs with hd
          · have henv' := factorialEnvelope_nonneg D B (by linarith)
              (d - Finsupp.single x 1)
            calc
              _ ≤ L ^ e'.degree * (1 + (level D (d - Finsupp.single x 1) : ℝ)) ^ e'.degree *
                  factorialEnvelope D B (d - Finsupp.single x 1) := hi _ _
              _ ≤ L ^ e'.degree * N ^ e'.degree * (N * factorialEnvelope D B d) := by
                gcongr
                · dsimp [N]; exact_mod_cast Nat.add_le_add_left (occupation_sub_bounds D d x).1 1
                · exact factorialEnvelope_sub_le D B hB d x
              _ = V := by dsimp [V]; rw [pow_succ]; ring
          · simpa only [norm_zero] using hV
        have hright : ‖wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) d e'‖ ≤ V := by
          exact (hi d _).trans (by dsimp [V]; gcongr; omega)
        rw [← hadd, wordCoeff_nil_add_single]
        calc
          _ ≤ ‖if x ∈ d.support then
              wordCoeff D α β [] m (d - Finsupp.single x 1) e' else 0‖ +
              ‖(bilinear D α (unitCharge D x.1) : ℂ) *
                wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) d e'‖ := norm_sub_le _ _
          _ ≤ V + T x.1 * V := by
            rw [norm_mul]
            exact add_le_add hleft (mul_le_mul_of_nonneg_left hright (norm_nonneg _))
          _ = (1 + T x.1) * V := by ring
          _ ≤ L * V := mul_le_mul_of_nonneg_right (hTx x) hV
          _ = L ^ (e' + Finsupp.single x 1).degree *
              (1 + (level D d : ℝ)) ^ (e' + Finsupp.single x 1).degree * factorialEnvelope D B d := by
            rw [map_add, Finsupp.degree_single, pow_succ L]
            dsimp [V, N]
            ring
          _ ≤ _ := le_rfl
        all_goals exact le_rfl
  exact fun e d m => haux e.degree e rfl d m

private def columnWeight (D : LatticeData) (B : ℝ) (K : ℕ) (d : Occ D) : ℝ :=
  (1 + (level D d : ℝ)) ^ K * factorialEnvelope D B d

private theorem columnWeight_nonneg (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K : ℕ) (d : Occ D) : 0 ≤ columnWeight D B K d :=
  mul_nonneg (by positivity) (factorialEnvelope_nonneg D B (by linarith) d)

private theorem columnWeight_grow (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K J : ℕ) (hK : K ≤ J) (d : Occ D) :
    columnWeight D B K d ≤ columnWeight D B J d := by
  apply mul_le_mul_of_nonneg_right _ (factorialEnvelope_nonneg D B (by linarith) d)
  exact pow_le_pow_right₀ (by have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith) hK

private theorem columnWeight_sub_le (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K : ℕ) (d : Occ D) (x : Index D) :
    columnWeight D B K (d - Finsupp.single x 1) ≤
      (1 + (level D d : ℝ)) * columnWeight D B K d := by
  have henv := factorialEnvelope_nonneg D B (by linarith) (d - Finsupp.single x 1)
  have henv' := factorialEnvelope_nonneg D B (by linarith) d
  dsimp [columnWeight]
  calc
    _ ≤ (1 + (level D d : ℝ)) ^ K *
        ((1 + (level D d : ℝ)) * factorialEnvelope D B d) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_left (occupation_sub_bounds D d x).1 1) K
      · exact factorialEnvelope_sub_le D B hB d x
      · exact henv
      · positivity
    _ = _ := by ring

/-- One actual normal-product insertion preserves the factorial column envelope. -/
private theorem word_column_step (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (x : Index D) (B : ℝ) (hB : 1 ≤ B) (K : ℕ)
    (C : Occ D → ℝ) (hC : ∀ e, 0 ≤ C e)
    (hcol : ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β ω m d e‖ ≤ C e * columnWeight D B (K + e.degree) d) (e : Occ D) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D α β (x :: ω) m d e‖ ≤
        S * columnWeight D B ((K + (x.2 + 2)) + e.degree) d := by
  classical
  let Z : ℝ := ‖(bilinear D (unitCharge D x.1) β : ℂ)‖
  let T : ℕ → ℝ := fun j => (j.choose x.2 : ℝ) *
    (if j < x.2 then 0 else if j = x.2 then Z * C e
    else ‖((j : ℤ) - x.2 : ℂ)‖ *
      ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
        C (e - Finsupp.single (a, j - x.2 - 1) 1))
  let S : ℝ := ∑ j ∈ Finset.range (x.2 + level D e + 1), T j
  have hCe := hC e
  have hT (j : ℕ) : 0 ≤ T j := by
    dsimp [T]
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (norm_nonneg _) hCe
    · apply mul_nonneg (norm_nonneg _)
      exact Finset.sum_nonneg (fun a ha =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (hC _))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj => hT j)
  refine ⟨C e + S, add_nonneg hCe hS, ?_⟩
  intro d m
  let N : ℝ := 1 + (level D d : ℝ)
  let W : ℝ := columnWeight D B (K + e.degree) d
  have hW : 0 ≤ W := columnWeight_nonneg D B hB _ d
  have hN : 1 ≤ N := by dsimp [N]; have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith
  have hshift (a : Fin D.rank) (n : ℕ) (m' : ℤ) :
      ‖wordCoeff D α β ω m' d (e - Finsupp.single (a,n) 1)‖ ≤
        C (e - Finsupp.single (a,n) 1) * W :=
    (hcol _ d m').trans (mul_le_mul_of_nonneg_left
      (columnWeight_grow D B hB _ _ (Nat.add_le_add_left (occupation_sub_bounds D e (a,n)).2 K) d)
      (hC _))
  have hpos (j : ℕ) :
      ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
        (if j < x.2 then 0 else if j = x.2 then
          (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) d e
        else ((j : ℤ) - x.2 : ℂ) *
          ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (e (a, j - x.2 - 1) : ℂ) *
            wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1))‖ ≤
        T j * W := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast, T]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    split_ifs with hlt heq
    · simp
    · rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcol e d _) (norm_nonneg (bilinear D (unitCharge D x.1) β : ℂ))
    · rw [norm_mul, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∑ a : Fin D.rank,
            ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
              ‖wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (by simp))
        _ ≤ ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
            (C (e - Finsupp.single (a, j - x.2 - 1) 1) * W) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hshift a _ _) (by positivity)
        _ = _ := by rw [Finset.sum_mul]; congr 1; funext a; ring
  have hneg (j : ℕ) (hj : j < level D d) :
      ‖((j + x.2).choose x.2 : ℂ) *
        if (x.1, j + x.2) ∈ d.support then
          wordCoeff D α β ω (m + j) (d - Finsupp.single (x.1, j + x.2) 1) e else 0‖ ≤
        C e * N ^ (x.2 + 1) * W := by
    have hchoose : ((j + x.2).choose x.2 : ℝ) ≤ N ^ x.2 := by
      calc
        _ ≤ (j + 1 : ℝ) ^ x.2 := by exact_mod_cast Nat.choose_add_le_add_one_pow j x.2
        _ ≤ N ^ x.2 := pow_le_pow_left₀ (by positivity)
          (by dsimp [N]; exact_mod_cast (show j + 1 ≤ 1 + level D d by omega)) _
    rw [norm_mul, Complex.norm_natCast]
    split_ifs with hd
    · have hh := (hcol e _ (m + j)).trans
        (mul_le_mul_of_nonneg_left (columnWeight_sub_le D B hB _ d (x.1, j + x.2)) hCe)
      calc
        _ ≤ N ^ x.2 * (C e * (N * W)) :=
          mul_le_mul hchoose hh (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    · simp only [norm_zero, mul_zero]; positivity
  rw [wordCoeff_cons]
  calc
    _ ≤ (∑ j ∈ Finset.range (level D d),
        ‖((j + x.2).choose x.2 : ℂ) *
          if (x.1, j + x.2) ∈ d.support then
            wordCoeff D α β ω (m + j) (d - Finsupp.single (x.1, j + x.2) 1) e else 0‖) +
      ∑ j ∈ Finset.range (x.2 + level D e + 1),
        ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
          (if j < x.2 then 0 else if j = x.2 then
            (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) d e
          else ((j : ℤ) - x.2 : ℂ) *
            ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (e (a, j - x.2 - 1) : ℂ) *
              wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ (level D d : ℝ) * (C e * N ^ (x.2 + 1) * W) + S * W := by
      apply add_le_add
      · exact (Finset.sum_le_sum (fun j hj => hneg j (Finset.mem_range.mp hj))).trans (by simp)
      · rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun j hj => hpos j)
    _ ≤ N * (C e * N ^ (x.2 + 1) * W) + S * W := by
      gcongr
      dsimp [N]
      linarith
    _ = C e * columnWeight D B ((K + (x.2 + 2)) + e.degree) d + S * W := by
      dsimp [columnWeight, W, N]
      rw [show K + (x.2 + 2) + e.degree = (K + e.degree) + (x.2 + 2) by omega]
      simp only [pow_add, pow_succ, pow_one]
      ring
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (columnWeight_grow D B hB _ _ (by omega) d) hS)

/-- Every actual descendant word has a factorial column envelope in every signed mode. -/
private theorem word_column_bound (D : LatticeData) (α β : Charge D) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ω : List (Index D), ∃ K : ℕ, ∀ e : Occ D,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Occ D) (m : ℤ),
        ‖wordCoeff D α β ω m d e‖ ≤ C * columnWeight D B (K + e.degree) d := by
  classical
  obtain ⟨B, L, hB, hL, hbase⟩ := ground_column_bound D α β
  refine ⟨B, hB, ?_⟩
  intro ω
  induction ω with
  | nil =>
    refine ⟨0, fun e => ⟨L ^ e.degree, by positivity, ?_⟩⟩
    intro d m
    simpa [columnWeight, mul_assoc] using hbase e d m
  | cons x ω ih =>
    obtain ⟨K, hi⟩ := ih
    choose C hC hb using hi
    exact ⟨K + (x.2 + 2), fun e => word_column_step D α β ω x B hB K C hC hb e⟩

private theorem factorialEnvelope_mul (D : LatticeData) (L B : ℝ) (d : Occ D) :
    L ^ d.degree * factorialEnvelope D B d = factorialEnvelope D (L * B) d := by
  classical
  have hdegree : L ^ d.degree = d.prod (fun _ n => L ^ n) := by
    simp [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  rw [hdegree]
  unfold factorialEnvelope Finsupp.prod
  rw [← mul_div_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [← mul_pow]
  congr 1
  ring

private theorem factorialEnvelope_creation (D : LatticeData) (B : ℝ) (d : Occ D) :
    factorialEnvelope D B d = B ^ d.degree *
      ‖(creationCoeff D (fun _ => 1) (level D d)).coeff d‖ := by
  classical
  have hdegree : B ^ d.degree = d.prod (fun _ n => B ^ n) := by
    simp [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  rw [creation_coefficient_norm, hdegree]
  simp only [Int.cast_one, norm_one]
  unfold factorialEnvelope FactorialFockMetric.weight Finsupp.prod
  rw [Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [div_pow, one_pow]
  ring

private theorem factorialEnvelope_summable (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q‖ ^ level D d * factorialEnvelope D B d) := by
  have hs := creation_occupation_summable D (fun _ => 1) B hB q hq
  simpa only [factorialEnvelope_creation, norm_mul, norm_pow, mul_left_comm, mul_comm,
    mul_assoc] using hs

private theorem polynomial_geometric_bound (K : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 + (n : ℝ)) ^ K * x ^ n ≤ C := by
  have hg := summable_geometric_of_lt_one hx hx1
  have hp := summable_pow_mul_geometric_of_norm_lt_one K
    (r := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)
  refine ⟨2 ^ (K - 1) * ((∑' n : ℕ, x ^ n) + (∑' n : ℕ, (n : ℝ) ^ K * x ^ n)),
    mul_nonneg (by positivity) (add_nonneg
      (tsum_nonneg (fun _ => pow_nonneg hx _))
      (tsum_nonneg (fun _ => mul_nonneg (by positivity) (pow_nonneg hx _)))), ?_⟩
  intro n
  calc
    _ ≤ (2 ^ (K - 1) * (1 ^ K + (n : ℝ) ^ K)) * x ^ n :=
      mul_le_mul_of_nonneg_right (add_pow_le (by positivity) (by positivity) K)
        (pow_nonneg hx _)
    _ = 2 ^ (K - 1) * (x ^ n + (n : ℝ) ^ K * x ^ n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (hg.le_tsum n (fun _ _ => pow_nonneg hx _))
        (hp.le_tsum n (fun _ _ => mul_nonneg (by positivity) (pow_nonneg hx _)))) (by positivity)

/-- Polynomial energy factors preserve summability of the factorial occupation envelope. -/
private theorem polynomial_factorialEnvelope_summable (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q‖ ^ level D d *
      (1 + (level D d : ℝ)) ^ K * factorialEnvelope D B d) := by
  obtain ⟨ρ, hqρ, hρ1⟩ := exists_between hq
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg q) hqρ
  have hx0 : 0 ≤ ‖q‖ / ρ := div_nonneg (norm_nonneg q) hρ0.le
  have hx1 : ‖q‖ / ρ < 1 := (div_lt_one hρ0).mpr hqρ
  obtain ⟨C, hC, hb⟩ := polynomial_geometric_bound K (‖q‖ / ρ) hx0 hx1
  have hs := factorialEnvelope_summable D B hB (ρ : ℂ)
    (by simpa [abs_of_pos hρ0] using hρ1)
  have hs' : Summable (fun d : Occ D => C * (ρ ^ level D d * factorialEnvelope D B d)) := by
    simpa [abs_of_pos hρ0] using hs.mul_left C
  refine hs'.of_nonneg_of_le (fun d => by
    exact mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg q) _) (by positivity))
      (factorialEnvelope_nonneg D B hB d)) ?_
  intro d
  have hh := mul_le_mul_of_nonneg_right (hb (level D d))
    (mul_nonneg (pow_nonneg hρ0.le (level D d)) (factorialEnvelope_nonneg D B hB d))
  calc
    _ = ((1 + (level D d : ℝ)) ^ K * (‖q‖ / ρ) ^ level D d) *
        (ρ ^ level D d * factorialEnvelope D B d) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := hh

/-- Ungrouped absolute summability for any two actual descendant words,
with arbitrary signed mode choices depending on the occupation. -/
private theorem word_contraction_summable (D : LatticeData) (α β γ : Charge D)
    (ω ν : List (Index D)) (e f : Occ D) (m n : Occ D → ℤ)
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ level D d *
      wordCoeff D α (β + γ) ω (m d) e d * wordCoeff D β γ ν (n d) d f‖) := by
  obtain ⟨L, hL, hr⟩ := word_row_bound D α (β + γ)
  obtain ⟨K, hr⟩ := hr ω
  obtain ⟨C, hC, hr⟩ := hr e
  obtain ⟨B, hB, hc⟩ := word_column_bound D β γ
  obtain ⟨J, hc⟩ := hc ν
  obtain ⟨S, hS, hc⟩ := hc f
  have hLB : 0 ≤ L * B := mul_nonneg (by linarith) (by linarith)
  have hs := (polynomial_factorialEnvelope_summable D (L * B) hLB
    (K + (J + f.degree)) q hq).mul_left (C * S)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro d
  rw [norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ ‖q‖ ^ level D d * (C * rowWeight D L K d) *
        (S * columnWeight D B (J + f.degree) d) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hr d (m d)) (pow_nonneg (norm_nonneg q) _))
        (hc d (n d)) (norm_nonneg _)
        (mul_nonneg (pow_nonneg (norm_nonneg q) _)
          (mul_nonneg hC (rowWeight_nonneg D L hL K d)))
    _ = _ := by
      dsimp [rowWeight, columnWeight]
      rw [pow_add, ← factorialEnvelope_mul]
      ring


private theorem polynomial_expansion (D : LatticeData) (p : Oscillator D) :
    p = ∑ e ∈ p.support, p.coeff e • b D e := by
  simpa only [b, smul_monomial, smul_eq_mul, mul_one] using p.as_sum

private theorem canonical_monomial_word (D : LatticeData) (α β : Charge D)
    (U : Occ D) (m : ℤ) (p : Oscillator D) :
    canonical D α β (b D U) m p = wordMap D α β (occurrences D U) m p := by
  change ((((Y D (Finsupp.single α (b D U)))[[m]]) (Finsupp.single β p)) (α + β)) = _
  rw [show b D U = monomial U (1 : ℂ) from rfl, stateField_monomial]
  rfl

private theorem canonical_coefficient_expansion (D : LatticeData) (α β : Charge D)
    (u w : Oscillator D) (m : ℤ) (e : Occ D) :
    (canonical D α β u m w).coeff e =
      ∑ U ∈ u.support, ∑ W ∈ w.support,
        (u.coeff U * w.coeff W) * wordCoeff D α β (occurrences D U) m e W := by
  classical
  conv_lhs => rw [polynomial_expansion D u, polynomial_expansion D w]
  simp only [map_sum, map_smul, Finset.sum_apply, LinearMap.sum_apply,
    Pi.smul_apply, LinearMap.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    smul_eq_mul, canonical_monomial_word, Finset.mul_sum, wordCoeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro W hW
  ring

private theorem canonical_basis_input_expansion (D : LatticeData) (α β : Charge D)
    (u : Oscillator D) (m : ℤ) (e d : Occ D) :
    (canonical D α β u m (b D d)).coeff e =
      ∑ U ∈ u.support, u.coeff U * wordCoeff D α β (occurrences D U) m e d := by
  classical
  rw [canonical_coefficient_expansion]
  simp [b]

private theorem inner_coefficient_expansion (D : LatticeData) (p t : Oscillator D) :
    H D p t = ∑ P ∈ p.support,
      (FactorialFockMetric.weight P : ℂ) * star (p.coeff P) * t.coeff P := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [H, FactorialFockMetric.inner, map_sum, sum_inner]
  exact Finset.sum_congr rfl (fun P hP =>
    FactorialFockMetric.inner_monomial_left P (p.coeff P) t)

private theorem inner_basis_coordinate (D : LatticeData) (d : Occ D) (t : Oscillator D) :
    H D (b D d) t / (FactorialFockMetric.weight d : ℂ) = t.coeff d := by
  have hw : (FactorialFockMetric.weight d : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (FactorialFockMetric.weight_pos d))
  simp [H, b, FactorialFockMetric.inner_monomial_left, hw]

/-- The literal sewing term is a finite external-state expansion of the actual word contractions.
No internal occupation is truncated or grouped. -/
private theorem sewnTerm_expansion (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) :
    sewnTerm D α β γ u v w p r s q d =
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ W ∈ w.support,
        ((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * w.coeff W) *
        (q ^ level D d *
          wordCoeff D α (β + γ) (occurrences D U) (r + (level D d : ℤ)) P d *
          wordCoeff D β γ (occurrences D V) (s - (level D d : ℤ)) d W) := by
  classical
  unfold sewnTerm A
  rw [inner_basis_coordinate, inner_coefficient_expansion,
    canonical_coefficient_expansion]
  simp only [canonical_basis_input_expansion, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := w.support) (t := p.support)]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := w.support) (t := u.support),
    Finset.sum_comm (s := v.support) (t := u.support)]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro W hW
  ring

/-- Absolute summability of the ungrouped literal canonical occupation contraction,
for all external oscillator polynomials, signed offsets and open-disk parameters.
The factorial form supplies coordinate resolution; BPZ invariance is not asserted. -/
theorem canonical_sewing_summable (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖sewnTerm D α β γ u v w p r s q d‖) := by
  classical
  have hs : Summable (fun d : Occ D =>
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ W ∈ w.support,
        ‖((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
            u.coeff U * v.coeff V * w.coeff W) *
          (q ^ level D d *
            wordCoeff D α (β + γ) (occurrences D U) (r + (level D d : ℤ)) P d *
            wordCoeff D β γ (occurrences D V) (s - (level D d : ℤ)) d W)‖) := by
    apply summable_sum
    intro P hP
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    apply summable_sum
    intro W hW
    simpa only [norm_mul] using
      (word_contraction_summable D α β γ (occurrences D U) (occurrences D V) P W
        (fun d => r + (level D d : ℤ)) (fun d => s - (level D d : ℤ)) q hq).mul_left
        ‖(FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * w.coeff W‖
  refine hs.of_nonneg_of_le (fun d => norm_nonneg _) ?_
  intro d
  rw [sewnTerm_expansion]
  apply norm_sum_le_of_le
  intro P hP
  apply norm_sum_le_of_le
  intro U hU
  apply norm_sum_le_of_le
  intro V hV
  exact norm_sum_le _ _


#print axioms canonical_sewing_summable
#print axioms word_contraction_summable
#print axioms creation_coefficient_factorial
#print axioms creation_radial_bound
#print axioms creation_occupation_summable
#print axioms word_column_bound
#print axioms ground_column_bound
#print axioms word_row_bound
#print axioms ground_row_bound
#print axioms wordMap_nil_X
#print axioms wordCoeff_cons_finite
#print axioms wordCoeff_cons

end
end D5.S3.VertexAlgebra.CanonicalOccupationSewing
