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
of the original lattice fields. -/

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
  simp only [smul_eq_mul]
  ring

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

#print axioms creation_coefficient_factorial
#print axioms creation_radial_bound
#print axioms creation_occupation_summable
#print axioms wordMap_nil_X
#print axioms wordCoeff_cons_finite
#print axioms wordCoeff_cons

end
end D5.S3.VertexAlgebra.CanonicalOccupationSewing
