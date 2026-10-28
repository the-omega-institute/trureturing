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
open scoped BigOperators

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
    · simp [map_sum, Derivation.map_smul, pderiv_X, Pi.single_apply, Prod.mk.injEq,
        h, Ne.symm h]
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
        simp [hx, Ne.symm hx]
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
        norm_prod, norm_div, norm_pow, Finset.prod_div_distrib, hn]

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
        simp [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1, mul_div_assoc,
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
    have hh := D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.
      summable_norm_signed_integer_occupations (Fin D.rank)
        (q := ((‖q‖ / ρ : ℝ) : ℂ)) (by simpa [abs_of_nonneg hR0] using hR1)
    simpa [D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.signedIntegerMonomial,
      D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.integerEnergy,
      level, LatticePositiveEnergy.oscillatorEnergy, abs_of_nonneg hR0] using hh
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

#print axioms creation_coefficient_factorial
#print axioms creation_radial_bound
#print axioms creation_occupation_summable

end
end D5.S3.VertexAlgebra.CanonicalOccupationSewing
