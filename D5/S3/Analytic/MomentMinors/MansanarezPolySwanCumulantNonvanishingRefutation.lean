/- GID: D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.claim; result=D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result; claim=D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.claim
   digest: Finite-support SMD law refutes universal cumulant-coefficient nonvanishing. -/

/-
Public result: proof_shape: bind-only; escape_witness: none (designated refutation result);
admission_basis: open-problem-resolution (#24312; Refuted).
Public claim is the literal preregistered source proposition; its proof uses the private
implementation definitions directly, with no substituted public aliases. Direct frozen dependencies: none.
The public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.ApplyFun
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- All absolute moments exist; integrability makes each source expectation genuine. -/
def AllMoments (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ

/-- Definition 2.1, expressed for the law of the random variable on the real line. -/
def SMD (μ : Measure ℝ) : Prop :=
  Measure.map (fun x : ℝ => -x) μ = μ ∧
  AllMoments μ ∧
  ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → AllMoments ν →
    (∀ n : ℕ, 1 ≤ n → moment id n μ = moment id n ν) → μ = ν

/-- Definition 2.3: K_n = (-i)^n (log φ)^(n)(0).
For a probability law φ(0)=1; the principal complex logarithm agrees with the
local logarithm at 1. The real part selects the real cumulant. -/
def cumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  (((-Complex.I) ^ n) *
    iteratedDeriv n (fun t : ℝ => Complex.log (charFun μ t)) 0).re

/-- D_j shifts one factor T_i to T_(i+j), extended linearly. -/
def shiftDerivative (j : ℕ) (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  ∑ i ∈ P.vars, MvPolynomial.X (i + j) * MvPolynomial.pderiv i P

/-- Definition 3.8: L = (D_1^2 - D_2)/2. -/
def sourceL (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (1 / 2 : ℝ) *
    (shiftDerivative 1 (shiftDerivative 1 P) - shiftDerivative 2 P)

/-- Definition 3.8, expanded formula for H on monomials, extended linearly. -/
def sourceH (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  ∑ i ∈ P.vars,
    (MvPolynomial.C (-1 / 2 : ℝ) *
      ∑ l ∈ Finset.Ico 1 i,
        MvPolynomial.C (Nat.choose i l : ℝ) *
          MvPolynomial.X (1 + l) * MvPolynomial.X (1 + i - l)) *
      MvPolynomial.pderiv i P

/-- Lemma 3.4: A_n = -sum_(k=1)^(n-1) binom(n,k) T_(1+k) T_(1+n-k) T_n. -/
def sourceA (n : ℕ) : MvPolynomial ℕ ℝ :=
  -(∑ k ∈ Finset.Ico 1 n,
    MvPolynomial.C (Nat.choose n k : ℝ) *
      MvPolynomial.X (1 + k) * MvPolynomial.X (1 + n - k) * MvPolynomial.X n)

/-- R_2 and R_3 are displayed in section 1.2; subsequent R_n obey Lemma 3.4. -/
def IsSourceSequence (R : ℕ → MvPolynomial ℕ ℝ) : Prop :=
  R 2 = 0 ∧
  R 3 = -MvPolynomial.C (2 : ℝ) * MvPolynomial.X 2 ^ 3 ∧
  ∀ n : ℕ, 3 ≤ n → R (n + 1) = sourceA n + sourceL (R n) + sourceH (R n)

/-- The coefficient of T_n^1, leaving the other indeterminates unchanged. -/
def linearCoefficient (n : ℕ) (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  ∑ d ∈ P.support,
    let c := P.coeff d
    if d n = 1 then MvPolynomial.monomial (d.erase n) c else 0

/-- The source's a_n: the coefficient of T_n in R_(n+1). -/
def coefficientForm (R : ℕ → MvPolynomial ℕ ℝ) (n : ℕ) : MvPolynomial ℕ ℝ :=
  linearCoefficient n (R (n + 1))

/-- Remark 3.31 with condition (star) of Theorem 2.12.
The existential conjunct prevents vacuous quantification over source sequences.
The law formulation includes every real random variable in the stated domain. -/
def claim : Prop :=
  (∃ R : ℕ → MvPolynomial ℕ ℝ, IsSourceSequence R) ∧
  ∀ (R : ℕ → MvPolynomial ℕ ℝ), IsSourceSequence R →
    ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → SMD μ →
      ∀ m : ℕ, 3 ≤ m →
        MvPolynomial.eval (cumulant μ) (coefficientForm R (2 * m)) ≠ 0

end D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation.MPSProbe
open Filter Complex
open scoped Topology BigOperators

private def phi (p : ℝ) (t : ℝ) : ℂ :=
  1 - p + (p/2 : ℂ) * Complex.exp (-Complex.I * t) +
    (p/2 : ℂ) * Complex.exp (Complex.I * t)

private def qjet (p : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (fun t : ℝ => Complex.log (phi p t)) 0

private theorem exp_real_jet (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c * t)) =
      fun t : ℝ => c^n * Complex.exp (c*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun t : ℝ => Complex.exp (c*t))
        (Complex.exp (c*t) * c) t := by
      convert ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).cexp using 1 <;> simp
    convert (hd.const_mul (c^n)).deriv using 1 <;> ring

private theorem phi_zero (p : ℝ) : phi p 0 = 1 := by simp [phi]; ring

private theorem phi_smooth (p : ℝ) : ContDiff ℝ ⊤ (phi p) := by
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((contDiff_const.sub contDiff_const).add
    (contDiff_const.mul (contDiff_const.mul hc).cexp)).add
    (contDiff_const.mul (contDiff_const.mul hc).cexp)

private theorem phi_jet (p : ℝ) (n : ℕ) (hn : n ≠ 0) :
    iteratedDeriv n (phi p) 0 = (p/2 : ℂ) * ((-Complex.I)^n + Complex.I^n) := by
  have hc : ContDiff ℝ n (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hm : ContDiff ℝ n (fun t : ℝ => (p/2 : ℂ) * Complex.exp (-Complex.I*t)) :=
    contDiff_const.mul (contDiff_const.mul hc).cexp
  have hp : ContDiff ℝ n (fun t : ℝ => (p/2 : ℂ) * Complex.exp (Complex.I*t)) :=
    contDiff_const.mul (contDiff_const.mul hc).cexp
  unfold phi
  rw [iteratedDeriv_fun_add (contDiff_const.add hm).contDiffAt hp.contDiffAt,
    iteratedDeriv_const_add (Nat.pos_of_ne_zero hn)]
  simp only [iteratedDeriv_const_mul_field, exp_real_jet, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one]
  ring

private theorem qjet_recurrence (p : ℝ) (n : ℕ) :
    iteratedDeriv (n+1) (phi p) 0 =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℂ) *
        iteratedDeriv i (phi p) 0 * qjet p (n-i+1) := by
  have hslit : phi p 0 ∈ Complex.slitPlane := by rw [phi_zero]; simp
  have hlog : ContDiffAt ℝ ⊤ (fun t => Complex.log (phi p t)) 0 :=
    ((Complex.contDiffAt_log hslit).restrict_scalars ℝ).comp 0 (phi_smooth p).contDiffAt
  have he : (fun t => phi p t * deriv (fun s => Complex.log (phi p s)) t) =ᶠ[𝓝 0]
      deriv (phi p) := by
    have hs : ∀ᶠ t in 𝓝 (0 : ℝ), phi p t ∈ Complex.slitPlane :=
      (phi_smooth p).continuous.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hslit)
    filter_upwards [hs] with t ht
    rw [((phi_smooth p).differentiable (by simp) t).hasDerivAt.clog_real ht |>.deriv]
    exact mul_div_cancel₀ _ (Complex.slitPlane_ne_zero ht)
  have hh := he.iteratedDeriv_eq n
  rw [iteratedDeriv_fun_mul ((phi_smooth p).contDiffAt.of_le (by simp))
      (hlog.derivWithin (by simp))] at hh
  simpa only [← iteratedDeriv_succ', qjet] using hh.symm

private theorem qjet_1 (p : ℝ) : qjet p 1 = 0 := by
  have he := qjet_recurrence p 0
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero] at he
  linear_combination -he

private theorem qjet_2 (p : ℝ) : qjet p 2 = -(p : ℂ) := by
  have he := qjet_recurrence p 1
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1] at he
  linear_combination -he

private theorem qjet_3 (p : ℝ) : qjet p 3 = 0 := by
  have he := qjet_recurrence p 2
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1, qjet_2] at he
  linear_combination -he

private theorem qjet_4 (p : ℝ) : qjet p 4 = (p : ℂ)-3*p^2 := by
  have he := qjet_recurrence p 3
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1, qjet_2, qjet_3] at he
  linear_combination -he

private theorem qjet_5 (p : ℝ) : qjet p 5 = 0 := by
  have he := qjet_recurrence p 4
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1, qjet_2, qjet_3, qjet_4] at he
  linear_combination -he

private theorem qjet_6 (p : ℝ) : qjet p 6 = -((p : ℂ)-15*p^2+30*p^3) := by
  have he := qjet_recurrence p 5
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1, qjet_2, qjet_3, qjet_4, qjet_5] at he
  linear_combination -he

private theorem qjet_8 (p : ℝ) : qjet p 8 = (p : ℂ)-63*p^2+420*p^3-630*p^4 := by
  have he := qjet_recurrence p 7
  norm_num [Finset.sum_range_succ, Nat.choose, pow_succ, phi_jet, phi_zero, qjet_1, qjet_2, qjet_3, qjet_4, qjet_5, qjet_6] at he
  linear_combination -he

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private def law (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (p/2) • Measure.dirac (-1) +
  ENNReal.ofReal (1-p) • Measure.dirac 0 +
  ENNReal.ofReal (p/2) • Measure.dirac 1

private theorem three_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a b c : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (f : ℝ → E) :
    (∫ x, f x ∂(a • Measure.dirac (-1) + b • Measure.dirac 0 + c • Measure.dirac 1)) =
      a.toReal • f (-1) + b.toReal • f 0 + c.toReal • f 1 := by
  let weights : Fin 3 → ℝ≥0∞ := ![a,b,c]
  let points : Fin 3 → ℝ := ![-1,0,1]
  have hw : ∀ i, weights i ≠ ⊤ := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have h := integral_sum_dirac_eq_tsum (f := f) (x := points) (c := weights) hw
    Summable.of_finite
  simpa [Measure.sum_fintype, Fin.sum_univ_succ, weights, points, add_assoc] using h

private theorem law_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : ℝ → E) :
    (∫ x, f x ∂law p) = (p/2) • f (-1) + (1-p) • f 0 + (p/2) • f 1 := by
  rw [law, three_integral _ _ _ (by simp) (by simp) (by simp)]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by linarith)]

private theorem law_probability {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (law p) := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by positivity) (by linarith),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  convert ENNReal.ofReal_one using 1 <;> ring

private theorem law_allMoments (p : ℝ) : AllMoments (law p) := by
  intro n
  unfold law
  exact (((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

private theorem law_symmetry (p : ℝ) :
    Measure.map (fun x : ℝ => -x) (law p) = law p := by
  simp only [law, Measure.map_add _ _ (measurable_neg : Measurable (fun x : ℝ => -x)), Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_dirac, neg_neg, neg_zero]
  ac_rfl

private theorem law_moment_two {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    moment id 2 (law p) = p := by
  unfold moment
  rw [law_integral hp hp1]
  norm_num [smul_eq_mul]

private theorem law_even_moment {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (hn : n ≠ 0) : moment id (2*n) (law p) = p := by
  unfold moment
  rw [law_integral hp hp1]
  simp [smul_eq_mul, pow_mul, zero_pow (by omega : 2*n ≠ 0)]

private theorem law_moment_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    moment id 1 (law p) = 0 := by
  unfold moment
  rw [law_integral hp hp1]
  norm_num [smul_eq_mul]

private theorem moment_support {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : Measure ℝ) (hm : AllMoments ν)
    (he : ∀ n : ℕ, 1 ≤ n → moment id n (law p) = moment id n ν) :
    ∀ᵐ x ∂ν, x = -1 ∨ x = 0 ∨ x = 1 := by
  have hi : Integrable (fun x : ℝ => x^6 - 2*x^4 + x^2) ν :=
    ((hm 6).sub ((hm 4).const_mul 2)).add (hm 2)
  have hz : (∫ x : ℝ, (x^6 - 2*x^4 + x^2) ∂ν) = 0 := by
    rw [integral_add (f := fun x : ℝ => x^6-2*x^4) (g := fun x : ℝ => x^2)
        ((hm 6).sub ((hm 4).const_mul 2)) (hm 2),
      integral_sub (f := fun x : ℝ => x^6) (g := fun x : ℝ => 2*x^4)
        (hm 6) ((hm 4).const_mul 2), integral_const_mul]
    change moment id 6 ν - 2*moment id 4 ν + moment id 2 ν = 0
    rw [← he 6 (by norm_num), ← he 4 (by norm_num), ← he 2 (by norm_num),
      show moment id 6 (law p) = p from law_even_moment hp hp1 3 (by norm_num),
      show moment id 4 (law p) = p from law_even_moment hp hp1 2 (by norm_num),
      law_moment_two hp hp1]
    ring
  have hnonneg : 0 ≤ (fun x : ℝ => x^6 - 2*x^4 + x^2) := by
    intro x
    have hr : x^6 - 2*x^4 + x^2 = (x*(x^2-1))^2 := by ring
    change 0 ≤ x^6 - 2*x^4 + x^2
    rw [hr]
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hz
  filter_upwards [hae] with x hx
  change x^6 - 2*x^4 + x^2 = 0 at hx
  have hf : (x*(x-1)*(x+1))^2 = 0 := by nlinarith [hx]
  have hf' : x*(x-1)*(x+1) = 0 := (sq_eq_zero_iff).mp hf
  rcases mul_eq_zero.mp hf' with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl h)
    · right; right; linarith
  · left; linarith

private theorem law_determinate {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hm : AllMoments ν)
    (he : ∀ n : ℕ, 1 ≤ n → moment id n (law p) = moment id n ν) : law p = ν := by
  classical
  have hs : ∀ᵐ x ∂ν, x ∈ ({-1,0,1} : Finset ℝ) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using moment_support hp hp1 ν hm he
  have hν := (Measure.ae_mem_finset_iff).mp hs
  have hν' : ν = ν {-1} • Measure.dirac (-1) + ν {0} • Measure.dirac 0 +
      ν {1} • Measure.dirac 1 := by
    simpa only [Finset.sum_insert (by norm_num : (-1:ℝ) ∉ ({0,1}:Finset ℝ)),
      Finset.sum_insert (by norm_num : (0:ℝ) ∉ ({1}:Finset ℝ)), Finset.sum_singleton,
      add_assoc] using hν
  have h1 := he 1 (by norm_num)
  have h2 := he 2 (by norm_num)
  rw [law_moment_one hp hp1] at h1
  rw [law_moment_two hp hp1] at h2
  unfold moment at h1 h2
  rw [hν', three_integral _ _ _ (measure_ne_top _ _) (measure_ne_top _ _)
    (measure_ne_top _ _)] at h1 h2
  norm_num [smul_eq_mul] at h1 h2
  have ht : (ν {-1}).toReal + (ν {0}).toReal + (ν {1}).toReal = 1 := by
    have hu : ν Set.univ = 1 := measure_univ
    rw [hν'] at hu
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one] at hu
    apply_fun ENNReal.toReal at hu
    simpa [ENNReal.toReal_add, measure_ne_top] using hu
  have ha : (ν {-1}).toReal = p/2 := by linarith
  have hb : (ν {0}).toReal = 1-p := by linarith
  have hc : (ν {1}).toReal = p/2 := by linarith
  have hea : ν {-1} = ENNReal.ofReal (p/2) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
    rw [ha, ENNReal.toReal_ofReal (by positivity)]
  have heb : ν {0} = ENNReal.ofReal (1-p) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
    rw [hb, ENNReal.toReal_ofReal (by linarith)]
  have hec : ν {1} = ENNReal.ofReal (p/2) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
    rw [hc, ENNReal.toReal_ofReal (by positivity)]
  rw [hν', hea, heb, hec]
  rfl

private theorem law_SMD {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : SMD (law p) := by
  refine ⟨law_symmetry p, law_allMoments p, ?_⟩
  intro ν hν hm he
  letI := hν
  exact law_determinate hp hp1 ν hm he

private theorem law_charFun {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    charFun (law p) = phi p := by
  funext t
  rw [charFun_apply_real, law_integral hp hp1]
  simp only [mul_neg_one, mul_zero, mul_one, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, Complex.real_smul, smul_eq_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  simp only [phi, neg_mul, mul_comm Complex.I (t : ℂ)]
  ring


private def quartic (p : ℝ) : ℝ :=
  56700*p^4 - 56700*p^3 + 18165*p^2 - 1950*p + 41

private theorem root_exists :
    ∃ p : ℝ, 1/100 < p ∧ p < 1/20 ∧ quartic p = 0 := by
  have ha : 0 < quartic (1/100) := by norm_num [quartic]
  have hb : quartic (1/20) < 0 := by norm_num [quartic]
  have hc : Continuous quartic := by unfold quartic; fun_prop
  obtain ⟨p, hp, he⟩ := intermediate_value_Ioo' (show (1/100:ℝ) ≤ 1/20 by norm_num)
    hc.continuousOn (show (0:ℝ) ∈ Set.Ioo (quartic (1/20)) (quartic (1/100)) from ⟨hb,ha⟩)
  exact ⟨p,hp.1,hp.2,he⟩

private theorem root_cancellation {p : ℝ} (h : quartic p = 0) :
    21*(p-15*p^2+30*p^3)^2 + 20*(p-3*p^2)*(p-63*p^2+420*p^3-630*p^4) = 0 := by
  calc
    _ = p^2 * quartic p := by unfold quartic; ring
    _ = 0 := by rw [h, mul_zero]

private theorem root_signs {p : ℝ} (ha : 1/100 < p) (hb : p < 1/20)
    (hz : quartic p = 0) :
    0 < p ∧ 0 < p-3*p^2 ∧ 0 < p-15*p^2+30*p^3 ∧
      p-63*p^2+420*p^3-630*p^4 < 0 := by
  have hp : 0 < p := by linarith
  have hk4 : 0 < p-3*p^2 := by nlinarith
  have hp3 : 0 < p^3 := pow_pos hp 3
  have hk6 : 0 < p-15*p^2+30*p^3 := by nlinarith
  have he := root_cancellation hz
  have hs : 0 < (p-15*p^2+30*p^3)^2 := sq_pos_of_pos hk6
  exact ⟨hp,hk4,hk6,by nlinarith⟩

private theorem law_cumulants {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    cumulant (law p) 2 = p ∧
    cumulant (law p) 3 = 0 ∧
    cumulant (law p) 4 = p-3*p^2 ∧
    cumulant (law p) 5 = 0 ∧
    cumulant (law p) 6 = p-15*p^2+30*p^3 ∧
    cumulant (law p) 8 = p-63*p^2+420*p^3-630*p^4 := by
  have hc (n : ℕ) : cumulant (law p) n = ((-Complex.I)^n * qjet p n).re := by
    simp only [cumulant, law_charFun hp hp1, qjet]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hc, qjet_2, qjet_3, qjet_4, qjet_5, qjet_6, qjet_8] <;>
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im]


open MvPolynomial
open scoped BigOperators

private theorem derivation_partials (f : ℕ → MvPolynomial ℕ ℝ) (P : MvPolynomial ℕ ℝ) :
    MvPolynomial.mkDerivation ℝ f P =
      ∑ i ∈ P.vars, f i * MvPolynomial.pderiv i P := by
  classical
  let D : Derivation ℝ (MvPolynomial ℕ ℝ) (MvPolynomial ℕ ℝ) :=
    ∑ i ∈ P.vars, f i • MvPolynomial.pderiv i
  have h : MvPolynomial.mkDerivation ℝ f P = D P := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    intro k hk
    simp [D, MvPolynomial.mkDerivation_X, MvPolynomial.pderiv_X, Pi.single_apply, hk]
  simpa [D, Derivation.smul_apply, smul_eq_mul] using h

private theorem shift_eq (j : ℕ) (P : MvPolynomial ℕ ℝ) :
    shiftDerivative j P = MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.X (i+j)) P := by
  exact (derivation_partials _ _).symm

private theorem lc_add (n : ℕ) (P Q : MvPolynomial ℕ ℝ) :
    linearCoefficient n (P+Q) = linearCoefficient n P + linearCoefficient n Q := by
  classical
  change (P.coeff + Q.coeff).sum (fun d c => if d n = 1 then MvPolynomial.monomial (d.erase n) c else 0) =
    P.coeff.sum (fun d c => if d n = 1 then MvPolynomial.monomial (d.erase n) c else 0) +
    Q.coeff.sum (fun d c => if d n = 1 then MvPolynomial.monomial (d.erase n) c else 0)
  apply Finsupp.sum_add_index'
  · intro d; split_ifs <;> simp
  · intro d a b; split_ifs <;> simp

private theorem lc_monomial (n : ℕ) (d : ℕ →₀ ℕ) (c : ℝ) :
    linearCoefficient n (MvPolynomial.monomial d c) =
      if d n = 1 then MvPolynomial.monomial (d.erase n) c else 0 := by
  classical
  change (MvPolynomial.monomial d c).coeff.sum
    (fun e a => if e n = 1 then MvPolynomial.monomial (e.erase n) a else 0) = _
  exact MvPolynomial.sum_monomial_eq (by split_ifs <;> simp)

private def baseH (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  MvPolynomial.mkDerivation ℝ (fun i => ∑ l ∈ Finset.Ico 1 i,
    MvPolynomial.C (Nat.choose i l : ℝ) *
      MvPolynomial.X (1+l) * MvPolynomial.X (1+i-l)) P

private theorem H_half (P : MvPolynomial ℕ ℝ) :
    sourceH P = MvPolynomial.C (-1/2 : ℝ) * baseH P := by
  rw [baseH, derivation_partials]
  simp only [sourceH, Finset.mul_sum, Finset.sum_mul, mul_assoc]

private theorem double_step (n : ℕ) (P : MvPolynomial ℕ ℝ) :
    (2 : MvPolynomial ℕ ℝ) * (sourceA n + sourceL P + sourceH P) =
      2 * sourceA n + shiftDerivative 1 (shiftDerivative 1 P) -
        shiftDerivative 2 P - baseH P := by
  have hh : (2 : MvPolynomial ℕ ℝ) * MvPolynomial.C (1/2:ℝ) = 1 := by
    rw [show (2:MvPolynomial ℕ ℝ) = MvPolynomial.C (2:ℝ) by
      rw [show (2:ℝ)=1+1 by norm_num, map_add, map_one]; ring,
      ← MvPolynomial.C_mul]
    norm_num
  have hn : (MvPolynomial.C (-1/2:ℝ) : MvPolynomial ℕ ℝ) = -MvPolynomial.C (1/2:ℝ) := by
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring, map_neg]
  rw [sourceL, H_half, hn]
  linear_combination (shiftDerivative 1 (shiftDerivative 1 P) - shiftDerivative 2 P -
    baseH P) * hh

private theorem deriv_C (D : Derivation ℝ (MvPolynomial ℕ ℝ) (MvPolynomial ℕ ℝ)) (c : ℝ) :
    D (MvPolynomial.C c) = 0 := MvPolynomial.derivation_C D c

private def r3 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (-2 : ℝ)*MvPolynomial.X 2^3

private def r4 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (6 : ℝ)*MvPolynomial.X 2^4 + MvPolynomial.C (-12 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2

private def r5 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (-24 : ℝ)*MvPolynomial.X 2^5 + MvPolynomial.C (120 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2 + MvPolynomial.C (-20 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^2 + MvPolynomial.C (-30 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4

private def r6 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (120 : ℝ)*MvPolynomial.X 2^6 + MvPolynomial.C (-1200 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^2 + MvPolynomial.C (300 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^2 + MvPolynomial.C (900 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (-30 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5^2 + MvPolynomial.C (210 : ℝ)*MvPolynomial.X 3^4 + MvPolynomial.C (-120 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (-30 : ℝ)*MvPolynomial.X 4^3

private def r7 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (-720 : ℝ)*MvPolynomial.X 2^7 + MvPolynomial.C (12600 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3^2 + MvPolynomial.C (-4200 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4^2 + MvPolynomial.C (-18900 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (630 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 5^2 + MvPolynomial.C (-8820 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^4 + MvPolynomial.C (5040 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (1260 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^3 + MvPolynomial.C (-42 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 6^2 + MvPolynomial.C (1260 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 5 + MvPolynomial.C (4830 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4^2 + MvPolynomial.C (-210 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-140 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (-210 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 5^2

private def r8 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (5040 : ℝ)*MvPolynomial.X 2^8 + MvPolynomial.C (-141120 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 3^2 + MvPolynomial.C (58800 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 4^2 + MvPolynomial.C (352800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (-11760 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 5^2 + MvPolynomial.C (246960 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^4 + MvPolynomial.C (-141120 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (-35280 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^3 + MvPolynomial.C (1176 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 6^2 + MvPolynomial.C (-70560 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^3*MvPolynomial.X 5 + MvPolynomial.C (-270480 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4^2 + MvPolynomial.C (11760 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (7840 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (11760 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (-56 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 7^2 + MvPolynomial.C (-95760 : ℝ)*MvPolynomial.X 3^4*MvPolynomial.X 4 + MvPolynomial.C (11760 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (14280 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 5^2 + MvPolynomial.C (40320 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 5 + MvPolynomial.C (-336 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (6230 : ℝ)*MvPolynomial.X 4^4 + MvPolynomial.C (-560 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-420 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 6^2 + MvPolynomial.C (-560 : ℝ)*MvPolynomial.X 5^2*MvPolynomial.X 6

private def r9 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (-40320 : ℝ)*MvPolynomial.X 2^9 + MvPolynomial.C (1693440 : ℝ)*MvPolynomial.X 2^6*MvPolynomial.X 3^2 + MvPolynomial.C (-846720 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 4^2 + MvPolynomial.C (-6350400 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (211680 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 5^2 + MvPolynomial.C (-5927040 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^4 + MvPolynomial.C (3386880 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (846720 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4^3 + MvPolynomial.C (-28224 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 6^2 + MvPolynomial.C (2540160 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^3*MvPolynomial.X 5 + MvPolynomial.C (9737280 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 4^2 + MvPolynomial.C (-423360 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-282240 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (-423360 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (2016 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 7^2 + MvPolynomial.C (6894720 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^4*MvPolynomial.X 4 + MvPolynomial.C (-846720 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (-1028160 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 5^2 + MvPolynomial.C (-2903040 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 5 + MvPolynomial.C (24192 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (-448560 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^4 + MvPolynomial.C (40320 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (30240 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 6^2 + MvPolynomial.C (40320 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (-72 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 8^2 + MvPolynomial.C (534240 : ℝ)*MvPolynomial.X 3^6 + MvPolynomial.C (-105840 : ℝ)*MvPolynomial.X 3^4*MvPolynomial.X 6 + MvPolynomial.C (-1980720 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (-1746360 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4^3 + MvPolynomial.C (30240 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (35532 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 6^2 + MvPolynomial.C (40320 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 7 + MvPolynomial.C (259560 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (60480 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5^3 + MvPolynomial.C (-504 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (60480 : ℝ)*MvPolynomial.X 4^3*MvPolynomial.X 6 + MvPolynomial.C (157500 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 5^2 + MvPolynomial.C (-1008 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (-756 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 7^2 + MvPolynomial.C (-630 : ℝ)*MvPolynomial.X 5^2*MvPolynomial.X 8 + MvPolynomial.C (-2520 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (-560 : ℝ)*MvPolynomial.X 6^3

private def r10 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (362880 : ℝ)*MvPolynomial.X 2^10 + MvPolynomial.C (-21772800 : ℝ)*MvPolynomial.X 2^7*MvPolynomial.X 3^2 + MvPolynomial.C (12700800 : ℝ)*MvPolynomial.X 2^6*MvPolynomial.X 4^2 + MvPolynomial.C (114307200 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (-3810240 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 5^2 + MvPolynomial.C (133358400 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3^4 + MvPolynomial.C (-76204800 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (-19051200 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 4^3 + MvPolynomial.C (635040 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 6^2 + MvPolynomial.C (-76204800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^3*MvPolynomial.X 5 + MvPolynomial.C (-292118400 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^2*MvPolynomial.X 4^2 + MvPolynomial.C (12700800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (8467200 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (12700800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (-60480 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 7^2 + MvPolynomial.C (-310262400 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^4*MvPolynomial.X 4 + MvPolynomial.C (38102400 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (46267200 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 5^2 + MvPolynomial.C (130636800 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 5 + MvPolynomial.C (-1088640 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (20185200 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^4 + MvPolynomial.C (-1814400 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-1360800 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4*MvPolynomial.X 6^2 + MvPolynomial.C (-1814400 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (3240 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 8^2 + MvPolynomial.C (-48081600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^6 + MvPolynomial.C (9525600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^4*MvPolynomial.X 6 + MvPolynomial.C (178264800 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (157172400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4^3 + MvPolynomial.C (-2721600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-3197880 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 6^2 + MvPolynomial.C (-3628800 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 7 + MvPolynomial.C (-23360400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-5443200 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 5^3 + MvPolynomial.C (45360 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (-5443200 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^3*MvPolynomial.X 6 + MvPolynomial.C (-14175000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^2*MvPolynomial.X 5^2 + MvPolynomial.C (90720 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (68040 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 7^2 + MvPolynomial.C (56700 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5^2*MvPolynomial.X 8 + MvPolynomial.C (226800 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (50400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 6^3 + MvPolynomial.C (-90 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 9^2 + MvPolynomial.C (16964640 : ℝ)*MvPolynomial.X 3^5*MvPolynomial.X 5 + MvPolynomial.C (81912600 : ℝ)*MvPolynomial.X 3^4*MvPolynomial.X 4^2 + MvPolynomial.C (-1814400 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 4*MvPolynomial.X 7 + MvPolynomial.C (-7786800 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-16153200 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (-27178200 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (68040 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (78120 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 7^2 + MvPolynomial.C (-29181600 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4^3*MvPolynomial.X 5 + MvPolynomial.C (226800 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 8 + MvPolynomial.C (700560 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (453600 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5^2*MvPolynomial.X 7 + MvPolynomial.C (630000 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6^2 + MvPolynomial.C (-720 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 8*MvPolynomial.X 9 + MvPolynomial.C (-2351160 : ℝ)*MvPolynomial.X 4^5 + MvPolynomial.C (50400 : ℝ)*MvPolynomial.X 4^3*MvPolynomial.X 8 + MvPolynomial.C (630000 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (525840 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 6^2 + MvPolynomial.C (1411200 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (-1680 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 7*MvPolynomial.X 9 + MvPolynomial.C (-1260 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 8^2 + MvPolynomial.C (179550 : ℝ)*MvPolynomial.X 5^4 + MvPolynomial.C (-2520 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 9 + MvPolynomial.C (-5040 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (-3150 : ℝ)*MvPolynomial.X 6^2*MvPolynomial.X 8 + MvPolynomial.C (-4200 : ℝ)*MvPolynomial.X 6*MvPolynomial.X 7^2

private def r11 : MvPolynomial ℕ ℝ :=
  MvPolynomial.C (-3628800 : ℝ)*MvPolynomial.X 2^11 + MvPolynomial.C (299376000 : ℝ)*MvPolynomial.X 2^8*MvPolynomial.X 3^2 + MvPolynomial.C (-199584000 : ℝ)*MvPolynomial.X 2^7*MvPolynomial.X 4^2 + MvPolynomial.C (-2095632000 : ℝ)*MvPolynomial.X 2^6*MvPolynomial.X 3^2*MvPolynomial.X 4 + MvPolynomial.C (69854400 : ℝ)*MvPolynomial.X 2^6*MvPolynomial.X 5^2 + MvPolynomial.C (-2933884800 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 3^4 + MvPolynomial.C (1676505600 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (419126400 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 4^3 + MvPolynomial.C (-13970880 : ℝ)*MvPolynomial.X 2^5*MvPolynomial.X 6^2 + MvPolynomial.C (2095632000 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3^3*MvPolynomial.X 5 + MvPolynomial.C (8033256000 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3^2*MvPolynomial.X 4^2 + MvPolynomial.C (-349272000 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-232848000 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (-349272000 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (1663200 : ℝ)*MvPolynomial.X 2^4*MvPolynomial.X 7^2 + MvPolynomial.C (11376288000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^4*MvPolynomial.X 4 + MvPolynomial.C (-1397088000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (-1696464000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3^2*MvPolynomial.X 5^2 + MvPolynomial.C (-4790016000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 5 + MvPolynomial.C (39916800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (-740124000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4^4 + MvPolynomial.C (66528000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (49896000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 4*MvPolynomial.X 6^2 + MvPolynomial.C (66528000 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (-118800 : ℝ)*MvPolynomial.X 2^3*MvPolynomial.X 8^2 + MvPolynomial.C (2644488000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^6 + MvPolynomial.C (-523908000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^4*MvPolynomial.X 6 + MvPolynomial.C (-9804564000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^3*MvPolynomial.X 4*MvPolynomial.X 5 + MvPolynomial.C (-8644482000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 4^3 + MvPolynomial.C (149688000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (175883400 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3^2*MvPolynomial.X 6^2 + MvPolynomial.C (199584000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 7 + MvPolynomial.C (1284822000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (299376000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 5^3 + MvPolynomial.C (-2494800 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 3*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (299376000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^3*MvPolynomial.X 6 + MvPolynomial.C (779625000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4^2*MvPolynomial.X 5^2 + MvPolynomial.C (-4989600 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (-3742200 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 4*MvPolynomial.X 7^2 + MvPolynomial.C (-3118500 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 5^2*MvPolynomial.X 8 + MvPolynomial.C (-12474000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (-2772000 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 6^3 + MvPolynomial.C (4950 : ℝ)*MvPolynomial.X 2^2*MvPolynomial.X 9^2 + MvPolynomial.C (-1866110400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^5*MvPolynomial.X 5 + MvPolynomial.C (-9010386000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^4*MvPolynomial.X 4^2 + MvPolynomial.C (199584000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^3*MvPolynomial.X 4*MvPolynomial.X 7 + MvPolynomial.C (856548000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^3*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (1776852000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4^2*MvPolynomial.X 6 + MvPolynomial.C (2989602000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 5^2 + MvPolynomial.C (-7484400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (-8593200 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3^2*MvPolynomial.X 7^2 + MvPolynomial.C (3209976000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4^3*MvPolynomial.X 5 + MvPolynomial.C (-24948000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 8 + MvPolynomial.C (-77061600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (-49896000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 5^2*MvPolynomial.X 7 + MvPolynomial.C (-69300000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6^2 + MvPolynomial.C (79200 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 8*MvPolynomial.X 9 + MvPolynomial.C (258627600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^5 + MvPolynomial.C (-5544000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^3*MvPolynomial.X 8 + MvPolynomial.C (-69300000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^2*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-57842400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4^2*MvPolynomial.X 6^2 + MvPolynomial.C (-155232000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (184800 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 7*MvPolynomial.X 9 + MvPolynomial.C (138600 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 8^2 + MvPolynomial.C (-19750500 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5^4 + MvPolynomial.C (277200 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 9 + MvPolynomial.C (554400 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 5*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (346500 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 6^2*MvPolynomial.X 8 + MvPolynomial.C (462000 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 6*MvPolynomial.X 7^2 + MvPolynomial.C (-110 : ℝ)*MvPolynomial.X 2*MvPolynomial.X 10^2 + MvPolynomial.C (-1259874000 : ℝ)*MvPolynomial.X 3^6*MvPolynomial.X 4 + MvPolynomial.C (14968800 : ℝ)*MvPolynomial.X 3^5*MvPolynomial.X 7 + MvPolynomial.C (552182400 : ℝ)*MvPolynomial.X 3^4*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (504781200 : ℝ)*MvPolynomial.X 3^4*MvPolynomial.X 5^2 + MvPolynomial.C (3151764000 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 4^2*MvPolynomial.X 5 + MvPolynomial.C (-6237000 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 5*MvPolynomial.X 8 + MvPolynomial.C (-25280640 : ℝ)*MvPolynomial.X 3^3*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (1314621000 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4^4 + MvPolynomial.C (-12474000 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4^2*MvPolynomial.X 8 + MvPolynomial.C (-134164800 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-109632600 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 4*MvPolynomial.X 6^2 + MvPolynomial.C (-147054600 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 5^2*MvPolynomial.X 6 + MvPolynomial.C (138600 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 7*MvPolynomial.X 9 + MvPolynomial.C (156420 : ℝ)*MvPolynomial.X 3^2*MvPolynomial.X 8^2 + MvPolynomial.C (-61538400 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4^3*MvPolynomial.X 7 + MvPolynomial.C (-459320400 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4^2*MvPolynomial.X 5*MvPolynomial.X 6 + MvPolynomial.C (-227858400 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 5^3 + MvPolynomial.C (554400 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 6*MvPolynomial.X 9 + MvPolynomial.C (1663200 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 4*MvPolynomial.X 7*MvPolynomial.X 8 + MvPolynomial.C (346500 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5^2*MvPolynomial.X 9 + MvPolynomial.C (2647260 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (1829520 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5*MvPolynomial.X 7^2 + MvPolynomial.C (2356200 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 6^2*MvPolynomial.X 7 + MvPolynomial.C (-990 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 9*MvPolynomial.X 10 + MvPolynomial.C (-58674000 : ℝ)*MvPolynomial.X 4^4*MvPolynomial.X 6 + MvPolynomial.C (-176160600 : ℝ)*MvPolynomial.X 4^3*MvPolynomial.X 5^2 + MvPolynomial.C (462000 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 5*MvPolynomial.X 9 + MvPolynomial.C (1829520 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 6*MvPolynomial.X 8 + MvPolynomial.C (1487640 : ℝ)*MvPolynomial.X 4^2*MvPolynomial.X 7^2 + MvPolynomial.C (2356200 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 5^2*MvPolynomial.X 8 + MvPolynomial.C (10053120 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 5*MvPolynomial.X 6*MvPolynomial.X 7 + MvPolynomial.C (2217600 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 6^3 + MvPolynomial.C (-2640 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 8*MvPolynomial.X 10 + MvPolynomial.C (-1980 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 9^2 + MvPolynomial.C (2217600 : ℝ)*MvPolynomial.X 5^3*MvPolynomial.X 7 + MvPolynomial.C (4853310 : ℝ)*MvPolynomial.X 5^2*MvPolynomial.X 6^2 + MvPolynomial.C (-4620 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 7*MvPolynomial.X 10 + MvPolynomial.C (-9240 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 8*MvPolynomial.X 9 + MvPolynomial.C (-2772 : ℝ)*MvPolynomial.X 6^2*MvPolynomial.X 10 + MvPolynomial.C (-13860 : ℝ)*MvPolynomial.X 6*MvPolynomial.X 7*MvPolynomial.X 9 + MvPolynomial.C (-9240 : ℝ)*MvPolynomial.X 6*MvPolynomial.X 8^2 + MvPolynomial.C (-11550 : ℝ)*MvPolynomial.X 7^2*MvPolynomial.X 8


private theorem step3 : sourceA 3 + sourceL r3 + sourceH r3 = r4 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r3, r4, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step4 : sourceA 4 + sourceL r4 + sourceH r4 = r5 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r4, r5, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step5 : sourceA 5 + sourceL r5 + sourceH r5 = r6 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r5, r6, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step6 : sourceA 6 + sourceL r6 + sourceH r6 = r7 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r6, r7, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step7 : sourceA 7 + sourceL r7 + sourceH r7 = r8 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r7, r8, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step8 : sourceA 8 + sourceL r8 + sourceH r8 = r9 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r8, r9, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step9 : sourceA 9 + sourceL r9 + sourceH r9 = r10 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r9, r10, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem step10 : sourceA 10 + sourceL r10 + sourceH r10 = r11 := by
  have htwo : (2:MvPolynomial ℕ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : ℕ => (0:ℝ))) h
    norm_num only [map_ofNat, map_zero] at he
  apply (mul_right_injective₀ htwo)
  dsimp only
  rw [double_step]
  simp only [r10, r11, sourceA, shift_eq, baseH, map_add, map_neg, map_nsmul,
    Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.mkDerivation_X, deriv_C,
    smul_eq_mul]
  norm_num [Nat.choose, Finset.sum_Ico_succ_top, nsmul_eq_mul, map_ofNat]
  ring

private theorem sequence_values (R : ℕ → MvPolynomial ℕ ℝ) (hR : IsSourceSequence R) :
    R 7 = r7 ∧ R 9 = r9 ∧ R 11 = r11 := by
  have h3 : R 3 = r3 := by simpa [r3] using hR.2.1
  have h4 : R 4 = r4 := by rw [hR.2.2 3 (by norm_num), h3]; exact step3
  have h5 : R 5 = r5 := by rw [hR.2.2 4 (by norm_num), h4]; exact step4
  have h6 : R 6 = r6 := by rw [hR.2.2 5 (by norm_num), h5]; exact step5
  have h7 : R 7 = r7 := by rw [hR.2.2 6 (by norm_num), h6]; exact step6
  have h8 : R 8 = r8 := by rw [hR.2.2 7 (by norm_num), h7]; exact step7
  have h9 : R 9 = r9 := by rw [hR.2.2 8 (by norm_num), h8]; exact step8
  have h10 : R 10 = r10 := by rw [hR.2.2 9 (by norm_num), h9]; exact step9
  have h11 : R 11 = r11 := by rw [hR.2.2 10 (by norm_num), h10]; exact step10
  exact ⟨h7, h9, h11⟩

private theorem coefficient6 :
    linearCoefficient 6 r7 = MvPolynomial.C (-210 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 5 + MvPolynomial.C (-140 : ℝ)*MvPolynomial.X 4^2 := by
  classical
  simp only [r7, MvPolynomial.X_pow_eq_monomial]
  simp only [lc_add, MvPolynomial.C_apply,
    MvPolynomial.X, MvPolynomial.monomial_mul_monomial, lc_monomial]
  norm_num [Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.erase_single, Finsupp.erase_single_ne]

private theorem coefficient8 :
    linearCoefficient 8 r9 = MvPolynomial.C (-504 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 7 + MvPolynomial.C (-1008 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 6 + MvPolynomial.C (-630 : ℝ)*MvPolynomial.X 5^2 := by
  classical
  simp only [r9, MvPolynomial.X_pow_eq_monomial]
  simp only [lc_add, MvPolynomial.C_apply,
    MvPolynomial.X, MvPolynomial.monomial_mul_monomial, lc_monomial]
  norm_num [Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.erase_single, Finsupp.erase_single_ne]

private theorem coefficient10 :
    linearCoefficient 10 r11 = MvPolynomial.C (-990 : ℝ)*MvPolynomial.X 3*MvPolynomial.X 9 + MvPolynomial.C (-2640 : ℝ)*MvPolynomial.X 4*MvPolynomial.X 8 + MvPolynomial.C (-4620 : ℝ)*MvPolynomial.X 5*MvPolynomial.X 7 + MvPolynomial.C (-2772 : ℝ)*MvPolynomial.X 6^2 := by
  classical
  simp only [r11, MvPolynomial.X_pow_eq_monomial]
  simp only [lc_add, MvPolynomial.C_apply,
    MvPolynomial.X, MvPolynomial.monomial_mul_monomial, lc_monomial]
  norm_num [Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.erase_single, Finsupp.erase_single_ne]

private theorem source_coefficients (R : ℕ → MvPolynomial ℕ ℝ) (hR : IsSourceSequence R) :
    coefficientForm R 6 = -210*MvPolynomial.X 3*MvPolynomial.X 5 - 140*MvPolynomial.X 4^2 ∧
    coefficientForm R 8 = -504*MvPolynomial.X 3*MvPolynomial.X 7 - 1008*MvPolynomial.X 4*MvPolynomial.X 6 - 630*MvPolynomial.X 5^2 ∧
    coefficientForm R 10 = -990*MvPolynomial.X 3*MvPolynomial.X 9 - 2640*MvPolynomial.X 4*MvPolynomial.X 8 - 4620*MvPolynomial.X 5*MvPolynomial.X 7 - 2772*MvPolynomial.X 6^2 := by
  obtain ⟨h7,h9,h11⟩ := sequence_values R hR
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [coefficientForm, h7, h9, h11, coefficient6, coefficient8, coefficient10] <;>
    norm_num [map_ofNat, map_neg] <;> ring


private theorem counterexample (R : ℕ → MvPolynomial ℕ ℝ) (hR : IsSourceSequence R) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ SMD μ ∧
      0 < cumulant μ 2 ∧ 0 < cumulant μ 4 ∧ 0 < cumulant μ 6 ∧ cumulant μ 8 < 0 ∧
      MvPolynomial.eval (cumulant μ) (coefficientForm R 6) < 0 ∧
      MvPolynomial.eval (cumulant μ) (coefficientForm R 8) < 0 ∧
      MvPolynomial.eval (cumulant μ) (coefficientForm R 10) = 0 := by
  obtain ⟨p,ha,hb,hz⟩ := root_exists
  have hp : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 := by linarith
  obtain ⟨h2,h3,h4,h5,h6,h8⟩ := law_cumulants hp hp1
  obtain ⟨s2,s4,s6,s8⟩ := root_signs ha hb hz
  obtain ⟨c6,c8,c10⟩ := source_coefficients R hR
  have e6 : MvPolynomial.eval (cumulant (law p)) (coefficientForm R 6) =
      -140*(p-3*p^2)^2 := by
    rw [c6]
    norm_num [h3,h4]
  have e8 : MvPolynomial.eval (cumulant (law p)) (coefficientForm R 8) =
      -1008*(p-3*p^2)*(p-15*p^2+30*p^3) := by
    rw [c8]
    norm_num [h3,h4,h5,h6]
  have e10 : MvPolynomial.eval (cumulant (law p)) (coefficientForm R 10) =
      -132*(21*(p-15*p^2+30*p^3)^2 +
        20*(p-3*p^2)*(p-63*p^2+420*p^3-630*p^4)) := by
    rw [c10]
    norm_num [h3,h4,h5,h6,h8]
    ring
  refine ⟨law p,law_probability hp hp1,law_SMD hp hp1,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [h2] using s2
  · simpa only [h4] using s4
  · simpa only [h6] using s6
  · simpa only [h8] using s8
  · rw [e6]; nlinarith [sq_pos_of_pos s4]
  · rw [e8]; nlinarith [mul_pos s4 s6]
  · rw [e10,root_cancellation hz,mul_zero]

end D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation.MPSProbe

namespace D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation

theorem result : ¬ D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation.claim := by
  intro h
  obtain ⟨R,hR⟩ := h.1
  obtain ⟨μ,hprob,hsmd,_,_,_,_,_,_,hz⟩ := MPSProbe.counterexample R hR
  exact (h.2 R hR μ hprob hsmd 5 (by norm_num)) hz


end D5.S3.Analytic.MomentMinors.MansanarezPolySwanCumulantNonvanishingRefutation
