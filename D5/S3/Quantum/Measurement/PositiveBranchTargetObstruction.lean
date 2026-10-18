/- GID: D5/S3/Quantum/Measurement/PositiveBranchTargetObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PositiveBranchTargetObstruction
   mirror-E: none(waiver:analytic-response-obstruction)
   anchors: []
   utility: none
   digest: Globally nonnegative bounded-degree probability responses cannot approach a negative analytic continuation. -/

import D5.S3.Quantum.Measurement.PositiveBranchRealRationalResponse
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Analytic continuation and compact coefficient pairs for probability responses. -/
noncomputable section
open Filter Topology Set Polynomial
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
set_option autoImplicit false

private theorem polynomial_zero_on_interval (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (hp : ∀ t ∈ Ioo a b, p.eval t = 0) : p = 0 := by
  apply p.eq_of_infinite_eval_eq 0
  exact (Set.Ioo_infinite hab).mono (fun t ht => by simpa using hp t ht)

private theorem analytic_polynomial_identity
    (f : ℝ → ℝ) (a b R : ℝ) (ha : 0 < a) (hab : a < b) (hbR : b ≤ R)
    (hf : AnalyticOnNhd ℝ f (Ioo 0 R)) (p q : ℝ[X])
    (heq : ∀ t ∈ Ioo a b, p.eval t = f t * q.eval t) :
    ∀ t ∈ Ioo 0 R, p.eval t = f t * q.eval t := by
  have hp : AnalyticOnNhd ℝ (fun t => p.eval t) (Ioo 0 R) :=
    (analyticOnNhd_id.aeval_polynomial p).mono (subset_univ _)
  have hq : AnalyticOnNhd ℝ (fun t => q.eval t) (Ioo 0 R) :=
    (analyticOnNhd_id.aeval_polynomial q).mono (subset_univ _)
  have hm : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  apply hp.eqOn_of_preconnected_of_eventuallyEq (hf.mul hq) isPreconnected_Ioo
    (show (a + b) / 2 ∈ Ioo 0 R by constructor <;> linarith [hm.1, hm.2])
  filter_upwards [isOpen_Ioo.mem_nhds hm] with t ht
  exact heq t ht

private theorem analytic_sign_obstruction
    (f : ℝ → ℝ) (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (hbR : b ≤ R) (hR : R ≤ 1)
    (hf : AnalyticOnNhd ℝ f (Ioo 0 R))
    (hneg : ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < R ∧ ∀ t ∈ Ioo l r, f t < 0)
    (p q : ℝ[X]) (hq : q ≠ 0)
    (hsign : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ p.eval t * q.eval t) :
    ¬ (∀ t ∈ Ioo a b, p.eval t = f t * q.eval t) := by
  intro heq
  have hid := analytic_polynomial_identity f a b R ha hab hbR hf p q heq
  obtain ⟨l, r, hl, hlr, hrb, hfn⟩ := hneg
  have hex : ∃ t ∈ Ioo l r, q.eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (polynomial_zero_on_interval q hlr h)
  obtain ⟨t, ht, hqt⟩ := hex
  have hz := hsign t ⟨hl.trans ht.1, ht.2.trans_le (hrb.le.trans hR)⟩
  rw [hid t ⟨hl.trans ht.1, ht.2.trans hrb⟩] at hz
  have hn := hfn t ht
  nlinarith [sq_pos_of_ne_zero hqt]

private abbrev Coefficients (M : ℕ) := Fin (M + 1) → ℝ
private abbrev CoefficientPair (M : ℕ) := Coefficients M × Coefficients M

private def coefficientEvaluation (M : ℕ) (t : ℝ) : Coefficients M →ₗ[ℝ] ℝ where
  toFun v := (Polynomial.ofFn (M + 1) v).eval t
  map_add' v w := by simp
  map_smul' r v := by simp

private theorem coefficientEvaluation_bound (M : ℕ) (v : Coefficients M)
    (hv : ‖v‖ ≤ 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |coefficientEvaluation M t v| ≤ M + 1 := by
  change |(Polynomial.ofFn (M + 1) v).eval t| ≤ _
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  calc
    |∑ i : Fin (M + 1), (monomial (i : ℕ) (v i)).eval t| ≤
        ∑ i : Fin (M + 1), |(monomial (i : ℕ) (v i)).eval t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (M + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.eval_monomial, abs_mul, abs_of_nonneg (pow_nonneg ht.1 _)]
      have hi : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
      exact mul_le_one₀ hi (pow_nonneg ht.1 _) (pow_le_one₀ ht.1 ht.2)
    _ = M + 1 := by simp

private def normalizedPairs (M : ℕ) : Set (CoefficientPair M) :=
  {x | ‖x‖ = 1 ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
    |coefficientEvaluation M t x.1| ≤ |coefficientEvaluation M t x.2| ∧
      0 ≤ coefficientEvaluation M t x.1 * coefficientEvaluation M t x.2}

private theorem normalizedPairs_compact (M : ℕ) : IsCompact (normalizedPairs M) := by
  have hc : IsClosed {x : CoefficientPair M | ∀ t ∈ Ioo (0 : ℝ) 1,
      |coefficientEvaluation M t x.1| ≤ |coefficientEvaluation M t x.2| ∧
        0 ≤ coefficientEvaluation M t x.1 * coefficientEvaluation M t x.2} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _
    have hp := (coefficientEvaluation M t).continuous_of_finiteDimensional.comp (continuous_fst : Continuous (fun x : CoefficientPair M => x.1))
    have hq := (coefficientEvaluation M t).continuous_of_finiteDimensional.comp (continuous_snd : Continuous (fun x : CoefficientPair M => x.2))
    exact (isClosed_le hp.abs hq.abs).inter (isClosed_le continuous_const (hp.mul hq))
  convert (isCompact_sphere (0 : CoefficientPair M) 1).inter_right hc using 1
  ext x
  simp [normalizedPairs, Metric.mem_sphere, dist_zero_right]

private def intervalResidual (M : ℕ) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    CoefficientPair M →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun x := ⟨fun t => coefficientEvaluation M t x.1 - f t * coefficientEvaluation M t x.2,
    ((Polynomial.continuous _).comp continuous_subtype_val).sub
      (hf.restrict.mul ((Polynomial.continuous _).comp continuous_subtype_val))⟩
  map_add' x y := by
    ext t
    change coefficientEvaluation M t (x + y).1 - f t * coefficientEvaluation M t (x + y).2 =
      (coefficientEvaluation M t x.1 - f t * coefficientEvaluation M t x.2) +
        (coefficientEvaluation M t y.1 - f t * coefficientEvaluation M t y.2)
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' r x := by
    ext t
    change coefficientEvaluation M t (r • x).1 - f t * coefficientEvaluation M t (r • x).2 =
      r * (coefficientEvaluation M t x.1 - f t * coefficientEvaluation M t x.2)
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
    ring

private theorem residual_positive (M : ℕ) (f : ℝ → ℝ) (a b R : ℝ)
    (ha : 0 < a) (hab : a < b) (hbR : b < R) (hR : R ≤ 1)
    (hf : AnalyticOnNhd ℝ f (Ioo 0 R))
    (hneg : ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < R ∧ ∀ t ∈ Ioo l r, f t < 0)
    (hfc : ContinuousOn f (Icc a b)) (x : CoefficientPair M)
    (hx : x ∈ normalizedPairs M) : 0 < ‖intervalResidual M f a b hfc x‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hq : Polynomial.ofFn (M + 1) x.2 ≠ 0 := by
    intro hq
    have hp : Polynomial.ofFn (M + 1) x.1 = 0 := by
      apply polynomial_zero_on_interval _ (by norm_num : (0 : ℝ) < 1)
      intro t ht
      have h := (hx.2 t ht).1
      change |(Polynomial.ofFn (M + 1) x.1).eval t| ≤
        |(Polynomial.ofFn (M + 1) x.2).eval t| at h
      rw [hq, eval_zero, abs_zero] at h
      exact abs_nonpos_iff.mp h
    have hx₁ : x.1 = 0 := (Polynomial.injective_ofFn _)
      (hp.trans (map_zero _).symm)
    have hx₂ : x.2 = 0 := (Polynomial.injective_ofFn _)
      (hq.trans (map_zero _).symm)
    have hxzero : x = 0 := Prod.ext hx₁ hx₂
    have hh := hx.1
    simp only [hxzero, norm_zero, zero_ne_one] at hh
  apply analytic_sign_obstruction f a b R ha hab hbR.le hR hf hneg _ _ hq
    (fun t ht => (hx.2 t ht).2)
  intro t ht
  have h := congrArg (fun g : C(Icc a b, ℝ) => g ⟨t, ht.1.le, ht.2.le⟩) hz
  exact sub_eq_zero.mp h

/-- A degree bound together with probability legality on the whole internal
source interval forces a positive uniform separation from an analytic target
whose continuation is negative. The coefficient set is compact after one
common normalization of numerator and denominator. -/
private theorem fixed_degree_probability_gap (M : ℕ) (f : ℝ → ℝ) (a b R : ℝ)
    (ha : 0 < a) (hab : a < b) (hbR : b < R) (hR : R ≤ 1)
    (hf : AnalyticOnNhd ℝ f (Ioo 0 R))
    (hneg : ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < R ∧ ∀ t ∈ Ioo l r, f t < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p q : ℝ[X]), p.natDegree ≤ M → q.natDegree ≤ M → q ≠ 0 →
      (∀ t ∈ Ioo (0 : ℝ) 1, |p.eval t| ≤ |q.eval t| ∧ 0 ≤ p.eval t * q.eval t) →
      ∀ ε : ℝ, 0 ≤ ε →
        (∀ t ∈ Icc a b, |p.eval t - f t * q.eval t| ≤ ε * |q.eval t|) → δ ≤ ε := by
  have hsub : Icc a b ⊆ Ioo 0 R := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hbR⟩
  have hfc := hf.continuousOn.mono hsub
  let L := intervalResidual M f a b hfc
  obtain ⟨δ, hδ, hmin⟩ := (normalizedPairs_compact M).exists_forall_le'
    L.continuous_of_finiteDimensional.norm.continuousOn
    (residual_positive M f a b R ha hab hbR hR hf hneg hfc)
  refine ⟨δ / (M + 1), div_pos hδ (by positivity), ?_⟩
  intro p q hp hq hqne hlegal ε hε herr
  let u : CoefficientPair M := (Polynomial.toFn (M + 1) p, Polynomial.toFn (M + 1) q)
  have hpback := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : p.natDegree < M + 1)
  have hqback := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : q.natDegree < M + 1)
  have hun : u ≠ 0 := by
    intro hu
    apply hqne
    have h := congrArg Prod.snd hu
    change Polynomial.toFn (M + 1) q = 0 at h
    simpa only [h, map_zero] using hqback.symm
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hun
  let x : CoefficientPair M := ‖u‖⁻¹ • u
  have hpoly₁ : Polynomial.ofFn (M + 1) x.1 = ‖u‖⁻¹ • p := by
    change Polynomial.ofFn (M + 1) (‖u‖⁻¹ • Polynomial.toFn (M + 1) p) = _
    rw [map_smul, hpback]
  have hpoly₂ : Polynomial.ofFn (M + 1) x.2 = ‖u‖⁻¹ • q := by
    change Polynomial.ofFn (M + 1) (‖u‖⁻¹ • Polynomial.toFn (M + 1) q) = _
    rw [map_smul, hqback]
  have heval₁ (t : ℝ) : coefficientEvaluation M t x.1 = ‖u‖⁻¹ * p.eval t := by
    change (Polynomial.ofFn (M + 1) x.1).eval t = _
    rw [hpoly₁, Polynomial.eval_smul, smul_eq_mul]
  have heval₂ (t : ℝ) : coefficientEvaluation M t x.2 = ‖u‖⁻¹ * q.eval t := by
    change (Polynomial.ofFn (M + 1) x.2).eval t = _
    rw [hpoly₂, Polynomial.eval_smul, smul_eq_mul]
  have hx : x ∈ normalizedPairs M := by
    refine ⟨?_, ?_⟩
    · dsimp only [x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    · intro t ht
      rw [heval₁, heval₂, abs_mul, abs_mul]
      refine ⟨mul_le_mul_of_nonneg_left (hlegal t ht).1 (abs_nonneg _), ?_⟩
      nlinarith [sq_nonneg ‖u‖⁻¹, (hlegal t ht).2]
  have hupper : ‖L x‖ ≤ ε * (M + 1) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hε (by positivity))).mpr
    intro t
    change |coefficientEvaluation M t x.1 - f t * coefficientEvaluation M t x.2| ≤ _
    have hres : |coefficientEvaluation M t x.1 - f t * coefficientEvaluation M t x.2| ≤
        ε * |coefficientEvaluation M t x.2| := by
      rw [heval₁, heval₂]
      have heq : ‖u‖⁻¹ * p.eval (t : ℝ) - f t * (‖u‖⁻¹ * q.eval (t : ℝ)) =
          ‖u‖⁻¹ * (p.eval (t : ℝ) - f t * q.eval (t : ℝ)) := by ring
      rw [heq, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (herr t t.property) (abs_nonneg ‖u‖⁻¹)]
    have hb := coefficientEvaluation_bound M x.2
      ((norm_snd_le x).trans_eq hx.1) t
      ⟨(ha.trans_le t.property.1).le, (t.property.2.trans hbR.le).trans hR⟩
    exact hres.trans (mul_le_mul_of_nonneg_left hb hε)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
    ((hmin x hx).trans hupper)

/-- The target singleton probability on the legal diagonal source family. -/
def targetCell (B C β t : ℝ) : ℝ := t / 2 - (C * (1 - B * t)) ^ β / 16

private theorem targetCell_analytic (B C β : ℝ) (hB : 0 < B) (hC : 0 < C) :
    AnalyticOnNhd ℝ (targetCell B C β) (Ioo 0 (1 / B)) := by
  intro t ht
  have hbase : 0 < C * (1 - B * t) := by
    have := (lt_div_iff₀ hB).mp ht.2
    exact mul_pos hC (by nlinarith)
  have hg : AnalyticAt ℝ (fun s : ℝ => C * (1 - B * s)) t := by
    fun_prop
  have hp : AnalyticAt ℝ (fun s : ℝ => (C * (1 - B * s)) ^ β) t := by
    have h := ((hg.log hbase).mul (analyticAt_const (v := β))).rexp
    apply h.congr
    filter_upwards [(hg.continuousAt.eventually (lt_mem_nhds hbase))] with s hs
    exact (Real.rpow_def_of_pos hs _).symm
  exact (analyticAt_id.div_const).sub (hp.div_const)

private theorem targetCell_negative_interval (B C β : ℝ)
    (hB : 0 < B) (hC : 0 < C) :
    ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < 1 / B ∧
      ∀ t ∈ Ioo l r, targetCell B C β t < 0 := by
  have hval : targetCell B C β 0 < 0 := by
    simp only [targetCell, zero_div, mul_zero, sub_zero, mul_one, zero_sub]
    exact neg_lt_zero.mpr (div_pos (Real.rpow_pos_of_pos hC β) (by norm_num))
  have hc : ContinuousAt (targetCell B C β) 0 := by
    have hg : ContinuousAt (fun t : ℝ => C * (1 - B * t)) 0 := by fun_prop
    have hp := hg.rpow_const (p := β) (Or.inl (by simpa using hC.ne'))
    exact (continuousAt_id.div_const 2).sub (hp.div_const 16)
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (gt_mem_nhds hval))
  let r := min δ (1 / B) / 2
  have hr : 0 < r := half_pos (lt_min hδ (one_div_pos.mpr hB))
  refine ⟨r / 2, r, half_pos hr, by linarith, ?_, ?_⟩
  · dsimp [r]
    linarith [min_le_right δ (1 / B), one_div_pos.mpr hB]
  · intro t ht
    apply hδf
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_trans (half_pos hr) ht.1)]
    exact ht.2.trans (by dsimp [r]; linarith [min_le_left δ (1 / B)])


/-- The five source weights allowed by a single fresh classical coin read. -/
inductive SourceWeight where
  | fixed | first | firstFailure | second | secondFailure
  deriving DecidableEq

def SourceWeight.value : SourceWeight → ℝ → ℝ → ℝ
  | .fixed, _, _ => 1
  | .first, p, _ => p
  | .firstFailure, p, _ => 1 - p
  | .second, _, q => q
  | .secondFailure, _, q => 1 - q

def SourceWeight.intercept : SourceWeight → ℝ
  | .fixed | .firstFailure | .secondFailure => 1
  | .first | .second => 0

def SourceWeight.slope : SourceWeight → ℝ
  | .fixed => 0
  | .first | .second => 1
  | .firstFailure | .secondFailure => -1

private theorem sourceWeight_diagonal (s : SourceWeight) (t : ℝ) :
    s.value t t = s.intercept + t * s.slope := by
  cases s <;> simp [SourceWeight.value, SourceWeight.intercept, SourceWeight.slope] <;> ring

private theorem sourceWeight_positive (s : SourceWeight) (p q : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) : 0 < s.value p q := by
  cases s <;> simp only [SourceWeight.value] <;> linarith [hp.1, hp.2, hq.1, hq.2]

/-- A fixed finite dimensional two-source instrument. Kraus operators, terminal
 effects and initial masses are independent of the source rates. Instrument
 completeness holds on the entire internal source square. Only one terminating
 diagonal initial-state experiment is required. -/
structure FourCellSourceInstrument (d : ℕ) where
  branches : ℕ
  groups : ℕ
  kraus : Fin branches → Matrix (Fin d) (Fin d) ℂ
  group : Fin branches → Fin groups
  source : Fin groups → SourceWeight
  effect : (Bool × Bool) → Fin branches → Matrix (Fin d) (Fin d) ℂ
  effect_nonneg : ∀ o a, 0 ≤ effect o a
  initial : Matrix (Fin d) (Fin d) ℂ
  initial_psd : initial.PosSemidef
  initialReturn : (Bool × Bool) → ℝ
  initialReturn_nonneg : ∀ o, 0 ≤ initialReturn o
  mass : initial.trace.re + ∑ o, initialReturn o = 1
  complete : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ q ∈ Ioo (0 : ℝ) 1,
    weightedDual kraus (fun a => (source (group a)).value p q) 1 +
      ∑ a, ((source (group a)).value p q : ℂ) • (∑ o, effect o a) = 1
  terminating : ∃ t₀ ∈ Ioo (0 : ℝ) 1,
    Tendsto (fun n => ((weightedCP kraus
      (fun a => (source (group a)).value t₀ t₀))^[n] initial).trace) atTop (𝓝 0)

/-- Actual eventual four-cell response, including any initial return. -/
def FourCellSourceInstrument.response {d : ℕ} (A : FourCellSourceInstrument d)
    (o : Bool × Bool) (p q : ℝ) : ℝ :=
  actualEventResponse A.kraus A.group A.initial (A.effect o) (A.initialReturn o)
    (fun j => (A.source j).value p q)

private theorem instrument_diagonal_rational {d : ℕ} (A : FourCellSourceInstrument d)
    (o : Bool × Bool) :
    ∃ P Q : ℝ[X], P.natDegree ≤ d ^ 2 ∧ Q.natDegree ≤ d ^ 2 ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, Q.eval t ≠ 0 ∧
        A.response o t t = P.eval t / Q.eval t ∧
        0 ≤ A.response o t t ∧ A.response o t t ≤ 1 := by
  let E : Fin A.branches → Matrix (Fin d) (Fin d) ℂ := fun a => ∑ o, A.effect o a
  have hE (a) : (E a).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun o _ => A.effect_nonneg o a)
  have hFE (a) : A.effect o a ≤ E a :=
    Finset.single_le_sum (fun o _ => A.effect_nonneg o a) (Finset.mem_univ o)
  have hmass : A.initialReturn o + A.initial.trace.re ≤ 1 := by
    have hsingle : A.initialReturn o ≤ ∑ o, A.initialReturn o :=
      Finset.single_le_sum (fun o _ => A.initialReturn_nonneg o) (Finset.mem_univ o)
    linarith [A.mass]
  obtain ⟨t₀, ht₀, hterm⟩ := A.terminating
  let w : ℝ → Fin A.groups → ℝ := fun t j => (A.source j).value t t
  have hc (j) : ContinuousOn (fun t => w t j) (Ioo (0 : ℝ) 1) := by
    have heq : (fun t => w t j) = fun t => (A.source j).intercept + t * (A.source j).slope :=
      funext (sourceWeight_diagonal (A.source j))
    rw [heq]
    fun_prop
  obtain ⟨hdim, P, Q, hP, hQ, hresp, _, _⟩ :=
    affine_source_real_rational_response A.kraus E hE A.group w (Ioo (0 : ℝ) 1)
      (fun t ht j => sourceWeight_positive (A.source j) t t ht ht) hc
      (fun t ht => A.complete t ht t ht) t₀ ht₀ A.initial A.initial_psd hterm
      (A.effect o) (A.effect_nonneg o) hFE (A.initialReturn o)
      (A.initialReturn_nonneg o) hmass id
      (fun j => (A.source j).intercept) (fun j => (A.source j).slope)
      (Ioo (0 : ℝ) 1) isOpen_Ioo (fun _ ht => ht)
      (fun t _ => funext (fun j => sourceWeight_diagonal (A.source j) t))
  refine ⟨P, Q, hP.trans (hdim.1.trans hdim.2), hQ.trans (hdim.1.trans hdim.2), ?_⟩
  intro t ht
  exact ⟨(hresp t ht).1, (hresp t ht).2.2⟩

/-- The requested diagonal-source four-cell law. -/
def targetFourCell (B C β h : ℝ) (o : Bool × Bool) : ℝ :=
  (if o.1 then (1 - h / C) / B else 1 - (1 - h / C) / B) / 2 +
    (if o.1 = o.2 then h ^ β / 16 else -(h ^ β / 16))

/-- Total variation of the complete returned four-cell law on the legal
 diagonal source subfamily. -/
def fourCellTV {d : ℕ} (A : FourCellSourceInstrument d) (B C β h : ℝ) : ℝ :=
  (∑ o, |A.response o ((1 - h / C) / B) ((1 - h / C) / B) -
    targetFourCell B C β h o|) / 2

private theorem cell_error_le_twice_tv {d : ℕ} (A : FourCellSourceInstrument d)
    (B C β h : ℝ) (o : Bool × Bool) :
    |A.response o ((1 - h / C) / B) ((1 - h / C) / B) - targetFourCell B C β h o| ≤
      2 * fourCellTV A B C β h := by
  have hs := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun o => |A.response o ((1 - h / C) / B) ((1 - h / C) / B) -
      targetFourCell B C β h o|)
    (fun o _ => abs_nonneg _) (Finset.mem_univ o)
  dsimp [fourCellTV]
  linarith


private theorem legal_source_interval (B C : ℝ) (hB : 0 < B) (hC : 1 ≤ C) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 / B ∧
      ∀ t ∈ Icc a b, C * (1 - B * t) ∈ Ioc (0 : ℝ) (1 / 4) := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let a := (1 - (1 / 8 : ℝ) / C) / B
  let b := (1 - (1 / 16 : ℝ) / C) / B
  have ha : 0 < a := div_pos
    (sub_pos.mpr ((div_lt_one hCp).mpr (by linarith))) hB
  have hab : a < b := by
    apply (div_lt_div_iff_of_pos_right hB).mpr
    have := div_lt_div_of_pos_right (by norm_num : (1 / 16 : ℝ) < 1 / 8) hCp
    linarith
  have hb : b < 1 / B := by
    apply (div_lt_div_iff_of_pos_right hB).mpr
    have := div_pos (by norm_num : (0 : ℝ) < 1 / 16) hCp
    linarith
  have hia : C * (1 - B * a) = 1 / 8 := by
    dsimp [a]
    field_simp [ne_of_gt hB, ne_of_gt hCp]
    <;> ring
  have hib : C * (1 - B * b) = 1 / 16 := by
    dsimp [b]
    field_simp [ne_of_gt hB, ne_of_gt hCp]
    <;> ring
  refine ⟨a, b, ha, hab, hb, ?_⟩
  intro t ht
  have hu : C * (1 - B * t) ≤ 1 / 8 := by
    rw [← hia]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (mul_le_mul_of_nonneg_left ht.1 hB.le) 1) hCp.le
  have hl : 1 / 16 ≤ C * (1 - B * t) := by
    rw [← hib]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (mul_le_mul_of_nonneg_left ht.2 hB.le) 1) hCp.le
  constructor <;> linarith

private theorem source_target_uniform_gap (B C β : ℝ) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e ≤ d, ∀ A : FourCellSourceInstrument e,
      ∀ ε : ℝ, 0 ≤ ε →
        (∀ h ∈ Ioc (0 : ℝ) (1 / 4), fourCellTV A B C β h ≤ ε) → δ ≤ ε := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨a, b, ha, hab, hb, hlegal⟩ := legal_source_interval B C hBp hC
  obtain ⟨δ, hδ, hsep⟩ := fixed_degree_probability_gap (d ^ 2)
    (targetCell B C β) a b (1 / B) ha hab hb ((div_le_one hBp).mpr hB)
    (targetCell_analytic B C β hBp hCp) (targetCell_negative_interval B C β hBp hCp)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro e hed A ε hε herr
  obtain ⟨P, Q, hP, hQ, hresponse⟩ := instrument_diagonal_rational A (true, false)
  have hqne : Q ≠ 0 := by
    intro hz
    have h := (hresponse (1 / 2) (by norm_num)).1
    simp [hz] at h
  have hdim : e ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hed 2
  have hpq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      P.eval t = A.response (true, false) t t * Q.eval t :=
    ((eq_div_iff (hresponse t ht).1).mp (hresponse t ht).2.1).symm
  have hprob (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      |P.eval t| ≤ |Q.eval t| ∧ 0 ≤ P.eval t * Q.eval t := by
    have hlo := (hresponse t ht).2.2.1
    have hhi := (hresponse t ht).2.2.2
    rw [hpq t ht, abs_mul, abs_of_nonneg hlo]
    refine ⟨mul_le_of_le_one_left (abs_nonneg _) hhi, ?_⟩
    nlinarith [mul_nonneg hlo (sq_nonneg (Q.eval t))]
  have hcross (t : ℝ) (ht : t ∈ Icc a b) :
      |P.eval t - targetCell B C β t * Q.eval t| ≤ (2 * ε) * |Q.eval t| := by
    have htU : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha.trans_le ht.1, (ht.2.trans_lt hb).trans_le ((div_le_one hBp).mpr hB)⟩
    let h := C * (1 - B * t)
    have hh : h ∈ Ioc (0 : ℝ) (1 / 4) := hlegal t ht
    have hback : (1 - h / C) / B = t := by
      dsimp [h]
      field_simp [ne_of_gt hBp, ne_of_gt hCp]
      <;> ring
    have htarget : targetFourCell B C β h (true, false) = targetCell B C β t := by
      simp only [targetFourCell, Bool.true_eq_false, if_false, if_true, hback, targetCell]
      rfl
    have he := (cell_error_le_twice_tv A B C β h (true, false)).trans
      (mul_le_mul_of_nonneg_left (herr h hh) (by norm_num : (0 : ℝ) ≤ 2))
    rw [hback, htarget] at he
    rw [hpq t htU]
    have hid : A.response (true, false) t t * Q.eval t -
        targetCell B C β t * Q.eval t =
        (A.response (true, false) t t - targetCell B C β t) * Q.eval t := by ring
    rw [hid, abs_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  have hs := hsep P Q (hP.trans hdim) (hQ.trans hdim) hqne hprob (2 * ε)
    (mul_nonneg (by norm_num) hε) hcross
  linarith

private theorem source_target_witness_gap (B C β : ℝ) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e ≤ d, ∀ A : FourCellSourceInstrument e,
      ∃ h ∈ Ioc (0 : ℝ) (1 / 4), δ ≤ fourCellTV A B C β h := by
  obtain ⟨δ, hδ, hbound⟩ := source_target_uniform_gap B C β hB hC d
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro e he A
  by_contra h
  push_neg at h
  have hh := hbound e he A (δ / 2) (half_pos hδ).le
    (fun t ht => (h t ht).le)
  linarith

/-- Every fixed finite source instrument fails the exact full four-cell target.
For each Hilbert dimension bound there is a positive uniform total-variation
separation, already witnessed by a legal diagonal-source world. The conclusion
includes every positive real exponent and asserts no quantitative rate. -/
theorem finite_quantum_target_obstruction (B C β : ℝ)
    (hB : B = 2 ∨ B = 4) (hC : 1 ≤ C ∧ C ≤ 1024 / 225) (_hβ : 0 < β) :
    (∀ d : ℕ, ∀ A : FourCellSourceInstrument d,
      ¬ (∀ h ∈ Ioc (0 : ℝ) (1 / 4), ∀ o : Bool × Bool,
        A.response o ((1 - h / C) / B) ((1 - h / C) / B) = targetFourCell B C β h o)) ∧
    ∀ d : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ e ≤ d, ∀ A : FourCellSourceInstrument e,
        ∃ h ∈ Ioc (0 : ℝ) (1 / 4), ε ≤ fourCellTV A B C β h := by
  have hB1 : 1 ≤ B := by rcases hB with rfl | rfl <;> norm_num
  have hg := source_target_witness_gap B C β hB1 hC.1
  refine ⟨?_, hg⟩
  intro d A hexact
  obtain ⟨ε, hε, hgap⟩ := hg d
  obtain ⟨h, hh, hlarge⟩ := hgap d le_rfl A
  have hz : fourCellTV A B C β h = 0 := by
    simp only [fourCellTV, hexact h hh, sub_self, abs_zero, Finset.sum_const_zero, zero_div]
  rw [hz] at hlarge
  exact (not_le_of_gt hε) hlarge

#print axioms finite_quantum_target_obstruction
end D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
