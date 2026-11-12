/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal renewal PMFs and the complete finite original joint execution law. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ENNReal BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws
open CriticalRenewalSource

/-- The two literal public shapes at the same parameter. -/
def shape (i : Bool) (x : ℝ) : ℝ :=
  x^9 + if i then
    (55800726477138*x - 224986136658885*x^2 + 420664314485485*x^3 -
      540138133491075*x^4 + 518234977000797*x^5 - 254383031435085*x^6 +
      77668004560980*x^7 + 43377331415040*x^8) / (35*10^24) else 0

def weight (q : ℝ) (i : Bool) (k : ℕ) : ℝ :=
  if k = 0 then 0 else shape i k * q^k

def normalizer (q : ℝ) (i : Bool) : ℝ := ∑' k, weight q i k

def density (q : ℝ) (i : Bool) (k : ℕ) : ℝ := weight q i k / normalizer q i

/-- K counts zeros; the intertick length is K+1. -/
def mean (q : ℝ) (i : Bool) : ℝ := ∑' k : ℕ, (k+1 : ℝ) * density q i k

def tail (q : ℝ) (i : Bool) (u : ℕ) : ℝ :=
  ∑' k : ℕ, if u ≤ k then density q i k else 0

def equilibrium (q : ℝ) (i : Bool) (u : ℕ) : ℝ := tail q i u / mean q i

private theorem shape_positive (i : Bool) {x : ℝ} (hx : 1 ≤ x) : 0 < shape i x := by
  have hx0 : 0 ≤ x := by linarith
  have h9 : 0 < x^9 := pow_pos (by linarith) _
  have h2 : x^2 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  have h4 : x^4 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  have h6 : x^6 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  cases i
  · simpa [shape] using h9
  · have hp : 0 ≤ 55800726477138*x + 420664314485485*x^3 +
        518234977000797*x^5 + 77668004560980*x^7 + 43377331415040*x^8 := by positivity
    simp only [shape, Bool.true_eq, ↓reduceIte]
    norm_num only [Nat.reducePow, Nat.reduceMul]
    linarith

private theorem weight_nonnegative {q : ℝ} (hq : 0 < q) (i : Bool) (k : ℕ) :
    0 ≤ weight q i k := by
  by_cases hk : k = 0
  · simp [weight, hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    simpa only [weight, hk, ↓reduceIte] using
      (mul_pos (shape_positive i hk1) (pow_pos hq k)).le

private theorem weighted_summable {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (p : ℕ) : Summable fun k : ℕ => (k : ℝ)^p * weight q i k := by
  have hs : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have ht (m : ℕ) : Summable (fun k : ℕ =>
      if k = 0 then (0 : ℝ) else (k : ℝ)^m * q^k) := by
    convert summable_term m hs using 1
    funext k
    simp only [term, neg_neg, mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log hq]
  have he (m k : ℕ) : (k : ℝ)^p *
      (if k = 0 then (0 : ℝ) else (k : ℝ)^m * q^k) =
      if k = 0 then 0 else (k : ℝ)^(p+m) * q^k := by
    split_ifs <;> simp [pow_add, mul_assoc]
  cases i
  · simpa only [weight, shape, Bool.false_eq_true, ↓reduceIte, add_zero,
      mul_ite, mul_zero, ← he] using ht (p+9)
  · have h1 := ((ht (p+1)).mul_left 55800726477138).sub
        ((ht (p+2)).mul_left 224986136658885)
    have h2 := h1.add ((ht (p+3)).mul_left 420664314485485)
    have h3 := h2.sub ((ht (p+4)).mul_left 540138133491075)
    have h4 := h3.add ((ht (p+5)).mul_left 518234977000797)
    have h5 := h4.sub ((ht (p+6)).mul_left 254383031435085)
    have h6 := h5.add ((ht (p+7)).mul_left 77668004560980)
    have h7 := h6.add ((ht (p+8)).mul_left 43377331415040)
    have hh := (ht (p+9)).add (h7.div_const (35*10^24))
    convert hh using 1
    funext k
    by_cases hk : k = 0
    · simp [weight, hk]
    · simp only [weight, shape, hk, ↓reduceIte, pow_add]
      ring

private theorem normalizer_positive {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    0 < normalizer q i := by
  apply (show Summable (weight q i) by simpa using weighted_summable hq hq1 i 0).tsum_pos
    (weight_nonnegative hq i) 1
  simp only [weight, one_ne_zero, ↓reduceIte, Nat.cast_one, pow_one]
  exact mul_pos (shape_positive i le_rfl) hq

private theorem density_summable {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (p : ℕ) : Summable fun k : ℕ => (k : ℝ)^p * density q i k := by
  simpa only [density, mul_div_assoc] using (weighted_summable hq hq1 i p).div_const _

private theorem density_nonnegative {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (k : ℕ) : 0 ≤ density q i k :=
  div_nonneg (weight_nonnegative hq i k) (normalizer_positive hq hq1 i).le

private theorem density_mass {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    ∑' k, density q i k = 1 := by
  simp only [density, tsum_div_const]
  exact div_self (normalizer_positive hq hq1 i).ne'

private theorem mean_positive {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    0 < mean q i := by
  have he : mean q i = (∑' k : ℕ, (k : ℝ) * density q i k) + 1 := by
    simp only [mean, add_mul, one_mul]
    rw [Summable.tsum_add (by simpa using density_summable hq hq1 i 1)
      (by simpa using density_summable hq hq1 i 0), density_mass hq hq1 i]
  rw [he]
  exact add_pos_of_nonneg_of_pos (tsum_nonneg fun k =>
    mul_nonneg (Nat.cast_nonneg _) (density_nonnegative hq hq1 i k)) zero_lt_one

private theorem tail_mass {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    Summable (tail q i) ∧ ∑' u, tail q i u = mean q i := by
  have hs : Summable fun k : ℕ => ((k : ℝ)+1) * density q i k := by
    simpa only [add_mul, one_mul, pow_one, pow_zero] using
      (density_summable hq hq1 i 1).add (density_summable hq hq1 i 0)
  have h := weighted_tails (density q i) (density_nonnegative hq hq1 i) 0
    (by simpa using hs)
  change Summable (fun u => ∑' k, if u ≤ k then density q i k else 0) ∧ _
  simpa only [pow_zero, one_mul, mul_one, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mean, tail] using h

/-- Exact positive-gap law for the literal degree-nine shape. -/
def gapLaw (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : Bool) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (density q i k), by
    have h := ENNReal.ofReal_tsum_of_nonneg (density_nonnegative hq hq1 i)
      (by simpa using density_summable hq hq1 i 0)
    rw [density_mass hq hq1 i, ENNReal.ofReal_one] at h
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The original stationary first wait includes the value zero. -/
def waitLaw (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : Bool) : PMF ℕ :=
  ⟨fun u => ENNReal.ofReal (equilibrium q i u), by
    have hn (u : ℕ) : 0 ≤ equilibrium q i u :=
      div_nonneg (tsum_nonneg fun k => by
        split_ifs <;> first | exact density_nonnegative hq hq1 i k | exact le_rfl)
        (mean_positive hq hq1 i).le
    have hs := (tail_mass hq hq1 i).1.div_const (mean q i)
    have hm : ∑' u, equilibrium q i u = 1 := by
      change (∑' u, tail q i u / mean q i) = 1
      rw [tsum_div_const, (tail_mass hq hq1 i).2,
        div_self (mean_positive hq hq1 i).ne']
    have h := ENNReal.ofReal_tsum_of_nonneg hn hs
    rw [hm, ENNReal.ofReal_one] at h
    exact h ▸ ENNReal.summable.hasSum⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws
open Classical ProbabilityTheory Function OriginalObserverNormalization ActualRenewalPrefixLaw

variable {C : Type*}

instance actionFinite [Finite C] (e : C → Option Bool) : Finite (Action e) := by
  let encode : Action e → C × Option Bool := fun a => match a with
    | .read c => (c.val, none)
    | .emit c d _ => (c, some d)
  apply Finite.of_injective encode
  intro a b h
  cases a <;> cases b <;> simp_all [encode]
  exact Subtype.ext h

instance actionMeasurableSpace (e : C → Option Bool) : MeasurableSpace (Action e) := ⊤
instance actionMeasurableSingletonClass (e : C → Option Bool) :
    MeasurableSingletonClass (Action e) := ⟨fun _ => trivial⟩

/-- Original stochastic primitives are specified before any innovation tape.
    The pair retains the correlation of the update and ensuing action choice.
    Both configuration values belong to the complete original carrier. -/
structure Stochastic (C : Type*) where
  emission : C → Option Bool
  label : Bool → C
  label_emission : ∀ d, emission (label d) = some d
  initialLaw : PMF (C × Action emission)
  operation : C → Bool → PMF (C × Action emission)

namespace Stochastic
variable (O : Stochastic C)

abbrev Outcome := C × Action O.emission
abbrev Innovation := C × Bool → O.Outcome

/-- This random table is fresh at each paid read. Only its selected entry is
    evaluated; it is not part of the retained configuration. -/
def machine : Machine C O.Outcome O.Innovation where
  emission := O.emission
  label := O.label
  label_emission := O.label_emission
  prepare := Prod.fst
  initialAction := fun _ seed => seed.2
  update := fun c b r => (r (c,b)).1
  afterRead := fun c b r _ => (r (c,b)).2

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

def seedLaw : Measure O.Outcome := O.initialLaw.toMeasure
def innovationLaw : Measure O.Innovation :=
  Measure.pi fun p : C × Bool => (O.operation p.1 p.2).toMeasure

instance : IsProbabilityMeasure O.seedLaw := by unfold seedLaw; infer_instance
instance : IsProbabilityMeasure O.innovationLaw := by unfold innovationLaw; infer_instance

private theorem table_entry (c : C) (b : Bool) :
    O.innovationLaw.map (fun r => r (c,b)) = (O.operation c b).toMeasure :=
  (measurePreserving_eval (fun p : C × Bool => (O.operation p.1 p.2).toMeasure) (c,b)).map_eq

/-- The original paid-operation semantics, with no reference to a random table.
    An emitted action holds without another read. -/
def nextLaw (e : O.Outcome) (b : Bool) : PMF O.Outcome :=
  match e.2 with
  | .read c => O.operation c.val b
  | .emit _ _ _ => PMF.pure e

/-- The complete finite original joint execution law. Each vector records the
    intermediate configuration and its correlated ensuing action. Emission
    is held analytically; this does not charge any additional read. -/
def executionLaw (source : ℕ → Bool) : (n : ℕ) → PMF (Fin (n + 1) → O.Outcome)
  | 0 => O.initialLaw.map (fun e _ => e)
  | n + 1 => (executionLaw source n).bind fun x =>
      (O.nextLaw (x (Fin.last n)) (source n)).map (fun y : O.Outcome => Fin.snoc x y)

def advance (e : O.Outcome) (b : Bool) (r : O.Innovation) : O.Outcome :=
  match e.2 with
  | .read c => r (c.val,b)
  | .emit _ _ _ => e

def develop (source : ℕ → Bool) (seed : O.Outcome) :
    (n : ℕ) → (Fin n → O.Innovation) → (Fin (n + 1) → O.Outcome)
  | 0, _ => fun _ => seed
  | n + 1, r =>
    let x := develop source seed n (fun j => r j.castSucc)
    Fin.snoc x (O.advance (x (Fin.last n)) (source n) (r (Fin.last n)))

private theorem advance_law (e : O.Outcome) (b : Bool) :
    O.innovationLaw.map (O.advance e b) = (O.nextLaw e b).toMeasure := by
  rcases e with ⟨c, a⟩
  cases a with
  | read s => exact O.table_entry s.val b
  | emit s d hd =>
    change O.innovationLaw.map (fun _ => (c, Action.emit s d hd)) = _
    simp [nextLaw, PMF.toMeasure_pure]

private theorem extend_law {n : ℕ} (ν : PMF (Fin (n + 1) → O.Outcome)) (b : Bool) :
    (ν.toMeasure.prod O.innovationLaw).map
      (fun p => Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) b p.2)) =
      (ν.bind fun x => (O.nextLaw (x (Fin.last n)) b).map
        (fun y : O.Outcome => (Fin.snoc x y : Fin (n + 2) → O.Outcome))).toMeasure := by
  ext B hB
  have hm : Measurable (fun p : (Fin (n + 1) → O.Outcome) × O.Innovation =>
      (Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) b p.2) :
        Fin (n + 2) → O.Outcome)) := measurable_of_countable _
  rw [Measure.map_apply hm hB, Measure.prod_apply (hm hB), lintegral_countable',
    PMF.toMeasure_bind_apply _ _ _ hB]
  apply tsum_congr
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) hB]
  rw [mul_comm]
  congr 1
  have hrow := congrArg (fun μ : Measure O.Outcome => μ ((fun y : O.Outcome => (Fin.snoc x y :
      Fin (n + 2) → O.Outcome)) ⁻¹' B))
    (O.advance_law (x (Fin.last n)) b)
  rw [Measure.map_apply (measurable_of_countable _)
    (hB.preimage (measurable_of_countable _))] at hrow
  exact hrow

/-- Fresh table evaluation preserves the whole finite original joint law,
    including all initial, updated, read-ready and emitted configurations. -/
theorem finite_execution_law (source : ℕ → Bool) (n : ℕ) :
    (O.seedLaw.prod (Measure.pi fun _ : Fin n => O.innovationLaw)).map
      (fun p => O.develop source p.1 n p.2) = (O.executionLaw source n).toMeasure := by
  induction n with
  | zero =>
    have he : (fun p : O.Outcome × (Fin 0 → O.Innovation) =>
        O.develop source p.1 0 p.2) = (fun e _ => e) ∘ Prod.fst := rfl
    rw [he, ← Measure.map_map (measurable_of_countable _) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, executionLaw, seedLaw,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
  | succ n ih =>
    let split : O.Outcome × (Fin (n + 1) → O.Innovation) →
        (O.Outcome × (Fin n → O.Innovation)) × O.Innovation := fun p =>
      ((p.1, fun j => p.2 j.castSucc), p.2 (Fin.last n))
    have hsplit : (O.seedLaw.prod (Measure.pi fun _ : Fin (n + 1) => O.innovationLaw)).map
        split = (O.seedLaw.prod (Measure.pi fun _ : Fin n => O.innovationLaw)).prod
          O.innovationLaw := by
      have he : split = MeasurableEquiv.prodAssoc.symm ∘
          Prod.map id (fun r : Fin (n + 1) → O.Innovation =>
            (fun j : Fin n => r j.castSucc, r (Fin.last n))) := rfl
      rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
        ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
        split_last O.innovationLaw n, ← Measure.prodAssoc_prod,
        MeasurableEquiv.map_symm_map]
    let step : (Fin (n + 1) → O.Outcome) × O.Innovation →
        (Fin (n + 2) → O.Outcome) := fun p =>
      Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) (source n) p.2)
    have he : (fun p => O.develop source p.1 (n + 1) p.2) =
        step ∘ Prod.map (fun p => O.develop source p.1 n p.2) id ∘ split := by
      funext p
      rfl
    rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop),
      ← Measure.map_map (measurable_of_countable _) (by fun_prop), hsplit,
      ← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,
      ih, Measure.map_id]
    exact O.extend_law (O.executionLaw source n) (source n)

attribute [local simp] advance.eq_1 develop.eq_1 develop.eq_2 develop.eq_def

end Stochastic

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws
