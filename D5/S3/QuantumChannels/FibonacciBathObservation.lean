/- GID: D5/S3/QuantumChannels/FibonacciBathObservation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/FibonacciBathObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three positive posterior classes give the minimal classical record of a finite thermal output. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Entropy.Submodularity.MutualInformationChainRule
import D5.S3.ObserverMemory.PredictionFactors.ConditionalProbabilityProfileMinimality
import D5.S3.Quantum.Decoherence.GibbsBathBandwidth
import D5.S3.Quantum.ProcessReconstruction.GibbsHiddenProcess
import D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The ground-state record of a Fibonacci Gibbs bath

The finite readout theorem concerns the posterior of the ground-state indicator.
The physical example uses the published energy-conserving permutation on the six-level
bath and its product input with an independent Gibbs state. Only positive joint
bath–record events constrain a sufficient readout.

Wheeler's discussion of apparatus-elicited answers provides historical context
in “Information, Physics, Quantum: The Search for Links”, §19.2, pp. 310–313.
https://cqi.inf.usi.ch/qic/wheeler.pdf#page=2
-/

set_option autoImplicit false

namespace D5.S3.QuantumChannels.FibonacciBathObservation

open scoped BigOperators
open D5.S3.Divergence.ChainRule (conditional marginal)
open D5.S3.Entropy.MutualInformation (mutualInformation)
open D5.S3.Entropy.Submodularity.StrongSubadditivity (xyProjection xzProjection)
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
  (markov_of_channel zFirstLaw)
open D5.S3.Entropy.Submodularity.MutualInformationChainRule
  (mutual_information_eq_of_markov_iff_conditional_product)
open D5.S3.ObserverMemory.PredictionFactors.ConditionalProbabilityProfileMinimality
  (conditional_probability_profile_is_minimal)

noncomputable section

variable {B T K : Type*}

/-- The marginal probability of a bath basis outcome in a binary-target law. -/
def bathMass (p : Bool × B → ℝ) (b : B) : ℝ :=
  marginal (fun q : B × Bool => p (q.2, q.1)) b

/-- The ground posterior, used only on events of positive mass. -/
def groundPosterior (p : Bool × B → ℝ) (b : B) : ℝ :=
  p (true, b) / bathMass p b

/-- The law of the ground indicator, the full bath readout and its randomized summary. -/
def readoutLaw (p : Bool × B → ℝ) (W : B → T → ℝ) :
    Bool × (B × T) → ℝ :=
  fun q => p (q.1, q.2.1) * W q.2.1 q.2.2

/-- The law of the ground indicator and the summary. -/
def recordLaw [Fintype B] (p : Bool × B → ℝ) (W : B → T → ℝ) :
    Bool × T → ℝ :=
  xzProjection (readoutLaw p W)

/-- The joint mass of a bath outcome and a record symbol. -/
def readoutMass (p : Bool × B → ℝ) (W : B → T → ℝ) (b : B) (t : T) : ℝ :=
  bathMass p b * W b t

/-- The probability of a record symbol. -/
def recordMass [Fintype B] (p : Bool × B → ℝ) (W : B → T → ℝ) (t : T) : ℝ :=
  ∑ b, readoutMass p W b t

/-- Record symbols that occur under the outgoing bath law. -/
abbrev PositiveRecord [Fintype B] (p : Bool × B → ℝ) (W : B → T → ℝ) :=
  {t : T // 0 < recordMass p W t}

/-- A summary preserves the posterior on every positive joint bath–record event. -/
def PreservesGroundPosterior [Fintype B] (p : Bool × B → ℝ) (W : B → T → ℝ) : Prop :=
  ∀ b t, 0 < readoutMass p W b t →
    groundPosterior p b = groundPosterior (recordLaw p W) t

private theorem bathMass_eq (p : Bool × B → ℝ) (b : B) :
    bathMass p b = p (true, b) + p (false, b) := by
  simp only [bathMass, marginal, Fintype.sum_bool]

private theorem joint_le_bathMass (p : Bool × B → ℝ) (hp : ∀ q, 0 ≤ p q)
    (x : Bool) (b : B) : p (x, b) ≤ bathMass p b := by
  rw [bathMass_eq]
  cases x
  · exact le_add_of_nonneg_left (hp (true, b))
  · exact le_add_of_nonneg_right (hp (false, b))

private theorem bathMass_nonneg (p : Bool × B → ℝ)
    (hp : ∀ q, 0 ≤ p q) (b : B) : 0 ≤ bathMass p b :=
  (hp (true, b)).trans (joint_le_bathMass p hp true b)

private theorem groundPosterior_mem (p : Bool × B → ℝ)
    (hp : ∀ q, 0 ≤ p q) (b : B) : groundPosterior p b ∈ Set.Icc 0 1 := by
  refine ⟨div_nonneg (hp _) (bathMass_nonneg p hp b), ?_⟩
  rcases eq_or_lt_of_le (bathMass_nonneg p hp b) with hb | hb
  · simp [groundPosterior, ← hb]
  · exact (div_le_one hb).2 (joint_le_bathMass p hp true b)

private theorem false_posterior (p : Bool × B → ℝ) (b : B)
    (hb : 0 < bathMass p b) : p (false, b) / bathMass p b = 1 - groundPosterior p b := by
  unfold groundPosterior
  have h := congrArg (fun m : ℝ => m / bathMass p b) (bathMass_eq p b)
  change bathMass p b / bathMass p b =
    (p (true, b) + p (false, b)) / bathMass p b at h
  rw [div_self hb.ne', add_div] at h
  linarith

private theorem readoutMass_nonneg (p : Bool × B → ℝ)
    (hp : ∀ q, 0 ≤ p q) (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t)
    (b : B) (t : T) : 0 ≤ readoutMass p W b t :=
  mul_nonneg (bathMass_nonneg p hp b) (hW b t)

private theorem bathMass_pos_of_readoutMass_pos (p : Bool × B → ℝ) (W : B → T → ℝ)
    (hW : ∀ b t, 0 ≤ W b t) {b : B} {t : T}
    (h : 0 < readoutMass p W b t) : 0 < bathMass p b := by
  by_contra! hb
  exact h.not_ge (mul_nonpos_of_nonpos_of_nonneg hb (hW b t))

private theorem sum_pos_iff_exists {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) : (0 < ∑ a, w a) ↔ ∃ a, 0 < w a := by
  constructor
  · intro h
    by_contra! hn
    exact h.not_ge (Finset.sum_nonpos fun a _ => hn a)
  · rintro ⟨a, ha⟩
    exact Finset.sum_pos' (fun a _ => hw a) ⟨a, Finset.mem_univ a, ha⟩

private theorem recordLaw_nonneg [Fintype B] (p : Bool × B → ℝ)
    (hp : ∀ q, 0 ≤ p q) (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t) :
    ∀ q, 0 ≤ recordLaw p W q := fun q =>
  Finset.sum_nonneg fun b _ => mul_nonneg (hp (q.1, b)) (hW b q.2)

private theorem bathMass_recordLaw [Fintype B] (p : Bool × B → ℝ)
    (W : B → T → ℝ) (t : T) : bathMass (recordLaw p W) t = recordMass p W t := by
  simp only [bathMass, marginal, recordLaw, xzProjection, readoutLaw]
  rw [Finset.sum_comm]
  simp only [recordMass, readoutMass, bathMass, marginal, Finset.sum_mul]

private theorem weighted_posterior (p : Bool × B → ℝ) (hp : ∀ q, 0 ≤ p q) (b : B) :
    bathMass p b * groundPosterior p b = p (true, b) := by
  by_cases hb : bathMass p b = 0
  · have hle := joint_le_bathMass p hp true b
    rw [hb] at hle
    simp only [hb, zero_mul]
    exact (le_antisymm hle (hp _)).symm
  · unfold groundPosterior
    exact mul_div_cancel₀ _ hb

/-- For a row-stochastic readout, equality of the two mutual informations is
equivalent to pointwise posterior preservation on the positive joint support. -/
theorem mutualInformation_eq_iff_preservesGroundPosterior [Fintype B] [Fintype T]
    (p : Bool × B → ℝ) (hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1)
    (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t) (hrows : ∀ b, ∑ t, W b t = 1) :
    mutualInformation (recordLaw p W) = mutualInformation p ↔ PreservesGroundPosterior p W := by
  let L := readoutLaw p W
  have hL : (∀ q, 0 ≤ L q) ∧ ∑ q, L q = 1 := by
    refine ⟨fun q => mul_nonneg (hp.1 _) (hW _ _), ?_⟩
    simpa only [L, readoutLaw, Fintype.sum_prod_type, ← Finset.mul_sum, hrows, mul_one]
      using hp.2
  have hxy : xyProjection L = p := by
    funext q
    simp only [L, xyProjection, readoutLaw, ← Finset.mul_sum, hrows, mul_one]
  have hz (t : T) : marginal (zFirstLaw L) t = recordMass p W t := by
    rw [← bathMass_recordLaw]
    simp only [marginal, zFirstLaw, bathMass, recordLaw, xzProjection, Fintype.sum_prod_type, L]
  have hleft (t : T) (x : Bool) :
      marginal (conditional (zFirstLaw L) t) x =
        recordLaw p W (x, t) / recordMass p W t := by
    simp only [marginal, conditional, zFirstLaw, recordLaw, xzProjection, ← Finset.sum_div, L]
    congr 1
    exact hz t
  have hright (t : T) (b : B) :
      marginal (fun q : B × Bool => conditional (zFirstLaw L) t (q.2, q.1)) b =
        readoutMass p W b t / recordMass p W t := by
    simp only [marginal, conditional, zFirstLaw, L, readoutLaw,
      ← Finset.sum_div, ← Finset.sum_mul, readoutMass, bathMass]
    congr 1
    exact hz t
  have hproduct (x : Bool) (b : B) (t : T) (hb : 0 < bathMass p b) :
      L (x, (b, t)) / recordMass p W t =
        (p (x, b) / bathMass p b) * (readoutMass p W b t / recordMass p W t) := by
    change p (x, b) * W b t / recordMass p W t = _
    calc
      _ = (p (x, b) * W b t * bathMass p b) / (recordMass p W t * bathMass p b) :=
        (mul_div_mul_right _ _ hb.ne').symm
      _ = _ := by
        rw [readoutMass, div_mul_div_comm, mul_comm (recordMass p W t) (bathMass p b)]
        congr 1 <;> ring
  have hinfo := mutual_information_eq_of_markov_iff_conditional_product L hL
    (markov_of_channel p W hrows)
  rw [hxy] at hinfo
  change mutualInformation (xzProjection L) = mutualInformation p ↔ _
  rw [hinfo]
  constructor
  · intro h b t hbt
    have ht : 0 < recordMass p W t :=
      (sum_pos_iff_exists _ (fun a => readoutMass_nonneg p hp.1 W hW a t)).2 ⟨b, hbt⟩
    have hb := bathMass_pos_of_readoutMass_pos p W hW hbt
    have htz : marginal (zFirstLaw L) t ≠ 0 := by
      rw [hz]
      exact ht.ne'
    have heq := congrFun (h t htz) (true, b)
    change L (true, (b, t)) / marginal (zFirstLaw L) t = _ at heq
    rw [hz, hleft, hright, hproduct true b t hb] at heq
    unfold groundPosterior
    rw [bathMass_recordLaw]
    exact mul_right_cancel₀ (div_ne_zero hbt.ne' ht.ne') heq
  · intro h t _
    funext q
    rcases q with ⟨x, b⟩
    change L (x, (b, t)) / marginal (zFirstLaw L) t = _
    rw [hz, hleft, hright]
    rcases eq_or_lt_of_le (readoutMass_nonneg p hp.1 W hW b t) with hzero | hpos
    · have hzero' : readoutMass p W b t = 0 := hzero.symm
      have hLzero : L (x, (b, t)) = 0 := by
        have hm : bathMass p b * W b t = 0 := hzero'
        rcases mul_eq_zero.mp hm with hb | hw
        · have hle := joint_le_bathMass p hp.1 x b
          rw [hb] at hle
          change p (x, b) * W b t = 0
          rw [le_antisymm hle (hp.1 _), zero_mul]
        · change p (x, b) * W b t = 0
          rw [hw, mul_zero]
      simp only [hLzero, hzero', zero_div, mul_zero]
    · have hb := bathMass_pos_of_readoutMass_pos p W hW hpos
      have ht : 0 < recordMass p W t :=
        (sum_pos_iff_exists _ (fun a => readoutMass_nonneg p hp.1 W hW a t)).2 ⟨b, hpos⟩
      have hs := h b t hpos
      rw [hproduct x b t hb]
      congr 1
      rw [← bathMass_recordLaw]
      cases x
      · rw [false_posterior p b hb, false_posterior (recordLaw p W) t
          (by rwa [bathMass_recordLaw]), hs]
      · exact hs

private def bernoulliProfile (r : Set.Icc (0 : ℝ) 1) : PMF Bool :=
  PMF.ofFintype (fun x => if x then ENNReal.ofReal r.1 else ENNReal.ofReal (1 - r.1)) (by
    rw [Fintype.sum_bool]
    change ENNReal.ofReal r.1 + ENNReal.ofReal (1 - r.1) = 1
    rw [← ENNReal.ofReal_add r.2.1 (sub_nonneg.mpr r.2.2),
      show r.1 + (1 - r.1) = 1 by ring, ENNReal.ofReal_one])

private theorem bernoulliProfile_injective : Function.Injective bernoulliProfile := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun p : PMF Bool => (p true).toReal) h
  simpa [bernoulliProfile, ENNReal.toReal_ofReal a.2.1, ENNReal.toReal_ofReal b.2.1] using he

/-- Every sufficient randomized summary has a unique decoder on its positive
support onto the distinct, positively realized posterior classes. -/
theorem existsUnique_surjective_recordDecoder [Fintype B] [Fintype T]
    (p : Bool × B → ℝ) (hp : ∀ q, 0 ≤ p q)
    (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t) (hrows : ∀ b, ∑ t, W b t = 1)
    (c : B → K) (r : K → ℝ) (hr : ∀ k, r k ∈ Set.Icc 0 1) (hinj : Function.Injective r)
    (hclass : ∀ b, 0 < bathMass p b → groundPosterior p b = r (c b))
    (hrealized : ∀ k, ∃ b, 0 < bathMass p b ∧ c b = k)
    (hsuff : PreservesGroundPosterior p W) :
    ∃! d : PositiveRecord p W → K, Function.Surjective d ∧
      ∀ b t, 0 < readoutMass p W b t.1 → d t = c b := by
  classical
  let X := {q : B × PositiveRecord p W // 0 < readoutMass p W q.1 q.2.1}
  letI : Fintype X := Fintype.ofFinite X
  let interface : X → PositiveRecord p W := fun q => q.1.2
  let kernel : X → PMF Bool := fun q => bernoulliProfile ⟨r (c q.1.1), hr _⟩
  let predictor : PositiveRecord p W → PMF Bool := fun t =>
    bernoulliProfile ⟨groundPosterior (recordLaw p W) t.1,
      groundPosterior_mem _ (recordLaw_nonneg p hp W hW) t.1⟩
  have hfactor : kernel = predictor ∘ interface := by
    funext q
    apply congrArg bernoulliProfile
    apply Subtype.ext
    exact (hclass _ (bathMass_pos_of_readoutMass_pos p W hW q.2)).symm.trans
      (hsuff _ _ q.2)
  have hseparate :=
    (conditional_probability_profile_is_minimal kernel interface predictor hfactor).2
  have hsame (b b' : B) (t : PositiveRecord p W)
      (hb : 0 < readoutMass p W b t.1) (hb' : 0 < readoutMass p W b' t.1) :
      c b = c b' := by
    let q : X := ⟨(b, t), hb⟩
    let q' : X := ⟨(b', t), hb'⟩
    have hlaw : kernel q = kernel q' := by
      by_contra hne
      exact hseparate q q' hne rfl
    exact hinj (congrArg Subtype.val (bernoulliProfile_injective hlaw))
  have hsource (t : PositiveRecord p W) : ∃ b, 0 < readoutMass p W b t.1 :=
    (sum_pos_iff_exists _ (fun b => readoutMass_nonneg p hp W hW b t.1)).1 t.2
  let d : PositiveRecord p W → K := fun t => c (Classical.choose (hsource t))
  have hd (b : B) (t : PositiveRecord p W) (hb : 0 < readoutMass p W b t.1) :
      d t = c b := hsame _ _ t (Classical.choose_spec (hsource t)) hb
  refine ⟨d, ⟨?_, hd⟩, ?_⟩
  · intro k
    obtain ⟨b, hb, hbk⟩ := hrealized k
    obtain ⟨t, ht⟩ := (sum_pos_iff_exists (W b) (hW b)).1
      (by rw [hrows b]; exact zero_lt_one)
    have hbt : 0 < readoutMass p W b t := mul_pos hb ht
    have hrecord : 0 < recordMass p W t :=
      (sum_pos_iff_exists _ (fun a => readoutMass_nonneg p hp W hW a t)).2 ⟨b, hbt⟩
    exact ⟨⟨t, hrecord⟩, (hd b ⟨t, hrecord⟩ hbt).trans hbk⟩
  · intro d' hd'
    funext t
    obtain ⟨b, hb⟩ := hsource t
    exact (hd'.2 b t hb).trans (hd b t hb).symm

/-- Any class decoder on the positive bath–record support preserves the posterior. -/
theorem preservesGroundPosterior_of_classDecoder [Fintype B]
    (p : Bool × B → ℝ) (hp : ∀ q, 0 ≤ p q)
    (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t)
    (c : B → K) (r : K → ℝ) (d : T → K)
    (hclass : ∀ b, 0 < bathMass p b → groundPosterior p b = r (c b))
    (hdecoder : ∀ b t, 0 < readoutMass p W b t → c b = d t) :
    PreservesGroundPosterior p W := by
  intro b t hb
  have ht : 0 < recordMass p W t :=
    (sum_pos_iff_exists _ (fun a => readoutMass_nonneg p hp W hW a t)).2 ⟨b, hb⟩
  have hnum : recordLaw p W (true, t) = recordMass p W t * r (d t) := by
    unfold recordLaw xzProjection recordMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    change p (true, a) * W a t = readoutMass p W a t * r (d t)
    rw [← weighted_posterior p hp a,
      show (bathMass p a * groundPosterior p a) * W a t =
        readoutMass p W a t * groundPosterior p a by
          unfold readoutMass
          ring]
    rcases eq_or_lt_of_le (readoutMass_nonneg p hp W hW a t) with ha | ha
    · simp only [← ha, zero_mul]
    · rw [hclass a (bathMass_pos_of_readoutMass_pos p W hW ha), hdecoder a t ha]
  rw [hclass b (bathMass_pos_of_readoutMass_pos p W hW hb), hdecoder b t hb,
    groundPosterior, bathMass_recordLaw, hnum]
  exact (eq_div_iff ht.ne').2 (mul_comm _ _)

/-- The conditional binary-entropy increase at a positive symbol is strict
exactly when the symbol receives positive mass from distinct posteriors. -/
theorem strict_binEntropy_increase_iff_mixes [Fintype B]
    (p : Bool × B → ℝ) (hp : ∀ q, 0 ≤ p q)
    (W : B → T → ℝ) (hW : ∀ b t, 0 ≤ W b t)
    (t : T) (ht : 0 < recordMass p W t) :
    (∑ b, (readoutMass p W b t / recordMass p W t) *
        Real.binEntropy (groundPosterior p b)) <
          Real.binEntropy (groundPosterior (recordLaw p W) t) ↔
      ∃ b b', 0 < readoutMass p W b t ∧ 0 < readoutMass p W b' t ∧
        groundPosterior p b ≠ groundPosterior p b' := by
  let w (b : B) := readoutMass p W b t / recordMass p W t
  have hw : ∀ b ∈ (Finset.univ : Finset B), 0 ≤ w b :=
    fun b _ => div_nonneg (readoutMass_nonneg p hp W hW b t) ht.le
  have hsum : ∑ b, w b = 1 := by
    simp only [w, ← Finset.sum_div]
    change recordMass p W t / recordMass p W t = 1
    exact div_self ht.ne'
  have hmean : (∑ b, w b • groundPosterior p b) = groundPosterior (recordLaw p W) t := by
    unfold groundPosterior
    rw [bathMass_recordLaw]
    change (∑ b, w b • (p (true, b) / bathMass p b)) =
      (∑ b, p (true, b) * W b t) / recordMass p W t
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    change (readoutMass p W b t / recordMass p W t) * groundPosterior p b = _
    rw [show (readoutMass p W b t / recordMass p W t) * groundPosterior p b =
      ((bathMass p b * groundPosterior p b) * W b t) / recordMass p W t by
        unfold readoutMass
        ring, weighted_posterior p hp b]
  have hwpos (b : B) : w b ≠ 0 ↔ 0 < readoutMass p W b t := by
    change readoutMass p W b t / recordMass p W t ≠ 0 ↔ _
    constructor
    · intro hn
      exact lt_of_le_of_ne (readoutMass_nonneg p hp W hW b t)
        (fun he => hn (by rw [← he, zero_div]))
    · intro h
      exact div_ne_zero h.ne' ht.ne'
  have hJensen := Real.strictConcave_binEntropy.lt_map_sum_iff_of_nonneg hw hsum
    (fun b _ => groundPosterior_mem p hp b)
  rw [hmean] at hJensen
  simpa only [smul_eq_mul, Finset.mem_univ, true_and, hwpos] using hJensen

end

section SixLevel

open Matrix
open scoped Kronecker CStarAlgebra Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity (thermalState)
open GibbsBathBandwidth (diagonalReal hamiltonian_selfAdjoint)
open UnitaryReconstruction.GibbsHiddenProcess (gibbs gibbs_matrix logBoltzmann)
open CoolingMapThermalOperationRefutation (IsEnergyConserving)
open ThermalDegeneracyWitness
  (bathLevel inputPopulation inputState bathState systemEnergy bathEnergy
    inverseTemperature jointUnitary)
-- The publication's checked permutation and rational Gibbs weights supply the
-- computation. Access their original definitions so the table checks that unitary.
open private jointPermutation rationalGibbsWeight partitionWeight_eq gibbsWeight_eq_rat
  jointUnitary_conj_diagonal jointUnitary_mem_unitaryGroup jointUnitary_energyConserving
  from D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation

private abbrev Joint := Fin 3 × Fin 20

/-- Each entry is the numerator of a joint probability, with common denominator 282.
Columns index bath levels and give the probability per basis coordinate. -/
private def outputNumerator (s : Fin 3) (j : ℕ) : ℕ :=
  if s = 0 then
    match j with
    | 1 => 64
    | 2 => 32
    | 3 => 16
    | 4 => 8
    | 5 => 4
    | _ => 0
  else if s = 1 then
    if j = 5 then 2 else 0
  else
    if j = 4 then 2 else if j = 5 then 1 else 0

/-- Exact diagonal of the outgoing qutrit–bath state in the joint energy basis. -/
def outputWeight (q : Fin 3 × Fin 20) : ℚ :=
  (outputNumerator q.1 (bathLevel q.2) : ℚ) / 282

private def permutedInputWeight (q : Joint) : ℚ :=
  inputPopulation (jointPermutation q).1 * rationalGibbsWeight (jointPermutation q).2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem permutedInputWeight_eq : ∀ q : Joint, permutedInputWeight q = outputWeight q := by
  simp only [permutedInputWeight, rationalGibbsWeight, partitionWeight_eq]
  decide +kernel

noncomputable section

/-- The actual terminal matrix of the published six-level unitary with product input. -/
def terminalJoint : Matrix (Fin 3 × Fin 20) (Fin 3 × Fin 20) ℂ :=
  jointUnitary * (inputState ⊗ₖ bathState) * jointUnitaryᴴ

/-- The independently supplied bath is the Hamiltonian Gibbs state, and the
published unitary conserves the total energy. -/
theorem terminalJoint_gibbs_implementation :
    jointUnitary ∈ Matrix.unitaryGroup (Fin 3 × Fin 20) ℂ ∧
      IsEnergyConserving systemEnergy bathEnergy jointUnitary ∧
      ∃ hH : (diagonalReal bathEnergy).IsHermitian,
        terminalJoint = jointUnitary *
          (inputState ⊗ₖ CStarMatrix.ofMatrix.symm
            (thermalState (CStarMatrix.ofMatrix (diagonalReal bathEnergy))
              (hamiltonian_selfAdjoint hH) inverseTemperature).1) * jointUnitaryᴴ := by
  have hH : (diagonalReal bathEnergy).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have hlog : (-inverseTemperature) • CStarMatrix.ofMatrix (diagonalReal bathEnergy) =
      logBoltzmann inverseTemperature bathEnergy := by
    apply CStarMatrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [CStarMatrix.ofMatrix_apply, diagonalReal, logBoltzmann,
        Complex.real_smul, Complex.ofReal_mul]
    · simp [CStarMatrix.ofMatrix_apply, diagonalReal, logBoltzmann, diagonal_apply_ne _ hij]
  have hthermal : thermalState (CStarMatrix.ofMatrix (diagonalReal bathEnergy))
      (hamiltonian_selfAdjoint hH) inverseTemperature = gibbs inverseTemperature bathEnergy := by
    unfold thermalState gibbs
    congr 1 <;> exact hlog
  refine ⟨jointUnitary_mem_unitaryGroup, jointUnitary_energyConserving, hH, ?_⟩
  rw [hthermal, gibbs_matrix] <;> rfl

/-- The kernel-computable table is the entire output of the actual unitary,
including the absence of off-diagonal matrix entries. -/
theorem terminalJoint_eq_diagonal :
    terminalJoint = Matrix.diagonal (fun q : Fin 3 × Fin 20 => (outputWeight q : ℂ)) := by
  unfold terminalJoint inputState bathState diagonalReal
  rw [Matrix.diagonal_kronecker_diagonal, jointUnitary_conj_diagonal]
  apply congrArg Matrix.diagonal
  funext q
  simp only [gibbsWeight_eq_rat, Complex.ofReal_ratCast, ← Rat.cast_mul]
  exact congrArg (fun x : ℚ => (x : ℂ)) (permutedInputWeight_eq q)

end

private def groundLawRat (q : Bool × Fin 20) : ℚ :=
  if q.1 then outputWeight (0, q.2)
  else outputWeight (1, q.2) + outputWeight (2, q.2)

private def bathMassRat (b : Fin 20) : ℚ :=
  groundLawRat (true, b) + groundLawRat (false, b)

/-- Levels 1 through 3 share class 0, level 4 has class 1, and level 5 has
class 2. The empty bottom level is assigned to class 0. -/
def recordClass (b : Fin 20) : Fin 3 :=
  if bathLevel b = 5 then 2 else if bathLevel b = 4 then 1 else 0

private def posteriorRateRat (k : Fin 3) : ℚ :=
  (![1, 4 / 5, 4 / 7] : Fin 3 → ℚ) k

private def firstCoordinate (k : Fin 3) : Fin 20 :=
  (![1, 7, 12] : Fin 3 → Fin 20) k

set_option maxRecDepth 4096 in
private theorem groundLawRat_isLaw :
    (∀ q, 0 ≤ groundLawRat q) ∧ ∑ q, groundLawRat q = 1 := by
  decide +kernel

private theorem posteriorRateRat_spec : ∀ b : Fin 20, 0 < bathMassRat b →
    groundLawRat (true, b) / bathMassRat b = posteriorRateRat (recordClass b) := by
  decide +kernel

private theorem firstCoordinate_spec : ∀ k : Fin 3,
    0 < bathMassRat (firstCoordinate k) ∧ recordClass (firstCoordinate k) = k := by
  decide +kernel

private theorem posteriorRateRat_injective : ∀ i j : Fin 3,
    posteriorRateRat i = posteriorRateRat j → i = j := by
  decide +kernel

private theorem posteriorRateRat_mem : ∀ k : Fin 3,
    0 ≤ posteriorRateRat k ∧ posteriorRateRat k ≤ 1 := by
  decide +kernel

private def classReadoutRat (b : Fin 20) (k : Fin 3) : ℚ :=
  if recordClass b = k then 1 else 0

private def classMassRat (k : Fin 3) : ℚ :=
  (![88 / 141, 25 / 141, 28 / 141] : Fin 3 → ℚ) k

set_option maxRecDepth 4096 in
private theorem classMassRat_spec : ∀ k : Fin 3,
    (∑ b, bathMassRat b * classReadoutRat b k) = classMassRat k := by
  decide +kernel

private theorem classMassRat_pos : ∀ k : Fin 3, 0 < classMassRat k := by
  decide +kernel

noncomputable section

/-- Joint law of the terminal ground-state indicator and the bath basis readout. -/
def groundLaw (q : Bool × Fin 20) : ℝ :=
  if q.1 then (terminalJoint (0, q.2) (0, q.2)).re
  else (terminalJoint (1, q.2) (1, q.2)).re + (terminalJoint (2, q.2) (2, q.2)).re

private theorem groundLaw_eq_rat (q : Bool × Fin 20) :
    groundLaw q = (groundLawRat q : ℝ) := by
  have hre (r : ℚ) : (r : ℂ).re = (r : ℝ) := Complex.ofReal_re _
  rcases q with ⟨x, b⟩
  cases x <;>
    simp [groundLaw, groundLawRat, terminalJoint_eq_diagonal, hre, Rat.cast_add]

private theorem groundLaw_isLaw :
    (∀ q, 0 ≤ groundLaw q) ∧ ∑ q, groundLaw q = 1 := by
  constructor
  · intro q
    rw [groundLaw_eq_rat, Rat.cast_nonneg]
    exact groundLawRat_isLaw.1 q
  · simpa only [Rat.cast_sum, Rat.cast_one, groundLaw_eq_rat] using
      congrArg (fun x : ℚ => (x : ℝ)) groundLawRat_isLaw.2

private theorem bathMass_groundLaw (b : Fin 20) :
    bathMass groundLaw b = (bathMassRat b : ℝ) := by
  rw [bathMass_eq]
  simp only [groundLaw_eq_rat, bathMassRat, Rat.cast_add]

/-- The three ground probabilities conditional on a positive bath outcome. -/
def posteriorRate (k : Fin 3) : ℝ := (posteriorRateRat k : ℝ)

/-- The ground posterior values in order of increasing bath energy. -/
theorem posteriorRate_values :
    posteriorRate 0 = 1 ∧ posteriorRate 1 = 4 / 5 ∧ posteriorRate 2 = 4 / 7 := by
  norm_num [posteriorRate, posteriorRateRat]

/-- Conditioning on the three-valued class gives the full ground posterior
of any positive bath outcome. -/
theorem groundPosterior_eq_classRate (b : Fin 20) (hb : 0 < bathMass groundLaw b) :
    groundPosterior groundLaw b = posteriorRate (recordClass b) := by
  rw [bathMass_groundLaw] at hb
  unfold groundPosterior
  rw [bathMass_groundLaw]
  simpa only [groundLaw_eq_rat, posteriorRate, Rat.cast_div] using
    congrArg (fun x : ℚ => (x : ℝ)) (posteriorRateRat_spec b (Rat.cast_pos.mp hb))

private theorem posteriorRate_mem (k : Fin 3) : posteriorRate k ∈ Set.Icc 0 1 := by
  change 0 ≤ (posteriorRateRat k : ℝ) ∧ (posteriorRateRat k : ℝ) ≤ 1
  exact ⟨Rat.cast_nonneg.mpr (posteriorRateRat_mem k).1,
    by exact_mod_cast (posteriorRateRat_mem k).2⟩

private theorem posteriorRate_injective : Function.Injective posteriorRate := by
  intro i j hij
  have hrat : posteriorRateRat i = posteriorRateRat j := by
    change (posteriorRateRat i : ℝ) = (posteriorRateRat j : ℝ) at hij
    exact_mod_cast hij
  exact posteriorRateRat_injective i j hrat

private theorem recordClass_realized (k : Fin 3) :
    ∃ b, 0 < bathMass groundLaw b ∧ recordClass b = k := by
  refine ⟨firstCoordinate k, ?_, (firstCoordinate_spec k).2⟩
  rw [bathMass_groundLaw, Rat.cast_pos]
  exact (firstCoordinate_spec k).1

/-- A finite randomized readout that preserves the physical ground posterior
must have at least three outcomes of positive outgoing probability. -/
theorem sixLevel_record_minimal {T : Type*} [Fintype T]
    (W : Fin 20 → T → ℝ) (hW : ∀ b t, 0 ≤ W b t) (hrows : ∀ b, ∑ t, W b t = 1)
    (hpres : PreservesGroundPosterior groundLaw W) :
    3 ≤ Nat.card (PositiveRecord groundLaw W) := by
  obtain ⟨d, hd, _⟩ := existsUnique_surjective_recordDecoder groundLaw groundLaw_isLaw.1 W hW hrows
    recordClass posteriorRate posteriorRate_mem posteriorRate_injective
    groundPosterior_eq_classRate recordClass_realized hpres
  letI : Fintype (PositiveRecord groundLaw W) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_surjective d hd.1

/-- The same three-symbol lower bound holds under equality of operational
mutual information for the ground indicator. -/
theorem sixLevel_record_minimal_of_mutualInformation_eq {T : Type*} [Fintype T]
    (W : Fin 20 → T → ℝ) (hW : ∀ b t, 0 ≤ W b t) (hrows : ∀ b, ∑ t, W b t = 1)
    (hinfo : mutualInformation (recordLaw groundLaw W) = mutualInformation groundLaw) :
    3 ≤ Nat.card (PositiveRecord groundLaw W) :=
  sixLevel_record_minimal W hW hrows
    ((mutualInformation_eq_iff_preservesGroundPosterior groundLaw groundLaw_isLaw W hW hrows).1
      hinfo)

/-- Deterministic classical readout of the three bath-energy classes. -/
def classReadout (b : Fin 20) (k : Fin 3) : ℝ := (classReadoutRat b k : ℝ)

private theorem classReadout_eq (b : Fin 20) (k : Fin 3) :
    classReadout b k = if recordClass b = k then 1 else 0 := by
  unfold classReadout classReadoutRat
  split <;> simp_all

private theorem classReadout_nonneg (b : Fin 20) (k : Fin 3) :
    0 ≤ classReadout b k := by
  rw [classReadout_eq]
  split <;> norm_num

private theorem classReadout_rows (b : Fin 20) : ∑ k, classReadout b k = 1 := by
  simp only [classReadout_eq, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem recordMass_classReadout (k : Fin 3) :
    recordMass groundLaw classReadout k = (classMassRat k : ℝ) := by
  simpa only [Rat.cast_sum, Rat.cast_mul, recordMass, readoutMass, bathMass_groundLaw,
    classReadout] using congrArg (fun x : ℚ => (x : ℝ)) (classMassRat_spec k)

/-- The class readout is a row-stochastic channel attaining three positive
outcomes and preserving the posterior and its mutual information. -/
theorem sixLevel_classReadout_attains :
    (∀ b k, 0 ≤ classReadout b k) ∧ (∀ b, ∑ k, classReadout b k = 1) ∧
      PreservesGroundPosterior groundLaw classReadout ∧
      mutualInformation (recordLaw groundLaw classReadout) = mutualInformation groundLaw ∧
      Nat.card (PositiveRecord groundLaw classReadout) = 3 := by
  have hsuff : PreservesGroundPosterior groundLaw classReadout := by
    apply preservesGroundPosterior_of_classDecoder groundLaw groundLaw_isLaw.1 classReadout
      classReadout_nonneg recordClass posteriorRate id groundPosterior_eq_classRate
    intro b k h
    by_contra hn
    have hk : recordClass b ≠ k := hn
    simp only [readoutMass, classReadout_eq, if_neg hk, mul_zero, lt_irrefl] at h
  refine ⟨classReadout_nonneg, classReadout_rows, hsuff, ?_, ?_⟩
  · exact (mutualInformation_eq_iff_preservesGroundPosterior groundLaw groundLaw_isLaw
      classReadout classReadout_nonneg classReadout_rows).2 hsuff
  · have hpos (k : Fin 3) : 0 < recordMass groundLaw classReadout k := by
      rw [recordMass_classReadout, Rat.cast_pos]
      exact classMassRat_pos k
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Nat.card_congr (Equiv.subtypeUnivEquiv hpos)

end
end SixLevel

#print axioms terminalJoint_eq_diagonal
#print axioms terminalJoint_gibbs_implementation
#print axioms sixLevel_record_minimal_of_mutualInformation_eq
#print axioms sixLevel_classReadout_attains

end D5.S3.QuantumChannels.FibonacciBathObservation
