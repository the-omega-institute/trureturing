/- GID: D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite Boolean outcome-table law admits an exact target-marginal transport preserving the full original law and attaining each coordinate's minimum mismatch probability. -/

import D5.S3.ConceptDynamics.CausalMoments.FiniteConditionalResponseTable
import D5.S3.ConceptDynamics.CausalMoments.ProductLawMomentSparsification

/-!
The original response coordinates need not be independent. A single auxiliary
random table realizes the finite family of one-coordinate transition kernels;
its product with the entire original law supplies one joint old/new-table law.
This reuses finite_conditional_table_realization and the exact product and
pushforward expectation owners. Independent transition entries are a possible
construction, not an assumption on original potential outcomes.

The construction is a finite rational instance of classical maximal Bernoulli
coupling and marginal shadows, as in Eckstein--Nutz, SIAM J. Math. Anal. 54(6)
(2022), 5922-5948. No regularized-transport theorem or convergence rate is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.BooleanOutcomeMarginalTransport

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.ProductLawMomentSparsification
open D5.S3.ConceptDynamics.CausalMoments.FiniteConditionalResponseTable

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The actual success expectation of a coordinate of one complete outcome law. -/
def tableMean (law : FiniteResponseLaw (M → Bool)) (i : M) : ℚ :=
  linearObjective (fun table => if table i then 1 else 0) law.mass

/-- Bounds follow from nonnegative normalized original weights. -/
theorem tableMean_mem (law : FiniteResponseLaw (M → Bool)) (i : M) :
    0 ≤ tableMean law i ∧ tableMean law i ≤ 1 := by
  unfold tableMean linearObjective
  constructor
  · apply Finset.sum_nonneg
    intro table _
    cases h : table i <;> simp [h, law.nonnegative table]
  · calc
      tableMean law i ≤ ∑ table, law.mass table := by
        apply Finset.sum_le_sum
        intro table _
        cases h : table i <;> simp [h, law.nonnegative table]
      _ = 1 := law.total

/-- Success probability of the target bit conditional on the original bit.
The unused zero-mass branch is defined even at source mean zero or one. -/
def bitTransition (source target : ℚ) (bit : Bool) : ℚ :=
  if source ≤ target then
    if bit then 1 else (target - source) / (1 - source)
  else if bit then target / source else 0

private theorem transition_bounds (r s : ℚ) (hr : 0 ≤ r ∧ r ≤ 1)
    (hs : 0 ≤ s ∧ s ≤ 1) (b : Bool) :
    0 ≤ bitTransition r s b ∧ bitTransition r s b ≤ 1 := by
  by_cases increasing : r ≤ s
  · cases b
    · simp only [bitTransition, if_pos increasing, Bool.false_eq_true, if_false]
      by_cases boundary : r = 1
      · simp [boundary]
      · have positive : 0 < 1-r := sub_pos.mpr (lt_of_le_of_ne hr.2 boundary)
        exact ⟨div_nonneg (sub_nonneg.mpr increasing) positive.le,
          (div_le_one positive).mpr (by linarith [hs.2])⟩
    · simp [bitTransition, increasing]
  · have positive : 0 < r := by linarith [hs.1]
    cases b
    · simp [bitTransition, increasing]
    · simpa [bitTransition, increasing] using (show 0 ≤ s/r ∧ s/r ≤ 1 from
          ⟨div_nonneg hs.1 positive.le, (div_le_one positive).mpr (le_of_lt (lt_of_not_ge increasing))⟩)

private theorem transition_moments (r s : ℚ) (hr : 0 ≤ r ∧ r ≤ 1)
    (hs : 0 ≤ s ∧ s ≤ 1) :
    (1-r)*bitTransition r s false + r*bitTransition r s true = s ∧
    (1-r)*bitTransition r s false + r*(1-bitTransition r s true) = |s-r| := by
  by_cases increasing : r ≤ s
  · by_cases boundary : r = 1
    · have target_one : s = 1 := by linarith [hs.2]
      simp [bitTransition, boundary, target_one]
    · have denominator : (1 : ℚ)-r ≠ 0 := by intro h; apply boundary; linarith
      constructor <;> simp [bitTransition, increasing,
        abs_of_nonneg (sub_nonneg.mpr increasing)] <;> field_simp [denominator] <;> ring
  · have positive : 0 < r := by linarith [hs.1]
    constructor <;> simp [bitTransition, increasing,
      abs_of_nonpos (by linarith : s-r ≤ 0)] <;> field_simp [ne_of_gt positive] <;> ring

private def coinLaw (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : FiniteResponseLaw Bool where
  mass := fun b => if b then p else 1-p
  nonnegative := by intro b; cases b <;> simp <;> linarith [hp.1, hp.2]
  total := by simp [Fintype.sum_bool] <;> ring

private theorem expectation_bool {X : Type*} [Fintype X]
    (law : FiniteResponseLaw X) (f : X → Bool) (h : Bool → ℚ) :
    linearObjective (fun x => h (f x)) law.mass =
      (1-linearObjective (fun x => if f x then 1 else 0) law.mass)*h false +
      linearObjective (fun x => if f x then 1 else 0) law.mass * h true := by
  have point (x : X) : h (f x) = h false + (h true-h false)*(if f x then (1 : ℚ) else 0) := by
    cases hf : f x <;> simp [hf]
  unfold linearObjective
  simp_rw [point, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, law.total, mul_one]
  have scale : (∑ x, ((h true-h false)*(if f x then (1 : ℚ) else 0))*law.mass x) =
      (h true-h false)*∑ x, (if f x then (1 : ℚ) else 0)*law.mass x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [scale]
  ring

private theorem product_expectation {X Y : Type*} [Fintype X] [Fintype Y]
    (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y) (f : X × Y → ℚ) :
    linearObjective f (productResponseLaw left right).mass =
      linearObjective (fun x => linearObjective (fun y => f (x,y)) right.mass) left.mass := by
  rw [product_linearObjective_eq_left]
  congr 1
  funext x
  exact Finset.sum_congr rfl (fun y _ => mul_comm _ _)

/-- One joint law preserves the complete original table distribution, attains
all target means, and changes coordinate i with probability exactly |s_i-r_i|.
The result covers arbitrary dependence, null probabilities and boundary means. -/
theorem exists_exact_marginal_transport (original : FiniteResponseLaw (M → Bool))
    (target : M → ℚ) (target_mem : ∀ i, 0 ≤ target i ∧ target i ≤ 1) :
    ∃ joint : FiniteResponseLaw ((M → Bool) × (M → Bool)),
      (∀ f : (M → Bool) → ℚ,
        linearObjective (fun pair => f pair.1) joint.mass = linearObjective f original.mass) ∧
      (∀ i, linearObjective (fun pair => if pair.2 i then 1 else 0) joint.mass = target i) ∧
      (∀ i, linearObjective (fun pair => if pair.1 i ≠ pair.2 i then 1 else 0) joint.mass =
        |target i-tableMean original i|) := by
  classical
  let kernel := fun index : M × Bool => coinLaw
    (bitTransition (tableMean original index.1) (target index.1) index.2)
    (transition_bounds _ _ (tableMean_mem original index.1) (target_mem index.1) index.2)
  obtain ⟨noise, rows⟩ := finite_conditional_table_realization kernel
  have noise_mean (i : M) (b : Bool) :
      linearObjective (fun u => if u (i,b) then (1 : ℚ) else 0) noise.mass =
        bitTransition (tableMean original i) (target i) b := by
    have h := pushforward_linearObjective noise (fun u => u (i,b))
      (fun bit : Bool => if bit then (1 : ℚ) else 0)
    change linearObjective (fun bit : Bool => if bit then (1 : ℚ) else 0)
      (tableEvaluationLaw noise (i,b)).mass = _ at h
    rw [rows] at h
    calc
      _ = linearObjective (fun bit : Bool => if bit then (1 : ℚ) else 0) (kernel (i,b)).mass := h.symm
      _ = _ := by simp [kernel, coinLaw, linearObjective, Fintype.sum_bool]
  have noise_mismatch (i : M) (b : Bool) :
      linearObjective (fun u => if b ≠ u (i,b) then (1 : ℚ) else 0) noise.mass =
        if b then 1-bitTransition (tableMean original i) (target i) true
        else bitTransition (tableMean original i) (target i) false := by
    rw [expectation_bool noise (fun u => u (i,b))
      (fun bit : Bool => if b ≠ bit then (1 : ℚ) else 0), noise_mean]
    cases b <;> norm_num
  let joint := pushforwardResponseLaw (productResponseLaw original noise)
    (fun source => (source.1, fun i => source.2 (i,source.1 i)))
  have pair_expectation (f : ((M → Bool) × (M → Bool)) → ℚ) :
      linearObjective f joint.mass =
      linearObjective (fun y => linearObjective (fun u => f (y,fun i => u (i,y i))) noise.mass)
        original.mass := by
    change linearObjective f (pushforwardResponseLaw (productResponseLaw original noise) _).mass = _
    rw [pushforward_linearObjective, product_expectation]
  refine ⟨joint, ?_, ?_, ?_⟩
  · intro f
    rw [pair_expectation]
    have constant (y : M → Bool) : linearObjective (fun _ => f y) noise.mass = f y := by
      unfold linearObjective
      rw [← Finset.mul_sum, noise.total, mul_one]
    simp_rw [constant]
  · intro i
    rw [pair_expectation]
    simp_rw [noise_mean]
    rw [expectation_bool original (fun y => y i)
      (bitTransition (tableMean original i) (target i))]
    exact (transition_moments _ _ (tableMean_mem original i) (target_mem i)).1
  · intro i
    rw [pair_expectation]
    simp_rw [noise_mismatch]
    rw [expectation_bool original (fun y => y i)
      (fun b => if b then 1-bitTransition (tableMean original i) (target i) true
        else bitTransition (tableMean original i) (target i) false)]
    exact (transition_moments _ _ (tableMean_mem original i) (target_mem i)).2

#print axioms exists_exact_marginal_transport

end D5.S3.ConceptDynamics.CausalMoments.BooleanOutcomeMarginalTransport
