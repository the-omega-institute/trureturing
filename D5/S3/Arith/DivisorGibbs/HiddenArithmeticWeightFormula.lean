/- GID: D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula
   generality: I
   mirror-B: D5/B/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual divisor Gibbs laws identify the hidden conditional entropy formula. -/

import Mathlib.Data.Finset.NatDivisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import D5.S3.Entropy.Fusion.QuotientFiberDecomposition
import D5.S3.Entropy.Forgetting.PushforwardComposition
import D5.S3.Entropy.MutualInformationProduct
import D5.S3.Entropy.MutualInformationEntropy

namespace D5.S3.Arith.DivisorGibbs.HiddenArithmeticWeightFormula

open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.PushforwardComposition
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open D5.S3.Entropy.Fusion.QuotientFiberDecomposition
open D5.S3.Entropy.MutualInformationProduct
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Divergence.ChainRule
open scoped BigOperators Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The actual finite carrier of positive divisors. -/
abbrev Div (n : Nat) := {d : Nat // d ∈ n.divisors}

/-- The real power weight, independently of entropy. -/
def weight {n : Nat} (s : Real) (d : Div n) : Real := (d.val : Real) ^ (-s)

/-- The finite divisor partition function. -/
def partition (n : Nat) (s : Real) : Real := ∑ d : Div n, weight s d

/-- The normalized divisor weight. -/
def mass (n : Nat) (s : Real) (d : Div n) : Real := weight s d / partition n s

private theorem divisor_pos {n : Nat} (d : Div n) : 0 < (d.val : Real) := by
  exact_mod_cast Nat.pos_of_mem_divisors d.property

private theorem weight_pos {n : Nat} (s : Real) (d : Div n) : 0 < weight s d :=
  Real.rpow_pos_of_pos (divisor_pos d) _

/-- Multiplication identifies the actual coprime divisor carriers. -/
def mulEquiv {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) : Div nJ × Div nT ≃ Div (nJ * nT) := by
  let f : Div nJ × Div nT → Div (nJ * nT) := fun ab =>
    ⟨ab.1.val * ab.2.val, Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors ab.1.property)
        (Nat.dvd_of_mem_divisors ab.2.property), (Nat.mul_pos hJ hT).ne'⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hv : (a.1.val, a.2.val) = (b.1.val, b.2.val) := hc.mul_injOn_divisors
      (by simpa only [Finset.mem_coe, Finset.mem_product] using
        And.intro a.1.property a.2.property)
      (by simpa only [Finset.mem_coe, Finset.mem_product] using
        And.intro b.1.property b.2.property) (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hv))
      (Subtype.ext (congrArg Prod.snd hv))
  · intro d
    have hd : d.val ∈ nJ.divisors * nT.divisors :=
      (Nat.divisors_mul nJ nT) ▸ d.property
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_mul.mp hd
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

/-- The observed divisor is the first inverse multiplication coordinate. -/
def qJ {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT) (hc : Nat.Coprime nJ nT)
    (d : Div (nJ * nT)) : Div nJ := ((mulEquiv hJ hT hc).symm d).1

/-- The hidden divisor is the second inverse multiplication coordinate. -/
def qT {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT) (hc : Nat.Coprime nJ nT)
    (d : Div (nJ * nT)) : Div nT := ((mulEquiv hJ hT hc).symm d).2

/-- The equivalence preserves the underlying natural multiplication. -/
theorem divisor_mul_equiv_val {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (a : Div nJ) (b : Div nT) :
    (mulEquiv hJ hT hc (a, b)).val = a.val * b.val := rfl

/-- Each actual full divisor has a unique factor pair. -/
theorem divisor_split_unique {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (d : Div (nJ * nT)) :
    ∃! ab : Div nJ × Div nT, ab.1.val * ab.2.val = d.val := by
  refine ⟨(mulEquiv hJ hT hc).symm d, ?_, ?_⟩
  · exact congrArg Subtype.val ((mulEquiv hJ hT hc).apply_symm_apply d)
  · intro ab hab
    apply (mulEquiv hJ hT hc).injective
    exact (Subtype.ext hab).trans ((mulEquiv hJ hT hc).apply_symm_apply d).symm

/-- The partition is positive at every real exponent. -/
theorem partition_pos {n : Nat} (hn : 0 < n) (s : Real) : 0 < partition n s := by
  let one : Div n := ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  exact Finset.sum_pos (fun d _ => weight_pos s d) ⟨one, Finset.mem_univ one⟩

private theorem weight_mul {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) (a : Div nJ) (b : Div nT) :
    weight s (mulEquiv hJ hT hc (a, b)) = weight s a * weight s b := by
  simp only [weight, divisor_mul_equiv_val, Nat.cast_mul]
  exact Real.mul_rpow (divisor_pos a).le (divisor_pos b).le

/-- Reindexing actual divisors yields coprime partition multiplicativity. -/
theorem partition_mul {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    partition (nJ * nT) s = partition nJ s * partition nT s := by
  rw [partition, ← (mulEquiv hJ hT hc).sum_comp]
  simp_rw [Fintype.sum_prod_type, weight_mul]
  exact (Fintype.sum_mul_sum _ _).symm

/-- Every actual divisor has strictly positive mass. -/
theorem mass_pos {n : Nat} (hn : 0 < n) (s : Real) (d : Div n) : 0 < mass n s d :=
  div_pos (weight_pos s d) (partition_pos hn s)

/-- The independently defined mass sums to one. -/
theorem mass_total {n : Nat} (hn : 0 < n) (s : Real) : ∑ d : Div n, mass n s d = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (partition_pos hn s).ne'

/-- Multiplication transports the full mass to the two independent divisor masses. -/
theorem mass_mul {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) (a : Div nJ) (b : Div nT) :
    mass (nJ * nT) s (mulEquiv hJ hT hc (a, b)) = mass nJ s a * mass nT s b := by
  simp only [mass, weight_mul, partition_mul hJ hT hc s]
  ring

/-- The full inverse decomposition pushes the actual law to its product law. -/
theorem split_pushforward {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    pushforward (fun d => (qJ hJ hT hc d, qT hJ hT hc d)) (mass (nJ * nT) s) =
      (fun ab : Div nJ × Div nT => mass nJ s ab.1 * mass nT s ab.2) := by
  classical
  funext ab
  rw [pushforward, ← (mulEquiv hJ hT hc).sum_comp]
  simp only [qJ, qT, Equiv.symm_apply_apply, Prod.mk.eta]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mass_mul hJ hT hc s ab.1 ab.2

/-- The observed marginal is the actual observed-factor Gibbs law. -/
theorem observer_pushforward {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    pushforward (qJ hJ hT hc) (mass (nJ * nT) s) = mass nJ s := by
  classical
  have h := pushforward_comp (mass (nJ * nT) s)
    (fun d => (qJ hJ hT hc d, qT hJ hT hc d)) Prod.fst
  rw [split_pushforward] at h
  change pushforward Prod.fst (fun ab : Div nJ × Div nT =>
    mass nJ s ab.1 * mass nT s ab.2) =
    pushforward (qJ hJ hT hc) (mass (nJ * nT) s) at h
  rw [← h]
  funext a
  simp only [pushforward, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.mul_sum, mass_total hT s, mul_one]

/-- The hidden marginal is the actual hidden-factor Gibbs law. -/
theorem hidden_pushforward {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    pushforward (qT hJ hT hc) (mass (nJ * nT) s) = mass nT s := by
  classical
  have h := pushforward_comp (mass (nJ * nT) s)
    (fun d => (qJ hJ hT hc d, qT hJ hT hc d)) Prod.snd
  rw [split_pushforward] at h
  change pushforward Prod.snd (fun ab : Div nJ × Div nT =>
    mass nJ s ab.1 * mass nT s ab.2) =
    pushforward (qT hJ hT hc) (mass (nJ * nT) s) at h
  rw [← h]
  funext b
  simp only [pushforward, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, mass_total hJ s, one_mul]

/-- The full-law hidden log expectation is the actual hidden-law expectation. -/
theorem hidden_log_expectation {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    (∑ d : Div (nJ * nT), mass (nJ * nT) s d * Real.log ((qT hJ hT hc d).val : Real)) =
      ∑ b : Div nT, mass nT s b * Real.log (b.val : Real) := by
  classical
  rw [← hidden_pushforward hJ hT hc s]
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp

/-- The observer-first graph retains exactly the hidden-factor entropy. -/
theorem observer_conditional_entropy {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    conditionalEntropy
      (pushforward (fun d => (qJ hJ hT hc d, d)) (mass (nJ * nT) s)) =
      shannonEntropy (mass nT s) := by
  classical
  let p : Div nJ × Div nT → Real := fun ab => mass nJ s ab.1 * mass nT s ab.2
  have hj : marginal p = mass nJ s := by
    funext a
    simp only [marginal, p, ← Finset.mul_sum, mass_total hT s, mul_one]
  have ht : marginal (fun ba => p (ba.2, ba.1)) = mass nT s := by
    funext b
    simp only [marginal, p, ← Finset.sum_mul, mass_total hJ s, one_mul]
  have hi := mutual_information_product_eq_zero (mass nJ s) (mass nT s)
    ⟨fun a => (mass_pos hJ s a).le, mass_total hJ s⟩
    ⟨fun b => (mass_pos hT s b).le, mass_total hT s⟩
  have ha := mutual_information_eq_entropy_sub p
    (fun ab => mul_nonneg (mass_pos hJ s ab.1).le (mass_pos hT s ab.2).le)
  rw [hj, ht] at ha
  have he := (pushforward_entropy_eq_iff_injective_on_support
    (mass (nJ * nT) s) (fun d => (qJ hJ hT hc d, qT hJ hT hc d))
    ⟨fun d => (mass_pos (Nat.mul_pos hJ hT) s d).le,
      mass_total (Nat.mul_pos hJ hT) s⟩).mpr
    (mulEquiv hJ hT hc).symm.injective.injOn
  rw [split_pushforward] at he
  have hg := (quotient_fiber_entropy_decomposition (mass (nJ * nT) s)
    (qJ hJ hT hc) (fun d => (mass_pos (Nat.mul_pos hJ hT) s d).le)
    (mass_total (Nat.mul_pos hJ hT) s)).2
  rw [observer_pushforward] at hg
  change shannonEntropy p = shannonEntropy (mass (nJ * nT) s) at he
  change _ = 0 at hi
  linarith

/-- The pointwise surprisal of an actual divisor is its finite Gibbs expression. -/
theorem neg_log_mass {n : Nat} (hn : 0 < n) (s : Real) (d : Div n) :
    -Real.log (mass n s d) = s * Real.log (d.val : Real) + Real.log (partition n s) := by
  rw [mass, Real.log_div (weight_pos s d).ne' (partition_pos hn s).ne']
  rw [weight, Real.log_rpow (divisor_pos d)]
  ring

/-- Finite normalization gives the actual divisor Gibbs entropy identity. -/
theorem gibbs_entropy {n : Nat} (hn : 0 < n) (s : Real) :
    shannonEntropy (mass n s) =
      s * (∑ d : Div n, mass n s d * Real.log (d.val : Real)) +
        Real.log (partition n s) := by
  have ht (d : Div n) : Real.negMulLog (mass n s d) =
      s * (mass n s d * Real.log (d.val : Real)) +
        mass n s d * Real.log (partition n s) := by
    have h := congrArg (fun x => mass n s d * x) (neg_log_mass hn s d)
    dsimp only [Real.negMulLog]
    nlinarith [h]
  simp only [shannonEntropy, ht, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, mass_total hn s, one_mul]

/-- The hidden arithmetic weight is the full-law observer-first conditional formula. -/
theorem hidden_arithmetic_weight_formula {nJ nT : Nat} (hJ : 0 < nJ) (hT : 0 < nT)
    (hc : Nat.Coprime nJ nT) (s : Real) :
    Real.log (partition nT s) =
      conditionalEntropy
        (pushforward (fun d => (qJ hJ hT hc d, d)) (mass (nJ * nT) s)) -
      s * (∑ d : Div (nJ * nT),
        mass (nJ * nT) s d * Real.log ((qT hJ hT hc d).val : Real)) := by
  rw [observer_conditional_entropy hJ hT hc s, hidden_log_expectation hJ hT hc s,
    gibbs_entropy hT s]
  ring

end

end D5.S3.Arith.DivisorGibbs.HiddenArithmeticWeightFormula
