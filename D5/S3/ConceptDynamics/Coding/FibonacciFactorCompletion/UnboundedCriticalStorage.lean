/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedCriticalStorage
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedCriticalStorage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded actual return counts force linear complete primitive-operation storage. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

private theorem critical_supply (o : Ownership) (contract : Contract) (xs : List Return) :
    ActualPairSupply .original o lam contract xs := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have positive (pre : List Return) : 0 < execute .high pre (initial .high .original) := by
    have h := (actual_complete_boundary_geometry .original pre).2.2.1 .high pre.length 0 0
    simp only [List.take_length, pow_zero, one_mul] at h
    linarith [h.1]
  have strict : ActualPairSupply .original o lam .strict xs := by
    apply (actual_strict_cost_supply .original o lam xs (by linarith)).mpr
    refine ⟨?_, by simp, ?_⟩
    · have hp := mul_pos (mul_pos (pow_pos gp 2) cp) (positive xs)
      linarith
    · apply (exact_control_iff_split .high lam xs (initial .high .original)).mpr
      intro before a after he
      have hp := mul_pos (mul_pos (pow_pos gp 2) (pow_pos cp a.r)) (positive before)
      linarith
  cases contract with
  | strict => exact strict
  | closed =>
    intro j
    obtain ⟨err, herr, hread, hzero, hfuture⟩ := strict j
    exact ⟨err, fun p => (herr p).le, hread, hzero, hfuture⟩
  | recordMargin =>
    intro j
    obtain ⟨err, herr, hread, hzero, hfuture⟩ := strict j
    have bp : 0 < lam := (abs_nonneg (err 0)).trans_lt (herr 0)
    have gap (k : ℕ) : ∃ eps > 0, eps ≤ lam ∧ ∀ p, p < k → |err p| ≤ lam-eps := by
      induction k with
      | zero => exact ⟨lam/2, by linarith, by linarith, fun p hp => by omega⟩
      | succ k ih =>
        obtain ⟨eps, heps, heb, hgap⟩ := ih
        let delta := min eps ((lam-|err k|)/2)
        have dp : 0 < delta := lt_min heps (by linarith [herr k])
        have de : delta ≤ eps := min_le_left _ _
        have dk : delta ≤ (lam-|err k|)/2 := min_le_right _ _
        refine ⟨delta, dp, de.trans heb, ?_⟩
        intro p hp
        by_cases hold : p < k
        · linarith [hgap p hold]
        · have eq : p = k := by omega
          rw [eq]
          linarith [herr k]
    obtain ⟨eps, heps, heb, hgap⟩ := gap (history .original xs).length
    refine ⟨err, ⟨eps, heps, ?_⟩, hread, hzero, hfuture⟩
    intro p
    by_cases hp : p < (history .original xs).length
    · exact hgap p hp
    · rw [hzero p (by omega), abs_zero]
      linarith

private theorem critical_fiber_card (o : Ownership) (contract : Contract) (n : ℕ)
    (hn : 0 < n) :
    Nat.card {xs : List Return // ActualPairSupply .original o lam contract xs ∧ listWeight xs = 2*n}
      = returnCount n := by
  let e : {xs : List Return // ActualPairSupply .original o lam contract xs ∧ listWeight xs = 2*n}
      ≃ ReturnFiber n :=
    { toFun := fun xs => ⟨xs.val, by
        intro he
        have hw := xs.property.2
        simp [he, listWeight] at hw
        omega, xs.property.2⟩
      invFun := fun xs => ⟨xs.val, critical_supply o contract xs.val, xs.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- Every faithful encoding of complete primitive states has the all-horizon
critical lower bound. Processing, safety and finite-source liveness refer to all
actual records. Infinite peaks remain allowed. -/
theorem critical_decoder_storage {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (contract : Contract)
    (processing : Processing action initialConfiguration (OperationRecord o lam contract))
    (safety : ∀ a r, OperationRecord o lam contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration, 0, []⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o lam contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration, 0, []⟩ t ∧ p < t.output.length)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o lam contract) H c}) :
    ∀ N B : ℕ, Peak action initialConfiguration (OperationRecord o lam contract) encoding N
      ≤ (B : WithTop ℕ) → alphaInfinity*(N : ℝ)-107*alphaInfinity-1 ≤ (B : ℝ) := by
  intro N B hpeak
  have apos := actual_count_log_bounds.1
  by_cases hN : 88 ≤ N
  · let n := (N-26)/2
    have hn : 31 ≤ n := by dsimp [n]; omega
    have checkpoint : 26+2*n ≤ N := by dsimp [n]; omega
    have parity : N ≤ 27+2*n := by dsimp [n]; omega
    obtain ⟨family, cuts, member, card, cut, injection, states, capacity, fixed, monotone, traces⟩ :=
      original_operation_decoder_storage action initialConfiguration .original o lam contract (2*n)
        processing safety liveness encoding faithful
    have hcut : Peak action initialConfiguration (OperationRecord o lam contract) encoding (26+2*n)
        ≤ (B : WithTop ℕ) := (peak_monotone _ _ _ _ checkpoint).trans hpeak
    have count := capacity B hcut
    rw [critical_fiber_card o contract n (by omega)] at count
    have fp := (actual_count_log_bounds.2 n hn).1
    have lower := (actual_count_log_bounds.2 n hn).2.1
    have capReal : (returnCount n : ℝ) ≤ (2 : ℝ)^(B+1) := by
      exact_mod_cast count.trans (Nat.sub_le _ _)
    have upper := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) fp capReal
    rw [Real.logb_pow] at upper
    norm_num at upper
    have pn : (N : ℝ) ≤ 27+2*(n : ℝ) := by exact_mod_cast parity
    nlinarith
  · have small : (N : ℝ) < 88 := by exact_mod_cast (lt_of_not_ge hN)
    have bpos : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage
