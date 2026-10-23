/- GID: D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.claim; result=D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result; claim=D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.claim
   digest: Refutation of the binary-outcome detection threshold conjecture at m = 13. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#15572; Refuted)
Direct frozen dependencies: CycleSingleCutMinimax.push, ChainRule.marginal,
FutureWordInformationChain.marginal_nonnegative,
CompletionEntropyMinimality.pushforward_is_law, CapacityMonotone.pushforward,
SumProductUpdate.sum_prod_update, FiniteSimplexFiberPolytope.pushMass,
FiberwiseEqualDistanceLift.labelKernel, GreenClassWindowEntropy.windowLaw and windowLaw_sum_eq_one,
RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass.
The finite two-output pushforward applies CycleSingleCutMinimax.push to the product outcome space.
Its weighted-sum identity applies the linear map FiniteSimplexFiberPolytope.pushMass.
The two one-output marginals apply ChainRule.marginal, with the coordinates swapped for Bob.
Their nonnegativity applies FutureWordInformationChain.marginal_nonnegative to the corresponding joint laws.
Their normalization and the deterministic-strategy weights apply CompletionEntropyMinimality.pushforward_is_law.
The response indicators apply FiberwiseEqualDistanceLift.labelKernel on paired outputs.
The product bit law applies GreenClassWindowEntropy.windowLaw to the complemented ScoreBridge.bernoulliMass bits.
Its coordinate moment applies SumProductUpdate.sum_prod_update.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There are no other authored public theorems; additional public theorem audits without four-slot evidence are unfinished under https://github.com/the-omega-institute/trureturing/issues/15774.
RelaxedHardyNoSignallingOptimum.IsNSBox has binary inputs and d outcomes for N parties; here there are m inputs and binary outcomes for two parties.
Declaration judgements (all helpers are consumed; no supporting module is frozen separately):
proof_shape: IsNSBox: bind-only; definition; consumers: activity_bounds, admissible_bddAbove, edgeMass_bounds, edgeRatio_bounds, edgeRatio_identity, etaStar, lower_bound, marginalA_eq, marginalA_nonneg, marginalA_norm, marginalB_eq, marginalB_nonneg, marginalB_norm, matrixWeight_nonneg, rA_bounds, rB_bounds, reconstructed_eq, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, universal_local.
proof_shape: lossy: bind-only; definition; consumers: admissible_bddAbove, etaStar, generatedBox_local, lossy_mix, lossy_push, lower_bound, parityBox_local, qModel_eq_lossy, universal_local.
proof_shape: IsLocal: bind-only; definition; consumers: IsLocal_mix, IsLocal_push, admissible_bddAbove, etaStar, generatedBox_local, lower_bound, universal_local.
proof_shape: leaderA: bind-only; definition; consumers: atomS, orientation_count, rawA, rawA_count, rawB, rawB_count.
proof_shape: followerB: bind-only; definition; consumers: atomS, orientation_count, rawA, rawA_count, rawB_count.
proof_shape: followerA: bind-only; definition; consumers: atomS, orientation_count, rawB, rawB_count.
proof_shape: atomW: bind-only; definition; consumers: atomW_nonneg, atomW_sum, orientation_count, parityBox_local, qModel, qModel_eq_lossy, weightOf_sum.
proof_shape: atomS: bind-only; definition; consumers: orientation_count, parityBox_local, qModel, qModel_eq_lossy.
proof_shape: allF: bind-only; definition; consumers: parityBox_local.
proof_shape: beta: bind-only; definition; consumers: parityBox_local, qModel, qModel_eq_lossy.
proof_shape: qModel: bind-only; definition; consumers: parityBox_local, qModel_eq_lossy.
proof_shape: alpha: bind-only; definition; consumers: expected_sum, orientation_count, qModel_eq_lossy.
proof_shape: rawA: bind-only; definition; consumers: orientation_count, rawA_count, rawB_count.
proof_shape: countAExpected: bind-only; definition; consumers: expected_sum, orientation_count, qModel_eq_lossy, rawA_count, rawB_count.
proof_shape: rawA_count: bind-only; consumers: orientation_count, rawB_count.
proof_shape: rawB: bind-only; definition; consumers: orientation_count, rawB_count.
proof_shape: rawB_count: bind-only; consumers: orientation_count.
proof_shape: orientation_count: bind-only; consumers: qModel_eq_lossy.
proof_shape: hit_count: bind-only; consumers: miss_count, weighted_hit.
proof_shape: triple_count: bind-only; consumers: miss_count.
proof_shape: miss_count: bind-only; consumers: weighted_miss.
proof_shape: atomW_sum: bind-only; consumers: weightOf_sum.
proof_shape: delta: bind-only; definition; consumers: IsLocal_mix, IsLocal_of_atoms, IsLocal_push, parityBox_local, push_delta.
proof_shape: IsLocal_of_atoms: bind-only; consumers: IsLocal_mix, IsLocal_push, parityBox_local.
proof_shape: parityBox: bind-only; definition; consumers: generatedBox_local, generatedBox_push, parityBox_local, qModel_eq_lossy.
proof_shape: weighted_hit: bind-only; consumers: expected_sum.
proof_shape: weighted_miss: bind-only; consumers: expected_sum.
proof_shape: expected_sum: bind-only; consumers: qModel_eq_lossy.
proof_shape: qModel_eq_lossy: bind-only; consumers: parityBox_local.
proof_shape: atomW_nonneg: bind-only; consumers: parityBox_local.
proof_shape: weightOf_sum: bind-only; consumers: parityBox_local.
proof_shape: parityBox_local: bind-only; consumers: generatedBox_local.
proof_shape: etaStar: bind-only; definition; consumers: claim, result.
proof_shape: claim: bind-only; definition; consumers: result.
proof_shape: bitLaw: bind-only; definition; consumers: bitLaw_moment, bitLaw_nonneg, matrixWeight, reconstructed_minor_minor.
proof_shape: bitLaw_nonneg: bind-only; consumers: matrixWeight_nonneg.
proof_shape: bitLaw_sum: bind-only; consumers: matrixWeight_sum.
proof_shape: bitLaw_moment: bind-only; consumers: reconstructed_minor_minor.
proof_shape: active: bind-only; definition; consumers: active_measurable, layerWeight, layerWeight_nonneg, layerWeight_sum, layer_integrable, layer_moment, layer_pair, layer_single.
proof_shape: active_measurable: bind-only; consumers: layer_integrable.
proof_shape: layerWeight: bind-only; definition; consumers: layerWeight_sum, layer_moment, layer_pair, layer_single, reconstructedBox, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm, universal_local.
proof_shape: layer_integrable: bind-only; consumers: layerWeight_sum, layer_moment.
proof_shape: layerWeight_nonneg: bind-only; consumers: universal_local.
proof_shape: layerWeight_sum: bind-only; consumers: reconstructed_norm, universal_local.
proof_shape: layer_moment: bind-only; consumers: layer_pair, layer_single.
proof_shape: threshold_integral: bind-only; consumers: layer_pair, layer_single.
proof_shape: layer_single: bind-only; consumers: reconstructed_marginalA, reconstructed_marginalB.
proof_shape: layer_pair: bind-only; consumers: reconstructed_minor_minor.
proof_shape: IsLocal_mix: bind-only; consumers: universal_local.
proof_shape: push: bind-only; definition; consumers: IsLocal_push, generatedBox_local, generatedBox_push, lossy_push, push_delta, push_mix.
proof_shape: mapStrategy: bind-only; definition; consumers: IsLocal_push, push_delta.
proof_shape: push_delta: bind-only; consumers: IsLocal_push.
proof_shape: push_mix: bind-only; consumers: IsLocal_push.
proof_shape: IsLocal_push: bind-only; consumers: generatedBox_local.
proof_shape: marginalA: bind-only; definition; consumers: edgeMass_bounds, marginalA_nonneg, marginalA_norm, minorA, rA, rA_bounds, reconstructed_eq.
proof_shape: marginalB: bind-only; definition; consumers: edgeMass_bounds, marginalB_nonneg, marginalB_norm, minorB, rB, rB_bounds, reconstructed_eq.
proof_shape: marginalA_eq: bind-only; consumers: edgeMass_bounds, reconstructed_eq.
proof_shape: marginalB_eq: bind-only; consumers: edgeMass_bounds, reconstructed_eq.
proof_shape: marginalA_nonneg: bind-only; consumers: rA_bounds.
proof_shape: marginalB_nonneg: bind-only; consumers: rB_bounds.
proof_shape: marginalA_norm: bind-only; consumers: rA_bounds.
proof_shape: marginalB_norm: bind-only; consumers: rB_bounds.
proof_shape: minorA: bind-only; definition; consumers: edgeMass, edgeMass_bounds, generatedBox, generatedBox_local, generatedBox_push, rA, rA_bounds, reconstructed_eq, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm.
proof_shape: minorB: bind-only; definition; consumers: edgeMass, edgeMass_bounds, generatedBox, generatedBox_local, generatedBox_push, rB, rB_bounds, reconstructed_eq, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm.
proof_shape: rA: bind-only; definition; consumers: activity, activity_bounds, edgeCap, edgeMass_bounds, edgeRatio_bounds, rA_bounds, reconstructed_eq, reconstructed_marginalA, reconstructed_minor_minor.
proof_shape: rB: bind-only; definition; consumers: activity, activity_bounds, edgeCap, edgeMass_bounds, edgeRatio_bounds, rB_bounds, reconstructed_eq, reconstructed_marginalB, reconstructed_minor_minor.
proof_shape: rA_bounds: bind-only; consumers: activity_bounds, edgeRatio_bounds.
proof_shape: rB_bounds: bind-only; consumers: activity_bounds, edgeRatio_bounds.
proof_shape: edgeMass: bind-only; definition; consumers: edgeMass_bounds, edgeRatio, edgeRatio_bounds, edgeRatio_identity, reconstructed_minor_minor.
proof_shape: edgeCap: bind-only; definition; consumers: edgeMass_bounds, edgeRatio, edgeRatio_bounds, edgeRatio_identity, reconstructed_minor_minor.
proof_shape: edgeMass_bounds: bind-only; consumers: edgeRatio_bounds, edgeRatio_identity.
proof_shape: edgeRatio: bind-only; definition; consumers: edgeRatio_bounds, edgeRatio_identity, matrixWeight, matrixWeight_nonneg, matrixWeight_sum, reconstructed_minor_minor.
proof_shape: edgeRatio_bounds: bind-only; consumers: matrixWeight_nonneg.
proof_shape: edgeRatio_identity: bind-only; consumers: reconstructed_minor_minor.
proof_shape: activity: bind-only; definition; consumers: activity_bounds, reconstructedBox, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm, universal_local.
proof_shape: activity_bounds: bind-only; consumers: reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor.
proof_shape: outputBit: bind-only; definition; consumers: entry, entry_marginalA, entry_marginalB, entry_minor_minor, entry_norm, generatedBox_local, generatedBox_push.
proof_shape: entry: bind-only; definition; consumers: entry_marginalA, entry_marginalB, entry_minor_minor, entry_norm, generatedBox, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm.
proof_shape: entry_norm: bind-only; consumers: reconstructed_norm.
proof_shape: entry_marginalA: bind-only; consumers: reconstructed_marginalA.
proof_shape: entry_marginalB: bind-only; consumers: reconstructed_marginalB.
proof_shape: entry_minor_minor: bind-only; consumers: reconstructed_minor_minor.
proof_shape: generatedBox: bind-only; definition; consumers: generatedBox_local, generatedBox_push, reconstructedBox, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm, universal_local.
proof_shape: matrixWeight: bind-only; definition; consumers: reconstructedBox, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm, universal_local.
proof_shape: matrixWeight_sum: bind-only; consumers: reconstructed_marginalA, reconstructed_marginalB, reconstructed_norm, universal_local.
proof_shape: matrixWeight_nonneg: bind-only; consumers: universal_local.
proof_shape: reconstructedBox: bind-only; definition; consumers: reconstructed_eq, reconstructed_marginalA, reconstructed_marginalB, reconstructed_minor_minor, reconstructed_norm, universal_local.
proof_shape: sum_mixture: bind-only; consumers: reconstructed_marginalA, reconstructed_marginalB, reconstructed_norm.
proof_shape: reconstructed_norm: bind-only; consumers: reconstructed_eq.
proof_shape: reconstructed_marginalA: bind-only; consumers: reconstructed_eq.
proof_shape: reconstructed_marginalB: bind-only; consumers: reconstructed_eq.
proof_shape: reconstructed_minor_minor: bind-only; consumers: reconstructed_eq.
proof_shape: binary_eq: bind-only; consumers: reconstructed_eq.
proof_shape: reconstructed_eq: bind-only; consumers: universal_local.
proof_shape: lossy_push: bind-only; consumers: generatedBox_local.
proof_shape: lossy_mix: bind-only; consumers: universal_local.
proof_shape: generatedBox_push: bind-only; consumers: generatedBox_local.
proof_shape: generatedBox_local: bind-only; consumers: universal_local.
proof_shape: universal_local: bind-only; consumers: lower_bound.
proof_shape: admissible_bddAbove: bind-only; consumers: lower_bound.
proof_shape: lower_bound: bind-only; consumers: result.
proof_shape: result: bind-only; consumers: settling result.
-/

import D5.S3.TotalVariation.CycleSingleCutMinimax
import D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
import D5.S3.Entropy.NamingWindow.FutureWordInformationChain
import D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
import D5.S3.Entropy.NamingWindow.SumProductUpdate
import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
open scoped BigOperators
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
noncomputable section

def IsNSBox {m : ℕ} (p : Fin m → Fin m → Bool → Bool → ℝ) : Prop :=
  (∀ x y a b, 0 ≤ p x y a b) ∧
  (∀ x y, ∑ a, ∑ b, p x y a b = 1) ∧
  (∀ x y y' a, ∑ b, p x y a b = ∑ b, p x y' a b) ∧
  (∀ x x' y b, ∑ a, p x y a b = ∑ a, p x' y a b)

def lossy {m : ℕ} (η : ℝ) (p : Fin m → Fin m → Bool → Bool → ℝ) :
    Fin m → Fin m → Option Bool → Option Bool → ℝ :=
  fun x y a b => match a, b with
  | some a, some b => η ^ 2 * p x y a b
  | some a, none => η * (1 - η) * ∑ b, p x y a b
  | none, some b => η * (1 - η) * ∑ a, p x y a b
  | none, none => (1 - η) ^ 2

def IsLocal {m : ℕ} (q : Fin m → Fin m → Option Bool → Option Bool → ℝ) : Prop :=
  ∃ w : ((Fin m → Option Bool) × (Fin m → Option Bool)) → ℝ,
    (∀ s, 0 ≤ w s) ∧
    (∑ s, w s = 1) ∧
    (∀ x y a b, q x y a b = ∑ s, w s *
      (if s.1 x = a ∧ s.2 y = b then 1 else 0))

private def leaderA (i j k : (Fin 13)) (ri rj rk : Bool) (x : (Fin 13)) : (Option Bool) :=
  if x = i then some ri else if x = j then some rj else if x = k then some rk else none

private def followerB (G : (Fin 13) → (Fin 13) → Bool) (i j k : (Fin 13)) (ri rj rk : Bool) (y : (Fin 13)) : (Option Bool) :=
  let u := ri.xor (G i y)
  let v := rj.xor (G j y)
  let w := rk.xor (G k y)
  if (u = v ∧ u = w) then some u else none

private def followerA (G : (Fin 13) → (Fin 13) → Bool) (i j k : (Fin 13)) (ri rj rk : Bool) (x : (Fin 13)) : (Option Bool) :=
  let u := ri.xor (G x i)
  let v := rj.xor (G x j)
  let w := rk.xor (G x k)
  if (u = v ∧ u = w) then some u else none

private def atomW (G : (Fin 13) → (Fin 13) → Bool) (i j k : (Fin 13)) (ri rj rk : Bool) (ori : Bool) :
    ℝ :=
  if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then
    (48 * (13 : ℝ) / (25^2 : ℝ)) / (2 * (13:ℝ) * 12 * 11 * 8)
  else 0

private def atomS (G : (Fin 13) → (Fin 13) → Bool) (i j k : (Fin 13)) (ri rj rk : Bool) (ori : Bool) :
    ((Fin 13) → (Option Bool)) × ((Fin 13) → (Option Bool)) :=
  if ori then (followerA G i j k ri rj rk, leaderA i j k ri rj rk)
  else (leaderA i j k ri rj rk, followerB G i j k ri rj rk)

private def allF : ((Fin 13) → (Option Bool)) × ((Fin 13) → (Option Bool)) := (fun _ => none, fun _ => none)

private def beta : ℝ := ((13 - 12 : ℝ)^2) / 25^2

private def qModel (G : (Fin 13) → (Fin 13) → Bool) (x y : (Fin 13)) (a b : (Option Bool)) : ℝ :=
  (if a = none ∧ b = none then beta else 0) +
    ∑ i, ∑ j, ∑ k, ∑ ri : Bool, ∑ rj : Bool, ∑ rk : Bool, ∑ ori : Bool,
      atomW G i j k ri rj rk ori *
        (if (atomS G i j k ri rj rk ori).1 x = a ∧
            (atomS G i j k ri rj rk ori).2 y = b then 1 else 0)

private def alpha : ℝ := (48 * (13 : ℝ) / (25^2 : ℝ)) / (2 * (13:ℝ) * 12 * 11 * 8)

private def rawA (G : (Fin 13) → (Fin 13) → Bool) (i j k x y : (Fin 13)) (ri rj rk : Bool) (a b : (Option Bool)) : ℝ :=
  D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel (fun _ : Unit => (leaderA i j k ri rj rk x, followerB G i j k ri rj rk y)) () (a, b)

private def countAExpected (G : (Fin 13) → (Fin 13) → Bool) (x y i j k : (Fin 13)) (a b : (Option Bool)) : ℝ :=
  match a,b with
  | some a, some b => if (x = i ∨ x = j ∨ x = k) ∧ a.xor b = G x y then 1 else 0
  | some _, none => if (x = i ∨ x = j ∨ x = k) then 3 else 0
  | none, some _ => if (x = i ∨ x = j ∨ x = k) then 0 else 1
  | none, none => if (x = i ∨ x = j ∨ x = k) then 0 else 6

set_option maxHeartbeats 10000000 in
private lemma rawA_count (G : (Fin 13) → (Fin 13) → Bool) (i j k x y : (Fin 13)) (a b : (Option Bool))
    (hD : (i ≠ j ∧ i ≠ k ∧ j ≠ k)) :
    (∑ ri : Bool, ∑ rj : Bool, ∑ rk : Bool, rawA G i j k x y ri rj rk a b) =
      countAExpected G x y i j k a b := by
  rcases hD with ⟨hij, hik, hjk⟩
  by_cases hxi : x = i
  · subst x
    fin_cases a <;> fin_cases b
    all_goals
      generalize h1 : G i y = u
      generalize h2 : G j y = v
      generalize h3 : G k y = w
      fin_cases u <;> fin_cases v <;> fin_cases w <;>
        norm_num [rawA, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, countAExpected, h1, h2, h3, hij, hik, hjk,
          hij.symm, hik.symm, hjk.symm, leaderA, followerB, Bool.xor,
          Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
  · by_cases hxj : x = j
    · subst x
      fin_cases a <;> fin_cases b
      all_goals
        generalize h1 : G i y = u
        generalize h2 : G j y = v
        generalize h3 : G k y = w
        fin_cases u <;> fin_cases v <;> fin_cases w <;>
          norm_num [rawA, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, countAExpected, h1, h2, h3, hij, hik, hjk,
            hij.symm, hik.symm, hjk.symm, leaderA, followerB, Bool.xor,
            Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
    · by_cases hxk : x = k
      · subst x
        fin_cases a <;> fin_cases b
        all_goals
          generalize h1 : G i y = u
          generalize h2 : G j y = v
          generalize h3 : G k y = w
          fin_cases u <;> fin_cases v <;> fin_cases w <;>
            norm_num [rawA, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, countAExpected, h1, h2, h3, hij, hik, hjk,
              hij.symm, hik.symm, hjk.symm, leaderA, followerB, Bool.xor,
              Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
      · fin_cases a <;> fin_cases b
        all_goals
          generalize h1 : G i y = u
          generalize h2 : G j y = v
          generalize h3 : G k y = w
          fin_cases u <;> fin_cases v <;> fin_cases w <;>
            norm_num [rawA, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, countAExpected, h1, h2, h3, hij, hik, hjk,
              hij.symm, hik.symm, hjk.symm, hxi, hxj, hxk, leaderA, followerB,
              Bool.xor, Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num

private def rawB (G : (Fin 13) → (Fin 13) → Bool) (i j k x y : (Fin 13)) (ri rj rk : Bool) (a b : (Option Bool)) : ℝ :=
  D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel (fun _ : Unit => (followerA G i j k ri rj rk x, leaderA i j k ri rj rk y)) () (a, b)

private lemma rawB_count (G : (Fin 13) → (Fin 13) → Bool) (i j k x y : (Fin 13)) (a b : (Option Bool))
    (hD : (i ≠ j ∧ i ≠ k ∧ j ≠ k)) :
    (∑ ri : Bool, ∑ rj : Bool, ∑ rk : Bool, rawB G i j k x y ri rj rk a b) =
      countAExpected (fun u v => G v u) y x i j k b a := by
  have heq (ri rj rk : Bool) : rawB G i j k x y ri rj rk a b =
      rawA (fun u v => G v u) i j k y x ri rj rk b a := by
    simp [rawA, rawB, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, leaderA, followerA, followerB, and_comm]
  simp_rw [heq]
  exact rawA_count (fun u v => G v u) i j k y x b a hD

private lemma orientation_count (G : (Fin 13) → (Fin 13) → Bool) (i j k x y : (Fin 13)) (a b : (Option Bool)) :
    (∑ ri : Bool, ∑ rj : Bool, ∑ rk : Bool, ∑ ori : Bool,
      atomW G i j k ri rj rk ori *
        (if (atomS G i j k ri rj rk ori).1 x = a ∧
            (atomS G i j k ri rj rk ori).2 y = b then 1 else 0)) =
      (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha *
        (countAExpected G x y i j k a b +
         countAExpected (fun u v => G v u) y x i j k b a) else 0) := by
  by_cases hD : (i ≠ j ∧ i ≠ k ∧ j ≠ k)
  · have hw (ri rj rk ori : Bool) : atomW G i j k ri rj rk ori = alpha := by
      simp [atomW, alpha, hD]
    have hs (ri rj rk : Bool) :
        (∑ ori : Bool, atomW G i j k ri rj rk ori *
          (if (atomS G i j k ri rj rk ori).1 x = a ∧
              (atomS G i j k ri rj rk ori).2 y = b then 1 else 0)) =
          alpha * rawA G i j k x y ri rj rk a b +
          alpha * rawB G i j k x y ri rj rk a b := by
      simp [atomS, hw, rawA, rawB, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, add_comm]
    simp_rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [rawA_count G i j k x y a b hD, rawB_count G i j k x y a b hD]
    simp [hD]
    ring
  · simp [atomW, hD]

set_option maxHeartbeats 10000000 in
private lemma hit_count (x : (Fin 13)) :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13),
      if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then (1 : ℝ) else 0) = 396 := by
  fin_cases x <;> simp [-Finset.sum_boole, Fin.sum_univ_succ] <;> norm_num
private lemma triple_count :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13), if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then (1 : ℝ) else 0) = 1716 := by
  simp [-Finset.sum_boole, Fin.sum_univ_succ]
  norm_num
private lemma miss_count (x : (Fin 13)) :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13),
      if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then (1 : ℝ) else 0) = 1320 := by
  have heq (i j k : (Fin 13)) :
      (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then (1 : ℝ) else 0) =
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then 1 else 0) +
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then 1 else 0) := by
    by_cases hd : (i ≠ j ∧ i ≠ k ∧ j ≠ k) <;> by_cases hh : (x = i ∨ x = j ∨ x = k) <;> simp [hd,hh]
  have h := triple_count
  simp_rw [heq, Finset.sum_add_distrib] at h
  rw [hit_count] at h
  linarith

private lemma atomW_sum (G : (Fin 13) → (Fin 13) → Bool) :
    (∑ i, ∑ j, ∑ k, ∑ ri : Bool, ∑ rj : Bool, ∑ rk : Bool, ∑ ori : Bool,
      atomW G i j k ri rj rk ori) = (48 * (13 : ℝ) / (25^2 : ℝ)) := by
  simp [atomW, Fin.sum_univ_succ]
  norm_num

variable {m : ℕ}

private def delta (s : ((Fin m → Option Bool) × (Fin m → Option Bool))) (x y : Fin m) (a b : Option Bool) : ℝ :=
  D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel (fun _ : Unit => (s.1 x, s.2 y)) () (a, b)
private lemma IsLocal_of_atoms {I : Type} [Fintype I] (w : I → ℝ)
    (S : I → ((Fin m → Option Bool) × (Fin m → Option Bool))) (q : (Fin m → Fin m → Option Bool → Option Bool → ℝ))
    (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1)
    (hq : ∀ x y a b, q x y a b = ∑ i, w i * delta (S i) x y a b) : IsLocal q := by
  classical
  have hLaw := D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law w S ⟨hw, hs⟩
  refine ⟨D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward S w, hLaw.1, hLaw.2, ?_⟩
  · intro x y a b
    rw [hq]
    simp only [D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward,
      delta, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single (S i)]
    · simp
    · intro s hs hne
      simp [Ne.symm hne]
    · simp

private def parityBox (G : (Fin 13) → (Fin 13) → Bool) (x y : (Fin 13)) (a b : Bool) : ℝ :=
  if a.xor b = G x y then 1 / 2 else 0

private lemma weighted_hit (x : (Fin 13)) (v : ℝ) :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13), if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then v else 0) = 396 * v := by
  have heq (i j k : (Fin 13)) :
      (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then v else 0) =
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then (1 : ℝ) else 0) * v := by
    split_ifs <;> simp
  simp_rw [heq, ← Finset.sum_mul]
  rw [hit_count]
private lemma weighted_miss (x : (Fin 13)) (v : ℝ) :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13), if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then v else 0) = 1320 * v := by
  have heq (i j k : (Fin 13)) :
      (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then v else 0) =
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then (1 : ℝ) else 0) * v := by
    split_ifs <;> simp
  simp_rw [heq, ← Finset.sum_mul]
  rw [miss_count]

private lemma expected_sum (G : (Fin 13) → (Fin 13) → Bool) (x y : (Fin 13)) (a b : Option Bool) :
    (∑ i : (Fin 13), ∑ j : (Fin 13), ∑ k : (Fin 13),
      if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha * countAExpected G x y i j k a b else 0) =
      match a,b with
      | some a, some b => if a.xor b = G x y then 9/625 else 0
      | some _, none => 27/625
      | none, some _ => 6/125
      | none, none => 36/125 := by
  cases a with
  | none =>
    cases b with
    | none =>
      have hf (i j k : (Fin 13)) :
          (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha * countAExpected G x y i j k none none else 0) =
            if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then alpha*6 else 0 := by
        by_cases hd : (i ≠ j ∧ i ≠ k ∧ j ≠ k) <;> by_cases hh : (x = i ∨ x = j ∨ x = k) <;>
          simp [countAExpected, hd,hh]
      simp_rw [hf]
      rw [weighted_miss]
      norm_num [alpha]
    | some b =>
      have hf (i j k : (Fin 13)) :
          (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha * countAExpected G x y i j k none (some b) else 0) =
            if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ ¬ (x = i ∨ x = j ∨ x = k) then alpha else 0 := by
        by_cases hd : (i ≠ j ∧ i ≠ k ∧ j ≠ k) <;> by_cases hh : (x = i ∨ x = j ∨ x = k) <;>
          simp [countAExpected, hd,hh]
      simp_rw [hf]
      rw [weighted_miss]
      norm_num [alpha]
  | some a =>
    cases b with
    | none =>
      have hf (i j k : (Fin 13)) :
          (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha * countAExpected G x y i j k (some a) none else 0) =
            if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then alpha*3 else 0 := by
        by_cases hd : (i ≠ j ∧ i ≠ k ∧ j ≠ k) <;> by_cases hh : (x = i ∨ x = j ∨ x = k) <;>
          simp [countAExpected, hd,hh]
      simp_rw [hf]
      rw [weighted_hit]
      norm_num [alpha]
    | some b =>
      by_cases hp : a.xor b = G x y
      · have hf (i j k : (Fin 13)) :
            (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha * countAExpected G x y i j k (some a) (some b) else 0) =
              if (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ (x = i ∨ x = j ∨ x = k) then alpha else 0 := by
          by_cases hd : (i ≠ j ∧ i ≠ k ∧ j ≠ k) <;> by_cases hh : (x = i ∨ x = j ∨ x = k) <;>
            simp [countAExpected, hp,hd,hh]
        simp_rw [hf]
        rw [weighted_hit]
        norm_num [alpha,hp]
      · simp [countAExpected, hp]

private lemma qModel_eq_lossy (G : (Fin 13) → (Fin 13) → Bool) : qModel G = lossy (6/25) (parityBox G) := by
  funext x y a b
  unfold qModel
  simp_rw [orientation_count]
  have hf (i j k : (Fin 13)) :
      (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha*(countAExpected G x y i j k a b +
        countAExpected (fun u v => G v u) y x i j k b a) else 0) =
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha*countAExpected G x y i j k a b else 0) +
        (if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then alpha*countAExpected (fun u v => G v u) y x i j k b a else 0) := by
    split_ifs <;> ring
  simp_rw [hf, Finset.sum_add_distrib]
  rw [expected_sum, expected_sum]
  fin_cases a <;> fin_cases b
  all_goals
    generalize hG : G x y = v
    fin_cases v <;> norm_num [lossy, parityBox, beta, Bool.xor, hG] <;> simp <;> norm_num

private lemma atomW_nonneg (G : (Fin 13) → (Fin 13) → Bool) (i j k : (Fin 13)) (ri rj rk ori : Bool) :
    0 ≤ atomW G i j k ri rj rk ori := by
  unfold atomW
  split_ifs <;> norm_num

private lemma weightOf_sum (G : (Fin 13) → (Fin 13) → Bool) : (∑ z : (Fin 13 × Fin 13 × Fin 13 × Bool × Bool × Bool × Bool), (atomW G z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2)) = 624 / 625 := by
  simp only [Fintype.sum_prod_type]
  rw [atomW_sum]
  norm_num

private lemma parityBox_local (G : (Fin 13) → (Fin 13) → Bool) : IsLocal (lossy (6/25) (parityBox G)) := by
  apply IsLocal_of_atoms
    (fun z : Option (Fin 13 × Fin 13 × Fin 13 × Bool × Bool × Bool × Bool) => match z with | none => beta | some z => (atomW G z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2))
    (fun z : Option (Fin 13 × Fin 13 × Fin 13 × Bool × Bool × Bool × Bool) => match z with | none => allF | some z => (atomS G z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2))
  · intro z
    cases z with
    | none => norm_num [beta]
    | some z => exact atomW_nonneg G _ _ _ _ _ _ _
  · rw [Fintype.sum_option]
    simp only [weightOf_sum]
    norm_num [beta]
  · intro x y a b
    rw [← qModel_eq_lossy]
    rw [Fintype.sum_option]
    simp only [Fintype.sum_prod_type, delta, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, allF]
    change qModel G x y a b = _
    unfold qModel
    have hz : (if a = none ∧ b = none then beta else 0) =
      beta * (if none = a ∧ none = b then (1 : ℝ) else 0) := by
      by_cases h : a = none ∧ b = none
      · rcases h with ⟨rfl,rfl⟩; simp
      · have hn : ¬(none = a ∧ none = b) := by simpa [eq_comm] using h
        simp [h,hn]
    rw [hz]

noncomputable def etaStar (m : ℕ) : ℝ :=
  sSup {η : ℝ | 0 ≤ η ∧ η ≤ 1 ∧
    ∀ p : Fin m → Fin m → Bool → Bool → ℝ, IsNSBox p → IsLocal (lossy η p)}

def claim : Prop := ∀ m : ℕ, 2 ≤ m → etaStar m = 4 / (m + 4)

variable {I : Type} [Fintype I] [DecidableEq I]
private def bitLaw (r : I → ℝ) (s : I → Bool) : ℝ :=
  D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy.windowLaw (fun i b => D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass (r i) (!b)) s
private lemma bitLaw_nonneg (r : I → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (s : I → Bool) :
    0 ≤ bitLaw r s := by
  unfold bitLaw D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy.windowLaw
  apply Finset.prod_nonneg
  intro i hi
  by_cases h : s i = true <;> simp [D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass, h, (hr i).1, sub_nonneg.mpr (hr i).2]
private lemma bitLaw_sum (r : I → ℝ) : (∑ s, bitLaw r s) = 1 := by
  apply D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy.windowLaw_sum_eq_one
  intro i
  simp [D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass]
private lemma bitLaw_moment (r : I → ℝ) (i : I) (f : Bool → ℝ) :
    (∑ s, bitLaw r s * f (s i)) = r i * f false + (1 - r i) * f true := by
  classical
  let p := fun j b => D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass (r j) (!b)
  have hg (s : I → Bool) :
      bitLaw r s * f (s i) =
        (∏ j ∈ Finset.univ.erase i, p j (s j)) * (p i (s i) * f (s i)) := by
    change (∏ j, p j (s j)) * f (s i) = _
    rw [← Finset.mul_prod_erase _ (fun j => p j (s j)) (Finset.mem_univ i)]
    ring
  simp_rw [hg]
  rw [D5.S3.Entropy.NamingWindow.SumProductUpdate.sum_prod_update p i (fun a => p i a * f a)]
  simp [p, D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge.bernoulliMass, add_comm]

private def active (u : I → ℝ) (t : ℝ) : I → Bool := fun i => decide (t ≤ u i)
private lemma active_measurable (u : I → ℝ) : Measurable (active u) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun t : ℝ => decide (t ≤ u i))
  have h : (fun t : ℝ => decide (t ≤ u i)) = (Iic (u i)).piecewise (fun _ => true) (fun _ => false) := by
    funext t
    simp [Set.piecewise, decide_eq_true_eq]
  rw [h]
  exact measurable_const.piecewise measurableSet_Iic measurable_const

private def layerWeight (u : I → ℝ) (s : I → Bool) : ℝ :=
  ∫ t, if active u t = s then 1 else 0 ∂(volume.restrict (Icc (0 : ℝ) 1))
private lemma layer_integrable (u : I → ℝ) (s : I → Bool) :
    Integrable (fun t => if active u t = s then (1 : ℝ) else 0) (volume.restrict (Icc (0 : ℝ) 1)) := by
  classical
  have hm : MeasurableSet {t | active u t = s} :=
    measurableSet_eq_fun (active_measurable u) measurable_const
  have hfun : (fun t => if active u t = s then (1 : ℝ) else 0) =
      {t | active u t = s}.indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases h : active u t = s <;> simp [h]
  rw [hfun]
  exact (integrable_const (μ := (volume.restrict (Icc (0 : ℝ) 1))) (1 : ℝ)).indicator hm
private lemma layerWeight_nonneg (u : I → ℝ) (s : I → Bool) : 0 ≤ layerWeight u s := by
  apply integral_nonneg
  intro t
  by_cases h : active u t = s <;> simp [h]
private lemma layerWeight_sum (u : I → ℝ) : (∑ s, layerWeight u s) = 1 := by
  unfold layerWeight
  rw [← integral_finset_sum _ (fun s _ => layer_integrable u s)]
  simp [Finset.sum_ite_eq, Real.volume_Icc]

private lemma layer_moment (u : I → ℝ) (f : (I → Bool) → ℝ) :
    (∑ s, layerWeight u s * f s) = ∫ t, f (active u t) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  classical
  unfold layerWeight
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun s _ => (layer_integrable u s).mul_const (f s))]
  congr 1
  funext t
  rw [Finset.sum_eq_single (active u t)]
  · simp
  · intro s hs hne
    simp [Ne.symm hne]
  · simp

private lemma threshold_integral (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, if t ≤ v then (1 : ℝ) else 0 ∂(volume.restrict (Icc (0 : ℝ) 1))) = v := by
  have hfun : (fun t => if t ≤ v then (1 : ℝ) else 0) =
      (Iic v).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases h : t ≤ v <;> simp [h]
  rw [hfun, integral_indicator measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hsets : Iic v ∩ Icc (0 : ℝ) 1 = Icc 0 v := by
    ext t; simp; constructor <;> intro h
    · exact ⟨h.2.1,h.1⟩
    · exact ⟨h.2,h.1, le_trans h.2 hv1⟩
  rw [hsets, integral_const]
  simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hv0]

private lemma layer_single (u : I → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) (i : I) :
    (∑ s, layerWeight u s * (if s i then 1 else 0)) = u i := by
  rw [layer_moment]
  simp only [active, decide_eq_true_eq]
  exact threshold_integral (u i) (hu0 i) (hu1 i)

private lemma layer_pair (u : I → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) (i j : I) :
    (∑ s, layerWeight u s * (if s i && s j then 1 else 0)) = min (u i) (u j) := by
  rw [layer_moment]
  have hfun : (fun t => if active u t i && active u t j then (1 : ℝ) else 0) =
      fun t => if t ≤ min (u i) (u j) then (1 : ℝ) else 0 := by
    funext t
    simp [active, le_min_iff]
  rw [hfun]
  exact threshold_integral _ (le_min (hu0 i) (hu0 j)) (le_trans (min_le_left _ _) (hu1 i))

variable {m : ℕ}

private lemma IsLocal_mix {I : Type} [Fintype I] (w : I → ℝ) (q : I → (Fin m → Fin m → Option Bool → Option Bool → ℝ))
    (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1) (hq : ∀ i, IsLocal (q i)) :
    IsLocal (fun x y a b => ∑ i, w i * q i x y a b) := by
  classical
  choose v hv hn he using hq
  apply IsLocal_of_atoms (fun z : I × ((Fin m → Option Bool) × (Fin m → Option Bool)) => w z.1 * v z.1 z.2) (fun z => z.2)
  · intro z
    exact mul_nonneg (hw z.1) (hv z.1 z.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hn, mul_one]
    exact hs
  · intro x y a b
    rw [Fintype.sum_prod_type]
    simp_rw [he, Finset.mul_sum, delta, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq, mul_assoc]

private def push {A B : Type} [Fintype A] [Fintype B] (q : Fin m → Fin m → A → B → ℝ)
    (f : Fin m → A → A) (g : Fin m → B → B) : Fin m → Fin m → A → B → ℝ :=
  fun x y a b => D5.S3.TotalVariation.CycleSingleCutMinimax.push
    (fun z : A × B => (f x z.1, g y z.2)) (fun z => q x y z.1 z.2) (a, b)

private def mapStrategy (f g : Fin m → Option Bool → Option Bool) (s : ((Fin m → Option Bool) × (Fin m → Option Bool))) : ((Fin m → Option Bool) × (Fin m → Option Bool)) :=
  Prod.map (fun sa x => f x (sa x)) (fun sb y => g y (sb y)) s

private lemma push_delta (f g : Fin m → Option Bool → Option Bool) (s : ((Fin m → Option Bool) × (Fin m → Option Bool)))
    (x y : Fin m) (a b : Option Bool) :
    push (delta s) f g x y a b = delta (mapStrategy f g s) x y a b := by
  unfold push D5.S3.TotalVariation.CycleSingleCutMinimax.push delta D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel mapStrategy
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  trans ∑ c : Option Bool, ∑ d : Option Bool,
    if s.1 x = c then if s.2 y = d then
      (if f x (s.1 x) = a ∧ g y (s.2 y) = b then (1 : ℝ) else 0) else 0 else 0
  · apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : s.1 x = c <;> by_cases hd : s.2 y = d <;> simp [hc, hd]
  · simp

private lemma push_mix {I : Type} [Fintype I] {A B : Type} [Fintype A] [Fintype B]
    (w : I → ℝ) (q : I → Fin m → Fin m → A → B → ℝ)
    (f : Fin m → A → A) (g : Fin m → B → B) :
    push (fun x y a b => ∑ i, w i*q i x y a b) f g =
      fun x y a b => ∑ i, w i*push (q i) f g x y a b := by
  classical
  funext x y a b
  let L := D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass
    (fun z : A × B => (f x z.1, g y z.2))
  have h := congrFun (map_sum L (fun i => w i • (fun z : A × B => q i x y z.1 z.2)) Finset.univ) (a, b)
  simp only [map_smul] at h
  dsimp [L, D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass] at h
  simpa only [push,
    D5.S3.TotalVariation.CycleSingleCutMinimax.push, Fintype.sum_prod_type, Prod.mk.injEq, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using h


private lemma IsLocal_push (q : (Fin m → Fin m → Option Bool → Option Bool → ℝ)) (hq : IsLocal q)
    (f g : Fin m → Option Bool → Option Bool) : IsLocal (push q f g) := by
  obtain ⟨w, hw, hs, he⟩ := hq
  have heq : q = fun x y a b => ∑ s, w s * delta s x y a b := by
    funext x y a b
    simpa only [delta, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel, Prod.mk.injEq] using he x y a b
  rw [heq, push_mix]
  apply IsLocal_of_atoms w (mapStrategy f g) _ hw hs
  intro x y a b
  simp_rw [push_delta]

private def marginalA (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x : (Fin 13)) (a : Bool) : ℝ :=
  D5.S3.Divergence.ChainRule.marginal (fun z : Bool × Bool => p x 0 z.1 z.2) a
private def marginalB (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (y : (Fin 13)) (b : Bool) : ℝ :=
  D5.S3.Divergence.ChainRule.marginal (fun z : Bool × Bool => p 0 y z.2 z.1) b
private lemma marginalA_eq (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) (a : Bool) :
    marginalA p x a = ∑ b, p x y a b := by
  exact hp.2.2.1 x 0 y a
private lemma marginalB_eq (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) (b : Bool) :
    marginalB p y b = ∑ a, p x y a b := by
  exact hp.2.2.2 0 x y b
private lemma marginalA_nonneg (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x : (Fin 13)) (a : Bool) :
    0 ≤ marginalA p x a := by
  exact D5.S3.Entropy.NamingWindow.FutureWordInformationChain.marginal_nonnegative
    (fun z : Bool × Bool => p x 0 z.1 z.2) (fun z => hp.1 x 0 z.1 z.2) a
private lemma marginalB_nonneg (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (y : (Fin 13)) (b : Bool) :
    0 ≤ marginalB p y b := by
  exact D5.S3.Entropy.NamingWindow.FutureWordInformationChain.marginal_nonnegative
    (fun z : Bool × Bool => p 0 y z.2 z.1) (fun z => hp.1 0 y z.2 z.1) b
private lemma marginalA_norm (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x : (Fin 13)) :
    marginalA p x false + marginalA p x true = 1 := by
  have h := (D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law
    (fun z : Bool × Bool => p x 0 z.1 z.2) Prod.fst
    ⟨(fun z => hp.1 x 0 z.1 z.2), by
      simpa only [Fintype.sum_prod_type] using hp.2.1 x 0⟩).2
  simpa [D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward, Fintype.sum_prod_type,
    marginalA, D5.S3.Divergence.ChainRule.marginal, add_comm] using h
private lemma marginalB_norm (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (y : (Fin 13)) :
    marginalB p y false + marginalB p y true = 1 := by
  have h := (D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law
    (fun z : Bool × Bool => p 0 y z.2 z.1) Prod.fst
    ⟨(fun z => hp.1 0 y z.2 z.1), by
      simpa [Fintype.sum_prod_type, add_comm, add_left_comm, add_assoc] using hp.2.1 0 y⟩).2
  simpa [D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward, Fintype.sum_prod_type,
    marginalB, D5.S3.Divergence.ChainRule.marginal, add_comm] using h

private def minorA (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x : (Fin 13)) : Bool := if marginalA p x false ≤ 1 / 2 then false else true
private def minorB (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (y : (Fin 13)) : Bool := if marginalB p y false ≤ 1 / 2 then false else true
private def rA (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x : (Fin 13)) : ℝ := marginalA p x (minorA p x)
private def rB (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (y : (Fin 13)) : ℝ := marginalB p y (minorB p y)
private lemma rA_bounds (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x : (Fin 13)) : 0 ≤ rA p x ∧ rA p x ≤ 1 / 2 := by
  unfold rA minorA
  split_ifs with h
  · exact ⟨marginalA_nonneg p hp x false,h⟩
  · refine ⟨marginalA_nonneg p hp x true,?_⟩
    have hn := marginalA_norm p hp x
    linarith
private lemma rB_bounds (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (y : (Fin 13)) : 0 ≤ rB p y ∧ rB p y ≤ 1 / 2 := by
  unfold rB minorB
  split_ifs with h
  · exact ⟨marginalB_nonneg p hp y false,h⟩
  · refine ⟨marginalB_nonneg p hp y true,?_⟩
    have hn := marginalB_norm p hp y
    linarith

private def edgeMass (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x y : (Fin 13)) : ℝ := p x y (minorA p x) (minorB p y)
private def edgeCap (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x y : (Fin 13)) : ℝ := min (rA p x) (rB p y)
private lemma edgeMass_bounds (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    0 ≤ edgeMass p x y ∧ edgeMass p x y ≤ edgeCap p x y := by
  unfold edgeMass
  refine ⟨hp.1 x y _ _,le_min ?_ ?_⟩
  · unfold rA
    rw [marginalA_eq p hp x y]
    exact Finset.single_le_sum (fun b _ => hp.1 x y (minorA p x) b)
      (Finset.mem_univ (minorB p y))
  · unfold rB
    rw [marginalB_eq p hp x y]
    exact Finset.single_le_sum (fun a _ => hp.1 x y a (minorB p y))
      (Finset.mem_univ (minorA p x))
private def edgeRatio (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x y : (Fin 13)) : ℝ :=
  if edgeCap p x y = 0 then 0 else edgeMass p x y / edgeCap p x y
private lemma edgeRatio_bounds (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    0 ≤ edgeRatio p x y ∧ edgeRatio p x y ≤ 1 := by
  unfold edgeRatio
  split_ifs with h
  · norm_num
  · have hpos : 0 < edgeCap p x y := lt_of_le_of_ne
      (le_min (rA_bounds p hp x).1 (rB_bounds p hp y).1) (Ne.symm h)
    exact ⟨div_nonneg (edgeMass_bounds p hp x y).1 hpos.le,
      (div_le_one hpos).mpr (edgeMass_bounds p hp x y).2⟩
private lemma edgeRatio_identity (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    edgeCap p x y * edgeRatio p x y = edgeMass p x y := by
  unfold edgeRatio
  split_ifs with h
  · have he := edgeMass_bounds p hp x y
    rw [h] at he
    have hz : edgeMass p x y = 0 := le_antisymm he.2 he.1
    simp [hz]
  · field_simp

private def activity (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) : (Sum (Fin 13) (Fin 13)) → ℝ
  | Sum.inl x => 2 * rA p x
  | Sum.inr y => 2 * rB p y
private lemma activity_bounds (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (i : (Sum (Fin 13) (Fin 13))) :
    0 ≤ activity p i ∧ activity p i ≤ 1 := by
  cases i with
  | inl x => dsimp [activity]; constructor <;> linarith [(rA_bounds p hp x).1, (rA_bounds p hp x).2]
  | inr y => dsimp [activity]; constructor <;> linarith [(rB_bounds p hp y).1, (rB_bounds p hp y).2]

private def outputBit (active : Bool) (minor : Bool) (raw : Bool) : Bool :=
  if active then raw.xor minor else !minor

private def entry (sa sb ma mb a b v : Bool) : ℝ :=
  D5.S3.TotalVariation.CycleSingleCutMinimax.push
    (fun z : Bool × Bool => (outputBit sa ma z.1, outputBit sb mb z.2))
    (fun z => if z.1.xor z.2 = v then 1 / 2 else 0) (a, b)
private lemma entry_norm (sa sb ma mb v : Bool) : (∑ a : Bool, ∑ b : Bool, entry sa sb ma mb a b v) = 1 := by
  fin_cases sa <;> fin_cases sb <;> fin_cases ma <;> fin_cases mb <;> fin_cases v <;>
    norm_num [entry, D5.S3.TotalVariation.CycleSingleCutMinimax.push, Fintype.sum_prod_type, Prod.mk.injEq, outputBit, Bool.xor, Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
private lemma entry_marginalA (sa sb ma mb v : Bool) : (∑ b : Bool, entry sa sb ma mb ma b v) =
    if sa then 1 / 2 else 0 := by
  fin_cases sa <;> fin_cases sb <;> fin_cases ma <;> fin_cases mb <;> fin_cases v <;>
    norm_num [entry, D5.S3.TotalVariation.CycleSingleCutMinimax.push, Fintype.sum_prod_type, Prod.mk.injEq, outputBit, Bool.xor, Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
private lemma entry_marginalB (sa sb ma mb v : Bool) : (∑ a : Bool, entry sa sb ma mb a mb v) =
    if sb then 1 / 2 else 0 := by
  fin_cases sa <;> fin_cases sb <;> fin_cases ma <;> fin_cases mb <;> fin_cases v <;>
    norm_num [entry, D5.S3.TotalVariation.CycleSingleCutMinimax.push, Fintype.sum_prod_type, Prod.mk.injEq, outputBit, Bool.xor, Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num
private lemma entry_minor_minor (sa sb ma mb v : Bool) : entry sa sb ma mb ma mb v =
    if sa && sb then (if v then 0 else 1 / 2) else 0 := by
  fin_cases sa <;> fin_cases sb <;> fin_cases ma <;> fin_cases mb <;> fin_cases v <;>
    norm_num [entry, D5.S3.TotalVariation.CycleSingleCutMinimax.push, Fintype.sum_prod_type, Prod.mk.injEq, outputBit, Bool.xor, Finset.filter_insert, Finset.filter_singleton] <;> simp <;> norm_num

private def generatedBox (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (s : (Sum (Fin 13) (Fin 13) → Bool)) (G : ((Fin 13 × Fin 13) → Bool)) : (Fin 13 → Fin 13 → Bool → Bool → ℝ) := fun x y a b =>
  entry (s (Sum.inl x)) (s (Sum.inr y)) (minorA p x) (minorB p y) a b (G (x,y))

private def matrixWeight (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (G : ((Fin 13 × Fin 13) → Bool)) : ℝ := bitLaw (fun e => edgeRatio p e.1 e.2) G
private lemma matrixWeight_sum (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) : (∑ G, matrixWeight p G) = 1 := bitLaw_sum _
private lemma matrixWeight_nonneg (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (G : ((Fin 13 × Fin 13) → Bool)) :
    0 ≤ matrixWeight p G := bitLaw_nonneg _ (fun e => edgeRatio_bounds p hp e.1 e.2) G

private def reconstructedBox (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) : (Fin 13 → Fin 13 → Bool → Bool → ℝ) := fun x y a b =>
  ∑ s : (Sum (Fin 13) (Fin 13) → Bool), layerWeight (activity p) s * ∑ G : ((Fin 13 × Fin 13) → Bool), matrixWeight p G * generatedBox p s G x y a b

private lemma sum_mixture {A I : Type} [Fintype A] [Fintype I]
    (w : I → ℝ) (f : I → A → ℝ) :
    (∑ a, ∑ i, w i * f i a) = ∑ i, w i * ∑ a, f i a := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

private lemma reconstructed_norm (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (x y : (Fin 13)) :
    (∑ a : Bool, ∑ b : Bool, reconstructedBox p x y a b) = 1 := by
  unfold reconstructedBox generatedBox
  simp_rw [sum_mixture]
  simp_rw [entry_norm]
  simp [matrixWeight_sum, layerWeight_sum]
private lemma reconstructed_marginalA (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    (∑ b : Bool, reconstructedBox p x y (minorA p x) b) = rA p x := by
  unfold reconstructedBox generatedBox
  simp_rw [sum_mixture, entry_marginalA]
  simp_rw [← Finset.sum_mul, matrixWeight_sum, one_mul]
  have h := layer_single (activity p) (fun i => (activity_bounds p hp i).1)
    (fun i => (activity_bounds p hp i).2) (Sum.inl x)
  have heq (s : (Sum (Fin 13) (Fin 13) → Bool)) :
      (if s (Sum.inl x) then (1 : ℝ)/2 else 0) = (if s (Sum.inl x) then 1 else 0)/2 := by
    cases s (Sum.inl x) <;> simp
  simp_rw [heq, ← mul_div_assoc, ← Finset.sum_div]
  rw [h]
  simp [activity]
private lemma reconstructed_marginalB (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    (∑ a : Bool, reconstructedBox p x y a (minorB p y)) = rB p y := by
  unfold reconstructedBox generatedBox
  simp_rw [sum_mixture, entry_marginalB]
  simp_rw [← Finset.sum_mul, matrixWeight_sum, one_mul]
  have h := layer_single (activity p) (fun i => (activity_bounds p hp i).1)
    (fun i => (activity_bounds p hp i).2) (Sum.inr y)
  have heq (s : (Sum (Fin 13) (Fin 13) → Bool)) :
      (if s (Sum.inr y) then (1 : ℝ)/2 else 0) = (if s (Sum.inr y) then 1 else 0)/2 := by
    cases s (Sum.inr y) <;> simp
  simp_rw [heq, ← mul_div_assoc, ← Finset.sum_div]
  rw [h]
  simp [activity]
private lemma reconstructed_minor_minor (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) (x y : (Fin 13)) :
    reconstructedBox p x y (minorA p x) (minorB p y) = edgeMass p x y := by
  unfold reconstructedBox generatedBox
  simp_rw [entry_minor_minor]
  have hG (s : (Sum (Fin 13) (Fin 13) → Bool)) :
      (∑ G : ((Fin 13 × Fin 13) → Bool), matrixWeight p G *
        (if s (Sum.inl x) && s (Sum.inr y) then (if G (x,y) then 0 else 1/2) else 0)) =
        (if s (Sum.inl x) && s (Sum.inr y) then edgeRatio p x y / 2 else 0) := by
    by_cases hs : (s (Sum.inl x) && s (Sum.inr y)) = true
    · simp only [hs, ite_true, matrixWeight]
      rw [bitLaw_moment (fun e => edgeRatio p e.1 e.2) (x,y) (fun b => if b then 0 else 1/2)]
      simp [div_eq_mul_inv]
    · simp [hs]
  simp_rw [hG]
  have h := layer_pair (activity p) (fun i => (activity_bounds p hp i).1)
    (fun i => (activity_bounds p hp i).2) (Sum.inl x) (Sum.inr y)
  have heq (s : (Sum (Fin 13) (Fin 13) → Bool)) :
      (if s (Sum.inl x) && s (Sum.inr y) then edgeRatio p x y / 2 else 0) =
        (if s (Sum.inl x) && s (Sum.inr y) then 1 else 0) * (edgeRatio p x y / 2) := by
    cases hs : (s (Sum.inl x) && s (Sum.inr y)) <;> simp
  simp_rw [heq, ← mul_assoc, ← Finset.sum_mul]
  rw [h]
  simp only [activity]
  have hid := edgeRatio_identity p hp x y
  unfold edgeCap at hid
  by_cases hle : rA p x ≤ rB p y
  · rw [min_eq_left hle] at hid
    rw [min_eq_left (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2))]
    linarith
  · have hge := le_of_not_ge hle
    rw [min_eq_right hge] at hid
    rw [min_eq_right (mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2))]
    linarith

private lemma binary_eq (f g : Bool → Bool → ℝ) (ma mb : Bool)
    (hn : (∑ a : Bool, ∑ b : Bool, f a b) = (∑ a : Bool, ∑ b : Bool, g a b))
    (ha : (∑ b : Bool, f ma b) = (∑ b : Bool, g ma b))
    (hb : (∑ a : Bool, f a mb) = (∑ a : Bool, g a mb))
    (hmm : f ma mb = g ma mb) : f = g := by
  funext a b
  fin_cases ma <;> fin_cases mb <;> fin_cases a <;> fin_cases b <;>
    simp_all <;> linarith

private lemma reconstructed_eq (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) : reconstructedBox p = p := by
  funext x y
  apply binary_eq _ _ (minorA p x) (minorB p y)
  · rw [reconstructed_norm, hp.2.1]
  · rw [reconstructed_marginalA p hp, ← marginalA_eq p hp x y]
    rfl
  · rw [reconstructed_marginalB p hp, ← marginalB_eq p hp x y]
    rfl
  · exact reconstructed_minor_minor p hp x y

private lemma lossy_push {m : ℕ} (η : ℝ) (p : Fin m → Fin m → Bool → Bool → ℝ)
    (f g : Fin m → Bool → Bool) :
    lossy η (push p f g) = push (lossy η p) (fun x => Option.map (f x)) (fun y => Option.map (g y)) := by
  funext x y a b
  generalize hf0 : f x false = f0
  generalize hf1 : f x true = f1
  generalize hg0 : g y false = g0
  generalize hg1 : g y true = g1
  fin_cases f0 <;> fin_cases f1 <;> fin_cases g0 <;> fin_cases g1 <;>
    fin_cases a <;> fin_cases b <;>
      simp [lossy, push, D5.S3.TotalVariation.CycleSingleCutMinimax.push,
        Fintype.sum_prod_type, Prod.mk.injEq, Fintype.sum_option, hf0, hf1, hg0, hg1] <;> ring <;> simp
private lemma lossy_mix {m : ℕ} {I : Type} [Fintype I] (η : ℝ) (w : I → ℝ)
    (p : I → Fin m → Fin m → Bool → Bool → ℝ) (hs : (∑ i, w i) = 1) :
    lossy η (fun x y a b => ∑ i, w i*p i x y a b) =
      fun x y a b => ∑ i, w i*lossy η (p i) x y a b := by
  funext x y a b
  cases a with
  | none =>
    cases b with
    | none => simp [lossy, ← Finset.sum_mul, hs]
    | some b =>
      simp only [lossy]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro c hc
      ring
  | some a =>
    cases b with
    | none =>
      simp only [lossy]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro c hc
      ring
    | some b =>
      simp only [lossy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private lemma generatedBox_push (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (s : (Sum (Fin 13) (Fin 13) → Bool)) (G : ((Fin 13 × Fin 13) → Bool)) :
    generatedBox p s G = push (parityBox (fun x y => G (x,y)))
      (fun x => outputBit (s (Sum.inl x)) (minorA p x))
      (fun y => outputBit (s (Sum.inr y)) (minorB p y)) := by
  funext x y a b
  rfl

private lemma generatedBox_local (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (s : (Sum (Fin 13) (Fin 13) → Bool)) (G : ((Fin 13 × Fin 13) → Bool)) :
    IsLocal (lossy (6/25) (generatedBox p s G)) := by
  rw [generatedBox_push, lossy_push (6/25) _ _ _]
  apply IsLocal_push
  exact parityBox_local (fun x y => G (x,y))

private lemma universal_local (p : (Fin 13 → Fin 13 → Bool → Bool → ℝ)) (hp : IsNSBox p) : IsLocal (lossy (6/25) p) := by
  rw [← reconstructed_eq p hp]
  unfold reconstructedBox
  rw [lossy_mix (6/25) _ _ (layerWeight_sum _)]
  apply IsLocal_mix
  · exact layerWeight_nonneg _
  · exact layerWeight_sum _
  · intro s
    rw [lossy_mix (6/25) _ _ (matrixWeight_sum p)]
    apply IsLocal_mix
    · exact matrixWeight_nonneg p hp
    · exact matrixWeight_sum p
    · intro G
      exact generatedBox_local p s G

private lemma admissible_bddAbove (m : ℕ) : BddAbove {η : ℝ | 0 ≤ η ∧ η ≤ 1 ∧
    ∀ p : Fin m → Fin m → Bool → Bool → ℝ, IsNSBox p → IsLocal (lossy η p)} := by
  refine ⟨1,?_⟩
  intro η hη
  exact hη.2.1

private lemma lower_bound : (6 : ℝ)/25 ≤ etaStar 13 := by
  apply le_csSup (admissible_bddAbove 13)
  refine ⟨by norm_num, by norm_num,?_⟩
  intro p hp
  exact universal_local p hp

theorem result : ¬ claim := by
  intro hc
  have heq := hc 13 (by norm_num)
  have hb := lower_bound
  rw [heq] at hb
  norm_num at hb

end
end D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
