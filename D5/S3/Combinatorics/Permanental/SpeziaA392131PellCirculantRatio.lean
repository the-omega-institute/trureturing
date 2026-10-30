/- GID: D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Pell circulant permanent divided by its signed determinant tends to one. -/

/- Mathematical classification:
   result: proof_shape: content
   escape_witness: cycle_activity_le, the weighted modular-cycle/composition estimate.
   admission_basis: open-problem-resolution (#21886; Proved)
   Direct frozen dependencies (declaration identities):
     D5.S1.Recurrence.PellCompanionGcd.P: sha256:9f54ab32a63dc156a14cd142dd1b3f0ae907265eae6f0c41fff9d561578aa069
     D5.S1.Recurrence.PellCompanionGcd.Q: sha256:68801f34b9be712ffac61e700e7a79347df9882bb467aced8bf778269ed4a87e
     D5.S1.Recurrence.PellCompanionGcd.pell_companion_step: sha256:cb470f2c3566a3c7813f32c2069cd458f5e459f1a34348e85dc4887bb4f18a37
     D5.S1.Recurrence.PellCompanionGcd.companion_odd: sha256:9c745166099e4e5785642f4352e5a0c043fa85fd1cb0ccdbb6ec3fadccff808b
     D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration.fixedLengthCompositionEquiv: sha256:e13797c5886c7347202e440ed4bf55aca9fb52270d6f4d58787eea469c0d7806
   Per-declaration proof_shape, consumers and frozen dependencies (same-delivery helpers expanded):
     C: definition; consumers: A392131, A392132, normalized, normalized_nonneg, normalized_ratio; frozen: P.
     A392131: definition; consumers: claim, normalized_ratio, result; frozen: P.
     A392132: definition; consumers: claim, normalized_ratio, result; frozen: P.
     claim: definition; consumers: result; frozen: P.
     pell_strict: bind-only; consumers: pell_pos; frozen: P, Q, companion_odd, pell_companion_step.
     pell_pos: bind-only; consumers: pell_entry_majorant, normalized_diagonal, normalized_ratio; frozen: P, Q, companion_odd, pell_companion_step.
     pell_ratio_bounds: content; consumers: pell_lower_step; frozen: P.
     pell_lower_step: content; consumers: pell_growth; frozen: P.
     pell_growth: content; consumers: pell_entry_majorant; frozen: P.
     pell_entry_majorant: content; consumers: normalized_entry; frozen: P, Q, companion_odd, pell_companion_step.
     cycleWeight: definition; consumers: cycleWeight_nonneg, cycleWeight_eq_term, cycleWeight_disjoint, cycleWeight_factors, permanent_le_cycle_product, permanent_le_exp_activity, cycleWeight_eq_orbit_product, cycleWeight_le_total, activity, cycle_activity_index_le, cycle_activity_le, activity_nonneg; frozen: none.
     cycleWeight_nonneg: bind-only; consumers: permanent_le_cycle_product, permanent_le_exp_activity, activity_nonneg; frozen: none.
     cycleWeight_eq_term: bind-only; consumers: permanent_le_cycle_product; frozen: none.
     cycleWeight_disjoint: bind-only; consumers: cycleWeight_factors; frozen: none.
     cycleWeight_factors: bind-only; consumers: permanent_le_cycle_product; frozen: none.
     permanent_le_cycle_product: bind-only; consumers: permanent_le_exp_activity; frozen: none.
     permanent_le_exp_activity: bind-only; consumers: normalized_permanent_tendsto; frozen: none.
     one_le_permanent: bind-only; consumers: normalized_permanent_tendsto; frozen: none.
     determinant_error_le_permanent_error: bind-only; consumers: normalized_determinant_tendsto; frozen: none.
     cycleBound: definition; consumers: cycleBound_tendsto, cycle_activity_le, normalized_activity_tendsto; frozen: none.
     cycleBound_tendsto: bind-only; consumers: normalized_activity_tendsto; frozen: none.
     cycleRoot: definition; consumers: cycleRoot_moved, stepCode, cycleCode, cycleCode_injective, stepCode_ne_zero, sum_stepCode, displacementTotal_dvd, cycleWeight_eq_orbit_product, composition_code_injective, cycleWeight_le_total, cycle_activity_index_le; frozen: none.
     cycleRoot_moved: bind-only; consumers: cycleCode_injective, stepCode_ne_zero, cycleWeight_eq_orbit_product; frozen: none.
     stepCode: definition; consumers: cycleCode, cycleCode_injective, stepCode_ne_zero, sum_stepCode, displacementTotal, displacementTotal_dvd, sum_stepCode_val_ge, displacementTotal_le, displacementComposition, displacementComposition_length, total_eq_index_mul, composition_code_injective, cycleWeight_le_total; frozen: none.
     cycleCode: definition; consumers: cycleCode_injective, composition_code_injective; frozen: none.
     cycleCode_injective: content; consumers: composition_code_injective; frozen: none.
     stepCode_ne_zero: bind-only; consumers: sum_stepCode_val_ge, displacementComposition, cycleWeight_le_total; frozen: none.
     sum_stepCode: bind-only; consumers: displacementTotal_dvd; frozen: none.
     displacementTotal: definition; consumers: displacementTotal_dvd, displacementTotal_le, displacementComposition, displacementComposition_length, cycleIndex, cycleIndex_lt, total_eq_index_mul, composition_code_injective, cycleWeight_le_total, cycle_activity_index_le; frozen: none.
     displacementTotal_dvd: bind-only; consumers: sum_stepCode_val_ge, total_eq_index_mul; frozen: none.
     sum_stepCode_val_ge: bind-only; consumers: total_eq_index_mul; frozen: none.
     cycleWeight_eq_orbit_product: bind-only; consumers: cycleWeight_le_total; frozen: none.
     fixed_length_composition_count: bind-only; consumers: weighted_composition_sum; frozen: fixedLengthCompositionEquiv.
     weighted_composition_sum: bind-only; consumers: cycle_activity_index_le; frozen: fixedLengthCompositionEquiv.
     displacementTotal_le: bind-only; consumers: cycleIndex_lt; frozen: none.
     displacementComposition: definition; consumers: displacementComposition_length, composition_code_injective, cycle_activity_index_le; frozen: none.
     displacementComposition_length: bind-only; consumers: cycle_activity_index_le; frozen: none.
     cycleIndex: definition; consumers: cycleIndex_lt, total_eq_index_mul, cycle_activity_index_le, cycle_activity_le; frozen: none.
     cycleIndex_lt: bind-only; consumers: cycle_activity_le; frozen: none.
     total_eq_index_mul: bind-only; consumers: cycle_activity_index_le; frozen: none.
     composition_code_injective: content; consumers: cycle_activity_index_le; frozen: none.
     cycleWeight_le_total: bind-only; consumers: cycle_activity_index_le; frozen: none.
     activity: definition; consumers: cycle_activity_le, activity_nonneg, normalized_activity_tendsto, normalized_permanent_tendsto; frozen: none.
     cycle_activity_index_le: content; consumers: cycle_activity_le; frozen: fixedLengthCompositionEquiv.
     cycle_activity_le: content; consumers: normalized_activity_tendsto; frozen: fixedLengthCompositionEquiv.
     normalized: definition; consumers: normalized_nonneg, normalized_diagonal, normalized_entry, normalized_ratio, normalized_activity_tendsto, normalized_permanent_tendsto, normalized_determinant_tendsto, result; frozen: P.
     normalized_nonneg: bind-only; consumers: normalized_activity_tendsto, normalized_permanent_tendsto, normalized_determinant_tendsto; frozen: P.
     normalized_diagonal: bind-only; consumers: normalized_permanent_tendsto, normalized_determinant_tendsto; frozen: P, Q, companion_odd, pell_companion_step.
     normalized_entry: content; consumers: normalized_activity_tendsto; frozen: P, Q, companion_odd, pell_companion_step.
     normalized_ratio: bind-only; consumers: result; frozen: P, Q, companion_odd, pell_companion_step.
     activity_nonneg: bind-only; consumers: normalized_activity_tendsto; frozen: none.
     normalized_activity_tendsto: content; consumers: normalized_permanent_tendsto; frozen: P, Q, companion_odd, pell_companion_step, fixedLengthCompositionEquiv.
     normalized_permanent_tendsto: content; consumers: normalized_determinant_tendsto, result; frozen: P, Q, companion_odd, pell_companion_step, fixedLengthCompositionEquiv.
     normalized_determinant_tendsto: content; consumers: result; frozen: P, Q, companion_odd, pell_companion_step, fixedLengthCompositionEquiv.
     result: content; consumers: none; frozen: P, Q, companion_odd, pell_companion_step, fixedLengthCompositionEquiv.
   C uses the source vector literally; proofs reuse the existing Pell sequence P.
   The source quotient has the signed determinant, with no absolute value.
   The public definitions are precisely C, A392131, A392132 and claim.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22411.
-/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
import D5.S1.Recurrence.PellCompanionGcd
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Cycle.Concrete

noncomputable section
attribute [local instance] Classical.propDecidable


namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

/-- The OEIS matrix: its first row is P(n-1), P(0), ..., P(n-2).
Mathlib's circulant uses row i, column j equal to v(i-j). -/
noncomputable def C (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.circulant (fun k : Fin n =>
    (D5.S1.Recurrence.PellCompanionGcd.P (n - 1 - k.val) : ℝ))

/-- OEIS A392131, including the empty determinant at n = 0. -/
noncomputable def A392131 (n : ℕ) : ℝ := Matrix.det (C n)

/-- OEIS A392132, including the empty permanent at n = 0. -/
noncomputable def A392132 (n : ℕ) : ℝ := Matrix.permanent (C n)

/-- The source limit assertion in explicit epsilon-N form. -/
def claim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧
    ∀ n : ℕ, N ≤ n → |A392132 n / A392131 n - 1| < ε

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open D5.S1.Recurrence.PellCompanionGcd

private theorem pell_strict : StrictMono P := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [(pell_companion_step n).1]
  exact Nat.lt_add_of_pos_right (companion_odd n).pos

private theorem pell_pos (n : ℕ) (hn : 0 < n) : 0 < P n := by
  simpa only [P] using pell_strict hn

private theorem pell_ratio_bounds (j : ℕ) (hj : 2 ≤ j) :
    12 * P j ≤ 5 * P (j + 1) ∧ 2 * P (j + 1) ≤ 5 * P j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
  induction k with
  | zero => norm_num [P]
  | succ k ih =>
    have ih' := ih (by omega)
    change 12 * P (2+k+1) ≤ 5 * (2*P (2+k+1)+P (2+k)) ∧
      2 * (2*P (2+k+1)+P (2+k)) ≤ 5 * P (2+k+1)
    constructor <;> omega

private theorem pell_lower_step (j : ℕ) (hj : 2 ≤ j) :
    (12 / 5 : ℝ) * (P j : ℝ) ≤ (P (j + 1) : ℝ) := by
  have h := (pell_ratio_bounds j hj).1
  have h' : (12 : ℝ) * (P j : ℝ) ≤ 5 * (P (j + 1) : ℝ) := by exact_mod_cast h
  linarith

private theorem pell_growth (m d : ℕ) (hm : 2 ≤ m) :
    (P m : ℝ) * (12 / 5 : ℝ) ^ d ≤ (P (m + d) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := pell_lower_step (m+d) (by omega)
    calc
      (P m : ℝ) * (12 / 5 : ℝ) ^ (d+1) =
          (12/5:ℝ) * ((P m : ℝ) * (12/5:ℝ)^d) := by ring
      _ ≤ (12/5:ℝ) * (P (m+d):ℝ) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ (P (m+(d+1)):ℝ) := by simpa only [Nat.add_assoc] using hs

private theorem pell_entry_majorant (m N : ℕ) (hN : 2 ≤ N) (hm : m < N) :
    (P m : ℝ) / (P N : ℝ) ≤ (6/5:ℝ) / (12/5:ℝ) ^ (N-m) := by
  have hpN : (0:ℝ) < P N := by exact_mod_cast pell_pos N (by omega)
  have hpq : (0:ℝ) < (12/5:ℝ)^(N-m) := pow_pos (by norm_num) _
  apply (div_le_div_iff₀ hpN hpq).mpr
  by_cases hm0 : m = 0
  · simp [hm0, P]
  by_cases hm1 : m = 1
  · subst m
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hN
    have h := pell_growth 2 d (by omega)
    norm_num [P] at h ⊢
    rw [show 1+d=d+1 by omega, pow_succ]
    nlinarith
  · have h := pell_growth m (N-m) (by omega)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hm)] at h
    have hn : (0:ℝ) ≤ P N := Nat.cast_nonneg _
    nlinarith

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

open scoped BigOperators
open Equiv Finset
namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
variable {α : Type*} [Fintype α] [DecidableEq α]

private def cycleWeight (A : Matrix α α ℝ) (σ : Perm α) : ℝ :=
  ∏ i ∈ σ.support, A (σ i) i

private theorem cycleWeight_nonneg (A : Matrix α α ℝ) (ha : ∀ i j, 0 ≤ A i j)
    (σ : Perm α) : 0 ≤ cycleWeight A σ := by
  exact Finset.prod_nonneg (fun i _ => ha (σ i) i)

private theorem cycleWeight_eq_term (A : Matrix α α ℝ) (hd : ∀ i, A i i = 1)
    (σ : Perm α) : cycleWeight A σ = ∏ i, A (σ i) i := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Perm.notMem_support.mp hi, hd]

private theorem cycleWeight_disjoint (A : Matrix α α ℝ) (σ τ : Perm α)
    (h : σ.Disjoint τ) : cycleWeight A (σ*τ) = cycleWeight A σ * cycleWeight A τ := by
  unfold cycleWeight
  rw [h.support_mul, Finset.prod_union h.disjoint_support]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Perm.mul_apply, Perm.notMem_support.mp (h.mem_imp hi)]
  · apply Finset.prod_congr rfl
    intro i hi
    have hs : σ (τ i) = τ i := Perm.notMem_support.mp
      (h.symm.mem_imp ((Perm.apply_mem_support).mpr hi))
    rw [Perm.mul_apply, hs]

private theorem cycleWeight_factors (A : Matrix α α ℝ) (σ : Perm α) :
    cycleWeight A σ = ∏ c ∈ σ.cycleFactorsFinset, cycleWeight A c := by
  induction σ using Perm.cycle_induction_on with
  | base_one => simp [cycleWeight]
  | base_cycles σ hs => rw [hs.cycleFactorsFinset_eq_singleton]; simp
  | induction_disjoint σ τ hd hs ihσ ihτ =>
    rw [cycleWeight_disjoint A σ τ hd, hd.cycleFactorsFinset_mul_eq_union,
      Finset.prod_union hd.disjoint_cycleFactorsFinset, ihσ, ihτ]

private theorem permanent_le_cycle_product (A : Matrix α α ℝ)
    (ha : ∀ i j, 0 ≤ A i j) (hd : ∀ i, A i i = 1) :
    A.permanent ≤ ∏ c ∈ (Finset.univ.filter fun c : Perm α => c.IsCycle),
      (1 + cycleWeight A c) := by
  classical
  let cs : Finset (Perm α) := Finset.univ.filter fun c => c.IsCycle
  let image : Finset (Finset (Perm α)) := Finset.univ.image Perm.cycleFactorsFinset
  have hsub : image ⊆ cs.powerset := by
    intro s hs
    obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hs
    apply Finset.mem_powerset.mpr
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Perm.mem_cycleFactorsFinset_iff.mp hc).1⟩
  calc
    A.permanent = ∑ σ : Perm α, cycleWeight A σ := by
      simp_rw [cycleWeight_eq_term A hd]; rfl
    _ = ∑ σ : Perm α, ∏ c ∈ σ.cycleFactorsFinset, cycleWeight A c := by
      exact Finset.sum_congr rfl (fun σ _ => cycleWeight_factors A σ)
    _ = ∑ s ∈ image, ∏ c ∈ s, cycleWeight A c := by
      exact (Finset.sum_image (f := fun s : Finset (Perm α) => ∏ c ∈ s, cycleWeight A c)
        (fun _ _ _ _ h => Perm.cycleFactorsFinset_injective h)).symm
    _ ≤ ∑ s ∈ cs.powerset, ∏ c ∈ s, cycleWeight A c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro s _ _
      exact Finset.prod_nonneg (fun c _ => cycleWeight_nonneg A ha c)
    _ = ∏ c ∈ cs, (1+cycleWeight A c) := (Finset.prod_one_add cs).symm

private theorem permanent_le_exp_activity (A : Matrix α α ℝ)
    (ha : ∀ i j, 0 ≤ A i j) (hd : ∀ i, A i i = 1) :
    A.permanent ≤ Real.exp (∑ c ∈ Finset.univ.filter (fun c : Perm α => c.IsCycle),
      cycleWeight A c) := by
  apply (permanent_le_cycle_product A ha hd).trans
  exact Real.prod_one_add_le_exp_sum _ (fun c => cycleWeight_nonneg A ha c)

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

open scoped BigOperators
open Equiv Finset Filter
namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem one_le_permanent (A : Matrix α α ℝ)
    (ha : ∀ i j, 0 ≤ A i j) (hd : ∀ i, A i i = 1) :
    1 ≤ A.permanent := by
  classical
  have ht : (∏ i, A ((1 : Perm α) i) i) = 1 := by simp [hd]
  rw [Matrix.permanent, ← ht]
  exact Finset.single_le_sum (fun σ _ => Finset.prod_nonneg (fun i _ => ha (σ i) i))
    (Finset.mem_univ (1 : Perm α))

private theorem determinant_error_le_permanent_error (A : Matrix α α ℝ)
    (ha : ∀ i j, 0 ≤ A i j) (hd : ∀ i, A i i = 1) :
    |A.det - 1| ≤ A.permanent - 1 := by
  classical
  let t : Perm α → ℝ := fun σ => ∏ i, A (σ i) i
  have hi : t 1 = 1 := by simp [t, hd]
  have hper : A.permanent - 1 = ∑ σ ∈ Finset.univ.erase 1, t σ := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Perm α)) t (Finset.mem_univ 1)
    rw [hi] at h
    change (∑ σ ∈ Finset.univ.erase 1, t σ) + 1 = A.permanent at h
    linarith
  have hdet : A.det - 1 = ∑ σ ∈ Finset.univ.erase 1, (Perm.sign σ : ℝ) * t σ := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Perm α))
      (fun σ => (Perm.sign σ : ℝ) * t σ) (Finset.mem_univ 1)
    simp only [map_one, Units.val_one, Int.cast_one, one_mul, hi] at h
    rw [Matrix.det_apply']
    change (∑ σ : Perm α, (Perm.sign σ : ℝ) * t σ) - 1 = _
    linarith
  rw [hper,hdet]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => ha (σ i) i))]
  have hs : |(Perm.sign σ : ℝ)| = 1 := by
    exact_mod_cast Perm.sign_abs σ
  rw [hs,one_mul]

private def cycleBound (n : ℕ) : ℝ :=
  (6*(n:ℝ)/11) * (11/12:ℝ)^n / (1-(11/12:ℝ)^n)

private theorem cycleBound_tendsto : Tendsto cycleBound atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (11/12:ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnpow := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ) ≤ 11/12)
    (by norm_num : (11/12:ℝ) < 1)
  have h := ((hnpow.const_mul (6/11:ℝ)).div (tendsto_const_nhds.sub hpow)
    (by norm_num : (1:ℝ)-0 ≠ 0))
  have hf : cycleBound = (fun n : ℕ => (6/11:ℝ)*((n:ℝ)*(11/12:ℝ)^n)/(1-(11/12:ℝ)^n)) := by
    funext n
    unfold cycleBound
    ring
  rw [hf]
  have h' : Tendsto (fun n : ℕ => (6/11:ℝ)*((n:ℝ)*(11/12:ℝ)^n)/(1-(11/12:ℝ)^n))
      atTop (nhds ((6/11:ℝ)*0/(1-0))) := by
    convert h using 1
  norm_num at h'
  exact h'

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

open scoped BigOperators
open Equiv Finset
namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
variable {n : ℕ} [NeZero n]

private def cycleRoot (σ : Perm (Fin n)) : Fin n :=
  if h : σ.IsCycle then Classical.choose h else 0

private theorem cycleRoot_moved (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    σ (cycleRoot σ) ≠ cycleRoot σ := by
  simp only [cycleRoot, dif_pos hσ]
  exact (Classical.choose_spec hσ).1

private def stepCode (σ : Perm (Fin n)) (k : ℕ) (j : Fin k) : Fin n :=
  σ ((σ^j.val) (cycleRoot σ)) - (σ^j.val) (cycleRoot σ)

private def cycleCode (σ : Perm (Fin n)) (k : ℕ) : Fin n × (Fin k → Fin n) :=
  (cycleRoot σ, stepCode σ k)

private theorem cycleCode_injective (k : ℕ) (σ τ : Perm (Fin n))
    (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hσk : σ.support.card = k) (hτk : τ.support.card = k)
    (hc : cycleCode σ k = cycleCode τ k) : σ = τ := by
  have hr : cycleRoot σ = cycleRoot τ := congrArg Prod.fst hc
  have hd : stepCode σ k = stepCode τ k := congrArg Prod.snd hc
  have hp : ∀ t : ℕ, t ≤ k → (σ^t) (cycleRoot σ) = (τ^t) (cycleRoot τ) := by
    intro t
    induction t with
    | zero => simpa using hr
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have he := congrFun hd (⟨t,by omega⟩ : Fin k)
      simp only [stepCode, hi] at he
      have he' := sub_left_inj.mp he
      simpa only [pow_succ', Perm.mul_apply, hi] using he'
  have hlσ : (σ.toList (cycleRoot σ)).length = k := by
    rw [Perm.length_toList, hσ.cycleOf_eq (cycleRoot_moved σ hσ), hσk]
  have hlτ : (τ.toList (cycleRoot τ)).length = k := by
    rw [Perm.length_toList, hτ.cycleOf_eq (cycleRoot_moved τ hτ), hτk]
  have hl : σ.toList (cycleRoot σ) = τ.toList (cycleRoot τ) := by
    apply List.ext_getElem (hlσ.trans hlτ.symm)
    intro i hi hj
    rw [Perm.getElem_toList, Perm.getElem_toList]
    exact hp i (by omega)
  calc
    σ = List.formPerm (σ.toList (cycleRoot σ)) := by
      rw [Perm.formPerm_toList, hσ.cycleOf_eq (cycleRoot_moved σ hσ)]
    _ = List.formPerm (τ.toList (cycleRoot τ)) := congrArg List.formPerm hl
    _ = τ := by rw [Perm.formPerm_toList, hτ.cycleOf_eq (cycleRoot_moved τ hτ)]

private theorem stepCode_ne_zero (σ : Perm (Fin n)) (hσ : σ.IsCycle)
    (k : ℕ) (j : Fin k) : stepCode σ k j ≠ 0 := by
  rw [stepCode, sub_ne_zero]
  have h := cycleRoot_moved σ hσ
  exact fun he => h ((σ^j.val).injective (by
    simpa only [← Perm.mul_apply, ← pow_succ, pow_succ'] using he))

private theorem sum_stepCode (σ : Perm (Fin n)) (k : ℕ) :
    ∑ j : Fin k, stepCode σ k j = (σ^k) (cycleRoot σ) - cycleRoot σ := by
  have h := Finset.sum_range_sub (fun t : ℕ => (σ^t) (cycleRoot σ)) k
  rw [Finset.sum_range] at h
  simpa only [stepCode, pow_succ', Perm.mul_apply, pow_zero, Perm.one_apply] using h

private def displacementTotal (σ : Perm (Fin n)) : ℕ :=
  ∑ j : Fin σ.support.card, (stepCode σ σ.support.card j).val

open scoped Fin.NatCast in
private theorem displacementTotal_dvd (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    n ∣ displacementTotal σ := by
  have hs : (∑ j : Fin σ.support.card, stepCode σ σ.support.card j) = 0 := by
    rw [sum_stepCode, ←hσ.orderOf, pow_orderOf_eq_one]
    simp
  apply Fin.natCast_eq_zero.mp
  change (↑(∑ j : Fin σ.support.card, (stepCode σ σ.support.card j).val) : Fin n) = 0
  change (Nat.castAddMonoidHom (Fin n)) (∑ j : Fin σ.support.card, (stepCode σ σ.support.card j).val) = 0
  rw [map_sum]
  simpa only [Nat.coe_castAddMonoidHom, Fin.cast_val_eq_self] using hs

open scoped Fin.NatCast in
private theorem sum_stepCode_val_ge (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    n ≤ ∑ j : Fin σ.support.card, (stepCode σ σ.support.card j).val := by
  have hn : 0 < σ.support.card := lt_of_lt_of_le (by decide : 0 < 2) hσ.two_le_card_support
  have hp : 0 < ∑ j : Fin σ.support.card, (stepCode σ σ.support.card j).val := by
    apply Finset.sum_pos
    · intro j hj
      exact Nat.pos_of_ne_zero (by
        intro hz
        apply stepCode_ne_zero σ hσ _ j
        exact Fin.ext (by simpa using hz))
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  exact Nat.le_of_dvd hp (displacementTotal_dvd σ hσ)

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open Equiv Finset
open scoped BigOperators
variable {n : ℕ} [NeZero n]

private theorem cycleWeight_eq_orbit_product (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : Perm (Fin n)) (hσ : σ.IsCycle) (k : ℕ) (hk : σ.support.card = k) :
    cycleWeight A σ = ∏ j : Fin k,
      A (σ ((σ^j.val) (cycleRoot σ))) ((σ^j.val) (cycleRoot σ)) := by
  classical
  have hr := cycleRoot_moved σ hσ
  have hl : (σ.toList (cycleRoot σ)).length = k := by
    rw [Perm.length_toList,hσ.cycleOf_eq hr,hk]
  have hlist : List.ofFn (fun j : Fin k => (σ^j.val) (cycleRoot σ)) =
      σ.toList (cycleRoot σ) := by
    apply List.ext_getElem (by simp [hl])
    intro i hi hj
    simp only [List.getElem_ofFn, Perm.getElem_toList]
  have hset : (σ.toList (cycleRoot σ)).toFinset = σ.support := by
    ext x
    rw [List.mem_toFinset,Perm.mem_toList_iff,← Perm.mem_support_cycleOf_iff,
      hσ.cycleOf_eq hr]
  unfold cycleWeight
  rw [←hset, List.prod_toFinset _ (Perm.nodup_toList _ _), ←hlist,
    List.map_ofFn, List.prod_ofFn]
  rfl

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open Equiv Finset
open scoped BigOperators
open D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

private theorem fixed_length_composition_count (m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter (fun d : Composition m => d.length = k+1)).card =
      (m-1).choose k := by
  classical
  have h := Fintype.card_congr (fixedLengthCompositionEquiv m (k+1) hm (by omega))
  rw [Fintype.card_finset_len,Fintype.card_fin] at h
  simpa only [Fintype.card_subtype, Nat.add_sub_cancel] using h

private theorem weighted_composition_sum (m : ℕ) (hm : 0 < m) (c : ℝ) :
    ∑ d : Composition m, c^d.length = c*(1+c)^(m-1) := by
  classical
  have hmap (d : Composition m) (hd : d ∈ (Finset.univ : Finset (Composition m))) :
      d.length-1 ∈ Finset.range m := by
    have h1 := d.length_le
    have h2 := d.length_pos_of_pos hm
    exact Finset.mem_range.mpr (by omega)
  have hterm (k : ℕ) :
      (∑ d ∈ (Finset.univ.filter fun d : Composition m => d.length-1=k), c^d.length) =
        ((m-1).choose k : ℝ)*c^(k+1) := by
    have hf : (Finset.univ.filter fun d : Composition m => d.length-1=k) =
        (Finset.univ.filter fun d : Composition m => d.length=k+1) := by
      ext d
      have h := d.length_pos_of_pos hm
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    rw [hf]
    calc
      (∑ d ∈ Finset.univ.filter (fun d : Composition m => d.length=k+1), c^d.length) =
          ∑ d ∈ Finset.univ.filter (fun d : Composition m => d.length=k+1), c^(k+1) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [(Finset.mem_filter.mp hd).2]
      _ = ((m-1).choose k : ℝ)*c^(k+1) := by
        rw [Finset.sum_const, nsmul_eq_mul, fixed_length_composition_count m k hm]
  calc
    (∑ d : Composition m, c^d.length) =
        ∑ k ∈ Finset.range m, ∑ d ∈ (Finset.univ.filter fun d : Composition m => d.length-1=k),
          c^d.length := (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ k ∈ Finset.range m, ((m-1).choose k:ℝ)*c^(k+1) :=
      Finset.sum_congr rfl (fun k _ => hterm k)
    _ = c*(∑ k ∈ Finset.range m, ((m-1).choose k:ℝ)*c^k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ]
      ring
    _ = c*(1+c)^(m-1) := by
      congr 1
      rw [add_comm (1:ℝ) c, add_pow]
      have he : m-1+1=m := by exact Nat.sub_add_cancel hm
      simp only [he,one_pow,mul_one]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open Equiv Finset
open scoped BigOperators
variable {n : ℕ} [NeZero n]

private theorem displacementTotal_le (σ : Perm (Fin n)) : displacementTotal σ ≤ n*(n-1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  calc
    displacementTotal σ ≤ ∑ j : Fin σ.support.card, (n-1) := by
      exact Finset.sum_le_sum fun j _ => Nat.le_sub_one_of_lt (stepCode σ _ j).isLt
    _ = σ.support.card*(n-1) := by simp
    _ ≤ n*(n-1) := Nat.mul_le_mul_right _ (by simpa using Finset.card_le_univ σ.support)

private def displacementComposition (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    Composition (displacementTotal σ) where
  blocks := List.ofFn (fun j : Fin σ.support.card => (stepCode σ σ.support.card j).val)
  blocks_pos := by
    intro d hd
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hd
    exact Nat.pos_of_ne_zero (by
      intro hz
      apply stepCode_ne_zero σ hσ _ j
      exact Fin.ext (by simpa using hz))
  blocks_sum := List.sum_ofFn

private theorem displacementComposition_length (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    (displacementComposition σ hσ).length = σ.support.card := List.length_ofFn

private def cycleIndex (σ : Perm (Fin n)) : ℕ := displacementTotal σ / n - 1

private theorem cycleIndex_lt (σ : Perm (Fin n)) : cycleIndex σ < n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h := Nat.div_le_div_right (displacementTotal_le σ) (c := n)
  rw [Nat.mul_div_cancel_left _ hn] at h
  unfold cycleIndex
  omega

private theorem total_eq_index_mul (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    displacementTotal σ = (cycleIndex σ+1)*n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hg := sum_stepCode_val_ge σ hσ
  have hp : 0 < displacementTotal σ / n := Nat.div_pos hg hn
  have hd := Nat.div_mul_cancel (displacementTotal_dvd σ hσ)
  unfold cycleIndex
  rw [Nat.sub_add_cancel (by omega : 1 ≤ displacementTotal σ / n)]
  exact hd.symm

private theorem composition_code_injective (σ τ : Perm (Fin n)) (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (m : ℕ) (hσm : displacementTotal σ = m) (hτm : displacementTotal τ = m)
    (hr : cycleRoot σ = cycleRoot τ)
    (hc : (displacementComposition σ hσ).cast hσm =
      (displacementComposition τ hτ).cast hτm) : σ = τ := by
  have hb := congrArg Composition.blocks hc
  change List.ofFn (fun j : Fin σ.support.card => (stepCode σ σ.support.card j).val) =
    List.ofFn (fun j : Fin τ.support.card => (stepCode τ τ.support.card j).val) at hb
  have hk : σ.support.card = τ.support.card := by
    have h := congrArg List.length hb
    simpa only [List.length_ofFn] using h
  apply cycleCode_injective σ.support.card σ τ hσ hτ rfl hk.symm
  apply Prod.ext hr
  funext j
  apply Fin.ext
  have hh := congrArg (fun l : List ℕ => l[j.val]?) hb
  rw [List.getElem?_eq_getElem (by simpa using j.isLt),
      List.getElem?_eq_getElem (by simp only [List.length_ofFn]; omega)] at hh
  change (stepCode σ σ.support.card j).val = (stepCode τ σ.support.card j).val
  simpa only [List.getElem_ofFn,stepCode] using (Option.some.inj hh)


private theorem cycleWeight_le_total (A : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, 0 ≤ A i j)
    (he : ∀ i j, i ≠ j → A i j ≤ (6/5:ℝ)/(12/5:ℝ)^((i-j).val))
    (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    cycleWeight A σ ≤ (6/5:ℝ)^σ.support.card/(12/5:ℝ)^(displacementTotal σ) := by
  rw [cycleWeight_eq_orbit_product A σ hσ σ.support.card rfl]
  calc
    (∏ j : Fin σ.support.card, A (σ ((σ^j.val) (cycleRoot σ))) ((σ^j.val) (cycleRoot σ))) ≤
        ∏ j : Fin σ.support.card, (6/5:ℝ)/(12/5:ℝ)^(stepCode σ σ.support.card j).val := by
      apply Finset.prod_le_prod₀
      · intro j hj; exact ha _ _
      · intro j hj
        exact he _ _ (by
          have h := stepCode_ne_zero σ hσ σ.support.card j
          simpa only [stepCode,sub_ne_zero] using h)
    _ = (6/5:ℝ)^σ.support.card/(12/5:ℝ)^(displacementTotal σ) := by
      rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,displacementTotal]

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open Equiv Finset
open scoped BigOperators
variable {n : ℕ} [NeZero n]

private def activity {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Perm α => σ.IsCycle), cycleWeight A σ

private theorem cycle_activity_index_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, 0 ≤ A i j)
    (he : ∀ i j, i ≠ j → A i j ≤ (6/5:ℝ)/(12/5:ℝ)^((i-j).val))
    (h : ℕ) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin n) => σ.IsCycle ∧ cycleIndex σ = h),
      cycleWeight A σ ≤ (6*(n:ℝ)/11)*(11/12:ℝ)^((h+1)*n) := by
  classical
  let m := (h+1)*n
  have hm : 0 < m := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne n))
  let cs := Finset.univ.filter (fun σ : Perm (Fin n) => σ.IsCycle ∧ cycleIndex σ = h)
  have hh (σ : cs) : σ.val.IsCycle ∧ cycleIndex σ.val = h :=
    (Finset.mem_filter.mp σ.property).2
  have ht (σ : cs) : displacementTotal σ.val = m := by
    rw [total_eq_index_mul σ.val (hh σ).1,(hh σ).2]
  let enc : cs → Fin n × Composition m := fun σ =>
    (cycleRoot σ.val,(displacementComposition σ.val (hh σ).1).cast (ht σ))
  let f : Fin n × Composition m → ℝ := fun p =>
    (6/5:ℝ)^p.2.length/(12/5:ℝ)^m
  have hi : Set.InjOn enc (Finset.univ : Finset cs) := by
    intro σ _ τ _ hc
    apply Subtype.ext
    exact composition_code_injective σ.val τ.val (hh σ).1 (hh τ).1 m (ht σ) (ht τ)
      (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  have hb : (∑ σ ∈ cs, cycleWeight A σ) ≤ ∑ p : Fin n × Composition m, f p := by
    rw [← Finset.sum_attach cs (fun σ => cycleWeight A σ)]
    apply Finset.sum_le_sum_of_injOn enc hi (Finset.subset_univ _)
    · intro σ hσ
      have hf : f (enc σ) = (6/5:ℝ)^σ.val.support.card/(12/5:ℝ)^m := by
        change (6/5:ℝ)^(displacementComposition σ.val (hh σ).1).length/(12/5:ℝ)^m = _
        rw [displacementComposition_length]
      rw [hf,←ht σ]
      exact cycleWeight_le_total A ha he σ.val (hh σ).1
    · intro p hp hnot
      exact div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  calc
    (∑ σ ∈ cs, cycleWeight A σ) ≤ ∑ p : Fin n × Composition m, f p := hb
    _ = (n:ℝ) * ((6/5:ℝ)*(1+6/5:ℝ)^(m-1)/(12/5:ℝ)^m) := by
      simp only [f,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.sum_div,weighted_composition_sum m hm]
    _ = (6*(n:ℝ)/11)*(11/12:ℝ)^m := by
      have hq : (1+(6/5:ℝ)) = 11/5 := by norm_num
      rw [hq]
      have hm' : m-1+1=m := by exact Nat.sub_add_cancel hm
      have hqpow : (12/5:ℝ)^m = (12/5:ℝ)^(m-1)*(12/5:ℝ) := by
        rw [←pow_succ,hm']
      have hrpow : (11/12:ℝ)^m = (11/12:ℝ)^(m-1)*(11/12:ℝ) := by
        rw [←pow_succ,hm']
      have hpow : (11/5:ℝ)^(m-1) = (11/12:ℝ)^(m-1)*(12/5:ℝ)^(m-1) := by
        rw [←mul_pow]
        norm_num
      rw [hqpow,hrpow,hpow]
      field_simp
      <;> ring


private theorem cycle_activity_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, 0 ≤ A i j)
    (he : ∀ i j, i ≠ j → A i j ≤ (6/5:ℝ)/(12/5:ℝ)^((i-j).val)) :
    activity A ≤ cycleBound n := by
  classical
  let cs := Finset.univ.filter (fun σ : Perm (Fin n) => σ.IsCycle)
  have hc (σ : Perm (Fin n)) (hσ : σ ∈ cs) : cycleIndex σ ∈ Finset.range n :=
    Finset.mem_range.mpr (cycleIndex_lt σ)
  have hr0 : 0 ≤ (11/12:ℝ)^n := pow_nonneg (by norm_num) _
  have hr1 : (11/12:ℝ)^n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (NeZero.ne n)
  have hg : ∑ h ∈ Finset.range n, ((11/12:ℝ)^n)^h ≤ (1-(11/12:ℝ)^n)⁻¹ := by
    have hs := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (Finset.range n)
      (fun h _ => pow_nonneg hr0 h)
    simpa only [tsum_geometric_of_lt_one hr0 hr1] using hs
  calc
    activity A = ∑ h ∈ Finset.range n,
        ∑ σ ∈ cs.filter (fun σ => cycleIndex σ = h), cycleWeight A σ :=
      (Finset.sum_fiberwise_of_maps_to hc _).symm
    _ ≤ ∑ h ∈ Finset.range n, (6*(n:ℝ)/11)*(11/12:ℝ)^((h+1)*n) := by
      apply Finset.sum_le_sum
      intro h hh
      simpa only [cs,Finset.filter_filter,and_assoc] using cycle_activity_index_le A ha he h
    _ = (6*(n:ℝ)/11)*(11/12:ℝ)^n * ∑ h ∈ Finset.range n, ((11/12:ℝ)^n)^h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [pow_mul,pow_succ]
      ring
    _ ≤ (6*(n:ℝ)/11)*(11/12:ℝ)^n*(1-(11/12:ℝ)^n)⁻¹ :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = cycleBound n := by simp only [cycleBound,div_eq_mul_inv]

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio

namespace D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
open D5.S1.Recurrence.PellCompanionGcd
open Equiv Finset Filter
open scoped BigOperators

private def normalized (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((P (n-1) : ℝ)⁻¹) • C n

private theorem normalized_nonneg (n : ℕ) (i j : Fin n) : 0 ≤ normalized n i j := by
  unfold normalized C
  change 0 ≤ (P (n-1) : ℝ)⁻¹ * (P (n-1-(i-j).val) : ℝ)
  positivity

private theorem normalized_diagonal (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    normalized n i i = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  have hp : (P (n-1):ℝ) ≠ 0 := by exact_mod_cast (pell_pos (n-1) (by omega)).ne'
  simp [normalized,C,Matrix.circulant_apply,hp]

private theorem normalized_entry (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    normalized n i j ≤ (6/5:ℝ)/(12/5:ℝ)^((i-j).val) := by
  haveI : NeZero n := ⟨by omega⟩
  have hd : 0 < (i-j).val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply sub_ne_zero.mpr hij
    exact Fin.ext (by simpa using hz)
  have hdn := (i-j).isLt
  have hm : n-1-(i-j).val < n-1 := by omega
  have h := pell_entry_majorant (n-1-(i-j).val) (n-1) (by omega) hm
  have he : n-1-(n-1-(i-j).val) = (i-j).val := by omega
  rw [he] at h
  simpa only [normalized,C,Matrix.smul_apply,smul_eq_mul,Matrix.circulant_apply,
    div_eq_mul_inv,mul_comm] using h

private theorem normalized_ratio (n : ℕ) (hn : 2 ≤ n) :
    (normalized n).permanent / (normalized n).det = A392132 n / A392131 n := by
  have hp : (P (n-1):ℝ) ≠ 0 := by exact_mod_cast (pell_pos (n-1) (by omega)).ne'
  simp only [normalized,Matrix.permanent_smul,Matrix.det_smul,Fintype.card_fin,
    A392131,A392132]
  exact mul_div_mul_left _ _ (pow_ne_zero n (inv_ne_zero hp))

private theorem activity_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (ha : ∀ i j, 0 ≤ A i j) : 0 ≤ activity A := by
  exact Finset.sum_nonneg (fun σ _ => cycleWeight_nonneg A ha σ)

private theorem normalized_activity_tendsto :
    Tendsto (fun n => activity (normalized n)) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => activity_nonneg _ (normalized_nonneg n)) _ cycleBound_tendsto
  filter_upwards [eventually_ge_atTop 3] with n hn
  haveI : NeZero n := ⟨by omega⟩
  exact cycle_activity_le (normalized n) (normalized_nonneg n) (normalized_entry n hn)

private theorem normalized_permanent_tendsto :
    Tendsto (fun n => (normalized n).permanent) atTop (nhds 1) := by
  have he : Tendsto (fun n => Real.exp (activity (normalized n))) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp normalized_activity_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact one_le_permanent _ (normalized_nonneg n) (normalized_diagonal n hn)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact permanent_le_exp_activity _ (normalized_nonneg n) (normalized_diagonal n hn)

private theorem normalized_determinant_tendsto :
    Tendsto (fun n => (normalized n).det) atTop (nhds 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hp : Tendsto (fun n => (normalized n).permanent-1) atTop (nhds 0) := by
    simpa using normalized_permanent_tendsto.sub (tendsto_const_nhds (x := (1:ℝ)))
  change Tendsto (fun n => |(normalized n).det-1|) atTop (nhds 0)
  apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) _ hp
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact determinant_error_le_permanent_error _ (normalized_nonneg n) (normalized_diagonal n hn)

theorem result : D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio.claim := by
  have hratio : Tendsto (fun n => A392132 n / A392131 n) atTop (nhds 1) := by
    have h := normalized_permanent_tendsto.div normalized_determinant_tendsto (by norm_num : (1:ℝ)≠0)
    simp only [div_self (by norm_num : (1:ℝ)≠0)] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact normalized_ratio n hn
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hratio ε hε
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro n hn
  simpa only [Real.dist_eq] using hN n (le_trans (le_max_left _ _) hn)

end D5.S3.Combinatorics.Permanental.SpeziaA392131PellCirculantRatio
end
