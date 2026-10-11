/- GID: D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/PairCore
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/PairCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affinity loss along actual synchronized paths forces exact emissions on closed recurrent pair classes. -/

import D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
import D5.S3.TotalVariation.HellingerDivergence
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Logic.Relation

namespace D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.PairCore

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.TotalVariation.Bhattacharyya D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.HellingerDivergence
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators Matrix

noncomputable section

private lemma mul_vec_mono {T : Type*} [Fintype T] (A : Matrix T T ℝ)
    (hA : ∀ i j, 0 ≤ A i j) {f g : T → ℝ} (hfg : f ≤ g) : A *ᵥ f ≤ A *ᵥ g := by
  intro i
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hfg j) (hA i j)

private lemma pow_entries_nonneg {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (n : Nat) :
    ∀ i j, 0 ≤ (A ^ n) i j := by
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hA k j)

private lemma survival_antitone {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1) :
    Antitone (fun n : Nat => A ^ n *ᵥ (1 : T → ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [pow_succ, ← Matrix.mulVec_mulVec]
  exact mul_vec_mono _ (pow_entries_nonneg A hA n) hrow

/-- Follow actual edges only while the current row has no loss. A loss encountered before
the nominated endpoint already suffices, so no irreducibility of the affinity matrix is used. -/
private lemma loss_along_actual_path {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1)
    (R : T → T → Prop)
    (hfull : ∀ i, (A *ᵥ 1) i = 1 → ∀ j, R i j → 0 < A i j)
    {i j : T} (hpath : Relation.ReflTransGen R i j) (hj : (A *ᵥ 1) j < 1) :
    ∃ n : Nat, 1 ≤ n ∧ (A ^ n *ᵥ 1) i < 1 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨1, le_rfl, by simpa using hj⟩
  | @head i k hik _ ih =>
    by_cases hi : (A *ᵥ 1) i < 1
    · exact ⟨1, le_rfl, by simpa using hi⟩
    · have he : (A *ᵥ 1) i = 1 := le_antisymm (hrow i) (le_of_not_gt hi)
      obtain ⟨n, hn, hkn⟩ := ih
      refine ⟨n+1, by omega, ?_⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hle : A ^ n *ᵥ (1 : T → ℝ) ≤ 1 := by
        simpa using survival_antitone A hA hrow (Nat.zero_le n)
      calc
        (A *ᵥ (A ^ n *ᵥ 1)) i < (A *ᵥ 1) i := by
          apply Finset.sum_lt_sum
          · intro t _
            exact mul_le_mul_of_nonneg_left (hle t) (hA i t)
          · exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left hkn (hfull i he k hik)⟩
        _ = 1 := he

private lemma common_loss {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1)
    (R : T → T → Prop)
    (hfull : ∀ i, (A *ᵥ 1) i = 1 → ∀ j, R i j → 0 < A i j)
    (hirr : ∀ i j, Relation.ReflTransGen R i j)
    (hdef : ∃ j, (A *ᵥ 1) j < 1) :
    ∃ L : Nat, 1 ≤ L ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i, (A ^ L *ᵥ 1) i ≤ c := by
  classical
  obtain ⟨j, hj⟩ := hdef
  choose n hn hlt using fun i => loss_along_actual_path A hA hrow R hfull (hirr i j) hj
  let L := Finset.univ.sup n
  have hnL (i : T) : n i ≤ L := Finset.le_sup (Finset.mem_univ i)
  have hL (i : T) : (A ^ L *ᵥ 1) i < 1 :=
    lt_of_le_of_lt (survival_antitone A hA hrow (hnL i) i) (hlt i)
  let s : Finset ℝ := Finset.univ.image (fun i => (A ^ L *ᵥ 1) i)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  refine ⟨L, (hn j).trans (hnL j), s.max' hs, ?_, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.max'_mem hs)
    rw [← hi]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (pow_entries_nonneg A hA L i k) zero_le_one
  · apply (Finset.max'_lt_iff _).mpr
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hL i
  · intro i
    exact s.le_max' _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.PairCore
