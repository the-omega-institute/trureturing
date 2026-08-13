/- GID: D5/S1/Words/Complexity/MorseHedlund
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/MorseHedlund
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Low factor complexity forces a one-sided infinite word to be eventually periodic. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

namespace D5.S1.Words.Complexity

variable {A : Type*} [Fintype A]

/-- The length-`n` factor of `x` beginning at the natural index `i`. -/
def wordFactor (x : Nat -> A) (n i : Nat) : Fin n -> A :=
  fun k => x (i + k)

/-- All length-`n` factors of a one-sided infinite word, at natural starts. -/
noncomputable def wordFactorSet (x : Nat -> A) (n : Nat) : Finset (Fin n -> A) := by
  classical
  exact Finset.univ.filter fun w => exists i, w = wordFactor x n i

/-- Membership in the factor set is exactly occurrence at a natural starting index. -/
theorem mem_wordFactorSet {x : Nat -> A} {n : Nat} {w : Fin n -> A} :
    w ∈ wordFactorSet x n ↔ exists i, w = wordFactor x n i := by
  classical
  simp [wordFactorSet]

private theorem wordFactorSet_zero_card (x : Nat -> A) : (wordFactorSet x 0).card = 1 := by
  classical
  have hset : wordFactorSet x 0 = {fun i => Fin.elim0 i} := by
    ext w
    rw [mem_wordFactorSet, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact Fin.elim0 i
    · intro hw
      exact ⟨0, by rw [hw]; funext i; exact Fin.elim0 i⟩
  rw [hset, Finset.card_singleton]

/-- Eventual periodicity in the repository's one-sided, natural-tail convention. -/
def EventuallyPeriodicWord (x : Nat -> A) : Prop :=
  exists s p : Nat, 0 < p ∧ forall t, x (s + t + p) = x (s + t)

private noncomputable def dropLast (x : Nat -> A) (n : Nat) :
    ↥(wordFactorSet x (n + 1)) -> ↥(wordFactorSet x n) := by
  intro w
  refine ⟨fun k => w.1 k.castSucc, ?_⟩
  obtain ⟨i, hi⟩ := mem_wordFactorSet.mp w.2
  apply mem_wordFactorSet.mpr
  refine ⟨i, ?_⟩
  funext k
  simpa [wordFactor] using congrFun hi k.castSucc

private theorem dropLast_surjective (x : Nat -> A) (n : Nat) :
    Function.Surjective (dropLast x n) := by
  intro w
  obtain ⟨i, hi⟩ := mem_wordFactorSet.mp w.2
  let v : ↥(wordFactorSet x (n + 1)) :=
    ⟨wordFactor x (n + 1) i, mem_wordFactorSet.mpr ⟨i, rfl⟩⟩
  refine ⟨v, Subtype.ext ?_⟩
  change (fun k => wordFactor x (n + 1) i k.castSucc) = w.1
  rw [hi]
  rfl

private theorem factor_complexity_mono (x : Nat -> A) (n : Nat) :
    (wordFactorSet x n).card <= (wordFactorSet x (n + 1)).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_surjective (dropLast x n) (dropLast_surjective x n)

private theorem exists_flat_complexity_step (x : Nat -> A) {N : Nat}
    (hcomplexity : (wordFactorSet x N).card <= N) :
    exists k, k < N ∧ (wordFactorSet x k).card = (wordFactorSet x (k + 1)).card := by
  by_contra hflat
  push Not at hflat
  have hlower : forall m, m <= N -> m + 1 <= (wordFactorSet x m).card := by
    intro m hm
    induction m with
    | zero => simpa using (wordFactorSet_zero_card x).ge
    | succ m ih =>
        have hmN : m < N := by omega
        have hmono := factor_complexity_mono x m
        have hne := hflat m hmN
        have hprev := ih (by omega)
        omega
  have := hlower N le_rfl
  omega

private theorem dropLast_injective_of_flat (x : Nat -> A) {n : Nat}
    (hflat : (wordFactorSet x n).card = (wordFactorSet x (n + 1)).card) :
    Function.Injective (dropLast x n) := by
  exact ((Fintype.bijective_iff_surjective_and_card (dropLast x n)).mpr
    ⟨dropLast_surjective x n, by simpa only [Fintype.card_coe] using hflat.symm⟩).1

private theorem factor_succ_eq_of_factor_eq_of_flat (x : Nat -> A) {n i j : Nat}
    (hflat : (wordFactorSet x n).card = (wordFactorSet x (n + 1)).card)
    (hfactor : wordFactor x n i = wordFactor x n j) :
    wordFactor x (n + 1) i = wordFactor x (n + 1) j := by
  let u : ↥(wordFactorSet x (n + 1)) :=
    ⟨wordFactor x (n + 1) i, mem_wordFactorSet.mpr ⟨i, rfl⟩⟩
  let v : ↥(wordFactorSet x (n + 1)) :=
    ⟨wordFactor x (n + 1) j, mem_wordFactorSet.mpr ⟨j, rfl⟩⟩
  have huv : u = v := dropLast_injective_of_flat x hflat (Subtype.ext hfactor)
  exact congrArg Subtype.val huv

private theorem shifted_factors_eq_of_flat (x : Nat -> A) {n i j : Nat}
    (hflat : (wordFactorSet x n).card = (wordFactorSet x (n + 1)).card)
    (hfactor : wordFactor x n i = wordFactor x n j) (t : Nat) :
    wordFactor x n (i + t) = wordFactor x n (j + t) := by
  induction t with
  | zero => simpa using hfactor
  | succ t ih =>
      have hext := factor_succ_eq_of_factor_eq_of_flat x hflat ih
      funext k
      have hk := congrFun hext k.succ
      simpa [wordFactor, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk

private theorem equal_factors_give_periodic_tail (x : Nat -> A) {n i j : Nat}
    (hij : i < j)
    (hflat : (wordFactorSet x n).card = (wordFactorSet x (n + 1)).card)
    (hfactor : wordFactor x n i = wordFactor x n j) : EventuallyPeriodicWord x := by
  refine ⟨i + n, j - i, Nat.sub_pos_of_lt hij, ?_⟩
  intro t
  have hshift := shifted_factors_eq_of_flat x hflat hfactor t
  have hext := factor_succ_eq_of_factor_eq_of_flat x hflat hshift
  have hletter := congrFun hext (Fin.last n)
  have hleft : i + n + t + (j - i) = j + t + n := by omega
  have hright : i + n + t = i + t + n := by omega
  rw [hleft, hright]
  simpa [wordFactor] using hletter.symm

/-- The one-sided Morse-Hedlund theorem: low factor complexity forces eventual periodicity. -/
theorem eventuallyPeriodic_of_factor_complexity_le (x : Nat -> A) (n : Nat)
    (hcomplexity : (wordFactorSet x n).card <= n) : EventuallyPeriodicWord x := by
  classical
  obtain ⟨k, hk, hflat⟩ := exists_flat_complexity_step x hcomplexity
  let starts : Fin ((wordFactorSet x k).card + 1) -> ↥(wordFactorSet x k) := fun i =>
    ⟨wordFactor x k i, mem_wordFactorSet.mpr ⟨i, rfl⟩⟩
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt starts (by
    simp only [Fintype.card_coe, Fintype.card_fin]
    omega)
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact equal_factors_give_periodic_tail x hij' hflat (congrArg Subtype.val heq)
  · exact equal_factors_give_periodic_tail x hji' hflat (congrArg Subtype.val heq.symm)

/-- A non-eventually-periodic word has at least `n + 1` factors of every length `n`. -/
theorem factor_complexity_ge_add_one_of_not_eventuallyPeriodic (x : Nat -> A)
    (haperiodic : ¬EventuallyPeriodicWord x) (n : Nat) :
    n + 1 <= (wordFactorSet x n).card := by
  by_contra h
  apply haperiodic
  apply eventuallyPeriodic_of_factor_complexity_le x n
  omega

private def boundedWordFactorSet [DecidableEq A]
    (x : Nat -> A) (n starts : Nat) : Finset (Fin n -> A) :=
  (Finset.range starts).image fun i => wordFactor x n i

private def periodThreeWord (n : Nat) : Fin 2 := if n % 3 = 1 then 1 else 0

private def prefixedPeriodThreeWord (n : Nat) : Fin 2 :=
  if n < 2 then 1 else periodThreeWord (n - 2)

private theorem period_three_bounded_complexities :
    (List.range 6).map (fun n => (boundedWordFactorSet periodThreeWord n 12).card) =
      [1, 2, 3, 3, 3, 3] := by
  decide

private theorem prefixed_period_three_bounded_complexities :
    (List.range 13).map (fun n => (boundedWordFactorSet prefixedPeriodThreeWord n 18).card) =
      [1, 2, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] := by
  decide

private theorem prefixed_period_three_tail : EventuallyPeriodicWord prefixedPeriodThreeWord := by
  refine ⟨2, 3, by omega, ?_⟩
  intro t
  have hperiod : periodThreeWord (t + 3) = periodThreeWord t := by
    simp [periodThreeWord]
  simp only [prefixedPeriodThreeWord, if_neg (by omega : ¬2 + t + 3 < 2),
    if_neg (by omega : ¬2 + t < 2)]
  have hleft : 2 + t + 3 - 2 = t + 3 := by omega
  have hright : 2 + t - 2 = t := by omega
  rw [hleft, hright]
  exact hperiod

#print axioms eventuallyPeriodic_of_factor_complexity_le
#print axioms factor_complexity_ge_add_one_of_not_eventuallyPeriodic

end D5.S1.Words.Complexity
