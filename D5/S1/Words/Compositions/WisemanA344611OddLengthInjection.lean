/- GID: D5/S1/Words/Compositions/WisemanA344611OddLengthInjection
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/WisemanA344611OddLengthInjection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nonnegative reverse-alternating partitions inject into odd-length partitions. -/

/-
admission_basis: open-problem-resolution (#23757; Proved)
escape_witness: none
proof_shape:
  reverseAlternatingSum, a344611, a160786, claim: definition.
  raiseList, raisePartition: definition; private implementation carriers.
  endpoint_even_le: content; two-step induction of the integer endpoint bound.
    Consumer: first_pair_eq.
  first_pair_eq: content after expanding endpoint_even_le.
    Consumer: raiseList_cross_ne.
  raiseList_spec: bind-only; parity cases, list order and arithmetic normalization.
    Consumers: raisePartition, raisePartition_injective.
  raiseList_cross_ne: content after expanding the endpoint induction.
    Consumer: raiseList_injective_on.
  raiseList_injective_on: content; separates the two parity branches.
    Consumer: raisePartition_injective.
  raisePartition_injective: content after expanding the list injection.
    Consumer: result.
  result: content after expanding all same-delivery helpers; its final step
    applies Nat.card_le_card_of_injective.
Direct frozen dependencies (same-delivery helpers expanded):
  reverseAlternatingSum:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
  a344611:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
  a160786:
    none.
  claim:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
  endpoint_even_le:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
  first_pair_eq:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
  raiseList:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
  raiseList_spec:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
  raiseList_cross_ne:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom.match_1
      sha256:a68942a380dfd45199998daf4f17ca199e59cae4c42668dec18b2bc743c5e46b
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
  raiseList_injective_on:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom.match_1
      sha256:a68942a380dfd45199998daf4f17ca199e59cae4c42668dec18b2bc743c5e46b
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump
      sha256:f84470e776ad42d805d5bfe08fee0287b4098ddeb9a87ae75d03ddaae3c73040
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump_bump
      sha256:f59553df8ae1ddaf3771d11773f4d6938118dabd05dce0d5fc938fe8b85ff79e
  raisePartition:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_pos
      sha256:b14edd4cb1256457a3ba7276355d4ed6d0b71955d3ae531299e060d1e5601263
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_sum
      sha256:73e94d147574a5858200392f7b2c178b278ec5dc977ddefabbb28d4509a9c360
  raisePartition_injective:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom.match_1
      sha256:a68942a380dfd45199998daf4f17ca199e59cae4c42668dec18b2bc743c5e46b
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sort_coe
      sha256:663f8a193cf06b5ef3ce5b86f447314c422e648c68d89596f1c5b8253f094abb
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_pos
      sha256:b14edd4cb1256457a3ba7276355d4ed6d0b71955d3ae531299e060d1e5601263
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_sum
      sha256:73e94d147574a5858200392f7b2c178b278ec5dc977ddefabbb28d4509a9c360
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump
      sha256:f84470e776ad42d805d5bfe08fee0287b4098ddeb9a87ae75d03ddaae3c73040
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump_bump
      sha256:f59553df8ae1ddaf3771d11773f4d6938118dabd05dce0d5fc938fe8b85ff79e
  result:
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom
      sha256:efbf2a9fd70bec8370796be26ac8d26e2ec48c7ed0a50dec9eeee23f05d761b1
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom.match_1
      sha256:a68942a380dfd45199998daf4f17ca199e59cae4c42668dec18b2bc743c5e46b
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums
      sha256:69e42940c91e1ff394d2d07105fae122f4c35d7ec7b6dcc562eb5079cdbebff9
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.bump
      sha256:3db8169d3a55c0f4fe73c63af5b3cb21ba0266097cbacd38c725e764caebb521
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sort_coe
      sha256:663f8a193cf06b5ef3ce5b86f447314c422e648c68d89596f1c5b8253f094abb
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_pos
      sha256:b14edd4cb1256457a3ba7276355d4ed6d0b71955d3ae531299e060d1e5601263
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sorted_sum
      sha256:73e94d147574a5858200392f7b2c178b278ec5dc977ddefabbb28d4509a9c360
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump
      sha256:f84470e776ad42d805d5bfe08fee0287b4098ddeb9a87ae75d03ddaae3c73040
    D5/S1/Words/Compositions/TrimmedAlternatingPartitions.unbump_bump
      sha256:f59553df8ae1ddaf3771d11773f4d6938118dabd05dce0d5fc938fe8b85ff79e
The decreasing parts are used as Multiset.sort directly, without a forwarding
sourceParts declaration; the literal sorting expression is inlined.
The public definitions reproduce the partition counts in #23757; the integer
accumulator is the existing owner, and getLastD 0 gives the empty sum zero.
OEIS A344611, FORMULA:
"Conjecture: a(n) <= A160786(n). The difference is 0, 0, 0, 0, 1, 2, 4, 9, 16, 28, 48, 79, ..."
All declarations are symbolic constructions or unbounded proofs; utility is none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24072
-/

import Batteries.Tactic.OpenPrivate

import Mathlib.SetTheory.Cardinal.NatCard
import D5.S1.Words.Compositions.TrimmedAlternatingPartitions

namespace D5.S1.Words.Compositions.WisemanA344611OddLengthInjection

/-- Source R(y_1,...,y_k) = Sum_i (-1)^(k-i) y_i, with R(()) = 0.
The existing integer recurrence s_j = y_j - s_(j-1), s_0 = 0,
has this value at its last endpoint. -/
noncomputable def reverseAlternatingSum {m : ℕ} (p : Nat.Partition m) : ℤ :=
  (D5.S1.Words.Compositions.TrimmedAlternatingPartitions.trimmedSums
    ((p.parts.sort (· ≥ ·)))).getLastD 0

/-- A344611(n): partitions of 2*n with reverse-alternating sum >= 0. -/
noncomputable def a344611 (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition (2 * n) // 0 ≤ reverseAlternatingSum p}

/-- A160786(n) = A027193(2*n+1): odd number of parts, with unrestricted part sizes. -/
noncomputable def a160786 (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition (2 * n + 1) // Odd p.parts.card}

/-- The A344611 FORMULA conjecture, including its offset n = 0. -/
def claim : Prop :=
  ∀ n : ℕ, a344611 n ≤ a160786 n

open D5.S1.Words.Compositions.TrimmedAlternatingPartitions
open private bump unbump unbump_bump sorted_pos sorted_sum sort_coe from
  D5.S1.Words.Compositions.TrimmedAlternatingPartitions

private theorem endpoint_even_le (q : List ℕ) (hs : q.Pairwise (· ≥ ·))
    (he : q.length % 2 = 0) (z : ℤ) : (sumsFrom z q).getLastD z ≤ z := by
  induction q using List.twoStepInduction generalizing z with
  | nil => simp [sumsFrom]
  | singleton a => simp at he
  | cons_cons a b q ih =>
    have hab : b ≤ a := (List.pairwise_cons.mp hs).1 b (by simp)
    have ht : q.length % 2 = 0 := by
      simp only [List.length_cons] at he
      omega
    have hh := ih hs.of_cons.of_cons ht ((b : ℤ) - ((a : ℤ) - z))
    simp only [sumsFrom, List.getLastD_cons] at *
    omega

private theorem first_pair_eq (a b : ℕ) (q : List ℕ)
    (hs : (a :: b :: q).Pairwise (· ≥ ·))
    (he : (a :: b :: q).length % 2 = 0)
    (hr : 0 ≤ (trimmedSums (a :: b :: q)).getLastD 0) : a = b := by
  have hab : b ≤ a := (List.pairwise_cons.mp hs).1 b (by simp)
  have ht : q.length % 2 = 0 := by
    simp only [List.length_cons] at he
    omega
  have hh := endpoint_even_le q hs.of_cons.of_cons ht ((b : ℤ) - (a : ℤ))
  simp only [trimmedSums, sumsFrom, List.getLastD_cons, sub_zero] at hr
  omega

private def raiseList (q : List ℕ) : List ℕ :=
  if Odd q.length then bump q else q ++ [1]

private theorem raiseList_spec (q : List ℕ) (hs : q.Pairwise (· ≥ ·))
    (hp : ∀ a ∈ q, 0 < a) :
    (raiseList q).Pairwise (· ≥ ·) ∧ (∀ a ∈ raiseList q, 0 < a) ∧
    (raiseList q).sum = q.sum + 1 ∧ Odd (raiseList q).length := by
  classical
  by_cases ho : Odd q.length
  · cases q with
    | nil => simp at ho
    | cons a t =>
      simp only [raiseList, ite_eq_left ho, bump]
      refine ⟨List.pairwise_cons.mpr ⟨?_, hs.of_cons⟩, ?_, ?_, ?_⟩
      · intro b hb
        have := (List.pairwise_cons.mp hs).1 b hb
        omega
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact hp b (by simp [hb])
      · simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simpa using ho
  · simp only [raiseList, ite_eq_right ho]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨hs, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact hp a ha
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hp a ha
      · rcases List.mem_singleton.mp ha with rfl
        decide
    · simp
    · simpa only [List.length_append, List.length_singleton] using Nat.odd_add_one.mpr ho

private theorem raiseList_cross_ne (q r : List ℕ)
    (ho : Odd q.length) (he : ¬ Odd r.length)
    (hsq : q.Pairwise (· ≥ ·)) (hsr : r.Pairwise (· ≥ ·))
    (hpq : ∀ a ∈ q, 0 < a)
    (hRr : 0 ≤ (trimmedSums r).getLastD 0) : raiseList q ≠ raiseList r := by
  classical
  cases q with
  | nil => simp at ho
  | cons a t =>
    intro h
    have ha := hpq a (by simp)
    simp only [raiseList, ite_eq_left ho, ite_eq_right he, bump] at h
    cases r with
    | nil =>
      simp only [List.nil_append] at h
      have hh := (List.cons.inj h).1
      omega
    | cons b u =>
      cases u with
      | nil => simp at he
      | cons c u =>
        have hmod : (b :: c :: u).length % 2 = 0 := Nat.not_odd_iff.mp he
        have hbc := first_pair_eq b c u hsr hmod hRr
        simp only [List.cons_append] at h
        have hh := (List.cons.inj h).1
        have ht := (List.cons.inj h).2
        have hc : c ∈ t := by rw [ht]; simp
        have hca := (List.pairwise_cons.mp hsq).1 c hc
        omega

private theorem raiseList_injective_on (q r : List ℕ)
    (hsq : q.Pairwise (· ≥ ·)) (hsr : r.Pairwise (· ≥ ·))
    (hpq : ∀ a ∈ q, 0 < a) (hpr : ∀ a ∈ r, 0 < a)
    (hRq : 0 ≤ (trimmedSums q).getLastD 0)
    (hRr : 0 ≤ (trimmedSums r).getLastD 0)
    (h : raiseList q = raiseList r) : q = r := by
  classical
  by_cases hq : Odd q.length <;> by_cases hr : Odd r.length
  · simp only [raiseList, ite_eq_left hq, ite_eq_left hr] at h
    have hh := congrArg unbump h
    simpa only [unbump_bump q hpq, unbump_bump r hpr] using hh
  · exact False.elim (raiseList_cross_ne q r hq hr hsq hsr hpq hRr h)
  · exact False.elim (raiseList_cross_ne r q hr hq hsr hsq hpr hRq h.symm)
  · simp only [raiseList, ite_eq_right hq, ite_eq_right hr] at h
    exact List.append_cancel_right h

private noncomputable def raisePartition {m : ℕ}
    (p : {p : Nat.Partition m // 0 ≤ reverseAlternatingSum p}) :
    {p : Nat.Partition (m + 1) // Odd p.parts.card} := by
  have hs := raiseList_spec ((p.val.parts.sort (· ≥ ·))) (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val)
  refine ⟨⟨raiseList ((p.val.parts.sort (· ≥ ·))), ?_, ?_⟩, ?_⟩
  · intro a ha
    exact hs.2.1 a ha
  · simpa only [Multiset.sum_coe, sorted_sum] using hs.2.2.1
  · simpa only [Multiset.coe_card] using hs.2.2.2

private theorem raisePartition_injective (m : ℕ) :
    Function.Injective (@raisePartition m) := by
  intro p q h
  have hs1 := (raiseList_spec ((p.val.parts.sort (· ≥ ·))) (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val)).1
  have hs2 := (raiseList_spec ((q.val.parts.sort (· ≥ ·))) (Multiset.pairwise_sort q.val.parts (· ≥ ·)) (sorted_pos q.val)).1
  have hh : raiseList ((p.val.parts.sort (· ≥ ·))) = raiseList ((q.val.parts.sort (· ≥ ·))) := by
    have hm := congrArg (fun p => p.val.parts.sort (· ≥ ·)) h
    change (raiseList ((p.val.parts.sort (· ≥ ·))) : Multiset ℕ).sort (· ≥ ·) =
      (raiseList ((q.val.parts.sort (· ≥ ·))) : Multiset ℕ).sort (· ≥ ·) at hm
    simpa only [sort_coe _ hs1, sort_coe _ hs2] using hm
  have he := raiseList_injective_on _ _ (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (Multiset.pairwise_sort q.val.parts (· ≥ ·))
    (sorted_pos p.val) (sorted_pos q.val) p.property q.property hh
  apply Subtype.ext
  apply Nat.Partition.ext
  have hm := congrArg (fun l : List ℕ => (l : Multiset ℕ)) he
  simpa only [Multiset.sort_eq] using hm

theorem result : D5.S1.Words.Compositions.WisemanA344611OddLengthInjection.claim := by
  intro n
  exact Nat.card_le_card_of_injective (@raisePartition (2 * n)) (raisePartition_injective _)

end D5.S1.Words.Compositions.WisemanA344611OddLengthInjection
