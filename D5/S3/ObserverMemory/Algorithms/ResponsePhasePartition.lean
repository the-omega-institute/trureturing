/- GID: D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ResponsePhasePartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded monotone reply ranks yield native finite and coherent half-line phases. -/

import D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
import Mathlib.Order.OrderIsoNat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition

open GuardedPhaseExecution

universe u v

/-- The sum of installed-coordinate ranks at one epoch. -/
def potential {A : Type u} [Fintype A] {R : Type v} {q : Nat}
    (rank : R → Fin (q + 1)) (obs : Nat → A → R) (j : Nat) : Nat :=
  ∑ a, (rank (obs j a)).val

/-- Every finite interval has strict native guards, distinct adjacent replies,
and one extra phase at most per unit of potential increase. -/
theorem finite_response_partition {A : Type u} [Fintype A] {R : Type v} {q : Nat}
    (obs : Nat → A → R) (rank : R → Fin (q + 1))
    (injective : Function.Injective rank)
    (monotone : ∀ a, Monotone (fun j => rank (obs j a)))
    (N J : Nat) (lower : N ≤ J) :
    ∃ blocks : List (Nat × (A → R)),
      Partition obs N (J + 1) blocks ∧
      blocks.IsChain (fun left right => left.2 ≠ right.2) ∧
      blocks.length + potential rank obs N ≤ potential rank obs J + 1 := by
  classical
  have construction : ∀ d N : Nat,
      ∃ blocks : List (Nat × (A → R)),
        Partition obs N (N + d + 1) blocks ∧
        blocks.IsChain (fun left right => left.2 ≠ right.2) ∧
        blocks.length + potential rank obs N ≤ potential rank obs (N + d) + 1 := by
    intro d
    induction d with
    | zero =>
        intro N
        refine ⟨[(N + 1, obs N)], ⟨by omega, by omega, ?_⟩, by simp, ?_⟩
        · intro j hj hk
          have : j = N := by omega
          subst j
          rfl
        · simp only [List.length_singleton, Nat.add_zero]
          omega
    | succ d ih =>
        intro N
        obtain ⟨blocks, partition, adjacent, count⟩ := ih (N + 1)
        cases blocks with
        | nil => exact partition.elim
        | cons first rest =>
            rcases first with ⟨b, reply⟩
            have firstGuard : Guard obs reply (N + 1) b := by
              cases rest with
              | nil => exact partition.2.2
              | cons next rest => exact partition.2.1
            have firstLower : N + 1 < b := by
              cases rest with
              | nil => exact partition.1
              | cons next rest => exact partition.1
            have firstReply : obs (N + 1) = reply :=
              firstGuard (N + 1) le_rfl firstLower
            have potentialStep : potential rank obs N ≤ potential rank obs (N + 1) :=
              Finset.sum_le_sum (fun a _ => monotone a (by omega))
            by_cases same : obs N = reply
            · have guard : Guard obs reply N b := by
                intro j hj hk
                by_cases atStart : j = N
                · simpa [atStart] using same
                · exact firstGuard j (by omega) hk
              refine ⟨(b, reply) :: rest, ?_, adjacent, ?_⟩
              · cases rest with
                | nil => exact ⟨by omega,
                      by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                        using partition.2.1, guard⟩
                | cons next rest =>
                    exact ⟨by omega, guard,
                      by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                        using partition.2.2⟩
              · simp only [List.length_cons] at count ⊢
                have endpoint : N + 1 + d = N + (d + 1) := by omega
                rw [endpoint] at count
                omega
            · have different : obs N ≠ obs (N + 1) := by simpa [firstReply] using same
              have changed : ∃ a, obs N a ≠ obs (N + 1) a := by
                by_contra absent
                push Not at absent
                exact different (funext absent)
              obtain ⟨a, ha⟩ := changed
              have strict : (rank (obs N a)).val < (rank (obs (N + 1) a)).val := by
                have le := monotone a (show N ≤ N + 1 by omega)
                have ne : rank (obs N a) ≠ rank (obs (N + 1) a) :=
                  fun equality => ha (injective equality)
                exact lt_of_le_of_ne le (fun equality => ne (Fin.ext equality))
              have charge : potential rank obs N < potential rank obs (N + 1) :=
                Finset.sum_lt_sum (fun a _ => monotone a (by omega))
                  ⟨a, Finset.mem_univ a, strict⟩
              refine ⟨(N + 1, obs N) :: (b, reply) :: rest, ?_, ?_, ?_⟩
              · refine ⟨by omega, ?_, ?_⟩
                · intro j hj hk
                  have : j = N := by omega
                  subst j
                  rfl
                · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using partition
              · simpa only [List.isChain_cons_cons] using And.intro same adjacent
              · simp only [List.length_cons] at count ⊢
                have endpoint : N + 1 + d = N + (d + 1) := by omega
                rw [endpoint] at count
                omega
  obtain ⟨blocks, partition, adjacent, count⟩ := construction (J - N) N
  have endpoint : N + (J - N) = J := by omega
  rw [endpoint] at partition count
  exact ⟨blocks, partition, adjacent, count⟩

/-- Retain the actual start of the final guard and replace only its delimiter. -/
private theorem final_block {A : Type u} {R : Type v} {obs : Nat → A → R}
    {N T : Nat} {blocks : List (Nat × (A → R))}
    (partition : Partition obs N (T + 1) blocks) :
    ∃ (initial : List (Nat × (A → R))) (s : Nat) (z : A → R),
      N ≤ s ∧ s ≤ T ∧ blocks = initial ++ [(T + 1, z)] ∧
      Guard obs z s (T + 1) ∧
      ∀ J, s ≤ J → Guard obs z s (J + 1) →
        Partition obs N (J + 1) (initial ++ [(J + 1, z)]) := by
  induction blocks generalizing N with
  | nil => exact partition.elim
  | cons first rest ih =>
      rcases first with ⟨b, reply⟩
      cases rest with
      | nil =>
          rcases partition with ⟨lower, rfl, guard⟩
          refine ⟨[], N, reply, le_rfl, by omega, rfl, guard, ?_⟩
          intro J hJ newGuard
          exact ⟨by omega, rfl, newGuard⟩
      | cons next rest =>
          obtain ⟨initial, s, z, hbs, hsT, reconstruction, guard, extend⟩ :=
            ih partition.2.2
          have hNb := partition.1
          refine ⟨(b, reply) :: initial, s, z, by omega, hsT, ?_, guard, ?_⟩
          · simpa only [List.cons_append] using congrArg (List.cons (b, reply)) reconstruction
          · intro J hJ newGuard
            have remaining := extend J hJ newGuard
            cases initial with
            | nil =>
                simp only [List.nil_append] at reconstruction remaining ⊢
                exact ⟨partition.1, partition.2.1, remaining⟩
            | cons head tail =>
                exact ⟨partition.1, partition.2.1, remaining⟩

/-- One fixed initial and one final guard serve every cutoff of the half-line.
The final guard starts at its actual finite-block start, even before stabilization. -/
theorem half_line_response_partition {A : Type u} [Fintype A] {R : Type v} {q : Nat}
    (obs : Nat → A → R) (rank : R → Fin (q + 1))
    (injective : Function.Injective rank)
    (monotone : ∀ a, Monotone (fun j => rank (obs j a))) (N : Nat) :
    ∃ (initial : List (Nat × (A → R))) (s : Nat) (z : A → R),
      N ≤ s ∧ (∀ j, s ≤ j → obs j = z) ∧
      (initial ++ [(s + 1, z)]).IsChain (fun left right => left.2 ≠ right.2) ∧
      initial.length + 1 ≤ q * Fintype.card A + 1 ∧
      ∀ J, s ≤ J → Partition obs N (J + 1) (initial ++ [(J + 1, z)]) := by
  classical
  let vector : Nat →o (A → Fin (q + 1)) :=
    ⟨fun j a => rank (obs j a), fun _ _ h a => monotone a h⟩
  obtain ⟨t, stable⟩ := WellFoundedGT.monotone_chain_condition vector
  let T := max N t
  have tail : ∀ j, T ≤ j → obs j = obs T := by
    intro j hj
    funext a
    apply injective
    exact congrFun ((stable T (by exact le_max_right N t)).symm.trans
      (stable j (by omega))).symm a
  obtain ⟨blocks, native, adjacent, bound⟩ :=
    finite_response_partition obs rank injective monotone N T (le_max_left N t)
  obtain ⟨initial, s, z, hNs, hsT, reconstruction, guard, extend⟩ := final_block native
  have atT : obs T = z := guard T hsT (by omega)
  have constant : ∀ j, s ≤ j → obs j = z := by
    intro j hj
    by_cases before : j ≤ T
    · exact guard j hj (by omega)
    · exact (tail j (by omega)).trans atT
  have length : blocks.length = initial.length + 1 := by simp [reconstruction]
  have chain : ∀ J : Nat, (initial ++ [(J + 1, z)]).IsChain
      (fun (left right : Nat × (A → R)) => left.2 ≠ right.2) := by
    intro J
    apply (List.isChain_map Prod.snd).mp
    have old := (List.isChain_map Prod.snd).mpr adjacent
    simpa only [reconstruction, List.map_append, List.map_singleton] using old
  have cap : potential rank obs T ≤ q * Fintype.card A := by
    calc
      potential rank obs T ≤ ∑ _a : A, q :=
        Finset.sum_le_sum (fun a _ => Nat.le_of_lt_succ (rank (obs T a)).isLt)
      _ = q * Fintype.card A := by simp [Nat.mul_comm]
  refine ⟨initial, s, z, hNs, constant, chain s, ?_, ?_⟩
  · omega
  · intro J hJ
    exact extend J hJ (fun j hj _ => constant j hj)

#print axioms finite_response_partition
#print axioms half_line_response_partition

end D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition
