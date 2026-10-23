/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strict native Fibonacci support chain and universal bounded-address agreement. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open DelayedOriginalReadout (rights)

/-- Both strict inclusions hold on all literal addresses, while every address
of length at most k is present in all three native trees. -/
theorem actual_fibonacci_support_chain (k : Nat) (hk : 1 ≤ k) :
    let T := fun j : Nat => substitution^[j] (FreeMagma.of true)
    let S := fun j : Nat => {q : Address | readout q (T j) ≠ .absent}
    let H := {q : Address | readout q (FreeMagma.mul (T (2*k)) (T (2*k))) ≠ .absent}
    S (2*k) ⊂ S (2*k+1) ∧ S (2*k+1) ⊂ H ∧
      ∀ q : Address, q.length ≤ k →
        (q ∈ S (2*k) ↔ q ∈ S (2*k+1)) ∧ (q ∈ S (2*k+1) ↔ q ∈ H) := by
  let T := fun j : Nat => substitution^[j] (FreeMagma.of true)
  let S := fun j : Nat => {q : Address | readout q (T j) ≠ .absent}
  let H := {q : Address | readout q (FreeMagma.mul (T (2*k)) (T (2*k))) ≠ .absent}
  change S (2*k) ⊂ S (2*k+1) ∧ S (2*k+1) ⊂ H ∧ _
  have recurrence (n : Nat) : T (n+2) = FreeMagma.mul (T (n+1)) (T n) := by
    have h := (SourceTransportCentralizer.source_transport_centralizer.1 (T n)).mpr ⟨n, rfl⟩
    simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using h
  have root (u : Source) : readout [] u ≠ .absent := by
    cases u with
    | of b => cases b <;> simp [readout]
    | mul l r => simp [readout]
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have presence (q : Address) (u : Source) :
      readout q u ≠ .absent ↔ ∃ t : Source, subtree q u = some t := by
    have h := readAt q [] u
    simp only [List.append_nil] at h
    rw [h]
    cases hs : subtree q u with
    | none => simp
    | some t => simp [root t]
  have monotone (n : Nat) : S n ⊆ S (n+1) := by
    intro q hq
    obtain ⟨t, ht⟩ := (presence q (T n)).mp hq
    apply (presence q (T (n+1))).mpr
    refine ⟨substitution t, ?_⟩
    simpa only [T, Function.iterate_succ_apply', Function.iterate_zero, id_eq] using
      NativeDepthPatterns.original_present_transport 1 q (T n) t ht
  have short (q : Address) : ∀ n : Nat, 2*q.length ≤ n → readout q (T n) ≠ .absent := by
    induction q with
    | nil => intro n _; exact root _
    | cons b q ih =>
        intro n hn
        have hn' : 2 ≤ n := by simp only [List.length_cons] at hn; omega
        obtain ⟨m, hm⟩ : ∃ m : Nat, n = m+2 := ⟨n-2, by omega⟩
        subst n
        rw [recurrence]
        cases b
        · exact ih (m+1) (by simp only [List.length_cons] at hn; omega)
        · exact ih m (by simp only [List.length_cons] at hn; omega)
  have spine (j n : Nat) (q : Address) :
      readout (rights j ++ q) (T (n+2*j)) = readout q (T n) := by
    induction j generalizing n with
    | zero => simp [rights]
    | succ j ih =>
        have he : n+2*(j+1) = (n+2*j)+2 := by omega
        rw [he, recurrence]
        simpa only [rights, List.replicate_succ, List.cons_append, readout] using ih n
  have pairInclusion : S (2*k+1) ⊆ H := by
    intro q hq
    have he : 2*k+1 = (2*k-1)+2 := by omega
    change readout q (T (2*k+1)) ≠ .absent at hq
    rw [he, recurrence] at hq
    have hi := monotone (2*k-1)
    have hi' : S (2*k-1) ⊆ S (2*k) := by simpa only [show 2*k-1+1 = 2*k by omega] using hi
    cases q with
    | nil => exact root _
    | cons b q =>
        cases b
        · simpa only [H, Set.mem_ofPred_eq, readout, show 2*k-1+1 = 2*k by omega] using hq
        · exact hi' hq
  obtain ⟨m, rfl⟩ : ∃ m : Nat, k = m+1 := ⟨k-1, by omega⟩
  have firstStrict : S (2*(m+1)) ⊂ S (2*(m+1)+1) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨monotone _, ?_⟩
    intro he
    have old : readout (rights m ++ [false, false]) (T (2*(m+1))) = .absent := by
      have hn : 2*(m+1) = 2+2*m := by omega
      rw [hn, spine]
      rfl
    have fresh : readout (rights m ++ [false, false]) (T (2*(m+1)+1)) ≠ .absent := by
      have hn : 2*(m+1)+1 = 3+2*m := by omega
      rw [hn, spine]
      decide
    have member : rights m ++ [false, false] ∈ S (2*(m+1)) := by
      rw [he]; exact fresh
    exact member old
  have secondStrict : S (2*(m+1)+1) ⊂ H := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨pairInclusion, ?_⟩
    intro he
    have old : readout (rights (m+1) ++ [false]) (T (2*(m+1)+1)) = .absent := by
      have hn : 2*(m+1)+1 = 1+2*(m+1) := by omega
      rw [hn, spine]
      rfl
    have fresh : rights (m+1) ++ [false] ∈ H := by
      change readout (rights (m+1) ++ [false])
        (FreeMagma.mul (T (2*(m+1))) (T (2*(m+1)))) ≠ .absent
      simp only [rights, List.replicate_succ, List.cons_append, readout]
      change readout (rights m ++ [false]) (T (2*(m+1))) ≠ .absent
      have hn : 2*(m+1) = 2+2*m := by omega
      rw [hn, spine]
      decide
    have member : rights (m+1) ++ [false] ∈ S (2*(m+1)+1) := by
      rw [he]; exact fresh
    exact member old
  refine ⟨firstStrict, secondStrict, ?_⟩
  intro q hq
  have a : q ∈ S (2*(m+1)) := short q _ (by omega)
  have b := monotone (2*(m+1)) a
  have c := pairInclusion b
  exact ⟨iff_of_true a b, iff_of_true b c⟩

end D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain

#print axioms D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain.actual_fibonacci_support_chain
