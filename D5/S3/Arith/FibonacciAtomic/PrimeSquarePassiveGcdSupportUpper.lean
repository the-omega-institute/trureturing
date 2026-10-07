/- GID: D5/S3/Arith/FibonacciAtomic/PrimeSquarePassiveGcdSupportUpper
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimeSquarePassiveGcdSupportUpper
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Original prime-square query supports have one shifted child band. -/

import D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController
import D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimeSquarePassiveGcdSupportUpper

open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
open D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization (memo)

/-- One empty-cache memoized original tree bounds all actual histories and
retains the complete positive numerical future on every natural source pair. -/
theorem result (p : ℕ) (hp : p.Prime) :
    (∀ v : ℕ × ℕ,
      (runPassiveProtocol (read p 2) (memo (protocol p 2) (fun _ => none)) v).length ≤
        zeroRank p + p - 2) ∧
    (∀ v w : ℕ × ℕ,
      runPassiveProtocol (read p 2) (memo (protocol p 2) (fun _ => none)) v =
        runPassiveProtocol (read p 2) (memo (protocol p 2) (fun _ => none)) w →
      ∀ k : ℕ, 0 < k → actualGcd (p ^ 2) k v = actualGcd (p ^ 2) k w) := by
  classical
  let : DecidableEq PositiveTime := Classical.decEq PositiveTime
  let r := zeroRank p
  have hr : 3 ≤ r := by simpa [r] using (rank_facts p hp 1 le_rfl).1
  have hp2 := hp.two_le
  let S (t : ℕ) : Finset ℕ := Finset.Icc 1 r ∪
    (Finset.Icc 1 (p - 2)).image (fun j => t + j * r + 1)
  have base (t k : ℕ) (hk : 1 ≤ k ∧ k ≤ r) : k ∈ S t :=
    Finset.mem_union_left _ (Finset.mem_Icc.mpr hk)
  have lift (t j : ℕ) (ht : t < r) (hj : j < p - 1) : t + j * r + 1 ∈ S t := by
    by_cases hz : j = 0
    · subst j
      exact base t _ (by simpa using (show 1 ≤ t + 1 ∧ t + 1 ≤ r by omega))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩)
  have childSupport (t : ℕ) (ht : t < r) (v : ℕ × ℕ) :
      ∀ n j, n + j = p - 1 → ∀ q ∈
        (runPassiveProtocol (read p 2)
          (children (p ^ 2) r t (continuation p 0 0 2) n j) v).map Sigma.fst,
        q.val ∈ S t := by
    intro n
    induction n with
    | zero => intro j _ q hq; simp [children, continuation, runPassiveProtocol] at hq
    | succ n ih =>
      intro j hj q hq
      simp only [children, runPassiveProtocol, List.map_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact lift t j ht (by omega)
      · split at hq
        · simp [continuation, runPassiveProtocol] at hq
        · exact ih (j + 1) (by omega) q hq
  have continuationSupport (c t : ℕ) (hc : c < 2) (ht : t < r) (v : ℕ × ℕ) :
      ∀ q ∈ (runPassiveProtocol (read p 2)
        (continuation p c (2 - c - 1) 1 t) v).map Sigma.fst, q.val ∈ S t := by
    by_cases hz : c = 0
    · subst c
      simp only [Nat.sub_zero, Nat.reduceSub, continuation, Nat.reduceAdd, pow_one]
      split
      · intro q hq
        simp only [runPassiveProtocol, List.map_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact base t _ (by change 1 ≤ t + 1 ∧ t + 1 ≤ r; omega)
        · split at hq <;> simp [runPassiveProtocol] at hq
      · exact childSupport t ht v (p - 1) 0 (by omega)
    · have hc1 : c = 1 := by omega
      subst c
      simp [continuation, runPassiveProtocol]
  have scanSupport (c : ℕ) (hc : c < 2) (v : ℕ × ℕ) :
      ∀ n phase, n + phase = r → ∃ t, t < r ∧ ∀ q ∈
        (runPassiveProtocol (read p 2)
          (firstLayer (p ^ (c + 1)) (continuation p c (2 - c - 1) 1) n phase) v).map Sigma.fst,
        q.val ∈ S t := by
    intro n
    induction n with
    | zero =>
      intro phase _
      exact ⟨0, by omega, by simp [firstLayer, runPassiveProtocol]⟩
    | succ n ih =>
      intro phase hphase
      by_cases hit : p ^ (c + 1) ∣ read p 2 ⟨phase + 1, by omega⟩ v
      · refine ⟨phase, by omega, ?_⟩
        intro q hq
        simp only [firstLayer, runPassiveProtocol, hit, ite_true, List.map_cons,
          List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact base phase _ (by change 1 ≤ phase + 1 ∧ phase + 1 ≤ r; omega)
        · exact continuationSupport c phase hc (by omega) v q hq
      · obtain ⟨t, ht, hs⟩ := ih (phase + 1) (by omega)
        refine ⟨t, ht, ?_⟩
        intro q hq
        simp only [firstLayer, runPassiveProtocol, hit, ite_false, List.map_cons,
          List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact base t _ (by change 1 ≤ phase + 1 ∧ phase + 1 ≤ r; omega)
        · exact hs q hq
  have protocolSupport (v : ℕ × ℕ) : ∃ t, t < r ∧ ∀ q ∈
      (runPassiveProtocol (read p 2) (protocol p 2) v).map Sigma.fst, q.val ∈ S t := by
    simp only [protocol, runPassiveProtocol, List.map_cons]
    split
    · refine ⟨0, by omega, ?_⟩
      intro q hq
      simp only [runPassiveProtocol, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl
      · exact base 0 1 ⟨by omega, by omega⟩
      · exact base 0 2 ⟨by omega, by omega⟩
    · split
      · rename_i h
        have hc := (Classical.choose_spec h).1
        obtain ⟨t, ht, hs⟩ := scanSupport (Classical.choose h) hc v r 0 (by omega)
        refine ⟨t, ht, ?_⟩
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact base t 1 ⟨by omega, by omega⟩
        · exact base t 2 ⟨by omega, by omega⟩
        · exact hs q hq
      · refine ⟨0, by omega, ?_⟩
        intro q hq
        simp only [runPassiveProtocol, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl
        · exact base 0 1 ⟨by omega, by omega⟩
        · exact base 0 2 ⟨by omega, by omega⟩
  have memoLaw := D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization.result
    (protocol p 2) (read p 2)
  refine ⟨?_, ?_⟩
  · intro v
    obtain ⟨t, _, hs⟩ := protocolSupport v
    let Q := ((runPassiveProtocol (read p 2) (protocol p 2) v).map Sigma.fst).toFinset
    have hinj : Function.Injective (fun q : PositiveTime => q.val) := Subtype.val_injective
    have hcard : (Q.image (fun q => q.val)).card = Q.card := Finset.card_image_of_injective Q hinj
    have hsub : Q.image (fun q => q.val) ⊆ S t := by
      intro k hk
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
      exact hs q (List.mem_toFinset.mp hq)
    have hbound := Finset.card_le_card hsub
    have hunion := Finset.card_union_le (Finset.Icc 1 r)
      ((Finset.Icc 1 (p - 2)).image (fun j => t + j * r + 1))
    have himage := Finset.card_image_le (s := Finset.Icc 1 (p - 2))
      (f := fun j => t + j * r + 1)
    have hIcc : (Finset.Icc 1 r).card = r := by simp
    have hchild : (Finset.Icc 1 (p - 2)).card = p - 2 := by simp
    rw [hcard] at hbound
    rw [(memoLaw.1 v).2.2.2]
    have hfinal : Q.card ≤ r + p - 2 := by
      dsimp [S] at hbound
      omega
    simpa only [Q, r] using hfinal
  · intro v w same
    exact (protocol_spec p 2 hp (by omega)).2 v w ((memoLaw.2 v w).mp same)

#print axioms result

end D5.S3.Arith.FibonacciAtomic.PrimeSquarePassiveGcdSupportUpper
