/- GID: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite compatible labels causally realize every acquired marker prefix. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails

/-! Finite path compatibility gives causal realization with the original seed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels

open AdaptiveMarkerStoppingTails

/-- An archive word is chronological; it stores no root or source. -/
abbrev Word := List (Side × Bool)

def actions (w : Word) (k : ℕ) : List Side := (w.take k).map Prod.fst

def replies (w : Word) (k : ℕ) : List Bool := (w.take k).map Prod.snd

def sideTotal (w : Word) (s : Side) : ℕ := (w.map Prod.fst).count s

def occurrences (w : Word) (s : Side) (k : ℕ) : ℕ := (actions w k).count s

private theorem occurrences_le (w : Word) (s : Side) (k : ℕ) :
    occurrences w s k ≤ sideTotal w s := by
  exact ((List.take_sublist k w).map Prod.fst).count_le s

private theorem occurrences_next_le (w : Word) (k : Fin w.length) :
    occurrences w w[k].1 k + 1 ≤ sideTotal w w[k].1 := by
  have h := occurrences_le w w[k].1 (k + 1)
  change ((w.take (k.val + 1)).map Prod.fst).count w[k].1 ≤ sideTotal w w[k].1 at h
  rw [List.take_succ_eq_append_getElem k.isLt, List.map_append, List.count_append] at h
  simpa [occurrences, actions] using h

/-- The first true reply is the final reply, and the word is nonempty. -/
def terminalFirstTrue (w : Word) : Prop :=
  0 < w.length ∧ ∀ k : Fin w.length, w[k].2 = decide (k.val + 1 = w.length)

/-- The original seed selects each action from its reversed acquired prefix. -/
def policyConformity {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word) : Prop :=
  ∀ k : Fin w.length,
    w[k].1 = p.choose u (actions w k).reverse (replies w k).reverse

/-- Auxiliary finite labels, not part of the archive. The two arms share their
initial label, avoid 11, and produce each acquired reply by their local 00 test. -/
structure Labels (w : Word) where
  bit : (s : Side) → Fin (sideTotal w s + 1) → Bool
  root : bit false ⟨0, Nat.zero_lt_succ _⟩ = bit true ⟨0, Nat.zero_lt_succ _⟩
  no11 : ∀ s i (hi : i < sideTotal w s),
    ¬(bit s ⟨i, by omega⟩ = true ∧ bit s ⟨i + 1, by omega⟩ = true)
  response : ∀ k : Fin w.length,
    w[k].2 = decide
      (bit w[k].1 ⟨occurrences w w[k].1 k, by
          have := occurrences_next_le w k; omega⟩ = false ∧
       bit w[k].1 ⟨occurrences w w[k].1 k + 1, by
          have := occurrences_next_le w k; omega⟩ = false)

/-- Extend each finite label sequence by false beyond its last acquired vertex. -/
def extended {w : Word} (z : Labels w) (s : Side) (i : ℕ) : Bool :=
  if h : i ≤ sideTotal w s then z.bit s ⟨i, by omega⟩ else false

def completion {w : Word} (z : Labels w) : Source :=
  (z.bit false ⟨0, Nat.zero_lt_succ _⟩,
    (fun i => extended z false (i + 1), fun i => extended z true (i + 1)))

private theorem arm_completion {w : Word} (z : Labels w) (s : Side) (i : ℕ) :
    arm (completion z) s i = extended z s (i + 1) := by
  cases s <;> rfl

private theorem endpoint_completion {w : Word} (z : Labels w) (s : Side) (i : ℕ) :
    endpoint (completion z) s i = extended z s i := by
  cases i with
  | zero =>
    cases s
    · simp [endpoint, completion, extended]
    · simpa [endpoint, completion, extended] using z.root
  | succ i => exact arm_completion z s i

private theorem completion_support {w : Word} (z : Labels w) :
    noAdjacentOnes (completion z) := by
  intro s i
  rw [endpoint_completion, arm_completion]
  by_cases hi : i < sideTotal w s
  · simpa [extended, show i ≤ sideTotal w s by omega,
      show i + 1 ≤ sideTotal w s by omega] using z.no11 s i hi
  · simp [extended, show ¬i + 1 ≤ sideTotal w s by omega]

private theorem completion_response {w : Word} (z : Labels w) (k : Fin w.length) :
    markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) = w[k].2 := by
  have hb := occurrences_next_le w k
  rw [markerResponse, endpoint_completion, arm_completion]
  simpa only [extended,
    dite_eq_left (show occurrences w w[k].1 k ≤ sideTotal w w[k].1 by omega),
    dite_eq_left (show occurrences w w[k].1 k + 1 ≤ sideTotal w w[k].1 by omega)] using
      (z.response k).symm

/-- Causal induction: the already reconstructed acquired prefix is the next
policy input. No execution or inverse equation is assumed in Labels. -/
private theorem prefix_realization {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word)
    (ht : terminalFirstTrue w) (hp : policyConformity p u w) (z : Labels w) :
    ∀ k, k ≤ w.length → actualRun p u (completion z) k =
      ⟨(actions w k).reverse, (replies w k).reverse, decide (k = w.length)⟩ := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [actualRun, actions, replies, Nat.ne_of_lt ht.1]
  | succ k ih =>
    intro hk
    have hklt : k < w.length := by omega
    have hprior := ih (by omega)
    have hne : k ≠ w.length := by omega
    simp only [hne, decide_false] at hprior
    have hpolicy := hp ⟨k, hklt⟩
    have hresponse := completion_response z ⟨k, hklt⟩
    have hterminal := ht.2 ⟨k, hklt⟩
    change w[k].1 = p.choose u (actions w k).reverse (replies w k).reverse at hpolicy
    change markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) = w[k].2
      at hresponse
    change w[k].2 = decide (k + 1 = w.length) at hterminal
    rw [actualRun, hprior]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hpolicy]
    simp only [sideCount, List.count_reverse]
    change State.mk (w[k].1 :: (actions w k).reverse)
      (markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) ::
        (replies w k).reverse)
      (markerResponse (completion z) w[k].1 (occurrences w w[k].1 k)) = _
    rw [hresponse, hterminal]
    simp only [actions, replies, List.take_succ_eq_append_getElem hklt,
      List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, hterminal]

/-- Every compatible finite-label witness gives one supported zero-tail source
realizing all acquired prefixes and stopping for the first time at word length. -/
theorem finite_label_realization {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word)
    (ht : terminalFirstTrue w) (hp : policyConformity p u w) (z : Labels w) :
    noAdjacentOnes (completion z) ∧
    (∀ s (i : Fin (sideTotal w s + 1)),
      endpoint (completion z) s i = z.bit s i) ∧
    (∀ k, k ≤ w.length → actualRun p u (completion z) k =
      ⟨(actions w k).reverse, (replies w k).reverse, decide (k = w.length)⟩) ∧
    actualRun p u (completion z) w.length =
      ⟨(w.map Prod.fst).reverse, (w.map Prod.snd).reverse, true⟩ ∧
    actualQueryCount p u (completion z) w.length = w.length ∧
    stoppingTime p u (completion z) = (w.length : WithTop ℕ) := by
  have hprefix := prefix_realization p u w ht hp z
  have hlast : actualRun p u (completion z) w.length =
      ⟨(w.map Prod.fst).reverse, (w.map Prod.snd).reverse, true⟩ := by
    simpa [actions, replies] using hprefix w.length le_rfl
  refine ⟨completion_support z, ?_, hprefix, hlast, ?_, ?_⟩
  · intro s i
    rw [endpoint_completion]
    simp [extended, show i.val ≤ sideTotal w s by omega]
  · simp [actualQueryCount, hlast]
  · classical
    have hex : ∃ k, (actualRun p u (completion z) k).stopped = true := by
      exact ⟨w.length, by rw [hlast]⟩
    have hfind : Nat.find hex = w.length := by
      apply (Nat.find_eq_iff hex).mpr
      constructor
      · rw [hlast]
      · intro k hk
        rw [hprefix k (by omega)]
        simp [Nat.ne_of_lt hk]
    simp [stoppingTime, hex, hfind]

end D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels
