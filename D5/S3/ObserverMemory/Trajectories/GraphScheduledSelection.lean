/- GID: D5/S3/ObserverMemory/Trajectories/GraphScheduledSelection
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/GraphScheduledSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Causal graph schedules and their complete early selected fibers. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.Trajectories.GraphScheduledSelection

open Finset
open scoped BigOperators Classical

/-- Positions and identity numbers are one-based; graph vertices are zero-based. -/
def pairCount (r : ℕ) : ℕ := r.choose 2

def lastTarget (r : ℕ) : ℕ := (r + 2) * pairCount r + r + r * r

def tailLength (r : ℕ) : ℕ := lastTarget r + 1

def initialLength (r : ℕ) : ℕ := lastTarget r + r - 3

def halfLength (r : ℕ) : ℕ := initialLength r + 2

def identityEnd (r : ℕ) : ℕ := initialLength r + r

def wordLength (r : ℕ) : ℕ := 2 * halfLength r

def delayedTarget (r i j : ℕ) : ℕ :=
  2 * pairCount r + r + (i - 1) * (pairCount r + r) + j

/-- Lexicographic enumeration of all pairs, before deleting any graph triggers. -/
def pairList (r : ℕ) : List (Fin r × Fin r) :=
  (((univ ×ˢ univ : Finset (Fin r × Fin r)).filter (fun e => e.1 < e.2)).image
    toLex).sort (· ≤ ·) |>.map ofLex

def edgeAt (r j : ℕ) : Option (Fin r × Fin r) := (pairList r)[j - 1]?

/-- Only the early trigger is removed when an edge is absent. -/
def Retained (r : ℕ) (G : SimpleGraph (Fin r)) (j i : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ pairCount r ∧ ∃ u v, edgeAt r j = some (u, v) ∧
    G.Adj u v ∧ (i = u.val + 1 ∨ i = v.val + 1)

/-- A marker prefix is represented by its one-positions, never supplied to the encoder. -/
def IsPrefix (c : ℕ) (w : Finset ℕ) : Prop := w ⊆ Icc 1 c

def identities (r : ℕ) (w : Finset ℕ) : Finset ℕ :=
  (Icc 1 r).filter (fun i => initialLength r + i ∈ w)

/-- This test inspects only positions through the specified first tail one. -/
def FirstTailOne (r : ℕ) (w : Finset ℕ) (j : ℕ) : Prop :=
  1 ≤ j ∧ identityEnd r + j ∈ w ∧
    ∀ k, 1 ≤ k → k < j → identityEnd r + k ∉ w

/-- The local decision of the full schedule, including rejected words.
The current count guards every branch; a delayed target ignores later marker values. -/
def Trigger (r : ℕ) (G : SimpleGraph (Fin r)) (c : ℕ) (w : Finset ℕ) : Prop :=
  (1 ≤ c ∧ c ≤ initialLength r ∧ c ∉ w) ∨
  (c = identityEnd r ∧ identities r w = ∅) ∨
  (∃ t u v, 1 ≤ t ∧ t ≤ pairCount r ∧ edgeAt r t = some (u, v) ∧
    ((identities r w).sort (· ≤ ·)).take 2 = [u.val + 1, v.val + 1] ∧
    c = identityEnd r + pairCount r + r + t) ∨
  (∃ i, 1 ≤ i ∧ i ≤ r ∧ identities r w = {i} ∧
    ((∃ j, FirstTailOne r w j ∧ j ≤ pairCount r + i ∧
      identityEnd r + j ≤ c ∧
      ((Retained r G j i ∧ c = identityEnd r + j) ∨
        (¬ Retained r G j i ∧ c = identityEnd r + delayedTarget r i j))) ∨
    (c = identityEnd r + pairCount r + i ∧
      ∀ k, 1 ≤ k → k ≤ pairCount r + i → identityEnd r + k ∉ w)))

/-- The first trigger latches once; all subsequent markers still belong to the source. -/
def FirstSelected (r : ℕ) (G : SimpleGraph (Fin r)) (c : ℕ) (w : Finset ℕ) : Prop :=
  Trigger r G c w ∧ ∀ d, d < c → ¬ Trigger r G d w

/-- Total finite-prefix bookmark query, with no promise on an unfinished raw history. -/
def bookmark (r : ℕ) (G : SimpleGraph (Fin r)) (c : ℕ) (w : Finset ℕ) : Option ℕ :=
  (List.range (c + 1)).find? (fun d => decide (Trigger r G d w))

/-- The original two repeated halves, including 0^0 = 1. -/
def coefficient (r : ℕ) (rho : Bool) (k : ℕ) : ZMod 2 :=
  (if rho then 1 else 0) ^ ((k - 1) % halfLength r)

def initialSyndrome (r : ℕ) (rho : Bool) : ZMod 2 :=
  ∑ k ∈ Icc 1 (halfLength r), coefficient r rho k

def syndrome (r : ℕ) (rho : Bool) (w : Finset ℕ) : ZMod 2 :=
  initialSyndrome r rho + ∑ k ∈ w, coefficient r rho k

structure BareAddress where
  count : ℕ
  weight : ℕ
  syndrome : ZMod 2
  deriving DecidableEq

def bareAddress (r : ℕ) (rho : Bool) (c : ℕ) (w : Finset ℕ) : BareAddress :=
  ⟨c, w.card, syndrome r rho w⟩

/-- No completion-count or acceptance pruning occurs in the selected dictionary. -/
def selectedFiber (r : ℕ) (G : SimpleGraph (Fin r)) (rho : Bool)
    (b : BareAddress) : Finset (Finset ℕ) :=
  ((Icc 1 b.count).powerset).filter (fun w =>
    FirstSelected r G b.count w ∧ w.card = b.weight ∧ syndrome r rho w = b.syndrome)

def colexRank (s : Finset (Finset ℕ)) (w : Finset ℕ) : ℕ :=
  (s.filter (fun v => toColex v < toColex w)).card

/-- The count distinguishes an all-zero prefix from the empty-word default. -/
def markerWord (c : ℕ) (w : Finset ℕ) : List Bool :=
  (List.range c).map (fun k => decide (k + 1 ∈ w))

/-- All natural-number codes are retained; out-of-range codes use the empty word. -/
def colexDecode (c : ℕ) (s : Finset (Finset ℕ)) (z : ℕ) : List Bool :=
  match ((s.image toColex).sort (· ≤ ·))[z]? with
  | some w => markerWord c (ofColex w)
  | none => []

/-- The word p_i 0^(j-1)1, as literal occupied marker positions. -/
def edgePrefix (r i j : ℕ) : Finset ℕ :=
  insert (identityEnd r + j) (insert (initialLength r + i) (Icc 1 (initialLength r)))

private theorem retained_bounds {r j i : ℕ} {G : SimpleGraph (Fin r)}
    (h : Retained r G j i) : 1 ≤ i ∧ i ≤ r := by
  obtain ⟨_, _, u, v, _, _, h | h⟩ := h
  · have := u.isLt
    omega
  · have := v.isLt
    omega

private theorem trigger_early {r j : ℕ} {G : SimpleGraph (Fin r)}
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (w : Finset ℕ) :
    Trigger r G (identityEnd r + j) w ↔
      ∃ i, 1 ≤ i ∧ i ≤ r ∧ identities r w = {i} ∧
        FirstTailOne r w j ∧ Retained r G j i := by
  constructor
  · intro ht
    rcases ht with h | h | h | h
    · have := h.2.1
      dsimp [identityEnd] at this
      omega
    · omega
    · obtain ⟨t, u, v, ht, _, _, _, he⟩ := h
      omega
    · obtain ⟨i, hi, hir, hid, h | h⟩ := h
      · obtain ⟨k, hk, _, _, h | h⟩ := h
        · have hkj : k = j := by omega
          subst k
          exact ⟨i, hi, hir, hid, hk, h.1⟩
        · have he := h.2
          dsimp [delayedTarget] at he
          have := hk.1
          omega
      · omega
  · rintro ⟨i, hi, hir, hid, hf, he⟩
    exact Or.inr (Or.inr (Or.inr ⟨i, hi, hir, hid,
      Or.inl ⟨j, hf, by omega, le_rfl, Or.inl ⟨he, rfl⟩⟩⟩))

private theorem edge_prefix_identities {r i j : ℕ} (hi : 1 ≤ i) (hir : i ≤ r)
    (hj : 1 ≤ j) : identities r (edgePrefix r i j) = {i} := by
  ext k
  simp only [identities, mem_filter, mem_Icc, edgePrefix, mem_insert, mem_singleton]
  dsimp [identityEnd]
  omega

private theorem edge_prefix_first_one {r i j : ℕ} (hir : i ≤ r) (hj : 1 ≤ j) :
    FirstTailOne r (edgePrefix r i j) j := by
  refine ⟨hj, by simp [edgePrefix], ?_⟩
  intro k hk hkj
  simp only [edgePrefix, mem_insert, mem_Icc]
  dsimp [identityEnd]
  omega

private theorem edge_prefix_subset {r i j : ℕ} (hi : 1 ≤ i) (hir : i ≤ r)
    (hj : 1 ≤ j) : IsPrefix (identityEnd r + j) (edgePrefix r i j) := by
  intro k hk
  simp only [edgePrefix, mem_insert, mem_Icc] at hk ⊢
  dsimp [identityEnd] at hk ⊢
  omega

/-- Every early first selection, over the whole prefix space, has exactly one
identity one and its first tail one at the current edge position. -/
theorem early_first_selection_support {r j : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (w : Finset ℕ) (hw : IsPrefix (identityEnd r + j) w) :
    FirstSelected r G (identityEnd r + j) w ↔
      ∃ i, Retained r G j i ∧ w = edgePrefix r i j := by
  constructor
  · rintro ⟨ht, hprev⟩
    obtain ⟨i, hi, hir, hid, hf, he⟩ := (trigger_early hr hj hjQ w).mp ht
    have hbase : Icc 1 (initialLength r) ⊆ w := by
      intro k hk
      simp only [mem_Icc] at hk
      by_contra hn
      exact hprev k (by dsimp [identityEnd]; omega) (Or.inl ⟨hk.1, hk.2, hn⟩)
    refine ⟨i, he, ?_⟩
    ext k
    constructor
    · intro hk
      have hb := hw hk
      simp only [mem_Icc] at hb
      by_cases hkb : k ≤ initialLength r
      · simp [edgePrefix, mem_Icc, hb.1, hkb]
      · by_cases hkc : k ≤ identityEnd r
        · have hki : k - initialLength r ∈ identities r w := by
            simp only [identities, mem_filter, mem_Icc]
            refine ⟨?_, ?_⟩
            · dsimp [identityEnd] at hkc
              omega
            · convert hk using 1; omega
          rw [hid, mem_singleton] at hki
          have heq : k = initialLength r + i := by omega
          simp [edgePrefix, heq]
        · have hlast : k = identityEnd r + j := by
            by_contra hne
            have hzero := hf.2.2 (k - identityEnd r) (by omega) (by omega)
            apply hzero
            convert hk using 1; omega
          simp [edgePrefix, hlast]
    · intro hk
      simp only [edgePrefix, mem_insert] at hk
      rcases hk with rfl | rfl | hk
      · exact hf.2.1
      · have hmem : i ∈ identities r w := by rw [hid]; simp
        exact (mem_filter.mp hmem).2
      · exact hbase hk
  · rintro ⟨i, he, rfl⟩
    obtain ⟨hi, hir⟩ := retained_bounds he
    have hid := edge_prefix_identities hi hir hj
    have hf := edge_prefix_first_one hir hj
    refine ⟨(trigger_early hr hj hjQ _).mpr ⟨i, hi, hir, hid, hf, he⟩, ?_⟩
    intro d hd ht
    rcases ht with h | h | h | h
    · exact h.2.2 (by simp [edgePrefix, mem_Icc, h.1, h.2.1])
    · rw [hid] at h
      exact singleton_ne_empty i h.2
    · obtain ⟨t, u, v, ht, _, _, _, heq⟩ := h
      omega
    · obtain ⟨a, ha, har, hai, h | h⟩ := h
      · have hai' : a = i := by simpa [hid] using hai.symm
        subst a
        obtain ⟨k, hk, _, _, h | h⟩ := h
        · have hki : k = j := by
            have hmem := hk.2.1
            simp only [edgePrefix, mem_insert, mem_Icc] at hmem
            dsimp [identityEnd] at hmem
            have := hk.1
            omega
          omega
        · have heq := h.2
          dsimp [delayedTarget] at heq
          have := hk.1
          omega
      · omega


private theorem geometry {r : ℕ} (hr : 3 ≤ r) :
    1 ≤ initialLength r ∧ r + pairCount r ≤ initialLength r := by
  have hsq : 3 ≤ r * r := by nlinarith
  have hmul : pairCount r ≤ (r + 2) * pairCount r := by nlinarith
  dsimp [initialLength, lastTarget]
  omega

private theorem edge_prefix_card {r i j : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r) (hj : 1 ≤ j) :
    (edgePrefix r i j).card = halfLength r := by
  have hb : initialLength r + i ∉ Icc 1 (initialLength r) := by simp; omega
  have ht : identityEnd r + j ∉ insert (initialLength r + i)
      (Icc 1 (initialLength r)) := by
    simp only [mem_insert, mem_Icc]
    dsimp [identityEnd]
    omega
  simp [edgePrefix, card_insert_of_notMem ht, hb, halfLength, Nat.card_Icc]

private theorem coefficient_zero {r k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ 2 * halfLength r) :
    coefficient r false k = if k = 1 ∨ k = halfLength r + 1 then 1 else 0 := by
  have hl : 0 < halfLength r := by simp [halfLength]
  by_cases hfirst : k ≤ halfLength r
  · have hm : (k - 1) % halfLength r = k - 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hk1 : k = 1
    · simp [coefficient, hk1]
    · have hn : k - 1 ≠ 0 := by omega
      have hk2 : k ≠ halfLength r + 1 := by omega
      simp [coefficient, hm, hk1, hk2, zero_pow hn]
  · have hm : (k - 1) % halfLength r = k - 1 - halfLength r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases hk2 : k = halfLength r + 1
    · simp [coefficient, hk2]
    · have hn : k - 1 - halfLength r ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      simp [coefficient, hm, hk1, hk2, zero_pow hn]

private theorem coefficient_zero_sum {r t : ℕ} (ht : 1 ≤ t) (htl : t ≤ halfLength r) :
    (∑ k ∈ Icc 1 t, coefficient r false k) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp [coefficient]
  · intro k hk hne
    have hk' := mem_Icc.mp hk
    rw [coefficient_zero hk'.1 (by omega)]
    have hne2 : k ≠ halfLength r + 1 := by omega
    simp [hne, hne2]
  · simp [ht]

private theorem edge_prefix_syndrome {r i j : ℕ} (hr : 3 ≤ r)
    (hi : 1 ≤ i) (hir : i ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (rho : Bool) :
    syndrome r rho (edgePrefix r i j) = if rho = false ∧ i = 3 then 1 else 0 := by
  have hb := geometry hr
  have hcard := edge_prefix_card hi hir hj
  cases rho
  · have hbase := coefficient_zero_sum hb.1 (r := r) (by simp [halfLength])
    have hinit := coefficient_zero_sum (r := r) (t := halfLength r)
      (by simp [halfLength]) le_rfl
    have hid : coefficient r false (initialLength r + i) = if i = 3 then 1 else 0 := by
      rw [coefficient_zero (by omega) (by dsimp [halfLength]; omega)]
      have hn : initialLength r + i ≠ 1 := by omega
      have heq : (initialLength r + i = halfLength r + 1) ↔ i = 3 := by
        dsimp [halfLength]; omega
      simp only [hn, false_or, heq]
    have htail : coefficient r false (identityEnd r + j) = 0 := by
      rw [coefficient_zero (by dsimp [identityEnd]; omega)
        (by dsimp [identityEnd, halfLength]; omega)]
      have hn1 : identityEnd r + j ≠ 1 := by dsimp [identityEnd]; omega
      have hn2 : identityEnd r + j ≠ halfLength r + 1 := by
        dsimp [identityEnd, halfLength]; omega
      simp [hn1, hn2]
    have hbi : initialLength r + i ∉ Icc 1 (initialLength r) := by simp; omega
    have hti : identityEnd r + j ∉ insert (initialLength r + i)
        (Icc 1 (initialLength r)) := by
      simp only [mem_insert, mem_Icc]; dsimp [identityEnd]; omega
    simp only [syndrome, initialSyndrome, edgePrefix, sum_insert hti,
      sum_insert hbi, hbase, hinit, hid, htail]
    simp only [true_and]
    by_cases hi3 : i = 3
    · simp only [hi3, ↓reduceIte]; decide
    · simp only [hi3, ↓reduceIte]; decide
  · simp only [syndrome, initialSyndrome, coefficient, Bool.true_eq,
      ↓reduceIte, one_pow, sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Icc, Nat.add_sub_cancel, hcard]
    exact CharTwo.add_self_eq_zero _

/-- The actual target address has zero syndrome for both acquired seeds. -/
def earlyAddress (r j : ℕ) : BareAddress := ⟨identityEnd r + j, halfLength r, 0⟩

/-- Both endpoint identities, with identity 3 removed exactly for seed zero. -/
def retainedIdentities (r : ℕ) (G : SimpleGraph (Fin r)) (rho : Bool) (j : ℕ) :
    Finset ℕ := (Icc 1 r).filter (fun i => Retained r G j i ∧ (rho = true ∨ i ≠ 3))

/-- The whole first-selected fibre at the original bare address, for either seed. -/
theorem c4_selected_fiber {r j : ℕ} (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (rho : Bool) :
    selectedFiber r G rho (earlyAddress r j) =
      (retainedIdentities r G rho j).image (edgePrefix r · j) := by
  ext w
  change (w ∈ ((Icc 1 (identityEnd r + j)).powerset).filter
    (fun w => FirstSelected r G (identityEnd r + j) w ∧
      w.card = halfLength r ∧ syndrome r rho w = 0)) ↔ _
  simp only [mem_filter, mem_powerset, mem_image]
  constructor
  · rintro ⟨hw, hf, _, hs⟩
    obtain ⟨i, he, rfl⟩ := (early_first_selection_support G hr hj hjQ w hw).mp hf
    obtain ⟨hi, hir⟩ := retained_bounds he
    have hsyn := edge_prefix_syndrome hr hi hir hj hjQ rho
    have hallowed : rho = true ∨ i ≠ 3 := by
      rw [hs] at hsyn
      cases rho
      · right
        intro hi3
        have hbad : (0 : ZMod 2) = 1 := by simpa only [hi3, and_self, ↓reduceIte] using hsyn
        exact zero_ne_one hbad
      · exact Or.inl rfl
    exact ⟨i, mem_filter.mpr ⟨mem_Icc.mpr ⟨hi, hir⟩, he, hallowed⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hib, he, ha⟩ := mem_filter.mp hi
    obtain ⟨hi1, hir⟩ := mem_Icc.mp hib
    have hw := edge_prefix_subset hi1 hir hj
    refine ⟨hw, (early_first_selection_support G hr hj hjQ _ hw).mpr ⟨i, he, rfl⟩,
      edge_prefix_card hi1 hir hj, ?_⟩
    rw [edge_prefix_syndrome hr hi1 hir hj hjQ rho]
    cases rho
    · have hi3 : i ≠ 3 := ha.resolve_left (by decide)
      simp only [hi3, and_false, ↓reduceIte]
    · simp only [Bool.true_eq_false, false_and, ↓reduceIte]

private theorem edge_prefix_colex {r i t j : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r) (ht : 1 ≤ t) (htr : t ≤ r) (hj : 1 ≤ j) :
    toColex (edgePrefix r i j) < toColex (edgePrefix r t j) ↔ i < t := by
  have hni : initialLength r + i ∉ insert (identityEnd r + j)
      (Icc 1 (initialLength r)) := by
    simp only [mem_insert, mem_Icc]; dsimp [identityEnd]; omega
  have hnt : initialLength r + t ∉ insert (identityEnd r + j)
      (Icc 1 (initialLength r)) := by
    simp only [mem_insert, mem_Icc]; dsimp [identityEnd]; omega
  simp only [edgePrefix, insert_comm (identityEnd r + j),
    Finset.Colex.insert_lt_insert hni hnt, Nat.add_lt_add_iff_left]

/-- Colex is recomputed inside the surviving fibre, including the seed-zero deletion. -/
theorem c4_colex_rank {r j i : ℕ} (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (rho : Bool)
    (hi : 1 ≤ i) (hir : i ≤ r) :
    colexRank (selectedFiber r G rho (earlyAddress r j)) (edgePrefix r i j) =
      ((retainedIdentities r G rho j).filter (· < i)).card := by
  rw [c4_selected_fiber G hr hj hjQ rho, colexRank, Finset.filter_image]
  have hfilter :
      (retainedIdentities r G rho j).filter
        (fun a => toColex (edgePrefix r a j) < toColex (edgePrefix r i j)) =
      (retainedIdentities r G rho j).filter (· < i) := by
    ext a
    simp only [mem_filter]
    apply and_congr_right
    intro ha
    have hab := mem_Icc.mp (mem_filter.mp ha).1
    exact edge_prefix_colex hab.1 hab.2 hi hir hj
  rw [hfilter]
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have hab := mem_Icc.mp (mem_filter.mp (mem_filter.mp ha).1).1
  have hbb := mem_Icc.mp (mem_filter.mp (mem_filter.mp hb).1).1
  have hid := congrArg (identities r) heq
  simpa only [edge_prefix_identities hab.1 hab.2 hj,
    edge_prefix_identities hbb.1 hbb.2 hj, singleton_inj] using hid

/-- The enumerated endpoints are all and only the surviving identities. -/
private theorem retained_identities_pair {r j : ℕ} (G : SimpleGraph (Fin r))
    (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (rho : Bool)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v) :
    retainedIdentities r G rho j =
      ({u.val + 1, v.val + 1} : Finset ℕ).filter (fun i => rho = true ∨ i ≠ 3) := by
  ext i
  have hu := u.isLt
  have hv := v.isLt
  simp only [retainedIdentities, mem_filter, mem_Icc, Retained, hj, hjQ,
    he, Option.some.injEq, Prod.mk.injEq, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨_, ⟨a, b,⟨rfl,rfl⟩,_,hi⟩,ha⟩
    exact ⟨hi, ha⟩
  · rintro ⟨hi, ha⟩
    refine ⟨?_, ⟨u, v,⟨rfl,rfl⟩,hG,hi⟩,ha⟩
    rcases hi with rfl | rfl <;> omega

/-- The complete edge fibre and its recomputed canonical integer ranks for both seeds. -/
theorem c4_edge_fiber_and_ranks {r j : ℕ} (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (rho : Bool)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v) :
    let ids := ({u.val + 1, v.val + 1} : Finset ℕ).filter (fun i => rho = true ∨ i ≠ 3)
    selectedFiber r G rho (earlyAddress r j) = ids.image (edgePrefix r · j) ∧
      ∀ i ∈ ids, colexRank (selectedFiber r G rho (earlyAddress r j)) (edgePrefix r i j) =
        (ids.filter (· < i)).card := by
  dsimp only
  have hid := retained_identities_pair G hj hjQ rho u v he hG
  refine ⟨by rw [c4_selected_fiber G hr hj hjQ rho, hid], ?_⟩
  intro i hi
  have hb := mem_Icc.mp (mem_filter.mp (hid.symm ▸ hi)).1
  rw [c4_colex_rank G hr hj hjQ rho hb.1 hb.2, hid]

/-! The source port supplies actual parser completions. Seed acquisition, paid
restoration and retries remain source-owned; no conditional sampling operation
is included in this interface. -/

open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
  (Letter ActivePhase Parses pWord parses_normal_form)

/-- Evidence that a raw segment is completed by the original parser. -/
structure CompletedMarker where
  raw : List Letter
  bit : Letter
  parsed : Parses (.active .p) raw bit

/-- The existing parser theorem supplies all and only the original segment language. -/
def completedMarker (returns : ℕ) (b : Letter) : CompletedMarker :=
  ⟨pWord returns b, b, (parses_normal_form .p _ b).mpr ⟨returns, rfl⟩⟩

/-- Source-owned observation events; only completed markers update the observer. -/
inductive SourceEvent where
  | hold
  | acquired (rho : Bool)
  | marker (completed : CompletedMarker)
  | stop (last : Bool)

/-- A mathematical projection of an actual raw execution. The source owns paid
seed acquisition, rejected pairs, return segments and
unfinished phases. These are projected to holds; the port does not implement
their probability law. It does
not supply a prefix, selector control or acceptance bit to a register. -/
structure SourceContract (History : Type) (r : ℕ) where
  legal : List SourceEvent → Prop
  projection : History → List SourceEvent
  actual_legal : ∀ h, legal (projection h)
  prefix_closed : ∀ xs ys, legal (xs ++ ys) → legal xs
  fixed_seed : ∀ xs ys a b,
    legal (xs ++ [.acquired a] ++ ys ++ [.acquired b]) → False
  markers_acquired : ∀ xs c,
    legal (xs ++ [.marker c]) → ∃ ys zs rho, xs = ys ++ [.acquired rho] ++ zs
  stop_terminal : ∀ xs b ys, legal (xs ++ [.stop b] ++ ys) → ys = []
  marker_bound : ∀ xs, legal xs →
    (xs.filter (fun e => match e with | .marker _ => true | _ => false)).length ≤ wordLength r
  stop_value : ∀ xs b, legal (xs ++ [.stop b]) →
    ∃ ys c, xs = ys ++ [.marker c] ∧ b = decide (c.bit = 1)
  stopped_count : ∀ xs b, legal (xs ++ [.stop b]) →
    (xs.filter (fun e => match e with | .marker _ => true | _ => false)).length = wordLength r
  zero_return_support : ∀ rho (bits : List Letter), bits.length = wordLength r →
    (∃ h, projection h = [.acquired rho] ++
      bits.map (fun b => .marker (completedMarker 0 b)) ++
      [.stop (decide (bits.getLastD 0 = 1))])

/-- Current completed-marker transactions carry only the allowed synchronous fields. -/
structure MarkerInput where
  seed : Bool
  old : BareAddress
  new : BareAddress
  bit : Bool
  phase : ActivePhase

/-- No current decision or selector state is an argument of a pre-decision update. -/
structure PreProgram (Z : Type) where
  initial : Z
  update : MarkerInput → Z → Z

/-- The Boolean argument is the actual current first-freeze event, with no identity. -/
structure BlindProgram (Z : Type) where
  initial : Z
  update : MarkerInput → Bool → Z → Z

/-- Read programs additionally inspect the separately paid selector control. -/
structure ReadProgram (Control Z : Type) where
  initial : Z
  update : MarkerInput → Control → Bool → Z → Z

/-- The single register and original frozen fields share the same first latch. -/
structure LatchedRegister (Z : Type) where
  value : Z
  snapshot : Option BareAddress

def writeThenLatch {Z : Type} (s : LatchedRegister Z) (b : BareAddress)
    (freeze : Bool) (value : Z) : LatchedRegister Z :=
  if s.snapshot.isSome then s else
    ⟨value, if freeze then some b else none⟩

def atCut (w : Finset ℕ) (c : ℕ) : Finset ℕ := w.filter (· ≤ c)

def markerInput (r : ℕ) (rho : Bool) (w : Finset ℕ) (c : ℕ) : MarkerInput :=
  ⟨rho, bareAddress r rho c (atCut w c),
    bareAddress r rho (c + 1) (atCut w (c + 1)), decide (c + 1 ∈ w), .p⟩

/-- This semantic execution retains no extra private register. The marker prefix
is used only to define the actual source input and separately paid selector. -/
def runBlind {Z : Type} (r : ℕ) (G : SimpleGraph (Fin r))
    (P : BlindProgram Z) (rho : Bool) (w : Finset ℕ) : ℕ → LatchedRegister Z
  | 0 => ⟨P.initial, none⟩
  | c + 1 =>
    let s := runBlind r G P rho w c
    let input := markerInput r rho w c
    let freeze := decide (FirstSelected r G (c + 1) (atCut w (c + 1)))
    writeThenLatch s input.new freeze (P.update input freeze s.value)

def asBlind {Z : Type} (P : PreProgram Z) : BlindProgram Z :=
  ⟨P.initial, fun input _ z => P.update input z⟩

/-- Marker projection of the recovery domain. Actual zero-return support and the
positive source law are separate obligations of the source port. -/
def Accepted (r : ℕ) (rho : Bool) (w : Finset ℕ) : Prop :=
  IsPrefix (wordLength r) w ∧ w.card = halfLength r ∧ syndrome r rho w = 0

/-- Terminal dictionaries retain the actual last-marker Stop block. -/
def stopBlock (r : ℕ) (G : SimpleGraph (Fin r)) (rho stop : Bool) : Finset (Finset ℕ) :=
  (selectedFiber r G rho ⟨wordLength r, halfLength r, 0⟩).filter
    (fun w => decide (wordLength r ∈ w) = stop)

/-- The original interface validity check is a supplied fixed contract, never
replaced by acceptance or positive completion count. Suffix and Stop are supplied
actual receiver inputs; the nonterminal dictionary does not refine by either. -/
structure ReceiverInput where
  seed : Bool
  address : BareAddress
  code : ℕ
  suffix : List Bool
  stop : Bool

def totalDecoder (r : ℕ) (G : SimpleGraph (Fin r))
    (originalValid : ReceiverInput → Prop) (input : ReceiverInput) : List Bool :=
  if originalValid input then
    if input.address.count < wordLength r then
      colexDecode input.address.count (selectedFiber r G input.seed input.address) input.code
    else if input.address = ⟨wordLength r, halfLength r, 0⟩ then
      colexDecode (wordLength r) (stopBlock r G input.seed input.stop) input.code
    else []
  else []

/-- Marker-level canonical-output correctness on one initialized selector and word.
Lifting this predicate to the raw source requires the source projection contract. -/
def CorrectBlind (r : ℕ) (G : SimpleGraph (Fin r)) (D : ℕ)
    (P : BlindProgram (Fin D)) : Prop :=
  ∀ rho w, Accepted r rho w → ∀ c, c ≤ wordLength r →
    FirstSelected r G c (atCut w c) →
    let b := bareAddress r rho c (atCut w c)
    (runBlind r G P rho w c).snapshot = some b ∧
    ((runBlind r G P rho w c).value : ℕ) =
      colexRank (if c < wordLength r then selectedFiber r G rho b
        else stopBlock r G rho (decide (wordLength r ∈ w))) (atCut w c)

/-- Capacity of the marker-level semantic model. -/
def blindCapacity (r : ℕ) (G : SimpleGraph (Fin r)) : ℕ∞ :=
  ⨅ D : {D : ℕ // ∃ P : BlindProgram (Fin D), CorrectBlind r G D P}, (D.val : ℕ∞)

def preCapacity (r : ℕ) (G : SimpleGraph (Fin r)) : ℕ∞ :=
  ⨅ D : {D : ℕ // ∃ P : PreProgram (Fin D), CorrectBlind r G D (asBlind P)}, (D.val : ℕ∞)

/-- A color-to-rank update uses no decision event. At a nonendpoint first tail
one its provisional rank can be nonzero; every subsequent marker clears it
because the old weight has left the one-hot waiting level. -/
def coloringPreProgram {r D : ℕ} (G : SimpleGraph (Fin r))
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) : PreProgram (Fin D) where
  initial := ⟨0, by omega⟩
  update input z :=
    let zero : Fin D := ⟨0, by omega⟩
    let one : Fin D := ⟨1, by omega⟩
    if input.phase ≠ .p ∨ input.new.count ≠ input.old.count + 1 ∨
        input.new.weight ≠ input.old.weight + (if input.bit then 1 else 0) ∨
        input.new.syndrome ≠ input.old.syndrome +
          (if input.bit then coefficient r input.seed input.new.count else 0) then zero
    else if input.new.count ≤ initialLength r then zero
    else if input.new.count ≤ identityEnd r then
      if input.bit then
        if input.old.weight = initialLength r then
          if h : input.new.count - initialLength r - 1 < r then
            color ⟨input.new.count - initialLength r - 1, h⟩ else zero
        else zero
      else z
    else if input.old.weight ≠ halfLength r - 1 then zero
    else if input.bit then
      match edgeAt r (input.new.count - identityEnd r) with
      | none => zero
      | some (u, v) =>
        if G.Adj u v ∧ (input.seed = true ∨ (u.val + 1 ≠ 3 ∧ v.val + 1 ≠ 3)) ∧
            z = color v then one else zero
    else if pairCount r < input.new.count - identityEnd r then zero else z

end D5.S3.ObserverMemory.Trajectories.GraphScheduledSelection
