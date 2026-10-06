/- GID: D5/S3/Combinatorics/PatternMatchings/P13Completions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Completions
   mirror-E: none(waiver:literal-continuation-decompositions)
   anchors: []
   utility: none
   digest: Literal accepted continuations have finite support and forced closure decompositions. -/

import D5.S3.Combinatorics.PatternMatchings.P13Correspondence
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

/-- Number of future closure vertices in a literal word. -/
def closingCount : List Step → ℕ
  | [] => 0
  | .opening :: w => closingCount w
  | .closing _ :: w => closingCount w + 1

/-- Number of future opening vertices in a literal word. -/
def openingCount : List Step → ℕ
  | [] => 0
  | .opening :: w => openingCount w + 1
  | .closing _ :: w => openingCount w

theorem vertex_count (w : List Step) :
    w.length = openingCount w + closingCount w := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp only [List.length_cons, openingCount, closingCount] <;> omega

/-- Every accepted suffix closes exactly its old, pending and future openers. -/
theorem continuation_balance {s : Base} {k : ℕ} {w : List Step}
    (h : AcceptFrom s k w) : s.size + k + openingCount w = closingCount w := by
  induction w generalizing s k with
  | nil => simp only [AcceptFrom] at h; simp only [openingCount, closingCount]; omega
  | cons x w ih =>
    cases x with
    | opening => have hh := ih h; simp only [openingCount, closingCount]; omega
    | closing r =>
      obtain ⟨hr, hw⟩ := h
      have hb := (blocks_spec r (s.size + k - r - 1)).1
      have hs : (afterClose s k r).size + 1 = s.size + k := by
        change (blocks r (s.size + k - r - 1)).size + 1 = _
        have hh := hr.1
        omega
      have hh := ih hw
      simp only [openingCount, closingCount]
      omega

/-- All closing ranks are bounded by the number of closures in the suffix. -/
theorem continuation_rank_bound {s : Base} {k : ℕ} {w : List Step}
    (h : AcceptFrom s k w) : ∀ r, .closing r ∈ w → r < closingCount w := by
  induction w generalizing s k with
  | nil => simp
  | cons x w ih =>
    cases x with
    | opening =>
      intro r hr
      have hm : .closing r ∈ w := by simpa using hr
      exact ih h r hm
    | closing q =>
      obtain ⟨hq, hw⟩ := h
      intro r hr
      rcases List.mem_cons.mp hr with he | hm
      · cases he
        have hb := continuation_balance (show AcceptFrom s k (.closing q :: w) from ⟨hq, hw⟩)
        have hh := hq.1
        omega
      · have hh := ih hw r hm
        simp only [closingCount]
        omega

/-- A completion has zero pending openings initially and no unfinished endpoint finally. -/
def Completion (s : Base) (d : ℕ) :=
  {w : List Step // AcceptFrom s 0 w ∧ closingCount w = d}

/-- Support, opening count, length and rank bounds are consequences of acceptance. -/
theorem completion_bounds {s : Base} {d : ℕ} (w : Completion s d) :
    s.size ≤ d ∧ openingCount w.1 = d - s.size ∧
    w.1.length = 2 * d - s.size ∧ ∀ r, .closing r ∈ w.1 → r < d := by
  have hb := continuation_balance w.2.1
  have hv := vertex_count w.1
  have hc := w.2.2
  refine ⟨by omega, by omega, by omega, ?_⟩
  simpa only [w.2.2] using continuation_rank_bound w.2.1

private def completionCode {s : Base} {d : ℕ} (w : Completion s d) :
    Fin (2 * d - s.size) → Option (Fin d) := fun i =>
  let x := w.1[i.val]'(by have := (completion_bounds w).2.2.1; omega)
  match hx : x with
  | .opening => none
  | .closing r => some ⟨r, (completion_bounds w).2.2.2 r (by
      have hm := List.getElem_mem (l := w.1) (n := i.val)
        (by have := (completion_bounds w).2.2.1; omega)
      simpa only [← hx] using hm)⟩

private theorem completionCode_injective (s : Base) (d : ℕ) :
    Function.Injective (@completionCode s d) := by
  intro v w h
  apply Subtype.ext
  apply List.ext_getElem
  · have hv := (completion_bounds v).2.2.1
    have hw := (completion_bounds w).2.2.1
    omega
  · intro i hi hj
    have hb : i < 2 * d - s.size := by have := (completion_bounds v).2.2.1; omega
    have he := congrFun h ⟨i, hb⟩
    dsimp only [completionCode] at he
    split at he <;> split at he <;>
      simp_all only [Option.some.injEq, reduceCtorEq, Fin.mk.injEq]


/-- Literal completions are finite, before their cardinalities are used. -/
instance completion_finite (s : Base) (d : ℕ) : Finite (Completion s d) :=
  Finite.of_injective _ (completionCode_injective s d)

/-- Concrete single-block continuation count. -/
noncomputable def c (m d : ℕ) : ℕ := Nat.card (Completion (.S m) d)

/-- Concrete normalized two-block continuation count. -/
noncomputable def g (a b d : ℕ) : ℕ := Nat.card (Completion (blocks a b) d)

/-- States with more old survivors than future closures have no completions. -/
theorem completion_count_zero {s : Base} {d : ℕ} (h : d < s.size) :
    Nat.card (Completion s d) = 0 := by
  have : IsEmpty (Completion s d) := ⟨fun w => by have := (completion_bounds w).1; omega⟩
  simp

/-- A single block cannot be completed with too few closures. -/
theorem c_support {m d : ℕ} (h : d < m) : c m d = 0 :=
  completion_count_zero h

/-- A run of pending opening vertices. -/
def openingRun (k : ℕ) : List Step := List.replicate k .opening

theorem closingCount_append (v w : List Step) :
    closingCount (v ++ w) = closingCount v + closingCount w := by
  induction v with
  | nil => simp [closingCount]
  | cons x v ih =>
    cases x with
    | opening => exact ih
    | closing r =>
      change closingCount (v ++ w) + 1 = closingCount v + 1 + closingCount w
      rw [ih]
      omega

theorem openingRun_closingCount (k : ℕ) : closingCount (openingRun k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [openingRun, List.replicate_succ, closingCount] using ih

theorem accept_openingRun (s : Base) (k n : ℕ) (w : List Step) :
    AcceptFrom s k (openingRun n ++ w) ↔ AcceptFrom s (k + n) w := by
  induction n generalizing k with
  | zero => simp [openingRun]
  | succ n ih =>
    simpa only [openingRun, List.replicate_succ, List.cons_append, AcceptFrom,
      Nat.add_assoc, Nat.add_comm 1 n] using ih (k + 1)

theorem first_closure_exists {w : List Step} (h : 0 < closingCount w) :
    ∃ k r v, w = openingRun k ++ .closing r :: v := by
  induction w with
  | nil => simp [closingCount] at h
  | cons x w ih =>
    cases x with
    | closing r => exact ⟨0, r, w, rfl⟩
    | opening =>
      obtain ⟨k, r, v, hv⟩ := ih h
      refine ⟨k + 1, r, v, ?_⟩
      simpa only [openingRun, List.replicate_succ, List.cons_append]
        using congrArg (Step.opening :: ·) hv

theorem first_closure_unique (k l r q : ℕ) (v w : List Step)
    (h : openingRun k ++ .closing r :: v = openingRun l ++ .closing q :: w) :
    k = l ∧ r = q ∧ v = w := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => simpa [openingRun] using h
    | succ l => simp [openingRun, List.replicate_succ] at h
  | succ k ih =>
    cases l with
    | zero => simp [openingRun, List.replicate_succ] at h
    | succ l =>
      have hh : openingRun k ++ .closing r :: v = openingRun l ++ .closing q :: w := by
        simpa only [openingRun, List.replicate_succ, List.cons_append, List.cons.injEq,
          true_and] using h
      obtain ⟨hkl, hrq, hvw⟩ := ih l hh
      exact ⟨by omega, hrq, hvw⟩

/-- Opening multiplicities before successively forced descending closures. -/
def forcedPrefix : List ℕ → List Step
  | [] => []
  | k :: ks => openingRun k ++ .closing ks.length :: forcedPrefix ks

private theorem forcedPrefix_closingCount (ks : List ℕ) :
    closingCount (forcedPrefix ks) = ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [forcedPrefix, closingCount_append, openingRun_closingCount,
      closingCount, ih]

private theorem forced_transition (a b k : ℕ) (hb : 0 < b) :
    Permitted (blocks (a + 1) b) k a ∧
    afterClose (blocks (a + 1) b) k a = blocks a (b + k) := by
  have he : blocks (a + 1) b = .T (a + 1) b := by simp [blocks, Nat.ne_of_gt hb]
  rw [he]
  constructor
  · change a < (a + 1) + b + k ∧ a + 1 = a + 1
    exact ⟨by omega, rfl⟩
  · unfold afterClose
    congr 1
    simp only [Base.size]
    omega

/-- Every transition of the forced prefix is legal, including its last normalization. -/
theorem forcedPrefix_accept (ks : List ℕ) (b : ℕ) (hb : 0 < b) (w : List Step) :
    AcceptFrom (blocks ks.length b) 0 (forcedPrefix ks ++ w) ↔
      AcceptFrom (.S (b + ks.sum)) 0 w := by
  induction ks generalizing b with
  | nil => simp [forcedPrefix, blocks]
  | cons k ks ih =>
    simp only [forcedPrefix, List.append_assoc, List.cons_append, List.length_cons]
    rw [accept_openingRun]
    simp only [Nat.zero_add, AcceptFrom]
    obtain ⟨hp, he⟩ := forced_transition ks.length b k hb
    rw [he, and_iff_right hp, ih (b + k) (by omega)]
    simp only [List.sum_cons, Nat.add_assoc]

private theorem forcedPrefix_unique (ks ls : List ℕ) (v w : List Step)
    (hl : ks.length = ls.length)
    (h : forcedPrefix ks ++ v = forcedPrefix ls ++ w) : ks = ls ∧ v = w := by
  induction ks generalizing ls with
  | nil =>
    have he : ls = [] := List.length_eq_zero_iff.mp hl.symm
    subst ls
    exact ⟨rfl, h⟩
  | cons k ks ih =>
    cases ls with
    | nil => simp at hl
    | cons l ls =>
      have hlen : ks.length = ls.length := by simpa using hl
      have hh := first_closure_unique k l ks.length ls.length
        (forcedPrefix ks ++ v) (forcedPrefix ls ++ w) (by
          simpa only [forcedPrefix, List.append_assoc, List.cons_append] using h)
      obtain ⟨hks, hvw⟩ := ih ls hlen hh.2.2
      exact ⟨by rw [hh.1, hks], hvw⟩

/-- Every accepted two-block suffix exhausts the first block in a unique forced prefix. -/
theorem forcedPrefix_exhaustive (a b : ℕ) (hb : 0 < b) (w : List Step)
    (hw : AcceptFrom (blocks a b) 0 w) :
    ∃ ks v, ks.length = a ∧ w = forcedPrefix ks ++ v ∧
      AcceptFrom (.S (b + ks.sum)) 0 v := by
  induction a generalizing b w with
  | zero => exact ⟨[], w, rfl, rfl, by simpa [blocks] using hw⟩
  | succ a ih =>
    have hpos : 0 < closingCount w := by
      have hs := (blocks_spec (a + 1) b).1
      have hbal := continuation_balance hw
      omega
    obtain ⟨k, r, v, rfl⟩ := first_closure_exists hpos
    have hh := (accept_openingRun (blocks (a + 1) b) 0 k (.closing r :: v)).mp hw
    simp only [Nat.zero_add, AcceptFrom] at hh
    have hr : r = a := by
      have he : blocks (a + 1) b = .T (a + 1) b := by simp [blocks, Nat.ne_of_gt hb]
      have hp := hh.1
      rw [he] at hp
      simp only [Permitted] at hp
      omega
    subst r
    have ht := (forced_transition a b k hb).2
    rw [ht] at hh
    obtain ⟨ks, v', hlen, hv, ha⟩ := ih (b + k) (by omega) v hh.2
    refine ⟨k :: ks, v', by simp [hlen], ?_, ?_⟩
    · simp only [forcedPrefix, hlen, List.append_assoc, List.cons_append]; rw [← hv]
    · simpa only [List.sum_cons, Nat.add_assoc] using ha

/-- A weak composition records the number of openings before each forced closure. -/
def OpeningMultiplicities (a t : ℕ) := {f : Fin a → ℕ // ∑ i, f i = t}

private noncomputable def multiplicitiesEquiv (a t : ℕ) :
    Sym (Fin a) t ≃ OpeningMultiplicities a t := Sym.equivNatSumOfFintype (Fin a) t

private instance multiplicities_finite (a t : ℕ) : Finite (OpeningMultiplicities a t) :=
  Finite.of_equiv _ (multiplicitiesEquiv a t)

/-- Finite forced-prefix data, with an actual accepted single-block suffix. -/
def ForcedData (a b d : ℕ) :=
  Σ t : Fin (d + 1), OpeningMultiplicities a t.val × Completion (.S (b + t.val)) (d - a)

private def forceCompletion (a b d : ℕ) (hb : 0 < b) (x : ForcedData a b d) :
    Completion (blocks a b) d := by
  let ks := List.ofFn x.2.1.1
  have hl : ks.length = a := List.length_ofFn
  have ht : ks.sum = x.1.val := by simpa only [ks, List.sum_ofFn] using x.2.1.2
  have hs := (completion_bounds x.2.2).1
  change b + x.1.val ≤ d - a at hs
  have hd : a ≤ d := by omega
  refine ⟨forcedPrefix ks ++ x.2.2.1, ?_, ?_⟩
  · have hw : AcceptFrom (.S (b + ks.sum)) 0 x.2.2.1 := by
      simpa only [ht] using x.2.2.2.1
    simpa only [hl] using (forcedPrefix_accept ks b hb _).mpr hw
  · rw [closingCount_append, forcedPrefix_closingCount, hl, x.2.2.2.2]
    omega

private theorem forceCompletion_injective (a b d : ℕ) (hb : 0 < b) :
    Function.Injective (forceCompletion a b d hb) := by
  rintro ⟨t, f, v⟩ ⟨u, h, w⟩ he
  have hvw := congrArg Subtype.val he
  change forcedPrefix (List.ofFn f.1) ++ v.1 = forcedPrefix (List.ofFn h.1) ++ w.1 at hvw
  obtain ⟨hfh, htail⟩ := forcedPrefix_unique _ _ _ _
    (by simp only [List.length_ofFn]) hvw
  have hsum := congrArg List.sum hfh
  simp only [List.sum_ofFn, f.2, h.2] at hsum
  have htu : t = u := Fin.ext hsum
  subst u
  have hff : f = h := Subtype.ext (List.ofFn_injective hfh)
  subst h
  have hv : v = w := Subtype.ext htail
  subst w
  rfl

private theorem forceCompletion_surjective (a b d : ℕ) (hb : 0 < b) :
    Function.Surjective (forceCompletion a b d hb) := by
  intro w
  obtain ⟨ks, v, hl, hw, hv⟩ := forcedPrefix_exhaustive a b hb w.1 w.2.1
  have hc : closingCount v = d - a := by
    have hh := w.2.2
    rw [hw, closingCount_append, forcedPrefix_closingCount, hl] at hh
    omega
  have hs := continuation_balance hv
  change b + ks.sum + 0 + openingCount v = closingCount v at hs
  have ht : ks.sum < d + 1 := by omega
  let f : Fin a → ℕ := fun i => ks[i.val]'(by omega)
  have hf : List.ofFn f = ks := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hl.symm
    · intro i hi hj; simp only [List.getElem_ofFn, f]
  have hsum : ∑ i, f i = ks.sum := by rw [← hf, List.sum_ofFn]
  refine ⟨⟨⟨ks.sum, ht⟩, ⟨f, hsum⟩, ⟨v, hv, hc⟩⟩, ?_⟩
  apply Subtype.ext
  change forcedPrefix (List.ofFn f) ++ v = w.1
  rw [hf, ← hw]

/-- Exhaustive bijection of literal words: opening multiplicities, then a concrete suffix.
No lower-bound hypothesis on d is needed; malformed short prefixes have empty data. -/
noncomputable def forcedCompletionEquiv (a b d : ℕ) (hb : 0 < b) :
    ForcedData a b d ≃ Completion (blocks a b) d :=
  Equiv.ofBijective (forceCompletion a b d hb)
    ⟨forceCompletion_injective a b d hb, forceCompletion_surjective a b d hb⟩

/-- The finite-degree two-block count, including d<a where both sides vanish. -/
theorem g_forced_sum (a b d : ℕ) (hb : 0 < b) :
    g a b d = ∑ t ∈ Finset.range (d + 1), (a + t - 1).choose t * c (b + t) (d - a) := by
  unfold g
  rw [← Nat.card_congr (forcedCompletionEquiv a b d hb)]
  unfold ForcedData
  rw [Nat.card_sigma]
  simp only [Nat.card_prod, c, ← Nat.card_congr (multiplicitiesEquiv a _),
    Sym.natCard_sym_eq_choose, Nat.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun t => (a + t - 1).choose t * c (b + t) (d - a)) (d + 1)

end D5.S3.Combinatorics.PatternMatchings.P13
