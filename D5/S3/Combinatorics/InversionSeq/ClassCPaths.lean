/- GID: D5/S3/Combinatorics/InversionSeq/ClassCPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/ClassCPaths
   mirror-E: none(waiver:finite-labelled-native-continuation-equivalence)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Finite labelled continuation paths correspond to actual native prefix extensions. -/

import D5.S3.Combinatorics.InversionSeq.ClassCSites
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.ClassCPaths

open D5.S3.Combinatorics Nonnesting ClassCSites

/-- Positions label choices even when several choices have equal children. -/
def Path : ℕ → State → Type
  | 0, _ => Unit
  | r + 1, q => (c : StateChoice q) × Path r (child q c)

instance path_finite (r : ℕ) (q : State) : Finite (Path r q) := by
  induction r generalizing q with
  | zero => change Finite Unit; infer_instance
  | succ r ih =>
    change Finite ((c : StateChoice q) × Path r (child q c))
    letI : Fintype (StateChoice q) := inferInstance
    letI : ∀ c : StateChoice q, Finite (Path r (child q c)) := fun c => ih (child q c)
    letI : ∀ c : StateChoice q, Fintype (Path r (child q c)) := fun _ => Fintype.ofFinite _
    exact Finite.of_fintype _

noncomputable def phi (r : ℕ) (q : State) : ℕ := Nat.card (Path r q)

noncomputable def b (r s : ℕ) (hs : 1 ≤ s) : ℕ := phi r (repeatState s hs)

/-- An extension is an actual suffix with native inversion bounds and native avoidance. -/
def Extensions (q : Prefix) (r : ℕ) :=
  {u : List ℕ // u.length = r ∧
    q.word ++ u ∈ InversionSeqDefs.avoiders (q.word.length + r) patterns}

private theorem avoidance_prefix (w u : List ℕ) (h : Avoids (w ++ u)) : Avoids w := by
  intro σ hσ ho
  apply h σ hσ
  obtain ⟨v, hstep, hmem, hsub, _⟩ := ho
  refine ⟨v, hstep, ?_, hsub.trans (List.sublist_append_left _ _), ?_⟩
  · intro i hlo hhi
    exact List.mem_append_left _ (hmem i hlo hhi)
  · simp

private noncomputable def splitExtension (q : Prefix) (r : ℕ) :
    Extensions q (r + 1) → (x : Legal q.word) × Extensions (q.append x) r
  | ⟨[], hu⟩ => False.elim (by simpa using hu.1)
  | ⟨x :: v, hu⟩ =>
    let chosen : Legal q.word := ⟨x, by
      have hbound := hu.2.2.1 q.word.length (by simp)
      simpa only [List.getD_append_right q.word (x :: v) 0 q.word.length (le_refl _),
        Nat.sub_self, List.getD_cons_zero] using hbound, by
      apply avoidance_prefix (q.word ++ [x]) v
      simpa only [List.append_assoc, List.singleton_append] using hu.2.2.2⟩
    ⟨chosen, ⟨v, by simpa using hu.1, by
      have hv : v.length = r := by simpa using hu.1
      refine ⟨by simp only [Prefix.append, List.length_append, List.length_singleton, hv], ?_, ?_⟩
      · simpa only [Prefix.append, List.append_assoc, List.singleton_append] using hu.2.2.1
      · simpa only [Prefix.append, List.append_assoc, List.singleton_append] using hu.2.2.2⟩⟩

private def joinExtension (q : Prefix) (r : ℕ) :
    ((x : Legal q.word) × Extensions (q.append x) r) → Extensions q (r + 1)
  | ⟨x, v⟩ => ⟨x.val :: v.val, by simp [v.property.1], by
      refine ⟨by simp [v.property.1], ?_, ?_⟩
      · simpa only [Prefix.append, List.append_assoc, List.singleton_append]
          using v.property.2.2.1
      · simpa only [Prefix.append, List.append_assoc, List.singleton_append]
          using v.property.2.2.2⟩

private noncomputable def extensionStep (q : Prefix) (r : ℕ) :
    Extensions q (r + 1) ≃ ((x : Legal q.word) × Extensions (q.append x) r) where
  toFun := splitExtension q r
  invFun := joinExtension q r
  left_inv := by
    rintro ⟨u, hlen, hwholelen, hinv, havoid⟩
    cases u with
    | nil => simp at hlen
    | cons x v => rfl
  right_inv := by
    rintro ⟨⟨x, hb, hs⟩, ⟨v, hv, hlen, hinv, havoid⟩⟩
    rfl

private noncomputable def extensionZero (q : Prefix) : Extensions q 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], rfl, by
    change (q.word ++ []).length = q.word.length + 0 ∧ _
    simpa using (show q.word.length = q.word.length ∧ InversionSeqDefs.IsInversionSeq q.word ∧ Avoids q.word from ⟨rfl, q.inversion, q.avoidance⟩)⟩
  left_inv := by
    rintro ⟨u, hu⟩
    have he : u = [] := List.length_eq_zero_iff.mp hu.1
    subst u
    rfl
  right_inv := by rintro ⟨⟩; rfl

private noncomputable def prefixChoice (q : Prefix) : Legal q.word ≃ StateChoice q.state :=
  (choiceEquiv q.word q.nonempty q.inversion q.avoidance).symm.trans
    (liftChoice q.word q.nonempty q.inversion)

private theorem prefix_child (q : Prefix) (x : Legal q.word) :
    (q.append x).state = child q.state (prefixChoice q x) := by
  have h := native_succession q.word q.nonempty q.inversion q.avoidance
    ((choiceEquiv q.word q.nonempty q.inversion q.avoidance).symm x)
  have hv : choiceValue q.word
      ((choiceEquiv q.word q.nonempty q.inversion q.avoidance).symm x) = x.val :=
    congrArg Subtype.val ((choiceEquiv q.word q.nonempty q.inversion q.avoidance).apply_symm_apply x)
  change (q.append x).state = child q.state
    ((liftChoice q.word q.nonempty q.inversion)
      ((choiceEquiv q.word q.nonempty q.inversion q.avoidance).symm x))
  simpa only [hv, Prefix.append, Prefix.state] using h

/-- Constructor and decoder correspondence, at every depth and every actual valid prefix. -/
noncomputable def extensionEquiv (r : ℕ) (q : Prefix) : Extensions q r ≃ Path r q.state := by
  induction r generalizing q with
  | zero => exact extensionZero q
  | succ r ih =>
    exact (extensionStep q r).trans
      (Equiv.sigmaCongr (prefixChoice q) fun x => (ih (q.append x)).trans
        (Equiv.cast (congrArg (Path r) (prefix_child q x))))

instance extensions_finite (q : Prefix) (r : ℕ) : Finite (Extensions q r) :=
  Finite.of_equiv (Path r q.state) (extensionEquiv r q).symm

/-- The continuation count is the cardinality of actual suffixes, without a state-sufficiency axiom. -/
theorem native_continuation_count (q : Prefix) (r : ℕ) :
    Nat.card (Extensions q r) = phi r q.state := Nat.card_congr (extensionEquiv r q)

private theorem short_avoids (w : List ℕ) (hw : w.length < 3) : Avoids w := by
  intro σ hσ ho
  obtain ⟨v, _, _, hsub, _⟩ := ho
  have hlen := hsub.length_le
  simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> simp only [List.length_map,
    List.length_cons, List.length_nil] at hlen <;> omega

private def root : Prefix :=
  ⟨[0], by simp, by intro i hi; simp at hi; subst i; simp,
    short_avoids [0] (by simp)⟩

private theorem root_safe : Safe [0] 0 := short_avoids [0, 0] (by simp)

private theorem root_state : root.state = repeatState 1 (by omega) := by
  classical
  have hv : values [0] = [0] := by
    simp only [values, admissible, maximum, List.foldr_cons, List.foldr_nil, max_self,
      Nat.zero_add, Finset.range_one]
    rw [Finset.filter_singleton]
    simp [root_safe]
  apply State.ext
  · simp [Prefix.state, stateOf, root, siteWord, hv, label, repeatState]
  · simp [Prefix.state, stateOf, root, maximum, repeatState]
  · simp [Prefix.state, stateOf, root, maximum, repeatState, root_safe]

private def rootToExtension (n : ℕ) :
    InversionSeqDefs.avoiders (n + 1) patterns → Extensions root n
  | ⟨[], hw⟩ => False.elim (by simpa using hw.1)
  | ⟨x :: v, hw⟩ => ⟨v, by
      have hx : x = 0 := by have := hw.2.1 0 (by simp); simpa using this
      subst x
      refine ⟨by have := hw.1; simp only [List.length_cons] at this; omega, ?_⟩
      simpa only [root, List.singleton_append, List.length_singleton, Nat.add_comm]
        using hw⟩

private def extensionToRoot (n : ℕ) :
    Extensions root n → InversionSeqDefs.avoiders (n + 1) patterns
  | ⟨v, hv⟩ => ⟨0 :: v, by
      simpa only [root, List.singleton_append, List.length_singleton, Nat.add_comm]
        using hv.2⟩

private def rootExtensionEquiv (n : ℕ) :
    InversionSeqDefs.avoiders (n + 1) patterns ≃ Extensions root n where
  toFun := rootToExtension n
  invFun := extensionToRoot n
  left_inv := by
    rintro ⟨w, hw⟩
    cases w with
    | nil => simpa using hw.1
    | cons x v =>
      apply Subtype.ext
      have hx : x = 0 := by have := hw.2.1 0 (by simp); simpa using this
      change 0 :: v = x :: v
      rw [hx]
  right_inv := by rintro ⟨v, hv⟩; rfl

/-- The empty count and the exact positive-length interpretation of the formal root count. -/
theorem native_avoider_counts :
    (InversionSeqDefs.avoiders 0 patterns).ncard = 1 ∧
      ∀ n : ℕ, (InversionSeqDefs.avoiders (n + 1) patterns).ncard = b n 1 (by omega) := by
  constructor
  · have he : InversionSeqDefs.avoiders 0 patterns = {[]} := by
      ext w
      constructor
      · intro hw
        simpa only [Set.mem_singleton_iff] using List.length_eq_zero_iff.mp hw.1
      · intro hw
        have he : w = [] := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨rfl, by intro i hi; simp at hi, short_avoids [] (by simp)⟩
    rw [he, Set.ncard_singleton]
  · intro n
    change Nat.card (InversionSeqDefs.avoiders (n + 1) patterns) = _
    rw [Nat.card_congr (rootExtensionEquiv n), native_continuation_count]
    simp only [b, root_state]

end D5.S3.Combinatorics.InversionSeq.ClassCPaths
