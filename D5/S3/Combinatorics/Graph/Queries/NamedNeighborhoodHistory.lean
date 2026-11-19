/- GID: D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Complete named neighborhood queries admit exact replay and a conditional fresh-name hit law. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
import D5.S0.Diagonal.Probability.EquivariantEscape
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact replay and the conditional probability of a fresh name in an adaptive graph query. -/

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion (uniform_filter)
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory

variable {V N : Type*}

/-- Answer with all neighbor names on a hit and a separate failure marker on a miss. -/
noncomputable def nameReply (G : SimpleGraph V) (n : N) (f : V ↪ N) : Option (Set N) := by
  classical
  exact if h : n ∈ Set.range f then some (f '' G.neighborSet h.choose) else none

@[simp] private theorem answer_at_name (G : SimpleGraph V) (f : V ↪ N) (x : V) :
    nameReply G (f x) f = some (f '' G.neighborSet x) := by
  classical
  have h : f x ∈ Set.range f := ⟨x, rfl⟩
  rw [nameReply, dite_eq_left h, f.injective h.choose_spec]

@[simp] private theorem answer_eq_none (G : SimpleGraph V) (f : V ↪ N) (q : N) :
    nameReply G q f = none ↔ q ∉ Set.range f := by
  classical
  by_cases h : q ∈ Set.range f <;> simp [nameReply, h]

abbrev History (N : Type*) := List (Σ _ : N, Option (Set N))

/-- Successful query names and the neighbor names returned with them. -/
def revealedNames (T : History N) : Set N :=
  {n | ∃ q r, (⟨q, some r⟩ : Σ _ : N, Option (Set N)) ∈ T ∧ (n = q ∨ n ∈ r)}

/-- Names for which the transcript records an unsuccessful query. -/
def absentNames (T : History N) : Set N := {n | (⟨n, none⟩ : Σ _ : N, Option (Set N)) ∈ T}

private theorem replay_iff {S : Type*} (read : N → S → Option (Set N))
    (p : PassiveProtocol N (fun _ => Option (Set N))) (s t : S) :
    runPassiveProtocol read p s = runPassiveProtocol read p t ↔
      ∀ (entry : Σ _ : N, Option (Set N)), entry ∈ runPassiveProtocol read p t →
        read entry.1 s = entry.2 := by
  induction p with
  | stop => simp [runPassiveProtocol]
  | query q next ih =>
    simp only [runPassiveProtocol]
    constructor
    · intro he
      obtain ⟨hhead, htail⟩ := List.cons.inj he
      have h : read q s = read q t := congrArg Sigma.snd hhead
      rw [h] at htail
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact h
      · exact (ih _).mp htail _ he
    · intro hreplay
      have h := hreplay ⟨q, read q t⟩ (List.mem_cons_self ..)
      change read q s = read q t at h
      rw [h]
      exact congrArg (List.cons ⟨q, read q t⟩) ((ih _).mpr
        fun entry he => hreplay entry (List.mem_cons_of_mem _ he))

private theorem same_history_iff_avoids_absent (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (f ref : V ↪ N)
    (initial : Set N)
    (agree : ∀ v, ref v ∈ initial ∪ revealedNames (runPassiveProtocol (nameReply G) p ref) → f v = ref v) :
    runPassiveProtocol (nameReply G) p f = runPassiveProtocol (nameReply G) p ref ↔
      Disjoint (Set.range f) (absentNames (runPassiveProtocol (nameReply G) p ref)) := by
  rw [replay_iff]
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro n hn ha
    exact (answer_eq_none G f n).mp (h ⟨n, none⟩ ha) hn
  · intro h entry he
    rcases entry with ⟨q, _ | r⟩
    · change nameReply G q f = none
      exact (answer_eq_none G f q).mpr (fun hq => Set.disjoint_left.mp h hq he)
    · have hrow := (replay_iff (nameReply G) p ref ref).mp rfl ⟨q, some r⟩ he
      change nameReply G q ref = some r at hrow
      obtain hq | hq := em (q ∈ Set.range ref)
      · obtain ⟨v, rfl⟩ := hq
        rw [answer_at_name] at hrow
        have hr := Option.some.inj hrow
        have hname := agree v (Or.inr ⟨ref v, r, he, Or.inl rfl⟩)
        change nameReply G (ref v) f = some r
        rw [← hname, answer_at_name]
        congr 1
        rw [← hr]
        apply Set.image_congr
        intro w hw
        exact agree w (Or.inr ⟨ref v, r, he, Or.inr (hr ▸ ⟨w, hw, rfl⟩)⟩)
      · rw [(answer_eq_none G ref q).mpr hq] at hrow
        contradiction

private theorem known_subset_range (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N) :
    revealedNames (runPassiveProtocol (nameReply G) p ref) ⊆ Set.range ref := by
  rintro n ⟨q, r, hentry, hn⟩
  have hrow := (replay_iff (nameReply G) p ref ref).mp rfl ⟨q, some r⟩ hentry
  change nameReply G q ref = some r at hrow
  have hq : q ∈ Set.range ref := by
    by_contra h
    rw [(answer_eq_none G ref q).mpr h] at hrow
    contradiction
  rcases hn with rfl | hn
  · exact hq
  · obtain ⟨v, rfl⟩ := hq
    rw [answer_at_name] at hrow
    rw [← Option.some.inj hrow] at hn
    exact Set.image_subset_range _ _ hn

private theorem name_permutation_preserves_history (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (f : V ↪ N) (e : Equiv.Perm N)
    (hfixed : ∀ q, q ∈ revealedNames (runPassiveProtocol (nameReply G) p f) ∪
      absentNames (runPassiveProtocol (nameReply G) p f) → e q = q) :
    runPassiveProtocol (nameReply G) p (f.trans e.toEmbedding) =
      runPassiveProtocol (nameReply G) p f := by
  apply (same_history_iff_avoids_absent G p (f.trans e.toEmbedding) f ∅ ?_).mpr
  · rw [Set.disjoint_left]
    rintro q ⟨v, hv⟩ hq
    have heq : e (f v) = e q := hv.trans (hfixed q (Or.inr hq)).symm
    have href := (same_history_iff_avoids_absent G p f f ∅ (fun _ _ => rfl)).mp rfl
    exact Set.disjoint_left.mp href ⟨v, e.injective heq⟩ hq
  · intro v hv
    exact hfixed (f v) (Or.inl (by simpa using hv))

abbrev CompatibleNaming (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N) (initial : Set N) :=
  {f : V ↪ N // runPassiveProtocol (nameReply G) p f = runPassiveProtocol (nameReply G) p ref ∧
    ∀ v, ref v ∈ initial → f v = ref v}

private def swapCompatibleNames (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N)
    (initial : Set N) [DecidableEq N] (a b : N)
    (ha : a ∉ (initial ∪ revealedNames (runPassiveProtocol (nameReply G) p ref)) ∪
      absentNames (runPassiveProtocol (nameReply G) p ref))
    (hb : b ∉ (initial ∪ revealedNames (runPassiveProtocol (nameReply G) p ref)) ∪
      absentNames (runPassiveProtocol (nameReply G) p ref)) :
    {f : CompatibleNaming G p ref initial // a ∈ Set.range f.1} ≃
      {f : CompatibleNaming G p ref initial // b ∈ Set.range f.1} := by
  let e := Equiv.swap a b
  have hfix q (hq : q ∈ (initial ∪ revealedNames (runPassiveProtocol (nameReply G) p ref)) ∪
      absentNames (runPassiveProtocol (nameReply G) p ref)) : e q = q :=
    Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hq)) (fun h => hb (h ▸ hq))
  let relabel (f : CompatibleNaming G p ref initial) : CompatibleNaming G p ref initial :=
    ⟨f.1.trans e.toEmbedding, by
      refine ⟨?_, fun v hv => ?_⟩
      · refine (name_permutation_preserves_history G p f.1 e ?_).trans f.2.1
        rw [f.2.1]
        rintro q (hq | hq)
        · exact hfix q (Or.inl (Or.inr hq))
        · exact hfix q (Or.inr hq)
      · change e (f.1 v) = ref v
        rw [f.2.2 v hv, hfix _ (Or.inl (Or.inl hv))]⟩
  have htwice (f : CompatibleNaming G p ref initial) : relabel (relabel f) = f := by
    apply Subtype.ext
    ext v
    change e (e (f.1 v)) = f.1 v
    simpa only [e, Equiv.symm_swap] using e.symm_apply_apply (f.1 v)
  exact {
    toFun := fun f => ⟨relabel f.1, by
      obtain ⟨x, hx⟩ := f.2
      refine ⟨x, ?_⟩
      change e (f.1.1 x) = b
      rw [hx, Equiv.swap_apply_left]⟩
    invFun := fun f => ⟨relabel f.1, by
      obtain ⟨x, hx⟩ := f.2
      refine ⟨x, ?_⟩
      change e (f.1.1 x) = a
      rw [hx, Equiv.swap_apply_right]⟩
    left_inv := fun f => Subtype.ext (htwice f.1)
    right_inv := fun f => Subtype.ext (htwice f.1) }

private theorem compatible_occupied_card [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range ref) (f : CompatibleNaming G p ref initial) :
    let T := runPassiveProtocol (nameReply G) p ref
    let S := initial ∪ revealedNames T
    let A := (S ∪ absentNames T)ᶜ
    Nat.card {a : A // a.1 ∈ Set.range f.1} = Fintype.card V - Nat.card S := by
  classical
  intro T S A
  have hS : S ⊆ Set.range f.1 := by
    intro n hn
    rcases hn with hInitial | hKnown
    · obtain ⟨v, hv⟩ := hinit hInitial
      exact ⟨v, (f.2.2 v (hv ▸ hInitial)).trans hv⟩
    · apply known_subset_range G p f.1
      rw [f.2.1]
      exact hKnown
  have hMiss : Disjoint (Set.range f.1) (absentNames T) := by
    have hf := (same_history_iff_avoids_absent G p f.1 f.1 ∅ (fun _ _ => rfl)).mp rfl
    rwa [f.2.1] at hf
  let named : Finset N := Finset.univ.map f.1
  let : Fintype S := Fintype.ofFinite _
  have hnamed (n : N) : n ∈ named ↔ n ∈ Set.range f.1 := by simp [named]
  have hs : S.toFinset ⊆ named := fun n hn => (hnamed n).mpr (hS (Set.mem_toFinset.mp hn))
  let e : {a : A // a.1 ∈ Set.range f.1} ≃ (named \ S.toFinset : Finset N) :=
    { toFun := fun a => ⟨a.1.1, Finset.mem_sdiff.mpr ⟨(hnamed _).2 a.2,
        fun hs => a.1.2 (Or.inl (Set.mem_toFinset.mp hs))⟩⟩
      invFun := fun n => by
        have hn := Finset.mem_sdiff.mp n.2
        have hRange := (hnamed _).1 hn.1
        exact ⟨⟨n.1, fun h => h.elim (fun h => hn.2 (Set.mem_toFinset.mpr h))
          (fun h => Set.disjoint_left.mp hMiss hRange h)⟩, hRange⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_sdiff_of_subset hs,
    Nat.card_eq_fintype_card]
  simp [named]

/-- Uniformly sampling the actual transcript fiber gives the same hit mass for
every as-yet unqueried and unexposed name, even when the transcript does not
identify the vertices bearing the exposed names. -/
theorem conditional_unseen_name_hit [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range ref) :
    let T := runPassiveProtocol (nameReply G) p ref
    let S := initial ∪ revealedNames T
    let A := (S ∪ absentNames T)ᶜ
    let freshCount := A.ncard
    let : Nonempty (V ↪ N) := ⟨ref⟩
    ∃ ν : PMF (CompatibleNaming G p ref initial),
      (∀ hs, (uniformPmf (V ↪ N)).filter {f | runPassiveProtocol (nameReply G) p f = T ∧
        ∀ v, ref v ∈ initial → f v = ref v} hs = ν.map Subtype.val) ∧
      ∀ a : A, ν.toOuterMeasure {f | a.1 ∈ Set.range f.1} =
        ((Fintype.card V - Nat.card S : ℕ) : ℝ≥0∞) / freshCount := by
  classical
  intro T S A freshCount _
  let X := CompatibleNaming G p ref initial
  let : Fintype X := Fintype.ofFinite _
  let : Nonempty X := ⟨⟨ref, rfl, fun _ _ => rfl⟩⟩
  let : Fintype A := Fintype.ofFinite _
  let P : (V ↪ N) → Prop := fun f =>
    runPassiveProtocol (nameReply G) p f = T ∧ ∀ v, ref v ∈ initial → f v = ref v
  refine ⟨uniformPmf X, fun hs => uniform_filter P hs, ?_⟩
  intro a
  let r (f : X) (b : A) : Prop := b.1 ∈ Set.range f.1
  let H : Set X := {f | r f a}
  let : Fintype H := Fintype.ofFinite _
  have countPerName (b : A) :
      (Finset.univ.bipartiteBelow r b).card = Nat.card {f : X // r f a} := by
    rw [Finset.bipartiteBelow, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (swapCompatibleNames G p ref initial b.1 a.1 b.2 a.2)
  have countPerNaming (f : X) :
      (Finset.univ.bipartiteAbove r f).card = Fintype.card V - Nat.card S := by
    rw [Finset.bipartiteAbove, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact compatible_occupied_card G p ref initial hinit f
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    (s := Finset.univ) (t := Finset.univ)
  simp only [countPerName, countPerNaming, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcount
  change (uniformPmf X).toOuterMeasure H =
    ((Fintype.card V - Nat.card S : ℕ) : ℝ≥0∞) / Nat.card A
  rw [uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card (α := H),
    Nat.card_eq_fintype_card (α := A)]
  have hA : Nonempty A := ⟨a⟩
  apply (ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)).mpr
  exact_mod_cast hcount.symm

/-- Within a fixed assignment of the observed names to vertices, a complete record
is replayed exactly by the remaining injections into unobserved and nonexcluded names. -/
theorem history_fiber_iff (G : SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N))) (f ref : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range ref) :
    let record := runPassiveProtocol (nameReply G) p ref
    let observed := initial ∪ revealedNames record
    let available := (observed ∪ absentNames record)ᶜ
    let agrees := ∀ v, ref v ∈ observed → f v = ref v
    (runPassiveProtocol (nameReply G) p f = record ∧ agrees) ↔
      (agrees ∧ ∀ v, ref v ∉ observed → f v ∈ available) := by
  intro record observed available agrees
  have hs : observed ⊆ Set.range ref :=
    Set.union_subset hinit (known_subset_range G p ref)
  have href : Disjoint (Set.range ref) (absentNames record) :=
    (same_history_iff_avoids_absent G p ref ref initial (fun _ _ => rfl)).mp rfl
  constructor
  · rintro ⟨hrecord, hagrees⟩
    have hmiss := (same_history_iff_avoids_absent G p f ref initial hagrees).mp hrecord
    refine ⟨hagrees, fun v hv hforbidden => ?_⟩
    rcases hforbidden with hseen | hfailed
    · obtain ⟨w, hw⟩ := hs hseen
      have hfixed := hagrees w (hw ▸ hseen)
      have hsame := f.injective (hfixed.trans hw)
      exact hv (hsame ▸ (hw ▸ hseen))
    · exact Set.disjoint_left.mp hmiss ⟨v, rfl⟩ hfailed
  · rintro ⟨hagrees, havailable⟩
    refine ⟨(same_history_iff_avoids_absent G p f ref initial hagrees).mpr ?_, hagrees⟩
    rw [Set.disjoint_left]
    rintro n ⟨v, rfl⟩ hn
    by_cases hv : ref v ∈ observed
    · exact Set.disjoint_left.mp href ⟨v, rfl⟩ (hagrees v hv ▸ hn)
    · exact havailable v hv (Or.inr hn)

end D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
