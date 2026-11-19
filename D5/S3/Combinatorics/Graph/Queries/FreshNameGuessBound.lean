/- GID: D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/FreshNameGuessBound
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A hypergeometric survival bound for adaptive guesses of unknown vertex names. -/

import D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
import D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
import D5.S3.Combinatorics.Probability.PartialNameAssignment
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
open D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open D5.S3.Combinatorics.Probability.PartialNameAssignment
open D5.S0.Diagonal.Probability.EquivariantEscape
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound

variable {V N : Type*}

private theorem absent_ncard_le_length [Finite N] (T : Record N) :
    (absentNames T).ncard ≤ T.length := by
  classical
  let queries := T.map Sigma.fst
  have hsubset : absentNames T ⊆ (queries.toFinset : Set N) := by
    intro q hq
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨⟨q, none⟩, hq, rfl⟩)
  calc
    (absentNames T).ncard ≤ (queries.toFinset : Set N).ncard := Set.ncard_le_ncard hsubset
    _ = queries.toFinset.card := Set.ncard_coe_finset _
    _ ≤ T.length := queries.toFinset_card_le.trans_eq (List.length_map ..)

private theorem revealed_cons (e : Σ _ : N, Reply N) (T : Record N) (initial : Set N) :
    initial ∪ revealedNames (e :: T) =
      namesAfter initial e.1 e.2 ∪ revealedNames T := by
  classical
  rcases e with ⟨q, _ | r⟩
  · ext n
    simp [revealedNames, namesAfter]
  · ext n
    simp only [revealedNames, namesAfter, Set.mem_union, Set.mem_ofPred_eq,
      List.mem_cons, Set.mem_insert_iff]
    aesop

private theorem no_hit_snoc (T : Record N) (e : Σ _ : N, Reply N) (initial : Set N) :
    noGuessedHit initial (T ++ [e]) ↔ noGuessedHit initial T ∧
      (e.2.isSome → e.1 ∈ initial ∪ revealedNames T) := by
  induction T generalizing initial with
  | nil => simp [noGuessedHit, revealedNames]
  | cons entry tail ih =>
    simp only [List.cons_append, noGuessedHit]
    rw [ih, revealed_cons]
    exact and_assoc.symm

private theorem next_prefix (G : SimpleGraph V) (p : Protocol N) (f : V ↪ N) (i : ℕ) :
    runPassiveProtocol (nameReply G) (truncate p (i+1)) f =
      runPassiveProtocol (nameReply G) (truncate p i) f ++
        ((nextQuery p (runPassiveProtocol (nameReply G) (truncate p i) f)).map
          (fun q => (⟨q, nameReply G q f⟩ : Σ _ : N, Reply N))).toList := by
  induction p generalizing i with
  | stop => cases i <;> rfl
  | query q next ih =>
    cases i with
    | zero => simp [truncate, runPassiveProtocol, nextQuery]
    | succ i =>
      simp only [truncate, runPassiveProtocol, nextQuery, List.cons_append, List.cons.injEq,
        true_and]
      exact ih (nameReply G q f) i

private theorem run_length_bound (G : SimpleGraph V) (p : Protocol N) (f : V ↪ N) (i : ℕ) :
    (runPassiveProtocol (nameReply G) (truncate p i) f).length ≤ i := by
  induction i with
  | zero => simp [truncate, runPassiveProtocol]
  | succ i ih =>
    rw [next_prefix, List.length_append]
    cases nextQuery p (runPassiveProtocol (nameReply G) (truncate p i) f) <;>
      simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        List.length_nil, List.length_singleton] <;> omega

private theorem card_step_from_fibers {W R : Type*} [DecidableEq W] [DecidableEq R]
    (prior next : Finset W) (record : W → R) (den misses : ℕ)
    (localBound : ∀ r ∈ prior.image record,
      misses * (prior.filter fun w => record w = r).card ≤
        den * (next.filter fun w => record w = r).card) :
    misses * prior.card ≤ den * next.card := by
  calc
    misses * prior.card =
        ∑ r ∈ prior.image record, misses * (prior.filter fun w => record w = r).card := by
      rw [← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ => Finset.mem_image_of_mem _)]
    _ ≤ ∑ r ∈ prior.image record, den * (next.filter fun w => record w = r).card :=
      Finset.sum_le_sum localBound
    _ ≤ den * next.card := by
      rw [← Finset.mul_sum, Finset.sum_card_fiberwise_eq_card_filter]
      exact Nat.mul_le_mul_left den (Finset.card_filter_le _ _)

private theorem remaining_counts [Fintype V] [Fintype N] (G : SimpleGraph V)
    (p : Protocol N) (ref : V ↪ N) (initial : Set N) (hinit : initial ⊆ Set.range ref) (i : ℕ) :
    let T := runPassiveProtocol (nameReply G) (truncate p i) ref
    let S := initial ∪ revealedNames T
    let B := absentNames T
    let d := S.ncard - initial.ncard
    let K := Fintype.card V - initial.ncard
    let D := Fintype.card N - Fintype.card V
    (S ∪ B)ᶜ.ncard = K - d + (D - B.ncard) ∧
      Fintype.card V - S.ncard = K - d ∧ B.ncard ≤ i := by
  intro T S B d K D
  have hInitS : initial ⊆ S := Set.subset_union_left
  have hS : S ⊆ Set.range ref := Set.union_subset hinit (known_subset_range _ _ _)
  have hDis := (same_history_iff_avoids_absent G (truncate p i) ref ref ∅
    (fun _ _ => rfl)).mp rfl
  have hRange : (Set.range ref).ncard = Fintype.card V := by
    rw [Set.ncard_range_of_injective ref.injective, Nat.card_eq_fintype_card]
  have hSCard : S.ncard ≤ Fintype.card V := by
    rw [← hRange]
    exact Set.ncard_le_ncard hS
  have hInitCard := Set.ncard_le_ncard hInitS
  have hB : B ⊆ (Set.range ref)ᶜ := by
    intro q hq hqr
    exact Set.disjoint_left.mp hDis hqr hq
  have hBCard : B.ncard ≤ D := by
    have h := Set.ncard_le_ncard hB
    rw [Set.ncard_compl, hRange, Nat.card_eq_fintype_card] at h
    exact h
  have hV := Fintype.card_le_of_injective ref ref.injective
  have hLen : T.length ≤ i := run_length_bound G p ref i
  refine ⟨?_, ?_, (absent_ncard_le_length T).trans hLen⟩
  · have hUnion : (S ∪ B).ncard = S.ncard + B.ncard :=
      Set.ncard_union_eq (hDis.mono_left hS)
    rw [Set.ncard_compl, hUnion, Nat.card_eq_fintype_card]
    dsimp only [K, d, D] at *
    omega
  · dsimp [K, d]
    omega

private theorem compatible_hit_count [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N) (ref : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range ref)
    (q : N) (hq : q ∉ (initial ∪ revealedNames (runPassiveProtocol (nameReply G) p ref)) ∪
      absentNames (runPassiveProtocol (nameReply G) p ref)) :
    let T := runPassiveProtocol (nameReply G) p ref
    let S := initial ∪ revealedNames T
    let A := (S ∪ absentNames T)ᶜ
    let C := CompatibleNaming G p ref initial
    (Nat.card {f : C // q ∈ Set.range f.1}) * A.ncard =
      (Fintype.card V - S.ncard) * Nat.card C := by
  classical
  intro T S A C
  let : Nonempty (V ↪ N) := ⟨ref⟩
  let : Fintype C := Fintype.ofFinite C
  let : Nonempty C := ⟨⟨ref, rfl, fun _ _ => rfl⟩⟩
  let H : Set C := {f | q ∈ Set.range f.1}
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨ν, hfilter, hratio⟩ := conditional_unseen_name_hit G p ref initial hinit
  let P : (V ↪ N) → Prop := fun f =>
    runPassiveProtocol (nameReply G) p f = T ∧ ∀ v, ref v ∈ initial → f v = ref v
  have hs : ∃ f ∈ {f | P f}, f ∈ (uniformPmf (V ↪ N)).support := by
    refine ⟨ref, ⟨rfl, fun _ _ => rfl⟩, ?_⟩
    simp [uniformPmf]
  have hmaps : (uniformPmf C).map Subtype.val = ν.map Subtype.val :=
    (D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion.uniform_filter P hs).symm.trans
      (hfilter hs)
  have hHit : (uniformPmf C).toOuterMeasure H = ν.toOuterMeasure H := by
    have hh := congrArg (fun μ : PMF (V ↪ N) => μ.toOuterMeasure {f | q ∈ Set.range f}) hmaps
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hh
    exact hh
  have hMass := hratio ⟨q, hq⟩
  change ν.toOuterMeasure H = ((Fintype.card V - Nat.card S : ℕ) : ℝ≥0∞) / A.ncard at hMass
  rw [← hHit, uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hMass
  have hC : Nat.card C ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hA : A.ncard ≠ 0 := ((Set.ncard_pos (s := A)).mpr ⟨q, hq⟩).ne'
  change (↑(Nat.card H) : ℝ≥0∞) / ↑(Nat.card C) =
    ↑(Fintype.card V - S.ncard) / ↑A.ncard at hMass
  have hCross := (ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr hC)
    (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr hA)
    (ENNReal.natCast_ne_top _)).mp hMass.symm
  change Nat.card H * A.ncard = _
  simpa only [Nat.mul_comm A.ncard _, Nat.mul_comm (Nat.card C) _] using
    (show A.ncard * Nat.card H = Nat.card C * (Fintype.card V - S.ncard) by exact_mod_cast hCross.symm)

private theorem compatible_hit_bound [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N) (ref : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range ref) (i : ℕ)
    (hi : i ≤ Fintype.card N - Fintype.card V) (q : N)
    (hq : q ∉ (initial ∪ revealedNames (runPassiveProtocol (nameReply G) (truncate p i) ref)) ∪
      absentNames (runPassiveProtocol (nameReply G) (truncate p i) ref)) :
    let C := CompatibleNaming G (truncate p i) ref initial
    let hidden := Fintype.card V - initial.ncard
    let available := Fintype.card N - initial.ncard
    Nat.card {f : C // q ∈ Set.range f.1} * (available - i) ≤ hidden * Nat.card C := by
  intro C hidden available
  let T := runPassiveProtocol (nameReply G) (truncate p i) ref
  let S := initial ∪ revealedNames T
  let B := absentNames T
  let A := (S ∪ B)ᶜ
  let discovered := S.ncard - initial.ncard
  let invalid := Fintype.card N - Fintype.card V
  let hit := Nat.card {f : C // q ∈ Set.range f.1}
  change hit * (available - i) ≤ hidden * Nat.card C
  obtain ⟨hA, hS, hB⟩ := remaining_counts G p ref initial hinit i
  change A.ncard = hidden - discovered + (invalid - B.ncard) at hA
  change Fintype.card V - S.ncard = hidden - discovered at hS
  change B.ncard ≤ i at hB
  have hI := Set.ncard_le_ncard hinit
  rw [Set.ncard_range_of_injective ref.injective, Nat.card_eq_fintype_card] at hI
  have hV := Fintype.card_le_of_injective ref ref.injective
  have hAvail : available = hidden + invalid := by
    dsimp [available, hidden, invalid]
    omega
  have hCross : (hidden - discovered) * (available - i) ≤ hidden * A.ncard := by
    rw [hAvail, hA, Nat.add_sub_assoc hi, Nat.mul_add, Nat.mul_add,
      Nat.mul_comm (hidden - discovered) hidden]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le_sub_left hB _)) _
  have hcount : hit * A.ncard = (Fintype.card V - S.ncard) * Nat.card C :=
    compatible_hit_count G (truncate p i) ref initial hinit q hq
  rw [hS] at hcount
  apply Nat.le_of_mul_le_mul_right _ ((Set.ncard_pos (s := A)).mpr ⟨q, hq⟩)
  calc
    hit * (available - i) * A.ncard = hit * A.ncard * (available - i) := by ac_rfl
    _ = Nat.card C * ((hidden - discovered) * (available - i)) := by rw [hcount]; ac_rfl
    _ ≤ Nat.card C * (hidden * A.ncard) := Nat.mul_le_mul_left _ hCross
    _ = hidden * Nat.card C * A.ncard := by ac_rfl

private theorem survives_succ_iff (G : SimpleGraph V) (p : Protocol N) (f : V ↪ N)
    (initial : Set N) (i : ℕ) :
    let T := runPassiveProtocol (nameReply G) (truncate p i) f
    noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p (i+1)) f) ↔
      noGuessedHit initial T ∧
        ∀ q, nextQuery p T = some q → q ∈ Set.range f → q ∈ initial ∪ revealedNames T := by
  intro T
  rw [next_prefix]
  change noGuessedHit initial
    (T ++ ((nextQuery p T).map (fun q => (⟨q, nameReply G q f⟩ : Σ _ : N, Reply N))).toList) ↔ _
  cases hq : nextQuery p T with
  | none => simp
  | some q =>
    simp only [Option.map_some, Option.toList_some, no_hit_snoc, Option.some.injEq,
      forall_eq']
    have hHit : (nameReply G q f).isSome ↔ q ∈ Set.range f := by
      cases hReply : nameReply G q f with
      | none => simp [(answer_eq_none G f q).mp hReply]
      | some r =>
        have h : q ∈ Set.range f := by
          by_contra h
          rw [(answer_eq_none G f q).mpr h] at hReply
          contradiction
        simp [h]
    rw [hHit]

private theorem agree_initial_congr (base ref f : V ↪ N) (initial : Set N)
    (hinit : initial ⊆ Set.range base)
    (href : ∀ v, base v ∈ initial → ref v = base v) :
    (∀ v, base v ∈ initial → f v = base v) ↔
      (∀ v, ref v ∈ initial → f v = ref v) := by
  have hmem v : ref v ∈ initial ↔ base v ∈ initial := by
    constructor
    · intro hv
      obtain ⟨u, hu⟩ := hinit hv
      have hEq := ref.injective ((href u (hu ▸ hv)).trans hu)
      exact hEq ▸ (hu ▸ hv)
    · intro hv
      rwa [href v hv]
  constructor
  · intro h v hv
    have huv := (hmem v).1 hv
    exact (h v huv).trans (href v huv).symm
  · intro h v hv
    exact (h v ((hmem v).2 hv)).trans (href v hv)

private def successfulPrefix (G : SimpleGraph V) (p : Protocol N)
    (base : V ↪ N) (initial : Set N) (i : ℕ) (f : V ↪ N) : Prop :=
  (∀ v, base v ∈ initial → f v = base v) ∧
    noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p i) f)

private theorem prefix_fiber_card_step [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N)
    (base ref : V ↪ N) (initial : Set N) (hinit : initial ⊆ Set.range base)
    (i : ℕ) (hi : i ≤ Fintype.card N - Fintype.card V)
    (href : successfulPrefix G p base initial i ref) :
    let T (f : V ↪ N) := runPassiveProtocol (nameReply G) (truncate p i) f
    let same := fun f => T f = T ref
    let prior : Set (V ↪ N) := {f | successfulPrefix G p base initial i f ∧ same f}
    let next : Set (V ↪ N) := {f | successfulPrefix G p base initial (i+1) f ∧ same f}
    (Fintype.card N - Fintype.card V - i) * prior.ncard ≤
      (Fintype.card N - initial.ncard - i) * next.ncard := by
  classical
  intro T same prior next
  let S := initial ∪ revealedNames (T ref)
  let B := absentNames (T ref)
  let C := CompatibleNaming G (truncate p i) ref initial
  have hInitRef : initial ⊆ Set.range ref := by
    intro n hn
    obtain ⟨v, hv⟩ := hinit hn
    exact ⟨v, (href.1 v (hv ▸ hn)).trans hv⟩
  have hprior (f : V ↪ N) : f ∈ prior ↔
      T f = T ref ∧ ∀ v, ref v ∈ initial → f v = ref v := by
    change ((∀ v, base v ∈ initial → f v = base v) ∧ noGuessedHit initial (T f)) ∧
      T f = T ref ↔ _
    rw [agree_initial_congr base ref f initial hinit href.1]
    have hgood : noGuessedHit initial (T ref) := href.2
    constructor
    · rintro ⟨⟨ha, _⟩, he⟩
      exact ⟨he, ha⟩
    · rintro ⟨he, ha⟩
      exact ⟨⟨ha, he.symm ▸ hgood⟩, he⟩
  let e : prior ≃ C := Equiv.subtypeEquivRight hprior
  have hC : prior.ncard = Nat.card C := Nat.card_congr e
  have hb : Fintype.card N - Fintype.card V - i ≤ Fintype.card N - initial.ncard - i := by
    have hI := Set.ncard_le_ncard hinit
    rw [Set.ncard_range_of_injective base.injective, Nat.card_eq_fintype_card] at hI
    omega
  have hnext (f : V ↪ N) : f ∈ next ↔ f ∈ prior ∧
      ∀ q, nextQuery p (T ref) = some q → q ∈ Set.range f → q ∈ S := by
    change ((∀ v, base v ∈ initial → f v = base v) ∧
      noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p (i+1)) f)) ∧
      T f = T ref ↔ _
    have hs := survives_succ_iff G p f initial i
    dsimp only at hs
    rw [hs]
    change (_ ∧ _ ∧ (∀ q, nextQuery p (T f) = some q → q ∈ Set.range f →
      q ∈ initial ∪ revealedNames (T f))) ∧ T f = T ref ↔ _
    constructor
    · rintro ⟨⟨ha, hgood, hn⟩, ht⟩
      exact ⟨⟨⟨ha, hgood⟩, ht⟩, by simpa only [ht, S] using hn⟩
    · rintro ⟨⟨⟨ha, hgood⟩, ht⟩, hn⟩
      refine ⟨⟨ha, hgood, ?_⟩, ht⟩
      rw [ht]
      exact hn
  have hnext_all (h : ∀ f ∈ prior,
      ∀ q, nextQuery p (T ref) = some q → q ∈ Set.range f → q ∈ S) : next = prior :=
    Set.ext fun f => (hnext f).trans ⟨And.left, fun hf => ⟨hf, h f hf⟩⟩
  cases hq : nextQuery p (T ref) with
  | none =>
    rw [hnext_all (by simp [hq])]
    exact Nat.mul_le_mul_right _ hb
  | some q =>
    by_cases hSeen : q ∈ S
    · rw [hnext_all (by
          intro f hf k hk hkr
          rw [hq, Option.some.injEq] at hk
          exact hk ▸ hSeen)]
      exact Nat.mul_le_mul_right _ hb
    by_cases hAbsent : q ∈ B
    · rw [hnext_all (by
          intro f hf k hk hkr
          rw [hq, Option.some.injEq] at hk
          subst k
          have he := (hprior f).1 hf
          have hMissing : q ∈ absentNames (T f) := he.1.symm ▸ hAbsent
          have hDis := (same_history_iff_avoids_absent G (truncate p i) f f ∅
            (fun _ _ => rfl)).mp rfl
          exact (Set.disjoint_left.mp hDis hkr hMissing).elim)]
      exact Nat.mul_le_mul_right _ hb
    have hFresh : q ∉ S ∪ B := fun h => h.elim hSeen hAbsent
    let missed : Set C := {f | q ∉ Set.range f.1}
    let hit : Set C := {f | q ∈ Set.range f.1}
    have hMiss : next.ncard = missed.ncard := by
      let bridge : next ≃ {f : prior // q ∉ Set.range f.1} := {
        toFun := fun f =>
          ⟨⟨f.1, ((hnext f.1).1 f.2).1⟩,
            fun hr => hSeen (((hnext f.1).1 f.2).2 q hq hr)⟩
        invFun := fun f =>
          ⟨f.1.1, (hnext f.1.1).2 ⟨f.1.2, fun n hn hr => False.elim (by
            rw [hq, Option.some.injEq] at hn
            subst n
            exact f.2 hr)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      exact Nat.card_congr (bridge.trans (Equiv.subtypeEquiv e (fun _ => Iff.rfl)))
    have hpart : hit.ncard + missed.ncard = Nat.card C := Set.ncard_add_ncard_compl hit
    have hbound := compatible_hit_bound G p ref initial hInitRef i hi q hFresh
    change hit.ncard * (Fintype.card N - initial.ncard - i) ≤
      (Fintype.card V - initial.ncard) * Nat.card C at hbound
    have hI := Set.ncard_le_ncard hinit
    rw [Set.ncard_range_of_injective base.injective, Nat.card_eq_fintype_card] at hI
    have hV := Fintype.card_le_of_injective base base.injective
    have hden : Fintype.card N - initial.ncard - i =
      (Fintype.card N - Fintype.card V - i) + (Fintype.card V - initial.ncard) := by omega
    rw [hC, hMiss]
    let den := Fintype.card N - initial.ncard - i
    let invalid := Fintype.card N - Fintype.card V - i
    let hidden := Fintype.card V - initial.ncard
    change den = invalid + hidden at hden
    change hit.ncard * den ≤ hidden * Nat.card C at hbound
    change invalid * Nat.card C ≤ den * missed.ncard
    have heq := congrArg (fun k : ℕ => den * k) hpart
    change den * (hit.ncard + missed.ncard) = den * Nat.card C at heq
    rw [Nat.mul_add, Nat.mul_comm den hit.ncard] at heq
    rw [hden, Nat.add_mul _ _ (Nat.card C)] at heq
    rw [hden] at hbound ⊢
    omega

private theorem prefix_card_step [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N) (base : V ↪ N) (initial : Set N)
    (hinit : initial ⊆ Set.range base) (i : ℕ) (hi : i ≤ Fintype.card N - Fintype.card V) :
    let survive (j : ℕ) : Set (V ↪ N) := {f | successfulPrefix G p base initial j f}
    (Fintype.card N - Fintype.card V - i) * (survive i).ncard ≤
      (Fintype.card N - initial.ncard - i) * (survive (i+1)).ncard := by
  classical
  intro survive
  let prior := (survive i).toFinite.toFinset
  let next := (survive (i+1)).toFinite.toFinset
  let T (f : V ↪ N) := runPassiveProtocol (nameReply G) (truncate p i) f
  change _ * (survive i).ncard ≤ _ * (survive (i+1)).ncard
  rw [Set.ncard_eq_toFinset_card (survive i), Set.ncard_eq_toFinset_card (survive (i+1))]
  change _ * prior.card ≤ _ * next.card
  apply card_step_from_fibers prior next T
  intro record hr
  obtain ⟨ref, href, rfl⟩ := Finset.mem_image.mp hr
  have hgood : ref ∈ survive i :=
    (Set.Finite.mem_toFinset (s := survive i) (a := ref) (survive i).toFinite).mp href
  have hl (j : ℕ) :
      (((survive j).toFinite.toFinset).filter fun w => T w = T ref).card =
        ({w | successfulPrefix G p base initial j w ∧ T w = T ref} : Set (V ↪ N)).ncard := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext w
    simp [survive]
  change _ * ((survive i).toFinite.toFinset.filter fun w => T w = T ref).card ≤
    _ * ((survive (i+1)).toFinite.toFinset.filter fun w => T w = T ref).card
  rw [hl, hl]
  exact prefix_fiber_card_step G p base ref initial hinit i hi hgood

private theorem product_miss_ratio (invalid available guesses : ℕ)
    (hguesses : guesses ≤ available) :
    (∏ i ∈ Finset.range guesses, (↑(invalid - i) : ℝ≥0∞) / ↑(available - i)) =
      (↑(invalid.choose guesses) : ℝ≥0∞) / ↑(available.choose guesses) := by
  rw [ENNReal.prod_div_distrib_of_ne_top (fun i _ => ENNReal.natCast_ne_top (available - i)),
    ← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have hFactorial : (↑guesses.factorial : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hAvailable : (↑(available.choose guesses) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hguesses).ne'
  rw [Nat.cast_mul, Nat.cast_mul]
  apply (ENNReal.div_eq_div_iff hAvailable (ENNReal.natCast_ne_top _)
    (mul_ne_zero hFactorial hAvailable) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _))).mpr
  simp only [mul_left_comm, mul_comm]

/-- The sharp survival product after bounding the conditional hazard at each step. -/
private theorem survival_ge_choose (survival : ℕ → ℝ≥0∞) (invalid available guesses : ℕ)
    (hguesses : guesses ≤ available) (hstart : survival 0 = 1)
    (hstep : ∀ i < guesses,
      survival i * (↑(invalid - i) / ↑(available - i)) ≤ survival (i + 1)) :
    (↑(invalid.choose guesses) : ℝ≥0∞) / ↑(available.choose guesses) ≤ survival guesses := by
  rw [← product_miss_ratio invalid available guesses hguesses]
  have hprod : ∀ i ≤ guesses,
      (∏ j ∈ Finset.range i, (↑(invalid - j) : ℝ≥0∞) / ↑(available - j)) ≤ survival i := by
    intro i
    induction i with
    | zero => intro _; simp [hstart]
    | succ i ih =>
      intro hi
      rw [Finset.prod_range_succ]
      refine le_trans ?_ (hstep i hi)
      gcongr
      exact ih (Nat.le_of_succ_le hi)
  exact hprod guesses le_rfl


private theorem proportion_step (current next total miss den : ℕ) (hden : den ≠ 0)
    (h : miss * current ≤ den * next) :
    ((current : ℝ≥0∞) / total) * ((miss : ℝ≥0∞) / den) ≤ (next : ℝ≥0∞) / total := by
  rw [mul_comm, ← mul_div_assoc, mul_comm (↑miss / ↑den : ℝ≥0∞), ← mul_div_assoc]
  have hm : (↑current * ↑miss : ℝ≥0∞) / ↑den ≤ ↑next := by
    apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hden) (ENNReal.natCast_ne_top _)).mpr
    rw [mul_comm (↑current : ℝ≥0∞), mul_comm (↑next : ℝ≥0∞)]
    exact_mod_cast h
  gcongr

private theorem no_guess_if_all_names_seen (G : SimpleGraph V) (p : Protocol N)
    (f : V ↪ N) (initial : Set N) (h : Set.range f ⊆ initial) :
    noGuessedHit initial (runPassiveProtocol (nameReply G) p f) := by
  induction p generalizing initial with
  | stop => trivial
  | query q next ih =>
    simp only [runPassiveProtocol, noGuessedHit]
    cases hr : nameReply G q f with
    | none => simpa [hr, namesAfter] using ih none initial h
    | some neighbors =>
      have hq : q ∈ Set.range f := by
        by_contra hm
        rw [(answer_eq_none G f q).2 hm] at hr
        contradiction
      refine ⟨fun _ => h hq, ih _ _ (h.trans ?_)⟩
      intro n hn
      exact Set.mem_insert_of_mem _ (Or.inl hn)

/-- For a uniformly named finite graph, no adaptive query strategy can make the
probability of avoiding an unknown-name hit smaller than the probability of
drawing only invalid names in a sample without replacement of the given size. -/
theorem fresh_guess_survival_ge [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N) (base : V ↪ N)
    (initial : Set N) (hinit : initial ⊆ Set.range base) (q : ℕ) :
    let available := Fintype.card N - initial.ncard
    let invalid := Fintype.card N - Fintype.card V
    let r := min q available
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    (↑(invalid.choose r) : ℝ≥0∞) / ↑(available.choose r) ≤
      (uniformPmf X).toOuterMeasure
        {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p q) f.1)} := by
  classical
  intro available invalid r X _ _
  have hI := Set.ncard_le_ncard hinit
  rw [Set.ncard_range_of_injective base.injective, Nat.card_eq_fintype_card] at hI
  have hV := Fintype.card_le_of_injective base base.injective
  have hr : r ≤ available := Nat.min_le_right ..
  by_cases hInvalid : r ≤ invalid
  · by_cases hq : q ≤ available
    · have hrq : r = q := Nat.min_eq_left hq
      let survive (i : ℕ) : Set (V ↪ N) := {f | successfulPrefix G p base initial i f}
      let mass (i : ℕ) : ℝ≥0∞ := ↑(survive i).ncard / ↑(survive 0).ncard
      have hzero : mass 0 = 1 := by
        have hpos : 0 < (survive 0).ncard := (Set.ncard_pos (s := survive 0)).mpr
          ⟨base, fun _ _ => rfl, by simp [truncate, runPassiveProtocol, noGuessedHit]⟩
        exact ENNReal.div_self (Nat.cast_ne_zero.mpr hpos.ne') (ENNReal.natCast_ne_top _)
      have hstep (i : ℕ) (hi : i < r) :
          mass i * (↑(invalid - i) / ↑(available - i)) ≤ mass (i+1) := by
        apply proportion_step _ _ _ _ _ (Nat.sub_ne_zero_of_lt (hi.trans_le hr))
        exact prefix_card_step G p base initial hinit i (hi.le.trans hInvalid)
      have hmass := survival_ge_choose mass invalid available r hr hzero hstep
      rw [hrq] at hmass
      let S : Set X := {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p q) f.1)}
      let : Fintype S := Fintype.ofFinite S
      let e : S ≃ survive q := {
        toFun := fun f => ⟨f.1.1, f.1.2, f.2⟩
        invFun := fun f => ⟨⟨f.1, f.2.1⟩, f.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      let e₀ : X ≃ survive 0 := {
        toFun := fun f => ⟨f.1, f.2, by simp [truncate, runPassiveProtocol, noGuessedHit]⟩
        invFun := fun f => ⟨f.1, f.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      change _ ≤ (uniformPmf X).toOuterMeasure S
      rw [uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card (α := S),
        ← Nat.card_eq_fintype_card (α := X), Nat.card_congr e, Nat.card_congr e₀]
      dsimp only [mass] at hmass
      rw [hrq]
      exact hmass
    · have hrAvail : r = available := Nat.min_eq_right (Nat.le_of_not_ge hq)
      have hIeq : initial.ncard = Fintype.card V := by
        rw [hrAvail] at hInvalid
        dsimp [available, invalid] at hInvalid
        omega
      have hall (f : X) : noGuessedHit initial
          (runPassiveProtocol (nameReply G) (truncate p q) f.1) := by
        apply no_guess_if_all_names_seen
        have hf : initial ⊆ Set.range f.1 := by
          intro n hn
          obtain ⟨v, hv⟩ := hinit hn
          exact ⟨v, (f.2 v (hv ▸ hn)).trans hv⟩
        have he : initial = Set.range f.1 := Set.eq_of_subset_of_ncard_le hf (by
          rw [Set.ncard_range_of_injective f.1.injective, Nat.card_eq_fintype_card, hIeq])
        exact he.symm.subset
      have hAll : ({f : X | noGuessedHit initial
          (runPassiveProtocol (nameReply G) (truncate p q) f.1)} : Set X) = Set.univ :=
        Set.eq_univ_of_forall hall
      rw [hAll, ((uniformPmf X).toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)]
      have hda : invalid = available := by dsimp [invalid, available]; rw [hIeq]
      rw [hda, hrAvail, Nat.choose_self]
      simp
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hInvalid)]


private def guessUntilHit : List N → Protocol N
  | [] => .stop
  | q :: rest => .query q fun
    | none => guessUntilHit rest
    | some _ => .stop

private theorem guess_depth (names : List N) (q : ℕ) (h : names.length ≤ q) :
    depthBound (guessUntilHit names) q := by
  induction names generalizing q with
  | nil => trivial
  | cons name rest ih =>
    cases q with
    | zero => simp at h
    | succ q =>
      intro reply
      cases reply
      · exact ih q (Nat.le_of_succ_le_succ h)
      · trivial

private theorem noGuessedHit_iff_avoids_guesses (G : SimpleGraph V) (f : V ↪ N)
    (names : List N) (initial : Set N) (hNames : ∀ q ∈ names, q ∉ initial) :
    noGuessedHit initial (runPassiveProtocol (nameReply G) (guessUntilHit names) f) ↔
      ∀ q ∈ names, q ∉ Set.range f := by
  induction names with
  | nil => simp [guessUntilHit, runPassiveProtocol, noGuessedHit]
  | cons q names ih =>
    have hq := hNames q (List.mem_cons_self ..)
    have hrest : ∀ n ∈ names, n ∉ initial :=
      fun n hn => hNames n (List.mem_cons_of_mem _ hn)
    simp only [guessUntilHit, runPassiveProtocol]
    cases hReply : nameReply G q f with
    | none =>
      have hm := (answer_eq_none G f q).1 hReply
      simpa only [noGuessedHit, Option.isSome_none, Bool.false_eq_true, false_implies,
        not_false_eq_true, true_and, namesAfter, List.forall_mem_cons, hm] using ih hrest
    | some r =>
      have hh : q ∈ Set.range f := by
        by_contra hm
        rw [(answer_eq_none G f q).2 hm] at hReply
        contradiction
      refine ⟨?_, fun h => (h q (List.mem_cons_self ..) hh).elim⟩
      intro h
      exact (hq (h.1 rfl)).elim

private theorem descending_factorial_ratio (available hidden guesses : ℕ)
    (hHidden : hidden ≤ available) (hGuesses : guesses ≤ available) :
    (↑((available - guesses).descFactorial hidden) : ℝ≥0∞) /
        ↑(available.descFactorial hidden) =
      ↑((available - hidden).choose guesses) / ↑(available.choose guesses) := by
  have hA : (available - guesses).descFactorial hidden * available.descFactorial guesses =
      available.descFactorial (guesses + hidden) := by
    have h := Nat.descFactorial_mul_descFactorial (n := available) (Nat.le_add_right guesses hidden)
    simpa only [Nat.add_sub_cancel_left] using h
  have hB : (available - hidden).descFactorial guesses * available.descFactorial hidden =
      available.descFactorial (guesses + hidden) := by
    have h := Nat.descFactorial_mul_descFactorial (n := available) (Nat.le_add_left hidden guesses)
    simpa only [Nat.add_sub_cancel] using h
  rw [Nat.descFactorial_eq_factorial_mul_choose available guesses] at hA
  rw [Nat.descFactorial_eq_factorial_mul_choose (available - hidden) guesses] at hB
  have cross : ((available - guesses).descFactorial hidden) * available.choose guesses =
      ((available - hidden).choose guesses) * available.descFactorial hidden := by
    apply Nat.mul_left_cancel guesses.factorial_pos
    calc
      _ = (available - guesses).descFactorial hidden *
          (guesses.factorial * available.choose guesses) := by ac_rfl
      _ = (guesses.factorial * (available - hidden).choose guesses) *
          available.descFactorial hidden := hA.trans hB.symm
      _ = _ := by ac_rfl
  have h0 : available.descFactorial hidden ≠ 0 :=
    fun h => (Nat.not_lt_of_ge hHidden) (Nat.descFactorial_eq_zero_iff_lt.mp h)
  refine (ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.choose_pos hGuesses).ne')
    (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr h0) (ENNReal.natCast_ne_top _)).mpr ?_
  rw [mul_comm (↑(available.choose guesses) : ℝ≥0∞),
    mul_comm (↑(available.descFactorial hidden) : ℝ≥0∞)]
  exact_mod_cast cross

private theorem constrained_naming_count [Fintype V] [Fintype N]
    (base : V ↪ N) (initial forbidden : Set N) (hinit : initial ⊆ Set.range base)
    (hsep : Disjoint initial forbidden) :
    Nat.card {f : V ↪ N // (∀ v, base v ∈ initial → f v = base v) ∧
      Disjoint (Set.range f) forbidden} =
      (Fintype.card N - initial.ncard - forbidden.ncard).descFactorial
        (Fintype.card V - initial.ncard) := by
  classical
  let K := (base ⁻¹' initial).toFinite.toFinset
  let A := (initial ∪ forbidden)ᶜ.toFinite.toFinset
  let named : K ↪ N := (Function.Embedding.subtype fun v => v ∈ K).trans base
  have hK (v : V) : v ∈ K ↔ base v ∈ initial := (Set.Finite.mem_toFinset _)
  have hA (n : N) : n ∈ A ↔ n ∉ initial ∪ forbidden := (Set.Finite.mem_toFinset _)
  have hs (v : K) : named v ∉ A := fun h => (hA _).mp h (Or.inl ((hK _).mp v.2))
  let X := {f : V ↪ N // (∀ v, base v ∈ initial → f v = base v) ∧
      Disjoint (Set.range f) forbidden}
  have hCand (f : V ↪ N) : ((∀ v, base v ∈ initial → f v = base v) ∧
      Disjoint (Set.range f) forbidden) ↔
      (∀ x : K, f x = named x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A := by
    constructor
    · rintro ⟨hf, hfD⟩
      refine ⟨fun x => hf x ((hK _).mp x.2), ?_⟩
      intro x
      apply (hA _).mpr
      rintro (hi | hmiss)
      · obtain ⟨v, hv⟩ := hinit hi
        have he := f.injective ((hf v (hv ▸ hi)).trans hv)
        exact x.2 ((hK _).mpr (he ▸ (hv ▸ hi)))
      · exact Set.disjoint_left.mp hfD ⟨x, rfl⟩ hmiss
    · rintro ⟨hf, hrest⟩
      refine ⟨fun v hv => hf ⟨v, (hK _).mpr hv⟩, ?_⟩
      rw [Set.disjoint_left]
      rintro q ⟨v, rfl⟩ hq
      by_cases hv : v ∈ K
      · have hInit : f v ∈ initial := by
          rw [show f v = base v from hf ⟨v, hv⟩]
          exact (hK _).mp hv
        exact Set.disjoint_left.mp hsep hInit hq
      · exact (hA _).mp (hrest ⟨v, hv⟩) (Or.inr hq)
  let e : X ≃ ({v // v ∉ K} ↪ A) :=
    (Equiv.subtypeEquivRight hCand).trans (residualEmbedding K A named hs)
  change Nat.card X = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_coe]
  have hAcard : A.card = Fintype.card N - initial.ncard - forbidden.ncard := by
    change (initial ∪ forbidden)ᶜ.toFinite.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card, Set.ncard_compl,
      Set.ncard_union_eq hsep, Nat.card_eq_fintype_card, Nat.sub_sub]
  have hKin : base '' (base ⁻¹' initial) = initial := Set.image_preimage_eq_of_subset hinit
  have hKcard : K.card = initial.ncard := by
    change (base ⁻¹' initial).toFinite.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card, ← Set.ncard_image_of_injective _ base.injective, hKin]
  have hHidden : Fintype.card {v // v ∉ K} = Fintype.card V - initial.ncard := by
    rw [← Nat.card_eq_fintype_card]
    change ((K : Set V)ᶜ).ncard = _
    rw [Set.ncard_compl, Set.ncard_coe_finset, Nat.card_eq_fintype_card, hKcard]
  rw [hAcard, hHidden]

private theorem guess_truncate (names : List N) (q : ℕ) (h : names.length ≤ q) :
    truncate (guessUntilHit names) q = guessUntilHit names := by
  induction names generalizing q with
  | nil => cases q <;> rfl
  | cons name rest ih =>
    cases q with
    | zero => simp at h
    | succ q =>
      have hrest := Nat.le_of_succ_le_succ h
      simp only [guessUntilHit, truncate]
      congr 1
      funext reply
      cases reply
      · exact ih q hrest
      · cases q <;> rfl

/-- Querying distinct initially unknown names and stopping at the first hit
attains the hypergeometric bound for any query budget. -/
theorem exists_strategy_attaining_guess_survival [Fintype V] [Fintype N]
    (G : SimpleGraph V) (base : V ↪ N) (initial : Set N)
    (hinit : initial ⊆ Set.range base) (q : ℕ) :
    let available := Fintype.card N - initial.ncard
    let invalid := Fintype.card N - Fintype.card V
    let r := min q available
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    ∃ p : Protocol N, depthBound p q ∧
      (uniformPmf X).toOuterMeasure
        {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p q) f.1)} =
      (↑(invalid.choose r) : ℝ≥0∞) / ↑(available.choose r) := by
  classical
  intro available invalid r X _ _
  let A := initialᶜ.toFinite.toFinset
  have hA : A.card = available := by
    change initialᶜ.toFinite.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card, Set.ncard_compl, Nat.card_eq_fintype_card]
  obtain ⟨Q, hQ, hQr⟩ := Finset.exists_subset_card_eq (s := A) (n := r)
    (hA.symm ▸ Nat.min_le_right q available)
  let names := Q.toList
  have hLen : names.length = r := Q.length_toList.trans hQr
  have hLenQ : names.length ≤ q := hLen ▸ Nat.min_le_left q available
  have hNames (n : N) (hn : n ∈ names) : n ∉ initial :=
    (Set.Finite.mem_toFinset initialᶜ.toFinite).mp (hQ (Finset.mem_toList.mp hn))
  let S : Set X := {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (guessUntilHit names) f.1)}
  let : Fintype S := Fintype.ofFinite S
  refine ⟨guessUntilHit names, guess_depth names q hLenQ, ?_⟩
  rw [guess_truncate names q hLenQ]
  change (uniformPmf X).toOuterMeasure S = _
  let Y := {f : V ↪ N // (∀ v, base v ∈ initial → f v = base v) ∧
      Disjoint (Set.range f) (Q : Set N)}
  have hAvoid (f : X) : f ∈ S ↔ Disjoint (Set.range f.1) (Q : Set N) := by
    change noGuessedHit initial (runPassiveProtocol (nameReply G) (guessUntilHit names) f.1) ↔ _
    rw [noGuessedHit_iff_avoids_guesses G f.1 names initial hNames, Set.disjoint_left]
    simp only [names, Finset.mem_toList, Finset.mem_coe]
    exact ⟨fun h n hr hn => h n hn hr, fun h n hn hr => h hr hn⟩
  let e : S ≃ Y := {
    toFun := fun f => ⟨f.1.1, f.1.2, (hAvoid f.1).mp f.2⟩
    invFun := fun f => ⟨⟨f.1, f.2.1⟩, (hAvoid _).mpr f.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e₀ : X ≃ {f : V ↪ N // (∀ v, base v ∈ initial → f v = base v) ∧
      Disjoint (Set.range f) (∅ : Set N)} :=
    Equiv.subtypeEquivRight fun _ => by simp
  rw [uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card (α := S),
    ← Nat.card_eq_fintype_card (α := X), Nat.card_congr e, Nat.card_congr e₀]
  have hDis : Disjoint initial (Q : Set N) := by
    rw [Set.disjoint_left]
    exact fun n hn hQn => hNames n (Finset.mem_toList.mpr hQn) hn
  rw [constrained_naming_count base initial (Q : Set N) hinit hDis,
    constrained_naming_count base initial ∅ hinit (Set.disjoint_empty _),
    Set.ncard_coe_finset, hQr, Set.ncard_empty, Nat.sub_zero]
  let hidden := Fintype.card V - initial.ncard
  change (↑((available - r).descFactorial hidden) : ℝ≥0∞) /
    ↑(available.descFactorial hidden) = ↑(invalid.choose r) / ↑(available.choose r)
  have hV := Fintype.card_le_of_injective base base.injective
  have hIc := Set.ncard_le_ncard hinit
  rw [Set.ncard_range_of_injective base.injective, Nat.card_eq_fintype_card] at hIc
  have hD : available - hidden = invalid := by
    dsimp [available, hidden, invalid]
    omega
  rw [← hD]
  exact descending_factorial_ratio available hidden r (Nat.sub_le_sub_right hV _) (Nat.min_le_right ..)


end D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
