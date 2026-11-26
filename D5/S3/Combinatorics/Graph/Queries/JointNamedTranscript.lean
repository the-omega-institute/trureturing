/- GID: D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/JointNamedTranscript
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: An actual named transcript weights the graph posterior by feasible name placements. -/

import D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
import D5.S3.Combinatorics.Probability.PartialNameAssignment
import Mathlib.Data.Set.Card
import Mathlib.Probability.ProbabilityMassFunction.Monad

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open D5.S3.Combinatorics.Probability.PartialNameAssignment

open D5.S0.Diagonal.Probability.EquivariantEscape
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript

variable {V N : Type*}

noncomputable def readWorld (q : N) (w : SimpleGraph V × (V ↪ N)) :=
  nameReply w.1 q w.2

def realizes (T : History N) (seen : Set N) (G : SimpleGraph V)
    (placement : seen ↪ V) : Prop :=
  ∀ q reply, (⟨q, some reply⟩ : Σ _ : N, Option (Set N)) ∈ T →
    ∀ (hq : q ∈ seen),
      G.neighborSet (placement ⟨q, hq⟩) =
        {v | ∃ a : seen, a.1 ∈ reply ∧ placement a = v}

private theorem reply_of_placement (T : History N) (seen : Set N)
    (hseen : revealedNames T ⊆ seen) (G : SimpleGraph V)
    (f : V ↪ N) (placement : seen ↪ V)
    (hf : ∀ a : seen, f (placement a) = a.1) (q : N) (r : Set N)
    (he : (⟨q, some r⟩ : Σ _ : N, Option (Set N)) ∈ T) :
    nameReply G q f = some r ↔
      G.neighborSet (placement ⟨q, hseen ⟨q, r, he, Or.inl rfl⟩⟩) =
        {v | ∃ a : seen, a.1 ∈ r ∧ placement a = v} := by
  classical
  let qs : seen := ⟨q, hseen ⟨q, r, he, Or.inl rfl⟩⟩
  change nameReply G q f = some r ↔ G.neighborSet (placement qs) = _
  have hReply : nameReply G q f = some (f '' G.neighborSet (placement qs)) := by
    have hq : f (placement qs) = q := hf qs
    rw [← hq, answer_at_name]
  rw [hReply, Option.some.injEq]
  constructor
  · intro h
    ext v
    constructor
    · intro hv
      have hr : f v ∈ r := h ▸ ⟨v, hv, rfl⟩
      let a : seen := ⟨f v, hseen ⟨q, r, he, Or.inr hr⟩⟩
      exact ⟨a, hr, f.injective (hf a)⟩
    · rintro ⟨a, ha, rfl⟩
      have H : f (placement a) ∈ r := (hf a).symm ▸ ha
      rw [← h] at H
      obtain ⟨u, hu, hu'⟩ := H
      exact (f.injective hu') ▸ hu
  · intro h
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := h ▸ hv
      rwa [hf]
    · intro ha
      let x : seen := ⟨a, hseen ⟨q, r, he, Or.inr ha⟩⟩
      exact ⟨placement x, h.symm ▸ ⟨x, ha, rfl⟩, hf x⟩

private theorem transcript_iff_feasible (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (G : SimpleGraph V)
    (f : V ↪ N) (seen : Set N)
    (hseen : revealedNames (runPassiveProtocol readWorld p ref) ⊆ seen)
    (placement : seen ↪ V) (hf : ∀ a : seen, f (placement a) = a.1) :
    let T := runPassiveProtocol readWorld p ref
    runPassiveProtocol readWorld p (G, f) = T ↔
      realizes T seen G placement ∧ Disjoint (Set.range f) (absentNames T) := by
  intro T
  rw [replay_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q r he hq
      exact (reply_of_placement T seen hseen G f placement hf q r he).1 (h ⟨q, some r⟩ he)
    · rw [Set.disjoint_left]
      intro q hq he
      exact (answer_eq_none G f q).mp (h ⟨q, none⟩ he) hq
  · rintro ⟨h, hmiss⟩ ⟨q, _ | r⟩ he
    · exact (answer_eq_none G f q).2 (fun hq => Set.disjoint_left.mp hmiss hq he)
    · exact (reply_of_placement T seen hseen G f placement hf q r he).2
        (h q r he (hseen ⟨q, r, he, Or.inl rfl⟩))


private noncomputable def locate (f : V ↪ N) (seen : Set N) (hs : seen ⊆ Set.range f) :
    seen ↪ V :=
  (⟨Set.inclusion hs, Set.inclusion_injective hs⟩ : seen ↪ Set.range f).trans (Equiv.ofInjective f f.injective).symm.toEmbedding

private theorem locate_inverse (f : V ↪ N) (seen : Set N) (hs : seen ⊆ Set.range f)
    (n : seen) : f (locate f seen hs n) = n.1 :=
  Equiv.apply_ofInjective_symm f.injective ⟨n.1, hs n.2⟩

abbrev Feasible (T : History N) (G : SimpleGraph V)
    (base : V ↪ N) (initial : Set N) :=
  {placement : (initial ∪ revealedNames T : Set N) ↪ V //
    realizes T (initial ∪ revealedNames T) G placement ∧
    ∀ v (h : base v ∈ initial), placement ⟨base v, Or.inl h⟩ = v}

private abbrev Extensions (seen banned : Set N) (placement : seen ↪ V) :=
  {f : V ↪ N // (∀ a : seen, f (placement a) = a.1) ∧
    Disjoint (Set.range f) banned}

private theorem run_world (p : PassiveProtocol N (fun _ => Option (Set N)))
    (G : SimpleGraph V) (f : V ↪ N) :
      runPassiveProtocol readWorld p (G, f) = runPassiveProtocol (nameReply G) p f := by
  induction p with
  | stop => rfl
  | query q next ih =>
    simp only [runPassiveProtocol, readWorld, ih]

private theorem equal_dependent_subtypes {I A : Type*} {P : I → A → Prop}
    (x y : Σ i : I, {a : A // P i a}) (hi : x.1 = y.1) (ha : x.2.1 = y.2.1) :
    x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  cases hi
  obtain rfl : x = y := Subtype.ext ha
  rfl

private noncomputable def transcriptEquiv (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (G : SimpleGraph V)
    (base : V ↪ N) (initial : Set N) (hInit : initial ⊆ Set.range base) :
    let T := runPassiveProtocol readWorld p ref
    {f : V ↪ N // runPassiveProtocol readWorld p (G, f) = T ∧
      ∀ v, base v ∈ initial → f v = base v} ≃
      (Σ a : Feasible T G base initial, Extensions (initial ∪ revealedNames T) (absentNames T) a.1) := by
  classical
  intro T
  let seen := initial ∪ revealedNames T
  have hseen : revealedNames T ⊆ seen := Set.subset_union_right
  let supported (f : V ↪ N) (ht : runPassiveProtocol readWorld p (G, f) = T)
      (ha : ∀ v, base v ∈ initial → f v = base v) : seen ⊆ Set.range f := by
    apply Set.union_subset
    · intro n hn
      obtain ⟨v, hv⟩ := hInit hn
      exact ⟨v, (ha v (hv ▸ hn)).trans hv⟩
    · rw [← ht, run_world]
      exact known_subset_range G p f
  refine {
    toFun := fun f => ?_
    invFun := fun a => ?_
    left_inv := fun f => ?_
    right_inv := fun a => ?_ }
  · let hs := supported f.1 f.2.1 f.2.2
    let a := locate f.1 seen hs
    have ha := locate_inverse f.1 seen hs
    have h := (transcript_iff_feasible p ref G f.1 seen hseen a ha).mp f.2.1
    exact ⟨⟨a, h.1, fun v hv => f.1.injective ((ha _).trans (f.2.2 v hv).symm)⟩,
      ⟨f.1, ha, h.2⟩⟩
  · let f := a.2.1
    refine ⟨f, (transcript_iff_feasible p ref G f seen hseen a.1.1 a.2.2.1).mpr
      ⟨a.1.2.1, a.2.2.2⟩, ?_⟩
    intro v hv
    have h := a.2.2.1 ⟨base v, Or.inl hv⟩
    rw [a.1.2.2 v hv] at h
    exact h
  · apply Subtype.ext
    rfl
  · have hPlacement : locate a.2.1 seen (fun n hn => ⟨a.1.1 ⟨n, hn⟩, a.2.2.1 ⟨n, hn⟩⟩) = a.1.1 := by
      ext n
      exact a.2.1.injective ((locate_inverse _ _ _ n).trans (a.2.2.1 n).symm)
    have hFirst : (⟨locate a.2.1 seen (fun n hn => ⟨a.1.1 ⟨n, hn⟩, a.2.2.1 ⟨n, hn⟩⟩),
      by
        rw [hPlacement]
        exact a.1.2⟩ : Feasible T G base initial) = a.1 := Subtype.ext hPlacement
    exact equal_dependent_subtypes _ _ hFirst rfl

private theorem extension_count [Fintype V] [Fintype N]
    (seen banned : Set N) (place : seen ↪ V) (hDis : Disjoint seen banned) :
    Nat.card (Extensions seen banned place) =
      (Fintype.card N - seen.ncard - banned.ncard).descFactorial
        (Fintype.card V - seen.ncard) := by
  classical
  let K := (Set.range place).toFinite.toFinset
  let A := (seen ∪ banned)ᶜ.toFinite.toFinset
  have hK (v : V) : v ∈ K ↔ v ∈ Set.range place := Set.Finite.mem_toFinset _
  have hA (n : N) : n ∈ A ↔ n ∉ seen ∪ banned := Set.Finite.mem_toFinset _
  let back : K ≃ Set.range place :=
    Equiv.subtypeEquivRight hK
  let named : K ↪ N := back.toEmbedding.trans
    ((Equiv.ofInjective place place.injective).symm.toEmbedding.trans
      (Function.Embedding.subtype (· ∈ seen)))
  have hNamed (n : seen) : named ⟨place n, (hK _).mpr ⟨n, rfl⟩⟩ = n.1 :=
    congrArg Subtype.val (Equiv.ofInjective_symm_apply place.injective n)
  have hPlace (v : K) : ∃ a : seen, place a = v.1 ∧ named v = a.1 := by
    obtain ⟨a, ha⟩ := (hK _).1 v.2
    refine ⟨a, ha, ?_⟩
    have hv : (⟨place a, (hK _).mpr ⟨a, rfl⟩⟩ : K) = v := Subtype.ext ha
    exact hv ▸ hNamed a
  have hSep (v : K) : named v ∉ A := by
    obtain ⟨a, _, ha⟩ := hPlace v
    rw [ha]
    exact fun h => (hA _).1 h (Or.inl a.2)
  have hCandidates (f : V ↪ N) :
      ((∀ a : seen, f (place a) = a.1) ∧ Disjoint (Set.range f) banned) ↔
        (∀ x : K, f x = named x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A := by
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨?_, ?_⟩
      · intro v
        obtain ⟨a, hv, hn⟩ := hPlace v
        exact (congrArg f hv).symm.trans ((ha a).trans hn.symm)
      · intro v
        apply (hA _).mpr
        rintro (hs | hm)
        · let a : seen := ⟨f v, hs⟩
          exact v.2 ((hK _).mpr ⟨a, f.injective (ha a)⟩)
        · exact Set.disjoint_left.mp hb ⟨v.1, rfl⟩ hm
    · rintro ⟨ha, hb⟩
      refine ⟨fun n => (ha ⟨place n, (hK _).mpr ⟨n, rfl⟩⟩).trans (hNamed n), ?_⟩
      rw [Set.disjoint_left]
      rintro n ⟨v, rfl⟩ hn
      by_cases hv : v ∈ K
      · obtain ⟨a, _, hs⟩ := hPlace ⟨v, hv⟩
        have he := (ha ⟨v, hv⟩).trans hs
        exact Set.disjoint_left.mp hDis (he ▸ a.2) hn
      · exact (hA _).mp (hb ⟨v, hv⟩) (Or.inr hn)
  let e : Extensions seen banned place ≃ ({v // v ∉ K} ↪ A) :=
    (Equiv.subtypeEquivRight hCandidates).trans (residualEmbedding K A named hSep)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_coe]
  have hAc : A.card = Fintype.card N - seen.ncard - banned.ncard := by
    change (seen ∪ banned)ᶜ.toFinite.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card, Set.ncard_compl, Set.ncard_union_eq hDis,
      Nat.card_eq_fintype_card, Nat.sub_sub]
  have hKc : K.card = seen.ncard := by
    change (Set.range place).toFinite.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card, Set.ncard_range_of_injective place.injective]
    rfl
  have hLeft : Fintype.card {v // v ∉ K} = Fintype.card V - seen.ncard := by
    rw [← Nat.card_eq_fintype_card]
    change ((K : Set V)ᶜ).ncard = _
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, Set.ncard_coe_finset, hKc]
  rw [hAc, hLeft]

/-- The naming fiber factors into feasible observed placements and their equal-size extensions. -/
theorem transcript_naming_count [Fintype V] [Fintype N]
    (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (G : SimpleGraph V)
    (base : V ↪ N) (initial : Set N) (hInit : initial ⊆ Set.range base)
    (hRef : ∀ v, base v ∈ initial → ref.2 v = base v) :
    let T := runPassiveProtocol readWorld p ref
    let seen := initial ∪ revealedNames T
    let banned := absentNames T
    let bannedCount := banned.ncard
    Nat.card {f : V ↪ N // runPassiveProtocol readWorld p (G, f) = T ∧
      ∀ v, base v ∈ initial → f v = base v} =
      Nat.card (Feasible T G base initial) *
        (Fintype.card N - seen.ncard - bannedCount).descFactorial
          (Fintype.card V - seen.ncard) := by
  classical
  intro T seen banned bannedCount
  have hR : T = runPassiveProtocol (nameReply ref.1) p ref.2 := run_world p ref.1 ref.2
  have hSeen : seen ⊆ Set.range ref.2 := by
    apply Set.union_subset
    · intro n hn
      obtain ⟨v, hv⟩ := hInit hn
      exact ⟨v, (hRef v (hv ▸ hn)).trans hv⟩
    · rw [hR]
      exact known_subset_range ref.1 p ref.2
  have hBanned : Disjoint (Set.range ref.2) banned := by
    change Disjoint (Set.range ref.2) (absentNames T)
    rw [hR]
    exact (same_history_iff_avoids_absent ref.1 p ref.2 ref.2 ∅ (fun _ _ => rfl)).mp rfl
  let : Fintype (Feasible T G base initial) := Fintype.ofFinite _
  rw [Nat.card_congr (transcriptEquiv p ref G base initial hInit), Nat.card_sigma]
  let C := (Fintype.card N - seen.ncard - banned.ncard).descFactorial (Fintype.card V - seen.ncard)
  change (∑ a : Feasible T G base initial, Nat.card (Extensions seen banned a.1)) =
    Nat.card (Feasible T G base initial) * C
  calc
    _ = ∑ _a : Feasible T G base initial, C :=
      Finset.sum_congr rfl (fun a _ => extension_count seen banned a.1 (hBanned.mono_left hSeen))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.cast_id]

private theorem uniform_transcript_mass [Fintype V] [Fintype N]
    (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (G : SimpleGraph V)
    (base : V ↪ N) (initial : Set N) (hInit : initial ⊆ Set.range base)
    (hRef : ∀ v, base v ∈ initial → ref.2 v = base v) :
    let T := runPassiveProtocol readWorld p ref
    let seen := initial ∪ revealedNames T
    let banned := absentNames T
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    let C := (Fintype.card N - seen.ncard - banned.ncard).descFactorial (Fintype.card V - seen.ncard)
    (uniformPmf X).toOuterMeasure {f | runPassiveProtocol readWorld p (G, f.1) = T} =
      (Nat.card (Feasible T G base initial) : ℝ≥0∞) * (↑C / ↑(Nat.card X)) := by
  classical
  intro T seen banned X _ _ C
  let H : Set X := {f | runPassiveProtocol readWorld p (G, f.1) = T}
  let : Fintype H := Fintype.ofFinite H
  let e : H ≃ {f : V ↪ N // runPassiveProtocol readWorld p (G, f) = T ∧
      ∀ v, base v ∈ initial → f v = base v} :=
    { toFun := fun f => ⟨f.1.1, f.2, f.1.2⟩
      invFun := fun f => ⟨⟨f.1, f.2.2⟩, f.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (uniformPmf X).toOuterMeasure H = _
  rw [uniformPmf_toOuterMeasure_apply, ← Nat.card_eq_fintype_card (α := H),
    ← Nat.card_eq_fintype_card (α := X), Nat.card_congr e]
  have hc := transcript_naming_count p ref G base initial hInit hRef
  change Nat.card {f : V ↪ N // runPassiveProtocol readWorld p (G, f) = T ∧
      ∀ v, base v ∈ initial → f v = base v} = Nat.card (Feasible T G base initial) * C at hc
  rw [hc, Nat.cast_mul, mul_div_assoc]

/-- The transcript posterior weights each graph prior mass by its compatible placements. -/
theorem graph_posterior [Fintype V] [Fintype N]
    {W : Type*} (π : PMF W) (graph : W → SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (base : V ↪ N)
    (initial : Set N) (hInit : initial ⊆ Set.range base)
    (hRef : ∀ v, base v ∈ initial → ref.2 v = base v) :
    let T := runPassiveProtocol readWorld p ref
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    let μ : PMF (W × X) := π.bind fun w => (uniformPmf X).map (Prod.mk w)
    let H : Set (W × X) := {x | runPassiveProtocol readWorld p (graph x.1, x.2.1) = T}
    let weight (w : W) : ℝ≥0∞ := π w * ↑(Nat.card (Feasible T (graph w) base initial))
    μ.toOuterMeasure H ≠ 0 →
      ∀ w, μ.toOuterMeasure (H ∩ {x | x.1 = w}) / μ.toOuterMeasure H =
        weight w / ∑' u, weight u := by
  classical
  intro T X _ _ μ H weight hPos w
  let seen := initial ∪ revealedNames T
  let banned := absentNames T
  let C := (Fintype.card N - seen.ncard - banned.ncard).descFactorial (Fintype.card V - seen.ncard)
  let c : ℝ≥0∞ := ↑C / ↑(Nat.card X)
  have hMass (u : W) :
      (uniformPmf X).toOuterMeasure {f | runPassiveProtocol readWorld p (graph u, f.1) = T} =
        ↑(Nat.card (Feasible T (graph u) base initial)) * c :=
    uniform_transcript_mass p ref (graph u) base initial hInit hRef
  have hAll : μ.toOuterMeasure H = (∑' u, weight u) * c := by
    change (π.bind fun u => (uniformPmf X).map (Prod.mk u)).toOuterMeasure H = _
    rw [PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro u
    rw [PMF.toOuterMeasure_map_apply]
    change π u * (uniformPmf X).toOuterMeasure
      {f | runPassiveProtocol readWorld p (graph u, f.1) = T} = _
    rw [hMass, mul_assoc]
  have hSingle : μ.toOuterMeasure (H ∩ {x | x.1 = w}) = weight w * c := by
    change (π.bind fun u => (uniformPmf X).map (Prod.mk u)).toOuterMeasure _ = _
    rw [PMF.toOuterMeasure_bind_apply, ← tsum_ite_eq w (fun u => weight u * c)]
    apply tsum_congr
    intro u
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hu : u = w
    · rw [ite_eq_left hu]
      have he : (Prod.mk u) ⁻¹' (H ∩ {x | x.1 = w}) =
          {f : X | runPassiveProtocol readWorld p (graph u, f.1) = T} := by
        ext f
        change (runPassiveProtocol readWorld p (graph u, f.1) = T ∧ u = w) ↔
          runPassiveProtocol readWorld p (graph u, f.1) = T
        simp only [hu, and_true]
      rw [he, hMass, mul_assoc]
    · rw [ite_eq_right hu]
      have he : (Prod.mk u) ⁻¹' (H ∩ {x | x.1 = w}) = (∅ : Set X) := by
        ext f
        change (_ ∧ u = w) ↔ False
        simp only [hu, and_false]
      rw [he, MeasureTheory.measure_empty, mul_zero]
  have hc : c ≠ 0 := by
    intro h
    exact hPos (by rw [hAll, h, mul_zero])
  have hct : c ≠ ∞ := by
    have hX : Nat.card X ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr hX)
  rw [hAll, hSingle, ENNReal.mul_div_mul_right _ _ hc hct]

end D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
