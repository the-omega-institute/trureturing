/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform enabled moves have the history law of scanning a uniform ranking under every free-color policy. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.TreeDecomposition

section

namespace CayleyScheduler

open SimpleGraph

universe u w
variable {V : Type u} {K : Type w}

/-- The graph of edges whose endpoints currently have the same color. -/
def conflict (G : SimpleGraph V) (color : V → K) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ color v = color w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- Restrict a conflict graph to the vertices that have yet to move. -/
def active (G : SimpleGraph V) (live : Set V) : SimpleGraph V where
  Adj v w := v ∈ live ∧ w ∈ live ∧ G.Adj v w
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.ne rfl⟩

def Enabled (G : SimpleGraph V) (live : Set V) (v : V) : Prop :=
  ∃ w, (active G live).Adj v w

private theorem recolor_conflict [DecidableEq V] (G : SimpleGraph V) (color : V → K)
    (v : V) (new : K) (free : ∀ w, G.Adj v w → new ≠ color w) :
    conflict G (Function.update color v new) =
      active (conflict G color) ({v}ᶜ : Set V) := by
  ext x y
  change (G.Adj x y ∧ Function.update color v new x = Function.update color v new y) ↔
    (x ≠ v ∧ y ≠ v ∧ G.Adj x y ∧ color x = color y)
  by_cases hx : x = v
  · subst x
    constructor
    · rintro ⟨ha, hc⟩
      rw [Function.update_self, Function.update_of_ne ha.ne.symm] at hc
      exact (free _ ha hc).elim
    · simp
  · by_cases hy : y = v
    · subst y
      constructor
      · rintro ⟨ha, hc⟩
        rw [Function.update_of_ne hx, Function.update_self] at hc
        exact (free _ ha.symm hc.symm).elim
      · simp
    · simp [hx, hy, Function.update_of_ne]

private theorem active_delete (G : SimpleGraph V) (live : Set V) (v : V) :
    active (active G live) ({v}ᶜ : Set V) = active G (live \ {v}) := by
  ext x y
  change (x ≠ v ∧ y ≠ v ∧ x ∈ live ∧ y ∈ live ∧ G.Adj x y) ↔
    ((x ∈ live ∧ x ≠ v) ∧ (y ∈ live ∧ y ≠ v) ∧ G.Adj x y)
  tauto

/-- Every step of a legal sequential recoloring. The free color can vary with the entire history. -/
inductive LegalRun [DecidableEq V] (G : SimpleGraph V) :
    (V → K) → List V → (V → K) → Prop where
  | nil (color) : LegalRun G color [] color
  | cons {color final : V → K} {v : V} {tail : List V} {new : K}
      (enabled : ∃ w, (conflict G color).Adj v w)
      (free : ∀ w, G.Adj v w → new ≠ color w)
      (rest : LegalRun G (Function.update color v new) tail final) :
      LegalRun G color (v :: tail) final

private theorem legalRun_conflicts [DecidableEq V] (G : SimpleGraph V) {color final : V → K}
    {history : List V} (run : LegalRun G color history final) :
    conflict G final = active (conflict G color) {v | v ∉ history} := by
  induction run with
  | nil color =>
    ext v w
    simp [active]
  | @cons color final v tail new enabled free rest ih =>
    rw [ih, recolor_conflict G color v new free]
    ext x y
    change (x ∉ tail ∧ y ∉ tail ∧ x ≠ v ∧ y ≠ v ∧ (conflict G color).Adj x y) ↔
      (x ∉ v :: tail ∧ y ∉ v :: tail ∧ (conflict G color).Adj x y)
    simp only [List.mem_cons, not_or]
    tauto

def First {ι : Type*} [LT ι] (G : SimpleGraph V) (rank : V → ι)
    (live : Set V) (v : V) : Prop :=
  Enabled G live v ∧ ∀ w, Enabled G live w → w ≠ v → rank v < rank w

inductive Prefix {ι : Type*} [LT ι] (G : SimpleGraph V) (rank : V → ι) :
    Set V → List V → Prop where
  | nil (live) : Prefix G rank live []
  | cons {live : Set V} {v : V} {tail : List V}
      (first : First G rank live v) (rest : Prefix G rank (live \ {v}) tail) :
      Prefix G rank live (v :: tail)

def remaining (live : Set V) (history : List V) : Set V :=
  {v | v ∈ live ∧ v ∉ history}

@[simp] theorem remaining_nil (live : Set V) : remaining live [] = live := by
  ext v
  simp [remaining]

private theorem remaining_cons (live : Set V) (v : V) (tail : List V) :
    remaining live (v :: tail) = remaining (live \ {v}) tail := by
  ext w
  simp [remaining, and_assoc, ← not_or]

private theorem remaining_subset (live : Set V) (history : List V) :
    remaining live history ⊆ live :=
  fun _ h => h.1

private theorem remaining_not_head (live : Set V) (v : V) (tail : List V) :
    v ∉ remaining live (v :: tail) := by
  simp [remaining]

private theorem enabled_mono {G : SimpleGraph V} {A B : Set V} (h : A ⊆ B) {v : V}
    (hv : Enabled G A v) : Enabled G B v := by
  obtain ⟨w, hv, hw, he⟩ := hv
  exact ⟨w, h hv, h hw, he⟩

private theorem prefix_snoc_iff {ι : Type*} [LT ι] (G : SimpleGraph V) (rank : V → ι)
    (live : Set V) (history : List V) (v : V) :
    Prefix G rank live (history ++ [v]) ↔
      Prefix G rank live history ∧ First G rank (remaining live history) v := by
  induction history generalizing live with
  | nil =>
    simp only [List.nil_append, remaining_nil]
    constructor
    · intro h
      cases h with
      | cons hf _ => exact ⟨.nil _, hf⟩
    · exact fun h => .cons h.2 (.nil _)
  | cons x tail ih =>
    rw [remaining_cons]
    change Prefix G rank live (x :: (tail ++ [v])) ↔ _
    constructor
    · intro h
      cases h with
      | cons hf hr =>
        obtain ⟨hp, hn⟩ := (ih (live \ {x})).mp hr
        exact ⟨.cons hf hp, hn⟩
    · rintro ⟨h, hn⟩
      cases h with
      | cons hf hr => exact .cons hf ((ih (live \ {x})).mpr ⟨hr, hn⟩)

def Moves {ι : Type*} [LT ι] (G : SimpleGraph V) (rank : V → ι)
    (live : Set V) (v : V) : Prop :=
  ∃ w, (active G live).Adj v w ∧ rank v < rank w

private theorem moves_delete_first {ι : Type*} [LinearOrder ι] (G : SimpleGraph V) (rank : V → ι)
    {live : Set V} {v x : V} (first : First G rank live x) :
    Moves G rank live v ↔ v = x ∨ Moves G rank (live \ {x}) v := by
  have hxx : Moves G rank live x := by
    obtain ⟨w, hw⟩ := first.1
    exact ⟨w, hw, first.2 w ⟨x, hw.symm⟩ hw.ne.symm⟩
  constructor
  · rintro ⟨w, hv, hlt⟩
    by_cases he : v = x
    · exact Or.inl he
    · have hw : w ≠ x := by
        intro h
        subst w
        exact (not_lt_of_gt (first.2 v ⟨x, hv⟩ he)) hlt
      exact Or.inr ⟨w, ⟨⟨hv.1, he⟩, ⟨hv.2.1, hw⟩, hv.2.2⟩, hlt⟩
  · rintro (rfl | ⟨w, hw, hlt⟩)
    · exact hxx
    · exact ⟨w, ⟨hw.1.1, hw.2.1.1, hw.2.2⟩, hlt⟩

private theorem prefix_pathwise {ι : Type*} [LinearOrder ι] {G : SimpleGraph V} {rank : V → ι}
    {live : Set V} {history : List V} (h : Prefix G rank live history)
    (stop : ∀ v, ¬ Enabled G (remaining live history) v) :
    history.Nodup ∧ ∀ v, v ∈ history ↔ Moves G rank live v := by
  induction h with
  | nil live =>
    rw [remaining_nil] at stop
    refine ⟨.nil, fun v => ?_⟩
    simpa only [List.not_mem_nil, false_iff] using
      (fun (hx : Moves G rank live v) => stop v ⟨hx.choose, hx.choose_spec.1⟩)
  | @cons live x tail first rest ih =>
    rw [remaining_cons] at stop
    obtain ⟨hn, hm⟩ := ih stop
    refine ⟨List.nodup_cons.mpr ⟨fun hb => ?_, hn⟩, fun v => ?_⟩
    · obtain ⟨w, hw, _⟩ := (hm x).mp hb
      exact hw.1.2 rfl
    · rw [List.mem_cons, hm, moves_delete_first G rank first]

private theorem pathwise_count [Fintype V] {ι : Type*} [LinearOrder ι]
    {G : SimpleGraph V} {rank : V → ι} {history : List V}
    (h : Prefix G rank Set.univ history)
    (stop : ∀ v, ¬ Enabled G (remaining Set.univ history) v) :
    history.length = CayleyProbe.filterCard (Moves G rank Set.univ) := by
  classical
  obtain ⟨hn, hm⟩ := prefix_pathwise h stop
  have he : history.toFinset = Finset.univ.filter (Moves G rank Set.univ) := by
    ext v
    simp [hm]
  unfold CayleyProbe.filterCard
  rw [← he, List.toFinset_card_of_nodup hn]

/-- Swapping two vertices still enabled after a prefix does not affect that prefix. -/
private theorem prefix_swap {ι : Type*} [LinearOrder ι] [DecidableEq V]
    {G : SimpleGraph V} {rank : V → ι} {live : Set V} {history : List V} {a b : V}
    (ha : Enabled G (remaining live history) a)
    (hb : Enabled G (remaining live history) b)
    (h : Prefix G rank live history) :
    Prefix G (rank ∘ Equiv.swap a b) live history := by
  induction h with
  | nil live => exact .nil _
  | @cons live x tail first rest ih =>
    have hax : a ≠ x := by
      intro e
      subst a
      obtain ⟨w, hw⟩ := ha
      exact remaining_not_head live x tail hw.1
    have hbx : b ≠ x := by
      intro e
      subst b
      obtain ⟨w, hw⟩ := hb
      exact remaining_not_head live x tail hw.1
    refine .cons ⟨first.1, fun w hw hwx => ?_⟩ (ih
      (remaining_cons live x tail ▸ ha) (remaining_cons live x tail ▸ hb))
    have hfix : Equiv.swap a b x = x :=
      Equiv.swap_apply_of_ne_of_ne hax.symm hbx.symm
    change rank (Equiv.swap a b x) < rank (Equiv.swap a b w)
    rw [hfix]
    apply first.2
    · by_cases hwa : w = a
      · subst w
        rw [Equiv.swap_apply_left]
        exact enabled_mono (remaining_subset _ _) hb
      · by_cases hwb : w = b
        · subst w
          rw [Equiv.swap_apply_right]
          exact enabled_mono (remaining_subset _ _) ha
        · rwa [Equiv.swap_apply_of_ne_of_ne hwa hwb]
    · exact fun he => hwx ((Equiv.swap a b).injective (he.trans hfix.symm))

private theorem first_swap {ι : Type*} [LinearOrder ι] [DecidableEq V]
    {G : SimpleGraph V} {rank : V → ι} {live : Set V} {a b : V}
    (ha : First G rank live a) (hb : Enabled G live b) :
    First G (rank ∘ Equiv.swap a b) live b := by
  refine ⟨hb, fun w hw hwb => ?_⟩
  change rank (Equiv.swap a b b) < rank (Equiv.swap a b w)
  rw [Equiv.swap_apply_right]
  apply ha.2
  · by_cases hwa : w = a
    · subst w
      simpa only [Equiv.swap_apply_left] using hb
    · rwa [Equiv.swap_apply_of_ne_of_ne hwa hwb]
  · exact fun he => hwb ((Equiv.swap a b).injective (he.trans (Equiv.swap_apply_right a b).symm))

section FiniteRanking

variable [Fintype V] [LinearOrder V]

private theorem existsUnique_first (G : SimpleGraph V) (rank : V ≃ V) (live : Set V)
    (hne : ∃ v, Enabled G live v) : ∃! v, First G rank live v := by
  classical
  let S := Finset.univ.filter (Enabled G live)
  have hne' : S.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S rank hne'
  have hfirst : First G rank live v := by
    refine ⟨(Finset.mem_filter.mp hv).2, fun w hw hne => ?_⟩
    apply lt_of_le_of_ne (hmin w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩))
    exact fun he => hne (rank.injective he.symm)
  exact ⟨v, hfirst, fun w hw => by
    by_contra hne
    exact (not_lt_of_gt (hfirst.2 w hw.1 hne)) (hw.2 v hfirst.1 (Ne.symm hne))⟩

/-- The exact finite set of rankings compatible with a history. -/
abbrev HistoryRank (G : SimpleGraph V) (live : Set V) (history : List V) :=
  {rank : Equiv.Perm V // Prefix G rank live history}

abbrev NextRank (G : SimpleGraph V) (live : Set V) (history : List V) (v : V) :=
  {rank : Equiv.Perm V // Prefix G rank live history ∧
    First G rank (remaining live history) v}

private noncomputable def swapNextRank (G : SimpleGraph V) (live : Set V) (history : List V)
    {a b : V} (ha : Enabled G (remaining live history) a)
    (hb : Enabled G (remaining live history) b) :
    NextRank G live history a ≃ NextRank G live history b where
  toFun rank := ⟨(Equiv.swap a b).trans rank.val,
    prefix_swap ha hb rank.prop.1, first_swap rank.prop.2 hb⟩
  invFun rank := ⟨(Equiv.swap b a).trans rank.val,
    prefix_swap hb ha rank.prop.1, first_swap rank.prop.2 ha⟩
  left_inv rank := by
    apply Subtype.ext
    ext v
    change rank.val (Equiv.swap a b (Equiv.swap b a v)) = rank.val v
    rw [Equiv.swap_comm b a, Equiv.swap_apply_self]
  right_inv rank := by
    apply Subtype.ext
    ext v
    change rank.val (Equiv.swap b a (Equiv.swap a b v)) = rank.val v
    rw [Equiv.swap_comm a b, Equiv.swap_apply_self]

private noncomputable def historyRankDecomp (G : SimpleGraph V) (live : Set V) (history : List V)
    (hne : ∃ v, Enabled G (remaining live history) v) :
    HistoryRank G live history ≃
      Σ v : {v // Enabled G (remaining live history) v}, NextRank G live history v.val := by
  classical
  let choose (rank : Equiv.Perm V) := (existsUnique_first G rank _ hne).exists.choose
  have spec (rank : Equiv.Perm V) : First G rank _ (choose rank) :=
    (existsUnique_first G rank _ hne).exists.choose_spec
  refine
    { toFun := fun r => ⟨⟨choose r.val, (spec r.val).1⟩, ⟨r.val, r.prop, spec r.val⟩⟩
      invFun := fun r => ⟨r.2.val, r.2.prop.1⟩
      left_inv := fun _ => rfl
      right_inv := ?_ }
  rintro ⟨⟨v, hv⟩, rank, hp, hf⟩
  have eq : v = choose rank := (existsUnique_first G rank _ hne).unique hf (spec rank)
  subst v
  rfl

/-- For a uniform ranking, every enabled next vertex has conditional mass one over the
size of the enabled set, whenever the prefix has positive mass. This integer identity also
covers zero-mass prefixes. -/
private theorem uniform_next_fibers (G : SimpleGraph V) (live : Set V) (history : List V)
    {v : V} (hv : Enabled G (remaining live history) v) :
    Nat.card (HistoryRank G live (history ++ [v])) *
      Nat.card {w // Enabled G (remaining live history) w} =
      Nat.card (HistoryRank G live history) := by
  classical
  let A := {w // Enabled G (remaining live history) w}
  let e : HistoryRank G live (history ++ [v]) ≃ NextRank G live history v :=
    Equiv.subtypeEquivRight (fun rank => prefix_snoc_iff G rank live history v)
  let f : (Σ w : A, NextRank G live history w.val) ≃ A × NextRank G live history v :=
    (Equiv.sigmaCongrRight fun w => swapNextRank G live history w.prop hv).trans
      (Equiv.sigmaEquivProd A (NextRank G live history v))
  rw [Nat.card_congr e, Nat.card_congr ((historyRankDecomp G live history ⟨v, hv⟩).trans f),
    Nat.card_prod, Nat.mul_comm]

end FiniteRanking

end CayleyScheduler

end

section

namespace CayleyScheduler

open SimpleGraph

universe u w
variable {V : Type u} {K : Type w} [Fintype V] [LinearOrder V]

def Stop (G : SimpleGraph V) (live : Set V) : Prop :=
  ∀ v, ¬ Enabled G live v

def Complete (G : SimpleGraph V) (rank : Equiv.Perm V) (live : Set V) (history : List V) : Prop :=
  Prefix G rank live history ∧ Stop G (remaining live history)

omit [Fintype V] in
private theorem first_unique {G : SimpleGraph V} {rank : Equiv.Perm V} {live : Set V} {a b : V}
    (ha : First G rank live a) (hb : First G rank live b) : a = b := by
  by_contra hn
  exact (not_lt_of_gt (ha.2 b hb.1 (Ne.symm hn))) (hb.2 a ha.1 hn)

private theorem exists_complete (G : SimpleGraph V) (rank : Equiv.Perm V) (live : Set V) :
    ∃ history, Complete G rank live history := by
  classical
  let size (s : Set V) := Nat.card s
  induction n : size live using Nat.strong_induction_on generalizing live with
  | h n ih =>
    by_cases hs : Stop G live
    · exact ⟨[], .nil _, by rwa [remaining_nil]⟩
    · have he : ∃ v, Enabled G live v := by
        simpa [Stop] using hs
      obtain ⟨v, hv, _⟩ := existsUnique_first G rank live he
      have hmem : v ∈ live := hv.1.choose_spec.1
      have hsize : size (live \ {v}) < size live := by
        let fL : Fintype (live \ {v} : Set V) := Fintype.ofFinite _
        let fR : Fintype live := Fintype.ofFinite _
        let e : (live \ {v} : Set V) → live := fun x => ⟨x.val,x.prop.1⟩
        have h := Fintype.card_lt_of_injective_not_surjective e
          (fun _ _ eq => Subtype.ext (congrArg (fun x : live => x.val) eq)) (fun surj => by
            obtain ⟨x,hx⟩ := surj ⟨v,hmem⟩
            exact x.prop.2 (congrArg (fun x : live => x.val) hx))
        change Nat.card (live \ {v} : Set V) < Nat.card live
        rw [@Nat.card_eq_fintype_card (live \ {v} : Set V) fL,
          @Nat.card_eq_fintype_card live fR]
        exact h
      obtain ⟨tail, hp, ht⟩ := ih _ (n ▸ hsize) _ rfl
      exact ⟨v :: tail, .cons hv hp, by rwa [remaining_cons]⟩

omit [Fintype V] in
private theorem complete_unique {G : SimpleGraph V} {rank : Equiv.Perm V} {live : Set V}
    {l l' : List V} (h : Complete G rank live l) (h' : Complete G rank live l') :
    l = l' := by
  obtain ⟨pr, stop⟩ := h
  induction pr generalizing l' with
  | nil live =>
    rw [remaining_nil] at stop
    cases h'.1 with
    | nil => rfl
    | cons hf _ => exact (stop _ hf.1).elim
  | @cons live v tail hv _ ih =>
    rw [remaining_cons] at stop
    obtain ⟨pr', stop'⟩ := h'
    cases pr' with
    | nil =>
      rw [remaining_nil] at stop'
      exact (stop' v hv.1).elim
    | @cons _ w tail' hw ht' =>
      have he := first_unique hv hw
      subst w
      rw [remaining_cons] at stop'
      exact congrArg (List.cons v) (ih ⟨ht',stop'⟩ stop)

noncomputable def rankedHistory (G : SimpleGraph V) (rank : Equiv.Perm V) (live : Set V) : List V :=
  (exists_complete G rank live).choose

theorem rankedHistory_spec (G : SimpleGraph V) (rank : Equiv.Perm V) (live : Set V) :
    Complete G rank live (rankedHistory G rank live) :=
  (exists_complete G rank live).choose_spec

/-- A policy can depend on the ordered mover history and the entire current coloring. An
external tape can be fixed as a parameter of such a policy. -/
def FreePolicy (G : SimpleGraph V) :=
  (past : List V) → (color : V → K) → (v : V) → (∃ w, (conflict G color).Adj v w) →
    {new : K // ∀ w, G.Adj v w → new ≠ color w}

/-- The consecutive choices that have positive probability for the random central daemon. -/
def LegalPrefix (G : SimpleGraph V) (live : Set V) (l : List V) : Prop :=
  List.recOn (motive := fun _ => Set V → Prop) l (fun _ => True)
    (fun v _ rec alive => Enabled G alive v ∧ rec (alive \ {v})) live

/-- On a legal prefix, the probability is one over the product of the enabled-set sizes. -/
noncomputable def choiceProduct (G : SimpleGraph V) (live : Set V) (l : List V) : Nat :=
  List.recOn (motive := fun _ => Set V → Nat) l (fun _ => 1)
    (fun v _ rec alive => Nat.card {w // Enabled G alive w} * rec (alive \ {v})) live

omit [Fintype V] [LinearOrder V] in
private theorem legalPrefix_snoc (G : SimpleGraph V) (live : Set V) (l : List V) (v : V) :
    LegalPrefix G live (l ++ [v]) ↔ LegalPrefix G live l ∧ Enabled G (remaining live l) v := by
  induction l generalizing live with
  | nil => simp [LegalPrefix]
  | cons x tail ih =>
    rw [remaining_cons]
    change (Enabled G live x ∧ LegalPrefix G (live \ {x}) (tail ++ [v])) ↔ _
    rw [ih]
    exact and_assoc.symm

omit [Fintype V] [LinearOrder V] in
private theorem choiceProduct_snoc (G : SimpleGraph V) (live : Set V) (l : List V) (v : V) :
    choiceProduct G live (l ++ [v]) =
      choiceProduct G live l * Nat.card {w // Enabled G (remaining live l) w} := by
  induction l generalizing live with
  | nil => simp [choiceProduct]
  | cons x tail ih =>
    rw [remaining_cons]
    change Nat.card {w // Enabled G live w} * choiceProduct G (live \ {x}) (tail ++ [v]) =
      (Nat.card {w // Enabled G live w} * choiceProduct G (live \ {x}) tail) * _
    rw [ih, Nat.mul_assoc]

omit [Fintype V] in
theorem Prefix.legal {G : SimpleGraph V} {rank : Equiv.Perm V} {live : Set V} {l : List V}
    (h : Prefix G rank live l) : LegalPrefix G live l := by
  induction h with
  | nil => trivial
  | cons hf _ ih => exact ⟨hf.1, ih⟩

private theorem uniform_prefix_product (G : SimpleGraph V) (live : Set V) (history : List V)
    (h : LegalPrefix G live history) :
    Nat.card (HistoryRank G live history) * choiceProduct G live history =
      Nat.card (Equiv.Perm V) := by
  classical
  induction history using List.reverseRecOn with
  | nil =>
    let e : HistoryRank G live [] ≃ Equiv.Perm V :=
      Equiv.subtypeUnivEquiv (fun _ => Prefix.nil live)
    rw [Nat.card_congr e]
    exact Nat.mul_one _
  | append_singleton tail v ih =>
    obtain ⟨hp,hv⟩ := (legalPrefix_snoc G live tail v).mp h
    rw [choiceProduct_snoc, Nat.mul_left_comm, uniform_next_fibers G live tail hv]
    exact (Nat.mul_comm _ _).trans (ih hp)

/-- Exact terminal-history law, expressed in natural counts. For each legal terminal history,
the uniform-ranking fiber fraction equals the product of reciprocal enabled-set sizes.
Every other history has an empty fiber. -/
private theorem complete_history_law (G : SimpleGraph V) (live : Set V) (history : List V) :
    (LegalPrefix G live history ∧ Stop G (remaining live history) →
      Nat.card {rank : Equiv.Perm V // rankedHistory G rank live = history} *
        choiceProduct G live history = Nat.card (Equiv.Perm V)) ∧
    (¬ (LegalPrefix G live history ∧ Stop G (remaining live history)) →
      IsEmpty {rank : Equiv.Perm V // rankedHistory G rank live = history}) := by
  constructor
  · rintro ⟨hl,hs⟩
    let e : HistoryRank G live history ≃ {rank : Equiv.Perm V // rankedHistory G rank live = history} :=
      Equiv.subtypeEquivRight fun rank => by
        constructor
        · intro hp
          exact complete_unique ⟨hp,hs⟩ (rankedHistory_spec G rank live) |>.symm
        · intro he
          exact he ▸ (rankedHistory_spec G rank live).1
    rw [← Nat.card_congr e]
    exact uniform_prefix_product G live history hl
  · intro h
    refine ⟨?_⟩
    rintro ⟨rank, hr⟩
    have hc : Complete G rank live history := hr ▸ rankedHistory_spec G rank live
    exact h ⟨hc.1.legal, hc.2⟩

omit [Fintype V] in
private theorem moves_iff_not_peak (G : SimpleGraph V) (rank : Equiv.Perm V) (v : V) :
    Moves G rank Set.univ v ↔ ¬ (∀ w, G.Adj v w → rank w < rank v) := by
  classical
  constructor
  · rintro ⟨w, h, hlt⟩ hp
    exact (lt_asymm hlt (hp w h.2.2))
  · intro hn
    push Not at hn
    obtain ⟨w, ha, hle⟩ := hn
    refine ⟨w, ⟨Set.mem_univ _, Set.mem_univ _, ha⟩,
      lt_of_le_of_ne hle (fun he => ha.ne (rank.injective he))⟩

theorem ranked_moves_complement (G : SimpleGraph V) (rank : Equiv.Perm V) :
    (rankedHistory G rank Set.univ).length =
      Fintype.card V - CayleyProbe.filterCard (fun v => ∀ w, G.Adj v w → rank w < rank v) := by
  classical
  obtain ⟨hp, hs⟩ := rankedHistory_spec G rank Set.univ
  rw [pathwise_count hp hs]
  let P (v : V) := ∀ w, G.Adj v w → rank w < rank v
  have he : (Finset.univ.filter (Moves G rank Set.univ)) = (Finset.univ.filter P)ᶜ := by
    ext v
    simp [P, moves_iff_not_peak]
  unfold CayleyProbe.filterCard
  rw [he, Finset.card_compl]
  congr 2
  ext v
  simp [P]

end CayleyScheduler

end

section

namespace CayleyScheduler

open SimpleGraph

universe u w
variable {V : Type u} {K : Type w}

/-- A trace following the specified free-color policy, with the past mover list as state. -/
inductive PolicyRun [DecidableEq V] (G : SimpleGraph V) (policy : FreePolicy (K := K) G) :
    List V → (V → K) → List V → (V → K) → Prop where
  | nil (past) (color) : PolicyRun G policy past color [] color
  | cons {past : List V} {color final : V → K} {v : V} {tail : List V}
      (enabled : ∃ w, (conflict G color).Adj v w)
      (rest : PolicyRun G policy (past ++ [v])
        (Function.update color v (policy past color v enabled).val) tail final) :
      PolicyRun G policy past color (v :: tail) final

private theorem PolicyRun.legal [DecidableEq V] {G : SimpleGraph V} {policy : FreePolicy (K := K) G}
    {past history : List V} {init final : V → K}
    (run : PolicyRun G policy past init history final) : LegalRun G init history final := by
  induction run with
  | nil past color => exact .nil color
  | cons he _ ih => exact .cons he (policy _ _ _ he).prop ih

private theorem policyRun_iff [DecidableEq V] (G : SimpleGraph V) (policy : FreePolicy (K := K) G)
    (H : SimpleGraph V) (history : List V) (alive : Set V)
    (init : V → K) (hc : conflict G init = active H alive) (past : List V) :
    LegalPrefix H alive history ↔
      ∃ final, PolicyRun G policy past init history final ∧
        conflict G final = active H (remaining alive history) := by
  induction history generalizing alive init past with
  | nil =>
    constructor
    · intro _
      exact ⟨init, .nil _ _, by rwa [remaining_nil]⟩
    · intro _
      trivial
  | cons v tail ih =>
    change (Enabled H alive v ∧ LegalPrefix H (alive \ {v}) tail) ↔ _
    rw [remaining_cons]
    constructor
    · rintro ⟨he, htail⟩
      have he' : ∃ w, (conflict G init).Adj v w := hc.symm ▸ he
      let new := policy past init v he'
      have hn : conflict G (Function.update init v new.val) = active H (alive \ {v}) := by
        rw [recolor_conflict G init v new.val new.prop, hc, active_delete]
      obtain ⟨final,run,hfinal⟩ := (ih _ _ hn _).mp htail
      exact ⟨final, .cons he' run, hfinal⟩
    · rintro ⟨final,run,hfinal⟩
      cases run with
      | cons he rest =>
        have he' : ∃ w, (active H alive).Adj v w := hc ▸ he
        refine ⟨he', ?_⟩
        have hn : conflict G (Function.update init v (policy past init v he).val) =
            active H (alive \ {v}) := by
          rw [recolor_conflict G init v _ (policy past init v he).prop, hc, active_delete]
        exact (ih _ _ hn _).mpr ⟨final,rest,hfinal⟩

theorem proper_policyRun [DecidableEq V] (G : SimpleGraph V) (policy : FreePolicy (K := K) G)
    (init : V → K) (history : List V) :
    (LegalPrefix (conflict G init) Set.univ history ∧
      Stop (conflict G init) (remaining Set.univ history)) ↔
    ∃ final, PolicyRun G policy [] init history final ∧ ∀ v w, ¬ (conflict G final).Adj v w := by
  have hc : conflict G init = active (conflict G init) Set.univ := by
    ext v w
    simp [active]
  constructor
  · rintro ⟨hl,hs⟩
    obtain ⟨final,run,hf⟩ := (policyRun_iff G policy _ history _ init hc []).mp hl
    exact ⟨final,run,fun v w h => hs v ⟨w,hf ▸ h⟩⟩
  · rintro ⟨final,run,hproper⟩
    have hf := legalRun_conflicts G run.legal
    have he : conflict G final = active (conflict G init) (remaining Set.univ history) := by
      rw [hf]
      congr 1
      ext v
      simp [remaining]
    exact ⟨(policyRun_iff G policy _ history _ init hc []).mpr ⟨final,run,he⟩,
      fun v ⟨w,ha⟩ => hproper v w (he.symm ▸ ha)⟩

variable [Fintype V] [LinearOrder V]

/-- The exact terminal mass for the original color-update process with the given policy. At
each enabled step the scheduler chooses uniformly. The resulting probability is the uniform
ranking fiber proportion for every ordered history, including the empty history. -/
theorem policy_terminal_law (G : SimpleGraph V) (policy : FreePolicy (K := K) G)
    (init : V → K) (history : List V) :
    let accept := ∃ final, PolicyRun G policy [] init history final ∧
      ∀ v w, ¬ (conflict G final).Adj v w
    let chosen := {rank : Equiv.Perm V //
      rankedHistory (conflict G init) rank Set.univ = history}
    (accept → Nat.card chosen * choiceProduct (conflict G init) Set.univ history =
      Nat.card (Equiv.Perm V)) ∧
    (¬ accept → IsEmpty chosen) := by
  have h := complete_history_law (conflict G init) Set.univ history
  rw [proper_policyRun G policy init history] at h
  exact h

end CayleyScheduler

end
