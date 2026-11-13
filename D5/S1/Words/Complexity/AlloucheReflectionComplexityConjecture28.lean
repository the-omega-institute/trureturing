/- GID: D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Linear factor complexity implies bounded integer reflection differences. -/

/-
result: proof_shape: content; escape_witness: none.
admission_basis: open-problem-resolution (#24159; Proved)
Direct frozen dependencies: MorseHedlund.wordFactor, wordFactorSet, mem_wordFactorSet.
The exact marked mirror and finite weighted factor graphs prove the full bounded-difference claim.
Automaticity and optimal bounds are separate questions.
-/

import D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
import D5.S1.Words.Complexity.MorseHedlund

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Graph
variable {V E : Type*}

private inductive EdgeWalk (src dst : E → V) (H : Finset E) (a : V) : V → Type _
  | nil : EdgeWalk src dst H a a
  | snoc {b : V} (p : EdgeWalk src dst H a b) (e : E) (he : e ∈ H)
      (hs : src e = b) : EdgeWalk src dst H a (dst e)

namespace EdgeWalk
variable {src dst : E → V} {H : Finset E} {a b c : V}

private def edges : {b : V} → EdgeWalk src dst H a b → List E
  | _, .nil => []
  | _, .snoc p e _ _ => p.edges ++ [e]

private def vertices (p : EdgeWalk src dst H a b) : List V := a :: p.edges.map dst

@[simp] private theorem vertices_snoc (p : EdgeWalk src dst H a b) (e : E) (he : e ∈ H) (hs : src e = b) :
    (p.snoc e he hs).vertices = p.vertices ++ [dst e] := by simp [vertices, edges]

private theorem mem_edges (p : EdgeWalk src dst H a b) {e : E} (he : e ∈ p.edges) : e ∈ H := by
  induction p with
  | nil => simp [edges] at he
  | snoc p f hf hs ih =>
    simp only [edges, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ih he
    · exact hf

private theorem prefix_at_vertex (p : EdgeWalk src dst H a b) {v : V} (hv : v ∈ p.vertices) :
    ∃ q : EdgeWalk src dst H a v, q.vertices.Sublist p.vertices := by
  induction p with
  | nil =>
    simp only [vertices, edges, List.map_nil, List.mem_singleton] at hv
    subst v
    exact ⟨.nil, List.Sublist.refl _⟩
  | snoc p e he hs ih =>
    rw [vertices_snoc] at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨q, hq⟩ := ih hv
      exact ⟨q, hq.trans (by rw [vertices_snoc]; exact (List.prefix_append _ _).sublist)⟩
    · simp only [List.mem_singleton] at hv
      subst v
      exact ⟨p.snoc e he hs, List.Sublist.refl _⟩

private theorem exists_simple (p : EdgeWalk src dst H a b) :
    ∃ q : EdgeWalk src dst H a b, q.vertices.Nodup := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp [vertices, edges]⟩
  | snoc p e he hs ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hv : dst e ∈ q.vertices
    · obtain ⟨r, hr⟩ := q.prefix_at_vertex hv
      exact ⟨r, hq.sublist hr⟩
    · refine ⟨q.snoc e he hs, ?_⟩
      rw [vertices_snoc, List.nodup_append]
      refine ⟨hq, by simp, ?_⟩
      intro v hv' u hu hEq
      have hu' : u = dst e := List.mem_singleton.mp hu
      exact hv (hu' ▸ hEq ▸ hv')

private theorem exists_bounded (p : EdgeWalk src dst H a b) :
    ∃ q : EdgeWalk src dst H a b, q.edges.length ≤ H.card := by
  classical
  obtain ⟨q, hq⟩ := p.exists_simple
  have hn : q.edges.Nodup := (List.nodup_cons.mp hq).2.of_map
  have hsub : q.edges.toFinset ⊆ H := by
    intro e he
    exact q.mem_edges (List.mem_toFinset.mp he)
  refine ⟨q, ?_⟩
  simpa only [List.toFinset_card_of_nodup hn] using Finset.card_le_card hsub

private theorem last_of_ne (p : EdgeWalk src dst H a b) (h : b ≠ a) :
    ∃ e, e ∈ H ∧ dst e = b ∧ Nonempty (EdgeWalk src dst H a (src e)) := by
  cases p with
  | nil => exact False.elim (h rfl)
  | snoc p e he hs => exact ⟨e, he, rfl, ⟨hs ▸ p⟩⟩
end EdgeWalk

variable [Fintype V] [Fintype E]
noncomputable local instance decidableLocal1 : DecidableEq V := Classical.decEq V
noncomputable local instance decidableLocal2 : DecidableEq E := Classical.decEq E

private noncomputable def reachSet (src dst : E → V) (H : Finset E) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Nonempty (EdgeWalk src dst H a v)

private theorem mem_reachSet {src dst : E → V} {H : Finset E} {a v : V} :
    v ∈ reachSet src dst H a ↔ Nonempty (EdgeWalk src dst H a v) := by
  classical
  simp [reachSet]

private theorem reachSet_root (src dst : E → V) (H : Finset E) (a : V) : a ∈ reachSet src dst H a :=
  mem_reachSet.mpr ⟨.nil⟩

private theorem reachSet_closed (src dst : E → V) (H : Finset E) (a : V)
    (e : E) (he : e ∈ H) (hs : src e ∈ reachSet src dst H a) :
    dst e ∈ reachSet src dst H a := by
  obtain ⟨p⟩ := mem_reachSet.mp hs
  exact mem_reachSet.mpr ⟨p.snoc e he rfl⟩

open scoped BigOperators

private noncomputable def edgePreimage (f : E → V) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => f e ∈ S

private theorem card_edgePreimage_lower (f : E → V) (hf : Function.Surjective f) (S : Finset V) :
    S.card ≤ (edgePreimage f S).card := by
  classical
  have heq : (edgePreimage f S).image f = S := by
    ext v
    simp only [Finset.mem_image, edgePreimage, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro hv
      obtain ⟨e, rfl⟩ := hf v
      exact ⟨e, hv, rfl⟩
  calc
    S.card = ((edgePreimage f S).image f).card := congrArg Finset.card heq.symm
    _ ≤ (edgePreimage f S).card := Finset.card_image_le

private theorem card_edgePreimage_upper (f : E → V) (hf : Function.Surjective f) (S : Finset V) :
    (edgePreimage f S).card + Fintype.card V ≤ Fintype.card E + S.card := by
  classical
  have hl := card_edgePreimage_lower f hf (Finset.univ \ S)
  have hp : (edgePreimage f S).card + (edgePreimage f (Finset.univ \ S)).card =
      Fintype.card E := by
    simpa only [edgePreimage, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.card_univ]
      using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E)) (fun e => f e ∈ S)
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ] at hs
  omega

private noncomputable def innerEdges (src dst : E → V) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => src e ∈ S ∧ dst e ∈ S

private noncomputable def cutOut (src dst : E → V) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => src e ∈ S ∧ dst e ∉ S

private noncomputable def cutIn (src dst : E → V) (S : Finset V) : Finset E := cutOut dst src S

private theorem split_out (src dst : E → V) (S : Finset V) :
    edgePreimage src S = innerEdges src dst S ∪ cutOut src dst S := by
  classical
  ext e
  simp only [edgePreimage, innerEdges, cutOut, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_union, true_and]
  tauto

private theorem disjoint_out (src dst : E → V) (S : Finset V) :
    Disjoint (innerEdges src dst S) (cutOut src dst S) := by
  classical
  rw [Finset.disjoint_left]
  intro e hi ho
  have hi' := (Finset.mem_filter.mp hi).2
  have ho' := (Finset.mem_filter.mp ho).2
  exact ho'.2 hi'.2

private theorem reachable_card_inner (src dst : E → V) (H : Finset E) (a : V) :
    (reachSet src dst H a).card ≤ (innerEdges src dst (reachSet src dst H a)).card + 1 := by
  classical
  let S := reachSet src dst H a
  have witness (v : ↥(S.erase a)) :
      ∃ e, src e ∈ S ∧ dst e = v.val := by
    have hv : v.val ∈ S := (Finset.mem_erase.mp v.property).2
    obtain ⟨p⟩ := mem_reachSet.mp hv
    obtain ⟨e, he, hd, hp⟩ := p.last_of_ne (Finset.mem_erase.mp v.property).1
    exact ⟨e, mem_reachSet.mpr hp, hd⟩
  let chosen (v : ↥(S.erase a)) : E := Classical.choose (witness v)
  have chosen_spec (v : ↥(S.erase a)) : src (chosen v) ∈ S ∧ dst (chosen v) = v.val :=
    Classical.choose_spec (witness v)
  let assign : ↥(S.erase a) → ↥(innerEdges src dst S) := fun v =>
    ⟨chosen v, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (chosen_spec v).1, ?_⟩
      rw [(chosen_spec v).2]
      exact (Finset.mem_erase.mp v.property).2⟩
  have hinj : Function.Injective assign := by
    intro v w he
    apply Subtype.ext
    exact ((chosen_spec v).2).symm.trans ((congrArg dst (congrArg Subtype.val he)).trans
      (chosen_spec w).2)
  have hc := Fintype.card_le_of_injective assign hinj
  simp only [Fintype.card_coe] at hc
  change S.card ≤ (innerEdges src dst S).card + 1
  have hr : a ∈ S := reachSet_root src dst H a
  have hS := Finset.card_erase_add_one hr
  omega

private theorem reachable_cut_card (src dst : E → V) (hsrc : Function.Surjective src)
    (H : Finset E) (a : V) :
    (cutOut src dst (reachSet src dst H a)).card ≤
      (Fintype.card E - Fintype.card V) + 1 := by
  classical
  have hl := reachable_card_inner src dst H a
  have hu := card_edgePreimage_upper src hsrc (reachSet src dst H a)
  have hE := Fintype.card_le_of_surjective src hsrc
  have heq := congrArg Finset.card (split_out src dst (reachSet src dst H a))
  rw [Finset.card_union_of_disjoint (disjoint_out _ _ _)] at heq
  omega

/-- A sufficiently heavy incoming edge cannot enter a high-weight reachability region
without allowing a return to its source. -/
private theorem heavy_edge_returns (src dst : E → V) (hsrc : Function.Surjective src)
    (w : E → ℕ) (K t : ℕ)
    (hcut : ∀ S : Finset V,
      ∑ e ∈ cutIn src dst S, w e ≤ (∑ e ∈ cutOut src dst S, w e) + K)
    (e : E) (he : ((Fintype.card E - Fintype.card V) + 1) * t + K < w e) :
    Nonempty (EdgeWalk src dst (Finset.univ.filter fun f => t ≤ w f) (dst e) (src e)) := by
  classical
  let H := Finset.univ.filter fun f => t ≤ w f
  let S := reachSet src dst H (dst e)
  by_contra hn
  have hsource : src e ∉ S := fun h => hn (mem_reachSet.mp h)
  have hdest : dst e ∈ S := reachSet_root src dst H (dst e)
  have hein : e ∈ cutIn src dst S := by
    simp only [cutIn, cutOut, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hdest, hsource⟩
  have hpoint (f : E) (hf : f ∈ cutOut src dst S) : w f ≤ t := by
    have hp := (Finset.mem_filter.mp hf).2
    by_contra hw
    have hH : f ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact hp.2 (reachSet_closed src dst H (dst e) f hH hp.1)
  have hsum : (∑ f ∈ cutOut src dst S, w f) ≤ (cutOut src dst S).card * t := by
    calc
      _ ≤ ∑ _f ∈ cutOut src dst S, t := Finset.sum_le_sum hpoint
      _ = _ := by simp
  have hsingle : w e ≤ ∑ f ∈ cutIn src dst S, w f :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hein
  have hcard := reachable_cut_card src dst hsrc H (dst e)
  have hmul := Nat.mul_le_mul_right t hcard
  change (cutOut src dst S).card * t ≤ ((Fintype.card E - Fintype.card V) + 1) * t at hmul
  have hc := hcut S
  omega

/-- High edge weights cannot branch if every pair of distinct return loops has
combined length larger than the word length. -/
private theorem no_two_heavy_edges (src dst : E → V) (hsrc : Function.Surjective src)
    (w : E → ℕ) (n C K : ℕ) (hn : 4 ≤ n)
    (htotal : (∑ e : E, w e) ≤ C * n)
    (hcut : ∀ S : Finset V,
      ∑ e ∈ cutIn src dst S, w e ≤ (∑ e ∈ cutOut src dst S, w e) + K)
    (hloop : ∀ (e f : E), src e = src f → e ≠ f →
      ∀ (p : EdgeWalk src dst (Finset.univ.filter fun g => 4*C+1 ≤ w g) (dst e) (src e))
        (q : EdgeWalk src dst (Finset.univ.filter fun g => 4*C+1 ≤ w g) (dst f) (src f)),
      n < (p.edges.length + 1) + (q.edges.length + 1))
    (e f : E) (hs : src e = src f) (hef : e ≠ f)
    (he : ((Fintype.card E - Fintype.card V) + 1) * (4*C+1) + K < w e)
    (hf : ((Fintype.card E - Fintype.card V) + 1) * (4*C+1) + K < w f) : False := by
  classical
  let H := Finset.univ.filter fun g => 4*C+1 ≤ w g
  obtain ⟨p⟩ := heavy_edge_returns src dst hsrc w K (4*C+1) hcut e he
  obtain ⟨q⟩ := heavy_edge_returns src dst hsrc w K (4*C+1) hcut f hf
  obtain ⟨p', hp'⟩ := p.exists_bounded
  obtain ⟨q', hq'⟩ := q.exists_bounded
  have hlength := hloop e f hs hef p' q'
  have hsize : n ≤ 4 * H.card := by change n ≤ 4 * H.card; change p'.edges.length ≤ H.card at hp'; change q'.edges.length ≤ H.card at hq'; omega
  have hpos : 0 < H.card := by omega
  have hsum : H.card * (4*C+1) ≤ ∑ g : E, w g := by
    calc
      _ = ∑ _g ∈ H, (4*C+1) := by simp
      _ ≤ ∑ g ∈ H, w g := by
        apply Finset.sum_le_sum
        intro g hg
        exact (Finset.mem_filter.mp hg).2
      _ ≤ ∑ g : E, w g :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (by intros; omega)
  nlinarith

/-- Directed cuts have imbalance at most the global edge excess. -/
private theorem cut_card_imbalance (src dst : E → V) (hsrc : Function.Surjective src)
    (hdst : Function.Surjective dst) (S : Finset V) :
    (cutIn src dst S).card ≤ (cutOut src dst S).card + (Fintype.card E - Fintype.card V) := by
  classical
  have hlow := card_edgePreimage_lower src hsrc S
  have hupp := card_edgePreimage_upper dst hdst S
  have hE := Fintype.card_le_of_surjective src hsrc
  have ho := congrArg Finset.card (split_out src dst S)
  have hi := congrArg Finset.card (split_out dst src S)
  rw [Finset.card_union_of_disjoint (disjoint_out _ _ _)] at ho hi
  have heq : innerEdges dst src S = innerEdges src dst S := by
    ext e
    simp only [innerEdges, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  rw [heq] at hi
  change (cutOut dst src S).card ≤ _
  omega

private noncomputable def fiberWeight {L : Type*} [Fintype L] (f : L → E) (e : E) : ℕ := by
  classical
  exact (edgePreimage f {e}).card - 1

private theorem fiberWeight_sum {L : Type*} [Fintype L] (f : L → E)
    (hf : Function.Surjective f) (S : Finset E) :
    (∑ e ∈ S, fiberWeight f e) + S.card = (edgePreimage f S).card := by
  classical
  have hcount : (edgePreimage f S).card =
      ∑ e ∈ S, ((edgePreimage f S).filter fun l => f l = e).card :=
    Finset.card_eq_sum_card_fiberwise (fun l hl => (Finset.mem_filter.mp hl).2)
  have hfilter (e : E) (he : e ∈ S) :
      (edgePreimage f S).filter (fun l => f l = e) = edgePreimage f {e} := by
    ext l
    simp only [edgePreimage, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact And.right
    · intro hl
      exact ⟨hl.symm ▸ he, hl⟩
  have hpos (e : E) : 1 ≤ (edgePreimage f {e}).card := by
    obtain ⟨l, hl⟩ := hf e
    apply Finset.one_le_card.mpr
    exact ⟨l, by simp only [edgePreimage, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_singleton, true_and]; exact hl⟩
  calc
    _ = ∑ e ∈ S, (fiberWeight f e + 1) := by simp [Finset.sum_add_distrib]
    _ = ∑ e ∈ S, (edgePreimage f {e}).card := by
      apply Finset.sum_congr rfl
      intro e he
      dsimp [fiberWeight]
      have := hpos e
      omega
    _ = _ := by
      rw [hcount]
      apply Finset.sum_congr rfl
      intro e he
      rw [hfilter e he]

/-- A surjective morphism of finite prolongable graphs gives the cut estimate
for the number of extra edge lifts. -/
private theorem fiberWeight_cut {V' E' : Type*} [Fintype V'] [Fintype E']
    (src dst : E → V) (hsrc : Function.Surjective src) (hdst : Function.Surjective dst)
    (src' dst' : E' → V') (hsrc' : Function.Surjective src') (hdst' : Function.Surjective dst')
    (fv : V' → V) (fe : E' → E) (hfe : Function.Surjective fe)
    (hsource : ∀ e, src (fe e) = fv (src' e)) (htarget : ∀ e, dst (fe e) = fv (dst' e))
    (S : Finset V) :
    (∑ e ∈ cutIn src dst S, fiberWeight fe e) ≤
      (∑ e ∈ cutOut src dst S, fiberWeight fe e) +
        ((Fintype.card E - Fintype.card V) + (Fintype.card E' - Fintype.card V')) := by
  classical
  have hi := fiberWeight_sum fe hfe (cutIn src dst S)
  have ho := fiberWeight_sum fe hfe (cutOut src dst S)
  have hpreout : edgePreimage fe (cutOut src dst S) =
      cutOut src' dst' (edgePreimage fv S) := by
    ext e
    simp only [edgePreimage, cutOut, Finset.mem_filter, Finset.mem_univ,
      true_and, hsource, htarget]
  have hprein : edgePreimage fe (cutIn src dst S) =
      cutIn src' dst' (edgePreimage fv S) := by
    ext e
    simp only [edgePreimage, cutIn, cutOut, Finset.mem_filter, Finset.mem_univ,
      true_and, hsource, htarget]
  rw [hpreout] at ho
  rw [hprein] at hi
  have hlong := cut_card_imbalance src' dst' hsrc' hdst' (edgePreimage fv S)
  have hshort := cut_card_imbalance dst src hdst hsrc S
  have hflip : cutIn dst src S = cutOut src dst S := rfl
  rw [hflip] at hshort
  change (cutOut src dst S).card ≤ (cutIn src dst S).card + _ at hshort
  omega

/-- Select the unique heavy outgoing edge whenever there is one. -/
private theorem choose_default (src : E → V) (hsrc : Function.Surjective src) (w : E → ℕ) (R : ℕ)
    (hunique : ∀ e f, src e = src f → R < w e → R < w f → e = f) :
    ∃ d : V → E, (∀ v, src (d v) = v) ∧ ∀ e, e ≠ d (src e) → w e ≤ R := by
  classical
  have hex (v : V) : ∃ e, src e = v ∧ ∀ f, src f = v → f ≠ e → w f ≤ R := by
    by_cases hv : ∃ e, src e = v ∧ R < w e
    · obtain ⟨e, he, hw⟩ := hv
      refine ⟨e, he, ?_⟩
      intro f hf hne
      by_contra h
      exact hne (hunique f e (hf.trans he.symm) (by omega) hw)
    · obtain ⟨e, he⟩ := hsrc v
      refine ⟨e, he, ?_⟩
      intro f hf _
      by_contra h
      exact hv ⟨f, hf, by omega⟩
  choose d hd hdw using hex
  exact ⟨d, hd, fun e he => hdw (src e) e rfl he⟩

/-- Counting edge lifts outside one chosen edge at each vertex controls every
intermediate graph's excess, provided the edge projections are right resolving. -/
private theorem peak_count_bound {V' E' L : Type*} [Fintype V'] [Fintype E'] [Fintype L]
    (src : E → V) (d : V → E) (hd : ∀ v, src (d v) = v)
    (src' : E' → V') (fv : V' → V) (fe : E' → E)
    (hsource : ∀ e, src (fe e) = fv (src' e))
    (hresolve : ∀ e f, src' e = src' f → fe e = fe f → e = f)
    (far : L → E) (hfar : Function.Surjective far)
    (g : L → E') (hg : Function.Surjective g) (hcomp : ∀ l, fe (g l) = far l)
    (R : ℕ) (hR : ∀ e, e ≠ d (src e) → fiberWeight far e ≤ R) :
    Fintype.card E' ≤ Fintype.card V' +
      (Fintype.card E - Fintype.card V) * (R + 1) := by
  classical
  let N : Finset E := Finset.univ.filter fun e => e ≠ d (src e)
  let B : Finset E' := edgePreimage fe N
  let G : Finset E' := Finset.univ \ B
  have hd_inj : Function.Injective d := by
    intro v w hvw
    have h := congrArg src hvw
    simpa only [hd] using h
  have hN : N.card + Fintype.card V = Fintype.card E := by
    have hD : Finset.univ \ N = Finset.univ.image d := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_univ, N, Finset.mem_filter, true_and,
        not_not, Finset.mem_image]
      constructor
      · intro he
        exact ⟨src e, he.symm⟩
      · rintro ⟨v, rfl⟩
        rw [hd]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    rw [hD, Finset.card_image_of_injective _ hd_inj, Finset.card_univ, Finset.card_univ] at hc
    omega
  have hgood : G.card ≤ Fintype.card V' := by
    let assign : ↥G → V' := fun e => src' e.val
    have hi : Function.Injective assign := by
      intro e f h
      apply Subtype.ext
      apply hresolve e.val f.val h
      have he : fe e.val = d (src (fe e.val)) := by
        have hmem := (Finset.mem_sdiff.mp e.property).2
        simpa only [B, edgePreimage, Finset.mem_filter, Finset.mem_univ, N,
          true_and, not_not] using hmem
      have hf : fe f.val = d (src (fe f.val)) := by
        have hmem := (Finset.mem_sdiff.mp f.property).2
        simpa only [B, edgePreimage, Finset.mem_filter, Finset.mem_univ, N,
          true_and, not_not] using hmem
      change src' e.val = src' f.val at h
      rw [he, hf, hsource, hsource, h]
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective assign hi
  have hbad : B.card ≤ N.card * (R+1) := by
    have hl := card_edgePreimage_lower g hg B
    have hp : edgePreimage g B = edgePreimage far N := by
      ext l
      simp only [edgePreimage, B, Finset.mem_filter, Finset.mem_univ, true_and, hcomp]
    rw [hp] at hl
    have hw := fiberWeight_sum far hfar N
    have hs : (∑ e ∈ N, fiberWeight far e) ≤ N.card * R := by
      calc
        _ ≤ ∑ _e ∈ N, R := by
          apply Finset.sum_le_sum
          intro e he
          exact hR e (Finset.mem_filter.mp he).2
        _ = _ := by simp
    nlinarith
  have hBG : G.card + B.card = Fintype.card E' := by
    simpa only [G, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have hs : N.card = Fintype.card E - Fintype.card V := Nat.eq_sub_of_add_eq hN
  rw [hs] at hbad
  omega

end D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Graph

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Graph
open EdgeWalk
variable {V E A : Type*} {src dst : E → V} {H : Finset E}

/-- Two loops that start with different letters cannot together fit inside their
common word vertex. This is the word overlap fact used in the graph estimate. -/
private theorem noncommuting_return_length (v : List A) (a b : A) (x y : List A)
    (hab : a ≠ b) (hx : v <:+ v ++ (a :: x)) (hy : v <:+ v ++ (b :: y)) :
    v.length < (a :: x).length + (b :: y).length := by
  by_contra hn
  have hlen : ((a :: x) ++ (b :: y)).length ≤ v.length := by simp only [List.length_append]; omega
  have hlen' : ((b :: y) ++ (a :: x)).length ≤ v.length := by simp only [List.length_append]; omega
  have hx' : v ++ (b :: y) <:+ (v ++ (a :: x)) ++ (b :: y) :=
    List.suffix_append_self_iff.mpr hx
  have hy' : v ++ (a :: x) <:+ (v ++ (b :: y)) ++ (a :: x) :=
    List.suffix_append_self_iff.mpr hy
  have hxy : v <:+ v ++ ((a :: x) ++ (b :: y)) := by
    simpa only [List.append_assoc] using hy.trans hx'
  have hyx : v <:+ v ++ ((b :: y) ++ (a :: x)) := by
    simpa only [List.append_assoc] using hx.trans hy'
  have hsxy := List.suffix_of_suffix_length_le (List.suffix_append v ((a :: x) ++ (b :: y))) hxy hlen
  have hsyx := List.suffix_of_suffix_length_le (List.suffix_append v ((b :: y) ++ (a :: x))) hyx hlen'
  have heq : (a :: x) ++ (b :: y) = (b :: y) ++ (a :: x) :=
    (List.suffix_of_suffix_length_le hsxy hsyx (by simp only [List.length_append]; omega)).eq_of_length
      (by simp only [List.length_append]; omega)
  exact hab (List.cons.inj heq).1

private theorem walk_word_suffix (word : V → List A) (label : E → A)
    (hstep : ∀ e, word (dst e) <:+ word (src e) ++ [label e])
    {a b : V} (p : EdgeWalk src dst H a b) :
    word b <:+ word a ++ p.edges.map label := by
  induction p with
  | nil => simp [edges]
  | snoc p e he hs ih =>
    have hstep' := hstep e
    rw [hs] at hstep'
    have htail : word _ ++ [label e] <:+ (word a ++ p.edges.map label) ++ [label e] :=
      List.suffix_append_self_iff.mpr ih
    simpa only [edges, List.map_append, List.map_singleton, List.append_assoc]
      using hstep'.trans htail

private theorem word_loop_obstruction (word : V → List A) (label : E → A) (n : ℕ)
    (hlen : ∀ v, (word v).length = n)
    (hstep : ∀ e, word (dst e) <:+ word (src e) ++ [label e])
    (hdet : ∀ e f, src e = src f → label e = label f → e = f)
    (e f : E) (hs : src e = src f) (hef : e ≠ f)
    (p : EdgeWalk src dst H (dst e) (src e))
    (q : EdgeWalk src dst H (dst f) (src f)) :
    n < (p.edges.length + 1) + (q.edges.length + 1) := by
  have hab : label e ≠ label f := fun h => hef (hdet e f hs h)
  have hp := walk_word_suffix word label hstep p
  have hq := walk_word_suffix word label hstep q
  have he : word (dst e) ++ p.edges.map label <:+
      (word (src e) ++ [label e]) ++ p.edges.map label :=
    List.suffix_append_self_iff.mpr (hstep e)
  have hf : word (dst f) ++ q.edges.map label <:+
      (word (src f) ++ [label f]) ++ q.edges.map label :=
    List.suffix_append_self_iff.mpr (hstep f)
  have hp' : word (src e) <:+ word (src e) ++ (label e :: p.edges.map label) := by
    simpa only [List.append_assoc, List.singleton_append] using hp.trans he
  have hq' : word (src e) <:+ word (src e) ++ (label f :: q.edges.map label) := by
    simpa only [List.append_assoc, List.singleton_append, ← hs] using hq.trans hf
  have h := noncommuting_return_length (word (src e)) (label e) (label f)
    (p.edges.map label) (q.edges.map label) hab hp' hq'
  simpa only [hlen, List.length_cons, List.length_map] using h

end D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Graph

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Language
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Graph
open scoped BigOperators
variable {A : Type*} [Fintype A]
noncomputable local instance decidableLocal1 : DecidableEq A := Classical.decEq A

/-- Crop a factor at a fixed finite offset. -/
private noncomputable def crop (z : ℤ → Option A) (m n k : ℕ) (h : k + n ≤ m) :
    ↥(intFactorSet z m) → ↥(intFactorSet z n) := fun w =>
  ⟨fun j => w.val ⟨k + j.val, by omega⟩, by
    obtain ⟨i, hi⟩ := (by simpa only [intFactorSet, Finset.mem_filter, Finset.mem_univ, true_and] using w.property : ∃ i, w.val = intFactor z _ i)
    simp only [intFactorSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨i + k, ?_⟩
    funext j
    simp only [hi, intFactor]
    congr 1
    push_cast
    omega⟩

/-- A bi-infinite word supplies all fixed-offset extensions. -/
private theorem crop_surjective (z : ℤ → Option A) (m n k : ℕ) (h : k + n ≤ m) :
    Function.Surjective (crop z m n k h) := by
  intro w
  obtain ⟨i, hi⟩ := (by simpa only [intFactorSet, Finset.mem_filter, Finset.mem_univ, true_and] using w.property : ∃ i, w.val = intFactor z _ i)
  refine ⟨⟨intFactor z m (i - k), (by simp only [intFactorSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i-k,rfl⟩)⟩, ?_⟩
  apply Subtype.ext
  funext j
  simp only [crop, hi, intFactor]
  congr 1
  push_cast
  omega

private noncomputable def source (z : ℤ → Option A) (n : ℕ) : ↥(intFactorSet z (n+1)) → ↥(intFactorSet z n) :=
  crop z (n+1) n 0 (by omega)
private noncomputable def target (z : ℤ → Option A) (n : ℕ) : ↥(intFactorSet z (n+1)) → ↥(intFactorSet z n) :=
  crop z (n+1) n 1 (by omega)

private theorem source_surjective (z : ℤ → Option A) (n : ℕ) : Function.Surjective (source z n) :=
  crop_surjective z (n+1) n 0 _
private theorem target_surjective (z : ℤ → Option A) (n : ℕ) : Function.Surjective (target z n) :=
  crop_surjective z (n+1) n 1 _

private noncomputable def tailMap (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m) : ↥(intFactorSet z m) → ↥(intFactorSet z n) :=
  crop z m n (m-n) (by omega)

private theorem tailMap_surjective (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m) :
    Function.Surjective (tailMap z m n h) := crop_surjective z m n (m-n) _

private theorem tailMap_source (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m) (e : ↥(intFactorSet z (m+1))) :
    source z n (tailMap z (m+1) (n+1) (by omega) e) =
      tailMap z m n h (source z m e) := by
  apply Subtype.ext
  funext i
  dsimp [source, tailMap, crop]
  apply congrArg e.val
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

private theorem tailMap_target (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m) (e : ↥(intFactorSet z (m+1))) :
    target z n (tailMap z (m+1) (n+1) (by omega) e) =
      tailMap z m n h (target z m e) := by
  apply Subtype.ext
  funext i
  dsimp [target, tailMap, crop]
  apply congrArg e.val
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

private def edgeLabel (z : ℤ → Option A) (n : ℕ) (e : ↥(intFactorSet z (n+1))) : Option A := e.val (Fin.last n)

private theorem source_label_determines (z : ℤ → Option A) (n : ℕ) (e f : ↥(intFactorSet z (n+1)))
    (hs : source z n e = source z n f) (hl : edgeLabel z n e = edgeLabel z n f) : e = f := by
  apply Subtype.ext
  funext k
  refine Fin.lastCases hl (fun i => ?_) k
  have h := congrFun (congrArg Subtype.val hs) i
  change e.val ⟨i.val, by omega⟩ = f.val ⟨i.val, by omega⟩
  simpa only [source, crop, Nat.zero_add] using h

private theorem word_step (z : ℤ → Option A) (n : ℕ) (e : ↥(intFactorSet z (n+1))) :
    List.ofFn (target z n e).val <:+ List.ofFn (source z n e).val ++ [edgeLabel z n e] := by
  have hs : List.ofFn e.val = List.ofFn (source z n e).val ++ [edgeLabel z n e] := by
    rw [List.ofFn_succ_last]
    apply congrArg (fun l : List (Option A) => l ++ [e.val (Fin.last n)])
    apply congrArg List.ofFn
    funext i
    dsimp [source, crop]
    apply congrArg e.val
    apply Fin.ext
    simp
  rw [← hs]
  refine ⟨[e.val 0], ?_⟩
  rw [List.ofFn_succ]
  change e.val 0 :: List.ofFn (target z n e).val = e.val 0 :: List.ofFn (fun i => e.val i.succ)
  apply congrArg (List.cons (e.val 0))
  apply congrArg List.ofFn
  funext i
  dsimp [target, crop]
  apply congrArg e.val
  apply Fin.ext
  simp only [Fin.val_mk, Fin.val_succ]
  omega

private theorem factor_loop_obstruction (z : ℤ → Option A) (n : ℕ) (H : Finset (↥(intFactorSet z (n+1))))
    (e f : ↥(intFactorSet z (n+1))) (hs : source z n e = source z n f) (hef : e ≠ f)
    (p : EdgeWalk (source z n) (target z n) H (target z n e) (source z n e))
    (q : EdgeWalk (source z n) (target z n) H (target z n f) (source z n f)) :
    n < (p.edges.length+1)+(q.edges.length+1) := by
  exact word_loop_obstruction (fun v => List.ofFn v.val) (edgeLabel z n) n
    (fun _ => List.length_ofFn) (word_step z n) (source_label_determines z n) e f hs hef p q

private theorem tailMap_comp (z : ℤ → Option A) (m l n : ℕ) (hnl : n ≤ l) (hlm : l ≤ m)
    (w : ↥(intFactorSet z m)) :
    tailMap z l n hnl (tailMap z m l hlm w) = tailMap z m n (by omega) w := by
  apply Subtype.ext
  funext i
  dsimp [tailMap, crop]
  apply congrArg w.val
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

private theorem tailMap_label (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m) (e : ↥(intFactorSet z (m+1))) :
    edgeLabel z n (tailMap z (m+1) (n+1) (by omega) e) = edgeLabel z m e := by
  dsimp [edgeLabel, tailMap, crop]
  apply congrArg e.val
  apply Fin.ext
  simp only [Fin.val_mk, Fin.val_last]
  omega

private theorem tailMap_right_resolving (z : ℤ → Option A) (m n : ℕ) (h : n ≤ m)
    (e f : ↥(intFactorSet z (m+1))) (hs : source z m e = source z m f)
    (ht : tailMap z (m+1) (n+1) (by omega) e = tailMap z (m+1) (n+1) (by omega) f) : e = f := by
  apply source_label_determines z m e f hs
  have hh := congrArg (edgeLabel z n) ht
  simpa only [tailMap_label z m n h] using hh

/-- A finite interval of the language has controlled excess as soon as its two
endpoint excesses and its total number of longer edge lifts are controlled. -/
private theorem factor_peak_bound (z : ℤ → Option A) (a n b : ℕ) (ha : 4 ≤ a)
    (han : a ≤ n) (hnb : n ≤ b) (C : ℕ)
    (hC : (intFactorSet z (b+1)).card ≤ C*a) :
    (intFactorSet z (n+1)).card ≤ (intFactorSet z n).card +
      ((intFactorSet z (a+1)).card - (intFactorSet z a).card) *
      (((intFactorSet z (a+1)).card - (intFactorSet z a).card + 1)*(4*C+1) +
       (((intFactorSet z (a+1)).card - (intFactorSet z a).card) +
        ((intFactorSet z (b+1)).card - (intFactorSet z b).card)) + 1) := by
  classical
  have hab : a ≤ b := Nat.le_trans han hnb
  let far := tailMap z (b+1) (a+1) (by omega)
  let w := fiberWeight far
  let s₁ := Fintype.card (↥(intFactorSet z (a+1))) - Fintype.card (↥(intFactorSet z a))
  let s₂ := Fintype.card (↥(intFactorSet z (b+1))) - Fintype.card (↥(intFactorSet z b))
  let R := (s₁+1)*(4*C+1)+(s₁+s₂)
  have hfar : Function.Surjective far := tailMap_surjective z (b+1) (a+1) (by omega)
  have htotal : (∑ e : ↥(intFactorSet z (a+1)), w e) ≤ C*a := by
    have hs := fiberWeight_sum far hfar Finset.univ
    have hs' : (∑ e : ↥(intFactorSet z (a+1)), w e) + (intFactorSet z (a+1)).card =
        (intFactorSet z (b+1)).card := by
      simpa only [w, edgePreimage, Finset.mem_univ, Finset.filter_true,
        Finset.card_univ, Fintype.card_coe] using hs
    omega
  have hcut (S : Finset (↥(intFactorSet z a))) :
      (∑ e ∈ cutIn (source z a) (target z a) S, w e) ≤
      (∑ e ∈ cutOut (source z a) (target z a) S, w e) + (s₁+s₂) := by
    exact fiberWeight_cut (source z a) (target z a) (source_surjective z a) (target_surjective z a)
      (source z b) (target z b) (source_surjective z b) (target_surjective z b)
      (tailMap z b a hab) far hfar (tailMap_source z b a hab) (tailMap_target z b a hab) S
  have huniq (e f : ↥(intFactorSet z (a+1))) (hs : source z a e = source z a f)
      (he : R < w e) (hf : R < w f) : e = f := by
    by_contra hne
    exact no_two_heavy_edges (source z a) (target z a) (source_surjective z a) w a C (s₁+s₂)
      ha htotal hcut (fun e f hs hne p q => factor_loop_obstruction z a _ e f hs hne p q)
      e f hs hne he hf
  obtain ⟨d, hd, hR⟩ := choose_default (source z a) (source_surjective z a) w R huniq
  have hc := peak_count_bound (source z a) d hd (source z n)
    (tailMap z n a han) (tailMap z (n+1) (a+1) (by omega))
    (tailMap_source z n a han) (tailMap_right_resolving z n a han)
    far hfar (tailMap z (b+1) (n+1) (by omega))
    (tailMap_surjective z (b+1) (n+1) (by omega))
    (tailMap_comp z (b+1) (n+1) (a+1) (by omega) (by omega)) R hR
  simpa only [R, s₁, s₂, Fintype.card_coe] using hc

end D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Language

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Scalar
open D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Language D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport

/-- Linear growth forces a small increment in every multiplicative interval. -/
private theorem exists_small_step (p : ℕ → ℕ) (C m : ℕ) (hm : 0 < m)
    (hC : ∀ n, p n ≤ C * (n+1)) :
    ∃ a, m ≤ a ∧ a < 2*m ∧ p (a+1) ≤ p a + 3*C := by
  by_contra h
  have hstep (a : ℕ) (ha : m ≤ a) (ha' : a < 2*m) : p a + (3*C+1) ≤ p (a+1) := by
    by_contra hs
    exact h ⟨a,ha,ha',by omega⟩
  have hind : ∀ k, k ≤ m → p m + k * (3*C+1) ≤ p (m+k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hs := hstep (m+k) (by omega) (by omega)
      have heq : m + (k+1) = (m+k)+1 := (Nat.add_assoc m k 1).symm
      rw [heq]
      nlinarith
  have hi := hind m le_rfl
  have hc := hC (2*m)
  have heq : m+m = 2*m := (Nat.two_mul m).symm
  rw [heq] at hi
  nlinarith

variable {A : Type} [Fintype A]

/-- The finite graph peak estimate yields Cassaigne's theorem for the precise
bi-infinite factor language needed by the mirror reduction. -/
private theorem biinfinite_bounded_differences (z : ℤ → Option A) (C : ℕ)
    (hC : ∀ n, (intFactorSet z n).card ≤ C * (n+1)) :
    ∃ D : ℕ, ∀ n, (intFactorSet z (n+1)).card ≤ (intFactorSet z n).card + D := by
  let p : ℕ → ℕ := fun n => (intFactorSet z n).card
  let D := max (9*C) (3*C*((3*C+1)*(24*C+1)+6*C+1))
  refine ⟨D, ?_⟩
  intro n
  change p (n+1) ≤ p n + D
  by_cases hn : n < 8
  · calc
      p (n+1) ≤ C*(n+2) := by simpa only [p, Nat.add_assoc] using hC (n+1)
      _ ≤ C*9 := Nat.mul_le_mul_left C (by omega)
      _ = 9*C := Nat.mul_comm _ _
      _ ≤ D := le_max_left _ _
      _ ≤ p n + D := by omega
  · have hm : 0 < n/2 := by omega
    obtain ⟨a, ha, han, hsa⟩ := exists_small_step p C (n/2) hm hC
    obtain ⟨b, hb, hbn, hsb⟩ := exists_small_step p C (n+1) (by omega) hC
    have ha4 : 4 ≤ a := by omega
    have han' : a ≤ n := by omega
    have hnb : n ≤ b := Nat.le_of_succ_le hb
    have hgrowth : p (b+1) ≤ (6*C)*a := by
      have hc := hC (b+1)
      have hmul : C*(b+2) ≤ C*(6*a) := Nat.mul_le_mul_left C (by omega)
      dsimp [p] at *
      nlinarith
    have hpeak := factor_peak_bound z a n b ha4 han' hnb (6*C) hgrowth
    change p (n+1) ≤ p n +
      (p (a+1)-p a) * (((p (a+1)-p a)+1)*(4*(6*C)+1) +
        ((p (a+1)-p a)+(p (b+1)-p b))+1) at hpeak
    have h₁ : p (a+1)-p a ≤ 3*C := by omega
    have h₂ : p (b+1)-p b ≤ 3*C := by omega
    have hprod : (p (a+1)-p a) * (((p (a+1)-p a)+1)*(4*(6*C)+1) +
        ((p (a+1)-p a)+(p (b+1)-p b))+1) ≤
        3*C*((3*C+1)*(24*C+1)+6*C+1) := by
      have heq : 4*(6*C)+1 = 24*C+1 := by omega
      rw [heq]
      gcongr <;> omega
    have hD : 3*C*((3*C+1)*(24*C+1)+6*C+1) ≤ D := le_max_right _ _
    omega

end D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28.Scalar

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport

/-- The bounded-difference assertion of Conjecture 28. Differences are in ℤ,
including the step at n = 0; no reversal closure or recurrence is assumed. -/
def claim : Prop :=
  ∀ (A : Type) [Fintype A] (x : ℕ → A),
    (∃ C : ℕ, ∀ n : ℕ, (wordFactorSet x n).card ≤ C * (n + 1)) →
      ∃ B : ℕ, ∀ n : ℕ,
        Int.natAbs ((reflectionComplexity x (n + 1) : ℤ) -
          (reflectionComplexity x n : ℤ)) ≤ B

theorem result : claim := by
  intro A inst x hx
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := Scalar.biinfinite_bounded_differences (mirrorWord x) (2 * C + 1)
    (mirrorFactorLinear x C hC)
  exact reflectionBoundOfMirrorBound x D hD

end D5.S1.Words.Complexity.AlloucheReflectionComplexityConjecture28
