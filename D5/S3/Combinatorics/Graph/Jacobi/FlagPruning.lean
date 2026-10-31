/- GID: D5/S3/Combinatorics/Graph/Jacobi/FlagPruning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/FlagPruning
   mirror-E: none(waiver:actual-flag-leaf-pruning)
   anchors: []
   utility: none
   digest: Actual leaf deletion preserves a core and leaves singly attached flag trees. -/

import D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation
import Mathlib.Data.Set.Finite.Lemmas

/-! Actual flag-counted leaf deletion and its incidence graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi

namespace Pruning

/-- Chronological deletion ranks: before the cut, a vertex has at most one
neighbor still present. Equal ranks are counted as present. -/
private structure LeafRanks {V : Type} (G : SimpleGraph V) where
  rank : V → ℕ
  cut : ℕ
  later_unique : ∀ v, rank v < cut → ∀ a b, G.Adj v a → G.Adj v b →
    rank v ≤ rank a → rank v ≤ rank b → a = b

private theorem acyclic_of_unique_later {V : Type} (G : SimpleGraph V) (rank : V → ℕ)
    (hu : ∀ v a b, G.Adj v a → G.Adj v b → rank v ≤ rank a → rank v ≤ rank b → a = b) :
    G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ c.support} rank
    c.support.finite_toSet ⟨v, c.start_mem_support⟩
  let q := c.rotate m hm
  have hq : q.IsCycle := hc.rotate hm
  have hs : q.snd ∈ c.support :=
    (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support 1)
  have hp : q.penultimate ∈ c.support :=
    (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support (q.length - 1))
  exact hq.snd_ne_penultimate (hu m q.snd q.penultimate
    (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm
    (hmin _ hs) (hmin _ hp))

private theorem deleted_acyclic {V : Type} {G : SimpleGraph V} (P : LeafRanks G) :
    (G.induce {v | P.rank v < P.cut}).IsAcyclic := by
  apply acyclic_of_unique_later _ (fun v => P.rank v.val)
  intro v a b ha hb hra hrb
  exact Subtype.ext (P.later_unique v.val v.property a.val b.val ha hb hra hrb)

private theorem cycle_retained {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    ∀ w ∈ c.support, P.cut ≤ P.rank w := by
  classical
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ c.support} P.rank
    c.support.finite_toSet ⟨v, c.start_mem_support⟩
  have hkeep : P.cut ≤ P.rank m := by
    by_contra hd
    let q := c.rotate m hm
    have hq : q.IsCycle := hc.rotate hm
    have hs : q.snd ∈ c.support :=
      (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support 1)
    have hp : q.penultimate ∈ c.support :=
      (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support (q.length - 1))
    exact hq.snd_ne_penultimate (P.later_unique m (by omega) q.snd q.penultimate
      (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm
      (hmin _ hs) (hmin _ hp))
  exact fun w hw => hkeep.trans (hmin w hw)

/-- A path between retained vertices cannot dip into a deleted vertex: a
minimum-rank internal vertex would have two distinct later neighbors. -/
private theorem retained_path {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hu : P.cut ≤ P.rank u) (hv : P.cut ≤ P.rank v) :
    ∀ w ∈ p.support, P.cut ≤ P.rank w := by
  classical
  intro w hw
  by_contra hbad
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ p.support} P.rank
    p.support.finite_toSet ⟨u, p.start_mem_support⟩
  have hdel : P.rank m < P.cut := lt_of_le_of_lt (hmin w hw) (by omega)
  obtain ⟨l, r, hl, hr, happ⟩ := hp.mem_support_iff_exists_append.mp hm
  have hln : ¬l.Nil := by
    intro hnil
    have heq := hnil.eq
    subst m
    omega
  have hrn : ¬r.Nil := by
    intro hnil
    have heq := hnil.eq
    subst v
    omega
  have hal : l.penultimate ∈ p.support := by
    rw [happ]
    exact l.support_subset_support_append_left r (l.getVert_mem_support _)
  have hbr : r.snd ∈ p.support := by
    rw [happ]
    exact l.support_subset_support_append_right r (r.getVert_mem_support 1)
  have heq := P.later_unique m hdel l.penultimate r.snd
    (l.adj_penultimate hln).symm (r.adj_snd hrn) (hmin _ hal) (hmin _ hbr)
  have hne := (happ ▸ hp).ne_of_mem_support_of_append
    (r.adj_snd hrn).ne' (l.getVert_mem_support (l.length - 1)) (r.getVert_mem_support 1)
  exact hne heq

private theorem retained_connected {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    (hc : G.Connected) (hne : ∃ v, P.cut ≤ P.rank v) :
    (G.induce {v | P.cut ≤ P.rank v}).Connected := by
  classical
  let : Nonempty {v | P.cut ≤ P.rank v} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  obtain ⟨p, hp⟩ := hc.exists_isPath u.val v.val
  exact (p.induce _ (retained_path P p hp u.property v.property)).reachable

private theorem boundary_walk {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {u v : V} (p : G.Walk u v) : p.IsPath →
    (∀ w ∈ p.support, P.rank w < P.cut) → ∀ a b,
    G.Adj u a → G.Adj v b → P.rank u ≤ P.rank a → P.cut ≤ P.rank b →
    a ∉ p.support → u = v ∧ a = b := by
  classical
  induction p with
  | @nil u =>
    intro hp hall a b ha hb hra hrb hnot
    exact ⟨rfl, P.later_unique u (hall u (by simp)) a b ha hb hra (by
      have := hall u (by simp)
      omega)⟩
  | @cons u v w huv p ih =>
    intro hp hall a b ha hb hra hrb hnot
    have hparts := (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp
    have hu : P.rank u < P.cut := hall u (by simp)
    have hdesc : P.rank v < P.rank u := by
      by_contra hh
      have heq := P.later_unique u hu a v ha huv hra (by omega)
      exact hnot (by simp [heq, p.start_mem_support])
    have hrec := ih hparts.1 (fun z hz => hall z (by simp [hz]))
      u b huv.symm hb (le_of_lt hdesc) hrb hparts.2
    have hbdel : P.rank b < P.cut := hrec.2 ▸ hu
    omega

end Pruning

namespace FlagGraph

def orbitSet {F : Type} (G : FlagGraph F) (f : F) : Set F :=
  {g | g = f ∨ g = G.next f ∨ g = G.next (G.next f)}

abbrev VertexOrbit {F : Type} (G : FlagGraph F) := Set.range G.orbitSet

def vertexOf {F : Type} (G : FlagGraph F) (f : F) : G.VertexOrbit :=
  ⟨G.orbitSet f, ⟨f, rfl⟩⟩

instance finiteVertexOrbit {F : Type} [Finite F] (G : FlagGraph F) : Finite G.VertexOrbit := by
  apply Finite.of_surjective G.vertexOf
  rintro ⟨s, f, rfl⟩
  exact ⟨f, rfl⟩

private theorem vertexOf_next {F : Type} (G : FlagGraph F) (f : F) :
    G.vertexOf (G.next f) = G.vertexOf f := by
  apply Subtype.ext
  change G.orbitSet (G.next f) = G.orbitSet f
  ext g
  simp only [orbitSet, Set.mem_ofPred_eq, G.next_cube]
  tauto

private theorem vertexOf_eq_iff {F : Type} (G : FlagGraph F) (f g : F) :
    G.vertexOf f = G.vertexOf g ↔
      g = f ∨ g = G.next f ∨ g = G.next (G.next f) := by
  constructor
  · intro h
    have hs : G.orbitSet f = G.orbitSet g := congrArg Subtype.val h
    have hg : g ∈ G.orbitSet g := Or.inl rfl
    rw [← hs] at hg
    exact hg
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact (G.vertexOf_next f).symm
    · exact ((G.vertexOf_next (G.next f)).trans (G.vertexOf_next f)).symm

abbrev IncidenceVertex {F : Type} (G : FlagGraph F) := G.VertexOrbit ⊕ F

def incidence {F : Type} (G : FlagGraph F) : SimpleGraph G.IncidenceVertex where
  Adj
    | .inl v, .inr f => G.vertexOf f = v
    | .inr f, .inl v => G.vertexOf f = v
    | .inr f, .inr g => G.edge f = g
    | .inl _, .inl _ => False
  symm := ⟨by
    rintro (v | f) (w | g) h
    · exact h
    · exact h
    · exact h
    · change G.edge f = g at h
      exact (G.edge_involutive f ▸ congrArg G.edge h).symm⟩
  loopless := ⟨by
    rintro (v | f) h
    · exact h
    · exact G.edge_ne f h⟩

def HasAnchor {F : Type} (G : FlagGraph F) (v : G.VertexOrbit) : Prop :=
  ∃ f i, G.vertexOf f = v ∧ G.color f = some (.anchor i)

/-- This is the actual source stability condition on the multigraph incidence
encoding: a cycle, or two distinct protected anchor vertices. -/
def Stable {F : Type} (G : FlagGraph F) : Prop :=
  (¬G.incidence.IsAcyclic) ∨ ∃ a b, a ≠ b ∧ G.HasAnchor a ∧ G.HasAnchor b

/-- A genuine chronological leaf-pruning sequence, including its terminal
condition. At time i every flag with mate rank at least i is still present,
including both ends of any loop. No desired forest or boundary property is assumed. -/
structure LeafPruning {F : Type} [Finite F] (G : FlagGraph F) where
  steps : ℕ
  rank : G.VertexOrbit → ℕ
  rank_le : ∀ v, rank v ≤ steps
  rank_injective : ∀ v w, rank v < steps → rank w < steps → rank v = rank w → v = w
  each_step : ∀ i, i < steps → ∃ v, rank v = i
  protect_anchor : ∀ v, G.HasAnchor v → rank v = steps
  deletion_degree : ∀ v, rank v < steps →
    Nat.card {f : F // G.vertexOf f = v ∧ rank v ≤ rank (G.vertexOf (G.edge f))} ≤ 1
  terminal_degree : ∀ v, rank v = steps → ¬G.HasAnchor v →
    2 ≤ Nat.card {f : F // G.vertexOf f = v ∧ rank (G.vertexOf (G.edge f)) = steps}

namespace LeafPruning

private theorem deletion_unique {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (v : G.VertexOrbit) (hv : P.rank v < P.steps)
    (f g : F) (hf : G.vertexOf f = v) (hg : G.vertexOf g = v)
    (hrf : P.rank v ≤ P.rank (G.vertexOf (G.edge f)))
    (hrg : P.rank v ≤ P.rank (G.vertexOf (G.edge g))) : f = g := by
  classical
  let X := {a : F // G.vertexOf a = v ∧ P.rank v ≤ P.rank (G.vertexOf (G.edge a))}
  let := Fintype.ofFinite X
  have hc := P.deletion_degree v hv
  rw [Nat.card_eq_fintype_card] at hc
  have hs : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp hc
  exact congrArg Subtype.val (hs.elim (⟨f, hf, hrf⟩ : X) ⟨g, hg, hrg⟩)

private def incidenceRank {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) : G.IncidenceVertex → ℕ
  | .inl v => 3 * P.rank v
  | .inr f =>
    if P.rank (G.vertexOf f) ≤ P.rank (G.vertexOf (G.edge f))
    then 3 * P.rank (G.vertexOf f) + 1
    else 3 * P.rank (G.vertexOf (G.edge f)) + 2

private theorem flagRank_ge_vertex {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (f : F) :
    3 * P.rank (G.vertexOf f) ≤ P.incidenceRank (.inr f) ↔
      P.rank (G.vertexOf f) ≤ P.rank (G.vertexOf (G.edge f)) := by
  simp only [incidenceRank]
  split_ifs <;> omega

private theorem mateRank_lt {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (f : F)
    (hv : P.incidenceRank (.inr f) ≤ 3 * P.rank (G.vertexOf f)) :
    P.incidenceRank (.inr (G.edge f)) < P.incidenceRank (.inr f) := by
  have ht : P.rank (G.vertexOf (G.edge f)) < P.rank (G.vertexOf f) := by
    by_contra h
    have hle : P.rank (G.vertexOf f) ≤ P.rank (G.vertexOf (G.edge f)) := by omega
    simp only [incidenceRank, ite_eq_left hle] at hv
    omega
  simp only [incidenceRank, G.edge_involutive f, ite_eq_right (not_le_of_gt ht),
    ite_eq_left (le_of_lt ht)]
  omega

private def incidenceLeafRanks {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) : Pruning.LeafRanks G.incidence where
  rank := P.incidenceRank
  cut := 3 * P.steps
  later_unique := by
    rintro (v | f) hv (a | a) (b | b) ha hb hra hrb
    · exact False.elim ha
    · exact False.elim ha
    · exact False.elim hb
    · change G.vertexOf a = v at ha
      change G.vertexOf b = v at hb
      have hva : P.rank v ≤ P.rank (G.vertexOf (G.edge a)) := by
        rw [← ha]
        apply (P.flagRank_ge_vertex a).mp
        simpa only [ha, incidenceRank] using hra
      have hvb : P.rank v ≤ P.rank (G.vertexOf (G.edge b)) := by
        rw [← hb]
        apply (P.flagRank_ge_vertex b).mp
        simpa only [hb, incidenceRank] using hrb
      exact congrArg Sum.inr (P.deletion_unique v (by change 3 * P.rank v < 3 * P.steps at hv; omega)
        a b ha hb hva hvb)
    · change G.vertexOf f = a at ha
      change G.vertexOf f = b at hb
      exact congrArg Sum.inl (ha.symm.trans hb)
    · change G.vertexOf f = a at ha
      change G.edge f = b at hb
      have ht := P.mateRank_lt f (by simpa only [incidenceRank, ha] using hra)
      subst b
      omega
    · change G.edge f = a at ha
      change G.vertexOf f = b at hb
      have ht := P.mateRank_lt f (by simpa only [incidenceRank, hb] using hrb)
      subst a
      omega
    · change G.edge f = a at ha
      change G.edge f = b at hb
      exact congrArg Sum.inr (ha.symm.trans hb)

private theorem vertex_retained {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (v : G.VertexOrbit) :
    3 * P.steps ≤ P.incidenceRank (.inl v) ↔ P.rank v = P.steps := by
  simp only [incidenceRank]
  have h := P.rank_le v
  omega

private theorem flag_retained {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (f : F) :
    3 * P.steps ≤ P.incidenceRank (.inr f) ↔
      P.rank (G.vertexOf f) = P.steps ∧ P.rank (G.vertexOf (G.edge f)) = P.steps := by
  have ha := P.rank_le (G.vertexOf f)
  have hb := P.rank_le (G.vertexOf (G.edge f))
  simp only [incidenceRank]
  split_ifs <;> omega

private theorem core_edge {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable) :
    ∃ a b, 3 * P.steps ≤ P.incidenceRank a ∧ 3 * P.steps ≤ P.incidenceRank b ∧
      G.incidence.Adj a b := by
  classical
  rcases hs with hcycle | ⟨a, b, hab, ha, hb⟩
  · change ¬∀ v (c : G.incidence.Walk v v), ¬c.IsCycle at hcycle
    push_neg at hcycle
    obtain ⟨v, c, hcy⟩ := hcycle
    have hr := Pruning.cycle_retained P.incidenceLeafRanks c hcy
    exact ⟨v, c.snd, hr v c.start_mem_support, hr _ (c.getVert_mem_support 1),
      c.adj_snd hcy.not_nil⟩
  · have har := (P.vertex_retained a).mpr (P.protect_anchor a ha)
    have hbr := (P.vertex_retained b).mpr (P.protect_anchor b hb)
    obtain ⟨p, hp⟩ := hc.exists_isPath (.inl a) (.inl b)
    have hn : ¬p.Nil := fun h => hab (Sum.inl.inj h.eq)
    have hr := Pruning.retained_path P.incidenceLeafRanks p hp har hbr
    exact ⟨.inl a, p.snd, har, hr _ (p.getVert_mem_support 1), p.adj_snd hn⟩

private theorem core_connected {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable) :
    (G.incidence.induce {v | 3 * P.steps ≤ P.incidenceRank v}).Connected := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.core_edge hc hs
  exact Pruning.retained_connected P.incidenceLeafRanks hc ⟨a, ha⟩

end LeafPruning

end FlagGraph

end D5.S3.Combinatorics.Graph.Jacobi
