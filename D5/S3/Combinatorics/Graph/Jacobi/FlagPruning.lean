/- GID: D5/S3/Combinatorics/Graph/Jacobi/FlagPruning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/FlagPruning
   mirror-E: none(waiver:actual-flag-leaf-pruning)
   anchors: []
   utility: none
   digest: Actual leaf deletion preserves a core and leaves singly attached flag trees. -/

import D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation
import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks

/-! Actual flag-counted leaf deletion and its incidence graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi


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

theorem vertexOf_next {F : Type} (G : FlagGraph F) (f : F) :
    G.vertexOf (G.next f) = G.vertexOf f := by
  apply Subtype.ext
  change G.orbitSet (G.next f) = G.orbitSet f
  ext g
  simp only [orbitSet, Set.mem_ofPred_eq, G.next_cube]
  tauto

theorem vertexOf_eq_iff {F : Type} (G : FlagGraph F) (f g : F) :
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
      exact congrArg Sum.inr (P.deletion_unique v (by
        change 3 * P.rank v < 3 * P.steps at hv
        omega) a b ha hb hva hvb)
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
    push Not at hcycle
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

private theorem vertex_deleted {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (v : G.VertexOrbit) :
    P.incidenceRank (.inl v) < 3 * P.steps ↔ P.rank v < P.steps := by
  simp only [incidenceRank]
  omega

private theorem flag_deleted {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (f : F) :
    P.incidenceRank (.inr f) < 3 * P.steps ↔
      P.rank (G.vertexOf f) < P.steps ∨ P.rank (G.vertexOf (G.edge f)) < P.steps := by
  have ha := P.rank_le (G.vertexOf f)
  have hb := P.rank_le (G.vertexOf (G.edge f))
  simp only [incidenceRank]
  split_ifs <;> omega

/-- The actual incidence graph left outside the retained hull. It includes
the outside mate flag of each boundary edge, but not that mate's core vertex. -/
abbrev DeletedIncidence {F : Type} [Finite F] {G : FlagGraph F} (P : G.LeafPruning) :=
  G.incidence.induce {x | P.incidenceRank x < 3 * P.steps}

abbrev DeletedComponent {F : Type} [Finite F] {G : FlagGraph F} (P : G.LeafPruning) :=
  P.DeletedIncidence.ConnectedComponent

/-- Only flags at removed original vertices belong to the final component.
The auxiliary incidence component's outside mate flag is excluded. -/
def ComponentFlags {F : Type} [Finite F] {G : FlagGraph F} (P : G.LeafPruning)
    (c : P.DeletedComponent) : Set F :=
  {f | ∃ hv : P.rank (G.vertexOf f) < P.steps,
    (⟨.inl (G.vertexOf f), (P.vertex_deleted _).mpr hv⟩ :
      {x | P.incidenceRank x < 3 * P.steps}) ∈ c}

private theorem component_flag_mem {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} {f : F} (hf : f ∈ P.ComponentFlags c) :
    ∃ hd : P.incidenceRank (.inr f) < 3 * P.steps,
      (⟨.inr f, hd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c := by
  rcases hf with ⟨hv, hm⟩
  refine ⟨(P.flag_deleted f).mpr (Or.inl hv), ?_⟩
  exact c.mem_supp_of_adj_mem_supp hm
    (show P.DeletedIncidence.Adj _ _ from rfl)

private theorem component_flag_owner {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} {f : F}
    (hd : P.incidenceRank (.inr f) < 3 * P.steps)
    (hm : (⟨.inr f, hd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c)
    (hv : P.rank (G.vertexOf f) < P.steps) : f ∈ P.ComponentFlags c := by
  refine ⟨hv, ?_⟩
  exact c.mem_supp_of_adj_mem_supp hm
    (show P.DeletedIncidence.Adj _ _ from rfl)

private theorem component_next_mem {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} {f : F} (hf : f ∈ P.ComponentFlags c) :
    G.next f ∈ P.ComponentFlags c := by
  change (∃ hv : P.rank (G.vertexOf f) < P.steps, _) at hf
  change ∃ hv : P.rank (G.vertexOf (G.next f)) < P.steps, _
  simpa only [ComponentFlags, G.vertexOf_next] using hf

private noncomputable def componentBoundary {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (c : P.DeletedComponent) : Pruning.ComponentBoundary P.incidenceLeafRanks c := by
  apply Classical.choice
  apply Pruning.component_boundary_nonempty P.incidenceLeafRanks hc
  obtain ⟨a, b, ha, hb, hab⟩ := P.core_edge hc hs
  exact ⟨a, ha⟩

private theorem boundary_shape {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent}
    (B : Pruning.ComponentBoundary P.incidenceLeafRanks c) :
    ∃ s : F, B.inside.val = .inr s ∧ B.outside = .inl (G.vertexOf s) := by
  rcases B with ⟨⟨v | f, hdel⟩, hm, (w | g), hkeep, hadj⟩
  · exact False.elim hadj
  · change G.vertexOf g = v at hadj
    have hk := (P.flag_retained g).mp hkeep
    have hd := (P.vertex_deleted v).mp hdel
    rw [hadj] at hk
    omega
  · change G.vertexOf f = w at hadj
    exact ⟨f, rfl, congrArg Sum.inl hadj.symm⟩
  · change G.edge f = g at hadj
    subst g
    have hk := (P.flag_retained (G.edge f)).mp hkeep
    have hfk : 3 * P.steps ≤ P.incidenceRank (.inr f) :=
      (P.flag_retained f).mpr ⟨by simpa only [G.edge_involutive f] using hk.2, hk.1⟩
    change P.incidenceRank (.inr f) < 3 * P.steps at hdel
    omega


/-- The literal outside flag of the unique boundary edge, with the inside
flag and uniqueness derived from deletion rather than postulated. -/
private structure CutData {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (c : P.DeletedComponent) where
  outside : F
  retained : P.rank (G.vertexOf outside) = P.steps
  root_mem : G.edge outside ∈ P.ComponentFlags c
  unique : ∀ f, f ∈ P.ComponentFlags c →
    P.rank (G.vertexOf (G.edge f)) = P.steps → G.edge f = outside

private theorem cutData_nonempty {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (c : P.DeletedComponent) : Nonempty (CutData P c) := by
  classical
  let B := P.componentBoundary hc hs c
  obtain ⟨s, hsi, hso⟩ := P.boundary_shape B
  have hkeep : P.rank (G.vertexOf s) = P.steps := by
    apply (P.vertex_retained _).mp
    have hk : 3 * P.steps ≤ P.incidenceRank B.outside := B.outside_retained
    simpa only [hso] using hk
  have hdel : P.incidenceRank (.inr s) < 3 * P.steps := by
    have hd : P.incidenceRank B.inside.val < 3 * P.steps := B.inside.property
    simpa only [hsi] using hd
  have hsmem : (⟨.inr s, hdel⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c := by
    have he : (⟨.inr s, hdel⟩ : {x | P.incidenceRank x < 3 * P.steps}) = B.inside :=
      Subtype.ext hsi.symm
    rw [he]
    exact B.inside_mem
  have hrdel : P.rank (G.vertexOf (G.edge s)) < P.steps := by
    have := (P.flag_deleted s).mp hdel
    omega
  have hrd := (P.flag_deleted (G.edge s)).mpr (Or.inl hrdel)
  have hrmem : (⟨.inr (G.edge s), hrd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c :=
    c.mem_supp_of_adj_mem_supp hsmem
      (show P.DeletedIncidence.Adj _ _ from rfl)
  refine ⟨⟨s, hkeep, P.component_flag_owner hrd hrmem hrdel, ?_⟩⟩
  intro f hf hk
  obtain ⟨hfd, hfm⟩ := P.component_flag_mem hf
  have hmd := (P.flag_deleted (G.edge f)).mpr (Or.inr (by
    simpa only [G.edge_involutive f] using hf.choose))
  have hmm : (⟨.inr (G.edge f), hmd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c :=
    c.mem_supp_of_adj_mem_supp hfm
      (show P.DeletedIncidence.Adj _ _ from rfl)
  let A : Pruning.ComponentBoundary P.incidenceLeafRanks c :=
    { inside := ⟨.inr (G.edge f), hmd⟩
      inside_mem := hmm
      outside := .inl (G.vertexOf (G.edge f))
      outside_retained := (P.vertex_retained _).mpr hk
      adjacent := rfl }
  have heq := (Pruning.component_boundary_unique P.incidenceLeafRanks A B).1
  exact Sum.inr.inj (heq.trans hsi)

private noncomputable def cutData {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (c : P.DeletedComponent) : CutData P c :=
  Classical.choice (P.cutData_nonempty hc hs c)

private theorem cut_mate_mem {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    {f : F} (hf : f ∈ P.ComponentFlags c) (hne : f ≠ G.edge D.outside) :
    G.edge f ∈ P.ComponentFlags c := by
  have hv : P.rank (G.vertexOf (G.edge f)) < P.steps := by
    have hle := P.rank_le (G.vertexOf (G.edge f))
    by_contra hh
    have heq := D.unique f hf (by omega)
    exact hne (by simpa only [G.edge_involutive f] using congrArg G.edge heq)
  obtain ⟨hd, hm⟩ := P.component_flag_mem hf
  have hmd := (P.flag_deleted (G.edge f)).mpr (Or.inl hv)
  apply P.component_flag_owner hmd _ hv
  exact c.mem_supp_of_adj_mem_supp hm
    (show P.DeletedIncidence.Adj _ _ from rfl)

private noncomputable def cutEdge {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (f : P.ComponentFlags c) : P.ComponentFlags c := by
  classical
  exact if h : f.val = G.edge D.outside then f
    else ⟨G.edge f.val, P.cut_mate_mem D f.property h⟩

/-- Cutting only the unique boundary edge produces an actual open flag graph.
All flags, cyclic orders and labels are inherited literally from the source. -/
private noncomputable def componentHair {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) : OpenHair where
  Flag := P.ComponentFlags c
  finiteFlag := inferInstance
  root := ⟨G.edge D.outside, D.root_mem⟩
  edge := P.cutEdge D
  edge_involutive f := by
    classical
    by_cases hf : f.val = G.edge D.outside
    · simp only [cutEdge, dite_eq_left hf]
    · have hm : G.edge f.val ≠ G.edge D.outside := by
        intro he
        have hfs : f.val = D.outside := G.edge_involutive.injective he
        have hd := f.property.choose
        rw [hfs, D.retained] at hd
        omega
      apply Subtype.ext
      simp only [cutEdge, dite_eq_right hf, dite_eq_right hm, G.edge_involutive f.val]
  edge_fixed_iff f := by
    classical
    by_cases hf : f.val = G.edge D.outside
    · exact ⟨fun _ => Subtype.ext hf, fun _ => by simp only [cutEdge, dite_eq_left hf]⟩
    · constructor
      · intro he
        have hv := congrArg Subtype.val he
        exact False.elim (G.edge_ne f.val (by simpa only [cutEdge, dite_eq_right hf] using hv))
      · intro he
        exact False.elim (hf (congrArg Subtype.val he))
  next f := ⟨G.next f.val, P.component_next_mem f.property⟩
  next_cube f := Subtype.ext (G.next_cube f.val)
  color f := G.color f.val
  color_none_iff f := by
    rw [G.color_none_iff]
    exact ⟨fun hn he => hn (congrArg Subtype.val he),
      fun hn he => hn (Subtype.ext he)⟩

private theorem componentHair_ordinary {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).OrdinaryLeaves := by
  intro f hf
  have hfix : G.next f.val = f.val := congrArg Subtype.val hf
  have hsome : G.color f.val ≠ none := by
    intro hnone
    exact ((G.color_none_iff f.val).mp hnone) hfix
  cases hcolor : G.color f.val with
  | none => exact False.elim (hsome hcolor)
  | some l =>
    cases l with
    | ordinary k => exact ⟨k, hcolor⟩
    | anchor i =>
      have hk := P.protect_anchor (G.vertexOf f.val) ⟨f.val, i, rfl, hcolor⟩
      have hd := f.property.choose
      omega


private theorem component_orbit_image {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (f : (P.componentHair D).Flag) :
    Subtype.val '' (P.componentHair D).orbitSet f = G.orbitSet f.val := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases hg with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  · rintro (rfl | rfl | rfl)
    · exact ⟨f, Or.inl rfl, rfl⟩
    · exact ⟨(P.componentHair D).next f, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨(P.componentHair D).next ((P.componentHair D).next f),
        Or.inr (Or.inr rfl), rfl⟩

private noncomputable def componentVertexMap {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).VertexOrbit ↪ G.VertexOrbit where
  toFun v := ⟨Subtype.val '' v.val, by
    obtain ⟨f, hf⟩ := v.property
    exact ⟨f.val, (P.component_orbit_image D f).symm.trans
      (congrArg (fun s => Subtype.val '' s) hf)⟩⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    exact Subtype.val_injective.image_injective (congrArg Subtype.val h)

private theorem componentVertexMap_vertexOf {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (f : (P.componentHair D).Flag) :
    P.componentVertexMap D ((P.componentHair D).vertexOf f) = G.vertexOf f.val :=
  Subtype.ext (P.component_orbit_image D f)

private theorem componentHair_edge_nonroot {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (f : (P.componentHair D).Flag) (hf : f ≠ (P.componentHair D).root) :
    ((P.componentHair D).edge f).val = G.edge f.val := by
  classical
  have hv : f.val ≠ G.edge D.outside := fun h => hf (Subtype.ext h)
  change (P.cutEdge D f).val = G.edge f.val
  exact congrArg Subtype.val (dite_eq_right (α := P.ComponentFlags c) hv)

private noncomputable def componentNodeMap {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).IncidenceVertex ↪ G.IncidenceVertex :=
  (P.componentVertexMap D).sumMap (Function.Embedding.subtype _)

private theorem componentNodeMap_adj {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    {x y : (P.componentHair D).IncidenceVertex}
    (h : (P.componentHair D).incidence.Adj x y) :
    G.incidence.Adj (P.componentNodeMap D x) (P.componentNodeMap D y) := by
  rcases x with v | f <;> rcases y with w | g
  · exact False.elim h
  · change G.vertexOf g.val = P.componentVertexMap D v
    rw [← P.componentVertexMap_vertexOf D g]
    exact congrArg (P.componentVertexMap D) h
  · change G.vertexOf f.val = P.componentVertexMap D w
    rw [← P.componentVertexMap_vertexOf D f]
    exact congrArg (P.componentVertexMap D) h
  · have hn : f ≠ (P.componentHair D).root := by
      intro hf
      have he := ((P.componentHair D).edge_fixed_iff f).mpr hf
      exact h.1 (he.symm.trans h.2)
    change G.edge f.val = g.val
    exact (P.componentHair_edge_nonroot D f hn).symm.trans (congrArg Subtype.val h.2)

private theorem componentNodeMap_mem {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (x : (P.componentHair D).IncidenceVertex) :
    ∃ hd : P.incidenceRank (P.componentNodeMap D x) < 3 * P.steps,
      (⟨P.componentNodeMap D x, hd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c := by
  rcases x with v | f
  · obtain ⟨f, hf⟩ := v.property
    have he : v = (P.componentHair D).vertexOf f := Subtype.ext hf.symm
    subst v
    have he : P.componentNodeMap D (.inl ((P.componentHair D).vertexOf f)) =
        .inl (G.vertexOf f.val) := congrArg Sum.inl (P.componentVertexMap_vertexOf D f)
    rw [he]
    exact ⟨(P.vertex_deleted _).mpr f.property.choose, f.property.choose_spec⟩
  · exact P.component_flag_mem f.property

private noncomputable def componentNodeHom {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).incidence →g P.DeletedIncidence where
  toFun x := ⟨P.componentNodeMap D x, (P.componentNodeMap_mem D x).choose⟩
  map_rel' h := P.componentNodeMap_adj D h

private theorem componentHair_acyclic {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).incidence.IsAcyclic := by
  apply SimpleGraph.IsAcyclic.comap (P.componentNodeHom D)
  · intro x y h
    exact (P.componentNodeMap D).injective (congrArg Subtype.val h)
  · exact Pruning.deleted_acyclic P.incidenceLeafRanks

private theorem component_flag_not_outside {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    {f : F} (hf : f ∈ P.ComponentFlags c) : f ≠ D.outside := by
  intro h
  have hd := hf.choose
  rw [h, D.retained] at hd
  omega

private theorem component_flag_of_not_outside {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    {f : F} (hd : P.incidenceRank (.inr f) < 3 * P.steps)
    (hm : (⟨.inr f, hd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c)
    (hne : f ≠ D.outside) : f ∈ P.ComponentFlags c := by
  by_cases hv : P.rank (G.vertexOf f) < P.steps
  · exact P.component_flag_owner hd hm hv
  · have hkeep : P.rank (G.vertexOf f) = P.steps := le_antisymm (P.rank_le _) (by omega)
    have hmdel : P.rank (G.vertexOf (G.edge f)) < P.steps := by
      have hh := (P.flag_deleted f).mp hd
      omega
    have hmd := (P.flag_deleted (G.edge f)).mpr (Or.inl hmdel)
    have hmm : (⟨.inr (G.edge f), hmd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c :=
      c.mem_supp_of_adj_mem_supp hm
        (show P.DeletedIncidence.Adj _ _ from rfl)
    have hmf := P.component_flag_owner hmd hmm hmdel
    have heq := D.unique (G.edge f) hmf (by simpa only [G.edge_involutive f] using hkeep)
    exact False.elim (hne (by simpa only [G.edge_involutive f] using heq))

private theorem outside_node_mem {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    ∃ hd : P.incidenceRank (.inr D.outside) < 3 * P.steps,
      (⟨.inr D.outside, hd⟩ : {x | P.incidenceRank x < 3 * P.steps}) ∈ c := by
  obtain ⟨hrd, hrm⟩ := P.component_flag_mem D.root_mem
  have hsd := (P.flag_deleted D.outside).mpr (Or.inr D.root_mem.choose)
  refine ⟨hsd, c.mem_supp_of_adj_mem_supp hrm ?_⟩
  change G.edge (G.edge D.outside) = D.outside
  exact G.edge_involutive D.outside

private noncomputable def outsideNode {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) : c :=
  ⟨⟨.inr D.outside, (P.outside_node_mem D).choose⟩, (P.outside_node_mem D).choose_spec⟩

private noncomputable def componentToComponent {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).IncidenceVertex ↪ c where
  toFun x := ⟨P.componentNodeHom D x, (P.componentNodeMap_mem D x).choose_spec⟩
  inj' := by
    intro x y h
    exact (P.componentNodeMap D).injective (congrArg (fun z => z.val.val) h)

private theorem componentToComponent_ne_outside {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    (x : (P.componentHair D).IncidenceVertex) :
    P.componentToComponent D x ≠ P.outsideNode D := by
  intro h
  have hh := congrArg (fun z => z.val.val) h
  rcases x with v | f
  · change Sum.inl (P.componentVertexMap D v) = Sum.inr D.outside at hh
    cases hh
  · exact P.component_flag_not_outside D f.property (Sum.inr.inj hh)

private noncomputable def trimmedComponent {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :=
  c.toSimpleGraph.induce {P.outsideNode D}ᶜ

private theorem outside_degree_one {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    letI := Fintype.ofFinite (c.toSimpleGraph.neighborSet (P.outsideNode D))
    c.toSimpleGraph.degree (P.outsideNode D) = 1 := by
  classical
  letI := Fintype.ofFinite (c.toSimpleGraph.neighborSet (P.outsideNode D))
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨P.componentToComponent D (.inr (P.componentHair D).root), ?_, ?_⟩
  · change G.edge D.outside = G.edge D.outside
    rfl
  · intro w hw
    have hh : G.incidence.Adj (.inr D.outside) w.val.val := hw
    rcases w with ⟨⟨v | f, hd⟩, hm⟩
    · change G.vertexOf D.outside = v at hh
      have hv := (P.vertex_deleted v).mp hd
      rw [← hh, D.retained] at hv
      omega
    · change G.edge D.outside = f at hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Sum.inr hh.symm

private theorem trimmed_connected {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.trimmedComponent D).Connected := by
  classical
  letI := Fintype.ofFinite (c.toSimpleGraph.neighborSet (P.outsideNode D))
  exact c.connected_toSimpleGraph.induce_compl_singleton_of_degree_eq_one
    (P.outside_degree_one D)

private noncomputable def componentToTrimmed {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).IncidenceVertex ↪ {x : c // x ∈ ({P.outsideNode D} : Set c)ᶜ} where
  toFun x := ⟨P.componentToComponent D x, P.componentToComponent_ne_outside D x⟩
  inj' := by
    intro x y h
    exact (P.componentToComponent D).injective (congrArg Subtype.val h)

private theorem componentToTrimmed_surjective {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    Function.Surjective (P.componentToTrimmed D) := by
  classical
  rintro ⟨⟨⟨v | f, hd⟩, hm⟩, hn⟩
  · obtain ⟨f, hf⟩ := v.property
    have hv : G.vertexOf f = v := Subtype.ext hf
    have hfd : f ∈ P.ComponentFlags c := by
      refine ⟨(P.vertex_deleted _).mp (hv.symm ▸ hd), ?_⟩
      simpa only [hv] using hm
    refine ⟨.inl ((P.componentHair D).vertexOf ⟨f, hfd⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Sum.inl (P.componentVertexMap D _) = Sum.inl v
    rw [P.componentVertexMap_vertexOf D ⟨f, hfd⟩]
    exact congrArg Sum.inl hv
  · have hne : f ≠ D.outside := by
      intro h
      apply hn
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Sum.inr h
    have hf := P.component_flag_of_not_outside D hd hm hne
    refine ⟨.inr ⟨f, hf⟩, ?_⟩
    rfl

private theorem componentNodeMap_adj_iff {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c)
    {x y : (P.componentHair D).IncidenceVertex} :
    G.incidence.Adj (P.componentNodeMap D x) (P.componentNodeMap D y) ↔
      (P.componentHair D).incidence.Adj x y := by
  refine ⟨?_, P.componentNodeMap_adj D⟩
  rcases x with v | f <;> rcases y with w | g
  · exact id
  · intro h
    apply (P.componentVertexMap D).injective
    exact (P.componentVertexMap_vertexOf D g).trans h
  · intro h
    apply (P.componentVertexMap D).injective
    exact (P.componentVertexMap_vertexOf D f).trans h
  · intro h
    change G.edge f.val = g.val at h
    have hn : f ≠ (P.componentHair D).root := by
      intro hf
      have he : g.val = D.outside := by
        rw [← h, show f.val = G.edge D.outside from congrArg Subtype.val hf]
        exact G.edge_involutive D.outside
      exact P.component_flag_not_outside D g.property he
    refine ⟨?_, Subtype.ext ((P.componentHair_edge_nonroot D f hn).trans h)⟩
    intro he
    exact G.edge_ne f.val (h.trans (congrArg Subtype.val he).symm)

private noncomputable def componentIncidenceIso {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).incidence ≃g P.trimmedComponent D where
  toEquiv := Equiv.ofBijective (P.componentToTrimmed D)
    ⟨(P.componentToTrimmed D).injective, P.componentToTrimmed_surjective D⟩
  map_rel_iff' := P.componentNodeMap_adj_iff D

private theorem componentHair_tree {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).incidence.IsTree := by
  refine ⟨?_, P.componentHair_acyclic D⟩
  exact SimpleGraph.Connected.map (P.componentIncidenceIso D).symm.toHom
    (P.componentIncidenceIso D).symm.toEquiv.surjective (P.trimmed_connected D)

private theorem core_flag_at_vertex {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (v : G.VertexOrbit) (hv : P.rank v = P.steps) :
    ∃ f, G.vertexOf f = v ∧ P.rank (G.vertexOf (G.edge f)) = P.steps := by
  classical
  let K := G.incidence.induce {x | 3 * P.steps ≤ P.incidenceRank x}
  let u : {x | 3 * P.steps ≤ P.incidenceRank x} :=
    ⟨.inl v, (P.vertex_retained v).mpr hv⟩
  obtain ⟨a, b, ha, hb, hab⟩ := P.core_edge hc hs
  let aa : {x | 3 * P.steps ≤ P.incidenceRank x} := ⟨a, ha⟩
  let bb : {x | 3 * P.steps ≤ P.incidenceRank x} := ⟨b, hb⟩
  have hcon : K.Connected := P.core_connected hc hs
  have hneigh : ∃ z, K.Adj u z := by
    by_cases hua : u = aa
    · exact ⟨bb, by change G.incidence.Adj u.val b; simpa only [hua] using hab⟩
    · exact (hcon u aa).nonempty_neighborSet_left hua
  obtain ⟨⟨w | f, hk⟩, hadj⟩ := hneigh
  · exact False.elim hadj
  · exact ⟨f, hadj, ((P.flag_retained f).mp hk).2⟩

private theorem outside_next_ne {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    {c : P.DeletedComponent} (D : CutData P c) : G.next D.outside ≠ D.outside := by
  intro hn
  obtain ⟨f, hf, hk⟩ := P.core_flag_at_vertex hc hs (G.vertexOf D.outside) D.retained
  have heq : f = D.outside := by
    rcases (G.vertexOf_eq_iff D.outside f).mp hf.symm with h | h | h
    · exact h
    · simpa only [hn] using h
    · simpa only [hn] using h
  have hd := D.root_mem.choose
  rw [heq] at hk
  omega

private noncomputable def parentVertex {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    {c : P.DeletedComponent} (D : CutData P c) : G.Vertex := by
  have hn := P.outside_next_ne hc hs D
  have h01 : D.outside ≠ G.next D.outside := Ne.symm hn
  have h02 : D.outside ≠ G.next (G.next D.outside) := by
    intro he
    have hh := congrArg G.next he
    exact hn (hh.trans (G.next_cube D.outside))
  have h12 : G.next D.outside ≠ G.next (G.next D.outside) :=
    fun h => h01 (G.next_injective h)
  exact
    { flag := ⟨![D.outside, G.next D.outside, G.next (G.next D.outside)], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
      next_flag := by
        intro i
        fin_cases i
        · rfl
        · rfl
        · exact G.next_cube D.outside }

private theorem parentVertex_owner {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    {c : P.DeletedComponent} (D : CutData P c) (i : Fin 3) :
    G.vertexOf ((P.parentVertex hc hs D).flag i) = G.vertexOf D.outside := by
  fin_cases i
  · rfl
  · exact G.vertexOf_next D.outside
  · exact (G.vertexOf_next (G.next D.outside)).trans (G.vertexOf_next D.outside)

private noncomputable def componentPlacement {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    {c : P.DeletedComponent} (D : CutData P c) :
    OpenHairPlacement G (P.componentHair D) where
  flag := Function.Embedding.subtype _
  next_flag f := rfl
  color_flag f := rfl
  edge_nonroot f hf := (P.componentHair_edge_nonroot D f hf).symm
  parent := P.parentVertex hc hs D
  root_pair := G.edge_involutive D.outside
  parent_disjoint i f := by
    intro he
    have hv := P.parentVertex_owner hc hs D i
    rw [he] at hv
    change G.vertexOf f.val = G.vertexOf D.outside at hv
    have hd := f.property.choose
    rw [hv, D.retained] at hd
    omega

/-- The number of literal univalent flags in a removed component. Anchors
cannot occur here because pruning protects their vertices. -/
noncomputable def componentLeafCount {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (c : P.DeletedComponent) : ℕ :=
  Nat.card {f : P.ComponentFlags c // G.next f.val = f.val}

private theorem componentHair_leafCount {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) {c : P.DeletedComponent} (D : CutData P c) :
    (P.componentHair D).leafCount = P.componentLeafCount c := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl (P.ComponentFlags c))
  intro f
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The extracted actual component and its literal inclusion. The tree,
ordinary labels and unique boundary are conclusions of genuine pruning. -/
structure PrunedComponentHair {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (c : P.DeletedComponent) where
  hair : OpenHair
  placement : OpenHairPlacement G hair
  flag_range : Set.range placement.flag = P.ComponentFlags c
  tree : hair.incidence.IsTree
  ordinary : hair.OrdinaryLeaves
  leafCount_eq : hair.leafCount = P.componentLeafCount c
  unique_boundary : ∀ f, f ∈ P.ComponentFlags c →
    (G.edge f ∉ P.ComponentFlags c ↔ f = placement.flag hair.root)

/-- Construct the open tree and its trivalent ambient placement from source
connectivity, source stability and the actual deletion chronology. -/
noncomputable def extractComponentHair {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (c : P.DeletedComponent) : P.PrunedComponentHair c := by
  let D := P.cutData hc hs c
  refine
    { hair := P.componentHair D
      placement := P.componentPlacement hc hs D
      flag_range := ?_
      tree := P.componentHair_tree D
      ordinary := P.componentHair_ordinary D
      leafCount_eq := P.componentHair_leafCount D
      unique_boundary := ?_ }
  · ext f
    exact ⟨fun ⟨g, hg⟩ => hg ▸ g.property, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
  · intro f hf
    change G.edge f ∉ P.ComponentFlags c ↔ f = G.edge D.outside
    constructor
    · intro h
      by_contra hn
      exact h (P.cut_mate_mem D hf hn)
    · intro h hm
      have he : G.edge f = D.outside := by rw [h, G.edge_involutive]
      exact P.component_flag_not_outside D hm he

/-- A component removed by genuine leaf pruning with at least two ordinary
leaves forces the ambient diagram to vanish in the actual AS/IHX/CL quotient. -/
theorem pruned_branching_component_vanishes {F : Type} [Finite F] (G : FlagGraph F)
    (P : G.LeafPruning) (hc : G.incidence.Connected) (hs : G.Stable)
    (c : P.DeletedComponent) (hl : 2 ≤ P.componentLeafCount c) : classOf G = 0 := by
  let H := P.extractComponentHair hc hs c
  apply actual_branching_hair_vanishes G H.hair H.tree H.ordinary _ H.placement
  rw [H.leafCount_eq]
  exact hl

end LeafPruning

end FlagGraph

end D5.S3.Combinatorics.Graph.Jacobi
