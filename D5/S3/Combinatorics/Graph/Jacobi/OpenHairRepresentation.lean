/- GID: D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation
   mirror-E: none(waiver:actual-incidence-tree-representation)
   anchors: []
   utility: none
   digest: Connected acyclic finite flag trees admit literal binary hair-tree models. -/

import D5.S3.Combinatorics.Graph.Jacobi.HairPlacement
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual cyclic vertex orbits and their flag incidence graph retain loops and parallel edges. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi

/-- A literal isomorphism of open flag graphs, including the distinguished root. -/
structure OpenHairIso (L R : OpenHair) where
  flagEquiv : L.Flag ≃ R.Flag
  root_eq : flagEquiv L.root = R.root
  edge_eq : ∀ f, R.edge (flagEquiv f) = flagEquiv (L.edge f)
  next_eq : ∀ f, R.next (flagEquiv f) = flagEquiv (L.next f)
  color_eq : ∀ f, R.color (flagEquiv f) = L.color f

namespace OpenHair

private theorem next_injective (T : OpenHair) : Function.Injective T.next := by
  intro f g h
  have hh := congrArg (fun x => T.next (T.next x)) h
  simpa only [T.next_cube] using hh

private theorem edge_root (T : OpenHair) : T.edge T.root = T.root :=
  (T.edge_fixed_iff T.root).mpr rfl

/-- The actual orbit of a flag under the cubic vertex rotor. -/
def orbitSet (T : OpenHair) (f : T.Flag) : Set T.Flag :=
  {g | g = f ∨ g = T.next f ∨ g = T.next (T.next f)}

private theorem orbitSet_next (T : OpenHair) (f : T.Flag) :
    T.orbitSet (T.next f) = T.orbitSet f := by
  ext g
  simp only [orbitSet, Set.mem_ofPred_eq, T.next_cube]
  tauto

/-- Distinct vertices are distinct rotor orbits, with literal flags retained separately. -/
abbrev VertexOrbit (T : OpenHair) := Set.range T.orbitSet

def vertexOf (T : OpenHair) (f : T.Flag) : T.VertexOrbit := ⟨T.orbitSet f, ⟨f, rfl⟩⟩

instance finiteVertexOrbit (T : OpenHair) : Finite T.VertexOrbit := by
  apply Finite.of_surjective T.vertexOf
  rintro ⟨s, f, rfl⟩
  exact ⟨f, rfl⟩

private theorem vertexOf_next (T : OpenHair) (f : T.Flag) :
    T.vertexOf (T.next f) = T.vertexOf f :=
  Subtype.ext (T.orbitSet_next f)

private theorem vertexOf_eq_iff (T : OpenHair) (f g : T.Flag) :
    T.vertexOf f = T.vertexOf g ↔
      g = f ∨ g = T.next f ∨ g = T.next (T.next f) := by
  constructor
  · intro h
    have hs : T.orbitSet f = T.orbitSet g := congrArg Subtype.val h
    have hg : g ∈ T.orbitSet g := Or.inl rfl
    rw [← hs] at hg
    exact hg
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact (T.vertexOf_next f).symm
    · exact ((T.vertexOf_next (T.next f)).trans (T.vertexOf_next f)).symm

/-- Incidence vertices and individual flags occupy separate summands. Every actual
edge has its own two flag vertices, so loops and parallel edges are retained. -/
abbrev IncidenceVertex (T : OpenHair) := T.VertexOrbit ⊕ T.Flag

def incidence (T : OpenHair) : SimpleGraph T.IncidenceVertex where
  Adj
    | .inl v, .inr f => T.vertexOf f = v
    | .inr f, .inl v => T.vertexOf f = v
    | .inr f, .inr g => f ≠ g ∧ T.edge f = g
    | .inl _, .inl _ => False
  symm := by
    constructor
    intro x y h
    rcases x with v | f <;> rcases y with w | g
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by rw [← h.2, T.edge_involutive]⟩
  loopless := by
    constructor
    intro x
    rcases x with v | f
    · exact id
    · exact fun h => h.1 rfl

private theorem incidence_vertex_flag (T : OpenHair) (f : T.Flag) :
    T.incidence.Adj (.inl (T.vertexOf f)) (.inr f) := rfl

private theorem incidence_mates (T : OpenHair) (f : T.Flag) (hf : f ≠ T.root) :
    T.incidence.Adj (.inr f) (.inr (T.edge f)) := by
  exact ⟨fun h => hf ((T.edge_fixed_iff f).mp h.symm), rfl⟩

/-- Local injectivity prevents a path from folding when its image lies in a tree. -/
private theorem locally_injective_path
    {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (hH : H.IsAcyclic)
    (hlocal : ∀ v a b, G.Adj v a → G.Adj v b → φ a = φ b → a = b)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) : (p.map φ).IsPath := by
  induction p with
  | nil => exact .nil
  | @cons u v w huv p ih =>
    have hparts := (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp
    apply SimpleGraph.Walk.IsPath.cons (ih hparts.1)
    intro hmem
    have he := hH.eq_snd_of_adj_start (ih hparts.1) (φ.map_adj huv.symm) hmem
    cases p with
    | nil => exact (φ.map_adj huv).ne (by simpa using he)
    | @cons v z w hvz q =>
      have huz : u = z := hlocal v u z huv.symm hvz (by simpa using he)
      exact hparts.2 (by simp [huz])

private theorem locally_injective_injective
    {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (hG : G.Connected) (hH : H.IsAcyclic)
    (hlocal : ∀ v a b, G.Adj v a → G.Adj v b → φ a = φ b → a = b) :
    Function.Injective φ := by
  classical
  intro u v huv
  let p := (hG u v).some.toPath
  have hp := locally_injective_path φ hH hlocal p.val p.property
  have hn := hp.nil_iff_eq.mpr huv
  have hl : p.val.length = 0 := by simpa using hn
  exact (SimpleGraph.Walk.length_eq_zero_iff.mp hl).eq

/-- Closure under the two actual flag permutations detects a connected open graph. -/
private def Generated (T : OpenHair) : Prop :=
  ∀ P : T.Flag → Prop, P T.root →
    (∀ f, P f → P (T.next f)) → (∀ f, P f → P (T.edge f)) → ∀ f, P f

private theorem connected_of_generated (T : OpenHair) (h : T.Generated) :
    T.incidence.Connected := by
  let : Nonempty T.IncidenceVertex := ⟨.inr T.root⟩
  let P := fun f => T.incidence.Reachable (.inr T.root) (.inr f)
  have hall : ∀ f, P f := by
    apply h P (SimpleGraph.Reachable.refl _)
    · intro f hf
      exact hf.trans ((T.incidence_vertex_flag f).symm.reachable.trans
        (show T.incidence.Adj (.inl (T.vertexOf f)) (.inr (T.next f)) from
          T.vertexOf_next f).reachable)
    · intro f hf
      by_cases hr : f = T.root
      · simpa [hr, T.edge_root] using hf
      · exact hf.trans (T.incidence_mates f hr).reachable
  have hv : ∀ x, T.incidence.Reachable (.inr T.root) x := by
    rintro (⟨s, f, rfl⟩ | f)
    · exact (hall f).trans (T.incidence_vertex_flag f).symm.reachable
    · exact hall f
  exact SimpleGraph.Connected.mk (fun x y => (hv x).symm.trans (hv y))

private theorem model_generated (t : HairTree Color) : t.model.Generated := by
  induction t with
  | leaf c =>
    intro P hr hn he f
    cases f
    exact hr
  | node l r il ir =>
    intro P hr hn he f
    have h1 : P (.inl 1) := hn (.inl 0) hr
    have h2 : P (.inl 2) := hn (.inl 1) h1
    have hL : ∀ g : l.model.Flag, P (.inr (.inl g)) := by
      apply il (fun g => P (.inr (.inl g)))
      · simpa [HairTree.model, node, nodeEdge] using he (.inl 1) h1
      · intro g hg
        exact hn (.inr (.inl g)) hg
      · intro g hg
        by_cases hgroot : g = l.model.root
        · simpa [hgroot, edge_root] using hg
        · simpa [HairTree.model, node, nodeEdge, hgroot] using he (.inr (.inl g)) hg
    have hR : ∀ g : r.model.Flag, P (.inr (.inr g)) := by
      apply ir (fun g => P (.inr (.inr g)))
      · simpa [HairTree.model, node, nodeEdge] using he (.inl 2) h2
      · intro g hg
        exact hn (.inr (.inr g)) hg
      · intro g hg
        by_cases hgroot : g = r.model.root
        · simpa [hgroot, edge_root] using hg
        · simpa [HairTree.model, node, nodeEdge, hgroot] using he (.inr (.inr g)) hg
    rcases f with i | f
    · fin_cases i
      · exact hr
      · exact h1
      · exact h2
    · rcases f with f | f
      · exact hL f
      · exact hR f

private theorem model_connected (t : HairTree Color) : t.model.incidence.Connected :=
  connected_of_generated _ (model_generated t)

private theorem generated_of_connected (T : OpenHair) (hc : T.incidence.Connected) :
    T.Generated := by
  intro P hr hn he
  let Q : T.IncidenceVertex → Prop
    | .inl v => ∀ f, T.vertexOf f = v → P f
    | .inr f => P f
  have hstep : ∀ x y, T.incidence.Adj x y → Q x → Q y := by
    rintro (v | f) (w | g) hadj hx
    · exact False.elim hadj
    · exact hx g hadj
    · intro g hg
      have hv : T.vertexOf f = T.vertexOf g := hadj.trans hg.symm
      rcases (T.vertexOf_eq_iff f g).mp hv with rfl | rfl | rfl
      · exact hx
      · exact hn f hx
      · exact hn (T.next f) (hn f hx)
    · exact hadj.2 ▸ he f hx
  have hwalk : ∀ {x y} (p : T.incidence.Walk x y), Q x → Q y := by
    intro x y p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx => ih (hstep _ _ h hx)
  intro f
  exact hwalk (hc (.inr T.root) (.inr f)).some hr

private theorem mapped_vertex_eq {S T : OpenHair}
    (φ : S.Flag → T.Flag) (hn : ∀ f, T.next (φ f) = φ (S.next f))
    {f g : S.Flag} (h : S.vertexOf f = S.vertexOf g) :
    T.vertexOf (φ f) = T.vertexOf (φ g) := by
  rcases (S.vertexOf_eq_iff f g).mp h with rfl | rfl | rfl
  · rfl
  · rw [← hn, T.vertexOf_next]
  · rw [← hn, ← hn, T.vertexOf_next, T.vertexOf_next]

private noncomputable def mappedVertex {S T : OpenHair}
    (φ : S.Flag → T.Flag) (v : S.VertexOrbit) : T.VertexOrbit :=
  T.vertexOf (φ v.property.choose)

private theorem mappedVertex_vertexOf {S T : OpenHair}
    (φ : S.Flag → T.Flag) (hn : ∀ f, T.next (φ f) = φ (S.next f)) (f : S.Flag) :
    mappedVertex φ (S.vertexOf f) = T.vertexOf (φ f) := by
  apply mapped_vertex_eq φ hn
  apply Subtype.ext
  exact (S.vertexOf f).property.choose_spec

private theorem rotor_injective {S T : OpenHair}
    (φ : S.Flag → T.Flag) (hn : ∀ f, T.next (φ f) = φ (S.next f))
    (hc : ∀ f, T.color (φ f) = S.color f)
    {f g : S.Flag} (hv : S.vertexOf f = S.vertexOf g) (he : φ f = φ g) : f = g := by
  have hfix : ∀ a, T.next (φ a) = φ a → S.next a = a := by
    intro a ha
    by_contra hs
    have hnone := (S.color_none_iff a).mpr hs
    have ht := (T.color_none_iff (φ a)).mp ((hc a).trans hnone)
    exact ht ha
  rcases (S.vertexOf_eq_iff f g).mp hv with rfl | rfl | rfl
  · rfl
  · exact (hfix f ((hn f).trans he.symm)).symm
  · have hsq : T.next (T.next (φ f)) = φ f := by rw [hn, hn, he]
    have hf : S.next f = f := hfix f (by
      have hh := congrArg T.next hsq
      simpa only [T.next_cube] using hh.symm)
    simp [hf]

private noncomputable def incidenceMap {S T : OpenHair}
    (φ : S.Flag → T.Flag)
    (hn : ∀ f, T.next (φ f) = φ (S.next f))
    (he : ∀ f, T.edge (φ f) = φ (S.edge f))
    (hr : ∀ f, φ f = T.root → f = S.root) : S.incidence →g T.incidence where
  toFun
    | .inl v => .inl (mappedVertex φ v)
    | .inr f => .inr (φ f)
  map_rel' := by
    rintro (v | f) (w | g) hadj
    · exact False.elim hadj
    · change T.vertexOf (φ g) = mappedVertex φ v
      rw [← mappedVertex_vertexOf φ hn, hadj]
    · change T.vertexOf (φ f) = mappedVertex φ w
      rw [← mappedVertex_vertexOf φ hn, hadj]
    · refine ⟨?_, (he f).trans (congrArg φ hadj.2)⟩
      intro hfg
      have hf : φ f = T.root := (T.edge_fixed_iff (φ f)).mp (by
        rw [he f, hadj.2, hfg])
      have hsr := hr f hf
      exact hadj.1 (by simpa [hsr, S.edge_root] using hadj.2)

private theorem incidenceMap_local {S T : OpenHair}
    (φ : S.Flag → T.Flag)
    (hn : ∀ f, T.next (φ f) = φ (S.next f))
    (he : ∀ f, T.edge (φ f) = φ (S.edge f))
    (hr : ∀ f, φ f = T.root → f = S.root)
    (hc : ∀ f, T.color (φ f) = S.color f) :
    ∀ v a b, S.incidence.Adj v a → S.incidence.Adj v b →
      incidenceMap φ hn he hr a = incidenceMap φ hn he hr b → a = b := by
  rintro (v | f) (a | a) (b | b) ha hb hab
  · exact False.elim ha
  · exact False.elim ha
  · exact False.elim hb
  · change S.vertexOf a = v at ha
    change S.vertexOf b = v at hb
    exact congrArg Sum.inr (rotor_injective φ hn hc (ha.trans hb.symm)
      (Sum.inr.inj hab))
  · change S.vertexOf f = a at ha
    change S.vertexOf f = b at hb
    exact congrArg Sum.inl (ha.symm.trans hb)
  · cases hab
  · cases hab
  · exact congrArg Sum.inr (ha.2.symm.trans hb.2)

/-- A rooted path enters the current actual vertex through its incoming flag. -/
private structure StemPath (T : OpenHair) (f : T.Flag) where
  walk : T.incidence.Walk (.inr T.root) (.inl (T.vertexOf f))
  isPath : walk.IsPath
  incoming : walk.penultimate = .inr f

private def rootStem (T : OpenHair) : StemPath T T.root where
  walk := SimpleGraph.Walk.nil.concat (T.incidence_vertex_flag T.root).symm
  isPath := SimpleGraph.Walk.IsPath.nil.concat (by simp) _
  incoming := by simp

private theorem outgoing_fresh (T : OpenHair) (ha : T.incidence.IsAcyclic)
    {f a : T.Flag} (p : StemPath T f) (hv : T.vertexOf a = T.vertexOf f) (hne : a ≠ f) :
    Sum.inr a ∉ p.walk.support := by
  intro hm
  have hh := ha.eq_penultimate_of_adj_end p.isPath
    (show T.incidence.Adj (.inl (T.vertexOf f)) (.inr a) from hv) hm
  rw [p.incoming] at hh
  exact hne (Sum.inr.inj hh)

private theorem outgoing_ne_root (T : OpenHair) (ha : T.incidence.IsAcyclic)
    {f a : T.Flag} (p : StemPath T f) (hv : T.vertexOf a = T.vertexOf f) (hne : a ≠ f) :
    a ≠ T.root := by
  intro h
  exact T.outgoing_fresh ha p hv hne (h ▸ p.walk.start_mem_support)

private def extendStem (T : OpenHair) (ha : T.incidence.IsAcyclic)
    {f a : T.Flag} (p : StemPath T f) (hv : T.vertexOf a = T.vertexOf f) (hne : a ≠ f) :
    StemPath T (T.edge a) := by
  let h₁ : T.incidence.Adj (.inl (T.vertexOf f)) (.inr a) := hv
  let p₁ := p.walk.concat h₁
  have hp₁ : p₁.IsPath := p.isPath.concat (T.outgoing_fresh ha p hv hne) h₁
  let h₂ := T.incidence_mates a (T.outgoing_ne_root ha p hv hne)
  have hf₂ : Sum.inr (T.edge a) ∉ p₁.support := by
    intro hm
    have hh := ha.eq_penultimate_of_adj_end hp₁ h₂ hm
    simp [p₁] at hh
  let p₂ := p₁.concat h₂
  have hp₂ : p₂.IsPath := hp₁.concat hf₂ h₂
  let h₃ := (T.incidence_vertex_flag (T.edge a)).symm
  have hf₃ : Sum.inl (T.vertexOf (T.edge a)) ∉ p₂.support := by
    intro hm
    have hh := ha.eq_penultimate_of_adj_end hp₂ h₃ hm
    simp [p₂] at hh
  exact ⟨p₂.concat h₃, hp₂.concat hf₃ h₃, by simp⟩

private theorem extendStem_length (T : OpenHair) (ha : T.incidence.IsAcyclic)
    {f a : T.Flag} (p : StemPath T f) (hv : T.vertexOf a = T.vertexOf f) (hne : a ≠ f) :
    (T.extendStem ha p hv hne).walk.length = p.walk.length + 3 := by
  simp [extendStem, SimpleGraph.Walk.length_concat, Nat.add_assoc]
  exact SimpleGraph.Walk.length_concat p.walk
    (show T.incidence.Adj (.inl (T.vertexOf f)) (.inr a) from hv)

private theorem next_next_ne (T : OpenHair) {f : T.Flag} (h : T.next f ≠ f) :
    T.next (T.next f) ≠ f := by
  intro hh
  have hc := congrArg T.next hh
  rw [T.next_cube] at hc
  exact h hc.symm

private theorem edge_ne_root (T : OpenHair) {a : T.Flag} (h : a ≠ T.root) :
    T.edge a ≠ T.root := by
  intro he
  exact h (by simpa only [T.edge_involutive a, T.edge_root] using congrArg T.edge he)

/-- The recursive construction first gives a flag map. Injectivity is proved
from the actual incidence tree, rather than built into a recursive hypothesis. -/
private structure PartialModel (T : OpenHair) (f : T.Flag) where
  tree : HairTree Color
  flag : tree.model.Flag → T.Flag
  root_eq : flag tree.model.root = f
  next_eq : ∀ g, T.next (flag g) = flag (tree.model.next g)
  color_eq : ∀ g, T.color (flag g) = tree.model.color g
  edge_nonroot : ∀ g, g ≠ tree.model.root → T.edge (flag g) = flag (tree.model.edge g)
  nonroot : ∀ g, g ≠ tree.model.root → flag g ≠ T.root

private def leafPartial (T : OpenHair) (f : T.Flag) (c : Color)
    (hn : T.next f = f) (hc : T.color f = some (.ordinary c)) : PartialModel T f where
  tree := .leaf c
  flag := fun _ => f
  root_eq := rfl
  next_eq := fun _ => hn
  color_eq := fun _ => hc
  edge_nonroot := by intro g hg; cases g; exact False.elim (hg rfl)
  nonroot := by intro g hg; cases g; exact False.elim (hg rfl)

private noncomputable def nodePartial (T : OpenHair) (f : T.Flag)
    (hn : T.next f ≠ f) (h₁ : T.next f ≠ T.root) (h₂ : T.next (T.next f) ≠ T.root)
    (L : PartialModel T (T.edge (T.next f)))
    (R : PartialModel T (T.edge (T.next (T.next f)))) : PartialModel T f := by
  let v : Fin 3 → T.Flag := ![f, T.next f, T.next (T.next f)]
  let φ : (HairTree.node L.tree R.tree).model.Flag → T.Flag
    | .inl i => v i
    | .inr (.inl g) => L.flag g
    | .inr (.inr g) => R.flag g
  have hcol : ∀ i, T.color (v i) = none := by
    intro i
    apply (T.color_none_iff _).mpr
    fin_cases i
    · exact hn
    · exact fun h => hn (T.next_injective h)
    · intro h
      exact hn (T.next_injective (T.next_injective h))
  refine ⟨.node L.tree R.tree, φ, rfl, ?_, ?_, ?_, ?_⟩
  · rintro (i | (g | g))
    · fin_cases i
      · rfl
      · rfl
      · exact T.next_cube f
    · exact L.next_eq g
    · exact R.next_eq g
  · rintro (i | (g | g))
    · exact hcol i
    · exact L.color_eq g
    · exact R.color_eq g
  · rintro (i | (g | g)) hg
    · fin_cases i
      · exact False.elim (hg rfl)
      · exact L.root_eq.symm
      · exact R.root_eq.symm
    · by_cases h : g = L.tree.model.root
      · subst g
        simp only [φ, L.root_eq]
        simpa [HairTree.model, node, nodeEdge, v] using T.edge_involutive (T.next f)
      · simpa [φ, HairTree.model, node, nodeEdge, h] using L.edge_nonroot g h
    · by_cases h : g = R.tree.model.root
      · subst g
        simp only [φ, R.root_eq]
        simpa [HairTree.model, node, nodeEdge, v] using T.edge_involutive (T.next (T.next f))
      · simpa [φ, HairTree.model, node, nodeEdge, h] using R.edge_nonroot g h
  · rintro (i | (g | g)) hg
    · fin_cases i
      · exact False.elim (hg rfl)
      · exact h₁
      · exact h₂
    · by_cases h : g = L.tree.model.root
      · simpa [φ, h, L.root_eq] using T.edge_ne_root h₁
      · exact L.nonroot g h
    · by_cases h : g = R.tree.model.root
      · simpa [φ, h, R.root_eq] using T.edge_ne_root h₂
      · exact R.nonroot g h

/-- Ordinary labels are required only on actual univalent vertices. -/
def OrdinaryLeaves (T : OpenHair) : Prop :=
  ∀ f, T.next f = f → ∃ c : Color, T.color f = some (.ordinary c)

private theorem partialModel_exists (T : OpenHair) (ha : T.incidence.IsAcyclic)
    (hc : T.OrdinaryLeaves) (n : ℕ) {f : T.Flag} (p : StemPath T f)
    (hbound : Nat.card T.IncidenceVertex ≤ p.walk.length + n) :
    Nonempty (PartialModel T f) := by
  classical
  induction n generalizing f with
  | zero =>
    let := Fintype.ofFinite T.IncidenceVertex
    have hlt := p.isPath.length_lt
    rw [Nat.card_eq_fintype_card] at hbound
    omega
  | succ n ih =>
    by_cases hf : T.next f = f
    · obtain ⟨c, hcol⟩ := hc f hf
      exact ⟨T.leafPartial f c hf hcol⟩
    · have hv₁ := T.vertexOf_next f
      have hv₂ := (T.vertexOf_next (T.next f)).trans hv₁
      have hn₂ := T.next_next_ne hf
      let pL := T.extendStem ha p hv₁ hf
      let pR := T.extendStem ha p hv₂ hn₂
      have hbL : Nat.card T.IncidenceVertex ≤ pL.walk.length + n := by
        dsimp [pL]
        rw [extendStem_length]
        omega
      have hbR : Nat.card T.IncidenceVertex ≤ pR.walk.length + n := by
        dsimp [pR]
        rw [extendStem_length]
        omega
      obtain ⟨L⟩ := ih pL hbL
      obtain ⟨R⟩ := ih pR hbR
      exact ⟨T.nodePartial f hf (T.outgoing_ne_root ha p hv₁ hf)
        (T.outgoing_ne_root ha p hv₂ hn₂) L R⟩

/-- Every finite connected acyclic actual open flag graph with ordinary leaves
is literally isomorphic to a binary hair-tree model. -/
theorem exists_hairTree_model (T : OpenHair) (ht : T.incidence.IsTree)
    (ho : T.OrdinaryLeaves) :
    ∃ t : HairTree Color, Nonempty (OpenHairIso t.model T) := by
  classical
  obtain ⟨M⟩ := T.partialModel_exists ht.isAcyclic ho (Nat.card T.IncidenceVertex)
    (T.rootStem) (by omega)
  have he : ∀ f, T.edge (M.flag f) = M.flag (M.tree.model.edge f) := by
    intro f
    by_cases hf : f = M.tree.model.root
    · subst f
      simp only [M.root_eq, T.edge_root, edge_root]
    · exact M.edge_nonroot f hf
  have hr : ∀ f, M.flag f = T.root → f = M.tree.model.root := by
    intro f hf
    by_contra hn
    exact M.nonroot f hn hf
  let φ := incidenceMap M.flag M.next_eq he hr
  have hinj := locally_injective_injective φ (model_connected M.tree) ht.isAcyclic
    (incidenceMap_local M.flag M.next_eq he hr M.color_eq)
  have hflag : Function.Injective M.flag := by
    intro f g hfg
    exact Sum.inr.inj (hinj (show φ (.inr f) = φ (.inr g) from congrArg Sum.inr hfg))
  have hsurj : Function.Surjective M.flag := by
    apply generated_of_connected T ht.connected (fun f => ∃ g, M.flag g = f)
    · exact ⟨_, M.root_eq⟩
    · rintro f ⟨g, rfl⟩
      exact ⟨_, (M.next_eq g).symm⟩
    · rintro f ⟨g, rfl⟩
      exact ⟨_, (he g).symm⟩
  exact ⟨M.tree, ⟨{ flagEquiv := Equiv.ofBijective M.flag ⟨hflag, hsurj⟩
                    root_eq := M.root_eq
                    edge_eq := he
                    next_eq := M.next_eq
                    color_eq := M.color_eq }⟩⟩

/-- The number of actual univalent vertices, counted as rotor-fixed flags. -/
noncomputable def leafCount (T : OpenHair) : ℕ := Nat.card {f : T.Flag // T.next f = f}

private def modelLeafEquiv (l r : HairTree Color) :
    {f : (HairTree.node l r).model.Flag // (HairTree.node l r).model.next f = f} ≃
      ({f : l.model.Flag // l.model.next f = f} ⊕
       {f : r.model.Flag // r.model.next f = f}) where
  toFun x := by
    rcases x with ⟨i | (f | f), h⟩
    · exact False.elim (by fin_cases i <;> cases h)
    · exact .inl ⟨f, Sum.inl.inj (Sum.inr.inj h)⟩
    · exact .inr ⟨f, Sum.inr.inj (Sum.inr.inj h)⟩
  invFun
    | .inl f => ⟨.inr (.inl f.val), congrArg (Sum.inr ∘ Sum.inl) f.property⟩
    | .inr f => ⟨.inr (.inr f.val), congrArg (Sum.inr ∘ Sum.inr) f.property⟩
  left_inv x := by
    rcases x with ⟨i | (f | f), h⟩
    · fin_cases i <;> cases h
    · rfl
    · rfl
  right_inv x := by rcases x with f | f <;> rfl

theorem model_leafCount (t : HairTree Color) : t.model.leafCount = t.leafCount := by
  induction t with
  | leaf c => simp [leafCount, HairTree.model, leaf, HairTree.leafCount]
  | node l r il ir =>
    change Nat.card _ = l.leafCount + r.leafCount
    rw [Nat.card_congr (modelLeafEquiv l r), Nat.card_sum]
    exact congrArg₂ (· + ·) il ir

end OpenHair

namespace OpenHairIso

theorem leafCount_eq {S T : OpenHair} (I : OpenHairIso S T) : S.leafCount = T.leafCount := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv I.flagEquiv
  intro f
  rw [I.next_eq]
  exact I.flagEquiv.injective.eq_iff.symm

end OpenHairIso

/-- A genuine ambient inclusion of an arbitrary actual open flag graph with
its stem paired to a separate trivalent parent. No recursive tree data is assumed. -/
structure OpenHairPlacement {F : Type} (G : FlagGraph F) (T : OpenHair) where
  flag : T.Flag ↪ F
  next_flag : ∀ f, G.next (flag f) = flag (T.next f)
  color_flag : ∀ f, G.color (flag f) = T.color f
  edge_nonroot : ∀ f, f ≠ T.root → G.edge (flag f) = flag (T.edge f)
  parent : G.Vertex
  root_pair : G.edge (flag T.root) = parent.flag 0
  parent_disjoint : ∀ i f, parent.flag i ≠ flag f

namespace OpenHairPlacement

/-- Compose the constructed literal flag isomorphism with the actual ambient inclusion. -/
noncomputable def toHairPlacement {F : Type} {G : FlagGraph F} {T : OpenHair}
    (P : OpenHairPlacement G T) {t : HairTree Color} (I : OpenHairIso t.model T) :
    HairPlacement G t where
  flag := I.flagEquiv.toEmbedding.trans P.flag
  next_flag f := (P.next_flag _).trans (congrArg P.flag (I.next_eq f))
  color_flag f := (P.color_flag _).trans (I.color_eq f)
  edge_nonroot f hf := by
    have h : I.flagEquiv f ≠ T.root := fun h =>
      hf (I.flagEquiv.injective (h.trans I.root_eq.symm))
    exact (P.edge_nonroot _ h).trans (congrArg P.flag (I.edge_eq f))
  parent := P.parent
  root_pair := by simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, I.root_eq]
    using P.root_pair
  parent_disjoint i f := P.parent_disjoint i _

end OpenHairPlacement

/-- An arbitrary actual acyclic connected hair component with at least two
ordinary leaves vanishes in the AS/IHX/ordinary-CL quotient, even when the ambient
diagram contains anchored leaves or cycles outside the component. -/
theorem actual_branching_hair_vanishes {F : Type} [Finite F]
    (G : FlagGraph F) (T : OpenHair) (ht : T.incidence.IsTree) (ho : T.OrdinaryLeaves)
    (hl : 2 ≤ T.leafCount) (P : OpenHairPlacement G T) : classOf G = 0 := by
  obtain ⟨t, ⟨I⟩⟩ := T.exists_hairTree_model ht ho
  have hcount : t.leafCount = T.leafCount := (OpenHair.model_leafCount t).symm.trans I.leafCount_eq
  obtain ⟨C⟩ := HairPlacement.extractCherry t (by omega) (P.toHairPlacement I)
  exact cherry_zero G C

end D5.S3.Combinatorics.Graph.Jacobi
