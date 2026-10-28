/- GID: D5/S3/Combinatorics/Graph/Eccentric/DePatraBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/DePatraBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual connected subgraph counts and bridge contraction with a fresh leaf. -/

import D5.S3.Combinatorics.Graph.ErdosGyarfasBridgeContraction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge

open SimpleGraph
open scoped BigOperators

noncomputable section

variable {V W : Type}

/-- Actual connected subgraphs containing every specified vertex. Edges are part of the object. -/
abbrev Containing (G : SimpleGraph V) (s : Set V) :=
  {K : G.Subgraph // K.Connected ∧ s ⊆ K.verts}

def countContaining (G : SimpleGraph V) (s : Set V) : ℕ := Nat.card (Containing G s)

def pairCount (G : SimpleGraph V) (x y : V) : ℕ := countContaining G {x, y}

/-- The target range is the entire vertex type, including the source vertex itself. -/
def eccentricity (G : SimpleGraph V) (x : V) : ℕ := sInf (Set.range (pairCount G x))

def eccentricSum [Fintype V] (G : SimpleGraph V) : ℕ := ∑ x, eccentricity G x

theorem countContaining_pos [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (s : Set V) : 0 < countContaining G s := by
  let K : Containing G s := ⟨SimpleGraph.toSubgraph (G := G) G le_rfl,
    SimpleGraph.Connected.toSubgraph (G := G) le_rfl hG, by intro x hx; trivial⟩
  let : Nonempty (Containing G s) := ⟨K⟩
  exact Nat.card_pos

theorem countContaining_antitone [Finite V] (G : SimpleGraph V) {s t : Set V}
    (h : s ⊆ t) : countContaining G t ≤ countContaining G s := by
  let f : Containing G t → Containing G s := fun K => ⟨K.val, K.property.1,
    h.trans K.property.2⟩
  exact Nat.card_le_card_of_injective f
    (fun K L he => Subtype.ext (congrArg (fun t : Containing G s => t.val) he))

/-- A distinct target excludes the singleton root, regardless of cycles or inducedness. -/
theorem pairCount_lt_root [Finite V] (G : SimpleGraph V) {x y : V} (hne : x ≠ y) :
    pairCount G x y < pairCount G x x := by
  classical
  let := Fintype.ofFinite (Containing G {x, y})
  let := Fintype.ofFinite (Containing G {x, x})
  let f : Containing G {x, y} → Containing G {x, x} := fun K =>
    ⟨K.val, K.property.1, by
      intro z hz
      have hz : z = x := by simpa using hz
      subst z
      exact K.property.2 (by simp)⟩
  let singleton : Containing G {x, x} := ⟨G.singletonSubgraph x,
    Subgraph.singletonSubgraph_connected, by simp⟩
  change Nat.card (Containing G {x, y}) < Nat.card (Containing G {x, x})
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_of_notMem f
    (fun K L he => Subtype.ext
      (congrArg (fun t : Containing G {x, x} => t.val) he)) (b := singleton)
  rintro ⟨K, hK⟩
  have he : K.val = G.singletonSubgraph x := congrArg Subtype.val hK
  have hy := K.property.2 (by simp : y ∈ ({x, y} : Set V))
  rw [he] at hy
  have hy' : y = x := by simpa using hy
  exact hne hy'.symm

theorem pairCount_symm (G : SimpleGraph V) (x y : V) :
    pairCount G x y = pairCount G y x := by rw [pairCount, pairCount, Set.pair_comm]

theorem eccentricity_le_pairCount (G : SimpleGraph V) (x y : V) :
    eccentricity G x ≤ pairCount G x y := csInf_le' ⟨y, rfl⟩

theorem eccentricity_attained (G : SimpleGraph V) (x : V) :
    ∃ y, pairCount G x y = eccentricity G x :=
  csInf_mem (show (Set.range (pairCount G x)).Nonempty from ⟨_, x, rfl⟩)

theorem le_eccentricity (G : SimpleGraph V) (x : V) {n : ℕ}
    (h : ∀ y, n ≤ pairCount G x y) : n ≤ eccentricity G x := by
  apply le_csInf (show (Set.range (pairCount G x)).Nonempty from ⟨_, x, rfl⟩)
  rintro _ ⟨y, rfl⟩
  exact h y

theorem eccentricity_pos [Finite V] {G : SimpleGraph V} (hG : G.Connected) (x : V) :
    0 < eccentricity G x := by
  obtain ⟨y, hy⟩ := eccentricity_attained G x
  rw [← hy]
  exact countContaining_pos hG _

/-- The minimum over the non-root targets, whose existence is explicit. -/
def rootMinimum (G : SimpleGraph V) (r : V) : ℕ :=
  sInf (pairCount G r '' {x | x ≠ r})

theorem rootMinimum_attained (G : SimpleGraph V) (r : V) (h : ∃ x, x ≠ r) :
    ∃ x, x ≠ r ∧ pairCount G r x = rootMinimum G r := by
  change rootMinimum G r ∈ pairCount G r '' {x | x ≠ r}
  apply csInf_mem
  obtain ⟨x, hx⟩ := h
  exact ⟨_, x, hx, rfl⟩

theorem rootMinimum_bounds [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (r : V) (h : ∃ x, x ≠ r) :
    0 < rootMinimum G r ∧ rootMinimum G r < pairCount G r r ∧
      2 ≤ pairCount G r r := by
  obtain ⟨x, hx, he⟩ := rootMinimum_attained G r h
  have hp : 0 < pairCount G r x := countContaining_pos hG _
  have hl := pairCount_lt_root G hx.symm
  rw [he] at hp hl
  omega

/-- A genuinely fresh vertex (none) attached to the chosen vertex of H. -/
def addLeaf (H : SimpleGraph W) (r : W) : SimpleGraph (Option W) where
  Adj x y := match x, y with
    | none, none => False
    | none, some y => y = r
    | some x, none => x = r
    | some x, some y => H.Adj x y
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

abbrev ContractVertex (v : V) := ErdosGyarfasBridgeContraction.ContractVertex v

/-- Source operation: identify u,v, discard their edge, then adjoin a fresh leaf. -/
def contractAddLeaf (G : SimpleGraph V) (u v : V) (huv : u ≠ v) :
    SimpleGraph (Option (ContractVertex v)) :=
  addLeaf (ErdosGyarfasBridgeContraction.contraction G u v) ⟨u, huv⟩

/-- The same operation retaining v as the name of the new leaf. -/
def bridgeShift (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x = v ∧ y = u) ∨ (x = u ∧ y = v) ∨
    (x ≠ v ∧ y ≠ v ∧ (G.Adj x y ∨ (x = u ∧ G.Adj v y) ∨ (y = u ∧ G.Adj x v))))
  symm := ⟨by
    intro x y h
    rcases h with ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
    · exact ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩
    · refine ⟨hne.symm, Or.inr (Or.inr ⟨h.2.1, h.1, ?_⟩)⟩
      rcases h.2.2 with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨h.1, h.2.symm⟩)
      · exact Or.inr (Or.inl ⟨h.1, h.2.symm⟩)⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

open Classical in
def relabelLeaf (v : V) : V ≃ Option (ContractVertex v) where
  toFun x := if h : x = v then none else some ⟨x, h⟩
  invFun x := match x with | none => v | some x => x.val
  left_inv x := by
    by_cases h : x = v <;> simp [h]
  right_inv x := by cases x with
    | none => simp
    | some x => simp [x.property]

theorem bridgeShift_adj_iff (G : SimpleGraph V) (u v : V) (huv : u ≠ v) (x y : V) :
    (bridgeShift G u v).Adj x y ↔
      (contractAddLeaf G u v huv).Adj (relabelLeaf v x) (relabelLeaf v y) := by
  classical
  by_cases hx : x = v <;> by_cases hy : y = v
  · subst x; subst y
    simp [bridgeShift, contractAddLeaf, relabelLeaf, addLeaf]
  · subst x
    simp [bridgeShift, contractAddLeaf, relabelLeaf, addLeaf, hy, Ne.symm hy]
  · subst y
    simp [bridgeShift, contractAddLeaf, relabelLeaf, addLeaf, hx]
  · simp [bridgeShift, contractAddLeaf, relabelLeaf, addLeaf, hx, hy,
      ErdosGyarfasBridgeContraction.contraction, Subtype.ext_iff]

def bridgeShiftIso (G : SimpleGraph V) (u v : V) (huv : u ≠ v) :
    bridgeShift G u v ≃g contractAddLeaf G u v huv where
  toEquiv := relabelLeaf v
  map_rel_iff' := fun {x y} => (bridgeShift_adj_iff G u v huv x y).symm

/-- Arithmetic comparison of both endpoint contributions jointly. -/
theorem endpoint_minima_strict (a b p q : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hp : 0 < p) (hq : 0 < q)
    (hpa : p < a) (hqb : q < b) :
    min ((b + 1) * p) (a * q) + min (b * p) ((a + 1) * q) <
      min (min (2 * b * p) (2 * a * q)) (a * b) + min (b * p) (a * q) := by
  by_cases h : b * p ≤ a * q
  · have h' : b * p ≤ (a + 1) * q := by nlinarith
    have h2 : 2 * b * p ≤ 2 * a * q := by nlinarith
    rw [min_eq_left h', min_eq_left h2, min_eq_left h]
    have hleft : min ((b + 1) * p) (a * q) < 2 * b * p :=
      lt_of_le_of_lt (min_le_left _ _) (by nlinarith)
    have hright : min ((b + 1) * p) (a * q) < a * b :=
      lt_of_le_of_lt (min_le_right _ _) (Nat.mul_lt_mul_of_pos_left hqb (by omega))
    exact Nat.add_lt_add_right (lt_min hleft hright) _
  · have h : a * q ≤ b * p := by omega
    have h' : a * q ≤ (b + 1) * p := by nlinarith
    have h2 : 2 * a * q ≤ 2 * b * p := by nlinarith
    rw [min_eq_right h', min_eq_right h2, min_eq_right h]
    have hleft : min (b * p) ((a + 1) * q) < 2 * a * q :=
      lt_of_le_of_lt (min_le_right _ _) (by nlinarith)
    have hright : min (b * p) ((a + 1) * q) < a * b :=
      lt_of_le_of_lt (min_le_left _ _) (by nlinarith)
    have hh := Nat.add_lt_add_right (lt_min hleft hright) (a * q)
    simpa [Nat.add_comm] using hh


/-- Restriction removes vertices and retains exactly the selected edges of K. -/
def restrict {G : SimpleGraph V} (K : G.Subgraph) (s : Set V) : G.Subgraph :=
  K.induce (K.verts ∩ s)

/-- A connected subgraph containing the sole exit r remains connected on either side.
The argument collapses the other side to r and permits consecutive equal images. -/
theorem restrict_connected {G : SimpleGraph V} (K : G.Subgraph) (s : Set V) (r : V)
    (hK : K.Connected) (hr : r ∈ K.verts) (hrs : r ∈ s)
    (hexit : ∀ x y, G.Adj x y → x ∈ s → y ∉ s → x = r) :
    (restrict K s).Connected := by
  classical
  let f : K.verts → (restrict K s).verts := fun x =>
    if hx : x.val ∈ s then ⟨x.val, x.property, hx⟩ else ⟨r, hr, hrs⟩
  have step : ∀ x y : K.verts, K.coe.Adj x y →
      (restrict K s).coe.Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hx : x.val ∈ s <;> by_cases hy : y.val ∈ s
    · apply Adj.reachable
      change (restrict K s).Adj (f x).val (f y).val
      simpa only [f, hx, hy, dite_true, restrict, Subgraph.induce_adj] using
        (show (x.val ∈ K.verts ∩ s) ∧ (y.val ∈ K.verts ∩ s) ∧ K.Adj x.val y.val from
          ⟨⟨x.property, hx⟩, ⟨y.property, hy⟩, hxy⟩)
    · have he := hexit x.val y.val (K.adj_sub hxy) hx hy
      have hf : f x = f y := by apply Subtype.ext; simp [f, hy, he, hrs]
      rw [hf]
    · have he := hexit y.val x.val (K.adj_sub hxy.symm) hy hx
      have hf : f x = f y := by apply Subtype.ext; simp [f, hx, he, hrs]
      rw [hf]
    · have hf : f x = f y := by simp [f, hx, hy]
      rw [hf]
  have reachable (x y : K.verts) (p : K.coe.Walk x y) :
      (restrict K s).coe.Reachable (f x) (f y) := by
    induction p with
    | nil => rfl
    | @cons x y z h p ih => exact (step x y h).trans ih
  apply Subgraph.connected_iff.mpr
  refine ⟨⟨?_⟩, ⟨r, hr, hrs⟩⟩
  intro x y
  let x0 : K.verts := ⟨x.val, x.property.1⟩
  let y0 : K.verts := ⟨y.val, y.property.1⟩
  have hfx : f x0 = x := by apply Subtype.ext; simp [f, x0, x.property.2]
  have hfy : f y0 = y := by apply Subtype.ext; simp [f, y0, y.property.2]
  obtain ⟨p⟩ := hK x0 y0
  simpa only [hfx, hfy] using reachable x0 y0 p


abbrev RootedWithin (G : SimpleGraph V) (side : Set V) (r : V) (targets : Set V) :=
  {K : G.Subgraph // K.Connected ∧ r ∈ K.verts ∧ targets ⊆ K.verts ∧ K.verts ⊆ side}

theorem restrict_sup_left {G : SimpleGraph V} (K L : G.Subgraph) (S T : Set V) (r : V)
    (hK : K.verts ⊆ S) (hL : L.verts ⊆ T) (hr : r ∈ K.verts)
    (hinter : ∀ x, x ∈ S → x ∈ T → x = r) : restrict (K ⊔ L) S = K := by
  apply Subgraph.ext
  · ext x
    change ((x ∈ K.verts ∨ x ∈ L.verts) ∧ x ∈ S) ↔ x ∈ K.verts
    constructor
    · rintro ⟨hx | hx, hs⟩
      · exact hx
      · have he := hinter x hs (hL hx)
        exact he.symm ▸ hr
    · exact fun hx => ⟨Or.inl hx, hK hx⟩
  · funext x y
    apply propext
    change (((x ∈ K.verts ∨ x ∈ L.verts) ∧ x ∈ S) ∧
      ((y ∈ K.verts ∨ y ∈ L.verts) ∧ y ∈ S) ∧ (K.Adj x y ∨ L.Adj x y)) ↔ K.Adj x y
    constructor
    · rintro ⟨hx, hy, hxy | hxy⟩
      · exact hxy
      · have hxr := hinter x hx.2 (hL (L.edge_vert hxy))
        have hyr := hinter y hy.2 (hL (L.edge_vert hxy.symm))
        exact False.elim (hxy.ne (hxr.trans hyr.symm))
    · intro hxy
      exact ⟨⟨Or.inl (K.edge_vert hxy), hK (K.edge_vert hxy)⟩,
        ⟨Or.inl (K.edge_vert hxy.symm), hK (K.edge_vert hxy.symm)⟩, Or.inl hxy⟩

theorem restrict_sup_reconstruct {G : SimpleGraph V} (K : G.Subgraph) (S T : Set V)
    (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hsplit : ∀ x y, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    restrict K S ⊔ restrict K T = K := by
  apply Subgraph.ext
  · ext x
    change ((x ∈ K.verts ∧ x ∈ S) ∨ (x ∈ K.verts ∧ x ∈ T)) ↔ x ∈ K.verts
    exact ⟨fun h => h.elim And.left And.left,
      fun h => (hcover x).elim (fun hs => Or.inl ⟨h, hs⟩) (fun ht => Or.inr ⟨h, ht⟩)⟩
  · funext x y
    apply propext
    change (((x ∈ K.verts ∧ x ∈ S) ∧ (y ∈ K.verts ∧ y ∈ S) ∧ K.Adj x y) ∨
      ((x ∈ K.verts ∧ x ∈ T) ∧ (y ∈ K.verts ∧ y ∈ T) ∧ K.Adj x y)) ↔ K.Adj x y
    constructor
    · exact fun h => h.elim (fun h => h.2.2) (fun h => h.2.2)
    · intro hxy
      rcases hsplit x y (K.adj_sub hxy) with h | h
      · exact Or.inl ⟨⟨K.edge_vert hxy, h.1⟩, ⟨K.edge_vert hxy.symm, h.2⟩, hxy⟩
      · exact Or.inr ⟨⟨K.edge_vert hxy, h.1⟩, ⟨K.edge_vert hxy.symm, h.2⟩, hxy⟩

/-- An edge-sensitive bijection: rooted subgraphs of a one-vertex union are independent
rooted subgraphs of its two sides. No inducedness assumption is imposed on the subgraphs. -/
def rootedGluingEquiv (G : SimpleGraph V) (S T : Set V) (r : V) (s : Set V)
    (hrs : r ∈ S) (hrt : r ∈ T) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hinter : ∀ x, x ∈ S → x ∈ T → x = r)
    (hsplit : ∀ x y, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    RootedWithin G Set.univ r s ≃
      RootedWithin G S r (s ∩ S) × RootedWithin G T r (s ∩ T) := by
  have exitS : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r := by
    intro x y hxy hx hy
    rcases hsplit x y hxy with h | h
    · exact False.elim (hy h.2)
    · exact hinter x hx h.1
  have exitT : ∀ x y, G.Adj x y → x ∈ T → y ∉ T → x = r := by
    intro x y hxy hx hy
    rcases hsplit x y hxy with h | h
    · exact hinter x h.1 hx
    · exact False.elim (hy h.2)
  let split : RootedWithin G Set.univ r s →
      RootedWithin G S r (s ∩ S) × RootedWithin G T r (s ∩ T) := fun K =>
    (⟨restrict K.val S, restrict_connected K.val S r K.property.1 K.property.2.1 hrs exitS,
      ⟨K.property.2.1, hrs⟩,
      fun _ hx => ⟨K.property.2.2.1 hx.1, hx.2⟩, fun _ hx => hx.2⟩,
     ⟨restrict K.val T, restrict_connected K.val T r K.property.1 K.property.2.1 hrt exitT,
      ⟨K.property.2.1, hrt⟩,
      fun _ hx => ⟨K.property.2.2.1 hx.1, hx.2⟩, fun _ hx => hx.2⟩)
  let glue : RootedWithin G S r (s ∩ S) × RootedWithin G T r (s ∩ T) →
      RootedWithin G Set.univ r s := fun KL =>
    ⟨KL.1.val ⊔ KL.2.val,
      Subgraph.connected_sup KL.1.property.1.preconnected KL.2.property.1.preconnected
        ⟨r, KL.1.property.2.1, KL.2.property.2.1⟩,
      Or.inl KL.1.property.2.1,
      fun x hx => (hcover x).elim
        (fun hs => Or.inl (KL.1.property.2.2.1 ⟨hx, hs⟩))
        (fun ht => Or.inr (KL.2.property.2.2.1 ⟨hx, ht⟩)),
      fun _ _ => Set.mem_univ _⟩
  refine ⟨split, glue, ?_, ?_⟩
  · intro K
    apply Subtype.ext
    exact restrict_sup_reconstruct K.val S T hcover hsplit
  · intro KL
    apply Prod.ext
    · apply Subtype.ext
      exact restrict_sup_left KL.1.val KL.2.val S T r KL.1.property.2.2.2
        KL.2.property.2.2.2 KL.1.property.2.1 hinter
    · apply Subtype.ext
      change restrict (KL.1.val ⊔ KL.2.val) T = KL.2.val
      rw [sup_comm]
      exact restrict_sup_left KL.2.val KL.1.val T S r KL.2.property.2.2.2
        KL.1.property.2.2.2 KL.2.property.2.1 (fun x ht hs => hinter x hs ht)

theorem rootedGluing_count [Finite V] (G : SimpleGraph V) (S T : Set V) (r : V) (s : Set V)
    (hrs : r ∈ S) (hrt : r ∈ T) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hinter : ∀ x, x ∈ S → x ∈ T → x = r)
    (hsplit : ∀ x y, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    Nat.card (RootedWithin G Set.univ r s) =
      Nat.card (RootedWithin G S r (s ∩ S)) * Nat.card (RootedWithin G T r (s ∩ T)) := by
  rw [Nat.card_congr (rootedGluingEquiv G S T r s hrs hrt hcover hinter hsplit), Nat.card_prod]



theorem subgraph_map_connected {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {K : G.Subgraph} (hK : K.Connected) : (K.map f).Connected := by
  let fK : K.coe →g (K.map f).coe := {
    toFun x := ⟨f x.val, Set.mem_image_of_mem f x.property⟩
    map_rel' := by intro x y h; exact ⟨x.val, y.val, h, rfl, rfl⟩ }
  apply Subgraph.connected_iff'.mpr
  apply hK.coe.map fK
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def subgraphIsoEquiv {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.Subgraph ≃ H.Subgraph where
  toFun K := K.map e.toHom
  invFun L := L.map e.symm.toHom
  left_inv K := by
    change (K.map e.toHom).map e.symm.toHom = K
    rw [← Subgraph.map_comp]
    have he : e.symm.toHom.comp e.toHom = Hom.id := by ext x; simp
    rw [he, Subgraph.map_id]
  right_inv L := by
    change (L.map e.symm.toHom).map e.toHom = L
    rw [← Subgraph.map_comp]
    have he : e.toHom.comp e.symm.toHom = Hom.id := by ext x; simp
    rw [he, Subgraph.map_id]

def containingIsoEquiv {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (s : Set V) :
    Containing G s ≃ Containing H (e '' s) where
  toFun K := ⟨K.val.map e.toHom, subgraph_map_connected e.toHom K.property.1,
    Set.image_mono K.property.2⟩
  invFun L := ⟨L.val.map e.symm.toHom, subgraph_map_connected e.symm.toHom L.property.1,
    by intro x hx; exact ⟨e x, L.property.2 ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩⟩
  left_inv K := Subtype.ext ((subgraphIsoEquiv e).left_inv K.val)
  right_inv L := Subtype.ext ((subgraphIsoEquiv e).right_inv L.val)

theorem countContaining_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s : Set V) : countContaining G s = countContaining H (e '' s) :=
  Nat.card_congr (containingIsoEquiv e s)

theorem pairCount_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (x y : V) : pairCount G x y = pairCount H (e x) (e y) := by
  simpa [pairCount, Set.image_pair] using countContaining_iso e {x, y}

theorem eccentricity_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (x : V) : eccentricity G x = eccentricity H (e x) := by
  apply le_antisymm
  · apply le_eccentricity
    intro y
    calc
      eccentricity G x ≤ pairCount G x (e.symm y) := eccentricity_le_pairCount G x _
      _ = pairCount H (e x) y := by simpa using pairCount_iso e x (e.symm y)
  · apply le_eccentricity
    intro y
    exact (eccentricity_le_pairCount H (e x) (e y)).trans_eq (pairCount_iso e x y).symm

theorem eccentricSum_iso [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : eccentricSum G = eccentricSum H := by
  exact Fintype.sum_equiv e.toEquiv _ _ (fun x => eccentricity_iso e x)

/-- The deletion components are the reachability classes containing the bridge endpoints. -/
def QualifyingBridge [Finite V] (G : SimpleGraph V) (u v : V) : Prop :=
  G.Connected ∧ G.IsBridge s(u, v) ∧
    2 ≤ Nat.card {x : V // (G.deleteEdges {s(u, v)}).Reachable u x} ∧
    2 ≤ Nat.card {x : V // (G.deleteEdges {s(u, v)}).Reachable v x}



abbrev Within (G : SimpleGraph V) (side targets : Set V) :=
  {K : G.Subgraph // K.Connected ∧ targets ⊆ K.verts ∧ K.verts ⊆ side}

abbrev RootlessWithin (G : SimpleGraph V) (side : Set V) (r : V) (targets : Set V) :=
  {K : G.Subgraph // K.Connected ∧ r ∉ K.verts ∧ targets ⊆ K.verts ∧ K.verts ⊆ side}

open Classical in
def withinPartitionEquiv (G : SimpleGraph V) (S s : Set V) (r : V) :
    Within G S s ≃ RootlessWithin G S r s ⊕ RootedWithin G S r s where
  toFun K := if hr : r ∈ K.val.verts then
    Sum.inr ⟨K.val, K.property.1, hr, K.property.2.1, K.property.2.2⟩ else
    Sum.inl ⟨K.val, K.property.1, hr, K.property.2.1, K.property.2.2⟩
  invFun K := match K with
    | Sum.inl K => ⟨K.val, K.property.1, K.property.2.2.1, K.property.2.2.2⟩
    | Sum.inr K => ⟨K.val, K.property.1, K.property.2.2.1, K.property.2.2.2⟩
  left_inv K := by by_cases hr : r ∈ K.val.verts <;> simp [hr]
  right_inv K := by
    cases K with
    | inl K => simp [K.property.2.1]
    | inr K => simp [K.property.2.1]

theorem within_count_partition [Finite V] (G : SimpleGraph V) (S s : Set V) (r : V) :
    Nat.card (Within G S s) = Nat.card (RootlessWithin G S r s) +
      Nat.card (RootedWithin G S r s) := by
  rw [Nat.card_congr (withinPartitionEquiv G S s r), Nat.card_sum]

theorem verts_subset_of_root_absent {G : SimpleGraph V} (K : G.Subgraph) (S : Set V) (r : V)
    (hK : K.Connected) (hr : r ∉ K.verts) (x : V) (hx : x ∈ K.verts) (hxs : x ∈ S)
    (hexit : ∀ a b, G.Adj a b → a ∈ S → b ∉ S → a = r) : K.verts ⊆ S := by
  classical
  have step (a b : K.verts) (hab : K.coe.Adj a b) (ha : a.val ∈ S) : b.val ∈ S := by
    by_contra hb
    have he := hexit a.val b.val (K.adj_sub hab) ha hb
    exact hr (he ▸ a.property)
  have walkWithin {a b : K.verts} (p : K.coe.Walk a b) : a.val ∈ S → b.val ∈ S := by
    induction p with
    | nil => exact id
    | @cons a b c h p ih => exact fun ha => ih (step a b h ha)
  intro y hy
  obtain ⟨p⟩ := hK ⟨x, hx⟩ ⟨y, hy⟩
  exact walkWithin p hxs

def rootlessRestrictionEquiv (G : SimpleGraph V) (S s : Set V) (r : V)
    (x : V) (hx : x ∈ s) (hxs : x ∈ S)
    (hexit : ∀ a b, G.Adj a b → a ∈ S → b ∉ S → a = r) :
    RootlessWithin G Set.univ r s ≃ RootlessWithin G S r s where
  toFun K := ⟨K.val, K.property.1, K.property.2.1, K.property.2.2.1,
    verts_subset_of_root_absent K.val S r K.property.1 K.property.2.1
      x (K.property.2.2.1 hx) hxs hexit⟩
  invFun K := ⟨K.val, K.property.1, K.property.2.1, K.property.2.2.1,
    fun _ _ => Set.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact counting for arbitrary targets on one side of a one-vertex union. The local
rootless contribution is unchanged; the rooted contribution is multiplied by the other side. -/
theorem within_gluing_count [Finite V] (G : SimpleGraph V) (S T s : Set V) (r : V)
    (hrs : r ∈ S) (hrt : r ∈ T) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hinter : ∀ x, x ∈ S → x ∈ T → x = r)
    (hsplit : ∀ x y, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hs : s ⊆ S) (x : V) (hx : x ∈ s) :
    Nat.card (Within G Set.univ s) = Nat.card (RootlessWithin G S r s) +
      Nat.card (RootedWithin G S r s) * Nat.card (RootedWithin G T r (s ∩ T)) := by
  have exitS : ∀ a b, G.Adj a b → a ∈ S → b ∉ S → a = r := by
    intro a b hab ha hb
    rcases hsplit a b hab with h | h
    · exact False.elim (hb h.2)
    · exact hinter a ha h.1
  have he : s ∩ S = s := Set.inter_eq_left.mpr hs
  rw [within_count_partition G Set.univ s r,
    Nat.card_congr (rootlessRestrictionEquiv G S s r x hx (hs hx) exitS),
    rootedGluing_count G S T r s hrs hrt hcover hinter hsplit, he]



def deletedSide (G : SimpleGraph V) (u v r : V) : Set V :=
  {x | (G.deleteEdges {s(u, v)}).Reachable r x}

theorem deletedSide_cover {G : SimpleGraph V} (hG : G.Connected) (u v : V) :
    ∀ x, x ∈ deletedSide G u v u ∨ x ∈ deletedSide G u v v := by
  let D := G.deleteEdges {s(u, v)}
  have step (x y : V) (hxy : G.Adj x y)
      (hx : D.Reachable u x ∨ D.Reachable v x) : D.Reachable u y ∨ D.Reachable v y := by
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr Reachable.rfl
      · exact Or.inl Reachable.rfl
    · have hd : D.Adj x y := deleteEdges_adj.mpr ⟨hxy, by simpa using he⟩
      exact hx.elim (fun hx => Or.inl (hx.trans hd.reachable))
        (fun hx => Or.inr (hx.trans hd.reachable))
  have transport {x y : V} (p : G.Walk x y) :
      (D.Reachable u x ∨ D.Reachable v x) → (D.Reachable u y ∨ D.Reachable v y) := by
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (step x y h hx)
  intro x
  obtain ⟨p⟩ := hG u x
  exact transport p (Or.inl Reachable.rfl)

theorem deletedSide_disjoint {G : SimpleGraph V} {u v : V} (hb : G.IsBridge s(u, v)) :
    Disjoint (deletedSide G u v u) (deletedSide G u v v) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hb (hx.trans hy.symm)

theorem deletedSide_connected (G : SimpleGraph V) (u v r : V) :
    ((G.deleteEdges {s(u, v)}).induce (deletedSide G u v r)).Connected := by
  let D := G.deleteEdges {s(u, v)}
  have hs : deletedSide G u v r = (D.connectedComponentMk r).supp := by
    ext x
    change D.Reachable r x ↔ D.connectedComponentMk x = D.connectedComponentMk r
    rw [ConnectedComponent.eq, reachable_comm]
  rw [hs]
  exact (D.connectedComponentMk r).connected_toSimpleGraph

/-- A native bridge with the stipulated two component sizes gives exactly two disjoint
connected deletion components, each with a non-root vertex. -/
theorem qualifying_components [Finite V] {G : SimpleGraph V} {u v : V}
    (h : QualifyingBridge G u v) :
    G.Adj u v ∧
    (∀ x, x ∈ deletedSide G u v u ∨ x ∈ deletedSide G u v v) ∧
    Disjoint (deletedSide G u v u) (deletedSide G u v v) ∧
    ((G.deleteEdges {s(u, v)}).induce (deletedSide G u v u)).Connected ∧
    ((G.deleteEdges {s(u, v)}).induce (deletedSide G u v v)).Connected ∧
    (∃ x ∈ deletedSide G u v u, x ≠ u) ∧ (∃ x ∈ deletedSide G u v v, x ≠ v) := by
  have nonroot (r : V) (hc : 2 ≤ Nat.card {x : V //
      (G.deleteEdges {s(u, v)}).Reachable r x}) : ∃ x ∈ deletedSide G u v r, x ≠ r := by
    by_contra hn
    have hs : Subsingleton {x : V // (G.deleteEdges {s(u, v)}).Reachable r x} := by
      constructor
      intro x y
      have hx : x.val = r := by
        by_contra hx
        exact hn ⟨x.val, x.property, hx⟩
      have hy : y.val = r := by
        by_contra hy
        exact hn ⟨y.val, y.property, hy⟩
      exact Subtype.ext (hx.trans hy.symm)
    let := hs
    let := Fintype.ofFinite {x : V // (G.deleteEdges {s(u, v)}).Reachable r x}
    let : Unique {x : V // (G.deleteEdges {s(u, v)}).Reachable r x} := {
      default := ⟨r, Reachable.rfl⟩
      uniq := fun _ => Subsingleton.elim _ _ }
    have hl : Fintype.card {x : V // (G.deleteEdges {s(u, v)}).Reachable r x} = 1 :=
      Fintype.card_unique
    rw [Nat.card_eq_fintype_card] at hc
    omega
  exact ⟨h.2.1.reachable_iff_adj.mp (h.1 u v), deletedSide_cover h.1 u v,
    deletedSide_disjoint h.2.1, deletedSide_connected G u v u,
    deletedSide_connected G u v v, nonroot u h.2.2.1, nonroot v h.2.2.2⟩



/-- Apply the actual-subgraph gluing bijection at the first endpoint of a native bridge.
The second side includes that endpoint and the bridge, in addition to its deletion component. -/
theorem bridge_rooted_count [Finite V] {G : SimpleGraph V} {u v : V}
    (h : QualifyingBridge G u v) (s : Set V) :
    Nat.card (RootedWithin G Set.univ u s) =
      Nat.card (RootedWithin G (deletedSide G u v u) u (s ∩ deletedSide G u v u)) *
      Nat.card (RootedWithin G (insert u (deletedSide G u v v)) u
        (s ∩ insert u (deletedSide G u v v))) := by
  have hparts := qualifying_components h
  apply rootedGluing_count
  · exact Reachable.rfl
  · exact Set.mem_insert u _
  · intro x
    exact (hparts.2.1 x).imp id (Set.mem_insert_of_mem u)
  · intro x hx hy
    rcases Set.mem_insert_iff.mp hy with he | hy
    · exact he
    · exact False.elim (Set.disjoint_left.mp hparts.2.2.1 hx hy)
  · intro x y hxy
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ Reachable.rfl⟩
      · exact Or.inr ⟨Set.mem_insert_of_mem _ Reachable.rfl, Set.mem_insert _ _⟩
    · have hd : (G.deleteEdges {s(u, v)}).Adj x y :=
        deleteEdges_adj.mpr ⟨hxy, by simpa using he⟩
      rcases hparts.2.1 x with hx | hx
      · exact Or.inl ⟨hx, hx.trans hd.reachable⟩
      · exact Or.inr ⟨Set.mem_insert_of_mem u hx,
          Set.mem_insert_of_mem u (hx.trans hd.reachable)⟩


#print axioms bridge_rooted_count
#print axioms qualifying_components
#print axioms within_gluing_count
#print axioms eccentricSum_iso
#print axioms rootedGluing_count
#print axioms rootMinimum_bounds
#print axioms bridgeShiftIso
#print axioms endpoint_minima_strict

end
end D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge
