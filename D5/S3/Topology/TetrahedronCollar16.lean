/- GID: D5/S3/Topology/TetrahedronCollar16
   generality: I
   mirror-B: D5/B/S3/Topology/TetrahedronCollar16
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: A checked tetrahedral collar yields compatible interval and complementary edge regions. -/

import D5.S3.Topology.GraphSubdivisionIntervals
import D5.S3.Topology.TetrahedronCollar16Data
import D5.S3.Topology.PathContiguity
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases

/-! The local ordered tetrahedron of Section 16. Each subdivision vertex is a
nonempty chain of faces of the preceding complex. A row lists the indices of
the members of that chain, and rows are indexed in lexicographic order. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace TetrahedronCollar16

open D5.S3.Topology
open BarycentricGraphDistance

abbrev V₁ := Fin 15
abbrev V₂ := Fin 149
abbrev V₃ := Fin 2745
abbrev Color := Fin 2

private def unpack (key : Nat) : List Nat :=
  ([key / 3375000, key / 22500 % 150, key / 150 % 150, key % 150].filter
    (· != 0)).map (· - 1)

private def pack (l : List Nat) : Nat :=
  ((l.map (· + 1) ++ [0, 0, 0, 0]).take 4).foldl (fun n d => 150 * n + d) 0

private def key₁ : Nat → Nat := Data.row Data.rows1
private def key₂ : Nat → Nat := Data.row Data.rows2
private def key₃ (i : Nat) : Nat := Data.row Data.rows3 i / 64

def face₁ (i : V₁) : List Nat := unpack (key₁ i)
def face₂ (i : V₂) : List Nat := unpack (key₂ i)
def face₃ (i : V₃) : List Nat := unpack (key₃ i)

private def searchKey (key : Nat → Nat) (target : Nat) :
    Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if hi ≤ lo then none else
      let mid := (lo + hi) / 2
      if key mid = target then some mid
      else if key mid < target then searchKey key target fuel (mid + 1) hi
      else searchKey key target fuel lo mid

private def findFace {n : Nat} (key : Nat → Nat) (l : List Nat) : Option (Fin n) :=
  match searchKey key (pack l) 13 0 n with
  | none => none
  | some i =>
    if hi : i < n then
      if unpack (key i) = l then some ⟨i, hi⟩ else none
    else none

private theorem findFace_sound {n : Nat} (key : Nat → Nat) {l : List Nat} {i : Fin n}
    (h : findFace key l = some i) : unpack (key i) = l := by
  unfold findFace at h
  split at h
  · contradiction
  · split at h
    · split at h
      · rename_i he
        cases Option.some.inj h
        exact he
      · contradiction
    · contradiction

/-- Structural insertion sort permits direct kernel reduction of the short face lists. -/
private def ascending (l : List Nat) : List Nat := l.insertionSort (· ≤ ·)

/-- The strict inclusion relation on increasing lists. -/
def Proper (s t : List Nat) : Prop := List.Sublist s t ∧ s ≠ t

instance (s t : List Nat) : Decidable (Proper s t) := by
  unfold Proper
  infer_instance

private def properSubfaces (l : List Nat) : List (List Nat) :=
  l.sublists.filter (fun s => s != [] && s != l)

private theorem mem_properSubfaces {s l : List Nat} (hne : s ≠ []) (h : Proper s l) :
    s ∈ properSubfaces l := by
  simp [properSubfaces, List.mem_sublists.mpr h.1, hne, h.2]

private def block {n : Nat} (p : Fin n → Bool) (k : Nat) : Bool :=
  (List.range' (64 * k) 64).all fun i => if hi : i < n then p ⟨i, hi⟩ else true

private theorem ofBlocks {n : Nat} {p : Fin n → Bool}
    (h : ∀ k : Fin ((n + 63) / 64), block p k = true) (i : Fin n) : p i = true := by
  have hi := i.isLt
  have hk : i.val / 64 < (n + 63) / 64 := by omega
  have hm : i.val ∈ List.range' (64 * (i.val / 64)) 64 := by
    rw [List.mem_range'_1]
    omega
  have hv := List.all_eq_true.mp (h ⟨i.val / 64, hk⟩) i.val hm
  simpa only [dif_pos hi] using hv

private def RowShape {n : Nat} (prev : Nat) (key : Nat → Nat) (i : Fin n) : Prop :=
  let l := unpack (key i)
  l ≠ [] ∧ l.length ≤ 4 ∧ l.Pairwise (· < ·) ∧ l.all (· < prev) = true ∧
    findFace key l = some i ∧ (i.val + 1 < n → key i < key (i.val + 1))

private instance {n : Nat} (prev : Nat) (key : Nat → Nat) (i : Fin n) :
    Decidable (RowShape prev key i) := by
  unfold RowShape
  infer_instance

private theorem shape₁ (i : V₁) : RowShape 4 key₁ i :=
  of_decide_eq_true (ofBlocks (p := fun j : V₁ => decide (RowShape 4 key₁ j))
    (by intro k; fin_cases k <;> decide +kernel) i)

private theorem shape₂ (i : V₂) : RowShape 15 key₂ i :=
  of_decide_eq_true (ofBlocks (p := fun j : V₂ => decide (RowShape 15 key₂ j))
    (by intro k; fin_cases k <;> decide +kernel) i)

private theorem shape₃ (i : V₃) : RowShape 149 key₃ i :=
  of_decide_eq_true (ofBlocks (p := fun j : V₃ => decide (RowShape 149 key₃ j))
    (by intro k; fin_cases k <;> decide +kernel) i)

private theorem find₁ (i : V₁) : findFace key₁ (face₁ i) = some i :=
  (shape₁ i).2.2.2.2.1

private theorem find₂ (i : V₂) : findFace key₂ (face₂ i) = some i :=
  (shape₂ i).2.2.2.2.1

private theorem find₃ (i : V₃) : findFace key₃ (face₃ i) = some i :=
  (shape₃ i).2.2.2.2.1

theorem face₃_injective : Function.Injective face₃ := by
  intro a b h
  apply Option.some.inj
  rw [← find₃ a, ← find₃ b, h]

private def boundedFace {n : Nat} (key : Nat → Nat) (i : Nat) : List Nat :=
  if i < n then unpack (key i) else []

def Next {n : Nat} (key : Nat → Nat) (s t : Nat) : Prop :=
  s < n ∧ t < n ∧ Proper (boundedFace (n := n) key s) (boundedFace (n := n) key t)

private instance {n : Nat} (key : Nat → Nat) (s t : Nat) :
    Decidable (Next (n := n) key s t) := by unfold Next; infer_instance

/-- The certificate orders members by index. For reasoning about a flag,
read them in increasing order of the cardinality of the preceding face. -/
def byInclusion {n : Nat} (prev : Nat → Nat) (l : List Nat) : List Nat :=
  l.insertionSort (fun a b =>
    (boundedFace (n := n) prev a).length ≤ (boundedFace (n := n) prev b).length)

theorem flags₂ (i : V₂) :
    (byInclusion (n := 15) key₁ (face₂ i)).Pairwise (Next (n := 15) key₁) :=
  of_decide_eq_true (ofBlocks (p := fun j : V₂ =>
    decide ((byInclusion (n := 15) key₁ (face₂ j)).Pairwise (Next (n := 15) key₁)))
    (by intro k; fin_cases k <;> decide +kernel) i)

theorem flags₃ (i : V₃) :
    (byInclusion (n := 149) key₂ (face₃ i)).Pairwise (Next (n := 149) key₂) :=
  of_decide_eq_true (ofBlocks (p := fun j : V₃ =>
    decide ((byInclusion (n := 149) key₂ (face₃ j)).Pairwise (Next (n := 149) key₂)))
    (by intro k; fin_cases k <;> decide +kernel) i)

private def lower {n : Nat} (key : Nat → Nat) (t : Nat) : List Nat :=
  (properSubfaces (boundedFace (n := n) key t)).filterMap fun l =>
    (findFace (n := n) key l).map Fin.val

private theorem lower_complete {n : Nat} (key : Nat → Nat)
    (hne : ∀ i : Fin n, unpack (key i) ≠ [])
    (hinv : ∀ i : Fin n, findFace key (unpack (key i)) = some i)
    {s t : Nat} (h : Next (n := n) key s t) : s ∈ lower (n := n) key t := by
  obtain ⟨hs, ht, hst⟩ := h
  have hp : Proper (unpack (key s)) (unpack (key t)) := by
    simpa only [boundedFace, if_pos hs, if_pos ht] using hst
  apply List.mem_filterMap.mpr
  refine ⟨unpack (key s), ?_, ?_⟩
  · simpa only [boundedFace, if_pos ht] using mem_properSubfaces (hne ⟨s, hs⟩) hp
  · rw [hinv ⟨s, hs⟩]
    rfl

private def descending (below : Nat → List Nat) : Nat → Nat → List (List Nat)
  | 0, t => [[t]]
  | fuel + 1, t => [t] :: (below t).flatMap fun s =>
      (descending below fuel s).map (t :: ·)

private theorem pairwise_chain {R : Nat → Nat → Prop} {l : List Nat}
    (h : l.Pairwise R) : l.IsChain R := by
  induction l with
  | nil => exact .nil
  | cons a tail ih =>
    cases tail with
    | nil => exact .singleton a
    | cons b tail =>
      obtain ⟨ha, hb⟩ := List.pairwise_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨ha b List.mem_cons_self, ih hb⟩

private theorem mem_descending {below : Nat → List Nat} {fuel t : Nat} {l : List Nat}
    (hc : (t :: l).IsChain (fun a b => b ∈ below a)) (hlen : l.length ≤ fuel) :
    t :: l ∈ descending below fuel t := by
  induction fuel generalizing t l with
  | zero =>
    cases l with
    | nil => simp [descending]
    | cons a l => simp at hlen
  | succ fuel ih =>
    cases l with
    | nil => simp [descending]
    | cons s l =>
      have hs := (List.isChain_cons_cons.mp hc).1
      have hl := (List.isChain_cons_cons.mp hc).2
      refine List.mem_cons.mpr (.inr (List.mem_flatMap.mpr ⟨s, hs, ?_⟩))
      exact List.mem_map.mpr ⟨s :: l, ih hl (by simpa using hlen), rfl⟩

private def coversFlags {n m : Nat} (prev curr : Nat → Nat) (t : Fin n) : Bool :=
  (descending (lower (n := n) prev) 3 t).all fun l =>
    (findFace (n := m) curr (ascending l.reverse)).isSome

private theorem covers₂ (t : V₁) : coversFlags (m := 149) key₁ key₂ t = true :=
  ofBlocks (p := coversFlags (m := 149) key₁ key₂)
    (by intro k; fin_cases k <;> decide +kernel) t

private theorem covers₃ (t : V₂) : coversFlags (m := 2745) key₂ key₃ t = true :=
  ofBlocks (p := coversFlags (m := 2745) key₂ key₃)
    (by intro k; fin_cases k <;> decide +kernel) t

private theorem exists_flag {n m : Nat} (prev curr : Nat → Nat)
    (hne : ∀ i : Fin n, unpack (prev i) ≠ [])
    (hinv : ∀ i : Fin n, findFace prev (unpack (prev i)) = some i)
    (hcover : ∀ t : Fin n, coversFlags (m := m) prev curr t = true)
    {l : List Nat} (hl : l ≠ []) (hlen : l.length ≤ 4)
    (hbound : ∀ i ∈ l, i < n) (hchain : l.Pairwise (Next (n := n) prev)) :
    ∃ i : Fin m, unpack (curr i) = ascending l := by
  cases hr : l.reverse with
  | nil => exact False.elim (hl (by simpa using congrArg List.reverse hr))
  | cons t tail =>
    have hmem : t ∈ l := by
      apply List.mem_reverse.mp
      rw [hr]
      exact List.mem_cons_self
    have hc : (t :: tail).IsChain (fun a b => b ∈ lower (n := n) prev a) := by
      have hp : l.reverse.Pairwise (fun a b => Next (n := n) prev b a) :=
        List.pairwise_reverse.mpr hchain
      rw [hr] at hp
      exact pairwise_chain (hp.imp (fun h => lower_complete prev hne hinv h))
    have ht : tail.length ≤ 3 := by
      have he := congrArg List.length hr
      simp only [List.length_reverse, List.length_cons] at he
      omega
    have hd := List.all_eq_true.mp (hcover ⟨t, hbound t hmem⟩) _ (mem_descending hc ht)
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (show
      (findFace curr (ascending (t :: tail).reverse) : Option (Fin m)).isSome from hd)
    refine ⟨i, (findFace_sound curr hi).trans (congrArg ascending ?_)⟩
    simpa using (congrArg List.reverse hr).symm

private theorem flag_length {n : Nat} {key : Nat → Nat} {l : List Nat}
    (hs : ∀ i : Fin n, (unpack (key i)).length ≤ 4) (hn : ∀ i : Fin n, unpack (key i) ≠ [])
    (hb : ∀ i ∈ l, i < n) (hc : l.Pairwise (Next (n := n) key)) :
    l.length ≤ 4 := by
  have aux : ∀ (t : List Nat) (lo : Nat),
      lo ≤ 5 → (∀ i ∈ t, i < n ∧ lo ≤ (unpack (key i)).length) →
      t.Pairwise (Next (n := n) key) → t.length + lo ≤ 5 := by
    intro t
    induction t with
    | nil =>
      intro lo h _ _
      simpa using h
    | cons a t ih =>
      intro lo _ hbound hpair
      obtain ⟨ha, hloa⟩ := hbound a List.mem_cons_self
      have hmax : (unpack (key a)).length ≤ 4 := hs ⟨a, ha⟩
      obtain ⟨hedges, htail⟩ := List.pairwise_cons.mp hpair
      have hlast : t.length + ((unpack (key a)).length + 1) ≤ 5 := by
        refine ih _ (by omega) ?_ htail
        intro i hi
        have hbi := (hbound i (List.mem_cons_of_mem _ hi)).1
        have hsub : Proper (unpack (key a)) (unpack (key i)) := by
          simpa only [boundedFace, if_pos ha, if_pos hbi] using (hedges i hi).2.2
        have hle := hsub.1.length_le
        have hne : (unpack (key a)).length ≠ (unpack (key i)).length :=
          fun hEq => hsub.2 (hsub.1.eq_of_length hEq)
        exact ⟨hbi, by omega⟩
      simp only [List.length_cons]
      omega
  have hr := aux l 1 (by decide) (fun i hi => ⟨hb i hi, by
    have hne : unpack (key i) ≠ [] := hn ⟨i, hb i hi⟩
    cases h : unpack (key i) with
    | nil => exact (hne h).elim
    | cons a t => simp⟩) hc
  omega

/-- Every nonempty chain of level-one faces occurs at level two. -/
theorem face₂_complete (l : List Nat) (hl : l ≠ [])
    (hb : ∀ i ∈ l, i < 15) (hc : l.Pairwise (Next (n := 15) key₁)) :
    ∃ i : V₂, face₂ i = ascending l :=
  exists_flag key₁ key₂ (fun i => (shape₁ i).1) find₁ covers₂ hl
    (flag_length (fun i : V₁ => (shape₁ i).2.1) (fun i => (shape₁ i).1) hb hc) hb hc

/-- Every nonempty chain of level-two faces occurs at level three. -/
theorem face₃_complete (l : List Nat) (hl : l ≠ [])
    (hb : ∀ i ∈ l, i < 149) (hc : l.Pairwise (Next (n := 149) key₂)) :
    ∃ i : V₃, face₃ i = ascending l :=
  exists_flag key₂ key₃ (fun i => (shape₂ i).1) find₂ covers₃ hl
    (flag_length (fun i : V₂ => (shape₂ i).2.1) (fun i => (shape₂ i).1) hb hc) hb hc

private theorem has_face₁ : (([0, 1, 2, 3] : List Nat).sublists.filter (· != [])).all
    (fun l => (findFace (n := 15) key₁ l).isSome) = true := by decide +kernel

theorem face₁_complete {l : List Nat} (h : List.Sublist l [0, 1, 2, 3]) (hne : l ≠ []) :
    ∃ i : V₁, face₁ i = l := by
  have hm : l ∈ ([0, 1, 2, 3] : List Nat).sublists.filter (· != []) := by
    simp [List.mem_sublists.mpr h, hne]
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (show
    (findFace (n := 15) key₁ l).isSome from List.all_eq_true.mp has_face₁ _ hm)
  exact ⟨i, findFace_sound key₁ hi⟩

/-- Adjacency is comparability by strict inclusion of depth-three face lists. -/
def graph : SimpleGraph V₃ where
  Adj u v := Proper (face₃ u) (face₃ v) ∨ Proper (face₃ v) (face₃ u)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.2 rfl) (fun h => h.2 rfl)⟩

def low (c : Color) : Nat := if c = 0 then 2 else 0
def high (c : Color) : Nat := low c + 1
def opposite (c : Color) : Color := if c = 0 then 1 else 0

/-- The original carrier obtained by expanding both levels of indices. -/
def carrier (v : V₃) : List Nat :=
  (((face₃ v).flatMap (boundedFace (n := 149) key₂)).flatMap
    (boundedFace (n := 15) key₁)).eraseDups

private def cut₁ (c : Color) (i : Nat) : List Nat :=
  (boundedFace (n := 15) key₁ i).filter fun a => a == low c || a == high c

private def cut₂ (c : Color) (i : Nat) : List (List Nat) :=
  (((boundedFace (n := 149) key₂ i).map (cut₁ c)).filter (· != [])).eraseDups

/-- At depth two a face needs one member meeting the color. At depth three
every member must satisfy that depth-two condition. -/
def InCollar (c : Color) (v : V₃) : Prop :=
  (face₃ v).all (fun i => cut₂ c i != []) = true

instance (c : Color) (v : V₃) : Decidable (InCollar c v) := by
  unfold InCollar
  infer_instance

/-- On the collar, the cut describes the composite retraction as a nested
list of faces. Repeated images under either cut are identified. Singleton
images are independent of the order of the surviving entries. -/
def retract (c : Color) (v : V₃) : List (List (List Nat)) :=
  ((face₃ v).map (cut₂ c)).eraseDups

def IsEndpoint (c : Color) (a : Nat) (v : V₃) : Prop := retract c v = [[[a]]]

instance (c : Color) (a : Nat) (v : V₃) : Decidable (IsEndpoint c a v) := by
  unfold IsEndpoint
  infer_instance

/-- In path coordinates, a retained vertex doubles its coordinate and the
barycenter of an edge has the sum of the two adjacent coordinates. -/
private def subdivisionCoordinate : List Nat → Nat
  | [] => 0
  | a :: tail => tail.foldl min a + tail.foldl max a

def retractionHeight (c : Color) (v : V₃) : Nat :=
  subdivisionCoordinate ((retract c v).map fun levelTwo =>
    subdivisionCoordinate (levelTwo.map fun levelOne =>
      subdivisionCoordinate (levelOne.map (· - low c))))

structure Label where
  color : Color
  height : Option Nat

def label (v : V₃) : Label :=
  let tag := Data.row Data.rows3 v % 64
  if tag < 17 then ⟨0, some tag⟩
  else if tag < 34 then ⟨1, some (tag - 17)⟩
  else ⟨if tag = 34 then 0 else 1, none⟩

def Main (c : Color) (v : V₃) : Prop :=
  (label v).color = c ∧ (label v).height.isSome = true

def Extra (c : Color) (v : V₃) : Prop :=
  (label v).color = c ∧ (label v).height = none

def height (v : V₃) : Nat := (label v).height.getD 0

def VertexRule (v : V₃) : Prop :=
  let c := (label v).color
  match (label v).height with
  | some h => InCollar c v ∧ h ≤ 16 ∧
      (IsEndpoint c (low c) v → h = 0) ∧ (IsEndpoint c (high c) v → h = 16)
  | none => InCollar (opposite c) v ∧
      low (opposite c) ∈ carrier v ∧ high (opposite c) ∈ carrier v

instance (v : V₃) : Decidable (VertexRule v) := by
  unfold VertexRule
  split <;> infer_instance

theorem vertex_rule (v : V₃) : VertexRule v :=
  of_decide_eq_true (ofBlocks (n := 2745) (p := fun j => decide (VertexRule j))
    (by intro k; fin_cases k <;> decide +kernel) v)

def RetractionPosition (c : Color) (v : V₃) : Prop :=
  retractionHeight c v ≤ 8 ∧
    (IsEndpoint c (low c) v ↔ retractionHeight c v = 0) ∧
    (IsEndpoint c (high c) v ↔ retractionHeight c v = 8)

instance (c : Color) (v : V₃) : Decidable (RetractionPosition c v) := by
  unfold RetractionPosition
  infer_instance

instance (c : Color) (v : V₃) : Decidable (Main c v) := by
  unfold Main
  infer_instance

theorem retraction_position {c : Color} {v : V₃} (hv : Main c v) :
    RetractionPosition c v := by
  have h : Main (label v).color v → RetractionPosition (label v).color v :=
    of_decide_eq_true (ofBlocks (n := 2745)
      (p := fun j => decide (Main (label j).color j → RetractionPosition (label j).color j))
      (by intro k; fin_cases k <;> decide +kernel) v)
  rw [hv.1] at h
  exact h hv

def UnitStep (a b : Nat) : Prop := a ≤ b + 1 ∧ b ≤ a + 1

instance (a b : Nat) : Decidable (UnitStep a b) := by
  unfold UnitStep
  infer_instance

private def HeightRule (r s : Nat) : Option Nat → Option Nat → Prop
  | none, none => True
  | some a, some b => UnitStep a b ∧ UnitStep r s
  | _, _ => False

private instance (r s : Nat) (a b : Option Nat) : Decidable (HeightRule r s a b) := by
  cases a <;> cases b <;> unfold HeightRule <;> infer_instance

/-- For an edge of one color, main and extra are incompatible. On a main
edge both height maps are unit-step maps. -/
def EdgeRule (u v : V₃) : Prop :=
  (label u).color = (label v).color →
    HeightRule (retractionHeight (label u).color u) (retractionHeight (label v).color v)
      (label u).height (label v).height

instance (u v : V₃) : Decidable (EdgeRule u v) := by
  unfold EdgeRule
  infer_instance

private def checksEdges (v : V₃) : Bool :=
  (properSubfaces (face₃ v)).all fun l =>
    match findFace key₃ l with
    | none => false
    | some u => decide (EdgeRule u v)

private theorem edgesChecked (v : V₃) : checksEdges v = true :=
  ofBlocks (p := checksEdges) (by intro k; fin_cases k <;> decide +kernel) v

private theorem edge_below {u v : V₃} (h : Proper (face₃ u) (face₃ v)) :
    EdgeRule u v := by
  have hm := mem_properSubfaces (shape₃ u).1 h
  have hc := List.all_eq_true.mp (edgesChecked v) _ hm
  change (match findFace key₃ (face₃ u) with
    | none => false
    | some w => decide (EdgeRule w v)) = true at hc
  rw [find₃ u] at hc
  exact of_decide_eq_true hc

private theorem proper_iff_finset {l r : List Nat}
    (hl : l.Pairwise (· < ·)) (hr : r.Pairwise (· < ·)) :
    Proper l r ↔ l.toFinset ⊂ r.toFinset := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha
      exact List.mem_toFinset.mpr (h.1.subset (List.mem_toFinset.mp ha))
    intro he
    apply h.2
    exact hl.eq_of_mem_iff hr (fun a => by
      rw [← List.mem_toFinset, he, List.mem_toFinset])
  · intro h
    refine ⟨List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup ?_) hl hr, ?_⟩
    · intro a ha
      exact List.mem_toFinset.mp (h.1 (List.mem_toFinset.mpr ha))
    · exact fun he => h.2 (congrArg List.toFinset he)

theorem edge_rule {u v : V₃} (h : graph.Adj u v) : EdgeRule u v := by
  rcases h with h | h
  · exact edge_below h
  · have hh := edge_below h
    unfold EdgeRule at hh ⊢
    intro hcolor
    specialize hh hcolor.symm
    cases hu : (label u).height <;> cases hv : (label v).height <;>
      simpa only [hu, hv, HeightRule, UnitStep, and_comm] using hh

/-- Exact undirected edge count via the proper nonempty subfaces. -/
theorem edge_count : (List.finRange 2745).foldl
    (fun n v => n + (properSubfaces (face₃ v)).length) 0 = 17000 := by decide +kernel

def onMain (c : Color) : Set V₃ := {v | Main c v}

theorem main_conditions {c : Color} {v : V₃} (hv : Main c v) :
    InCollar c v ∧ height v ≤ 16 ∧
    (IsEndpoint c (low c) v → height v = 0) ∧
    (IsEndpoint c (high c) v → height v = 16) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (show (label v).height.isSome from hv.2)
  have rule := vertex_rule v
  unfold VertexRule at rule
  rw [ha, hv.1] at rule
  simpa [height, ha] using rule

theorem pocket_conditions {c : Color} {v : V₃} (hv : Extra c v) :
    InCollar (opposite c) v ∧
      low (opposite c) ∈ carrier v ∧ high (opposite c) ∈ carrier v := by
  have rule := vertex_rule v
  unfold VertexRule at rule
  rw [hv.2, hv.1] at rule
  exact rule

theorem main_interval (c : Color) :
    PathContiguity.IsIntervalMap (graph.induce (onMain c)) 16
      (fun v => height v.val) := by
  have present {v : V₃} (hv : Main c v) : ∃ a, (label v).height = some a :=
    Option.isSome_iff_exists.mp hv.2
  refine ⟨?_, ?_⟩
  · exact fun v => (main_conditions v.property).2.1
  · intro u v e
    obtain ⟨a, ha⟩ := present u.property
    obtain ⟨b, hb⟩ := present v.property
    have hu : Main c u.val := u.property
    have hv : Main c v.val := v.property
    have he := edge_rule (u := u.val) (v := v.val) e (hu.1.trans hv.1.symm)
    rw [ha, hb] at he
    simpa only [height, ha, hb, Option.getD_some, UnitStep] using
      (show UnitStep a b from he.1)

theorem main_extra_separated {c : Color} {u v : V₃} (hu : Main c u) (hv : Extra c v) :
    ¬ graph.Adj u v := by
  intro e
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (show (label u).height.isSome from hu.2)
  have h := edge_rule e (hu.1.trans hv.1.symm)
  simpa [ha, hv.2, HeightRule] using h

def OnBoundary (minority : Color) (v : V₃) : Prop :=
  ¬ (low minority ∈ carrier v ∧ high minority ∈ carrier v)

instance (minority : Color) (v : V₃) : Decidable (OnBoundary minority v) := by
  unfold OnBoundary
  infer_instance

/-- On a face missing one vertex of color c, a main-c label is pinned
to the retained vertex of that color. -/
def ThinFacePin (c : Color) (v : V₃) : Prop :=
  (low c ∈ carrier v ∧ IsEndpoint c (low c) v ∧ height v = 0) ∨
    (high c ∈ carrier v ∧ IsEndpoint c (high c) v ∧ height v = 16)

instance (c : Color) (v : V₃) : Decidable (ThinFacePin c v) := by
  unfold ThinFacePin
  infer_instance

theorem thin_face_pin (c : Color) (v : V₃) (hm : Main c v) (hb : OnBoundary c v) :
    ThinFacePin c v := by
  have h : Main (label v).color v → OnBoundary (label v).color v →
      ThinFacePin (label v).color v :=
    of_decide_eq_true (ofBlocks (n := 2745)
      (p := fun j => decide (Main (label j).color j → OnBoundary (label j).color j →
        ThinFacePin (label j).color j))
      (by intro k; fin_cases k <;> decide +kernel) v)
  rw [hm.1] at h
  exact h hm hb

/-- The two old endpoint fibers within the main part. -/
def endpointFibers (c : Color) : Set (onMain c) :=
  {v | IsEndpoint c (low c) v.val ∨ IsEndpoint c (high c) v.val}

theorem retraction_interval (c : Color) :
    PathContiguity.IsIntervalMap (graph.induce (onMain c)) 8
      (fun v => retractionHeight c v.val) := by
  refine ⟨fun v => (retraction_position v.property).1, ?_⟩
  intro u v e
  have hu : Main c u.val := u.property
  have hv : Main c v.val := v.property
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (show (label u.val).height.isSome from hu.2)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (label v.val).height.isSome from hv.2)
  have h := edge_rule (u := u.val) (v := v.val) e (hu.1.trans hv.1.symm)
  rw [ha, hb, hu.1, hv.1] at h
  exact h.2

/-- Within an ordered chamber, the height map followed by the left-endpoint
selection and the two-cut retraction are relatively contiguous on the
depth-three path. -/
theorem relative_retraction (c : Color) :
    Relation.ReflTransGen
      (PathContiguity.RelativeContiguous (graph.induce (onMain c)) 8
        (endpointFibers c) (fun v => retractionHeight c v.val))
      (fun v => retractionHeight c v.val) (fun v => height v.val / 2) := by
  have hn : PathContiguity.IsIntervalMap (graph.induce (onMain c)) 8
      (fun v => height v.val / 2) := by
    refine ⟨?_, ?_⟩
    · intro v
      have h : height v.val ≤ 16 := (main_interval c).1 v
      change height v.val / 2 ≤ 8
      omega
    · intro u v e
      obtain ⟨h₁, h₂⟩ : UnitStep (height u.val) (height v.val) := (main_interval c).2 e
      change UnitStep (height u.val / 2) (height v.val / 2)
      exact ⟨by omega, by omega⟩
  apply PathContiguity.relative_contiguity _ _ _ (retraction_interval c) hn
  intro v hv
  have hm := main_conditions v.property
  have hp := retraction_position v.property
  change retractionHeight c v.val = height v.val / 2
  rcases hv with h | h
  · rw [hm.2.2.1 h, hp.2.1.mp h]
  · rw [hm.2.2.2 h, hp.2.2.mp h]

#print axioms flags₂
#print axioms flags₃
#print axioms face₁_complete
#print axioms face₂_complete
#print axioms face₃_complete
#print axioms edge_count
#print axioms vertex_rule
#print axioms retraction_position
#print axioms edge_rule
#print axioms thin_face_pin
#print axioms relative_retraction

section LiteralSubdivision

open D5.S3.Topology.BarycentricNeighborhoodIteration (iteratedAmbient)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)

abbrev orderedTetrahedron : PreAbstractSimplicialComplex (Fin 4) := simplex Finset.univ

private def asFinset (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val ∈ l

private theorem mem_asFinset {n : ℕ} {l : List ℕ} {i : Fin n} :
    i ∈ asFinset n l ↔ i.val ∈ l := by
  simp [asFinset]

private theorem asFinset_nonempty {n : ℕ} {l : List ℕ} (hne : l ≠ [])
    (hb : ∀ a ∈ l, a < n) : (asFinset n l).Nonempty := by
  cases l with
  | nil => contradiction
  | cons a t =>
    have ha : a ∈ a :: t := List.mem_cons_self
    exact ⟨⟨a, hb a ha⟩, mem_asFinset.mpr ha⟩

private theorem asFinset_eq_of_perm {n : ℕ} {l r : List ℕ} (h : List.Perm l r) :
    asFinset n l = asFinset n r := by
  ext i
  exact mem_asFinset.trans (h.mem_iff.trans mem_asFinset.symm)

private theorem asFinset_injective_on {n : ℕ} {l r : List ℕ}
    (hl : l.Pairwise (· < ·)) (hr : r.Pairwise (· < ·))
    (hbl : ∀ a ∈ l, a < n) (hbr : ∀ a ∈ r, a < n)
    (he : asFinset n l = asFinset n r) : l = r := by
  apply hl.eq_of_mem_iff hr
  intro a
  constructor
  · intro ha
    let i : Fin n := ⟨a, hbl a ha⟩
    exact mem_asFinset.mp (he ▸ (mem_asFinset.mpr ha : i ∈ asFinset n l))
  · intro ha
    let i : Fin n := ⟨a, hbr a ha⟩
    exact mem_asFinset.mp (he.symm ▸ (mem_asFinset.mpr ha : i ∈ asFinset n r))

private theorem proper_iff_asFinset {n : ℕ} {l r : List ℕ}
    (hl : l.Pairwise (· < ·)) (hr : r.Pairwise (· < ·))
    (hbl : ∀ a ∈ l, a < n) (hbr : ∀ a ∈ r, a < n) :
    Proper l r ↔ asFinset n l ⊂ asFinset n r := by
  rw [proper_iff_finset hl hr, Finset.ssubset_iff_subset_ne, Finset.ssubset_iff_subset_ne]
  have hsub : l.toFinset ⊆ r.toFinset ↔ asFinset n l ⊆ asFinset n r := by
    constructor
    · intro h a ha
      exact mem_asFinset.mpr (List.mem_toFinset.mp (h (List.mem_toFinset.mpr (mem_asFinset.mp ha))))
    · intro h a ha
      have hm := List.mem_toFinset.mp ha
      let i : Fin n := ⟨a, hbl a hm⟩
      exact List.mem_toFinset.mpr (mem_asFinset.mp (h (mem_asFinset.mpr hm : i ∈ asFinset n l)))
  exact and_congr hsub ⟨fun h he => h (by rw [asFinset_injective_on hl hr hbl hbr he]),
    fun h he => h (by ext i; simp only [mem_asFinset, ← List.mem_toFinset, he])⟩

private theorem limit_of_shape {n p : ℕ} {key : Nat → Nat} {i : Fin n}
    (h : RowShape p key i) : ∀ a ∈ unpack (key i), a < p := by
  intro a ha
  simpa using (List.all_eq_true.mp h.2.2.2.1 a ha)

def literalFace₁ (i : V₁) : Face orderedTetrahedron :=
  ⟨asFinset 4 (face₁ i), asFinset_nonempty (shape₁ i).1 (limit_of_shape (shape₁ i)),
    Finset.subset_univ _⟩

private def literalFace₁Embedding : V₁ ↪ Face orderedTetrahedron where
  toFun := literalFace₁
  inj' := by
    intro i j he
    have hr : face₁ i = face₁ j := asFinset_injective_on
      (shape₁ i).2.2.1 (shape₁ j).2.2.1 (limit_of_shape (shape₁ i)) (limit_of_shape (shape₁ j))
      (congrArg Subtype.val he)
    exact Option.some.inj ((find₁ i).symm.trans (hr ▸ find₁ j))

private theorem literalFace₁_lt (i j : V₁) :
    literalFace₁ i < literalFace₁ j ↔ Proper (face₁ i) (face₁ j) :=
  (proper_iff_asFinset (shape₁ i).2.2.1 (shape₁ j).2.2.1
    (limit_of_shape (shape₁ i)) (limit_of_shape (shape₁ j))).symm

private theorem literalFace₁_surjective : Function.Surjective literalFace₁ := by
  intro s
  let indexSet := s.val.map Fin.valEmbedding
  let l := indexSet.sort (· ≤ ·)
  have hs : l.toFinset = indexSet := Finset.sort_toFinset _ _
  have hne : l ≠ [] := by
    intro h
    have hn : indexSet.Nonempty := Finset.map_nonempty.mpr
      ((orderedTetrahedron.isRelLowerSet_faces s.property).1)
    have hz : indexSet = ∅ := by simpa only [h, List.toFinset_nil] using hs.symm
    simp [hz] at hn
  have hl : l.Sublist [0, 1, 2, 3] := by
    have hp : l.Pairwise (· < ·) := (Finset.sortedLT_sort indexSet).pairwise
    refine List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hp.nodup ?_) hp (by decide)
    intro a ha
    have hm := List.mem_toFinset.mpr ha
    rw [hs, Finset.mem_map] at hm
    obtain ⟨x, _, rfl⟩ := hm
    have hx := x.isLt
    change x.val ∈ [0, 1, 2, 3]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨i, hi⟩ := face₁_complete hl hne
  refine ⟨i, Subtype.ext ?_⟩
  ext a
  change a ∈ asFinset 4 (face₁ i) ↔ a ∈ s.val
  rw [hi, mem_asFinset, ← List.mem_toFinset, hs, Finset.mem_map]
  exact ⟨fun ⟨b, hb, he⟩ => (Fin.ext he : b = a) ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

private theorem chain_of_row {X : Type} {n : ℕ} {K : PreAbstractSimplicialComplex X}
    (e : Fin n ↪ Face K) (key : Nat → Nat) {l : List Nat}
    (hrel : ∀ (i j : Fin n), Next (n := n) key i.val j.val → e i < e j)
    (hchain : (byInclusion (n := n) key l).Pairwise (Next (n := n) key)) :
    IsChain (· < ·) ((asFinset n l).map e : Set (Face K)) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
  have hperm : List.Perm (byInclusion (n := n) key l) l := List.perm_insertionSort _ _
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hperm.mem_iff.mpr (mem_asFinset.mp ha))
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (hperm.mem_iff.mpr (mem_asFinset.mp hb))
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inl (hrel a b (by simpa only [hi, hj] using hchain.rel_get_of_lt hij))
  · exact (hxy (congrArg e (Fin.ext (hi.symm.trans (hij ▸ hj))))).elim
  · exact Or.inr (hrel b a (by simpa only [hi, hj] using hchain.rel_get_of_lt hij))

def literalFace₂ (i : V₂) : Face (iteratedAmbient orderedTetrahedron 1).2 := by
  refine ⟨(asFinset 15 (face₂ i)).map literalFace₁Embedding, ?_⟩
  refine ⟨Finset.map_nonempty.mpr (asFinset_nonempty (shape₂ i).1 (limit_of_shape (shape₂ i))),
    chain_of_row literalFace₁Embedding key₁ ?_ (flags₂ i), fun a _ => a.property⟩
  intro a b h
  exact (literalFace₁_lt a b).2 (by simpa only [face₁, boundedFace, ite_eq_left a.isLt, ite_eq_left b.isLt] using h.2.2)

private def literalFace₂Embedding : V₂ ↪ Face (iteratedAmbient orderedTetrahedron 1).2 where
  toFun := literalFace₂
  inj' := by
    intro i j he
    have hfin : asFinset 15 (face₂ i) = asFinset 15 (face₂ j) :=
      Finset.map_injective literalFace₁Embedding (congrArg Subtype.val he)
    have hr : face₂ i = face₂ j := asFinset_injective_on
      (shape₂ i).2.2.1 (shape₂ j).2.2.1 (limit_of_shape (shape₂ i)) (limit_of_shape (shape₂ j)) hfin
    exact Option.some.inj ((find₂ i).symm.trans (hr ▸ find₂ j))

private theorem literalFace₂_lt (i j : V₂) :
    literalFace₂ i < literalFace₂ j ↔ Proper (face₂ i) (face₂ j) := by
  change (asFinset 15 (face₂ i)).map literalFace₁Embedding ⊂
    (asFinset 15 (face₂ j)).map literalFace₁Embedding ↔ _
  rw [Finset.map_ssubset_map]
  exact (proper_iff_asFinset (shape₂ i).2.2.1 (shape₂ j).2.2.1
    (limit_of_shape (shape₂ i)) (limit_of_shape (shape₂ j))).symm

/-- The table index is a vertex of the literal third ordinary subdivision. -/
def literalFace₃ (i : V₃) : Face (iteratedAmbient orderedTetrahedron 2).2 := by
  refine ⟨(asFinset 149 (face₃ i)).map literalFace₂Embedding, ?_⟩
  refine ⟨Finset.map_nonempty.mpr (asFinset_nonempty (shape₃ i).1 (limit_of_shape (shape₃ i))),
    chain_of_row literalFace₂Embedding key₂ ?_ (flags₃ i), fun a _ => a.property⟩
  intro a b h
  exact (literalFace₂_lt a b).2 (by simpa only [face₂, boundedFace, ite_eq_left a.isLt, ite_eq_left b.isLt] using h.2.2)

theorem literalFace₃_lt (i j : V₃) :
    literalFace₃ i < literalFace₃ j ↔ Proper (face₃ i) (face₃ j) := by
  change (asFinset 149 (face₃ i)).map literalFace₂Embedding ⊂
    (asFinset 149 (face₃ j)).map literalFace₂Embedding ↔ _
  rw [Finset.map_ssubset_map]
  exact (proper_iff_asFinset (shape₃ i).2.2.1 (shape₃ j).2.2.1
    (limit_of_shape (shape₃ i)) (limit_of_shape (shape₃ j))).symm

/-- The adjacency checked by the table is ordinary subdivision adjacency. -/
theorem literalFace₃_adj (i j : V₃) :
    graph.Adj i j ↔ (subdivisionGraph (iteratedAmbient orderedTetrahedron 2).2).Adj
      (literalFace₃ i) (literalFace₃ j) := by
  exact or_congr (literalFace₃_lt i j).symm (literalFace₃_lt j i).symm

private theorem literal_rows_cover {X : Type} {K : PreAbstractSimplicialComplex X}
    {n m : ℕ} (e : Fin n ↪ Face K) (surj : Function.Surjective e)
    (key : Nat → Nat) (row : Fin m → List Nat)
    (hrel : ∀ (i j : Fin n), e i < e j → Next (n := n) key i.val j.val)
    (hcomplete : ∀ l : List Nat, l ≠ [] → (∀ i ∈ l, i < n) →
      l.Pairwise (Next (n := n) key) → ∃ i : Fin m, row i = ascending l)
    (s : Face (BarycentricBaseRigidity.sd K)) :
    ∃ i : Fin m, (asFinset n (row i)).map e = s.val := by
  classical
  let u := s.val.preimage e e.injective.injOn
  have hu : u.map e = s.val := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp hi
    · intro hx
      obtain ⟨i, rfl⟩ := surj x
      exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr hx, rfl⟩
  let rank (i : Fin n) := (e i).val.card
  let order (a b : Fin n) := rank a ≤ rank b
  letI : Std.Total order := ⟨fun a b => le_total (rank a) (rank b)⟩
  letI : IsTrans (Fin n) order := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  let sorted := u.toList.insertionSort order
  let l := sorted.map Fin.val
  have hperm : List.Perm sorted u.toList := List.perm_insertionSort _ _
  have hsorted : sorted.Pairwise order := List.pairwise_insertionSort _ _
  have hnodup : sorted.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList u)
  have hlist : asFinset n l = u := by
    ext i
    rw [mem_asFinset, List.mem_map]
    constructor
    · rintro ⟨j, hj, he⟩
      have hij : j = i := Fin.ext he
      simpa [hij] using hperm.mem_iff.mp hj
    · intro hi
      exact ⟨i, hperm.mem_iff.mpr (Finset.mem_toList.mpr hi), rfl⟩
  have hne : l ≠ [] := by
    intro he
    have hn : (u.map e).Nonempty := hu.symm ▸ s.property.1
    have hz : u = ∅ := by simpa [he, asFinset] using hlist.symm
    simp [hz] at hn
  have hb : ∀ i ∈ l, i < n := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact j.isLt
  have hnext : l.Pairwise (Next (n := n) key) := by
    apply List.pairwise_map.mpr
    apply (List.pairwise_iff_get).2
    intro a b hab
    let x := sorted.get a
    let y := sorted.get b
    have hxy : x ≠ y := hnodup.rel_get_of_lt hab
    have hx : e x ∈ s.val := by
      rw [← hu]
      exact Finset.mem_map.mpr ⟨x, Finset.mem_toList.mp
        (hperm.mem_iff.mp (List.get_mem _ _)), rfl⟩
    have hy : e y ∈ s.val := by
      rw [← hu]
      exact Finset.mem_map.mpr ⟨y, Finset.mem_toList.mp
        (hperm.mem_iff.mp (List.get_mem _ _)), rfl⟩
    have hle : rank x ≤ rank y := hsorted.rel_get_of_lt hab
    rcases s.property.2.1 hx hy (fun h => hxy (e.injective h)) with h | h
    · exact hrel x y h
    · exact ((not_lt_of_ge hle) (Finset.card_lt_card h)).elim
  obtain ⟨i, hi⟩ := hcomplete l hne hb hnext
  refine ⟨i, ?_⟩
  have hsort : List.Perm (ascending l) l := List.perm_insertionSort _ _
  rw [hi, asFinset_eq_of_perm hsort, hlist, hu]

private theorem literalFace₂_surjective : Function.Surjective literalFace₂ := by
  intro s
  obtain ⟨i, hi⟩ := literal_rows_cover literalFace₁Embedding literalFace₁_surjective key₁ face₂
    (fun a b h => ⟨a.isLt, b.isLt,
      by simpa only [face₁, boundedFace, ite_eq_left a.isLt, ite_eq_left b.isLt] using (literalFace₁_lt a b).1 h⟩)
    face₂_complete s
  exact ⟨i, Subtype.ext hi⟩

theorem literalFace₃_bijective : Function.Bijective literalFace₃ := by
  constructor
  · intro i j hij
    have he : asFinset 149 (face₃ i) = asFinset 149 (face₃ j) :=
      Finset.map_injective literalFace₂Embedding (congrArg Subtype.val hij)
    apply face₃_injective
    exact asFinset_injective_on (shape₃ i).2.2.1 (shape₃ j).2.2.1
      (limit_of_shape (shape₃ i)) (limit_of_shape (shape₃ j)) he
  · intro s
    obtain ⟨i, hi⟩ := literal_rows_cover literalFace₂Embedding literalFace₂_surjective key₂ face₃
      (fun a b h => ⟨a.isLt, b.isLt,
        by simpa only [face₂, boundedFace, ite_eq_left a.isLt, ite_eq_left b.isLt] using (literalFace₂_lt a b).1 h⟩)
      face₃_complete s
    exact ⟨i, Subtype.ext hi⟩

private theorem support_three {X : Type} {A : PreAbstractSimplicialComplex X}
    (s : Face (iteratedAmbient A 2).2) (a : X) :
    a ∈ GraphSubdivisionIntervals.originalSupport A 3 {s} ↔
      ∃ y ∈ s.val, ∃ x ∈ y.val, a ∈ x.val := by
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq (Face A) := Classical.decEq (Face A)
  letI : DecidableEq (Face (iteratedAmbient A 1).2) :=
    Classical.decEq (Face (iteratedAmbient A 1).2)
  let first (y : Face (iteratedAmbient A 1).2) : Finset (Face A) := y.val
  let second (x : Face A) : Finset X := x.val
  let start (x : Face (iteratedAmbient A 2).2) : Finset (Face (iteratedAmbient A 1).2) := x.val
  have h : a ∈ (s.val.biUnion first).biUnion second ↔
      ∃ y ∈ s.val, ∃ x ∈ first y, a ∈ second x := by
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, ha⟩
      obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp hx
      exact ⟨y, hy, x, hx, ha⟩
    · rintro ⟨y, hy, x, hx, ha⟩
      exact ⟨x, Finset.mem_biUnion.mpr ⟨y, hy, hx⟩, ha⟩
  change a ∈ (({s} : Finset _).biUnion start |>.biUnion first |>.biUnion second) ↔ _
  rw [Finset.singleton_biUnion]
  exact h

/-- The table's old carrier agrees with the support of the corresponding
vertex in the ordinary third subdivision. -/
theorem literalFace₃_carrier (i : V₃) (a : Fin 4) :
    a ∈ GraphSubdivisionIntervals.originalSupport orderedTetrahedron 3 {literalFace₃ i} ↔
      a.val ∈ carrier i := by
  classical
  have support : a ∈ GraphSubdivisionIntervals.originalSupport orderedTetrahedron 3 {literalFace₃ i} ↔
      ∃ j : V₂, j.val ∈ face₃ i ∧ ∃ k : V₁, k.val ∈ face₂ j ∧ a.val ∈ face₁ k := by
    rw [support_three]
    constructor
    · rintro ⟨y, hy, x, hxy, ha⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (show y ∈ (asFinset 149 (face₃ i)).map
        literalFace₂Embedding from hy)
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp (show x ∈ (asFinset 15 (face₂ j)).map
        literalFace₁Embedding from hxy)
      exact ⟨j, mem_asFinset.mp hj, k, mem_asFinset.mp hk, mem_asFinset.mp ha⟩
    · rintro ⟨j, hj, k, hk, ha⟩
      exact ⟨literalFace₂ j, Finset.mem_map.mpr ⟨j, mem_asFinset.mpr hj, rfl⟩,
        literalFace₁ k, Finset.mem_map.mpr ⟨k, mem_asFinset.mpr hk, rfl⟩, mem_asFinset.mpr ha⟩
  rw [support]
  change _ ↔ a.val ∈ (((face₃ i).flatMap (boundedFace (n := 149) key₂)).flatMap
    (boundedFace (n := 15) key₁)).eraseDups
  simp only [List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, k, hk, ha⟩
    exact ⟨k.val, ⟨j.val, hj, by simpa only [boundedFace, ite_eq_left j.isLt, face₂] using hk⟩,
      by simpa only [boundedFace, ite_eq_left k.isLt, face₁] using ha⟩
  · rintro ⟨k, ⟨j, hj, hk⟩, ha⟩
    have h₁ := limit_of_shape (shape₃ i) j hj
    let jt : V₂ := ⟨j, h₁⟩
    have h₂ : k ∈ face₂ jt := by
      simpa only [boundedFace, ite_eq_left h₁, face₂, jt] using hk
    have h₃ : k < 15 := limit_of_shape (shape₂ jt) k h₂
    let kt : V₁ := ⟨k, h₃⟩
    exact ⟨jt, hj, kt, h₂, by simpa only [boundedFace, ite_eq_left h₃, face₁, kt] using ha⟩

end LiteralSubdivision

end TetrahedronCollar16
