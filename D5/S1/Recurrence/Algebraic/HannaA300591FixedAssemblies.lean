/- GID: D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Signed ordered assemblies factor over fixed vertices and obey block-removal recursion. -/

import Mathlib.Data.Fintype.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Exact splitting of invariant ordered assemblies with ambient markers. -/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies

noncomputable section

/-- An ordered block, its color, and its two ambient markers. -/
abbrev Block (V C : Type) := {l : List V // l.Nodup} × C × V × V

/-- The vertices of a decorated block, in their specified order. -/
def vertices {V C : Type} (b : Block V C) : List V := b.1.val

/-- The color is transported unchanged by vertex relabeling. -/
def color {V C : Type} (b : Block V C) : C := b.2.1

/-- The first ambient marker, with repetition of the second marker allowed. -/
def leftMarker {V C : Type} (b : Block V C) : V := b.2.2.1

/-- The second ambient marker. -/
def rightMarker {V C : Type} (b : Block V C) : V := b.2.2.2

/-- Relabel vertices and both ambient markers, preserving the block order and color. -/
def relabel {V C : Type} (g : Equiv.Perm V) (b : Block V C) : Block V C :=
  ⟨⟨b.1.val.map g, b.1.property.map g.injective⟩,
    color b, g (leftMarker b), g (rightMarker b)⟩

/-- Nonempty disjoint ordered blocks cover exactly S; both markers lie in T.
The color admissibility predicate may depend on the block's size. -/
structure AssemblyLaw {V C : Type} (allowed : ℕ → C → Prop)
    (S T : Finset V) (E : Finset (Block V C)) : Prop where
  nonempty : ∀ b ∈ E, vertices b ≠ []
  support : ∀ b ∈ E, ∀ x ∈ vertices b, x ∈ S
  admissible : ∀ b ∈ E, allowed (vertices b).length (color b)
  left_mem : ∀ b ∈ E, leftMarker b ∈ T
  right_mem : ∀ b ∈ E, rightMarker b ∈ T
  cover : ∀ x ∈ S, ∃ b ∈ E, x ∈ vertices b
  separate : ∀ b ∈ E, ∀ c ∈ E, ∀ x,
    x ∈ vertices b → x ∈ vertices c → b = c

/-- Assemblies retain their ambient marker domain independently of vertex support. -/
abbrev Assembly {V C : Type} (allowed : ℕ → C → Prop) (S T : Finset V) :=
  {E : Finset (Block V C) // AssemblyLaw allowed S T E}

/-- Stability under the actual simultaneous relabeling of vertices and markers. -/
def Stable {V C : Type} (g : Equiv.Perm V) (E : Finset (Block V C)) : Prop :=
  ∀ b ∈ E, relabel g b ∈ E

/-- The invariant assemblies for one permutation. -/
abbrev FixedAssembly {V C : Type} (allowed : ℕ → C → Prop)
    (S T : Finset V) (g : Equiv.Perm V) :=
  {E : Finset (Block V C) // AssemblyLaw allowed S T E ∧ Stable g E}

instance {V C : Type} [Fintype V] [Fintype C]
    (allowed : ℕ → C → Prop) (S T : Finset V) : Fintype (Assembly allowed S T) :=
  Fintype.ofFinite _

instance {V C : Type} [Fintype V] [Fintype C]
    (allowed : ℕ → C → Prop) (S T : Finset V) (g : Equiv.Perm V) :
    Fintype (FixedAssembly allowed S T g) := Fintype.ofFinite _

/-- The actual fixed vertices of g. -/
def fixedVertices {V : Type} [Fintype V] [DecidableEq V] (g : Equiv.Perm V) (S : Finset V) : Finset V :=
  S.filter fun x => g x = x

/-- The actual moved vertices of g. -/
def movedVertices {V : Type} [Fintype V] [DecidableEq V] (g : Equiv.Perm V) (S : Finset V) : Finset V :=
  S.filter fun x => g x ≠ x

/-- Multiplicative block weights include arbitrary signed colors. -/
def weight {V C : Type} (sign : C → ℤ) (E : Finset (Block V C)) : ℤ :=
  ∏ b ∈ E, sign (color b)

variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
variable {allowed : ℕ → C → Prop} {g : Equiv.Perm V} {S T : Finset V}

theorem fixed_of_map_eq (l : List V) (h : l.map g = l) :
    ∀ x ∈ l, g x = x := by
  have he : l.map g = l.map id := by simpa using h
  exact List.map_inj_left.mp he

private theorem relabel_eq_of_fixed (b : Block V C)
    (hb : ∀ x ∈ vertices b, g x = x)
    (hl : g (leftMarker b) = leftMarker b)
    (hr : g (rightMarker b) = rightMarker b) : relabel g b = b := by
  have he : (vertices b).map g = vertices b := by
    simpa using (List.map_inj_left.mpr hb : (vertices b).map g = (vertices b).map id)
  apply Prod.ext
  · exact Subtype.ext he
  · exact Prod.ext rfl (Prod.ext hl hr)

private theorem fixed_block (E : Finset (Block V C))
    (hE : AssemblyLaw allowed S T E) (hg : Stable g E)
    (b : Block V C) (hb : b ∈ E) (x : V) (hx : x ∈ vertices b) (hfix : g x = x) :
    (∀ y ∈ vertices b, g y = y) ∧
      g (leftMarker b) = leftMarker b ∧ g (rightMarker b) = rightMarker b := by
  have hmem : x ∈ vertices (relabel g b) := by
    change x ∈ (vertices b).map g
    exact hfix ▸ List.mem_map_of_mem hx
  have he : relabel g b = b := hE.separate _ (hg b hb) _ hb x hmem hx
  refine ⟨fixed_of_map_eq _ (congrArg vertices he), ?_, ?_⟩
  · exact congrArg leftMarker he
  · exact congrArg rightMarker he

private def fixedPart (g : Equiv.Perm V) (E : Finset (Block V C)) : Finset (Block V C) :=
  E.filter fun b => ∀ x ∈ vertices b, g x = x

private def movedPart (g : Equiv.Perm V) (E : Finset (Block V C)) : Finset (Block V C) :=
  E.filter fun b => ¬ ∀ x ∈ vertices b, g x = x

private theorem fixedPart_law (E : Finset (Block V C))
    (hE : AssemblyLaw allowed S T E) (hg : Stable g E) :
    AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) (fixedPart g E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; exact hE.nonempty b (mem_filter.mp hb).1
  · intro b hb x hx
    exact mem_filter.mpr ⟨hE.support b (mem_filter.mp hb).1 x hx, (mem_filter.mp hb).2 x hx⟩
  · intro b hb; exact hE.admissible b (mem_filter.mp hb).1
  · intro b hb
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hE.nonempty b (mem_filter.mp hb).1)
    exact mem_filter.mpr ⟨hE.left_mem b (mem_filter.mp hb).1,
      (fixed_block E hE hg b (mem_filter.mp hb).1 x hx ((mem_filter.mp hb).2 x hx)).2.1⟩
  · intro b hb
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hE.nonempty b (mem_filter.mp hb).1)
    exact mem_filter.mpr ⟨hE.right_mem b (mem_filter.mp hb).1,
      (fixed_block E hE hg b (mem_filter.mp hb).1 x hx ((mem_filter.mp hb).2 x hx)).2.2⟩
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := hE.cover x (mem_filter.mp hx).1
    exact ⟨b, mem_filter.mpr ⟨hb,
      (fixed_block E hE hg b hb x hxb (mem_filter.mp hx).2).1⟩, hxb⟩
  · intro b hb c hc x hxb hxc
    exact hE.separate b (mem_filter.mp hb).1 c (mem_filter.mp hc).1 x hxb hxc

private theorem movedPart_law (E : Finset (Block V C))
    (hE : AssemblyLaw allowed S T E) (hg : Stable g E) :
    AssemblyLaw allowed (movedVertices g S) T (movedPart g E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; exact hE.nonempty b (mem_filter.mp hb).1
  · intro b hb x hx
    refine mem_filter.mpr ⟨hE.support b (mem_filter.mp hb).1 x hx, ?_⟩
    intro hfix
    exact (mem_filter.mp hb).2 (fixed_block E hE hg b (mem_filter.mp hb).1 x hx hfix).1
  · intro b hb; exact hE.admissible b (mem_filter.mp hb).1
  · intro b hb; exact hE.left_mem b (mem_filter.mp hb).1
  · intro b hb; exact hE.right_mem b (mem_filter.mp hb).1
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := hE.cover x (mem_filter.mp hx).1
    exact ⟨b, mem_filter.mpr ⟨hb, fun hh => (mem_filter.mp hx).2 (hh x hxb)⟩, hxb⟩
  · intro b hb c hc x hxb hxc
    exact hE.separate b (mem_filter.mp hb).1 c (mem_filter.mp hc).1 x hxb hxc

private theorem movedPart_stable (E : Finset (Block V C)) (hg : Stable g E) :
    Stable g (movedPart g E) := by
  intro b hb
  refine mem_filter.mpr ⟨hg b (mem_filter.mp hb).1, ?_⟩
  intro hh
  apply (mem_filter.mp hb).2
  intro x hx
  have he := hh (g x) (List.mem_map_of_mem hx)
  exact g.injective he

private theorem assembly_disjoint
    (A B : Finset (Block V C))
    (hA : AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) A)
    (hB : AssemblyLaw allowed (movedVertices g S) T B) : Disjoint A B := by
  apply disjoint_left.mpr
  intro b hbA hbB
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hA.nonempty b hbA)
  exact (mem_filter.mp (hB.support b hbB x hx)).2
    (mem_filter.mp (hA.support b hbA x hx)).2

private theorem union_law
    (A B : Finset (Block V C))
    (hA : AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) A)
    (hB : AssemblyLaw allowed (movedVertices g S) T B) :
    AssemblyLaw allowed S T (A ∪ B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact (mem_union.mp hb).elim (hA.nonempty b) (hB.nonempty b)
  · intro b hb x hx
    rcases mem_union.mp hb with hb | hb
    · exact (mem_filter.mp (hA.support b hb x hx)).1
    · exact (mem_filter.mp (hB.support b hb x hx)).1
  · intro b hb
    exact (mem_union.mp hb).elim (hA.admissible b) (hB.admissible b)
  · intro b hb
    exact (mem_union.mp hb).elim (fun hb => (mem_filter.mp (hA.left_mem b hb)).1)
      (hB.left_mem b)
  · intro b hb
    exact (mem_union.mp hb).elim (fun hb => (mem_filter.mp (hA.right_mem b hb)).1)
      (hB.right_mem b)
  · intro x hxS
    by_cases hx : g x = x
    · obtain ⟨b, hb, hxb⟩ := hA.cover x (mem_filter.mpr ⟨hxS, hx⟩)
      exact ⟨b, mem_union_left B hb, hxb⟩
    · obtain ⟨b, hb, hxb⟩ := hB.cover x (mem_filter.mpr ⟨hxS, hx⟩)
      exact ⟨b, mem_union_right A hb, hxb⟩
  · intro b hb c hc x hxb hxc
    rcases mem_union.mp hb with hb | hb <;> rcases mem_union.mp hc with hc | hc
    · exact hA.separate b hb c hc x hxb hxc
    · exact False.elim ((mem_filter.mp (hB.support c hc x hxc)).2
        (mem_filter.mp (hA.support b hb x hxb)).2)
    · exact False.elim ((mem_filter.mp (hB.support b hb x hxb)).2
        (mem_filter.mp (hA.support c hc x hxc)).2)
    · exact hB.separate b hb c hc x hxb hxc

private theorem union_stable
    (A B : Finset (Block V C))
    (hA : AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) A)
    (hgB : Stable g B) : Stable g (A ∪ B) := by
  intro b hb
  rcases mem_union.mp hb with hb | hb
  · have he : relabel g b = b := relabel_eq_of_fixed b
      (fun x hx => (mem_filter.mp (hA.support b hb x hx)).2)
      (mem_filter.mp (hA.left_mem b hb)).2
      (mem_filter.mp (hA.right_mem b hb)).2
    rw [he]
    exact mem_union_left B hb
  · exact mem_union_right A (hgB b hb)

private theorem fixedPart_union
    (A B : Finset (Block V C))
    (hA : AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) A)
    (hB : AssemblyLaw allowed (movedVertices g S) T B) : fixedPart g (A ∪ B) = A := by
  ext b
  constructor
  · intro hb
    obtain ⟨hab, hfix⟩ := mem_filter.mp hb
    rcases mem_union.mp hab with ha | hb
    · exact ha
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hB.nonempty b hb)
      exact False.elim ((mem_filter.mp (hB.support b hb x hx)).2 (hfix x hx))
  · intro hb
    exact mem_filter.mpr ⟨mem_union_left B hb,
      fun x hx => (mem_filter.mp (hA.support b hb x hx)).2⟩

private theorem movedPart_union
    (A B : Finset (Block V C))
    (hA : AssemblyLaw allowed (fixedVertices g S) (fixedVertices g T) A)
    (hB : AssemblyLaw allowed (movedVertices g S) T B) : movedPart g (A ∪ B) = B := by
  ext b
  constructor
  · intro hb
    obtain ⟨hab, hnot⟩ := mem_filter.mp hb
    rcases mem_union.mp hab with ha | hb
    · exact False.elim (hnot (fun x hx => (mem_filter.mp (hA.support b ha x hx)).2))
    · exact hb
  · intro hb
    refine mem_filter.mpr ⟨mem_union_right A hb, ?_⟩
    intro hh
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hB.nonempty b hb)
    exact (mem_filter.mp (hB.support b hb x hx)).2 (hh x hx)

private def splitEquiv (allowed : ℕ → C → Prop) (S T : Finset V) (g : Equiv.Perm V) :
    FixedAssembly allowed S T g ≃
      Assembly allowed (fixedVertices g S) (fixedVertices g T) ×
        FixedAssembly allowed (movedVertices g S) T g where
  toFun E :=
    (⟨fixedPart g E.val, fixedPart_law E.val E.property.1 E.property.2⟩,
     ⟨movedPart g E.val, movedPart_law E.val E.property.1 E.property.2,
       movedPart_stable E.val E.property.2⟩)
  invFun AB := ⟨AB.1.val ∪ AB.2.val,
    union_law _ _ AB.1.property AB.2.property.1,
    union_stable _ _ AB.1.property AB.2.property.2⟩
  left_inv E := by
    apply Subtype.ext
    exact filter_union_filter_not_eq _ _
  right_inv AB := by
    apply Prod.ext
    · exact Subtype.ext (fixedPart_union _ _ AB.1.property AB.2.property.1)
    · exact Subtype.ext (movedPart_union _ _ AB.1.property AB.2.property.1)

omit [DecidableEq C] in
/-- For every permutation and arbitrary signed block weights, the exact fixed-assembly
sum factors into the assembly sum on fixed vertices with fixed markers and the invariant
moved-vertex assembly sum with its original full ambient marker domain. -/
theorem fixed_assembly_weight_factorization (allowed : ℕ → C → Prop)
    (S T : Finset V) (g : Equiv.Perm V) (sign : C → ℤ) :
    (∑ E : FixedAssembly allowed S T g, weight sign E.val) =
      (∑ A : Assembly allowed (fixedVertices g S) (fixedVertices g T), weight sign A.val) *
      (∑ B : FixedAssembly allowed (movedVertices g S) T g, weight sign B.val) := by
  classical
  calc
    _ = ∑ AB : Assembly allowed (fixedVertices g S) (fixedVertices g T) ×
        FixedAssembly allowed (movedVertices g S) T g,
        weight sign (AB.1.val ∪ AB.2.val) := by
      apply Fintype.sum_equiv (splitEquiv allowed S T g)
      intro E
      change weight sign E.val = weight sign (fixedPart g E.val ∪ movedPart g E.val)
      rw [show fixedPart g E.val ∪ movedPart g E.val = E.val from
        filter_union_filter_not_eq _ _]
    _ = ∑ AB : Assembly allowed (fixedVertices g S) (fixedVertices g T) ×
        FixedAssembly allowed (movedVertices g S) T g,
        weight sign AB.1.val * weight sign AB.2.val := by
      apply sum_congr rfl
      intro AB _
      exact prod_union (assembly_disjoint _ _ AB.1.property AB.2.property.1)
    _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- The allowed block containing a specified vertex, with the original ambient markers. -/
def RootBlockLaw (allowed : ℕ → C → Prop) (S T : Finset V) (x : V)
    (b : Block V C) : Prop :=
  x ∈ vertices b ∧ (∀ y ∈ vertices b, y ∈ S) ∧
    allowed (vertices b).length (color b) ∧ leftMarker b ∈ T ∧ rightMarker b ∈ T

/-- All choices for the block at the specified vertex. -/
abbrev RootBlock (allowed : ℕ → C → Prop) (S T : Finset V) (x : V) :=
  {b : Block V C // RootBlockLaw allowed S T x b}

instance (allowed : ℕ → C → Prop) (S T : Finset V) (x : V) :
    Fintype (RootBlock allowed S T x) := Fintype.ofFinite _

variable {x : V}

private theorem erase_block_law (E : Finset (Block V C))
    (hE : AssemblyLaw allowed S T E) (b : Block V C) (hb : b ∈ E) :
    AssemblyLaw allowed (S \ (vertices b).toFinset) T (E.erase b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; exact hE.nonempty c (mem_erase.mp hc).2
  · intro c hc y hy
    refine mem_sdiff.mpr ⟨hE.support c (mem_erase.mp hc).2 y hy, ?_⟩
    intro hyb
    exact (mem_erase.mp hc).1 (hE.separate c (mem_erase.mp hc).2 b hb y hy
      (List.mem_toFinset.mp hyb))
  · intro c hc; exact hE.admissible c (mem_erase.mp hc).2
  · intro c hc; exact hE.left_mem c (mem_erase.mp hc).2
  · intro c hc; exact hE.right_mem c (mem_erase.mp hc).2
  · intro y hy
    obtain ⟨c, hc, hyc⟩ := hE.cover y (mem_sdiff.mp hy).1
    refine ⟨c, mem_erase.mpr ⟨?_, hc⟩, hyc⟩
    intro he
    subst c
    exact (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr hyc)
  · intro c hc d hd y hyc hyd
    exact hE.separate c (mem_erase.mp hc).2 d (mem_erase.mp hd).2 y hyc hyd

private theorem root_not_mem (b : RootBlock allowed S T x)
    (E : Assembly allowed (S \ (vertices b.val).toFinset) T) : b.val ∉ E.val := by
  intro hb
  exact (mem_sdiff.mp (E.property.support b.val hb x b.property.1)).2
    (List.mem_toFinset.mpr b.property.1)

private theorem insert_root_law (b : RootBlock allowed S T x)
    (E : Assembly allowed (S \ (vertices b.val).toFinset) T) :
    AssemblyLaw allowed S T (insert b.val E.val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mem_insert.mp hc with rfl | hc
    · intro hz
      simpa [hz] using b.property.1
    · exact E.property.nonempty c hc
  · intro c hc y hy
    rcases mem_insert.mp hc with rfl | hc
    · exact b.property.2.1 y hy
    · exact (mem_sdiff.mp (E.property.support c hc y hy)).1
  · intro c hc
    exact (mem_insert.mp hc).elim (fun h => h ▸ b.property.2.2.1)
      (E.property.admissible c)
  · intro c hc
    exact (mem_insert.mp hc).elim (fun h => h ▸ b.property.2.2.2.1)
      (E.property.left_mem c)
  · intro c hc
    exact (mem_insert.mp hc).elim (fun h => h ▸ b.property.2.2.2.2)
      (E.property.right_mem c)
  · intro y hy
    by_cases hyb : y ∈ vertices b.val
    · exact ⟨b.val, mem_insert_self _ _, hyb⟩
    · obtain ⟨c, hc, hyc⟩ := E.property.cover y
        (mem_sdiff.mpr ⟨hy, by simpa using hyb⟩)
      exact ⟨c, mem_insert_of_mem hc, hyc⟩
  · intro c hc d hd y hyc hyd
    rcases mem_insert.mp hc with rfl | hc <;> rcases mem_insert.mp hd with rfl | hd
    · rfl
    · exact False.elim ((mem_sdiff.mp (E.property.support d hd y hyd)).2
        (List.mem_toFinset.mpr hyc))
    · exact False.elim ((mem_sdiff.mp (E.property.support c hc y hyc)).2
        (List.mem_toFinset.mpr hyd))
    · exact E.property.separate c hc d hd y hyc hyd

private def rootChoice (x : V) (hx : x ∈ S) (E : Assembly allowed S T) :
    RootBlock allowed S T x :=
  let b := (E.property.cover x hx).choose
  let hb := (E.property.cover x hx).choose_spec
  ⟨b, hb.2, E.property.support b hb.1, E.property.admissible b hb.1,
    E.property.left_mem b hb.1, E.property.right_mem b hb.1⟩

private theorem rootChoice_mem (x : V) (hx : x ∈ S) (E : Assembly allowed S T) :
    (rootChoice x hx E).val ∈ E.val := (E.property.cover x hx).choose_spec.1

private def rootEquiv (allowed : ℕ → C → Prop) (S T : Finset V) (x : V) (hx : x ∈ S) :
    Assembly allowed S T ≃
      Σ b : RootBlock allowed S T x, Assembly allowed (S \ (vertices b.val).toFinset) T where
  toFun E := ⟨rootChoice x hx E,
    ⟨E.val.erase (rootChoice x hx E).val,
      erase_block_law E.val E.property _ (rootChoice_mem x hx E)⟩⟩
  invFun B := ⟨insert B.1.val B.2.val, insert_root_law B.1 B.2⟩
  left_inv E := by
    apply Subtype.ext
    exact insert_erase (rootChoice_mem x hx E)
  right_inv B := by
    obtain ⟨b, E⟩ := B
    have he : rootChoice x hx ⟨insert b.val E.val, insert_root_law b E⟩ = b := by
      apply Subtype.ext
      apply (insert_root_law b E).separate
        _ (rootChoice_mem x hx ⟨_, insert_root_law b E⟩) _ (mem_insert_self _ _) x
      · exact (rootChoice x hx ⟨_, insert_root_law b E⟩).property.1
      · exact b.property.1
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (fun E' => by dsimp only; rw [he])).mpr
    change (insert b.val E.val).erase
      (rootChoice x hx ⟨insert b.val E.val, insert_root_law b E⟩).val = E.val
    rw [he, erase_insert (root_not_mem b E)]

omit [DecidableEq C] in
/-- Removing the unique block at x gives the exact signed assembly recurrence.
The remaining vertices lose that block and the ambient marker domain remains T. -/
theorem assembly_weight_point_recursion (allowed : ℕ → C → Prop)
    (S T : Finset V) (x : V) (hx : x ∈ S) (sign : C → ℤ) :
    (∑ E : Assembly allowed S T, weight sign E.val) =
      ∑ b : RootBlock allowed S T x, sign (color b.val) *
        ∑ E : Assembly allowed (S \ (vertices b.val).toFinset) T, weight sign E.val := by
  classical
  calc
    _ = ∑ B : (Σ b : RootBlock allowed S T x,
          Assembly allowed (S \ (vertices b.val).toFinset) T),
        sign (color B.1.val) * weight sign B.2.val := by
      apply Fintype.sum_equiv (rootEquiv allowed S T x hx)
      intro E
      dsimp [rootEquiv]
      change weight sign E.val = sign (color (rootChoice x hx E).val) *
        weight sign (E.val.erase (rootChoice x hx E).val)
      exact (mul_prod_erase _ _ (rootChoice_mem x hx E)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro b _
      rw [mul_sum]


end

end D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
