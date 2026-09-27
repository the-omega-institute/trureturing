/- GID: D5/S3/Combinatorics/Graph/OctahedralCochainSharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/OctahedralCochainSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four antipodal faces give two defects and a sharp edge-repair barrier. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.OctahedralCochainSharpness

abbrev Cube := Bool × Bool × Bool × Bool
abbrev Bits := Bool × Bool × Bool
abbrev Face := Fin 4 × Bits
abbrev Vertex := Fin 4 × Bool
abbrev Cochain := Face → ZMod 2
abbrev EdgeCochain := Finset Vertex → ZMod 2

abbrev ValidTriangle :=
  {s : Finset Vertex // s.card = 3 ∧
    ∀ v ∈ s, ∀ w ∈ s, v.1 = w.1 → v = w}

def bit (b : Cube) (i : Fin 4) : Bool :=
  if i = 0 then b.1 else if i = 1 then b.2.1 else
  if i = 2 then b.2.2.1 else b.2.2.2

def drop (i : Fin 4) (b : Cube) : Bits :=
  if i = 0 then (b.2.1, b.2.2.1, b.2.2.2) else
  if i = 1 then (b.1, b.2.2.1, b.2.2.2) else
  if i = 2 then (b.1, b.2.1, b.2.2.2) else
    (b.1, b.2.1, b.2.2.1)

def insertZero (i : Fin 4) (t : Bits) : Cube :=
  if i = 0 then (false, t.1, t.2.1, t.2.2) else
  if i = 1 then (t.1, false, t.2.1, t.2.2) else
  if i = 2 then (t.1, t.2.1, false, t.2.2) else
    (t.1, t.2.1, t.2.2, false)

/-- The four distinct vertices of a valid tetrahedron. -/
def tetraVertices (b : Cube) : Finset Vertex :=
  {(0, b.1), (1, b.2.1), (2, b.2.2.1), (3, b.2.2.2)}

/-- The unordered triangle obtained by omitting coordinate `f.1`. -/
def triA (f : Face) : Vertex :=
  if f.1 = 0 then (1, f.2.1) else (0, f.2.1)

def triB (f : Face) : Vertex :=
  if f.1 = 0 ∨ f.1 = 1 then (2, f.2.2.1) else (1, f.2.2.1)

def triC (f : Face) : Vertex :=
  if f.1 = 3 then (2, f.2.2.2) else (3, f.2.2.2)

def triangleVertices (f : Face) : Finset Vertex :=
  {triA f, triB f, triC f}

/-- A coordinate class and three signs determine an actual unordered face. -/
def triangleAsValid (f : Face) : ValidTriangle :=
  ⟨triangleVertices f, by
    have h : ∀ g : Face, (triangleVertices g).card = 3 ∧
        ∀ v ∈ triangleVertices g, ∀ w ∈ triangleVertices g,
          v.1 = w.1 → v = w := by decide
    exact h f⟩

/-- The simplicial coboundary of an edge cochain. -/
def d1 (e : EdgeCochain) : Cochain :=
  fun f => e {triA f, triB f} + e {triA f, triC f} + e {triB f, triC f}

/-- The four triangle values around a tetrahedron, in characteristic two. -/
def d2 (F : Cochain) (b : Cube) : ZMod 2 :=
  ∑ i : Fin 4, F (i, drop i b)

def weight (F : Cochain) : ℕ :=
  ∑ f : Face, if F f ≠ 0 then 1 else 0

def defects (F : Cochain) : ℕ :=
  ∑ b : Cube, if d2 F b ≠ 0 then 1 else 0

/-- The four cube edges of a monotone path between opposite tetrahedra. -/
def path : Cochain := fun f =>
  if f = ((0 : Fin 4), (false, false, false)) ∨
     f = ((1 : Fin 4), (true, false, false)) ∨
     f = ((2 : Fin 4), (true, true, false)) ∨
     f = ((3 : Fin 4), (true, true, true)) then 1 else 0

/-- The octahedral witness has two defects, while every simplicial edge
coboundary repair has at least four triangular errors. -/
theorem antipodal_repair_sharpness :
    Fintype.card Cube = 16 ∧ Fintype.card Face = 32 ∧
    Fintype.card ValidTriangle = 32 ∧
    Function.Bijective triangleAsValid ∧
    (∀ b : Cube, (tetraVertices b).card = 4 ∧
      ∀ i : Fin 4, triangleVertices (i, drop i b) ⊆ tetraVertices b) ∧
    weight path = 4 ∧ defects path = 2 ∧
    (∀ e : EdgeCochain, 4 ≤ weight (path + d1 e)) := by
  have cut (H : Cochain) (i : Fin 4) :
      (∑ b : Cube, if bit b i = false then d2 H b else 0) =
        ∑ t : Bits, H (i, t) := by
    fin_cases i <;>
      simp [bit, d2, drop, Fintype.sum_prod_type,
        Fin.sum_univ_succ] <;>
      ring_nf <;>
      simp [show (2 : ZMod 2) = 0 by decide]
  have chain (e : EdgeCochain) (b : Cube) : d2 (d1 e) b = 0 := by
    rcases b with ⟨a, c, d, f⟩
    cases a <;> cases c <;> cases d <;> cases f <;>
      simp [d2, d1, triA, triB, triC, drop,
        Fin.sum_univ_succ] <;>
      ring_nf <;>
      simp [show (2 : ZMod 2) = 0 by decide]
  have cutPath (i : Fin 4) :
      (∑ b : Cube, if bit b i = false then d2 path b else 0) = 1 := by
    fin_cases i <;> decide
  have repairDefect (e : EdgeCochain) (b : Cube) :
      d2 (path + d1 e) b = d2 path b := by
    calc
      d2 (path + d1 e) b = d2 path b + d2 (d1 e) b := by
        simp [d2, Finset.sum_add_distrib]
      _ = d2 path b := by rw [chain]; simp
  have barrier (H : Cochain)
      (hH : ∀ b : Cube, d2 H b = d2 path b) : 4 ≤ weight H := by
    have direction (i : Fin 4) : (∑ t : Bits, H (i, t)) = 1 := by
      rw [← cut]
      simp_rw [hH]
      exact cutPath i
    have nonzero (i : Fin 4) : ∃ t : Bits, H (i, t) ≠ 0 := by
      by_contra h
      push Not at h
      have hz : (∑ t : Bits, H (i, t)) = 0 := by simp [h]
      exact (by decide : (0 : ZMod 2) ≠ 1) (hz.symm.trans (direction i))
    have lower (i : Fin 4) :
        1 ≤ ∑ t : Bits, if H (i, t) ≠ 0 then 1 else 0 := by
      obtain ⟨t, ht⟩ := nonzero i
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset Bits))
        (f := fun u => if H (i, u) ≠ 0 then (1 : ℕ) else 0)
        (fun u _ => Nat.zero_le _) (Finset.mem_univ t)
      simpa [ht] using hsingle
    calc
      4 = ∑ i : Fin 4, (1 : ℕ) := by decide
      _ ≤ ∑ i : Fin 4, ∑ t : Bits, if H (i, t) ≠ 0 then 1 else 0 :=
        Finset.sum_le_sum (fun i _ => lower i)
      _ = weight H := by simp [weight, Fintype.sum_prod_type]
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  intro e
  exact barrier (path + d1 e) (repairDefect e)

#print axioms antipodal_repair_sharpness

end D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
