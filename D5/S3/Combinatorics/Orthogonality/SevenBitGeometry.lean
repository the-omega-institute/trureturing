/- GID: D5/S3/Combinatorics/Orthogonality/SevenBitGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenBitGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenBitGeometry.bits_bijective
   digest: Exact original seven-bit symplectic and quadratic data for the written nineteen-color obstruction. -/

import D5.S3.Combinatorics.Orthogonality.CompatibleFamilyCheck
import D5.S3.Combinatorics.Orthogonality.BinaryLineGraph

/-! These are the received bit coordinates, characteristic vector127, and
quadratic refinement from basis(3,12,48,65,71,95). This is the written
capacity/parity/partial-spread proof domain. No paused n7 case exclusions,
SAT run, exact chromatic number or nineteen-color witness is asserted. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitGeometry
abbrev Vector := Fin 128
abbrev Coordinates := Fin 7 → ZMod 2

def bits (v : Vector) : Coordinates := fun i => (v.val / 2^i.val % 2 : ℕ)
def add (v w : Vector) : Vector := ⟨(v.val ^^^ w.val) % 128,by omega⟩
def dot (v w : Vector) : ℕ :=
  ((List.range 7).map (fun i => (v.val / 2^i % 2) * (w.val / 2^i % 2))).sum % 2
def compatible (v w : Vector) : Bool := decide (dot v w = 1)
def even (v : Vector) : Prop := dot v v = 0
instance (v : Vector) : Decidable (even v) := inferInstanceAs (Decidable (_ = _))
def oddPoint (v : Vector) : Vector := add v 127

def evenPoints : Finset Vector := Finset.univ.filter (fun v => v ≠ 0 ∧ even v)
def deleted : List Vector := (List.finRange 128).filter (fun v => v ≠ 0 ∧ v ≠ 127)
def evenPart (S : Finset Vector) : Finset Vector := S.filter even
def oddPoints (S : Finset Vector) : Finset Vector := (S.filter (fun v => ¬ even v)).image oddPoint

/-- Exact original refinement in the supplied symplectic coordinates. -/
def quadratic (v : Vector) : ℕ :=
  let b := fun i : ℕ => v.val / 2^i % 2
  let c5 := (b 4 + b 5) % 2
  let c4 := (b 2 + b 3) % 2
  let c2 := b 5
  let c1 := (b 3 + c5) % 2
  let c0 := (b 1 + c4 + c5) % 2
  let c3 := (b 6 + c4 + c5) % 2
  (c0*c3+c1*c4+c2*c5) % 2

/-- Full original nonzero points of a three-dimensional Lagrangian,
including XOR closure and all point/hyperplane incidence counts. -/
def LagrangianData (L : Finset Vector) : Prop :=
  L ⊆ evenPoints ∧ L.card = 7 ∧
  (∀ u ∈ L, ∀ v ∈ L, dot u v = 0) ∧
  (∀ u ∈ insert 0 L, ∀ v ∈ insert 0 L, add u v ∈ insert 0 L) ∧
  ∀ e ∈ evenPoints, (L.filter (fun v => dot e v = 0)).card = if e ∈ L then 7 else 3
instance (L : Finset Vector) : Decidable (LagrangianData L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every saturated class in the original deleted line graph has exactly
one of the received three types. The entire odd fiber is retained. -/
def ClassProperty (S : Finset Vector) : Prop :=
  S.card ≤ 7 ∧ (S.card = 7 →
    ((evenPart S).card = 7 ∧ (∑ v ∈ evenPart S, quadratic v) % 2 = 1) ∨
    (evenPart S).card = 6 ∨
    ((evenPart S).card = 0 ∧ LagrangianData (oddPoints S)))
instance (S : Finset Vector) : Decidable (ClassProperty S) :=
  inferInstanceAs (Decidable (_ ∧ _))

def good (S : Finset Vector) : Bool := decide (ClassProperty S)
/-- Exact complete finite coordinate equivalence, not selected vectors. -/
theorem bits_bijective : Function.Bijective bits := by decide +kernel

theorem bits_zero : bits 0 = 0 := by decide +kernel

theorem bits_add : ∀ u v : Vector, bits (add u v) = bits u + bits v := by
  decide +kernel

theorem bits_dot : ∀ u v : Vector,
    dotProduct (bits u) (bits v) = 0 ↔ dot u v = 0 := by decide +kernel

/-- The entire original even-point domain. -/
theorem even_card : evenPoints.card = 63 := by decide +kernel

/-- All nonzero even-point hyperplanes have the received31 points. -/
theorem hyperplane_card : ∀ e ∈ evenPoints,
    (evenPoints.filter (fun v => dot e v = 0)).card = 31 := by decide +kernel

/-- Exact received quadratic total, over every nonzero even point. -/
theorem quadratic_total : (∑ v ∈ evenPoints, quadratic v) = 28 := by decide +kernel

/-- The complete original polarization identity, on all4096 pairs. -/
theorem quadratic_polarization : ∀ u ∈ insert 0 evenPoints, ∀ v ∈ insert 0 evenPoints,
    quadratic (add u v) = (quadratic u + quadratic v + dot u v) % 2 := by
  decide +kernel

/-- Every original nonzero bit vector, with no coordinate-line restriction. -/
abbrev LineVertex := {v : Vector // v ≠ 0}

def graph : SimpleGraph LineVertex where
  Adj u v := u ≠ v ∧ dot u.val v.val = 0
  symm := ⟨by
    intro u v h
    have hs : ∀ a b : Vector, dot a b = dot b a := by
      intro a b
      simp only [dot,Nat.mul_comm]
    exact ⟨h.1.symm,(hs v.val u.val).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The full original126-line domain, deleting precisely the characteristic line. -/
abbrev DeletedVertex := {v : LineVertex // v.val ≠ 127}
def deletedGraph : SimpleGraph DeletedVertex := graph.induce {v : LineVertex | v.val ≠ 127}

noncomputable def bitsEquiv : Vector ≃ Coordinates :=
  Equiv.ofBijective bits bits_bijective

noncomputable def vectorEquiv : LineVertex ≃ BinaryLineGraph.VectorVertex 7 :=
  bitsEquiv.subtypeEquiv (fun v => by
    change v ≠ 0 ↔ bitsEquiv v ≠ 0
    have hz : bitsEquiv 0 = 0 := bits_zero
    rw [← hz,bitsEquiv.injective.ne_iff])

/-- Complete actual vector-graph transport, in both directions. -/
noncomputable def maskGraphIso : graph ≃g BinaryLineGraph.vectorGraph 7 where
  toEquiv := vectorEquiv
  map_rel_iff' := by
    intro x y
    change (vectorEquiv x ≠ vectorEquiv y ∧ dotProduct (bits x.val) (bits y.val) = 0) ↔
      (x ≠ y ∧ dot x.val y.val = 0)
    rw [vectorEquiv.injective.ne_iff,bits_dot]

/-- The original graph is exactly the full graph on actual one-dimensional Submodules. -/
noncomputable def actualLineGraphIso : graph ≃g BinaryLineGraph.lineGraph 7 :=
  maskGraphIso.trans (BinaryLineGraph.graphIso 7)

end D5.S3.Combinatorics.Orthogonality.SevenBitGeometry
