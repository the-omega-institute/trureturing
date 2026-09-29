/- GID: D5/S3/VertexAlgebra/DefectTwoSourceBlindness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/DefectTwoSourceBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite two-source trees have zero cubic carry response. -/

/-
proof_shape: two_source_carry_blind: content
escape_witness: Structural induction keeps the label of every finite coefficient tree
  in the two-source plane; the finite carry calculation then annihilates any three such labels.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import D5.S3.VertexAlgebra.CharacterCarryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.VertexAlgebra.DefectTwoSourceBlindness

abbrev E := Fin 3 → ZMod 2

def basis (i : Fin 3) : E := fun j => if i = j then 1 else 0

def f0 (g h : E) : ZMod 2 :=
  g 0 * h 0 + g 1 * h 1 + g 2 * h 2 +
  g 0 * h 1 + g 0 * h 2 + g 1 * h 2 +
  g 0 * g 1 * h 2 + g 0 * g 2 * h 1 + g 1 * g 2 * h 0

def alternating (mask g h : E) : ZMod 2 :=
  mask 0 * (g 0 * h 1 + g 1 * h 0) +
  mask 1 * (g 0 * h 2 + g 2 * h 0) +
  mask 2 * (g 1 * h 2 + g 2 * h 1)

def sign (mask g h : E) : ZMod 2 := f0 g h + alternating mask g h

def ell (mask g : E) : E := fun i => sign mask g (basis i)

def wedge (g h : E) : E := fun i =>
  if i = 0 then g 1 * h 2 + g 2 * h 1
  else if i = 1 then g 0 * h 2 + g 2 * h 0
  else g 0 * h 1 + g 1 * h 0

def dot (g h : E) : ZMod 2 := g 0 * h 0 + g 1 * h 1 + g 2 * h 2

def plane (g h : E) (a b : ZMod 2) : E := fun i => a * g i + b * h i

def sourceTree (g h : E) :
    CharacterCarryCompletion.LabelTree (ZMod 2 × ZMod 2) →
      CharacterCarryCompletion.LabelTree E
  | .leaf coefficients =>
      .leaf (plane g h coefficients.1 coefficients.2)
  | .fork left right =>
      .fork (sourceTree g h left) (sourceTree g h right)

-- The closed eight-mask carry calculation and recursive tree proof share this elaboration.
set_option maxHeartbeats 0 in
/-- Any finite binary composition of two-source labels remains blind to cubic carry. -/
theorem two_source_carry_blind (mask g h : E)
    (left middle right : CharacterCarryCompletion.LabelTree (ZMod 2 × ZMod 2)) :
    dot
      (CharacterCarryCompletion.carry (ell mask)
        (CharacterCarryCompletion.total (sourceTree g h left))
        (CharacterCarryCompletion.total (sourceTree g h middle)))
      (CharacterCarryCompletion.total (sourceTree g h right)) = 0 := by
  have hCarry : ∀ mask x y : E,
      CharacterCarryCompletion.carry (ell mask) x y = wedge x y := by
    decide
  have hTree (tree : CharacterCarryCompletion.LabelTree (ZMod 2 × ZMod 2)) :
      CharacterCarryCompletion.total (sourceTree g h tree) =
        plane g h (CharacterCarryCompletion.total tree).1
          (CharacterCarryCompletion.total tree).2 := by
    induction tree with
    | leaf coefficients => rfl
    | fork first second first_ih second_ih =>
        simp only [sourceTree, CharacterCarryCompletion.total, first_ih, second_ih]
        funext i
        simp only [plane, Pi.add_apply, Prod.fst_add, Prod.snd_add]
        ring
  rw [hTree left, hTree middle, hTree right, hCarry]
  simp [dot, wedge, plane]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide,
    show (6 : ZMod 2) = 0 by decide, mul_zero, add_zero]

end D5.S3.VertexAlgebra.DefectTwoSourceBlindness
