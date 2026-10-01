/- GID: D5/S3/VertexAlgebra/MonsterShortSupportSpin
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterShortSupportSpin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Monster labels carry quadratic parity and a public short-support API. -/

/-
proof_shape: finite_quadratic_ground_sections: content
escape_witness: The quadratic label is independent of the section map; right-additivity
  gives its ground value, and the opposite law gives distinct-section polar pairing.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/VertexAlgebra/MonsterShortSupport.unique_short_support.
-/

import D5.S3.VertexAlgebra.MonsterShortSupport
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterShortSupportSpin

open D5.S3.VertexAlgebra.MonsterCharacterCarry
open D5.S3.VertexAlgebra.MonsterFusionSpan
open D5.S3.VertexAlgebra.MonsterShortSupport

abbrev Coeff := Fin 7 → F

/-- Public support weight for the seven-section coefficient vector. -/
def shortWeight (c : Coeff) : Nat :=
  (Finset.univ.filter (fun i => c i = 1)).card

/-- The finite quadratic parity on a six-bit label `(g, ξ)`. -/
def labelQuadratic (x : Label) : F :=
  x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2

@[simp] theorem labelQuadratic_apply (x : Label) :
    labelQuadratic x = x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2 := rfl

private theorem coords (g : E) :
    g = g 0 • unit 0 + g 1 • unit 1 + g 2 • unit 2 := by
  funext i
  fin_cases i <;> simp [unit, Pi.add_apply, Pi.smul_apply]

private theorem right_smul (f : E → E → F) (hf : IsSignTable f)
    (g v : E) (a : F) : f g (a • v) = a * f g v := by
  have hcases : ∀ z : F, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcases := hcases a
  rcases hcases with rfl | rfl
  · rw [zero_smul, hf.zero_right, zero_mul]
  · simp

private theorem eval_coords (f : E → E → F) (hf : IsSignTable f) (g h : E) :
    f g h = h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
  have hc := coords h
  calc
    f g h = f g (h 0 • unit 0 + h 1 • unit 1 + h 2 • unit 2) := congrArg (f g) hc
    _ = f g (h 0 • unit 0) + f g (h 1 • unit 1) + f g (h 2 • unit 2) := by
      rw [hf.right_add, hf.right_add]
    _ = h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
      rw [right_smul f hf, right_smul f hf, right_smul f hf]

private theorem ground_quadratic_formula (f : E → E → F) (hf : IsSignTable f) (g : E) :
    labelQuadratic (groundSection f g) = f g g := by
  calc
    labelQuadratic (groundSection f g) =
        g 0 * f g (unit 0) + g 1 * f g (unit 1) + g 2 * f g (unit 2) := by
      simp [labelQuadratic, groundSection, ell]
    _ = f g g := (eval_coords f hf g g).symm

/-- The quadratic parity of a ground section is its diagonal sign. -/
theorem labelQuadratic_groundSection (f : E → E → F) (hf : IsSignTable f) (g : E) :
    labelQuadratic (groundSection f g) = f g g :=
  ground_quadratic_formula f hf g

theorem labelQuadratic_groundSection_nonzero (f : E → E → F) (hf : IsSignTable f)
    {g : E} (hg : g ≠ 0) :
    labelQuadratic (groundSection f g) = 1 := by
  rw [labelQuadratic_groundSection f hf]
  exact hf.diagonal g hg

private theorem labelQuadratic_add (x y : Label) :
    labelQuadratic (x + y) = labelQuadratic x + labelQuadratic y +
      (x.1 0 * y.2 0 + x.1 1 * y.2 1 + x.1 2 * y.2 2 +
       y.1 0 * x.2 0 + y.1 1 * x.2 1 + y.1 2 * x.2 2) := by
  simp only [labelQuadratic, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

private theorem ground_pairing_formula (f : E → E → F) (hf : IsSignTable f)
    (g h : E) :
    (groundSection f g).1 0 * (groundSection f h).2 0 +
      (groundSection f g).1 1 * (groundSection f h).2 1 +
      (groundSection f g).1 2 * (groundSection f h).2 2 +
      (groundSection f h).1 0 * (groundSection f g).2 0 +
      (groundSection f h).1 1 * (groundSection f g).2 1 +
      (groundSection f h).1 2 * (groundSection f g).2 2 =
      f g h + f h g := by
  calc
    _ = g 0 * f h (unit 0) + g 1 * f h (unit 1) + g 2 * f h (unit 2) +
          h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
      simp [groundSection, ell]
    _ = f h g + f g h := by
      rw [eval_coords f hf h g, eval_coords f hf g h]
      ring
    _ = f g h + f h g := by ring

/-- Distinct nonzero ground sections have polar pairing one. -/
theorem labelQuadratic_groundSection_polar
    (f : E → E → F) (hf : IsSignTable f) {g h : E}
    (hg : g ≠ 0) (hh : h ≠ 0) (hne : g ≠ h) :
    labelQuadratic (groundSection f g + groundSection f h) =
      labelQuadratic (groundSection f g) + labelQuadratic (groundSection f h) + 1 := by
  rw [labelQuadratic_add, ground_pairing_formula f hf]
  rw [hf.opposite g h hg hh hne]

#print axioms labelQuadratic_groundSection
#print axioms labelQuadratic_groundSection_polar

end D5.S3.VertexAlgebra.MonsterShortSupportSpin
