/- GID: D5/S3/HomologicalAlgebra/InflatedCupCoboundary
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A central sign coordinate trivializes the inflated linear cup term. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

/-! The linear multiples of the extension quadratic function disappear
on inflation to the sign extension. The central coordinate gives the
explicit null-cochain. This is the cup product step in excluding the
degree-three candidates for the Barnes–Wall chiral anomaly. -/

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.InflatedCupCoboundary

open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (F₂ SignExtension)

variable {A : Type*} [AddCommGroup A] (c : A →+ A →+ F₂) (ell : A →+ F₂)

/-- On the abelian quotient the extension cocycle cupped with a linear
character is a 3-cocycle. Its diagonal is the product of the quadratic
function with that character. -/
theorem cup_cocycle (g h k l : A) :
    c h k * ell l - c (g + h) k * ell l + c g (h + k) * ell l -
      c g h * ell (k + l) + c g h * ell k = 0 := by
  simp only [map_add, AddMonoidHom.add_apply]
  ring

/-- The sign coordinate carries the extension cocycle. Cupping the sign
coordinate with a linear character gives the primitive of the inflated
3-cocycle. -/
theorem inflated_cup_is_coboundary (g h k : SignExtension A c) :
    h.sign * ell k.charge - (g * h).sign * ell k.charge +
      g.sign * ell (h * k).charge - g.sign * ell h.charge =
      c g.charge h.charge * ell k.charge := by
  change h.sign * ell k.charge -
      (g.sign + h.sign + c g.charge h.charge) * ell k.charge +
      g.sign * ell (h.charge + k.charge) - g.sign * ell h.charge = _
  simp only [map_add, CharTwo.sub_eq_add, mul_add, add_mul]
  let u := h.sign * ell k.charge
  let v := g.sign * ell k.charge
  let w := g.sign * ell h.charge
  calc
    _ = c g.charge h.charge * ell k.charge + (u + u) + (v + v) + (w + w) := by
      dsimp only [u, v, w]
      ring
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

end D5.S3.HomologicalAlgebra.InflatedCupCoboundary
