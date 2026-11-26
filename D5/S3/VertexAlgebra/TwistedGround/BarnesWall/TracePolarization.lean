/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TracePolarization
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two lifted Weyl sections give a symmetric polarization of their coupled trace exponent. -/

module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Abel

/-! Polarization of the sign exponent for a product of Weyl intertwiners. -/

public section

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall

set_option maxHeartbeats 900000 in
/-- Polarizing the two lifted Weyl sections cancels their pullback half-Gram
terms. The surviving symmetric pairing is between the sum of the sections
(and the displacement) and the second displacement. -/
theorem trace_exponent_polarization {V C : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup C] [Module (ZMod 2) C]
    (H : LinearMap.BilinForm (ZMod 2) V) (gI gJ : V →ₗ[ZMod 2] V)
    (a b w : C →ₗ[ZMod 2] V) (phaseI phaseJ : V → ZMod 2)
    (ha : ∀ x, gI (a x) = a x + w x) (hb : ∀ x, gJ (b x) = b x + w x)
    (hI : ∀ x y, phaseI (x + y) = phaseI x + phaseI y + (H x y + H (gI x) (gI y)))
    (hJ : ∀ x y, phaseJ (x + y) = phaseJ x + phaseJ y + (H x y + H (gJ x) (gJ y)))
    (x y : C) :
    let Q := fun z => phaseI (a z) + phaseJ (b z) + H (w z) (a z + b z + w z)
    Q (x + y) = Q x + Q y +
      (H (a x + b x + w x) (w y) + H (w y) (a x + b x + w x)) := by
  dsimp only
  simp only [a.map_add, b.map_add, w.map_add, hI, hJ, ha, hb,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
  let P := H (a x) (a y) + H (b x) (b y) + H (w x) (a y) +
    H (w x) (b y) + H (w x) (w y)
  calc
    _ = phaseI (a x) + phaseJ (b x) + (H (w x) (a x) + H (w x) (b x) + H (w x) (w x)) +
        (phaseI (a y) + phaseJ (b y) + (H (w y) (a y) + H (w y) (b y) + H (w y) (w y))) +
        (H (a x) (w y) + H (b x) (w y) + H (w x) (w y) +
          (H (w y) (a x) + H (w y) (b x) + H (w y) (w x))) + (P + P) := by
      dsimp only [P]
      abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall
