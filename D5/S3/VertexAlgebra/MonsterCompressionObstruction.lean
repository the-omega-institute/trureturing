/- GID: D5/S3/VertexAlgebra/MonsterCompressionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterCompressionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Section-additive compression kills every character and cannot preserve spin. -/

/-
proof_shape: compression_obstruction: content
escape_witness: For an arbitrary target additive group and sign table, use the three
  determinant-carry directions to force the whole character fiber into the
  compression kernel, then construct two labels with equal image and different spin.
admission_basis: escape-witness
Direct frozen dependency: D5/S3/VertexAlgebra/MonsterCharacterCarry.classification_and_carry,
  statement_id sha256:a371677ae708ab55da46b776f1d86138926e22e3cb81e4fb47dd8f3dadb8b955.
-/

import D5.S3.VertexAlgebra.MonsterFusionSpan
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterCompressionObstruction

open D5.S3.VertexAlgebra.MonsterCharacterCarry
open D5.S3.VertexAlgebra.MonsterFusionSpan

/-- The finite quadratic form on defect-character labels. -/
def Q (a : Label) : F := ∑ i : Fin 3, a.1 i * a.2 i

/-- Any additive compression that makes all ground sections additive erases
the complete character fiber; the quadratic spin then cannot descend. -/
theorem compression_obstruction (f : E → E → F) (hf : IsSignTable f)
    (G : Type*) [AddCommGroup G] (p : Label →+ G)
    (hp : ∀ g h : E, p (groundSection f g + groundSection f h) =
      p (groundSection f (g + h))) :
    (∀ ξ : E, p (0, ξ) = 0) ∧
      ¬ ∃ Q' : G → F, ∀ a : Label, Q a = Q' (p a) := by
  let u0 : E := unit 0
  let u1 : E := unit 1
  let u2 : E := unit 2
  have hc := (classification_and_carry f hf).2.2.1
  have h01 : groundSection f u0 + groundSection f u1 +
      groundSection f (u0 + u1) = (0, u2) := by
    apply Prod.ext
    · funext i
      change u0 i + u1 i + (u0 + u1) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u0 u1 (unit i)
      change f u0 (unit i) + f u1 (unit i) + f (u0 + u1) (unit i) = u2 i
      rw [h]
      fin_cases i <;> decide
  have h02 : groundSection f u0 + groundSection f u2 +
      groundSection f (u0 + u2) = (0, u1) := by
    apply Prod.ext
    · funext i
      change u0 i + u2 i + (u0 + u2) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u0 u2 (unit i)
      change f u0 (unit i) + f u2 (unit i) + f (u0 + u2) (unit i) = u1 i
      rw [h]
      fin_cases i <;> decide
  have h12 : groundSection f u1 + groundSection f u2 +
      groundSection f (u1 + u2) = (0, u0) := by
    apply Prod.ext
    · funext i
      change u1 i + u2 i + (u1 + u2) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u1 u2 (unit i)
      change f u1 (unit i) + f u2 (unit i) + f (u1 + u2) (unit i) = u0 i
      rw [h]
      fin_cases i <;> decide
  have htwo (a : Label) : a + a = 0 := by
    apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _
  have hkill (g h ξ : E)
      (hb : groundSection f g + groundSection f h + groundSection f (g + h) = (0, ξ)) :
      p (0, ξ) = 0 := by
    calc
      p (0, ξ) = p (groundSection f g + groundSection f h + groundSection f (g + h)) := by
        rw [hb]
      _ = p (groundSection f (g + h) + groundSection f (g + h)) := by
        rw [p.map_add, hp, ← p.map_add]
      _ = 0 := by rw [htwo, p.map_zero]
  have h0 : p ((0, u0) : Label) = 0 := hkill u1 u2 u0 h12
  have h1 : p ((0, u1) : Label) = 0 := hkill u0 u2 u1 h02
  have h2 : p ((0, u2) : Label) = 0 := hkill u0 u1 u2 h01
  have hsmul (t : F) (a : Label) (ha : p a = 0) : p (t • a) = 0 := by
    have ht : t = 0 ∨ t = 1 := by
      fin_cases t
      · left
        rfl
      · right
        rfl
    rcases ht with ht | ht <;> subst t <;> simp [ha]
  have hpure (ξ : E) : p ((0, ξ) : Label) = 0 := by
    have hd : ((0, ξ) : Label) =
        ξ 0 • ((0, u0) : Label) + ξ 1 • ((0, u1) : Label) +
          ξ 2 • ((0, u2) : Label) := by
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [u0, u1, u2]
      · funext i
        fin_cases i <;> simp [u0, u1, u2, unit, Pi.add_apply]
    rw [hd, p.map_add, p.map_add, hsmul _ _ h0, hsmul _ _ h1,
      hsmul _ _ h2, add_zero, zero_add]
  constructor
  · exact hpure
  · rintro ⟨Q', hQ⟩
    let g : E := u0
    let ξ : E := u0
    have heq : p ((g, ξ) : Label) = p ((g, 0) : Label) := by
      have h := hpure ξ
      have hsum : ((g, 0) : Label) + (0, ξ) = (g, ξ) := by simp
      rw [← hsum, p.map_add, h, add_zero]
    have hval : Q (g, ξ) = (1 : F) := by decide
    have hzero : Q (g, 0) = (0 : F) := by simp [Q]
    have hc : Q (g, ξ) = Q (g, 0) := by
      rw [hQ, hQ, heq]
    rw [hval, hzero] at hc
    exact one_ne_zero hc

end D5.S3.VertexAlgebra.MonsterCompressionObstruction
