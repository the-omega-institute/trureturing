/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/FirstSlotLiftPhase
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two exceptional slots have triangular complement corrections. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliPairing

/-! The half-Gram correction of each exceptional Barnes–Wall generator is
supported on a complement pairing in its first-bit block. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.FirstSlotLiftPhase

open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word complement parity pairing complementTriangle phaseQuadratic)

variable {ι : Type} [Fintype ι] [LinearOrder ι]

abbrev Coordinate (ι : Type) := Bool × Word ι

def headFlip (u : Coordinate ι) : Coordinate ι := (!u.1, u.2)

def active (bit : Bool) (u : Coordinate ι) : Prop :=
  u.1 = bit ∧ parity u.2 = (if bit then 0 else 1)

def evenWord (u : Coordinate ι) : Prop :=
  parity u.2 = (if u.1 then 1 else 0)

open Classical in
noncomputable def headDeviation (bit : Bool) : Matrix (Coordinate ι) (Coordinate ι) F₂ :=
  fun u v => if active bit u ∧ v = headFlip u then 1 else 0

noncomputable def halfComplement : Matrix (Coordinate ι) (Coordinate ι) F₂ :=
  fun u v => if u.1 = true ∧ v.1 = false then pairing u.2 v.2 else 0

private theorem parity_complement (hcard : (Fintype.card ι : F₂) = 0) (u : Word ι) :
    parity (complement u) = parity u := by
  apply CharTwo.add_eq_zero.mp
  unfold parity
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ r : ι, (1 : F₂) := by
      apply Finset.sum_congr rfl
      intro r _
      cases hu : u r <;> simp [complement, hu]
    _ = 0 := by simpa using hcard

private theorem even_headFlip (bit : Bool) (u : Coordinate ι) (hu : active bit u) :
    evenWord (headFlip u) := by
  obtain ⟨hbit, hparity⟩ := hu
  cases bit <;> simpa [headFlip, evenWord, hbit] using hparity

open Classical in
private theorem deviation_left (bit : Bool) (A : Matrix (Coordinate ι) (Coordinate ι) F₂)
    (u v : Coordinate ι) :
    (headDeviation bit * A : Matrix (Coordinate ι) (Coordinate ι) F₂) u v =
      if active bit u then A (headFlip u) v else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hu : active bit u <;> simp [headDeviation, hu, ite_mul]

open Classical in
private theorem deviation_right (bit : Bool) (A : Matrix (Coordinate ι) (Coordinate ι) F₂)
    (u v : Coordinate ι) :
    (A * (headDeviation bit)ᵀ : Matrix (Coordinate ι) (Coordinate ι) F₂) u v =
      if active bit v then A u (headFlip v) else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hv : active bit v <;> simp [headDeviation, hv, mul_ite]

open Classical in
/-- In the half-Gram correction from KRR Lemma A.4, the part vanishing
on even full words contributes zero. The remaining part is the tail
complement pairing supported on the selected first-bit block. -/
theorem first_slot_correction (hcard : (Fintype.card ι : F₂) = 0)
    (H₂ : Matrix (Coordinate ι) (Coordinate ι) F₂)
    (hrow : ∀ u v, evenWord u → H₂ u v = 0)
    (hcol : ∀ u v, evenWord v → H₂ u v = 0)
    (bit : Bool) (u v : Coordinate ι) :
    let A := headDeviation bit
    let H := halfComplement + H₂
    (A * H + H * Aᵀ + A * H * Aᵀ : Matrix (Coordinate ι) (Coordinate ι) F₂) u v =
      if active bit u ∧ active bit v then pairing u.2 v.2 else 0 := by
  classical
  dsimp only
  have hl : headDeviation bit * H₂ = 0 := by
    ext x y
    rw [deviation_left]
    split
    · rename_i hx
      exact hrow _ _ (even_headFlip bit x hx)
    · rfl
  have hr : H₂ * (headDeviation bit)ᵀ = 0 := by
    ext x y
    rw [deviation_right]
    split
    · rename_i hy
      exact hcol _ _ (even_headFlip bit y hy)
    · rfl
  rw [mul_add, add_mul, hl, hr, add_zero, add_zero]
  simp only [Matrix.add_apply, deviation_right, deviation_left]
  obtain ⟨a, x⟩ := u
  obtain ⟨b, y⟩ := v
  by_cases h : y = complement x
  · subst y
    cases bit <;> cases a <;> cases b <;>
      simp [active, halfComplement, headFlip, parity_complement hcard]
  · cases bit <;> cases a <;> cases b <;>
      simp [active, halfComplement, headFlip, pairing, h]

private theorem sum_head_block (bit : Bool) (F : Coordinate ι → Coordinate ι → F₂)
    (P : Word ι → Word ι → F₂)
    (h : ∀ (p q : Bool) (u v : Word ι),
      F (p, u) (q, v) = if p = bit ∧ q = bit then P u v else 0) :
    (∑ u, ∑ v, F u v) = ∑ u, ∑ v, P u v := by
  simp_rw [Fintype.sum_prod_type, h, Fintype.sum_bool]
  cases bit <;> simp

open Classical in
/-- Reading the triangular half-Gram correction on a coordinate vector
recovers the complement quadratic form on its active tail coordinates. -/
theorem first_slot_exponent (hcard : (Fintype.card ι : F₂) = 0)
    (H₂ : Matrix (Coordinate ι) (Coordinate ι) F₂)
    (hrow : ∀ u v, evenWord u → H₂ u v = 0)
    (hcol : ∀ u v, evenWord v → H₂ u v = 0)
    (bit : Bool) (a : Coordinate ι → F₂) (order : LinearOrder (Word ι))
    (strictTriangle : Coordinate ι → Coordinate ι → Prop)
    (horder : ∀ u v, strictTriangle (bit, u) (bit, v) ↔ @LT.lt _ order.toLT u v) :
    let D := headDeviation bit
    let H := halfComplement + H₂
    let C : Matrix (Coordinate ι) (Coordinate ι) F₂ := D * H + H * Dᵀ + D * H * Dᵀ
    let R : Matrix (Coordinate ι) (Coordinate ι) F₂ :=
      fun u v => if strictTriangle u v then C u v else 0
    R.toBilin' a a = phaseQuadratic order (fun u => if active bit (bit, u) then a (bit, u) else 0) := by
  classical
  intro D H C R
  let b : Word ι → F₂ := fun u => if active bit (bit, u) then a (bit, u) else 0
  change R.toBilin' a a = phaseQuadratic order b
  have hc (u v : Coordinate ι) :
      C u v = if active bit u ∧ active bit v then pairing u.2 v.2 else 0 :=
    first_slot_correction hcard H₂ hrow hcol bit u v
  have entry (p q : Bool) (u v : Word ι) :
      a (p, u) * R (p, u) (q, v) * a (q, v) =
        if p = bit ∧ q = bit then b u * complementTriangle order u v * b v else 0 := by
    change a (p, u) * (if strictTriangle (p, u) (q, v) then C (p, u) (q, v) else 0) *
      a (q, v) = _
    rw [hc]
    by_cases hp : p = bit
    · subst p
      by_cases hq : q = bit
      · subst q
        by_cases hu : active bit (bit, u) <;> by_cases hv : active bit (bit, v) <;>
          simp [b, hu, hv, complementTriangle, horder]
      · simp [active, hq]
    · simp [active, hp]
  simpa only [phaseQuadratic, Matrix.toBilin'_apply] using sum_head_block bit
    (fun u v => a u * R u v * a v) (fun u v => b u * complementTriangle order u v * b v) entry

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.FirstSlotLiftPhase
