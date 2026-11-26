/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/FixedWordPhase
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/FixedWordPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exceptional half-Gram phases vanish on fixed Pauli involution charges. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorSubsetRows
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.FirstSlotLiftPhase

/-! The complement phases of a lifted Pauli word cancel on its integral
fixed lattice coordinates. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.FixedWordPhase

open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word phaseQuadratic fixed_phase_zero)
open TailPauliQuotientMaps (Coeff embed reduce signedWord selections dev
  signedWord_transport_in_B)

variable {ι : Type} [Fintype ι] [LinearOrder ι] [Nonempty ι]

/-- The selected first-slot factors act after the signed tail operator.
The coordinates in the ambient pair are `(a + b, b)`. -/
theorem fixed_word_phase (negative xFirst zFirst : Bool) (word : List (ι × Bool))
    (order : LinearOrder (Word ι)) (a b : Coeff ι)
    (haway : ∀ r s : ι, ∃ t, t ≠ r ∧ t ≠ s)
    (hsquare : (∑ r, selections false word r * selections true word r) =
      (if xFirst then 1 else 0) * (if zFirst then 1 else 0))
    (hfixed :
      let g := signedWord negative 0 word
      let t := embed 0 a + b
      (if xFirst then g b else g t) = t ∧
      (if zFirst then -(if xFirst then g t else g b) else
        (if xFirst then g t else g b)) = b) :
    (if xFirst then phaseQuadratic order (reduce 1 a) else 0) +
      (if zFirst then phaseQuadratic order (reduce 0 b) else 0) = 0 := by
  let g := signedWord negative 0 word
  let M := TailPauliPairing.deviationMatrix (selections false word) (selections true word)
  obtain ⟨⟨_, hB⟩, c, hhalf, hA⟩ := signedWord_transport_in_B negative word b a
  change reduce 1 (dev g b) = reduce 0 b ᵥ* M at hB
  change dev g (embed 0 a) = (2 : ℤ) • c at hhalf
  change reduce 0 c = reduce 1 a ᵥ* M at hA
  apply fixed_phase_zero order _ _ haway xFirst zFirst _ _ hsquare
  · intro hx
    have hb : g b = embed 0 a + b := by simpa [g, hx] using hfixed.1
    have hd : dev g b = embed 0 a := by
      change g b - b = _
      rw [hb, add_sub_cancel_right]
    rw [← hB, hd]
    funext u
    by_cases hp : TailPauliPairing.parity u = 1
    · simp [hp, embed]
    · simp [hp]
  · intro hx hz
    have hb : -(g b) = b := by simpa [g, hx, hz] using hfixed.2
    have ht : g (embed 0 a + b) = embed 0 a + b := by
      simpa [g, hx] using hfixed.1
    have hd : dev g (embed 0 a) = (2 : ℤ) • b := by
      change g (embed 0 a) - embed 0 a = _
      rw [map_add] at ht
      rw [two_smul]
      linear_combination (norm := abel) ht + hb
    have hc : c = b := by
      funext v
      have he := congrFun (hhalf.symm.trans hd) v
      change 2 * c v = 2 * b v at he
      omega
    rw [← hA, hc]

open TensorSubsetRows (synthesize ambientWord ambientWord_square rationalSign
  synthesize_injective synthesize_signedWord)

private theorem rationalSign_injective : Function.Injective rationalSign := by
  intro a b h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact ha.trans hb.symm
  · norm_num [rationalSign, ha, hb] at h
  · norm_num [rationalSign, ha, hb] at h
  · have hz : ∀ t : F₂, t = 0 ∨ t = 1 := by decide +kernel
    exact ((hz a).resolve_left ha).trans ((hz b).resolve_left hb).symm

/-- A fixed vector for the signed Pauli action on the synthesized ambient
pair has zero exceptional phase when the tail square supplies the
first-slot central sign. -/
theorem fixed_word_phase_of_ambient {n : ℕ} [Nonempty (Fin n)]
    (word : List (Fin n × Bool)) (negative xFirst zFirst : Bool)
    (order : LinearOrder (Word (Fin n))) (a b : Coeff (Fin n))
    (heven : (n : F₂) = 0)
    (haway : ∀ r s : Fin n, ∃ t, t ≠ r ∧ t ≠ s)
    (hsquare : ∀ (f : Word (Fin n) → ℚ) (v : Word (Fin n)),
      ambientWord word (ambientWord word f) v =
        rationalSign ((if xFirst then 1 else 0) * (if zFirst then 1 else 0)) * f v)
    (hfixed :
      let t := synthesize (embed 0 a + b)
      let s := synthesize b
      let g (f : Word (Fin n) → ℚ) := if negative then -ambientWord word f else ambientWord word f
      (if xFirst then g s else g t) = t ∧
      (if zFirst then -(if xFirst then g t else g s) else
        (if xFirst then g t else g s)) = s) :
    (if xFirst then phaseQuadratic order (reduce 1 a) else 0) +
      (if zFirst then phaseQuadratic order (reduce 0 b) else 0) = 0 := by
  have he : (Fintype.card (Fin n) : F₂) = 0 := by simpa using heven
  have hneg (c : Coeff (Fin n)) : synthesize (-c) = -synthesize c := by
    funext v
    simp [synthesize, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  have hparity := hsquare (fun _ => 1) (fun _ => false)
  rw [ambientWord_square, mul_one, mul_one] at hparity
  apply fixed_word_phase negative xFirst zFirst word order a b haway
    (rationalSign_injective hparity)
  constructor
  · apply synthesize_injective
    cases xFirst <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, synthesize_signedWord he] using hfixed.1
  · apply synthesize_injective
    cases xFirst <;> cases zFirst <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, hneg, synthesize_signedWord he]
        using hfixed.2

private theorem ambientWord_neg (word : List (ι × Bool)) (f : Word ι → ℚ) :
    ambientWord word (-f) = -ambientWord word f := by
  induction word generalizing f with
  | nil => rfl
  | cons factor word ih =>
    obtain ⟨r, isZ⟩ := factor
    rw [ambientWord, ambientWord]
    have h : (fun v : Word ι =>
        if isZ then (if v r then (-1 : ℚ) else 1) * (-f) v
        else (-f) (TailPauliPairing.flip v r)) =
        -(fun v : Word ι => if isZ then (if v r then (-1 : ℚ) else 1) * f v
          else f (TailPauliPairing.flip v r)) := by
      funext v
      cases isZ <;> simp [mul_neg]
    rw [h, ih]

/-- The signed Pauli action on the two ambient coordinate slices. -/
def ambientPairAction (word : List (ι × Bool)) (negative xFirst zFirst : Bool)
    (p : (Word ι → ℚ) × (Word ι → ℚ)) : (Word ι → ℚ) × (Word ι → ℚ) :=
  let g (f : Word ι → ℚ) := if negative then -ambientWord word f else ambientWord word f
  let t := if xFirst then g p.2 else g p.1
  let s := if xFirst then g p.1 else g p.2
  (t, if zFirst then -s else s)

/-- For an actual ambient Pauli involution, the exceptional lift phase
vanishes on every integral fixed vector. -/
theorem fixed_word_phase_of_involution {n : ℕ} [Nonempty (Fin n)]
    (word : List (Fin n × Bool)) (negative xFirst zFirst : Bool)
    (order : LinearOrder (Word (Fin n))) (a b : Coeff (Fin n))
    (heven : (n : F₂) = 0)
    (haway : ∀ r s : Fin n, ∃ t, t ≠ r ∧ t ≠ s)
    (hsquare : Function.Involutive (ambientPairAction word negative xFirst zFirst))
    (hfixed : let p := (synthesize (embed 0 a + b), synthesize b)
      ambientPairAction word negative xFirst zFirst p = p) :
    (if xFirst then phaseQuadratic order (reduce 1 a) else 0) +
      (if zFirst then phaseQuadratic order (reduce 0 b) else 0) = 0 := by
  let f : Word (Fin n) → ℚ := fun _ => 1
  have h := congrArg (fun p : (Word (Fin n) → ℚ) × (Word (Fin n) → ℚ) =>
    p.1 (fun _ => false)) (hsquare (f, f))
  have hsign : rationalSign (∑ r, selections false word r * selections true word r) =
      rationalSign ((if xFirst then 1 else 0) * (if zFirst then 1 else 0)) := by
    cases negative <;> cases xFirst <;> cases zFirst <;>
      simp [ambientPairAction, ambientWord_neg, ambientWord_square, f] at h <;>
      first
      | simpa [rationalSign] using h
      | simpa [rationalSign] using neg_eq_iff_eq_neg.mp h
  apply fixed_word_phase_of_ambient word negative xFirst zFirst order a b heven haway
  · intro g v
    rw [ambientWord_square, hsign]
  · exact ⟨congrArg Prod.fst hfixed, congrArg Prod.snd hfixed⟩

open FirstSlotLiftPhase (Coordinate evenWord headDeviation halfComplement first_slot_exponent)

private noncomputable def exceptionalPhase
    (H₂ : Matrix (Coordinate ι) (Coordinate ι) F₂)
    (triangle : Coordinate ι → Coordinate ι → Prop) (bit : Bool)
    (coeff : Coordinate ι → F₂) : F₂ := by
  classical
  let A : Matrix (Coordinate ι) (Coordinate ι) F₂ := headDeviation bit
  let H := halfComplement + H₂
  let R : Matrix (Coordinate ι) (Coordinate ι) F₂ :=
    fun u v => if triangle u v then (A * H + H * Aᵀ + A * H * Aᵀ) u v else 0
  exact R.toBilin' coeff coeff

/-- The two triangular half-Gram corrections of a literal Pauli involution
cancel on every fixed vector in the integral tensor lattice. -/
theorem half_gram_phase_zero_of_involution {n : ℕ} [Nonempty (Fin n)]
    (word : List (Fin n × Bool)) (negative xFirst zFirst : Bool)
    (order : LinearOrder (Word (Fin n))) (a b : Coeff (Fin n))
    (H₂ : Matrix (Coordinate (Fin n)) (Coordinate (Fin n)) F₂)
    (hrow : ∀ u v, evenWord u → H₂ u v = 0)
    (hcol : ∀ u v, evenWord v → H₂ u v = 0)
    (triangle : Coordinate (Fin n) → Coordinate (Fin n) → Prop)
    (horder : ∀ bit u v, triangle (bit, u) (bit, v) ↔ @LT.lt _ order.toLT u v)
    (heven : (n : F₂) = 0)
    (haway : ∀ r s : Fin n, ∃ t, t ≠ r ∧ t ≠ s)
    (hsquare : Function.Involutive (ambientPairAction word negative xFirst zFirst))
    (hfixed : let p := (synthesize (embed 0 a + b), synthesize b)
      ambientPairAction word negative xFirst zFirst p = p) :
    let coeff : Coordinate (Fin n) → F₂ := fun u => if u.1 then b u.2 else a u.2
    (if xFirst then exceptionalPhase H₂ triangle false coeff else 0) +
      (if zFirst then exceptionalPhase H₂ triangle true coeff else 0) = 0 := by
  classical
  let coeff : Coordinate (Fin n) → F₂ := fun u => if u.1 then b u.2 else a u.2
  have he : (Fintype.card (Fin n) : F₂) = 0 := by simpa using heven
  have hx : exceptionalPhase H₂ triangle false coeff = phaseQuadratic order (reduce 1 a) := by
    have h := first_slot_exponent he H₂ hrow hcol false coeff order triangle (horder false)
    rw [show reduce 1 a = (fun u : Word (Fin n) =>
      if TailPauliPairing.parity u = 1 then (a u : F₂) else 0) from rfl]
    simpa [exceptionalPhase, FirstSlotLiftPhase.active, coeff] using h
  have hz : exceptionalPhase H₂ triangle true coeff = phaseQuadratic order (reduce 0 b) := by
    have h := first_slot_exponent he H₂ hrow hcol true coeff order triangle (horder true)
    rw [show reduce 0 b = (fun u : Word (Fin n) =>
      if TailPauliPairing.parity u = 0 then (b u : F₂) else 0) from rfl]
    simpa [exceptionalPhase, FirstSlotLiftPhase.active, coeff] using h
  change (if xFirst then exceptionalPhase H₂ triangle false coeff else 0) +
    (if zFirst then exceptionalPhase H₂ triangle true coeff else 0) = 0
  rw [hx, hz]
  exact fixed_word_phase_of_involution word negative xFirst zFirst order a b
    heven haway hsquare hfixed

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.FixedWordPhase
