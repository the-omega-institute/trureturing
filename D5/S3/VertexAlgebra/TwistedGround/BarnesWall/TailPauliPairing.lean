/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TailPauliPairing
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The tail deviation maps pull back the complement quadratic form. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8TraceSign
import Batteries.Tactic.OpenPrivate

/-! The two quotient maps of the Barnes–Wall tail lattices pull back
the complement pairing by the square exponent of the Pauli word. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliPairing

open LatticeTwistedGroundRealization (symmetric_pairing_split)
open LatticeTwistedGroundRealization.SignQuotient (F₂)

variable {ι : Type} [Fintype ι] [LinearOrder ι]

abbrev Word (ι : Type*) := ι → Bool

def complement (u : Word ι) : Word ι := fun t => !(u t)

def flip (u : Word ι) (r : ι) : Word ι :=
  fun t => if t = r then !(u t) else u t

def activity (x z : ι → F₂) (u : Word ι) (r : ι) : F₂ :=
  if u r then z r else x r

noncomputable def pairing (u v : Word ι) : F₂ := by
  classical
  exact if v = complement u then 1 else 0

private theorem flipped_bits_iff (a b : Bool) (p q : Prop) [Decidable p] [Decidable q] :
    (if q then !b else b) = !(if p then !a else a) ↔
      (a == b) = xor (decide p) (decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> cases a <;> cases b <;> simp [hp, hq]

omit [Fintype ι] in
private theorem flip_complement_iff (u v : Word ι) (r s : ι) :
    flip v s = complement (flip u r) ↔
      ∀ t, (u t == v t) = xor (decide (t = r)) (decide (t = s)) := by
  rw [funext_iff]
  apply forall_congr'
  intro t
  exact flipped_bits_iff (u t) (v t) (t = r) (t = s)

omit [Fintype ι] in
private theorem flip_complement_diag (u v : Word ι) (r : ι) :
    flip v r = complement (flip u r) ↔ v = complement u := by
  rw [flip_complement_iff, funext_iff]
  apply forall_congr'
  intro t
  cases hu : u t <;> cases v t <;> simp [complement, hu]

omit [Fintype ι] in
private theorem flip_complement_swap (u v : Word ι) (r s : ι) :
    flip v s = complement (flip u r) ↔ flip v r = complement (flip u s) := by
  rw [flip_complement_iff, flip_complement_iff]
  simp only [Bool.xor_comm]

omit [Fintype ι] in
/-- A single row is supported on a set on which the complement pairing
vanishes. In particular, its diagonal values for the paired quadratic form
are all zero. -/
theorem neighbors_not_complementary (u : Word ι) (r s : ι)
    (ht : ∃ t, t ≠ r ∧ t ≠ s) :
    flip u s ≠ complement (flip u r) := by
  intro h
  obtain ⟨t, hr, hs⟩ := ht
  have h' := (flip_complement_iff u u r s).mp h t
  simp [hr, hs] at h'

private noncomputable def coefficient (x z : ι → F₂) (u v : Word ι) :
    Matrix ι ι F₂ :=
  fun r s => activity x z u r * activity x z v s * pairing (flip u r) (flip v s)

private theorem coefficient_diagonal (x z : ι → F₂) (u v : Word ι) (r : ι) :
    coefficient x z u v r r = x r * z r * pairing u v := by
  classical
  unfold coefficient pairing
  simp only [flip_complement_diag]
  by_cases h : v = complement u
  · subst v
    cases hu : u r <;> simp [activity, complement, hu, mul_comm]
  · simp [h]

private theorem coefficient_symmetric (x z : ι → F₂) (u v : Word ι) :
    (coefficient x z u v).IsSymm := by
  classical
  ext r s
  change coefficient x z u v s r = coefficient x z u v r s
  by_cases h : r = s
  · subst s
    rfl
  have hswitch := flip_complement_swap u v r s
  by_cases hp : flip v s = complement (flip u r)
  · have hv := (flip_complement_iff u v r s).mp hp
    have hr : u r = v r := by
      apply beq_iff_eq.mp
      simpa [h] using hv r
    have hs : u s = v s := by
      apply beq_iff_eq.mp
      simpa [Ne.symm h] using hv s
    simp only [coefficient, pairing, hp, hswitch.mp hp, ite_true, mul_one, activity, ← hr, ← hs]
    exact mul_comm _ _
  · have hp' : flip v r ≠ complement (flip u s) := fun hs => hp (hswitch.mpr hs)
    simp [coefficient, pairing, hp, hp']

/-- The pullback of the complement pairing under the tail deviation maps
is scaled by the exponent of the square of the Pauli group element. -/
theorem tail_pullback_pairing (x z : ι → F₂) (u v : Word ι) :
    (∑ r, ∑ s,
      activity x z u r * activity x z v s * pairing (flip u r) (flip v s)) =
      (∑ r, x r * z r) * pairing u v := by
  let S := coefficient x z u v
  have h := symmetric_pairing_split S (coefficient_symmetric x z u v)
    (fun _ => 1) (fun _ => 1)
  simp only [Matrix.toBilin'_apply, one_mul, mul_one, CharTwo.add_self_eq_zero, mul_zero,
    Finset.sum_const_zero, add_zero] at h
  change (∑ r, ∑ s, S r s) = _
  rw [h, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => coefficient_diagonal x z u v r

open Q8TraceSign (same_quadratic)

variable (order : LinearOrder (Word ι))

/-- A strict triangular representative of the quadratic form that pairs each
tail word with its complement, with zero basis values. -/
noncomputable def complementTriangle (order : LinearOrder (Word ι)) :
    Matrix (Word ι) (Word ι) F₂ :=
  fun u v => @ite F₂ (@LT.lt _ order.toLT u v) (order.toDecidableLT u v) (pairing u v) 0

omit [Fintype ι] [LinearOrder ι] in
private theorem complement_involutive : Function.Involutive (complement (ι := ι)) := by
  intro u
  funext r
  simp [complement]

omit [LinearOrder ι] in
private theorem pairing_symm (u v : Word ι) : pairing u v = pairing v u := by
  classical
  have h : v = complement u ↔ u = complement v := by
    constructor <;> intro h <;> subst_vars <;> exact (complement_involutive _).symm
  simp only [pairing, h]

omit [LinearOrder ι] in
private theorem pairing_self [Nonempty ι] (u : Word ι) : pairing u u = 0 := by
  classical
  obtain ⟨r⟩ := (inferInstance : Nonempty ι)
  have hn : u ≠ complement u := by
    intro h
    have hr := congrFun h r
    cases hu : u r <;> simp [complement, hu] at hr
  simp [pairing, hn]

omit [LinearOrder ι] in
private theorem triangle_symmetrize [Nonempty ι] (u v : Word ι) :
    complementTriangle order u v + complementTriangle order v u = pairing u v := by
  rcases @lt_trichotomy _ order u v with huv | rfl | hvu
  · simp [complementTriangle, huv, @lt_asymm _ order.toPreorder _ _ huv]
  · simp [complementTriangle, @lt_irrefl _ order.toPreorder u, pairing_self]
  · simp [complementTriangle, hvu, @lt_asymm _ order.toPreorder _ _ hvu, pairing_symm v u]

/-- The coefficients obtained by applying the two quotient deviations to the
arguments of the complement quadratic form. -/
noncomputable def pulledTriangle (x z : ι → F₂) : Matrix (Word ι) (Word ι) F₂ :=
  fun u v => ∑ r, ∑ s, activity x z u r * activity x z v s *
    complementTriangle order (flip u r) (flip v s)

private theorem pulledTriangle_symmetrize [Nonempty ι] (x z : ι → F₂) (u v : Word ι) :
    pulledTriangle order x z u v + pulledTriangle order x z v u =
      (∑ r, x r * z r) * pairing u v := by
  have hswap : pulledTriangle order x z v u = ∑ r, ∑ s,
      activity x z u r * activity x z v s * complementTriangle order (flip v s) (flip u r) := by
    rw [pulledTriangle, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm (activity x z v s)]
  rw [hswap, pulledTriangle, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← mul_add, triangle_symmetrize order]
  exact tail_pullback_pairing x z u v

/-- Pulling back the complement quadratic form by the sparse Pauli tail
deviation scales it by the square exponent. -/
theorem tail_pullback_quadratic [Nonempty ι] (x z : ι → F₂)
    (haway : ∀ r s : ι, ∃ t, t ≠ r ∧ t ≠ s) (a : Word ι → F₂) :
    (pulledTriangle order x z).toBilin' a a =
      ((∑ r, x r * z r) • complementTriangle order).toBilin' a a := by
  apply @same_quadratic (Word ι) inferInstance order
  · intro u
    have hdiag : pulledTriangle order x z u u = 0 := by
      unfold pulledTriangle
      apply Finset.sum_eq_zero
      intro r _
      apply Finset.sum_eq_zero
      intro s _
      simp [complementTriangle, pairing, neighbors_not_complementary u r s (haway r s)]
    simp [hdiag, complementTriangle, @lt_irrefl _ order.toPreorder u]
  · intro u v
    rw [pulledTriangle_symmetrize]
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_add, triangle_symmetrize order]

/-- A tail row is sent to the sum of its active one-bit neighbors. -/
noncomputable def deviationMatrix (x z : ι → F₂) : Matrix (Word ι) (Word ι) F₂ :=
  fun u v => ∑ r, if v = flip u r then activity x z u r else 0

/-- The Hamming weight modulo two selects the two lattice quotients. -/
def parity (u : Word ι) : F₂ := ∑ r, if u r then 1 else 0

theorem parity_flip (u : Word ι) (r : ι) :
    parity (flip u r) = parity u + 1 := by
  unfold parity
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
  have hrest : ∑ t ∈ Finset.univ.erase r, (if flip u r t then (1 : F₂) else 0) =
      ∑ t ∈ Finset.univ.erase r, (if u t then (1 : F₂) else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [flip, Finset.ne_of_mem_erase ht]
  rw [hrest, add_assoc]
  cases hu : u r <;> simp [flip, hu, CharTwo.add_self_eq_zero]

/-- The same sparse matrix induces both tail maps, from even to odd
coordinates and from odd to even coordinates. -/
theorem deviation_support (x z : ι → F₂) (p : F₂) (a : Word ι → F₂)
    (ha : ∀ u, parity u ≠ p → a u = 0) (v : Word ι) (hv : parity v ≠ p + 1) :
    (a ᵥ* deviationMatrix x z) v = 0 := by
  change (∑ u, a u * deviationMatrix x z u v) = 0
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : parity u = p
  · have hn (r : ι) : v ≠ flip u r := by
      intro h
      exact hv (by rw [h, parity_flip, hu])
    simp [deviationMatrix, hn]
  · simp [ha u hu]

private theorem deviation_mul (x z : ι → F₂) (A : Matrix (Word ι) (Word ι) F₂)
    (u v : Word ι) :
    (deviationMatrix x z * A) u v = ∑ r, activity x z u r * A (flip u r) v := by
  rw [Matrix.mul_apply]
  simp_rw [deviationMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

private theorem pulledTriangle_eq (x z : ι → F₂) :
    pulledTriangle order x z =
      deviationMatrix x z * complementTriangle order * (deviationMatrix x z)ᵀ := by
  ext u v
  rw [Matrix.mul_apply, pulledTriangle]
  simp_rw [deviation_mul, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [Matrix.transpose_apply, deviationMatrix, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  simp [mul_ite, mul_assoc]
  exact Finset.sum_congr rfl fun s _ =>
    congrArg (activity x z u r * ·) (mul_comm _ _)

/-- The lift phase from pairs of complementary tail coordinates. -/
noncomputable def phaseQuadratic (a : Word ι → F₂) : F₂ :=
  (complementTriangle order).toBilin' a a

private theorem phaseQuadratic_deviation [Nonempty ι] (x z : ι → F₂)
    (haway : ∀ r s : ι, ∃ t, t ≠ r ∧ t ≠ s) (a : Word ι → F₂) :
    phaseQuadratic order (a ᵥ* deviationMatrix x z) =
      (∑ r, x r * z r) * phaseQuadratic order a := by
  have h := tail_pullback_quadratic order x z haway a
  rw [pulledTriangle_eq] at h
  unfold phaseQuadratic
  rw [Matrix.toBilin'_apply', Matrix.mulVec_vecMul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
  rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec] at h
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.toBilin'_apply'] using h

/-- The two exceptional first-slot phases cancel at fixed coordinates when the
tail square exponent agrees with the first-slot square exponent. -/
theorem fixed_phase_zero [Nonempty ι] (x z : ι → F₂)
    (haway : ∀ r s : ι, ∃ t, t ≠ r ∧ t ≠ s)
    (xFirst zFirst : Bool) (a b : Word ι → F₂)
    (hsquare : (∑ r, x r * z r) = (if xFirst then 1 else 0) * (if zFirst then 1 else 0))
    (hfixedX : xFirst = true → b ᵥ* deviationMatrix x z = a)
    (hfixedZ : xFirst = false → zFirst = true → a ᵥ* deviationMatrix x z = b) :
    (if xFirst then phaseQuadratic order a else 0) +
      (if zFirst then phaseQuadratic order b else 0) = 0 := by
  cases xFirst
  · cases zFirst
    · simp
    · have h := phaseQuadratic_deviation order x z haway a
      rw [hfixedZ rfl rfl, hsquare] at h
      simpa using h
  · have h := phaseQuadratic_deviation order x z haway b
    rw [hfixedX rfl, hsquare] at h
    cases zFirst <;> simp [h, CharTwo.add_self_eq_zero]

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliPairing
