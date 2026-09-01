/- GID: D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/StepTwoChronologicalLogarithm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Step-two chronological logarithms identify Chen multiplication with the truncated BCH group and its antipode. -/

import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.Tactic

/-!
# Step-two chronological logarithm

This module upgrades the scalar doubled Magnus coordinate to a complete
step-two logarithmic coordinate. Its multiplication is the division-free
second-order Baker-Campbell-Hausdorff operation

`(x, X) BCH (y, Y) = (x + y, X + Y + [x,y])`.

The chronological logarithm subtracts the square of degree one from doubled
degree two. Its inverse exponential adds that square back. The two coordinate
maps are mutually inverse and multiplicative, so Chen composition and the
truncated BCH product are explicitly equivalent.

The same formulas give an antipode on step-two signatures. In logarithmic
coordinates it is ordinary negation, while in signature coordinates it is
`(x,D) ↦ (-x,-D+2*x*x)`.

This file proves finite algebraic identities over a possibly noncommutative
ring. It does not construct a completed tensor Hopf algebra, an infinite
signature, a convergent Magnus series, a rough path, or a physical arrow of
time.
-/

/- Library-search audit trail (2026-09-01):
   * `StepTwoChronologicalSignature` owns Chen composition and the scalar
     doubled degree-two BCH identity. Those owners are reused below.
   * `ProjectionCommutatorIdentity` owns the repository commutator convention
     `[x,y] = x*y-y*x`, inherited through the imported signature module.
   * Repository search found no existing owner of this full two-coordinate BCH
     monoid, the mutually inverse logarithm and exponential, or their
     multiplicative equivalence with chronological signatures.
   * Pinned Mathlib supplies `Equiv`, `MulEquiv`, and `noncomm_ring`. The
     doubled convention requires no division by two or characteristic
     assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature

universe u

/-- Degree one together with the doubled degree-two Lie coordinate. -/
@[ext]
structure StepTwoLogarithm (A : Type u) where
  degreeOne : A
  doubledLieDegreeTwo : A

namespace StepTwoLogarithm

variable {A : Type u}

/-- The division-free degree-two Baker-Campbell-Hausdorff product. -/
def bch [Ring A]
    (left right : StepTwoLogarithm A) : StepTwoLogarithm A where
  degreeOne := left.degreeOne + right.degreeOne
  doubledLieDegreeTwo :=
    left.doubledLieDegreeTwo + right.doubledLieDegreeTwo +
      commutator left.degreeOne right.degreeOne

/-- The zero logarithmic coordinate. -/
def identity [Zero A] : StepTwoLogarithm A where
  degreeOne := 0
  doubledLieDegreeTwo := 0

/-- The truncated BCH law is associative and unital over every ring. -/
instance [Ring A] : Monoid (StepTwoLogarithm A) where
  one := identity
  mul := bch
  one_mul coordinate := by
    rcases coordinate with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, bch, commutator]
  mul_one coordinate := by
    rcases coordinate with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, bch, commutator]
  mul_assoc left middle right := by
    rcases left with ⟨x, X⟩
    rcases middle with ⟨y, Y⟩
    rcases right with ⟨z, Z⟩
    ext <;> simp [bch, commutator] <;> noncomm_ring

@[simp]
theorem degreeOne_one [Ring A] :
    (1 : StepTwoLogarithm A).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledLieDegreeTwo_one [Ring A] :
    (1 : StepTwoLogarithm A).doubledLieDegreeTwo = 0 := by
  rfl

@[simp]
theorem degreeOne_mul [Ring A]
    (left right : StepTwoLogarithm A) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledLieDegreeTwo_mul [Ring A]
    (left right : StepTwoLogarithm A) :
    (left * right).doubledLieDegreeTwo =
      left.doubledLieDegreeTwo + right.doubledLieDegreeTwo +
        commutator left.degreeOne right.degreeOne := by
  rfl

/-- Explicit inverse for the degree-two BCH product. -/
def inverse [Ring A]
    (coordinate : StepTwoLogarithm A) : StepTwoLogarithm A where
  degreeOne := -coordinate.degreeOne
  doubledLieDegreeTwo := -coordinate.doubledLieDegreeTwo

/-- The explicit BCH inverse cancels on the left. -/
theorem inverse_bch [Ring A] (coordinate : StepTwoLogarithm A) :
    inverse coordinate * coordinate = 1 := by
  rcases coordinate with ⟨x, X⟩
  ext <;> simp [inverse, bch, identity, commutator] <;> noncomm_ring

/-- The explicit BCH inverse cancels on the right. -/
theorem bch_inverse [Ring A] (coordinate : StepTwoLogarithm A) :
    coordinate * inverse coordinate = 1 := by
  rcases coordinate with ⟨x, X⟩
  ext <;> simp [inverse, bch, identity, commutator] <;> noncomm_ring

/-- BCH inversion is involutive. -/
theorem inverse_involutive [Ring A] (coordinate : StepTwoLogarithm A) :
    inverse (inverse coordinate) = coordinate := by
  rcases coordinate with ⟨x, X⟩
  ext <;> simp [inverse]

/-- BCH inversion reverses multiplication order. -/
theorem inverse_mul_rev [Ring A]
    (left right : StepTwoLogarithm A) :
    inverse (left * right) = inverse right * inverse left := by
  rcases left with ⟨x, X⟩
  rcases right with ⟨y, Y⟩
  ext <;> simp [inverse, bch, commutator] <;> noncomm_ring

end StepTwoLogarithm

/-- The complete step-two chronological logarithm. -/
def chronologicalLog {A : Type u} [Ring A]
    (signature : StepTwoSignature A) : StepTwoLogarithm A where
  degreeOne := signature.degreeOne
  doubledLieDegreeTwo := doubledMagnusDegreeTwo signature

/-- The division-free step-two exponential. -/
def chronologicalExp {A : Type u} [Ring A]
    (coordinate : StepTwoLogarithm A) : StepTwoSignature A where
  degreeOne := coordinate.degreeOne
  doubledDegreeTwo :=
    coordinate.doubledLieDegreeTwo +
      coordinate.degreeOne * coordinate.degreeOne

/-- Exponentiating the chronological logarithm recovers the signature. -/
theorem chronological_exp_log {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    chronologicalExp (chronologicalLog signature) = signature := by
  rcases signature with ⟨x, X⟩
  ext <;>
    simp [chronologicalExp, chronologicalLog, doubledMagnusDegreeTwo] <;>
    noncomm_ring

/-- Taking the logarithm of the step-two exponential recovers the coordinate. -/
theorem chronological_log_exp {A : Type u} [Ring A]
    (coordinate : StepTwoLogarithm A) :
    chronologicalLog (chronologicalExp coordinate) = coordinate := by
  rcases coordinate with ⟨x, X⟩
  ext <;>
    simp [chronologicalExp, chronologicalLog, doubledMagnusDegreeTwo] <;>
    noncomm_ring

/-- The complete logarithm converts chronological composition into the
truncated BCH product. -/
theorem chronological_log_mul {A : Type u} [Ring A]
    (left right : StepTwoSignature A) :
    chronologicalLog (left * right) =
      chronologicalLog left * chronologicalLog right := by
  apply StepTwoLogarithm.ext
  · rfl
  · change
      doubledMagnusDegreeTwo (left * right) =
        doubledMagnusDegreeTwo left + doubledMagnusDegreeTwo right +
          commutator left.degreeOne right.degreeOne
    exact doubled_magnus_degree_two_mul left right

/-- The logarithm sends the empty signature to the zero coordinate. -/
@[simp]
theorem chronological_log_one {A : Type u} [Ring A] :
    chronologicalLog (1 : StepTwoSignature A) = 1 := by
  ext <;>
    simp [chronologicalLog, doubledMagnusDegreeTwo,
      StepTwoLogarithm.identity]

/-- The exponential converts the BCH product back to chronological
composition. -/
theorem chronological_exp_mul {A : Type u} [Ring A]
    (left right : StepTwoLogarithm A) :
    chronologicalExp (left * right) =
      chronologicalExp left * chronologicalExp right := by
  rcases left with ⟨x, X⟩
  rcases right with ⟨y, Y⟩
  ext <;>
    simp [chronologicalExp, StepTwoLogarithm.bch,
      StepTwoSignature.compose, commutator] <;>
    noncomm_ring

/-- Logarithm and exponential form an equivalence of coordinate spaces. -/
def chronologicalLogEquiv {A : Type u} [Ring A] :
    StepTwoSignature A ≃ StepTwoLogarithm A where
  toFun := chronologicalLog
  invFun := chronologicalExp
  left_inv := chronological_exp_log
  right_inv := chronological_log_exp

/-- The coordinate equivalence is multiplicative. This is the exact
step-two identification of Chen composition with the BCH law. -/
def chronologicalLogMulEquiv {A : Type u} [Ring A] :
    StepTwoSignature A ≃* StepTwoLogarithm A where
  toEquiv := chronologicalLogEquiv
  map_mul' := chronological_log_mul

/-- Explicit antipode transported to chronological signature coordinates. -/
def signatureAntipode {A : Type u} [Ring A]
    (signature : StepTwoSignature A) : StepTwoSignature A where
  degreeOne := -signature.degreeOne
  doubledDegreeTwo :=
    -signature.doubledDegreeTwo +
      2 * (signature.degreeOne * signature.degreeOne)

/-- The signature antipode cancels chronological composition on the left. -/
theorem signature_antipode_mul {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    signatureAntipode signature * signature = 1 := by
  rcases signature with ⟨x, X⟩
  ext <;>
    simp [signatureAntipode, StepTwoSignature.compose,
      StepTwoSignature.identity] <;>
    noncomm_ring

/-- The signature antipode cancels chronological composition on the right. -/
theorem mul_signature_antipode {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    signature * signatureAntipode signature = 1 := by
  rcases signature with ⟨x, X⟩
  ext <;>
    simp [signatureAntipode, StepTwoSignature.compose,
      StepTwoSignature.identity] <;>
    noncomm_ring

/-- The logarithm turns the signature antipode into coordinatewise negation. -/
theorem chronological_log_antipode {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    chronologicalLog (signatureAntipode signature) =
      StepTwoLogarithm.inverse (chronologicalLog signature) := by
  rcases signature with ⟨x, X⟩
  ext <;>
    simp [chronologicalLog, signatureAntipode,
      StepTwoLogarithm.inverse, doubledMagnusDegreeTwo] <;>
    noncomm_ring

/-- The signature antipode is involutive. -/
theorem signature_antipode_involutive {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    signatureAntipode (signatureAntipode signature) = signature := by
  rcases signature with ⟨x, X⟩
  ext <;> simp [signatureAntipode] <;> noncomm_ring

/-- The signature antipode reverses chronological multiplication. -/
theorem signature_antipode_mul_rev {A : Type u} [Ring A]
    (left right : StepTwoSignature A) :
    signatureAntipode (left * right) =
      signatureAntipode right * signatureAntipode left := by
  rcases left with ⟨x, X⟩
  rcases right with ⟨y, Y⟩
  ext <;>
    simp [signatureAntipode, StepTwoSignature.compose] <;>
    noncomm_ring

/-- The antipode of a one-event signature is the signature of the negated
event value. -/
theorem signature_antipode_event {A : Type u} [Ring A] (value : A) :
    signatureAntipode (eventSignature value) =
      eventSignature (-value) := by
  ext <;> simp [signatureAntipode, eventSignature] <;> noncomm_ring

example : StepTwoLogarithm ℤ := ⟨0, 0⟩

#print axioms StepTwoLogarithm.inverse_bch
#print axioms StepTwoLogarithm.bch_inverse
#print axioms StepTwoLogarithm.inverse_mul_rev
#print axioms chronological_exp_log
#print axioms chronological_log_exp
#print axioms chronological_log_mul
#print axioms chronological_exp_mul
#print axioms chronologicalLogMulEquiv
#print axioms signature_antipode_mul
#print axioms mul_signature_antipode
#print axioms chronological_log_antipode
#print axioms signature_antipode_involutive
#print axioms signature_antipode_mul_rev
#print axioms signature_antipode_event

end D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm
