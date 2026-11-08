/- GID: D5/S3/Topology/BrauerZeroMonoid
   generality: I
   mirror-B: D5/B/S3/Topology/BrauerZeroMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.GroupWithZero.Defs]
   utility: none
   digest: Literal matching concatenation with an absorbing zero for every internal loop. -/
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Topology.FiniteMatchingSewing
import D5.S3.Topology.FiniteMatchingAssociativity
import Mathlib.Algebra.GroupWithZero.Defs

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Topology.BrauerZeroMonoid
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition
open D5.S3.Topology.FiniteMatchingSewing
open D5.S3.Topology.FiniteMatchingAssociativity

attribute [local irreducible] composite internalLoopCount

abbrev ZeroMatching (N : ℕ) := Option (Matching (Boundary N))

private def multiply {N : ℕ} : ZeroMatching N → ZeroMatching N → ZeroMatching N
  | some d, some e => if internalLoopCount d e = 0 then some (composite d e) else none
  | _, _ => none

private theorem multiply_some {N : ℕ} (d e : Matching (Boundary N)) :
    multiply (some d) (some e) =
      if internalLoopCount d e = 0 then some (composite d e) else none := rfl

private theorem multiply_none_left {N : ℕ} (a : ZeroMatching N) : multiply none a = none := rfl

private theorem multiply_none_right {N : ℕ} (a : ZeroMatching N) : multiply a none = none := by
  cases a <;> rfl

attribute [local irreducible] multiply

private theorem multiply_assoc {N : ℕ} (a b c : ZeroMatching N) :
    multiply (multiply a b) c = multiply a (multiply b c) := by
  cases a with
  | none => rw [multiply_none_left, multiply_none_left, multiply_none_left]
  | some d =>
    cases b with
    | none => simp only [multiply_none_right, multiply_none_left]
    | some e =>
      cases c with
      | none => rw [multiply_none_right, multiply_none_right, multiply_none_right]
      | some f =>
        have h := internalLoopCount_cocycle d e f
        rw [multiply_some d e, multiply_some e f]
        by_cases hde : internalLoopCount d e = 0
        · rw [ite_eq_left hde]
          by_cases hef : internalLoopCount e f = 0
          · rw [ite_eq_left hef, multiply_some, multiply_some]
            have hc : internalLoopCount (composite d e) f = internalLoopCount d (composite e f) := by omega
            rw [hc, composite_assoc]
          · rw [ite_eq_right hef, multiply_none_right, multiply_some]
            have hc : internalLoopCount (composite d e) f ≠ 0 := by omega
            rw [ite_eq_right hc]
        · rw [ite_eq_right hde, multiply_none_left]
          by_cases hef : internalLoopCount e f = 0
          · rw [ite_eq_left hef, multiply_some]
            have hc : internalLoopCount d (composite e f) ≠ 0 := by omega
            rw [ite_eq_right hc]
          · rw [ite_eq_right hef, multiply_none_right]

instance zeroMatchingMonoid (N : ℕ) : MonoidWithZero (ZeroMatching N) where
  mul := multiply
  one := some (identityMatching N)
  zero := none
  mul_assoc := multiply_assoc
  one_mul := by
    intro a
    cases a with
    | none => exact multiply_none_right _
    | some d =>
      change multiply (some (identityMatching N)) (some d) = some d
      rw [multiply_some, internalLoopCount_left_identity, ite_eq_left rfl, composite_left_identity]
  mul_one := by
    intro a
    cases a with
    | none => exact multiply_none_left _
    | some d =>
      change multiply (some d) (some (identityMatching N)) = some d
      rw [multiply_some, internalLoopCount_right_identity, ite_eq_left rfl, composite_right_identity]
  zero_mul := multiply_none_left
  mul_zero := multiply_none_right

end D5.S3.Topology.BrauerZeroMonoid
