/- GID: D5/S3/Topology/BrauerZeroMonoid
   generality: I
   mirror-B: D5/B/S3/Topology/BrauerZeroMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.GroupWithZero.Defs]
   utility: none
   digest: Literal matching concatenation with an absorbing zero for every internal loop. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PlanarDiagramAlgebra = D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
BrauerZeroMonoid = D5.S3.Topology.BrauerZeroMonoid
zeroMatchingMonoid = D5.S3.Topology.BrauerZeroMonoid.zeroMatchingMonoid

Direct frozen dependencies (declaration statement_ids):
D5/S3/Topology/FiniteMatchingClosure.Boundary
  sha256:2d22740b62cc9ff6a486d404f032436c21abd62130e080eb9e91719ecefa9bc6
D5/S3/Topology/FiniteMatchingClosure.Matching
  sha256:fd9df4ba1fc572f200a8c9ff58f36e53a205ade28d7c790a87120a8723a6cdb9
D5/S3/Topology/FiniteMatchingClosure.identityMatching
  sha256:4e81ed32fda7d78d7b0879b1359e8b4456fd02d02a1bddfc3866467d3101eef3
D5/S3/Topology/FiniteMatchingComposition.composite
  sha256:916faedcd34e169a2fbdf6728df71f94600d26fc1f3c6b285d74c8f06225beff
D5/S3/Topology/FiniteMatchingComposition.internalLoopCount
  sha256:93bdce1ab5e61437907986b6f2bdde47b0b5f569fbacb1d341051b76d3d98b2c
D5/S3/Topology/FiniteMatchingSewing.composite_left_identity
  sha256:07912fb2ac6197baa42796958728686f79195325313b2c6d3682bd8d6c50fcb2
D5/S3/Topology/FiniteMatchingSewing.composite_right_identity
  sha256:643f2f32e49dc01e35c1135e3562a2f176c2b572e06e19e36ee84cee1e927698
D5/S3/Topology/FiniteMatchingSewing.internalLoopCount_left_identity
  sha256:80ce9232074dd54887115f25733c4f875d5e942b05ec0197c57b6a1e17cc8552
D5/S3/Topology/FiniteMatchingSewing.internalLoopCount_right_identity
  sha256:de071019f564dc4808f5c050b1f8c8607ac1f07c80967b80eea3a67d0873c179
ZeroMatching: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.flags,
  BrauerZeroMonoid.multiply
multiply: proof_shape=bind-only; consumers=BrauerZeroMonoid.multiply_assoc,
  BrauerZeroMonoid.multiply_none_left
multiply_some: proof_shape=bind-only; consumers=BrauerZeroMonoid.multiply_assoc,
  BrauerZeroMonoid.some_mul_some
multiply_none_left: proof_shape=bind-only; consumers=BrauerZeroMonoid.multiply_assoc,
  BrauerZeroMonoid.zeroMatchingMonoid
multiply_none_right: proof_shape=bind-only; consumers=BrauerZeroMonoid.multiply_assoc,
  BrauerZeroMonoid.zeroMatchingMonoid
multiply_assoc: proof_shape=bind-only; consumers=BrauerZeroMonoid.zeroMatchingMonoid,
  BrauerZeroMonoid.zeroMatchingMonoid._proof_3
zeroMatchingMonoid: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.flags,
  BrauerZeroMonoid.some_mul_some
some_mul_some: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.flags
-/
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
        have h := internalLoopCount_pos_assoc d e f
        rw [multiply_some d e, multiply_some e f]
        by_cases hde : internalLoopCount d e = 0
        · rw [ite_eq_left hde]
          by_cases hef : internalLoopCount e f = 0
          · rw [ite_eq_left hef, multiply_some, multiply_some]
            have hc : (internalLoopCount (composite d e) f = 0) ↔
                internalLoopCount d (composite e f) = 0 := by omega
            simp only [hc, composite_assoc]
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

/-- The monoid product follows the actual sewn paths, with an internal loop giving zero. -/
theorem some_mul_some {N : ℕ} (d e : Matching (Boundary N)) :
    (some d : ZeroMatching N) * some e =
      if internalLoopCount d e = 0 then some (composite d e) else none := by
  exact multiply_some d e


end D5.S3.Topology.BrauerZeroMonoid
