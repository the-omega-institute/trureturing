/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeAffineImageSaturation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original native image saturation at the exact guarded affine parameter map. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization
import D5.S0.Computability.PresburgerSyntax

/-! Finite symbolic terminals are indexed by affine expressions in the original
finite natural parameter tuple. Their natural ranks are derived from the
explicit nonnegativity guards, without independent terminal parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation

open NativeCompletionPrefixLifting NativeGuardedFreeExtension
open NativeGuardedImageSaturation NativeRootLinkNormalization

/-- A purely syntactic original input. None of its fields asserts a semantic
normalization, extension, rationality or correctness property. -/
structure Input (n k m : Nat) where
  equations : System k m
  filters : List (Filter k m)
  indices : Fin k → PresburgerArithmetic.Affine
  guard : PresburgerArithmetic.Formula

def environment {n : Nat} (p : Fin n → Nat) : List Int :=
  List.ofFn fun i => Int.ofNat (p i)

/-- The original Presburger guard and the explicit guards for all affine
atomic indices, evaluated at the same original parameter tuple. -/
def Legal {n k m : Nat} (I : Input n k m) (p : Fin n → Nat) : Prop :=
  I.guard.holds (environment p) ∧ ∀ j, 0 ≤ (I.indices j).eval (environment p)

def ranks {n k m : Nat} (I : Input n k m) (p : Fin n → Nat) : Fin k → Nat :=
  fun j => ((I.indices j).eval (environment p)).toNat

/-- The source equations use the derived affine ranks, not additional freely
chosen natural parameters. The last token is the explicit Omega terminal. -/
def SourceSatisfies {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop := Satisfies I.equations (ranks I p) v

def SourcePasses {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop := Passes (ranks I p) v I.filters

def SourceInMode {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (mode : FreeMode I.equations (threshold I.filters)) (v : Fin m → CompletionTree) : Prop :=
  OriginalInMode I.equations (ranks I p) mode v

noncomputable def sourceCanonical {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (mode : FreeMode I.equations (threshold I.filters)) : Fin m → CompletionTree :=
  originalCanonical I.equations (ranks I p) I.filters mode

/-- Finite-exception completeness at every fixed legal original parameter.
The affine-to-natural equality makes the complete parameter correspondence
explicit, including negative coefficients under their original guards. -/
theorem affine_original_saturation {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (mode : FreeMode I.equations (threshold I.filters)) :
    (∀ j, (ranks I p j : Int) = (I.indices j).eval (environment p)) ∧
    SourceSatisfies I p (sourceCanonical I p mode) ∧
    SourceInMode I p mode (sourceCanonical I p mode) ∧
    ((∃ v, SourceSatisfies I p v ∧ SourceInMode I p mode v ∧ SourcePasses I p v) ↔
      SourcePasses I p (sourceCanonical I p mode)) := by
  refine ⟨?_, original_saturation I.equations (ranks I p) I.filters mode⟩
  intro j
  exact Int.toNat_of_nonneg (legal.2 j)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
