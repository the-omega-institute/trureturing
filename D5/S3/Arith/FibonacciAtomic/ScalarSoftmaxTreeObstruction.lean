/- GID: D5/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Scalar bilinear trees with affine softmax heads have uniform three-class risk floors. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ScalarSoftmaxTreeObstruction

open LiteralWindowEnd (Window first last)
open TreeMessageRealization (Full leaves Implementation evaluate)

private abbrev TaskTree := TreeMessageRealization.Tree
open scoped BigOperators

/-- Three initial windows and an arbitrary tail. Positions start at zero. -/
abbrev Word (m : ℕ) := FirstRejectionCutCapacity.Word (m + 2)

/-- The first two rejecting seams receive labels one and two; all later
rejections, terminal failures and acceptance receive label zero. -/
noncomputable def coarse {m : ℕ} (w : Word m) : Fin 3 := by
  classical
  exact if FirstRejectionCutCapacity.task w =
      ((⟨0, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) then 1
    else if FirstRejectionCutCapacity.task w =
      ((⟨1, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) then 2
    else 0

/-- All messages live in the real line. A zero-dimensional message embeds as
the constant zero coordinate. Each merger is separately linear on the whole
ambient real line and has no additional input or affine constant. -/
def scalarImplementation {m : ℕ} (f : Fin (m + 3) → Window → ℝ)
    (B : TaskTree (Fin (m + 3)) → TaskTree (Fin (m + 3)) → ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) :
    Implementation (fun _ : Fin (m + 3) => Window) where
  Message := fun _ => ℝ
  empty := 0
  encode := fun i _ _ => f i
  combine := fun l r => B l r

def logit (u v : Fin 3 → ℝ) (z : ℝ) (y : Fin 3) : ℝ := u y * z + v y

noncomputable def maxima (u v : Fin 3 → ℝ) (z : ℝ) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun y => ∀ j, logit u v z j ≤ logit u v z y)

def LegalChoice (choose : Finset (Fin 3) → Fin 3) : Prop :=
  ∀ S, S.Nonempty → choose S ∈ S

noncomputable def prediction (u v : Fin 3 → ℝ)
    (choose : Finset (Fin 3) → Fin 3) (z : ℝ) : Fin 3 := choose (maxima u v z)

noncomputable def probability (u v : Fin 3 → ℝ) (z : ℝ) (y : Fin 3) : ℝ :=
  Real.exp (logit u v z y) / ∑ j, Real.exp (logit u v z j)

noncomputable def errorRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ)
    (choose : Finset (Fin 3) → Fin 3) : ℝ := by
  classical
  exact 𝔼 w, if prediction u v choose (z w) = coarse w then (0 : ℝ) else 1

noncomputable def squareRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ) : ℝ := by
  classical
  exact 𝔼 w, ∑ y, (probability u v (z w) y - if coarse w = y then 1 else 0) ^ 2

noncomputable def logRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  𝔼 w, -Real.log (probability u v (z w) (coarse w))

end D5.S3.Arith.FibonacciAtomic.ScalarSoftmaxTreeObstruction
