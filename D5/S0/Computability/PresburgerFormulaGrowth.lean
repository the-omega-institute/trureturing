/- GID: D5/S0/Computability/PresburgerFormulaGrowth
   generality: G
   mirror-B: D5/B/S0/Computability/PresburgerFormulaGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original Presburger QF semantics derive separated-atom Growth at a fixed prefix. -/

import D5.S0.Computability.PresburgerPatternGrowth
import D5.S0.Computability.PresburgerSyntax

set_option autoImplicit false

namespace PresburgerFormulaGrowth

open PresburgerArithmetic PresburgerPatternGrowth

universe u v

/-- Splitting the original truncated dot product preserves short coefficient lists. -/
private theorem dot_append (a xs ys : List Int) :
    Affine.dot a (xs ++ ys) =
      Affine.dot (a.take xs.length) xs + Affine.dot (a.drop xs.length) ys := by
  induction xs generalizing a with
  | nil => simp [Affine.dot]
  | cons x xs ih =>
      cases a with
      | nil => simp [Affine.dot]
      | cons a as => simp [Affine.dot, ih]; ring

/-- Fixed modulus product and threshold count of the original QF syntax. -/
def budget : QF → Nat × Nat
  | .truth | .falsity => (1, 0)
  | .atom (.le _) => (1, 1)
  | .atom (.dvd d _ _) | .atom (.ndvd d _ _) => (d, 0)
  | .not p => budget p
  | .and p q | .or p q => ((budget p).1 * (budget q).1, (budget p).2 + (budget q).2)

/-- Every original QF formula has an actual Growth derivation when a fixed-length
source prefix precedes its descriptor suffix. Constants stay in the suffix part. -/
theorem qf_growth {X : Type u} {Y : Type v} (p : QF) (m : Nat)
    (sourceEnv : X → List Int) (suffixEnv : Y → List Int)
    (length_source : ∀ x, (sourceEnv x).length = m) :
    Growth (fun x y => p.eval (sourceEnv x ++ suffixEnv y))
      (budget p).1 (budget p).2 := by
  have split (a : Affine) (x : X) (y : Y) :
      a.eval (sourceEnv x ++ suffixEnv y) =
        Affine.dot (a.coeffs.take m) (sourceEnv x) +
          (a.constant + Affine.dot (a.coeffs.drop m) (suffixEnv y)) := by
    rw [Affine.eval, dot_append, length_source]
    ring
  induction p with
  | truth => exact Growth.constant true
  | falsity => exact Growth.constant false
  | atom a =>
      cases a with
      | le a =>
          have he : (fun x y => QF.eval (.atom (.le a)) (sourceEnv x ++ suffixEnv y)) =
              (fun x y => decide (-Affine.dot (a.coeffs.take m) (sourceEnv x) ≤
                a.constant + Affine.dot (a.coeffs.drop m) (suffixEnv y))) := by
            funext x y
            simp only [QF.eval, Atom.eval, split]
            congr 1
            apply propext
            omega
          rw [he]
          exact Growth.threshold _ _
      | dvd d hd a =>
          simpa only [QF.eval, Atom.eval, split, budget] using
            (Growth.dvd d hd (fun x => Affine.dot (a.coeffs.take m) (sourceEnv x))
              (fun y => a.constant + Affine.dot (a.coeffs.drop m) (suffixEnv y)))
      | ndvd d hd a =>
          simpa only [QF.eval, Atom.eval, split, budget] using
            (Growth.ndvd d hd (fun x => Affine.dot (a.coeffs.take m) (sourceEnv x))
              (fun y => a.constant + Affine.dot (a.coeffs.drop m) (suffixEnv y)))
  | and p q hp hq => exact Growth.binary Bool.and hp hq
  | or p q hp hq => exact Growth.binary Bool.or hp hq
  | not p hp => exact Growth.unary Bool.not hp

#print axioms dot_append
#print axioms qf_growth

end PresburgerFormulaGrowth
