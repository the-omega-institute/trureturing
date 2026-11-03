/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableData
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableData
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact paired row bounds and finite row type. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

/-! Exact paired row bounds and finite row type. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

structure FixedRow where
  x : ℕ
  p : ℕ
  q : ℕ
  h : ℕ
  v : ℕ
  m : ℕ
  M : ℕ
  before : Bool

def rowBounds (x p q h v m M : ℤ) (before : Bool) : Prop :=
  (∀ r : Fin 3,
    0≤oldEnds x p q h v m M r.castSucc ∧
    oldEnds x p q h v m M r.castSucc≤oldHeads x p q h r.castSucc-1 ∧
    0≤newEnds x p q h v m M before r.castSucc ∧
    newEnds x p q h v m M before r.castSucc≤newHeads x p q h r.castSucc-1) ∧
  1≤v ∧ 2*v≤T x p q ∧ 0≤M ∧ 2*M≤Y x p q h-2


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
