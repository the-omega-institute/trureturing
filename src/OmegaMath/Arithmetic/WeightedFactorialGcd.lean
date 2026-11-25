module
prelude
public import OmegaMath.Arithmetic.SimultaneousFloor

/-! Omega original.

Nonnegative weighted finite profiles. Saturating the unweighted lower bound
gives one common minimizer for every natural weight vector. Complementary
weights partition the same profile exactly.
-/

@[expose] public section

namespace Omega.Arithmetic.WeightedFactorialGcd

open Omega
open SimultaneousFloor

def weightedTotal (n : Nat) (c f : Nat → Nat) : Nat :=
  sumBelow n (fun i => (c i).mul (f i))

/-- A single unweighted saturation certificate works for all natural weights. -/
theorem saturation_weighted (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, Nat.lt i n → Nat.le (f i) (g i))
    (hs : Eq (sumBelow n f) (sumBelow n g)) (c : Nat → Nat) :
    Eq (weightedTotal n c f) (weightedTotal n c g) :=
  sumBelow_congr n _ _
    (fun i hi => congrArg (Nat.mul (c i)) (saturation n f g h hs i hi))

private theorem sumBelow_add (n : Nat) (f g : Nat → Nat) :
    Eq (sumBelow n (fun i => (f i).add (g i)))
      ((sumBelow n f).add (sumBelow n g)) :=
  Nat.rec (motive := fun n =>
      Eq (sumBelow n (fun i => (f i).add (g i)))
        ((sumBelow n f).add (sumBelow n g))) rfl
    (fun i ih => (congrArg (fun x => x.add ((f i).add (g i))) ih).trans
      ((Nat.add_assoc _ _ _).trans
        ((congrArg (Nat.add (sumBelow i f))
          ((Nat.add_assoc _ _ _).symm.trans
            ((congrArg (fun x => x.add (g i)) (Nat.add_comm (sumBelow i g) (f i))).trans
              (Nat.add_assoc _ _ _)))).trans (Nat.add_assoc _ _ _).symm))) n

/-- The two weights split the same finite profile, including zero coefficients. -/
theorem weightedTotal_partition (n : Nat) (c d f : Nat → Nat) :
    Eq (weightedTotal n (fun i => (c i).add (d i)) f)
      ((weightedTotal n c f).add (weightedTotal n d f)) :=
  (sumBelow_congr n _ _ (fun i _ => Nat.add_mul (c i) (d i) (f i))).trans
    (sumBelow_add n (fun i => (c i).mul (f i)) (fun i => (d i).mul (f i)))

end Omega.Arithmetic.WeightedFactorialGcd
