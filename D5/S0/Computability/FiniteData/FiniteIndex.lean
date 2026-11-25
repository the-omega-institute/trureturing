/- GID: D5/S0/Computability/FiniteData/FiniteIndex
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite ordinals represented by zero and successor constructors indexed by their bound. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core
public import OmegaMathlib.Data.Fin.Fin2

/-!
Omega original.

Finite ordinals represented by zero and successor constructors indexed by their bound.
-/

@[expose] public section

namespace Omega

/-- An index below a given natural-number bound. -/
inductive FiniteIndex : Nat → Type where
  | zero {bound : Nat} : FiniteIndex bound.succ
  | succ {bound : Nat} : FiniteIndex bound → FiniteIndex bound.succ

namespace FiniteIndex

/-- Interpret the recorded zero/successor index as Mathlib's inductive finite ordinal. -/
noncomputable def toFin2 {n : Nat} (i : FiniteIndex n) : OmegaMathlib.Fin2 n :=
  FiniteIndex.rec (motive := fun n _ => OmegaMathlib.Fin2 n)
    (fun {_} => OmegaMathlib.Fin2.fz) (fun {_} _ acc => OmegaMathlib.Fin2.fs acc) i

/-- Read a standard finite ordinal using the original constructors. -/
noncomputable def ofFin2 {n : Nat} (i : OmegaMathlib.Fin2 n) : FiniteIndex n :=
  OmegaMathlib.Fin2.rec (motive := fun n _ => FiniteIndex n)
    (fun {_} => zero) (fun {_} _ acc => succ acc) i

theorem ofFin2_toFin2 {n : Nat} (i : FiniteIndex n) : Eq (ofFin2 (toFin2 i)) i :=
  FiniteIndex.rec (motive := fun _ x => Eq (ofFin2 (toFin2 x)) x)
    (fun {_} => rfl) (fun {_} _ ih => congrArg succ ih) i

theorem toFin2_ofFin2 {n : Nat} (i : OmegaMathlib.Fin2 n) : Eq (toFin2 (ofFin2 i)) i :=
  OmegaMathlib.Fin2.rec (motive := fun _ x => Eq (toFin2 (ofFin2 x)) x)
    (fun {_} => rfl) (fun {_} _ ih => congrArg OmegaMathlib.Fin2.fs ih) i

end FiniteIndex
end Omega
