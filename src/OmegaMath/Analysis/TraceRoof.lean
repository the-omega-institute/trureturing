/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

A positive bilinear pairing and one common upper bound control a crossed
pairing. Every comparison refers to the same six operands. Scalar subtraction
obeys its ordinary ordered additive group laws.
-/

noncomputable section
@[expose] public section
namespace Omega.TraceRoof

private theorem transport {R : Type u} (le : R → R → Prop) {a b c d : R}
    (hac : Eq a c) (hbd : Eq b d) (h : le a b) : le c d :=
  Eq.subst (motive := fun y => le c y) hbd
    (Eq.subst (motive := fun x => le x b) hac h)

/-- A single common roof bounds the crossed pairing below. Diagonal pairing
identities and the four local order comparisons are hypotheses of this
estimate, separate from the primitive order and bilinearity laws. -/
theorem common_roof {M : Type u} {R : Type v}
    (le : M → M → Prop) (positive : M → Prop) (sub : M → M → M)
    (trace : M → R) (pair : M → M → R) (leR : R → R → Prop) (subR : R → R → R)
    (trans : ∀ {a b c}, leR a b → leR b c → leR a c)
    (sub_left : ∀ {a b}, leR a b → ∀ c, leR (subR a c) (subR b c))
    (sub_right : ∀ {a b}, leR a b → ∀ c, leR (subR c b) (subR c a))
    (flip : ∀ {a b c}, leR (subR a b) c → leR (subR a c) b)
    (sub_positive : ∀ {a b}, le a b → positive (sub b a))
    (mono_left : ∀ {a b}, le a b → ∀ c, positive c → leR (pair a c) (pair b c))
    (mono_right : ∀ {a b}, le a b → ∀ c, positive c → leR (pair c a) (pair c b))
    (pair_sub : ∀ a b c, Eq (pair a (sub b c)) (subR (pair a b) (pair a c)))
    (a b c fa fb fc ga gb gc : M) (hfa : positive fa) (hgb : positive gb)
    (hfac : le fa fc) (hfbc : le fb fc) (hgac : le ga gc) (hgbc : le gb gc)
    (ha : Eq (pair fa ga) (trace a)) (hb : Eq (pair fb gb) (trace b))
    (hc : Eq (pair fc gc) (trace c)) :
    leR (subR (trace a) (subR (trace c) (trace b))) (pair fa gb) :=
  have first := sub_left (mono_right hgac fa hfa) (pair fa gb)
  have middle := transport leR (pair_sub fa gc gb) (pair_sub fc gc gb)
    (mono_left hfac (sub gc gb) (sub_positive hgbc))
  have last := sub_right (mono_left hfbc gb hgb) (pair fc gc)
  have chain := trans first (trans middle last)
  have bound := transport leR
    (congrArg (fun x => subR x (pair fa gb)) ha)
    ((congrArg (fun x => subR x (pair fb gb)) hc).trans (congrArg (subR (trace c)) hb)) chain
  flip bound
end Omega.TraceRoof
