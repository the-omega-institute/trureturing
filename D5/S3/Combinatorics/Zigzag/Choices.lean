/- GID: D5/S3/Combinatorics/Zigzag/Choices
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/Choices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic,
     mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Literal labelled zigzag choices and their balance-only cardinality. -/

/- The six endpoint formulas are transcribed directly from Section 5, equation (2), of
   Feldman, "The Missing Zigzag", arXiv:2609.26114v1.  They were compared with
   `formPair` at DavidVFeldman/missing-zigzag-new, commit 5da74e8b5a1b19ff.
   This file is a fresh definition from the published formula; it imports no
   code or certificates from that Lean 4.28 development. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

open scoped BigOperators

/-- The labels I--VI.  The finite index is part of the object, so labels remain
distinct even when two endpoint pairs coincide in a small modulus. -/
abbrev Form := Fin 6

namespace Form

def I : Form := 0
def II : Form := 1
def III : Form := 2
def IV : Form := 3
def V : Form := 4
def VI : Form := 5

end Form

/-- The labelled directed edge of class `k` in `ZMod n`. -/
def formPair (n k : Nat) (f : Form) : ZMod n × ZMod n :=
  [((1 : ZMod n), (k : ZMod n) - 1),
    ((k : ZMod n), 1 - (k : ZMod n)),
    (-1, (k : ZMod n)),
    ((k : ZMod n) - 1, -(k : ZMod n)),
    (-(k : ZMod n), 1),
    (1 - (k : ZMod n), -1)].get f

/-- The four labels which are zigzag choices at class two. -/
def Form.allowedAtTwo (f : Form) : Prop :=
  f = II ∨ f = III ∨ f = IV ∨ f = V

instance (f : Form) : Decidable f.allowedAtTwo := by
  simp only [Form.allowedAtTwo]
  infer_instance

/-- A labelled choice for every class `k = 2, ..., 3*t-2`, with exactly the
source restriction at class two. -/
def Choices (t : Nat) :=
  {choose : Fin (3 * t - 3) -> Form //
    forall i, i.val = 0 -> (choose i).allowedAtTwo}

noncomputable instance (t : Nat) : Fintype (Choices t) := by
  classical
  unfold Choices
  infer_instance

/-- The actual class represented by a choice-function index. -/
def classIndex {t : Nat} (i : Fin (3 * t - 3)) : Nat := i.val + 2

/-- The class paired with low class `j` under inversion. -/
def highClass (n j : Nat) : Nat := n + 1 - j

/-- Integer out-degree minus in-degree at one residue. -/
def imbalance {t : Nat} (c : Choices t) (v : ZMod (3 * t)) : Int :=
  ∑ i,
    let e := formPair (3 * t) (classIndex i) (c.1 i)
    (if e.1 = v then 1 else 0) - (if e.2 = v then 1 else 0)

/-- Feldman's balance-only predicate: every nonzero node has equal integer
out-degree and in-degree.  No closure or connectivity condition occurs. -/
def Balanced {t : Nat} (c : Choices t) : Prop :=
  forall v : ZMod (3 * t), v ≠ 0 -> imbalance c v = 0

noncomputable instance {t : Nat} (c : Choices t) : Decidable (Balanced c) :=
  Classical.propDecidable _

/-- The literal balanced labelled-choice cardinality in Conjecture 9.3. -/
noncomputable def balancedCount (t : Nat) : Nat :=
  by
    classical
    exact ((Finset.univ : Finset (Choices t)).filter fun c => Balanced c).card

end D5.S3.Combinatorics.Zigzag
