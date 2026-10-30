/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Physical old-leaf birth dynamics, immutable descriptors and complete direction depths. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth

open GenealogicalFiberTransport (Source decompose)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (height)

/-- The initial label is immutable; true denotes alpha. -/
structure Descriptor where
  born : Nat
  initial : Bool
  deriving DecidableEq

/-- The index starts at one and advances only when an old beta leaf branches. -/
structure Birth where
  time : Nat
  index : Nat
  bit : Bool
  deriving DecidableEq

/-- Physical left and right retain the literal ports a and b. -/
inductive Physical where
  | leaf : Descriptor → Bool → Physical
  | branch : Descriptor → Birth → Physical → Physical → Physical

def Physical.descriptor : Physical → Descriptor
  | .leaf d _ => d
  | .branch d _ _ _ => d

def Physical.source : Physical → Source
  | .leaf _ b => .of b
  | .branch _ _ a b => .mul a.source b.source

/-- Traverse the old tree, a before b. The new children are returned without
recursing into them, and changing alpha into beta consumes no stream bit. -/
def update (z : Nat → Bool) (t : Nat) : Physical → Nat → Physical × Nat
  | .leaf d true, j => (.leaf d false, j)
  | .leaf d false, j =>
      let bit := z (j + 1)
      (.branch d ⟨t, j + 1, bit⟩
        (.leaf ⟨t, !bit⟩ (!bit)) (.leaf ⟨t, bit⟩ bit), j + 1)
  | .branch d e a b, j =>
      let x := update z t a j
      let y := update z t b x.2
      (.branch d e x.1 y.1, y.2)

/-- The actual alpha-origin orbit, with its single global birth counter. -/
def orbit (z : Nat → Bool) : Nat → Physical × Nat
  | 0 => (.leaf ⟨0, true⟩ true, 0)
  | n + 1 => update z (n + 1) (orbit z n).1 (orbit z n).2

private inductive Ranked : Nat → Type where
  | alpha : Descriptor → Ranked 0
  | beta : Descriptor → Ranked 1
  | fork {q : Nat} : Descriptor → Birth → Ranked (q + 1) → Ranked q → Ranked (q + 2)

private def Ranked.root : {q : Nat} → Ranked q → Descriptor
  | _, .alpha d => d
  | _, .beta d => d
  | _, .fork d _ _ _ => d

private def Ranked.physical : {q : Nat} → Ranked q → Physical
  | _, .alpha d => .leaf d true
  | _, .beta d => .leaf d false
  | _, .fork d e h l =>
      if e.bit then .branch d e h.physical l.physical
      else .branch d e l.physical h.physical

private def advance (z : Nat → Bool) (t : Nat) :
    {q : Nat} → Ranked q → Nat → Ranked (q + 1) × Nat
  | _, .alpha d, j => (.beta d, j)
  | _, .beta d, j =>
      (.fork d ⟨t, j + 1, z (j + 1)⟩ (.beta ⟨t, false⟩) (.alpha ⟨t, true⟩), j + 1)
  | _, .fork d e h l, j =>
      if e.bit then
        let x := advance z t h j
        let y := advance z t l x.2
        (.fork d e x.1 y.1, y.2)
      else
        let x := advance z t l j
        let y := advance z t h x.2
        (.fork d e y.1 x.1, y.2)

private theorem advance_physical (z : Nat → Bool) (t : Nat)
    {q : Nat} (T : Ranked q) (j : Nat) :
    ((advance z t T j).1.physical, (advance z t T j).2) = update z t T.physical j := by
  induction T generalizing j with
  | alpha d => rfl
  | beta d =>
      simp only [advance, Ranked.physical, update]
      cases z (j + 1) <;> rfl
  | fork d e h l ihh ihl =>
      cases hb : e.bit <;>
        simp only [advance, Ranked.physical, hb, Bool.false_eq_true, if_false, if_true, update]
      · have hx := ihl j
        have hy := ihh (advance z t l j).2
        cases hx
        cases hy
        rfl
      · have hx := ihh j
        have hy := ihl (advance z t h j).2
        cases hx
        cases hy
        rfl

private theorem advance_root (z : Nat → Bool) (t : Nat)
    {q : Nat} (T : Ranked q) (j : Nat) : (advance z t T j).1.root = T.root := by
  cases T with
  | alpha d => rfl
  | beta d => rfl
  | fork d e h l => cases hb : e.bit <;> simp [advance, hb, Ranked.root]

private def Stamp (n : Nat) : {q : Nat} → Ranked q → Prop
  | _, .alpha d => d.initial = true ∧ n = d.born
  | _, .beta d => (d.initial = true ∧ n = d.born + 1) ∨
      (d.initial = false ∧ n = d.born)
  | _, .fork d e h l =>
      e.time = d.born + (if d.initial then 2 else 1) ∧ e.time ≤ n ∧
      h.root = ⟨e.time, false⟩ ∧ l.root = ⟨e.time, true⟩ ∧ Stamp n h ∧ Stamp n l

private theorem advance_stamp (z : Nat → Bool) (n : Nat)
    {q : Nat} (T : Ranked q) (j : Nat) (s : Stamp n T) :
    Stamp (n + 1) (advance z (n + 1) T j).1 := by
  induction T generalizing j with
  | alpha d => exact Or.inl ⟨s.1, congrArg (· + 1) s.2⟩
  | beta d =>
      change n + 1 = d.born + (if d.initial then 2 else 1) ∧ _
      refine ⟨?_, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl, rfl⟩
      rcases s with ⟨hi, hn⟩ | ⟨hi, hn⟩ <;> simp only [hi, if_true, if_false] <;> omega
  | fork d e h l ihh ihl =>
      rcases s with ⟨he, hn, hh, hl, sh, sl⟩
      cases hb : e.bit <;> simp only [advance, hb, Bool.false_eq_true, if_false, if_true, Stamp]
      · exact ⟨he, by omega, (advance_root z _ h _).trans hh,
          (advance_root z _ l _).trans hl, ihh _ sh, ihl _ sl⟩
      · exact ⟨he, by omega, (advance_root z _ h _).trans hh,
          (advance_root z _ l _).trans hl, ihh _ sh, ihl _ sl⟩

private theorem stamp_rank {n q : Nat} (T : Ranked q) (s : Stamp n T) :
    T.root.born ≤ n ∧ q = n - T.root.born + (if T.root.initial then 0 else 1) := by
  induction T with
  | alpha d => simp only [Stamp] at s; simp [Ranked.root, s.1, s.2]
  | beta d =>
      rcases s with ⟨hi, hn⟩ | ⟨hi, hn⟩ <;> simp [Ranked.root, hi, hn]
  | @fork r d e h l ihh ihl =>
      rcases s with ⟨he, hn, hh, hl, sh, sl⟩
      have rh := ihh sh
      rw [hh] at rh
      simp only [Ranked.root]
      cases hi : d.initial <;> simp only [hi, if_true, if_false] at he ⊢ <;> omega

private def rankedOrbit (z : Nat → Bool) : (n : Nat) → Ranked n × Nat
  | 0 => (.alpha ⟨0, true⟩, 0)
  | n + 1 => advance z (n + 1) (rankedOrbit z n).1 (rankedOrbit z n).2

private theorem orbit_correspondence (z : Nat → Bool) (n : Nat) :
    ((rankedOrbit z n).1.physical, (rankedOrbit z n).2) = orbit z n ∧
      Stamp n (rankedOrbit z n).1 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      constructor
      · change ((advance z (n + 1) (rankedOrbit z n).1 _).1.physical, _) = _
        rw [advance_physical]
        simpa only [orbit, ← ih.1]
      · exact advance_stamp z n _ _ ih.2

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth
