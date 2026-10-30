/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Physical old-leaf birth dynamics, immutable descriptors and complete direction depths. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth

/-! The stream is consumed only by lexicographically ordered old beta leaves. -/

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
        simp only [advance, Ranked.physical, hb, Bool.false_eq_true, ite_false, ite_true, update]
      · rw [← ihl j, ← ihh (advance z t l j).2]
      · rw [← ihh j, ← ihl (advance z t h j).2]

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
      rcases s with ⟨hi, hn⟩ | ⟨hi, hn⟩ <;> simp [hi, hn, Nat.add_assoc]
  | fork d e h l ihh ihl =>
      rcases s with ⟨he, hn, hh, hl, sh, sl⟩
      cases hb : e.bit <;> simp only [advance, hb, Bool.false_eq_true, ite_false, ite_true, Stamp]
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
      dsimp at rh
      simp only [Ranked.root]
      by_cases hi : d.initial = true
      · simp [hi] at he ⊢; omega
      · simp [hi] at he ⊢; omega

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
      · change ((advance z (n + 1) (rankedOrbit z n).1 (rankedOrbit z n).2).1.physical,
          (advance z (n + 1) (rankedOrbit z n).1 (rankedOrbit z n).2).2) =
          update z (n + 1) (orbit z n).1 (orbit z n).2
        rw [advance_physical, ← ih.1]
      · exact advance_stamp z n _ _ ih.2

/-- Literal lookup in the physical tree retains the immutable node metadata. -/
def Physical.at : Address → Physical → Option Physical
  | [], T => some T
  | _ :: _, .leaf _ _ => none
  | false :: p, .branch _ _ a _ => Physical.at p a
  | true :: p, .branch _ _ _ b => Physical.at p b

/-- The descriptor coordinate is mathematical metadata, not an observer field. -/
def rank (n : Nat) (T : Physical) : Nat :=
  n - T.descriptor.born + (if T.descriptor.initial then 0 else 1)

private theorem physical_root {q : Nat} (T : Ranked q) :
    T.physical.descriptor = T.root := by
  cases T with
  | alpha d => rfl
  | beta d => rfl
  | fork d e h l => cases hb : e.bit <;> simp [Ranked.physical, hb, Physical.descriptor, Ranked.root]

private theorem ranked_height {q : Nat} (T : Ranked q) :
    height T.physical.source = q - 1 := by
  induction T with
  | alpha d => rfl
  | beta d => rfl
  | @fork r d e h l ihh ihl =>
      cases hb : e.bit <;>
        simp only [Ranked.physical, hb, Bool.false_eq_true, ite_false, ite_true, Physical.source]
      · change max (height l.physical.source) (height h.physical.source) + 1 = r + 2 - 1
        rw [ihh, ihl]
        omega
      · change max (height h.physical.source) (height l.physical.source) + 1 = r + 2 - 1
        rw [ihh, ihl]
        omega

private def Aligned (z : Nat → Bool) : {q : Nat} → Ranked q → Prop
  | _, .alpha _ => True
  | _, .beta _ => True
  | _, .fork _ e h l => 0 < e.index ∧ e.bit = z e.index ∧ Aligned z h ∧ Aligned z l

private theorem advance_aligned (z : Nat → Bool) (t : Nat)
    {q : Nat} (T : Ranked q) (j : Nat) (h : Aligned z T) :
    Aligned z (advance z t T j).1 := by
  induction T generalizing j with
  | alpha d => trivial
  | beta d => exact ⟨Nat.zero_lt_succ _, rfl, trivial, trivial⟩
  | fork d e a b iha ihb =>
      rcases h with ⟨hi, hb, ha, hc⟩
      cases he : e.bit <;> simp only [advance, he, Bool.false_eq_true, ite_false, ite_true, Aligned]
      · exact ⟨hi, hb, iha _ ha, ihb _ hc⟩
      · exact ⟨hi, hb, iha _ ha, ihb _ hc⟩

private theorem orbit_aligned (z : Nat → Bool) (n : Nat) : Aligned z (rankedOrbit z n).1 := by
  induction n with
  | zero => trivial
  | succ n ih => exact advance_aligned z (n + 1) _ _ ih

private theorem reached (n : Nat) (z : Nat → Bool) {q : Nat} (T : Ranked q)
    (s : Stamp n T) (a : Aligned z T) (p : Address) (U : Physical)
    (found : Physical.at p T.physical = some U) :
    ∃ (r : Nat) (R : Ranked r), R.physical = U ∧ Stamp n R ∧ Aligned z R ∧ r + p.length ≤ q := by
  induction p generalizing q T U with
  | nil =>
      have eq : T.physical = U := Option.some.inj found
      exact ⟨q, T, eq, s, a, by simp⟩
  | cons b p ih =>
      cases T with
      | alpha d => simp [Ranked.physical, Physical.at] at found
      | beta d => simp [Ranked.physical, Physical.at] at found
      | @fork r d e h l =>
          rcases s with ⟨_, _, _, _, sh, sl⟩
          rcases a with ⟨_, _, ah, al⟩
          cases he : e.bit <;> cases b <;>
            simp only [Ranked.physical, he, Bool.false_eq_true, ite_false, ite_true,
              Physical.at] at found
          · obtain ⟨j, R, hR, sR, aR, hj⟩ := ih l sl al U found
            exact ⟨j, R, hR, sR, aR, by simp only [List.length_cons]; omega⟩
          · obtain ⟨j, R, hR, sR, aR, hj⟩ := ih h sh ah U found
            exact ⟨j, R, hR, sR, aR, by simp only [List.length_cons]; omega⟩
          · obtain ⟨j, R, hR, sR, aR, hj⟩ := ih h sh ah U found
            exact ⟨j, R, hR, sR, aR, by simp only [List.length_cons]; omega⟩
          · obtain ⟨j, R, hR, sR, aR, hj⟩ := ih l sl al U found
            exact ⟨j, R, hR, sR, aR, by simp only [List.length_cons]; omega⟩

private theorem source_at (U T : Physical) (p : Address)
    (found : Physical.at p U = some T) : subtree p U.source = some T.source := by
  induction p generalizing U with
  | nil => have e := Option.some.inj found; subst T; rfl
  | cons b p ih =>
      cases U with
      | leaf d c => simp [Physical.at] at found
      | branch d e a c => cases b <;> exact ih _ found

private theorem branch_law (n : Nat) (z : Nat → Bool) {q : Nat} (T : Ranked q)
    (s : Stamp n T) (aligned : Aligned z T) (d : Descriptor) (e : Birth) (a b : Physical)
    (eq : T.physical = .branch d e a b) :
    2 ≤ q ∧ e.time = d.born + (if d.initial then 2 else 1) ∧ e.time ≤ n ∧
      0 < e.index ∧ e.bit = z e.index ∧ a.descriptor.born = e.time ∧
      b.descriptor.born = e.time ∧ a.descriptor.initial = !e.bit ∧
      b.descriptor.initial = e.bit ∧
      (if e.bit then rank n a else rank n b) = q - 1 ∧
      (if e.bit then rank n b else rank n a) = q - 2 ∧
      (if e.bit then height a.source else height b.source) = q - 2 ∧
      (if e.bit then height b.source else height a.source) = q - 3 := by
  cases T with
  | alpha c => cases eq
  | beta c => cases eq
  | @fork r c f h l =>
      rcases s with ⟨ht, hn, hh, hl, sh, sl⟩
      rcases aligned with ⟨hi, hz, ah, al⟩
      have hr := (stamp_rank h sh).2
      have lr := (stamp_rank l sl).2
      have hd := physical_root h
      have ld := physical_root l
      have hht := ranked_height h
      have lht := ranked_height l
      have he : h.physical.descriptor = ⟨f.time, false⟩ := hd.trans hh
      have le : l.physical.descriptor = ⟨f.time, true⟩ := ld.trans hl
      have hrr : rank n h.physical = r + 1 := by simpa only [rank, hd] using hr.symm
      have lrr : rank n l.physical = r := by simpa only [rank, ld] using lr.symm
      cases hb : f.bit <;>
        simp only [Ranked.physical, hb, Bool.false_eq_true, ite_false, ite_true] at eq
      · cases eq
        simp only [hb, Bool.false_eq_true, ite_false, Bool.not_false, he, le,
          hrr, lrr, hht, lht]
        exact ⟨by omega, ht, hn, hi, hz, rfl, rfl, rfl, rfl,
          by omega, by omega, by omega, by omega⟩
      · cases eq
        simp only [hb, ite_true, Bool.not_true, he, le, hrr, lrr, hht, lht]
        exact ⟨by omega, ht, hn, hi, hz, rfl, rfl, rfl, rfl,
          by omega, by omega, by omega, by omega⟩

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth
