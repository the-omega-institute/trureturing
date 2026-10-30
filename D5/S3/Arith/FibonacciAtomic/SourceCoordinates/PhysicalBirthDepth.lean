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
      · exact ⟨hi, by simpa only [he] using hb, iha _ ha, ihb _ hc⟩
      · exact ⟨hi, by simpa only [he] using hb, iha _ ha, ihb _ hc⟩

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
        exact ⟨by omega, ht, hn, hi, by simpa only [hb] using hz, trivial, trivial, trivial, trivial,
          by omega, by omega, by omega, by omega⟩
      · cases eq
        simp only [hb, ite_true, Bool.not_true, he, le, hrr, lrr, hht, lht]
        exact ⟨by omega, ht, hn, hi, by simpa only [hb] using hz, trivial, trivial, trivial, trivial,
          by omega, by omega, by omega, by omega⟩

open PhysicalTapeDepth (depth probes PaidWalk)

/-- A maximum is stated only through values of the complete fixed-length tape function. -/
def DepthMaximum (T : Source) (L m : Nat) : Prop :=
  (∀ u : Address, u.length = L → depth T u ≤ m) ∧
    ∃ u : Address, u.length = L ∧ depth T u = m

/-- The comparison reads only the two complete depth functions, not descriptors or labels. -/
def Beats (a b : Source) (L : Nat) : Prop :=
  ∃ u : Address, u.length = L ∧
    ∀ v : Address, v.length = L → depth b v < depth a u

/-- Compare the two child restrictions of one complete full-root depth function. -/
def RootBeats (U : Source) (p : Address) (L : Nat) : Prop :=
  ∃ u : Address, u.length = L ∧ ∀ v : Address, v.length = L →
    depth U (p ++ true :: v) < depth U (p ++ false :: u)

private theorem root_comparison (U a b : Source) (p : Address) (L : Nat)
    (offset : ∀ w, depth U (p ++ w) = p.length + depth (.mul a b) w) :
    RootBeats U p L ↔ Beats a b L := by
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    intro v hv
    have bound := h v hv
    rw [offset, offset] at bound
    simpa only [depth, Nat.add_lt_add_iff_left, Nat.add_lt_add_iff_right] using bound
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    intro v hv
    rw [offset, offset]
    simpa only [depth, Nat.add_lt_add_iff_left, Nat.add_lt_add_iff_right] using h v hv

private theorem maximum_of_height (T : Source) (L : Nat) (h : height T ≤ L) :
    DepthMaximum T L (height T) :=
  ⟨fun u _ => (PhysicalTapeDepth.tape_geometry T).2.2.1 u,
    (PhysicalTapeDepth.tape_geometry T).2.2.2.2.1 L h⟩

private theorem beats_iff_height (a b : Source) (L : Nat)
    (ha : height a ≤ L) (hb : height b ≤ L) :
    Beats a b L ↔ height b < height a := by
  obtain ⟨ua, hua, hda⟩ := (maximum_of_height a L ha).2
  obtain ⟨ub, hub, hdb⟩ := (maximum_of_height b L hb).2
  constructor
  · rintro ⟨u, hu, h⟩
    have e := h ub hub
    have bound := (maximum_of_height a L ha).1 u hu
    omega
  · intro h
    refine ⟨ua, hua, ?_⟩
    intro v hv
    have bound := (maximum_of_height b L hb).1 v hv
    omega

private theorem small_rank {q : Nat} (T : Ranked q) :
    (q ≤ 1 ↔ ∃ d c, T.physical = .leaf d c) ∧
    (q = 2 → ∀ (d : Descriptor) (e : Birth) (a b : Physical),
      T.physical = .branch d e a b → a.source = .of (!e.bit) ∧ b.source = .of e.bit) := by
  cases T with
  | alpha d => exact ⟨⟨fun _ => ⟨d, true, rfl⟩, fun _ => by omega⟩, by omega⟩
  | beta d => exact ⟨⟨fun _ => ⟨d, false, rfl⟩, fun _ => by omega⟩, by omega⟩
  | @fork r d e h l =>
      constructor
      · constructor
        · omega
        · rintro ⟨c, b, eq⟩
          cases hb : e.bit <;> simp [Ranked.physical, hb] at eq
      · intro hr c f a b eq
        have er : r = 0 := by omega
        subst r
        cases h with
        | beta hd =>
          cases l with
          | alpha ld =>
            cases hb : e.bit <;>
              simp only [Ranked.physical, hb, Bool.false_eq_true, ite_false, ite_true] at eq
            · cases eq; simp [Physical.source, hb]
            · cases eq; simp [Physical.source, hb]

/-- All depth claims for one reached physical cone; q is its immutable descriptor rank. -/
def ConeLaw (n : Nat) (z : Nat → Bool) (p : Address) (T : Physical) : Prop :=
  let q := rank n T
  T.descriptor.born ≤ n ∧ q + p.length ≤ n ∧ height T.source = q - 1 ∧
  (q ≤ 1 ↔ ∃ d c, T = .leaf d c) ∧
  (∀ u : Address, depth T.source u ≤ q - 1) ∧
  (∀ (L : Nat), q - 1 ≤ L → DepthMaximum T.source L (q - 1)) ∧
  (∀ u : Address, q - 1 ≤ u.length →
    PaidWalk (orbit z n).1.source p u (probes T.source p u) (depth T.source u) ∧
      (probes T.source p u).length = depth T.source u + 1 ∧
      Observer.NativeSerialMachine.Run PhysicalTapeDepth.controller (.walk p u 0) 0 (orbit z n).1.source
        (PhysicalTapeDepth.eventTrace (orbit z n).1.source (probes T.source p u))
        (depth T.source u)) ∧
  (∀ u v : Address, q - 1 ≤ u.length → depth T.source (u ++ v) = depth T.source u) ∧
  (∀ (L : Nat), n - 1 ≤ L → q - 1 ≤ L - p.length) ∧
  (∀ u : Address, depth (orbit z n).1.source (p ++ u) = p.length + depth T.source u) ∧
  (∀ u v : Address, 2 ≤ n → u.length = (2 * n - 1) - p.length →
    v.length = p.length →
    depth (orbit z n).1.source (p ++ u) = p.length + depth T.source u ∧
    p.length + depth T.source u = p.length + depth T.source (u ++ v)) ∧
  (∀ (U : Source) (L : Nat), q - 1 ≤ L → height U ≤ L →
    (∀ u : Address, u.length = L →
      depth (orbit z n).1.source (p ++ u) = p.length + depth U u) →
      (decompose T.source).1 = (decompose U).1) ∧
  (∀ (d : Descriptor) (e : Birth) (a b : Physical), T = .branch d e a b →
    2 ≤ q ∧ e.time = d.born + (if d.initial then 2 else 1) ∧ e.time ≤ n ∧
    0 < e.index ∧ e.bit = z e.index ∧ a.descriptor.born = e.time ∧
    b.descriptor.born = e.time ∧ a.descriptor.initial = !e.bit ∧
    b.descriptor.initial = e.bit ∧
    (if e.bit then rank n a else rank n b) = q - 1 ∧
    (if e.bit then rank n b else rank n a) = q - 2 ∧
    (if e.bit then height a.source else height b.source) = q - 2 ∧
    (if e.bit then height b.source else height a.source) = q - 3 ∧
    (∀ (L : Nat), q - 2 ≤ L →
      DepthMaximum (if e.bit then a.source else b.source) L (q - 2) ∧
      DepthMaximum (if e.bit then b.source else a.source) L (q - 3) ∧
      (3 ≤ q → (e.bit = true ↔ Beats a.source b.source L))) ∧
    (3 ≤ q → q - 2 ≤ (2 * n - 1) - p.length - 1 ∧
      p.length + 1 + ((2 * n - 1) - p.length - 1) = 2 * n - 1 ∧
      (e.bit = true ↔ RootBeats (orbit z n).1.source p ((2 * n - 1) - p.length - 1))) ∧
    (q = 3 → (if e.bit then height a.source else height b.source) = 1 ∧
      (if e.bit then height b.source else height a.source) = 0) ∧
    (q = 2 → a.source = .of (!e.bit) ∧ b.source = .of e.bit ∧
      (∀ u : Address, u ≠ [] → depth T.source u = 1) ∧
      ∀ u : Address, depth T.source u = depth (.mul b.source a.source) u))

private theorem cone_law (n : Nat) (z : Nat → Bool) (p : Address) (T : Physical)
    (found : Physical.at p (orbit z n).1 = some T) : ConeLaw n z p T := by
  have corr := orbit_correspondence z n
  have rootEq : (rankedOrbit z n).1.physical = (orbit z n).1 := congrArg Prod.fst corr.1
  have rootHeight : height (orbit z n).1.source = n - 1 := by
    rw [← rootEq]; exact ranked_height _
  obtain ⟨q, R, eq, stamp, aligned, margin⟩ :=
    reached n z (rankedOrbit z n).1 corr.2 (orbit_aligned z n) p T (by rw [rootEq]; exact found)
  have sr := stamp_rank R stamp
  have qr : rank n T = q := by
    rw [← eq, rank, physical_root]
    exact sr.2.symm
  have ht : height T.source = q - 1 := by rw [← eq]; exact ranked_height R
  have atSource := source_at (orbit z n).1 T p found
  have geo := PhysicalTapeDepth.tape_geometry T.source
  have prefixLaw := geo.2.2.2.2.2.1 (orbit z n).1.source p atSource
  have remaining : ∀ L : Nat, n - 1 ≤ L → q - 1 ≤ L - p.length := by
    intro L hL
    have hp := prefixLaw.1
    rw [ht, rootHeight] at hp
    omega
  have loc : ∀ w, readout (p ++ w) (orbit z n).1.source = readout w T.source := by
    intro w
    have h := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      p w (orbit z n).1.source
    simpa only [atSource] using h
  unfold ConeLaw
  rw [qr]
  refine ⟨?_, margin, ht, ?_, ?_, ?_, ?_, ?_, remaining, prefixLaw.2, ?_, ?_, ?_⟩
  · rw [← eq, physical_root]; exact sr.1
  · simpa only [← eq] using (small_rank R).1
  · intro u; simpa only [ht] using geo.2.2.1 u
  · intro L hL; simpa only [ht] using maximum_of_height T.source L (by omega)
  · intro u hu
    have paid := geo.1 (orbit z n).1.source p u loc (by omega)
    exact ⟨paid.1, geo.2.1 p u, paid.2⟩
  · intro u v hu; exact geo.2.2.2.1 u v (by omega)
  · intro u v hn hu hv
    refine ⟨prefixLaw.2 u, ?_⟩
    have hp := geo.2.2.2.1 u v (by rw [ht, hu]; exact remaining _ (by omega))
    rw [hp]
  · intro U L hL hU same
    apply geo.2.2.2.2.2.2 U L (by omega) hU
    intro u hu
    have e := same u hu
    rw [prefixLaw.2] at e
    exact Nat.add_left_cancel e
  · intro d e a b he
    have bl := branch_law n z R stamp aligned d e a b (eq.trans he)
    rcases bl with ⟨hq, htime, hn, hi, hz, hab, hbb, hai, hbi, har, hbr, hah, hbh⟩
    refine ⟨hq, htime, hn, hi, hz, hab, hbb, hai, hbi, har, hbr, hah, hbh, ?_, ?_, ?_, ?_⟩
    · intro L hL
      have ha : height a.source ≤ L := by cases hb : e.bit <;> simp [hb] at hah hbh <;> omega
      have hb : height b.source ≤ L := by cases hc : e.bit <;> simp [hc] at hah hbh <;> omega
      constructor
      · cases hc : e.bit <;> simp [hc] at hah ⊢ <;>
          simpa only [← hah] using maximum_of_height _ L (by omega)
      constructor
      · cases hc : e.bit <;> simp [hc] at hbh ⊢ <;>
          simpa only [← hbh] using maximum_of_height _ L (by omega)
      · intro hthree
        rw [beats_iff_height a.source b.source L ha hb]
        cases hc : e.bit <;> simp [hc] at hah hbh ⊢ <;> omega
    · intro hthree
      refine ⟨by omega, by omega, ?_⟩
      rw [root_comparison (orbit z n).1.source a.source b.source p _ (by
        intro w
        simpa only [he, Physical.source] using prefixLaw.2 w)]
      have hL : q - 2 ≤ (2 * n - 1) - p.length - 1 := by omega
      have ha : height a.source ≤ (2 * n - 1) - p.length - 1 := by
        cases hc : e.bit <;> simp [hc] at hah hbh <;> omega
      have hb : height b.source ≤ (2 * n - 1) - p.length - 1 := by
        cases hc : e.bit <;> simp [hc] at hah hbh <;> omega
      rw [beats_iff_height _ _ _ ha hb]
      cases hc : e.bit <;> simp [hc] at hah hbh ⊢ <;> omega
    · intro hthree; rw [hthree] at hah hbh; exact ⟨hah, hbh⟩
    · intro htwo
      obtain ⟨ha, hb⟩ := (small_rank R).2 htwo d e a b (eq.trans he)
      refine ⟨ha, hb, ?_, ?_⟩
      · intro u hu
        rw [he]
        cases u with
        | nil => exact False.elim (hu rfl)
        | cons c u => cases c <;> simp [Physical.source, depth, ha, hb]
      · intro u
        rw [he]
        cases u with
        | nil => rfl
        | cons c u => cases c <;> simp [Physical.source, depth, ha, hb]

/-- Every actual reached cone has complete physical depth geometry and recovers
all branch bits of rank at least three, with precisely the depth-only rank-two boundary. -/
theorem observable_orientations (n : Nat) (z : Nat → Bool) :
    (orbit z n).1.descriptor = ⟨0, true⟩ ∧ rank n (orbit z n).1 = n ∧
    ∀ (p : Address) (T : Physical), Physical.at p (orbit z n).1 = some T → ConeLaw n z p T := by
  have rd : (rankedOrbit z n).1.root = ⟨0, true⟩ := by
    induction n with
    | zero => rfl
    | succ n ih => exact (advance_root z (n + 1) _ _).trans ih
  have eq := congrArg Prod.fst (orbit_correspondence z n).1
  have descriptor : (orbit z n).1.descriptor = ⟨0, true⟩ := by
    rw [← eq, physical_root]
    exact rd
  exact ⟨descriptor, by simp [rank, descriptor], cone_law n z⟩

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth
