/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete finite direction depths, paid terminal tests and ordered terminal frontiers. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

/-! Full root literals and the terminal frontier of a complete direction function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth

open GenealogicalFiberTransport (Source decompose)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (height)

/-- A finite tape is totalized by stopping at an exhausted branch. Sufficient
horizons below ensure that this extra case is never used. -/
def depth : Source → Address → Nat
  | .of _, _ => 0
  | .mul _ _, [] => 0
  | .mul a _, false :: u => depth a u + 1
  | .mul _ b, true :: u => depth b u + 1

/-- The trace retains full root literals, including the last child test even
when there are no remaining directions. -/
def probes : Source → Address → Address → List Address
  | .of _, p, _ => [p ++ [false]]
  | .mul _ _, p, [] => [p ++ [false]]
  | .mul a _, p, false :: u => (p ++ [false]) :: probes a (p ++ [false]) u
  | .mul _ b, p, true :: u => (p ++ [false]) :: probes b (p ++ [true]) u

/-- Every continuation submits the current full root literal followed by a.
The stop constructor is justified by absence, not by tape exhaustion. -/
inductive PaidWalk (U : Source) : Address → Address → List Address → Nat → Prop where
  | stop (p u : Address) (absent : readout (p ++ [false]) U = .absent) :
      PaidWalk U p u [p ++ [false]] 0
  | step (p u : Address) (b : Bool) (tr : List Address) (d : Nat)
      (present : readout (p ++ [false]) U ≠ .absent)
      (next : PaidWalk U (p ++ [b]) u tr d) :
      PaidWalk U p (b :: u) ((p ++ [false]) :: tr) (d + 1)

private theorem probe_count (T : Source) (p u : Address) :
    (probes T p u).length = depth T u + 1 := by
  induction T generalizing p u with
  | of b => rfl
  | mul a b iha ihb =>
      cases u with
      | nil => rfl
      | cons c u => cases c <;> simp [probes, depth, iha, ihb]

private theorem paid_walk (T U : Source) (p u : Address)
    (loc : ∀ w, readout (p ++ w) U = readout w T)
    (enough : height T ≤ u.length) :
    PaidWalk U p u (probes T p u) (depth T u) := by
  induction T generalizing p u with
  | of b => exact PaidWalk.stop p u (by simpa [readout] using loc [false])
  | mul a b iha ihb =>
      cases u with
      | nil => change max (height a) (height b) + 1 ≤ 0 at enough; omega
      | cons c u =>
          have ha : height a ≤ u.length := by
            change max (height a) (height b) + 1 ≤ u.length + 1 at enough
            omega
          have hb : height b ≤ u.length := by
            change max (height a) (height b) + 1 ≤ u.length + 1 at enough
            omega
          have present : readout (p ++ [false]) U ≠ .absent := by
            rw [loc]
            cases a with
            | of d => cases d <;> simp [readout]
            | mul l r => simp [readout]
          cases c
          · exact PaidWalk.step p u false _ _ present (iha _ _ (by
              intro w
              simpa only [List.append_assoc, List.singleton_append, readout] using loc (false :: w)) ha)
          · exact PaidWalk.step p u true _ _ present (ihb _ _ (by
              intro w
              simpa only [List.append_assoc, List.singleton_append, readout] using loc (true :: w)) hb)

private theorem depth_bound (T : Source) (u : Address) : depth T u ≤ height T := by
  induction T generalizing u with
  | of b => exact le_rfl
  | mul a b iha ihb =>
      cases u with
      | nil => exact Nat.zero_le _
      | cons c u =>
          cases c
          · exact Nat.add_le_add_right ((iha u).trans (Nat.le_max_left _ _)) 1
          · exact Nat.add_le_add_right ((ihb u).trans (Nat.le_max_right _ _)) 1

private theorem depth_padding (T : Source) (u v : Address)
    (enough : height T ≤ u.length) : depth T (u ++ v) = depth T u := by
  induction T generalizing u with
  | of b => rfl
  | mul a b iha ihb =>
      cases u with
      | nil => change max (height a) (height b) + 1 ≤ 0 at enough; omega
      | cons c u =>
          change max (height a) (height b) + 1 ≤ u.length + 1 at enough
          cases c <;> simp only [List.cons_append, depth]
          · exact congrArg (· + 1) (iha u (by omega))
          · exact congrArg (· + 1) (ihb u (by omega))

private theorem depth_maximum (T : Source) (L : Nat) (enough : height T ≤ L) :
    ∃ u : Address, u.length = L ∧ depth T u = height T := by
  induction T generalizing L with
  | of b => exact ⟨List.replicate L false, by simp, rfl⟩
  | mul a b iha ihb =>
      have h : max (height a) (height b) + 1 ≤ L := enough
      by_cases hab : height a ≤ height b
      · obtain ⟨u, hu, hd⟩ := ihb (L - 1) (by omega)
        refine ⟨true :: u, by simp [hu]; omega, ?_⟩
        change depth b u + 1 = max (height a) (height b) + 1
        rw [hd, max_eq_right hab]
      · obtain ⟨u, hu, hd⟩ := iha (L - 1) (by omega)
        refine ⟨false :: u, by simp [hu]; omega, ?_⟩
        change depth a u + 1 = max (height a) (height b) + 1
        rw [hd, max_eq_left (by omega)]

private theorem depth_prefix (U T : Source) (p u : Address)
    (found : subtree p U = some T) : depth U (p ++ u) = p.length + depth T u := by
  induction p generalizing U with
  | nil => simp only [subtree, Option.some.injEq] at found; subst U; simp
  | cons b p ih =>
      cases U with
      | of c => simp [subtree] at found
      | mul a c =>
          cases b <;> simp only [subtree] at found <;>
            simp only [List.cons_append, depth, ih _ found, List.length_cons] <;> omega

private theorem height_prefix (U T : Source) (p : Address)
    (found : subtree p U = some T) : p.length + height T ≤ height U := by
  induction p generalizing U with
  | nil => simp only [subtree, Option.some.injEq] at found; subst U; simp
  | cons b p ih =>
      cases U with
      | of c => simp [subtree] at found
      | mul a c =>
          cases b <;> simp only [subtree] at found
          · have h := ih a found
            change p.length + 1 + height T ≤ max (height a) (height c) + 1
            omega
          · have h := ih c found
            change p.length + 1 + height T ≤ max (height a) (height c) + 1
            omega

private def blank (T : Source) : Source := FreeMagma.map (fun _ : Bool => true) T

private theorem blank_shape (T : Source) : (decompose (blank T)).1 = (decompose T).1 := by
  induction T with
  | of b => rfl
  | mul a b iha ihb =>
      change BinaryTree.node () (decompose (blank a)).1 (decompose (blank b)).1 = _
      rw [iha, ihb]; rfl

private theorem blank_leaves (T : Source) : leaves (blank T) = leaves T := by
  induction T with
  | of b => rfl
  | mul a b iha ihb =>
      change (leaves (blank a)).map (false :: ·) ++ (leaves (blank b)).map (true :: ·) = _
      rw [iha, ihb]
      rfl

private theorem frontier_from_depth (V U : Source) (L : Nat)
    (hv : height V ≤ L) (hu : height U ≤ L)
    (same : ∀ u : Address, u.length = L → depth V u = depth U u) :
    ∀ p ∈ leaves V, readout p (blank U) = readout p (blank V) := by
  induction V generalizing U L with
  | of b =>
      intro p hp
      have hp' : p = [] := by simpa only [leaves, List.mem_singleton] using hp
      subst p
      cases U with
      | of c => rfl
      | mul a c =>
          have hl : 0 < L := by change max (height a) (height c) + 1 ≤ L at hu; omega
          have e := same (false :: List.replicate (L - 1) false) (by simp; omega)
          simp only [depth] at e
          omega
  | mul a b iha ihb =>
      cases U with
      | of c =>
          have hl : 0 < L := by change max (height a) (height b) + 1 ≤ L at hv; omega
          have e := same (false :: List.replicate (L - 1) false) (by simp; omega)
          simp only [depth] at e
          omega
      | mul c d =>
          have hv' : max (height a) (height b) + 1 ≤ L := hv
          have hu' : max (height c) (height d) + 1 ≤ L := hu
          have sl : ∀ u : Address, u.length = L - 1 → depth a u = depth c u := by
            intro u hlu
            have e := same (false :: u) (by simp [hlu]; omega)
            simpa only [depth, Nat.add_right_cancel_iff] using e
          have sr : ∀ u : Address, u.length = L - 1 → depth b u = depth d u := by
            intro u hlu
            have e := same (true :: u) (by simp [hlu]; omega)
            simpa only [depth, Nat.add_right_cancel_iff] using e
          intro p hp
          simp only [leaves, List.mem_append, List.mem_map] at hp
          rcases hp with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
          · exact iha c (L - 1) (by omega) (by omega) sl p hp
          · exact ihb d (L - 1) (by omega) (by omega) sr p hp

private theorem shape_from_depth (V U : Source) (L : Nat)
    (hv : height V ≤ L) (hu : height U ≤ L)
    (same : ∀ u : Address, u.length = L → depth V u = depth U u) :
    (decompose V).1 = (decompose U).1 := by
  have eq : blank U = blank V := ActualTreeReadoutAcquisition.source_foundation.2.2.1
    (blank V) (blank U) (by
      rw [blank_leaves]
      exact frontier_from_depth V U L hv hu same)
  have hs := congrArg (fun T : Source => (decompose T).1) eq
  simpa only [blank_shape] using hs.symm

/-- Complete tape depths retain the ordered terminal frontier. All tests use
full root literals and include the final absent-child test. -/
theorem tape_geometry (T : Source) :
    (∀ (U : Source) (p u : Address),
      (∀ w, readout (p ++ w) U = readout w T) → height T ≤ u.length →
      PaidWalk U p u (probes T p u) (depth T u)) ∧
    (∀ p u : Address, (probes T p u).length = depth T u + 1) ∧
    (∀ u : Address, depth T u ≤ height T) ∧
    (∀ u v : Address, height T ≤ u.length → depth T (u ++ v) = depth T u) ∧
    (∀ L : Nat, height T ≤ L → ∃ u : Address, u.length = L ∧ depth T u = height T) ∧
    (∀ (U : Source) (p : Address), subtree p U = some T →
      p.length + height T ≤ height U ∧
      ∀ u : Address, depth U (p ++ u) = p.length + depth T u) ∧
    (∀ (U : Source) (L : Nat), height T ≤ L → height U ≤ L →
      (∀ u : Address, u.length = L → depth T u = depth U u) →
      (decompose T).1 = (decompose U).1) :=
  ⟨paid_walk T, probe_count T, depth_bound T, depth_padding T, depth_maximum T,
    fun U p found => ⟨height_prefix U T p found, fun u => depth_prefix U T p u found⟩,
    shape_from_depth T⟩

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
