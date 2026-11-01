/- GID: D5/S1/Dynamics/FinitePhaseCoboundary
   generality: G
   mirror-B: D5/B/S1/Dynamics/FinitePhaseCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identity return transport on a finite phase tower gives a continuous coboundary. -/

import D5.S1.Dynamics.PeriodicOrbits.SkewGroupHolonomy
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.LocallyConstant.Basic

/-! # Continuous coboundaries on finite phase towers -/

set_option autoImplicit false

namespace D5.S1.Dynamics.FinitePhaseCoboundary

open Function
open D5.S1.Dynamics.PeriodicOrbits.SkewGroupHolonomy

variable {X G : Type*} [Group G]

/-- Transport with the current cocycle multiplied on the left. The existing
right-ordered holonomy is reused in the opposite group. -/
def leftHolonomy (T : X → X) (c : X → G) (n : ℕ) (x : X) : G :=
  MulOpposite.unop (groupHolonomy T (fun y => MulOpposite.op (c y)) n x)

private theorem leftHolonomy_succ (T : X → X) (c : X → G) (n : ℕ) (x : X) :
    leftHolonomy T c (n + 1) x = c (T^[n] x) * leftHolonomy T c n x := by
  simp [leftHolonomy, groupHolonomy]

variable [AddAction ℤ X]

private theorem iterate_unit_vadd (n : ℕ) (x : X) :
    (fun y : X => (1 : ℤ) +ᵥ y)^[n] x = (n : ℤ) +ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← add_vadd]
    congr 1
    omega

private def phaseTransfer {h : ℕ} (p : X → ZMod h) (c : X → G) (x : X) : G :=
  leftHolonomy (fun y => (1 : ℤ) +ᵥ y) c (p x).val
    ((-((p x).val : ℤ)) +ᵥ x)

variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_leftHolonomy
    (hact : ∀ g : ℤ, Continuous (fun x : X => g +ᵥ x))
    (c : X → G) (hc : Continuous c) (n : ℕ) :
    Continuous (leftHolonomy (fun y => (1 : ℤ) +ᵥ y) c n) := by
  induction n with
  | zero =>
    change Continuous (fun _ : X => (1 : G))
    exact continuous_const
  | succ n ih =>
    have he : leftHolonomy (fun y : X => (1 : ℤ) +ᵥ y) c (n + 1) =
        fun x => c ((n : ℤ) +ᵥ x) *
          leftHolonomy (fun y => (1 : ℤ) +ᵥ y) c n x := by
      funext x
      rw [leftHolonomy_succ, iterate_unit_vadd]
    rw [he]
    exact (hc.comp (hact (n : ℤ))).mul ih

private theorem continuous_phaseTransfer {h : ℕ}
    (hact : ∀ g : ℤ, Continuous (fun x : X => g +ᵥ x))
    (p : X → ZMod h) (hp : Continuous p) (c : X → G) (hc : Continuous c) :
    Continuous (phaseTransfer p c) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hfixed : Continuous (fun y : X =>
      leftHolonomy (fun z => (1 : ℤ) +ᵥ z) c (p x).val
        ((-((p x).val : ℤ)) +ᵥ y)) :=
    (continuous_leftHolonomy hact c hc (p x).val).comp (hact _)
  apply hfixed.continuousAt.congr_of_eventuallyEq
  have hlc := (IsLocallyConstant.iff_continuous p).2 hp
  filter_upwards [hlc.eventually_eq x] with y hy
  simp only [phaseTransfer, hy]

/-- A continuous cocycle whose full return transport is the identity on the
zero phase of a positive finite cyclic tower is a continuous coboundary.
The transfer is normalized to one on that phase. Neither compactness nor
minimality of the action, nor finiteness or commutativity of the group, is needed. -/
theorem exists_continuous_transfer_of_phase_return
    (hact : ∀ g : ℤ, Continuous (fun x : X => g +ᵥ x))
    (h : ℕ) (hh : 0 < h) (p : X → ZMod h) (hp : Continuous p)
    (hphase : ∀ (g : ℤ) (x : X), p (g +ᵥ x) = (g : ZMod h) + p x)
    (c : X → G) (hc : Continuous c)
    (hreturn : ∀ z, p z = 0 →
      leftHolonomy (fun x => (1 : ℤ) +ᵥ x) c h z = 1) :
    ∃ b : X → G, Continuous b ∧ (∀ z, p z = 0 → b z = 1) ∧
      ∀ x, b ((1 : ℤ) +ᵥ x) = c x * b x := by
  let : NeZero h := ⟨Nat.ne_of_gt hh⟩
  let b := phaseTransfer p c
  have hbzero : ∀ z, p z = 0 → b z = 1 := by
    intro z hz
    simp [b, phaseTransfer, hz, leftHolonomy]
  refine ⟨b, continuous_phaseTransfer hact p hp c hc, hbzero, ?_⟩
  intro x
  let r := (p x).val
  let z := (-(r : ℤ)) +ᵥ x
  have hz : p z = 0 := by
    simp [z, r, hphase]
  have hx : (fun y : X => (1 : ℤ) +ᵥ y)^[r] z = x := by
    rw [iterate_unit_vadd]
    simp [z, ← add_vadd]
  have hr : r < h := ZMod.val_lt (p x)
  have hpx : p ((1 : ℤ) +ᵥ x) = ((r + 1 : ℕ) : ZMod h) := by
    simp [hphase, r, add_comm]
  by_cases hs : r + 1 < h
  · have hv : (p ((1 : ℤ) +ᵥ x)).val = r + 1 := by
      rw [hpx, ZMod.val_natCast_of_lt hs]
    have hbase : (-((p ((1 : ℤ) +ᵥ x)).val : ℤ)) +ᵥ ((1 : ℤ) +ᵥ x) = z := by
      rw [hv, ← add_vadd]
      dsimp [z]
      congr 1
      omega
    change leftHolonomy _ c (p ((1 : ℤ) +ᵥ x)).val
      ((-((p ((1 : ℤ) +ᵥ x)).val : ℤ)) +ᵥ ((1 : ℤ) +ᵥ x)) = _
    rw [hbase, hv, leftHolonomy_succ, hx]
    rfl
  · have he : r + 1 = h := by omega
    have hpzero : p ((1 : ℤ) +ᵥ x) = 0 := by
      rw [hpx, he]
      simp
    rw [hbzero _ hpzero]
    have hlast := hreturn z hz
    rw [← he, leftHolonomy_succ, hx] at hlast
    exact hlast.symm

end D5.S1.Dynamics.FinitePhaseCoboundary
