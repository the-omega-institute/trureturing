/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full compatible raw-history fibers and their exact nominal cardinalities. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber

open ActualTreeReadoutAcquisition (Address Reply)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination (RawHistory)

abbrev CoarseHistory := List (Sigma (fun _ : Address => Option Bool))

/-- All raw lifts of one coarse symbol, including raw absence. -/
abbrev ReplyLift (z : Option Bool) := {y : Reply // kappa y = z}

/-- An ordered raw lift at every position; no realizability predicate removes ghosts. -/
def CompatCache : CoarseHistory → Type
  | [] => PUnit
  | a :: g => ReplyLift a.2 × CompatCache g

instance (g : CoarseHistory) : Fintype (CompatCache g) := by
  induction g with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons a g ih =>
    letI := ih
    exact inferInstanceAs (Fintype (ReplyLift a.2 × CompatCache g))

/-- Decode the literal ordered cache, without changing any raw lift. -/
def decode : (g : CoarseHistory) → CompatCache g → RawHistory
  | [], _ => []
  | a :: g, c => ⟨a.1, c.1.val⟩ :: decode g c.2

theorem decode_projection (g : CoarseHistory) (c : CompatCache g) :
    kappa_hist (decode g c) = g := by
  induction g with
  | nil => rfl
  | cons a g ih =>
    simp only [decode, kappa_hist, List.map_cons]
    rw [show kappa c.1.val = a.2 from c.1.property, ← kappa_hist, ih]

theorem decode_injective (g : CoarseHistory) : Function.Injective (decode g) := by
  induction g with
  | nil => intro c d _; cases c; cases d; rfl
  | cons a g ih =>
    intro c d equal
    have parts := List.cons.inj equal
    exact Prod.ext (Subtype.ext (congrArg Sigma.snd parts.1)) (ih parts.2)

/-- Every raw history with the given projection occurs in the fiber. -/
theorem decode_surjective (g : CoarseHistory) (h : RawHistory)
    (equal : kappa_hist h = g) : ∃ c : CompatCache g, decode g c = h := by
  induction h generalizing g with
  | nil => subst g; exact ⟨PUnit.unit, rfl⟩
  | cons a h ih =>
    subst g
    obtain ⟨c, hc⟩ := ih (kappa_hist h) rfl
    refine ⟨(⟨a.2, rfl⟩, c), ?_⟩
    change (⟨a.1, a.2⟩ : Sigma (fun _ : Address => Reply)) :: decode _ c = a :: h
    rw [hc]

/-- Repack an exact raw cache; only its coarse projection is required. -/
noncomputable def pack (g : CoarseHistory) (h : RawHistory)
    (equal : kappa_hist h = g) : CompatCache g :=
  (decode_surjective g h equal).choose

theorem decode_pack (g : CoarseHistory) (h : RawHistory)
    (equal : kappa_hist h = g) : decode g (pack g h equal) = h :=
  (decode_surjective g h equal).choose_spec

/-- The fiber is exactly the full inverse image of the coarse projection. -/
noncomputable def cacheEquiv (g : CoarseHistory) :
    CompatCache g ≃ {h : RawHistory // kappa_hist h = g} where
  toFun c := ⟨decode g c, decode_projection g c⟩
  invFun h := pack g h.val h.property
  left_inv c := decode_injective g (decode_pack g _ _)
  right_inv h := Subtype.ext (decode_pack g _ _)

/-- With address distinctness, every lift is an ordered first-occurrence cache. -/
theorem decode_addresses (g : CoarseHistory) (c : CompatCache g) :
    (decode g c).map Sigma.fst = g.map Sigma.fst := by
  have h := congrArg (List.map Sigma.fst) (decode_projection g c)
  simpa only [kappa_hist, List.map_map, Function.comp_def] using h

/-- Number of coarse-none positions, hence free raw branch/absent choices. -/
def noneCount (g : CoarseHistory) : Nat :=
  (g.filter (fun a => a.2.isNone)).length

theorem compatible_cache_card (g : CoarseHistory) :
    Fintype.card (CompatCache g) = 2 ^ noneCount g := by
  have liftCard (z : Option Bool) :
      Fintype.card (ReplyLift z) = if z.isNone then 2 else 1 := by
    cases z with
    | none => decide
    | some b => cases b <;> decide
  induction g with
  | nil => rfl
  | cons a g ih =>
    change Fintype.card (ReplyLift a.2 × CompatCache g) = _
    rw [Fintype.card_prod, liftCard, ih]
    cases h : a.2 with
    | none => simp [noneCount, h, Nat.pow_succ, Nat.mul_comm]
    | some b => simp [noneCount, h]

end D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
