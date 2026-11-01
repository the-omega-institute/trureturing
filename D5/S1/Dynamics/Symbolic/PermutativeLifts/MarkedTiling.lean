/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact two-sided marked tilings by nonempty variable-length binary words. -/

import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.DivMod
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- A letter carries its block type and its offset inside that block. -/
abbrev TileState (W : Bool → List Bool) := Σ a : Bool, Fin (W a).length

instance tileStateFintype (W : Bool → List Bool) : Fintype (TileState W) :=
  inferInstanceAs (Fintype (Σ a : Bool, Fin (W a).length))

instance tileStateTopology (W : Bool → List Bool) : TopologicalSpace (TileState W) := ⊥

instance tileStateDiscrete (W : Bool → List Bool) : DiscreteTopology (TileState W) :=
  discreteTopology_bot _

/-- Inside a block the offset advances by one. Only a last offset may be followed
by the start of another block, whose type is unrestricted. -/
def TileNext (W : Bool → List Bool) (s t : TileState W) : Prop :=
  (s.1 = t.1 ∧ (t.2 : ℕ) = (s.2 : ℕ) + 1) ∨
    ((s.2 : ℕ) + 1 = (W s.1).length ∧ (t.2 : ℕ) = 0)

/-- Actual bi-infinite local block coordinates, without a chosen origin block. -/
def Tiled (W : Bool → List Bool) (x : ℤ → TileState W) : Prop :=
  ∀ i : ℤ, TileNext W (x i) (x (i + 1))

abbrev MarkedTiling (W : Bool → List Bool) := {x : ℤ → TileState W // Tiled W x}

theorem tiled_closed (W : Bool → List Bool) : IsClosed {x | Tiled W x} := by
  have hlocal (i : ℤ) :
      IsClosed {x : ℤ → TileState W | TileNext W (x i) (x (i + 1))} := by
    have hc : Continuous (fun x : ℤ → TileState W => (x i, x (i + 1))) :=
      (continuous_apply i).prodMk (continuous_apply (i + 1))
    have hs : IsClosed {p : TileState W × TileState W | TileNext W p.1 p.2} :=
      isClosed_discrete _
    exact hs.preimage hc
  have heq : {x | Tiled W x} =
      ⋂ i : ℤ, {x | TileNext W (x i) (x (i + 1))} := by
    ext x
    simp [Tiled]
  rw [heq]
  exact isClosed_iInter hlocal

instance markedTilingCompact (W : Bool → List Bool) : CompactSpace (MarkedTiling W) :=
  isCompact_iff_compactSpace.mp (tiled_closed W).isCompact

/-- Integer translation preserves the local block coordinates. -/
theorem tiled_shift (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (k : ℤ) : Tiled W (shift k x) := by
  intro i
  simpa only [shift_apply, add_assoc] using hx (k + i)

def shiftTiling (W : Bool → List Bool) (k : ℤ) (x : MarkedTiling W) :
    MarkedTiling W :=
  ⟨shift k x.1, tiled_shift W x.2 k⟩

@[simp] theorem shiftTiling_apply (W : Bool → List Bool) (k : ℤ)
    (x : MarkedTiling W) (i : ℤ) :
    (shiftTiling W k x).1 i = x.1 (k + i) := rfl

/-- The actual binary symbol written at a marked state. -/
def readTile (W : Bool → List Bool) (s : TileState W) : Bool :=
  (W s.1).get s.2

/-- Reading a marked state at a specified type and physical offset. -/
theorem readTile_of_coordinates (W : Bool → List Bool) (s : TileState W)
    (a : Bool) (p : ℕ) (hp : p < (W a).length)
    (ht : s.1 = a) (ho : s.2.val = p) : readTile W s = (W a)[p] := by
  rcases s with ⟨b, q⟩
  dsimp at ht ho
  subst a
  subst p
  rfl

def readTiling (W : Bool → List Bool) (x : MarkedTiling W) : ℤ → Bool :=
  fun i => readTile W (x.1 i)

theorem continuous_readTiling (W : Bool → List Bool) : Continuous (readTiling W) := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous (readTile W)).comp
    ((continuous_apply i).comp continuous_subtype_val)

@[simp] theorem readTiling_shift (W : Bool → List Bool) (k : ℤ)
    (x : MarkedTiling W) :
    readTiling W (shiftTiling W k x) = shift k (readTiling W x) := rfl

/-- A periodic tiling entirely by the block of type `a`. -/
def periodicTile (W : Bool → List Bool) (a : Bool) (ha : 0 < (W a).length)
    (i : ℤ) : TileState W :=
  ⟨a, ⟨(i % ((W a).length : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg i (show ((W a).length : ℤ) ≠ 0 by omega)
    have hlt := Int.emod_lt_of_pos i (show 0 < ((W a).length : ℤ) by omega)
    omega⟩⟩

theorem periodicTile_tiled (W : Bool → List Bool) (a : Bool)
    (ha : 0 < (W a).length) : Tiled W (periodicTile W a ha) := by
  intro i
  let h : ℕ := (W a).length
  have hh : 0 < (h : ℤ) := by dsimp [h]; omega
  have hr0 : 0 ≤ i % (h : ℤ) := Int.emod_nonneg i (by omega)
  have hrh : i % (h : ℤ) < (h : ℤ) := Int.emod_lt_of_pos i hh
  have heq : (i + 1) % (h : ℤ) = (i % (h : ℤ) + 1) % (h : ℤ) :=
    (Int.emod_add_emod i (h : ℤ) 1).symm
  change (a = a ∧ ((i + 1) % (h : ℤ)).toNat =
      (i % (h : ℤ)).toNat + 1) ∨
    ((i % (h : ℤ)).toNat + 1 = h ∧ ((i + 1) % (h : ℤ)).toNat = 0)
  by_cases hr : i % (h : ℤ) + 1 < (h : ℤ)
  · left
    refine ⟨rfl, ?_⟩
    rw [heq, Int.emod_eq_of_lt (by omega) hr]
    omega
  · right
    have hb : i % (h : ℤ) + 1 = (h : ℤ) := by omega
    refine ⟨by omega, ?_⟩
    rw [heq, hb, Int.emod_self]
    rfl

theorem markedTiling_nonempty (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) : Nonempty (MarkedTiling W) :=
  ⟨⟨periodicTile W false (hW false), periodicTile_tiled W false (hW false)⟩⟩

/-- Exactly the binary configurations admitting a marked tiling by `W`. -/
def tiledSubshift (W : Bool → List Bool) : Subshift Bool ℤ where
  carrier := Set.range (readTiling W)
  isClosed := (isCompact_range (continuous_readTiling W)).isClosed
  mapsTo := by
    intro k y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨shiftTiling W k x, readTiling_shift W k x⟩

theorem tiledSubshift_nonempty (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) : (tiledSubshift W).carrier.Nonempty := by
  obtain ⟨x⟩ := markedTiling_nonempty W hW
  exact ⟨readTiling W x, x, rfl⟩

/-- A positive offset determines its preceding state inside the same block. -/
theorem tiled_previous (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) (hi : 0 < (x i).2.val) :
    (x (i - 1)).1 = (x i).1 ∧ (x (i - 1)).2.val + 1 = (x i).2.val := by
  have hn := hx (i - 1)
  have heq : i - 1 + 1 = i := by omega
  rw [heq] at hn
  rcases hn with hn | hn
  · exact ⟨hn.1, hn.2.symm⟩
  · omega

/-- The marked offset really counts all steps back to the start of this block. -/
theorem tiled_backwards (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) (k : ℕ) (hk : k ≤ (x i).2.val) :
    (x (i - (k : ℤ))).1 = (x i).1 ∧
      (x (i - (k : ℤ))).2.val = (x i).2.val - k := by
  induction k generalizing i with
  | zero =>
    have heq : x (i - (0 : ℤ)) = x i := congrArg x (sub_zero i)
    exact ⟨congrArg (fun s : TileState W => s.1) heq,
      congrArg (fun s : TileState W => s.2.val) heq⟩
  | succ k ih =>
    have hp := tiled_previous W hx i (by omega)
    have hb := ih (i - 1) (by omega)
    have heq : i - ((k + 1 : ℕ) : ℤ) = (i - 1) - (k : ℤ) := by omega
    rw [heq]
    exact ⟨hb.1.trans hp.1, by omega⟩

theorem tiled_boundary_behind (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) :
    (x (i - ((x i).2.val : ℤ))).1 = (x i).1 ∧
      (x (i - ((x i).2.val : ℤ))).2.val = 0 := by
  simpa using tiled_backwards W hx i (x i).2.val (le_refl _)

theorem tiled_no_boundary_behind (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i j : ℤ)
    (hij : i - ((x i).2.val : ℤ) < j) (hji : j ≤ i) : (x j).2.val ≠ 0 := by
  let k := (i - j).toNat
  have hk : k ≤ (x i).2.val := by dsimp [k]; omega
  have hi : i - (k : ℤ) = j := by dsimp [k]; omega
  have hb := (tiled_backwards W hx i k hk).2
  rw [hi] at hb
  dsimp [k] at hb
  omega

/-- The next position begins a block exactly when this one ends its block. -/
theorem tileNext_boundary_iff (W : Bool → List Bool) {s t : TileState W}
    (hst : TileNext W s t) :
    t.2.val = 0 ↔ s.2.val + 1 = (W s.1).length := by
  rcases hst with hst | hst
  · have ht := t.2.isLt
    have hlen := congrArg (fun a => (W a).length) hst.1
    constructor <;> intro h <;> omega
  · exact ⟨fun _ => hst.1, fun _ => hst.2⟩

theorem tiled_next_inside (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) (hi : (x i).2.val + 1 < (W (x i).1).length) :
    (x (i + 1)).1 = (x i).1 ∧ (x (i + 1)).2.val = (x i).2.val + 1 := by
  rcases hx i with hn | hn
  · exact ⟨hn.1.symm, hn.2⟩
  · omega

/-- Up to its final offset the local path is exactly the specified finite block. -/
theorem tiled_forwards (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) (k : ℕ)
    (hk : (x i).2.val + k < (W (x i).1).length) :
    (x (i + (k : ℤ))).1 = (x i).1 ∧
      (x (i + (k : ℤ))).2.val = (x i).2.val + k := by
  induction k with
  | zero =>
    have heq : x (i + (0 : ℤ)) = x i := congrArg x (add_zero i)
    exact ⟨congrArg (fun s : TileState W => s.1) heq,
      congrArg (fun s : TileState W => s.2.val) heq⟩
  | succ k ih =>
    have hp := ih (by omega)
    have hh : (x (i + (k : ℤ))).2.val + 1 <
        (W (x (i + (k : ℤ))).1).length := by
      have hlen := congrArg (fun a => (W a).length) hp.1
      omega
    have hn := tiled_next_inside W hx (i + (k : ℤ)) hh
    have heq : i + ((k + 1 : ℕ) : ℤ) = i + (k : ℤ) + 1 := by omega
    rw [heq]
    exact ⟨hn.1.trans hp.1, by omega⟩

/-- The first position after the current finite block is a genuine boundary. -/
theorem tiled_boundary_ahead (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i : ℤ) :
    (x (i + (((W (x i).1).length - (x i).2.val : ℕ) : ℤ))).2.val = 0 := by
  have hi := (x i).2.isLt
  let k : ℕ := (W (x i).1).length - (x i).2.val - 1
  have hk : (x i).2.val + k < (W (x i).1).length := by dsimp [k]; omega
  have hp := tiled_forwards W hx i k hk
  have hsum : (x i).2.val + k + 1 = (W (x i).1).length := by
    dsimp [k]
    omega
  have hn := (tileNext_boundary_iff W (hx (i + (k : ℤ)))).2 (by
    have hlen := congrArg (fun a => (W a).length) hp.1
    omega)
  have heq : i + (k : ℤ) + 1 =
      i + (((W (x i).1).length - (x i).2.val : ℕ) : ℤ) := by dsimp [k]; omega
  exact (congrArg (fun j : ℤ => (x j).2.val) heq).symm.trans hn

theorem tiled_no_boundary_ahead (W : Bool → List Bool) {x : ℤ → TileState W}
    (hx : Tiled W x) (i j : ℤ) (hij : i < j)
    (hji : j < i + (((W (x i).1).length - (x i).2.val : ℕ) : ℤ)) :
    (x j).2.val ≠ 0 := by
  have hi := (x i).2.isLt
  let k := (j - i).toNat
  have hk : (x i).2.val + k < (W (x i).1).length := by dsimp [k]; omega
  have heq : i + (k : ℤ) = j := by dsimp [k]; omega
  have hp := (tiled_forwards W hx i k hk).2
  rw [heq] at hp
  dsimp [k] at hp
  omega

/-- The set of boundaries determines every offset, independently of the symbols. -/
theorem tiled_offset_eq_of_boundaries (W : Bool → List Bool)
    {x y : ℤ → TileState W} (hx : Tiled W x) (hy : Tiled W y)
    (hb : ∀ j, (x j).2.val = 0 ↔ (y j).2.val = 0) (i : ℤ) :
    (x i).2.val = (y i).2.val := by
  have hxy : (x i).2.val ≤ (y i).2.val := by
    by_contra h
    have hz := (hb (i - ((y i).2.val : ℤ))).2 (tiled_boundary_behind W hy i).2
    exact tiled_no_boundary_behind W hx i (i - ((y i).2.val : ℤ))
      (by omega) (by omega) hz
  have hyx : (y i).2.val ≤ (x i).2.val := by
    by_contra h
    have hz := (hb (i - ((x i).2.val : ℤ))).1 (tiled_boundary_behind W hx i).2
    exact tiled_no_boundary_behind W hy i (i - ((x i).2.val : ℤ))
      (by omega) (by omega) hz
  omega

/-- If the two word heights differ, boundaries determine the entire marked tiling. -/
theorem tiled_eq_of_boundaries (W : Bool → List Bool)
    (hW : Function.Injective (fun a => (W a).length))
    {x y : ℤ → TileState W} (hx : Tiled W x) (hy : Tiled W y)
    (hb : ∀ j, (x j).2.val = 0 ↔ (y j).2.val = 0) : x = y := by
  funext i
  have hoff := tiled_offset_eq_of_boundaries W hx hy hb i
  have hxi := (x i).2.isLt
  have hyi := (y i).2.isLt
  have hxy : (W (x i).1).length ≤ (W (y i).1).length := by
    by_contra h
    let j := i + (((W (y i).1).length - (y i).2.val : ℕ) : ℤ)
    have hz := (hb j).2 (tiled_boundary_ahead W hy i)
    exact tiled_no_boundary_ahead W hx i j (by dsimp [j]; omega)
      (by dsimp [j]; omega) hz
  have hyx : (W (y i).1).length ≤ (W (x i).1).length := by
    by_contra h
    let j := i + (((W (x i).1).length - (x i).2.val : ℕ) : ℤ)
    have hz := (hb j).1 (tiled_boundary_ahead W hx i)
    exact tiled_no_boundary_ahead W hy i j (by dsimp [j]; omega)
      (by dsimp [j]; omega) hz
  have htype := hW (Nat.le_antisymm hxy hyx)
  cases hxs : x i with
  | mk a p =>
    cases hys : y i with
    | mk b q =>
      have hxoff : (x i).2.val = p.val :=
        congrArg (fun s : TileState W => s.2.val) hxs
      have hyoff : (y i).2.val = q.val :=
        congrArg (fun s : TileState W => s.2.val) hys
      have hxt : (x i).1 = a := congrArg (fun s : TileState W => s.1) hxs
      have hyt : (y i).1 = b := congrArg (fun s : TileState W => s.1) hys
      have hab : a = b := hxt.symm.trans (htype.trans hyt)
      have hpq : p.val = q.val := hxoff.symm.trans (hoff.trans hyoff)
      cases hab
      exact congrArg (Sigma.mk a) (Fin.ext hpq)

end D5.S1.Dynamics.Symbolic.PermutativeLifts
