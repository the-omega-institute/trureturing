/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryBirth
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryBirth
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Whole canonical birth packs and literal old-enumeration readbacks. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

/-! Birth packs retain the entire enumerations, including all unborn labels. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent

local instance carrierMeasurable {b : Ordinal.{0}} (C : Set (Cube b)) :
    MeasurableSpace C := borel C
local instance carrierBorel {b : Ordinal.{0}} (C : Set (Cube b)) :
    BorelSpace C := ⟨rfl⟩

/-- One whole birth, separate from the permanent N arrival entry. -/
structure BirthPack {b : Ordinal.{0}} (C : Set (Cube b)) where
  U : Label → SupportFamily C
  Uonto : Surjective U
  B : ℕ → Clopens C
  Bonto : Surjective B
  V : SupportFamily C
  nu : Label → BornData V
  nuonto : Surjective nu

namespace BirthPack

variable {b : Ordinal.{0}} {C D : Set (Cube b)}

def measure (W : BirthPack C) (d : Label) (n : ℕ) : SignedMeasure C :=
  ((W.nu d).1 n).1

/-- Only equality of literal carriers is used; all whole labels stay fixed. -/
def cast (h : C = D) (W : BirthPack C) : BirthPack D := by
  subst D
  exact W

theorem cast_heq (h : C = D) (W : BirthPack C) : HEq (cast h W) W := by
  subst D
  rfl

theorem cast_B_heq (h : C = D) (W : BirthPack C) : HEq (cast h W).B W.B := by
  subst D
  rfl

theorem heq_V (h : C = D) (W : BirthPack C) (W' : BirthPack D)
    (he : HEq W W') : HEq W.V W'.V := by
  subst D
  cases eq_of_heq he
  rfl

theorem heq_measure (h : C = D) (W : BirthPack C) (W' : BirthPack D)
    (he : HEq W W') (d : Label) (n : ℕ) : HEq (W.measure d n) (W'.measure d n) := by
  subst D
  cases eq_of_heq he
  rfl

theorem cast_cast {E : Set (Cube b)} (h : C = D) (h' : D = E) (W : BirthPack C) :
    cast h' (cast h W) = cast (h.trans h') W := by
  subst D
  subst E
  rfl

/-- Equality of all archived fields determines the whole transported birth. -/
theorem eq_cast (h : C = D) (W : BirthPack C) (W' : BirthPack D)
    (hU : HEq W.U W'.U) (hB : HEq W.B W'.B)
    (hV : HEq W.V W'.V) (hnu : HEq W.nu W'.nu) : cast h W = W' := by
  subst D
  cases W with
  | mk U hUonto B hBonto V nu hnuonto =>
    cases W' with
    | mk U' hUonto' B' hBonto' V' nu' hnuonto' =>
      have hu := eq_of_heq hU
      have hb := eq_of_heq hB
      have hv := eq_of_heq hV
      dsimp only at hu hb hv
      subst U'
      subst B'
      subst V'
      have hn := eq_of_heq hnu
      dsimp only at hn
      subst nu'
      rfl

private theorem ext_measure (W W' : BirthPack C)
    (hU : W.U = W'.U) (hB : W.B = W'.B) (hV : W.V = W'.V)
    (hnu : ∀ d n, W.measure d n = W'.measure d n) : W = W' := by
  cases W with
  | mk U hUonto B hBonto V nu hnuonto =>
    cases W' with
    | mk U' hUonto' B' hBonto' V' nu' hnuonto' =>
      dsimp only at hU hB hV hnu
      subst U'
      subst B'
      subst V'
      have he : nu = nu' := by
        funext d
        apply Subtype.ext
        funext n
        apply Subtype.ext
        exact hnu d n
      subst nu'
      rfl

end BirthPack

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a} (Q : Prepared H ha P launch)

/-- The canonical whole newborn object is a readout of Q, without reselection. -/
def newborn : BirthPack (H.carrier (top a)) where
  U := Q.U
  Uonto := Q.Uonto
  B := Q.B
  Bonto := Q.Bonto
  V := Q.V (newRow a ha)
  nu := Q.nu (newRow a ha)
  nuonto := Q.nuonto (newRow a ha)

/-- A current view of an old row, with B supplied by its archived birth. -/
def predecessorPack (bornB : OldClopens H ha)
    (hB : ∀ r hr, Surjective (bornB r hr))
    (r : Rows a) (hr : r ≠ newRow a ha) : BirthPack (H.carrier (rowIndex r)) where
  U := P.U r hr
  Uonto := P.Uonto r hr
  B := bornB r hr
  Bonto := hB r hr
  V := P.V r hr
  nu := P.nu r hr
  nuonto := P.nuonto r hr

/-- Preparation preserves every old whole label, even labels not yet eligible
for J. The B component is read from the old birth on both sides. -/
def preparedOldPack (bornB : OldClopens H ha)
    (hB : ∀ r hr, Surjective (bornB r hr))
    (r : Rows a) (hr : r ≠ newRow a ha) : BirthPack (H.carrier (rowIndex r)) where
  U := P.U r hr
  Uonto := P.Uonto r hr
  B := bornB r hr
  Bonto := hB r hr
  V := Q.V r
  nu := Q.nu r
  nuonto := Q.nuonto r

theorem prepared_old_readback (bornB : OldClopens H ha)
    (hB : ∀ r hr, Surjective (bornB r hr))
    (r : Rows a) (hr : r ≠ newRow a ha) :
    preparedOldPack Q bornB hB r hr = predecessorPack (P := P) bornB hB r hr := by
  apply BirthPack.ext_measure
  · rfl
  · rfl
  · exact Q.oldV r hr
  · exact Q.oldNu r hr

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth
