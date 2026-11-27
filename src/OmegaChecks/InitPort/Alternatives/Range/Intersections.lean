module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Fin
public import Init.Data.Range.Polymorphic.UInt
import all Init.Data.Range.Polymorphic.Internal.SignedBitVec
import all Init.Data.Range.Polymorphic.SInt
import all Init.Data.Char.Ordinal
import all Init.Data.Range.Polymorphic.Char
import Init.Data.BitVec.Lemmas
public import OmegaChecks.InitPort.Alternatives.Range.Characters
import all OmegaChecks.InitPort.Alternatives.Range.Characters

/-! Sizes of intersections of natural ranges. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

private theorem boundedNatIntersection (lo hi slo shi a : Nat) :
    (max lo slo ≤ a ∧ a < min hi shi) ↔ (lo ≤ a ∧ a < hi) ∧ (slo ≤ a ∧ a < shi) :=
  ⟨fun ⟨above, below⟩ => ⟨⟨(Nat.max_le.mp above).1, (Nat.lt_min.mp below).1⟩,
    ⟨(Nat.max_le.mp above).2, (Nat.lt_min.mp below).2⟩⟩,
   fun ⟨r, s⟩ => ⟨Nat.max_le.mpr ⟨r.1, s.1⟩, Nat.lt_min.mpr ⟨r.2, s.2⟩⟩⟩

private theorem upperNatIntersection (hi slo shi a : Nat) :
    (slo ≤ a ∧ a < min hi shi) ↔ a < hi ∧ (slo ≤ a ∧ a < shi) :=
  ⟨fun ⟨above, below⟩ => ⟨(Nat.lt_min.mp below).1, above, (Nat.lt_min.mp below).2⟩,
   fun ⟨r, s⟩ => ⟨s.1, Nat.lt_min.mpr ⟨r, s.2⟩⟩⟩

private theorem lowerNatIntersection (lo slo shi a : Nat) :
    (max lo slo ≤ a ∧ a < shi) ↔ lo ≤ a ∧ (slo ≤ a ∧ a < shi) :=
  ⟨fun ⟨above, below⟩ => ⟨(Nat.max_le.mp above).1, (Nat.max_le.mp above).2, below⟩,
   fun ⟨r, s⟩ => ⟨Nat.max_le.mpr ⟨r, s.1⟩, s.2⟩⟩

public theorem Std.instLawfulRcoIntersectionNat : Roo.LawfulRcoIntersection Nat where
  mem_intersection_iff := boundedNatIntersection _ _ _ _ _

public theorem Std.instLawfulRcoIntersectionNat_1 : Roc.LawfulRcoIntersection Nat where
  mem_intersection_iff {a r s} := (boundedNatIntersection (r.lower + 1) (r.upper + 1) s.lower s.upper a).trans
    (and_congr_left fun _ => and_congr_right fun _ => Nat.lt_succ_iff)

public theorem Std.instLawfulRcoIntersectionNat_2 : Roi.LawfulRcoIntersection Nat where
  mem_intersection_iff := lowerNatIntersection _ _ _ _

public theorem Std.instLawfulRcoIntersectionNat_3 : Rco.LawfulRcoIntersection Nat where
  mem_intersection_iff := boundedNatIntersection _ _ _ _ _

public theorem Std.instLawfulRcoIntersectionNat_4 : Rcc.LawfulRcoIntersection Nat where
  mem_intersection_iff {a r s} := (boundedNatIntersection r.lower (r.upper + 1) s.lower s.upper a).trans
    (and_congr_left fun _ => and_congr_right fun _ => Nat.lt_succ_iff)

public theorem Std.instLawfulRcoIntersectionNat_5 : Rci.LawfulRcoIntersection Nat where
  mem_intersection_iff := lowerNatIntersection _ _ _ _

public theorem Std.instLawfulRcoIntersectionNat_6 : Rio.LawfulRcoIntersection Nat where
  mem_intersection_iff := upperNatIntersection _ _ _ _

public theorem Std.instLawfulRcoIntersectionNat_7 : Ric.LawfulRcoIntersection Nat where
  mem_intersection_iff {a r s} := (upperNatIntersection (r.upper + 1) s.lower s.upper a).trans
    (and_congr_left fun _ => Nat.lt_succ_iff)

end OmegaChecks.InitPort.Alternatives
