import Reg.Support.LegacyCausalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Support.LegacyCausalSlots
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Reg.Support.LegacyCausalCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

/-- Eight slots: four components of each of the two original readouts. -/
abbrev Slot := Fin 8
def coarse (i : Slot) : Bool := decide (i.val < 4)
def fineSlot : Slot := 7

def choose {Y : Type} (i j : Slot) (yes no : Y) : Y :=
  Bool.rec no yes (decide (i = j))
def slot0 : Slot := ⟨Nat.zero, by decide⟩
def slot1 : Slot := ⟨(Nat.succ Nat.zero), by decide⟩
def slot2 : Slot := ⟨(Nat.succ (Nat.succ Nat.zero)), by decide⟩
def slot3 : Slot := ⟨(Nat.succ (Nat.succ (Nat.succ Nat.zero))), by decide⟩
def slot4 : Slot := ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))), by decide⟩
def slot5 : Slot := ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))), by decide⟩
def slot6 : Slot := ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))), by decide⟩

def signature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Slot
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def vectorRealization {X Y : Type} [DecidableEq Y]
    (s0 s1 s2 s3 s4 s5 s6 : Slot)
    (c0 c1 c2 c3 f0 f1 f2 f3 : X → Y) : PrimitiveRealization (signature X Y) where
  readout := fun i x =>
    (choose i s0 (c0 x) (choose i s1 (c1 x) (choose i s2 (c2 x) (choose i s3 (c3 x) (choose i s4 (f0 x) (choose i s5 (f1 x) (choose i s6 (f2 x) (f3 x))))))))
  anchor := Fin.elim0

def slotRealization {X Y : Type} [DecidableEq Y] (read : Slot → X → Y) :
    PrimitiveRealization (signature X Y) := ⟨read, Fin.elim0⟩

def split {X Y : Type} [DecidableEq Y] (f g : X → Y × Y × Y × Y) :=
  vectorRealization slot0 slot1 slot2 slot3 slot4 slot5 slot6
    (fun x => (f x).1) (fun x => (f x).2.1)
    (fun x => (f x).2.2.1) (fun x => (f x).2.2.2)
    (fun x => (g x).1) (fun x => (g x).2.1)
    (fun x => (g x).2.2.1) (fun x => (g x).2.2.2)

theorem split_coarse {X Y : Type} [DecidableEq Y] (f g : X → Y × Y × Y × Y)
    (x y : X) :
    (∀ i, coarse i = true → (split f g).readout i x = (split f g).readout i y) ↔
      f x = f y := by
  simp [split, vectorRealization, coarse, Fin.forall_fin_succ, choose, slot0, slot1, slot2, slot3, slot4, slot5, slot6, Prod.ext_iff]
  <;> tauto

theorem split_fine {X Y : Type} [DecidableEq Y] (f g : X → Y × Y × Y × Y)
    (x y : X) :
    (∃ i, coarse i = false ∧ (split f g).readout i x ≠ (split f g).readout i y) ↔
      g x ≠ g y := by
  simp [split, vectorRealization, coarse, Fin.exists_fin_succ, choose, slot0, slot1, slot2, slot3, slot4, slot5, slot6, Prod.ext_iff]
  <;> tauto

def arena (A : Arena) (Y E : Type) [DecidableEq Y] (embed : E → A.State) :
    PrimitiveLawArena where
  toArena := A
  signature := signature A.State Y
  Law r := ∃ a b : E,
    (∀ i, coarse i = true → r.readout i (embed a) = r.readout i (embed b)) ∧
    ∃ i, coarse i = false ∧ r.readout i (embed a) ≠ r.readout i (embed b)

theorem split_law (A : Arena) (Y E : Type) [DecidableEq Y] (embed : E → A.State)
    (f g : A.State → Y × Y × Y × Y) :
    (arena A Y E embed).Law (split f g) ↔
      ∃ a b : E, f (embed a) = f (embed b) ∧ g (embed a) ≠ g (embed b) := by
  simp only [arena, split_coarse, split_fine]

def constant {X Y : Type} [DecidableEq Y] (z : Y) : PrimitiveRealization (signature X Y) :=
  ⟨fun _ _ => z, Fin.elim0⟩

theorem constant_rejected (A : Arena) (Y E : Type) [DecidableEq Y]
    (embed : E → A.State) (z : Y) : ¬ (arena A Y E embed).Law (constant z) := by
  rintro ⟨a, b, _, i, _, h⟩
  exact h rfl

/-- Each separate source component admits a Law-changing intervention, with
all other components and all anchors fixed. -/
theorem sensitivity (A : Arena) (Y E : Type) [DecidableEq Y]
    (embed : E → A.State) (d : A.State → Y) (z : Y)
    (a b : E) (different : d (embed a) ≠ d (embed b)) :
    FiniteSlotSensitivity (arena A Y E embed) := by
  classical
  constructor
  · intro i
    by_cases hi : coarse i = true
    · let good : PrimitiveRealization (signature A.State Y) :=
        ⟨fun j x => if j = fineSlot then d x else z, Fin.elim0⟩
      let bad : PrimitiveRealization (signature A.State Y) :=
        ⟨fun j x => if j = i ∨ j = fineSlot then d x else z, Fin.elim0⟩
      have hf : coarse fineSlot = false := rfl
      have neq : i ≠ fineSlot := by intro h; rw [h, hf] at hi; cases hi
      have hg : (arena A Y E embed).Law good := by
        refine ⟨a, b, ?_, fineSlot, hf, ?_⟩
        · intro j hj
          have hn : j ≠ fineSlot := by intro h; rw [h, hf] at hj; cases hj
          simp [good, hn]
        · simpa [good] using different
      have hb : ¬ (arena A Y E embed).Law bad := by
        rintro ⟨x, y, same, j, hj, diff⟩
        have hd : d (embed x) = d (embed y) := by simpa [bad] using same i hi
        apply diff
        simp [bad, hd]
      refine ⟨good, bad, ?_, ?_, ⟨fun _ => hb, fun _ => hg⟩⟩
      · intro j hj; funext x; simp [good, bad, hj]
      · intro j; exact Fin.elim0 j
    · have hf : coarse i = false := by cases h : coarse i <;> simp_all
      let good : PrimitiveRealization (signature A.State Y) :=
        ⟨fun j x => if j = i then d x else z, Fin.elim0⟩
      have hg : (arena A Y E embed).Law good := by
        refine ⟨a, b, ?_, i, hf, ?_⟩
        · intro j hj
          have hn : j ≠ i := by intro h; rw [h, hf] at hj; cases hj
          simp [good, hn]
        · simpa [good] using different
      refine ⟨good, constant z, ?_, ?_,
        ⟨fun _ => constant_rejected A Y E embed z, fun _ => hg⟩⟩
      · intro j hj; funext x; simp [good, constant, hj]
      · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

/-- No branch bit is discarded: None becomes four Nones and Some retains all bits. -/
def spread (x : Option Code) : Option Bool × Option Bool × Option Bool × Option Bool :=
  (x.map (fun b => b.1), x.map (fun b => b.2.1),
    x.map (fun b => b.2.2.1), x.map (fun b => b.2.2.2))

theorem spread_injective : Function.Injective spread := by
  intro a b
  cases a <;> cases b <;> simp [spread, Prod.ext_iff]

def localActual := split icInt icCF
def icActual := split (fun x => spread (icCoarse x)) (fun x => spread (icFine x))
def oiActual := split (fun x => spread (oiCoarse x)) (fun x => spread (oiFine x))
def localArena := arena icObjectArena Bool ICData id
def icArena := arena objectArena (Option Bool) ICData Sum.inl
def oiArena := arena objectArena (Option Bool) OIData Sum.inr

def localDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := localArena
  Domain := IC.Model

def icDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := icArena
  Domain := IC.Model

def oiDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := oiArena
  Domain := OI.Model

theorem local_law : localArena.Law localActual ↔
    LegacyCausalCoordinates.localLawArena.Law LegacyCausalCoordinates.localActual :=
  split_law icObjectArena Bool ICData id icInt icCF

theorem ic_law : icArena.Law icActual ↔
    LegacyCausalCoordinates.icLawArena.Law LegacyCausalCoordinates.icActual := by
  rw [show icActual = split (fun x => spread (icCoarse x))
    (fun x => spread (icFine x)) from rfl]
  exact (split_law _ _ _ _ _ _).trans (by
    change (∃ a b : ICData, spread (icCoarse (.inl a)) = spread (icCoarse (.inl b)) ∧
      spread (icFine (.inl a)) ≠ spread (icFine (.inl b))) ↔ _
    simp only [ne_eq, spread_injective.eq_iff]
    rfl)

theorem oi_law : oiArena.Law oiActual ↔
    LegacyCausalCoordinates.oiLawArena.Law LegacyCausalCoordinates.oiActual := by
  rw [show oiActual = split (fun x => spread (oiCoarse x))
    (fun x => spread (oiFine x)) from rfl]
  exact (split_law _ _ _ _ _ _).trans (by
    change (∃ a b : OIData, spread (oiCoarse (.inr a)) = spread (oiCoarse (.inr b)) ∧
      spread (oiFine (.inr a)) ≠ spread (oiFine (.inr b))) ↔ _
    simp only [ne_eq, spread_injective.eq_iff]
    rfl)

theorem local_bridge : LegacyPrimitiveRealization localArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) localActual :=
  ⟨LegacyCausalCoordinates.local_bridge.equivalence.trans local_law.symm⟩
theorem ic_bridge : LegacyPrimitiveRealization icArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) icActual :=
  ⟨LegacyCausalCoordinates.ic_bridge.equivalence.trans ic_law.symm⟩
theorem oi_bridge : LegacyPrimitiveRealization oiArena
    (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N) oiActual :=
  ⟨LegacyCausalCoordinates.oi_bridge.equivalence.trans oi_law.symm⟩

theorem local_variation : localArena.Law localActual ∧ ¬ localArena.Law (constant false) :=
  ⟨local_law.mpr local_positive, constant_rejected _ _ _ _ _⟩
theorem ic_variation : icArena.Law icActual ∧ ¬ icArena.Law (constant none) :=
  ⟨ic_law.mpr ic_positive, constant_rejected _ _ _ _ _⟩
theorem oi_variation : oiArena.Law oiActual ∧ ¬ oiArena.Law (constant none) :=
  ⟨oi_law.mpr oi_positive, constant_rejected _ _ _ _ _⟩

theorem local_sensitivity : FiniteSlotSensitivity localArena :=
  sensitivity icObjectArena Bool ICData id (fun b => b.1) false
    (false, false, false, false) (true, true, true, true) (by decide)
theorem ic_sensitivity : FiniteSlotSensitivity icArena :=
  sensitivity objectArena (Option Bool) ICData Sum.inl (fun x => Option.map (fun b => b.1) (icFine x)) none
    (false, false, false, false) (true, true, true, true) (by decide)
theorem oi_sensitivity : FiniteSlotSensitivity oiArena :=
  sensitivity objectArena (Option Bool) OIData Sum.inr (fun x => Option.map (fun b => b.1) (oiFine x)) none
    (false, (false, false), (false, false)) (false, (true, true), (true, true)) (by decide)

theorem local_dependence : ∀ i : Slot, ∃ x y : ICData,
    localActual.readout i x ≠ localActual.readout i y := by
  intro i
  refine ⟨(false, false, false, false), (true, true, true, true), ?_⟩
  fin_cases i <;> change (false : Bool) ≠ true <;> decide

theorem ic_dependence : ∀ i : Slot, ∃ x y : UnifiedData,
    icActual.readout i x ≠ icActual.readout i y := by
  intro i
  refine ⟨.inl (false, false, false, false), .inl (true, true, true, true), ?_⟩
  fin_cases i <;> change (some false : Option Bool) ≠ some true <;> decide

theorem oi_dependence : ∀ i : Slot, ∃ x y : UnifiedData,
    oiActual.readout i x ≠ oiActual.readout i y := by
  intro i
  refine ⟨.inr (false, (false, false), (false, false)),
    .inr (false, (true, true), (true, true)), ?_⟩
  fin_cases i <;> change (some false : Option Bool) ≠ some true <;> decide

/-- Both original observation relations survive separately on the whole
48-state coproduct, including pairs in different branches. -/
theorem ic_coarse_slots (x y : UnifiedData) :
    (∀ i, coarse i = true → icActual.readout i x = icActual.readout i y) ↔
      interventionCounterfactualUnifiedRealization.readout .intervention (unifiedEquiv.symm x) =
      interventionCounterfactualUnifiedRealization.readout .intervention (unifiedEquiv.symm y) :=
  (split_coarse _ _ x y).trans
    (spread_injective.eq_iff.trans (ic_coarse_transport x y))

theorem ic_fine_slots (x y : UnifiedData) :
    (∃ i, coarse i = false ∧ icActual.readout i x ≠ icActual.readout i y) ↔
      interventionCounterfactualUnifiedRealization.readout .counterfactual (unifiedEquiv.symm x) ≠
      interventionCounterfactualUnifiedRealization.readout .counterfactual (unifiedEquiv.symm y) :=
  (split_fine _ _ x y).trans
    ((not_congr spread_injective.eq_iff).trans (not_congr (ic_fine_transport x y)))

theorem oi_coarse_slots (x y : UnifiedData) :
    (∀ i, coarse i = true → oiActual.readout i x = oiActual.readout i y) ↔
      observationInterventionUnifiedRealization.readout .observation (unifiedEquiv.symm x) =
      observationInterventionUnifiedRealization.readout .observation (unifiedEquiv.symm y) :=
  (split_coarse _ _ x y).trans
    (spread_injective.eq_iff.trans (oi_coarse_transport x y))

theorem oi_fine_slots (x y : UnifiedData) :
    (∃ i, coarse i = false ∧ oiActual.readout i x ≠ oiActual.readout i y) ↔
      observationInterventionUnifiedRealization.readout .intervention (unifiedEquiv.symm x) ≠
      observationInterventionUnifiedRealization.readout .intervention (unifiedEquiv.symm y) :=
  (split_fine _ _ x y).trans
    ((not_congr spread_injective.eq_iff).trans (not_congr (oi_fine_transport x y)))

theorem ic_opposite_slots (b : OIData) (i : Slot) : icActual.readout i (.inr b) = none := by
  fin_cases i <;> rfl

theorem oi_opposite_slots (b : ICData) (i : Slot) : oiActual.readout i (.inl b) = none := by
  fin_cases i <;> rfl

#print axioms ic_coarse_slots
#print axioms ic_fine_slots
#print axioms oi_coarse_slots
#print axioms oi_fine_slots
#print axioms local_bridge
#print axioms ic_bridge
#print axioms oi_bridge
#print axioms sensitivity
#print axioms local_dependence
#print axioms ic_dependence
#print axioms oi_dependence
end Reg.Support.LegacyCausalSlots

open Reg.Support.LegacyCausalSlots LeanInformationAudit

register_information_template slotRealization
