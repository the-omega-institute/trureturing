/- GID: D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/IntegerRepresentatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical signed HF event archives realise every integer exactly. -/

import D5.S0.History.Spacetime.ArchiveCarrier
import D5.S0.History.Spacetime.IntegerEncoding
import D5.S0.History.Spacetime.CoordinateEncoding
import D5.S0.History.Spacetime.SourceTreeEncoding
import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives

open D5.S0.History.Spacetime
open ArchiveCarrier HFEncoding IntegerEncoding CoordinateEncoding SourceTreeEncoding
open ComplementCharge

noncomputable section
open scoped BigOperators
local instance : DecidableEq HF := Classical.decEq _

/- Utility is none: the construction and its proofs quantify over arbitrary
   integers and dimensions; zero emptiness is a boundary characterization.
   emptyRepresentative and U are literal definitions, not certified instances.
   This module contains no enumeration, checker or numerical reduction. -/

/- The first coordinate is a von Neumann natural code and the second is the
   fixed integer sign code.  This is the literal pair required by Definition 8. -/
def eventName (i : Nat) (positive : Bool) : HF :=
  pair (natCode i) (signCode positive)

def eventNames (n : Int) : Finset HF :=
  (Finset.univ : Finset (Fin (Int.natAbs n))).product Finset.univ |>.image
    (fun p => eventName p.1.val p.2)

def positiveNames (n : Int) : Finset HF :=
  (Finset.univ : Finset (Fin (Int.natAbs n))).image (fun i => eventName i.val true)

def negativeNames (n : Int) : Finset HF :=
  (Finset.univ : Finset (Fin (Int.natAbs n))).image (fun i => eventName i.val false)

def selectedNames (n : Int) : Finset HF :=
  match n with
  | .ofNat 0 => ∅
  | .ofNat (_ + 1) => positiveNames n
  | .negSucc _ => negativeNames n

theorem signCode_injective : Function.Injective signCode := by
  intro a b h
  exact sign_code_equiv.injective (Subtype.ext h)

theorem eventName_injective : Function.Injective (fun p : Nat × Bool => eventName p.1 p.2) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hp := pair_inj.mp h
  have hi : i = j := natCode_inj.mp hp.1
  have hb : b = c := signCode_injective hp.2
  exact Prod.ext hi hb

theorem eventPair_injective {m : Nat} :
    Function.Injective (fun p : Fin m × Bool => eventName p.1.val p.2) := by
  intro p q h
  exact Prod.ext (Fin.ext (natCode_inj.mp (pair_inj.mp h).1))
    (signCode_injective (pair_inj.mp h).2)

theorem eventNames_mem (n : Int) (i : Fin (Int.natAbs n)) (b : Bool) :
    eventName i.val b ∈ eventNames n := by
  unfold eventNames
  apply Finset.mem_image.mpr
  exact ⟨(i, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

theorem positiveNames_subset (n : Int) : positiveNames n ⊆ eventNames n := by
  intro e he
  unfold positiveNames at he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  exact eventNames_mem n i true

theorem negativeNames_subset (n : Int) : negativeNames n ⊆ eventNames n := by
  intro e he
  unfold negativeNames at he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  exact eventNames_mem n i false

theorem eventNames_card (n : Int) : (eventNames n).card = 2 * Int.natAbs n := by
  calc
    (eventNames n).card =
        ((Finset.univ : Finset (Fin (Int.natAbs n))).product Finset.univ).card := by
      apply Finset.card_image_of_injective
      intro p q h
      exact Prod.ext (Fin.ext (natCode_inj.mp (pair_inj.mp h).1))
        (signCode_injective (pair_inj.mp h).2)
    _ = 2 * Int.natAbs n := by simp [Finset.card_product, Nat.mul_comm]

theorem positiveNames_card (n : Int) : (positiveNames n).card = Int.natAbs n := by
  calc
    (positiveNames n).card =
        (Finset.univ : Finset (Fin (Int.natAbs n))).card := by
      apply Finset.card_image_of_injective
      intro i j h
      exact Fin.ext (natCode_inj.mp (pair_inj.mp h).1)
    _ = Int.natAbs n := by simp

theorem negativeNames_card (n : Int) : (negativeNames n).card = Int.natAbs n := by
  calc
    (negativeNames n).card =
        (Finset.univ : Finset (Fin (Int.natAbs n))).card := by
      apply Finset.card_image_of_injective
      intro i j h
      exact Fin.ext (natCode_inj.mp (pair_inj.mp h).1)
    _ = Int.natAbs n := by simp

def eventEquiv (n : Int) :
    (Fin (Int.natAbs n) × Bool) ≃ {e : HF // e ∈ eventNames n} :=
  Equiv.ofBijective
    (fun p => ⟨eventName p.1.val p.2, eventNames_mem n p.1 p.2⟩)
    ⟨by
      intro p q h
      exact eventPair_injective (congrArg Subtype.val h), by
      rintro ⟨e, he⟩
      unfold eventNames at he
      rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
      exact ⟨p, Subtype.ext rfl⟩⟩

def eventAttributes (d : Nat) (n : Int)
    (e : {e : HF // e ∈ eventNames n}) : Attributes d :=
  let p := (eventEquiv n).symm e
  { time := 0
    position := fun _ => 0
    positive := p.2
    source := FreeMagma.of p.1.val }

theorem eventAttributes_name (d : Nat) (n : Int) (i : Fin (Int.natAbs n)) (b : Bool) :
    eventAttributes d n ⟨eventName i.val b, eventNames_mem n i b⟩ =
      { time := 0, position := fun _ => 0, positive := b,
        source := FreeMagma.of i.val } := by
  have hsub :
      (⟨eventName i.val b, eventNames_mem n i b⟩ : {e : HF // e ∈ eventNames n}) =
        eventEquiv n (i, b) := by
    apply Subtype.ext
    rfl
  rw [hsub]
  simp [eventAttributes]

abbrev representativeArchive (d : Nat) (n : Int) : Archive d where
  events := eventNames n
  attributes := eventAttributes d n
  causal := fun _ _ => False
  irrefl := by simp
  trans := by simp
  time_lt := by simp

abbrev representativeContext (d : Nat) (n : Int) : Context d where
  archive := representativeArchive d n
  current := Finset.univ

def selectedEmbedding (d : Nat) (n : Int) :
    (selectedNames n) ↪ (representativeArchive d n).Event where
  toFun e := ⟨e.val, by
    cases n with
    | ofNat k =>
      cases k with
      | zero => exfalso; simpa [selectedNames] using e.property
      | succ k => exact positiveNames_subset _ e.property
    | negSucc k => exact negativeNames_subset _ e.property⟩
  inj' x y h := by
    apply Subtype.ext
    exact congrArg (fun z : (representativeArchive d n).Event => z.val) h

def selectedEvents (d : Nat) (n : Int) : Finset (representativeArchive d n).Event :=
  Finset.univ.map (selectedEmbedding d n)

theorem selectedEvents_card (d : Nat) (n : Int) :
    (selectedEvents d n).card = (selectedNames n).card := by
  unfold selectedEvents
  rw [Finset.card_map, Finset.card_univ, Fintype.card_coe]

theorem selected_positive_contribution (d k : Nat)
    (e : selectedNames (Int.ofNat (Nat.succ k))) :
    contribution (representativeContext d (Int.ofNat (Nat.succ k)))
      (selectedEmbedding d (Int.ofNat (Nat.succ k)) e) = 1 := by
  have hp : e.val ∈ positiveNames (Int.ofNat (Nat.succ k)) := by
    simpa [selectedNames] using e.property
  rcases Finset.mem_image.mp hp with ⟨i, hi, he⟩
  have hs : (selectedEmbedding d (Int.ofNat (Nat.succ k)) e :
      (representativeArchive d (Int.ofNat (Nat.succ k))).Event) =
      ⟨eventName i.val true, eventNames_mem _ i true⟩ := by
    apply Subtype.ext
    exact he.symm
  rw [hs]
  change (if (eventAttributes d (Int.ofNat (Nat.succ k))
      ⟨eventName i.val true, eventNames_mem _ i true⟩).positive then 1 else -1) = 1
  rw [eventAttributes_name]
  simp

theorem selected_negative_contribution (d k : Nat)
    (e : selectedNames (Int.negSucc k)) :
    contribution (representativeContext d (Int.negSucc k))
      (selectedEmbedding d (Int.negSucc k) e) = -1 := by
  have hp : e.val ∈ negativeNames (Int.negSucc k) := by
    simpa [selectedNames] using e.property
  rcases Finset.mem_image.mp hp with ⟨i, hi, he⟩
  have hs : (selectedEmbedding d (Int.negSucc k) e :
      (representativeArchive d (Int.negSucc k)).Event) =
      ⟨eventName i.val false, eventNames_mem _ i false⟩ := by
    apply Subtype.ext
    exact he.symm
  rw [hs]
  change (if (eventAttributes d (Int.negSucc k)
      ⟨eventName i.val false, eventNames_mem _ i false⟩).positive then 1 else -1) = -1
  rw [eventAttributes_name]
  simp

def representative (d : Nat) (n : Int) : Rich d :=
  let c := representativeContext d n
  ⟨c, ⟨selectedEvents d n, by
    intro e he
    change e ∈ (Finset.univ : Finset c.Event)
    exact Finset.mem_univ _⟩⟩

theorem selectedEvents_mem_iff (d : Nat) (n : Int)
    (e : (representativeArchive d n).Event) :
    e ∈ selectedEvents d n ↔ e.val ∈ selectedNames n := by
  unfold selectedEvents
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨u, _, hu⟩
    have huv : u.val = e.val := congrArg Subtype.val hu
    exact huv ▸ u.property
  · intro he
    apply Finset.mem_map.mpr
    refine ⟨⟨e.val, he⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rfl

theorem selectedNames_of_positive {n : Int} (h : 0 < n) :
    selectedNames n = positiveNames n := by
  cases n with
  | ofNat k =>
    cases k with
    | zero => simp at h
    | succ k => rfl
  | negSucc k => simp at h

theorem selectedNames_of_negative {n : Int} (h : n < 0) :
    selectedNames n = negativeNames n := by
  cases n with
  | ofNat k => exact False.elim ((not_lt_of_ge (Int.natCast_nonneg k)) h)
  | negSucc k => rfl

theorem representative_selection_positive_iff {d : Nat} {n : Int}
    (h : 0 < n) (e : (representativeArchive d n).Event) :
    e ∈ (representative d n).2.val ↔ e.val ∈ positiveNames n := by
  change e ∈ selectedEvents d n ↔ _
  rw [selectedEvents_mem_iff, selectedNames_of_positive h]

theorem representative_selection_negative_iff {d : Nat} {n : Int}
    (h : n < 0) (e : (representativeArchive d n).Event) :
    e ∈ (representative d n).2.val ↔ e.val ∈ negativeNames n := by
  change e ∈ selectedEvents d n ↔ _
  rw [selectedEvents_mem_iff, selectedNames_of_negative h]

@[simp] theorem representative_archive_eq (d : Nat) (n : Int) :
    (representative d n).1.archive = representativeArchive d n := by rfl

@[simp] theorem representative_current_eq (d : Nat) (n : Int) :
    (representative d n).1.current = Finset.univ := by rfl

notation "ι(" n ")" => representative 3 n

def emptyRepresentative : Rich 3 := representative 3 0

/- U is the literal source object. Its archive, current and selection sizes
   specialize the general cardinality theorems at d=3,n=1. -/
def U : Rich 3 := representative 3 1

theorem representative_archive_card (d : Nat) (n : Int) :
    (representativeArchive d n).events.card = 2 * Int.natAbs n :=
  eventNames_card n

theorem representative_current_card (d : Nat) (n : Int) :
    (representativeContext d n).current.card = 2 * Int.natAbs n := by
  change (Finset.univ : Finset {e : HF // e ∈ eventNames n}).card = _
  rw [Finset.card_univ, Fintype.card_coe]
  exact eventNames_card n

theorem representative_selected_card (d : Nat) (n : Int) :
    (representative d n).2.val.card = Int.natAbs n := by
  change (selectedEvents d n).card = _
  rw [selectedEvents_card]
  cases n with
  | ofNat k =>
    cases k with
    | zero => simp [selectedNames]
    | succ k => simpa [selectedNames] using positiveNames_card (.ofNat (k + 1))
  | negSucc k => simpa [selectedNames] using negativeNames_card (.negSucc k)

theorem representative_background_zero (d : Nat) (n : Int) :
    Balanced (representativeContext d n) := by
  unfold Balanced background charge
  change (∑ e : {e : HF // e ∈ eventNames n},
    contribution (representativeContext d n) e) = 0
  rw [← Equiv.sum_comp (eventEquiv n)]
  rw [Fintype.sum_prod_type]
  simp [eventAttributes, eventEquiv, contribution]

theorem representative_readout (d : Nat) (n : Int) :
    q (representative d n) = n := by
  change charge (representativeContext d n) (selectedEvents d n) = n
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      have hs : selectedEvents d 0 = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [selectedEvents_card]
        simp [selectedNames]
      change charge (representativeContext d 0) (selectedEvents d 0) = 0
      rw [hs]
      simp [charge]
    | succ k =>
      unfold selectedEvents charge
      rw [Finset.sum_map]
      simp_rw [selected_positive_contribution d k]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe]
      have hcard : (selectedNames (Int.ofNat (Nat.succ k))).card = Nat.succ k := by
        have hp := positiveNames_card (Int.ofNat (Nat.succ k))
        have hn : ((k : Int) + 1).natAbs = k + 1 := by omega
        simpa [selectedNames, hn, Nat.succ_eq_add_one] using hp
      simpa [Nat.succ_eq_add_one] using congrArg Int.ofNat hcard
  | negSucc k =>
    unfold selectedEvents charge
    rw [Finset.sum_map]
    simp_rw [selected_negative_contribution d k]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe]
    have hcard : (selectedNames (Int.negSucc k)).card = Nat.succ k := by
      simpa [selectedNames] using negativeNames_card (Int.negSucc k)
    have hi := congrArg Int.ofNat hcard
    simpa [Int.negSucc_eq] using congrArg Neg.neg hi

theorem representative_balanced (d : Nat) (n : Int) :
    Balanced (representative d n).1 :=
  representative_background_zero d n

theorem representative_zero_empty (d : Nat) :
    (representative d 0).1.archive.events = ∅ ∧
      (representative d 0).1.current = ∅ ∧ (representative d 0).2.val = ∅ := by
  have hc : (representative d 0).1.current.card = 0 := by
    rw [representative_current_eq]
    simpa using representative_current_card d 0
  have hs : (representative d 0).2.val.card = 0 := by
    simpa using representative_selected_card d 0
  exact ⟨Finset.card_eq_zero.mp (by simpa [representative_archive_eq] using representative_archive_card d 0),
    Finset.card_eq_zero.mp hc, Finset.card_eq_zero.mp hs⟩

end
end D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
