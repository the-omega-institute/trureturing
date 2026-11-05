/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp native predecessor-row fibers at one update with exact supplementary capacity. -/

import D5.S3.Arith.FibonacciAtomic.FiniteHereditaryPatternRealization
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
import D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
import D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
import D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address readout leaves)
open ActualLeafHistoryRigidity (subtree)
open FiniteHereditaryPatternRealization (B_T hole locate hole_locate)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder
open NativeCutFibers
open NativePredecessorRowRecovery (H)
open SourceCoordinates.IntrinsicSubstitutionCoordinates (no_alpha)

/-- A right child of each existing comb hole. -/
def position (n : Nat) (i : Fin (n + 1)) : Address := hole n i ++ [true]

def cut (n : Nat) : CutSet := Finset.univ.image (position n)

/-- An old beta or an old pair with the native alpha on the left. -/
def site (z : Source) (selected : Bool) : Source :=
  if selected then .of false else .mul (.of true) z

/-- Every selector refers to the same finite context and public epoch one. -/
def origin (n : Nat) (z : Fin (n + 1) → Source) (a : Option (Fin (n + 1))) : Source :=
  B_T n (fun i => site (z i) (decide (a = some i)))

theorem comb_at (n : Nat) (X : Fin (n + 1) → Source) (i : Fin (n + 1)) :
    subtree (hole n i) (B_T n X) = some (X i) := by
  have reads (w : Address) : readout (hole n i ++ w) (B_T n X) = readout w (X i) := by
    rw [FiniteHereditaryPatternRealization.result.1, hole_locate]
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases ht : subtree (hole n i) (B_T n X) with
  | none =>
      have h := reads []
      rw [app, ht] at h
      cases hx : X i with
      | of b => cases b <;> simp [hx, readout] at h
      | mul l r => simp [hx, readout] at h
  | some t =>
      have eq : t = X i := ActualTreeReadoutAcquisition.source_foundation.2.2.1 _ _ (by
        intro w _
        have h := reads w
        rw [app, ht] at h
        exact h)
      simp [eq]

private theorem position_injective (n : Nat) : Function.Injective (position n) := by
  intro i j eq
  exact (FiniteHereditaryPatternRealization.result.2.2.2.1 n i j [true] [true] eq).1

private theorem cut_prefix_free (n : Nat) : CutPrefixFree (cut n) := by
  rintro p hp q hq ⟨s, eq⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  have e : hole n i ++ ([true] ++ s) = hole n j ++ [true] := by
    simpa [position, List.append_assoc] using eq
  have h := FiniteHereditaryPatternRealization.result.2.2.2.1 n i j _ _ e
  exact congrArg (position n) h.1

private theorem site_exterior (P : CutSet) (a : Address) (z : Source) (b : Bool)
    (ha : a ∉ P) (hl : a ++ [false] ∉ P) (hr : a ++ [true] ∈ P) :
    cutExterior P a (substitution (site z b)) =
      cutExterior P a (substitution (site z false)) := by
  have stop (t : Source) : cutExterior P (a ++ [true]) t = .of (.inr (a ++ [true])) := by
    cases t <;> simp [cutExterior, hr]
  cases b <;> simp [site, substitution, cutExterior, ha, hl, hr, stop]

/-- Uniform child-cut installation through the existing arbitrary-size context.
The old constructor may change at every site; the entire current exterior does not. -/
private theorem installation (n : Nat) (z : Fin (n + 1) → Source)
    (s : Fin (n + 1) → Bool) (P : CutSet) (a : Address)
    (cuts : ∀ w : Address, a ++ w ∈ P ↔ ∃ i, w = position n i) :
    cutExterior P a (substitution (B_T n (fun i => site (z i) (s i)))) =
      cutExterior P a (substitution (B_T n (fun i => site (z i) false))) := by
  induction n generalizing a with
  | zero =>
      have ha : a ∉ P := by simpa [position, hole] using cuts []
      have hl : a ++ [false] ∉ P := by simpa [position, hole] using cuts [false]
      have hr : a ++ [true] ∈ P := by simpa [position, hole] using cuts [true]
      exact site_exterior P a (z 0) (s 0) ha hl hr
  | succ n ih =>
      have ha : a ∉ P := by
        intro mem
        obtain ⟨i, hi⟩ := (cuts []).mp (by simpa using mem)
        have len := congrArg List.length hi
        simp [position] at len
      have cl : ∀ w : Address, (a ++ [false]) ++ w ∈ P ↔ w = [true] := by
        intro w
        rw [List.append_assoc, cuts]
        simp [position, hole, Fin.exists_fin_succ]
      have cr : ∀ w : Address, (a ++ [true]) ++ w ∈ P ↔ ∃ i, w = position n i := by
        intro w
        rw [List.append_assoc, cuts]
        simp [position, hole, Fin.exists_fin_succ]
      have left : cutExterior P (a ++ [false]) (substitution (site (z 0) (s 0))) =
          cutExterior P (a ++ [false]) (substitution (site (z 0) false)) := by
        exact site_exterior P (a ++ [false]) (z 0) (s 0)
          (by simpa using cl []) (by simpa using cl [false]) (by simpa using cl [true])
      change cutExterior P a (.mul (substitution (site (z 0) (s 0)))
        (substitution (B_T n (fun i => site (z i.succ) (s i.succ))))) =
        cutExterior P a (.mul (substitution (site (z 0) false))
          (substitution (B_T n (fun i => site (z i.succ) false))))
      simp only [cutExterior, ha, ↓reduceIte]
      exact congrArg₂ FreeMagma.mul left
        (ih (fun i => z i.succ) (fun i => s i.succ) (a ++ [true]) cr)


private theorem current_at (n : Nat) (z : Fin (n + 1) → Source)
    (a : Option (Fin (n + 1))) (i : Fin (n + 1)) :
    subtree (position n i) (substitution (origin n z a)) =
      some (if a = some i then .of true else substitution (z i)) := by
  have atSite := NativeDepthPatterns.original_present_transport 1 (hole n i)
    (origin n z a) (site (z i) (decide (a = some i))) (comb_at n _ i)
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [position, app]
  simp only [Function.iterate_one] at atSite
  rw [atSite]
  by_cases h : a = some i <;> simp [site, h, substitution, subtree]

private theorem old_at (n : Nat) (z : Fin (n + 1) → Source)
    (a : Option (Fin (n + 1))) (i : Fin (n + 1)) :
    subtree (position n i) (origin n z a) = if a = some i then none else some (z i) := by
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [position, app]
  change (subtree (hole n i) (B_T n (fun j => site (z j) (decide (a = some j))))).bind
    (subtree [true]) = _
  rw [comb_at]
  by_cases h : a = some i <;> simp [site, h, subtree]

private theorem payload_injective (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) (a : Option (Fin (n + 1))) :
    Function.Injective (fun i => if a = some i then (FreeMagma.of true : Source)
      else substitution (z i)) := by
  have inj := SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
    ⟨substitution.map_mul, fun _ => rfl⟩
  intro i j eq
  dsimp only at eq
  by_cases hi : a = some i <;> by_cases hj : a = some j
  · exact Option.some.inj (hi.symm.trans hj)
  · rw [if_pos hi, if_neg hj] at eq
    exact False.elim (no_alpha (z j) eq.symm)
  · rw [if_neg hi, if_pos hj] at eq
    exact False.elim (no_alpha (z i) eq)
  · rw [if_neg hi, if_neg hj] at eq
    exact hz (inj eq)

private theorem ordered_mem (n : Nat) (z : Fin (n + 1) → Source)
    (a : Option (Fin (n + 1))) (p : Address) :
    p ∈ orderedHoles (cut n) (substitution (origin n z a)) ↔ p ∈ cut n := by
  rw [orderedHoles_mem _ (cut_prefix_free n)]
  constructor
  · exact And.left
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hp, by rw [current_at]; rfl⟩

private theorem current_row (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) (a : Option (Fin (n + 1))) :
    canonicalRow (cut n) (substitution (origin n z a)) =
      canonicalRow (cut n) (substitution (origin n z none)) := by
  have exterior := installation n z (fun i => decide (a = some i)) (cut n) []
    (by intro w; simp [cut, position, eq_comm])
  apply (canonicalRow_record_iff _ (cut_prefix_free n) _ _).mpr
  apply Prod.ext exterior
  ext pq
  rcases pq with ⟨p, q⟩
  simp only [literalRecord, actualPartition, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, List.mem_toFinset, ordered_mem]
  constructor
  · rintro ⟨⟨hp,hq⟩, eq⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    rw [current_at, current_at, Option.some.injEq] at eq
    have ij := payload_injective n z hz a eq
    subst j
    exact ⟨⟨by simp [cut], by simp [cut]⟩, rfl⟩
  · rintro ⟨⟨hp,hq⟩, eq⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    rw [current_at, current_at, Option.some.injEq] at eq
    have ij := payload_injective n z hz none eq
    subst j
    exact ⟨⟨by simp [cut], by simp [cut]⟩, rfl⟩

private theorem old_support (n : Nat) (z : Fin (n + 1) → Source)
    (a : Option (Fin (n + 1))) :
    H (cut n) (origin n z a) =
      match a with | none => cut n | some i => (cut n).erase (position n i) := by
  ext p
  rw [H, List.mem_toFinset, canonicalRow_reached _ (cut_prefix_free n)]
  cases a with
  | none =>
      constructor
      · exact And.left
      · intro hp
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
        exact ⟨hp, by rw [old_at]; rfl⟩
  | some j =>
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hp, present⟩
        refine ⟨?_, hp⟩
        intro eq
        subst p
        simp [old_at] at present
      · rintro ⟨ne, hp⟩
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
        have ij : i ≠ j := by intro e; subst i; exact ne rfl
        have sel : (some j : Option (Fin (n + 1))) ≠ some i := by
          intro e; exact ij (Option.some.inj e).symm
        exact ⟨hp, by rw [old_at, if_neg sel]; rfl⟩

/-- The common current row, including every ordered bracket and disequality. -/
def current (n : Nat) (z : Fin (n + 1) → Source) : LiteralRow :=
  canonicalRow (cut n) (substitution (origin n z none))

/-- Only occurring names are counted; their raw ordinal values may be sparse. -/
def className (n : Nat) (z : Fin (n + 1) → Source) (i : Fin (n + 1)) : Nat :=
  classOrdinal (cut n) (substitution (origin n z none)) (position n i)

private theorem classes_card (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) : Nat.card (Classes (current n z)) = n + 1 := by
  have reached (i : Fin (n + 1)) :
      position n i ∈ orderedHoles (cut n) (substitution (origin n z none)) :=
    (ordered_mem n z none _).mpr (by simp [cut])
  have names : labels (current n z) = Finset.univ.image (className n z) := by
    rw [current, labels_canonical]
    have sets : (orderedHoles (cut n) (substitution (origin n z none))).toFinset = cut n := by
      ext p; simp [ordered_mem]
    rw [sets, cut, Finset.image_image]
    rfl
  have inj : Function.Injective (className n z) := by
    intro i j eq
    have equal := (classOrdinal_eq_iff _ _ (reached i) (reached j)).mp eq
    rw [current_at, current_at, Option.some.injEq] at equal
    exact payload_injective n z hz none equal
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, names, Finset.card_image_of_injective _ inj]
  simp

theorem right_birth (q : Address) (v : Source)
    (present : (subtree (q ++ [true]) (substitution v)).isSome) :
    subtree (q ++ [true]) v = none ↔
      subtree (q ++ [true]) (substitution v) = some (.of true) := by
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have absent := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.1
  constructor
  · intro missing
    obtain ⟨r, b, w, old, eq, ne⟩ := (absent v (q ++ [true])).mp missing
    have transport : subtree r (substitution v) = some (substitution (.of b)) := by
      simpa only [Function.iterate_one] using
        NativeDepthPatterns.original_present_transport 1 r v (.of b) old
    have atRead : subtree (q ++ [true]) (substitution v) =
        subtree w (substitution (.of b)) := by
      rw [eq, app, transport]
      rfl
    rw [atRead] at present ⊢
    cases w with
    | nil => exact False.elim (ne rfl)
    | cons d w =>
        cases b with
        | true => cases d <;> simp [substitution, subtree] at present
        | false =>
            cases w with
            | cons e w => cases d <;> simp [substitution, subtree] at present
            | nil =>
                cases d with
                | true => rfl
                | false =>
                    have reversed := congrArg List.reverse eq
                    simp at reversed
  · intro currentAlpha
    cases old : subtree (q ++ [true]) v with
    | none => rfl
    | some t =>
        have transport : subtree (q ++ [true]) (substitution v) =
            some (substitution t) := by
          simpa only [Function.iterate_one] using
            NativeDepthPatterns.original_present_transport 1 (q ++ [true]) v t old
        exact False.elim (no_alpha t (Option.some.inj (transport.symm.trans currentAlpha)))


private theorem old_rows_injective (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) :
    Function.Injective (fun a => canonicalRow (cut n) (origin n z a)) := by
  have supports := fun a => old_support n z a
  intro a b eq
  have hs := (NativePredecessorRowRecovery.native_predecessor_row_recovery _
    (cut_prefix_free n)).2 (origin n z a) (origin n z b)
    ((current_row n z hz a).trans (current_row n z hz b).symm)
  have sets := hs.mp eq
  rw [supports a, supports b] at sets
  cases a with
  | none => cases b with
    | none => rfl
    | some j =>
        dsimp only at sets
        have hj : position n j ∈ cut n := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        rw [sets] at hj
        simp at hj
  | some i => cases b with
    | none =>
        dsimp only at sets
        have hi : position n i ∈ cut n := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        rw [← sets] at hi
        simp at hi
    | some j =>
        dsimp only at sets
        apply congrArg some
        apply position_injective n
        by_contra ne
        have hi : position n i ∈ (cut n).erase (position n j) :=
          Finset.mem_erase.mpr ⟨ne, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
        rw [← sets] at hi
        simp at hi

/-- All finite actual origins with exactly the retained current row. -/
abbrev ActualPredecessors (n : Nat) (z : Fin (n + 1) → Source) :=
  {v : Source // canonicalRow (cut n) (substitution v) = current n z}

private theorem fiber_present (n : Nat) (z : Fin (n + 1) → Source)
    (v : ActualPredecessors n z) (i : Fin (n + 1)) :
    (subtree (position n i) (substitution v.val)).isSome := by
  have reached := (canonicalRow_reached _ (cut_prefix_free n)
    (substitution (origin n z none)) (position n i)).mpr
    ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, by rw [current_at]; rfl⟩
  change position n i ∈ holeAddresses [] (current n z) at reached
  rw [← v.property] at reached
  exact ((canonicalRow_reached _ (cut_prefix_free n) _ _).mp reached).2

private theorem fiber_values_injective (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) (v : ActualPredecessors n z) :
    Function.Injective (fun i => subtree (position n i) (substitution v.val)) := by
  intro i j eq
  have pi : position n i ∈ cut n := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have pj : position n j ∈ cut n := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have names := (canonicalRow_partition _ (cut_prefix_free n) (substitution v.val)
    _ _ pi pj (fiber_present n z v i) (fiber_present n z v j)).1.mpr eq
  rw [v.property] at names
  have same := (canonicalRow_partition _ (cut_prefix_free n)
    (substitution (origin n z none)) _ _ pi pj
    (by rw [current_at]; rfl) (by rw [current_at]; rfl)).1.mp names
  rw [current_at, current_at, Option.some.injEq] at same
  exact payload_injective n z hz none same

private theorem exhaustive (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) (v : ActualPredecessors n z) :
    ∃ a : Option (Fin (n + 1)), canonicalRow (cut n) v.val =
      canonicalRow (cut n) (origin n z a) := by
  have old (i : Fin (n + 1)) :
      subtree (position n i) v.val = none ↔
        subtree (position n i) (substitution v.val) = some (.of true) :=
    right_birth (hole n i) v.val (fiber_present n z v i)
  have support : ∀ p : Address, p ∈ H (cut n) v.val ↔
      p ∈ cut n ∧ (subtree p v.val).isSome := by
    intro p; simp only [H, List.mem_toFinset, canonicalRow_reached _ (cut_prefix_free n)]
  have rows (a : Option (Fin (n + 1))) (eq : H (cut n) v.val = H (cut n) (origin n z a)) :
      canonicalRow (cut n) v.val = canonicalRow (cut n) (origin n z a) :=
    (NativePredecessorRowRecovery.native_predecessor_row_recovery _ (cut_prefix_free n)).2
      _ _ (v.property.trans (current_row n z hz a).symm) |>.mpr eq
  by_cases existsAlpha : ∃ i, subtree (position n i) (substitution v.val) = some (.of true)
  · obtain ⟨i, hi⟩ := existsAlpha
    refine ⟨some i, rows (some i) ?_⟩
    rw [old_support]
    ext p
    rw [support, Finset.mem_erase]
    constructor
    · rintro ⟨hp, present⟩
      refine ⟨?_, hp⟩
      intro eq; subst p
      rw [(old i).mpr hi] at present
      cases present
    · rintro ⟨ne, hp⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      have present : (subtree (position n j) v.val).isSome := by
        cases h : subtree (position n j) v.val with
        | some t => rfl
        | none =>
            have currentAlpha := (old j).mp h
            have eqij := fiber_values_injective n z hz v (hi.trans currentAlpha.symm)
            exact False.elim (ne (congrArg (position n) eqij.symm))
      exact ⟨hp, present⟩
  · refine ⟨none, rows none ?_⟩
    rw [old_support]
    ext p
    rw [support]
    constructor
    · exact And.left
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      have present : (subtree (position n i) v.val).isSome := by
        cases h : subtree (position n i) v.val with
        | some t => rfl
        | none => exact False.elim (existsAlpha ⟨i, (old i).mp h⟩)
      exact ⟨hp, present⟩

/-- A supplementary configuration and a decoder correct on the entire actual
fiber. The decoder receives no native source and makes no new source queries. -/
def Encodable (n : Nat) (z : Fin (n + 1) → Source) (S : Type) : Prop :=
  ∃ encode : ActualPredecessors n z → S, ∃ decode : S → LiteralRow,
    ∀ v, decode (encode v) = canonicalRow (cut n) v.val

private theorem encoding_capacity (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) (S : Type) [Fintype S] :
    Encodable n z S ↔ n + 2 ≤ Fintype.card S := by
  constructor
  · rintro ⟨encode, decode, correct⟩
    let family (a : Option (Fin (n + 1))) : ActualPredecessors n z :=
      ⟨origin n z a, current_row n z hz a⟩
    have injective : Function.Injective (fun a => encode (family a)) := by
      intro a b eq
      apply old_rows_injective n z hz
      exact (correct (family a)).symm.trans
        ((congrArg decode eq).trans (correct (family b)))
    have bound :=
      D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound.finite_identification_capacity_bound
        (fun _ : Unit => S) (fun a _ => encode (family a)) (by
          intro a b eq; exact injective (congrFun eq ()))
    simp [D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound.Cap,
      Nat.card_eq_fintype_card] at bound
    exact bound
  · intro bound
    let X := Option (Fin (n + 1))
    have bound' : Fintype.card X ≤ Fintype.card S := by
      change Fintype.card (Option (Fin (n + 1))) ≤ Fintype.card S
      rw [Fintype.card_option, Fintype.card_fin]
      omega
    let emb : X → S := fun a => (Fintype.equivFin S).symm
      ⟨(Fintype.equivFin X a).val,
        Nat.lt_of_lt_of_le (Fintype.equivFin X a).isLt bound'⟩
    have inj : Function.Injective emb := by
      intro a b eq
      apply (Fintype.equivFin X).injective
      apply Fin.ext
      have h := congrArg (fun t => (Fintype.equivFin S t).val) eq
      simpa [emb] using h
    let select (v : ActualPredecessors n z) : X := Classical.choose (exhaustive n z hz v)
    let support (a : X) : CutSet :=
      match a with | none => cut n | some i => (cut n).erase (position n i)
    refine ⟨fun v => emb (select v), fun t =>
      (NativePredecessorRowRecovery.back (current n z)
        (support (Function.invFun emb t))).getD (.of (.inl true)), ?_⟩
    intro v
    dsimp only
    rw [Function.leftInverse_invFun inj]
    have recover :=
      (NativePredecessorRowRecovery.native_predecessor_row_recovery _ (cut_prefix_free n)).1
        (origin n z (select v))
    rw [current_row n z hz (select v), old_support] at recover
    change NativePredecessorRowRecovery.back (current n z) (support (select v)) =
      some (canonicalRow (cut n) (origin n z (select v))) at recover
    rw [recover, Option.getD_some]
    exact (Classical.choose_spec (exhaustive n z hz v)).symm

/-- Clause-complete sharpness on all actual origins sharing the complete row.
Supplementary capacity is conditional information, not an acquisition algorithm. -/
def Sharp (n : Nat) (z : Fin (n + 1) → Source)
    (oldRows : Option (Fin (n + 1)) → LiteralRow) : Prop :=
  CutPrefixFree (cut n) ∧
  (∀ a, canonicalRow (cut n) (substitution (origin n z a)) = current n z) ∧
  Nat.card (Classes (current n z)) = n + 1 ∧
  (∀ a, H (cut n) (origin n z a) =
    match a with | none => cut n | some i => (cut n).erase (position n i)) ∧
  Function.Injective oldRows ∧
  (∀ r, r ∈ Finset.univ.image oldRows ↔
    ∃ v : ActualPredecessors n z, canonicalRow (cut n) v.val = r) ∧
  (Finset.univ.image oldRows).card = n + 2 ∧
  (∀ m, Encodable n z (Fin m) ↔ n + 2 ≤ m) ∧
  (∀ b, Encodable n z (Fin b → Bool) ↔ Nat.clog 2 (n + 2) ≤ b)

/-- An arbitrary injective native tag family realizes the full sharp predecessor
fiber at epoch one, with exact supplementary configurations and binary width. -/
theorem native_sharp_predecessor_fiber (n : Nat) (z : Fin (n + 1) → Source)
    (hz : Function.Injective z) :
    Sharp n z (fun a => canonicalRow (cut n) (origin n z a)) := by
  refine ⟨cut_prefix_free n, current_row n z hz, classes_card n z hz,
    old_support n z, old_rows_injective n z hz, ?_, ?_, ?_, ?_⟩
  · intro r
    constructor
    · intro mem
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp mem
      exact ⟨⟨origin n z a, current_row n z hz a⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨a, eq⟩ := exhaustive n z hz v
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, eq.symm⟩
  · rw [Finset.card_image_of_injective _ (old_rows_injective n z hz)]
    simp
  · intro m
    simpa using encoding_capacity n z hz (Fin m)
  · intro b
    simpa [Nat.clog_le_iff_le_pow (show 1 < 2 by decide)] using
      encoding_capacity n z hz (Fin b → Bool)

#print axioms installation
#print axioms right_birth
#print axioms native_sharp_predecessor_fiber
end D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
