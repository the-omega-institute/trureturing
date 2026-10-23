/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Computable occurrence repair and exact native predecessor-row recovery. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder

/-- The old reached support is extracted from the complete old row. -/
def H (P : CutSet) (v : Source) : CutSet :=
  (holeAddresses [] (canonicalRow P v)).toFinset

/-- Opaque substitution fixes markers and acts natively on concrete leaves. -/
def sigma : LiteralRow →ₙ* LiteralRow := FreeMagma.lift fun x =>
  match x with
  | .inl true => .of (.inl false)
  | .inl false => .mul (.of (.inl false)) (.of (.inl true))
  | .inr n => .of (.inr n)

/-- Repair visits occurrences, rather than current equality classes. Old
markers remain opaque and are renamed on the restricted ordered support.
A newborn root has no final edge and is rejected. -/
def repairAt (C : LiteralRow) (O : CutSet) : Address → LiteralRow → Option LiteralRow
  | _, .of (.inl b) => some (.of (.inl b))
  | a, .of (.inr _) =>
      if a ∈ O then some (.of (.inr (decoderClass O C a)))
      else a.getLast?.map (fun d => .of (.inl d))
  | a, .mul l r => do
      let l' ← repairAt C O (a ++ [false]) l
      let r' ← repairAt C O (a ++ [true]) r
      pure (.mul l' r')

/-- Finite repair reads only the supplied row and old occurrence set. -/
def repair (C : LiteralRow) (O : CutSet) : Option LiteralRow := repairAt C O [] C

/-- The special beta/alpha block is parsed before an ordinary ordered pair. -/
def delta : LiteralRow → Option LiteralRow
  | .of (.inl false) => some (.of (.inl true))
  | .of (.inl true) => none
  | .of (.inr n) => some (.of (.inr n))
  | .mul l r =>
      if l = .of (.inl false) ∧ r = .of (.inl true) then some (.of (.inl false))
      else do
        let l' ← delta l
        let r' ← delta r
        pure (.mul l' r')

/-- Uniform partial decoder. No source witness is a runtime argument. -/
def back (C : LiteralRow) (O : CutSet) : Option LiteralRow := (repair C O).bind delta

private theorem sigma_not_alpha (t : LiteralRow) : sigma t ≠ .of (.inl true) := by
  cases t with
  | of x => cases x with
    | inl b =>
        cases b <;> simp only [sigma, FreeMagma.lift_of] <;> intro h <;> cases h
    | inr n => simp only [sigma, FreeMagma.lift_of]; intro h; cases h
  | mul l r => simp only [map_mul, FreeMagma.mul_eq]; intro h; cases h

private theorem delta_sigma (t : LiteralRow) : delta (sigma t) = some t := by
  induction t with
  | of x => cases x with
    | inl b => cases b <;> simp [sigma, FreeMagma.lift_of, delta]
    | inr n => simp [sigma, FreeMagma.lift_of, delta]
  | mul l r ihl ihr =>
      simp [map_mul, FreeMagma.mul_eq, delta, sigma_not_alpha r, ihl, ihr]

private theorem current_at_old (P : CutSet) (hP : CutPrefixFree P) (v : Source)
    (p : Address) (hp : p ∈ H P v) :
    rowAt p (canonicalRow P (substitution v)) =
      some (.of (.inr (classOrdinal P (substitution v) p))) := by
  have reached := (canonicalRow_reached P hP v p).mp (by simpa [H] using hp)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp reached.2
  have transport : subtree p (substitution v) = some (substitution t) := by
    simpa using NativeDepthPatterns.original_present_transport 1 p v t ht
  rw [canonicalRow_at_cut P hP _ p reached.1, transport]
  rfl

private theorem old_decoder_holes (P : CutSet) (hP : CutPrefixFree P) (v : Source) :
    decoderHoles (H P v) (canonicalRow P (substitution v)) = orderedHoles P v := by
  unfold decoderHoles orderedHoles
  rw [← literalRow_hole_support P v]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro p hp
  rw [current_at_old P hP v p hp]
  rfl

private theorem old_decoder_class (P : CutSet) (hP : CutPrefixFree P) (v : Source)
    (p : Address) (hp : p ∈ H P v) :
    decoderClass (H P v) (canonicalRow P (substitution v)) p = classOrdinal P v p := by
  unfold decoderClass classOrdinal firstEqIndex
  rw [old_decoder_holes P hP v]
  apply idxOf_map_relation (orderedHoles P v)
    (fun q => rowAt q (canonicalRow P (substitution v))) (fun q => subtree q v) p
  intro q hq
  have qold : q ∈ H P v := by
    simpa [H, orderedHoles, ← literalRow_hole_support P v] using hq
  have pr := (canonicalRow_reached P hP v p).mp (by simpa [H] using hp)
  have qr := (orderedHoles_mem P hP v q).mp hq
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp pr.2
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp qr.2
  have ps : subtree p (substitution v) = some (substitution s) := by
    simpa using NativeDepthPatterns.original_present_transport 1 p v s hs
  have qt : subtree q (substitution v) = some (substitution t) := by
    simpa using NativeDepthPatterns.original_present_transport 1 q v t ht
  have inj : Function.Injective substitution :=
    SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
      ⟨fun s t => substitution.map_mul s t, fun _ => rfl⟩
  rw [current_at_old P hP v q qold, current_at_old P hP v p hp]
  have markers (n m : Nat) :
      (FreeMagma.of (.inr n) : LiteralRow) = .of (.inr m) ↔ n = m := by
    constructor
    · intro h; cases h; rfl
    · intro h; rw [h]
  simp only [Option.some.injEq, markers]
  rw [classOrdinal_eq_iff P (substitution v)
    ((orderedHoles_mem P hP _ q).mpr ⟨qr.1, by simp [qt]⟩)
    ((orderedHoles_mem P hP _ p).mpr ⟨pr.1, by simp [ps]⟩)]
  simp only [qt, ps, ht, hs, Option.some.injEq, inj.eq_iff]

private theorem old_at_subtree (P : CutSet) (hP : CutPrefixFree P)
    (v t : Source) (a : Address) (ht : subtree a v = some t) :
    a ∈ H P v ↔ a ∈ P := by
  simpa [H, ht] using canonicalRow_reached P hP v a

private theorem no_strict_cut_child (P : CutSet) (a : Address) (d : Bool)
    (outside : ∀ p ∈ P, p.IsPrefix a → p = a) (ha : a ∉ P) :
    ∀ p ∈ P, p.IsPrefix (a ++ [d]) → p = a ++ [d] := by
  intro p hp pre
  rcases List.prefix_or_prefix_of_prefix pre (List.prefix_append a [d]) with h | h
  · exact False.elim (ha (outside p hp h ▸ hp))
  · have plen := pre.length_le
    have alen := h.length_le
    by_cases len : a.length = p.length
    · have eq := h.eq_of_length len
      exact False.elim (ha (eq.symm ▸ hp))
    · exact pre.eq_of_length (by
        simp only [List.length_append, List.length_singleton] at plen ⊢
        omega)

private theorem repair_substitution_at (P : CutSet) (hP : CutPrefixFree P)
    (v t : Source) (a : Address) (ht : subtree a v = some t)
    (outside : ∀ p ∈ P, p.IsPrefix a → p = a) :
    repairAt (canonicalRow P (substitution v)) (H P v) a
      (literalRow P (substitution v) a (substitution t)) =
        some (sigma (literalRow P v a t)) := by
  induction t generalizing a with
  | of b =>
      by_cases ha : a ∈ P
      · have old := (old_at_subtree P hP v (.of b) a ht).mpr ha
        have stop (s : Source) : literalRow P (substitution v) a s =
            .of (.inr (classOrdinal P (substitution v) a)) := by
          cases s <;> simp [literalRow, ha]
        rw [stop]
        simp only [literalRow, ha, ↓reduceIte, repairAt, old,
          old_decoder_class P hP v a old, sigma, FreeMagma.lift_of]
      · cases b with
        | true => simp [substitution, FreeMagma.lift_of, literalRow, ha, repairAt, sigma]
        | false =>
            have app := ActualLeafHistoryRigidity.actual_address_geometry
              |>.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have unborn (d : Bool) : a ++ [d] ∉ H P v := by
              intro h
              have reached := (canonicalRow_reached P hP v (a ++ [d])).mp (by simpa [H] using h)
              rw [app, ht] at reached
              cases d <;> simp [subtree] at reached
            have child (d : Bool) :
                repairAt (canonicalRow P (substitution v)) (H P v) (a ++ [d])
                  (literalRow P (substitution v) (a ++ [d]) (.of d)) =
                    some (.of (.inl d)) := by
              by_cases hd : a ++ [d] ∈ P
              · simp [literalRow, hd, repairAt, unborn d]
              · simp [literalRow, hd, repairAt]
            have beta : substitution (.of false) = .mul (.of false) (.of true) := rfl
            rw [beta]
            have row : literalRow P (substitution v) a (.mul (.of false) (.of true)) =
                .mul (literalRow P (substitution v) (a ++ [false]) (.of false))
                  (literalRow P (substitution v) (a ++ [true]) (.of true)) := by
              simp only [literalRow, ha, ↓reduceIte]
            rw [row]
            change (do
              let l' ← repairAt (canonicalRow P (substitution v)) (H P v) (a ++ [false])
                (literalRow P (substitution v) (a ++ [false]) (.of false))
              let r' ← repairAt (canonicalRow P (substitution v)) (H P v) (a ++ [true])
                (literalRow P (substitution v) (a ++ [true]) (.of true))
              pure (FreeMagma.mul l' r')) = _
            rw [child false, child true]
            simp [literalRow, ha, sigma, FreeMagma.lift_of]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · have old := (old_at_subtree P hP v (.mul l r) a ht).mpr ha
        simp [map_mul, FreeMagma.mul_eq, literalRow, ha, repairAt, old,
          old_decoder_class P hP v a old, sigma, FreeMagma.lift_of]
      · have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hl : subtree (a ++ [false]) v = some l := by rw [app, ht]; rfl
        have hr : subtree (a ++ [true]) v = some r := by rw [app, ht]; rfl
        simp only [map_mul, FreeMagma.mul_eq, literalRow, ha, ↓reduceIte, repairAt]
        rw [ihl _ hl (no_strict_cut_child P a false outside ha),
          ihr _ hr (no_strict_cut_child P a true outside ha)]
        rfl

/-- Exact recovery on actual transitions, and the complete conditional
same-current-row equivalence. Empty cuts, root cuts and absent cuts remain
in scope. Successful parsing of alleged data certifies no physical origin. -/
theorem native_predecessor_row_recovery (P : CutSet) (hP : CutPrefixFree P) :
    (∀ v : Source, back (canonicalRow P (substitution v)) (H P v) =
      some (canonicalRow P v)) ∧
    (∀ v w : Source, canonicalRow P (substitution v) = canonicalRow P (substitution w) →
      (canonicalRow P v = canonicalRow P w ↔ H P v = H P w)) := by
  have compatibility (v : Source) :
      repair (canonicalRow P (substitution v)) (H P v) = some (sigma (canonicalRow P v)) :=
    repair_substitution_at P hP v v [] rfl (by intro p _ h; exact List.prefix_nil.mp h)
  have correct (v : Source) : back (canonicalRow P (substitution v)) (H P v) =
      some (canonicalRow P v) := by
    rw [back, compatibility v, Option.bind_some, delta_sigma]
  refine ⟨correct, ?_⟩
  intro v w current
  constructor
  · intro previous
    exact congrArg (fun C => (holeAddresses [] C).toFinset) previous
  · intro support
    apply Option.some.inj
    calc
      some (canonicalRow P v) = back (canonicalRow P (substitution v)) (H P v) :=
        (correct v).symm
      _ = back (canonicalRow P (substitution w)) (H P w) := by rw [current, support]
      _ = some (canonicalRow P w) := correct w

end D5.S3.Arith.FibonacciAtomic.Observer.NativePredecessorRowRecovery
