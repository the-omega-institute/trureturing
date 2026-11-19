import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Combinatorics.NormalizedPfaffian
import Reg.Support.PfaffianSourceReadouts

namespace Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian
open _root_.D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open _root_.D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation
open _root_.D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing
open _root_.D5.S0.Certificates.Combinatorics.NormalizedPfaffianCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PfaffianSourceReadouts LeanInformationAudit
open scoped BigOperators

noncomputable section
universe u

namespace IndexCases
abbrev arena : Arena where
  signature := finSignature
  Law r := ∀ {n : ℕ} (x : Fin (2*n)),
    ∃ i : Fin n, r.readout () n x (first i) ∨ x = second i

theorem rejected_law : ¬ arena.Law finRejected := by
  intro h
  obtain ⟨i, hi | hi⟩ := h (n := 1) (0 : Fin (2*1))
  · have hzero : i = 0 := Subsingleton.elim _ _
    exact hi (by subst i; rfl)
  · have hv := congrArg Fin.val hi
    change 0 = 2 * i.val + 1 at hv
    omega

def source : Registration arena (type_of% @index_cases) where
  actual := finActual
  bridge := Iff.rfl
  variation := ⟨index_cases, finRejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := finDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@index_cases) (Realization finSignature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.IndexCases.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.IndexCases.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finSignature finActual.readout finActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end IndexCases

namespace CanonicalMate
abbrev arena : Arena where
  signature := finSignature
  Law r := ∀ {n : ℕ} (p : P n) (i : Fin n),
    r.readout () n (p.val (canonicalListing p ⟨2*i.val, by omega⟩))
      (canonicalListing p ⟨2*i.val+1, by omega⟩)

theorem rejected_law : ¬ arena.Law finRejected := by
  intro h
  exact h (e 1) 0 (canonical_mate (e 1) 0)

def source : Registration arena (type_of% @canonical_mate) where
  actual := finActual
  bridge := Iff.rfl
  variation := ⟨canonical_mate, finRejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := finDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_mate) (Realization finSignature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.CanonicalMate.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.CanonicalMate.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finSignature finActual.readout finActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CanonicalMate

namespace PairingIff
abbrev arena : Arena where
  signature := finSignature
  Law r := ∀ {n : ℕ} (s : Equiv.Perm (Fin (2*n))) (p : P n),
    pairingOfListing s = p ↔ ∀ i : Fin n,
      r.readout () n (p.val (s ⟨2*i.val, by omega⟩)) (s ⟨2*i.val+1, by omega⟩)

theorem rejected_law : ¬ arena.Law finRejected := by
  intro h
  let s : Equiv.Perm (Fin (2*1)) := 1
  exact (h (n := 1) s (pairingOfListing s)).mp rfl 0
    ((pairing_eq_iff (n := 1) s (pairingOfListing s)).mp rfl 0)

def source : Registration arena (type_of% @pairing_eq_iff) where
  actual := finActual
  bridge := Iff.rfl
  variation := ⟨pairing_eq_iff, finRejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := finDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairing_eq_iff) (Realization finSignature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.PairingIff.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.PairingIff.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finSignature finActual.readout finActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairingIff

namespace ListingValue
abbrev arena : Arena where
  signature := unitSignature
  Law r := ∀ {n : ℕ} (f : Fin (2*n) → Fin (2*n) → ℤˣ),
    (∀ x y, x ≠ y → f y x = -f x y) → ∀ s : Equiv.Perm (Fin (2*n)),
      r.readout () () (listingValue f s) (listingValue f (canonicalListing (pairingOfListing s)))

theorem rejected_law : ¬ arena.Law unitRejected := by
  intro h
  let f : Fin (2*0) → Fin (2*0) → ℤˣ := fun _ _ => 1
  have hf : ∀ x y, x ≠ y → f y x = -f x y := by intro x; exact Fin.elim0 x
  exact h f hf 1 (listing_value_canonical f hf 1)

def source : Registration arena (type_of% @listing_value_canonical) where
  actual := unitActual
  bridge := Iff.rfl
  variation := ⟨listing_value_canonical, unitRejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := unitDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@listing_value_canonical) (Realization unitSignature) Type Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.ListingValue.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.ListingValue.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize unitSignature unitActual.readout unitActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ListingValue

namespace Count
abbrev signature := equalitySignature Unit (fun _ => ℕ)
abbrev actual := equalityActual Unit (fun _ => ℕ)
abbrev rejected := equalityRejected Unit (fun _ => ℕ)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (s : Equiv.Perm (Pos n)), s ∈ normalizedListings n →
    r.readout () () (Fintype.card (InvType s))
      (Fintype.card (CrossType (pairingOfListing s)) +
        2 * Fintype.card (NestType (pairingOfListing s)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (1 : Equiv.Perm (Pos 0)) ∈ normalizedListings 0 := by
    simp [normalizedListings]
  exact h 1 hs (inversion_card_eq_cross_add_two_nesting_card 1 hs)

def source : Registration arena (type_of% @inversion_card_eq_cross_add_two_nesting_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inversion_card_eq_cross_add_two_nesting_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := equalityDependence ⟨(), 0, 1, by decide⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inversion_card_eq_cross_add_two_nesting_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.Count.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.Count.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Count

namespace CrossingSum
abbrev signature : Signature where
  Params := Σ n : ℕ, Type u
  State p := Matrix (Fin (2*p.1)) (Fin (2*p.1)) p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin (2*p.1)) (Fin (2*p.1)) p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _ (fun _ _ A => A) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize _
  (fun _ _ A => A.transpose) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : ℕ} {R : Type u} [CommRing R] (A : Matrix (Pos n) (Pos n) R),
    pfaffian (r.readout () ⟨n, R⟩ A) =
      ∑ s ∈ normalizedListings n, crossingCoefficient (pairingOfListing s) *
        ∏ a : lowerEndpoints (pairingOfListing s), A a.val ((pairingOfListing s).val a.val)

theorem actual_law : arena.{u}.Law actual := @pfaffian_eq_crossing_sum.{u}
theorem bridge : (type_of% @pfaffian_eq_crossing_sum.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Matrix (Fin (2*1)) (Fin (2*1)) (ULift.{u} ℤ) :=
    fun i j => if i = 0 ∧ j = 1 then 1 else 0
  have hh := @h 1 (ULift.{u} ℤ) inferInstance A
  have ht := @pfaffian_eq_crossing_sum 1 (ULift.{u} ℤ) inferInstance A
  have he := hh.trans ht.symm
  change pfaffian A.transpose = pfaffian A at he
  have hz : pfaffian A.transpose = 0 := by dsimp [A]; decide +kernel
  have ho : pfaffian A = 1 := by dsimp [A]; decide +kernel
  rw [hz, ho] at he
  exact zero_ne_one he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨1, ULift.{u} ℤ⟩, 0, 1, ?_⟩
  intro he
  have hv := congrArg (fun A => (A 0 0).down) he
  change (0 : ℤ) = 1 at hv
  exact Int.zero_ne_one hv

def source : Registration arena.{u} (type_of% @pfaffian_eq_crossing_sum.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pfaffian_eq_crossing_sum.{u}) (Realization signature.{u}) (type_of% (@Matrix.{0,0,u})) Unit where
  unitName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.CrossingSum.unit
  realizationName := `Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian.CrossingSum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Combinatorics.NormalizedPfaffian
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CrossingSum

end
end Reg.D5.S0.Certificates.Combinatorics.NormalizedPfaffian
