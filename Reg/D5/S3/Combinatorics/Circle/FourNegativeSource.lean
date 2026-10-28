import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.FourNegativeSource
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open TwoOppositeLargeExchange ThreeLargePacketExchange BinaryRunSource FourNegativeSource
open scoped BigOperators

/-! Exact source-family evidence. A source-selection binding for the assembled
flux readout and a counterfactual law witness for the original minimum remain
open under issue #22063. These partial records assert no validated binding. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Combinatorics.Circle.FourNegativeSource

namespace flux
structure Parameters where
  carrier : Type
  finite : Fintype carrier
  equality : DecidableEq carrier
  rotate : Equiv.Perm carrier
  threshold : ℤ

structure Reading where
  positiveCount : ℕ
  negativeCount : ℕ
  smallMass : ℤ
  arrivalMass : ℤ
  largeMass : ℤ

abbrev signature : Signature where
  Params := Parameters
  State p := p.carrier → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reading
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p f => by
    letI := p.finite
    letI := p.equality
    exact {
      positiveCount := (Finset.univ.filter (fun i => p.threshold ≤ f i)).card
      negativeCount := (Finset.univ.filter (fun i => f i ≤ -p.threshold)).card
      smallMass := ∑ i ∈ Finset.univ.filter (fun i => 0 < f i ∧ f i < p.threshold), f i
      arrivalMass := ∑ i ∈ Finset.univ.filter (fun i => f i ≤ -p.threshold), f (p.rotate i)
      largeMass := ∑ i ∈ Finset.univ.filter (fun i => p.threshold ≤ f i), f i })
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨0,0,0,0,1⟩) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [Fintype α] [DecidableEq α]
    (ρ : Equiv.Perm α) (f : α → ℤ) (q : ℤ)
    (hq : 0 < q)
    (hbound : ∀ i, -(2 * q - 1) ≤ f i ∧ f i ≤ 2 * q - 1)
    (hstep : ∀ i, f (ρ i) = doubleStep (4 * q - 1) (f i)),
    let o := R.readout () ⟨α, inferInstance, inferInstance, ρ, q⟩ f
    o.positiveCount = o.negativeCount ∧ o.smallMass + o.arrivalMass = o.largeMass

theorem bridge :
    (type_of% (@permutation_doubleStep_positive_flux.{0})) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (Equiv.refl Unit) (fun _ => 0) 1 (by norm_num)
    (by intro i; norm_num) (by intro i; norm_num [doubleStep])
  change (0 : ℕ) = 0 ∧ (0 : ℤ) + 0 = 1 at hh
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨⟨Fin 1, inferInstance, inferInstance, Equiv.refl _, 2⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrArg Reading.smallMass h
  norm_num [actual, realize] at hh

def source_registration : Registration arena
    (type_of% (@permutation_doubleStep_positive_flux.{0})) where
  actual := actual
  bridge := bridge
  variation := ⟨@permutation_doubleStep_positive_flux.{0}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

-- The five mathematical readouts occur separately in the source conclusion.
-- No sourceSelection is asserted for a synthetic tuple absent from that source.
def audit : Contract.Registration
    (@permutation_doubleStep_positive_flux.{0})
    (type_of% (realize signature (fun r p f => actual.readout r p f) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegativeSource.permutation_doubleStep_positive_flux.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegativeSource.flux.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun r p f => actual.readout r p f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end flux

namespace minimum
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * s k t p)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hPY : s k t p < -s k t y)
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V),
    5 ≤ R.readout () k t

theorem bridge :
    (type_of% (@actualSource_minimum_negativeLargeCount_ge_five)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @actualSource_minimum_negativeLargeCount_ge_five

theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨3, 0, 1, ?_⟩
  change actualNegativeLargeCount 3 0 ≠ actualNegativeLargeCount 3 1
  decide

-- A rejected whole-family law needs a concrete original H1-H12 configuration.
-- Neither the conditional source theorem nor these readouts supply such an
-- existence witness. No variation/sensitivity or Contract registration is claimed.
#print axioms actual_law
end minimum
end Reg.D5.S3.Combinatorics.Circle.FourNegativeSource
