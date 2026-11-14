import D5.S3.Quantum.Routing.HannRouterDephasing
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The complete physical-router source telescope, with fidelity as dependent readout. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Reg.D5.S3.Quantum.Routing.HannRouterDephasing

open _root_.D5.S3.Quantum.Routing.HannRouterDephasing
open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, ℝ × (Address n → Bool))
    (fun p => Address p.1 × Bool → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p ψ => squaredFidelity p.1 p.2.1 p.2.2 ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (D : Address n → Bool),
    (∀ (X : Matrix Qutrit Qutrit ℂ) (s t : Qutrit),
      (∑ e, localRecord q s e * conj (localRecord q t e)) * X s t =
        (q : ℂ) * X s t + (1-(q : ℂ)) * (if s = t then X s t else 0)) ∧
    (∀ t : _root_.D5.S3.Quantum.Routing.HannSpatialQram.Tree n, recordOverlap n q t t = 1) ∧
    (∀ (a a' : Address n) (b b' : Bool),
      routerMismatch n ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 =
          (if a = a' then 0 else 2 * (n -
            (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
              (addressWord n a) (addressWord n a')).length) - 1) ∧
      recordOverlap n q ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 = (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      (∑ e, jointOutput n q D ψ s e * conj (jointOutput n q D ψ t e)) =
        noisyOutput n q D ψ s t) ∧
    (∀ (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool),
      noisyOutput n q D ψ (clean n a (xor b (D a))) (clean n a' (xor b' (D a'))) =
        ψ (a,b) * conj (ψ (a',b')) * (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      ((∀ a b, s ≠ clean n a b) ∨ (∀ a b, t ≠ clean n a b)) →
        noisyOutput n q D ψ s t = 0) ∧
    (∀ ψ : Address n × Bool → ℂ, Normalized n ψ →
      (∑ s, Complex.normSq (idealOutput n D ψ s)) = 1 ∧
      R.readout () ⟨n,q,D⟩ ψ = (addressEnergy n q (addressProbability n ψ) : ℂ) ∧
        minimumFidelity n q ≤ (R.readout () ⟨n,q,D⟩ ψ).re) ∧
    Normalized n (uniformInput n) ∧
      R.readout () ⟨n,q,D⟩ (uniformInput n) = (minimumFidelity n q : ℂ) ∧
      minimumFidelity 0 q = 1 ∧
      (∀ ab, uniformInput n ab = if ab.2 then 0 else
        (((2 : ℝ)^(-(n : ℝ)/2) : ℝ) : ℂ))

abbrev arena : Arena := ⟨signature, sourceLaw⟩

private theorem rejected_law : ¬ sourceLaw rejected := by
  intro h
  have h₀ := h 0 0 (by norm_num) (by norm_num) (fun _ => false)
  rcases h₀ with ⟨_, _, _, _, _, _, _, _, hu, _⟩
  norm_num [rejected, realize, minimumFidelity] at hu

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0, fun _ => false⟩, (fun _ => 0), uniformInput 0, ?_⟩
  intro h
  change squaredFidelity 0 0 (fun _ => false) (fun _ => 0) =
    squaredFidelity 0 0 (fun _ => false) (uniformInput 0) at h
  have hz : squaredFidelity 0 0 (fun _ => false) (fun _ => 0) = 0 := by
    simp [squaredFidelity, idealOutput]
  have hu := result 0 0 (by norm_num) (by norm_num) (fun _ => false)
  rcases hu with ⟨_, _, _, _, _, _, _, _, hu, _⟩
  rw [hz, hu] at h
  norm_num [minimumFidelity] at h

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity sourceLaw actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    result (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p ψ => squaredFidelity p.1 p.2.1 p.2.2 ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterDephasing
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace InitializedClean

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, (Address n × Bool → ℂ) × Address n)
    (fun _ => Bool) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p b => initialized p.1 p.2.1 (clean p.1 p.2.2 b)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (ψ : Address n × Bool → ℂ) (a : Address n) (b : Bool),
    R.readout () ⟨n, ψ, a⟩ b = ψ (a, b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 (fun _ => 1) () false
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, (fun ab => if ab.2 then 1 else 0), ()⟩, false, true, ?_⟩
  change initialized 0 _ _ ≠ initialized 0 _ _
  rw [initialized_clean, initialized_clean]
  norm_num

def family : Registration arena (type_of% initialized_clean) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨initialized_clean, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    initialized_clean (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.InitializedClean.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.InitializedClean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => initialized p.1 p.2.1 (clean p.1 p.2.2 b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterDephasing
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InitializedClean

namespace KetSources

structure Params where
  index : Type
  basis : Type
  indices : Fintype index
  bases : Fintype basis
  decidableBasis : DecidableEq basis
  vector : index → basis
  amplitude : index → ℂ

abbrev signature : Signature.{1, 0, 0, 0, 0} where
  Params := Params
  State p := p.basis → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual (conjugate : Bool) : Realization signature :=
  realize signature (fun _ p g => by
    letI := p.indices
    letI := p.bases
    letI := p.decidableBasis
    exact ∑ s, (if conjugate then conj (∑ i, if s = p.vector i then p.amplitude i else 0)
      else ∑ i, if s = p.vector i then p.amplitude i else 0) * g s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (conjugate : Bool) (R : Realization signature) : Prop :=
  ∀ {ι σ : Type} [fi : Fintype ι] [fs : Fintype σ] [ds : DecidableEq σ]
    (v : ι → σ) (ψ : ι → ℂ) (g : σ → ℂ),
    R.readout () ⟨ι, σ, fi, fs, ds, v, ψ⟩ g =
      ∑ i, (if conjugate then conj (ψ i) else ψ i) * g (v i)

abbrev arena (conjugate : Bool) : Arena := ⟨signature, sourceLaw conjugate⟩

private theorem rejected_law (conjugate : Bool) : ¬ sourceLaw conjugate rejected := by
  intro h
  have he := @h Unit Unit inferInstance inferInstance inferInstance (fun _ => ())
    (fun _ => 1) (fun _ => 1)
  cases conjugate <;> norm_num [rejected, realize] at he

private theorem sensitivity (conjugate : Bool) :
    Sensitivity (arena conjugate) (actual conjugate) := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law conjugate⟩
    intro j h
    exact (h (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

private theorem dependence (conjugate : Bool) :
    ObservationalDependence signature (actual conjugate) := by
  intro i
  refine ⟨⟨Unit, Unit, inferInstance, inferInstance, inferInstance, (fun _ => ()),
    (fun _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  cases conjugate <;> norm_num [actual, realize]

end KetSources

namespace SumKet
open KetSources

def family : Registration (KetSources.arena false) (type_of% (@sum_ket)) where
  actual := KetSources.actual false
  bridge := Iff.rfl
  variation := ⟨@sum_ket, KetSources.rejected, KetSources.rejected_law false⟩
  sensitivity := KetSources.sensitivity false
  dependence := KetSources.dependence false

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sum_ket) (Realization KetSources.signature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.SumKet.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.SumKet.family
  realizationSource := none
  generated := false
  arena := .source ⟨KetSources.arena false⟩
  objectArena := .source ⟨KetSources.arena false⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (KetSources.arena false) ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize KetSources.signature
    (KetSources.actual false).readout (KetSources.actual false).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end SumKet

namespace SumKetConj
open KetSources

def family : Registration (KetSources.arena true) (type_of% (@sum_ket_conj)) where
  actual := KetSources.actual true
  bridge := Iff.rfl
  variation := ⟨@sum_ket_conj, KetSources.rejected, KetSources.rejected_law true⟩
  sensitivity := KetSources.sensitivity true
  dependence := KetSources.dependence true

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sum_ket_conj) (Realization KetSources.signature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.SumKetConj.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.SumKetConj.family
  realizationSource := none
  generated := false
  arena := .source ⟨KetSources.arena true⟩
  objectArena := .source ⟨KetSources.arena true⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (KetSources.arena true) ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize KetSources.signature
    (KetSources.actual true).readout (KetSources.actual true).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end SumKetConj

namespace AddressCard

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => Fintype.card (Address n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = 2 ^ n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Fintype.card (Address 0) ≠ Fintype.card (Address 1)
  rw [address_card, address_card]
  norm_num

def family : Registration arena (type_of% address_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨address_card, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    address_card (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.AddressCard.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterDephasing.AddressCard.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => Fintype.card (Address n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Address
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterDephasing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AddressCard

end Reg.D5.S3.Quantum.Routing.HannRouterDephasing
