import D5.S3.Quantum.Routing.HannRouterProfiles
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Reg.D5.S3.Quantum.Routing.HannRouterProfiles

open _root_.D5.S3.Quantum.Routing
open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.HannRouterProfiles
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, Qutrit × Router (n + 1))
    (fun p => Address (p.1 + 1)) (fun _ => Qutrit)

def actual : Realization signature :=
  realize signature (fun _ p a => loadedLabel (p.1 + 1) a p.2.1 p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Qutrit.zero) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (q : Router (n + 1) → ℝ),
    (∀ (a a' : Address (n + 1)) (bus bus' : Qutrit),
      (∀ v, q v < 1 → R.readout () ⟨n, bus, v⟩ a = loadedLabel (n + 1) a' bus' v) →
        a = a') ↔ ∀ u : Address n, q (deepest n u) < 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h 0 (fun _ => 0)).mpr (by intro u; norm_num)
  have he := hs (true, ()) (false, ()) Qutrit.wait Qutrit.wait (by
    intro v hv
    cases v with
    | none => rfl
    | some v => exact v.2.elim)
  cases he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Qutrit.wait, none⟩, (false, ()), (true, ()), ?_⟩
  intro h
  change Qutrit.zero = Qutrit.one at h
  cases h

def family : Registration arena (type_of% profile_separation_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨profile_separation_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    profile_separation_iff (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.family
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
    (fun _ p a => loadedLabel (p.1 + 1) a p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterProfiles
    definition := none
    coordinates := #[0, 4, 6]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body",
        "domain", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

namespace FullEvent

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, (Router n → ℝ) × (Address n → Bool))
    (fun p => Address p.1 × Bool → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p ψ => squaredFidelity p.1 p.2.1 p.2.2 ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq' : ∀ v, q v ≤ 1) (D : Address n → Bool),
    (∀ (a : Address n) (bus : Qutrit),
      treeRecord n q ((load n n) (loading n a bus 0)).2.2 = record n q a) ∧
    (∀ t : Tree n, (∑ e, Complex.normSq (treeRecord n q t e)) = 1) ∧
    (∀ (a b : Address n) (bus bus' : Qutrit),
      profile n q a = profile n q b ↔
        ∀ v, q v < 1 → loadedLabel n a bus v = loadedLabel n b bus' v) ∧
    LinearIndependent ℂ (classRecord n q) ∧
    (gram n q).rank = Fintype.card (Profile n q) ∧
    (∀ x : Address n → ℂ, (gram n q).mulVec x = 0 ↔ ∀ c, classSum n q x c = 0) ∧
    ((gram n q).rank = 2 ^ n ↔ DeepestActive n q) ∧
    (n = 0 → (gram n q).rank = 1) ∧
    (∀ p : AddressDistribution n,
      addressEnergy n q p.weights = classEnergy n q (classMass n q p).weights) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s : State n),
      HannRouterDephasing.idealOutput n D ψ s =
        initialized n ψ ((load n n).symm ((HannRouterDephasing.postLoad n D).symm s))) ∧
    (∀ (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool),
      noisyOutput n q D ψ (HannRouterDephasing.outputBasis n D (a, b))
        (HannRouterDephasing.outputBasis n D (a', b')) =
          ψ (a, b) * conj (ψ (a', b')) * gram n q a a') ∧
    (∀ ψ : Address n × Bool → ℂ, R.readout () ⟨n, q, D⟩ ψ =
      (addressEnergy n q (HannRouterDephasing.addressProbability n ψ) : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ), HannRouterDephasing.Normalized n ψ →
      (∑ s, ∑ e, Complex.normSq (jointOutput n q D ψ s e)) = 1 ∧
      (∑ s, Complex.normSq (HannRouterDephasing.idealOutput n D ψ s)) = 1) ∧
    (∀ p : AddressDistribution n,
      ∃ h : HannRouterDephasing.Normalized n (distributionInput n p),
        inputDistribution n (distributionInput n p) h = p) ∧
    ∃ x : ClassDistribution n q,
      (∀ y : ClassDistribution n q, classEnergy n q x.weights ≤ classEnergy n q y.weights) ∧
      (∀ y : ClassDistribution n q,
        (∀ z : ClassDistribution n q, classEnergy n q y.weights ≤ classEnergy n q z.weights) →
          y = x) ∧
      Function.Surjective (classMass n q) ∧
      (∀ p : AddressDistribution n,
        (∀ r : AddressDistribution n, addressEnergy n q p.weights ≤ addressEnergy n q r.weights) ↔
          classMass n q p = x) ∧
      (∀ (ψ : Address n × Bool → ℂ) (hψ : HannRouterDephasing.Normalized n ψ),
        (∀ (φ : Address n × Bool → ℂ), HannRouterDephasing.Normalized n φ →
          (R.readout () ⟨n, q, D⟩ ψ).re ≤ (R.readout () ⟨n, q, D⟩ φ).re) ↔
            classMass n q (inputDistribution n ψ hψ) = x)

abbrev arena : Arena := ⟨signature, sourceLaw⟩

private theorem rejected_law : ¬ sourceLaw rejected := by
  intro h
  have h0 := h 0 (fun _ => 0) (by intro v; exact v.elim) (by intro v; exact v.elim)
    (fun _ => false)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, hf, _⟩
  have he := hf (fun _ => 1)
  norm_num [rejected, realize, addressEnergy, HannRouterDephasing.addressProbability,
    gram, record, Router] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, (fun _ => 0), (fun _ => false)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have h0 := physical_profile_event 0 (fun _ => 0) (by intro v; exact v.elim)
    (by intro v; exact v.elim) (fun _ => false)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, hf, _⟩
  change squaredFidelity 0 (fun _ => 0) (fun _ => false) (fun _ => 0) =
    squaredFidelity 0 (fun _ => 0) (fun _ => false) (fun _ => 1) at h
  rw [hf, hf] at h
  norm_num [addressEnergy, HannRouterDephasing.addressProbability, gram, record, Router] at h

def family : Registration arena (type_of% physical_profile_event) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_profile_event, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity sourceLaw actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    physical_profile_event (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.FullEvent.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.FullEvent.family
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
    owner := `D5.S3.Quantum.Routing.HannRouterProfiles
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end FullEvent

end Reg.D5.S3.Quantum.Routing.HannRouterProfiles
