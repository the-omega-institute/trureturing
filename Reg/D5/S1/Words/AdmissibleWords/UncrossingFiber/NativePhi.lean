import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.UncrossingFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe t s o

/-- Signature assembly is universe polymorphic; only roles and anchors are finite. -/
private abbrev singleSignature (P : Type t) (X : P → Type s) (Y : P → Type o) :
    Signature.{t,s,0,o,0} where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem singleton_sensitivity {P : Type t} {X : P → Type s} {Y : P → Type o}
    (law : Realization (singleSignature P X Y) → Prop)
    (actual bad : Realization (singleSignature P X Y)) (hbad : ¬ law bad) :
    Sensitivity ⟨singleSignature P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem empty_fence (n : Nat) : fence n ∅ := by
  intro i j hij
  constructor <;> intro he h <;> simp at h

private theorem singleton_zero_not_fence : ¬ fence 2 ({0} : Finset (Fin 2)) := by
  intro h
  have hj := (h 0 1 rfl).1 (by decide) (by simp)
  simpa using hj

namespace FenceObservation
abbrev signature := singleSignature Nat (fun n => Finset (Fin n)) (fun _ => Bool)
noncomputable def actual : Realization signature := by
  classical
  exact realize signature (fun _ n A => decide (fence n A)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  cases i
  refine ⟨2, (∅ : Finset (Fin 2)), ({0} : Finset (Fin 2)), ?_⟩
  simp [actual, realize, empty_fence, singleton_zero_not_fence]
end FenceObservation

namespace Audit_fence_inter_union
abbrev signature := FenceObservation.signature
abbrev actual := FenceObservation.actual
abbrev rejected := FenceObservation.rejected
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} {A B : Finset (Fin n)}
    (hA : fence n A) (hB : fence n B),
    F.readout () n (A ∩ B) = true ∧ fence n (A ∪ B)

theorem bridge : (type_of% (@fence_inter_union)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n A B hA hB
    simpa [actual, FenceObservation.actual, realize] using @h n A B hA hB
  · intro h n A B hA hB
    simpa [actual, FenceObservation.actual, realize] using @h n A B hA hB

theorem positive : arena.Law actual := bridge.mp (@fence_inter_union)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := (@law 0 ∅ ∅ (empty_fence 0) (empty_fence 0)).1
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual :=
  singleton_sensitivity _ _ _ negative

theorem dependence : ObservationalDependence signature actual := FenceObservation.dependence
noncomputable def registration : Registration arena (type_of% (@fence_inter_union)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_fence_inter_union
namespace Audit_phi_involutive
abbrev signature := singleSignature Nat (fun n => Fin n → Bool) (fun n => Fin n → Bool)
def actual : Realization signature :=
  realize signature (fun _ _ w => phi w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} (w : Fin n → Bool), F.readout () n (phi w) = w

theorem bridge : (type_of% (@phi_involutive)) ↔ arena.Law actual := Iff.rfl
theorem positive : arena.Law actual := bridge.mp (@phi_involutive)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := congrFun (law (fun _ : Fin 1 => true)) (0 : Fin 1)
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, (fun _ : Fin 1 => false), (fun _ : Fin 1 => true), ?_⟩
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simpa [actual, realize, phi] using h0

def registration : Registration arena (type_of% (@phi_involutive)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_phi_involutive
namespace Audit_support_phi_injective
abbrev signature := singleSignature Nat (fun n => Fin n → Bool) (fun n => Finset (Fin n))
def actual : Realization signature :=
  realize signature (fun _ _ w => support (phi w)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat}, Function.Injective (fun w : Fin n → Bool => F.readout () n w)

theorem bridge : (type_of% (@support_phi_injective)) ↔ arena.Law actual := Iff.rfl
theorem positive : arena.Law actual := @support_phi_injective
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := @law 1 (fun _ : Fin 1 => false) (fun _ : Fin 1 => true) rfl
  have h0 := congrFun h (0 : Fin 1)
  cases h0

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, (fun _ : Fin 1 => false), (fun _ : Fin 1 => true), ?_⟩
  intro h
  have hm : (0 : Fin 1) ∈ actual.readout () 1 (fun _ => true) := by
    simp [actual, realize, support, phi]
  rw [← h] at hm
  simpa [actual, realize, support, phi] using hm

def registration : Registration arena (type_of% (@support_phi_injective)) where
  actual := actual
  bridge := bridge
  variation := ⟨@positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_support_phi_injective
namespace Audit_phi_support_fence
abbrev signature := FenceObservation.signature
abbrev actual := FenceObservation.actual
abbrev rejected := FenceObservation.rejected
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} {w : Fin n → Bool} (hw : Adm n w),
    F.readout () n (support (phi w)) = true

theorem bridge : (type_of% (@phi_support_fence)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n w hw
    simpa [actual, FenceObservation.actual, realize] using @h n w hw
  · intro h n w hw
    simpa [actual, FenceObservation.actual, realize] using @h n w hw

theorem positive : arena.Law actual := bridge.mp (@phi_support_fence)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := @law 0 (fun i => Fin.elim0 i) (by trivial)
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := FenceObservation.dependence
noncomputable def registration : Registration arena (type_of% (@phi_support_fence)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_phi_support_fence
namespace Audit_phi_support_fence_iff
abbrev signature := FenceObservation.signature
abbrev actual := FenceObservation.actual
abbrev rejected := FenceObservation.rejected
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} (w : Fin n → Bool),
    F.readout () n (support (phi w)) = true ↔ Adm n w

theorem bridge : (type_of% (@phi_support_fence_iff)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n w
    simpa [actual, FenceObservation.actual, realize] using @h n w
  · intro h n w
    simpa [actual, FenceObservation.actual, realize] using @h n w

theorem positive : arena.Law actual := bridge.mp (@phi_support_fence_iff)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := (law (fun i : Fin 0 => Fin.elim0 i)).mpr (by trivial)
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := FenceObservation.dependence
noncomputable def registration : Registration arena (type_of% (@phi_support_fence_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_phi_support_fence_iff
namespace Audit_mem_fenceFamily
abbrev signature := singleSignature Nat (fun n => Finset (Fin n)) (fun _ => Bool)
noncomputable def actual : Realization signature := by
  classical
  exact realize signature (fun _ n A => decide (A ∈ fenceFamily n)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} {A : Finset (Fin n)}, F.readout () n A = true ↔ fence n A

theorem bridge : (type_of% (@mem_fenceFamily)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n A
    simpa [actual, realize] using @h n A
  · intro h n A
    simpa [actual, realize] using @h n A

theorem positive : arena.Law actual := bridge.mp (@mem_fenceFamily)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := (@law 0 ∅).mpr (empty_fence 0)
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  cases i
  refine ⟨2, (∅ : Finset (Fin 2)), ({0} : Finset (Fin 2)), ?_⟩
  have hg : (∅ : Finset (Fin 2)) ∈ fenceFamily 2 := mem_fenceFamily.mpr (empty_fence 2)
  have hb : ¬ ({0} : Finset (Fin 2)) ∈ fenceFamily 2 :=
    fun h => singleton_zero_not_fence (mem_fenceFamily.mp h)
  simp [actual, realize, hg, hb]

noncomputable def registration : Registration arena (type_of% (@mem_fenceFamily)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_mem_fenceFamily
namespace Audit_fenceFamily_closed
abbrev signature := singleSignature Nat (fun n => Finset (Finset (Fin n))) (fun _ => Bool)
noncomputable def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ L => decide (ClosedFamily L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (n : Nat), F.readout () n (fenceFamily n) = true

theorem bridge : (type_of% (@fenceFamily_closed)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n
    simpa [actual, realize] using h n
  · intro h n
    simpa [actual, realize] using h n

theorem positive : arena.Law actual := bridge.mp (@fenceFamily_closed)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law 0
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  cases i
  let good : Finset (Finset (Fin 2)) := {∅}
  let bad : Finset (Finset (Fin 2)) := {{0}, {1}}
  have hg : ClosedFamily good := by
    intro A hA B hB
    have hA' : A = ∅ := by simpa [good] using hA
    have hB' : B = ∅ := by simpa [good] using hB
    subst A
    subst B
    simp [good]
  have hb : ¬ ClosedFamily bad := by
    intro h
    have hi := (h (A := ({0} : Finset (Fin 2))) (by simp [bad])
      (B := ({1} : Finset (Fin 2))) (by simp [bad])).1
    have hempty : ({0} : Finset (Fin 2)) ∩ {1} = ∅ := by decide
    rw [hempty] at hi
    simpa [bad] using hi
  refine ⟨2, good, bad, ?_⟩
  simp [actual, realize, hg, hb]

noncomputable def registration : Registration arena (type_of% (@fenceFamily_closed)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_fenceFamily_closed
namespace Audit_phiRows_margin
abbrev Parameters := Sigma (fun n : Nat => Fin n)
abbrev signature := singleSignature Parameters
  (fun p => Multiset (Fin p.1 → Bool)) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ p M => margin (phiRows M) p.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} (M : Multiset (Fin n → Bool)) (i : Fin n),
    F.readout () ⟨n, i⟩ M =
      if Even i.val then occupancyCount M i else M.card - occupancyCount M i

theorem bridge : (type_of% (@phiRows_margin)) ↔ arena.Law actual := Iff.rfl
theorem positive : arena.Law actual := bridge.mp (@phiRows_margin)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law (0 : Multiset (Fin 1 → Bool)) (0 : Fin 1)
  simpa [rejected, realize, occupancyCount] using h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, (0 : Multiset (Fin 1 → Bool)),
    ((fun _ : Fin 1 => true) ::ₘ 0), ?_⟩
  simp [actual, realize, margin, phiRows, support, phi]

def registration : Registration arena (type_of% (@phiRows_margin)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_phiRows_margin

private abbrev crossA : Finset (Fin 3) := {0, 1}
private abbrev crossB : Finset (Fin 3) := {1, 2}
private abbrev crossInput : Multiset (Finset (Fin 3)) := crossA ::ₘ crossB ::ₘ 0
private abbrev crossOutput : Multiset (Finset (Fin 3)) :=
  (crossA ∩ crossB) ::ₘ (crossA ∪ crossB) ::ₘ 0

private theorem crossA_fence : fence 3 crossA := by
  unfold fence
  decide
private theorem crossB_fence : fence 3 crossB := by
  unfold fence
  decide
private theorem crossInput_family : FamilyRows (fenceFamily 3) crossInput := by
  intro A hA
  rcases Multiset.mem_cons.mp hA with rfl | hA
  · exact mem_fenceFamily.mpr crossA_fence
  rcases Multiset.mem_cons.mp hA with rfl | hA
  · exact mem_fenceFamily.mpr crossB_fence
  · simp at hA

private theorem cross_step : ForwardStep crossInput crossOutput := by
  refine ⟨0, crossA, crossB, ?_, ?_, rfl, rfl⟩ <;> decide

private theorem cross_native_step :
    NativeForwardStep (unphiRows crossInput) (unphiRows crossOutput) :=
  adm_phi_forward_consumer crossInput_family cross_step

private theorem no_native_step_to_zero {n : Nat} {M : Multiset (Fin n → Bool)} :
    ¬ NativeForwardStep M 0 := by
  rintro ⟨hM, R, a, b, hab, hba, hsource, htarget⟩
  have hc := congrArg Multiset.card htarget
  simp only [Multiset.card_zero, Multiset.card_cons] at hc
  omega

namespace Audit_adm_phi_forward_consumer
abbrev Parameters := Sigma (fun n : Nat => Multiset (Finset (Fin n)))
abbrev signature := singleSignature Parameters
  (fun p => Multiset (Fin p.1 → Bool)) (fun _ => Bool)
noncomputable def actual : Realization signature := by
  classical
  exact realize signature
    (fun _ p Y => decide (NativeForwardStep (unphiRows p.2) Y)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} {M N : Multiset (Finset (Fin n))}
    (hM : FamilyRows (fenceFamily n) M) (h : ForwardStep M N),
    F.readout () ⟨n, M⟩ (unphiRows N) = true

theorem bridge : (type_of% (@adm_phi_forward_consumer)) ↔ arena.Law actual := by
  classical
  constructor
  · intro h n M N hM hstep
    simpa [actual, realize] using @h n M N hM hstep
  · intro h n M N hM hstep
    simpa [actual, realize] using @h n M N hM hstep

theorem positive : arena.Law actual := bridge.mp (@adm_phi_forward_consumer)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := @law 3 crossInput crossOutput crossInput_family cross_step
  change false = true at h
  cases h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  cases i
  refine ⟨⟨3, crossInput⟩, unphiRows crossOutput, (0 : Multiset (Fin 3 → Bool)), ?_⟩
  have hb : ¬ NativeForwardStep (unphiRows crossInput) (0 : Multiset (Fin 3 → Bool)) :=
    no_native_step_to_zero
  simp [actual, realize, cross_native_step, hb]

noncomputable def registration : Registration arena (type_of% (@adm_phi_forward_consumer)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_adm_phi_forward_consumer
namespace Audit_nativePath_invariants
abbrev signature := singleSignature Nat (fun n => Multiset (Fin n → Bool)) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ M => M.card) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} {M N : Multiset (Fin n → Bool)}
    (hM : NativeRows M) (h : NativePath M N),
    NativeRows N ∧ F.readout () n N = M.card ∧
      ∀ i, occupancyCount N i = occupancyCount M i

theorem bridge : (type_of% (@nativePath_invariants)) ↔ arena.Law actual := Iff.rfl
theorem positive : arena.Law actual := bridge.mp (@nativePath_invariants)
theorem negative : ¬ arena.Law rejected := by
  intro law
  let M : Multiset (Fin 0 → Bool) := (fun i => Fin.elim0 i) ::ₘ 0
  have hM : NativeRows M := by
    intro w hw
    trivial
  have hp : NativePath M M := .refl
  have h := (@law 0 M M hM hp).2.1
  simpa [rejected, realize, M] using h

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨0, (0 : Multiset (Fin 0 → Bool)), ((fun j : Fin 0 => Fin.elim0 j) ::ₘ 0), ?_⟩
  simp [actual, realize]

def registration : Registration arena (type_of% (@nativePath_invariants)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_nativePath_invariants

private theorem support_phi_true_one :
    support (phi (fun _ : Fin 1 => true)) = ({0} : Finset (Fin 1)) := by
  ext i
  fin_cases i
  simp [support, phi]

namespace Audit_adm_phi_route_bound
abbrev signature := singleSignature Nat (fun n => Multiset (Fin n → Bool)) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ M => energy (phiRows M)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} (M : Multiset (Fin n → Bool)) (hM : NativeRows M),
    ∃ k, 2 * k + F.readout () n M ≤ M.card * n ^ 2 ∧ k ≤ M.card * n ^ 2 / 2 ∧
      ForwardRoute (phiRows M) (thresholdRows (phiRows M)) k ∧
      NativePath M (nativeCanonical M) ∧ NativeRows (nativeCanonical M) ∧
      phiRows (nativeCanonical M) = thresholdRows (phiRows M) ∧
      (∀ j : Fin (phiRows M).card, Adm n (unphi (thresholdRow (phiRows M) j))) ∧
      (∀ k' P, ForwardRoute (phiRows M) P k' → Comparable P →
        P = thresholdRows (phiRows M))

theorem bridge : (type_of% (@adm_phi_route_bound)) ↔ arena.Law actual := Iff.rfl
theorem positive : arena.Law actual := bridge.mp (@adm_phi_route_bound)
theorem negative : ¬ arena.Law rejected := by
  intro law
  have hM : NativeRows (0 : Multiset (Fin 1 → Bool)) := by
    intro w hw
    simp at hw
  obtain ⟨k, he, hk, hr, hp, hn, hc, hj, hu⟩ := law (0 : Multiset (Fin 1 → Bool)) hM
  change 2 * k + 1 ≤ (0 : Multiset (Fin 1 → Bool)).card * 1 ^ 2 at he
  simp only [Multiset.card_zero, zero_mul] at he
  omega

theorem sensitivity : Sensitivity arena actual := singleton_sensitivity _ _ _ negative
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, (0 : Multiset (Fin 1 → Bool)), ((fun _ : Fin 1 => true) ::ₘ 0), ?_⟩
  simp [actual, realize, energy, height, phiRows, support_phi_true_one]

def registration : Registration arena (type_of% (@adm_phi_route_bound)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence
end Audit_adm_phi_route_bound

/- Compiler-derived direct-source wires. -/

namespace Audit_fence_inter_union

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@fence_inter_union)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.fence_inter_union.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_fence_inter_union.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ n A => decide (fence n A)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_fence_inter_union
namespace Audit_phi_involutive

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := false }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@phi_involutive)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.phi_involutive.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_phi_involutive.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ _ w => phi w) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_phi_involutive
namespace Audit_support_phi_injective

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@support_phi_injective)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.support_phi_injective.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_support_phi_injective.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ _ w => support (phi w)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_support_phi_injective

namespace Audit_phi_support_fence

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@phi_support_fence)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.phi_support_fence.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_phi_support_fence.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ n A => decide (fence n A)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_phi_support_fence

namespace Audit_phi_support_fence_iff

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@phi_support_fence_iff)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.phi_support_fence_iff.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_phi_support_fence_iff.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ n A => decide (fence n A)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_phi_support_fence_iff

namespace Audit_mem_fenceFamily

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@mem_fenceFamily)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.mem_fenceFamily.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_mem_fenceFamily.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ n A => decide (A ∈ fenceFamily n)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_mem_fenceFamily

namespace Audit_fenceFamily_closed

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@fenceFamily_closed)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.fenceFamily_closed.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_fenceFamily_closed.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ _ L => decide (ClosedFamily L)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_fenceFamily_closed

namespace Audit_phiRows_margin

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0, 2]
  readouts := #[{
    path := #["body", "body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["fn", "arg", "arg"]
    booleanPredicate := false }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@phiRows_margin)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.phiRows_margin.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_phiRows_margin.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ p M => margin (phiRows M) p.2) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_phiRows_margin

namespace Audit_adm_phi_forward_consumer

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0, 1]
  readouts := #[{
    path := #["body", "body", "body", "body", "body"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["arg"]
    booleanPredicate := true }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@adm_phi_forward_consumer)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.adm_phi_forward_consumer.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_adm_phi_forward_consumer.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ p Y => decide (NativeForwardStep (unphiRows p.2) Y)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_adm_phi_forward_consumer

namespace Audit_nativePath_invariants

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@nativePath_invariants)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.nativePath_invariants.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_nativePath_invariants.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ _ M => M.card) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_nativePath_invariants

namespace Audit_adm_phi_route_bound

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
    stateBinder := 1
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@adm_phi_route_bound)
      (Realization signature) Unit Unit := by
  classical
  exact {
    unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.adm_phi_route_bound.__information_unit
    realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi.Audit_adm_phi_route_bound.registration
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨registration⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature (fun _ _ M => energy (phiRows M)) (fun e => nomatch e))
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some sourceSelection
    continuation := .unknown
    familyRecord := none
    options := #[] }
end Audit_adm_phi_route_bound

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.NativePhi

end
