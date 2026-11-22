import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
import Reg.Support.DependentFamily

/-! Real next-cut presence on the true physical service, with fixed cut and address. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness (matureSize bitNat eval adaptiveEval)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Address
  State _ := OutputStream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => queryNext p.1 p.2 s) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (C : LawfulClass) (_hC : ValidClass C) (n : Nat) (_hn : 2 ≤ n),
    (∀ (s : OutputStream) (_hs : ClassLegal C s),
      ((∀ t, Compatible C n s t → ∀ p : Address, F.readout () ⟨n, p⟩ s = queryNext n p t) ↔
        (∀ t, Compatible C n s t → bornWord n s = bornWord n t)) ∧
      ((∀ t, Compatible C n s t → physicalTree n s = physicalTree n t) ↔
        (∀ t, Compatible C n s t → bornWord n s = bornWord n t)) ∧
      ((∀ t, Compatible C n s t → future n s = future n t) ↔
        (∀ t, Compatible C n s t → s = t))) ∧
    (∀ g : Geometry,
      (UniformReady C g n (physicalTree n) ↔ requiredBits C ≤ matureSize n) ∧
      (UniformReady C g n (fun s p => queryNext n p s) ↔ requiredBits C ≤ matureSize n) ∧
      (UniformReady C g n (future n) ↔ requiredBits C ≤ matureSize n)) ∧
    matureSize n = Nat.fib n - 1 ∧
    (∀ g : Geometry, ∀ s t : OutputStream, acquired g n s = acquired g n t ↔
      matureWord n s = matureWord n t) ∧
    (∀ s t : OutputStream, (∀ as, (eval (birthOf s) n as).1 = (eval (birthOf t) n as).1) ↔ s = t) ∧
    (∀ s t : OutputStream, (∀ policy fuel hist, adaptiveEval policy (birthOf s) fuel n hist =
      adaptiveEval policy (birthOf t) fuel n hist) ↔ s = t) ∧
    (∀ (g : Geometry) (s : OutputStream), ClassLegal C s → requiredBits C ≤ matureSize n →
      install C g (acquired g n s) = some (n,s) ∧
      solve C g (acquired g n s) = some (physicalTree n s, fun p => queryNext n p s, future n s))

private def zeroStream : OutputStream := fun _ => false

private theorem zeroLegal : ClassLegal (.binary 0) zeroStream :=
  ⟨0, Nat.le_refl _, Fin.elim0, by intro i; simp [zeroStream, bitNat]⟩

private theorem zero_only (s : OutputStream) (hs : ClassLegal (.binary 0) s) : s = zeroStream := by
  obtain ⟨r, hr, c, hc⟩ := hs
  have h : r = 0 := by omega
  subst r
  funext i
  have hi := hc i
  cases he : s i
  · rfl
  · simp [he, bitNat] at hi

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := ((h (.binary 0) trivial 2 (by decide)).1 zeroStream zeroLegal).1
  have hw : ∀ t, Compatible (.binary 0) 2 zeroStream t →
      bornWord 2 zeroStream = bornWord 2 t := by
    intro t ht
    rw [zero_only t ht.1]
  have bad := hh.mpr hw zeroStream ⟨zeroLegal, rfl⟩ []
  change false = queryNext 2 [] zeroStream at bad
  have hroot : queryNext 2 [] zeroStream = true := by decide
  rw [hroot] at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, [false, false]⟩, zeroStream, fun _ => true, ?_⟩
  change queryNext 2 [false,false] zeroStream ≠ queryNext 2 [false,false] (fun _ => true)
  decide

def family : Registration arena (type_of% lawful_source_readiness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lawful_source_readiness, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lawful_source_readiness) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
    definition := none
    coordinates := #[2, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg",
        "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
