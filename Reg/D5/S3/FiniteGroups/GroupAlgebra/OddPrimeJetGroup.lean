import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
import Reg.Support.FiniteJetAudit
import Reg.Support.OddPrimeJetAudit

/-! Full-telescope source evidence for the unrestricted normalized conjugation law. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open OddPrimeJetDeformation OddPrimeJetCommutant FiniteJetClassification OddPrimeJetGroup

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
universe u
namespace normalized_conjugation

structure Scope where
  d : Reg.Support.FiniteJetAudit.CountData.{u}
  A : Fin (d.n-1) → d.K
  g : labelGroup (Q (p := d.p) d.n A)

abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Scope.{u}
  (fun s => Polynomial.degreeLT s.d.K s.d.p)
  (fun s => Polynomial.degreeLT s.d.K s.d.p)

def actual : Realization signature.{u} := realize signature
  (fun _ s v => degreeLift s.d.hn s.d.hK s.A s.g v) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun i s v => actual.readout i s v + constantLinear 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [kk : Field K] [ka : Algebra (ZMod p) K] [kt : Fintype K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p^n) (A : Fin (n-1) → K)
    (g : labelGroup (Q (p := p) n A)) (a : Fin (p-1) → K)
    (T : K →ₗ[ZMod p] K) (v : Polynomial.degreeLT K p),
    r.readout () ⟨⟨⟨⟨p,K,n⟩,hn,hK⟩⟩,A,g⟩ (toeplitz a T v) =
      toeplitz (fun j => (labelScalar hn hK A g : K)^j.val *
        labelSigma hn hK A g (a j)) (transformedTop hn hK A g T)
        (degreeLift hn hK A g v)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hbad
  have h := hbad (p := 3) (K := ULift.{u} (ZMod 3)) (n := 1)
    (by decide) (by simp) 0 1 0 0 0
  have hz : constantLinear (p := 3) (K := ULift.{u} (ZMod 3)) 1 = 0 := by
    simpa [rejected, actual, realize, toeplitz, scalarMap, topMap,
      transformedTop] using h
  have hc := congrArg (fun v : Polynomial.degreeLT (ULift.{u} (ZMod 3)) 3 =>
    (v : Polynomial (ULift.{u} (ZMod 3))).coeff 0) hz
  simpa [constantLinear] using hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let s : Scope.{u} := ⟨Reg.Support.FiniteJetAudit.threeCount,0,1⟩
  refine ⟨s, 0, constantLinear 1, ?_⟩
  intro he
  have hz : (0 : Polynomial.degreeLT s.d.K s.d.p) = constantLinear 1 :=
    (degreeLift s.d.hn s.d.hK s.A s.g).injective he
  have hc := congrArg (fun v : Polynomial.degreeLT s.d.K s.d.p =>
    (v : Polynomial s.d.K).coeff 0) hz
  simpa [constantLinear] using hc

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup.normalized_conjugation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup.normalized_conjugation.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup.normalized_conjugation.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup.normalized_conjugation.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup.normalized_conjugation.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end normalized_conjugation
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
