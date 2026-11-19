import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification
universe uK
noncomputable section

/-- The field and its dictionary remain coordinates; the additive parameter is observed. -/
abbrev signature : Signature where
  Params := Σ K : Type uK, Field K
  State d := d.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := d.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ d _ => letI := d.2; (0 : d.1)) (fun e => nomatch e)

/-- The original fixed automorphism, both jets, and every dependent binder are retained. -/
abbrev arena : Arena where
  signature := signature.{uK}
  Law f := ∀ {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {K : Type uK} [kk : Field K] [Algebra (ZMod p) K]
    (q r : K →ₗ[ZMod p] K) (hq1 : q 1 = 0) (hr1 : r 1 = 0)
    (φ : Multiplicative K ≃* Multiplicative K),
    (∃ P : Polynomial.degreeLT K p ≃ₗ[ZMod p] Polynomial.degreeLT K p,
      ∀ (g : Multiplicative K) (v : Polynomial.degreeLT K p),
      P (originalRepresentation (p := p) q g v) = originalRepresentation r (φ g) (P v)) ↔
    ∃ (c : Kˣ) (σ : K ≃ₐ[ZMod p] K) (δ : Derivation (ZMod p) K K),
      (∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd (f.readout () ⟨K, kk⟩ a))) =
        (c : K) * σ a) ∧
      ∀ a : K, r ((c : K) * σ a) = σ a * r c + (c : K)^(p-1) * σ (q a-δ a)

private instance testPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev testK := ULift.{uK} (ZMod 3)

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  have hi : ∃ P : Polynomial.degreeLT testK.{uK} 3 ≃ₗ[ZMod 3]
      Polynomial.degreeLT testK.{uK} 3, ∀ g v,
      P (originalRepresentation (p := 3) (0 : testK.{uK} →ₗ[ZMod 3] testK.{uK}) g v) =
      originalRepresentation 0 ((MulEquiv.refl (Multiplicative testK.{uK})) g) (P v) :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  obtain ⟨c, σ, δ, hc, _⟩ :=
    (hbad (p := 3) (K := testK.{uK}) 0 0 rfl rfl (MulEquiv.refl _)).mp hi
  have hz := hc 1
  have hzero : (0 : testK.{uK}) = (c : testK.{uK}) := by
    simpa [rejected, realize] using hz
  exact c.ne_zero hzero.symm

def family : Registration arena.{uK}
    (type_of% (@fixed_automorphism_intertwining_iff.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_automorphism_intertwining_iff.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨testK.{uK}, inferInstance⟩, 0, 1, ?_⟩
    exact zero_ne_one

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_automorphism_intertwining_iff.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification.fixed_automorphism_intertwining_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification
