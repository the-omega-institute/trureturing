import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.TotalVariation.FairBiasCycleFactorization
import Mathlib.Algebra.Module.ULift

/-! Source-bound observation of signed normalization at a top facet. -/

namespace Reg.D5.S3.TotalVariation.FairBiasCycleFactorization

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.TotalVariation.FairBiasCycleFactorization
open _root_.D5.S3.TotalVariation.FairBiasMatching
open _root_.D5.S3.TotalVariation.FairBiasRestriction
open _root_.D5.S3.TotalVariation.FairBiasShelling
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

set_option linter.checkUnivs false in
abbrev Params :=
  Σ A : Type u, Σ L : Type v, Σ g : AddCommGroup A, Σ f : Fintype L,
    Σ c : L → A, @Face A L g f c

abbrev sig := signature Params.{u,v}
  (fun ⟨A, L, g, f, c, _⟩ => @Face A L g f c → ℤ) (fun _ => ℤ)

def actual : Realization sig.{u,v} :=
  realize sig (fun _ ⟨_, _, _, _, _, F⟩ z => z F) (fun e => nomatch e)

def rejected : Realization sig.{u,v} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

local instance {A L : Type*} [AddCommGroup A] [Fintype L] (c : L → A) : Fintype (Face c) := by
  classical
  unfold Face
  infer_instance

abbrev arena : Arena where
  signature := sig.{u,v}
  Law r := ∀ {A : Type u} {L : Type v} [g : AddCommGroup A] [Module (ZMod 2) A] [Finite A]
      [f : Fintype L] [LinearOrder (L × Bool)] (c : L → A) (B : Face c),
    TopFacet c B.val → restrictionFace c B.val = B.val →
    (∃! z, SignedNormalized c B z) ∧
    (∀ z, SignedNormalized c B z → B.val = ∅ →
      ∀ F : Face c, r.readout () ⟨A, L, g, f, c, F⟩ z = simplex ∅ F.val) ∧
    ∀ e, LeastNonloop (signedMatroid c) e →
      let C := circuitAt (signedMatroid c) B.val e
      let D := B.val \ C
      PassiveBase (signedMatroid c ／ (C : Set (L × Bool))) D ∧
      ∀ z w, SignedNormalized c B z →
        Normalized (signedMatroid c ／ (C : Set (L × Bool))) D w →
        (∀ F : Face c, z F = circuitLift C e B.val w F.val) ∧
        (∀ F : Face c, z F ≠ 0 ↔ ∃ x ∈ C, F.val ∩ C = C.erase x ∧
          F.val \ C ∈ cycleSupport w) ∧
        (univ.filter fun F : Face c => z F ≠ 0).card = C.card * (cycleSupport w).card

private abbrev EmptyLabels := PEmpty.{v+1}

local instance : LinearOrder (EmptyLabels.{v} × Bool) :=
  LinearOrder.lift' Prod.snd (fun a => a.1.elim)

private def emptyColumns : EmptyLabels.{v} → ULift.{u} (ZMod 2) := PEmpty.elim

private def emptyFacet : Face emptyColumns.{u,v} :=
  ⟨∅, by simp [augmentedFaces]⟩

private theorem empty_top : TopFacet emptyColumns.{u,v} emptyFacet.val := by
  refine .inr ⟨rfl, ?_⟩
  rintro ⟨F, hF⟩
  obtain ⟨⟨a, _⟩, _⟩ := ((facet_iff_base emptyColumns.{u,v} F).1 (mem_facets.1 hF)).1
  exact a.elim

private theorem empty_restriction :
    restrictionFace emptyColumns.{u,v} emptyFacet.val = emptyFacet.val := by
  ext a
  exact a.1.elim

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨z, hz, _⟩ := (signed_cycle_factorization emptyColumns.{u,v} emptyFacet
    empty_top empty_restriction).1
  have hh := (h emptyColumns.{u,v} emptyFacet empty_top empty_restriction).2.1
    z hz rfl emptyFacet
  simp [simplex, emptyFacet, rejected, realize] at hh

private theorem dependence : ObservationalDependence sig.{u,v} actual := by
  intro i
  refine ⟨⟨_, _, inferInstance, inferInstance, emptyColumns.{u,v}, emptyFacet⟩,
    fun _ => 0, fun _ => 1, ?_⟩
  exact Int.zero_ne_one

def source_registration :
    Registration arena.{u,v} (type_of% (@signed_cycle_factorization.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_cycle_factorization.{u,v}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@signed_cycle_factorization.{u,v}) (Realization sig.{u,v}) Type Unit where
  unitName := (`D5.S3.TotalVariation.FairBiasCycleFactorization.signed_cycle_factorization).str
    "__information_unit"
  realizationName := `Reg.D5.S3.TotalVariation.FairBiasCycleFactorization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.FairBiasCycleFactorization
    definition := none
    coordinates := #[0, 1, 7, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.FairBiasCycleFactorization
