import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedBallHistoryCapture

/-! Full source telescope and exact free-pair observations for historical capture. -/

namespace Reg.D5.S3.Topology.InverseLimit.SignedBallHistoryCapture

open CategoryTheory CategoryTheory.Limits Opposite Set Function Filter MeasureTheory
open _root_.D5.S3.Topology.InverseLimit
open _root_.D5.S3.Topology.InverseLimit.CountableClopenReflection
open _root_.D5.S3.Topology.InverseLimit.SignedBallHistoryCapture
open _root_.D5.S3.Topology.Measures
open _root_.D5.S3.Topology.Measures.NormPreservingLifts
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped Topology

local instance (X : Profinite.{1}) : MeasurableSpace X := borel X
local instance (X : Profinite.{1}) : BorelSpace X := ⟨rfl⟩

structure SystemInputs where
  F : CountableStageᵒᵖ ⥤ Profinite.{1}
  nonempty : ∀ j, Nonempty (F.obj j)
  C : Cone F
  hC : IsLimit C
  hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a)
  H : RawHistory F

structure SourceInputs extends SystemInputs where
  s : ℕ → SignedMeasure C.pt
  W : ℕ → Set C.pt
  regular : ∀ n, (s n).totalVariation.Regular
  norm : ∀ n, (s n).totalVariation.real univ = 1
  clopen : ∀ n, IsClopen (W n) ∧ (W n).Nonempty
  disjoint : Pairwise (Disjoint on W)
  carry : ∀ n, (s n).totalVariation (W n)ᶜ = 0
  half : ∀ n, (1 / 2 : ℝ) ≤ (s n).toJordanDecomposition.posPart.real univ
  f : Ultrafilter ℕ → WeakDual ℝ C(C.pt, ℝ)
  continuous : Continuous f
  principal : ∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (s n))

def certificate (P : SourceInputs) (w : Ultrafilter ℕ × Ultrafilter ℕ) : Prop :=
  (w.1 : Filter ℕ) ≤ cofinite ∧ (w.2 : Filter ℕ) ≤ cofinite ∧
    w.1 ≠ w.2 ∧ P.f w.1 = P.f w.2

def signature : DependentFamily.Signature where
  Params := SourceInputs
  State := fun _ => Ultrafilter ℕ × Ultrafilter ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ P w => certificate P w)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ P, ∃ w, r.readout () P w

def captureScope : Prop :=
  ∀ P : SystemInputs, SignedBallReduction.SignedClopenCollision (K := P.C.pt)

theorem source_bridge : captureScope ↔ arena.Law actual := by
  constructor
  · intro h P
    obtain ⟨p, q, hp, hq, hpq, heq⟩ := h P.toSystemInputs
      P.s P.W P.regular P.norm P.clopen P.disjoint P.carry P.half
      P.f P.continuous P.principal
    exact ⟨(p, q), hp, hq, hpq, heq⟩
  · intro h P s W hreg hnorm hW hdis hcarry hhalf f hf hext
    let Q : SourceInputs :=
      ⟨P, s, W, hreg, hnorm, hW, hdis, hcarry, hhalf, f, hf, hext⟩
    obtain ⟨⟨p, q⟩, hp, hq, hpq, heq⟩ := h Q
    exact ⟨p, q, hp, hq, hpq, heq⟩

/- The exact source bridge supplies neither the missing capture proof nor
an actual-positive family witness. No validated registration is asserted. -/

end Reg.D5.S3.Topology.InverseLimit.SignedBallHistoryCapture
