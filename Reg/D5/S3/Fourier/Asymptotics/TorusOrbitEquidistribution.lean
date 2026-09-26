import D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
open Filter MeasureTheory Set TopologicalSpace Topology
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

abbrev signature : Signature where
  Params := Σ I : Type u, I → Circle
  State p := C((Subgroup.zpowers p.2).topologicalClosure, ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C((Subgroup.zpowers p.2).topologicalClosure, ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The full source statement; the intervention changes only orbit observations.
The subgroup equality and the integral of the original observable remain fixed. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I] (g : I → Circle),
    let G := (Subgroup.zpowers g).topologicalClosure
    letI : CompactSpace G := isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
    (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) ∧
    ∀ f : C(G, ℂ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (r.readout () ⟨I, g⟩ f) ⟨g ^ (n + 1),
        G.pow_mem (subset_closure (Subgroup.mem_zpowers g)) (n + 1)⟩) / (N : ℂ))
      atTop (𝓝 (∫ z : G, f z ∂μ))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I := ULift.{u} Unit
  let g : I → Circle := 1
  let G := (Subgroup.zpowers g).topologicalClosure
  letI : CompactSpace G := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  letI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have ht := (h g).2 (1 : C(G, ℂ))
  have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa [rejected, realize, signature, μ] using ht
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hz)

def registration : Registration arena.{u}
    (∀ {I : Type u} [Fintype I] (g : I → Circle),
      let G := (Subgroup.zpowers g).topologicalClosure
      letI : CompactSpace G := isCompact_iff_compactSpace.mp
        (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
      letI : MeasurableSpace G := borel G
      letI : BorelSpace G := ⟨rfl⟩
      let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
      (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) ∧
      ∀ f : C(G, ℂ), Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, f ⟨g ^ (n + 1),
          G.pow_mem (subset_closure (Subgroup.mem_zpowers g)) (n + 1)⟩) / (N : ℂ))
        atTop (𝓝 (∫ z : G, f z ∂μ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    let G := (Subgroup.zpowers (1 : ULift.{u} Unit → Circle)).topologicalClosure
    refine ⟨⟨ULift.{u} Unit, 1⟩, (0 : C(G, ℂ)), (1 : C(G, ℂ)), ?_⟩
    intro h
    have hv := congrArg (fun f : C(G, ℂ) => f 1) h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) hv

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result in arena
  readout via (realize signature.{u} (fun _ _ f => f) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "fn",
        "arg", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
