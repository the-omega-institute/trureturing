import D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
open Filter MeasureTheory Set
open scoped Topology
open _root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

private abbrev full (I : Type u) : ClosedSubgroup (I → Circle) :=
  ⟨⊤, isClosed_univ⟩

private abbrev trivial (I : Type u) : ClosedSubgroup (I → Circle) :=
  ⟨⊥, isClosed_singleton⟩

abbrev signature : Signature where
  Params := Type u
  State I := ClosedSubgroup (I → Circle)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := ClosedSubgroup (I → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ I _ => trivial I) (fun e => nomatch e)

/-- The original Hausdorff premise, dictionaries and both probability-measure topologies
are fixed. Only the subgroup occurrence in the limiting ambient Haar measure is read out. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I]
    (Hn : ℕ → ClosedSubgroup (I → Circle)) (H : ClosedSubgroup (I → Circle)),
    Tendsto (fun n => Metric.hausdorffDist (Hn n : Set (I → Circle))
      (H : Set (I → Circle))) atTop (𝓝 0) →
    letI : MeasurableSpace (I → Circle) := borel _
    letI : BorelSpace (I → Circle) := ⟨rfl⟩
    Tendsto (fun n => ambientHaar (Hn n)) atTop (𝓝 (ambientHaar (r.readout () I H)))

/-- The coordinate character separates full-torus Haar from trivial-subgroup Haar. -/
theorem top_ne_bot :
    ambientHaar (full (ULift.{u} Unit)) ≠ ambientHaar (trivial (ULift.{u} Unit)) := by
  let I := ULift.{u} Unit
  letI : MeasurableSpace (I → Circle) := borel _
  letI : BorelSpace (I → Circle) := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : MeasurableSpace K := borel K
  let (K : ClosedSubgroup (I → Circle)) : BorelSpace K := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : IsTopologicalGroup K :=
    inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let μ (K : ClosedSubgroup (I → Circle)) : Measure K := Measure.haarMeasure ⊤
  let (K : ClosedSubgroup (I → Circle)) : IsProbabilityMeasure (μ K) :=
    ⟨Measure.haarMeasure_self⟩
  let f : (I → Circle) → ℂ := fun z => (z ⟨()⟩ : ℂ)
  have hf : Continuous f := by fun_prop
  have hmap (K : ClosedSubgroup (I → Circle)) :
      ∫ x, f x ∂(ambientHaar K : Measure (I → Circle)) = ∫ x : K, f x ∂μ K :=
    integral_map continuous_subtype_val.measurable.aemeasurable
      hf.aestronglyMeasurable
  have hb : (∫ x : (trivial I), f x ∂μ (trivial I)) = 1 := by
    apply integral_eq_const
    apply Eventually.of_forall
    intro x
    have hx : (x : I → Circle) = 1 := x.property
    simp [f, hx]
  have ht : (∫ x : (full I), f x ∂μ (full I)) = 0 := by
    let a : (full I) := ⟨fun _ => -1, Set.mem_univ _⟩
    have h := integral_mul_left_eq_self (μ := μ (full I))
      (fun x : (full I) => f x) a
    have he : (fun x : (full I) => f ((a * x : full I) : I → Circle)) =
        (fun x : (full I) => (-1 : ℂ) * f x) := by
      funext x
      simp [f, a]
    rw [he, integral_const_mul] at h
    linear_combination - (1 / 2 : ℂ) * h
  intro h
  have hi := congrArg (fun ν : @ProbabilityMeasure (I → Circle) (borel _) =>
    ∫ x, f x ∂(ν : Measure (I → Circle))) h
  rw [hmap, hmap, ht, hb] at hi
  exact zero_ne_one hi

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I := ULift.{u} Unit
  letI : MeasurableSpace (I → Circle) := borel _
  letI : BorelSpace (I → Circle) := ⟨rfl⟩
  have ht := h (fun _ => (full I)) (full I) (by
    simp only [Metric.hausdorffDist_self_zero]
    exact tendsto_const_nhds)
  change Tendsto (fun _ : ℕ => ambientHaar (full I))
    atTop (𝓝 (ambientHaar (trivial I))) at ht
  exact top_ne_bot (tendsto_nhds_unique tendsto_const_nhds ht)

def registration : Registration arena.{u}
    (∀ {I : Type u} [Fintype I]
      (Hn : ℕ → ClosedSubgroup (I → Circle)) (H : ClosedSubgroup (I → Circle)),
      Tendsto (fun n => Metric.hausdorffDist (Hn n : Set (I → Circle))
        (H : Set (I → Circle))) atTop (𝓝 0) →
      letI : MeasurableSpace (I → Circle) := borel _
      letI : BorelSpace (I → Circle) := ⟨rfl⟩
      Tendsto (fun n => ambientHaar (Hn n)) atTop (𝓝 (ambientHaar H))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result,
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
    refine ⟨ULift.{u} Unit, full (ULift.{u} Unit), trivial (ULift.{u} Unit), ?_⟩
    intro h
    exact top_ne_bot (congrArg ambientHaar h)

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result in arena
  readout via (realize signature.{u} (fun _ _ H => H) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
