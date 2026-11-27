/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularLevelGraphs
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularLevelGraphs
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ImplicitContDiff]
   utility: none
   digest: Countably many differentiable implicit graphs cover a regular level set. -/
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Bases

/-! The local implicit function theorem and second countability give a
countable graph cover in a fixed projection direction. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularLevelGraphs

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

/-- A subset of a level on which the derivative in the last variable is
invertible is covered by countably many graphs over the first variable. -/
theorem countable_cover_regular_level (f : E × ℝ → ℝ) (A : Set (E × ℝ)) (r : ℝ)
    (h₀ : ∀ p ∈ A, f p = r) (h₁ : ∀ p ∈ A, ContDiffAt ℝ 1 f p)
    (h₂ : ∀ p ∈ A, (fderiv ℝ f p ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible) :
    ∃ (C : Set (E × ℝ)) (D : C → Set E) (g : C → E → ℝ),
      C.Countable ∧ (∀ p, DifferentiableOn ℝ (g p) (D p)) ∧
        A ⊆ ⋃ p : C, (fun x => (x, g p x)) '' D p := by
  classical
  have local_graph (p : E × ℝ) (hp : p ∈ A) :
      ∃ (g : E → ℝ) (D : Set E) (U : Set (E × ℝ)),
        U ∈ 𝓝 p ∧ DifferentiableOn ℝ g D ∧
        ∀ q ∈ U, f q = r → q.1 ∈ D ∧ g q.1 = q.2 := by
    let g := (h₁ p hp).implicitFunction one_ne_zero (h₂ p hp)
    have hg : ContDiffAt ℝ 1 g p.1 :=
      (h₁ p hp).contDiffAt_implicitFunction one_ne_zero (h₂ p hp)
    let D : Set E := {x | ContDiffAt ℝ 1 g x}
    have hD : D ∈ 𝓝 p.1 := hg.eventually (by simp)
    let U : Set (E × ℝ) := Prod.fst ⁻¹' D ∩ {q | f q = r ↔ g q.1 = q.2}
    have hU : U ∈ 𝓝 p := by
      apply inter_mem (continuous_fst.continuousAt.preimage_mem_nhds hD)
      change ∀ᶠ q in 𝓝 p, f q = r ↔ g q.1 = q.2
      simpa only [h₀ p hp] using
        (h₁ p hp).eventually_apply_eq_iff_implicitFunction one_ne_zero (h₂ p hp)
    exact ⟨g, D, U, hU, fun _ hx => hx.differentiableAt_one.differentiableWithinAt,
      fun q hq hqf => ⟨hq.1, hq.2.mp hqf⟩⟩
  choose g D U hU hdiff hgraph using local_graph
  let chosen (p : E × ℝ) : Set (E × ℝ) := if hp : p ∈ A then U p hp else ∅
  have hn (p : E × ℝ) (hp : p ∈ A) : chosen p ∈ 𝓝[A] p := by
    have h := hU p hp
    apply nhdsWithin_le_nhds
    simpa [chosen, hp] using h
  obtain ⟨C, hC, hcount, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin hn
  refine ⟨C, fun p => D p (hC p.property), fun p => g p (hC p.property),
    hcount, fun p => hdiff p (hC p.property), ?_⟩
  intro q hq
  obtain ⟨p, hpC, hqp⟩ := mem_iUnion₂.mp (hcover hq)
  have hpA := hC hpC
  have hu : q ∈ U p hpA := by simpa [chosen, hpA] using hqp
  obtain ⟨hqD, he⟩ := hgraph p hpA q hu (h₀ q hq)
  exact mem_iUnion.mpr ⟨⟨p, hpC⟩, ⟨q.1, hqD, Prod.ext rfl he⟩⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A graph over a covered base preserves the dimensions of the maps that
cover the base, including on restricted domains. -/
theorem lift_graph_cover {ι κ : Type*} (A : Set (E × ℝ))
    (D : ι → Set H) (p : ι → H → E) (U : κ → Set E) (g : κ → E → ℝ)
    (hp : ∀ i, DifferentiableOn ℝ (p i) (D i))
    (hg : ∀ j, DifferentiableOn ℝ (g j) (U j))
    (hbase : Prod.fst '' A ⊆ ⋃ i, p i '' D i)
    (hgraph : A ⊆ ⋃ j, (fun x => (x, g j x)) '' U j) :
    ∃ (V : ι × κ → Set H) (q : ι × κ → H → E × ℝ),
      (∀ i, DifferentiableOn ℝ (q i) (V i)) ∧ A ⊆ ⋃ i, q i '' V i := by
  let V : ι × κ → Set H := fun ij => D ij.1 ∩ p ij.1 ⁻¹' U ij.2
  let q : ι × κ → H → E × ℝ := fun ij x => (p ij.1 x, g ij.2 (p ij.1 x))
  refine ⟨V, q, ?_, ?_⟩
  · intro ij
    have h : DifferentiableOn ℝ (p ij.1) (V ij) := (hp ij.1).mono inter_subset_left
    exact h.prodMk ((hg ij.2).comp h inter_subset_right)
  · intro x hx
    obtain ⟨i, u, hu, he⟩ := mem_iUnion.mp (hbase ⟨x, hx, rfl⟩)
    obtain ⟨j, y, hy, hz⟩ := mem_iUnion.mp (hgraph hx)
    have hye : y = x.1 := congrArg Prod.fst hz
    refine mem_iUnion.mpr ⟨(i, j), ⟨u, ⟨hu, ?_⟩, ?_⟩⟩
    · change p i u ∈ U j
      rwa [he, ← hye]
    · change (p i u, g j (p i u)) = x
      rwa [he, ← hye]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularLevelGraphs
