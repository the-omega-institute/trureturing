/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSCompactFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSCompactFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Topology.DiscreteSubset]
   utility: none
   digest: Compact locally injective fibers are finite and nearby fibers stay in their charts. -/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Hausdorff

/-! Compactness confines observations near a locally injective fiber to finitely many charts. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber

open Set

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

/-- A closed neighborhood complement in the compact source cannot acquire a
preimage of a nearby value if it has none over the center. -/
theorem nearby_fibers_subset {f : X → Y} (hf : Continuous f) {y : Y} {V : Set X}
    (hV : IsOpen V) (hcover : f ⁻¹' {y} ⊆ V) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ f ⁻¹' W ⊆ V := by
  refine ⟨(f '' Vᶜ)ᶜ, (hf.isClosedMap _ hV.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hcover hxy)
  · intro x hx
    by_contra hnx
    exact hx ⟨x, hnx, rfl⟩

/-- When the map is locally injective at every point of a fiber, the fiber
consists of finitely many points. -/
theorem finite_fiber_of_local_injective {f : X → Y} (hf : Continuous f) (y : Y)
    (hlocal : ∀ x ∈ f ⁻¹' {y}, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    (f ⁻¹' {y}).Finite := by
  refine (isClosed_singleton.preimage hf).isCompact.finite ?_
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨U, hU, hxU, hI⟩ := hlocal x hx
  refine ⟨U, hU, ?_⟩
  ext z
  constructor
  · rintro ⟨hzU, hz⟩
    exact hI hzU hxU (hz.trans hx.symm)
  · rintro (rfl : z = x)
    exact ⟨hxU, hx⟩

/-- A saturated open dense subset of a compact source descends to a relatively
open dense subset of its image. A dense set of ordinary source points suffices
to witness density of the descended set. -/
theorem descend_open_dense {f : X → Y} (hf : Continuous f) {G D : Set X}
    (hG : IsOpen G) (hdense : Dense G) (hD : Dense D)
    (hsat : ∀ x ∈ G, ∀ y, f y = f x → y ∈ G) :
    ∃ W : Set Y, IsOpen W ∧
      f '' G = range f ∩ W ∧ range f ⊆ closure (f '' (G ∩ D)) := by
  let W := (f '' Gᶜ)ᶜ
  refine ⟨W, (hf.isClosedMap _ hG.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_range_self _, ?_⟩
      rintro ⟨z, hz, he⟩
      exact hz (hsat x hx z he)
    · rintro ⟨⟨x, rfl⟩, hx⟩
      refine ⟨x, ?_, rfl⟩
      by_contra hnx
      exact hx ⟨x, hnx, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact (image_closure_subset_closure_image hf ⟨x,
      (hdense.inter_of_isOpen_left hD hG) x, rfl⟩)

end D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber
