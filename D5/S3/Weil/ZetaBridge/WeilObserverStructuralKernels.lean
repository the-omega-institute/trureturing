/- GID: D5/S3/Weil/ZetaBridge/WeilObserverStructuralKernels
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilObserverStructuralKernels
   mirror-E: none(waiver:infinite-state-structural-observer-interface)
   anchors: []
   digest: Prove faithful inclusion-reversing channel kernels on actual Weil tests, explicit leave-one-channel-out witnesses, and common-depth kernel invariance. -/

import D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder

/-!
# Structural kernels of the actual scalar-even observer

The state type is the actual `WeilTestFunction`. Finite channel count does not
make that state type finite. The results give equivalence kernels and strict
pair witnesses on this original state space. They do not assign finite-state
collision rates or assert occurrence registration in a maximal theorem catalog.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilObserverStructuralKernels

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FiniteEvenWeilOrbitFrame Z ι)

/-- Equality kernel of the specified finite set of actual odd readouts. -/
def frameObserverKernel (S : Finset ι) (g h : WeilTestFunction) : Prop :=
  ∀ i ∈ S, frameOddReadout F g i = frameOddReadout F h i

/-- The observer relation is an equivalence relation on the actual test type. -/
theorem frameObserverKernel_equivalence (S : Finset ι) :
    Equivalence (frameObserverKernel F S) := by
  constructor
  · intro g i _
    rfl
  · intro g h hgh i hi
    exact (hgh i hi).symm
  · intro g h k hgh hhk i hi
    exact (hgh i hi).trans (hhk i hi)

/-- Existing interpolation identifies the pullback kernel exactly. -/
theorem frameObserverKernel_synthesis_iff
    (S : Finset ι) (a b : ι → ℂ) :
    frameObserverKernel F S (frameOddSynthesis F a) (frameOddSynthesis F b) ↔
      ∀ i ∈ S, a i = b i := by
  simp only [frameObserverKernel, frameOddSynthesis_readout]

/-- Every channel has an exclusive pair of actual tests relative to all other
channels of the given frame. The frame remains an input. -/
theorem frameObserver_leave_one_out_witness (i : ι) :
    ∃ g h : WeilTestFunction,
      (∀ j : ι, j ≠ i → frameOddReadout F g j = frameOddReadout F h j) ∧
      frameOddReadout F g i ≠ frameOddReadout F h i := by
  refine ⟨frameOddSynthesis F (frameDelta i),
    frameOddSynthesis F (fun _ => 0), ?_, ?_⟩
  · intro j hji
    simp only [frameOddSynthesis_readout]
    simp [frameDelta, hji]
  · simp only [frameOddSynthesis_readout]
    simp [frameDelta]

/-- Channel inclusion is exactly reverse inclusion of equality kernels. -/
theorem frameObserverKernel_refines_iff (S T : Finset ι) :
    (∀ g h : WeilTestFunction,
      frameObserverKernel F T g h → frameObserverKernel F S g h) ↔ S ⊆ T := by
  constructor
  · intro hrefines i hiS
    by_contra hiT
    obtain ⟨g, h, hother, hdistinguish⟩ := frameObserver_leave_one_out_witness F i
    have hT : frameObserverKernel F T g h := by
      intro j hjT
      apply hother j
      intro hji
      exact hiT (hji ▸ hjT)
    exact hdistinguish (hrefines g h hT i hiS)
  · intro hST g h hT i hiS
    exact hT i (hST hiS)

/-- Distinct channel subsets have distinct equality kernels. -/
theorem frameObserverKernel_eq_iff (S T : Finset ι) :
    frameObserverKernel F S = frameObserverKernel F T ↔ S = T := by
  constructor
  · intro hkernel
    apply Finset.Subset.antisymm
    · apply (frameObserverKernel_refines_iff F S T).1
      intro g h hT
      rw [hkernel]
      exact hT
    · apply (frameObserverKernel_refines_iff F T S).1
      intro g h hS
      rw [← hkernel]
      exact hS
  · rintro rfl
    rfl

/-- Joining observations intersects their kernels. -/
theorem frameObserverKernel_union (S T : Finset ι) (g h : WeilTestFunction) :
    frameObserverKernel F (S ∪ T) g h ↔
      frameObserverKernel F S g h ∧ frameObserverKernel F T g h := by
  constructor
  · intro hST
    exact ⟨fun i hi => hST i (Finset.mem_union_left T hi),
      fun i hi => hST i (Finset.mem_union_right S hi)⟩
  · rintro ⟨hS, hT⟩ i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · exact hS i hiS
    · exact hT i hiT

/-- Removing one channel strictly enlarges the kernel, witnessed by tests. -/
theorem frameObserverKernel_strict_leave_one_out (i : ι) :
    (∀ g h : WeilTestFunction,
      frameObserverKernel F Finset.univ g h →
        frameObserverKernel F (Finset.univ.erase i) g h) ∧
    ∃ g h : WeilTestFunction,
      frameObserverKernel F (Finset.univ.erase i) g h ∧
      ¬ frameObserverKernel F Finset.univ g h := by
  constructor
  · intro g h hall j _
    exact hall j (Finset.mem_univ j)
  · obtain ⟨g, h, hother, hdistinguish⟩ := frameObserver_leave_one_out_witness F i
    refine ⟨g, h, ?_, ?_⟩
    · intro j hj
      exact hother j (Finset.mem_erase.mp hj).1
    · intro hall
      exact hdistinguish (hall i (Finset.mem_univ i))

/-- Common-depth localization preserves the selected-channel pullback kernel. -/
theorem frameObserverKernel_burnol_iff
    (P : OrbitBurnolPacket F) (N : ℕ) (S : Finset ι) (a b : ι → ℂ) :
    frameObserverKernel F S (burnolSynthesis F P N a) (burnolSynthesis F P N b) ↔
      ∀ i ∈ S, a i = b i := by
  simp only [frameObserverKernel, burnolSynthesis_readout]

/-- Power depth changes no distinction on the fixed selected observer. -/
theorem frameObserverKernel_burnol_depth_invariant
    (P : OrbitBurnolPacket F) (N M : ℕ) (S : Finset ι) (a b : ι → ℂ) :
    frameObserverKernel F S (burnolSynthesis F P N a) (burnolSynthesis F P M b) ↔
      ∀ i ∈ S, a i = b i := by
  simp only [frameObserverKernel, burnolSynthesis_readout]

/-- Localization and interpolation have identical selected pullback kernels. -/
theorem frameObserverKernel_burnol_eq_interpolation
    (P : OrbitBurnolPacket F) (N : ℕ) (S : Finset ι) (a b : ι → ℂ) :
    frameObserverKernel F S (burnolSynthesis F P N a) (burnolSynthesis F P N b) ↔
      frameObserverKernel F S (frameOddSynthesis F a) (frameOddSynthesis F b) := by
  rw [frameObserverKernel_burnol_iff, frameObserverKernel_synthesis_iff]

#print axioms frameObserverKernel_refines_iff
#print axioms frameObserverKernel_eq_iff
#print axioms frameObserverKernel_strict_leave_one_out
#print axioms frameObserverKernel_burnol_depth_invariant

end D5.S3.Weil.ZetaBridge.WeilObserverStructuralKernels
