/- GID: D5/S1/Solenoid/StreamlineTheorem
   generality: I
   mirror-B: D5/B/S1/Solenoid/StreamlineTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A continuous solenoid path has one hidden offset throughout its history. -/

import D5.S1.Dynamics.JumpCocycle
import D5.S1.Solenoid.ThroatTransitionCocycle
import Mathlib.Topology.Connected.TotallyDisconnected

namespace D5.S1.Solenoid.StreamlineTheorem

open Set
open D5.S1.Dynamics

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The prime-indexed profinite address carried by a hidden solenoid fiber. -/
abbrev HiddenAddress := ∀ p : Nat.Primes, ℤ_[p.1]

/-- A path together with a continuous visible lift and a topological additive
identification of the hidden kernel with its prime-indexed address. -/
structure StreamlineDecomposition (s : Set ℝ) where
  path : ℝ → UniversalSolenoid
  visibleLift : ℝ → UniversalSolenoid
  sameVisible : UniversalSolenoid.projection ∘ path =
    UniversalSolenoid.projection ∘ visibleLift
  path_continuous : ContinuousOn path s
  visibleLift_continuous : ContinuousOn visibleLift s
  hiddenEquiv : HiddenAddress ≃+ UniversalSolenoid.projection.ker
  hiddenEquiv_symm_continuous :
    Continuous (hiddenEquiv.symm : UniversalSolenoid.projection.ker → HiddenAddress)

/-- The difference between the path and its visible lift, regarded as an
element of the hidden kernel. -/
def kernelDifference {s : Set ℝ} (d : StreamlineDecomposition s) (t : ℝ) :
    UniversalSolenoid.projection.ker :=
  ⟨d.path t - d.visibleLift t, by
    change UniversalSolenoid.projection (d.path t - d.visibleLift t) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun d.sameVisible t)⟩

/-- The prime-indexed throat coordinate of a decomposed solenoid path. -/
noncomputable def throatComponent {s : Set ℝ}
    (d : StreamlineDecomposition s) (t : ℝ) :
    HiddenAddress :=
  d.hiddenEquiv.symm (kernelDifference d t)

/-- The definition of the throat coordinate reconstructs the path as its
visible lift translated by a unique hidden offset. -/
theorem path_decomposition {s : Set ℝ} (d : StreamlineDecomposition s) (t : ℝ) :
    d.path t = d.visibleLift t +
      (d.hiddenEquiv (throatComponent d t) : UniversalSolenoid) := by
  simp [throatComponent, kernelDifference]

private theorem continuousOn_kernelDifference {s : Set ℝ}
    (d : StreamlineDecomposition s) :
    ContinuousOn (kernelDifference d) s := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  simpa [Function.comp_def, kernelDifference] using
    d.path_continuous.sub d.visibleLift_continuous

private theorem continuousOn_throatComponent {s : Set ℝ}
    (d : StreamlineDecomposition s) :
    ContinuousOn (throatComponent d) s := by
  change ContinuousOn
    (fun t => d.hiddenEquiv.symm (kernelDifference d t)) s
  exact d.hiddenEquiv_symm_continuous.comp_continuousOn
    (continuousOn_kernelDifference d)

private theorem hiddenAddress_rigidity {s : Set ℝ} (hs : IsPreconnected s)
    (f : ℝ → HiddenAddress) (hf : ContinuousOn f s) :
    ∀ x ∈ s, ∀ y ∈ s, f x = f y := fun _ hx _ hy =>
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- On a preconnected interval, continuity of a hidden address is equivalent
to agreement with its value at any chosen base point. -/
theorem offset_continuous_iff_constant {s : Set ℝ} (hs : IsPreconnected s)
    (offset : ℝ → HiddenAddress) (x : ℝ) (hx : x ∈ s) :
    ContinuousOn offset s ↔ ∀ y ∈ s, offset y = offset x := by
  constructor
  · intro hoffset y hy
    exact hiddenAddress_rigidity hs offset hoffset y hy x hx
  · intro hconstant
    exact continuousOn_const.congr fun y hy => hconstant y hy

/-- **Streamline theorem.** On a preconnected interval containing the base
time, the throat coordinate relative to time zero vanishes throughout the
history. Consequently the whole path is one continuous visible lift translated
by the single hidden address present at time zero. -/
theorem streamline_constant_offset {s : Set ℝ} (hs : IsPreconnected s)
    (hzero : 0 ∈ s) (d : StreamlineDecomposition s) :
    (∀ t ∈ s, throatComponent d t - throatComponent d 0 = 0) ∧
    ∀ t ∈ s, d.path t = d.visibleLift t +
      (d.hiddenEquiv (throatComponent d 0) : UniversalSolenoid) := by
  have hconstant :=
    (offset_continuous_iff_constant hs (throatComponent d) 0 hzero).mp
      (continuousOn_throatComponent d)
  constructor
  · intro t ht
    exact sub_eq_zero.mpr (hconstant t ht)
  · intro t ht
    rw [path_decomposition d t, hconstant t ht]

/-- A proposed hidden history that takes two different values on a
preconnected interval cannot be continuous. This is the negative witness that
rules out a nonconstant fake streamline. -/
theorem nonconstant_offset_not_continuous {s : Set ℝ} (hs : IsPreconnected s)
    (offset : ℝ → HiddenAddress) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : offset x ≠ offset y) :
    ¬ ContinuousOn offset s := by
  intro hoffset
  exact hxy (((offset_continuous_iff_constant hs offset x hx).mp
    hoffset y hy).symm)

end D5.S1.Solenoid.StreamlineTheorem
