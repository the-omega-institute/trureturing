/- GID: D5/S1/Solenoid/StreamlineTheorem
   generality: I
   mirror-B: D5/B/S1/Solenoid/StreamlineTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A supplied decomposition has a continuous throat offset iff that offset is constant. -/

import D5.S1.Dynamics.UniversalSolenoid
import D5.S3.Arith.HiddenFiberRigidity

namespace D5.S1.Solenoid.StreamlineTheorem

open Set
open D5.S1.Dynamics

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The prime-indexed profinite address carried by a hidden solenoid fiber. -/
abbrev HiddenAddress := ∀ p : Nat.Primes, ℤ_[p.1]

/-- A supplied visible/hidden decomposition of a solenoid-valued history.

This is input data: the declaration does not construct a canonical visible
lift or prove that every continuous solenoid path admits such a decomposition. -/
structure StreamlineDecomposition where
  path : ℝ → UniversalSolenoid
  visibleLift : ℝ → UniversalSolenoid
  sameVisible : UniversalSolenoid.projection ∘ path =
    UniversalSolenoid.projection ∘ visibleLift
  hiddenEquiv : HiddenAddress ≃+ UniversalSolenoid.projection.ker

/-- The difference between the path and its visible lift, regarded as an
element of the hidden kernel. -/
def kernelDifference (d : StreamlineDecomposition) (t : ℝ) :
    UniversalSolenoid.projection.ker :=
  ⟨d.path t - d.visibleLift t, by
    change UniversalSolenoid.projection (d.path t - d.visibleLift t) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun d.sameVisible t)⟩

/-- The prime-indexed throat coordinate of a decomposed solenoid path. -/
noncomputable def throatComponent
    (d : StreamlineDecomposition) (t : ℝ) :
    HiddenAddress :=
  d.hiddenEquiv.symm (kernelDifference d t)

/-- The definition of the throat coordinate reconstructs the path as its
visible lift translated by a unique hidden offset. -/
theorem path_decomposition (d : StreamlineDecomposition) (t : ℝ) :
    d.path t = d.visibleLift t +
      (d.hiddenEquiv (throatComponent d t) : UniversalSolenoid) := by
  simp [throatComponent, kernelDifference]

/-- **Conditional streamline rigidity.** Given a decomposition and a base point
in a preconnected interval, its throat offset is continuous exactly when it is
constant there. Existence or canonicity of the supplied decomposition is a
separate residual, not a conclusion of this theorem. -/
theorem streamline_offset_continuous_iff_constant {s : Set ℝ}
    (hs : IsPreconnected s) (d : StreamlineDecomposition)
    (x : ℝ) (hx : x ∈ s) :
    ContinuousOn (throatComponent d) s ↔
      ∀ y ∈ s, throatComponent d y = throatComponent d x := by
  constructor
  · intro hoffset y hy
    exact D5.S3.Arith.HiddenFiberRigidity.hidden_fiber_rigidity
      hs (throatComponent d) hoffset y hy x hx
  · intro hconstant
    exact continuousOn_const.congr fun y hy => hconstant y hy

/-- A proposed hidden history that takes two different values on a
preconnected interval cannot be continuous. This is the negative witness that
rules out a nonconstant candidate throat offset. -/
theorem nonconstant_offset_not_continuous {s : Set ℝ} (hs : IsPreconnected s)
    (offset : ℝ → HiddenAddress) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : offset x ≠ offset y) :
    ¬ ContinuousOn offset s := by
  intro hoffset
  exact hxy (D5.S3.Arith.HiddenFiberRigidity.hidden_fiber_rigidity
    hs offset hoffset x hx y hy)

end D5.S1.Solenoid.StreamlineTheorem
