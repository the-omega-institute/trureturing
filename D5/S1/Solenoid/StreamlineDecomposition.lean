/- GID: D5/S1/Solenoid/StreamlineDecomposition
   generality: I
   mirror-B: D5/B/S1/Solenoid/StreamlineDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every continuous solenoid path has a unique base-normalized real
     lift and constant hidden offset. -/

/- Library-search audit trail (2026-08-12):
   * `AddCircle.isCoveringMap_coe` and
     `IsCoveringMap.existsUnique_continuousMap_lifts` supply the normalized
     lift of the visible projection.
   * `AddCircle.finite_torsion`, `Set.Finite.isDiscrete`, and
     `IsPreconnected.constant_of_mapsTo` make each coordinate of the hidden
     difference constant.
   * No library theorem packages the resulting universal-solenoid
     decomposition, so only that assembly is proved here.
-/

import D5.S1.Dynamics.UniversalSolenoid
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

namespace D5.S1.Solenoid.StreamlineDecomposition

open Function Set
open D5.S1.Dynamics

/-- The canonical representative in `[0, 1)` of the path's visible phase at
the normalization time. -/
noncomputable def baseRepresentative (path : C(ℝ, UniversalSolenoid))
    (t0 : ℝ := 0) : ℝ :=
  AddCircle.equivIco (1 : ℝ) 0 (UniversalSolenoid.projection (path t0))

@[simp] theorem coe_baseRepresentative (path : C(ℝ, UniversalSolenoid))
    (t0 : ℝ := 0) :
    ((baseRepresentative path t0 : ℝ) : AddCircle (1 : ℝ)) =
      UniversalSolenoid.projection (path t0) := by
  exact AddCircle.coe_equivIco

private noncomputable def projectedPath
    (path : C(ℝ, UniversalSolenoid)) : C(ℝ, AddCircle (1 : ℝ)) where
  toFun t := UniversalSolenoid.projection (path t)
  continuous_toFun :=
    UniversalSolenoid.continuous_projection.comp path.continuous

private theorem coordinate_torsion
    (theta : UniversalSolenoid)
    (htheta : UniversalSolenoid.projection theta = 0) (m : ℕ+) :
    m.1 • theta.1 m = 0 := by
  calc
    m.1 • theta.1 m = theta.1 ⟨1, Nat.zero_lt_one⟩ := by
      simpa using theta.2 ⟨1, Nat.zero_lt_one⟩ m
    _ = UniversalSolenoid.projection theta := rfl
    _ = 0 := htheta

private theorem continuous_kernel_motion_constant
    (motion : C(ℝ, UniversalSolenoid))
    (hmotion : ∀ t, UniversalSolenoid.projection (motion t) = 0) :
    ∀ s t, motion s = motion t := by
  intro s t
  apply Subtype.ext
  funext m
  let coordinate : ℝ → AddCircle (1 : ℝ) := fun u => (motion u).1 m
  have hcontinuous : Continuous coordinate :=
    ((continuous_apply m).comp continuous_subtype_val).comp motion.continuous
  have hmaps : MapsTo coordinate Set.univ
      {u : AddCircle (1 : ℝ) | m.1 • u = 0} := by
    intro u _
    exact coordinate_torsion (motion u) (hmotion u) m
  exact isPreconnected_univ.constant_of_mapsTo
    (AddCircle.finite_torsion (1 : ℝ) m.2).isDiscrete hcontinuous.continuousOn
    hmaps (by simp) (by simp)

/-- After fixing one real representative of the visible phase at one time,
every continuous solenoid path has exactly one continuous real lift and one
time-independent hidden offset. The normalization is necessary: without it,
integer translates of the real lift give the same visible phase. -/
theorem existsUnique_streamline
    (path : C(ℝ, UniversalSolenoid)) (t0 r0 : ℝ)
    (hRepresentative :
      ((r0 : ℝ) : AddCircle (1 : ℝ)) =
        UniversalSolenoid.projection (path t0)) :
    ∃! data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker,
      data.1 t0 = r0 ∧
        ∀ t, path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1 := by
  rcases (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      (projectedPath path) t0 r0 hRepresentative with
    ⟨lift, hlift, hliftUnique⟩
  let difference : C(ℝ, UniversalSolenoid) :=
    ⟨fun t => path t - UniversalSolenoid.realFlow (lift t),
      path.continuous.sub
        (UniversalSolenoid.continuous_realFlow.comp lift.continuous)⟩
  have hdifferenceKernel (t : ℝ) :
      UniversalSolenoid.projection (difference t) = 0 := by
    rw [show difference t = path t - UniversalSolenoid.realFlow (lift t) from rfl,
      UniversalSolenoid.projection.map_sub,
      UniversalSolenoid.projection_realFlow]
    exact sub_eq_zero.mpr (congrFun hlift.2 t).symm
  let hidden : UniversalSolenoid.projection.ker :=
    ⟨difference t0, hdifferenceKernel t0⟩
  have hdifferenceConstant (t : ℝ) : difference t = hidden.1 :=
    continuous_kernel_motion_constant difference hdifferenceKernel t t0
  refine ⟨(lift, hidden), ?_, ?_⟩
  · refine ⟨hlift.1, fun t => ?_⟩
    rw [show hidden.1 = difference t from (hdifferenceConstant t).symm]
    simp [difference]
  · rintro ⟨otherLift, otherHidden⟩ ⟨hotherBase, hotherReconstruct⟩
    have hotherProjection :
        ((fun t : ℝ => (t : AddCircle (1 : ℝ))) ∘ otherLift) =
          projectedPath path := by
      funext t
      have hreconstruct := congrArg UniversalSolenoid.projection
        (hotherReconstruct t)
      change ((otherLift t : ℝ) : AddCircle (1 : ℝ)) =
        UniversalSolenoid.projection (path t)
      rw [hreconstruct, map_add, UniversalSolenoid.projection_realFlow,
        otherHidden.property, add_zero]
    have hLift : otherLift = lift :=
      hliftUnique otherLift ⟨hotherBase, hotherProjection⟩
    subst otherLift
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply add_left_cancel (a := UniversalSolenoid.realFlow (lift t0))
      calc
        UniversalSolenoid.realFlow (lift t0) + otherHidden.1 = path t0 :=
          (hotherReconstruct t0).symm
        _ = UniversalSolenoid.realFlow (lift t0) + hidden.1 := by
          rw [show hidden.1 = difference t0 from rfl]
          simp [difference]

/-- The canonical `[0, 1)` representative gives a choice-free normalized
version at any specified base time. -/
theorem existsUnique_normalized_streamline
    (path : C(ℝ, UniversalSolenoid)) (t0 : ℝ := 0) :
    ∃! data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker,
      data.1 t0 = baseRepresentative path t0 ∧
        ∀ t, path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1 :=
  existsUnique_streamline path t0 (baseRepresentative path t0)
    (coe_baseRepresentative path t0)

/-- The real-flow element at time one is invisible at the visible coordinate. -/
noncomputable def hiddenUnitOffset : UniversalSolenoid.projection.ker :=
  ⟨UniversalSolenoid.realFlow 1, by
    change UniversalSolenoid.projection (UniversalSolenoid.realFlow 1) = 0
    rw [UniversalSolenoid.projection_realFlow]
    exact AddCircle.coe_period (1 : ℝ)⟩

/-- The invisible unit-flow offset is nevertheless nonzero, as its
modulus-two coordinate is the nonzero class of one half. -/
theorem hiddenUnitOffset_ne_zero : hiddenUnitOffset ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (fun theta : UniversalSolenoid.projection.ker =>
      theta.1.1 (⟨2, by norm_num⟩ : ℕ+)) hzero
  change (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 at hcoordinate
  rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoordinate with ⟨z, hz⟩
  have hz' : (z : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hz
  have : (2 : ℤ) * z = 1 := by
    exact_mod_cast (show (2 : ℝ) * z = 1 by linarith)
  omega

private noncomputable def translatedRealFlow : C(ℝ, UniversalSolenoid) :=
  ⟨fun t => UniversalSolenoid.realFlow t + hiddenUnitOffset.1,
    UniversalSolenoid.continuous_realFlow.add continuous_const⟩

/-- Anti-vacuity witness: the translated real-flow path has a nonconstant
normalized visible lift and a provably nonzero constant hidden offset. The
whole pair is still unique under the same base normalization. -/
theorem translated_realFlow_has_nonzero_hidden_offset :
    ∃! data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker,
      data.1 0 = baseRepresentative translatedRealFlow 0 ∧
        (∀ t, translatedRealFlow t =
          UniversalSolenoid.realFlow (data.1 t) + data.2.1) ∧
        data.1 0 ≠ data.1 1 ∧ data.2 ≠ 0 := by
  let identityLift : C(ℝ, ℝ) := ⟨id, continuous_id⟩
  have hbase : baseRepresentative translatedRealFlow 0 = 0 := by
    change ((AddCircle.equivIco (1 : ℝ) 0)
      (UniversalSolenoid.projection (translatedRealFlow 0)) : ℝ) = 0
    have hphase : UniversalSolenoid.projection (translatedRealFlow 0) = 0 := by
      simp [translatedRealFlow, hiddenUnitOffset,
        UniversalSolenoid.projection_realFlow]
    rw [hphase]
    exact congrArg Subtype.val
      (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0)
        (x := (0 : ℝ)) (by norm_num))
  have hproperties :
      identityLift 0 = baseRepresentative translatedRealFlow 0 ∧
        (∀ t, translatedRealFlow t =
          UniversalSolenoid.realFlow (identityLift t) + hiddenUnitOffset.1) ∧
        identityLift 0 ≠ identityLift 1 ∧ hiddenUnitOffset ≠ 0 := by
    refine ⟨by simp [hbase, identityLift], fun _ => rfl, ?_,
      hiddenUnitOffset_ne_zero⟩
    norm_num [identityLift]
  refine ⟨(identityLift, hiddenUnitOffset), hproperties, ?_⟩
  rintro ⟨otherLift, otherHidden⟩ hother
  rcases existsUnique_normalized_streamline translatedRealFlow 0 with
    ⟨canonical, hcanonical, hcanonicalUnique⟩
  have hIdentity : (identityLift, hiddenUnitOffset) = canonical :=
    hcanonicalUnique _ ⟨hproperties.1, hproperties.2.1⟩
  have hOther : (otherLift, otherHidden) = canonical :=
    hcanonicalUnique _ ⟨hother.1, hother.2.1⟩
  exact hOther.trans hIdentity.symm

end D5.S1.Solenoid.StreamlineDecomposition
