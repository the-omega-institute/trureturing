/- GID: D5/S3/Observer/ObserverMetric
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize observer update defects and their finite perturbation seminorm. -/

import D5.S3.Quantum.ObserverAlgebra
import D5.S3.Quantum.ObserverCommutator

namespace D5.S3.Observer.ObserverMetric

open D5.S3.Quantum.ObserverAlgebra
open D5.S3.Quantum.ObserverCommutator

/- Provenance: OBSERVER-QUANTUM.md, section 3, theorem
   "Observer metric and two types of infinity" (v2). -/

/-- The coefficient of the represented read-update commutator. -/
def updateDefect {index : Type*} (tau : Equiv.Perm index) (f : index → ℂ) :
    index → ℂ :=
  fun i => f (tau.symm i) - f i

/-- Read and update commute on every register exactly when their defect vanishes. -/
theorem commute_iff_updateDefect_eq_zero {index : Type*}
    (tau : Equiv.Perm index) (f : index → ℂ) :
    (∀ psi : Register index, observerUpdate tau (readObservable f psi) =
      readObservable f (observerUpdate tau psi)) ↔ updateDefect tau f = 0 := by
  constructor
  · intro hCommute
    have hZero :
        observerUpdate tau (readObservable f (fun _ => 1)) -
            readObservable f (observerUpdate tau (fun _ => 1)) = 0 :=
      sub_eq_zero.mpr (hCommute (fun _ => 1))
    rw [observer_read_update_commutator_formula] at hZero
    funext i
    simpa [updateDefect] using congrFun hZero i
  · intro hDefect psi
    apply sub_eq_zero.mp
    rw [observer_read_update_commutator_formula]
    funext i
    have hi := congrFun hDefect i
    simpa [updateDefect] using
      congrArg (fun z : ℂ => z * psi (tau.symm i)) hi

/-- A zero update defect is exactly invariance under the supplied permutation. -/
theorem updateDefect_eq_zero_iff_invariant {index : Type*}
    (tau : Equiv.Perm index) (f : index → ℂ) :
    updateDefect tau f = 0 ↔ ∀ i, f (tau i) = f i := by
  constructor
  · intro hDefect i
    have hi := congrFun hDefect (tau i)
    have hSub : f i - f (tau i) = 0 := by
      simpa [updateDefect] using hi
    exact (sub_eq_zero.mp hSub).symm
  · intro hInvariant
    funext i
    apply sub_eq_zero.mpr
    simpa [updateDefect] using (hInvariant (tau.symm i)).symm

/-- On a nonempty cyclic window, the update-invariant observables are precisely constants. -/
theorem invariant_iff_const_on_cyclic_window {M : ℕ} [NeZero M]
    (f : ZMod M → ℂ) :
    updateDefect (Equiv.addRight (1 : ZMod M)) f = 0 ↔
      ∃ c : ℂ, f = Function.const (ZMod M) c := by
  rw [updateDefect_eq_zero_iff_invariant]
  constructor
  · intro hInvariant
    refine ⟨f 0, ?_⟩
    funext i
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective i
    induction n with
    | zero => simp [Function.const]
    | succ n ih =>
        simpa [Nat.cast_succ] using (hInvariant (n : ZMod M)).trans ih
  · rintro ⟨c, rfl⟩ i
    rfl

/-- The largest pointwise update defect on a nonempty finite index type. -/
noncomputable def perturbationSeminorm {index : Type*} [Fintype index] [Nonempty index]
    (tau : Equiv.Perm index) (f : index → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖updateDefect tau f i‖)

/-- The perturbation seminorm vanishes exactly on update-invariant observables. -/
theorem perturbationSeminorm_eq_zero_iff {index : Type*}
    [Fintype index] [Nonempty index] (tau : Equiv.Perm index) (f : index → ℂ) :
    perturbationSeminorm tau f = 0 ↔ ∀ i, f (tau i) = f i := by
  rw [← updateDefect_eq_zero_iff_invariant]
  constructor
  · intro hSeminorm
    funext i
    have hi : ‖updateDefect tau f i‖ ≤ perturbationSeminorm tau f := by
      exact Finset.le_sup' (fun j => ‖updateDefect tau f j‖) (Finset.mem_univ i)
    rw [hSeminorm] at hi
    exact norm_eq_zero.mp (le_antisymm hi (norm_nonneg _))
  · intro hDefect
    simp [perturbationSeminorm, hDefect]

/-- The perturbation seminorm is subadditive. -/
theorem perturbationSeminorm_add_le {index : Type*}
    [Fintype index] [Nonempty index] (tau : Equiv.Perm index)
    (f g : index → ℂ) :
    perturbationSeminorm tau (f + g) ≤
      perturbationSeminorm tau f + perturbationSeminorm tau g := by
  unfold perturbationSeminorm
  apply Finset.sup'_le
  intro i hi
  calc
    ‖updateDefect tau (f + g) i‖ =
        ‖updateDefect tau f i + updateDefect tau g i‖ := by
      congr 1
      simp only [updateDefect, Pi.add_apply]
      ring
    _ ≤ ‖updateDefect tau f i‖ + ‖updateDefect tau g i‖ :=
      norm_add_le _ _
    _ ≤
        Finset.univ.sup' Finset.univ_nonempty (fun j => ‖updateDefect tau f j‖) +
          Finset.univ.sup' Finset.univ_nonempty (fun j => ‖updateDefect tau g j‖) :=
      add_le_add
        (Finset.le_sup' (fun j => ‖updateDefect tau f j‖) hi)
        (Finset.le_sup' (fun j => ‖updateDefect tau g j‖) hi)

/-- The perturbation seminorm is absolutely homogeneous over the complex scalars. -/
theorem perturbationSeminorm_smul {index : Type*}
    [Fintype index] [Nonempty index] (tau : Equiv.Perm index)
    (c : ℂ) (f : index → ℂ) :
    perturbationSeminorm tau (c • f) = ‖c‖ * perturbationSeminorm tau f := by
  unfold perturbationSeminorm
  rw [Finset.mul₀_sup' (norm_nonneg c)
    (fun i => ‖updateDefect tau f i‖) Finset.univ Finset.univ_nonempty]
  refine Finset.sup'_congr Finset.univ_nonempty rfl ?_
  intro i _
  change ‖c * f (tau.symm i) - c * f i‖ =
    ‖c‖ * ‖f (tau.symm i) - f i‖
  rw [← mul_sub, norm_mul]

end D5.S3.Observer.ObserverMetric
