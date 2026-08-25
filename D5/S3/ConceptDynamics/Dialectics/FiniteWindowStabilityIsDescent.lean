/- GID: D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stability of the finite-window kernel, its forward invariance, and exact descent through the window are equivalent without finiteness or nonemptiness assumptions. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'finite_window_stability_congruence_descent_tfae' D5
     Golden/Frozen/accepted` returned no matches.
   * Full-repository searches for finite-window stability, descent, and the
     depth-one/next-window bridge found no public or private exact result.
   * All three existing modules in the target directory were read by digest;
     none states stability of a finite-window kernel.
   * `deterministic_interface_sixfold_equivalence` supplies the congruence and
     effective-descent equivalence and is specialized below to `finiteWindow q F n`.
   * Pinned Mathlib supplies finite function extensionality and iterate identities;
     no separate theorem states the finite-window bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.FiniteWindowStabilityIsDescent

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
open D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/-- The kernel `K_n` identifies states with the same observations through time `n`. -/
def finiteWindowKernel {X O : Type*} (q : X → O) (F : X → X) (n : Nat) :
    X → X → Prop :=
  depthZeroKernel (finiteWindow q F n)

/-- Adding one update to a depth-`n` window is exactly the depth-`n + 1` kernel. -/
theorem depth_one_finite_window_eq_next_window {X O : Type*}
    (q : X → O) (F : X → X) (n : Nat) :
    depthOneKernel (finiteWindow q F n) F = finiteWindowKernel q F (n + 1) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hCurrent, hShifted⟩
    funext i
    by_cases hi : i.val < n + 1
    · let j : Fin (n + 1) := ⟨i.val, hi⟩
      simpa [j, finiteWindow, orbitTarget, jointTarget, finiteWindowKernel,
        depthZeroKernel] using
        congrFun hCurrent j
    · have hiValue : i.val = n + 1 := by omega
      simpa [finiteWindow, orbitTarget, jointTarget, finiteWindowKernel, depthZeroKernel,
        hiValue, Function.iterate_succ_apply] using congrFun hShifted (Fin.last n)
  · intro hNext
    constructor
    · funext i
      simpa [finiteWindow, orbitTarget, jointTarget, finiteWindowKernel,
        depthZeroKernel] using
        congrFun hNext i.castSucc
    · funext i
      simpa [finiteWindow, orbitTarget, jointTarget, finiteWindowKernel, depthZeroKernel,
        Function.iterate_succ_apply] using congrFun hNext i.succ

/-- Kernel stability, forward invariance, and exact effective descent are equivalent. -/
theorem finite_window_stability_congruence_descent_tfae {X O : Type*}
    (q : X → O) (F : X → X) (n : Nat) :
    List.TFAE [
      finiteWindowKernel q F n = finiteWindowKernel q F (n + 1),
      InterfaceCongruence (finiteWindow q F n) F,
      EffectiveDescent (finiteWindow q F n) F] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hStable
      apply
        ((deterministic_interface_sixfold_equivalence
          (finiteWindow q F n) F).out 5 1).mp
      calc
        depthZeroKernel (finiteWindow q F n) = finiteWindowKernel q F n := rfl
        _ = finiteWindowKernel q F (n + 1) := hStable
        _ = depthOneKernel (finiteWindow q F n) F :=
          (depth_one_finite_window_eq_next_window q F n).symm
    · intro hCongruence
      have hKernels :=
        ((deterministic_interface_sixfold_equivalence
          (finiteWindow q F n) F).out 1 5).mp hCongruence
      calc
        finiteWindowKernel q F n = depthZeroKernel (finiteWindow q F n) := rfl
        _ = depthOneKernel (finiteWindow q F n) F := hKernels
        _ = finiteWindowKernel q F (n + 1) :=
          depth_one_finite_window_eq_next_window q F n
  tfae_have 2 ↔ 3 :=
    (deterministic_interface_sixfold_equivalence (finiteWindow q F n) F).out 1 0
  tfae_finish

example :
    List.TFAE [
      finiteWindowKernel (id : Bool → Bool) Bool.not 0 =
        finiteWindowKernel (id : Bool → Bool) Bool.not 1,
      InterfaceCongruence (finiteWindow (id : Bool → Bool) Bool.not 0) Bool.not,
      EffectiveDescent (finiteWindow (id : Bool → Bool) Bool.not 0) Bool.not] :=
  finite_window_stability_congruence_descent_tfae id Bool.not 0

example :
    List.TFAE [
      finiteWindowKernel (fun x : Empty ↦ (Empty.elim x : Unit))
          (id : Empty → Empty) 0 =
        finiteWindowKernel (fun x : Empty ↦ (Empty.elim x : Unit)) id 1,
      InterfaceCongruence
        (finiteWindow (fun x : Empty ↦ (Empty.elim x : Unit)) id 0)
        (id : Empty → Empty),
      EffectiveDescent
        (finiteWindow (fun x : Empty ↦ (Empty.elim x : Unit)) id 0)
        (id : Empty → Empty)] :=
  finite_window_stability_congruence_descent_tfae
    (fun x : Empty ↦ (Empty.elim x : Unit)) id 0

#print axioms finite_window_stability_congruence_descent_tfae

end D5.S3.ConceptDynamics.Dialectics.FiniteWindowStabilityIsDescent
