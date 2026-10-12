/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamColimitCuts
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integer-cut coordinates and stationary transition on an integral direct limit. -/
import D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (stationaryTransition StationaryModule induced)

variable {M : Type*} [AddCommGroup M] [Module ℤ M] (T : Module.End ℤ M)

/- The direct-limit construction carries its own `Module ℤ` instance.  The
   generic `AddCommGroup.toIntModule` fallback can otherwise be selected when
   the scalar parameter of `StationaryModule` is hidden behind the abbreviation,
   making the canonical stage map have a definitionally different codomain
   instance. -/
instance stationaryIntModule : Module ℤ (StationaryModule T) :=
  Module.DirectLimit.module (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => M)
    (f := stationaryTransition T)

def stage (N : ℕ) : M →ₗ[ℤ] StationaryModule T :=
  Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => M) (stationaryTransition T) N

/-- The canonical nonnegative upper stage is n.toNat; the exponent is
(-n).toNat. These are the two cases of the same integer-cut definition. -/
def intStage (n : ℤ) : M →ₗ[ℤ] StationaryModule T :=
  (stage T n.toNat).comp (T ^ (-n).toNat)

/-- Independence of EVERY nonnegative upper stage N≥n. -/
theorem intStage_at (n : ℤ) (N : ℕ) (hn : n ≤ (N : ℤ)) (z : M) :
    intStage T n z = stage T N ((T ^ ((N : ℤ) - n).toNat) z) := by
  have hN : n.toNat ≤ N := by omega
  have he : (N - n.toNat) + (-n).toNat = ((N : ℤ) - n).toNat := by omega
  have hf := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => M)
    (f := stationaryTransition T) (i := n.toNat) (j := N) (hij := hN)
    (x := (T ^ (-n).toNat) z)
  change stage T N ((T ^ (N - n.toNat)) ((T ^ (-n).toNat) z)) = intStage T n z at hf
  rw [← Module.End.mul_apply, ← pow_add, he] at hf
  exact hf.symm

@[simp] theorem intStage_nat (N : ℕ) (z : M) : intStage T (N : ℤ) z = stage T N z := by
  simp [intStage]

/-- Genuine forward refinement compatibility, with nonnegative powers only. -/
theorem intStage_refine (n : ℤ) (r : ℕ) (z : M) :
    intStage T n z = intStage T (n + (r : ℤ)) ((T ^ r) z) := by
  let N := (n + (r : ℤ)).toNat
  have hn : n ≤ (N : ℤ) := by dsimp [N]; omega
  have hnr : n + (r : ℤ) ≤ (N : ℤ) := by dsimp [N]; omega
  rw [intStage_at T n N hn, intStage_at T (n + (r : ℤ)) N hnr]
  rw [← Module.End.mul_apply, ← pow_add]
  have he : ((N : ℤ) - (n + (r : ℤ))).toNat + r = ((N : ℤ) - n).toNat := by omega
  rw [he]

/-- Existing stationary transition on the actual integer group. -/
def Theta : Module.End ℤ (StationaryModule T) := induced T T (Commute.refl T)

@[simp] theorem Theta_stage (N : ℕ) (z : M) :
    Theta T (stage T N z) = stage T N (T z) := by
  simp only [Theta, stage, induced, Module.DirectLimit.map_apply_of]

theorem Theta_intStage (n : ℤ) (z : M) : Theta T (intStage T n z) = intStage T n (T z) := by
  change Theta T (stage T n.toNat ((T ^ (-n).toNat) z)) =
    stage T n.toNat ((T ^ (-n).toNat) (T z))
  rw [Theta_stage]
  have he : T * T ^ (-n).toNat = T ^ (-n).toNat * T := (Commute.refl T).pow_right _ |>.eq
  exact congrArg (stage T n.toNat) (LinearMap.congr_fun he z)

/-- Exact direction of unit left shift, including the negative cut at stage 0. -/
theorem intStage_shift (n : ℤ) (z : M) : intStage T (n - 1) z = Theta T (intStage T n z) := by
  have he := intStage_refine T (n - 1) 1 z
  simpa only [Int.natCast_one, sub_add_cancel, pow_one, Theta_intStage] using he

/-- Equality of the actual row transition indices transports the EXISTING
stationary modules without introducing a new colimit foundation. -/
theorem cast_stage (T' : Module.End ℤ M) (h : T = T') (N : ℕ) (z : M) :
    LinearEquiv.cast (R := ℤ) (M := fun P : Module.End ℤ M => StationaryModule P) h
      (stage T N z) = stage T' N z := by
  cases h
  rfl

theorem cast_intStage (T' : Module.End ℤ M) (h : T = T') (n : ℤ) (z : M) :
    LinearEquiv.cast (R := ℤ) (M := fun P : Module.End ℤ M => StationaryModule P) h
      (intStage T n z) = intStage T' n z := by
  cases h
  rfl

end D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
