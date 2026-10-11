/- GID: D5/S3/Quantum/SpinChains/BinaryBinBaseChange
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/BinaryBinBaseChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary-bin scalar extension gives a two-bin sl₂ action in characteristic zero. -/

import D5.S3.Quantum.SpinChains.HypereclecticNonShortening
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

open scoped TensorProduct BigOperators
open D5.S3.Quantum.SpinChains.Sl2WeightFiltration

attribute [local instance] LieRing.ofAssociativeRing

namespace D5.S3.Quantum.SpinChains.BinaryBinBaseChange

open HypereclecticNonShortening

variable (K : Type*) [Field K] [CharZero K]

/-- Scalar extension in the finite delta coordinates. -/
noncomputable def extend {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Module.End ℚ (ι → ℚ) →+* Module.End K (ι → K) :=
  (TensorProduct.piScalarRight ℚ K K ι).conjRingEquiv.toRingHom.comp
    (Module.End.baseChangeHom ℚ K (ι → ℚ)).toRingHom

private theorem extend_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Module.End ℚ (ι → ℚ)) (i j : ι) :
    extend K A (Pi.single i 1) j = (A (Pi.single i 1) j : K) := by
  change (TensorProduct.piScalarRight ℚ K K ι)
    (A.baseChange K ((TensorProduct.piScalarRight ℚ K K ι).symm (Pi.single i 1))) j = _
  simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def]

/-- The weight multiplication after scalar extension. -/
noncomputable def binWeight (m : ℕ) : Module.End K ((Fin m → Bool) → K) :=
  extend K (LinearMap.mulLeft ℚ (fun w : Fin m → Bool => weight w))

/-- The raising operator after scalar extension. -/
noncomputable def binRaising (m : ℕ) : Module.End K ((Fin m → Bool) → K) :=
  extend K (Rbin m)

/-- The lowering operator after scalar extension. -/
noncomputable def binLowering (m : ℕ) : Module.End K ((Fin m → Bool) → K) :=
  extend K (Hbin m)

private theorem rational_relations (m : ℕ) :
    Sl2Relations (LinearMap.mulLeft ℚ (fun w : Fin m → Bool => weight w))
      (Rbin m) (Hbin m) := by
  by_cases hm : 2 ≤ m
  · have t := binSl2Triple m hm
    exact ⟨t.lie_e_f, by simpa [Ring.lie_def] using t.lie_h_e_smul (R := ℚ),
      by simpa [Ring.lie_def, neg_smul] using t.lie_lie_smul_f (R := ℚ)⟩
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · constructor <;> ext v w <;> simp [Rbin, Hbin, weight]
    · constructor <;> ext v w <;> simp [Rbin, Hbin, weight]

/-- Relations and the three delta coefficients, with short bins included. -/
theorem bin_action (m : ℕ) :
    Sl2Relations (binWeight K m) (binRaising K m) (binLowering K m) ∧
    ∀ (w u : Fin m → Bool),
      binWeight K m (Pi.single w 1) u = (weight u : K) * (Pi.single w 1 : _ → K) u ∧
      binRaising K m (Pi.single w 1) u = (Rbin m (Pi.single w 1) u : K) ∧
      binLowering K m (Pi.single w 1) u = (Hbin m (Pi.single w 1) u : K) := by
  constructor
  · have a := rational_relations m
    constructor
    · simpa [binWeight, binRaising, binLowering, map_sub, map_mul] using
        congrArg (extend K) a.ef
    · have eq := congrArg (extend K) a.he
      simpa [binWeight, binRaising, map_sub, map_mul, two_smul] using eq
    · have eq := congrArg (extend K) a.hf
      simpa [binWeight, binLowering, map_sub, map_mul, two_smul, neg_smul] using eq
  · intro w u
    refine ⟨?_, extend_basis K (Rbin m) w u, extend_basis K (Hbin m) w u⟩
    rw [binWeight, extend_basis]
    by_cases hu : u = w <;> simp [LinearMap.mulLeft_apply, Pi.single_apply, hu, eq_comm]

end D5.S3.Quantum.SpinChains.BinaryBinBaseChange
