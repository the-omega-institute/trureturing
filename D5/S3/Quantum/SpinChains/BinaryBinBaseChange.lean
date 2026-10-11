/- GID: D5/S3/Quantum/SpinChains/BinaryBinBaseChange
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/BinaryBinBaseChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary-bin scalar extension gives a two-bin sl₂ action in characteristic zero. -/

import D5.S3.Quantum.SpinChains.Sl2WeightFiltration
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
  LinearMap.mulLeft K (fun w : Fin m → Bool => (weight w : K))

private theorem weight_extension (m : ℕ) :
    extend K (LinearMap.mulLeft ℚ (fun w : Fin m → Bool => weight w)) =
      binWeight K m := by
  apply (Pi.basisFun K (Fin m → Bool)).ext
  intro w
  ext u
  rw [Pi.basisFun_apply, extend_basis]
  simp only [binWeight, LinearMap.mulLeft_apply, Pi.mul_apply, Rat.cast_mul]
  by_cases hu : u = w <;> simp_all

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
    · simpa [binRaising, binLowering, map_sub, map_mul, weight_extension] using
        congrArg (extend K) a.ef
    · have eq := congrArg (extend K) a.he
      simpa [binRaising, map_sub, map_mul, two_smul, weight_extension] using eq
    · have eq := congrArg (extend K) a.hf
      simpa [binLowering, map_sub, map_mul, two_smul, neg_smul, weight_extension] using eq
  · intro w u
    refine ⟨?_, extend_basis K (Rbin m) w u, extend_basis K (Hbin m) w u⟩
    rfl

/-- The sum of the two weight actions on a tensor product. -/
noncomputable def twoWeight (m n : ℕ) :
    Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) :=
  (binWeight K m).rTensor ((Fin n → Bool) → K) +
    (binWeight K n).lTensor ((Fin m → Bool) → K)

/-- The sum of the two raising actions on a tensor product. -/
noncomputable def twoRaising (m n : ℕ) :
    Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) :=
  (binRaising K m).rTensor ((Fin n → Bool) → K) +
    (binRaising K n).lTensor ((Fin m → Bool) → K)

/-- The sum of the two lowering actions on a tensor product. -/
noncomputable def twoLowering (m n : ℕ) :
    Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) :=
  (binLowering K m).rTensor ((Fin n → Bool) → K) +
    (binLowering K n).lTensor ((Fin m → Bool) → K)

omit [CharZero K] in
private theorem tensor_commutator {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (a c : Module.End K V) (b d : Module.End K W) :
    (a.rTensor W + b.lTensor V) * (c.rTensor W + d.lTensor V) -
      (c.rTensor W + d.lTensor V) * (a.rTensor W + b.lTensor V) =
      (a * c - c * a).rTensor W + (b * d - d * b).lTensor V := by
  have cross (x : Module.End K V) (y : Module.End K W) :
      x.rTensor W * y.lTensor V = y.lTensor V * x.rTensor W := by
    change (x.rTensor W).comp (y.lTensor V) = (y.lTensor V).comp (x.rTensor W)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  simp only [LinearMap.rTensor_sub, LinearMap.lTensor_sub,
    LinearMap.rTensor_mul, LinearMap.lTensor_mul, add_mul, mul_add]
  rw [cross a d, cross c b]
  abel

omit [CharZero K] in
private theorem tensor_relations {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {h e f : Module.End K V} {h' e' f' : Module.End K W}
    (a : Sl2Relations h e f) (b : Sl2Relations h' e' f') :
    Sl2Relations (h.rTensor W + h'.lTensor V) (e.rTensor W + e'.lTensor V)
      (f.rTensor W + f'.lTensor V) := by
  constructor
  · rw [tensor_commutator, a.ef, b.ef]
  · rw [tensor_commutator, a.he, b.he]
    simp only [LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]
  · rw [tensor_commutator, a.hf, b.hf]
    simp only [LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

/-- The two-bin relations and their action on the tensor delta basis. -/
theorem two_bin_action (m n : ℕ) :
    Sl2Relations (twoWeight K m n) (twoRaising K m n) (twoLowering K m n) ∧
    ∀ (w : Fin m → Bool) (v : Fin n → Bool),
      twoWeight K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        ((weight w : K) + (weight v : K)) • (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) ∧
      twoRaising K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        (fun u => (Rbin m (Pi.single w 1) u : K)) ⊗ₜ[K] Pi.single v 1 +
        Pi.single w 1 ⊗ₜ[K] (fun u => (Rbin n (Pi.single v 1) u : K)) ∧
      twoLowering K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        (fun u => (Hbin m (Pi.single w 1) u : K)) ⊗ₜ[K] Pi.single v 1 +
        Pi.single w 1 ⊗ₜ[K] (fun u => (Hbin n (Pi.single v 1) u : K)) := by
  have a := bin_action K m
  have b := bin_action K n
  refine ⟨tensor_relations K a.1 b.1, ?_⟩
  intro w v
  have hw (r : ℕ) (x : Fin r → Bool) :
      binWeight K r (Pi.single x 1) = (weight x : K) • Pi.single x 1 := by
    ext u
    rw [(bin_action K r).2 x u |>.1]
    by_cases hu : u = x <;> simp_all
  have he (r : ℕ) (x : Fin r → Bool) :
      binRaising K r (Pi.single x 1) = fun u => (Rbin r (Pi.single x 1) u : K) :=
    funext fun u => ((bin_action K r).2 x u).2.1
  have hf (r : ℕ) (x : Fin r → Bool) :
      binLowering K r (Pi.single x 1) = fun u => (Hbin r (Pi.single x 1) u : K) :=
    funext fun u => ((bin_action K r).2 x u).2.2
  simp only [twoWeight, twoRaising, twoLowering, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hw, he, hf,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, add_smul, and_self]

/-- The concrete triple together with its relation certificate. -/
noncomputable def twoBinRepresentation (m n : ℕ) :
    {a : Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) ×
      Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) ×
      Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)) //
      Sl2Relations a.1 a.2.1 a.2.2} :=
  ⟨(twoWeight K m n, twoRaising K m n, twoLowering K m n), (two_bin_action K m n).1⟩

end D5.S3.Quantum.SpinChains.BinaryBinBaseChange
