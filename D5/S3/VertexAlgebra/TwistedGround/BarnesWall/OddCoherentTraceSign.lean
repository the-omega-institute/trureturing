/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddCoherentTraceSign
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/OddCoherentTraceSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The cyclic modular character and uniform Barnes–Wall trace product exclude the inflated anomaly. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddWeylTrace
import D5.S3.HomologicalAlgebra.BarnesWallQ8CyclicGauge
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CyclicEtaTrace
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorDefectDet
import D5.S3.Fourier.CyclicFluxChargeExchange

/-! The cyclic transport can be checked by a normalized trace ratio over
`ℂ`. The global character cancels by multiplicativity on `i * j = k`,
without imposing reality of the original operators' traces. -/

open scoped Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddCoherentTraceSign

open LatticeTwistedGroundRealization (sign_square sign_one)
open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign)
open TailPauliPairing (Word)
open TensorDefectDet (quaternionWord groundMultiplicity_eq)
open HomologicalAlgebra.BarnesWallQ8CohomologyDetector (Q8 i j k i_mul_j)
open HomologicalAlgebra.BarnesWallQ8CyclicGauge (beta generator)
open Fourier.CyclicFluxChargeExchange (chargeTransform modularS chargeTransform_modularS)
open UpperHalfPlane

/-- For the actual odd-slot tensor phase, a common cyclic character in the
phase-free modular normalization excludes the nonzero inflated candidate.
A global quaternion character may still rephase the ground operators. -/
theorem zero_candidate_of_uniform_modular_identity
    {ι : Type} [Fintype ι] [LinearOrder ι] [LinearOrder (Word ι)]
    (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
    (P : (Word ι → F₂) → Module.End ℂ V) (hzero : P 0 = 1)
    (hmul : ∀ x y, P x * P y = complexSign (TensorGram.halfGram.toBilin' x y) • P (x + y))
    (hdim : Module.finrank ℂ V = 2 ^ (2 ^ (Fintype.card ι - 1)))
    {Ti Tj Tk : Module.End ℂ V} (hTi : Ti ≠ 0) (hTj : Tj ≠ 0)
    (hcovI : ∀ x, Ti * P x =
      complexSign (TensorLift.wordLiftExponent [(r₁, false), (r₁, true)] x) •
        (P (x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix [(r₁, false), (r₁, true)])) * Ti))
    (hcovJ : ∀ x, Tj * P x =
      complexSign (TensorLift.wordLiftExponent [(r₁, false), (r₂, false), (r₂, true)] x) •
        (P (x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix [(r₁, false), (r₂, false), (r₂, true)])) * Tj))
    (hcoherent : Ti * Tj = Tk)
    (e : F₂) (χ : Q8 →* ℂ) (cyclicTrace : Fin 3 → ℂ) (multiplicity : Fin 3 → ℕ)
    (hdefect : ∀ r, (multiplicity r : ℤ) ^ 2 =
      |(1 - TensorLift.wordMatrix (quaternionWord r₁ r₂ r)).det|)
    (C : Fin 3 → ℍ → ZMod 4 → ZMod 4 → ℂ)
    (hS : ∀ r z, C r (ModularGroup.S • z) = modularS (C r z))
    (horder : ∀ r z, chargeTransform (C r z) 1 2 = (multiplicity r : ℂ) *
      (ModularForm.eta ((z : ℂ) / 4) * ModularForm.eta z /
        ModularForm.eta ((z : ℂ) / 2) ^ 2) ^ (2 * 2 ^ (Fintype.card ι - 2)))
    (hreflection : ∀ r z, chargeTransform (C r z) 2 (-1) = cyclicTrace r *
      (Function.Periodic.qParam 24 z ^ (2 * 2 ^ (Fintype.card ι - 2)) *
        CyclicEtaTrace.reflectionOscillator (Function.Periodic.qParam 1 z) ^
          (2 * 2 ^ (Fintype.card ι - 2))))
    (htransport : ∀ r, cyclicTrace r = complexSign (beta e 1 2 - beta e 2 1) *
      χ (generator r) * (![LinearMap.trace ℂ V Ti, LinearMap.trace ℂ V Tj,
        LinearMap.trace ℂ V Tk] : Fin 3 → ℂ) r) : e = 0 := by
  let tr := LinearMap.trace ℂ V
  let n : ℕ := 2 ^ (Fintype.card ι - 2)
  let pref : ℂ := 2 ^ n
  let phase := complexSign (beta e 1 2 - beta e 2 1)
  have hp : pref ≠ 0 := pow_ne_zero _ (by norm_num)
  have hphase : phase * phase = 1 := sign_square _
  have hchi : χ i * χ j = χ k := by rw [← map_mul, i_mul_j]
  have htrace (r : Fin 3) : cyclicTrace r = pref := by
    have hmult := groundMultiplicity_eq r₁ r₂ h₁₂ r hodd (by omega) (multiplicity r) (hdefect r)
    apply CyclicEtaTrace.reflection_ground_trace_of_even_eta_power n
      (fun z => chargeTransform (C r z) 2 (-1)) pref (cyclicTrace r) _ (hreflection r)
    intro z
    have htwine : chargeTransform (C r (ModularGroup.S • z)) 1 2 =
        chargeTransform (C r z) 2 (-1) := by rw [hS, chargeTransform_modularS]
    rw [← htwine]
    simpa only [hmult, Nat.cast_pow, Nat.cast_ofNat, modular_S_smul, coe_mk, inv_neg,
      div_eq_mul_inv, neg_one_mul] using
      horder r (ModularGroup.S • z)
  have hi : pref = phase * χ i * tr Ti := (htrace 0).symm.trans (htransport 0)
  have hj : pref = phase * χ j * tr Tj := (htrace 1).symm.trans (htransport 1)
  have hk : pref = phase * χ k * tr Tk := (htrace 2).symm.trans (htransport 2)
  have htrI : tr Ti ≠ 0 := fun h => hp (by simpa [h] using hi)
  have htrJ : tr Tj ≠ 0 := fun h => hp (by simpa [h] using hj)
  have hdim' : (Module.finrank ℂ V : ℂ) = pref ^ 2 := by
    have hexp : Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 := by omega
    rw [hdim, Nat.cast_pow, Nat.cast_ofNat, hexp, pow_succ (2 : ℕ), pow_mul]
  have hpair := OddWeylTrace.normalized_tensor_trace_mul r₁ r₂ t h₁₂ ht₁ ht₂ hodd hm
    P hzero hmul hdim hTi hTj hcovI hcovJ
  change ((Module.finrank ℂ V : ℂ) * tr (Ti * Tj)) / (tr Ti * tr Tj) = pref at hpair
  rw [hcoherent, hdim'] at hpair
  have hpair' := (div_eq_iff (mul_ne_zero htrI htrJ)).mp hpair
  have hprod : pref ^ 2 = χ k * (tr Ti * tr Tj) := calc
    pref ^ 2 = (phase * χ i * tr Ti) * (phase * χ j * tr Tj) := by
      rw [pow_two, ← hi, ← hj]
    _ = (phase * phase) * (χ i * χ j) * (tr Ti * tr Tj) := by ring
    _ = χ k * (tr Ti * tr Tj) := by rw [hphase, hchi, one_mul]
  have hcancel : χ k * tr Tk = pref := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hp)
    calc
      pref ^ 2 * (χ k * tr Tk) = χ k * (pref ^ 2 * tr Tk) := by ring
      _ = pref * (χ k * (tr Ti * tr Tj)) := by rw [hpair']; ring
      _ = pref ^ 2 * pref := by rw [← hprod, mul_comm]
  have hone : phase = 1 := by
    apply mul_right_cancel₀ hp
    simpa only [one_mul, mul_assoc, hcancel] using hk.symm
  have hb : ∀ e : F₂, beta e 1 2 - beta e 2 1 = e := by decide +kernel
  by_contra he
  have hcases : ∀ e : F₂, e = 0 ∨ e = 1 := by decide +kernel
  change complexSign (beta e 1 2 - beta e 2 1) = 1 at hone
  rw [hb, (hcases e).resolve_left he, sign_one] at hone
  norm_num at hone

#print axioms zero_candidate_of_uniform_modular_identity

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddCoherentTraceSign
