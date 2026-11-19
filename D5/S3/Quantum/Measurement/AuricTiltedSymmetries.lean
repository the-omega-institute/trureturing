import D5.S3.Quantum.Measurement.AuricTiltedInstrument
import D5.S3.Quantum.Measurement.AuricPhaseTwirledGram
import D5.S3.Quantum.Measurement.AuricFiveLevelTilt
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Realization of the relabeled and conjugated tilted protocols -/

namespace D5.S3.Quantum.Measurement.AuricTiltedSymmetries

open _root_.Matrix
open D5.S3.Quantum.Measurement.AuricProjectiveTree
open D5.S3.Quantum.Measurement.AuricTiltedInstrument
open D5.S3.Quantum.Measurement.AuricPhaseTwirledGram
open D5.S3.Quantum.Measurement.AuricFiveLevelTilt

noncomputable def tiltedKraus (c t d b : ℝ) (j : Fin 2) : Registers :=
  Fin.cases (firstKraus c t) (fun _ => secondKraus c t d b) j

@[simp] theorem tiltedKraus_zero (c t d b : ℝ) :
    tiltedKraus c t d b 0 = firstKraus c t := rfl

@[simp] theorem tiltedKraus_one (c t d b : ℝ) :
    tiltedKraus c t d b 1 = secondKraus c t d b := rfl

/-- Relabeling and paired unitary conjugation of the two Kraus operators
are implemented by one projective node and two final unitary leaves. -/
theorem realizes_conjugated_tilt (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) (U : Matrix.unitaryGroup (Fin 5) ℂ) (f : Equiv.Perm (Fin 2)) :
    ∃ p : Protocol (Fin 5), ∃ e : Terminal p ≃ Fin 2,
      ∀ j, flag p (e.symm j) = f j ∧
        kraus p (e.symm j) = U.val * tiltedKraus c t d b j * U.valᴴ := by
  obtain ⟨U₀, U₁, h₀, h₁⟩ := realizes_tilted_operators c t d b hc hd
  let V : Fin 2 → Matrix.unitaryGroup (Fin 5) ℂ := Fin.cases U₀ (fun _ => U₁)
  let p := Protocol.branch (star U) 2 (tiltedPVM c t hc) (fun j => .leaf (f j) (U * V j))
  let e : Terminal p ≃ Fin 2 := Equiv.sigmaUnique (Fin 2) (fun _ => Unit)
  refine ⟨p, e, fun j => ⟨rfl, ?_⟩⟩
  change (U.val * (V j).val) * ((tiltedPVM c t hc).proj j * U.valᴴ) =
    U.val * tiltedKraus c t d b j * U.valᴴ
  have hK : tiltedKraus c t d b j = (V j).val * (tiltedPVM c t hc).proj j := by
    fin_cases j
    · exact h₀
    · exact h₁
  rw [hK]
  simp only [Matrix.mul_assoc]

/-- A basis permutation requires only a unitary on the original register. -/
def permutationUnitary (s : Equiv.Perm (Fin 5)) : Matrix.unitaryGroup (Fin 5) ℂ :=
  ⟨s.permMatrix ℂ, Matrix.mem_unitaryGroup_iff'.2 (by
    change (s.permMatrix ℂ)ᴴ * s.permMatrix ℂ = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp)⟩

/-- Each term of the independent phase and permutation mixture is itself a
finite allowed same-register protocol. -/
theorem realizes_phase_permuted_tilt (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) (s : Equiv.Perm (Fin 5)) (f : Equiv.Perm (Fin 2))
    (phases : Fin 5 → Fin 4) :
    let U := (phaseUnitary phases * permutationUnitary s).val
    ∃ p : Protocol (Fin 5), ∃ e : Terminal p ≃ Fin 2,
      ∀ j, flag p (e.symm j) = f j ∧
        kraus p (e.symm j) = U * tiltedKraus c t d b j * Uᴴ :=
  realizes_conjugated_tilt c t d b hc hd (phaseUnitary phases * permutationUnitary s) f

/-- The optimizing scalar mass supplies two genuine unit vectors and the
direction that attains the sum of the two squared witness traces. -/
theorem tilt_parameters (r : ℝ) (hr : 1 < r) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    let c := Real.sqrt (1 - p)
    let t := Real.sqrt p
    let n := tiltNormalizer r p
    let d := c / n
    let b := r * t / n
    (c ^ 2 + t ^ 2 = 1) ∧ (d ^ 2 + b ^ 2 = 1) ∧
      (d * c = tiltedActive r p) ∧ (b * t = tiltedSpectator r p) ∧
      (d * c + r * (b * t) = n) := by
  dsimp only
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  have hc : c ^ 2 = 1 - p := Real.sq_sqrt (sub_nonneg.mpr hp.2)
  have ht : t ^ 2 = p := Real.sq_sqrt hp.1
  have hpos : 0 < 1 + (r ^ 2 - 1) * p := by
    have h : 0 ≤ r ^ 2 - 1 := by nlinarith
    linarith [mul_nonneg h hp.1]
  have hsq : n ^ 2 = 1 + (r ^ 2 - 1) * p := Real.sq_sqrt hpos.le
  have hn : 0 < n := Real.sqrt_pos.2 hpos
  refine ⟨by linarith only [hc, ht], ?_, ?_, ?_, ?_⟩
  · change (c / n) ^ 2 + (r * t / n) ^ 2 = 1
    field_simp [hn.ne']
    nlinarith only [hsq, hc, congrArg (fun x : ℝ => r ^ 2 * x) ht]
  · change c / n * c = (1 - p) / n
    field_simp [hn.ne']
    nlinarith only [hc]
  · change r * t / n * t = r * p / n
    field_simp [hn.ne']
    nlinarith only [ht, congrArg (fun x : ℝ => r * x) ht]
  · change c / n * c + r * (r * t / n * t) = n
    field_simp [hn.ne']
    nlinarith only [hsq, hc, congrArg (fun x : ℝ => r ^ 2 * x) ht]

end D5.S3.Quantum.Measurement.AuricTiltedSymmetries
