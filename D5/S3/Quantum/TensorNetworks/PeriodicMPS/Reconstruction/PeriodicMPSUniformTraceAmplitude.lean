/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceAmplitude
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceAmplitude
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Weighted scaling of the periodic trace-word amplitude. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

/-! The literal trace-word amplitude and its weighted scaling law at arbitrary period. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteTraceBase

open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped Matrix

open private wordProduct_smul map_form form from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

noncomputable section

/-- The trace-algebra polynomial evaluated at each binary word of length `n`. -/
def amplitudeOfLength {R : Type*} [CommRing R] (n : ℕ)
    (p : Fin 5 → R) (w : Word n) : R :=
  wordPolynomial (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn w)

theorem amplitudeOfLength_actual (n : ℕ) (A : Fin 2 → Bond ℂ) :
    amplitudeOfLength n ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace] =
      traceWord 2 2 n A :=
  funext fun w => wordPolynomial_eq_trace A w

theorem amplitudeOfLength_scale (n : ℕ) (z t s d e k : ℂ) :
    amplitudeOfLength n ![z * t, z * s, z ^ 2 * d, z ^ 2 * e, z ^ 2 * k] =
      z ^ n • amplitudeOfLength n (![t, s, d, e, k] : Fin 5 → ℂ) := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates t s d e k
  have h := amplitudeOfLength_actual n (fun i => z • A i)
  simp only [Matrix.trace_smul, smul_eq_mul, Matrix.det_smul, Fintype.card_fin,
    smul_mul_assoc, mul_smul_comm, smul_smul, ht, hs, hd, he, hk, ← pow_two] at h
  have hA := amplitudeOfLength_actual n A
  rw [ht, hs, hd, he, hk] at hA
  rw [h, hA]
  funext w
  change (wordProduct (fun i => z • A i) w).trace = z ^ n * (wordProduct A w).trace
  rw [wordProduct_smul A (fun _ => z), Matrix.trace_smul, smul_eq_mul]
  change (List.ofFn (fun _ : Fin n => z)).prod * (wordProduct A w).trace =
    z ^ n * (wordProduct A w).trace
  rw [List.ofFn_const, List.prod_replicate]

theorem map_amplitudeOfLength {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (p : Fin 5 → R) (w : Word n) :
    f (amplitudeOfLength n p w) = amplitudeOfLength n (f ∘ p) w := by
  unfold amplitudeOfLength wordPolynomial
  rw [show (f ∘ p) 0 = f (p 0) from rfl, show (f ∘ p) 1 = f (p 1) from rfl,
    show (f ∘ p) 2 = f (p 2) from rfl, show (f ∘ p) 3 = f (p 3) from rfl,
    show (f ∘ p) 4 = f (p 4) from rfl, map_form]
  rcases form (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn w) with ⟨u, a, b, c⟩
  simp [map_ofNat]

theorem differentiable_amplitudeOfLength {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] (n : ℕ) : Differentiable 𝕜 (amplitudeOfLength (R := ℂ) n) := by
  apply differentiable_pi.mpr
  intro w
  have h (b : Fin 5 → ℂ) :
      MvPolynomial.eval b (amplitudeOfLength n MvPolynomial.X w) = amplitudeOfLength n b w := by
    rw [map_amplitudeOfLength]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := b) i
  simpa only [h] using
    differentiable_eval_polynomial (𝕜 := 𝕜) (amplitudeOfLength n MvPolynomial.X w)
      (fun i (b : Fin 5 → ℂ) => b i) (fun i => differentiable_apply i)

end

end D5.S3.Quantum.TensorNetworks.SevenSiteTraceBase
