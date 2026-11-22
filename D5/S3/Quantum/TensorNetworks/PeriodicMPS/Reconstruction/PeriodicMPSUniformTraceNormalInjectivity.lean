/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalInjectivity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalInjectivity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Injectivity of proportional normal amplitudes. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTracePowerSimpleRoots

/-! The symmetric contraction and the determinant-normal map for every ring length. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceNormalInjectivity

open Polynomial
open scoped BigOperators Matrix
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open PeriodicMPSUniformTraceBase (amplitude normalizedTracePower)
open PeriodicMPSUniformTracePowerBoundary (trace_pow_eq_eval_dickson)
open PeriodicMPSUniformTracePowerSimpleRoots (rootMultiplicity_normalizedTracePower)
open SevenSiteTraceBase (Bond Word wordProduct wordPolynomial wordPolynomial_eq_trace
  pencil line proportional pencilNormal)

open private form map_form wordProduct_smul sum_wordProduct from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

noncomputable section

private theorem map_amplitude {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (p : Fin 5 → R) (i : Word n) :
    f (amplitude n p i) = amplitude n (f ∘ p) i := by
  unfold amplitude wordPolynomial
  rw [show (f ∘ p) 0 = f (p 0) from rfl, show (f ∘ p) 1 = f (p 1) from rfl,
    show (f ∘ p) 2 = f (p 2) from rfl, show (f ∘ p) 3 = f (p 3) from rfl,
    show (f ∘ p) 4 = f (p 4) from rfl, map_form]
  rcases form (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn i) with ⟨u, a, b, c⟩
  simp [map_ofNat]

/-- Contract the binary word tensor against the same two-vector at every site. -/
def contraction {R : Type*} [CommRing R] {n : ℕ} (z w : R) (v : Word n → R) : R :=
  ∑ i : Word n, (List.ofFn fun j => if i j = 0 then z else w).prod * v i

/-- The symmetric contraction of the actual trace-word polynomials is the power trace
of the matrix pencil, expressed in its trace and determinant. -/
theorem contraction_amplitude (n : ℕ) (p : Fin 5 → ℂ) (z w : ℂ) :
    contraction z w (amplitude n p) =
      (dickson 1 (pencil p z w) n).eval (p 0 * z + p 1 * w) := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
  let c : Fin 2 → ℂ := fun i => if i = 0 then z else w
  let B : Fin 2 → Bond ℂ := fun i => c i • A i
  have hword (i : Word n) : amplitude n p i = (wordProduct A i).trace := by
    simpa only [amplitude, ht, hs, hd, he, hk] using wordPolynomial_eq_trace A i
  calc
    contraction z w (amplitude n p) = ∑ i : Word n, (wordProduct B i).trace := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [B, wordProduct_smul, Matrix.trace_smul, smul_eq_mul, hword, c]
    _ = ((z • A 0 + w • A 1) ^ n).trace := by
      rw [← Matrix.trace_sum, sum_wordProduct]
      rfl
    _ = _ := by
      have hdet : (z • A 0 + w • A 1).det = pencil p z w := by
        rw [pencil, ← ht, ← hs, ← hd, ← he, ← hk]
        simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        ring
      rw [trace_pow_eq_eval_dickson, hdet, Matrix.trace_add, Matrix.trace_smul,
        Matrix.trace_smul, ht, hs]
      simp only [smul_eq_mul, mul_comm z, mul_comm w]

/-- The contraction identity also holds over a polynomial line in the coordinates. -/
theorem contraction_amplitude_polynomial (n : ℕ) (p : Fin 5 → ℂ[X]) (z w : ℂ[X]) :
    contraction z w (amplitude n p) =
      (dickson 1 (pencil p z w) n).eval (p 0 * z + p 1 * w) := by
  apply Polynomial.funext
  intro x
  let f : ℂ[X] →+* ℂ := evalRingHom x
  change f (contraction z w (amplitude n p)) =
    f ((dickson 1 (pencil p z w) n).eval (p 0 * z + p 1 * w))
  rw [← eval_map_apply f, map_dickson]
  simpa only [contraction, pencil, map_sum, map_mul, map_list_prod, List.map_ofFn,
    Function.comp_def, apply_ite, map_sub, map_add, map_pow, map_amplitude]
    using contraction_amplitude n (f ∘ p) (f z) (f w)

/-- The coefficient of the line parameter in each coordinate of the trace-word tensor. -/
def normal (n : ℕ) (b v : Fin 5 → ℂ) : Word n → ℂ :=
  fun i => (amplitude n (line b v) i).coeff 1

private theorem contraction_normal (n : ℕ) (b v : Fin 5 → ℂ) (z w : ℂ) :
    contraction z w (normal n b v) =
      ((dickson 1 (pencil (line b v) (C z) (C w)) n).eval
        (line b v 0 * C z + line b v 1 * C w)).coeff 1 := by
  have hC (i : Word n) :
      (List.ofFn fun j => if i j = 0 then C z else C w).prod =
        C ((List.ofFn fun j => if i j = 0 then z else w).prod) := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, apply_ite]
  have h := congrArg (fun p : ℂ[X] => p.coeff 1)
    (contraction_amplitude_polynomial n (line b v) (C z) (C w))
  simpa only [contraction, finsetSum_coeff, hC, coeff_C_mul, normal] using h

private theorem coeff_one_tracePower_line (n : ℕ) (a d : ℂ) :
    ((dickson 1 (C a + X * C d : ℂ[X]) n).eval 1).coeff 1 =
      d * (normalizedTracePower n).derivative.eval a := by
  let q : ℂ[X] := C a + X * C d
  let f : ℂ[X] →+* ℂ[X] := compRingHom q
  have hf : f X = q := X_comp
  have h := eval_map_apply (p := dickson 1 (X : ℂ[X]) n) f 1
  rw [map_dickson, map_one, hf] at h
  change (dickson 1 q n).eval 1 = (normalizedTracePower n).comp q at h
  change ((dickson 1 q n).eval 1).coeff 1 = _
  rw [h]
  calc
    ((normalizedTracePower n).comp q).coeff 1 =
        ((normalizedTracePower n).comp q).derivative.eval 0 := by
      simp only [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, mul_one]
    _ = _ := by
      simp [derivative_comp, eval_comp, q]

/-- On the trace-one slice of the symmetric contraction, the first coefficient
is the determinant variation times the slope of the normalized power trace. -/
theorem contraction_proportional_normal (n : ℕ) (s a w : ℂ) (v : Fin 3 → ℂ) :
    contraction (1 - s * w) w (normal n (proportional s a) (pencilNormal v)) =
      (v 0 * (1 - s * w) ^ 2 - v 2 * (1 - s * w) * w + v 1 * w ^ 2) *
        (normalizedTracePower n).derivative.eval a := by
  let z : ℂ := 1 - s * w
  let b : Fin 5 → ℂ[X] := line (proportional s a) (pencilNormal v)
  have hb₀ : b 0 = 1 := by simp [b, line, proportional, pencilNormal]
  have hb₁ : b 1 = C s := by simp [b, line, proportional, pencilNormal]
  have hb₂ : b 2 = C a + X * C (v 0) := rfl
  have hb₃ : b 3 = C (a * s ^ 2) + X * C (v 1) := rfl
  have hb₄ : b 4 = C ((1 - 2 * a) * s) + X * C (v 2) := rfl
  have hz : z + s * w = 1 := by simp [z]
  have hτ : b 0 * C z + b 1 * C w = 1 := by
    rw [hb₀, hb₁, one_mul, ← map_mul, ← map_add, hz, map_one]
  have hD : pencil b (C z) (C w) =
      C a + X * C (v 0 * z ^ 2 - v 2 * z * w + v 1 * w ^ 2) := by
    rw [pencil, hb₀, hb₁, hb₂, hb₃, hb₄]
    simp only [z, map_add, map_sub, map_mul, map_pow, map_one, Polynomial.C_ofNat]
    ring
  have h := contraction_normal n (proportional s a) (pencilNormal v) z w
  change contraction z w _ =
    ((dickson 1 (pencil b (C z) (C w)) n).eval (b 0 * C z + b 1 * C w)).coeff 1 at h
  change contraction z w _ =
    (v 0 * z ^ 2 - v 2 * z * w + v 1 * w ^ 2) * (normalizedTracePower n).derivative.eval a
  rw [h, hτ, hD, coeff_one_tracePower_line]

/-- At every trace-one base curve, the first coefficient of the actual length-`n`
trace-word tensor is injective on the three determinant and mixed-trace directions. -/
theorem proportional_normal_injective (n : ℕ) (hn : 2 ≤ n) (s a : ℂ)
    (ha : (normalizedTracePower n).IsRoot a) :
    Function.Injective (fun v => normal n (proportional s a) (pencilNormal v)) := by
  have hmult := rootMultiplicity_normalizedTracePower n hn a ha
  have hne : normalizedTracePower n ≠ 0 := by
    intro h
    rw [h, rootMultiplicity_zero] at hmult
    exact Nat.zero_ne_one hmult
  have hslope : (normalizedTracePower n).derivative.eval a ≠ 0 := by
    intro h
    have htwo : 1 < (normalizedTracePower n).rootMultiplicity a :=
      (one_lt_rootMultiplicity_iff_isRoot hne).2 ⟨ha, h⟩
    rw [hmult] at htwo
    exact (lt_irrefl 1) htwo
  intro u v huv
  have heval (w : ℂ) :
      u 0 * (1 - s * w) ^ 2 - u 2 * (1 - s * w) * w + u 1 * w ^ 2 =
        v 0 * (1 - s * w) ^ 2 - v 2 * (1 - s * w) * w + v 1 * w ^ 2 := by
    have h := congrArg (contraction (1 - s * w) w) huv
    change contraction (1 - s * w) w (normal n (proportional s a) (pencilNormal u)) =
      contraction (1 - s * w) w (normal n (proportional s a) (pencilNormal v)) at h
    rw [contraction_proportional_normal, contraction_proportional_normal] at h
    exact mul_right_cancel₀ hslope h
  let q (v : Fin 3 → ℂ) : ℂ[X] :=
    monomial 0 (v 0) + monomial 1 (-2 * s * v 0 - v 2) +
      monomial 2 (s ^ 2 * v 0 + s * v 2 + v 1)
  have hq : q u = q v := by
    apply Polynomial.funext
    intro w
    simp only [q, eval_add, eval_monomial, pow_zero, pow_one, mul_one]
    linear_combination (heval w)
  have h₀ : u 0 = v 0 := by
    simpa [q, coeff_add, coeff_monomial] using congrArg (fun p : ℂ[X] => p.coeff 0) hq
  have h₁ : -2 * s * u 0 - u 2 = -2 * s * v 0 - v 2 := by
    simpa [q, coeff_add, coeff_monomial] using congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have h₂ : s ^ 2 * u 0 + s * u 2 + u 1 = s ^ 2 * v 0 + s * v 2 + v 1 := by
    simpa [q, coeff_add, coeff_monomial] using congrArg (fun p : ℂ[X] => p.coeff 2) hq
  have hk : u 2 = v 2 := by linear_combination -h₁ - 2 * s * h₀
  funext i
  fin_cases i
  · exact h₀
  · change u 1 = v 1
    linear_combination h₂ - s ^ 2 * h₀ - s * hk
  · exact hk

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceNormalInjectivity
