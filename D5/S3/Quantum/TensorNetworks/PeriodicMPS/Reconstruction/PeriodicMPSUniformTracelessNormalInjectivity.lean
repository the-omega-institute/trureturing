/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracelessNormalInjectivity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracelessNormalInjectivity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Injectivity of traceless normal amplitudes. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTraceNormalInjectivity

/-! The trace-normal map at the traceless boundary of odd binary rings. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracelessNormalInjectivity

open Polynomial
open scoped Matrix
open SevenSiteTraceBase (Bond Word line pencil traceBase traceNormal)
open PeriodicMPSUniformTraceNormalInjectivity
  (contraction contraction_amplitude_polynomial normal)
open PeriodicMPSUniformTracePowerBoundary
  (trace_pow_eq_eval_dickson trace_pow_odd_at_traceless_curve)

noncomputable section

private theorem coeff_one_dickson_at_traceless_curve {R : Type*} [CommRing R]
    (T D : R[X]) (hT : T.eval 0 = 0) (n : ℕ) (hn : Odd n) :
    ((dickson 1 D n).eval T).coeff 1 =
      (n : R) * (-D.eval 0) ^ ((n - 1) / 2) * T.derivative.eval 0 := by
  let M : Bond R[X] := !![T, -D; 1, 0]
  have ht : M.trace = T := by simp [M, Matrix.trace_fin_two]
  have hd : M.det = D := by simp [M, Matrix.det_fin_two]
  have hm := (trace_pow_odd_at_traceless_curve M (ht ▸ hT) n hn).2
  rw [trace_pow_eq_eval_dickson, ht, hd] at hm
  simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero,
    mul_one] using hm

/-- Contracting the first trace coefficient against `(z, w)` gives the odd
power-trace slope times the corresponding change in the trace. -/
theorem contraction_traceless_normal (n : ℕ) (hn : Odd n)
    (p : Fin 3 → ℂ) (v : Fin 2 → ℂ) (z w : ℂ) :
    contraction z w (normal n (traceBase p) (traceNormal v)) =
      (n : ℂ) * (-(p 0 * z ^ 2 - p 2 * z * w + p 1 * w ^ 2)) ^ ((n - 1) / 2) *
        (v 0 * z + v 1 * w) := by
  let b := line (traceBase p) (traceNormal v)
  let T := b 0 * C z + b 1 * C w
  let D := pencil b (C z) (C w)
  have hC (i : Word n) :
      (List.ofFn fun j => if i j = 0 then C z else C w).prod =
        C ((List.ofFn fun j => if i j = 0 then z else w).prod) := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, apply_ite]
  have hcoeff : contraction z w (normal n (traceBase p) (traceNormal v)) =
      ((dickson 1 D n).eval T).coeff 1 := by
    simpa only [contraction, finsetSum_coeff, hC, coeff_C_mul, normal, T, D, b] using
      congrArg (fun f : ℂ[X] => f.coeff 1) (contraction_amplitude_polynomial n b (C z) (C w))
  have ht : T = X * C (v 0 * z + v 1 * w) := by
    simp [T, b, line, traceBase, traceNormal, map_add, map_mul]
    ring
  -- The full determinant includes the quadratic contribution from the two traces.
  have hd : D = C (p 0 * z ^ 2 - p 2 * z * w + p 1 * w ^ 2) +
      X ^ 2 * C (v 0 * v 1 * z * w) := by
    simp [D, pencil, b, line, traceBase, traceNormal, map_add, map_sub, map_mul, map_pow]
    ring
  have hT : T.eval 0 = 0 := by simp [ht]
  have hD : D.eval 0 = p 0 * z ^ 2 - p 2 * z * w + p 1 * w ^ 2 := by simp [hd]
  have hT' : T.derivative.eval 0 = v 0 * z + v 1 * w := by
    simp [ht, derivative_mul]
  rw [hcoeff, coeff_one_dickson_at_traceless_curve T D hT n hn, hD, hT']

/-- The contracted first trace coefficient at `(1, X)` records both trace
directions in the same polynomial. -/
theorem contraction_traceless_normal_one_X (n : ℕ) (hn : Odd n)
    (p : Fin 3 → ℂ) (v : Fin 2 → ℂ) :
    contraction (1 : ℂ[X]) X (C ∘ normal n (traceBase p) (traceNormal v)) =
      (n : ℂ[X]) * (-(C (p 0) - C (p 2) * X + C (p 1) * X ^ 2)) ^ ((n - 1) / 2) *
        (C (v 0) + C (v 1) * X) := by
  apply Polynomial.funext
  intro x
  let f : ℂ[X] →+* ℂ := evalRingHom x
  change f _ = f _
  simp only [contraction, map_sum, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    apply_ite, map_natCast, map_neg, map_pow, map_add, map_sub]
  simpa only [f, coe_evalRingHom, eval_one, eval_X, eval_C, contraction, one_pow, mul_one] using
    contraction_traceless_normal n hn p v 1 x

/-- For every odd length, at `(0, 0, d, e, k)` with nonzero determinant pencil,
the first coefficient of the literal trace-word tensor is injective on the
two trace directions. -/
theorem traceless_normal_injective (n : ℕ) (hn : Odd n) (p : Fin 3 → ℂ) (hp : p ≠ 0) :
    Function.Injective (fun v => normal n (traceBase p) (traceNormal v)) := by
  let D : ℂ[X] := C (p 0) - C (p 2) * X + C (p 1) * X ^ 2
  have hD : D ≠ 0 := by
    intro h
    apply hp
    funext i
    fin_cases i
    · simpa [D, coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow] using
        congrArg (fun q : ℂ[X] => q.coeff 0) h
    · simpa [D, coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow] using
        congrArg (fun q : ℂ[X] => q.coeff 2) h
    · simpa [D, coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow] using
        congrArg (fun q : ℂ[X] => q.coeff 1) h
  have hn' : (n : ℂ[X]) ≠ 0 := Nat.cast_ne_zero.mpr (Odd.pos hn).ne'
  have hslope : (n : ℂ[X]) * (-D) ^ ((n - 1) / 2) ≠ 0 :=
    mul_ne_zero hn' (pow_ne_zero _ (neg_ne_zero.mpr hD))
  intro u v huv
  have h := congrArg (fun a : Word n → ℂ => contraction (1 : ℂ[X]) X (C ∘ a)) huv
  rw [contraction_traceless_normal_one_X n hn p u,
    contraction_traceless_normal_one_X n hn p v] at h
  have hL : C (u 0) + C (u 1) * X = C (v 0) + C (v 1) * X := mul_left_cancel₀ hslope h
  funext i
  fin_cases i
  · simpa [coeff_add, coeff_C_mul, coeff_X] using congrArg (fun q : ℂ[X] => q.coeff 0) hL
  · simpa [coeff_add, coeff_C_mul, coeff_X] using congrArg (fun q : ℂ[X] => q.coeff 1) hL

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTracelessNormalInjectivity
