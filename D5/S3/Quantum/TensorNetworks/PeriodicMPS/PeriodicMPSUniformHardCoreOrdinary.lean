/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreOrdinary
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreOrdinary
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner]
   utility: none
   digest: The vacuum, singleton and separated-pair amplitudes fix the ordinary trace invariants of a core realization of the cyclic independent-set witness. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner

/-! Recovery of the ordinary trace invariants at the cyclic independent-set tensor. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreOrdinary

open PeriodicMPSParentIntersection
  (Bond Word wordMatrix wordMatrix_append wordMatrix_snoc)
open PeriodicMPSUniformZeroCorner
  (trace_det_sq_second_eq_zero_of_prefix_zero trace_gap_product trace_gap_recurrence
    trace_pow_succ_of_det_eq_zero)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped Matrix

noncomputable section

/-- The three pair samples at gaps `(1, m + 2)`, `(2, m + 1)`, and `(3, m)`
force the determinant coefficient of the gap recurrence to vanish. -/
theorem det_eq_zero_of_three_gap_products (f : ℕ → ℂ) (t d c : ℂ) (m : ℕ)
    (hzero : f 0 = 0)
    (hrec : ∀ g : ℕ, f (g + 2) = t * f (g + 1) - d * f g)
    (hc : c ≠ 0)
    (h₁ : f 1 * f (m + 2) = c) (h₂ : f 2 * f (m + 1) = c)
    (h₃ : f 3 * f m = c) : d = 0 := by
  have hfirst : f 1 ≠ 0 := by
    intro h
    exact hc (by simpa only [h, zero_mul] using h₁.symm)
  have hlast : f m ≠ 0 := by
    intro h
    exact hc (by simpa only [h, mul_zero] using h₃.symm)
  have htwo : f 2 = t * f 1 := by
    simpa only [Nat.zero_add, hzero, mul_zero, sub_zero] using hrec 0
  have hnext : f (m + 2) = t * f (m + 1) := by
    apply mul_left_cancel₀ hfirst
    calc
      f 1 * f (m + 2) = c := h₁
      _ = f 2 * f (m + 1) := h₂.symm
      _ = f 1 * (t * f (m + 1)) := by
        rw [htwo]
        ac_rfl
  have hz : d * f m = 0 := by linear_combination hrec m - hnext
  exact (mul_eq_zero.mp hz).resolve_right hlast

/-- The word consisting of `g` zeros followed by a one. -/
def singletonWord {n : ℕ} (g : ℕ) (hlen : g + 1 = n) : Word n :=
  fun i => (Fin.snoc (fun _ : Fin g => (0 : Fin 2)) 1 : Word (g + 1)) (Fin.cast hlen.symm i)

/-- The cyclic pair word `0^g 1 0^h 1`. The two ones are independent
when both gaps are positive. -/
def pairWord {n : ℕ} (g h : ℕ) (hlen : (g + 1) + (h + 1) = n) : Word n :=
  fun i => (Fin.append (singletonWord g rfl) (singletonWord h rfl)) (Fin.cast hlen.symm i)

private theorem wordMatrix_vacuum (P : Fin 2 → Bond) (n : ℕ) :
    wordMatrix P (fun _ : Fin n => 0) = P 0 ^ n := by
  simp only [wordMatrix, List.ofFn_const, List.prod_replicate]

private theorem wordMatrix_singletonWord (P : Fin 2 → Bond) {n : ℕ} (g : ℕ)
    (hlen : g + 1 = n) :
    wordMatrix P (singletonWord g hlen) = P 0 ^ g * P 1 := by
  subst n
  change wordMatrix P (Fin.snoc (fun _ : Fin g => (0 : Fin 2)) 1) = _
  rw [wordMatrix_snoc, wordMatrix_vacuum]

theorem traceWord_vacuum (P : Fin 2 → Bond) (n : ℕ) :
    traceWord 2 2 n P (fun _ => 0) = (P 0 ^ n).trace := by
  change (wordMatrix P (fun _ : Fin n => 0)).trace = _
  rw [wordMatrix_vacuum]

theorem traceWord_singletonWord (P : Fin 2 → Bond) {n : ℕ} (g : ℕ)
    (hlen : g + 1 = n) :
    traceWord 2 2 n P (singletonWord g hlen) = (P 0 ^ g * P 1).trace := by
  change (wordMatrix P (singletonWord g hlen)).trace = _
  rw [wordMatrix_singletonWord]

theorem traceWord_pairWord (P : Fin 2 → Bond) (hd : (P 1).det = 0) {n : ℕ} (g h : ℕ)
    (hlen : (g + 1) + (h + 1) = n) :
    traceWord 2 2 n P (pairWord g h hlen) =
      (P 0 ^ g * P 1).trace * (P 0 ^ h * P 1).trace := by
  subst n
  change (wordMatrix P (Fin.append (singletonWord g rfl) (singletonWord h rfl))).trace = _
  rw [wordMatrix_append, wordMatrix_singletonWord P g rfl, wordMatrix_singletonWord P h rfl]
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using
    trace_gap_product (P 0) (P 1) hd g [h]

/-- For `n ≥ 7`, the ordinary hard-core amplitude data determine the invariant tuple
`(t, 0, 0, 0, t²)`, where `t = tr(P 0) ≠ 0`. The common amplitude is `t^n`.
The vacuum and the chosen cyclic representatives of singletons and independent pairs
all have amplitude `c`. The prefix hypothesis supplies the adjacent-ones vanishing. -/
theorem ordinary_invariants_of_hard_core_amplitudes (P : Fin 2 → Bond)
    (n : ℕ) (hn : 7 ≤ n) (c : ℂ) (hc : c ≠ 0)
    (hprefix : ∀ w : Word (n - 2), (P 1 * P 1 * wordMatrix P w).trace = 0)
    (hvac : traceWord 2 2 n P (fun _ => 0) = c)
    (hsingle : traceWord 2 2 n P (singletonWord (n - 1) (by omega)) = c)
    (hpair : ∀ (g h : ℕ), 0 < g → 0 < h → ∀ hlen : (g + 1) + (h + 1) = n,
      traceWord 2 2 n P (pairWord g h hlen) = c) :
    (P 0).trace ≠ 0 ∧ (P 1).trace = 0 ∧ (P 0).det = 0 ∧ (P 1).det = 0 ∧
      (P 0 * P 1).trace = (P 0).trace ^ 2 ∧ c = (P 0).trace ^ n := by
  have hne : traceWord 2 2 n P ≠ 0 := by
    intro h
    have hz : traceWord 2 2 n P (fun _ => 0) = 0 :=
      congrFun h (fun _ : Fin n => 0)
    exact hc (hvac.symm.trans hz)
  obtain ⟨htB, hdB, _⟩ :=
    trace_det_sq_second_eq_zero_of_prefix_zero P n (by omega) hne hprefix
  let f : ℕ → ℂ := fun g => (P 0 ^ g * P 1).trace
  have hzero : f 0 = 0 := by simp only [f, pow_zero, one_mul, htB]
  have hrec (g : ℕ) :
      f (g + 2) = (P 0).trace * f (g + 1) - (P 0).det * f g :=
    trace_gap_recurrence (P 0) (P 1) g
  have hgap (g h : ℕ) (hg : 0 < g) (hh : 0 < h) (hlen : (g + 1) + (h + 1) = n) :
      f g * f h = c :=
    (traceWord_pairWord P hdB g h hlen).symm.trans (hpair g h hg hh hlen)
  have h₁ : f 1 * f ((n - 5) + 2) = c :=
    hgap 1 ((n - 5) + 2) (by omega) (by omega) (by omega)
  have h₂ : f 2 * f ((n - 5) + 1) = c :=
    hgap 2 ((n - 5) + 1) (by omega) (by omega) (by omega)
  have h₃ : f 3 * f (n - 5) = c :=
    hgap 3 (n - 5) (by omega) (by omega) (by omega)
  have hdA : (P 0).det = 0 :=
    det_eq_zero_of_three_gap_products f (P 0).trace (P 0).det c (n - 5)
      hzero hrec hc h₁ h₂ h₃
  have hclosed (g : ℕ) : f (g + 1) = (P 0).trace ^ g * (P 0 * P 1).trace := by
    induction g with
    | zero => simp only [f, Nat.zero_add, pow_one, pow_zero, one_mul]
    | succ g ih =>
      change f (g + 2) = (P 0).trace ^ (g + 1) * (P 0 * P 1).trace
      rw [hrec g, hdA, zero_mul, sub_zero, ih, pow_succ' (P 0).trace g, mul_assoc]
  have hnpos : (n - 1) + 1 = n := by omega
  have hvacPow : (P 0).trace ^ n = c := by
    have hsingular := trace_pow_succ_of_det_eq_zero (P 0) hdA (n - 1)
    rw [hnpos] at hsingular
    exact hsingular.symm.trans ((traceWord_vacuum P n).symm.trans hvac)
  have htA : (P 0).trace ≠ 0 := by
    intro hz
    exact hc (by simpa only [hz, zero_pow (show n ≠ 0 by omega)] using hvacPow.symm)
  have hsingle' : f (n - 1) = c :=
    (traceWord_singletonWord P (n - 1) hnpos).symm.trans hsingle
  have hsinglePow : (P 0).trace ^ (n - 2) * (P 0 * P 1).trace = c := by
    have h := hclosed (n - 2)
    rw [show n - 2 + 1 = n - 1 by omega] at h
    exact h.symm.trans hsingle'
  have hmixed : (P 0 * P 1).trace = (P 0).trace ^ 2 := by
    have hfactor : (P 0).trace ^ (n - 2) * (P 0).trace ^ 2 = c := by
      rw [← pow_add, show n - 2 + 2 = n by omega]
      exact hvacPow
    exact mul_left_cancel₀ (pow_ne_zero _ htA) (hsinglePow.trans hfactor.symm)
  exact ⟨htA, htB, hdA, hdB, hmixed, hvacPow.symm⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreOrdinary
