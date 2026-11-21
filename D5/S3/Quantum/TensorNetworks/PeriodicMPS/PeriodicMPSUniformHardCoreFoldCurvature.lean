/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFoldCurvature
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFoldCurvature
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness]
   utility: none
   digest: The shifted hard-core energy controls a stationary marginal functional and gives strict coherence curvature on the kernel of the regular differential. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Strict normal curvature of the independent-set witness in the uniform MPS chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature

open PeriodicMPSUniformHardCoreFirstJet
open PeriodicMPSUniformHardCoreQuarticSign (F G Z G_pos fib_bounds denominator_factors)
open PeriodicMPSUniformHardCoreTransferRecurrence (hardCoreChart)
open PeriodicMPSUniformHardCoreCounts (Configuration Independent emptyConfiguration)
open PeriodicMPSUniformHardCoreEnergy
open PeriodicMPSUniformHardCoreMarginalWitness
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_cons wordMatrix_snoc
  twoFlattening)
open PeriodicMPSTwoSiteAmbiguity (rawTwo flattening_entry rawTwo_star_swap)
open UniformMPSExpectedDimensionRefutation (traceWord)
open Filter
open scoped BigOperators Matrix Topology

open private rawTwo_entry from D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
open private raw_zero rawReal pA pB qA raw_one_parts mass_one twoMass normalizedTwo
  mass_eval mass_zero from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet

noncomputable section

private theorem hasDerivAt_deriv_sq_at_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (h0 : f 0 = 0) :
    HasDerivAt (deriv (fun t => f t ^ 2)) (2 * deriv f 0 ^ 2) 0 := by
  have hd (t : ℝ) : HasDerivAt f (deriv f t) t :=
    (hf.differentiable (by decide) t).hasDerivAt
  have hdd : DifferentiableAt ℝ (deriv f) 0 :=
    hf.differentiable_deriv_two 0
  have h := ((hd 0).mul hdd.hasDerivAt).const_mul 2
  rw [h0, zero_mul, add_zero, ← pow_two] at h
  convert h using 1
  ext t
  simpa [mul_assoc] using ((hd t).fun_pow 2).deriv

/-- Differentiation of the finite Dirichlet sum at a constant amplitude vector. -/
theorem hasDerivAt_deriv_shiftedEnergy {n : ℕ} (hn : 7 ≤ n)
    (ψ : ℝ → Configuration n → ℂ)
    (hsmooth : ∀ S, ContDiff ℝ 2 (fun t => ψ t S))
    (hbase : ∀ S, ψ 0 S = ψ 0 (emptyConfiguration n)) :
    HasDerivAt (deriv (fun t => shiftedEnergy (ψ t)))
      (2 * shiftedEnergy (fun S => deriv (fun t => ψ t S) 0)) 0 := by
  let d (S T : Configuration n) (t : ℝ) := ψ t S - ψ t T
  have hd (S T : Configuration n) : ContDiff ℝ 2 (d S T) := (hsmooth S).sub (hsmooth T)
  have h (S T : Configuration n) :
      HasDerivAt (deriv (fun t => Complex.normSq (d S T t)))
        (2 * Complex.normSq (deriv (d S T) 0)) 0 := by
    have h0 : d S T 0 = 0 := by simp [d, hbase]
    have hr := hasDerivAt_deriv_sq_at_zero (Complex.reCLM.contDiff.comp (hd S T))
      (show (d S T 0).re = 0 by simp [h0])
    have hi := hasDerivAt_deriv_sq_at_zero (Complex.imCLM.contDiff.comp (hd S T))
      (show (d S T 0).im = 0 by simp [h0])
    have hder (t : ℝ) : HasDerivAt (d S T) (deriv (d S T) t) t :=
      ((hd S T).differentiable (by decide) t).hasDerivAt
    have hRe (t : ℝ) := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t))
    have hIm (t : ℝ) := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hder t))
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply] at hRe hIm
    simp only [Function.comp_def, Complex.reCLM_apply] at hr
    simp only [Function.comp_def, Complex.imCLM_apply] at hi
    rw [(hRe 0).deriv] at hr
    rw [(hIm 0).deriv] at hi
    convert hr.add hi using 1
    · ext t
      rw [show (fun u => Complex.normSq (d S T u)) =
        (fun u => (d S T u).re ^ 2 + (d S T u).im ^ 2) by
          funext u; simp [Complex.normSq_apply, pow_two]]
      exact deriv_add ((hRe t).fun_pow 2).differentiableAt ((hIm t).fun_pow 2).differentiableAt
    · simp only [Complex.normSq_apply, pow_two]
      ring
  let f (S T : Configuration n) (t : ℝ) := transitionWeight S T * Complex.normSq (d S T t)
  have hf (S T : Configuration n) (t : ℝ) : DifferentiableAt ℝ (f S T) t := by
    apply DifferentiableAt.const_mul
    exact ((Complex.reCLM.contDiff.comp (hd S T)).differentiable (by decide) t).mul
      ((Complex.reCLM.contDiff.comp (hd S T)).differentiable (by decide) t) |>.add
        (((Complex.imCLM.contDiff.comp (hd S T)).differentiable (by decide) t).mul
          ((Complex.imCLM.contDiff.comp (hd S T)).differentiable (by decide) t))
  have hfd (S T : Configuration n) (t : ℝ) :
      deriv (f S T) t = transitionWeight S T * deriv (fun t => Complex.normSq (d S T t)) t :=
    deriv_const_mul_field (transitionWeight S T)
  have hsum := (HasDerivAt.sum (u := (Finset.univ : Finset (Configuration n))) fun S _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Configuration n))) fun T _ =>
      (h S T).const_mul (transitionWeight S T)).div_const 2
  have hDiff (S T : Configuration n) :
      deriv (d S T) 0 = deriv (fun t => ψ t S) 0 - deriv (fun t => ψ t T) 0 :=
    deriv_sub ((hsmooth S).differentiable (by decide) 0)
      ((hsmooth T).differentiable (by decide) 0)
  simp_rw [shiftedEnergy_eq_dirichlet hn]
  convert hsum using 1
  · ext t
    simpa only [Finset.sum_apply, hfd] using (((HasDerivAt.sum (u := (Finset.univ : Finset (Configuration n))) fun S _ =>
      HasDerivAt.sum (u := (Finset.univ : Finset (Configuration n))) fun T _ =>
        (hf S T t).hasDerivAt).div_const 2).deriv)
  · simp_rw [hDiff, ← mul_assoc, mul_comm (transitionWeight _ _) 2,
      mul_assoc, ← Finset.mul_sum]
    ring

/-- The slope parameter of the regular null direction at chain length `n`. -/
def nullSlope (n : ℕ) : ℝ := 2 * F n / G n - 3

/-- Unit imaginary (a) component, with (b) chosen to kill the imaginary coherence jet. -/
def nullDirection (n : ℕ) : Coord := ![Complex.I, -(nullSlope n : ℂ) * Complex.I, 0, 0]

private theorem nullSlope_lt_one {n : ℕ} (hn : 7 ≤ n) : nullSlope n < 1 := by
  have hg := G_pos hn
  have h := (fib_bounds hn).2.1
  unfold nullSlope
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hg]
  linarith

theorem regularJet_nullDirection (n : ℕ) (hn : 7 ≤ n) :
    regularJet n (nullDirection n) = 0 := by
  have hg := (G_pos hn).ne'
  have hz := (denominator_factors hn).2.1.ne'
  have hre : (fun i : Fin 4 => (nullDirection n i).re) = 0 := by
    funext i
    fin_cases i <;> simp [nullDirection, Complex.mul_re]
  have him : (![ (nullDirection n 1).im, (nullDirection n 2).im, (nullDirection n 3).im] :
      Fin 3 → ℝ) = ![-nullSlope n, 0, 0] := by
    funext i
    fin_cases i <;> simp [nullDirection, Complex.mul_im]
  unfold regularJet
  rw [hre, him, Matrix.mulVec_zero]
  refine Prod.ext rfl ?_
  have h0 : (nullDirection n 0).im = 1 := Complex.I_im
  rw [h0, one_smul]
  funext i
  change (∑ j : Fin 3, imagBlock n i j * (![ -nullSlope n, 0, 0] : Fin 3 → ℝ) j) +
    imagA n i = 0
  rw [Fin.sum_univ_three]
  fin_cases i
  · simp [imagBlock, imagA, nullSlope]
    field_simp
    ring
  · simp [imagBlock, imagA]
  · simp [imagBlock, imagA]

private theorem wordMatrix_intertwine (A B : Fin 2 → Bond) (P : Bond)
    (h : ∀ i, P * A i = B i * P) {n : ℕ} (w : Word n) :
    P * wordMatrix A w = wordMatrix B w * P := by
  induction n with
  | zero => simp [wordMatrix]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ← Matrix.mul_assoc,
      h, Matrix.mul_assoc, ih, Matrix.mul_assoc]

private theorem traceWord_witness (n : ℕ) (hn : 7 ≤ n) (w : Word n) :
    traceWord 2 2 n (cores witness) w = if Independent (occupied w) then 1 else 0 := by
  let A := PeriodicMPSUniformDeterminantPencil.witnessCore
  let P : Bond := !![1, 0; -1, 1]
  let Q : Bond := !![1, 0; 1, 1]
  have hQP : Q * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, P, Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ : P * Q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, P, Matrix.mul_apply, Fin.sum_univ_two]
  have h (i : Fin 2) : P * cores witness i = A i * P := by
    fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      norm_num [A, P, PeriodicMPSUniformDeterminantPencil.witnessCore, cores, witness,
        hardCoreChart, Matrix.mul_apply, Fin.sum_univ_two]
  have hW := wordMatrix_intertwine (cores witness) A P h w
  have he : wordMatrix (cores witness) w = Q * (wordMatrix A w * P) := by
    rw [← hW, ← Matrix.mul_assoc, hQP, one_mul]
  calc
    traceWord 2 2 n (cores witness) w = (wordMatrix A w).trace := by
      change (wordMatrix (cores witness) w).trace = _
      rw [he, Matrix.trace_mul_comm, Matrix.mul_assoc, hPQ, mul_one]
    _ = _ := PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator hn w

private theorem smooth_amplitude (k : WithTop ℕ∞) {n : ℕ} (w : Word n) :
    ContDiff ℝ k (fun x : Coord => traceWord 2 2 n (cores x) w) := by
  have hcore (i j l : Fin 2) : ContDiff ℝ k (fun x : Coord => cores x i j l) := by
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      first | exact contDiff_const | exact contDiff_apply ℝ (fun _ : Fin 4 => ℂ) _
  have hprod (l : List (Fin 2)) (i j : Fin 2) :
      ContDiff ℝ k (fun x : Coord => (l.map (cores x)).prod i j) := by
    induction l generalizing i j with
    | nil => exact contDiff_const
    | cons l ls ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact ContDiff.sum fun a _ => (hcore l i a).mul (ih a j)
  simp only [traceWord, Matrix.trace, Matrix.diag, List.ofFn_comp']
  exact ContDiff.sum fun i _ => hprod (List.ofFn w) i i

private def path (r : ℕ) (t : ℝ) : Coord := witness + t • nullDirection (r + 4)

private theorem cores_path (r : ℕ) (t : ℝ) :
    cores (path r t) =
      hardCoreChart ((t : ℂ) * Complex.I) (1 + (t : ℂ) * (-(nullSlope (r + 4) : ℂ) * Complex.I))
        (0 : ℂ) 0 := by
  simp [path, cores, witness, nullDirection, Complex.real_smul]

private def amplitude (r : ℕ) (t : ℝ) : Amplitudes (r + 2) :=
  traceWord 2 2 (2 + (r + 2)) (cores (path r t))

private def supportedAmplitude (r : ℕ) (t : ℝ) (S : Configuration (2 + (r + 2))) : ℂ :=
  amplitude r t (configWord S.val)

private theorem amplitude_smooth (r : ℕ) (w : Word (2 + (r + 2))) :
    ContDiff ℝ 2 (fun t => amplitude r t w) := by
  have hp : ContDiff ℝ 2 (path r) := contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (smooth_amplitude 2 w).comp hp

private theorem supportedAmplitude_base (r : ℕ) (hr : 3 ≤ r)
    (S : Configuration (2 + (r + 2))) : supportedAmplitude r 0 S = 1 := by
  simp only [supportedAmplitude, amplitude, path, zero_smul, add_zero,
    traceWord_witness _ (by omega : 7 ≤ 2 + (r + 2)), occupied_configWord, ite_eq_left S.property]

private theorem rawTwo_forbidden (a b : ℂ) (r : ℕ) (p : Fin 2 × Fin 2) :
    rawTwo (hardCoreChart a b 0 0) r (1, 1) p = 0 := by
  have hB : (hardCoreChart a b 0 0 1 : Bond) * hardCoreChart a b 0 0 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hardCoreChart, Matrix.mul_apply, Fin.sum_univ_two]
  rw [rawTwo_entry]
  simp [flattening_entry, hB]

private theorem amplitude_support (r : ℕ) (hr : 3 ≤ r) (t : ℝ) (w : Word (2 + (r + 2)))
    (hw : ¬ Independent (occupied w)) : amplitude r t w = 0 :=
  support_of_pairGram_corner_zero (by omega) (cyclic_traceWord _)
    (by rw [pairGram_traceWord, cores_path]; exact rawTwo_forbidden _ _ _ _) w hw


private theorem hardCoreAPow (a b : ℂ) (n : ℕ) :
    hardCoreChart a b 0 0 0 ^ n = !![1, 0; ∑ i ∈ Finset.range n, a ^ i, a ^ n] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_range_succ, pow_succ a]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hardCoreChart, Matrix.mul_apply, Fin.sum_univ_two]

private theorem wordMatrix_constant (A : Fin 2 → Bond) (n : ℕ) :
    wordMatrix A (fun _ : Fin n => 0) = A 0 ^ n := by
  simp [wordMatrix, List.ofFn_const, List.prod_replicate]

private theorem configWord_empty {n : ℕ} :
    configWord (emptyConfiguration n).val = fun _ => 0 := by
  funext i
  simp [configWord, emptyConfiguration]

private def singletonConfiguration (n : ℕ) (i : Fin n) : Configuration n :=
  ⟨{i}, by
    intro j hj k hk hne
    change j ∈ ({i} : Finset (Fin n)) at hj
    change k ∈ ({i} : Finset (Fin n)) at hk
    simp only [Finset.mem_singleton] at hj hk
    exact (hne (hj.trans hk.symm)).elim⟩

private theorem configWord_singleton_zero (n : ℕ) :
    configWord (singletonConfiguration (n + 1) 0).val =
      Fin.cons 1 (fun _ : Fin n => 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [configWord, singletonConfiguration, Fin.succ_ne_zero]

private theorem amplitude_vacuum (r : ℕ) (t : ℝ) :
    supportedAmplitude r t (emptyConfiguration (2 + (r + 2))) =
      1 + ((t : ℂ) * Complex.I) ^ (2 + (r + 2)) := by
  change (wordMatrix (cores (path r t)) (configWord (emptyConfiguration _).val)).trace = _
  rw [configWord_empty, wordMatrix_constant, cores_path, hardCoreAPow]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private theorem amplitude_singleton (r : ℕ) (t : ℝ) :
    supportedAmplitude r t (singletonConfiguration (2 + (r + 2)) 0) =
      (1 + (t : ℂ) * (-(nullSlope (r + 4) : ℂ) * Complex.I)) *
        ∑ i ∈ Finset.range (2 + (r + 1)), ((t : ℂ) * Complex.I) ^ i := by
  change (wordMatrix (cores (path r t)) (configWord (singletonConfiguration _ 0).val)).trace = _
  have hw : configWord (singletonConfiguration (2 + (r + 2)) 0).val =
      Fin.cons 1 (fun _ : Fin (2 + (r + 1)) => 0) := configWord_singleton_zero _
  rw [hw, wordMatrix_cons, wordMatrix_constant, cores_path, hardCoreAPow]
  simp [hardCoreChart, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply]

private theorem ofReal_line_hasDerivAt (z : ℂ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * z) z 0 := by
  simpa [Complex.real_smul] using (hasDerivAt_id (0 : ℝ)).smul_const z

private theorem power_line_hasDerivAt (k : ℕ) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I) ^ k)
      (if k = 1 then Complex.I else 0) 0 := by
  have h := (ofReal_line_hasDerivAt Complex.I).fun_pow k
  rcases k with _ | k
  · simpa using h
  rcases k with _ | k
  · simpa using h
  simpa [Nat.succ_ne_zero, pow_succ] using h

private theorem supportedAmplitude_vacuum_deriv (r : ℕ) :
    deriv (fun t => supportedAmplitude r t (emptyConfiguration (2 + (r + 2)))) 0 = 0 := by
  have h := (power_line_hasDerivAt (2 + (r + 2))).const_add 1
  simp only [show 2 + (r + 2) ≠ 1 by omega, ite_false] at h
  rw [funext (amplitude_vacuum r)]
  exact h.deriv

private theorem supportedAmplitude_singleton_deriv (r : ℕ) :
    deriv (fun t => supportedAmplitude r t (singletonConfiguration (2 + (r + 2)) 0)) 0 =
      (1 - (nullSlope (r + 4) : ℂ)) * Complex.I := by
  let n := 2 + (r + 1)
  have hs := HasDerivAt.sum (u := Finset.range n) (fun k _ => power_line_hasDerivAt k)
  have hs' : HasDerivAt (fun t : ℝ => ∑ i ∈ Finset.range n, ((t : ℂ) * Complex.I) ^ i)
      Complex.I 0 := by
    have hsum : (∑ i ∈ Finset.range n, if i = 1 then Complex.I else 0) = Complex.I := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact (h (Finset.mem_range.mpr (by dsimp [n]; omega))).elim
    rw [hsum] at hs
    exact hs.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      (Finset.sum_apply t (Finset.range n)
        (fun i (x : ℝ) => ((x : ℂ) * Complex.I) ^ i)).symm)
  have hval : (∑ i ∈ Finset.range n, (((0 : ℝ) : ℂ) * Complex.I) ^ i) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [zero_pow hi]
    · intro h
      exact (h (Finset.mem_range.mpr (by dsimp [n]; omega))).elim
  have h := ((ofReal_line_hasDerivAt (-(nullSlope (r + 4) : ℂ) * Complex.I)).const_add 1).mul hs'
  rw [hval] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_one, one_mul] at h
  have hEq := funext (amplitude_singleton r)
  rw [hEq]
  convert h.deriv using 1
  ring

private theorem supportedAmplitude_tangent_energy_pos (r : ℕ) (hr : 3 ≤ r) :
    0 < shiftedEnergy (fun S => deriv (fun t => supportedAmplitude r t S) 0) := by
  have hn : 7 ≤ 2 + (r + 2) := by omega
  apply lt_of_le_of_ne (shiftedEnergy_nonneg hn _)
  intro h
  have hconst := (shiftedEnergy_eq_zero_iff hn _).mp h.symm (singletonConfiguration _ 0)
  rw [supportedAmplitude_singleton_deriv, supportedAmplitude_vacuum_deriv] at hconst
  have hz : (1 - (nullSlope (r + 4) : ℂ)) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    exact (nullSlope_lt_one (by omega : 7 ≤ r + 4)).ne (sub_eq_zero.mp hre).symm
  exact (mul_ne_zero hz Complex.I_ne_zero) hconst

/-- The strict second derivative of the compressed shifted energy along the literal null line. -/
theorem shiftedEnergy_nullPath_curvature (r : ℕ) (hr : 3 ≤ r) :
    ∃ κ : ℝ, 0 < κ ∧ HasDerivAt (deriv (fun t => shiftedEnergy (supportedAmplitude r t))) κ 0 := by
  refine ⟨_, mul_pos two_pos (supportedAmplitude_tangent_energy_pos r hr), ?_⟩
  apply hasDerivAt_deriv_shiftedEnergy (by omega)
  · intro S
    exact amplitude_smooth r _
  · intro S
    rw [supportedAmplitude_base r hr S, supportedAmplitude_base r hr]


private theorem wordMatrix_reverse_intertwine (A : Fin 2 → Bond) (P : Bond)
    (h : ∀ i, P * A i = (A i).transpose * P) {n : ℕ} (w : Word n) :
    P * wordMatrix A (w ∘ Fin.rev) = (wordMatrix A w).transpose * P := by
  induction n with
  | zero => simp [wordMatrix]
  | succ n ih =>
    have he : w ∘ Fin.rev = Fin.cons (w (Fin.last n)) (Fin.init w ∘ Fin.rev) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Function.comp_def, Fin.rev_succ, Fin.init]
    rw [he, wordMatrix_cons, ← Matrix.mul_assoc, h, Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc, ← Matrix.transpose_mul, ← wordMatrix_snoc, Fin.snoc_init_self]

private theorem hardCore_flattening_reverse (a b : ℂ) (r : ℕ) (i j : Fin 2)
    (w : Word (r + 2)) :
    twoFlattening (hardCoreChart a b 0 0) r (i, j) (w ∘ Fin.rev) =
      twoFlattening (hardCoreChart a b 0 0) r (j, i) w := by
  let A := hardCoreChart a b 0 0
  let P : Bond := !![0, 1; 1, a - 1]
  let Q : Bond := !![1 - a, 1; 1, 0]
  have hQP : Q * P = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ : P * Q = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two]
  have hp (i : Fin 2) : P * A i = (A i).transpose * P := by
    fin_cases i <;> ext k l <;> fin_cases k <;> fin_cases l <;>
      simp [P, A, hardCoreChart, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  change twoFlattening A r (i, j) (w ∘ Fin.rev) = twoFlattening A r (j, i) w
  rw [flattening_entry, flattening_entry]
  let M := A i * A j * wordMatrix A (w ∘ Fin.rev)
  have hM : P * M = (wordMatrix A w * A j * A i).transpose * P := by
    dsimp [M]
    calc
      _ = ((P * A i) * A j) * wordMatrix A (w ∘ Fin.rev) := by simp only [Matrix.mul_assoc]
      _ = (A i).transpose * ((P * A j) * wordMatrix A (w ∘ Fin.rev)) := by
        rw [hp i]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hp j, Matrix.mul_assoc ((A j).transpose), wordMatrix_reverse_intertwine A P hp w]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  change M.trace = _
  have he : M = Q * ((wordMatrix A w * A j * A i).transpose * P) := by
    rw [← hM, ← Matrix.mul_assoc, hQP, one_mul]
  rw [he, Matrix.trace_mul_comm, Matrix.mul_assoc, hPQ, mul_one, Matrix.trace_transpose]
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm (wordMatrix A w) (A j * A i)

private theorem hardCore_rawTwo_swap (a b : ℂ) (r : ℕ) (i j k l : Fin 2) :
    rawTwo (hardCoreChart a b 0 0) r (i, j) (k, l) =
      rawTwo (hardCoreChart a b 0 0) r (j, i) (l, k) := by
  rw [rawTwo_entry, rawTwo_entry]
  let e : Word (r + 2) ≃ Word (r + 2) :=
    { toFun := fun w => w ∘ Fin.rev
      invFun := fun w => w ∘ Fin.rev
      left_inv := fun w => by funext i; simp
      right_inv := fun w => by funext i; simp }
  exact Fintype.sum_equiv e _ _ (fun w => by
    change _ = twoFlattening _ r (j, i) (w ∘ Fin.rev) *
      star (twoFlattening _ r (l, k) (w ∘ Fin.rev))
    rw [hardCore_flattening_reverse, hardCore_flattening_reverse])

/-- The energy covector with the linear response of the forbidden coherences removed.
On each level of the regular readout it is a constant minus twice the real coherence. -/
def normalOutput (r : ℕ) (x : Coord) : ℝ :=
  1 - 2 * component false r 3 x - component false r 1 x - component false r 2 x +
    (2 * G (r + 4) / (F (r + 4) - G (r + 4))) *
      (2 * component false r 5 x - component false r 4 x)

private theorem mass_pos_witness (r : ℕ) (hr : 3 ≤ r) :
    0 < twoMass (cores witness) r := by
  have h := mass_eval (0 : Coord) r 0
  rw [Complex.ofReal_zero, mass_zero (0 : Coord) (r + 4) (by omega),
    zero_smul, add_zero] at h
  rw [← h]
  exact (denominator_factors (by omega : 7 ≤ r + 4)).2.1

private theorem twoMass_smooth (k : WithTop ℕ∞) (r : ℕ) :
    ContDiff ℝ k (fun x : Coord => twoMass (cores x) r) := by
  have h : (fun x : Coord => twoMass (cores x) r) =
      fun x => mass (traceWord 2 2 (2 + (r + 2)) (cores x)) := by
    funext x
    rw [mass_eq_trace, pairGram_traceWord]
    rfl
  rw [h]
  unfold mass
  apply ContDiff.sum
  intro w _
  rw [show (fun x : Coord => Complex.normSq (traceWord 2 2 (2 + (r + 2)) (cores x) w)) =
      (fun x => (traceWord 2 2 (2 + (r + 2)) (cores x) w).re ^
        2 + (traceWord 2 2 (2 + (r + 2)) (cores x) w).im ^ 2) by
          funext x; simp [Complex.normSq_apply, pow_two]]
  exact ((Complex.reCLM.contDiff.comp (smooth_amplitude k w)).pow 2).add
    ((Complex.imCLM.contDiff.comp (smooth_amplitude k w)).pow 2)

private theorem component_smooth (k : WithTop ℕ∞) (r : ℕ) (hr : 3 ≤ r)
    (imag : Bool) (i : Fin 8) : ContDiffAt ℝ k (component imag r i) witness := by
  have hF (p : Pair) (w : Word (r + 2)) :
      ContDiff ℝ k (fun x : Coord => twoFlattening (cores x) r p w) :=
    smooth_amplitude k _
  have hRaw : ContDiff ℝ k (fun x : Coord => rawTwo (cores x) r (entry i).1 (entry i).2) := by
    simp only [rawTwo_entry]
    exact ContDiff.sum fun w _ => (hF _ w).mul (Complex.conjCLE.contDiff.comp (hF _ w))
  have h := ((twoMass_smooth k r).contDiffAt.inv (mass_pos_witness r hr).ne').smul
    hRaw.contDiffAt
  cases imag
  · exact Complex.reCLM.contDiff.contDiffAt.comp witness h
  · exact Complex.imCLM.contDiff.contDiffAt.comp witness h

private theorem normalOutput_smooth (k : WithTop ℕ∞) (r : ℕ) (hr : 3 ≤ r) :
    ContDiffAt ℝ k (normalOutput r) witness := by
  unfold normalOutput
  have h (i : Fin 8) := component_smooth k r hr false i
  fun_prop

private theorem normalOutput_hasDerivAt (r : ℕ) (hr : 3 ≤ r) (u : Coord) :
    HasDerivAt (fun t : ℝ => normalOutput r (witness + t • u)) 0 0 := by
  let n := r + 4
  have hn : 7 ≤ r + 4 := by omega
  have hz := (denominator_factors hn).2.1.ne'
  have hfg : F n - G n ≠ 0 := by
    have hg := G_pos hn
    have h := (fib_bounds hn).1
    dsimp [n]
    linarith
  have h (i : Fin 8) := hasDerivAt_component false r hr i u
  have hd := (((((h 3).const_mul 2).const_sub 1).sub (h 1)).sub (h 2)).add
    ((((h 5).const_mul 2).sub (h 4)).const_mul (2 * G n / (F n - G n)))
  apply hd.congr_deriv
  dsimp [n] at hfg
  simp [raw_zero u _ _ hn, (raw_one_parts u _ hn _).1, rawReal, pA, pB, qA,
    mass_one u _ hn, n]
  field_simp
  unfold Z
  ring

/-- The displayed affine marginal functional annihilates the full chart derivative. -/
theorem normalOutput_hasFDerivAt (r : ℕ) (hr : 3 ≤ r) :
    HasFDerivAt (normalOutput r) (0 : Coord →L[ℝ] ℝ) witness := by
  have hd := (normalOutput_smooth 1 r hr).differentiableAt (by decide)
  suffices h : fderiv ℝ (normalOutput r) witness = 0 by simpa [h] using hd.hasFDerivAt
  ext u
  have hp : HasDerivAt (fun t : ℝ => witness + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add witness
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)).unique
    (normalOutput_hasDerivAt r hr u)

private theorem normalOutput_path_eq (r : ℕ) (hr : 3 ≤ r) (t : ℝ)
    (hpos : 0 < twoMass (cores (path r t)) r) :
    normalOutput r (path r t) =
      shiftedEnergy (supportedAmplitude r t) /
        ((2 + (r + 2) : ℕ) * twoMass (cores (path r t)) r) := by
  have henergy := shiftedEnergy_eq_observed (by omega : 7 ≤ 2 + (r + 2))
    (cyclic_traceWord (cores (path r t))) (amplitude_support r hr t)
  rw [mass_eq_trace, pairGram_traceWord] at henergy
  change shiftedEnergy (supportedAmplitude r t) =
    _ * twoMass (cores (path r t)) r + _ at henergy
  let A := cores (path r t)
  have hf (p : Pair) : rawTwo A r (1, 1) p = 0 := by
    dsimp [A]
    rw [cores_path]
    exact rawTwo_forbidden _ _ _ _
  have hf' (p : Pair) : rawTwo A r p (1, 1) = 0 := by
    rw [← rawTwo_star_swap, hf, star_zero]
  have hswap (i j k l : Fin 2) : rawTwo A r (i, j) (k, l) = rawTwo A r (j, i) (l, k) := by
    dsimp [A]
    rw [cores_path]
    exact hardCore_rawTwo_swap _ _ _ _ _ _ _
  rw [henergy]
  change normalOutput r (path r t) =
    (_ * twoMass A r + _ * edgeExpectation (rawTwo A r)) / (_ * twoMass A r)
  unfold edgeExpectation normalOutput
  rw [hswap 0 0 1 0, hswap 1 0 1 0, hf' (0, 1), hf (1, 1)]
  have hN (i : Fin 8) : component false r i (path r t) =
      (twoMass A r)⁻¹ * (rawTwo A r (entry i).1 (entry i).2).re := by
    simp [component, normalizedTwo, Matrix.smul_apply, Complex.real_smul, Complex.mul_re, A]
  simp [hN, entry, hf]
  have hn : (0 : ℝ) < ((2 + (r + 2) : ℕ) : ℝ) := by positivity
  change 0 < twoMass A r at hpos
  field_simp [hpos.ne', hn.ne']
  ring


private theorem path_smooth (k : WithTop ℕ∞) (r : ℕ) : ContDiff ℝ k (path r) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

private theorem path_zero (r : ℕ) : path r 0 = witness := by simp [path]

/-- The corrected marginal has a strictly positive second derivative on the actual null line. -/
theorem normalOutput_nullPath_curvature (r : ℕ) (hr : 3 ≤ r) :
    0 < deriv (deriv (fun t : ℝ => normalOutput r
      (witness + t • nullDirection (r + 4)))) 0 := by
  let M : ℝ → ℝ := fun t => ((2 + (r + 2) : ℕ) : ℝ) * twoMass (cores (path r t)) r
  let N : ℝ → ℝ := fun t => normalOutput r (path r t)
  let E : ℝ → ℝ := fun t => shiftedEnergy (supportedAmplitude r t)
  have hM : ContDiff ℝ 2 M :=
    contDiff_const.mul ((twoMass_smooth 2 r).comp (path_smooth 2 r))
  have hN : ContDiffAt ℝ 2 N 0 := by
    have h := normalOutput_smooth 2 r hr
    rw [← path_zero r] at h
    exact h.comp 0 (path_smooth 2 r).contDiffAt
  have hmass : ∀ᶠ t : ℝ in 𝓝 0, 0 < twoMass (cores (path r t)) r := by
    have hc : ContinuousAt (fun t => twoMass (cores (path r t)) r) 0 :=
      ((twoMass_smooth 2 r).comp (path_smooth 2 r)).continuous.continuousAt
    apply hc.eventually (lt_mem_nhds ?_)
    simpa only [path_zero] using mass_pos_witness r hr
  have hM0 : 0 < M 0 := by
    dsimp [M]
    rw [path_zero]
    exact mul_pos (by positivity) (mass_pos_witness r hr)
  have heq : E =ᶠ[𝓝 (0 : ℝ)] fun t => M t * N t := by
    filter_upwards [hmass] with t ht
    have h := normalOutput_path_eq r hr t ht
    change N t = E t / M t at h
    rw [h, mul_div_cancel₀]
    exact (mul_pos (by positivity : (0 : ℝ) < ↑(2 + (r + 2) : ℕ)) ht).ne'
  have he0 : E 0 = 0 :=
    (shiftedEnergy_eq_zero_iff (by omega) _).mpr (fun S => by
      rw [supportedAmplitude_base r hr S, supportedAmplitude_base r hr])
  have hN0 : N 0 = 0 := by
    have h := heq.eq_of_nhds
    change E 0 = M 0 * N 0 at h
    rw [he0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hM0.ne'
  have hNd0 : deriv N 0 = 0 :=
    (normalOutput_hasDerivAt r hr (nullDirection (r + 4))).deriv
  have hdEq : deriv E =ᶠ[𝓝 (0 : ℝ)] (fun t => deriv M t * N t + M t * deriv N t) := by
    refine heq.deriv.trans ?_
    filter_upwards [hN.eventually (by decide)] with t ht
    exact deriv_fun_mul (hM.differentiable (by decide) t) (ht.differentiableAt (by decide))
  have hdM : DifferentiableAt ℝ (deriv M) 0 := hM.differentiable_deriv_two 0
  have hdN : DifferentiableAt ℝ (deriv N) 0 :=
    (hN.derivWithin (m := 1) (by decide)).differentiableAt (by decide)
  have hcalc := (hdM.hasDerivAt.mul (hN.differentiableAt (by decide)).hasDerivAt).add
    (((hM.differentiable (by decide) 0).hasDerivAt).mul hdN.hasDerivAt)
  have hresult := hcalc.congr_of_eventuallyEq hdEq
  rw [hN0, hNd0] at hresult
  simp only [mul_zero, add_zero, zero_add] at hresult
  obtain ⟨κ, hκ, hE⟩ := shiftedEnergy_nullPath_curvature r hr
  have hval : M 0 * deriv (deriv N) 0 = κ := hresult.unique hE
  change 0 < deriv (deriv N) 0
  exact pos_of_mul_pos_right (hval.symm ▸ hκ) hM0.le

private theorem hasDerivAt_deriv_comp_of_stationary
    {f : Coord → ℝ} {γ : ℝ → Coord} {u : Coord}
    (hf : ContDiffAt ℝ 2 f witness) (hf0 : HasFDerivAt f (0 : Coord →L[ℝ] ℝ) witness)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = witness) (hu : HasDerivAt γ u 0) :
    HasDerivAt (deriv (fun t => f (γ t)))
      (fderiv ℝ (fderiv ℝ f) witness u u) 0 := by
  have hdf := (hf.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have hfirst := hdf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hγ0.symm
  have hsecond := ((hγ.derivWithin (m := 1) (by decide)).differentiableAt
    (by decide)).hasDerivAt
  have h := hfirst.clm_apply hsecond
  simp only [Function.comp_apply, hγ0, hf0.fderiv, hu.deriv] at h
  simp only [zero_apply, add_zero] at h
  apply h.congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 f (γ t) := by
    have hc := hγ.continuousAt
    rw [← hγ0] at hf
    exact hc.eventually (hf.eventually (by decide))
  filter_upwards [hnear, hγ.eventually (by decide)] with t ht ht'
  exact ((ht.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t
    (ht'.differentiableAt (by decide)).hasDerivAt).deriv

/-- The literal Fréchet Hessian of the normal marginal covector is positive on the kernel line. -/
theorem normalOutput_hessian_pos (r : ℕ) (hr : 3 ≤ r) :
    let u := nullDirection (r + 4)
    0 < fderiv ℝ (fderiv ℝ (normalOutput r)) witness u u := by
  have hp : HasDerivAt (path r) (nullDirection (r + 4)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const
      (nullDirection (r + 4))).const_add witness
    rw [one_smul] at h
    exact h
  have h := hasDerivAt_deriv_comp_of_stationary (normalOutput_smooth 2 r hr)
    (normalOutput_hasFDerivAt r hr) (path_smooth 2 r).contDiffAt (path_zero r) hp
  dsimp only
  rw [← h.deriv]
  exact normalOutput_nullPath_curvature r hr

private theorem normalOutput_eq_on_level (r : ℕ) {x : Coord}
    (hx : regularReadout r x = regularReadout r witness) :
    normalOutput r x = normalOutput r witness + 2 * component false r 3 witness -
      2 * component false r 3 x := by
  have h (i : Fin 4) := congrFun (congrArg Prod.fst hx) i
  have hp : component false r 1 x = component false r 1 witness := h 0
  have hq : component false r 2 x = component false r 2 witness := h 1
  have hw : component false r 4 x = component false r 4 witness := h 2
  have hv : component false r 5 x = component false r 5 witness := h 3
  unfold normalOutput
  rw [hp, hq, hw, hv]
  ring

/-- Every twice differentiable parametrization with the regular observations fixed and
the specified tangent has strictly negative second derivative of the real coherence. -/
theorem coherence_curvature_on_regular_level (r : ℕ) (hr : 3 ≤ r) (γ : ℝ → Coord)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = witness)
    (hu : HasDerivAt γ (nullDirection (r + 4)) 0)
    (hR : ∀ᶠ t : ℝ in 𝓝 0, regularReadout r (γ t) = regularReadout r witness) :
    deriv (deriv (fun t => component false r 3 (γ t))) 0 < 0 := by
  let C := normalOutput r witness + 2 * component false r 3 witness
  let H : ℝ → ℝ := fun t => component false r 3 (γ t)
  have hH : ContDiffAt ℝ 2 H 0 := by
    have h := component_smooth 2 r hr false 3
    rw [← hγ0] at h
    exact h.comp 0 hγ
  have he : (fun t => normalOutput r (γ t)) =ᶠ[𝓝 (0 : ℝ)] fun t => C - 2 * H t := by
    exact hR.mono fun _ ht => normalOutput_eq_on_level r ht
  have hdEq : deriv (fun t => normalOutput r (γ t)) =ᶠ[𝓝 (0 : ℝ)] fun t => -(2 * deriv H t) := by
    refine he.deriv.trans ?_
    filter_upwards [hH.eventually (by decide)] with t ht
    exact (((ht.differentiableAt (by decide)).hasDerivAt.const_mul 2).const_sub C).deriv
  have hD := (((hH.derivWithin (m := 1) (by decide)).differentiableAt
    (by decide)).hasDerivAt.const_mul 2).neg.congr_of_eventuallyEq hdEq
  have h := hasDerivAt_deriv_comp_of_stationary (normalOutput_smooth 2 r hr)
    (normalOutput_hasFDerivAt r hr) hγ hγ0 hu
  have hpos := normalOutput_hessian_pos r hr
  dsimp only at hpos
  rw [← hD.unique h] at hpos
  change deriv (deriv H) 0 < 0
  linarith


/-- The diagonal forbidden entry has zero differential on the whole chart at the witness. -/
theorem forbidden_corner_hasFDerivAt (r : ℕ) (hr : 3 ≤ r) :
    HasFDerivAt (component false r 6) (0 : Coord →L[ℝ] ℝ) witness := by
  have hd := (component_smooth 1 r hr false 6).differentiableAt (by decide)
  suffices h : fderiv ℝ (component false r 6) witness = 0 by simpa [h] using hd.hasFDerivAt
  ext u
  have hp : HasDerivAt (fun t : ℝ => witness + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add witness
  have h := hasDerivAt_component false r hr 6 u
  have hn : 7 ≤ r + 4 := by omega
  simp [raw_zero u 6 _ hn, (raw_one_parts u _ hn 6).1, rawReal] at h
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)).unique h

/-- The diagonal forbidden entry vanishes identically on the null line. -/
theorem forbidden_corner_nullPath (r : ℕ) (t : ℝ) :
    component false r 6 (witness + t • nullDirection (r + 4)) = 0 := by
  change component false r 6 (path r t) = 0
  have h : rawTwo (cores (path r t)) r (1, 1) (1, 1) = 0 := by
    rw [cores_path]
    exact rawTwo_forbidden _ _ _ _
  simp [component, normalizedTwo, Matrix.smul_apply, entry, h]


/-- The second variation of the forbidden diagonal is zero in the regular kernel direction. -/
theorem forbidden_corner_hessian_zero (r : ℕ) (hr : 3 ≤ r) :
    let u := nullDirection (r + 4)
    fderiv ℝ (fderiv ℝ (component false r 6)) witness u u = 0 := by
  have hp : HasDerivAt (path r) (nullDirection (r + 4)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const
      (nullDirection (r + 4))).const_add witness
    rw [one_smul] at h
    exact h
  have h := hasDerivAt_deriv_comp_of_stationary (component_smooth 2 r hr false 6)
    (forbidden_corner_hasFDerivAt r hr) (path_smooth 2 r).contDiffAt (path_zero r) hp
  have hzero : (fun t : ℝ => component false r 6 (path r t)) = fun _ => 0 :=
    funext (forbidden_corner_nullPath r)
  rw [hzero] at h
  simpa using h.deriv.symm

private theorem regularCoordinates_smooth (r : ℕ) (hr : 3 ≤ r) :
    ContDiffAt ℝ 2 (regularCoordinates r) witness := by
  have h : ContDiffAt ℝ 2 (regularReadout r) witness := by
    apply ContDiffAt.prodMk
    · apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> exact component_smooth 2 r hr false _
    · apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> exact component_smooth 2 r hr true _
  let π : Coord →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj 0)
  exact π.contDiff.contDiffAt.prodMk h

private theorem exists_regularCoordinates_equiv (r : ℕ) (hr : 3 ≤ r) :
    ∃ L : Coord ≃L[ℝ] (ℝ × ((Fin 4 → ℝ) × (Fin 3 → ℝ))),
      HasFDerivAt (regularCoordinates r) (L : Coord →L[ℝ] _) witness ∧
      L (nullDirection (r + 4)) = (1, 0) := by
  let π : Coord →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj 0)
  let A := π.prod (fderiv ℝ (regularReadout r) witness)
  have hA (u : Coord) : A u = ((u 0).im, regularJet (r + 4) u) :=
    Prod.ext rfl (fderiv_regularReadout_apply r hr u)
  have hB : Function.Bijective A := by
    constructor
    · intro u v hv
      rw [hA, hA] at hv
      obtain ⟨w, _, hw⟩ := reconstruct_regularJet (r + 4) (by omega) (u 0).im
        (regularJet (r + 4) u)
      exact (hw u ⟨rfl, rfl⟩).trans
        (hw v ⟨(congrArg Prod.fst hv).symm, (congrArg Prod.snd hv).symm⟩).symm
    · rintro ⟨t, y⟩
      obtain ⟨u, hu, _⟩ := reconstruct_regularJet (r + 4) (by omega) t y
      exact ⟨u, (hA u).trans (Prod.ext hu.1 hu.2)⟩
  let L := (LinearEquiv.ofBijective A.toLinearMap hB).toContinuousLinearEquiv
  have he : (L : Coord →L[ℝ] _) = A := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  refine ⟨L, ?_, ?_⟩
  · rw [he]
    exact π.hasFDerivAt.prodMk
      ((regularReadout_contDiffAt r hr).differentiableAt (by decide)).hasFDerivAt
  · change A _ = _
    rw [hA, regularJet_nullDirection _ (by omega)]
    rfl

private theorem exists_regular_level_curve (r : ℕ) (hr : 3 ≤ r) :
    ∃ γ : ℝ → Coord, ContDiffAt ℝ 2 γ 0 ∧ γ 0 = witness ∧
      HasDerivAt γ (nullDirection (r + 4)) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, regularCoordinates r (γ t) = (t, regularReadout r witness)) := by
  obtain ⟨L, hL, hu⟩ := exists_regularCoordinates_equiv r hr
  have hs := regularCoordinates_smooth r hr
  have hS := hs.hasStrictFDerivAt' hL (by decide)
  let g : ℝ → ℝ × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) := fun t => (t, regularReadout r witness)
  have hg0 : g 0 = regularCoordinates r witness := rfl
  have hg2 : ContDiff ℝ 2 g := contDiff_id.prodMk contDiff_const
  have hg : HasDerivAt g (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (regularReadout r witness))
  have hInv : HasFDerivAt (hs.localInverse hL (by decide))
      (L.symm : _ →L[ℝ] Coord) (regularCoordinates r witness) :=
    hS.to_localInverse.hasFDerivAt
  let γ := (hs.localInverse hL (by decide)) ∘ g
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · have h := hs.to_localInverse hL (by decide)
    rw [← hg0] at h
    exact h.comp 0 hg2.contDiffAt
  · change hs.localInverse hL (by decide) (g 0) = witness
    rw [hg0]
    exact hs.localInverse_apply_image hL (by decide)
  · have h := hInv.comp_hasDerivAt_of_eq 0 hg hg0.symm
    simpa only [← hu, ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using h
  · have ht := hS.eventually_right_inverse
    rw [← hg0] at ht
    exact hg2.continuous.continuousAt.eventually ht

/-- At every length at least seven, the real (00,01) coherence has a nondegenerate
critical point in the free coordinate on the actual fixed-regular-output slice. -/
theorem exists_regular_level_fold (r : ℕ) (hr : 3 ≤ r) :
    ∃ γ : ℝ → Coord, ContDiffAt ℝ 2 γ 0 ∧ γ 0 = witness ∧
      HasDerivAt γ (nullDirection (r + 4)) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, regularCoordinates r (γ t) = (t, regularReadout r witness)) ∧
      deriv (fun t => component false r 3 (γ t)) 0 = 0 ∧
      deriv (deriv (fun t => component false r 3 (γ t))) 0 < 0 := by
  obtain ⟨γ, hγ, hγ0, hu, hc⟩ := exists_regular_level_curve r hr
  have hR : ∀ᶠ t : ℝ in 𝓝 0, regularReadout r (γ t) = regularReadout r witness :=
    hc.mono fun _ h => congrArg Prod.snd h
  refine ⟨γ, hγ, hγ0, hu, hc, ?_, coherence_curvature_on_regular_level r hr γ hγ hγ0 hu hR⟩
  let C := normalOutput r witness + 2 * component false r 3 witness
  let H : ℝ → ℝ := fun t => component false r 3 (γ t)
  have hH := (component_smooth 1 r hr false 3).differentiableAt (by decide)
  have hd := hH.hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hγ0.symm
  have hn := (normalOutput_hasFDerivAt r hr).comp_hasDerivAt_of_eq 0 hu hγ0.symm
  have he : (fun t => normalOutput r (γ t)) =ᶠ[𝓝 (0 : ℝ)] fun t => C - 2 * H t := by
    exact hR.mono fun _ ht => normalOutput_eq_on_level r ht
  have hh := (hd.const_mul 2).const_sub C
  have hgrad := (hh.congr_of_eventuallyEq he).unique hn
  simp only [zero_apply] at hgrad
  change deriv (component false r 3 ∘ γ) 0 = 0
  rw [hd.deriv]
  linarith


/-- The seven regular outputs, the real (00,01) coherence, and the forbidden diagonal. -/
def observation (r : ℕ) (x : Coord) : ((Fin 4 → ℝ) × (Fin 3 → ℝ)) × (ℝ × ℝ) :=
  (regularReadout r x, (component false r 3 x, component false r 6 x))

private def regularCorrection (r : ℕ) : ((Fin 4 → ℝ) × (Fin 3 → ℝ)) →L[ℝ] ℝ :=
  let π (i : Fin 4) := (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (Fin 4 → ℝ) (Fin 3 → ℝ))
  (-(π 0)) - π 1 + (2 * G (r + 4) / (F (r + 4) - G (r + 4))) • (2 • π 3 - π 2)

private theorem coherence_derivative (r : ℕ) (hr : 3 ≤ r) :
    HasFDerivAt (component false r 3)
      ((1 / 2 : ℝ) • ((regularCorrection r).comp (fderiv ℝ (regularReadout r) witness)))
      witness := by
  have hR := ((regularReadout_contDiffAt r hr).differentiableAt (by decide)).hasFDerivAt
  have h := (((hasFDerivAt_const (1 : ℝ) witness).add
    ((regularCorrection r).hasFDerivAt.comp witness hR)).sub
      (normalOutput_hasFDerivAt r hr)).const_smul (1 / 2 : ℝ)
  simp only [zero_add, sub_zero] at h
  convert h using 1
  funext x
  simp [normalOutput, regularCorrection, regularReadout, two_smul]
  ring

/-- The differential of all nine literal readouts has the same rank as
the certified differential of the seven regular readouts. -/
theorem observation_rank_seven (r : ℕ) (hr : 3 ≤ r) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (observation r) witness).toLinearMap) = 7 := by
  let A := fderiv ℝ (regularReadout r) witness
  let B := A.prod (((1 / 2 : ℝ) • ((regularCorrection r).comp A)).prod
    (0 : Coord →L[ℝ] ℝ))
  have hR := ((regularReadout_contDiffAt r hr).differentiableAt (by decide)).hasFDerivAt
  have hD : HasFDerivAt (observation r) B witness :=
    hR.prodMk ((coherence_derivative r hr).prodMk (forbidden_corner_hasFDerivAt r hr))
  have hker : LinearMap.ker B.toLinearMap = LinearMap.ker A.toLinearMap := by
    ext u
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · exact fun h => congrArg Prod.fst h
    · intro h
      simp [B, h]
  have h1 := B.toLinearMap.finrank_range_add_finrank_ker
  have h2 := A.toLinearMap.finrank_range_add_finrank_ker
  rw [hker] at h1
  have hrank := regularReadout_rank_seven r hr
  change Module.finrank ℝ (LinearMap.range A.toLinearMap) = 7 at hrank
  rw [hD.fderiv]
  omega

/-- The kernel of the regular differential is the real line generated by the stated tangent. -/
theorem regular_kernel_iff (r : ℕ) (hr : 3 ≤ r) (u : Coord) :
    fderiv ℝ (regularReadout r) witness u = 0 ↔
      ∃ t : ℝ, u = t • nullDirection (r + 4) := by
  have hk : fderiv ℝ (regularReadout r) witness (nullDirection (r + 4)) = 0 := by
    rw [fderiv_regularReadout_apply r hr, regularJet_nullDirection _ (by omega)]
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := reconstruct_regularJet (r + 4) (by omega) (u 0).im 0
    have hu : (u 0).im = (u 0).im ∧ regularJet (r + 4) u = 0 := by
      exact ⟨rfl, (fderiv_regularReadout_apply r hr u).symm.trans h⟩
    let t := (u 0).im
    have hz := (fderiv ℝ (regularReadout r) witness).map_smul t (nullDirection (r + 4))
    rw [hk, smul_zero, fderiv_regularReadout_apply r hr] at hz
    have ht : ((t • nullDirection (r + 4)) 0).im = (u 0).im := by
      simp [t, nullDirection, Complex.real_smul, Complex.mul_im]
    exact ⟨t, (hv u hu).trans (hv _ ⟨ht, hz⟩).symm⟩
  · rintro ⟨t, rfl⟩
    rw [map_smul, hk, smul_zero]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.shiftedEnergy_nullPath_curvature
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.normalOutput_hasFDerivAt
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.normalOutput_hessian_pos
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.forbidden_corner_hessian_zero
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.exists_regular_level_fold
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.observation_rank_seven
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFoldCurvature.regular_kernel_iff
