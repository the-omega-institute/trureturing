/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteTraceBase
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteTraceBase
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The zero locus and normal maps of the seven-site trace polynomial. -/
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The full seven-site trace polynomial, its base locus, and the two normal maps. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteTraceBase

open Matrix Polynomial
open scoped BigOperators
open D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation (traceWord)
open D5.S0.Observation.MatrixTracePowerSum (pow_add_two trace_pow_add_two)

noncomputable section

abbrev Word (n : ℕ) := Fin n → Fin 2
abbrev Amp := Word 7 → ℂ
abbrev Bond (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- Coefficients in the ordered list (1, A, B, AB), for traces t,s,
determinants d,e, and mixed trace k. -/
private def form {R : Type*} [CommRing R] (t s d e k : R) :
    List (Fin 2) → R × R × R × R
  | [] => (1, 0, 0, 0)
  | i :: w =>
    let (u,a,b,c) := form t s d e k w
    if i = 0 then (-d*a, u+t*a, -d*c, b+t*c)
    else ((k-t*s)*a-e*b-t*e*c, s*a+e*c, u+t*a+s*b+k*c, -a)

/-- The polynomial in the five literal trace/determinant coordinates. -/
def wordPolynomial {R : Type*} [CommRing R] (t s d e k : R) (w : List (Fin 2)) : R :=
  let (u,a,b,c) := form t s d e k w
  2*u+t*a+s*b+k*c

def amplitude {R : Type*} [CommRing R] (p : Fin 5 → R) (w : Word 7) : R :=
  wordPolynomial (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn w)

private def realize {R : Type*} [CommRing R] (A B : Bond R) (f : R × R × R × R) :
    Bond R :=
  f.1 • 1 + f.2.1 • A + f.2.2.1 • B + f.2.2.2 • (A * B)

private theorem realize_form {R : Type*} [CommRing R] (A B : Bond R) (w : List (Fin 2)) :
    realize A B (form A.trace B.trace A.det B.det (A * B).trace w) =
      (w.map fun i => if i = 0 then A else B).prod := by
  have square (M : Bond R) : M * M = M.trace • M - M.det • 1 := by
    simpa only [Nat.reduceAdd, pow_two, pow_one, pow_zero] using pow_add_two M 0
  have hBA : B * A =
      A.trace • B + B.trace • A + ((A * B).trace - A.trace * B.trace) • 1 - A * B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> ring
  have hAAB : A * (A * B) = A.trace • (A * B) - A.det • B := by
    rw [← mul_assoc, square A, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have hBAB : B * (A * B) =
      (-(A.trace * B.det)) • 1 + B.det • A + (A * B).trace • B := by
    have hABB : (A * B) * B = B.trace • (A * B) - B.det • A := by
      rw [mul_assoc, square B, mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
    rw [← mul_assoc, hBA, sub_mul, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
      smul_mul_assoc, one_mul, square B, hABB]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  induction w with
  | nil => simp [form, realize]
  | cons i w ih =>
    rcases hf : form A.trace B.trace A.det B.det (A * B).trace w with ⟨u,a,b,c⟩
    simp only [form, hf, List.map_cons, List.prod_cons, ← ih]
    by_cases hi : i = 0
    · simp only [hi, if_true, realize, mul_add, mul_smul_comm, mul_one, square A, hAAB]
      ext j l
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · simp only [hi, if_false, realize, mul_add, mul_smul_comm, mul_one, square B, hBA, hBAB]
      ext j l
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring

def wordProduct {R : Type*} [CommRing R] {n : ℕ} (A : Fin 2 → Bond R) (w : Word n) :
    Bond R := (List.ofFn fun j => A (w j)).prod

theorem wordPolynomial_eq_trace {R : Type*} [CommRing R] {n : ℕ}
    (A : Fin 2 → Bond R) (w : Word n) :
    wordPolynomial (A 0).trace (A 1).trace (A 0).det (A 1).det (A 0 * A 1).trace
      (List.ofFn w) = (wordProduct A w).trace := by
  have select (i : Fin 2) : (if i = 0 then A 0 else A 1) = A i := by fin_cases i <;> rfl
  have h := congrArg Matrix.trace (realize_form (A 0) (A 1) (List.ofFn w))
  rcases hf : form (A 0).trace (A 1).trace (A 0).det (A 1).det
      (A 0 * A 1).trace (List.ofFn w) with ⟨u,a,b,c⟩
  simp only [hf, realize, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul, List.map_ofFn, Function.comp_def, select] at h
  simp only [wordPolynomial, hf, wordProduct]
  rw [← h]
  ring

theorem amplitude_actual (A : Fin 2 → Bond ℂ) :
    amplitude ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace] =
      traceWord 2 2 7 A :=
  funext fun w => wordPolynomial_eq_trace A w

private theorem map_form {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t s d e k : R) (w : List (Fin 2)) :
    form (f t) (f s) (f d) (f e) (f k) w =
      (f (form t s d e k w).1, f (form t s d e k w).2.1,
        f (form t s d e k w).2.2.1, f (form t s d e k w).2.2.2) := by
  induction w with
  | nil => simp [form]
  | cons i w ih =>
    rcases hw : form t s d e k w with ⟨u,a,b,c⟩
    rw [hw] at ih
    by_cases hi : i = 0 <;> simp [form, hi, ih, hw]

theorem map_amplitude {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Fin 5 → R) (w : Word 7) :
    f (amplitude p w) = amplitude (f ∘ p) w := by
  unfold amplitude wordPolynomial
  rw [show (f ∘ p) 0 = f (p 0) from rfl, show (f ∘ p) 1 = f (p 1) from rfl,
    show (f ∘ p) 2 = f (p 2) from rfl, show (f ∘ p) 3 = f (p 3) from rfl,
    show (f ∘ p) 4 = f (p 4) from rfl, map_form]
  rcases form (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn w) with ⟨u,a,b,c⟩
  simp [map_ofNat]

private theorem wordProduct_smul {R : Type*} [CommRing R] {n : ℕ}
    (A : Fin 2 → Bond R) (c : Fin 2 → R) (w : Word n) :
    wordProduct (fun i => c i • A i) w =
      (List.ofFn fun i => c (w i)).prod • wordProduct A w := by
  induction n with
  | zero => simp [wordProduct]
  | succ n ih =>
    change (List.ofFn fun i => c (w i) • A (w i)).prod = _
    simp only [List.ofFn_succ, List.prod_cons, wordProduct]
    rw [show (List.ofFn fun i : Fin n => c (w i.succ) • A (w i.succ)).prod =
        (List.ofFn fun i : Fin n => c (w i.succ)).prod •
          (List.ofFn fun i : Fin n => A (w i.succ)).prod from ih (fun i => w i.succ)]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem amplitude_scale (z t s d e k : ℂ) :
    amplitude ![z*t,z*s,z^2*d,z^2*e,z^2*k] =
      z^7 • amplitude (![t,s,d,e,k] : Fin 5 → ℂ) := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates t s d e k
  have h := amplitude_actual (fun i => z • A i)
  simp only [Matrix.trace_smul, smul_eq_mul, Matrix.det_smul, Fintype.card_fin,
    smul_mul_assoc, mul_smul_comm, smul_smul, ht, hs, hd, he, hk, ← pow_two] at h
  have hA := amplitude_actual A
  rw [ht, hs, hd, he, hk] at hA
  rw [h, hA]
  funext w
  change (wordProduct (fun i => z • A i) w).trace = z^7 * (wordProduct A w).trace
  rw [wordProduct_smul A (fun _ => z), Matrix.trace_smul, smul_eq_mul]
  change (List.ofFn (fun _ : Fin 7 => z)).prod * (wordProduct A w).trace =
    z^7 * (wordProduct A w).trace
  rw [List.ofFn_const, List.prod_replicate]

private theorem form_traceless {R : Type*} [CommRing R] (d e k : R) (w : List (Fin 2)) :
    let f := form 0 0 d e k w
    (w.length % 2 = 0 → f.2.1 = 0 ∧ f.2.2.1 = 0) ∧
      (w.length % 2 = 1 → f.1 = 0 ∧ f.2.2.2 = 0) := by
  induction w with
  | nil => simp [form]
  | cons i w ih =>
    rcases hw : form (0 : R) 0 d e k w with ⟨u,a,b,c⟩
    simp only [hw] at ih
    constructor
    · intro h
      rw [List.length_cons] at h
      obtain ⟨hu, hc⟩ := ih.2 (by omega)
      by_cases hi : i = 0 <;> simp [form, hi, hw, hu, hc]
    · intro h
      rw [List.length_cons] at h
      obtain ⟨ha, hb⟩ := ih.1 (by omega)
      by_cases hi : i = 0 <;> simp [form, hi, hw, ha, hb]

theorem amplitude_traceless (d e k : ℂ) :
    amplitude (![0,0,d,e,k] : Fin 5 → ℂ) = 0 := by
  funext w
  have hw : (List.ofFn w).length % 2 = 1 := by simp
  have h := (form_traceless d e k (List.ofFn w)).2 hw
  unfold amplitude
  change wordPolynomial 0 0 d e k (List.ofFn w) = 0
  unfold wordPolynomial
  rcases hf : form (0 : ℂ) 0 d e k (List.ofFn w) with ⟨u,a,b,c⟩
  simp only [hf] at h
  simp [hf, h.1, h.2]

def pencil {R : Type*} [CommRing R] (p : Fin 5 → R) (z w : R) : R :=
  p 2 * z^2 + (p 0 * p 1 - p 4) * z*w + p 3 * w^2

def powerTrace {R : Type*} [CommRing R] (t d : R) : R :=
  t * (t^6 - 7*t^4*d + 14*t^2*d^2 - 7*d^3)

def vacuum {R : Type*} [CommRing R] (a : R) : R := 1 - 7*a + 14*a^2 - 7*a^3

def vacuumSlope {R : Type*} [CommRing R] (a : R) : R := -7 + 28*a - 21*a^2

theorem vacuumSlope_ne_zero {a : ℂ} (ha : vacuum a = 0) : vacuumSlope a ≠ 0 := by
  intro hb
  have hc : (-5 + 14 * a) / 9 = 0 := by
    unfold vacuum at ha
    unfold vacuumSlope at hb
    linear_combination ha - (a / 3 - 2 / 9) * hb
  have h : a = 5 / 14 := by linear_combination (9 / 14 : ℂ) * hc
  rw [h] at hb
  norm_num [vacuumSlope] at hb

private theorem trace_pow_seven {R : Type*} [CommRing R] (M : Bond R) :
    (M ^ 7).trace = powerTrace M.trace M.det := by
  have h₂ := trace_pow_add_two M 0
  have h₃ := trace_pow_add_two M 1
  have h₄ := trace_pow_add_two M 2
  have h₅ := trace_pow_add_two M 3
  have h₆ := trace_pow_add_two M 4
  have h₇ := trace_pow_add_two M 5
  norm_num only [Nat.reduceAdd, pow_zero, pow_one, Matrix.trace_one, Fintype.card_fin]
    at h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₇, h₆, h₅, h₄, h₃, h₂]
  unfold powerTrace
  ring

private theorem sum_wordProduct {R : Type*} [CommRing R] (A : Fin 2 → Bond R) (n : ℕ) :
    ∑ w : Word n, wordProduct A w = (A 0 + A 1)^n := by
  induction n with
  | zero => simp [wordProduct]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, wordProduct, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.prod_cons, Fin.sum_univ_two, ← Finset.mul_sum]
    change A 0 * (∑ w : Word n, wordProduct A w) +
      A 1 * (∑ w : Word n, wordProduct A w) = _
    rw [← add_mul, ih, pow_succ']

def contraction {R : Type*} [CommRing R] (z w : R) (v : Word 7 → R) : R :=
  ∑ i : Word 7, (List.ofFn fun j => if i j = 0 then z else w).prod * v i

/-- The symmetric contraction of the literal tensor is the seventh power trace. -/
theorem contraction_amplitude (p : Fin 5 → ℂ) (z w : ℂ) :
    contraction z w (amplitude p) = powerTrace (p 0*z + p 1*w) (pencil p z w) := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
  let c : Fin 2 → ℂ := fun i => if i = 0 then z else w
  let B : Fin 2 → Bond ℂ := fun i => c i • A i
  have hword (i : Word 7) : amplitude p i = (wordProduct A i).trace := by
    simpa only [amplitude, ht, hs, hd, he, hk] using wordPolynomial_eq_trace A i
  calc
    contraction z w (amplitude p) = ∑ i : Word 7, (wordProduct B i).trace := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [B, wordProduct_smul, Matrix.trace_smul, smul_eq_mul, hword, c]
    _ = ((z • A 0 + w • A 1)^7).trace := by
      rw [← Matrix.trace_sum, sum_wordProduct]
      rfl
    _ = _ := by
      rw [trace_pow_seven, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ht, hs]
      have hdet : (z • A 0 + w • A 1).det = pencil p z w := by
        rw [pencil, ← ht, ← hs, ← hd, ← he, ← hk]
        simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      rw [hdet]
      congr 1
      simp only [smul_eq_mul]
      ring

/-- The same contraction identity over a polynomial extension, by evaluation. -/
theorem contraction_amplitude_extension {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (h : ∀ (p : Fin 5 → R) (z w : R),
      contraction z w (amplitude p) = powerTrace (p 0*z + p 1*w) (pencil p z w))
    (p : Fin 5 → R[X]) (z w : R[X]) :
    contraction z w (amplitude p) = powerTrace (p 0*z + p 1*w) (pencil p z w) := by
  apply Polynomial.funext
  intro x
  let f := Polynomial.evalRingHom x
  change f (contraction z w (amplitude p)) =
    f (powerTrace (p 0*z + p 1*w) (pencil p z w))
  simpa only [contraction, powerTrace, pencil, map_sum, map_mul, map_one, map_list_prod,
    List.map_ofFn, Function.comp_def, apply_ite, map_sub, map_add, map_pow,
    map_ofNat, map_amplitude] using h (f ∘ p) (f z) (f w)

def proportional (s a : ℂ) : Fin 5 → ℂ := ![1,s,a,a*s^2,(1-2*a)*s]

theorem amplitude_proportional (s a : ℂ) (ha : vacuum a = 0) :
    amplitude (proportional s a) = 0 := by
  let A : Bond ℂ := !![0,-a;1,1]
  let B : Fin 2 → Bond ℂ := ![A,s • A]
  have hA : A.trace = 1 := by simp [A, Matrix.trace_fin_two]
  have hD : A.det = a := by simp [A, Matrix.det_fin_two]
  have hB : (B 1).trace = s := by simp [B, Matrix.trace_smul, hA]
  have hE : (B 1).det = a*s^2 := by
    simp [B, Matrix.det_smul, Fintype.card_fin, hD, mul_comm]
  have hK : (B 0 * B 1).trace = (1-2*a)*s := by
    change (A * (s • A)).trace = _
    have hh := trace_pow_add_two A 0
    norm_num only [Nat.reduceAdd, pow_one, pow_zero, Matrix.trace_one, Fintype.card_fin] at hh
    rw [mul_smul_comm, Matrix.trace_smul, ← pow_two, hh, hA, hD]
    simp only [smul_eq_mul]
    ring
  have hActual : amplitude (proportional s a) = traceWord 2 2 7 B := by
    have h := amplitude_actual B
    change amplitude ![A.trace, (B 1).trace, A.det, (B 1).det, (B 0 * B 1).trace] = _ at h
    simpa only [proportional, hA, hB, hD, hE, hK] using h
  rw [hActual]
  funext w
  have hB' : B = fun i => (if i = 0 then 1 else s) • A := by
    funext i
    fin_cases i <;> simp [B]
  change (wordProduct B w).trace = 0
  rw [hB', wordProduct_smul (fun _ => A), Matrix.trace_smul]
  have hprod : wordProduct (fun _ : Fin 2 => A) w = A^7 := by
    change (List.ofFn (fun _ : Fin 7 => A)).prod = A^7
    rw [List.ofFn_const, List.prod_replicate]
  rw [hprod, trace_pow_seven, hA, hD]
  have hh : powerTrace (1 : ℂ) a = vacuum a := by simp [powerTrace, vacuum]
  rw [hh, ha, smul_zero]

private theorem vacuum_constant (D : ℂ[X]) (hD : vacuum D = 0) :
    D = C (D.coeff 0) := by
  by_contra h
  have hn : 0 < D.natDegree :=
    Nat.pos_of_ne_zero fun hz => h (eq_C_of_natDegree_eq_zero hz)
  let q : ℂ[X] := 1 - 7*D + 14*D^2
  have hq : q.natDegree ≤ 2 * D.natDegree := by
    unfold q
    have h₁ : (1 - 7*D : ℂ[X]).natDegree ≤ D.natDegree := by
      have hsub := natDegree_sub_le (1 : ℂ[X]) (7 * D)
      rw [natDegree_one, max_eq_right (Nat.zero_le _)] at hsub
      exact hsub.trans (by simpa only [natDegree_ofNat, zero_add] using
        (natDegree_mul_le (p := (7 : ℂ[X])) (q := D)))
    have h₂ : (14 * D^2 : ℂ[X]).natDegree ≤ 2 * D.natDegree := by
      have hmul := natDegree_mul_le (p := (14 : ℂ[X])) (q := D^2)
      rw [natDegree_ofNat, zero_add] at hmul
      exact hmul.trans (natDegree_pow_le (p := D) (n := 2))
    exact natDegree_add_le_of_degree_le (h₁.trans (by omega)) h₂
  have h₃ : (7 * D^3 : ℂ[X]).natDegree = 3 * D.natDegree := by
    have hd : D ≠ 0 := fun e => h (by simp [e])
    rw [natDegree_mul (by norm_num) (pow_ne_zero _ hd), natDegree_pow]
    rw [natDegree_ofNat, zero_add]
  have heq : q = 7 * D^3 := sub_eq_zero.mp hD
  rw [heq, h₃] at hq
  omega

/-- The exact base locus in the trace-one chart. -/
theorem amplitude_first_eq_zero_iff (s d e k : ℂ) :
    amplitude (![1,s,d,e,k] : Fin 5 → ℂ) = 0 ↔
      vacuum d = 0 ∧ e = d*s^2 ∧ k = (1-2*d)*s := by
  constructor
  · intro h
    let p : Fin 5 → ℂ := ![1,s,d,e,k]
    let z : ℂ[X] := 1 - C s * X
    let D := pencil (C ∘ p) z X
    have hp : amplitude (C ∘ p) = 0 := by
      funext w
      rw [← map_amplitude C p w]
      simpa only [show amplitude p w = 0 from congrFun h w, map_zero, Pi.zero_apply]
    have hτ : (C ∘ p) 0 * z + (C ∘ p) 1 * X = 1 := by
      change C (1 : ℂ) * z + C s * X = 1
      simp [z]
    have hdet := contraction_amplitude_extension contraction_amplitude (C ∘ p) z X
    rw [hp, hτ] at hdet
    have hD : vacuum D = 0 := by
      simpa [contraction, powerTrace, vacuum, D] using hdet.symm
    have hDC := vacuum_constant D hD
    have heval (x : ℂ) : d*(1-s*x)^2 + (s-k)*(1-s*x)*x + e*x^2 = D.coeff 0 := by
      have hh := congrArg (Polynomial.eval x) hDC
      simpa [D, pencil, p, z] using hh
    have h0 : d = D.coeff 0 := by simpa using heval 0
    have h1 := heval 1
    have hm := heval (-1)
    have hd : vacuum d = 0 := by
      have hh := congrArg (Polynomial.eval 0) hD
      rw [hDC, ← h0] at hh
      simpa [vacuum] using hh
    exact ⟨hd, by linear_combination (h1 + hm) / 2 - h0 +
        s * (h1 - hm) / 2, by linear_combination -(h1 - hm) / 2⟩
  · rintro ⟨hd,rfl,rfl⟩
    exact amplitude_proportional s d hd


def line {R : Type*} [CommRing R] (b v : Fin 5 → R) (i : Fin 5) : R[X] :=
  C (b i) + X * C (v i)

theorem eval_line_amplitude (b v : Fin 5 → ℂ) (l : ℂ) (w : Word 7) :
    (amplitude (line b v) w).eval l = amplitude (b + l • v) w := by
  rw [← Polynomial.coe_evalRingHom, map_amplitude]
  congr 1
  funext i
  change (line b v i).eval l = (b + l • v) i
  simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The coefficient linear in the normal parameter. -/
def normal (b v : Fin 5 → ℂ) : Amp := fun w => (amplitude (line b v) w).coeff 1

def secant (b v : Fin 5 → ℂ) (l : ℂ) : Amp :=
  fun w => ((amplitude (line b v) w).divX).eval l

theorem secant_zero (b v : Fin 5 → ℂ) : secant b v 0 = normal b v := by
  funext w
  simp only [secant, normal, ← coeff_zero_eq_eval_zero, coeff_divX, zero_add]

/-- Exact factorization of the amplitude on a line through a base point. -/
theorem amplitude_eq_smul_secant (b v : Fin 5 → ℂ) (l : ℂ) (hb : amplitude b = 0) :
    amplitude (b + l • v) = l • secant b v l := by
  funext w
  have h := congrArg (Polynomial.eval l) (X_mul_divX_add (amplitude (line b v) w))
  have h0 : (amplitude (line b v) w).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_line_amplitude, zero_smul, add_zero, hb]
    rfl
  simpa [h0, eval_line_amplitude, secant, Pi.smul_apply, smul_eq_mul] using h.symm

private theorem contraction_normal (b v : Fin 5 → ℂ) (z w : ℂ[X]) :
    contraction z w (C ∘ normal b v) =
      (powerTrace
        (line (C ∘ b) (C ∘ v) 0 * C z + line (C ∘ b) (C ∘ v) 1 * C w)
        (pencil (line (C ∘ b) (C ∘ v)) (C z) (C w))).coeff 1 := by
  let f : ℂ →+* ℂ[X] := C
  have hmap (j : Word 7) :
      amplitude (line (C ∘ b) (C ∘ v)) j = (amplitude (line b v) j).map f := by
    rw [← coe_mapRingHom, map_amplitude]
    congr 1
    funext i
    simp [line, f]
  have hC (i : Word 7) :
      (List.ofFn fun j => if i j = 0 then C z else C w).prod =
        C ((List.ofFn fun j => if i j = 0 then z else w).prod) := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, apply_ite]
  have h := congrArg (fun p : (ℂ[X])[X] => p.coeff 1)
    (contraction_amplitude_extension
      (contraction_amplitude_extension contraction_amplitude)
      (line (C ∘ b) (C ∘ v)) (C z) (C w))
  simpa only [contraction, finsetSum_coeff, hC, coeff_C_mul, hmap, coeff_map,
    Function.comp_apply, normal, f] using h

private theorem quadratic_coefficients {a b c : ℂ}
    (h : C a + C b * X + C c * X^2 = (0 : ℂ[X])) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := congrArg (Polynomial.eval 0) h
  have h1 := congrArg (Polynomial.eval 1) h
  have hm := congrArg (Polynomial.eval (-1)) h
  norm_num at h0 h1 hm
  exact ⟨h0, by linear_combination (h1 - hm)/2, by linear_combination (h1 + hm)/2 - h0⟩

def traceBase (p : Fin 3 → ℂ) : Fin 5 → ℂ := ![0,0,p 0,p 1,p 2]

def traceNormal (v : Fin 2 → ℂ) : Fin 5 → ℂ := ![v 0,v 1,0,0,0]

def pencilNormal (v : Fin 3 → ℂ) : Fin 5 → ℂ := ![0,0,v 0,v 1,v 2]

/-- Over a nonzero traceless pencil the first-order symmetric contractions
recover both independent trace variations. -/
theorem trace_normal_injective (p : Fin 3 → ℂ) (hp : p ≠ 0) :
    Function.Injective (fun v => normal (traceBase p) (traceNormal v)) := by
  let D : ℂ[X] := C (p 0) + C (-(p 2)) * X + C (p 1) * X^2
  have hD : D ≠ 0 := by
    intro h
    obtain ⟨h₀,h₂,h₁⟩ := quadratic_coefficients h
    apply hp
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact neg_eq_zero.mp h₂
  have hdet (v : Fin 2 → ℂ) :
      contraction (1 : ℂ[X]) X (C ∘ normal (traceBase p) (traceNormal v)) =
        -7 * (C (v 0) + C (v 1) * X) * D^3 := by
    let L : ℂ[X] := C (v 0) + C (v 1) * X
    let b : Fin 5 → (ℂ[X])[X] := line (C ∘ traceBase p) (C ∘ traceNormal v)
    let traceLine : (ℂ[X])[X] := X * C L
    let detLine : (ℂ[X])[X] := pencil b 1 (C (X : ℂ[X]))
    have h := contraction_normal (traceBase p) (traceNormal v) 1 X
    change _ = (powerTrace (b 0 * C 1 + b 1 * C X) (pencil b (C 1) (C X))).coeff 1 at h
    have hτ : b 0 * C 1 + b 1 * C X = traceLine := by
      simp [traceLine, b, L, line, traceBase, traceNormal] <;> ring
    have hpencil : detLine.eval 0 = D := by
      simp [detLine, pencil, b, line, D, traceBase, traceNormal] <;> ring
    have htrace : traceLine.eval 0 = 0 := by
      simp only [traceLine, Polynomial.eval_mul, Polynomial.eval_X, zero_mul]
    have hcoeff (q : (ℂ[X])[X]) : (traceLine * q).coeff 1 = (C L * q).eval 0 := by
      change ((X * C L) * q).coeff 1 = _
      rw [mul_assoc]
      exact (Polynomial.coeff_X_mul (C L * q) 0).trans
        (Polynomial.coeff_zero_eq_eval_zero (C L * q))
    have hpower : (powerTrace traceLine detLine).coeff 1 = -7 * L * D ^ 3 := by
      unfold powerTrace
      rw [hcoeff]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_ofNat, htrace, hpencil]
      ring
    have hC1 : (Polynomial.C (1 : ℂ[X]) : (ℂ[X])[X]) = 1 :=
      map_one (Polynomial.C : ℂ[X] →+* (ℂ[X])[X])
    rw [h, hτ, hC1]
    exact hpower
  intro u v huv
  have h := (hdet u).symm.trans ((congrArg
    (fun a : Amp => contraction (1 : ℂ[X]) X (C ∘ a)) huv).trans (hdet v))
  have hL : (C (u 0) + C (u 1) * X : ℂ[X]) = C (v 0) + C (v 1) * X := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hD)
    apply mul_left_cancel₀ (show (-7 : ℂ[X]) ≠ 0 by norm_num)
    calc
      -7 * ((C (u 0) + C (u 1) * X) * D^3) = _ := (mul_assoc _ _ _).symm
      _ = -7 * ((C (v 0) + C (v 1) * X) * D^3) := h.trans (mul_assoc _ _ _)
  have h0 := congrArg (Polynomial.eval 0) hL
  have h1 := congrArg (Polynomial.eval 1) hL
  simp at h0 h1
  funext i
  fin_cases i
  · exact h0
  · change u 1 = v 1
    rw [h0] at h1
    exact add_left_cancel h1

private theorem coeff_one_vacuum_line (R : Type*) [CommRing R] (a n : R) :
    (vacuum (C a + X * C n : R[X])).coeff 1 = vacuumSlope a * n := by
  have h : vacuum (C a + X * C n : R[X]) =
      C (vacuum a) + X * C (vacuumSlope a * n) +
        X^2 * (C ((14 - 21*a)*n^2) - X * C (7*n^3)) := by
    simp only [vacuum, vacuumSlope, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
      map_neg]
    ring
  rw [h, coeff_add, coeff_add, pow_two, mul_assoc, coeff_X_mul, coeff_X_mul,
    coeff_X_mul_zero, coeff_C_zero]
  simp

/-- On each proportional component the first-order contraction is the
nonzero vacuum slope times the entire normal determinant pencil. -/
theorem proportional_normal_injective (s a : ℂ) (ha : vacuum a = 0) :
    Function.Injective (fun v => normal (proportional s a) (pencilNormal v)) := by
  let z : ℂ[X] := 1 - C s * X
  let Q (v : Fin 3 → ℂ) : ℂ[X] := C (v 0) * z^2 - C (v 2) * z*X + C (v 1)*X^2
  have hdet (v : Fin 3 → ℂ) :
      contraction z X (C ∘ normal (proportional s a) (pencilNormal v)) =
        C (vacuumSlope a) * Q v := by
    let b : Fin 5 → (ℂ[X])[X] := line (C ∘ proportional s a) (C ∘ pencilNormal v)
    have h := contraction_normal (proportional s a) (pencilNormal v) z X
    change _ = (powerTrace (b 0 * C z + b 1 * C X) (pencil b (C z) (C X))).coeff 1 at h
    have hb₀ : b 0 = 1 := by simp [b, line, proportional, pencilNormal]
    have hb₁ : b 1 = C (C s) := by simp [b, line, proportional, pencilNormal]
    have hb₂ : b 2 = C (C a) + X * C (C (v 0)) := rfl
    have hb₃ : b 3 = C (C (a * s^2)) + X * C (C (v 1)) := rfl
    have hb₄ : b 4 = C (C ((1-2*a)*s)) + X * C (C (v 2)) := rfl
    have hτ : b 0 * C z + b 1 * C X = 1 := by
      rw [hb₀, hb₁]
      simp [z]
    have hD : pencil b (C z) (C X) = C (C a) + X * C (Q v) := by
      rw [pencil, hb₀, hb₁, hb₂, hb₃, hb₄]
      simp only [Q, z, map_add, map_sub, map_mul, map_pow, map_one, Polynomial.C_ofNat]
      ring
    have hSlope : vacuumSlope (Polynomial.C a : ℂ[X]) = Polynomial.C (vacuumSlope a) := by
      unfold vacuumSlope
      rw [map_sub (Polynomial.C : ℂ →+* ℂ[X]) (-7 + 28 * a) (21 * a ^ 2),
        map_add (Polynomial.C : ℂ →+* ℂ[X]) (-7) (28 * a)]
      simp only [map_mul, map_pow, map_neg, Polynomial.C_ofNat]
    rw [h, hτ, hD, show ∀ (p : (ℂ[X])[X]), powerTrace 1 p = vacuum p from
      fun p => by simp [powerTrace, vacuum], coeff_one_vacuum_line, hSlope]
  intro u v huv
  have h := (hdet u).symm.trans ((congrArg (fun p : Amp => contraction z X (C ∘ p))
    huv).trans (hdet v))
  have hQ := mul_left_cancel₀ (show (C (vacuumSlope a) : ℂ[X]) ≠ 0 by
    simp [vacuumSlope_ne_zero ha]) h
  have heval (x : ℂ) :
      u 0 * (1-s*x)^2 - u 2 * (1-s*x)*x + u 1*x^2 =
        v 0 * (1-s*x)^2 - v 2 * (1-s*x)*x + v 1*x^2 := by
    simpa [Q, z] using congrArg (Polynomial.eval x) hQ
  have h₀ := heval 0
  have h₁ := heval 1
  have hm := heval (-1)
  funext i
  fin_cases i
  · change u 0 = v 0
    simpa using h₀
  · change u 1 = v 1
    linear_combination (h₁ + hm)/2 - h₀ + s*(h₁ - hm)/2 + s^2*h₀
  · change u 2 = v 2
    linear_combination -(h₁ - hm)/2 - 2*s*h₀

theorem differentiable_eval_polynomial {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : MvPolynomial ι ℂ) (f : ι → E → ℂ)
    (hf : ∀ i, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (fun x => MvPolynomial.eval (fun i => f i x) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.fun_mul (hf i)

theorem differentiable_amplitude {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] : Differentiable 𝕜 (amplitude (R := ℂ)) := by
  apply differentiable_pi.mpr
  intro w
  let p : Fin 5 → MvPolynomial (Fin 5) ℂ := MvPolynomial.X
  have h (b : Fin 5 → ℂ) : MvPolynomial.eval b (amplitude p w) = amplitude b w := by
    rw [map_amplitude]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := b) i
  simpa only [h] using differentiable_eval_polynomial (𝕜 := 𝕜) (amplitude p w)
    (fun i (b : Fin 5 → ℂ) => b i) (fun i => differentiable_apply i)

theorem normal_smul (b v : Fin 5 → ℂ) (c : ℂ) :
    normal b (c • v) = c • normal b v := by
  let f : ℂ[X] →+* ℂ[X] := Polynomial.compRingHom (C c * X)
  have hline : f ∘ line b v = line b (c • v) := by
    funext i
    simp only [Function.comp_apply, f, Polynomial.coe_compRingHom_apply, line,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Pi.smul_apply, smul_eq_mul, Polynomial.C_mul]
    rw [mul_comm (C c) X, mul_assoc]
  funext w
  have hamplitude : f (amplitude (line b v) w) = amplitude (line b (c • v)) w := by
    rw [map_amplitude f (line b v) w, hline]
  change (amplitude (line b (c • v)) w).coeff 1 = c * (amplitude (line b v) w).coeff 1
  calc
    _ = (f (amplitude (line b v) w)).coeff 1 :=
      congrArg (fun p : ℂ[X] => p.coeff 1) hamplitude.symm
    _ = (amplitude (line b v) w).coeff 1 * c := by
      simp only [f, Polynomial.coe_compRingHom_apply, Polynomial.comp_C_mul_X_coeff, pow_one]
    _ = _ := mul_comm _ _

theorem normal_zero (b : Fin 5 → ℂ) : normal b 0 = 0 := by
  simpa only [zero_smul] using normal_smul b 0 0

private abbrev SecantVariables := Fin 5 ⊕ (Fin 5 ⊕ Unit)

private def secantPolynomial (w : Word 7) : MvPolynomial SecantVariables ℂ :=
  let b : Fin 5 → MvPolynomial SecantVariables ℂ := fun i => MvPolynomial.X (.inl i)
  let v : Fin 5 → MvPolynomial SecantVariables ℂ := fun i => MvPolynomial.X (.inr (.inl i))
  (amplitude (line b v) w).divX.eval (MvPolynomial.X (.inr (.inr ())))

private def secantValues (x : (Fin 5 → ℂ) × (Fin 5 → ℂ) × ℂ) :
    SecantVariables → ℂ
  | .inl i => x.1 i
  | .inr (.inl i) => x.2.1 i
  | .inr (.inr _) => x.2.2

private theorem secant_eq_eval (b v : Fin 5 → ℂ) (l : ℂ) (w : Word 7) :
    secant b v l w = MvPolynomial.eval (secantValues (b,v,l)) (secantPolynomial w) := by
  let f := MvPolynomial.eval (secantValues (b,v,l))
  let p : (MvPolynomial SecantVariables ℂ)[X] := amplitude (line (fun i => MvPolynomial.X (.inl i))
    (fun i => MvPolynomial.X (.inr (.inl i)))) w
  have hl : f (MvPolynomial.X (.inr (.inr ()))) = l :=
    MvPolynomial.eval_X (f := secantValues (b,v,l)) _
  have hp : p.map f = amplitude (line b v) w := by
    rw [← coe_mapRingHom, map_amplitude]
    congr 1
    funext i
    simp [line, f, secantValues]
  have hdiv : p.divX.map f = (p.map f).divX := by
    apply Polynomial.ext
    intro i
    simp only [coeff_map, coeff_divX]
  change ((amplitude (line b v) w).divX).eval l =
    f (p.divX.eval (MvPolynomial.X (.inr (.inr ()))))
  rw [← eval_map_apply, hl, hdiv, hp]

theorem differentiable_secant {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] :
    Differentiable 𝕜 (fun x : (Fin 5 → ℂ) × (Fin 5 → ℂ) × ℂ =>
      secant x.1 x.2.1 x.2.2) := by
  apply differentiable_pi.mpr
  intro w
  simp_rw [secant_eq_eval]
  apply differentiable_eval_polynomial
  rintro (i | i | ⟨⟩) <;> simp only [secantValues] <;> fun_prop

end

end D5.S3.Quantum.TensorNetworks.SevenSiteTraceBase
