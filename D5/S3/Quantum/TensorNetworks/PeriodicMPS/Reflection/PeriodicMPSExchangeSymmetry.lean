/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSExchangeSymmetry
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSExchangeSymmetry
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection]
   utility: none
   digest: Exchange symmetry of the actual two-site state. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSExchangeSymmetry

open Matrix
open scoped Matrix Polynomial
open PeriodicMPSParentIntersection (Bond Word)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSUniformHardCoreMarginalWitness (pairGram)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal)
open TwoQubitMarginalReflection (ExchangeSymmetric)

noncomputable section

private abbrev Core (R : Type*) := Fin 2 → Matrix (Fin 2) (Fin 2) R

private def intertwiningEquation {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    Fin 3 → R :=
  ![M 0 1, M 1 1 - M 0 0, -M 1 0]

private def symmetricIntertwiner {R : Type*} [CommRing R] (A : Core R) :
    Matrix (Fin 2) (Fin 2) R :=
  let a := intertwiningEquation (A 0)
  let b := intertwiningEquation (A 1)
  let x := a 1 * b 2 - a 2 * b 1
  let y := a 2 * b 0 - a 0 * b 2
  let z := a 0 * b 1 - a 1 * b 0
  !![x, y; y, z]

private theorem intertwines {R : Type*} [CommRing R] (A : Core R) (i : Fin 2) :
    symmetricIntertwiner A * A i = (A i)ᵀ * symmetricIntertwiner A := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [symmetricIntertwiner, intertwiningEquation, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

private def wordProduct {R : Type*} [CommRing R] (A : Core R) (w : List (Fin 2)) :
    Matrix (Fin 2) (Fin 2) R :=
  (w.map A).prod

private theorem intertwines_word {R : Type*} [CommRing R] (A : Core R) (w : List (Fin 2)) :
    symmetricIntertwiner A * wordProduct A w = (wordProduct A w.reverse)ᵀ *
      symmetricIntertwiner A := by
  induction w with
  | nil => simp [wordProduct]
  | cons i w ih =>
    simp only [wordProduct, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, Matrix.mul_one, Matrix.transpose_mul] at *
    rw [← Matrix.mul_assoc, intertwines, Matrix.mul_assoc, ih, Matrix.mul_assoc]

private theorem trace_word_reverse_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (A : Core R) (h : (symmetricIntertwiner A).det ≠ 0) (w : List (Fin 2)) :
    (wordProduct A w).trace = (wordProduct A w.reverse).trace := by
  let S := symmetricIntertwiner A
  have he := congrArg (fun M => (S.adjugate * M).trace) (intertwines_word A w)
  change (S.adjugate * (S * wordProduct A w)).trace =
    (S.adjugate * ((wordProduct A w.reverse)ᵀ * S)).trace at he
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, ← Matrix.mul_assoc S.adjugate,
    Matrix.trace_mul_comm _ S, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_transpose] at he
  exact mul_left_cancel₀ h he

private theorem map_intertwiner {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (A : Core R) :
    f.mapMatrix (symmetricIntertwiner A) =
      symmetricIntertwiner (fun i => f.mapMatrix (A i)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [symmetricIntertwiner, intertwiningEquation, RingHom.mapMatrix_apply]

private theorem map_wordProduct {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (A : Core R) (w : List (Fin 2)) :
    f.mapMatrix (wordProduct A w) = wordProduct (fun i => f.mapMatrix (A i)) w := by
  induction w with
  | nil => simp [wordProduct]
  | cons i w ih =>
    change f.mapMatrix (A i * wordProduct A w) =
      f.mapMatrix (A i) * wordProduct (fun i => f.mapMatrix (A i)) w
    rw [map_mul, ih]

private def referenceCore : Core ℂ :=
  ![!![0, 0; 0, 1], !![0, 1; 1, 0]]

private theorem referenceIntertwiner_det : (symmetricIntertwiner referenceCore).det = 1 := by
  simp [Matrix.det_fin_two, symmetricIntertwiner, intertwiningEquation, referenceCore]

private def interpolation (A : Core ℂ) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  Matrix.of fun a b => (1 - Polynomial.X) * Polynomial.C (A i a b) +
    Polynomial.X * Polynomial.C (referenceCore i a b)

private theorem eval_interpolation_zero (A : Core ℂ) (i : Fin 2) :
    (Polynomial.evalRingHom 0).mapMatrix (interpolation A i) = A i := by
  ext a b; simp [interpolation, RingHom.mapMatrix_apply]

private theorem eval_interpolation_one (A : Core ℂ) (i : Fin 2) :
    (Polynomial.evalRingHom 1).mapMatrix (interpolation A i) = referenceCore i := by
  ext a b; simp [interpolation, RingHom.mapMatrix_apply]

/-- Reversing a binary word preserves its trace for any bond-two core.
The polynomial interpolation removes the generic invertibility condition on
the simultaneous transpose intertwiner, including for singular cores. -/
private theorem trace_word_reverse (A : Core ℂ) (w : List (Fin 2)) :
    (wordProduct A w.reverse).trace = (wordProduct A w).trace := by
  have hs : (symmetricIntertwiner (interpolation A)).det ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.evalRingHom (1 : ℂ)) h
    rw [RingHom.map_det, map_intertwiner] at he
    simp only [eval_interpolation_one, map_zero, referenceIntertwiner_det] at he
    exact one_ne_zero he
  have he := congrArg (Polynomial.evalRingHom (0 : ℂ))
    (trace_word_reverse_of_det_ne_zero (interpolation A) hs w)
  rw [AddMonoidHom.map_trace, AddMonoidHom.map_trace] at he
  change ((Polynomial.evalRingHom (0 : ℂ)).mapMatrix (wordProduct _ w)).trace =
    ((Polynomial.evalRingHom (0 : ℂ)).mapMatrix (wordProduct _ w.reverse)).trace at he
  rw [map_wordProduct, map_wordProduct] at he
  simpa only [eval_interpolation_zero] using he.symm

private def join {m : ℕ} (p : Fin 2 × Fin 2) (b : Word m) : Word (2 + m) :=
  Fin.append ![p.1, p.2] b

private theorem ofFn_rev (m : ℕ) (b : Word m) :
    List.ofFn (b ∘ Fin.rev) = (List.ofFn b).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
  change b (Fin.rev ⟨i, _⟩) = b ⟨_, _⟩
  congr 1
  apply Fin.ext
  simp only [Fin.rev, List.length_ofFn]
  omega

private theorem traceWord_eq_wordProduct (A : Core ℂ) (n : ℕ) (w : Word n) :
    traceWord 2 2 n A w = (wordProduct A (List.ofFn w)).trace := by
  simp only [traceWord, wordProduct, List.map_ofFn, Function.comp_def]

private theorem joined_trace_swap (A : Core ℂ) (m : ℕ) (p : Fin 2 × Fin 2) (b : Word m) :
    traceWord 2 2 (2 + m) A (join p.swap (b ∘ Fin.rev)) =
      traceWord 2 2 (2 + m) A (join p b) := by
  let l := List.ofFn b
  have hp : List.ofFn (join p b) = p.1 :: p.2 :: l := by
    simp [join, List.ofFn_fin_append, List.ofFn_succ, l]
  have hq : List.ofFn (join p.swap (b ∘ Fin.rev)) = p.2 :: p.1 :: l.reverse := by
    simp [join, List.ofFn_fin_append, List.ofFn_succ, l, ofFn_rev]
  simp only [traceWord_eq_wordProduct, hp, hq]
  rw [← trace_word_reverse A (p.1 :: p.2 :: l)]
  simp only [wordProduct, List.reverse_cons, List.map_cons, List.prod_cons,
    List.map_append, List.prod_append, List.map_nil, List.prod_nil, Matrix.mul_one]
  rw [← Matrix.mul_assoc (A p.2), Matrix.trace_mul_comm (A p.2 * A p.1)]
  simp [Matrix.mul_assoc]

/-- Every literal adjacent marginal of a binary bond-two periodic trace state
has exchange symmetry, at all lengths with at least two sites. -/
theorem normalizedMarginal_exchangeSymmetric (A : Core ℂ) (m : ℕ) :
    ExchangeSymmetric (normalizedMarginal m A) := by
  intro p q
  unfold normalizedMarginal
  simp only [Matrix.smul_apply]
  congr 1
  unfold pairGram
  let e : Word m ≃ Word m := (Fin.revPerm (n := m)).arrowCongr (Equiv.refl (Fin 2))
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  change traceWord 2 2 (2 + m) A (join p.swap (b ∘ Fin.rev)) *
      star (traceWord 2 2 (2 + m) A (join q.swap (b ∘ Fin.rev))) = _
  rw [joined_trace_swap, joined_trace_swap]
  rfl

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSExchangeSymmetry
