/- GID: D5/S3/Observer/Monodromy/TraceSymplecticCertificate
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TraceSymplecticCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Anchored traces construct the invariant form and determine every alternating invariant form. -/

import D5.S3.Observer.Monodromy.TransvectionTraceReconstruction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# An observable symplectic certificate

This module continues the actual reconstruction from TransvectionTraceReconstruction.
The scalar data construct both the operators and a bilinear form. Preservation,
readback, uniqueness up to an explicit scalar, and the determinant obstruction
are proved from matrix entries. No symplectic group or invariant form is assumed
in the construction. The classical invariant-form criterion is discussed in
Eberhard, arXiv:2308.07086v3, Proposition 3.4; the source here supplies a rational
star chart, including degenerate data, over an arbitrary field.

A rank-eight geometric lift and Zariski density remain external obligations for
the order-two expectation of Kraemer--Litt--Maculan, arXiv:2604.20970, Section 1.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TraceSymplecticCertificate

open D5.S3.Observer.Monodromy.TransvectionTraceReconstruction

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def symplecticWeight (a : I) (p : I → K) (i : I) : K :=
  if i = a then 1 else -(p i)⁻¹

/-- A form constructed solely from the observed pair and triangle traces. -/
def recoveredForm (a : I) (p : I → K) (t : I → I → K) : Matrix I I K :=
  fun i j => symplecticWeight a p i * recoveredGram a p t i j

private theorem weight_ne_zero (a : I) (p : I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0) (i : I) : symplecticWeight a p i ≠ 0 := by
  by_cases hi : i = a
  · simp [symplecticWeight, hi]
  · simp [symplecticWeight, hi, hp i hi]

private theorem gram_diagonal (a : I) (p : I → K) (t : I → I → K)
    (ht : ∀ i, t i i = 0) (i : I) : recoveredGram a p t i i = 0 := by
  by_cases hi : i = a <;> simp [recoveredGram, hi, ht]

/-- The data have the asserted pair and triangle readback on the observable chart. -/
theorem reconstructed_readback (a : I) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0) :
    (∀ j, j ≠ a → pairRead (recoveredGram a p t) a j = p j) ∧
    (∀ i j, i ≠ a → j ≠ a →
      tripleRead (recoveredGram a p t) a i j = t i j) := by
  constructor
  · intro j hj
    simp [pairRead, trace_pair, recoveredGram, hj]
  · intro i j hi hj
    simp [tripleRead, trace_triple, recoveredGram, hi, hj, hp j hj]

/-- Alternating oriented triangles produce an alternating form. No division by two. -/
theorem recoveredForm_alternating (a : I) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0)
    (ht : ∀ i, t i i = 0) (hskew : ∀ i j, t i j = -t j i) :
    (∀ i, recoveredForm a p t i i = 0) ∧
      (∀ i j, recoveredForm a p t i j = -recoveredForm a p t j i) := by
  constructor
  · intro i
    simp [recoveredForm, gram_diagonal a p t ht i]
  · intro i j
    by_cases hi : i = a
    · subst i
      by_cases hj : j = a
      · subst j
        simp [recoveredForm, symplecticWeight, recoveredGram]
      · simp [recoveredForm, symplecticWeight, recoveredGram, hj, hp j hj]
    · by_cases hj : j = a
      · subst j
        simp [recoveredForm, symplecticWeight, recoveredGram, hi, hp i hi]
      · simp only [recoveredForm, symplecticWeight, recoveredGram, hi, hj, if_false]
        rw [hskew i j]
        field_simp [hp i hi, hp j hj] <;> ring

private theorem transpose_increment_mul_entry (H B : Matrix I I K) (i r c : I) :
    ((increment H i).transpose * B) r c = H i r * B i c := by
  classical
  simp [Matrix.mul_apply, Matrix.transpose_apply, increment]

private theorem mul_increment_entry (H B : Matrix I I K) (i r c : I) :
    (B * increment H i) r c = B r i * H i c := by
  classical
  simp [Matrix.mul_apply, increment]

private theorem sandwich_entry (H B : Matrix I I K) (i r c : I) :
    ((increment H i).transpose * B * increment H i) r c =
      H i r * B i i * H i c := by
  classical
  simp [Matrix.mul_apply, transpose_increment_mul_entry, increment, mul_assoc]

private theorem isometry_entry (H B : Matrix I I K) (i r c : I) :
    ((1 + increment H i).transpose * B * (1 + increment H i)) r c =
      B r c + H i r * B i c + B r i * H i c + H i r * B i i * H i c := by
  have hm : (1 + increment H i).transpose * B * (1 + increment H i) =
      B + (increment H i).transpose * B + B * increment H i +
        (increment H i).transpose * B * increment H i := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    noncomm_ring
  rw [hm]
  simp only [Matrix.add_apply, transpose_increment_mul_entry, mul_increment_entry,
    sandwich_entry]

/-- The generators preserve the form constructed from their scalar data. -/
theorem reconstructed_generators_preserve_form
    (a : I) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0)
    (ht : ∀ i, t i i = 0) (hskew : ∀ i j, t i j = -t j i) (i : I) :
    (1 + increment (recoveredGram a p t) i).transpose * recoveredForm a p t *
        (1 + increment (recoveredGram a p t) i) = recoveredForm a p t := by
  ext r c
  rw [isometry_entry]
  have ha := recoveredForm_alternating a p t hp ht hskew
  rw [ha.1 i, ha.2 r i]
  simp only [recoveredForm]
  ring

private theorem isometry_linear_constraint
    (H B : Matrix I I K) (hzero : ∀ i, B i i = 0) (i : I)
    (hpres : (1 + increment H i).transpose * B * (1 + increment H i) = B)
    (r c : I) : H i r * B i c + B r i * H i c = 0 := by
  have he := congrArg (fun M : Matrix I I K => M r c) hpres
  rw [isometry_entry, hzero i] at he
  linear_combination he

/-- Every alternating form preserved by the reconstructed tuple is an explicit
scalar multiple of the displayed form. No irreducibility hypothesis is needed. -/
theorem invariant_alternating_form_unique
    (a b : I) (hb : b ≠ a) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0)
    (B : Matrix I I K) (hzero : ∀ i, B i i = 0)
    (hskew : ∀ i j, B i j = -B j i)
    (hpres : ∀ i, (1 + increment (recoveredGram a p t) i).transpose * B *
      (1 + increment (recoveredGram a p t) i) = B) :
    B = (B a b) • recoveredForm a p t := by
  have rowa : ∀ j, j ≠ a → B a j = B a b := by
    intro j hj
    have he := isometry_linear_constraint (recoveredGram a p t) B hzero a
      (hpres a) b j
    simp only [recoveredGram, if_pos rfl, if_neg hb, if_neg hj, one_mul, mul_one] at he
    rw [hskew b a] at he
    linear_combination he
  ext i j
  by_cases hi : i = a
  · subst i
    by_cases hj : j = a
    · subst j
      simp [recoveredForm, symplecticWeight, recoveredGram, hzero]
    · simp [recoveredForm, symplecticWeight, recoveredGram, hj, rowa j hj]
  · have he := isometry_linear_constraint (recoveredGram a p t) B hzero i
      (hpres i) a j
    have hia : recoveredGram a p t i a = p i := by simp [recoveredGram, hi]
    rw [hia, rowa i hi] at he
    change B i j = B a b * (symplecticWeight a p i * recoveredGram a p t i j)
    simp only [symplecticWeight, hi, if_false]
    have heq : B i j * p i = -(B a b * recoveredGram a p t i j) := by
      linear_combination he
    calc
      B i j = -(B a b * recoveredGram a p t i j) / p i :=
        (eq_div_iff (hp i hi)).mpr heq
      _ = B a b * (-(p i)⁻¹ * recoveredGram a p t i j) := by
        rw [div_eq_mul_inv]
        ring

private theorem form_eq_diagonal_mul (a : I) (p : I → K) (t : I → I → K) :
    recoveredForm a p t = Matrix.diagonal (symplecticWeight a p) *
      recoveredGram a p t := by
  ext i j
  simp [recoveredForm, Matrix.mul_apply, Matrix.diagonal]

/-- Exact nondegeneracy test: the form has no additional hidden rank condition. -/
theorem form_nondegenerate_iff (a : I) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0) :
    Matrix.det (recoveredForm a p t) ≠ 0 ↔ Matrix.det (recoveredGram a p t) ≠ 0 := by
  have hw : (∏ i, symplecticWeight a p i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact weight_ne_zero a p hp i
  rw [form_eq_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal]
  simp [hw]

#print axioms reconstructed_generators_preserve_form
#print axioms invariant_alternating_form_unique
#print axioms form_nondegenerate_iff

end D5.S3.Observer.Monodromy.TraceSymplecticCertificate
