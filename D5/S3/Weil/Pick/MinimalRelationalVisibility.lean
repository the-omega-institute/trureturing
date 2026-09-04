/- GID: D5/S3/Weil/Pick/MinimalRelationalVisibility
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/MinimalRelationalVisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two legal Pick-kernel diagonal tests can combine into a non-Gram relation matrix. -/

import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Minimal relational visibility

At a unit-disk point where a Schur candidate takes the value one, the standard
Pick kernel passes both one-point scalar tests but its joint two-point matrix
has determinant minus one. The negative determinant also rules out a positive
semidefinite or conjugate-transpose Gram factorization.
-/

/- Library-search and duplication audit trail (2026-09-03):
   * D5 searches for the standard disk Pick kernel, two-point negative
     certificate, pointwise diagonal legality, and Gram obstruction found no
     whole-statement owner. The adjacent Pick family supplies general kernel
     and positive-semidefinite infrastructure but not this source matrix.
   * A body-shape search for `(1 - s z * star (s w)) / (1 - z * star w)`
     found no existing D5 or pinned-Mathlib definition, so the source kernel
     is constructed locally in the public statement rather than forked as a
     new global definition.
   * Pinned Mathlib has no exact theorem named for minimal relational
     visibility or this Pick matrix. It supplies `Matrix.PosSemidef.det_nonneg`
     and `Matrix.posSemidef_conjTranspose_mul_self`, both applied below.
   * GitHub Lean-code searches for `Pick kernel` with `PosSemidef`, and for
     `Pick` with `det_fin_two`, returned no exact theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace D5.S3.Weil.Pick.MinimalRelationalVisibility

/-- A Schur candidate with values zero at the origin and one at an interior
point has legal one-point Pick tests, while its first joint relation matrix is
the determinant-minus-one matrix and admits no Gram factorization. -/
theorem minimal_relational_visibility
    (schur : Complex -> Complex) (a : Complex.UnitDisc)
    (hzero : schur 0 = 0) (hcontact : schur a = 1) :
    let pickKernel : Complex -> Complex -> Complex := fun z w =>
      (1 - schur z * conj (schur w)) / (1 - z * conj w)
    let points : Fin 2 -> Complex := ![0, a]
    let relation : Matrix (Fin 2) (Fin 2) Complex := fun i j =>
      pickKernel (points i) (points j)
    relation = !![(1 : Complex), 1; 1, 0] /\
      (forall i : Fin 2, 0 <= relation i i) /\
      Matrix.det relation = -1 /\
      Not relation.PosSemidef /\
      ¬ ∃ factor : Matrix (Fin 2) (Fin 2) Complex,
        relation = factor.conjTranspose * factor := by
  dsimp only
  have hrelation :
      (fun i j : Fin 2 =>
        (1 - schur (![0, (a : Complex)] i) *
          conj (schur (![0, (a : Complex)] j))) /
          (1 - (![0, (a : Complex)] i) *
            conj (![0, (a : Complex)] j))) =
        !![(1 : Complex), 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hzero, hcontact]
  have hsingle : forall i : Fin 2,
      0 <= (fun i j : Fin 2 =>
          (1 - schur (![0, (a : Complex)] i) *
            conj (schur (![0, (a : Complex)] j))) /
            (1 - (![0, (a : Complex)] i) *
              conj (![0, (a : Complex)] j))) i i := by
    intro i
    fin_cases i <;> simp [hzero, hcontact]
  have hdet : Matrix.det
      (fun i j : Fin 2 =>
        (1 - schur (![0, (a : Complex)] i) *
          conj (schur (![0, (a : Complex)] j))) /
          (1 - (![0, (a : Complex)] i) *
            conj (![0, (a : Complex)] j))) = -1 := by
    rw [hrelation]
    norm_num [Matrix.det_fin_two]
  have hnot : Not (Matrix.PosSemidef
      (fun i j : Fin 2 =>
        (1 - schur (![0, (a : Complex)] i) *
          conj (schur (![0, (a : Complex)] j))) /
          (1 - (![0, (a : Complex)] i) *
            conj (![0, (a : Complex)] j)))) := by
    intro hpositive
    have hnonnegative := hpositive.det_nonneg
    rw [hdet] at hnonnegative
    norm_num at hnonnegative
  refine ⟨hrelation, hsingle, hdet, hnot, ?_⟩
  rintro ⟨factor, hgram⟩
  apply hnot
  rw [hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self factor

#print axioms minimal_relational_visibility

end D5.S3.Weil.Pick.MinimalRelationalVisibility
