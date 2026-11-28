/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed SL(2,23) row action preserves the P48p Paley graph and its two Hamming weights. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph
import OmegaBuild.Commands

/-!
# The signed action on the P48p Paley graph

The determinant of two projective rows is unchanged by right multiplication
by an element of SL(2,23). Normalizing the two rows contributes their two
quadratic-character signs to the conference coefficient.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyAction

open scoped BigOperators Matrix
open P48pFrameProjectiveAction
  (Direction F23 SL23 normalizedRow transformedRow projectiveStep projectiveStep_factor
    projectiveStep_sign)
open P48pTernaryPaleyGraph (F3 paleyC)

open private projectiveStep_one projectiveStep_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pFrameProjectiveAction
open private directionEquiv paleyDirection normalizedRows from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

private def projectiveDirectionPerm (g : SL23) : Equiv.Perm Direction where
  toFun d := (projectiveStep g d).1
  invFun d := (projectiveStep g⁻¹ d).1
  left_inv d := by
    have h := congrArg Prod.fst (projectiveStep_mul g g⁻¹ d)
    simpa only [mul_inv_cancel, projectiveStep_one] using h.symm
  right_inv d := by
    have h := congrArg Prod.fst (projectiveStep_mul g⁻¹ g d)
    simpa only [inv_mul_cancel, projectiveStep_one] using h.symm

/-- The action on the directions in the index order of the actual Paley matrix. -/
def paleyPerm (g : SL23) : Equiv.Perm (Fin 24) :=
  directionEquiv.trans ((projectiveDirectionPerm g).trans directionEquiv.symm)

private theorem paleyDirection_perm (g : SL23) (d : Fin 24) :
    paleyDirection (paleyPerm g d) = (projectiveStep g (paleyDirection d)).1 := by
  change directionEquiv (directionEquiv.symm (projectiveStep g (paleyDirection d)).1) = _
  exact directionEquiv.apply_symm_apply _

private theorem paleyPerm_one (d : Fin 24) : paleyPerm 1 d = d := by
  apply directionEquiv.injective
  change paleyDirection (paleyPerm 1 d) = paleyDirection d
  simp only [paleyDirection_perm, projectiveStep_one]

private theorem paleyPerm_mul (g h : SL23) (d : Fin 24) :
    paleyPerm (g * h) d = paleyPerm h (paleyPerm g d) := by
  apply directionEquiv.injective
  change paleyDirection (paleyPerm (g * h) d) =
    paleyDirection (paleyPerm h (paleyPerm g d))
  simp only [paleyDirection_perm, projectiveStep_mul]

/-- The quadratic-character sign attached to the source direction of the move. -/
def paleySign (g : SL23) (d : Fin 24) : F3 :=
  (quadraticChar F23 (projectiveStep g (paleyDirection d)).2 : F3)

private theorem paleySign_sq (g : SL23) (d : Fin 24) :
    paleySign g d * paleySign g d = 1 := by
  rcases projectiveStep_sign g (paleyDirection d) with h | h <;> simp [paleySign, h]

private theorem paleySign_ne_zero (g : SL23) (d : Fin 24) : paleySign g d ≠ 0 := by
  intro h
  have hsq := paleySign_sq g d
  rw [h, zero_mul] at hsq
  exact zero_ne_one hsq

private theorem paleySign_one (d : Fin 24) : paleySign 1 d = 1 := by
  simp only [paleySign, projectiveStep_one, map_one, Int.cast_one]

private theorem paleySign_mul (g h : SL23) (d : Fin 24) :
    paleySign (g * h) d = paleySign g d * paleySign h (paleyPerm g d) := by
  simp only [paleySign, paleyDirection_perm, projectiveStep_mul, map_mul, Int.cast_mul]

private theorem normalizedRows_det (g : SL23) (d e : Fin 24) :
    (normalizedRows d e).det =
      ((projectiveStep g (paleyDirection d)).2 * (projectiveStep g (paleyDirection e)).2) *
        (normalizedRows (paleyPerm g d) (paleyPerm g e)).det := by
  let scales : Fin 2 → F23 :=
    ![(projectiveStep g (paleyDirection d)).2, (projectiveStep g (paleyDirection e)).2]
  have factor (k : Fin 24) (j : Fin 2) :
      transformedRow g (paleyDirection k) j =
        (projectiveStep g (paleyDirection k)).2 *
          normalizedRow (paleyDirection (paleyPerm g k)) j := by
    rw [paleyDirection_perm]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (projectiveStep_factor g (paleyDirection k)) j
  have rows :
      normalizedRows d e * (g : Matrix (Fin 2) (Fin 2) F23) =
        Matrix.diagonal scales * normalizedRows (paleyPerm g d) (paleyPerm g e) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    fin_cases i
    · exact factor d j
    · exact factor e j
  simpa only [Matrix.det_mul, g.det_coe, mul_one, Matrix.det_diagonal, Fin.prod_univ_two,
    scales, Matrix.cons_val_zero, Matrix.cons_val_one] using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) F23 => M.det) rows

/-- Under the projective permutation, a Paley entry picks up the two
quadratic-character signs, including when the determinant vanishes. -/
theorem paleyC_covariance (g : SL23) (d e : Fin 24) :
    paleyC d e =
      (paleySign g d * paleySign g e) * paleyC (paleyPerm g d) (paleyPerm g e) := by
  simp only [paleyC, normalizedRows_det g d e, map_mul, Int.cast_mul, paleySign]

/-- Move each row entry to its projective destination and multiply by its sign. -/
def paleyRowAction (g : SL23) (a : Fin 24 → F3) : Fin 24 → F3 :=
  fun j => paleySign g ((paleyPerm g).symm j) * a ((paleyPerm g).symm j)

theorem paleyRowAction_apply_perm (g : SL23) (a : Fin 24 → F3) (d : Fin 24) :
    paleyRowAction g a (paleyPerm g d) = paleySign g d * a d := by
  simp only [paleyRowAction, Equiv.symm_apply_apply]

theorem paleyRowAction_ne_zero_iff (g : SL23) (a : Fin 24 → F3) (d : Fin 24) :
    paleyRowAction g a (paleyPerm g d) ≠ 0 ↔ a d ≠ 0 := by
  rw [paleyRowAction_apply_perm, mul_ne_zero_iff_left (paleySign_ne_zero g d)]

theorem paleyRowAction_one (a : Fin 24 → F3) : paleyRowAction 1 a = a := by
  funext j
  obtain ⟨d, rfl⟩ := (paleyPerm 1).surjective j
  rw [paleyRowAction_apply_perm, paleyPerm_one, paleySign_one, one_mul]

/-- This is a right action, so the move by `g` is applied before the move by `h`. -/
theorem paleyRowAction_mul (g h : SL23) (a : Fin 24 → F3) :
    paleyRowAction (g * h) a = paleyRowAction h (paleyRowAction g a) := by
  funext j
  obtain ⟨d, rfl⟩ := (paleyPerm (g * h)).surjective j
  rw [paleyRowAction_apply_perm (g * h) a d, paleyPerm_mul,
    paleyRowAction_apply_perm h, paleyRowAction_apply_perm g, paleySign_mul]
  ring

/-- The signed row action commutes with the actual Paley graph map. -/
theorem paleyRowAction_vecMul (g : SL23) (a : Fin 24 → F3) :
    paleyRowAction g (a ᵥ* paleyC) = paleyRowAction g a ᵥ* paleyC := by
  funext j
  obtain ⟨e, rfl⟩ := (paleyPerm g).surjective j
  rw [paleyRowAction_apply_perm g (a ᵥ* paleyC) e,
    Matrix.vecMul_apply_eq_sum a paleyC e,
    Matrix.vecMul_apply_eq_sum (paleyRowAction g a) paleyC (paleyPerm g e),
    Finset.mul_sum]
  calc
    _ = ∑ d, paleyRowAction g a (paleyPerm g d) *
        paleyC (paleyPerm g d) (paleyPerm g e) := by
      apply Finset.sum_congr rfl
      intro d _
      have hentry : paleySign g e * paleyC d e =
          paleySign g d * paleyC (paleyPerm g d) (paleyPerm g e) := by
        rw [paleyC_covariance g d e]
        calc
          _ = (paleySign g e * paleySign g e) *
                (paleySign g d * paleyC (paleyPerm g d) (paleyPerm g e)) := by ring
          _ = _ := by rw [paleySign_sq, one_mul]
      rw [paleyRowAction_apply_perm]
      calc
        _ = a d * (paleySign g e * paleyC d e) := by ring
        _ = _ := by rw [hentry]; ring
    _ = _ := Equiv.sum_comp (paleyPerm g)
      (fun d => paleyRowAction g a d * paleyC d (paleyPerm g e))

/-- Applying the same signed permutation to the two halves preserves the graph relation. -/
theorem paleyRowAction_graph_iff (g : SL23) (a b : Fin 24 → F3) :
    paleyRowAction g b = paleyRowAction g a ᵥ* paleyC ↔ b = a ᵥ* paleyC := by
  rw [← paleyRowAction_vecMul]
  constructor
  · intro h
    have hi := congrArg (paleyRowAction g⁻¹) h
    simpa only [← paleyRowAction_mul, mul_inv_cancel, paleyRowAction_one] using hi
  · exact congrArg (paleyRowAction g)

/-- The row action preserves the number of nonzero coordinates. -/
theorem hammingNorm_paleyRowAction (g : SL23) (a : Fin 24 → F3) :
    hammingNorm (paleyRowAction g a) = hammingNorm a := by
  simp only [hammingNorm, Finset.card_filter]
  calc
    _ = ∑ d, if paleyRowAction g a (paleyPerm g d) ≠ 0 then (1 : ℕ) else 0 :=
      (Equiv.sum_comp (paleyPerm g)
        (fun d => if paleyRowAction g a d ≠ 0 then (1 : ℕ) else 0)).symm
    _ = _ := by simp only [paleyRowAction_ne_zero_iff]

/-- A move used to anchor an input support also preserves its total graph weight. -/
theorem paleyRowAction_graph_weight (g : SL23) (a : Fin 24 → F3) :
    hammingNorm (paleyRowAction g a) + hammingNorm (paleyRowAction g a ᵥ* paleyC) =
      hammingNorm a + hammingNorm (a ᵥ* paleyC) := by
  rw [← paleyRowAction_vecMul, hammingNorm_paleyRowAction, hammingNorm_paleyRowAction]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyAction
