/- GID: D5/S3/Quantum/Fermionic/JointSignProjectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/JointSignProjectors
   mirror-E: none(waiver:general-joint-spectral-projector)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Hermitian]
   utility: none
   digest: Independent sign reversals give a joint minus projector with exact trace. -/

/-
joint_sign_projection:
  proof_shape: content
  escape_witness: joint_sign_projection (form 2): induction on finite subsets
    constructs a joint spectral projector; each independent sign reversal cancels
    the inserted mixed trace, yielding the exact trace divided by a power of two.
admission_basis: escape-witness
Same-delivery inlined content: local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  none; remaining prerequisites are pinned Mathlib declarations.
computational_content.kind: none; the argument concerns arbitrary finite families
  and matrix dimensions, rather than a bounded sign-pattern enumeration.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

open Matrix
open scoped BigOperators

noncomputable section
namespace D5.S3.Quantum.Fermionic.JointSignProjectors

/-- Commuting involutions with independent sign reversals have the full joint minus sector. -/
theorem joint_sign_projection {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
    (B U : I → Matrix Ω Ω ℂ)
    (hB : ∀ i, (B i).IsHermitian ∧ B i * B i = 1)
    (hBB : ∀ i j, Commute (B i) (B j))
    (hU : ∀ i, U i * U i = 1)
    (hflip : ∀ i, U i * B i = -(B i * U i))
    (hfix : ∀ i j, i ≠ j → Commute (U i) (B j)) :
    ∃ P : Matrix Ω Ω ℂ, IsStarProjection P ∧
      Matrix.trace P = (Fintype.card Ω : ℂ) / 2 ^ Fintype.card I ∧
      (∀ i, B i * P = -P) ∧
      (∀ Q : Matrix Ω Ω ℂ, (∀ i, Commute Q (B i)) → Commute Q P) := by
  classical
  let e (i : I) := (1/2 : ℂ) • (1 - B i)
  have hproj (i : I) : IsStarProjection (e i) := by
    constructor
    · change e i * e i = e i
      simp only [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hh : (1 - B i) * (1 - B i) = (2 : ℂ) • (1 - B i) := by
        rw [two_smul]
        noncomm_ring [(hB i).2]
      rw [hh, smul_smul]
      norm_num
    · change (e i)ᴴ = e i
      simp [e, (hB i).1.eq]
  have hecomm (i j : I) : Commute (e i) (e j) := by
    rw [commute_iff_eq]
    simp only [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    noncomm_ring [(hBB i j).eq]
  let P (s : Finset I) := s.noncommProd e (fun i _ j _ _ => hecomm i j)
  have hpempty : P ∅ = 1 := rfl
  have hpinsert (s : Finset I) (i : I) (hi : i ∉ s) :
      P (insert i s) = e i * P s := by
    exact Finset.noncommProd_insert_of_notMem s i e _ hi
  have hcomm (s : Finset I) (Q : Matrix Ω Ω ℂ)
      (hQ : ∀ i ∈ s, Commute Q (B i)) : Commute Q (P s) := by
    apply Finset.noncommProd_commute
    intro i hi
    rw [commute_iff_eq]
    simp only [e, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    noncomm_ring [(hQ i hi).eq]
  have hall (s : Finset I) : IsStarProjection (P s) ∧
      Matrix.trace (P s) = (Fintype.card Ω : ℂ) / 2 ^ s.card ∧
      (∀ i ∈ s, B i * P s = -P s) := by
    induction s using Finset.induction_on with
    | empty =>
      rw [hpempty]
      exact ⟨IsStarProjection.one _, by simp, fun i hi => False.elim (Finset.notMem_empty i hi)⟩
    | @insert i s hi ih =>
      rw [hpinsert s i hi]
      have hc : Commute (e i) (P s) := by
        apply Finset.noncommProd_commute
        exact fun j _ => hecomm i j
      have hUP : Commute (U i) (P s) := hcomm s (U i) (fun j hj =>
        hfix i j (fun hij => hi (hij ▸ hj)))
      have hz : Matrix.trace (B i * P s) = 0 := by
        have hinvar : Matrix.trace (U i * (B i * P s) * U i) =
            Matrix.trace (B i * P s) := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU i, Matrix.one_mul]
        have hneg : U i * (B i * P s) * U i = -(B i * P s) := by
          rw [← Matrix.mul_assoc, hflip i, Matrix.neg_mul,
            Matrix.mul_assoc, hUP.eq, Matrix.neg_mul]
          simp only [Matrix.mul_assoc, hU i, Matrix.mul_one]
        rw [hneg, Matrix.trace_neg] at hinvar
        linear_combination -(1/2 : ℂ) * hinvar
      refine ⟨(hproj i).mul ih.1 hc, ?_, ?_⟩
      · dsimp only [e]
        rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_smul,
          Matrix.trace_sub, hz, sub_zero, ih.2.1, Finset.card_insert_of_notMem hi, pow_succ]
        simp only [smul_eq_mul]
        field_simp
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          have he : B i * e i = -e i := by
            simp only [e, Matrix.mul_smul]
            have hh : B i * (1 - B i) = -(1 - B i) := by
              noncomm_ring [(hB i).2]
            rw [hh, smul_neg]
          rw [← Matrix.mul_assoc, he, Matrix.neg_mul]
        · have hjc : Commute (B j) (e i) := by
            rw [commute_iff_eq]
            simp only [e, Matrix.mul_smul, Matrix.smul_mul]
            congr 1
            noncomm_ring [(hBB j i).eq]
          rw [← Matrix.mul_assoc, hjc.eq, Matrix.mul_assoc, ih.2.2 j hj, Matrix.mul_neg]
  refine ⟨P Finset.univ, (hall _).1, ?_, fun i => (hall _).2.2 i (Finset.mem_univ i), ?_⟩
  · simpa using (hall Finset.univ).2.1
  · intro Q hQ
    exact hcomm Finset.univ Q (fun i _ => hQ i)

end D5.S3.Quantum.Fermionic.JointSignProjectors
