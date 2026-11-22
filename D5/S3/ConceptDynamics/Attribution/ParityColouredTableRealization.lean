/- GID: D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityColouredTableRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realize exact coordinate fixation from coloured parity cell multiplicities. -/

import D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Mathlib.Algebra.BigOperators.Fin

/-! Minimal coordinate fixation for coloured parity multiplicity tables. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization

open Finset MulAction
open CoordinateFlagCoupling CoordinateColourOrbit CoordinateFibreCounts
open ParitySeedBudget ParitySeedOptimization ParityFourSparseCounts

noncomputable section

private def evenPoint (n : ℕ) : (ParityClass (n + 2) 0 × Fin 2) ≃ slice (n + 2) 0 :=
  sliceEquiv (n + 2) 0

private def oddPoint (n : ℕ) : (ParityClass (n + 2) 1 × Fin 2) ≃ slice (n + 2) 1 :=
  sliceEquiv (n + 2) 1

private theorem evenPoint_profile {n : ℕ} (x : ParityClass (n + 2) 0 × Fin 2)
    (i : Fin (n + 2)) : ((evenPoint n) x).val.profile i = true ↔ x.1.val i = 1 := by
  change booleanProfile x.1.val i = true ↔ _
  simp [booleanProfile]

private theorem oddPoint_profile {n : ℕ} (x : ParityClass (n + 2) 1 × Fin 2)
    (i : Fin (n + 2)) : ((oddPoint n) x).val.profile i = true ↔ x.1.val i = 1 := by
  change booleanProfile x.1.val i = true ↔ _
  simp [booleanProfile]

/-- Realize the least per-fibre coordinate counts on one equivariant seed space.
A full even profile retains its left colour. Every other profile uses the
same multiplicity at both left colours. -/
theorem realize_coloured_table {n k : ℕ}
    (b : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → Fin 2 → ℕ)
    (rows : ∀ p c, ∑ q, b p q c = k)
    (cols : ∀ q, ∑ p, (b p q 0 + b p q 1) = 2 * k)
    (ordinary : ∀ p q, p.val ≠ 1 → b p q 0 = b p q 1) :
    RealizableSeedCounts n k fun i =>
      2 * (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, ∑ c : Fin 2,
        if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0) := by
  classical
  let w (a : Pair n) : ℕ :=
    b ((evenPoint n).symm a.1).1 ((oddPoint n).symm a.2).1 ((evenPoint n).symm a.1).2
  have eval (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) (c d : Fin 2) :
      w (evenPoint n (p,c), oddPoint n (q,d)) = b p q c := by
    simp [w]
  have left (x : slice (n + 2) 0) : ∑ y : slice (n + 2) 1, w (x,y) = 2*k := by
    obtain ⟨⟨p,c⟩, rfl⟩ := (evenPoint n).surjective x
    rw [← (oddPoint n).sum_comp (fun y => w (evenPoint n (p,c), y)), Fintype.sum_prod_type]
    simp_rw [eval, Fin.sum_univ_two, ← two_mul, ← mul_sum, rows]
  have right (y : slice (n + 2) 1) : ∑ x : slice (n + 2) 0, w (x,y) = 2*k := by
    obtain ⟨⟨q,d⟩, rfl⟩ := (oddPoint n).surjective y
    rw [← (evenPoint n).sum_comp (fun x => w (x, oddPoint n (q,d))), Fintype.sum_prod_type]
    simp_rw [eval, Fin.sum_univ_two, cols]
  have invariant (g : Acting (Fin (n + 2))) (a : Pair n) : w (g • a) = w a := by
    obtain ⟨⟨p,c⟩, hp⟩ := (evenPoint n).surjective a.1
    obtain ⟨⟨q,d⟩, hq⟩ := (oddPoint n).surjective a.2
    obtain ⟨⟨p',c'⟩, hp'⟩ := (evenPoint n).surjective (g • a).1
    obtain ⟨⟨q',d'⟩, hq'⟩ := (oddPoint n).surjective (g • a).2
    rw [← Prod.eta (g • a), ← Prod.eta a, ← hp', ← hq', ← hp, ← hq, eval, eval]
    have sameEven : p' = p := by
      apply Subtype.ext
      have profile : booleanProfile p'.val = booleanProfile p.val :=
        (congrArg (fun x => x.val.profile) hp').trans (congrArg (fun x => x.val.profile) hp).symm
      simpa using congrArg bitProfile profile
    have sameOdd : q' = q := by
      apply Subtype.ext
      have profile : booleanProfile q'.val = booleanProfile q.val :=
        (congrArg (fun y => y.val.profile) hq').trans (congrArg (fun y => y.val.profile) hq).symm
      simpa using congrArg bitProfile profile
    subst p' q'
    by_cases full : p.val = 1
    · have all (i : Fin (n + 2)) : a.1.val.profile i = true := by
        rw [← hp]
        change booleanProfile p.val i = true
        simp [full, booleanProfile]
      have fixing : (g • a).1 = a.1 := by
        apply Subtype.ext
        change Output.mk a.1.val.profile (shift a.1.val.profile g.toAdd + a.1.val.colour) = a.1.val
        rw [all_true_shift _ all, zero_add]
      have sameColour : c' = c := by
        have both := (evenPoint n).injective (hp'.trans (fixing.trans hp.symm))
        exact congrArg Prod.snd both
      rw [sameColour]
    · have equalAll (e : Fin 2) : b p q e = b p q 0 := by
        fin_cases e
        · rfl
        · exact (ordinary p q full).symm
      rw [equalAll, equalAll c]
  apply weighted_realization w invariant left right
  intro i
  calc
    _ = ∑ a : Pair n, if a.1.val.profile i && a.2.val.profile i then w a % 2 else 0 := by
      apply sum_congr rfl
      intro a _
      split <;> simp_all
    _ = _ := by
      rw [Fintype.sum_prod_type, ← (evenPoint n).sum_comp (fun x => ∑ y,
        if x.val.profile i && y.val.profile i then w (x,y) % 2 else 0)]
      have rightSum (x : slice (n + 2) 0) :
          (∑ y : slice (n + 2) 1, if x.val.profile i && y.val.profile i then w (x,y) % 2 else 0) =
          ∑ y : ParityClass (n + 2) 1 × Fin 2,
            if x.val.profile i && ((oddPoint n) y).val.profile i then w (x, (oddPoint n) y) % 2 else 0 :=
        ((oddPoint n).sum_comp (fun y =>
          if x.val.profile i && y.val.profile i then w (x,y) % 2 else 0)).symm
      simp_rw [rightSum, Fintype.sum_prod_type, Bool.and_eq_true, evenPoint_profile,
        oddPoint_profile, eval]
      simp_rw [sum_comm (s := (univ : Finset (Fin 2))) (t := (univ : Finset (ParityClass (n + 2) 1))),
        Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_sum]

end
end D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
