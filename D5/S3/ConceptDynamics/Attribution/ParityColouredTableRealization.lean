/- GID: D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityColouredTableRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realize exact coordinate fixation from coloured parity cell multiplicities. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Mathlib.Algebra.BigOperators.Fin

/-! Minimal coordinate fixation for coloured parity multiplicity tables. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization

open Finset MulAction
open CoordinateFlagCoupling CoordinateColourOrbit CoordinateFibreCounts
open ParitySeedBudget ParitySeedOptimization ParitySeedCountSpectrum

noncomputable section

open Classical in
private theorem card_eq_indicator {A : Type*} [Fintype A] (P : A → Prop) :
    Nat.card {a : A // P a} = ∑ a, if P a then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [sum_filter]

open Classical in
private theorem point_sums {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B × C) (x : B) :
    (∑ c : C, Nat.card {a : A // f a = (x,c)}) =
      ∑ a, if (f a).1 = x then 1 else 0 := by
  simp_rw [card_eq_indicator, Prod.ext_iff]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : (f a).1 = x <;> simp [h]

open Classical in
private theorem fixed_point_sums {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (P : A → Prop) :
    (∑ b : B, Nat.card {a : A // f a = b ∧ P a}) = ∑ a, if P a then 1 else 0 := by
  simp_rw [card_eq_indicator]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

open Classical in
private theorem realize_least_point_fixation {n k : ℕ} (w : Pair n → ℕ)
    (invariant : ∀ (g : Acting (Fin (n + 2))) a, w (g • a) = w a)
    (rows : ∀ x : slice (n + 2) 0, ∑ y : slice (n + 2) 1, w (x,y) = 2*k)
    (cols : ∀ y : slice (n + 2) 1, ∑ x : slice (n + 2) 0, w (x,y) = 2*k) :
    RealizableSeedCounts n k (fun i => ∑ a : Pair n, if generator i • a = a then w a % 2 else 0) := by
  classical
  let m : orbitRel.Quotient (Acting (Fin (n + 2))) (Pair n) → ℕ :=
    Quotient.lift w (fun a b hab => by
      obtain ⟨g, eq⟩ := hab
      rw [← eq, invariant])
  let z (o : orbitRel.Quotient (Acting (Fin (n + 2))) (Pair n)) (_ : Fin (n + 2)) :=
    m o % 2
  obtain ⟨S, _, _, f, equiv, fibres, fixed⟩ := (exact_orbit_fibre_counts m z).mpr
    (fun a i _ => ⟨Nat.mod_le _ _, Nat.mod_mod _ _⟩)
  have sizes (a : Pair n) : Nat.card {s : S // f s = a} = w a := fibres a
  have left (x : slice (n + 2) 0) :
      (∑ s, @ite ℕ ((f s).1 = x) (Classical.propDecidable _) 1 0) = 2*k := by
    rw [← point_sums f x]
    simp_rw [sizes, rows]
  have right (y : slice (n + 2) 1) :
      (∑ s, @ite ℕ ((f s).2 = y) (Classical.propDecidable _) 1 0) = 2*k := by
    rw [← cols y]
    simp_rw [← sizes, card_eq_indicator, Prod.ext_iff]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    by_cases h : (f s).2 = y <;> simp [h]
  have total : Fintype.card S = 2 ^ (n + 3) * k := by
    have counted := fixed_point_sums f (fun _ => True)
    have sizeEq : Fintype.card S = ∑ a : Pair n, w a := by
      simpa only [and_true, sizes, ite_eq_left (show True from trivial), sum_const,
        card_univ, nsmul_eq_mul, Nat.cast_id, mul_one] using counted.symm
    have card_slice : Fintype.card (slice (n + 2) 0) = 2 ^ (n + 2) := by
      rw [Fintype.card_congr (sliceEquiv (n + 2) 0).symm, Fintype.card_prod,
        ← Nat.card_eq_fintype_card, parityCard, ZMod.card]
      rfl
    rw [sizeEq, Fintype.sum_prod_type]
    simp_rw [rows, sum_const, nsmul_eq_mul, card_univ, Nat.cast_id, card_slice]
    simp only [pow_succ]
    ring
  refine ⟨S, inferInstance, inferInstance, f, total, equiv, ⟨2*k, left, right⟩, ?_⟩
  intro i
  unfold fixedSeedCount
  simp_rw [coordinate_fixed_iff_generator]
  rw [← fixed_point_sums f (fun s => generator i • s = s)]
  apply sum_congr rfl
  intro a _
  by_cases ha : generator i • a = a <;> simpa [ha, z, m] using fixed i a

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
  have realize := realize_least_point_fixation (n := n) (k := k) w invariant left right
  have sameCount (i : Fin (n + 2)) :
      (∑ a : Pair n, if generator i • a = a then w a % 2 else 0) =
        2 * (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, ∑ c : Fin 2,
          if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0) := by
    rw [Fintype.sum_prod_type,
      ← (evenPoint n).sum_comp (fun x => ∑ y, if generator i • (x,y) = (x,y) then w (x,y) % 2 else 0)]
    simp_rw [← (oddPoint n).sum_comp (fun y => if generator i • (_,y) = (_,y) then w (_,y) % 2 else 0),
      Fintype.sum_prod_type, ← coordinate_fixed_iff_generator, pair_fixed_coordinate,
      evenPoint_profile, oddPoint_profile, eval]
    simp_rw [sum_comm (s := (univ : Finset (Fin 2))) (t := (univ : Finset (ParityClass (n + 2) 1))),
      Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_sum]
  simpa only [sameCount] using realize

end
end D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
