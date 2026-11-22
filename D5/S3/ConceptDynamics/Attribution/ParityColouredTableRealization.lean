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
open ParitySeedBudget ParitySeedOptimization

noncomputable section

section
attribute [local instance 10000] Classical.propDecidable

/-- A uniform equivariant seed implementation with specified joint fibre sizes
and coordinate fixed-seed counts on the same action. -/
def RealizesFibreCounts (n k : ℕ) (w : Pair n → ℕ) (z : Fin (n + 2) → ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S)
    (f : S → Pair n), Fintype.card S = 2 ^ (n + 3) * k ∧
      (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) ∧
      (∀ i, fixedSeedCount (n := n) S i = z i) ∧
      ∀ a, Nat.card {s : S // f s = a} = w a

set_option maxHeartbeats 800000 in
-- The proof partitions and reindexes two coloured marginals and every fixed fibre.
/-- Realize invariant output weights and the least coordinate-fixed counts
without losing the size of any individual joint fibre. -/
theorem weighted_realization_with_fibres {n k : ℕ} {z : Fin (n + 2) → ℕ} (w : Pair n → ℕ)
    (inv : ∀ (g : Acting (Fin (n + 2))) t, w (g • t) = w t)
    (rows : ∀ x : slice (n + 2) 0, (∑ y, w (x, y)) = 2 * k)
    (cols : ∀ y : slice (n + 2) 1, (∑ x, w (x, y)) = 2 * k)
    (counts : ∀ i, (∑ t : Pair n,
      if t.1.val.profile i && t.2.val.profile i then w t % 2 else 0) = z i) :
    RealizesFibreCounts n k w z := by
  classical
  let m : orbitRel.Quotient (Acting (Fin (n + 2))) (Pair n) → ℕ :=
    Quotient.lift w (by intro a b h; obtain ⟨g, hg⟩ := h; exact (congrArg w hg).symm.trans (inv g b))
  have wlift (t : Pair n) : m (Quotient.mk'' t) = w t := rfl
  obtain ⟨S, _, _, f, equiv, size, fixed⟩ :=
    (exact_orbit_fibre_counts m (fun o _ => m o % 2)).mpr
      (fun _ _ _ => ⟨Nat.mod_le _ _, Nat.mod_mod _ _⟩)
  have countPartition (P : S → Prop) [DecidablePred P] :
      (∑ s, if P s then 1 else (0 : ℕ)) =
        ∑ t, Nat.card {s : S // f s = t ∧ P s} := by
    calc
      _ = #(univ.filter P) := by rw [← sum_filter, card_eq_sum_ones]
      _ = ∑ t : Pair n, #((univ.filter P).filter fun s => f s = t) := by
        simpa only [mem_univ, filter_true] using
          (sum_card_fiberwise_eq_card_filter (univ.filter P) univ f).symm
      _ = _ := by
        apply sum_congr rfl
        intro t _
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_filter]
        congr 1
        ext s
        simp [and_comm]
  have event (P : Pair n → Prop) :
      (∑ s, if P (f s) then 1 else (0 : ℕ)) = ∑ t, if P t then w t else 0 := by
    rw [countPartition (fun s => P (f s))]
    apply sum_congr rfl
    intro t _
    rw [← wlift t, ← size t]
    by_cases h : P t
    · rw [ite_eq_left h]
      exact Nat.card_congr
        { toFun := fun s => ⟨s.val, s.property.1⟩
          invFun := fun s => ⟨s.val, s.property, s.property.symm ▸ h⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    · have : IsEmpty {s : S // f s = t ∧ P (f s)} :=
        ⟨fun s => h (s.property.1 ▸ s.property.2)⟩
      simp [h]
  have pointEvent (P : Pair n → Prop) (d : DecidablePred P)
      (dS : ∀ s : S, Decidable (P (f s))) :
      (∑ s, @ite ℕ (P (f s)) (dS s) 1 0) = ∑ t, @ite ℕ (P t) (d t) (w t) 0 := by
    convert event P using 1
    · apply sum_congr rfl
      intro s _
      split <;> simp_all
    · apply sum_congr rfl
      intro t _
      split <;> simp_all
  have left (x : slice (n + 2) 0) :
      (∑ s, @ite ℕ ((f s).1 = x) (Classical.propDecidable _) 1 0) = 2 * k := by
    refine (pointEvent (fun t => t.1 = x) (fun _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _)).trans ?_
    rw [Fintype.sum_prod_type, ← rows x, sum_eq_single x]
    · apply sum_congr rfl
      intro y _
      simp
    · intro a _ ne
      simp [ne]
    · simp
  have right (y : slice (n + 2) 1) :
      (∑ s, @ite ℕ ((f s).2 = y) (Classical.propDecidable _) 1 0) = 2 * k := by
    refine (pointEvent (fun t => t.2 = y) (fun _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _)).trans ?_
    rw [Fintype.sum_prod_type, ← cols y]
    apply sum_congr rfl
    intro x _
    rw [sum_eq_single y]
    · simp
    · intro b _ ne
      simp [ne]
    · simp
  have cardLeft : Fintype.card (slice (n + 2) 0) = 2 ^ (n + 2) := by
    rw [← Fintype.card_congr (sliceEquiv (n + 2) 0), Fintype.card_prod, ZMod.card,
      ← Nat.card_eq_fintype_card, parityCard]
    exact (pow_succ (2 : ℕ) (n + 1)).symm
  have card : Fintype.card S = 2 ^ (n + 3) * k := by
    calc
      Fintype.card S = ∑ s : S, (1 : ℕ) := by simp
      _ = ∑ s, ∑ x : slice (n + 2) 0,
          @ite ℕ ((f s).1 = x) (Classical.propDecidable _) 1 0 := by
        apply sum_congr rfl
        intro s _
        rw [sum_eq_single (f s).1]
        · simp
        · intro a _ ne
          simp [Ne.symm ne]
        · simp
      _ = ∑ x : slice (n + 2) 0,
          ∑ s, @ite ℕ ((f s).1 = x) (Classical.propDecidable _) 1 0 := sum_comm
      _ = 2 ^ (n + 2) * (2 * k) := by
        calc
          _ = ∑ _x : slice (n + 2) 0, (2 * k) := sum_congr rfl fun x _ => left x
          _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, cardLeft]
      _ = _ := by rw [← Nat.mul_assoc, ← pow_succ]
  refine ⟨S, inferInstance, inferInstance, f, card, equiv, ⟨2 * k, left, right⟩, ?_,
    fun a => (size a).trans (wlift a)⟩
  intro i
  unfold fixedSeedCount
  simp_rw [ParitySeedCountSpectrum.coordinate_fixed_iff_generator]
  rw [countPartition (fun s => generator i • s = s), ← counts i]
  apply sum_congr rfl
  intro t _
  rw [fixed, wlift, ← ParitySeedCountSpectrum.coordinate_fixed_iff_generator,
    pair_fixed_coordinate, ← Bool.and_eq_true]


end

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

/-- Give both right colours the same weight from the parity table. -/
def colouredPairWeight {n : ℕ}
    (b : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → Fin 2 → ℕ) (a : Pair n) : ℕ :=
  b ((evenPoint n).symm a.1).1 ((oddPoint n).symm a.2).1 ((evenPoint n).symm a.1).2

/-- Realize the least per-fibre coordinate counts on one equivariant seed space.
A full even profile retains its left colour. Every other profile uses the
same multiplicity at both left colours. -/
theorem realize_coloured_table {n k : ℕ}
    (b : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → Fin 2 → ℕ)
    (rows : ∀ p c, ∑ q, b p q c = k)
    (cols : ∀ q, ∑ p, (b p q 0 + b p q 1) = 2 * k)
    (ordinary : ∀ p q, p.val ≠ 1 → b p q 0 = b p q 1) :
    RealizesFibreCounts n k (colouredPairWeight b) (fun i =>
      2 * (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, ∑ c : Fin 2,
        if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0)) := by
  classical
  let w : Pair n → ℕ := colouredPairWeight b
  have eval (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) (c d : Fin 2) :
      w (evenPoint n (p,c), oddPoint n (q,d)) = b p q c := by
    simp [w, colouredPairWeight]
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
  have counts (i : Fin (n + 2)) :
      (∑ a : Pair n, @ite ℕ (a.1.val.profile i && a.2.val.profile i) (Classical.propDecidable _)
        (w a % 2) 0) =
      2 * (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, ∑ c : Fin 2,
        if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0) := by
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
  exact weighted_realization_with_fibres w invariant left right counts

end
end D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
