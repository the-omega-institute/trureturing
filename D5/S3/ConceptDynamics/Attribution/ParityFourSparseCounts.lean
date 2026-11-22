/- GID: D5/S3/ConceptDynamics/Attribution/ParityFourSparseCounts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityFourSparseCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four fixed seeds at just one coordinate in dimension four require multiplier at least two. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts

open Finset MulAction
open D5.S3.ConceptDynamics.Attribution
open CoordinateFlagCoupling CoordinateFibreCounts ParitySeedBudget ParitySeedOptimization

noncomputable section

private theorem subgroup_fixed_iff {I X : Type*} [Fintype I] [MulAction (Acting I) X]
    (x : X) (i : I) :
    (∀ h : coordinate i, (h : Acting I) • x = x) ↔ generator i • x = x := by
  rw [show (∀ h : coordinate i, (h : Acting I) • x = x) ↔
      coordinate i ≤ stabilizer (Acting I) x from
    ⟨fun fixes g hg => fixes ⟨g, hg⟩, fun sub h => sub h.property⟩,
    coordinate, Subgroup.zpowers_le, mem_stabilizer_iff]

private theorem fixed_condition {n : ℕ} (t : Pair n) (i : Fin (n + 2)) :
    generator i • t = t ↔ t.1.val.profile i = true ∧ t.2.val.profile i = true := by
  rw [← subgroup_fixed_iff, ← Bool.and_eq_true, ← fixed_pair_iff]
  constructor
  · intro fixed g hg
    exact ⟨congrArg (fun x : Pair n => x.1.val) (fixed ⟨g, hg⟩),
      congrArg (fun x : Pair n => x.2.val) (fixed ⟨g, hg⟩)⟩
  · intro fixed g
    exact Prod.ext (Subtype.ext (fixed g g.property).1) (Subtype.ext (fixed g g.property).2)

section
attribute [local instance 10000] Classical.propDecidable

set_option maxHeartbeats 800000 in
private theorem weighted_realization {n k : ℕ} {z : Fin (n + 2) → ℕ} (w : Pair n → ℕ)
    (inv : ∀ (g : Acting (Fin (n + 2))) t, w (g • t) = w t)
    (rows : ∀ x : slice (n + 2) 0, (∑ y, w (x, y)) = 2 * k)
    (cols : ∀ y : slice (n + 2) 1, (∑ x, w (x, y)) = 2 * k)
    (counts : ∀ i, (∑ t : Pair n,
      if t.1.val.profile i && t.2.val.profile i then w t % 2 else 0) = z i) :
    RealizableSeedCounts n k z := by
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
  refine ⟨S, inferInstance, inferInstance, f, card, equiv, ⟨2 * k, left, right⟩, ?_⟩
  intro i
  unfold fixedSeedCount
  simp_rw [subgroup_fixed_iff]
  rw [countPartition (fun s => generator i • s = s), ← counts i]
  apply sum_congr rfl
  intro t _
  rw [fixed, wlift, fixed_condition, ← Bool.and_eq_true]

end

private def evenMask : Fin 8 → ℕ := ![0, 3, 5, 6, 9, 10, 12, 15]

private def oddMask : Fin 8 → ℕ := ![1, 2, 4, 7, 8, 11, 13, 14]

private def evenWord (p : Fin 8) (i : Fin 4) : Bool := (evenMask p).testBit i.val

private def oddWord (q : Fin 8) (i : Fin 4) : Bool := (oddMask q).testBit i.val

private def ordinaryEntries (oddBudget : Bool) : List (ℕ × ℕ × ℕ) :=
  if oddBudget then
    [(0, 7, 1), (0, 11, 1), (0, 2, 1), (12, 1, 1), (10, 1, 1), (6, 8, 1),
      (9, 2, 1), (5, 2, 1), (3, 4, 1), (3, 4, 2), (5, 8, 2), (6, 7, 2),
      (9, 11, 2), (10, 13, 2), (12, 14, 2)]
  else
    [(0, 1, 1), (0, 4, 1), (3, 1, 1), (3, 4, 1), (5, 2, 2), (6, 7, 2),
      (9, 8, 2), (10, 11, 2), (12, 13, 2)]

private def specialEntries (oddBudget : Bool) : List (ℕ × ℕ × ℕ) :=
  if oddBudget then [(0, 1, 1), (1, 1, 1), (0, 13, 2), (1, 14, 2)]
  else [(0, 14, 2), (1, 14, 2)]

private def certifiedWeight (oddBudget : Bool) (p q : Fin 8) (c : ZMod 2) : ℕ :=
  let entries := if evenMask p = 15 then specialEntries oddBudget else ordinaryEntries oddBudget
  let row := if evenMask p = 15 then c.val else evenMask p
  (entries.filterMap (fun (r, t, v) => if r = row ∧ t = oddMask q then some v else none)).sum

private theorem certificate_rows (oddBudget : Bool) (p : Fin 8) (c : ZMod 2) :
    (∑ q : Fin 8, ∑ _d : ZMod 2, certifiedWeight oddBudget p q c) =
      if oddBudget then 6 else 4 := by
  revert oddBudget p c
  decide

private theorem certificate_cols (oddBudget : Bool) (q : Fin 8) :
    (∑ p : Fin 8, ∑ c : ZMod 2, certifiedWeight oddBudget p q c) =
      if oddBudget then 6 else 4 := by
  revert oddBudget q
  decide

private theorem certificate_fixed (oddBudget : Bool) (i : Fin 4) :
    (∑ p : Fin 8, ∑ q : Fin 8, ∑ c : ZMod 2, ∑ _d : ZMod 2,
      if evenWord p i && oddWord q i then certifiedWeight oddBudget p q c % 2 else 0) =
      if i = 0 then 4 else 0 := by
  revert oddBudget i
  decide

private def indexedSlice (word : Fin 8 → Fin 4 → Bool) (parityBit : ZMod 2)
    (classLaw : ∀ p, parity (bitProfile (word p)) = parityBit)
    (inj : Function.Injective (bitProfile ∘ word)) : Fin 8 × ZMod 2 ≃ slice 4 parityBit :=
  (Equiv.ofBijective (fun p => (⟨bitProfile (word p), classLaw p⟩ : ParityClass 4 parityBit)) <| by
      apply (Fintype.bijective_iff_injective_and_card _).2
      refine ⟨fun _ _ h => inj (congrArg Subtype.val h), ?_⟩
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, parityCard]
      rfl).prodCongr (Equiv.refl _) |>.trans (sliceEquiv 4 parityBit)

private noncomputable def leftSlice : Fin 8 × ZMod 2 ≃ slice 4 0 :=
  indexedSlice evenWord 0 (by decide) (by decide)

private noncomputable def rightSlice : Fin 8 × ZMod 2 ≃ slice 4 1 :=
  indexedSlice oddWord 1 (by decide) (by decide)

private theorem indexedSlice_value (word : Fin 8 → Fin 4 → Bool) (parityBit : ZMod 2)
    (classLaw : ∀ p, parity (bitProfile (word p)) = parityBit)
    (inj : Function.Injective (bitProfile ∘ word)) (p : Fin 8) (c : ZMod 2) :
    (indexedSlice word parityBit classLaw inj (p, c)).val = ⟨word p, c⟩ := by
  change Output.mk (booleanProfile (bitProfile (word p))) c = ⟨word p, c⟩
  congr 1
  funext i
  cases h : word p i <;> simp [booleanProfile, bitProfile, h]

private theorem leftSlice_value (p : Fin 8) (c : ZMod 2) :
    (leftSlice (p, c)).val = ⟨evenWord p, c⟩ :=
  indexedSlice_value _ _ _ _ _ _

private theorem rightSlice_value (q : Fin 8) (d : ZMod 2) :
    (rightSlice (q, d)).val = ⟨oddWord q, d⟩ :=
  indexedSlice_value _ _ _ _ _ _

private theorem act_indexed {parityBit : ZMod 2} (e : Fin 8 × ZMod 2 ≃ slice 4 parityBit)
    (word : Fin 8 → Fin 4 → Bool) (repr : ∀ p c, (e (p, c)).val = ⟨word p, c⟩)
    (g : Acting (Fin 4)) (p : Fin 8) (c : ZMod 2) :
    g • e (p, c) = e (p, shift (word p) g.toAdd + c) := by
  apply Subtype.ext
  change g • (e (p, c)).val = (e (p, shift (word p) g.toAdd + c)).val
  rw [repr, repr]
  rfl

private noncomputable def weightCertificate (oddBudget : Bool) (t : Pair 2) : ℕ :=
  certifiedWeight oddBudget (leftSlice.symm t.1).1 (rightSlice.symm t.2).1
    (leftSlice.symm t.1).2

set_option maxRecDepth 1800 in
set_option maxHeartbeats 800000 in
private theorem budget_two_or_three (oddBudget : Bool) :
    RealizableSeedCounts 2 (if oddBudget then 3 else 2) (fun i => if i = 0 then 4 else 0) := by
  apply weighted_realization (weightCertificate oddBudget)
  · rintro g ⟨x,y⟩
    obtain ⟨⟨p,c⟩,rfl⟩ := leftSlice.surjective x
    obtain ⟨⟨q,d⟩,rfl⟩ := rightSlice.surjective y
    change weightCertificate oddBudget (g • leftSlice (p, c), g • rightSlice (q, d)) =
      weightCertificate oddBudget (leftSlice (p,c), rightSlice (q,d))
    rw [act_indexed leftSlice evenWord leftSlice_value, act_indexed rightSlice oddWord rightSlice_value]
    simp only [weightCertificate, Equiv.symm_apply_apply]
    unfold certifiedWeight
    by_cases h : evenMask p = 15
    · have all : ∀ i, evenWord p i = true :=
        (by decide : ∀ r : Fin 8, evenMask r = 15 → ∀ i, evenWord r i = true) p h
      simp [h, shift, all]
    · simp [h]
  · intro x
    obtain ⟨⟨p,c⟩,rfl⟩ := leftSlice.surjective x
    rw [← Equiv.sum_comp rightSlice]
    simpa only [Fintype.sum_prod_type, weightCertificate, Equiv.symm_apply_apply, mul_ite] using
      certificate_rows oddBudget p c
  · intro y
    obtain ⟨⟨q,d⟩,rfl⟩ := rightSlice.surjective y
    rw [← Equiv.sum_comp leftSlice]
    simpa only [Fintype.sum_prod_type, weightCertificate, Equiv.symm_apply_apply, mul_ite] using
      certificate_cols oddBudget q
  · intro i
    rw [Fintype.sum_prod_type, ← Equiv.sum_comp leftSlice]
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ p : Fin 8, ∑ c : ZMod 2, ∑ q : Fin 8, ∑ _d : ZMod 2,
          if evenWord p i && oddWord q i then certifiedWeight oddBudget p q c % 2 else 0 := by
        apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro c _
        rw [← Equiv.sum_comp rightSlice]
        simp only [Fintype.sum_prod_type, leftSlice_value, rightSlice_value,
          weightCertificate, Equiv.symm_apply_apply]
      _ = _ := by
        rw [← certificate_fixed oddBudget i]
        apply sum_congr rfl
        intro p _
        exact sum_comm

private theorem below_two_impossible
    (k : ℕ) (tooSmall : k < 2) :
    ¬ RealizableSeedCounts 2 k (fun i => if i = 0 then 4 else 0) := by
  intro realized
  have kCases : k = 0 ∨ k = 1 := by omega
  rcases kCases with rfl | rfl
  · obtain ⟨S, _, _, _, card, _, _, h⟩ := realized
    have empty : IsEmpty S := Fintype.card_eq_zero_iff.mp (by simpa using card)
    have hz := h 0
    simp [fixedSeedCount] at hz
  · obtain ⟨a, fixed, cuts⟩ :=
      (ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts 2 _).mp realized
    let ones : Profile 4 := fun _ => 1
    have allEven : parity ones = 0 := by decide
    have cut := cuts ones allEven
    have oneTerm (i : Fin 4) : 4 - a i = if i = 0 then 1 else 0 := by
      have eq := (fixed i).2
      change (if i = 0 then 4 else 0) = 4 * (4 - a i) at eq
      by_cases hi : i = 0 <;> simp [hi] at eq ⊢ <;> omega
    change 4 ≤ ∑ i : Fin 4, if ones i = 0 then a i else 4 - a i at cut
    simp only [ones, one_ne_zero, ite_false, oneTerm] at cut
    simp at cut

end

open ParitySeedCountSpectrum

/-- At budget 32k, four seeds can be fixed at one prescribed coordinate
and zero at all other coordinates exactly when k is at least two. -/
theorem exact_four_sparse (k : ℕ) (i : Fin 4) :
    RealizableSeedCounts 2 k (fun j => if j = i then 4 else 0) ↔ 2 ≤ k := by
  let p : Equiv.Perm (Fin 4) := Equiv.swap i 0
  have zeroBlock (r : ℕ) : RealizableSeedCounts 2 (r + r) (fun _ => 0) :=
    (zero_coordinate_counts_iff 2 (r + r)).mpr (Or.inr ⟨r, rfl⟩)
  have relabelTarget {a : ℕ} (v : Fin 4) (h : RealizableSeedCounts 2 a
      (fun j => if j = v then 4 else 0)) :
      RealizableSeedCounts 2 a (fun j => if j = p.symm v then 4 else 0) := by
    have h' := ParitySeedCoordinateRelabel.realizable_relabel p h
    convert h' using 1
    funext j
    simp only [Function.comp_apply, Equiv.eq_symm_apply]
  constructor
  · intro h
    by_contra! low
    apply below_two_impossible k low
    simpa [p] using relabelTarget i h
  · intro enough
    have hk : k = 2 + (k / 2 - 1 + (k / 2 - 1)) ∨
        k = 3 + (k / 2 - 1 + (k / 2 - 1)) := by omega
    rcases hk with he | ho
    · rw [he]
      have h := add_realizable_seed_counts (budget_two_or_three false) (zeroBlock (k / 2 - 1))
      simpa [p] using relabelTarget 0 (by simpa using h)
    · rw [ho]
      have h := add_realizable_seed_counts (budget_two_or_three true) (zeroBlock (k / 2 - 1))
      simpa [p] using relabelTarget 0 (by simpa using h)

end D5.S3.ConceptDynamics.Attribution.ParityFourSparseCounts
