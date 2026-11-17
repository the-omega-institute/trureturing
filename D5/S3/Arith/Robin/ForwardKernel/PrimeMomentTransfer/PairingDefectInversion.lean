/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wick deviations control all subfamily pairing defects by triangular inversion. -/

/-
proof_shape: pairing_defect_inversion, inversionConstant_nonneg: content.
proof_shape: pairingSupport_map: bind-only (consumers: partialPairing_map_iff,
  subset_quadratic_pairing_defect_transfer);
  partialPairing_map_iff: bind-only (consumer: sum_partialPairings_map);
  sum_partialPairings_map: bind-only (consumers: subset_quadratic_pairing_defect_transfer,
    inversionConstant_subset_recursion);
  subsetDistinctMoment_map: bind-only (consumer: subset_quadratic_pairing_defect_transfer);
  subset_quadratic_pairing_defect_transfer, pairing_weight_abs_le,
    subset_pairing_defect_small, pairing_remainder_card: bind-only
    (consumer: pairing_defect_inversion);
  inversionConstant_eq: bind-only (consumers: inversionConstant_small,
    inversionConstant_nonneg, inversionConstant_subset_recursion);
  inversionConstant_small, inversionConstant_subset_recursion, wickDeviationSup_bounds:
    bind-only (consumer: pairing_defect_inversion).
escape_witness: pairing_defect_inversion constructs its universal estimate by well-founded
  triangular induction: the empty pairing isolates the unknown defect and every nonempty
  pairing reduces its order. This estimate cannot be obtained from the forward convolution
  by instantiation or normalization without that induction. The public conclusion is the
  output of this new estimate construction. inversionConstant_nonneg supplies the recursive
  coefficient positivity on its live path.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectTransfer

/-! Quantitative Wick-defect inversion, Theorem 501.3, inequality (501.2). -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] in
private theorem pairingSupport_map (e : α ↪ β) (P : Finset (Finset α)) :
    pairingSupport (P.map (Finset.mapEmbedding e).toEmbedding) =
      (pairingSupport P).map e := by
  ext x
  constructor
  · intro hx
    obtain ⟨E, hE, hxE⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hE
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxE
    exact Finset.mem_map.mpr ⟨i, Finset.mem_biUnion.mpr ⟨d, hd, hi⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨d, hd, hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨d.map e,
      Finset.mem_map.mpr ⟨d, hd, rfl⟩, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩

omit [Fintype α] [Fintype β] in
private theorem partialPairing_map_iff (e : α ↪ β) (U : Finset α)
    (P : Finset (Finset α)) :
    IsPartialPairing (U.map e) (P.map (Finset.mapEmbedding e).toEmbedding) ↔
      IsPartialPairing U P := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro E hE
      simpa using h.1 (E.map e) (Finset.mem_map.mpr ⟨E, hE, rfl⟩)
    · intro E hE F hF hEF
      apply (Finset.disjoint_map e).mp
      exact h.2.1 (Finset.mem_map.mpr ⟨E, hE, rfl⟩)
        (Finset.mem_map.mpr ⟨F, hF, rfl⟩) (fun hh => hEF (Finset.map_injective e hh))
    · have hh := h.2.2
      rw [pairingSupport_map] at hh
      exact Finset.map_subset_map.mp hh
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro E hE
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hE
      simpa using h.1 d hd
    · intro E hE F hF hEF
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hE
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hF
      exact (Finset.disjoint_map e).mpr (h.2.1 hd hq (fun hh => hEF (congrArg _ hh)))
    · rw [pairingSupport_map]
      exact Finset.map_subset_map.mpr h.2.2

private theorem sum_partialPairings_map (e : α ↪ β) (U : Finset α)
    (F : Finset (Finset β) → ℝ) :
    (∑ P : Finset (Finset α) with IsPartialPairing U P,
      F (P.map (Finset.mapEmbedding e).toEmbedding)) =
      ∑ Q : Finset (Finset β) with IsPartialPairing (U.map e) Q, F Q := by
  apply Finset.sum_bij (fun P _ => P.map (Finset.mapEmbedding e).toEmbedding)
  · intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (partialPairing_map_iff e U P).mpr (Finset.mem_filter.mp hP).2⟩
  · intro P hP Q hQ h
    exact Finset.map_injective _ h
  · intro Q hQ
    have hQp := (Finset.mem_filter.mp hQ).2
    have hsub : Q ⊆ U.powerset.map (Finset.mapEmbedding e).toEmbedding := by
      intro E hE
      have hEU : E ⊆ U.map e := by
        intro i hi
        exact hQp.2.2 (Finset.mem_biUnion.mpr ⟨E, hE, hi⟩)
      obtain ⟨d, hd, heq⟩ := Finset.subset_map_iff.mp hEU
      exact Finset.mem_map.mpr ⟨d, Finset.mem_powerset.mpr hd, heq.symm⟩
    obtain ⟨P, hPU, hP⟩ := Finset.subset_map_iff.mp hsub
    refine ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hP.symm⟩
    apply (partialPairing_map_iff e U P).mp
    rw [← hP]
    exact hQp
  · intro P hP
    rfl

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem subsetDistinctMoment_map {ι A : Type*} [Fintype ι]
    [CommRing A] [Algebra ℝ A] (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (e : α ↪ β) (f : β → ι → ℝ) (U : Finset α) :
    subsetDistinctMoment ℓ Y f (U.map e) =
      subsetDistinctMoment ℓ Y (fun i => f (e i)) U := by
  classical
  rw [subsetDistinctMoment, ← retained_assignment_reindex ℓ Y (U.map e) f]
  exact assignment_moment_reindex ℓ Y
    ((Finset.equivMap e U).symm.trans (Fintype.equivFin U))
    (fun i : U.map e => f i.val)

private theorem subset_quadratic_pairing_defect_transfer {k : ℕ}
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (a b C H L : ℝ) (hC : 1 ≤ C) (hHL : L ≤ H) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C (Real.sqrt (H * L)))
    (U : Finset (Fin k)) :
    ∃ E : ℝ,
      subsetFamilyMoment ℓ Y f U -
          finitePairingPolynomial U (subsetFamilyMoment ℓ Y f) =
        (∑ P : Finset (Finset (Fin k)) with IsPartialPairing U P,
          b ^ P.card * (∏ e ∈ P, subsetWeightSum f e) *
            subsetPairingDefect ℓ Y f (U \ pairingSupport P)) + E ∧
      |E| ≤ pairingDefectConstant U.card C * (Real.sqrt (H * L)) ^ U.card *
        (Real.sqrt (L / H) + 1 / H) := by
  let e : Fin U.card ↪ Fin k :=
    ⟨fun i => (U.equivFin.symm i).val,
      fun i j hij => U.equivFin.symm.injective (Subtype.ext hij)⟩
  let g : Fin U.card → ι → ℝ := fun i => f (e i)
  have hmap : (Finset.univ : Finset (Fin U.card)).map e = U := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (U.equivFin.symm i).property
    · intro hx
      refine ⟨U.equivFin ⟨x, hx⟩, ?_⟩
      change (U.equivFin.symm (U.equivFin ⟨x, hx⟩)).val = x
      exact congrArg Subtype.val (U.equivFin.symm_apply_apply ⟨x, hx⟩)
  have hcard : U.card ≤ k := by
    simpa using Finset.card_le_univ U
  have hgR : DisjointLabelMomentBound ℓ Y g C (Real.sqrt (H * L)) := by
    intro r hr2 hrm labels hnon hdis
    have hh := hR r hr2 (lt_of_lt_of_le hrm hcard)
      (fun j => (labels j).map e)
      (fun j => (Finset.map_nonempty).mpr (hnon j))
      (fun i j hij => (Finset.disjoint_map e).mpr (hdis i j hij))
    simpa only [Finset.prod_map, g] using hh
  have hV : quadraticFamilyMoment ℓ Y g = subsetFamilyMoment ℓ Y f U := by
    calc
      quadraticFamilyMoment ℓ Y g = subsetFamilyMoment ℓ Y f
          ((Finset.univ : Finset (Fin U.card)).map e) := by
        simp only [quadraticFamilyMoment, subsetFamilyMoment, Finset.prod_map, g]
      _ = subsetFamilyMoment ℓ Y f U := congrArg (subsetFamilyMoment ℓ Y f) hmap
  let F : Finset (Finset (Fin k)) → ℝ := fun P =>
    b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
      subsetDistinctMoment ℓ Y f (U \ pairingSupport P)
  have hterm (P : Finset (Finset (Fin U.card))) :
      b ^ P.card * (∏ E ∈ P, subsetWeightSum g E) *
          subsetDistinctMoment ℓ Y g (Finset.univ \ pairingSupport P) =
        F (P.map (Finset.mapEmbedding e).toEmbedding) := by
    have hrem : U \ pairingSupport (P.map (Finset.mapEmbedding e).toEmbedding) =
        ((Finset.univ : Finset (Fin U.card)) \ pairingSupport P).map e := by
      rw [Finset.map_sdiff, pairingSupport_map, hmap]
    have hweight (E : Finset (Fin U.card)) :
        subsetWeightSum f (E.map e) = subsetWeightSum g E := by
      simp only [subsetWeightSum, Finset.prod_map, g]
    dsimp only [F]
    rw [Finset.card_map, Finset.prod_map, hrem, subsetDistinctMoment_map ℓ Y e f]
    apply congrArg₂ (fun x y : ℝ => b ^ P.card * x * y) ?_ rfl
    exact Finset.prod_congr rfl (fun E hE => (hweight E).symm)
  have hmain :
      (∑ P : Finset (Finset (Fin U.card)) with IsPartialPairing Finset.univ P,
        b ^ P.card * (∏ E ∈ P, subsetWeightSum g E) *
          subsetDistinctMoment ℓ Y g (Finset.univ \ pairingSupport P)) =
      ∑ Q : Finset (Finset (Fin k)) with IsPartialPairing U Q, F Q := by
    calc
      _ = ∑ P : Finset (Finset (Fin U.card)) with IsPartialPairing Finset.univ P,
          F (P.map (Finset.mapEmbedding e).toEmbedding) := by
        apply Finset.sum_congr rfl
        intro P hP
        exact hterm P
      _ = ∑ Q : Finset (Finset (Fin k)) with
          IsPartialPairing ((Finset.univ : Finset (Fin U.card)).map e) Q, F Q :=
        sum_partialPairings_map e Finset.univ F
      _ = _ := by rw [hmap]
  obtain ⟨E, hraw, _, hE⟩ := quadratic_pairing_defect_transfer ℓ Y g a b C H L
    hC hHL hL ha hb hquad hunit hcenter hD (fun i d => hf (e i) d) hgR
  rw [hV, hmain] at hraw
  have hconv := subset_pairing_defect_convolution ℓ Y a b hunit hcenter
    (fun d => by simpa only [Algebra.smul_def, mul_one] using hquad d) f U
  refine ⟨E, ?_, hE⟩
  dsimp only [F] at hraw
  linarith [hraw, hconv]

omit [Fintype α] [DecidableEq α] in
private theorem pairing_weight_abs_le {ι : Type*} [Fintype ι]
    (f : α → ι → ℝ) (b C H L : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hb : |b| ≤ C * L) (hD : (Fintype.card ι : ℝ) ≤ C * H)
    (hf : ∀ i d, |f i d| ≤ 1) (P : Finset (Finset α)) :
    |b| ^ P.card * |∏ e ∈ P, subsetWeightSum f e| ≤
      (C ^ 2 * (Real.sqrt (H * L)) ^ 2) ^ P.card := by
  have hT (E : Finset α) : |subsetWeightSum f E| ≤ C * H := by
    calc
      |subsetWeightSum f E| ≤ ∑ d : ι, |∏ i ∈ E, f i d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i hi => hf i d)
      _ ≤ C * H := by simpa using hD
  rw [Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _E ∈ P, (C ^ 2 * Real.sqrt (H * L) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro E hE
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      · intro E hE
        calc
          |b| * |subsetWeightSum f E| ≤ (C * L) * (C * H) :=
            mul_le_mul hb (hT E) (abs_nonneg _) (mul_nonneg hC hL)
          _ = C ^ 2 * Real.sqrt (H * L) ^ 2 := by
            rw [Real.sq_sqrt (mul_nonneg hH hL)]
            ring
    _ = _ := by simp

theorem subset_pairing_defect_small
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : α → ι → ℝ)
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (U : Finset α) (hU : U.card ≤ 2) :
    subsetPairingDefect ℓ Y f U = 0 := by
  have hclass (P : Finset (Finset α)) :
      IsPerfectPairing U P ↔
        (U = ∅ ∧ P = ∅) ∨ (U.card = 2 ∧ P = {U}) := by
    constructor
    · intro hP
      have hsub : P ⊆ {U} := by
        intro E hE
        apply Finset.mem_singleton.mpr
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          exact hP.1.2.2 (Finset.mem_biUnion.mpr ⟨E, hE, hi⟩)
        · rw [hP.1.1 E hE]
          exact hU
      rcases Finset.subset_singleton_iff.mp hsub with h0 | h1
      · left
        refine ⟨?_, h0⟩
        simpa only [h0, pairingSupport, Finset.biUnion_empty] using hP.2.symm
      · right
        refine ⟨?_, h1⟩
        exact hP.1.1 U (by rw [h1]; simp)
    · rintro (⟨rfl, rfl⟩ | ⟨h2, rfl⟩)
      · simp [IsPerfectPairing, IsPartialPairing, pairingSupport]
      · simp [IsPerfectPairing, IsPartialPairing, pairingSupport, h2]
  have hpoly (c : Finset α → ℝ) :
      finitePairingPolynomial U c =
        if U = ∅ then 1 else if U.card = 2 then c U else 0 := by
    unfold finitePairingPolynomial
    simp_rw [hclass]
    by_cases h0 : U = ∅
    · subst U
      simp [Finset.sum_filter]
    · by_cases h2 : U.card = 2
      · simp [h0, h2, Finset.sum_filter]
      · simp [h0, h2]
  rw [subsetPairingDefect, hpoly]
  by_cases h0 : U = ∅
  · subst U
    simp [subsetDistinctMoment, distinctIndexMoment, hunit, Function.Injective]
  · by_cases h2 : U.card = 2
    · simp [h0, h2]
    · have h1 : Fintype.card U = 1 := by
        rw [Fintype.card_coe]
        have : U.card ≠ 0 := fun hc => h0 (Finset.card_eq_zero.mp hc)
        omega
      have hz (n : ℕ) (w : Fin n → ι → ℝ) (hn : n = 1) :
          distinctIndexMoment ℓ Y w = 0 := by
        subst n
        unfold distinctIndexMoment
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Fin.prod_univ_one, hcenter, mul_zero]
      have hR : subsetDistinctMoment ℓ Y f U = 0 := by
        exact hz _ _ h1
      simp [h0, h2, hR]

omit [Fintype α] in
theorem pairing_remainder_card (U : Finset α) (P : Finset (Finset α))
    (hP : IsPartialPairing U P) :
    (U \ pairingSupport P).card = U.card - 2 * P.card ∧
      (P.Nonempty → (U \ pairingSupport P).card < U.card) ∧
      2 * P.card ≤ U.card := by
  have hsupp : (pairingSupport P).card = 2 * P.card := by
    calc
      (pairingSupport P).card = ∑ E ∈ P, E.card :=
        Finset.card_biUnion hP.2.1
      _ = ∑ _E ∈ P, 2 := Finset.sum_congr rfl (fun E hE => hP.1 E hE)
      _ = 2 * P.card := by simp [Nat.mul_comm]
  have hcard : (U \ pairingSupport P).card = U.card - 2 * P.card := by
    rw [Finset.card_sdiff_of_subset hP.2.2, hsupp]
  have hle := Finset.card_le_card hP.2.2
  rw [hsupp] at hle
  refine ⟨hcard, ?_, hle⟩
  intro hne
  have hp := Finset.card_pos.mpr hne
  rw [hcard]
  omega

/-- The triangular inversion constant, with zero entries in orders at most two. -/
def inversionConstant (C : ℝ) (m : ℕ) : ℝ :=
  Nat.strongRecOn m fun n rec =>
    if hn : n ≤ 2 then 0 else
      1 + ∑ P : Finset (Finset (Fin n)) with IsPartialPairing Finset.univ P,
        if hP : P.Nonempty then
          C ^ (2 * P.card) * rec (n - 2 * P.card)
            (by have hp := Finset.card_pos.mpr hP; omega)
        else 0

private theorem inversionConstant_eq (C : ℝ) (m : ℕ) :
    inversionConstant C m =
      if m ≤ 2 then 0 else
        1 + ∑ P : Finset (Finset (Fin m)) with
          IsPartialPairing Finset.univ P ∧ P.Nonempty,
          C ^ (2 * P.card) * inversionConstant C (m - 2 * P.card) := by
  unfold inversionConstant
  rw [Nat.strongRecOn_eq]
  split_ifs with hm
  · rfl
  · simp only [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hp : IsPartialPairing Finset.univ P <;>
      by_cases hne : P.Nonempty <;> simp [hp, hne]


private theorem inversionConstant_small (C : ℝ) {m : ℕ} (hm : m ≤ 2) :
    inversionConstant C m = 0 := by
  rw [inversionConstant_eq, if_pos hm]


private theorem inversionConstant_nonneg (C : ℝ) (m : ℕ) :
    0 ≤ inversionConstant C m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rw [inversionConstant_eq]
      split_ifs with hm
      · exact le_rfl
      · apply add_nonneg zero_le_one
        apply Finset.sum_nonneg
        intro P hP
        have hp : P.Nonempty := (Finset.mem_filter.mp hP).2.2
        have hlt : m - 2 * P.card < m := by
          have := Finset.card_pos.mpr hp
          omega
        exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg C) _)
          (ih _ hlt)


private theorem inversionConstant_subset_recursion (C : ℝ) (U : Finset α)
    (hU : 2 < U.card) :
    inversionConstant C U.card =
      1 + ∑ P : Finset (Finset α) with IsPartialPairing U P ∧ P.Nonempty,
        C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card) := by
  let e : Fin U.card ↪ α :=
    U.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have he : (Finset.univ : Finset (Fin U.card)).map e = U := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (U.equivFin.symm i).property
    · intro hx
      refine ⟨U.equivFin ⟨x, hx⟩, ?_⟩
      simp [e]
  rw [inversionConstant_eq, if_neg (by omega)]
  have hsum := sum_partialPairings_map e (Finset.univ : Finset (Fin U.card))
    (fun P => if P.Nonempty then
      C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card) else 0)
  rw [he] at hsum
  simp only [Finset.card_map, Finset.map_nonempty] at hsum
  simp only [Finset.sum_filter, ite_and] at hsum ⊢
  exact congrArg (fun x : ℝ => 1 + x) hsum

/-- The largest normalized Wick deviation on subfamilies of order at least three,
with value zero when there are no such subfamilies. -/
def wickDeviationSup {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : α → ι → ℝ) (s : ℝ)
    (U : Finset α) : ℝ :=
  (insert 0 ((U.powerset.filter (fun V => 3 ≤ V.card)).image
    (fun V => |subsetFamilyMoment ℓ Y f V -
      finitePairingPolynomial V (subsetFamilyMoment ℓ Y f)| / s ^ V.card))).sup'
      (by simp) id

private theorem wickDeviationSup_bounds {ι A : Type*} [Fintype ι]
    [CommRing A] [Algebra ℝ A]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : α → ι → ℝ) (s : ℝ) (U : Finset α) :
    0 ≤ wickDeviationSup ℓ Y f s U ∧
    (∀ V ⊆ U, 3 ≤ V.card →
      |subsetFamilyMoment ℓ Y f V -
        finitePairingPolynomial V (subsetFamilyMoment ℓ Y f)| / s ^ V.card ≤
          wickDeviationSup ℓ Y f s U) ∧
    (∀ V ⊆ U, wickDeviationSup ℓ Y f s V ≤ wickDeviationSup ℓ Y f s U) := by
  refine ⟨Finset.le_sup' (f := id) (Finset.mem_insert_self _ _), ?_, ?_⟩
  · intro V hVU hV
    apply Finset.le_sup' (f := id)
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨V,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hVU, hV⟩, rfl⟩
  · intro V hVU
    apply Finset.sup'_le
    intro x hx
    apply Finset.le_sup' (f := id)
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨W, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp
          (Finset.mem_filter.mp hW).1).trans hVU), (Finset.mem_filter.mp hW).2⟩, rfl⟩

theorem pairing_defect_inversion {k : ℕ}
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (a b C H L M : ℝ) (hC : 1 ≤ C) (hHL : L ≤ H) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C (Real.sqrt (H * L)))
    (hM0 : 0 ≤ M) (hM : ∀ j ≤ k, pairingDefectConstant j C ≤ M) :
    ∀ U : Finset (Fin k),
      |subsetPairingDefect ℓ Y f U| ≤ inversionConstant C U.card *
        (wickDeviationSup ℓ Y f (Real.sqrt (H * L)) U +
          M * (Real.sqrt (L / H) + 1 / H)) * (Real.sqrt (H * L)) ^ U.card := by
  let s := Real.sqrt (H * L)
  let η := Real.sqrt (L / H) + 1 / H
  have hC0 : 0 ≤ C := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (by linarith) (by linarith))
  have hs0 : 0 ≤ s := le_of_lt hs
  have hη : 0 ≤ η := add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr hH0)
  intro U
  refine Finset.strongInductionOn U ?_
  intro U ih
  by_cases hsmall : U.card ≤ 2
  · rw [subset_pairing_defect_small ℓ Y f hunit hcenter U hsmall,
      inversionConstant_small C hsmall]
    simp
  have hU : 2 < U.card := by omega
  have hcard : U.card ≤ k := by simpa using Finset.card_le_univ U
  let D := wickDeviationSup ℓ Y f s U + M * η
  have hD0 : 0 ≤ D := add_nonneg (wickDeviationSup_bounds ℓ Y f s U).1
    (mul_nonneg hM0 hη)
  let S : Finset (Finset (Finset (Fin k))) :=
    Finset.univ.filter (IsPartialPairing U)
  let t : Finset (Finset (Fin k)) → ℝ := fun P =>
    b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
      subsetPairingDefect ℓ Y f (U \ pairingSupport P)
  have hempty : ∅ ∈ S := by
    simp [S, IsPartialPairing, pairingSupport]
  have ht0 : t ∅ = subsetPairingDefect ℓ Y f U := by
    simp [t, pairingSupport]
  have hsplit : (∑ P ∈ S, t P) =
      subsetPairingDefect ℓ Y f U + ∑ P ∈ S.erase ∅, t P := by
    rw [← Finset.add_sum_erase S t hempty, ht0]
  have hSerase : S.erase ∅ =
      Finset.univ.filter (fun P => IsPartialPairing U P ∧ P.Nonempty) := by
    ext P
    simp [S, Finset.nonempty_iff_ne_empty, and_comm]
  obtain ⟨E, htransfer, hE⟩ := subset_quadratic_pairing_defect_transfer ℓ Y f
    a b C H L hC hHL hL ha hb hquad hunit hcenter hD hf hR U
  change subsetFamilyMoment ℓ Y f U -
      finitePairingPolynomial U (subsetFamilyMoment ℓ Y f) =
    (∑ P ∈ S, t P) + E at htransfer
  rw [hsplit] at htransfer
  have hisolate : subsetPairingDefect ℓ Y f U =
      (subsetFamilyMoment ℓ Y f U -
        finitePairingPolynomial U (subsetFamilyMoment ℓ Y f)) - E -
          ∑ P ∈ S.erase ∅, t P := by linarith [htransfer]
  have hdev : |subsetFamilyMoment ℓ Y f U -
      finitePairingPolynomial U (subsetFamilyMoment ℓ Y f)| ≤
      wickDeviationSup ℓ Y f s U * s ^ U.card := by
    exact (div_le_iff₀ (pow_pos hs _)).mp
      ((wickDeviationSup_bounds ℓ Y f s U).2.1 U (Finset.Subset.refl U) (by omega))
  have hE' : |E| ≤ (M * η) * s ^ U.card := by
    calc
      |E| ≤ pairingDefectConstant U.card C * s ^ U.card * η := hE
      _ ≤ M * s ^ U.card * η :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hM U.card hcard) (pow_nonneg hs0 _)) hη
      _ = (M * η) * s ^ U.card := by ring
  have hterm (P : Finset (Finset (Fin k))) (hPS : P ∈ S.erase ∅) :
      |t P| ≤
        (C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
          D * s ^ U.card := by
    have hP : IsPartialPairing U P := (Finset.mem_filter.mp
      (Finset.mem_erase.mp hPS).2).2
    have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hPS).1
    let V := U \ pairingSupport P
    have hVsub : V ⊆ U := Finset.sdiff_subset
    have hVcard : V.card = U.card - 2 * P.card :=
      (pairing_remainder_card U P hP).1
    have hVlt : V.card < U.card := (pairing_remainder_card U P hP).2.1 hPne
    have hVstrict : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr
      ⟨hVsub, fun h => by rw [h] at hVlt; omega⟩
    have hA0 : 0 ≤ inversionConstant C V.card := inversionConstant_nonneg C V.card
    have hΩ : wickDeviationSup ℓ Y f s V ≤ wickDeviationSup ℓ Y f s U :=
      (wickDeviationSup_bounds ℓ Y f s U).2.2 V hVsub
    have hVbound : |subsetPairingDefect ℓ Y f V| ≤
        inversionConstant C V.card * D * s ^ V.card := by
      apply (ih V hVstrict).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hΩ (le_refl (M * η))) hA0)
        (pow_nonneg hs0 _)
    have hpbound : 2 * P.card ≤ U.card := (pairing_remainder_card U P hP).2.2
    have hdegree : 2 * P.card + V.card = U.card := by omega
    have hscale : (C ^ 2 * s ^ 2) ^ P.card * s ^ V.card =
        C ^ (2 * P.card) * s ^ U.card := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add, hdegree]
    have hw := pairing_weight_abs_le f b C H L hC0 hH0 hL0 hb hD hf P
    change |(b ^ P.card * ∏ E ∈ P, subsetWeightSum f E) *
      subsetPairingDefect ℓ Y f V| ≤ _
    rw [abs_mul, abs_mul, abs_pow]
    calc
      _ ≤ (|b| ^ P.card * |∏ E ∈ P, subsetWeightSum f E|) *
          (inversionConstant C V.card * D * s ^ V.card) :=
        mul_le_mul_of_nonneg_left hVbound
          (mul_nonneg (pow_nonneg (abs_nonneg b) _) (abs_nonneg _))
      _ ≤ (C ^ 2 * s ^ 2) ^ P.card *
          (inversionConstant C V.card * D * s ^ V.card) :=
        mul_le_mul_of_nonneg_right hw
          (mul_nonneg (mul_nonneg hA0 hD0) (pow_nonneg hs0 _))
      _ = (inversionConstant C V.card * D) *
          ((C ^ 2 * s ^ 2) ^ P.card * s ^ V.card) := by ring
      _ = (C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
          D * s ^ U.card := by rw [hscale, hVcard]; ring
  have hsum : (∑ P ∈ S.erase ∅, |t P|) ≤
      (∑ P ∈ S.erase ∅,
        C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
          D * s ^ U.card := by
    calc
      _ ≤ ∑ P ∈ S.erase ∅,
          (C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
            D * s ^ U.card := Finset.sum_le_sum hterm
      _ = _ := by simp only [← Finset.sum_mul]
  have hrec := inversionConstant_subset_recursion C U hU
  rw [← hSerase] at hrec
  calc
    |subsetPairingDefect ℓ Y f U| =
        |(subsetFamilyMoment ℓ Y f U -
          finitePairingPolynomial U (subsetFamilyMoment ℓ Y f)) - E -
            ∑ P ∈ S.erase ∅, t P| := congrArg abs hisolate
    _ ≤ |(subsetFamilyMoment ℓ Y f U -
        finitePairingPolynomial U (subsetFamilyMoment ℓ Y f)) - E| +
          |∑ P ∈ S.erase ∅, t P| := abs_sub _ _
    _ ≤ (|subsetFamilyMoment ℓ Y f U -
        finitePairingPolynomial U (subsetFamilyMoment ℓ Y f)| + |E|) +
          ∑ P ∈ S.erase ∅, |t P| :=
      add_le_add (abs_sub _ _) (Finset.abs_sum_le_sum_abs t (S.erase ∅))
    _ ≤ (wickDeviationSup ℓ Y f s U * s ^ U.card + (M * η) * s ^ U.card) +
        (∑ P ∈ S.erase ∅,
          C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
            D * s ^ U.card := add_le_add (add_le_add hdev hE') hsum
    _ = (1 + ∑ P ∈ S.erase ∅,
        C ^ (2 * P.card) * inversionConstant C (U.card - 2 * P.card)) *
          D * s ^ U.card := by dsimp only [D]; ring
    _ = inversionConstant C U.card * D * s ^ U.card := by rw [hrec]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
