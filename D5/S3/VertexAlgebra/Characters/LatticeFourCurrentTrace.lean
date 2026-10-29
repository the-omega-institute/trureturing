/- GID: D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite four-current cycle traces and the bounded labeled partial-matching coefficient. -/

import D5.S3.VertexAlgebra.Characters.FourCurrent.MatchingRotation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator
open MvPolynomial

namespace D5.S3.VertexAlgebra.LatticeFourCurrentTrace
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter LatticeTwoCurrentTrace

open private sum_fullFiber
  from D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace

open private e12 e13 e14 e23 e24 e34 edgeParam
  PM4.unpaired arcMem sideMem min4 max4 matchingShift contraction
  rotateFour original_four_rotate edges_ordered le_max4
  from D5.S3.VertexAlgebra.Characters.FourCurrent.TraceRecurrence

open private signedPairCoefficient original_four_finite_coefficient no_increase_constant currentMode modeCompatible modeFrequency modeSide
  compatible_matching_modes windingEnergy creationDelay matching_energy_transport orderedChargeWeight orderedFourCurrentCoefficient bounded_coefficient_ordered
  from D5.S3.VertexAlgebra.Characters.FourCurrent.MatchingModes

open private original_four_constant_matching bounded_coefficient_rotation finite_residual_delta bounded_division_sum bounded_geometric_delta
  from D5.S3.VertexAlgebra.Characters.FourCurrent.MatchingRotation

private theorem matching_parameter_bounds (n : Four → ℕ) (Q t : ℕ) (M : PM4)
    (ell : edgeParam M → ℕ) (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ)
    (hpos : ∀ e, 0 < ell e)
    (heq : ∀ j, n j = Q + t + matchingShift M ell ε k j) :
    Q ≤ min4 n ∧ t ≤ min4 n ∧
      ∀ e, ell e ≤ max4 n ∧ k e ≤ min4 n := by
  classical
  have hQ (j : Four) : Q ≤ n j := by have h := heq j; omega
  have ht (j : Four) : t ≤ n j := by have h := heq j; omega
  refine ⟨le_min (le_min (hQ 0) (hQ 1)) (le_min (hQ 2) (hQ 3)),
    le_min (le_min (ht 0) (ht 1)) (le_min (ht 2) (ht 3)), ?_⟩
  intro e
  have hterm (j : Four) :
      ell e * (k e + if sideMem (ε e) e.1 j then 1 else 0) ≤
        matchingShift M ell ε k j := by
    unfold matchingShift
    exact Finset.single_le_sum
      (fun (x : edgeParam M) _ => Nat.zero_le
        (ell x * (k x + if sideMem (ε x) x.1 j then 1 else 0))) (Finset.mem_univ e)
  have hwind (j : Four) : k e ≤ n j := by
    have hmul : k e ≤ ell e * k e := by
      simpa using Nat.mul_le_mul_right (k e) (show 1 ≤ ell e from hpos e)
    have hpart : ell e * k e ≤
        ell e * (k e + if sideMem (ε e) e.1 j then 1 else 0) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hs := hterm j
    have hn := heq j
    omega
  have hside : ∃ j : Four, sideMem (ε e) e.1 j := by
    by_cases h : (ε e).1 = 0
    · refine ⟨e.1.2, ?_⟩
      simp [sideMem, h, arcMem, edges_ordered M e.1 e.2]
    · refine ⟨e.1.1, ?_⟩
      simp [sideMem, h, arcMem]
  obtain ⟨j, hj⟩ := hside
  have hs := hterm j
  rw [if_pos hj] at hs
  have hl : ell e ≤ ell e * (k e + 1) := by
    simpa using Nat.mul_le_mul_left (ell e) (show 1 ≤ k e + 1 by omega)
  have hn := heq j
  have hm := le_max4 n j
  exact ⟨by omega,
    le_min (le_min (hwind 0) (hwind 1)) (le_min (hwind 2) (hwind 3))⟩

private theorem charge_cutoff_nat (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) (β : Charge D) :
    β ∈ positiveChargeCutoff D hD (N : ℤ) ↔ (chargeEnergy D β).toNat ≤ N := by
  have hq := chargeEnergy_nonneg D hD β
  have hcast := Int.toNat_of_nonneg hq
  simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  omega

private theorem charge_cutoff_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (B R : ℕ) (hR : R ≤ B)
    (f : Charge D → ℂ) :
    (∑ β ∈ positiveChargeCutoff D hD (B : ℤ),
      if (chargeEnergy D β).toNat ≤ R then f β else 0) =
        ∑ β ∈ positiveChargeCutoff D hD (R : ℤ), f β := by
  classical
  have hsub : positiveChargeCutoff D hD (R : ℤ) ⊆ positiveChargeCutoff D hD (B : ℤ) := by
    intro β hβ
    rw [charge_cutoff_nat] at hβ ⊢
    omega
  calc
    _ = ∑ β ∈ positiveChargeCutoff D hD (R : ℤ),
        if (chargeEnergy D β).toNat ≤ R then f β else 0 := by
      apply (Finset.sum_subset hsub ?_).symm
      intro β _ hβ
      have hn : ¬ (chargeEnergy D β).toNat ≤ R := by
        rwa [← charge_cutoff_nat D hD R β]
      simp [hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro β hβ
      rw [if_pos ((charge_cutoff_nat D hD R β).mp hβ)]

private theorem pair_natural_parameters (N : ℕ) (q : ℤ) (h : 0 ≤ (N : ℤ) + q) :
    min N ((N : ℤ) + q).toNat = N - (-q).toNat ∧
      Nat.dist N ((N : ℤ) + q).toNat = q.natAbs := by
  by_cases hq : 0 ≤ q
  · have hδ : (-q).toNat = 0 := by omega
    have hq' : q = (q.toNat : ℤ) := by omega
    have hb : ((N : ℤ) + q).toNat = N + q.toNat := by omega
    rw [hδ, hb, Nat.sub_zero, Nat.min_eq_left (by omega),
      Nat.dist_eq_sub_of_le (by omega), hq', Int.natAbs_natCast]
    omega
  · have hδ : q = -((-q).toNat : ℤ) := by omega
    have hL : (-q).toNat ≤ N := by omega
    have hb : ((N : ℤ) + q).toNat = N - (-q).toNat := by omega
    rw [hb, Nat.min_eq_right (by omega), Nat.dist_eq_sub_of_le_right (by omega),
      hδ, Int.natAbs_neg, Int.natAbs_natCast]
    omega

private def pairEnergyCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (B N : ℕ) (q : ℤ) : ℂ := by
  classical
  exact if q = 0 then
    ∑ β ∈ positiveChargeCutoff D hD (B : ℤ), ∑ t : Fin (B + 1),
      if N = (chargeEnergy D β).toNat + t.1 then
        (Nat.card (IntegerFiber D t.1) : ℂ) *
          (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ)
      else 0
  else (q.natAbs : ℂ) * (D.G i j : ℂ) *
    ∑ β ∈ positiveChargeCutoff D hD (B : ℤ),
      ∑ k : Fin (B + 1), ∑ t : Fin (B + 1),
        if N = (chargeEnergy D β).toNat + t.1 + (-q).toNat + k.1 * q.natAbs then
          (Nat.card (IntegerFiber D t.1) : ℂ)
        else 0

private theorem pair_energy_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (B N : ℕ) (hN : N ≤ B) :
    signedPairCoefficient D hD i j (N : ℤ) 0 = pairEnergyCoefficient D hD i j B N 0 := by
  classical
  simp only [signedPairCoefficient, add_zero, Nat.cast_nonneg, and_self, ↓reduceIte,
    Int.toNat_natCast, pairEnergyCoefficient]
  have hs (β : Charge D) :
      (∑ t : Fin (B + 1), if N = (chargeEnergy D β).toNat + t.1 then
        (Nat.card (IntegerFiber D t.1) : ℂ) *
          (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ)
        else 0) =
      if (chargeEnergy D β).toNat ≤ N then
        (Nat.card (IntegerFiber D (N - (chargeEnergy D β).toNat)) : ℂ) *
          (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ)
      else 0 :=
    finite_residual_delta
      (fun t => (Nat.card (IntegerFiber D t) : ℂ) *
        (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ))
      N (chargeEnergy D β).toNat B hN
  simp_rw [hs]
  rw [charge_cutoff_sum D hD B N hN]
  apply Finset.sum_congr rfl
  intro β _
  unfold occupationMultiplicity
  ring

private theorem pair_energy_nonzero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (B N : ℕ) (hN : N ≤ B) (q : ℤ) (hq : q ≠ 0) :
    signedPairCoefficient D hD i j (N : ℤ) q = pairEnergyCoefficient D hD i j B N q := by
  classical
  have hL : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hcollapse (β : Charge D) :
      (∑ k : Fin (B + 1), ∑ t : Fin (B + 1),
        if N = (chargeEnergy D β).toNat + t.1 + (-q).toNat + k.1 * q.natAbs then
          (Nat.card (IntegerFiber D t.1) : ℂ) else 0) =
      if (chargeEnergy D β).toNat + (-q).toNat ≤ N then
        ∑ k ∈ Finset.range ((N - ((chargeEnergy D β).toNat + (-q).toNat)) / q.natAbs + 1),
          (Nat.card (IntegerFiber D (N - ((chargeEnergy D β).toNat + (-q).toNat) -
            k * q.natAbs)) : ℂ)
      else 0 := by
    have he (t k : ℕ) : (chargeEnergy D β).toNat + t + (-q).toNat + k * q.natAbs =
        ((chargeEnergy D β).toNat + (-q).toNat) + t + k * q.natAbs := by omega
    simp_rw [he]
    exact bounded_geometric_delta (fun t => (Nat.card (IntegerFiber D t) : ℂ))
      N ((chargeEnergy D β).toNat + (-q).toNat) q.natAbs B hL hN
  unfold pairEnergyCoefficient
  rw [if_neg hq]
  simp_rw [hcollapse]
  by_cases h : 0 ≤ (N : ℤ) + q
  · have hδ : (-q).toNat ≤ N := by omega
    have hp := pair_natural_parameters N q h
    have hne : N ≠ ((N : ℤ) + q).toNat := by omega
    simp only [signedPairCoefficient, Nat.cast_nonneg, h, and_self, ↓reduceIte,
      Int.toNat_natCast, hne, hp.1, hp.2]
    have hguard (β : Charge D) : (chargeEnergy D β).toNat + (-q).toNat ≤ N ↔
        (chargeEnergy D β).toNat ≤ N - (-q).toNat := by omega
    have hres (β : Charge D) : N - ((chargeEnergy D β).toNat + (-q).toNat) =
        N - (-q).toNat - (chargeEnergy D β).toNat := by omega
    simp_rw [hguard, hres]
    rw [charge_cutoff_sum D hD B (N - (-q).toNat) (by omega)]
    rfl
  · have hδ : N < (-q).toNat := by omega
    simp only [signedPairCoefficient, Nat.cast_nonneg, h, and_false, ↓reduceIte,
      Int.toNat_natCast]
    have hz : ∀ β : Charge D, ¬ (chargeEnergy D β).toNat + (-q).toNat ≤ N := by
      intro β
      omega
    simp [hz]

private theorem pair_energy_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (B N : ℕ) (hN : N ≤ B) (q : ℤ) :
    signedPairCoefficient D hD i j (N : ℤ) q = pairEnergyCoefficient D hD i j B N q := by
  by_cases hq : q = 0
  · subst q
    exact pair_energy_zero D hD i j B N hN
  · exact pair_energy_nonzero D hD i j B N hN q hq

private def edgePoint (M : PM4) (a : Four × Four) (ha : a ∈ M.edges) : edgeParam M := ⟨a, ha⟩

private def singleEdgeValueEquiv (M : PM4) (a : Four × Four) (h : M.edges = {a})
    (α : Type*) : (edgeParam M → α) ≃ α where
  toFun f := f (edgePoint M a (by rw [h]; simp))
  invFun x := fun _ => x
  left_inv f := by
    funext e
    have he : e.1 = a := by simpa [h] using e.2
    have hs : e = edgePoint M a (by rw [h]; simp) := Subtype.ext he
    rw [hs]
  right_inv _ := rfl

private def doubleEdgeValueEquiv (M : PM4) (a b : Four × Four)
    (h : M.edges = {a, b}) (hab : a ≠ b) (α : Type*) :
    (edgeParam M → α) ≃ α × α where
  toFun f := (f (edgePoint M a (by rw [h]; simp)), f (edgePoint M b (by rw [h]; simp)))
  invFun x e := if e.1 = a then x.1 else x.2
  left_inv f := by
    funext e
    have he : e.1 = a ∨ e.1 = b := by simpa [h] using e.2
    rcases he with he | he
    · have hs : e = edgePoint M a (by rw [h]; simp) := Subtype.ext he
      simp only [he, ↓reduceIte]
      rw [hs]
    · have hs : e = edgePoint M b (by rw [h]; simp) := Subtype.ext he
      have hne : e.1 ≠ a := by rw [he]; exact hab.symm
      simp only [hne, ↓reduceIte]
      rw [hs]
  right_inv x := by
    apply Prod.ext <;> simp [edgePoint, hab, hab.symm]

private theorem edge_univ_single (M : PM4) (a : Four × Four) (h : M.edges = {a}) :
    (Finset.univ : Finset (edgeParam M)) = {edgePoint M a (by rw [h]; simp)} := by
  classical
  apply Finset.ext
  intro e
  constructor
  · intro _
    apply Finset.mem_singleton.mpr
    have he : e.1 = a := by simpa only [h, Finset.mem_singleton] using e.2
    exact Subtype.ext he
  · intro _
    exact Finset.mem_univ e

private theorem edge_univ_double (M : PM4) (a b : Four × Four) (h : M.edges = {a, b}) :
    (Finset.univ : Finset (edgeParam M)) =
      {edgePoint M a (by rw [h]; simp), edgePoint M b (by rw [h]; simp)} := by
  classical
  ext e
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have he : e.1 = a ∨ e.1 = b := by simpa [h] using e.2
  exact he.elim (fun ha => Or.inl (Subtype.ext ha)) (fun hb => Or.inr (Subtype.ext hb))

private theorem pm4_sum (f : PM4 → ℂ) :
    (∑ M : PM4, f M) = f .empty + f .p12 + f .p13 + f .p14 + f .p23 + f .p24 + f .p34 +
      f .p12_34 + f .p13_24 + f .p14_23 := by
  classical
  have hu : (Finset.univ : Finset PM4) =
      {.empty, .p12, .p13, .p14, .p23, .p24, .p34, .p12_34, .p13_24, .p14_23} := by decide
  rw [hu]
  simp <;> ring

private def unpairedTable : PM4 → Finset Four
  | .empty => Finset.univ
  | .p12 => {2, 3}
  | .p13 => {1, 3}
  | .p14 => {1, 2}
  | .p23 => {0, 3}
  | .p24 => {0, 2}
  | .p34 => {0, 1}
  | .p12_34 | .p13_24 | .p14_23 => ∅

private theorem unpaired_table : ∀ M : PM4, M.unpaired = unpairedTable M := by decide


private def channelMate : Fin 3 → Four := ![1, 2, 3]
private def channelRest : Fin 3 → Four × Four := ![(2, 3), (1, 3), (1, 2)]
private def channelSingle : Fin 3 → PM4 := ![.p12, .p13, .p14]
private def channelDouble : Fin 3 → PM4 := ![.p12_34, .p13_24, .p14_23]
private def channelEdge (c : Fin 3) : Four × Four := (0, channelMate c)

private theorem channel_single_edges : ∀ c : Fin 3,
    (channelSingle c).edges = {channelEdge c} := by decide

private theorem channel_double_edges : ∀ c : Fin 3,
    (channelDouble c).edges = {channelEdge c, channelRest c} := by decide

private theorem channel_edges_distinct : ∀ c : Fin 3, channelEdge c ≠ channelRest c := by decide

private theorem channel_single_unpaired : ∀ c : Fin 3,
    (channelSingle c).unpaired = {(channelRest c).1, (channelRest c).2} := by decide

private theorem channel_double_unpaired : ∀ c : Fin 3,
    (channelDouble c).unpaired = ∅ := by decide

private theorem compatible_channel_single (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    modeCompatible n (channelSingle c) ↔
      currentMode n 0 + currentMode n (channelMate c) = 0 ∧
        currentMode n (channelRest c).1 = 0 := by
  classical
  fin_cases c <;>
    simp [channelSingle, channelMate, channelRest, modeCompatible, edgeParam,
      unpaired_table, unpairedTable, PM4.edges, e12, e13, e14, currentMode] <;> omega

private theorem compatible_channel_double (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    modeCompatible n (channelDouble c) ↔
      currentMode n 0 + currentMode n (channelMate c) = 0 ∧
        currentMode n (channelRest c).1 ≠ 0 := by
  classical
  fin_cases c <;>
    simp [channelDouble, channelMate, channelRest, modeCompatible, edgeParam,
      unpaired_table, unpairedTable, PM4.edges, e12, e13, e14, e23, e24, e34, currentMode] <;> omega

private def modeEnergyWeight (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (M : PM4) (k : edgeParam M → ℕ) (t : ℕ) : ℂ := by
  classical
  exact if modeCompatible n M ∧ n 0 = (chargeEnergy D β).toNat + t +
      creationDelay n M + windingEnergy n M k then
    (Nat.card (IntegerFiber D t) : ℂ) *
      (∏ a ∈ M.unpaired, (bilinear D (unitCharge D (i a)) β : ℂ)) *
        ∏ e : edgeParam M, (modeFrequency n e : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)
  else 0

private def matchingEnergyCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (B : ℕ) (M : PM4) : ℂ := by
  classical
  exact ∑ β ∈ positiveChargeCutoff D hD (B : ℤ),
    ∑ k : edgeParam M → Fin (B + 1), ∑ t : Fin (B + 1),
      modeEnergyWeight D i n β M (fun e => (k e).1) t.1

private theorem ordered_matching_energy (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    orderedFourCurrentCoefficient D hD i n =
      ∑ M : PM4, matchingEnergyCoefficient D hD i n (min4 n) M := by
  classical
  unfold orderedFourCurrentCoefficient matchingEnergyCoefficient orderedChargeWeight modeEnergyWeight
  exact Finset.sum_comm

private def channelEnergyCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (c : Fin 3) : ℂ :=
  let ell := n 1 - n 0
  contraction D (i 0) (i (channelMate c)) ell (currentMode n (channelMate c)) *
    ∑ a : Fin (n 0 + 1), if a.1 * ell ≤ n 0 then
      pairEnergyCoefficient D hD (i (channelRest c).1) (i (channelRest c).2)
        (n 0) (n 0 - a.1 * ell) (currentMode n (channelRest c).1)
    else 0

private theorem leading_frequency (n : Four → ℕ) (h : n 0 < n 1) :
    currentMode n 0 = ((n 1 - n 0 : ℕ) : ℤ) := by
  dsimp [currentMode]
  omega

private theorem mode_creation_delay (m : ℤ) :
    (if m < 0 then m.natAbs else 0) = (-m).toNat := by
  by_cases h : m < 0
  · have he : m = -((-m).toNat : ℤ) := by omega
    rw [if_pos h, he, Int.natAbs_neg, Int.natAbs_natCast]
    omega
  · rw [if_neg h]
    omega

private theorem channel_rest_distinct : ∀ c : Fin 3, (channelRest c).1 ≠ (channelRest c).2 := by decide

private theorem single_mode_energy_weight (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (h : n 0 < n 1) (c : Fin 3) (a t : ℕ) :
    modeEnergyWeight D i n β (channelSingle c) (fun _ => a) t =
      if (currentMode n 0 + currentMode n (channelMate c) = 0 ∧
          currentMode n (channelRest c).1 = 0) ∧
        n 0 = (chargeEnergy D β).toNat + t + a * (n 1 - n 0) then
        ((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ) *
          ((Nat.card (IntegerFiber D t) : ℂ) *
            (bilinear D (unitCharge D (i (channelRest c).1)) β : ℂ) *
            (bilinear D (unitCharge D (i (channelRest c).2)) β : ℂ))
      else 0 := by
  classical
  let M := channelSingle c
  have hu := edge_univ_single M (channelEdge c) (channel_single_edges c)
  have hm : ¬ currentMode n 0 < 0 := by rw [leading_frequency n h]; omega
  have hd : creationDelay n M = 0 := by
    unfold creationDelay
    rw [hu]
    simp only [Finset.sum_singleton, edgePoint, channelEdge]
    rw [if_neg hm]
  have hw : windingEnergy n M (fun _ => a) = a * (n 1 - n 0) := by
    unfold windingEnergy
    rw [hu]
    simp only [Finset.sum_singleton, modeFrequency, edgePoint, channelEdge]
    rw [leading_frequency n h, Int.natAbs_natCast, Nat.mul_comm]
  have hp : (∏ e : edgeParam M, (modeFrequency n e : ℂ) *
      (D.G (i e.1.1) (i e.1.2) : ℂ)) =
      ((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ) := by
    rw [hu]
    simp only [Finset.prod_singleton, modeFrequency, edgePoint, channelEdge]
    rw [leading_frequency n h, Int.natAbs_natCast]
  have hup : (∏ b ∈ M.unpaired, (bilinear D (unitCharge D (i b)) β : ℂ)) =
      (bilinear D (unitCharge D (i (channelRest c).1)) β : ℂ) *
        (bilinear D (unitCharge D (i (channelRest c).2)) β : ℂ) := by
    rw [channel_single_unpaired]
    simp [channel_rest_distinct c]
  unfold modeEnergyWeight
  change (if modeCompatible n M ∧ n 0 = (chargeEnergy D β).toNat + t +
      creationDelay n M + windingEnergy n M (fun _ => a) then
    (Nat.card (IntegerFiber D t) : ℂ) *
      (∏ b ∈ M.unpaired, (bilinear D (unitCharge D (i b)) β : ℂ)) *
      (∏ e : edgeParam M, (modeFrequency n e : ℂ) *
        (D.G (i e.1.1) (i e.1.2) : ℂ)) else 0) = _
  rw [compatible_channel_single n h c, hd, hw, hp, hup]
  simp only [Nat.add_zero]
  split_ifs <;> ring

private theorem double_mode_energy_weight (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (h : n 0 < n 1) (c : Fin 3) (a b t : ℕ) :
    modeEnergyWeight D i n β (channelDouble c)
      (fun e => if e.1 = channelEdge c then a else b) t =
      if (currentMode n 0 + currentMode n (channelMate c) = 0 ∧
          currentMode n (channelRest c).1 ≠ 0) ∧
        n 0 = (chargeEnergy D β).toNat + t + (-currentMode n (channelRest c).1).toNat +
          a * (n 1 - n 0) + b * (currentMode n (channelRest c).1).natAbs then
        (((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ)) *
          (((currentMode n (channelRest c).1).natAbs : ℂ) *
            (D.G (i (channelRest c).1) (i (channelRest c).2) : ℂ)) *
          (Nat.card (IntegerFiber D t) : ℂ)
      else 0 := by
  classical
  let M := channelDouble c
  let ea := edgePoint M (channelEdge c) (by rw [channel_double_edges]; simp)
  let eb := edgePoint M (channelRest c) (by rw [channel_double_edges]; simp)
  have hu := edge_univ_double M (channelEdge c) (channelRest c) (channel_double_edges c)
  have hne : ea ≠ eb := by
    intro he
    exact channel_edges_distinct c (congrArg Subtype.val he)
  have hm : ¬ currentMode n 0 < 0 := by rw [leading_frequency n h]; omega
  have hd : creationDelay n M = (-currentMode n (channelRest c).1).toNat := by
    unfold creationDelay
    rw [hu]
    simp only [show edgePoint M (channelEdge c) _ = ea from rfl,
      show edgePoint M (channelRest c) _ = eb from rfl]
    rw [Finset.sum_pair hne]
    change (if currentMode n 0 < 0 then (currentMode n 0).natAbs else 0) +
      (if currentMode n (channelRest c).1 < 0 then (currentMode n (channelRest c).1).natAbs else 0) = _
    rw [if_neg hm, zero_add, mode_creation_delay]
  have hw : windingEnergy n M (fun e => if e.1 = channelEdge c then a else b) =
      a * (n 1 - n 0) + b * (currentMode n (channelRest c).1).natAbs := by
    unfold windingEnergy
    rw [hu, Finset.sum_pair hne]
    dsimp only [ea, eb, edgePoint, modeFrequency]
    rw [if_pos rfl, if_neg (channel_edges_distinct c).symm]
    change (currentMode n 0).natAbs * a +
      (currentMode n (channelRest c).1).natAbs * b = _
    rw [leading_frequency n h, Int.natAbs_natCast]
    ring
  have hp : (∏ e : edgeParam M, (modeFrequency n e : ℂ) *
      (D.G (i e.1.1) (i e.1.2) : ℂ)) =
      (((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ)) *
        (((currentMode n (channelRest c).1).natAbs : ℂ) *
          (D.G (i (channelRest c).1) (i (channelRest c).2) : ℂ)) := by
    rw [hu, Finset.prod_pair hne]
    change ((currentMode n 0).natAbs : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ) *
      (((currentMode n (channelRest c).1).natAbs : ℂ) *
        (D.G (i (channelRest c).1) (i (channelRest c).2) : ℂ)) = _
    rw [leading_frequency n h, Int.natAbs_natCast]
  have hup : (∏ d ∈ M.unpaired, (bilinear D (unitCharge D (i d)) β : ℂ)) = 1 := by
    rw [channel_double_unpaired]
    simp
  unfold modeEnergyWeight
  change (if modeCompatible n M ∧ n 0 = (chargeEnergy D β).toNat + t +
      creationDelay n M + windingEnergy n M (fun e => if e.1 = channelEdge c then a else b) then
    (Nat.card (IntegerFiber D t) : ℂ) *
      (∏ d ∈ M.unpaired, (bilinear D (unitCharge D (i d)) β : ℂ)) *
      (∏ e : edgeParam M, (modeFrequency n e : ℂ) *
        (D.G (i e.1.1) (i e.1.2) : ℂ)) else 0) = _
  rw [compatible_channel_double n h c, hd, hw, hp, hup, mul_one]
  have he : (n 0 = (chargeEnergy D β).toNat + t + (-currentMode n (channelRest c).1).toNat +
      (a * (n 1 - n 0) + b * (currentMode n (channelRest c).1).natAbs)) ↔
      n 0 = (chargeEnergy D β).toNat + t + (-currentMode n (channelRest c).1).toNat +
        a * (n 1 - n 0) + b * (currentMode n (channelRest c).1).natAbs := by omega
  simp only [he]
  split_ifs <;> ring


private theorem mode_energy_support (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (M : PM4) (k : edgeParam M → ℕ) (t : ℕ)
    (hz : modeEnergyWeight D i n β M k t ≠ 0) :
    (chargeEnergy D β).toNat ≤ min4 n ∧ t ≤ min4 n ∧ ∀ e, k e ≤ min4 n := by
  classical
  have hh : modeCompatible n M ∧ n 0 = (chargeEnergy D β).toNat + t +
      creationDelay n M + windingEnergy n M k := by
    by_contra hn
    exact hz (by simp [modeEnergyWeight, hn])
  have hb := matching_parameter_bounds n (chargeEnergy D β).toNat t M
    (modeFrequency n) (modeSide n) k (compatible_matching_modes n M hh.1).1
    ((matching_energy_transport n _ _ M k hh.1).mpr hh.2)
  exact ⟨hb.1, hb.2.1, fun e => (hb.2.2 e).2⟩

private theorem bounded_tuple_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C : ℕ) (hBC : B ≤ C) (f : (ι → ℕ) → ℕ → ℂ)
    (hs : ∀ k t, f k t ≠ 0 → t ≤ B ∧ ∀ e, k e ≤ B) :
    (∑ k : ι → Fin (B + 1), ∑ t : Fin (B + 1), f (fun e => (k e).1) t.1) =
      ∑ k : ι → Fin (C + 1), ∑ t : Fin (C + 1), f (fun e => (k e).1) t.1 := by
  classical
  let emb : ((ι → Fin (B + 1)) × Fin (B + 1)) →
      ((ι → Fin (C + 1)) × Fin (C + 1)) :=
    fun x => (fun e => Fin.castLE (Nat.succ_le_succ hBC) (x.1 e),
      Fin.castLE (Nat.succ_le_succ hBC) x.2)
  have hinj : Function.Injective emb := by
    intro x y h
    apply Prod.ext
    · funext e
      apply Fin.ext
      exact congrArg (fun z => (z.1 e).1) h
    · apply Fin.ext
      exact congrArg (fun z => z.2.1) h
  have hz (x : (ι → Fin (C + 1)) × Fin (C + 1)) (hx : x ∉ Set.range emb) :
      f (fun e => (x.1 e).1) x.2.1 = 0 := by
    by_contra hn
    have hb := hs _ _ hn
    apply hx
    refine ⟨((fun e => ⟨(x.1 e).1, Nat.lt_succ_of_le (hb.2 e)⟩),
      ⟨x.2.1, Nat.lt_succ_of_le hb.1⟩), ?_⟩
    apply Prod.ext
    · funext e
      apply Fin.ext
      rfl
    · apply Fin.ext
      rfl
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_of_injective emb hinj
      (fun x => f (fun e => (x.1 e).1) x.2.1)
      (fun x => f (fun e => (x.1 e).1) x.2.1) hz (fun _ => rfl))

private theorem min4_le (n : Four → ℕ) (a : Four) : min4 n ≤ n a := by
  fin_cases a <;> dsimp [min4] <;> omega

private theorem matching_energy_enlarge (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (M : PM4) :
    matchingEnergyCoefficient D hD i n (min4 n) M =
      matchingEnergyCoefficient D hD i n (n 0) M := by
  classical
  unfold matchingEnergyCoefficient
  have hs (β : Charge D) :
      (∑ k : edgeParam M → Fin (min4 n + 1), ∑ t : Fin (min4 n + 1),
        modeEnergyWeight D i n β M (fun e => (k e).1) t.1) =
      ∑ k : edgeParam M → Fin (n 0 + 1), ∑ t : Fin (n 0 + 1),
        modeEnergyWeight D i n β M (fun e => (k e).1) t.1 := by
    apply bounded_tuple_sum (min4 n) (n 0) (min4_le n 0)
    intro k t hz
    have hb := mode_energy_support D i n β M k t hz
    exact hb.2
  simp_rw [hs]
  have hsub : positiveChargeCutoff D hD (min4 n : ℤ) ⊆
      positiveChargeCutoff D hD (n 0 : ℤ) := by
    intro β hβ
    rw [charge_cutoff_nat] at hβ ⊢
    exact hβ.trans (min4_le n 0)
  apply Finset.sum_subset hsub
  intro β _ hβ
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro t _
  by_contra hz
  have hb := (mode_energy_support D i n β M _ _ hz).1
  exact hβ ((charge_cutoff_nat D hD _ β).mpr hb)

private theorem sum_single_edge (M : PM4) (a : Four × Four) (ha : M.edges = {a})
    (α : Type*) [Fintype α] (f : (edgeParam M → α) → ℂ) :
    (∑ k, f k) = ∑ x : α, f (fun _ => x) := by
  exact ((singleEdgeValueEquiv M a ha α).symm.sum_comp f).symm

private theorem sum_double_edge (M : PM4) (a b : Four × Four)
    (ha : M.edges = {a, b}) (hab : a ≠ b)
    (α : Type*) [Fintype α] (f : (edgeParam M → α) → ℂ) :
    (∑ k, f k) = ∑ x : α, ∑ y : α, f (fun e => if e.1 = a then x else y) := by
  have h := ((doubleEdgeValueEquiv M a b ha hab α).symm.sum_comp f).symm
  simpa only [Fintype.sum_prod_type, doubleEdgeValueEquiv, Equiv.coe_fn_symm_mk] using h

private theorem matching_single_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    matchingEnergyCoefficient D hD i n (n 0) (channelSingle c) =
      ∑ β ∈ positiveChargeCutoff D hD (n 0 : ℤ),
        ∑ a : Fin (n 0 + 1), ∑ t : Fin (n 0 + 1),
          if (currentMode n 0 + currentMode n (channelMate c) = 0 ∧
              currentMode n (channelRest c).1 = 0) ∧
            n 0 = (chargeEnergy D β).toNat + t.1 + a.1 * (n 1 - n 0) then
            ((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ) *
              ((Nat.card (IntegerFiber D t.1) : ℂ) *
                (bilinear D (unitCharge D (i (channelRest c).1)) β : ℂ) *
                (bilinear D (unitCharge D (i (channelRest c).2)) β : ℂ))
          else 0 := by
  classical
  unfold matchingEnergyCoefficient
  apply Finset.sum_congr rfl
  intro β _
  rw [sum_single_edge (channelSingle c) (channelEdge c) (channel_single_edges c)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  exact single_mode_energy_weight D i n β h c a.1 t.1

private theorem matching_double_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    matchingEnergyCoefficient D hD i n (n 0) (channelDouble c) =
      ∑ β ∈ positiveChargeCutoff D hD (n 0 : ℤ),
        ∑ a : Fin (n 0 + 1), ∑ b : Fin (n 0 + 1), ∑ t : Fin (n 0 + 1),
          if (currentMode n 0 + currentMode n (channelMate c) = 0 ∧
              currentMode n (channelRest c).1 ≠ 0) ∧
            n 0 = (chargeEnergy D β).toNat + t.1 +
              (-currentMode n (channelRest c).1).toNat + a.1 * (n 1 - n 0) +
                b.1 * (currentMode n (channelRest c).1).natAbs then
            (((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ)) *
              (((currentMode n (channelRest c).1).natAbs : ℂ) *
                (D.G (i (channelRest c).1) (i (channelRest c).2) : ℂ)) *
              (Nat.card (IntegerFiber D t.1) : ℂ)
          else 0 := by
  classical
  unfold matchingEnergyCoefficient
  apply Finset.sum_congr rfl
  intro β _
  rw [sum_double_edge (channelDouble c) (channelEdge c) (channelRest c)
    (channel_double_edges c) (channel_edges_distinct c)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  simpa only [apply_ite] using double_mode_energy_weight D i n β h c a.1 b.1 t.1

private theorem matching_channel_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    matchingEnergyCoefficient D hD i n (n 0) (channelSingle c) +
      matchingEnergyCoefficient D hD i n (n 0) (channelDouble c) =
        channelEnergyCoefficient D hD i n c := by
  classical
  have hc : contraction D (i 0) (i (channelMate c)) ((n 1 - n 0 : ℕ) : ℤ)
      (currentMode n (channelMate c)) =
      if currentMode n 0 + currentMode n (channelMate c) = 0 then
        ((n 1 - n 0 : ℕ) : ℂ) * (D.G (i 0) (i (channelMate c)) : ℂ) else 0 := by
    rw [leading_frequency n h]
    simp only [contraction, Int.cast_natCast]
  rw [matching_single_sum D hD i n h c, matching_double_sum D hD i n h c]
  unfold channelEnergyCoefficient
  dsimp only
  rw [hc]
  by_cases hm : currentMode n 0 + currentMode n (channelMate c) = 0
  · rw [if_pos hm]
    by_cases hq : currentMode n (channelRest c).1 = 0
    · simp only [hm, hq, true_and, ne_eq, not_true_eq_false, false_and,
        ↓reduceIte, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.1 * (n 1 - n 0) ≤ n 0
      · rw [if_pos ha]
        simp only [pairEnergyCoefficient, hq, ↓reduceIte]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        apply Finset.sum_congr rfl
        intro t _
        have he : n 0 = (chargeEnergy D β).toNat + t.1 + a.1 * (n 1 - n 0) ↔
            n 0 - a.1 * (n 1 - n 0) = (chargeEnergy D β).toNat + t.1 := by omega
        split_ifs with hleft hright hright
        · ring
        · exact False.elim (hright (he.mp hleft))
        · exact False.elim (hleft (he.mpr hright))
        · ring
      · rw [if_neg ha, mul_zero]
        apply Finset.sum_eq_zero
        intro β _
        apply Finset.sum_eq_zero
        intro t _
        have he : n 0 ≠ (chargeEnergy D β).toNat + t.1 + a.1 * (n 1 - n 0) := by omega
        exact if_neg he
    · simp only [hm, hq, true_and, ne_eq, not_false_eq_true, false_and,
        ↓reduceIte, Finset.sum_const_zero, zero_add]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.1 * (n 1 - n 0) ≤ n 0
      · rw [if_pos ha]
        simp only [pairEnergyCoefficient, hq, ↓reduceIte]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro t _
        have he : n 0 = (chargeEnergy D β).toNat + t.1 +
            (-currentMode n (channelRest c).1).toNat + a.1 * (n 1 - n 0) +
              b.1 * (currentMode n (channelRest c).1).natAbs ↔
            n 0 - a.1 * (n 1 - n 0) = (chargeEnergy D β).toNat + t.1 +
              (-currentMode n (channelRest c).1).toNat +
                b.1 * (currentMode n (channelRest c).1).natAbs := by omega
        split_ifs with hleft hright hright
        · ring
        · exact False.elim (hright (he.mp hleft))
        · exact False.elim (hleft (he.mpr hright))
        · ring
      · rw [if_neg ha, mul_zero]
        apply Finset.sum_eq_zero
        intro β _
        apply Finset.sum_eq_zero
        intro b _
        apply Finset.sum_eq_zero
        intro t _
        have he : n 0 ≠ (chargeEnergy D β).toNat + t.1 +
            (-currentMode n (channelRest c).1).toNat + a.1 * (n 1 - n 0) +
              b.1 * (currentMode n (channelRest c).1).natAbs := by omega
        exact if_neg he
  · simp only [hm, false_and, ↓reduceIte, Finset.sum_const_zero, zero_add, zero_mul]

private theorem matching_energy_incompatible (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (B : ℕ) (M : PM4)
    (hM : ¬ modeCompatible n M) : matchingEnergyCoefficient D hD i n B M = 0 := by
  classical
  simp [matchingEnergyCoefficient, modeEnergyWeight, hM]

private theorem ordered_positive_channels (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) :
    orderedFourCurrentCoefficient D hD i n =
      ∑ c : Fin 3, channelEnergyCoefficient D hD i n c := by
  classical
  rw [ordered_matching_energy]
  simp_rw [matching_energy_enlarge]
  have hz (M : PM4) (hu : (0 : Four) ∈ M.unpaired) :
      matchingEnergyCoefficient D hD i n (n 0) M = 0 := by
    apply matching_energy_incompatible
    intro hc
    have hm := hc.1 0 hu
    rw [leading_frequency n h] at hm
    omega
  rw [pm4_sum, hz .empty (by decide), hz .p23 (by decide),
    hz .p24 (by decide), hz .p34 (by decide)]
  have hc0 := matching_channel_sum D hD i n h 0
  have hc1 := matching_channel_sum D hD i n h 1
  have hc2 := matching_channel_sum D hD i n h 2
  change matchingEnergyCoefficient D hD i n (n 0) .p12 +
    matchingEnergyCoefficient D hD i n (n 0) .p12_34 = _ at hc0
  change matchingEnergyCoefficient D hD i n (n 0) .p13 +
    matchingEnergyCoefficient D hD i n (n 0) .p13_24 = _ at hc1
  change matchingEnergyCoefficient D hD i n (n 0) .p14 +
    matchingEnergyCoefficient D hD i n (n 0) .p14_23 = _ at hc2
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  change _ = channelEnergyCoefficient D hD i n 0 +
    (channelEnergyCoefficient D hD i n 1 + channelEnergyCoefficient D hD i n 2)
  linear_combination hc0 + hc1 + hc2

private theorem channel_energy_original (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) (c : Fin 3) :
    channelEnergyCoefficient D hD i n c =
      contraction D (i 0) (i (channelMate c)) ((n 1 - n 0 : ℕ) : ℤ) (currentMode n (channelMate c)) *
        ∑ a ∈ Finset.range (n 0 / (n 1 - n 0) + 1),
          signedPairCoefficient D hD (i (channelRest c).1) (i (channelRest c).2)
            ((n 0 : ℤ) - (a : ℤ) * ((n 1 - n 0 : ℕ) : ℤ)) (currentMode n (channelRest c).1) := by
  classical
  unfold channelEnergyCoefficient
  dsimp only
  congr 1
  rw [← bounded_division_sum
    (fun a => signedPairCoefficient D hD (i (channelRest c).1) (i (channelRest c).2)
      ((n 0 : ℤ) - (a : ℤ) * ((n 1 - n 0 : ℕ) : ℤ)) (currentMode n (channelRest c).1))
    (n 0) (n 1 - n 0) (n 0) (by omega) le_rfl]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.1 * (n 1 - n 0) ≤ n 0
  · rw [if_pos ha, if_pos ha]
    have he : ((n 0 - a.1 * (n 1 - n 0) : ℕ) : ℤ) =
        (n 0 : ℤ) - (a.1 : ℤ) * ((n 1 - n 0 : ℕ) : ℤ) := by
      rw [Nat.cast_sub ha, Nat.cast_mul]
    rw [← he]
    exact (pair_energy_coefficient D hD _ _ _ _ (by omega) _).symm
  · rw [if_neg ha, if_neg ha]

private theorem original_four_positive_matching (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) :
    actualFourCurrentCycleTrace D hD i n = boundedFourCurrentCoefficient D hD i n := by
  classical
  rw [bounded_coefficient_ordered, ordered_positive_channels D hD i n h]
  simp_rw [channel_energy_original D hD i n h, Finset.mul_sum]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simpa [channelMate, channelRest, currentMode, add_assoc] using
    original_four_finite_coefficient D hD i n h

/-- The bounded labeled partial-matching formula for the original finite four-current cycle
on every full natural energy-grade quadruple. -/
theorem actual_four_current_grade_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    actualFourCurrentCycleTrace D hD i n = boundedFourCurrentCoefficient D hD i n := by
  by_cases h0 : n 0 < n 1
  · exact original_four_positive_matching D hD i n h0
  by_cases h1 : n 1 < n 2
  · rw [original_four_rotate, bounded_coefficient_rotation]
    exact original_four_positive_matching D hD (rotateFour i) (rotateFour n) h1
  by_cases h2 : n 2 < n 3
  · rw [original_four_rotate, original_four_rotate D hD (rotateFour i),
      bounded_coefficient_rotation, bounded_coefficient_rotation D hD (rotateFour i)]
    exact original_four_positive_matching D hD (rotateFour (rotateFour i))
      (rotateFour (rotateFour n)) h2
  by_cases h3 : n 3 < n 0
  · rw [original_four_rotate, original_four_rotate D hD (rotateFour i),
      original_four_rotate D hD (rotateFour (rotateFour i)),
      bounded_coefficient_rotation, bounded_coefficient_rotation D hD (rotateFour i),
      bounded_coefficient_rotation D hD (rotateFour (rotateFour i))]
    exact original_four_positive_matching D hD (rotateFour (rotateFour (rotateFour i)))
      (rotateFour (rotateFour (rotateFour n))) h3
  have hn := no_increase_constant n h0 h1 h2 h3
  rw [hn]
  exact original_four_constant_matching D hD i (n 0)


end D5.S3.VertexAlgebra.LatticeFourCurrentTrace
