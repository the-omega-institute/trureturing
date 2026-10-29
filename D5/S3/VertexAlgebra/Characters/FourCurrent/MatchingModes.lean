/- GID: D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact labeled matching modes and the bounded ordered four-current coefficient. -/

import D5.S3.VertexAlgebra.Characters.FourCurrent.TraceRecurrence

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

open private edgeParam arcMem sideMem min4 max4 matchingShift
  gradeShift chargeWeight gradeTrace contraction pair_trace_signed original_four_finite_sum edges_ordered
  le_max4
  from D5.S3.VertexAlgebra.Characters.FourCurrent.TraceRecurrence

private def signedPairCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q : ℤ) : ℂ := by
  classical
  let a := N.toNat
  let b := (N + q).toNat
  exact if 0 ≤ N ∧ 0 ≤ N + q then
    if a = b then
      ∑ β ∈ positiveChargeCutoff D hD (a : ℤ),
        (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ) *
          occupationMultiplicity D (a - (chargeEnergy D β).toNat)
    else
      (Nat.dist a b : ℂ) * (D.G i j : ℂ) *
        ∑ β ∈ positiveChargeCutoff D hD ((min a b : ℕ) : ℤ),
          ∑ k ∈ Finset.range ((min a b - (chargeEnergy D β).toNat) / Nat.dist a b + 1),
            occupationMultiplicity D (min a b - (chargeEnergy D β).toNat - k * Nat.dist a b)
  else 0

private theorem pair_trace_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q r : ℤ) (hr : q + r = 0) :
    gradeTrace D hD N (neutralMode D i q * neutralMode D j r) =
      signedPairCoefficient D hD i j N q := by
  rw [pair_trace_signed D hD i j N q r hr]
  simp only [signedPairCoefficient, actual_two_current_grade_trace]

private theorem contracted_pair_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j k s : Fin D.rank) (m p q r N : ℤ) (ht : m + (p + (q + r)) = 0) :
    contraction D i j m p * gradeTrace D hD N (neutralMode D k q * neutralMode D s r) =
      contraction D i j m p * signedPairCoefficient D hD k s N q := by
  by_cases h : m + p = 0
  · rw [pair_trace_coefficient D hD k s N q r (by omega)]
  · simp [contraction, h]

private theorem original_four_finite_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) :
    let ell := n 1 - n 0
    let p := (n 2 : ℤ) - n 1
    let q := (n 3 : ℤ) - n 2
    let r := (n 0 : ℤ) - n 3
    actualFourCurrentCycleTrace D hD i n =
      ∑ a ∈ Finset.range (n 0 / ell + 1),
        (contraction D (i 0) (i 1) ell p *
            signedPairCoefficient D hD (i 2) (i 3) ((n 0 : ℤ) - (a : ℤ) * ell) q +
          contraction D (i 0) (i 2) ell q *
            signedPairCoefficient D hD (i 1) (i 3) ((n 0 : ℤ) - (a : ℤ) * ell) p +
          contraction D (i 0) (i 3) ell r *
            signedPairCoefficient D hD (i 1) (i 2) ((n 0 : ℤ) - (a : ℤ) * ell) p) := by
  dsimp only
  rw [original_four_finite_sum D hD i n h]
  apply Finset.sum_congr rfl
  intro a ha
  rw [contracted_pair_coefficient D hD (i 0) (i 1) (i 2) (i 3) _ _ _ _ _ (by omega),
    contracted_pair_coefficient D hD (i 0) (i 2) (i 1) (i 3) _ _ _ _ _ (by omega),
    contracted_pair_coefficient D hD (i 0) (i 3) (i 1) (i 2) _ _ _ _ _ (by omega)]


private def zeroFourCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (N : ℕ) : ℂ :=
  ∑ β ∈ positiveChargeCutoff D hD (N : ℤ),
    (∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ)) *
      (Nat.card (IntegerFiber D (N - (chargeEnergy D β).toNat)) : ℂ)

private theorem no_increase_constant (n : Four → ℕ)
    (h0 : ¬ n 0 < n 1) (h1 : ¬ n 1 < n 2)
    (h2 : ¬ n 2 < n 3) (h3 : ¬ n 3 < n 0) :
    n = fun _ => n 0 := by
  have h10 : n 1 = n 0 := by omega
  have h20 : n 2 = n 0 := by omega
  have h30 : n 3 = n 0 := by omega
  funext a
  fin_cases a
  · rfl
  · exact h10
  · exact h20
  · exact h30

private def currentMode (n : Four → ℕ) (a : Four) : ℤ :=
  (n (a + 1) : ℤ) - n a

private def sideIndicator (ε : Fin 2) (e : Four × Four) (a : Four) : ℤ :=
  if sideMem ε e a then 1 else 0

private def orientation (ε : Fin 2) : ℤ := if ε.1 = 0 then 1 else -1

private def orientedFrequency (ell : ℕ) (ε : Fin 2) : ℤ := (ell : ℤ) * orientation ε

private def matchingMode (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (a : Four) : ℤ := by
  classical
  exact ∑ e : edgeParam M,
    ((if a = e.1.1 then 1 else 0) - (if a = e.1.2 then 1 else 0)) *
      orientedFrequency (ell e) (ε e)

private theorem side_indicator_step : ∀ (e : Four × Four), e.1.1 < e.2.1 →
    ∀ (ε : Fin 2) (a : Four),
    sideIndicator ε e (a + 1) - sideIndicator ε e a =
      ((if a = e.1 then 1 else 0) - (if a = e.2 then 1 else 0)) * orientation ε := by
  decide

private theorem matching_shift_mode (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) (a : Four) :
    (matchingShift M ell ε k (a + 1) : ℤ) - matchingShift M ell ε k a =
      matchingMode M ell ε a := by
  classical
  unfold matchingShift matchingMode
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hs := side_indicator_step e.1 (edges_ordered M e.1 e.2) (ε e) a
  change (ell e : ℤ) * ((k e : ℤ) + sideIndicator (ε e) e.1 (a + 1)) -
      (ell e : ℤ) * ((k e : ℤ) + sideIndicator (ε e) e.1 a) = _
  calc
    _ = (ell e : ℤ) *
        (sideIndicator (ε e) e.1 (a + 1) - sideIndicator (ε e) e.1 a) := by ring
    _ = _ := by rw [hs]; unfold orientedFrequency; ring

private theorem matching_equations_iff (n : Four → ℕ) (Q t : ℕ) (M : PM4)
    (ell : edgeParam M → ℕ) (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) :
    (∀ a, n a = Q + t + matchingShift M ell ε k a) ↔
      n 0 = Q + t + matchingShift M ell ε k 0 ∧
        ∀ a, currentMode n a = matchingMode M ell ε a := by
  constructor
  · intro h
    refine ⟨h 0, ?_⟩
    intro a
    rw [← matching_shift_mode M ell ε k a]
    dsimp only [currentMode]
    rw [h (a + 1), h a]
    push_cast
    ring
  · rintro ⟨h0, hm⟩
    have h1 := hm 0
    have h2 := hm 1
    have h3 := hm 2
    rw [← matching_shift_mode M ell ε k 0] at h1
    rw [← matching_shift_mode M ell ε k 1] at h2
    rw [← matching_shift_mode M ell ε k 2] at h3
    norm_num [currentMode] at h1 h2 h3
    have hn1 : n 1 = Q + t + matchingShift M ell ε k 1 := by omega
    have hn2 : n 2 = Q + t + matchingShift M ell ε k 2 := by omega
    have hn3 : n 3 = Q + t + matchingShift M ell ε k 3 := by omega
    intro a
    fin_cases a
    · exact h0
    · exact hn1
    · exact hn2
    · exact hn3

private theorem matching_edges_disjoint : ∀ (M : PM4) (e f : Four × Four),
    e ∈ M.edges → f ∈ M.edges → e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by decide

private theorem matching_mode_first (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (e : edgeParam M) :
    matchingMode M ell ε e.1.1 = orientedFrequency (ell e) (ε e) := by
  classical
  unfold matchingMode
  rw [Finset.sum_eq_single e]
  · have hne : e.1.1 ≠ e.1.2 := by
      have h := edges_ordered M e.1 e.2
      exact fun he => by rw [he] at h; exact (lt_irrefl _ h)
    simp [hne]
  · intro f _ hfe
    have hef : e.1 ≠ f.1 := by intro h; exact hfe (Subtype.ext h.symm)
    have hd := matching_edges_disjoint M e.1 f.1 e.2 f.2 hef
    simp [hd.1, hd.2.1]
  · simp

private theorem matching_mode_second (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (e : edgeParam M) :
    matchingMode M ell ε e.1.2 = -orientedFrequency (ell e) (ε e) := by
  classical
  unfold matchingMode
  rw [Finset.sum_eq_single e]
  · have hne : e.1.2 ≠ e.1.1 := by
      have h := edges_ordered M e.1 e.2
      exact fun he => by rw [he] at h; exact (lt_irrefl _ h)
    simp [hne]
  · intro f _ hfe
    have hef : e.1 ≠ f.1 := by intro h; exact hfe (Subtype.ext h.symm)
    have hd := matching_edges_disjoint M e.1 f.1 e.2 f.2 hef
    simp [hd.2.2.1, hd.2.2.2]
  · simp

private theorem matching_mode_unpaired (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (a : Four) (ha : a ∈ M.unpaired) :
    matchingMode M ell ε a = 0 := by
  classical
  have hu : ∀ e ∈ M.edges, a ≠ e.1 ∧ a ≠ e.2 := by
    simpa [PM4.unpaired] using ha
  unfold matchingMode
  apply Finset.sum_eq_zero
  intro e _
  simp [(hu e.1 e.2).1, (hu e.1 e.2).2]

private def modeCompatible (n : Four → ℕ) (M : PM4) : Prop :=
  (∀ a ∈ M.unpaired, currentMode n a = 0) ∧
    ∀ e : edgeParam M,
      currentMode n e.1.1 = -currentMode n e.1.2 ∧ currentMode n e.1.1 ≠ 0

private def modeFrequency (n : Four → ℕ) {M : PM4} (e : edgeParam M) : ℕ :=
  (currentMode n e.1.1).natAbs

private def modeSide (n : Four → ℕ) {M : PM4} (e : edgeParam M) : Fin 2 :=
  if 0 < currentMode n e.1.1 then 0 else 1

private theorem oriented_frequency_nonzero (ell : ℕ) (ε : Fin 2) (hl : 0 < ell) :
    orientedFrequency ell ε ≠ 0 := by
  fin_cases ε <;> simp [orientedFrequency, orientation] <;> omega

private theorem oriented_frequency_recover (ell : ℕ) (ε : Fin 2) (hl : 0 < ell) :
    (orientedFrequency ell ε).natAbs = ell ∧
      (if 0 < orientedFrequency ell ε then (0 : Fin 2) else 1) = ε := by
  fin_cases ε <;> simp [orientedFrequency, orientation, hl]

private theorem matching_assignment_modes (n : Four → ℕ) (Q t : ℕ) (M : PM4)
    (ell : edgeParam M → ℕ) (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ)
    (hpos : ∀ e, 0 < ell e)
    (heq : ∀ a, n a = Q + t + matchingShift M ell ε k a) :
    modeCompatible n M ∧ ell = modeFrequency n ∧ ε = modeSide n := by
  classical
  have hm := ((matching_equations_iff n Q t M ell ε k).mp heq).2
  have hf (e : edgeParam M) : currentMode n e.1.1 = orientedFrequency (ell e) (ε e) := by
    rw [hm, matching_mode_first]
  have hs (e : edgeParam M) : currentMode n e.1.2 = -orientedFrequency (ell e) (ε e) := by
    rw [hm, matching_mode_second]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rw [hm, matching_mode_unpaired M ell ε a ha]
  · intro e
    rw [hf, hs, neg_neg]
    exact ⟨rfl, oriented_frequency_nonzero _ _ (hpos e)⟩
  · funext e
    exact ((oriented_frequency_recover _ _ (hpos e)).1).symm.trans (by
      dsimp [modeFrequency]; rw [hf])
  · funext e
    dsimp [modeSide]
    rw [hf]
    exact ((oriented_frequency_recover _ _ (hpos e)).2).symm

private theorem oriented_frequency_of_mode (m : ℤ) (hm : m ≠ 0) :
    orientedFrequency m.natAbs (if 0 < m then 0 else 1) = m := by
  by_cases hp : 0 < m
  · simp [hp, orientedFrequency, orientation, Int.natCast_natAbs, abs_of_pos hp]
  · have hn : m < 0 := by omega
    simp [hp, orientedFrequency, orientation, Int.natCast_natAbs, abs_of_neg hn]

private theorem compatible_matching_modes (n : Four → ℕ) (M : PM4)
    (hc : modeCompatible n M) :
    (∀ e : edgeParam M, 0 < modeFrequency n e) ∧
      ∀ a, matchingMode M (modeFrequency n) (modeSide n) a = currentMode n a := by
  classical
  have hf (e : edgeParam M) :
      orientedFrequency (modeFrequency n e) (modeSide n e) = currentMode n e.1.1 :=
    oriented_frequency_of_mode _ (hc.2 e).2
  refine ⟨?_, ?_⟩
  · intro e
    exact Int.natAbs_pos.mpr (hc.2 e).2
  · intro a
    by_cases ha : ∃ e : edgeParam M, a = e.1.1 ∨ a = e.1.2
    · obtain ⟨e, he | he⟩ := ha
      · subst a
        rw [matching_mode_first, hf]
      · subst a
        rw [matching_mode_second, hf]
        exact (neg_eq_iff_eq_neg.mpr (hc.2 e).1)
    · have hu : a ∈ M.unpaired := by
        simp only [PM4.unpaired, Finset.mem_filter, Finset.mem_univ, true_and]
        intro e he
        constructor
        · intro h; exact ha ⟨⟨e, he⟩, Or.inl h⟩
        · intro h; exact ha ⟨⟨e, he⟩, Or.inr h⟩
      rw [matching_mode_unpaired _ _ _ _ hu, hc.1 a hu]

private def windingEnergy (n : Four → ℕ) (M : PM4) (k : edgeParam M → ℕ) : ℕ :=
  ∑ e : edgeParam M, modeFrequency n e * k e

private def creationDelay (n : Four → ℕ) (M : PM4) : ℕ := by
  classical
  exact ∑ e : edgeParam M, if currentMode n e.1.1 < 0 then modeFrequency n e else 0

private theorem matching_shift_initial (n : Four → ℕ) (M : PM4)
    (k : edgeParam M → ℕ) (hc : modeCompatible n M) :
    matchingShift M (modeFrequency n) (modeSide n) k 0 =
      creationDelay n M + windingEnergy n M k := by
  classical
  unfold matchingShift creationDelay windingEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hne : currentMode n e.1.1 ≠ 0 := (hc.2 e).2
  have harc : ¬ arcMem e.1 0 := by simp [arcMem]
  by_cases hp : 0 < currentMode n e.1.1
  · have hn : ¬ currentMode n e.1.1 < 0 := by omega
    simp [modeSide, hp, sideMem, harc, hn]
  · have hn : currentMode n e.1.1 < 0 := by omega
    simp [modeSide, hp, sideMem, harc, hn, Nat.mul_add, Nat.add_comm]

private theorem matching_energy_transport (n : Four → ℕ) (Q t : ℕ) (M : PM4)
    (k : edgeParam M → ℕ) (hc : modeCompatible n M) :
    (∀ a, n a = Q + t + matchingShift M (modeFrequency n) (modeSide n) k a) ↔
      n 0 = Q + t + creationDelay n M + windingEnergy n M k := by
  rw [matching_equations_iff, matching_shift_initial n M k hc]
  have hm := (compatible_matching_modes n M hc).2
  simp only [hm, implies_true, and_true]
  omega

private theorem mode_frequency_bound (n : Four → ℕ) (M : PM4) (e : edgeParam M) :
    modeFrequency n e ≤ max4 n := by
  have ha := le_max4 n e.1.1
  have hb := le_max4 n (e.1.1 + 1)
  dsimp only [modeFrequency, currentMode]
  by_cases h : n e.1.1 ≤ n (e.1.1 + 1)
  · have hm : (n (e.1.1 + 1) : ℤ) - n e.1.1 = ((n (e.1.1 + 1) - n e.1.1 : ℕ) : ℤ) := by omega
    rw [hm, Int.natAbs_natCast]
    omega
  · have hm : (n (e.1.1 + 1) : ℤ) - n e.1.1 = -((n e.1.1 - n (e.1.1 + 1) : ℕ) : ℤ) := by omega
    rw [hm, Int.natAbs_neg, Int.natAbs_natCast]
    omega

private def boundedModeFrequency (n : Four → ℕ) (M : PM4) :
    edgeParam M → Fin (max4 n + 1) :=
  fun e => ⟨modeFrequency n e, Nat.lt_succ_of_le (mode_frequency_bound n M e)⟩

private def orderedChargeWeight (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (M : PM4)
    (k : edgeParam M → Fin (min4 n + 1)) (t : Fin (min4 n + 1)) : ℂ := by
  classical
  exact if modeCompatible n M ∧
      n 0 = (chargeEnergy D β).toNat + t.1 + creationDelay n M +
        windingEnergy n M (fun e => (k e).1) then
    (Nat.card (IntegerFiber D t.1) : ℂ) *
      (∏ a ∈ M.unpaired, (bilinear D (unitCharge D (i a)) β : ℂ)) *
        ∏ e : edgeParam M, (modeFrequency n e : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)
  else 0

private def orderedFourCurrentCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) : ℂ := by
  classical
  exact ∑ β ∈ positiveChargeCutoff D hD (min4 n : ℤ),
    ∑ M : PM4, ∑ k : edgeParam M → Fin (min4 n + 1),
      ∑ t : Fin (min4 n + 1), orderedChargeWeight D i n β M k t

private theorem charge_weight_frequency_unique (D : LatticeData)
    (i : Four → Fin D.rank) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (t : Fin (min4 n + 1)) (hne : ell ≠ boundedModeFrequency n M) :
    chargeWeight D i n β M ell ε k t = 0 := by
  classical
  unfold chargeWeight
  split_ifs with h
  · exfalso
    have hu := matching_assignment_modes n (chargeEnergy D β).toNat t.1 M
      (fun e => (ell e).1) ε (fun e => (k e).1) h.2 h.1
    apply hne
    funext e
    apply Fin.ext
    exact congrFun hu.2.1 e
  · rfl

private theorem charge_weight_side_unique (D : LatticeData)
    (i : Four → Fin D.rank) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (t : Fin (min4 n + 1)) (hne : ε ≠ modeSide n) :
    chargeWeight D i n β M ell ε k t = 0 := by
  classical
  unfold chargeWeight
  split_ifs with h
  · exfalso
    have hu := matching_assignment_modes n (chargeEnergy D β).toNat t.1 M
      (fun e => (ell e).1) ε (fun e => (k e).1) h.2 h.1
    exact hne hu.2.2
  · rfl

private theorem charge_weight_ordered (D : LatticeData)
    (i : Four → Fin D.rank) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (k : edgeParam M → Fin (min4 n + 1)) (t : Fin (min4 n + 1)) :
    chargeWeight D i n β M (boundedModeFrequency n M) (modeSide n) k t =
      orderedChargeWeight D i n β M k t := by
  classical
  have hi :
      ((∀ a, n a = (chargeEnergy D β).toNat + t.1 +
          gradeShift D n β M (boundedModeFrequency n M) (modeSide n) k a) ∧
        (∀ e : edgeParam M, 0 < ((boundedModeFrequency n M) e).1)) ↔
      modeCompatible n M ∧ n 0 = (chargeEnergy D β).toNat + t.1 +
        creationDelay n M + windingEnergy n M (fun e => (k e).1) := by
    constructor
    · rintro ⟨heq, hpos⟩
      have hc := (matching_assignment_modes n (chargeEnergy D β).toNat t.1 M
        (modeFrequency n) (modeSide n) (fun e => (k e).1) hpos heq).1
      exact ⟨hc, (matching_energy_transport n _ _ M _ hc).mp heq⟩
    · rintro ⟨hc, heq⟩
      exact ⟨(matching_energy_transport n _ _ M _ hc).mpr heq,
        (compatible_matching_modes n M hc).1⟩
  unfold chargeWeight orderedChargeWeight
  split_ifs with h h'
  · rfl
  · exact False.elim (h' (hi.mp h))
  · rename_i h'
    exact False.elim (h (hi.mpr h'))
  · rfl

private theorem bounded_coefficient_ordered (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    boundedFourCurrentCoefficient D hD i n = orderedFourCurrentCoefficient D hD i n := by
  classical
  unfold boundedFourCurrentCoefficient orderedFourCurrentCoefficient
  apply Finset.sum_congr rfl
  intro β hβ
  apply Finset.sum_congr rfl
  intro M _
  rw [Finset.sum_eq_single (boundedModeFrequency n M)]
  · rw [Finset.sum_eq_single (modeSide n)]
    · apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro t _
      exact charge_weight_ordered D i n β M k t
    · intro ε _ hε
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro t _
      exact charge_weight_side_unique D i n β M _ ε k t hε
    · simp
  · intro ell _ hell
    apply Finset.sum_eq_zero
    intro ε _
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro t _
    exact charge_weight_frequency_unique D i n β M ell ε k t hell
  · simp


end D5.S3.VertexAlgebra.LatticeFourCurrentTrace
