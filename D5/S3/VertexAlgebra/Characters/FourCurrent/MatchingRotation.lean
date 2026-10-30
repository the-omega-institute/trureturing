/- GID: D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labeled coefficient rotation and finite residual and geometric sums. -/

import D5.S3.VertexAlgebra.Characters.FourCurrent.MatchingModes

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

open private edgeParam sideMem min4 max4 matchingShift pm4_empty_unpaired
  rotateFour original_four_zero_charge_trace edges_ordered
  from D5.S3.VertexAlgebra.Characters.FourCurrent.TraceRecurrence

open private zeroFourCoefficient currentMode modeCompatible windingEnergy creationDelay orderedChargeWeight orderedFourCurrentCoefficient
  bounded_coefficient_ordered
  from D5.S3.VertexAlgebra.Characters.FourCurrent.MatchingModes

private theorem edges_empty_iff : ∀ M : PM4, M.edges = ∅ ↔ M = .empty := by decide

private theorem compatible_constant_iff (N : ℕ) (M : PM4) :
    modeCompatible (fun _ => N) M ↔ M = .empty := by
  classical
  constructor
  · intro hc
    apply (edges_empty_iff M).mp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact (hc.2 ⟨e, he⟩).2 (by simp [currentMode])
  · rintro rfl
    constructor
    · intro a _
      simp [currentMode]
    · intro e
      exact isEmptyElim e

private theorem ordered_weight_incompatible (D : LatticeData)
    (i : Four → Fin D.rank) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (k : edgeParam M → Fin (min4 n + 1)) (t : Fin (min4 n + 1))
    (hc : ¬ modeCompatible n M) : orderedChargeWeight D i n β M k t = 0 := by
  classical
  simp [orderedChargeWeight, hc]

private theorem ordered_empty_weight (D : LatticeData)
    (i : Four → Fin D.rank) (N : ℕ) (β : Charge D)
    (k : edgeParam PM4.empty → Fin (min4 (fun _ => N) + 1))
    (t : Fin (min4 (fun _ => N) + 1)) :
    orderedChargeWeight D i (fun _ => N) β .empty k t =
      if N = (chargeEnergy D β).toNat + t.1 then
        (Nat.card (IntegerFiber D t.1) : ℂ) *
          ∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ)
      else 0 := by
  classical
  have hc := (compatible_constant_iff N PM4.empty).mpr rfl
  simp [orderedChargeWeight, hc, creationDelay, windingEnergy,
    PM4.edges, pm4_empty_unpaired]

private theorem ordered_constant_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (N : ℕ) :
    orderedFourCurrentCoefficient D hD i (fun _ => N) = zeroFourCoefficient D hD i N := by
  classical
  unfold orderedFourCurrentCoefficient zeroFourCoefficient
  have hmin : min4 (fun _ => N) = N := by simp [min4]
  have hcut : positiveChargeCutoff D hD (min4 (fun _ => N) : ℤ) =
      positiveChargeCutoff D hD (N : ℤ) := by rw [hmin]
  apply Finset.sum_congr hcut
  intro β hβ
  have hq : (chargeEnergy D β).toNat ≤ N := by
    have hQ : chargeEnergy D β ≤ (N : ℤ) := by simpa [positiveChargeCutoff] using hβ
    omega
  rw [Finset.sum_eq_single PM4.empty]
  · simp_rw [ordered_empty_weight]
    have hsum :
        (∑ t : Fin (min4 (fun _ => N) + 1),
          if N = (chargeEnergy D β).toNat + t.1 then
            (Nat.card (IntegerFiber D t.1) : ℂ) *
              ∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ)
          else 0) =
        (Nat.card (IntegerFiber D (N - (chargeEnergy D β).toNat)) : ℂ) *
          ∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ) := by
      let t0 : Fin (min4 (fun _ => N) + 1) := ⟨N - (chargeEnergy D β).toNat, by rw [hmin]; omega⟩
      rw [Finset.sum_eq_single t0]
      · simp [t0, Nat.add_sub_of_le hq]
      · intro t _ hne
        have hneq : N ≠ (chargeEnergy D β).toNat + t.1 := by
          intro h
          apply hne
          apply Fin.ext
          dsimp [t0]
          omega
        simp [hneq]
      · simp
    rw [hsum]
    simp [mul_comm]
  · intro M _ hM
    have hc : ¬ modeCompatible (fun _ => N) M := by
      rw [compatible_constant_iff]
      exact hM
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro t _
    exact ordered_weight_incompatible D i (fun _ => N) β M k t hc
  · simp

private theorem original_four_constant_matching (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (N : ℕ) :
    actualFourCurrentCycleTrace D hD i (fun _ => N) =
      boundedFourCurrentCoefficient D hD i (fun _ => N) := by
  rw [bounded_coefficient_ordered, ordered_constant_coefficient]
  exact original_four_zero_charge_trace D hD i N

private def rotateMatching : PM4 → PM4
  | .empty => .empty
  | .p12 => .p14
  | .p13 => .p24
  | .p14 => .p34
  | .p23 => .p12
  | .p24 => .p13
  | .p34 => .p23
  | .p12_34 => .p14_23
  | .p13_24 => .p13_24
  | .p14_23 => .p12_34

private def rotateMatchingEquiv : PM4 ≃ PM4 where
  toFun := rotateMatching
  invFun := fun M => rotateMatching (rotateMatching (rotateMatching M))
  left_inv := by decide
  right_inv := by decide

private def rotateEdge (e : Four × Four) : Four × Four :=
  if e.1 = 0 then (e.2 - 1, 3) else (e.1 - 1, e.2 - 1)

private def unrotateEdge (e : Four × Four) : Four × Four :=
  if e.2 = 3 then (0, e.1 + 1) else (e.1 + 1, e.2 + 1)

private theorem rotate_edge_mem : ∀ (M : PM4) (e : Four × Four),
    e ∈ M.edges → rotateEdge e ∈ (rotateMatching M).edges := by decide

private theorem unrotate_edge_mem : ∀ (M : PM4) (e : Four × Four),
    e ∈ (rotateMatching M).edges → unrotateEdge e ∈ M.edges := by decide

private theorem rotate_edge_left : ∀ (e : Four × Four), e.1.1 < e.2.1 →
    unrotateEdge (rotateEdge e) = e := by decide

private theorem rotate_edge_right : ∀ (e : Four × Four), e.1.1 < e.2.1 →
    rotateEdge (unrotateEdge e) = e := by decide

private def rotateEdgeEquiv (M : PM4) : edgeParam M ≃ edgeParam (rotateMatching M) where
  toFun e := ⟨rotateEdge e.1, rotate_edge_mem M e.1 e.2⟩
  invFun e := ⟨unrotateEdge e.1, unrotate_edge_mem M e.1 e.2⟩
  left_inv e := Subtype.ext (rotate_edge_left e.1 (edges_ordered M e.1 e.2))
  right_inv e := Subtype.ext (rotate_edge_right e.1
    (edges_ordered (rotateMatching M) e.1 e.2))

private def rotateEdgeValues (M : PM4) (α : Type*) :
    (edgeParam M → α) ≃ (edgeParam (rotateMatching M) → α) :=
  Equiv.arrowCongr (rotateEdgeEquiv M) (Equiv.refl α)

private theorem rotate_values_apply (M : PM4) (α : Type*)
    (f : edgeParam M → α) (e : edgeParam M) :
    rotateEdgeValues M α f (rotateEdgeEquiv M e) = f e := by
  change f ((rotateEdgeEquiv M).symm (rotateEdgeEquiv M e)) = f e
  rw [Equiv.symm_apply_apply]

private def flipSide (e : Four × Four) (ε : Fin 2) : Fin 2 :=
  if e.1 = 0 then 1 - ε else ε

private theorem flip_side_twice : ∀ (e : Four × Four) (ε : Fin 2),
    flipSide e (flipSide e ε) = ε := by decide

private theorem side_rotation : ∀ (e : Four × Four), e.1.1 < e.2.1 →
    ∀ (ε : Fin 2) (a : Four),
      sideMem (flipSide e ε) (rotateEdge e) a ↔ sideMem ε e (a + 1) := by decide

private def rotateSides (M : PM4) :
    (edgeParam M → Fin 2) ≃ (edgeParam (rotateMatching M) → Fin 2) where
  toFun ε e := flipSide ((rotateEdgeEquiv M).symm e).1 (ε ((rotateEdgeEquiv M).symm e))
  invFun ε e := flipSide e.1 (ε (rotateEdgeEquiv M e))
  left_inv ε := by
    funext e
    simp [flip_side_twice]
  right_inv ε := by
    funext e
    simp [flip_side_twice]

private theorem rotate_sides_apply (M : PM4) (ε : edgeParam M → Fin 2)
    (e : edgeParam M) :
    rotateSides M ε (rotateEdgeEquiv M e) = flipSide e.1 (ε e) := by
  change flipSide ((rotateEdgeEquiv M).symm (rotateEdgeEquiv M e)).1
    (ε ((rotateEdgeEquiv M).symm (rotateEdgeEquiv M e))) = _
  rw [Equiv.symm_apply_apply]

private theorem matching_shift_rotation (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) (a : Four) :
    matchingShift M ell ε k (a + 1) =
      matchingShift (rotateMatching M) (rotateEdgeValues M ℕ ell)
        (rotateSides M ε) (rotateEdgeValues M ℕ k) a := by
  classical
  unfold matchingShift
  apply Fintype.sum_equiv (rotateEdgeEquiv M)
  intro e
  have hs := side_rotation e.1 (edges_ordered M e.1 e.2) (ε e) a
  simp only [rotate_values_apply, rotate_sides_apply]
  change ell e * (k e + if sideMem (ε e) e.1 (a + 1) then 1 else 0) =
    ell e * (k e + if sideMem (flipSide e.1 (ε e)) (rotateEdge e.1) a then 1 else 0)
  simp only [hs]

private theorem min4_rotation (n : Four → ℕ) : min4 (rotateFour n) = min4 n := by
  dsimp [min4, rotateFour]
  omega

private theorem max4_rotation (n : Four → ℕ) : max4 (rotateFour n) = max4 n := by
  dsimp [max4, rotateFour]
  omega

private theorem unpaired_rotation : ∀ (M : PM4) (a : Four),
    a - 1 ∈ (rotateMatching M).unpaired ↔ a ∈ M.unpaired := by decide

private theorem gram_rotation (D : LatticeData) (i : Four → Fin D.rank)
    (e : Four × Four) (he : e.1.1 < e.2.1) :
    D.G ((rotateFour i) (rotateEdge e).1) ((rotateFour i) (rotateEdge e).2) =
      D.G (i e.1) (i e.2) := by
  rcases e with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  all_goals norm_num at he
  all_goals simp [rotateEdge, rotateFour]
  all_goals exact D.symmetric _ _

private def unrestrictedChargeWeight (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) (t : ℕ) : ℂ := by
  classical
  exact if (∀ a, n a = (chargeEnergy D β).toNat + t + matchingShift M ell ε k a) ∧
      (∀ e, 0 < ell e) then
    (Nat.card (IntegerFiber D t) : ℂ) *
      (∏ a ∈ M.unpaired, (bilinear D (unitCharge D (i a)) β : ℂ)) *
        ∏ e : edgeParam M, (ell e : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)
  else 0

private theorem unpaired_weight_rotation (D : LatticeData) (i : Four → Fin D.rank)
    (β : Charge D) (M : PM4) :
    (∏ a ∈ M.unpaired, (bilinear D (unitCharge D (i a)) β : ℂ)) =
      ∏ a ∈ (rotateMatching M).unpaired,
        (bilinear D (unitCharge D ((rotateFour i) a)) β : ℂ) := by
  classical
  refine Finset.prod_bij (fun a _ => a - 1) ?_ ?_ ?_ ?_
  · intro a ha
    exact (unpaired_rotation M a).mpr ha
  · intro a _ b _ hab
    have h := congrArg (fun x : Four => x + 1) hab
    simpa using h
  · intro b hb
    refine ⟨b + 1, ?_, by simp⟩
    exact (unpaired_rotation M (b + 1)).mp (by simpa using hb)
  · intro a _
    simp [rotateFour]

private theorem paired_weight_rotation (D : LatticeData) (i : Four → Fin D.rank)
    (M : PM4) (ell : edgeParam M → ℕ) :
    (∏ e : edgeParam M, (ell e : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)) =
      ∏ e : edgeParam (rotateMatching M),
        ((rotateEdgeValues M ℕ ell) e : ℂ) *
          (D.G ((rotateFour i) e.1.1) ((rotateFour i) e.1.2) : ℂ) := by
  classical
  apply Fintype.prod_equiv (rotateEdgeEquiv M)
  intro e
  simp only [rotate_values_apply]
  change (ell e : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ) =
    (ell e : ℂ) * (D.G ((rotateFour i) (rotateEdge e.1).1)
      ((rotateFour i) (rotateEdge e.1).2) : ℂ)
  rw [gram_rotation D i e.1 (edges_ordered M e.1 e.2)]

private theorem unrestricted_weight_rotation (D : LatticeData) (i : Four → Fin D.rank)
    (n : Four → ℕ) (β : Charge D) (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) (t : ℕ) :
    unrestrictedChargeWeight D i n β M ell ε k t =
      unrestrictedChargeWeight D (rotateFour i) (rotateFour n) β (rotateMatching M)
        (rotateEdgeValues M ℕ ell) (rotateSides M ε) (rotateEdgeValues M ℕ k) t := by
  classical
  have heq : (∀ a, n a = (chargeEnergy D β).toNat + t + matchingShift M ell ε k a) ↔
      (∀ a, rotateFour n a = (chargeEnergy D β).toNat + t +
        matchingShift (rotateMatching M) (rotateEdgeValues M ℕ ell)
          (rotateSides M ε) (rotateEdgeValues M ℕ k) a) := by
    constructor
    · intro h a
      rw [← matching_shift_rotation]
      exact h (a + 1)
    · intro h a
      have h' := h (a - 1)
      rw [← matching_shift_rotation] at h'
      simpa [rotateFour] using h'
  have hpos : (∀ e, 0 < ell e) ↔
      (∀ e, 0 < rotateEdgeValues M ℕ ell e) := by
    constructor
    · intro h e
      exact h ((rotateEdgeEquiv M).symm e)
    · intro h e
      have h' := h (rotateEdgeEquiv M e)
      rwa [rotate_values_apply] at h'
  unfold unrestrictedChargeWeight
  split_ifs with h h'
  · rw [← unpaired_weight_rotation, ← paired_weight_rotation]
  · exact False.elim (h' ⟨heq.mp h.1, hpos.mp h.2⟩)
  · rename_i h'
    exact False.elim (h ⟨heq.mpr h'.1, hpos.mpr h'.2⟩)
  · rfl

private theorem bounded_coefficient_rotation (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    boundedFourCurrentCoefficient D hD i n =
      boundedFourCurrentCoefficient D hD (rotateFour i) (rotateFour n) := by
  classical
  change (∑ β ∈ positiveChargeCutoff D hD (min4 n : ℤ), ∑ M : PM4,
    ∑ ell : edgeParam M → Fin (max4 n + 1), ∑ ε : edgeParam M → Fin 2,
      ∑ k : edgeParam M → Fin (min4 n + 1), ∑ t : Fin (min4 n + 1),
        unrestrictedChargeWeight D i n β M (fun e => (ell e).1) ε
          (fun e => (k e).1) t.1) =
    (∑ β ∈ positiveChargeCutoff D hD (min4 (rotateFour n) : ℤ), ∑ M : PM4,
      ∑ ell : edgeParam M → Fin (max4 (rotateFour n) + 1), ∑ ε : edgeParam M → Fin 2,
        ∑ k : edgeParam M → Fin (min4 (rotateFour n) + 1),
          ∑ t : Fin (min4 (rotateFour n) + 1),
            unrestrictedChargeWeight D (rotateFour i) (rotateFour n) β M
              (fun e => (ell e).1) ε (fun e => (k e).1) t.1)
  rw [min4_rotation, max4_rotation]
  apply Finset.sum_congr rfl
  intro β _
  apply Fintype.sum_equiv rotateMatchingEquiv
  intro M
  apply Fintype.sum_equiv (rotateEdgeValues M (Fin (max4 n + 1)))
  intro ell
  apply Fintype.sum_equiv (rotateSides M)
  intro ε
  apply Fintype.sum_equiv (rotateEdgeValues M (Fin (min4 n + 1)))
  intro k
  apply Finset.sum_congr rfl
  intro t _
  exact unrestricted_weight_rotation D i n β M (fun e => (ell e).1) ε
    (fun e => (k e).1) t.1


private theorem finite_residual_delta (f : ℕ → ℂ) (N x B : ℕ) (hN : N ≤ B) :
    (∑ t : Fin (B + 1), if N = x + t.1 then f t.1 else 0) =
      if x ≤ N then f (N - x) else 0 := by
  classical
  by_cases hx : x ≤ N
  · rw [if_pos hx]
    let t0 : Fin (B + 1) := ⟨N - x, by omega⟩
    rw [Finset.sum_eq_single t0]
    · simp [t0, Nat.add_sub_of_le hx]
    · intro t _ ht
      have hne : N ≠ x + t.1 := by
        intro he
        apply ht
        apply Fin.ext
        dsimp [t0]
        omega
      simp [hne]
    · simp
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro t _
    have hne : N ≠ x + t.1 := by omega
    simp [hne]

private theorem bounded_division_sum (f : ℕ → ℂ) (N ell B : ℕ)
    (hl : 0 < ell) (hN : N ≤ B) :
    (∑ k : Fin (B + 1), if k.1 * ell ≤ N then f k.1 else 0) =
      ∑ k ∈ Finset.range (N / ell + 1), f k := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k * ell ≤ N then f k else 0) (B + 1)]
  have hb : N / ell + 1 ≤ B + 1 := by
    have hd := Nat.div_le_self N ell
    omega
  calc
    _ = ∑ k ∈ Finset.range (N / ell + 1), if k * ell ≤ N then f k else 0 := by
      apply (Finset.sum_subset (Finset.range_mono hb) ?_).symm
      intro k hk hnot
      have hk' : N / ell < k := by simpa using hnot
      have hn : ¬ k * ell ≤ N := by
        intro he
        have := (Nat.le_div_iff_mul_le hl).mpr he
        omega
      simp [hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ N / ell := by simpa using hk
      rw [if_pos ((Nat.le_div_iff_mul_le hl).mp hk')]

private theorem bounded_geometric_delta (f : ℕ → ℂ) (N x ell B : ℕ)
    (hl : 0 < ell) (hN : N ≤ B) :
    (∑ k : Fin (B + 1), ∑ t : Fin (B + 1),
      if N = x + t.1 + k.1 * ell then f t.1 else 0) =
      if x ≤ N then
        ∑ k ∈ Finset.range ((N - x) / ell + 1), f (N - x - k * ell)
      else 0 := by
  classical
  have hs (k : Fin (B + 1)) :
      (∑ t : Fin (B + 1), if N = x + t.1 + k.1 * ell then f t.1 else 0) =
        if x + k.1 * ell ≤ N then f (N - x - k.1 * ell) else 0 := by
    have he (t : Fin (B + 1)) : x + t.1 + k.1 * ell = (x + k.1 * ell) + t.1 := by omega
    simp_rw [he]
    rw [finite_residual_delta f N (x + k.1 * ell) B hN, Nat.sub_sub]
  simp_rw [hs]
  by_cases hx : x ≤ N
  · rw [if_pos hx]
    have he (k : Fin (B + 1)) : x + k.1 * ell ≤ N ↔ k.1 * ell ≤ N - x := by omega
    simp_rw [he]
    exact bounded_division_sum (fun k => f (N - x - k * ell)) (N - x) ell B hl (by omega)
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro k _
    have hn : ¬ x + k.1 * ell ≤ N := by omega
    simp [hn]



end D5.S3.VertexAlgebra.LatticeFourCurrentTrace
