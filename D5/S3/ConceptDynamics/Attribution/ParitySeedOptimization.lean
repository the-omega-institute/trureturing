/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedOptimization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A sharp count for the least coordinate fixed set under a uniform finite seed budget. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
import D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching

/-! The coordinate fixed counts of exact uniform coloured parity readouts. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization

open Finset CoordinateFlagCoupling ParitySeedBudget
open D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
open scoped Classical

private def liftedMatrix {n : ℕ}
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (x y : Output (Fin (n + 2))) : ℕ :=
  if hx : parity (bitProfile x.profile) = 0 then
    if hy : parity (bitProfile y.profile) = 1 then
      w ⟨bitProfile x.profile, hx⟩ ⟨bitProfile y.profile, hy⟩
    else 0
  else 0

private theorem lift_values {n : ℕ}
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) (c d : ZMod 2) :
    entry (liftedMatrix w) p q c d = w p q := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  simp [entry, liftedMatrix, hp, hq]

private theorem lift_pooled {n : ℕ}
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
    pairMass (liftedMatrix w) p.val q.val = 4 * w p q := by
  change (∑ c : ZMod 2, ∑ d : ZMod 2, entry (liftedMatrix w) p q c d) = _
  simp only [lift_values, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  exact (Nat.mul_assoc 2 2 _).symm

set_option maxHeartbeats 1000000 in
-- Reindexing the two coloured marginal sums requires additional elaboration.
private theorem natural_profile_lift {n k : ℕ}
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, w p q = k) (cols : ∀ q, ∑ p, w p q = k) :
    MatrixRealizes n (2 ^ (n + 3) * k) (liftedMatrix w) := by
  have invariant (g : Acting (Fin (n + 2))) (x y : Output (Fin (n + 2))) :
      liftedMatrix w (g • x) (g • y) = liftedMatrix w x y := rfl
  have total :
      (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1,
        pairMass (liftedMatrix w) p.val q.val) = 2 ^ (n + 3) * k := by
    simp_rw [lift_pooled, ← mul_sum, rows]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, parityCard]
    change 4 * ((2 : ℕ) ^ (n + 1) * k) = 2 ^ (n + 3) * k
    calc
      _ = (2 ^ (n + 1) * 4) * k := by ac_rfl
      _ = _ := congrArg (· * k) (pow_add (2 : ℕ) (n + 1) 2).symm
  refine ⟨invariant, total, 2 * k, ?_, ?_⟩
  · intro p c
    simp_rw [lift_values]
    rw [sum_comm]
    simp [rows, ZMod.card]
  · intro q d
    simp_rw [lift_values]
    rw [sum_comm]
    simp [cols, ZMod.card]

private theorem pair_fixed_coordinate {n : ℕ} (a : Pair n) (i : Fin (n + 2)) :
    (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a) ↔
      a.1.val.profile i = true ∧ a.2.val.profile i = true := by
  rw [← Bool.and_eq_true, ← fixed_pair_iff]
  constructor
  · intro fixed g hg
    exact ⟨congrArg (fun z : Pair n => z.1.val) (fixed ⟨g, hg⟩),
      congrArg (fun z : Pair n => z.2.val) (fixed ⟨g, hg⟩)⟩
  · intro fixed g
    obtain ⟨left, right⟩ := fixed g g.property
    exact Prod.ext (Subtype.ext left) (Subtype.ext right)

private theorem normalize_coloured_counts {n k : ℕ}
    {w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ}
    (h : MatrixRealizes n (2 ^ (n + 3) * k) w) :
    ∃ W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, W p q = k) ∧ (∀ q, ∑ p, W p q = k) ∧
      ∀ p q, 4 * W p q = pairMass w p.val q.val := by
  have cells := h.four_dvd.2
  let W (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :=
    (pairMass w p.val q.val) / 4
  have scale (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      4 * W p q = pairMass w p.val q.val := by
    unfold W
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (cells p q)
  obtain ⟨_, total, c, rows, cols⟩ := h
  have rowSum (p : ParityClass (n + 2) 0) :
      (∑ q : ParityClass (n + 2) 1, pairMass w p.val q.val) = 2 * c := by
    change (∑ q, ∑ a, ∑ b, entry w p q a b) = _
    rw [sum_comm]
    simp [rows, ZMod.card]
  have colSum (q : ParityClass (n + 2) 1) :
      (∑ p : ParityClass (n + 2) 0, pairMass w p.val q.val) = 2 * c := by
    calc
      _ = ∑ p : ParityClass (n + 2) 0, ∑ b : ZMod 2, ∑ a : ZMod 2, entry w p q a b :=
        sum_congr rfl fun _ _ => sum_comm
      _ = ∑ b : ZMod 2, ∑ p : ParityClass (n + 2) 0, ∑ a : ZMod 2, entry w p q a b :=
        sum_comm
      _ = _ := by simp [cols, ZMod.card]
  have total' : (2 : ℕ) ^ (n + 1) * (2 * c) = 2 ^ (n + 3) * k := by
    simpa only [rowSum, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      parityCard, Nat.cast_id] using total
  have margin : 2 * c = 4 * k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
    calc
      _ = 2 ^ (n + 3) * k := total'
      _ = _ := by
        have powSplit : (2 : ℕ) ^ (n + 3) = 2 ^ (n + 1) * 4 := pow_add 2 (n + 1) 2
        rw [powSplit, Nat.mul_assoc]
  refine ⟨W, ?_, ?_, scale⟩
  · intro p
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (4 : ℕ))
    rw [mul_sum]
    simp only [scale, rowSum, margin]
  · intro q
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (4 : ℕ))
    rw [mul_sum]
    simp only [scale, colSum, margin]

open Classical in
private theorem seed_indicator_sum {n : ℕ} {S : Type} [Fintype S] (f : S → Pair n)
    (P : Pair n → Prop) :
    (∑ s, if P (f s) then (1 : ℕ) else 0) =
      ∑ a, if P a then seedWeight (seedPushforward f) a else 0 := by
  have atom (a : Pair n) : seedWeight (seedPushforward f) a =
      ∑ s, if f s = a then (1 : ℕ) else 0 := by
    unfold seedWeight seedPushforward
    apply sum_congr rfl
    intro s _
    by_cases eq : f s = a
    · simp [eq]
    · have ne : ¬((f s).1 = a.1 ∧ (f s).2 = a.2) := fun h =>
        eq (Prod.ext h.1 h.2)
      simp [eq, ne]
  simp_rw [atom]
  have rearrange (a : Pair n) :
      (if P a then (∑ s, if f s = a then (1 : ℕ) else 0) else 0) =
      ∑ s, if f s = a then (if P a then 1 else 0) else 0 := by
    by_cases h : P a
    · simp [h]
    · simp [h]
  simp_rw [rearrange]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  simp

open Classical in
private theorem fixed_seed_count_le_pushforward {n : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (i : Fin (n + 2)) :
    (∑ s : S, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s)
      then (1 : ℕ) else 0) ≤
      ∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
        then seedWeight (seedPushforward f) a else 0 := by
  let P (a : Pair n) : Prop := ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a
  have bound : (∑ s : S, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s)
      then (1 : ℕ) else 0) ≤ ∑ s : S, if P (f s) then (1 : ℕ) else 0 := by
    apply sum_le_sum
    intro s _
    by_cases hfixed : ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s
    · have hf : P (f s) := by
        intro h
        rw [← equiv, hfixed h]
      rw [ite_eq_left hfixed, ite_eq_left hf]
    · rw [ite_eq_right hfixed]
      exact Nat.zero_le _
  refine bound.trans (le_of_eq ?_)
  convert seed_indicator_sum f P using 1
  · apply sum_congr rfl
    intro s _
    by_cases hs : P (f s)
    · rw [ite_eq_left hs, ite_eq_left hs]
    · rw [ite_eq_right hs, ite_eq_right hs]
  · apply sum_congr rfl
    intro a _
    by_cases ha : P a
    · rw [ite_eq_left ha, ite_eq_left ha]
    · rw [ite_eq_right ha, ite_eq_right ha]

private theorem matrix_fixed_total {n : ℕ}
    (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ) (i : Fin (n + 2)) :
    (∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
      then seedWeight w a else 0) =
      ∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1,
        if p.val i = 1 ∧ q.val i = 1 then pairMass w p.val q.val else 0 := by
  simp_rw [pair_fixed_coordinate]
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp (sliceEquiv (n + 2) 0)]
  simp_rw [← Equiv.sum_comp (sliceEquiv (n + 2) 1), Fintype.sum_prod_type]
  have values (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1)
      (c d : ZMod 2) :
      (if (sliceEquiv (n + 2) 0 (p, c)).val.profile i = true ∧
          (sliceEquiv (n + 2) 1 (q, d)).val.profile i = true
        then seedWeight w (sliceEquiv (n + 2) 0 (p, c), sliceEquiv (n + 2) 1 (q, d))
        else 0) = if p.val i = 1 ∧ q.val i = 1 then entry w p q c d else 0 := by
    change (if booleanProfile p.val i = true ∧ booleanProfile q.val i = true
      then entry w p q c d else 0) = _
    simp [booleanProfile]
  simp_rw [values]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases h : p.val i = 1 ∧ q.val i = 1 <;> simp [h, entry, pairMass]

private theorem scaled_fixed_total {n : ℕ}
    {w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ}
    {W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ}
    (scale : ∀ p q, 4 * W p q = pairMass w p.val q.val) (i : Fin (n + 2)) :
    (∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
      then seedWeight w a else 0) = 4 * commonOneCount W i := by
  rw [matrix_fixed_total]
  unfold commonOneCount
  simp_rw [mul_sum, ← scale]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split <;> simp_all

/-- The number of seeds fixed by the subgroup acting in coordinate `i`. -/
def fixedSeedCount {n : ℕ} (S : Type) [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (i : Fin (n + 2)) : ℕ :=
  ∑ s : S, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s) then 1 else 0

section
attribute [local instance 10000] Classical.propDecidable

/-- Fixed-seed count vectors attained by exact uniform coloured parity implementations. -/
def RealizableSeedCounts (n k : ℕ) (v : Fin (n + 2) → ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
    Fintype.card S = 2 ^ (n + 3) * k ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
    (∃ c : ℕ,
      (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
      (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) ∧
    ∀ i, fixedSeedCount (n := n) S i = v i

end

private theorem realize_scaled_profile_counts {n k : ℕ}
    (W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, W p q = k) (cols : ∀ q, ∑ p, W p q = k) :
    RealizableSeedCounts n k (fun i => 4 * commonOneCount W i) := by
  classical
  obtain ⟨S, _, _, f, card, equiv, fixed, counts, uniform⟩ :=
    matrix_to_seeds_with_readouts (natural_profile_lift W rows cols)
  refine ⟨S, inferInstance, inferInstance, f, card, equiv, uniform, fun i => ?_⟩
  unfold fixedSeedCount
  simp_rw [fixed (coordinate i)]
  let P (a : Pair n) : Prop := ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a
  have reduced : (∑ s : S, if (∀ h : coordinate i,
      (h : Acting (Fin (n + 2))) • f s = f s) then (1 : ℕ) else 0) =
      ∑ a : Pair n, if (∀ h : coordinate i,
        (h : Acting (Fin (n + 2))) • a = a) then seedWeight (liftedMatrix W) a else 0 := by
    convert counts P using 1 <;> apply sum_congr rfl <;> intro a _ <;>
      (first | by_cases h : P (f a) | by_cases h : P a) <;> simp [P] at h ⊢
  rw [reduced, scaled_fixed_total (fun p q => (lift_pooled W p q).symm) i]

private theorem realize_profile_boundary {n k : ℕ} {v : Fin (n + 2) → ℕ}
    (h : ProfileBoundary n k v) :
    RealizableSeedCounts n k (fun i => 4 * v i) := by
  obtain ⟨⟨W, rows, cols, bounds⟩, maximal⟩ := (exact_profile_frontier n k v).2 h
  have eq := maximal (commonOneCount W) ⟨W, rows, cols, fun _ => le_rfl⟩ bounds
  simpa only [eq] using realize_scaled_profile_counts W rows cols

private theorem seed_vector_dominated {n k : ℕ} {z : Fin (n + 2) → ℕ}
    (h : RealizableSeedCounts n k z) :
    ∃ v, ProfileBoundary n k v ∧ ∀ i, z i ≤ 4 * v i := by
  obtain ⟨S, _, _, f, card, equiv, ⟨c, rows, cols⟩, equal⟩ := h
  obtain ⟨W, wRows, wCols, scale⟩ :=
    normalize_coloured_counts (seeds_to_pushforward f card equiv c rows cols)
  obtain ⟨v, boundary, bounds⟩ :=
    profile_floor_dominated (n := n) (k := k) (v := commonOneCount W)
      ⟨W, wRows, wCols, fun _ => le_rfl⟩
  refine ⟨v, boundary, fun i => ?_⟩
  rw [← equal i]
  refine (fixed_seed_count_le_pushforward f equiv i).trans ?_
  rw [scaled_fixed_total scale i]
  exact Nat.mul_le_mul_left 4 (bounds i)

/-- The maximal coordinate fixed-seed vectors are the scaled profile boundary. -/
theorem maximal_coordinate_fixed_vectors (n k : ℕ) (z : Fin (n + 2) → ℕ) :
    (RealizableSeedCounts n k z ∧
      ∀ u, RealizableSeedCounts n k u → (∀ i, z i ≤ u i) → u = z) ↔
    ∃ v, ProfileBoundary n k v ∧ ∀ i, z i = 4 * v i := by
  constructor
  · rintro ⟨feasible, maximal⟩
    obtain ⟨v, boundary, dominates⟩ := seed_vector_dominated feasible
    have eq := maximal (fun i => 4 * v i) (realize_profile_boundary boundary) dominates
    exact ⟨v, boundary, fun i => (congrFun eq i).symm⟩
  · rintro ⟨v, boundary, equal⟩
    have hz : z = (fun i => 4 * v i) := funext equal
    subst z
    refine ⟨realize_profile_boundary boundary, ?_⟩
    intro u feasible dominates
    obtain ⟨w, wBoundary, wDominates⟩ := seed_vector_dominated feasible
    have vw (i : Fin (n + 2)) : v i ≤ w i := by
      have h := (dominates i).trans (wDominates i)
      change 4 * v i ≤ 4 * w i at h
      exact Nat.le_of_mul_le_mul_left h (by decide)
    have hw : w = v :=
      ((exact_profile_frontier n k v).2 boundary).2 w
        ((exact_profile_frontier n k w).2 wBoundary).1 vw
    subst w
    exact funext fun i => le_antisymm (wDominates i) (dominates i)


attribute [local instance 10000] Classical.propDecidable

private def optimalCoordinateCount (n k : ℕ) : ℕ :=
  let M := k * 2 ^ n
  4 * (M - (M + (n + 2 - 1)) / (n + 2))

/-- The greatest minimum number of seeds fixed by a coordinate subgroup at an exact budget. -/
theorem best_fixed_seed_count (n k : ℕ) (positive : 0 < k) :
    let N := 2 ^ (n + 3) * k
    let best := optimalCoordinateCount n k
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = N ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) ∧
      ∀ i, best ≤ fixedSeedCount (n := n) S i) ∧
    ∀ (S : Type) [Fintype S] [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n),
      Fintype.card S = N → (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) →
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) →
      ∃ i, fixedSeedCount (n := n) S i ≤ best := by
  classical
  dsimp only [optimalCoordinateCount]
  obtain ⟨lower, upper⟩ := best_profile_count n k positive
  constructor
  · obtain ⟨W, rows, cols, bounds⟩ := lower
    obtain ⟨S, _, _, f, card, equiv, fixed, counts, uniform⟩ :=
      matrix_to_seeds_with_readouts (natural_profile_lift W rows cols)
    refine ⟨S, inferInstance, inferInstance, f, card, equiv, uniform, fun i => ?_⟩
    unfold fixedSeedCount
    simp_rw [fixed (coordinate i)]
    let P (a : Pair n) : Prop := ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a
    have reduced : (∑ s : S, if (∀ h : coordinate i,
        (h : Acting (Fin (n + 2))) • f s = f s) then (1 : ℕ) else 0) =
        ∑ a : Pair n, if (∀ h : coordinate i,
          (h : Acting (Fin (n + 2))) • a = a) then seedWeight (liftedMatrix W) a else 0 := by
      convert counts P using 1
      · apply sum_congr rfl
        intro s _
        by_cases h : P (f s)
        · rw [ite_eq_left h, ite_eq_left h]
        · rw [ite_eq_right h, ite_eq_right h]
      · apply sum_congr rfl
        intro a _
        by_cases h : P a
        · rw [ite_eq_left h, ite_eq_left h]
        · rw [ite_eq_right h, ite_eq_right h]
    rw [reduced, scaled_fixed_total (fun p q => (lift_pooled W p q).symm) i]
    exact Nat.mul_le_mul_left 4 (bounds i)
  · intro S _ _ f card equiv uniform
    obtain ⟨c, rows, cols⟩ := uniform
    obtain ⟨W, wRows, wCols, scale⟩ :=
      normalize_coloured_counts (seeds_to_pushforward f card equiv c rows cols)
    obtain ⟨i, bound⟩ := upper W wRows wCols
    refine ⟨i, (fixed_seed_count_le_pushforward f equiv i).trans ?_⟩
    rw [scaled_fixed_total scale i]
    exact Nat.mul_le_mul_left 4 bound

end D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
