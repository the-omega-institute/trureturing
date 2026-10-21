/- GID: D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.claim; result=D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result; claim=D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.claim
   digest: A lattice disk with 121 vertices has larger mean first exit time than the square. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed

/-! First exit times for the simple random walk on finite subsets of the square lattice. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.RandomWalks.SquareClusterExitTimeRefutation

open Finset
open scoped Topology

/-- The four equally likely directions of the square lattice. -/
abbrev Dir := Fin 4

/-- Unit coordinate steps. -/
def step : Dir → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The starting point plus the first `j` steps, stopping at the end of the word. -/
def position (p : ℤ × ℤ) : {n : ℕ} → (Fin n → Dir) → ℕ → ℤ × ℤ
  | 0, _, _ => p
  | _ + 1, _, 0 => p
  | _ + 1, w, j + 1 => position (p + step (w 0)) (Fin.tail w) j

/-- A word exits for the first time at its final position. -/
def exits (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) {n : ℕ} (w : Fin n → Dir) : Prop :=
  (∀ j : Fin n, position p w j ∈ S) ∧ position p w n ∉ S

/-- The fraction of all length-`n` words whose first exit occurs at time `n`. -/
noncomputable def exitProb (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (n : ℕ) : ℝ := by
  classical
  exact ((univ.filter (exits S p : (Fin n → Dir) → Prop)).card : ℝ) / 4 ^ n

/-- Expected first exit time, defined from its exit distribution. -/
noncomputable def expectedExit (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * exitProb S p n

/-- Uniform mean over the starting vertices of the cluster. -/
noncomputable def meanExit (S : Finset (ℤ × ℤ)) : ℝ :=
  (∑ p ∈ S, expectedExit S p) / S.card

/-- Nearest-neighbour steps with both endpoints in the cluster. -/
def adjacent (S : Finset (ℤ × ℤ)) (p q : ℤ × ℤ) : Prop :=
  p ∈ S ∧ q ∈ S ∧ ∃ d : Dir, q = p + step d

/-- Any two cluster vertices can be joined by steps inside the cluster. -/
def connected (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (adjacent S) p q

/-- The `m` by `m` square with coordinates from `0` to `m - 1`. -/
def square (m : ℕ) : Finset (ℤ × ℤ) :=
  ((range m) ×ˢ (range m)).image (fun p => ((p.1 : ℤ), (p.2 : ℤ)))

/-- Squares maximize mean first exit time among connected clusters of the same size. -/
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ S : Finset (ℤ × ℤ),
    S.card = m ^ 2 → connected S → meanExit S ≤ meanExit (square m)

private noncomputable def killed (S : Finset (ℤ × ℤ)) :
    (ℤ × ℤ → ℝ) →ₗ[ℝ] (ℤ × ℤ → ℝ) where
  toFun f p := if p ∈ S then (∑ d : Dir, f (p + step d)) / 4 else 0
  map_add' f g := by
    funext p
    dsimp
    split_ifs <;> simp only [sum_add_distrib, add_div, add_zero]
  map_smul' c f := by
    funext p
    dsimp
    split_ifs <;> simp only [← mul_sum, mul_div_assoc, mul_zero]

private def inside (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℝ := if p ∈ S then 1 else 0

private theorem exits_cons (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (n : ℕ)
    (d : Dir) (w : Fin n → Dir) :
    exits S p (Fin.cons d w) ↔ p ∈ S ∧ exits S (p + step d) w := by
  unfold exits
  rw [Fin.forall_fin_succ]
  change ((p ∈ S ∧ ∀ j : Fin n, position (p + step d) w j ∈ S) ∧
    position (p + step d) w n ∉ S) ↔ _
  exact and_assoc

private theorem exit_prob_zero (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    exitProb S p 0 = 1 - inside S p := by
  classical
  rw [exitProb, natCast_card_filter]
  simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, div_one]
  have he : ∀ w : Fin 0 → Dir, exits S p w ↔ p ∉ S := by
    intro w
    simp only [exits, position, IsEmpty.forall_iff, true_and]
  rw [he]
  by_cases hp : p ∈ S <;> simp only [inside, hp, not_true_eq_false, ite_false, ite_true] <;> norm_num

private theorem exit_prob_succ (S : Finset (ℤ × ℤ)) (n : ℕ) :
    (fun p => exitProb S p (n + 1)) = killed S (fun p => exitProb S p n) := by
  classical
  funext p
  simp only [exitProb, natCast_card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Dir).sum_comp, Fintype.sum_prod_type]
  change (∑ d : Dir, ∑ w : Fin n → Dir,
    if exits S p (Fin.cons d w) then (1 : ℝ) else 0) / 4 ^ (n + 1) =
    if p ∈ S then
      (∑ d : Dir, (∑ w : Fin n → Dir,
        if exits S (p + step d) w then (1 : ℝ) else 0) / 4 ^ n) / 4 else 0
  simp_rw [exits_cons]
  by_cases hp : p ∈ S
  · simp only [hp, true_and, ite_true, ← sum_div, pow_succ, div_div]
  · simp only [hp, false_and, ite_false, sum_const_zero, zero_div]

private theorem killed_mono (S : Finset (ℤ × ℤ)) : Monotone (killed S) := by
  intro f g h p
  change (if p ∈ S then _ else 0) ≤ (if p ∈ S then _ else 0)
  split_ifs
  · exact div_le_div_of_nonneg_right (sum_le_sum fun d _ => h _) (by norm_num)
  · exact le_rfl

private theorem killed_one (S : Finset (ℤ × ℤ)) : killed S (fun _ => 1) = inside S := by
  funext p
  change (if p ∈ S then _ else _) = if p ∈ S then _ else _
  norm_num

private theorem expected_of_certificate (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ → ℝ)
    (hz : ∀ p, p ∉ S → t p = 0)
    (hb : ∀ p ∈ S, 1 ≤ t p ∧ t p ≤ 43)
    (ht : ∀ p ∈ S, t p = 1 + (∑ d : Dir, t (p + step d)) / 4)
    (p : ℤ × ℤ) : expectedExit S p = t p := by
  classical
  let P := killed S
  let r : ℝ := 42 / 43
  have hr : 0 ≤ r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hi : (0 : ℤ × ℤ → ℝ) ≤ inside S := by
    intro q
    dsimp [inside]
    split_ifs <;> norm_num
  have hit : inside S ≤ t := by
    intro q
    change (if q ∈ S then 1 else 0) ≤ t q
    by_cases hq : q ∈ S
    · rw [ite_eq_left hq]
      exact (hb q hq).1
    · simp only [ite_eq_right hq, hz q hq, le_refl]
  have hcert : t = inside S + P t := by
    funext q
    change t q = (if q ∈ S then 1 else 0) + (if q ∈ S then _ else 0)
    by_cases hq : q ∈ S
    · rw [ite_eq_left hq, ite_eq_left hq]
      exact ht q hq
    · rw [ite_eq_right hq, ite_eq_right hq, hz q hq, add_zero]
  have hcontract : P t ≤ r • t := by
    intro q
    change (if q ∈ S then _ else 0) ≤ r * t q
    by_cases hq : q ∈ S
    · rw [ite_eq_left hq]
      have h := ht q hq
      have h43 := (hb q hq).2
      dsimp [r]
      linarith
    · rw [ite_eq_right hq, hz q hq, mul_zero]
  have hm : ∀ n : ℕ, Monotone (P ^ n) := by
    intro n
    rw [Module.End.coe_pow]
    exact (killed_mono S).iterate n
  have hdecay : ∀ n : ℕ, (P ^ n) t ≤ r ^ n • t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      calc
        (P ^ n) (P t) ≤ (P ^ n) (r • t) := hm n hcontract
        _ = r • (P ^ n) t := map_smul _ _ _
        _ ≤ r • (r ^ n • t) := by
          intro q
          exact mul_le_mul_of_nonneg_left (ih q) hr
        _ = r ^ (n + 1) • t := by rw [smul_smul, pow_succ']
  have he0 : (fun q => exitProb S q 0) = (fun _ => 1) - inside S := by
    funext q
    exact exit_prob_zero S q
  have hed : ∀ n : ℕ, (fun q => exitProb S q (n + 1)) =
      (P ^ n) (inside S) - (P ^ (n + 1)) (inside S) := by
    intro n
    induction n with
    | zero => rw [exit_prob_succ, he0, map_sub, killed_one]; simp [P]
    | succ n ih =>
      rw [exit_prob_succ, ih, map_sub, pow_succ' (n := n + 1), pow_succ' (n := n)]
      rfl
  let a : ℕ → ℝ := fun n => (P ^ n) (inside S) p
  let b : ℕ → ℝ := fun n => (P ^ n) t p
  have hab : ∀ n, 0 ≤ a n ∧ a n ≤ b n ∧ b n ≤ r ^ n * t p := by
    intro n
    refine ⟨?_, hm n hit p, hdecay n p⟩
    have h := hm n hi p
    simpa only [map_zero, Pi.zero_apply] using h
  have hab0 : ∀ n, 0 ≤ b n := fun n => (hab n).1.trans (hab n).2.1
  have hrec : ∀ n, a n = b n - b (n + 1) := by
    intro n
    have h := congrArg (fun f => (P ^ n) f p) hcert
    rw [map_add, ← Module.End.mul_apply, ← pow_succ] at h
    change b n = a n + b (n + 1) at h
    linarith
  have he : ∀ n, exitProb S p (n + 1) = a n - a (n + 1) := by
    intro n
    exact congrArg (fun f => f p) (hed n)
  have hs : ∀ N : ℕ, (∑ n ∈ range N, a n) = t p - b N := by
    intro N
    simp_rw [hrec]
    rw [sum_range_sub']
    simp [b]
  have hpartial : ∀ N : ℕ, (∑ n ∈ range (N + 1), (n : ℝ) * exitProb S p n) =
      t p - b N - (N : ℝ) * a N := by
    intro N
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    calc
      (∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) * exitProb S p (n + 1)) =
          ∑ n ∈ range N, (a n + ((n : ℝ) * a n - ((n + 1 : ℕ) : ℝ) * a (n + 1))) := by
        apply sum_congr rfl
        intro n _
        rw [he, Nat.cast_add, Nat.cast_one]
        ring
      _ = _ := by
        rw [sum_add_distrib, hs, sum_range_sub']
        simp only [Nat.cast_zero, zero_mul, zero_sub]
        ring
  have hb0 : Filter.Tendsto b Filter.atTop (𝓝 0) := by
    apply squeeze_zero hab0 (fun n => (hab n).2.2)
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const (t p)
  have hna0 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * a n) Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n) (hab n).1)
      (fun n => mul_le_mul_of_nonneg_left ((hab n).2.1.trans (hab n).2.2)
        (Nat.cast_nonneg n))
    simpa only [zero_mul, mul_assoc] using
      (tendsto_self_mul_const_pow_of_lt_one hr hr1).mul_const (t p)
  have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) * exitProb S p n := by
    intro n
    exact mul_nonneg (Nat.cast_nonneg n) (by unfold exitProb; positivity)
  apply HasSum.tsum_eq
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg (t p)).2
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  simp_rw [hpartial]
  simpa only [sub_zero] using (tendsto_const_nhds.sub hb0).sub hna0

private def disk : Finset (ℤ × ℤ) :=
  ((Icc (-6 : ℤ) 6) ×ˢ (Icc (-6 : ℤ) 6)).filter (fun p => p.1 ^ 2 + p.2 ^ 2 ≤ 37)

private theorem mem_disk (p : ℤ × ℤ) : p ∈ disk ↔ p.1 ^ 2 + p.2 ^ 2 ≤ 37 := by
  change p ∈ ((Icc (-6 : ℤ) 6) ×ˢ (Icc (-6 : ℤ) 6)).filter _ ↔ _
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]

private def orbit (p : ℤ × ℤ) : ℕ × ℕ :=
  (max p.1.natAbs p.2.natAbs, min p.1.natAbs p.2.natAbs)

private def diskNumerator (p : ℤ × ℤ) : ℤ :=
  match orbit p with
  | (0, 0) => 2955311541 | (1, 0) => 2886399328 | (1, 1) => 2816841781
  | (2, 0) => 2680953357 | (2, 1) => 2609459808 | (2, 2) => 2396809064
  | (3, 0) => 2342845632 | (3, 1) => 2267586178 | (3, 2) => 2046333894
  | (3, 3) => 1689887568 | (4, 0) => 1879607963 | (4, 1) => 1796056526
  | (4, 2) => 1555403914 | (4, 3) => 1195616816 | (4, 4) => 666720621
  | (5, 0) => 1307824316 | (5, 1) => 1205979197 | (5, 2) => 907959568
  | (5, 3) => 594806309 | (6, 0) => 664082055 | (6, 1) => 536427526
  | _ => 0

private def squareNumerator (p : ℤ × ℤ) : ℤ :=
  match orbit (p.1 - 5, p.2 - 5) with
  | (0, 0) => 83246922 | (1, 0) => 81274462 | (1, 1) => 79361003
  | (2, 0) => 75239080 | (2, 1) => 73502624 | (2, 2) => 68176671
  | (3, 0) => 64786770 | (3, 1) => 63343902 | (3, 2) => 58905798
  | (3, 3) => 51131799 | (4, 0) => 49330356 | (4, 1) => 48290576
  | (4, 2) => 45080980 | (4, 3) => 39412880 | (4, 4) => 30737643
  | (5, 0) => 28063662 | (5, 1) => 27517226 | (5, 2) => 25824826
  | (5, 3) => 22811258 | (5, 4) => 18117486 | (5, 5) => 11031203
  | _ => 0

private def diskA (p : ℤ × ℤ) : ℤ :=
  if p.1 ^ 2 + p.2 ^ 2 ≤ 37 then diskNumerator p else 0

private def squareA (p : ℤ × ℤ) : ℤ :=
  if 0 ≤ p.1 ∧ p.1 < 11 ∧ 0 ≤ p.2 ∧ p.2 < 11 then squareNumerator p else 0

private theorem mem_square_eleven (p : ℤ × ℤ) :
    p ∈ square 11 ↔ 0 ≤ p.1 ∧ p.1 < 11 ∧ 0 ≤ p.2 ∧ p.2 < 11 := by
  change p ∈ ((range 11) ×ˢ (range 11)).image _ ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    obtain ⟨hx, hy⟩ := mem_product.mp h
    have hx : x < 11 := mem_range.mp hx
    have hy : y < 11 := mem_range.mp hy
    change 0 ≤ (x : ℤ) ∧ (x : ℤ) < 11 ∧ 0 ≤ (y : ℤ) ∧ (y : ℤ) < 11
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hx,
      Int.natCast_nonneg _, by exact_mod_cast hy⟩
  · rintro ⟨hx0, hx, hy0, hy⟩
    refine ⟨(p.1.toNat, p.2.toNat), mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ?_⟩
    exact Prod.ext (Int.toNat_of_nonneg hx0) (Int.toNat_of_nonneg hy0)

set_option maxRecDepth 10000 in
private theorem disk_data : disk.card = 121 ∧
    (∀ p ∈ disk, 68912213 ≤ diskA p ∧ diskA p ≤ 43 * 68912213 ∧
      4 * diskA p = 4 * 68912213 + ∑ d : Dir, diskA (p + step d)) ∧
    (∑ p ∈ disk, diskA p) = 198008236169 := by
  decide

set_option maxRecDepth 10000 in
private theorem square_data : (square 11).card = 121 ∧
    (∀ p ∈ square 11, 1972460 ≤ squareA p ∧ squareA p ≤ 43 * 1972460 ∧
      4 * squareA p = 4 * 1972460 + ∑ d : Dir, squareA (p + step d)) ∧
    (∑ p ∈ square 11, squareA p) = 5622237966 := by
  decide

private def parent (p : ℤ × ℤ) : ℤ × ℤ :=
  if p.1 = 0 then (0, p.2 - p.2.sign) else (p.1 - p.1.sign, p.2)

set_option maxRecDepth 10000 in
private theorem disk_parent : ∀ p ∈ disk, p ≠ (0, 0) →
    parent p ∈ disk ∧ (parent p).1.natAbs + (parent p).2.natAbs < p.1.natAbs + p.2.natAbs ∧
      adjacent disk p (parent p) ∧ adjacent disk (parent p) p := by
  unfold adjacent
  decide

private theorem disk_connected : connected disk := by
  have paths : ∀ n : ℕ, ∀ p ∈ disk, p.1.natAbs + p.2.natAbs = n →
      Relation.ReflTransGen (adjacent disk) p (0, 0) ∧
      Relation.ReflTransGen (adjacent disk) (0, 0) p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp hn
      by_cases h0 : p = (0, 0)
      · subst p
        exact ⟨.refl, .refl⟩
      · obtain ⟨hm, hlt, hpm, hmp⟩ := disk_parent p hp h0
        obtain ⟨h1, h2⟩ := ih _ (hlt.trans_eq hn) (parent p) hm rfl
        exact ⟨h1.head hpm, h2.tail hmp⟩
  intro p hp q hq
  exact (paths _ p hp rfl).1.trans (paths _ q hq rfl).2

private theorem integer_certificate (S : Finset (ℤ × ℤ)) (A : ℤ × ℤ → ℤ) (D : ℤ)
    (hD : 0 < D) (hz : ∀ p, p ∉ S → A p = 0)
    (hc : ∀ p ∈ S, D ≤ A p ∧ A p ≤ 43 * D ∧
      4 * A p = 4 * D + ∑ d : Dir, A (p + step d))
    (p : ℤ × ℤ) : expectedExit S p = (A p : ℝ) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  apply expected_of_certificate S (fun q => (A q : ℝ) / D) ?_ ?_ ?_ p
  · intro q hq
    rw [hz q hq, Int.cast_zero, zero_div]
  · intro q hq
    obtain ⟨hl, hu, _⟩ := hc q hq
    constructor
    · apply (le_div_iff₀ hDr).2
      simpa only [one_mul] using (show (D : ℝ) ≤ A q by exact_mod_cast hl)
    · apply (div_le_iff₀ hDr).2
      exact_mod_cast hu
  · intro q hq
    have h : (4 : ℝ) * (A q : ℝ) = 4 * (D : ℝ) + ∑ d : Dir, (A (q + step d) : ℝ) := by
      exact_mod_cast (hc q hq).2.2
    rw [← sum_div]
    field_simp [ne_of_gt hDr]
    nlinarith

theorem result : ¬ claim := by
  have hd : ∀ p ∈ disk, expectedExit disk p = (diskA p : ℝ) / 68912213 := by
    intro p _
    apply integer_certificate disk diskA 68912213 (by norm_num) ?_ disk_data.2.1 p
    intro p hp
    exact ite_eq_right (fun h => hp ((mem_disk p).2 h))
  have hq : ∀ p ∈ square 11, expectedExit (square 11) p = (squareA p : ℝ) / 1972460 := by
    intro p _
    apply integer_certificate (square 11) squareA 1972460 (by norm_num) ?_ square_data.2.1 p
    intro p hp
    exact ite_eq_right (fun h => hp ((mem_square_eleven p).2 h))
  have hdm : meanExit disk = (198008236169 : ℝ) / 8338377773 := by
    unfold meanExit
    rw [disk_data.1]
    have hsum : (∑ p ∈ disk, expectedExit disk p) =
        ((∑ p ∈ disk, diskA p : ℤ) : ℝ) / 68912213 := by
      rw [Int.cast_sum, sum_div]
      exact sum_congr rfl hd
    rw [hsum, disk_data.2.2]
    norm_num
  have hqm : meanExit (square 11) = (2811118983 : ℝ) / 119333830 := by
    unfold meanExit
    rw [square_data.1]
    have hsum : (∑ p ∈ square 11, expectedExit (square 11) p) =
        ((∑ p ∈ square 11, squareA p : ℤ) : ℝ) / 1972460 := by
      rw [Int.cast_sum, sum_div]
      exact sum_congr rfl hq
    rw [hsum, square_data.2.2]
    norm_num
  intro h
  have hle := h 11 (by norm_num) disk (by rw [disk_data.1]; norm_num) disk_connected
  rw [hdm, hqm] at hle
  norm_num at hle

end D5.S3.StatisticalMechanics.RandomWalks.SquareClusterExitTimeRefutation
