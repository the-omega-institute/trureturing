/- GID: D5/S3/Combinatorics/Partitions/CommonBlockWeights
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/CommonBlockWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One clipped weight family allocates all compatible grouped demands. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.GCD.Basic

/-! Simultaneous grouped allocation by a fixed family of integer weights. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.CommonBlockWeights

open Finset

private theorem select_bounded_counts {I : Type*} [DecidableEq I]
    (s : Finset I) (capacity : I → ℕ) {N : ℕ} (enough : N ≤ ∑ i ∈ s, capacity i) :
    ∃ a : I → ℕ, (∀ i ∈ s, a i ≤ capacity i) ∧ ∑ i ∈ s, a i = N := by
  induction s using Finset.induction_on generalizing N with
  | empty =>
    have zero : N = 0 := Nat.eq_zero_of_le_zero (by simpa using enough)
    exact ⟨fun _ => 0, by simp, by simp [zero]⟩
  | @insert j s hjs ih =>
    let first := min N (capacity j)
    have remaining : N - first ≤ ∑ i ∈ s, capacity i := by
      rw [Finset.sum_insert hjs] at enough
      by_cases h : N ≤ capacity j
      · simp [first, min_eq_left h]
      · have eq : first = capacity j := min_eq_right (le_of_not_ge h)
        omega
    obtain ⟨rest, hrest, total⟩ := ih remaining
    let a := Function.update rest j first
    refine ⟨a, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with eq | hi
      · subst i
        simpa only [a, Function.update_self] using min_le_right N (capacity j)
      · have neq : i ≠ j := by
          intro eq
          exact hjs (by simpa only [eq] using hi)
        simpa only [a, Function.update_of_ne neq] using hrest i hi
    · rw [Finset.sum_insert hjs]
      have others : (∑ i ∈ s, a i) = ∑ i ∈ s, rest i :=
        Finset.sum_congr rfl fun i hi =>
          Function.update_of_ne (show i ≠ j by
            intro eq
            exact hjs (by simpa only [eq] using hi)) first rest
      rw [others, total]
      simp only [a, Function.update_self]
      exact Nat.add_sub_of_le (min_le_left N (capacity j))

/-- If the old total covers the maximal combined loss from rounding down capacities, then
all requested new equal-weight blocks fit within the target counts. -/
private theorem extend_block_allocation {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℕ) {d M old : ℕ} (positive : 0 < d)
    (threshold : (Fintype.card I - 1) * (d - 1) ≤ old)
    (total : ∑ i, x i = old + M * d) :
    ∃ a : I → ℕ, (∑ i, a i = M) ∧ (∀ i, a i * d ≤ x i) ∧
      ∑ i, (x i - a i * d) = old := by
  classical
  let C := ∑ i, x i / d
  let R := ∑ i, x i % d
  have equation : R + C * d = old + M * d := by
    dsimp only [R, C]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← total]
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa only [Nat.mul_comm (x i / d) d] using Nat.mod_add_div (x i) d
  have remainder : R ≤ Fintype.card I * (d - 1) := by
    calc
      R ≤ ∑ i : I, (d - 1) := Finset.sum_le_sum fun i _ => by
        have lt := Nat.mod_lt (x i) positive
        omega
      _ = Fintype.card I * (d - 1) := by simp
  have extra :
      Fintype.card I * (d - 1) = (Fintype.card I - 1) * (d - 1) + (d - 1) := by
    have card : 1 ≤ Fintype.card I := Fintype.card_pos
    conv_lhs => rw [← Nat.sub_add_cancel card]
    rw [Nat.add_mul, Nat.one_mul]
  have enough : M ≤ C := by
    by_contra h
    have multiple : C * d + d ≤ M * d := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right d (by omega)
    omega
  obtain ⟨a, ha, counts⟩ := select_bounded_counts (univ : Finset I) (fun i => x i / d) enough
  have follows (i : I) : a i * d ≤ x i :=
    (Nat.mul_le_mul_right _ (ha i (mem_univ _))).trans (Nat.div_mul_le_self _ _)
  refine ⟨a, counts, follows, ?_⟩
  have recover : (∑ i, (x i - a i * d)) + M * d = old + M * d := by
    have selected : (∑ i, a i * d) = M * d := by rw [← Finset.sum_mul, counts]
    rw [← selected, ← Finset.sum_add_distrib]
    have exactTotal : ∑ i, (x i - a i * d + a i * d) = ∑ i, x i :=
      Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (follows i)
    rw [exactTotal, total, selected]
  omega



/-- Exact allocations of all admissible grouped demands using shared block weights. -/
def CoversAllocations {n : ℕ} (k q : ℕ) (w : Fin n → ℕ) : Prop :=
  ∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ, (∑ i, x i) = U * q →
    ∃ a : Fin n → Fin t → ℕ,
      (∀ j, ∑ i, a j i = U) ∧ (∀ i, ∑ j, a j i * w j = x i)

private theorem cover_by_capacity {k n q : ℕ} (bound : q ≤ (∑ i ∈ range n, (k + 1) ^ i)) :
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w := by
  induction n generalizing q with
  | zero =>
    have q0 : q = 0 := Nat.eq_zero_of_le_zero (by simpa using bound)
    subst q
    refine ⟨fun j => j.elim0, by simp, ?_⟩
    intro t U _ _ x sum
    refine ⟨fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro i
    have le : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (mem_univ i)
    simp only [Nat.mul_zero] at sum
    have eq : x i = 0 := by omega
    simp [eq]
  | succ n ih =>
    let old := min q (∑ i ∈ range n, (k + 1) ^ i)
    let d := q - old
    have totals : old + d = q := Nat.add_sub_of_le (min_le_left _ _)
    have dBound : d ≤ k * old + 1 := by
      by_cases fit : q ≤ (∑ i ∈ range n, (k + 1) ^ i)
      · simp [d, old, min_eq_left fit]
      · change q - min q (∑ i ∈ range n, (k + 1) ^ i) ≤ k * min q (∑ i ∈ range n, (k + 1) ^ i) + 1
        rw [min_eq_right (le_of_not_ge fit)]
        have b : q ≤ (k + 1) * (∑ i ∈ range n, (k + 1) ^ i) + 1 := by
          simpa only [geom_sum_succ] using bound
        rw [Nat.add_mul, Nat.one_mul] at b
        omega
    obtain ⟨w, sumW, covers⟩ := ih (min_le_right q (∑ i ∈ range n, (k + 1) ^ i))
    refine ⟨Fin.snoc w d, ?_, ?_⟩
    · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, sumW] using totals
    · intro t U tpos hblocks x xsum
      let _ : Nonempty (Fin t) := ⟨⟨0, tpos⟩⟩
      have xsum' : ∑ i, x i = U * old + U * d := by rw [← Nat.mul_add, totals, xsum]
      have step :
          ∃ a : Fin t → ℕ, (∑ i, a i = U) ∧ (∀ i, a i * d ≤ x i) ∧
            ∑ i, (x i - a i * d) = U * old := by
        by_cases z : d = 0
        · let a (i : Fin t) := if i = ⟨0, tpos⟩ then U else 0
          exact ⟨a, by simp [a], by simp [z], by simpa only [z, Nat.mul_zero, Nat.sub_zero, Nat.add_zero] using xsum'⟩
        · apply extend_block_allocation x (Nat.pos_of_ne_zero z) _ xsum'
          rw [Fintype.card_fin]
          calc
            (t - 1) * (d - 1) ≤ (t - 1) * (k * old) :=
              Nat.mul_le_mul_left _ (by omega)
            _ = (k * (t - 1)) * old := by rw [← Nat.mul_assoc, Nat.mul_comm (t - 1) k]
            _ ≤ U * old := Nat.mul_le_mul_right _ hblocks
      obtain ⟨a, count, fits, leftover⟩ := step
      obtain ⟨rest, hcount, hmass⟩ := covers t U tpos hblocks (fun i => x i - a i * d) leftover
      refine ⟨Fin.snoc rest a, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_last] using count
        · simpa only [Fin.snoc_castSucc] using hcount j
      · intro i
        simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hmass] using
          Nat.sub_add_cancel (fits i)

/-- One clipped weight family allocates every demand vector within each compatible block budget. -/
theorem common_weights_for_allocations {k n q : ℕ} (kpos : 0 < k)
    (budget : k * q + 1 ≤ (k + 1) ^ n) :
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w := by
  rw [← geom_sum_mul_add k n, Nat.mul_comm (∑ i ∈ range n, (k + 1) ^ i) k] at budget
  exact cover_by_capacity (Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right budget) kpos)

private theorem bundle_last_weight {k n q p b t U : ℕ} {w : Fin n → ℕ}
    (cover : CoversAllocations k q w) (ppos : 0 < p)
    (whole : b ∣ U) (tpos : 0 < t) (block_bound : k * (t - 1) ≤ U)
    (rounding : (t - 1) * (p - 1) ≤ U * q)
    (x : Fin t → ℕ) (total : ∑ i, x i = U * q + (U / b) * p) :
    ∃ a : Fin (n + 1) → Fin t → ℕ,
      (∀ j, ∑ i, a j i = U) ∧
      (∀ i, ∑ j, a j i * (Fin.snoc (α := fun _ => ℕ) (fun j => b * w j) p j) = b * x i) := by
  let _ : Nonempty (Fin t) := ⟨⟨0, tpos⟩⟩
  have hround : (Fintype.card (Fin t) - 1) * (p - 1) ≤ U * q := by
    simpa only [Fintype.card_fin] using rounding
  obtain ⟨bundles, all_bundles, fits, leftover⟩ :=
    extend_block_allocation x ppos hround total
  obtain ⟨old, old_count, old_mass⟩ := cover t U tpos block_bound
    (fun i => x i - bundles i * p) leftover
  refine ⟨Fin.snoc old (fun i => b * bundles i), ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, ← Finset.mul_sum, all_bundles]
      rw [Nat.mul_comm, Nat.div_mul_cancel whole]
    · simpa only [Fin.snoc_castSucc] using old_count j
  · intro i
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have old_scaled : (∑ j, old j i * (b * w j)) = b * (x i - bundles i * p) := by
      rw [← old_mass i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ac_rfl
    rw [old_scaled, Nat.mul_assoc, ← Nat.mul_add, Nat.sub_add_cancel (fits i)]

private theorem common_bundled_weights {k n A b K : ℕ}
    (kPositive : 0 < k) (bPositive : 0 < b) (KPositive : 0 < K)
    (factor : K * b = k) (atLeastOne : b ≤ A)
    (capacity : K * A + 1 ≤ (K + 1) * (k + 1)^n) :
    ∃ w : Fin (n + 1) → ℕ, (∑ j, w j = A) ∧
      ∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → b ∣ U → ∀ x : Fin t → ℕ,
        b * (∑ i, x i) = U * A →
        ∃ a : Fin (n + 1) → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = b * x i) := by
  let C := ∑ i ∈ range n, (k + 1)^i
  let T := min (A / b) C
  let p := A - b * T
  have C_eq : k * C + 1 = (k + 1)^n := by
    dsimp [C]
    rw [Nat.mul_comm]
    exact geom_sum_mul_add k n
  have bT : b * T ≤ A := by
    calc
      b * T ≤ b * (A / b) := Nat.mul_le_mul_left b (min_le_left _ _)
      _ ≤ A := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self A b
  have decomposition : b * T + p = A := Nat.add_sub_of_le bT
  have bound : p ≤ k * T + 1 := by
    by_cases h : A / b ≤ C
    · have Teq : T = A / b := min_eq_left h
      have oneLe : 1 ≤ T := by
        rw [Teq]
        exact (Nat.le_div_iff_mul_le bPositive).mpr (by simpa using atLeastOne)
      have pb : p < b := by
        have split := Nat.mod_add_div A b
        rw [← Teq] at split
        have modLT := Nat.mod_lt A bPositive
        omega
      have bk : b ≤ k := by
        calc
          b = 1 * b := (Nat.one_mul _).symm
          _ ≤ K * b := Nat.mul_le_mul_right _ (by omega)
          _ = k := factor
      have kT : k ≤ k * T := by simpa using Nat.mul_le_mul_left k oneLe
      omega
    · have Teq : T = C := min_eq_right (le_of_not_ge h)
      have c : K * (b * C + p) + 1 ≤ (K + 1) * (k * C + 1) := by
        rw [← C_eq] at capacity
        simpa only [Teq] using (show K * (b * T + p) + 1 ≤ (K + 1) * (k * C + 1) from
          decomposition ▸ capacity)
      rw [Nat.mul_add, ← Nat.mul_assoc, factor, Nat.add_mul, Nat.one_mul] at c
      have product : K * p ≤ K * (k * C + 1) := by omega
      simpa only [Teq] using Nat.le_of_mul_le_mul_left product KPositive
  have Tcapacity : k * T + 1 ≤ (k + 1)^n := by
    rw [← C_eq]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (min_le_right _ _)) _
  obtain ⟨w, total, cover⟩ := common_weights_for_allocations kPositive Tcapacity
  refine ⟨Fin.snoc (α := fun _ => ℕ) (fun j => b * w j) p, ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Finset.mul_sum, total, decomposition]
  · intro t U tpos blocks whole x exactTotal
    have hUB : b * (U / b) = U := by
      rw [Nat.mul_comm, Nat.div_mul_cancel whole]
    have normalized : (∑ i, x i) = U * T + (U / b) * p := by
      apply Nat.eq_of_mul_eq_mul_left bPositive
      rw [exactTotal, Nat.mul_add, ← Nat.mul_assoc b (U / b) p, hUB]
      rw [← decomposition, Nat.mul_add]
      congr 1
      ac_rfl
    have round : (t - 1) * (p - 1) ≤ U * T := by
      have p_le : p - 1 ≤ k * T := by omega
      calc
        _ ≤ (t - 1) * (k * T) := Nat.mul_le_mul_left _ p_le
        _ = (k * (t - 1)) * T := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ blocks
    by_cases pzero : p = 0
    · have leave : ∑ i, x i = U * T := by simpa [pzero] using normalized
      obtain ⟨old, old_count, old_mass⟩ := cover t U tpos blocks x leave
      let unused (i : Fin t) := if i = ⟨0, tpos⟩ then U else 0
      refine ⟨Fin.snoc old unused, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [unused]
        · simpa only [Fin.snoc_castSucc] using old_count j
      · intro i
        simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, pzero,
          Nat.mul_zero, Nat.add_zero]
        rw [← old_mass i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ac_rfl
    exact bundle_last_weight cover (Nat.pos_of_ne_zero pzero) whole tpos blocks round x normalized

private theorem common_bundled_weights_all_totals {k n A b K : ℕ}
    (hb : 0 < b) (hK : 0 < K) (factor : K * b = k)
    (cap : K * A + 1 ≤ (K + 1) * (k + 1)^n) :
    ∃ w : Fin (n + 1) → ℕ, (∑ j, w j = A) ∧
      ∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → b ∣ U → ∀ x : Fin t → ℕ,
        b * (∑ i, x i) = U * A →
        ∃ a : Fin (n + 1) → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = b * x i) := by
  have hk : 0 < k := factor ▸ Nat.mul_pos hK hb
  by_cases large : b ≤ A
  · exact common_bundled_weights hk hb hK factor large cap
  have bk : b ≤ k := by
    calc
      b = 1 * b := (Nat.one_mul _).symm
      _ ≤ K * b := Nat.mul_le_mul_right _ hK
      _ = k := factor
  have bound : k * A + 1 ≤ (k + 1)^(n + 1) := by
    cases n with
    | zero =>
      simp only [pow_zero, Nat.mul_one, Nat.add_le_add_iff_right] at cap
      have A1 : A ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using cap) hK
      simpa using Nat.add_le_add_right (Nat.mul_le_mul_left k A1) 1
    | succ n =>
      have Ak : A ≤ k := (Nat.le_of_lt (Nat.lt_of_not_ge large)).trans bk
      calc
        _ ≤ k * k + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left k Ak) 1
        _ ≤ (k + 1)^2 := by rw [pow_two, Nat.add_mul, Nat.mul_add]; simp; omega
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨w, hw, covers⟩ := common_weights_for_allocations hk bound
  refine ⟨w, hw, ?_⟩
  intro t U ht hU _ x total
  have exactSum : ∑ i, b * x i = U * A := by rwa [← Finset.mul_sum]
  exact covers t U ht hU (fun i => b * x i) exactSum

/-- One family of numerator weights distributes every compatible set of fractional
demands. The demand sum supplies the bundle divisibility after reduction. -/
theorem common_fractional_allocations {k n A b K : ℕ}
    (hk : 0 < k) (factor : K * b = k)
    (cap : K * A + 1 ≤ (K + 1) * (k + 1)^n) :
    ∃ w : Fin (n + 1) → ℕ, (∑ j, w j = A) ∧
      ∀ t U : ℕ, (0 < t ∨ U = 0) → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
        b * (∑ i, x i) = U * A →
        ∃ a : Fin (n + 1) → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = b * x i) := by
  have prodPos : 0 < K * b := factor.symm ▸ hk
  have hb : 0 < b := Nat.pos_of_ne_zero (fun zero => by simp [zero] at prodPos)
  have hK : 0 < K := Nat.pos_of_ne_zero (fun zero => by simp [zero] at prodPos)
  let g := b.gcd A
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hb
  obtain ⟨b', A', cop, eb, ea⟩ := Nat.exists_coprime b A
  change b = b' * g at eb
  change A = A' * g at ea
  have bscaled : g * b' = b := by rw [eb, Nat.mul_comm]
  have ascaled : g * A' = A := by rw [ea, Nat.mul_comm]
  have hb' : 0 < b' := Nat.pos_of_ne_zero fun zero => by simp [zero] at eb; omega
  let K' := K * g
  have hKK' : K ≤ K' := by simpa [K'] using Nat.mul_le_mul_left K hg
  have factor' : K' * b' = k := by rw [show K' * b' = K * (g * b') by simp [K', Nat.mul_assoc], bscaled, factor]
  have cap' : K' * A' + 1 ≤ (K' + 1) * (k + 1)^n := by
    calc
      K' * A' + 1 = K * A + 1 := by simp [K', Nat.mul_assoc, ascaled]
      _ ≤ _ := cap
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right hKK' 1)
  obtain ⟨w, hw, cover⟩ := common_bundled_weights_all_totals hb' (lt_of_lt_of_le hK hKK') factor' cap'
  refine ⟨fun j => g * w j, by rw [← Finset.mul_sum, hw, ascaled], ?_⟩
  intro t U feasible blocks x total
  by_cases ht : 0 < t
  swap
  · have tzero : t = 0 := by omega
    have Uzero : U = 0 := feasible.resolve_left ht
    subst t
    subst U
    exact ⟨fun _ i => i.elim0, by simp, fun i => i.elim0⟩
  have smaller : b' * (∑ i, x i) = U * A' := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      _ = b * (∑ i, x i) := by rw [← bscaled, Nat.mul_assoc]
      _ = U * A := total
      _ = _ := by rw [← ascaled]; ac_rfl
  have whole : b' ∣ U := cop.dvd_of_dvd_mul_right ⟨∑ i, x i, smaller.symm⟩
  obtain ⟨a, counts, mass⟩ := cover t U ht blocks whole x smaller
  refine ⟨a, counts, fun i => ?_⟩
  rw [← bscaled, Nat.mul_assoc, ← mass i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    change a j i * (g * w j) = g * (a j i * w j)
    ac_rfl

end D5.S3.Combinatorics.Partitions.CommonBlockWeights
