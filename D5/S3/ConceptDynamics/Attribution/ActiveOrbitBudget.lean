/- GID: D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ActiveOrbitBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Active orbit columns determine the eventual period of rational event budgets. -/

import D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
import Mathlib.Algebra.Order.Archimedean.Basic

import D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Rat.Lemmas

namespace D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget

open Finset
open UniformTableCalibration (form integer_optimum count_pos Orbit orbitCount)

set_option maxHeartbeats 900000 in
private theorem positive_integer_fiber {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (w : I → ℤ)
    (normalization : ∃ i, ∀ j, 0 < A i j)
    (x : J → ℝ) (hx : ∀ j, 0 < x j)
    (equation : ∀ i, ∑ j, (A i j : ℝ) * x j = w i) :
    ∃ (B : ℕ) (p : J → ℤ), 0 < B ∧ (∀ j, 0 < p j) ∧
      ∀ i, ∑ j, A i j * p j = (B : ℤ) * w i := by
  classical
  choose L hL using fun j => exists_nat_one_div_lt (hx j)
  let k : ℕ := (∑ j, L j) + 1
  have hk : 0 < k := Nat.zero_lt_succ _
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have size (j : J) : (1 : ℝ) ≤ (k : ℝ) * x j := by
    have hLk : L j + 1 ≤ k := Nat.add_le_add_right
      (Finset.single_le_sum (fun j _ => Nat.zero_le (L j)) (Finset.mem_univ j)) 1
    have hLr : (L j : ℝ) + 1 ≤ k := by exact_mod_cast hLk
    have positive : (0 : ℝ) < (L j : ℝ) + 1 := by positivity
    have size₀ := (div_lt_iff₀ positive).mp (hL j)
    rw [mul_comm] at size₀
    exact size₀.le.trans (mul_le_mul_of_nonneg_right hLr (hx j).le)
  let z (i : I) : ℤ := (k : ℤ) * w i - ∑ j, A i j
  have feasible : ∃ y : J → ℝ, (∀ j, 0 ≤ y j) ∧
      (∀ i, form (fun j => (A i j : ℝ)) y = (z i : ℝ)) ∧
      ∀ t : J → ℝ, (∀ j, 0 ≤ t j) →
        (∀ i, form (fun j => (A i j : ℝ)) t = (z i : ℝ)) → form 0 t ≤ form 0 y := by
    refine ⟨fun j => (k : ℝ) * x j - 1, fun j => sub_nonneg.mpr (size j), ?_, ?_⟩
    · intro i
      unfold form z
      push_cast
      have step (j : J) : (A i j : ℝ) * ((k : ℝ) * x j - 1) =
          (k : ℝ) * ((A i j : ℝ) * x j) - (A i j : ℝ) := by ring
      simp_rw [step]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, equation]
    · intro t _ _
      simp [form]
  obtain ⟨y, _, hAy, _, rows, _, hd, n, hn⟩ :=
    integer_optimum A (fun i => (z i : ℝ)) 0 normalization feasible 1 (by decide) z
      (fun _ => by norm_num)
  let d : ℕ := (A.submatrix rows Subtype.val).det.natAbs
  have hdpos : 0 < d := Int.natAbs_pos.mpr hd
  let p (j : J) : ℤ := (n j : ℤ) + d
  refine ⟨d * k, p, Nat.mul_pos hdpos hk, ?_, ?_⟩
  · intro j
    have hdint : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
    exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg _) hdint
  · intro i
    have scaled (j : J) : ((n j : ℕ) : ℝ) = (d : ℝ) * y j := by
      simpa [d] using hn j
    have target : (∑ j, (A i j : ℝ) * (p j : ℝ)) =
        ((d * k : ℕ) : ℝ) * (w i : ℝ) := by
      simp only [p, Int.cast_add, Int.cast_natCast, Nat.cast_mul, scaled]
      have step (j : J) : (A i j : ℝ) * ((d : ℝ) * y j + d) =
          (d : ℝ) * ((A i j : ℝ) * y j) + (d : ℝ) * (A i j : ℝ) := by ring
      simp_rw [step]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← form, hAy]
      simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
      ring
    exact_mod_cast target


set_option maxHeartbeats 900000 in
private theorem positive_integer_fiber_from_coordinate_witnesses {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (w : I → ℤ)
    (normalization : ∃ i, ∀ j, 0 < A i j)
    (feasible : ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, ∑ j, (A i j : ℝ) * x j = w i))
    (active : ∀ j : J, ∃ x : J → ℝ, 0 < x j ∧ (∀ k, 0 ≤ x k) ∧
      (∀ i, ∑ k, (A i k : ℝ) * x k = w i)) :
    ∃ (B : ℕ) (p : J → ℤ), 0 < B ∧ (∀ j, 0 < p j) ∧
      ∀ i, ∑ j, A i j * p j = (B : ℤ) * w i := by
  classical
  obtain ⟨base, hbase, hbaseA⟩ := feasible
  choose x hx hnn hxA using active
  let f (j : J) : ℝ := (base j + ∑ k, x k j) / ((Fintype.card J : ℝ) + 1)
  have cardPos : (0 : ℝ) < (Fintype.card J : ℝ) + 1 := by positivity
  have pos (j : J) : 0 < f j := by
    have hs : 0 < ∑ k, x k j :=
      (sum_pos_iff_of_nonneg (fun k _ => hnn k j)).mpr ⟨j, mem_univ j, hx j⟩
    exact div_pos (add_pos_of_nonneg_of_pos (hbase j) hs) cardPos
  have equation (i : I) : ∑ j, (A i j : ℝ) * f j = w i := by
    have product (j : J) : (A i j : ℝ) * (base j + ∑ k, x k j) =
        (A i j : ℝ) * base j + ∑ k, (A i j : ℝ) * x k j := by
      rw [mul_add, Finset.mul_sum]
    simp only [f, mul_div_assoc', ← Finset.sum_div, product, Finset.sum_add_distrib]
    rw [hbaseA, Finset.sum_comm]
    simp only [hxA, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (div_eq_iff cardPos.ne').mpr (by ring)
  exact positive_integer_fiber A w normalization f pos equation


/-- A column is active if it has positive weight in a feasible nonnegative solution. -/
def Active {I J : Type*} [Fintype J] (A : Matrix I J ℤ) (w : I → ℤ) (j : J) : Prop :=
  ∃ x : J → ℝ, 0 < x j ∧ (∀ k, 0 ≤ x k) ∧
    (∀ i, ∑ k, (A i k : ℝ) * x k = w i)

set_option maxHeartbeats 900000 in
open Classical in
private theorem positive_integer_fiber_on_active_columns {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (w : I → ℤ)
    (normalization : ∃ i, ∀ j, 0 < A i j)
    (feasible : ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, ∑ j, (A i j : ℝ) * x j = w i)) :
    ∃ (B : ℕ) (p : {j // Active A w j} → ℤ), 0 < B ∧ (∀ j, 0 < p j) ∧
      ∀ i, ∑ j, A i j.val * p j = (B : ℤ) * w i := by
  let A' : Matrix I {j // Active A w j} ℤ := A.submatrix id Subtype.val
  have restriction (x : J → ℝ) (h₀ : ∀ j, 0 ≤ x j)
      (eq : ∀ i, ∑ j, (A i j : ℝ) * x j = w i) (i : I) :
      ∑ j : {j // Active A w j}, (A' i j : ℝ) * x j.val = w i := by
    change (∑ j : {j // Active A w j}, (A i j.val : ℝ) * x j.val) = w i
    rw [← eq i]
    calc
      _ = ∑ j ∈ univ.filter (Active A w), (A i j : ℝ) * x j :=
        ((univ.filter (Active A w)).sum_subtype (p := Active A w) (by simp) (fun j => (A i j : ℝ) * x j)).symm
      _ = _ := ?_
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ outside
    have hz : x j = 0 := le_antisymm
      (le_of_not_gt fun hp => outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hp, h₀, eq⟩))
      (h₀ j)
    simp [hz]
  obtain ⟨i, hi⟩ := normalization
  apply positive_integer_fiber_from_coordinate_witnesses A' w ⟨i, fun j => hi j.val⟩
  · obtain ⟨x, h₀, eq⟩ := feasible
    exact ⟨fun j => x j.val, fun j => h₀ j.val, restriction x h₀ eq⟩
  · intro j
    obtain ⟨x, hj, h₀, eq⟩ := j.property
    exact ⟨fun k => x k.val, hj, fun k => h₀ k.val, restriction x h₀ eq⟩


set_option maxHeartbeats 900000 in
open Classical in
private theorem active_integer_degrees_iff {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (w : I → ℤ) (k : ℕ) (hk : 0 < k) :
    (∃ n : {j // Active A w j} → ℤ, (∀ j, 0 ≤ n j) ∧
      ∀ i, ∑ j, A i j.val * n j = (k : ℤ) * w i) ↔
      ∃ n : J → ℤ, (∀ j, 0 ≤ n j) ∧ ∀ i, ∑ j, A i j * n j = (k : ℤ) * w i := by
  have sumActive (f : J → ℤ)
      (vanish : ∀ j, ¬ Active A w j → f j = 0) :
      (∑ j : {j // Active A w j}, f j.val) = ∑ j, f j := by
    calc
      _ = ∑ j ∈ univ.filter (Active A w), f j :=
        ((univ.filter (Active A w)).sum_subtype (p := Active A w) (by simp) f).symm
      _ = _ := Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj =>
        vanish j (fun active => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, active⟩))
  constructor
  · rintro ⟨n, nn, eq⟩
    let m (j : J) : ℤ := if h : Active A w j then n ⟨j, h⟩ else 0
    refine ⟨m, fun j => ?_, fun i => ?_⟩
    · by_cases active : Active A w j
      · simpa [m, active] using nn ⟨j, active⟩
      · simp [m, active]
    · rw [← sumActive (fun j => A i j * m j)]
      · convert eq i using 1
        apply Finset.sum_congr rfl
        intro j _
        simp [m, j.property]
      · intro j outside
        simp [m, outside]
  · rintro ⟨n, nn, eq⟩
    have kr : (0 : ℝ) < k := by exact_mod_cast hk
    let x (j : J) : ℝ := (n j : ℝ) / (k : ℝ)
    have xnn (j : J) : 0 ≤ x j := div_nonneg (by exact_mod_cast nn j) kr.le
    have xeq (i : I) : ∑ j, (A i j : ℝ) * x j = w i := by
      have raw : ∑ j, (A i j : ℝ) * (n j : ℝ) = (k : ℝ) * (w i : ℝ) := by
        exact_mod_cast eq i
      rw [show (∑ j, (A i j : ℝ) * x j) = (∑ j, (A i j : ℝ) * (n j : ℝ)) / (k : ℝ) by
        simp only [x, mul_div_assoc', Finset.sum_div]]
      rw [raw]
      field_simp
    have inactive (j : J) (outside : ¬ Active A w j) : n j = 0 := by
      by_contra hn
      have pos : 0 < n j := lt_of_le_of_ne (nn j) (Ne.symm hn)
      exact outside ⟨x, div_pos (by exact_mod_cast pos) kr, xnn, xeq⟩
    refine ⟨fun j => n j.val, fun j => nn j.val, fun i => ?_⟩
    rw [sumActive (fun j => A i j * n j) (fun j no => by simp [inactive j no]), eq i]


open Finset
open D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
open D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees (countedDegrees eventual_counts)

universe u v w

open Classical in
private theorem rational_event_budget_iff {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    (E : I → Finset T) (q : I → ℚ) (m : ℕ) (w : I → ℤ)
    (representation : ∀ i, (w i : ℚ) = m * q i)
    (normalization : ∃ i, E i = univ ∧ q i = 1)
    (N k : ℕ) (positive : 0 < N) (scaled : N = m * k) :
    k ∈ countedDegrees (orbitEventMatrix (G := G) E) w ↔
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        Fintype.card S = N ∧ (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ i, ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) / N = q i := by
  classical
  rw [orbit_event_counts_match_fiber]
  have posQ : (N : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have coeff (i : I) : (k : ℚ) * (w i : ℚ) = (N : ℚ) * q i := by
    rw [scaled, Nat.cast_mul, representation]
    ring
  constructor
  · rintro ⟨S, _, _, f, equiv, fixed, counts⟩
    have scaledCounts (i : I) :
        ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) = (N : ℚ) * q i := by
      have integers := counts i
      have inQ : ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) =
          (k : ℚ) * (w i : ℚ) := by exact_mod_cast integers
      exact inQ.trans (coeff i)
    have cardinal : Fintype.card S = N := by
      obtain ⟨i, events, norm⟩ := normalization
      have total := scaledCounts i
      simp [events, norm, Finset.sum_const, Finset.card_univ] at total
      exact_mod_cast total
    refine ⟨S, inferInstance, inferInstance, f, cardinal, equiv, fixed, fun i => ?_⟩
    exact (div_eq_iff posQ).mpr (by simpa [mul_comm] using scaledCounts i)
  · rintro ⟨S, _, _, f, _, equiv, fixed, masses⟩
    refine ⟨S, inferInstance, inferInstance, f, equiv, fixed, fun i => ?_⟩
    have actual := (div_eq_iff posQ).mp (masses i)
    have raw : ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) =
        (k : ℚ) * (w i : ℚ) := by simpa [coeff i, mul_comm] using actual
    exact_mod_cast raw


open Classical in
/-- The integer event matrix restricted to active orbit columns. -/
noncomputable def restrictedOrbitMap {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    (E : I → Finset T) (w : I → ℤ) :
    ({o // Active (fun i o => (orbitCount (G := G) (E i) o : ℤ)) w o} → ℤ)
      →+ (I → ℤ) where
  toFun n i := ∑ o, (orbitCount (G := G) (E i) o.val : ℤ) * n o
  map_zero' := by ext i; simp
  map_add' n m := by ext i; simp [mul_add, Finset.sum_add_distrib]

open Classical in
private theorem active_rational_event_budget_iff {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    (E : I → Finset T) (q : I → ℚ) (m : ℕ) (w : I → ℤ)
    (representation : ∀ i, (w i : ℚ) = m * q i)
    (normalization : ∃ i, E i = univ ∧ q i = 1)
    (N k : ℕ) (positive : 0 < N) (scaled : N = m * k) :
    k ∈ countedDegrees (restrictedOrbitMap (G := G) E w) w ↔
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        Fintype.card S = N ∧ (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ i, ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) / N = q i := by
  have hk : 0 < k := by
    have prod : 0 < m * k := scaled ▸ positive
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at prod)
  have bridge : k ∈ countedDegrees (restrictedOrbitMap (G := G) E w) w ↔
      k ∈ countedDegrees (orbitEventMatrix (G := G) E) w := by
    let M : Matrix I (Orbit G T) ℤ := fun i o => (orbitCount (G := G) (E i) o : ℤ)
    change (∃ n : {o // Active M w o} → ℤ, (∀ j, 0 ≤ n j) ∧
      restrictedOrbitMap (G := G) E w n = k • w) ↔
      ∃ n : Orbit G T → ℤ, (∀ j, 0 ≤ n j) ∧ orbitEventMatrix (G := G) E n = k • w
    simp only [funext_iff]
    exact active_integer_degrees_iff M w k hk
  exact bridge.trans (rational_event_budget_iff E q m w representation normalization N k positive scaled)


open Classical in
private theorem positive_restricted_orbit_fiber {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)] [Fintype I]
    (E : I → Finset T) (w : I → ℤ) (total : ∃ i, E i = univ)
    (feasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ i, ∑ o, (orbitCount (E i) o : ℝ) * x o = w i) :
    ∃ (B : ℕ) (p : {o // Active (fun i o => (orbitCount (G := G) (E i) o : ℤ)) w o} → ℤ),
      0 < B ∧ (∀ j, 0 < p j) ∧ restrictedOrbitMap (G := G) E w p = B • w := by
  let M : Matrix I (Orbit G T) ℤ := fun i o => (orbitCount (E i) o : ℤ)
  have normalization : ∃ i, ∀ o, 0 < M i o := by
    obtain ⟨i, rows⟩ := total
    refine ⟨i, fun o => ?_⟩
    change 0 < (orbitCount (E i) o : ℤ)
    rw [rows]
    exact_mod_cast count_pos o
  have realFeasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ i, ∑ o, (M i o : ℝ) * x o = w i := by
    simpa [M] using feasible
  obtain ⟨B, p, pos, nonzero, counted⟩ :=
    positive_integer_fiber_on_active_columns M w normalization realFeasible
  exact ⟨B, p, pos, nonzero, funext counted⟩


open Classical in
private theorem eventual_budget_from_active_fiber {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)] [Fintype I]
    (E : I → Finset T) (q : I → ℚ) (m : ℕ) (hm : 0 < m) (w : I → ℤ)
    (representation : ∀ i, (w i : ℚ) = m * q i)
    (normalization : ∃ i, E i = univ ∧ q i = 1)
    (feasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ i, ∑ o, (orbitCount (E i) o : ℝ) * x o = w i) :
    let M := restrictedOrbitMap (G := G) E w
    let h := addOrderOf (QuotientAddGroup.mk w : (I → ℤ) ⧸ M.range)
    0 < h ∧ ∃ threshold : ℕ, ∀ t : ℕ, 0 < t → threshold ≤ t →
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        Fintype.card S = m * (h * t) ∧ (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ i, ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) / (m * (h * t) : ℕ) = q i := by
  let M := restrictedOrbitMap (G := G) E w
  let h := addOrderOf (QuotientAddGroup.mk w : (I → ℤ) ⧸ M.range)
  obtain ⟨B, p, hB, hp, eq⟩ := positive_restricted_orbit_fiber E w
    (normalization.imp fun _ hi => hi.1) feasible
  obtain ⟨hh, _, b, _, ⟨u, hU⟩, tail⟩ := eventual_counts M w p B hB hp eq
  obtain ⟨_, _, _, eventual⟩ := tail u hU
  let _ : Fintype {o // Active (fun i o => (orbitCount (G := G) (E i) o : ℤ)) w o} := Fintype.ofFinite _
  refine ⟨hh, (b - 1) * ((1 + ∑ j, (u j).natAbs) * b), fun t ht enough => ?_⟩
  exact (active_rational_event_budget_iff E q m w representation normalization
    (m * (h * t)) (h * t) (Nat.mul_pos hm (Nat.mul_pos hh ht)) rfl).mp (eventual t enough)


private theorem joint_denominator {I : Type*} [Fintype I] (q : I → ℚ) :
    let m := (univ : Finset I).lcm fun i => (q i).den
    0 < m ∧ ∀ N : ℕ, 0 < N →
      (m ∣ N ↔ ∀ i, ∃ z : ℤ, q i = (z : ℚ) / N) := by
  classical
  let m := (univ : Finset I).lcm fun i => (q i).den
  have hm : m ≠ 0 := by
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    push Not
    exact fun i _ => (q i).den_nz
  refine ⟨Nat.pos_of_ne_zero hm, fun N hN => ?_⟩
  rw [Finset.lcm_dvd_iff]
  constructor
  · intro all i
    obtain ⟨k, hk⟩ := all i (mem_univ i)
    have hnq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨(q i).num * k, (eq_div_iff hnq).mpr ?_⟩
    rw [hk, Nat.cast_mul, ← mul_assoc]
    have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_nz
    have hnum : q i * ((q i).den : ℚ) = ((q i).num : ℚ) :=
      (eq_div_iff hden).mp (q i).num_div_den.symm
    rw [hnum, Int.cast_mul, Int.cast_natCast]
  · intro all i _
    obtain ⟨z, hz⟩ := all i
    have form : q i = Rat.divInt z (N : ℤ) := by
      simpa [Rat.divInt_eq_div] using hz
    rw [form]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd z N)


open Classical in
/-- A finite equivariant realization of the rational event masses at a specified budget. -/
def EventBudget {G : Type u} {T : Type v} {I : Type w}
    [Group G] [MulAction G T] (E : I → Finset T) (q : I → ℚ) (N : ℕ) : Prop :=
  ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
    Fintype.card S = N ∧ (∀ (g : G) s, f (g • s) = g • f s) ∧
    (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
      ∀ h : H, (h : G) • f s = f s) ∧
    ∀ i, ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℚ) / N = q i

open Classical in
/-- A feasible rational event law admits every sufficiently large multiple of its active period. -/
theorem eventual_uniform_event_budgets {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)] [Fintype I]
    (E : I → Finset T) (q : I → ℚ)
    (normalization : ∃ i, E i = univ ∧ q i = 1)
    (feasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ i, ∑ o, (orbitCount (E i) o : ℝ) * x o = (q i : ℝ)) :
    let m := (univ : Finset I).lcm fun i => (q i).den
    ∃ w : I → ℤ, (∀ i, (w i : ℚ) = m * q i) ∧
      let M := restrictedOrbitMap (G := G) E w
      let h := addOrderOf (QuotientAddGroup.mk w : (I → ℤ) ⧸ M.range)
      0 < h ∧
        (∀ N : ℕ, 0 < N → EventBudget (G := G) E q N → m * h ∣ N) ∧
        ∃ threshold : ℕ, ∀ t : ℕ, 0 < t → threshold ≤ t →
          EventBudget (G := G) E q (m * (h * t)) := by
  let m := (univ : Finset I).lcm fun i => (q i).den
  obtain ⟨hm, minimal⟩ := joint_denominator q
  have representationRaw := (minimal m hm).mp (dvd_refl m)
  choose w hw using representationRaw
  have mq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have representation (i : I) : (w i : ℚ) = m * q i := by
    rw [mul_comm]
    exact ((eq_div_iff mq).mp (hw i)).symm
  have scaledFeasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ i, ∑ o, (orbitCount (E i) o : ℝ) * x o = w i := by
    obtain ⟨x, hx, hx_eq⟩ := feasible
    refine ⟨fun o => (m : ℝ) * x o, fun o => mul_nonneg (Nat.cast_nonneg _) (hx o), fun i => ?_⟩
    have lift (o : Orbit G T) : (orbitCount (E i) o : ℝ) * ((m : ℝ) * x o) =
        (m : ℝ) * ((orbitCount (E i) o : ℝ) * x o) := by ring
    simp_rw [lift]
    rw [← Finset.mul_sum, hx_eq]
    exact_mod_cast (representation i).symm
  obtain ⟨pos, tail⟩ := eventual_budget_from_active_fiber E q m hm w representation normalization scaledFeasible
  let M := restrictedOrbitMap (G := G) E w
  let h := addOrderOf (QuotientAddGroup.mk w : (I → ℤ) ⧸ M.range)
  refine ⟨w, representation, pos, ?_, tail⟩
  intro N N_pos calibration
  have divides : m ∣ N := by
    obtain ⟨S, _, _, f, _, _, _, counts⟩ := calibration
    apply (minimal N N_pos).mpr
    intro i
    let n : ℕ := ∑ s : S, if f s ∈ E i then (1 : ℕ) else 0
    have nQ : ((n : ℤ) : ℚ) = ∑ s : S, if f s ∈ E i then (1 : ℚ) else 0 := by
      unfold n
      rw [Int.cast_natCast, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases mem : f s ∈ E i <;> simp [mem]
    exact ⟨(n : ℤ), (counts i).symm.trans (congrArg (fun value : ℚ => value / N) nQ.symm)⟩
  obtain ⟨k, hk⟩ := divides
  have counted : k ∈ countedDegrees M w :=
    (active_rational_event_budget_iff E q m w representation normalization N k N_pos hk).mpr calibration
  obtain ⟨B, p, hB, hp, eq⟩ := positive_restricted_orbit_fiber E w
    (normalization.imp fun _ hi => hi.1) scaledFeasible
  obtain ⟨_, periodic, _⟩ := eventual_counts M w p B hB hp eq
  obtain ⟨t, ht⟩ := periodic k counted
  exact ⟨t, by rw [hk, ht, mul_assoc]⟩

end D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget
