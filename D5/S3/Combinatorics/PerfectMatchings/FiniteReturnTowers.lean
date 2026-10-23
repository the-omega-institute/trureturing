/- GID: D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: First-return towers recover every orbit and its exact length. -/
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers
noncomputable section
attribute [local instance] Classical.propDecidable
open Equiv
open scoped BigOperators
open FiniteEndpointPairing

variable {X : Type*} [Finite X]

/-- Complete first-return data. The application below constructs these data
from the actual cut matching; the return times are not cycle-size premises. -/
structure ReturnData (f : Perm X) (S : Set X) where
  next : Perm S
  length : S → ℕ
  first : ∀ x : S, FirstVisit f S x (length x)
  jump : ∀ x : S, (f ^ length x) x = next x

private theorem period_exists (f : Perm X) (x : X) :
    ∃ n : ℕ, 0 < n ∧ (f ^ n) x = x := by
  exact ⟨orderOf f, orderOf_pos f, by simp only [pow_orderOf_eq_one, Perm.one_apply]⟩

/-- The least positive period, including period one at fixed points. -/
noncomputable def orbitPeriod (f : Perm X) (x : X) : ℕ :=
  Nat.find (period_exists f x)

theorem orbit_period_spec (f : Perm X) (x : X) :
    IsLeast {n : ℕ | 0 < n ∧ (f ^ n) x = x} (orbitPeriod f x) := by
  exact ⟨Nat.find_spec (period_exists f x), fun _ hn => Nat.find_min' _ hn⟩

theorem orbit_period_unique (f : Perm X) (x : X) (n : ℕ)
    (hn : IsLeast {k : ℕ | 0 < k ∧ (f ^ k) x = x} n) : orbitPeriod f x = n := by
  exact le_antisymm ((orbit_period_spec f x).2 hn.1) (hn.2 (orbit_period_spec f x).1)

private theorem period_at_iterate (f : Perm X) (x : X) (k : ℕ) :
    orbitPeriod f ((f ^ k) x) = orbitPeriod f x := by
  have he (n : ℕ) : (f ^ n) ((f ^ k) x) = (f ^ k) x ↔ (f ^ n) x = x := by
    have hc : (f ^ n) ((f ^ k) x) = (f ^ k) ((f ^ n) x) := by
      simp only [← Perm.mul_apply, ← pow_add, Nat.add_comm]
    rw [hc, (f ^ k).injective.eq_iff]
  apply orbit_period_unique
  simpa only [he] using orbit_period_spec f x

/-- Full cycle inventory polynomial, with fixed-point cycles retained.
Each root contributes 1/period, so each entire cycle contributes once. -/
noncomputable def cycleInventory [Fintype X] (f : Perm X) : Polynomial ℚ := by
  classical
  exact ∑ x : X, Polynomial.monomial (orbitPeriod f x) (1 / (orbitPeriod f x : ℚ))

namespace ReturnData
variable {f : Perm X} {S : Set X} (R : ReturnData f S)

def elapsed (x : S) : ℕ → ℕ
  | 0 => 0
  | n + 1 => elapsed x n + R.length ((R.next ^ n) x)

private theorem elapsed_strict (x : S) : StrictMono (R.elapsed x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := (R.first ((R.next ^ n) x)).1
  simp only [elapsed]
  omega

private theorem index_le_elapsed (x : S) (n : ℕ) : n ≤ R.elapsed x n := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih =>
    have hp := (R.first ((R.next ^ n) x)).1
    simp only [elapsed]
    omega

private theorem elapsed_position (x : S) (n : ℕ) :
    (f ^ R.elapsed x n) x = (R.next ^ n) x := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih =>
    rw [elapsed, Nat.add_comm, pow_add, Perm.mul_apply, ih, R.jump]
    simp only [pow_succ', Perm.mul_apply]

/-- Every elapsed time lies in a completed-return interval. -/
private theorem interval_exists (x : S) (k : ℕ) :
    ∃ n, R.elapsed x n ≤ k ∧ k < R.elapsed x (n + 1) := by
  have hex : ∃ n, k < R.elapsed x (n + 1) :=
    ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (R.index_le_elapsed x (k + 1))⟩
  let n := Nat.find hex
  have hu : k < R.elapsed x (n + 1) := Nat.find_spec hex
  refine ⟨n, ?_, hu⟩
  by_cases hn : n = 0
  · simp [hn, elapsed]
  · have hp : n - 1 < n := by omega
    have hm := Nat.find_min hex hp
    have he : n - 1 + 1 = n := by omega
    rw [he] at hm
    omega

/-- Greedy time decomposition supplies an actual interior position. Together
with segment injectivity this gives the unique full tower coordinate. -/
private theorem greedy_decomposition (x : S) (k : ℕ) :
    ∃ n d, k = R.elapsed x n + d ∧
      d < R.length ((R.next ^ n) x) ∧
      (f ^ k) x = (f ^ d) ((R.next ^ n) x : S) := by
  obtain ⟨n, hl, hu⟩ := R.interval_exists x k
  let d := k - R.elapsed x n
  have he : k = R.elapsed x n + d := by omega
  have hd : d < R.length ((R.next ^ n) x) := by
    change k < R.elapsed x n + R.length ((R.next ^ n) x) at hu
    omega
  refine ⟨n, d, he, hd, ?_⟩
  rw [he, Nat.add_comm, pow_add, Perm.mul_apply, R.elapsed_position]

/-- Each natural time has exactly one number of completed returns and one
interior offset. This counts elapsed returns even after a whole induced cycle;
the spatial tower coordinate may repeat, while this temporal pair is unique. -/
theorem temporal_decomposition (x : S) (k : ℕ) :
    ∃! p : ℕ × ℕ, k = R.elapsed x p.1 + p.2 ∧
      p.2 < R.length ((R.next ^ p.1) x) ∧
      (f ^ k) x = (f ^ p.2) ((R.next ^ p.1) x : S) := by
  obtain ⟨n, d, he, hd, hp⟩ := R.greedy_decomposition x k
  refine ⟨(n, d), ⟨he, hd, hp⟩, ?_⟩
  rintro ⟨n', d'⟩ ⟨he', hd', _⟩
  change k = R.elapsed x n' + d' at he'
  change d' < R.length ((R.next ^ n') x) at hd'
  have hu : k < R.elapsed x (n + 1) := by
    rw [elapsed]
    omega
  have hu' : k < R.elapsed x (n' + 1) := by
    rw [elapsed]
    omega
  have hn : n' = n := by
    apply le_antisymm
    · by_contra h
      have ht := (R.elapsed_strict x).monotone (show n + 1 ≤ n' by omega)
      omega
    · by_contra h
      have ht := (R.elapsed_strict x).monotone (show n' + 1 ≤ n by omega)
      omega
  have hdn : d' = d := by
    simp only [hn] at he'
    omega
  exact Prod.ext hn hdn

def Untouched (_R : ReturnData f S) : Set X := {z | ∀ x : S, ¬ f.SameCycle x z}
abbrev Tower := Σ x : S, Fin (R.length x)
abbrev Model := R.Untouched ⊕ R.Tower

def encode : R.Model → X
  | Sum.inl z => z
  | Sum.inr ⟨x, k⟩ => (f ^ k.val) x

private theorem tower_injective :
    Function.Injective (fun p : R.Tower => (f ^ p.2.val) p.1) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have equal_offsets (x y : S) (i : Fin (R.length x)) (j : Fin (R.length y))
      (h : (f ^ i.val) x = (f ^ j.val) y) (hij : i.val ≤ j.val) :
      i.val = j.val := by
    have hc : (x : X) = (f ^ (j.val - i.val)) y := by
      apply (f ^ i.val).injective
      have hsum : i.val + (j.val - i.val) = j.val := by omega
      rw [← Perm.mul_apply, ← pow_add, hsum]
      exact h
    by_contra hne
    have hp : 0 < j.val - i.val := by omega
    have hs := (R.first y).2.2 (j.val - i.val) hp (by omega)
    apply hs
    rw [← hc]
    exact x.property
  have hij : i.val = j.val := by
    rcases le_total i.val j.val with hle | hle
    · exact equal_offsets x y i j h hle
    · exact (equal_offsets y x j i h.symm hle).symm
  have hxy : x = y := by
    apply Subtype.ext
    apply (f ^ i.val).injective
    simpa only [hij] using h
  subst y
  have hi : i = j := Fin.ext hij
  subst j
  rfl

private theorem encode_injective : Function.Injective R.encode := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext h)
    | inr b =>
      have hc : f.SameCycle b.1 (R.encode (Sum.inr b)) :=
        ⟨(b.2.val : ℤ), by simp only [zpow_natCast]; rfl⟩
      apply False.elim
      apply a.property b.1
      change f.SameCycle b.1 (R.encode (Sum.inl a))
      rw [h]
      exact hc
  | inr a =>
    cases b with
    | inl b =>
      have hc : f.SameCycle a.1 (R.encode (Sum.inr a)) :=
        ⟨(a.2.val : ℤ), by simp only [zpow_natCast]; rfl⟩
      apply False.elim
      apply b.property a.1
      change f.SameCycle a.1 (R.encode (Sum.inl b))
      rw [← h]
      exact hc
    | inr b => exact congrArg Sum.inr (R.tower_injective h)

private theorem encode_surjective : Function.Surjective R.encode := by
  classical
  intro z
  by_cases hz : z ∈ R.Untouched
  · exact ⟨Sum.inl ⟨z, hz⟩, rfl⟩
  · simp only [Untouched, Set.mem_setOf_eq, not_forall, not_not] at hz
    obtain ⟨x, hx⟩ := hz
    obtain ⟨k, hk⟩ := hx.exists_nat_pow_eq
    obtain ⟨⟨n, d⟩, ⟨_, hd, hp⟩, _⟩ := R.temporal_decomposition x k
    exact ⟨Sum.inr ⟨(R.next ^ n) x, ⟨d, hd⟩⟩, hp.symm.trans hk⟩

noncomputable def modelEquiv : R.Model ≃ X :=
  Equiv.ofBijective R.encode ⟨R.encode_injective, R.encode_surjective⟩

private theorem untouched_next (z : R.Untouched) : f z ∈ R.Untouched := by
  intro x hx
  apply z.property x
  simpa only [Perm.sameCycle_apply_right] using hx

/-- Defined independently of the encoding: move inside a segment, or take
the return-map step at its roof. Untouched cycles keep their original step. -/
def step : R.Model → R.Model
  | Sum.inl z => Sum.inl ⟨f z, R.untouched_next z⟩
  | Sum.inr ⟨x, k⟩ =>
    if h : k.val + 1 < R.length x then
      Sum.inr ⟨x, ⟨k.val + 1, h⟩⟩
    else Sum.inr ⟨R.next x, ⟨0, (R.first (R.next x)).1⟩⟩

private theorem encode_step (p : R.Model) : R.encode (R.step p) = f (R.encode p) := by
  rcases p with z | ⟨x, k⟩
  · rfl
  · by_cases h : k.val + 1 < R.length x
    · simp only [step, dif_pos h, encode, pow_succ', Perm.mul_apply]
    · have hk : k.val + 1 = R.length x := by omega
      simp only [step, dif_neg h, encode, pow_zero, Perm.one_apply]
      rw [← R.jump x]
      calc
        (f ^ R.length x) x = (f ^ (k.val + 1)) x :=
          congrArg (fun n : ℕ => (f ^ n) (x : X)) hk.symm
        _ = f ((f ^ k.val) x) := by rw [pow_succ', Perm.mul_apply]

/-- The complete constructive cycle model, including all untouched cycles.
This equivalence identifies every original point, not only marked endpoints. -/
theorem tower_decomposition :
    (∀ z : R.Untouched, R.modelEquiv (Sum.inl z) = z) ∧
    (∀ x : S, ∀ k : Fin (R.length x),
      R.modelEquiv (Sum.inr ⟨x, k⟩) = (f ^ k.val) x) ∧
    (∀ p, R.modelEquiv (R.step p) = f (R.modelEquiv p)) :=
  ⟨fun _ => rfl, fun _ _ => rfl, R.encode_step⟩

/-- Least positive orbit periods are weighted sums around return-map cycles. -/
theorem least_period_sum (x : S) (N : ℕ)
    (hN : IsLeast {n : ℕ | 0 < n ∧ (R.next ^ n) x = x} N) :
    IsLeast {n : ℕ | 0 < n ∧ (f ^ n) x = (x : X)} (R.elapsed x N) := by
  have hp : 0 < N := hN.1.1
  have hreturn : (R.next ^ N) x = x := hN.1.2
  refine ⟨⟨lt_of_lt_of_le hp (R.index_le_elapsed x N), ?_⟩, ?_⟩
  · rw [R.elapsed_position, hreturn]
  · intro k hk
    have hkpos : 0 < k := hk.1
    obtain ⟨⟨j, d⟩, ⟨he, hd, hpos⟩, _⟩ := R.temporal_decomposition x k
    change k = R.elapsed x j + d at he
    change d < R.length ((R.next ^ j) x) at hd
    change (f ^ k) x = (f ^ d) ((R.next ^ j) x : S) at hpos
    have hd0 : d = 0 := by
      by_contra hd0
      apply (R.first ((R.next ^ j) x)).2.2 d (Nat.pos_of_ne_zero hd0) hd
      rw [← hpos, hk.2]
      exact x.property
    have hke : k = R.elapsed x j := by simpa only [hd0, Nat.add_zero] using he
    have hjp : 0 < j := by
      by_contra hh
      have hj0 : j = 0 := by omega
      simp only [hj0, elapsed] at hke
      omega
    have hjr : (R.next ^ j) x = x := by
      apply Subtype.ext
      have hh := hpos.symm.trans hk.2
      simpa only [hd0, pow_zero, Perm.one_apply] using hh
    have hNj := hN.2 ⟨hjp, hjr⟩
    rw [hke]
    exact (R.elapsed_strict x).monotone hNj


private theorem elapsed_eq_sum (x : S) (n : ℕ) :
    R.elapsed x n = ∑ i ∈ Finset.range n, R.length ((R.next ^ i) x) := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih => simp only [elapsed, Finset.sum_range_succ, ih]

/-- Weight of a complete induced cycle, from its actual segment lengths. -/
noncomputable def weightedPeriod (x : S) : ℕ :=
  ∑ i ∈ Finset.range (orbitPeriod R.next x), R.length ((R.next ^ i) x)

private theorem period_eq_weight (x : S) : orbitPeriod f x = R.weightedPeriod x := by
  have h := orbit_period_unique f x _
    (R.least_period_sum x (orbitPeriod R.next x) (orbit_period_spec R.next x))
  exact h.trans (R.elapsed_eq_sum x _)

/-- Complete orbit-length inventory. The arbitrary additive observable can
select any length, so this recovers every cycle multiplicity, not only a mean. -/
theorem weighted_inventory [Fintype X] {A : Type*} [AddCommMonoid A] (Φ : ℕ → A) :
    (∑ z : X, Φ (orbitPeriod f z)) =
      (∑ z : R.Untouched, Φ (orbitPeriod f z)) +
      ∑ x : S, R.length x • Φ (R.weightedPeriod x) := by
  classical
  letI : Fintype R.Tower := inferInstanceAs (Fintype (Σ x : S, Fin (R.length x)))
  letI : Fintype R.Model := inferInstanceAs (Fintype (R.Untouched ⊕ R.Tower))
  have hs : (∑ p : R.Model, Φ (orbitPeriod f (R.modelEquiv p))) =
      ∑ z : X, Φ (orbitPeriod f z) := by
    apply Fintype.sum_equiv R.modelEquiv
    intro p
    rfl
  rw [← hs]
  change (∑ p : R.Untouched ⊕ (Σ x : S, Fin (R.length x)),
    Φ (orbitPeriod f (R.modelEquiv p))) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [R.tower_decomposition.1, R.tower_decomposition.2.1]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [encode, period_at_iterate, R.period_eq_weight]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Exact full cycle inventory, including all cycles disjoint from the marked
set. Segment weights are essential: unweighted endpoint counts are wrong. -/
theorem weighted_cycle_inventory [Fintype X] :
    cycleInventory f =
      (∑ z : R.Untouched,
        Polynomial.monomial (orbitPeriod f z) (1 / (orbitPeriod f z : ℚ))) +
      ∑ x : S, R.length x •
        Polynomial.monomial (R.weightedPeriod x) (1 / (R.weightedPeriod x : ℚ)) := by
  exact R.weighted_inventory
    (fun n => Polynomial.monomial n (1 / (n : ℚ)))

end ReturnData

#print axioms ReturnData.temporal_decomposition
#print axioms ReturnData.tower_decomposition
#print axioms ReturnData.least_period_sum
#print axioms ReturnData.weighted_inventory
#print axioms ReturnData.weighted_cycle_inventory
end
end D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers
