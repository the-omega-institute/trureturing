/- GID: D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/DirectionMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Boolean cube perfect matching realizes exactly the even direction counts of the correct total. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import D5.S3.FiniteGroups.Hall.PrescribedDifferences
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

noncomputable section
open Finset
open scoped Classical

namespace D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching

abbrev Profile (n : ℕ) := Fin n → ZMod 2
def parity {n : ℕ} (p : Profile n) : ZMod 2 := ∑ i, p i
abbrev ParityClass (n : ℕ) (t : ZMod 2) := {p : Profile n // parity p = t}

/-- The tail determines the head once the parity is fixed. -/
def tailEquiv (n : ℕ) (t : ZMod 2) : ParityClass (n + 1) t ≃ Profile n where
  toFun p := Fin.tail p.val
  invFun f := ⟨Fin.cons (t - ∑ i, f i) f, by simp [parity, Fin.sum_univ_succ]⟩
  left_inv p := by
    have h := p.property
    rw [parity, Fin.sum_univ_succ] at h
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change t - (∑ j : Fin n, p.val j.succ) = p.val 0
      exact (congrArg (fun x => x - ∑ j : Fin n, p.val j.succ) h).symm.trans
        (add_sub_cancel_right _ _)
    · rfl
  right_inv f := by simp

private def unit {n : ℕ} (i : Fin n) : Profile n := Pi.single i (1 : ZMod 2)

private def directionRequest {n : ℕ} (i : Fin (n + 1)) : Profile n :=
  Fin.cases 0 unit i

private theorem single_tail {n : ℕ} (i : Fin (n + 1)) :
    Fin.tail (unit i) = directionRequest i := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Fin.tail, directionRequest, unit]
  · simp [Fin.tail, directionRequest, unit, Pi.single_apply]

/-- Flip one coordinate of an even profile. -/
def flipToOdd {n : ℕ} (p : ParityClass (n + 1) 0) (i : Fin (n + 1)) :
    ParityClass (n + 1) 1 :=
  ⟨p.val + unit i, by
    change (∑ j, (p.val + unit i) j) = 1
    simp only [Pi.add_apply, sum_add_distrib]
    change parity p.val + ∑ j, unit i j = 1
    unfold unit
    rw [p.property, zero_add, sum_eq_single i]
    · simp
    · intro j _ h
      exact Pi.single_eq_of_ne h _
    · simp⟩

private theorem number_parity_classes (n : ℕ)
    (dirs : Fin (Nat.card (Profile n)) → Fin (n + 1))
    (zeroSum : (∑ j, directionRequest (dirs j)) = 0) :
    ∃ (E : Fin (Nat.card (Profile n)) ≃ ParityClass (n + 1) 0)
      (O : Fin (Nat.card (Profile n)) ≃ ParityClass (n + 1) 1),
      ∀ j, O j = flipToOdd (E j) (dirs j) := by
  obtain ⟨x, h⟩ :=
    (D5.S3.FiniteGroups.Hall.PrescribedDifferences.numbering_iff_sum_eq_zero
      (Profile n) (fun j => directionRequest (dirs j))).mpr zeroSum
  let E := x.trans (tailEquiv n 0).symm
  let O := (Equiv.ofBijective _ h).trans (tailEquiv n 1).symm
  refine ⟨E, O, fun j => (tailEquiv n 1).injective ?_⟩
  have hj : Fin.tail (E j).val = x j := (tailEquiv n 0).apply_symm_apply (x j)
  have ho : Fin.tail (O j).val = x j + directionRequest (dirs j) :=
    (tailEquiv n 1).apply_symm_apply _
  change Fin.tail (O j).val = Fin.tail ((E j).val + unit (dirs j))
  rw [ho, show Fin.tail ((E j).val + unit (dirs j)) =
    Fin.tail (E j).val + Fin.tail (unit (dirs j)) by rfl, hj, single_tail]


/-- A binary profile has two choices independently in each coordinate. -/
theorem profileCard (n : ℕ) : Nat.card (Profile n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]

private def labels {n : ℕ} (d : Fin (n + 1) → ℕ) (total : ∑ i, d i = 2 ^ n) :
    Fin (Nat.card (Profile n)) ≃ Σ i, Fin (d i) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, profileCard, Fintype.card_sigma]; simpa using total.symm)

private theorem direction_labels_count {n : ℕ} (d : Fin (n + 1) → ℕ)
    (total : ∑ i, d i = 2 ^ n) (i : Fin (n + 1)) :
    (∑ j, if (labels d total j).1 = i then 1 else (0 : ℕ)) = d i := by
  rw [(labels d total).sum_comp (fun a => if a.1 = i then (1 : ℕ) else 0), Fintype.sum_sigma]
  calc
    _ = ∑ x, if x = i then d x else 0 := by
      apply sum_congr rfl
      intro x _
      split <;> simp_all
    _ = _ := by simp

private theorem direction_sum {n : ℕ} {J : Type*} [Fintype J]
    (dirs : J → Fin (n + 1)) (d : Fin (n + 1) → ℕ)
    (counts : ∀ i, (∑ j, if dirs j = i then 1 else (0 : ℕ)) = d i) :
    (∑ j, directionRequest (dirs j)) = ∑ i, d i • directionRequest i := by
  calc
    _ = ∑ j, ∑ i, if dirs j = i then directionRequest i else 0 := by
      apply sum_congr rfl
      intro j _
      simp
    _ = ∑ i, ∑ j, if dirs j = i then directionRequest i else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [← counts i, sum_smul]
      apply sum_congr rfl
      intro j _
      split <;> simp_all

private theorem sum_directions_even {n : ℕ} (d : Fin (n + 1) → ℕ) (h : ∀ i, Even (d i)) :
    (∑ i, d i • directionRequest i) = 0 := by
  apply sum_eq_zero
  intro i _
  obtain ⟨k, hk⟩ := h i
  have twice (v : Profile n) : 2 • v = 0 := by
    funext j
    rw [two_nsmul]
    change v j + v j = 0
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [hk, add_nsmul, ← two_nsmul]
  exact twice _

private theorem hall_prescribes_direction_counts (n : ℕ) (d : Fin (n + 1) → ℕ)
    (total : ∑ i, d i = 2 ^ n) (allEven : ∀ i, Even (d i)) :
    ∃ (F : ParityClass (n + 1) 0 ≃ ParityClass (n + 1) 1) (dir : ParityClass (n + 1) 0 → Fin (n + 1)),
      (∀ p, F p = flipToOdd p (dir p)) ∧
      ∀ i, (∑ p, if dir p = i then 1 else (0 : ℕ)) = d i := by
  let dirs j := (labels d total j).1
  have counts : ∀ i, (∑ j, if dirs j = i then 1 else (0 : ℕ)) = d i :=
    direction_labels_count d total
  have zeroSum : ∑ j, directionRequest (dirs j) = 0 :=
    (direction_sum dirs d counts).trans (sum_directions_even d allEven)
  obtain ⟨E, O, pointwise⟩ := number_parity_classes n dirs zeroSum
  refine ⟨E.symm.trans O, fun p => dirs (E.symm p), ?_, ?_⟩
  · intro p
    simpa using pointwise (E.symm p)
  · intro i
    rw [E.symm.sum_comp (fun j => if dirs j = i then (1 : ℕ) else 0)]
    exact counts i


private theorem request_sum_zero_of_matching {n : ℕ}
    (F : ParityClass (n + 1) 0 ≃ ParityClass (n + 1) 1) (dir : ParityClass (n + 1) 0 → Fin (n + 1))
    (edges : ∀ p, F p = flipToOdd p (dir p)) :
    (∑ p, directionRequest (dir p)) = 0 := by
  let tail (t : ZMod 2) := tailEquiv n t
  have equal : (∑ p, tail 1 (F p)) = ∑ p, tail 0 p := by
    calc
      _ = ∑ q, tail 1 q := F.sum_comp (tail 1)
      _ = ∑ v : Profile n, v := (tail 1).sum_comp id
      _ = _ := ((tail 0).sum_comp id).symm
  have step (p : ParityClass (n + 1) 0) :
      tail 1 (F p) = tail 0 p + directionRequest (dir p) := by
    rw [edges]
    change Fin.tail (p.val + unit (dir p)) = Fin.tail p.val + directionRequest (dir p)
    rw [show Fin.tail (p.val + unit (dir p)) = Fin.tail p.val + Fin.tail (unit (dir p)) by rfl,
      single_tail]
  simp_rw [step] at equal
  rw [sum_add_distrib] at equal
  exact add_left_cancel (equal.trans (add_zero _).symm)

private theorem coordinate_demand_even {n : ℕ} (d : Fin (n + 1) → ℕ)
    (zero : (∑ i, d i • directionRequest i) = 0) (j : Fin n) : Even (d j.succ) := by
  have eval : (∑ i, (d i • directionRequest i) j) = (0 : ZMod 2) := by
    simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun zero j
  have value (i : Fin (n + 1)) :
      (d i • directionRequest i) j = if i = j.succ then (d j.succ : ZMod 2) else 0 := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [directionRequest, Ne.symm (Fin.succ_ne_zero j)]
    · by_cases h : k = j
      · subst k
        simp [directionRequest, unit]
      · have hs : k.succ ≠ j.succ := fun e => h (Fin.succ_injective _ e)
        simp [directionRequest, unit, Pi.single_eq_of_ne (Ne.symm h), hs]
  simp_rw [value] at eval
  simp only [sum_ite_eq', mem_univ, ite_true] at eval
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp eval)

private theorem matching_even_demands (n : ℕ) (d : Fin (n + 2) → ℕ)
    (total : ∑ i, d i = 2 ^ (n + 1))
    (F : ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1) (dir : ParityClass (n + 2) 0 → Fin (n + 2))
    (edges : ∀ p, F p = flipToOdd p (dir p))
    (counts : ∀ i, (∑ p, if dir p = i then 1 else (0 : ℕ)) = d i) :
    ∀ i, Even (d i) := by
  have zero := (direction_sum dir d counts).symm.trans (request_sum_zero_of_matching F dir edges)
  have suffix := coordinate_demand_even d zero
  refine Fin.cases ?_ suffix
  have tailEven : Even (∑ j : Fin (n + 1), d j.succ) := Finset.even_sum _ fun j _ => suffix j
  have totalEven : Even (∑ i, d i) := by
    rw [total, pow_succ]
    exact even_two.mul_left _
  rw [Fin.sum_univ_succ, Nat.even_add] at totalEven
  exact totalEven.mpr tailEven

/-- The prescribed counts of a perfect matching exist exactly when each is even. -/
theorem exact_matching_directions (n : ℕ) (d : Fin (n + 2) → ℕ)
    (total : ∑ i, d i = 2 ^ (n + 1)) :
    (∃ (F : ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1) (dir : ParityClass (n + 2) 0 → Fin (n + 2)),
      (∀ p, F p = flipToOdd p (dir p)) ∧
      ∀ i, (∑ p, if dir p = i then 1 else (0 : ℕ)) = d i) ↔ (∀ i, Even (d i)) := by
  constructor
  · rintro ⟨F, dir, edges, counts⟩
    exact matching_even_demands n d total F dir edges counts
  · exact hall_prescribes_direction_counts (n + 1) d total

end D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
