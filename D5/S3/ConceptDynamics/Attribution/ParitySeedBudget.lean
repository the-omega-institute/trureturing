/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedBudget
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform coloured parity implementations have exactly the fourfold profile budgets. -/

import D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
import Mathlib.GroupTheory.GroupAction.SubMulAction
import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedBudget

open scoped Classical

open Finset

private theorem exceptional_row {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℕ) (a₀ a₁ : A) (distinct : a₁ ≠ a₀) (k s : ℕ)
    (rows : ∀ a, ∑ b, w a b = s) (cols : ∀ b, ∑ a, w a b = s)
    (ordinary : ∀ a b, a ≠ a₀ → k ∣ w a b) :
    k ∣ s ∧ ∀ a b, k ∣ w a b := by
  classical
  have ds : k ∣ s := by
    rw [← rows a₁]
    exact Finset.dvd_sum fun b _ => ordinary a₁ b distinct
  refine ⟨ds, ?_⟩
  intro a b
  by_cases ha : a = a₀
  · subst a
    have remainder : k ∣ ∑ x ∈ univ.erase a₀, w x b :=
      Finset.dvd_sum fun x hx => ordinary x b (ne_of_mem_erase hx)
    have split : (∑ x ∈ univ.erase a₀, w x b) + w a₀ b = s :=
      (sum_erase_add _ _ (mem_univ a₀)).trans (cols b)
    exact (Nat.dvd_add_iff_right remainder).mpr (split.symm ▸ ds)
  · exact ordinary a b ha


open Finset

abbrev Profile (n : ℕ) := Fin n → ZMod 2
def parity {n : ℕ} (p : Profile n) : ZMod 2 := ∑ i, p i
abbrev ParityClass (n : ℕ) (t : ZMod 2) := {p : Profile n // parity p = t}

private def parityEquiv (n : ℕ) (t : ZMod 2) : ParityClass (n + 1) t ≃ Profile n where
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

theorem parityCard (n : ℕ) (t : ZMod 2) :
    Nat.card (ParityClass (n + 1) t) = 2 ^ n := by
  rw [Nat.card_congr (parityEquiv n t), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]

private theorem bit (z : ZMod 2) : z = 0 ∨ z = 1 := by decide +revert

private theorem another_profile_in_all_one_class (n : ℕ) :
    ∃ p : ParityClass (n + 2) (parity (1 : Profile (n + 2))), p.val ≠ 1 := by
  let p : Profile (n + 2) := Fin.cons 0 (Fin.cons 0 1)
  have eq : parity p = parity (1 : Profile (n + 2)) := by
    unfold parity
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    change (0 : ZMod 2) + (0 + ∑ i : Fin n, 1) = 1 + (1 + ∑ i : Fin n, 1)
    rw [← add_assoc (1 : ZMod 2) 1, show (1 : ZMod 2) + 1 = 0 by decide]
    simp
  refine ⟨⟨p, eq⟩, ?_⟩
  intro h
  have := congrFun h 0
  exact zero_ne_one this


private theorem parity_cells {n : ℕ} {s t : ZMod 2} (different : s ≠ t)
    (w : ParityClass (n + 2) s → ParityClass (n + 2) t → ℕ) (m : ℕ)
    (row : ∀ p, ∑ q, w p q = m) (col : ∀ q, ∑ p, w p q = m)
    (ordinary : ∀ p q, p.val ≠ 1 → q.val ≠ 1 → 4 ∣ w p q) :
    4 ∣ m ∧ ∀ p q, 4 ∣ w p q := by
  classical
  let ones : Profile (n + 2) := 1
  by_cases hs : parity ones = s
  · let e : ParityClass (n + 2) s := ⟨ones, hs⟩
    obtain ⟨p, hp⟩ := another_profile_in_all_one_class n
    let a : ParityClass (n + 2) s := ⟨p.val, p.property.trans hs⟩
    refine exceptional_row w e a (fun h => hp (congrArg Subtype.val h)) 4 m row col ?_
    intro x y hx
    apply ordinary
    · exact fun h => hx (Subtype.ext h)
    · intro h
      exact different (hs.symm.trans ((congrArg parity h).symm.trans y.property))
  · by_cases ht : parity ones = t
    · let e : ParityClass (n + 2) t := ⟨ones, ht⟩
      obtain ⟨q, hq⟩ := another_profile_in_all_one_class n
      let a : ParityClass (n + 2) t := ⟨q.val, q.property.trans ht⟩
      have result := exceptional_row (fun y x => w x y) e a
        (fun h => hq (congrArg Subtype.val h)) 4 m col row ?_
      · exact ⟨result.1, fun p q => result.2 q p⟩
      · intro y x hy
        apply ordinary
        · exact fun h => hs ((congrArg parity h).symm.trans x.property)
        · exact fun h => hy (Subtype.ext h)
    · have div : ∀ p q, 4 ∣ w p q := fun p q => ordinary p q
        (fun h => hs ((congrArg parity h).symm.trans p.property))
        (fun h => ht ((congrArg parity h).symm.trans q.property))
      obtain ⟨p⟩ : Nonempty (ParityClass (n + 2) s) := ⟨(parityEquiv (n + 1) s).symm 0⟩
      refine ⟨?_, div⟩
      rw [← row p]
      exact Finset.dvd_sum fun q _ => div p q

private theorem parity_divisor {n : ℕ} {s t : ZMod 2} (different : s ≠ t)
    (w : ParityClass (n + 2) s → ParityClass (n + 2) t → ℕ) (N m : ℕ)
    (total : (∑ p, ∑ q, w p q) = N)
    (row : ∀ p, ∑ q, w p q = m) (col : ∀ q, ∑ p, w p q = m)
    (ordinary : ∀ p q, p.val ≠ 1 → q.val ≠ 1 → 4 ∣ w p q) :
    2 ^ (n + 3) ∣ N ∧ ∀ p q, 4 ∣ w p q := by
  obtain ⟨⟨l, hl⟩, cells⟩ := parity_cells different w m row col ordinary
  refine ⟨⟨l, ?_⟩, cells⟩
  rw [← total]
  simp only [row, sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card, parityCard, hl]
  change (2 : ℕ)^(n + 1) * (4 * l) = 2 ^ (n + 3) * l
  calc
    _ = (2 ^ (n + 1) * 4) * l := (Nat.mul_assoc _ _ _).symm
    _ = _ := congrArg (· * l) (pow_add (2 : ℕ) (n + 1) 2).symm


open D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit

def booleanProfile {n : ℕ} (p : Profile n) : Fin n → Bool :=
  fun i => decide (p i = 1)

private theorem booleanProfile_injective (n : ℕ) :
    Function.Injective (booleanProfile (n := n)) := by
  intro p q h
  funext i
  have at_i := congrFun h i
  rcases bit (p i) with hp | hp <;> rcases bit (q i) with hq | hq <;>
    simp_all [booleanProfile, zero_ne_one]

private theorem hasFalse {n : ℕ} {p : Profile n} (h : p ≠ 1) :
    ∃ i, booleanProfile p i = false := by
  by_contra! noFalse
  apply h
  apply booleanProfile_injective
  funext i
  change booleanProfile p i = decide ((1 : Profile n) i = 1)
  rw [show (1 : Profile n) i = 1 by rfl]
  cases b : booleanProfile p i
  · exact (noFalse i b).elim
  · simp

def pairMass {n : ℕ} (w : Output (Fin n) → Output (Fin n) → ℕ)
    (p q : Profile n) : ℕ :=
  ∑ c : ZMod 2, ∑ d : ZMod 2, w ⟨booleanProfile p, c⟩ ⟨booleanProfile q, d⟩

private theorem check_coloured_count {n : ℕ} (N : ℕ)
    (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ)
    (inv : ∀ (g : Acting (Fin (n + 2))) x y, w (g • x) (g • y) = w x y)
    (m : ℕ)
    (total : (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, pairMass w p.val q.val) = N)
    (row : ∀ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, pairMass w p.val q.val = m)
    (col : ∀ q : ParityClass (n + 2) 1, ∑ p : ParityClass (n + 2) 0, pairMass w p.val q.val = m) :
    2 ^ (n + 3) ∣ N ∧ ∀ (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1),
      4 ∣ pairMass w p.val q.val := by
  refine parity_divisor zero_ne_one (fun p q => pairMass w p.val q.val) N m total row col ?_
  intro p q hp hq
  have distinct : booleanProfile p.val ≠ booleanProfile q.val := by
    intro h
    have same := congrArg parity (booleanProfile_injective _ h)
    exact zero_ne_one (p.property.symm.trans (same.trans q.property))
  exact (universally_four_dvd_iff _ _).mpr ⟨distinct, hasFalse hp, hasFalse hq⟩ w inv


private def nextProfile (n : ℕ) : ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1 :=
  (parityEquiv (n + 1) 0).trans (parityEquiv (n + 1) 1).symm

private def matchingCount (n k : ℕ) (x y : Output (Fin (n + 2))) : ℕ :=
  if ∃ p : ParityClass (n + 2) 0, x.profile = booleanProfile p.val ∧
    y.profile = booleanProfile ((nextProfile n) p).val then k else 0

private theorem matchingCount_invariant (n k : ℕ) :
    ∀ (g : Acting (Fin (n + 2))) x y,
      matchingCount n k (g • x) (g • y) = matchingCount n k x y := by
  intro g x y
  rfl

private theorem matching_cell (n k : ℕ) (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
    pairMass (matchingCount n k) p.val q.val = if nextProfile n p = q then 4 * k else 0 := by
  have matched : (∃ x : ParityClass (n + 2) 0, booleanProfile p.val = booleanProfile x.val ∧
        booleanProfile q.val = booleanProfile ((nextProfile n) x).val) ↔
      nextProfile n p = q := by
    constructor
    · rintro ⟨x, hx, hq⟩
      have eq : p = x := Subtype.ext (booleanProfile_injective _ hx)
      exact (congrArg (nextProfile n) eq).trans
        (Subtype.ext (booleanProfile_injective _ hq)).symm
    · intro h
      exact ⟨p, rfl, congrArg (fun y => booleanProfile y.val) h.symm⟩
  simp only [pairMass, matchingCount, matched, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  split
  · exact (Nat.mul_assoc 2 2 k).symm
  · simp

private theorem matching_row (n k : ℕ) (p : ParityClass (n + 2) 0) :
    (∑ q : ParityClass (n + 2) 1, pairMass (matchingCount n k) p.val q.val) = 4 * k := by
  simp [matching_cell]

private theorem matching_total (n k : ℕ) :
    (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1,
      pairMass (matchingCount n k) p.val q.val) = 2 ^ (n + 3) * k := by
  simp only [matching_row, sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card, parityCard]
  change (2 : ℕ)^(n + 1) * (4 * k) = 2 ^ (n + 3) * k
  calc
    _ = (2 ^ (n + 1) * 4) * k := (Nat.mul_assoc _ _ _).symm
    _ = _ := congrArg (· * k) (pow_add (2 : ℕ) (n + 1) 2).symm


def entry {n : ℕ} (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) (c d : ZMod 2) : ℕ :=
  w ⟨booleanProfile p.val, c⟩ ⟨booleanProfile q.val, d⟩

def MatrixRealizes (n N : ℕ) (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ) : Prop :=
  (∀ (g : Acting (Fin (n + 2))) x y, w (g • x) (g • y) = w x y) ∧
  (∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, pairMass w p.val q.val) = N ∧
  ∃ k : ℕ,
    (∀ (p : ParityClass (n + 2) 0) (c : ZMod 2), (∑ q, ∑ d, entry w p q c d) = k) ∧
    (∀ (q : ParityClass (n + 2) 1) (d : ZMod 2), (∑ p, ∑ c, entry w p q c d) = k)

theorem MatrixRealizes.four_dvd {n N : ℕ}
    {w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ} (h : MatrixRealizes n N w) :
    2 ^ (n + 3) ∣ N ∧ ∀ (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1),
      4 ∣ pairMass w p.val q.val := by
  obtain ⟨inv, total, k, row, col⟩ := h
  refine check_coloured_count N w inv (2 * k) total ?_ ?_
  · intro p
    change (∑ q, ∑ c, ∑ d, entry w p q c d) = 2 * k
    rw [sum_comm]
    simp [row, ZMod.card]
  · intro q
    change (∑ p, ∑ c, ∑ d, entry w p q c d) = 2 * k
    calc
      _ = ∑ p : ParityClass (n + 2) 0, ∑ d : ZMod 2, ∑ c, entry w p q c d :=
        sum_congr rfl fun _ _ => sum_comm
      _ = ∑ d : ZMod 2, ∑ p : ParityClass (n + 2) 0, ∑ c, entry w p q c d := sum_comm
      _ = _ := by simp [col, ZMod.card]

private theorem matching_entry (n k : ℕ) (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1)
    (c d : ZMod 2) : entry (matchingCount n k) p q c d = if nextProfile n p = q then k else 0 := by
  unfold entry matchingCount
  apply if_congr ?_ rfl rfl
  constructor
  · rintro ⟨x, hx, hq⟩
    have eq : p = x := Subtype.ext (booleanProfile_injective _ hx)
    exact (congrArg (nextProfile n) eq).trans
      (Subtype.ext (booleanProfile_injective _ hq)).symm
  · intro h
    exact ⟨p, rfl, congrArg (fun y => booleanProfile y.val) h.symm⟩

private theorem exact_matrix_budget (n N : ℕ) :
    (∃ w, MatrixRealizes n N w) ↔ 2 ^ (n + 3) ∣ N := by
  constructor
  · rintro ⟨w, h⟩
    exact h.four_dvd.1
  · rintro ⟨k, rfl⟩
    refine ⟨matchingCount n k, matchingCount_invariant n k, matching_total n k, 2 * k, ?_, ?_⟩
    · intro p c
      simp_rw [matching_entry]
      simp [ZMod.card]
    · intro q d
      simp_rw [matching_entry]
      rw [← (nextProfile n).symm.sum_comp]
      simp [ZMod.card]


def bitProfile {n : ℕ} (p : Fin n → Bool) : Profile n :=
  fun i => if p i then 1 else 0

@[simp] theorem bitProfile_booleanProfile {n : ℕ} (p : Profile n) :
    bitProfile (booleanProfile p) = p := by
  funext i
  rcases bit (p i) with h | h <;> simp [bitProfile, booleanProfile, h]

@[simp] private theorem booleanProfile_bitProfile {n : ℕ} (p : Fin n → Bool) :
    booleanProfile (bitProfile p) = p := by
  funext i
  cases h : p i <;> simp [bitProfile, booleanProfile, h, zero_ne_one]

def slice (n : ℕ) (t : ZMod 2) :
    SubMulAction (Acting (Fin n)) (Output (Fin n)) where
  carrier := {y | parity (bitProfile y.profile) = t}
  smul_mem' _ _ h := h

/-- A coloured parity output is a parity profile with its binary colour. -/
def sliceEquiv (n : ℕ) (t : ZMod 2) :
    ParityClass n t × ZMod 2 ≃ slice n t where
  toFun a := ⟨⟨booleanProfile a.1.val, a.2⟩, by
    change parity (bitProfile (booleanProfile a.1.val)) = t
    rw [bitProfile_booleanProfile, a.1.property]⟩
  invFun y := (⟨bitProfile y.val.profile, y.property⟩, y.val.colour)
  left_inv := by
    rintro ⟨⟨p, hp⟩, c⟩
    apply Prod.ext
    · exact Subtype.ext (bitProfile_booleanProfile p)
    · rfl
  right_inv := by
    rintro ⟨⟨p, c⟩, h⟩
    apply Subtype.ext
    change Output.mk (booleanProfile (bitProfile p)) c = Output.mk p c
    rw [booleanProfile_bitProfile]

noncomputable instance sliceFintype (n : ℕ) (t : ZMod 2) : Fintype (slice n t) :=
  Fintype.ofEquiv _ (sliceEquiv n t)

abbrev Pair (n : ℕ) := slice (n + 2) 0 × slice (n + 2) 1

def seedWeight {n : ℕ}
    (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ) (a : Pair n) : ℕ :=
  w a.1.val a.2.val

private theorem seedWeight_invariant {n : ℕ}
    (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ)
    (inv : ∀ (g : Acting (Fin (n + 2))) x y, w (g • x) (g • y) = w x y) :
    ∀ (g : Acting (Fin (n + 2))) (a : Pair n), seedWeight w (g • a) = seedWeight w a :=
  fun g a => inv g a.1.val a.2.val

private theorem sum_seedWeight {n : ℕ}
    (w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ) :
    (∑ a : Pair n, seedWeight w a) =
      ∑ p : ParityClass (n + 2) 0, ∑ q : ParityClass (n + 2) 1, pairMass w p.val q.val := by
  rw [Fintype.sum_prod_type]
  change (∑ x : slice (n + 2) 0, ∑ y : slice (n + 2) 1, w x.val y.val) = _
  rw [← (sliceEquiv (n + 2) 0).sum_comp]
  simp_rw [← (sliceEquiv (n + 2) 1).sum_comp]
  simp_rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  exact sum_comm

attribute [local instance 10000] Classical.propDecidable

section

attribute [local instance 10000] Classical.propDecidable

/-- Realize a count matrix by seed copies while retaining fixed sets and predicate counts. -/
theorem matrix_to_seeds_with_readouts {n N : ℕ}
    {w : Output (Fin (n + 2)) → Output (Fin (n + 2)) → ℕ} (h : MatrixRealizes n N w) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = N ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      (∀ (H : Subgroup (Acting (Fin (n + 2)))) s,
        (∀ h : H, (h : Acting (Fin (n + 2))) • s = s) ↔
          ∀ h : H, (h : Acting (Fin (n + 2))) • f s = f s) ∧
      (∀ predicate : Pair n → Prop,
        (∑ s, if predicate (f s) then (1 : ℕ) else 0) =
          ∑ a, if predicate a then seedWeight w a else 0) ∧
      ∃ k : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = k) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = k) := by
  obtain ⟨inv, total, k, row, col⟩ := h
  obtain ⟨S, _, _, f, equiv, fixed, counts⟩ :=
    D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.SeedCopies.exact_card_count
      (seedWeight w) (seedWeight_invariant w inv)
  refine ⟨S, inferInstance, inferInstance, f, ?_, equiv, fixed, counts, k, ?_, ?_⟩
  · have cardCount : Fintype.card S = ∑ a, seedWeight w a := by
      simpa using counts (fun _ => True)
    exact cardCount.trans ((sum_seedWeight w).trans total)
  · intro x
    obtain ⟨⟨p, c⟩, rfl⟩ := (sliceEquiv (n + 2) 0).surjective x
    have h := counts (fun a => a.1 = sliceEquiv (n + 2) 0 (p, c))
    have mEq : (∑ a : Pair n, if a.1 = sliceEquiv (n + 2) 0 (p, c)
          then seedWeight w a else 0) = k := by
      rw [Fintype.sum_prod_type, sum_comm]
      simp only [sum_ite_eq', mem_univ, ite_true]
      rw [← (sliceEquiv (n + 2) 1).sum_comp, Fintype.sum_prod_type]
      convert row p c using 1
      apply Finset.sum_congr
      · ext q
        simp
      · intro q _
        rfl
    exact h.trans mEq
  · intro y
    obtain ⟨⟨q, d⟩, rfl⟩ := (sliceEquiv (n + 2) 1).surjective y
    have h := counts (fun a => a.2 = sliceEquiv (n + 2) 1 (q, d))
    have mEq : (∑ a : Pair n, if a.2 = sliceEquiv (n + 2) 1 (q, d)
          then seedWeight w a else 0) = k := by
      rw [Fintype.sum_prod_type]
      simp only [sum_ite_eq', mem_univ, ite_true]
      rw [← (sliceEquiv (n + 2) 0).sum_comp, Fintype.sum_prod_type]
      convert col q d using 1
      apply Finset.sum_congr
      · ext p
        simp
      · intro p _
        rfl
    exact h.trans mEq

end

/-- The number of seeds realizing an ordered pair of profiles, summing over both colours. -/
def profileFibreCount {n : ℕ} {S : Type} [Fintype S] (f : S → Pair n)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) : ℕ :=
  ∑ s, if (f s).1.val.profile = booleanProfile p.val ∧
    (f s).2.val.profile = booleanProfile q.val then 1 else 0

def seedPushforward {n : ℕ} {S : Type} [Fintype S] (f : S → Pair n)
    (x y : Output (Fin (n + 2))) : ℕ :=
  ∑ s, if (f s).1.val = x ∧ (f s).2.val = y then 1 else 0

private theorem seedPushforward_invariant {n : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (g : Acting (Fin (n + 2))) (x y : Output (Fin (n + 2))) :
    seedPushforward f (g • x) (g • y) = seedPushforward f x y := by
  unfold seedPushforward
  rw [← Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm S)
    (fun s => if (f s).1.val = g • x ∧ (f s).2.val = g • y then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro s _
  change (if (f (g • s)).1.val = g • x ∧ (f (g • s)).2.val = g • y then 1 else 0) = _
  rw [equiv]
  change (if g • (f s).1.val = g • x ∧ g • (f s).2.val = g • y then 1 else 0) = _
  let move : Equiv.Perm (Output (Fin (n + 2))) := MulAction.toPerm g
  have inject : ∀ a b : Output (Fin (n + 2)), g • a = g • b ↔ a = b :=
    fun _ _ => move.injective.eq_iff
  rw [inject, inject]

private theorem seedPushforward_pooled {n : ℕ} {S : Type} [Fintype S] (f : S → Pair n)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
    pairMass (seedPushforward f) p.val q.val = profileFibreCount f p q := by
  unfold pairMass seedPushforward profileFibreCount
  simp_rw [sum_comm (s := (univ : Finset (ZMod 2))) (t := (univ : Finset S))]
  apply sum_congr rfl
  intro s _
  rcases (f s).1.val with ⟨profile₁, colour₁⟩
  rcases (f s).2.val with ⟨profile₂, colour₂⟩
  simp only [Output.mk.injEq]
  by_cases hp : profile₁ = booleanProfile p.val
  · by_cases hq : profile₂ = booleanProfile q.val
    · simp only [hp, hq, true_and, ite_true]
      calc
        _ = ∑ a : ZMod 2 × ZMod 2, if (colour₁, colour₂) = a then (1 : ℕ) else 0 := by
          rw [Fintype.sum_prod_type]
          simp only [Prod.mk.injEq]
        _ = 1 := by simp
    · simp [hp, hq]
  · simp [hp]

/-- Uniform profile marginals force fourfold divisibility in every ordered profile fibre. -/
theorem profile_fibre_four_dvd {n : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) (k : ℕ)
    (rows : ∀ p, (∑ q, profileFibreCount f p q) = k)
    (cols : ∀ q, (∑ p, profileFibreCount f p q) = k)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
    4 ∣ profileFibreCount f p q := by
  let w := seedPushforward f
  have pooled (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      pairMass w p.val q.val = profileFibreCount f p q := seedPushforward_pooled f p q
  have result := check_coloured_count _ w (seedPushforward_invariant f equiv) k rfl
    (fun p => (sum_congr (Finset.ext fun q => by simp) (fun q _ => pooled p q)).trans (rows p))
    (fun q => (sum_congr (Finset.ext fun p => by simp) (fun p _ => pooled p q)).trans (cols q))
  rw [← pooled]
  exact result.2 p q

section

attribute [local instance 10000] Classical.propDecidable

/-- The specific pushforward count matrix of a seed implementation realizes its marginals. -/
theorem seeds_to_pushforward {n N : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n) (card : Fintype.card S = N)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (k : ℕ)
    (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = k)
    (cols : ∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = k) :
    MatrixRealizes n N (seedPushforward f) := by
  let w := seedPushforward f
  have atom (x : slice (n + 2) 0) (y : slice (n + 2) 1) :
      w x.val y.val = ∑ s : S, if (f s).1 = x ∧ (f s).2 = y then 1 else 0 := by
    unfold w seedPushforward
    simp only [Subtype.val_inj]
  have rowCount (x : slice (n + 2) 0) :
      (∑ y : slice (n + 2) 1, w x.val y.val) = k := by
    simp_rw [atom]
    rw [sum_comm, ← rows x]
    apply sum_congr rfl
    intro s _
    by_cases matchX : (f s).1 = x <;> simp [matchX]
  have colCount (y : slice (n + 2) 1) :
      (∑ x : slice (n + 2) 0, w x.val y.val) = k := by
    simp_rw [atom]
    rw [sum_comm, ← cols y]
    apply sum_congr rfl
    intro s _
    by_cases matchY : (f s).2 = y <;> simp [matchY]
  have total : (∑ a : Pair n, seedWeight w a) = N := by
    simp_rw [seedWeight, atom]
    rw [sum_comm]
    have single (s : S) :
        (∑ a : Pair n, if (f s).1 = a.1 ∧ (f s).2 = a.2 then (1 : ℕ) else 0) = 1 := by
      simp [← Prod.ext_iff]
    simp [single, card]
  refine ⟨seedPushforward_invariant f equiv, (sum_seedWeight w).symm.trans total, k, ?_, ?_⟩
  · intro p c
    have h := rowCount (sliceEquiv (n + 2) 0 (p, c))
    rw [← (sliceEquiv (n + 2) 1).sum_comp, Fintype.sum_prod_type] at h
    convert h using 1
    apply Finset.sum_congr
    · ext q
      simp
    · intro q _
      rfl
  · intro q d
    have h := colCount (sliceEquiv (n + 2) 1 (q, d))
    rw [← (sliceEquiv (n + 2) 0).sum_comp, Fintype.sum_prod_type] at h
    convert h using 1
    apply Finset.sum_congr
    · ext p
      simp
    · intro p _
      rfl

end

/-- Count budgets for an equivariant implementation of two uniform coloured parity laws. -/
theorem exact_seed_budget (n N : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = N ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      ∃ k : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = k) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = k)) ↔
    2 ^ (n + 3) ∣ N := by
  constructor
  · rintro ⟨S, _, _, f, card, equiv, k, rows, cols⟩
    apply (exact_matrix_budget n N).mp
    refine ⟨seedPushforward f, seeds_to_pushforward f card equiv k ?_ ?_⟩
    · intro x
      convert rows x using 1
    · intro y
      convert cols y using 1
  · intro d
    obtain ⟨w, h⟩ := (exact_matrix_budget n N).mpr d
    obtain ⟨S, _, _, f, card, equiv, _, _, k, rows, cols⟩ := matrix_to_seeds_with_readouts h
    refine ⟨S, inferInstance, inferInstance, f, card, equiv, k, ?_, ?_⟩
    · intro x
      convert rows x using 1
    · intro y
      convert cols y using 1

end D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
