/- GID: D5/S3/ConceptDynamics/Attribution/JointFixedTableMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/JointFixedTableMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A scalar inequality characterizes joint attainment of two invariant output event bounds. -/

import D5.S3.Analytic.Probability.FiniteOrderedStrassen
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Simultaneous attainment of two fixed-table masses for pointwise invariant row laws. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.JointFixedTableMass

open Finset

section
variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

open Classical in
private theorem product_coordinate (K : X → Y → ℝ) (normalized : ∀ x, ∑ y, K x y = 1)
    (x : X) (y : Y) :
    (∑ t : X → Y, if t x = y then ∏ i, K i (t i) else 0) = K x y := by
  let restricted (i : X) (z : Y) := if i = x then (if z = y then K i z else 0) else K i z
  have product (t : X → Y) :
      (if t x = y then ∏ i, K i (t i) else 0) = ∏ i, restricted i (t i) := by
    by_cases ht : t x = y
    · rw [ite_eq_left ht]
      apply prod_congr rfl
      intro i _
      by_cases hi : i = x
      · subst i
        simp [restricted, ht]
      · simp [restricted, hi]
    · rw [ite_eq_right ht]
      symm
      apply prod_eq_zero (mem_univ x)
      simp [restricted, ht]
  simp_rw [product]
  rw [← Fintype.prod_sum]
  have total (i : X) : (∑ z, restricted i z) = if i = x then K x y else 1 := by
    by_cases hi : i = x
    · subst i
      simp [restricted]
    · simp [restricted, hi, normalized]
  simp_rw [total]
  simp

open Classical in
private noncomputable def jointWeight (m : A → ℝ) (coupling : X → A → Y → ℝ) (a : A) (t : X → Y) : ℝ :=
  m a * ∏ x, coupling x a (t x) / m a

omit [Fintype A] in
open Classical in
private theorem joint_weight_glues (m : A → ℝ) (C : X → A → Y → ℝ)
    (mass : ∀ a, 0 ≤ m a)
    (nonneg : ∀ x a y, 0 ≤ C x a y)
    (normalize : ∀ x a, ∑ y, C x a y = m a) :
    (∀ a t, 0 ≤ jointWeight m C a t) ∧
    (∀ a, ∑ t, jointWeight m C a t = m a) ∧
    (∀ x a y, (∑ t : X → Y, if t x = y then jointWeight m C a t else 0) = C x a y) ∧
    ∀ (R : A → Y → Prop), (∀ x a y, ¬ R a y → C x a y = 0) →
      ∀ a t, (∃ x, ¬ R a (t x)) → jointWeight m C a t = 0 := by
  refine ⟨fun a t => ?_, fun a => ?_, fun x a y => ?_, fun R supported a t outside => ?_⟩
  · unfold jointWeight
    exact mul_nonneg (mass a) (prod_nonneg fun x _ => div_nonneg (nonneg x a (t x)) (mass a))
  · by_cases h : m a = 0
    · simp [jointWeight, h]
    · have normal (x : X) : (∑ y, C x a y / m a) = 1 := by
        rw [← sum_div, normalize, div_self h]
      unfold jointWeight
      rw [← mul_sum, ← Fintype.prod_sum (fun x y => C x a y / m a)]
      simp [normal]
  · by_cases h : m a = 0
    · have atom := single_le_sum (fun z _ => nonneg x a z) (mem_univ y)
      rw [normalize, h] at atom
      simp [jointWeight, h, le_antisymm atom (nonneg x a y)]
    · have normal (i : X) : (∑ z, C i a z / m a) = 1 := by
        rw [← sum_div, normalize, div_self h]
      have pull (t : X → Y) :
          (if t x = y then jointWeight m C a t else 0) =
            m a * (if t x = y then ∏ i, C i a (t i) / m a else 0) := by
        by_cases ht : t x = y <;> simp [jointWeight, ht]
      simp_rw [pull]
      rw [← mul_sum, product_coordinate (fun i z => C i a z / m a) normal]
      field_simp
  · obtain ⟨x, hx⟩ := outside
    unfold jointWeight
    rw [prod_eq_zero (mem_univ x) (show C x a (t x) / m a = 0 by rw [supported x a (t x) hx, zero_div])]
    exact mul_zero _
end

section
variable {A B Y : Type*} [Fintype A] [Fintype B] [Fintype Y]

open Classical in
private theorem lift_along_profile (p : Y → ℝ) (nn : ∀ y, 0 ≤ p y) (profile : Y → B)
    (π : A → B → ℝ) (pn : ∀ a b, 0 ≤ π a b)
    (columns : ∀ b, ∑ a, π a b = ∑ y ∈ univ.filter (fun y => profile y = b), p y) :
    ∃ C : A → Y → ℝ,
      (∀ a y, 0 ≤ C a y) ∧
      (∀ y, ∑ a, C a y = p y) ∧
      (∀ a, ∑ y, C a y = ∑ b, π a b) ∧
      (∀ a y, π a (profile y) = 0 → C a y = 0) ∧
      (∀ a y z, profile y = profile z → p y = p z → C a y = C a z) := by
  let q (b : B) := ∑ y ∈ univ.filter (fun y => profile y = b), p y
  let C (a : A) (y : Y) := π a (profile y) * (p y / q (profile y))
  have qn (b : B) : 0 ≤ q b := sum_nonneg (fun y _ => nn y)
  have zeroColumn (a : A) (b : B) (hb : q b = 0) : π a b = 0 := by
    have atom := single_le_sum (fun a _ => pn a b) (mem_univ a)
    have col := columns b
    change ∑ a, π a b = q b at col
    rw [col, hb] at atom
    exact le_antisymm atom (pn a b)
  refine ⟨C, fun a y => mul_nonneg (pn a _) (div_nonneg (nn y) (qn _)), ?_, ?_,
    fun a y hp => by simp [C, hp], fun a y z mask weight => by simp [C, mask, weight]⟩
  · intro y
    have leq : p y ≤ q (profile y) :=
      single_le_sum (fun z _ => nn z) (mem_filter.mpr ⟨mem_univ y, rfl⟩)
    change (∑ a, π a (profile y) * (p y / q (profile y))) = p y
    rw [← sum_mul, columns (profile y)]
    change q (profile y) * (p y / q (profile y)) = p y
    by_cases hq : q (profile y) = 0
    · rw [hq] at leq
      simp [hq, le_antisymm leq (nn y)]
    · rw [mul_comm, div_mul_cancel₀ _ hq]
  · intro a
    rw [← sum_fiberwise_of_maps_to (g := profile) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro b _
    calc
      _ = ∑ y ∈ univ.filter (fun y => profile y = b), π a b * (p y / q b) := by
        apply sum_congr rfl
        intro y hy
        simp [C, (mem_filter.mp hy).2]
      _ = π a b := by
        rw [← mul_sum, ← sum_div]
        change π a b * (q b / q b) = π a b
        by_cases hb : q b = 0
        · rw [zeroColumn a b hb, zero_mul]
        · rw [div_self hb, mul_one]
end

section
variable {G X Y B : Type*} [Monoid G] [MulAction G Y] [Fintype X] [Fintype Y]
  [Fintype B] [PartialOrder B]

open Classical in
private theorem ordered_table_gluing (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (invariance : ∀ (g : G) x y, P x (g • y) = P x y)
    (profile : Y → B) (stable : ∀ (g : G) y, profile (g • y) = profile y)
    (m : B → ℝ) (mnn : ∀ a, 0 ≤ m a) (total : ∑ a, m a = 1)
    (π : X → B → B → ℝ) (pn : ∀ x a b, 0 ≤ π x a b)
    (rows : ∀ x a, ∑ b, π x a b = m a)
    (columns : ∀ x b, ∑ a, π x a b = ∑ y ∈ univ.filter (fun y => profile y = b), P x y)
    (ordered : ∀ x a b, ¬ a ≤ b → π x a b = 0) :
    ∃ w : (X → Y) → ℝ,
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧
      (∀ (g : G) t, w (fun x => g • t x) = w t) ∧
      (∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y) ∧
      ∀ U : Finset B, (∀ ⦃a b⦄, a ∈ U → a ≤ b → b ∈ U) →
        ∑ a ∈ U, m a ≤ ∑ t ∈ univ.filter (fun t : X → Y => ∀ x, profile (t x) ∈ U), w t := by
  choose C cn cy ca c0 cs using fun x =>
    lift_along_profile (P x) (nn x) profile (π x) (pn x) (columns x)
  have normal (x : X) (a : B) : ∑ y, C x a y = m a := (ca x a).trans (rows x a)
  let J := jointWeight m C
  obtain ⟨jn, ja, jxy, supp⟩ := joint_weight_glues m C mnn cn normal
  let w (t : X → Y) : ℝ := ∑ a, J a t
  refine ⟨w, fun t => sum_nonneg fun a _ => jn a t, ?_, ?_, ?_, ?_⟩
  · unfold w
    rw [sum_comm]
    simpa only [J, ja] using total
  · intro g t
    apply sum_congr rfl
    intro a _
    unfold J jointWeight
    congr 1
    exact prod_congr rfl fun x _ => congrArg (fun value : ℝ => value / m a)
      (cs x a (g • t x) (t x) (stable g _) (invariance g x _))
  · intro x y
    have pull (t : X → Y) :
        (if t x = y then w t else 0) = ∑ a, if t x = y then J a t else 0 := by
      by_cases e : t x = y <;> simp [w, e]
    simp_rw [pull]
    rw [sum_comm]
    simpa only [J, jxy] using cy x y
  · intro U upper
    let E := univ.filter (fun t : X → Y => ∀ x, profile (t x) ∈ U)
    have subset : E ⊆ (univ : Finset (X → Y)) := filter_subset _ _
    have supported (a : B) (ha : a ∈ U) (t : X → Y) (outside : t ∉ E) : J a t = 0 := by
      apply supp (fun a y => a ≤ profile y) (fun x a y h => c0 x a y (ordered x a _ h))
      have missing : ¬ ∀ x, profile (t x) ∈ U := fun hp => outside (mem_filter.mpr ⟨mem_univ _, hp⟩)
      obtain ⟨x, hx⟩ := not_forall.mp missing
      exact ⟨x, fun hb => hx (upper ha hb)⟩
    calc
      ∑ a ∈ U, m a = ∑ a ∈ U, ∑ t ∈ E, J a t := by
        apply sum_congr rfl
        intro a ha
        exact (ja a).symm.trans (sum_subset subset (fun t _ h => supported a ha t h)).symm
      _ = ∑ t ∈ E, ∑ a ∈ U, J a t := sum_comm
      _ ≤ ∑ t ∈ E, w t := by
        apply sum_le_sum
        intro t _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun a _ _ => jn a t)
end

section
abbrev Flags := Bool × Bool

def both : Finset Flags := {(true, true)}
def first : Finset Flags := {(true, false), (true, true)}
def second : Finset Flags := {(false, true), (true, true)}
def either : Finset Flags := {(false, true), (true, false), (true, true)}

private def IsUpper (U : Finset Flags) : Prop := ∀ x y : Flags, x ∈ U → x ≤ y → y ∈ U

private theorem six_upper_sets (U : Finset Flags) (h : IsUpper U) :
    U = ∅ ∨ U = both ∨ U = first ∨ U = second ∨ U = either ∨ U = univ := by
  have leTop (x : Flags) : x ≤ (true, true) := by
    rcases x with ⟨_ | _, _ | _⟩ <;> decide
  have botLe (x : Flags) : (false, false) ≤ x := by
    rcases x with ⟨_ | _, _ | _⟩ <;> decide
  have rising (x : Flags) (hx : x ∈ U) : (true, true) ∈ U :=
    h x (true, true) hx (leTop x)
  by_cases zero : (false, false) ∈ U
  · right; right; right; right; right
    ext x
    exact iff_of_true (h (false, false) x zero (botLe x)) (mem_univ x)
  by_cases top : (true, true) ∈ U
  · by_cases left : (true, false) ∈ U <;> by_cases right : (false, true) ∈ U
    · right; right; right; right; left
      ext x
      rcases x with ⟨_ | _, _ | _⟩ <;> simp [either, zero, top, left, right]
    · right; right; left
      ext x
      rcases x with ⟨_ | _, _ | _⟩ <;> simp [first, zero, top, left, right]
    · right; right; right; left
      ext x
      rcases x with ⟨_ | _, _ | _⟩ <;> simp [second, zero, top, left, right]
    · right; left
      ext x
      rcases x with ⟨_ | _, _ | _⟩ <;> simp [both, zero, top, left, right]
  · left
    ext x
    exact iff_of_false (fun hx => top (rising x hx)) (notMem_empty x)

private abbrev mass (p : Flags → ℝ) (U : Finset Flags) : ℝ := ∑ x ∈ U, p x

private noncomputable def law (a b c : ℝ) : Flags → ℝ
  | (false, false) => 1 - a - b + c
  | (true, false) => a - c
  | (false, true) => b - c
  | (true, true) => c

private theorem law_values (a b c : ℝ) :
    mass (law a b c) univ = 1 ∧ mass (law a b c) both = c ∧
    mass (law a b c) first = a ∧ mass (law a b c) second = b ∧
    mass (law a b c) either = a + b - c := by
  have fill : (univ : Finset Flags) =
      {(false, false), (true, false), (false, true), (true, true)} := by decide
  rw [fill]
  simp [mass, both, first, second, either, law]
  constructor <;> ring

private theorem law_nonneg (a b c : ℝ) (hc : 0 ≤ c) (h₁ : c ≤ a) (h₂ : c ≤ b) (h : a + b - c ≤ 1) :
    ∀ x, 0 ≤ law a b c x := by
  rintro ⟨_ | _, _ | _⟩ <;> simp only [law] <;> linarith

private theorem coupled_mask {X : Type*} (p : X → Flags → ℝ) (a b c : ℝ)
    (nonneg : ∀ x z, 0 ≤ p x z) (total : ∀ x, mass (p x) univ = 1)
    (hc : 0 ≤ c) (h₁ : c ≤ a) (h₂ : c ≤ b) (h : a + b - c ≤ 1)
    (rowFirst : ∀ x, a ≤ mass (p x) first) (rowSecond : ∀ x, b ≤ mass (p x) second)
    (rowBoth : ∀ x, c ≤ mass (p x) both)
    (rowEither : ∀ x, a + b - c ≤ mass (p x) either) :
    ∀ x, ∃ π : Flags → Flags → ℝ, (∀ i j, 0 ≤ π i j) ∧
      (∀ i, ∑ j, π i j = law a b c i) ∧ (∀ j, ∑ i, π i j = p x j) ∧
      (∀ i j, ¬ i ≤ j → π i j = 0) := by
  intro x
  obtain ⟨lu, lb, lf, ls, le⟩ := law_values a b c
  apply (D5.S3.Analytic.Probability.FiniteOrderedStrassen.forall_isUpperSet_sum_le_iff_exists_coupling
    (law a b c) (p x) (law_nonneg a b c hc h₁ h₂ h) (nonneg x) (lu.trans (total x).symm)).mp
  intro U hu
  change mass (law a b c) U ≤ mass (p x) U
  rcases six_upper_sets U (fun _ _ hm hle => hu hm hle) with e | e | e | e | e | e
  · simp [e]
  · rw [e, lb]
    exact rowBoth x
  · rw [e, lf]
    exact rowFirst x
  · rw [e, ls]
    exact rowSecond x
  · rw [e, le]
    exact rowEither x
  · rw [e, lu, total]
end

section
variable {X Y B : Type*} [Fintype X] [Fintype Y] [Fintype B] [PartialOrder B]

open Classical in
noncomputable def rowMass (P : X → Y → ℝ) (flag : Y → B) (x : X) (U : Finset B) : ℝ :=
  ∑ y ∈ univ.filter (fun y => flag y ∈ U), P x y

open Classical in
noncomputable def tableMass (w : (X → Y) → ℝ) (flag : Y → B) (U : Finset B) : ℝ :=
  ∑ t ∈ univ.filter (fun t => ∀ x, flag (t x) ∈ U), w t

omit [Fintype B] [PartialOrder B] in
open Classical in
private theorem table_mass_le_row (P : X → Y → ℝ) (w : (X → Y) → ℝ)
    (wn : ∀ t, 0 ≤ w t)
    (marginal : ∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y)
    (flag : Y → B) (x : X) (U : Finset B) :
    tableMass w flag U ≤ rowMass P flag x U := by
  let E := univ.filter (fun y => flag y ∈ U)
  have row : (∑ t ∈ univ.filter (fun t : X → Y => t x ∈ E), w t) = rowMass P flag x U := by
    rw [← sum_fiberwise_eq_sum_filter univ E (fun t : X → Y => t x) w]
    unfold rowMass
    apply sum_congr rfl
    intro y _
    rw [sum_filter]
    exact marginal x y
  rw [← row]
  unfold tableMass
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    exact mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ht).2 x⟩⟩
  · exact fun t _ _ => wn t

open Classical in
private theorem table_mass_eq_of_tight_row {G : Type*} [Monoid G] [MulAction G Y]
    {I : Type*} (P : X → Y → ℝ) (Pnn : ∀ x y, 0 ≤ P x y)
    (Pinv : ∀ (g : G) x y, P x (g • y) = P x y)
    (flag : Y → B) (stable : ∀ (g : G) y, flag (g • y) = flag y)
    (m : B → ℝ) (mnn : ∀ a, 0 ≤ m a) (total : ∑ a, m a = 1)
    (π : X → B → B → ℝ) (pn : ∀ x a b, 0 ≤ π x a b)
    (rows : ∀ x a, ∑ b, π x a b = m a)
    (columns : ∀ x b, ∑ a, π x a b = ∑ y ∈ univ.filter (fun y => flag y = b), P x y)
    (ordered : ∀ x a b, ¬ a ≤ b → π x a b = 0)
    (U : I → Finset B) (upper : ∀ i, ∀ ⦃a b⦄, a ∈ U i → a ≤ b → b ∈ U i)
    (tight : ∀ i, ∃ x, rowMass P flag x (U i) = ∑ a ∈ U i, m a) :
    ∃ w : (X → Y) → ℝ,
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧
      (∀ (g : G) t, w (fun x => g • t x) = w t) ∧
      (∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y) ∧
      ∀ i, tableMass w flag (U i) = ∑ a ∈ U i, m a := by
  obtain ⟨w, wn, norm, inv, marg, lower⟩ :=
    ordered_table_gluing P Pnn Pinv flag stable m mnn total π pn rows columns ordered
  refine ⟨w, wn, norm, inv, marg, fun i => ?_⟩
  obtain ⟨x, eq⟩ := tight i
  exact le_antisymm ((table_mass_le_row P w wn marg flag x (U i)).trans_eq eq)
    (lower (U i) (upper i))
end

section
variable {G X Y : Type*} [Monoid G] [MulAction G Y] [Fintype X] [Fintype Y]

omit [Fintype X] in
open Classical in
private theorem pushed_rows (P : X → Y → ℝ) (flag : Y → Flags) :
    let p (x : X) (z : Flags) := ∑ y ∈ univ.filter (fun y => flag y = z), P x y
    ∀ x U, mass (p x) U = rowMass P flag x U := by
  dsimp only
  intro x U
  unfold mass rowMass
  calc
    _ = ∑ j ∈ U, ∑ y ∈ univ.filter (fun y => flag y = j), P x y := rfl
    _ = ∑ y ∈ univ.filter (fun y => flag y ∈ U), P x y :=
      sum_fiberwise_eq_sum_filter univ U flag (P x)
    _ = _ := by
      apply sum_congr
      · ext y
        simp
      · intro y _
        rfl

open Classical in
private theorem simultaneous_flag_optima (P : X → Y → ℝ) (Pnn : ∀ x y, 0 ≤ P x y)
    (Pnorm : ∀ x, ∑ y, P x y = 1)
    (Pinv : ∀ (g : G) x y, P x (g • y) = P x y)
    (flag : Y → Flags) (stable : ∀ (g : G) y, flag (g • y) = flag y)
    (m₁ m₂ iMin uMin : ℝ)
    (least₁ : ∀ x, m₁ ≤ rowMass P flag x first)
    (least₂ : ∀ x, m₂ ≤ rowMass P flag x second)
    (leastI : ∀ x, iMin ≤ rowMass P flag x both)
    (leastU : ∀ x, uMin ≤ rowMass P flag x either)
    (attain₁ : ∃ x, rowMass P flag x first = m₁)
    (attain₂ : ∃ x, rowMass P flag x second = m₂)
    (attainI : ∃ x, rowMass P flag x both = iMin)
    (attainU : ∃ x, rowMass P flag x either = uMin)
    (ineq : m₁ + m₂ ≤ iMin + uMin) :
    ∃ w : (X → Y) → ℝ,
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧
      (∀ (g : G) t, w (fun x => g • t x) = w t) ∧
      (∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y) ∧
      tableMass w flag first = m₁ ∧ tableMass w flag second = m₂ := by
  let p (x : X) (a : Flags) := ∑ y ∈ univ.filter (fun y => flag y = a), P x y
  let c := max 0 (m₁ + m₂ - uMin)
  have pnn (x : X) (a : Flags) : 0 ≤ p x a := sum_nonneg (fun y _ => Pnn x y)
  have ptotal (x : X) : mass (p x) univ = 1 := by
    rw [pushed_rows P flag x univ]
    simpa [rowMass] using Pnorm x
  have lower (x : X) (U : Finset Flags) : 0 ≤ rowMass P flag x U :=
    sum_nonneg (fun y _ => Pnn x y)
  have sub (U V : Finset Flags) (h : U ⊆ V) (x : X) :
      rowMass P flag x U ≤ rowMass P flag x V := by
    unfold rowMass
    apply sum_le_sum_of_subset_of_nonneg
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      exact h hy
    · exact fun y _ _ => Pnn x y
  obtain ⟨x₁, h₁⟩ := attain₁
  obtain ⟨x₂, h₂⟩ := attain₂
  obtain ⟨xI, hI⟩ := attainI
  obtain ⟨xU, hU⟩ := attainU
  have mn₁ := h₁ ▸ lower x₁ first
  have mn₂ := h₂ ▸ lower x₂ second
  have inonneg := hI ▸ lower xI both
  have u₁ : m₁ ≤ uMin := (least₁ xU).trans (hU ▸ sub first either (by decide) xU)
  have u₂ : m₂ ≤ uMin := (least₂ xU).trans (hU ▸ sub second either (by decide) xU)
  have u₀ : uMin ≤ 1 := by
    have hu := sub either univ (subset_univ _) xU
    rw [hU, ← pushed_rows P flag xU univ] at hu
    exact hu.trans_eq (ptotal xU)
  have c₀ : 0 ≤ c := le_max_left _ _
  have c₁ : c ≤ m₁ := max_le mn₁ (by linarith)
  have c₂ : c ≤ m₂ := max_le mn₂ (by linarith)
  have ci : c ≤ iMin := max_le inonneg (by linarith)
  have cu : m₁ + m₂ - c ≤ uMin := by
    have h := le_max_right (0 : ℝ) (m₁ + m₂ - uMin)
    change m₁ + m₂ - uMin ≤ c at h
    linarith
  have pfirst (x : X) : m₁ ≤ mass (p x) first := by
    rw [pushed_rows P flag x first]
    exact least₁ x
  have psecond (x : X) : m₂ ≤ mass (p x) second := by
    rw [pushed_rows P flag x second]
    exact least₂ x
  have pboth (x : X) : c ≤ mass (p x) both := by
    rw [pushed_rows P flag x both]
    exact ci.trans (leastI x)
  have peither (x : X) : m₁ + m₂ - c ≤ mass (p x) either := by
    rw [pushed_rows P flag x either]
    exact cu.trans (leastU x)
  choose π πn πr πc πs using coupled_mask p m₁ m₂ c pnn ptotal c₀ c₁ c₂ (cu.trans u₀)
    pfirst psecond pboth peither
  let U (b : Bool) := if b then first else second
  obtain ⟨norm, _, lf, ls, _⟩ := law_values m₁ m₂ c
  have upper (b : Bool) : ∀ ⦃a d : Flags⦄, a ∈ U b → a ≤ d → d ∈ U b := by
    cases b <;> decide
  have tight (b : Bool) : ∃ x, rowMass P flag x (U b) = ∑ a ∈ U b, law m₁ m₂ c a := by
    cases b
    · exact ⟨x₂, h₂.trans ls.symm⟩
    · exact ⟨x₁, h₁.trans lf.symm⟩
  obtain ⟨w, wn, wt, wi, wr, eq⟩ := table_mass_eq_of_tight_row P Pnn Pinv flag stable
    (law m₁ m₂ c) (law_nonneg m₁ m₂ c c₀ c₁ c₂ (cu.trans u₀)) norm π πn πr (fun x b => by
      rw [πc]
      apply sum_congr
      · ext y
        simp
      · intro y _
        rfl) πs U upper tight
  exact ⟨w, wn, wt, wi, wr, (eq true).trans lf, (eq false).trans ls⟩

open Classical in
private theorem simultaneous_flag_optima_bound (P : X → Y → ℝ)
    (w : (X → Y) → ℝ) (wn : ∀ t, 0 ≤ w t)
    (marg : ∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y)
    (flag : Y → Flags) (xI xU : X) :
    tableMass w flag first + tableMass w flag second ≤
      rowMass P flag xI both + rowMass P flag xU either := by
  let tables (U : Finset Flags) := univ.filter (fun t : X → Y => ∀ x, flag (t x) ∈ U)
  let First := tables first
  let Second := tables second
  let Both := tables both
  let Either := tables either
  have count (U : Finset Flags) : tableMass w flag U = ∑ t ∈ tables U, w t := by
    unfold tableMass tables
    apply sum_congr
    · ext t
      simp
    · intro _ _
      rfl
  have overlap : First ∩ Second = Both := by
    have same : ∀ a : Flags, a ∈ first ∧ a ∈ second ↔ a ∈ both := by decide
    ext t
    simp only [First, Second, Both, tables, mem_inter, mem_filter, mem_univ, true_and, ← same]
    exact forall_and.symm
  have cover : First ∪ Second ⊆ Either := by
    have fst : first ⊆ either := by decide
    have snd : second ⊆ either := by decide
    intro t ht
    simp only [First, Second, Either, tables, mem_union, mem_filter, mem_univ, true_and] at ht ⊢
    rcases ht with hf | hs
    · exact fun x => fst (hf x)
    · exact fun x => snd (hs x)
  have unpack : tableMass w flag first + tableMass w flag second =
      (∑ t ∈ First ∪ Second, w t) + ∑ t ∈ Both, w t := by
    rw [← overlap, sum_union_inter, count first, count second]
  rw [unpack, ← count both]
  have boundUnion : (∑ t ∈ First ∪ Second, w t) ≤ tableMass w flag either := by
    rw [count either]
    exact sum_le_sum_of_subset_of_nonneg cover (fun t _ _ => wn t)
  exact (add_le_add (boundUnion.trans (table_mass_le_row P w wn marg flag xU either))
    (table_mass_le_row P w wn marg flag xI both)).trans_eq (add_comm _ _)
end

section

variable {G X Y : Type*} [Monoid G] [MulAction G Y] [Fintype X] [Fintype Y]

open Classical in
/-- A single invariant table law attains both coordinate row minima exactly when their sum
is at most the sum of the least intersection and least union masses. -/
theorem two_table_masses_attain_row_minima_iff (P : X → Y → ℝ)
    (Pnn : ∀ x y, 0 ≤ P x y) (Pnorm : ∀ x, ∑ y, P x y = 1)
    (Pinv : ∀ (g : G) x y, P x (g • y) = P x y)
    (flag : Y → Flags) (stable : ∀ (g : G) y, flag (g • y) = flag y)
    (m₁ m₂ iMin uMin : ℝ)
    (least₁ : ∀ x, m₁ ≤ rowMass P flag x first)
    (least₂ : ∀ x, m₂ ≤ rowMass P flag x second)
    (leastI : ∀ x, iMin ≤ rowMass P flag x both)
    (leastU : ∀ x, uMin ≤ rowMass P flag x either)
    (attain₁ : ∃ x, rowMass P flag x first = m₁)
    (attain₂ : ∃ x, rowMass P flag x second = m₂)
    (attainI : ∃ x, rowMass P flag x both = iMin)
    (attainU : ∃ x, rowMass P flag x either = uMin) :
    (∃ w : (X → Y) → ℝ,
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧
      (∀ (g : G) t, w (fun x => g • t x) = w t) ∧
      (∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y) ∧
      tableMass w flag first = m₁ ∧ tableMass w flag second = m₂) ↔
    m₁ + m₂ ≤ iMin + uMin := by
  constructor
  · rintro ⟨w, wn, _, _, wm, e₁, e₂⟩
    obtain ⟨xI, hI⟩ := attainI
    obtain ⟨xU, hU⟩ := attainU
    have bound := simultaneous_flag_optima_bound P w wn wm flag xI xU
    rwa [e₁, e₂, hI, hU] at bound
  · exact simultaneous_flag_optima P Pnn Pnorm Pinv flag stable m₁ m₂ iMin uMin
      least₁ least₂ leastI leastU attain₁ attain₂ attainI attainU

end
end D5.S3.ConceptDynamics.Attribution.JointFixedTableMass
