/- GID: D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic]
   utility: none
   digest: Partial assignment flows preserve all masses and exactly the archived terminal laws. -/

import D5.S3.Estimation.DataProcessing.OrderedCoordinateFlowRealization

open MeasureTheory Finset Function
open scoped BigOperators ENNReal Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Estimation.DataProcessing.PartialAssignmentOccupancyFlow
open OrderedCoordinateHistoryInterpreter OrderedCoordinateFlowRealization

variable {I : Type*} {X : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

/-- A literal named partial assignment, with a separate dependent alphabet at each coordinate. -/
abbrev Assignment (X : I → Type*) := (i : I) → Option (X i)
def empty : Assignment X := fun _ => none
def support (a : Assignment X) : Finset I := univ.filter fun i => (a i).isSome
def rank (a : Assignment X) : ℕ := (support a).card
abbrev Available (a : Assignment X) := {i : I // a i = none}
abbrev Assigned (a : Assignment X) := {i : I // (a i).isSome}
def value (a : Assignment X) (i : Assigned a) : X i.val := (a i.val).get i.property
def insert (a : Assignment X) (i : I) (x : X i) : Assignment X :=
  Function.update a i (some x)
def delete (a : Assignment X) (i : I) : Assignment X := Function.update a i none

@[simp] theorem mem_support (a : Assignment X) (i : I) :
    i ∈ support a ↔ (a i).isSome := by simp [support]
@[simp] theorem empty_rank : rank (empty : Assignment X) = 0 := by simp [rank, support, empty]

/-- Erasure keeps the actual value at each read coordinate and discards only order. -/
def erase {k : ℕ} (h : History X k) (i : I) : Option (X i) :=
  if hj : ∃ j, (h.val j).1 = i then
    some (hj.choose_spec ▸ (h.val hj.choose).2) else none

/-- The graph of erasure is exactly the graph of the ordered history. -/
theorem erase_some_iff {k : ℕ} (h : History X k) (i : I) (x : X i) :
    erase h i = some x ↔ ∃ j, h.val j = ⟨i, x⟩ := by
  classical
  unfold erase
  split_ifs with hj
  · let j := hj.choose
    have he : (h.val j).1 = i := hj.choose_spec
    have hc : ∀ (z : Sigma X) (c : I) (e : z.1 = c), z = ⟨c, e ▸ z.2⟩ := by
      rintro ⟨c,y⟩ d e
      cases e
      rfl
    have hz : (h.val j) = ⟨i, he ▸ (h.val j).2⟩ := hc _ _ he
    constructor
    · intro hx
      exact ⟨j, hz.trans (by simpa using congrArg (fun y : X i => (⟨i,y⟩ : Sigma X)) (Option.some.inj hx))⟩
    · rintro ⟨l, hl⟩
      have hc : (h.val l).1 = i := congrArg Sigma.fst hl
      have hlj : l = j := h.property (hc.trans he.symm)
      subst l
      have hx := (Sigma.mk.inj (hz.symm.trans hl)).2
      exact congrArg some (eq_of_heq hx)
  · simp only [reduceCtorEq, false_iff, not_exists]
    intro j he
    exact hj ⟨j, congrArg Sigma.fst he⟩

/-- Unread coordinates are the same before and after erasure. -/
theorem erase_none_iff {k : ℕ} (h : History X k) (i : I) :
    erase h i = none ↔ ∀ j, (h.val j).1 ≠ i := by
  unfold erase
  split_ifs with hj
  · simp only [Option.some_ne_none, false_iff, not_forall, not_not]
    exact hj
  · simp only [true_iff, not_exists] at *
    exact hj

abbrev unreadEquiv {k : ℕ} (h : History X k) : Unread h ≃ Available (erase h) where
  toFun i := ⟨i.val, (erase_none_iff h i.val).mpr i.property⟩
  invFun i := ⟨i.val, (erase_none_iff h i.val).mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem erase_root : erase (root : History X 0) = empty := by
  funext i
  apply (erase_none_iff _ _).mpr
  intro j
  exact Fin.elim0 j

/-- Erasure preserves the number of read named coordinates. -/
theorem erase_rank {k : ℕ} (h : History X k) : rank (erase h) = k := by
  have hs : support (erase h) = univ.image (fun j => (h.val j).1) := by
    ext i
    simp only [mem_support, mem_image, mem_univ, true_and]
    constructor
    · intro hi
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hi
      obtain ⟨j,hj⟩ := (erase_some_iff h i x).mp hx
      exact ⟨j, congrArg Sigma.fst hj⟩
    · rintro ⟨j,hj⟩
      have hx : erase h i = some (hj ▸ (h.val j).2) :=
        (erase_some_iff h i _).mpr ⟨j, by cases hj; rfl⟩
      rw [hx]; rfl
  rw [rank, hs, card_image_of_injective _ h.property]
  simp

/-- Appending a read corresponds to literal insertion into the named assignment. -/
theorem erase_append {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) :
    erase (append h i x) = insert (erase h) i.val x := by
  funext j
  by_cases hj : j = i.val
  · subst j
    rw [insert, Function.update_self]
    exact (erase_some_iff _ _ _).mpr ⟨Fin.last k, by simp [append]⟩
  · rw [insert, Function.update_of_ne hj]
    apply Option.ext
    intro y
    rw [erase_some_iff, erase_some_iff]
    constructor
    · rintro ⟨l,hl⟩
      refine Fin.lastCases ?_ (fun l hl => ?_) l hl
      · intro hl
        have he : i.val = j := by simpa [append] using congrArg Sigma.fst hl
        exact (hj he.symm).elim
      · exact ⟨l, by simpa [append] using hl⟩
    · rintro ⟨l,hl⟩
      exact ⟨l.castSucc, by simpa [append] using hl⟩

/-- Deleting the actual last coordinate recovers the parent's erased assignment. -/
theorem erase_parent {k : ℕ} (h : History X (k+1)) :
    erase (parent h) = delete (erase h) (lastCoord h).val := by
  have he : erase h = insert (erase (parent h)) (lastCoord h).val (lastLetter h) :=
    (congrArg erase (append_parent h)).symm.trans (erase_append _ _ _)
  rw [he]
  funext j
  by_cases hj : j = (lastCoord h).val
  · subst j
    rw [delete, Function.update_self]
    exact (erase_none_iff _ _).mpr (lastCoord h).property
  · simp [delete, insert, hj]

/-- Incoming parents are indexed by every assigned coordinate, not by one chosen order. -/
abbrev Incoming (k : ℕ) (a : Assignment X) :=
  Σ i : Assigned a, {h : History X k // erase h = delete a i.val}
abbrev Fiber (k : ℕ) (a : Assignment X) := {h : History X k // erase h = a}

def incomingAppend {k : ℕ} {a : Assignment X} (e : Incoming k a) : Fiber (k+1) a := by
  let i : Unread e.2.val := ⟨e.1.val, (erase_none_iff _ _).mp (by rw [e.2.property]; simp [delete])⟩
  refine ⟨append e.2.val i (value a e.1), ?_⟩
  rw [erase_append, e.2.property]
  change insert (delete a e.1.val) e.1.val (value a e.1) = a
  funext j
  by_cases hj : j = e.1.val
  · subst j
    simp only [insert, Function.update_self]
    exact Option.some_get e.1.property
  · simp [insert, delete, hj]

/-- The actual last-coordinate partition is a bijection on order-erasure fibers. -/
theorem incomingAppend_bijective (k : ℕ) (a : Assignment X) :
    Function.Bijective (incomingAppend (k := k) (a := a)) := by
  constructor
  · rintro ⟨i,h⟩ ⟨j,g⟩ he
    have hev : (incomingAppend ⟨i,h⟩).val = (incomingAppend ⟨j,g⟩).val := congrArg Subtype.val he
    have hc : i.val = j.val := by
      simpa [incomingAppend, append] using congrArg (fun z : History X (k+1) => (z.val (Fin.last k)).1) hev
    have hij : i = j := Subtype.ext hc
    subst j
    have hh : h.val = g.val := by
      simpa [incomingAppend] using congrArg parent hev
    have hg : h = g := Subtype.ext hh
    subst g
    rfl
  · intro h
    let i : Assigned a := ⟨(lastCoord h.val).val, by
      have hx : erase h.val (lastCoord h.val).val = some (lastLetter h.val) :=
        (erase_some_iff _ _ _).mpr ⟨Fin.last k, rfl⟩
      rw [h.property] at hx
      rw [hx]; rfl⟩
    let g : Fiber k (delete a i.val) := ⟨parent h.val, by rw [erase_parent, h.property]⟩
    refine ⟨⟨i,g⟩, ?_⟩
    apply Subtype.ext
    have hx : value a i = lastLetter h.val := by
      have hz : a i.val = some (lastLetter h.val) := by
        exact (congrArg (fun z : Assignment X => z i.val) h.property).symm.trans
          ((erase_some_iff _ _ _).mpr ⟨Fin.last k,rfl⟩)
      apply Option.some.inj
      exact (Option.some_get i.property).trans hz
    change append (parent h.val) _ (value a i) = h.val
    rw [hx]
    exact append_parent h.val

/-- Finite sums over child fibers split into all deleted-parent fibers. -/
def incomingEquiv (k : ℕ) (a : Assignment X) : Incoming k a ≃ Fiber (k+1) a :=
  Equiv.ofBijective incomingAppend (incomingAppend_bijective k a)

/-- The occupancy constraints contain only literal node and edge masses. -/
@[ext] structure OccupancyFlow (r : I → ℝ) where
  mass : Assignment X → ℝ
  select : (a : Assignment X) → Available a → ℝ
  result : (a : Assignment X) → (i : Available a) → X i.val → ℝ
  mass_nonneg : ∀ a, 0 ≤ mass a
  select_nonneg : ∀ a i, 0 ≤ select a i
  result_nonneg : ∀ a i x, 0 ≤ result a i x
  root_mass : mass empty = 1
  select_sum : ∀ a, rank a < Fintype.card I → ∑ i, select a i = mass a
  result_sum : ∀ a i, ∑ x, result a i x = select a i
  result_cap : ∀ a i x, result a i x ≤ r i.val * select a i
  incoming : ∀ a, a ≠ empty → mass a = ∑ i : Assigned a,
    result (delete a i.val) ⟨i.val, by simp [delete]⟩ (value a i)

@[simp] theorem support_delete (a : Assignment X) (i : I) :
    support (delete a i) = (support a).erase i := by
  ext j
  rw [mem_support, Finset.mem_erase, mem_support]
  by_cases hj : j = i
  · subst j; simp only [delete, Function.update_self, Option.isSome_none]; simp
  · rw [delete, Function.update_of_ne hj]
    exact (and_iff_right hj).symm
theorem delete_rank (a : Assignment X) (i : Assigned a) :
    rank (delete a i.val) + 1 = rank a := by
  change (support (delete a i.val)).card + 1 = (support a).card
  rw [support_delete]
  exact Finset.card_erase_add_one ((mem_support a i.val).mpr i.property)

theorem rank_zero_iff (a : Assignment X) : rank a = 0 ↔ a = empty := by
  constructor
  · intro ha
    have hs : support a = ∅ := Finset.card_eq_zero.mp ha
    funext i
    have hi : ¬ (a i).isSome := by
      intro hi
      have hm := (mem_support a i).mpr hi
      rw [hs] at hm
      simpa using hm
    cases hx : a i with
    | none => rfl
    | some x => exact (hi (by rw [hx]; rfl)).elim
  · rintro rfl; exact empty_rank

theorem available_nonempty (a : Assignment X) (ha : rank a < Fintype.card I) :
    Nonempty (Available a) := by
  by_contra hn
  have hs : support a = univ := by
    ext i
    simp only [mem_univ, iff_true, mem_support]
    cases hi : a i with
    | none => exact (hn ⟨⟨i,hi⟩⟩).elim
    | some x => rfl
  have hc : rank a = Fintype.card I := by rw [rank,hs]; simp
  omega

namespace OccupancyFlow
variable {r : I → ℝ} (o : OccupancyFlow (X := X) r)

/-- Uniform fallback at a null node is a lawful row on the actual unread coordinates. -/
def sigma (a : Assignment X) (i : Available a) : ℝ :=
  if o.mass a = 0 then 1 / Fintype.card (Available a) else o.select a i / o.mass a

/-- Uniform fallback at a null selection uses that coordinate's own alphabet. -/
def q (a : Assignment X) (i : Available a) (x : X i.val) : ℝ :=
  if o.select a i = 0 then 1 / Fintype.card (X i.val) else o.result a i x / o.select a i
theorem select_zero (a : Assignment X) (ha : rank a < Fintype.card I)
    (hm : o.mass a = 0) (i : Available a) : o.select a i = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => o.select_nonneg a i)).mp
    ((o.select_sum a ha).trans hm) i (mem_univ i)
theorem result_zero (a : Assignment X) (i : Available a)
    (hf : o.select a i = 0) (x : X i.val) : o.result a i x = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => o.result_nonneg a i x)).mp
    ((o.result_sum a i).trans hf) x (mem_univ x)
theorem sigma_law (a : Assignment X) (ha : rank a < Fintype.card I) :
    (∀ i, 0 ≤ o.sigma a i) ∧ ∑ i, o.sigma a i = 1 := by
  letI := available_nonempty a ha
  by_cases hm : o.mass a = 0
  · simp only [sigma,hm,if_true]
    exact ⟨fun _ => by positivity, by simp [Fintype.card_ne_zero]⟩
  · simp only [sigma,hm,if_false]
    exact ⟨fun i => div_nonneg (o.select_nonneg a i) (o.mass_nonneg a), by
      rw [← Finset.sum_div, o.select_sum a ha, div_self hm]⟩
theorem q_law (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (a : Assignment X) (i : Available a) :
    (∀ x, 0 ≤ o.q a i x ∧ o.q a i x ≤ r i.val) ∧ ∑ x, o.q a i x = 1 := by
  by_cases hf : o.select a i = 0
  · simp only [q,hf,if_true]
    exact ⟨fun _ => ⟨by positivity,hr i.val⟩, by simp [Fintype.card_ne_zero]⟩
  · simp only [q,hf,if_false]
    have hp : 0 < o.select a i := lt_of_le_of_ne (o.select_nonneg a i) (Ne.symm hf)
    exact ⟨fun x => ⟨div_nonneg (o.result_nonneg a i x) hp.le,
      (div_le_iff₀ hp).mpr (o.result_cap a i x)⟩, by
      rw [← Finset.sum_div, o.result_sum a i, div_self hf]⟩

/-- Weighted rows are literal flow identities even when the row's denominator vanishes. -/
theorem weighted_sigma (a : Assignment X) (ha : rank a < Fintype.card I)
    (i : Available a) : o.mass a * o.sigma a i = o.select a i := by
  by_cases hm : o.mass a = 0
  · rw [hm, zero_mul, o.select_zero a ha hm i]
  · simp only [sigma,hm,if_false]
    field_simp
theorem weighted_q (a : Assignment X) (i : Available a) (x : X i.val) :
    o.select a i * o.q a i x = o.result a i x := by
  by_cases hf : o.select a i = 0
  · rw [hf, zero_mul, o.result_zero a i hf x]
  · simp only [q,hf,if_false]
    field_simp

/-- Ordered node masses are constructed recursively, rather than supplied as a witness. -/
def orderedMass (o : OccupancyFlow (X := X) r) : (k : ℕ) → History X k → ℝ
  | 0, _ => 1
  | k+1, h => orderedMass o k (parent h) *
      o.sigma (erase (parent h)) (unreadEquiv (parent h) (lastCoord h)) *
      o.q (erase (parent h)) (unreadEquiv (parent h) (lastCoord h)) (lastLetter h)
def orderedSelect (k : ℕ) (h : History X k) (i : Unread h) : ℝ :=
  o.orderedMass k h * o.sigma (erase h) (unreadEquiv h i)
def orderedResult (k : ℕ) (h : History X k) (i : Unread h) (x : X i.val) : ℝ :=
  o.orderedSelect k h i * o.q (erase h) (unreadEquiv h i) x
theorem ordered_child (k : ℕ) (h : History X k) (i : Unread h) (x : X i.val) :
    o.orderedMass (k+1) (append h i x) = o.orderedResult k h i x := by
  exact congrArg (fun e : Σ g : History X k, Σ j : Unread g, X j.val =>
    o.orderedMass k e.1 * o.sigma (erase e.1) (unreadEquiv e.1 e.2.1) *
      o.q (erase e.1) (unreadEquiv e.1 e.2.1) e.2.2)
    ((extensionEquiv k).symm_apply_apply ⟨h,i,x⟩)

theorem orderedMass_nonneg (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (h : History X k) : 0 ≤ o.orderedMass k h := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    have hk : k < Fintype.card I := by
      have hc := Fintype.card_le_of_injective (fun j => (h.val j).1) h.property
      simp only [Fintype.card_fin] at hc
      omega
    exact mul_nonneg (mul_nonneg (ih _) ((o.sigma_law _ (by rw [erase_rank]; exact hk)).1 _))
      (((o.q_law hr _ _).1 _).1)

/-- The recursively built masses satisfy every ordered-flow field. -/
def lift (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) : Flow (X := X) r where
  mass := o.orderedMass
  select := o.orderedSelect
  result := o.orderedResult
  mass_nonneg := o.orderedMass_nonneg hr
  select_nonneg k h i := mul_nonneg (o.orderedMass_nonneg hr k h)
    ((o.sigma_law _ (by rw [erase_rank]; exact unread_lt h i)).1 _)
  result_nonneg k h i x := by
    unfold orderedResult orderedSelect
    exact mul_nonneg (mul_nonneg (o.orderedMass_nonneg hr k h)
      ((o.sigma_law _ (by rw [erase_rank]; exact unread_lt h i)).1 _))
        (((o.q_law hr (erase h) (unreadEquiv h i)).1 x).1)
  root_mass := rfl
  select_sum k hk h := by
    unfold orderedSelect
    rw [← Finset.mul_sum, (unreadEquiv h).sum_comp]
    rw [(o.sigma_law _ (by rw [erase_rank]; exact hk)).2,mul_one]
  result_sum k h i := by
    have hq := (o.q_law hr (erase h) (unreadEquiv h i)).2
    dsimp only [unreadEquiv,Equiv.coe_fn_mk] at hq
    unfold orderedResult
    dsimp only [unreadEquiv,Equiv.coe_fn_mk]
    rw [← Finset.mul_sum,hq,mul_one]
  result_cap k h i x := by
    have hn : 0 ≤ o.orderedSelect k h i := by
      unfold orderedSelect
      exact mul_nonneg (o.orderedMass_nonneg hr k h)
        ((o.sigma_law _ (by rw [erase_rank]; exact unread_lt h i)).1 _)
    exact (mul_le_mul_of_nonneg_left (((o.q_law hr (erase h) (unreadEquiv h i)).1 x).2) hn).trans_eq (mul_comm _ _)
  child_mass := o.ordered_child
end OccupancyFlow

/-- Transport only the unread-coordinate proof, retaining the named coordinate itself. -/
abbrev fiberUnread {k : ℕ} {a : Assignment X} (h : Fiber k a) (i : Available a) : Unread h.val :=
  ⟨i.val, (erase_none_iff h.val i.val).mp
    ((congrArg (fun z : Assignment X => z i.val) h.property).trans i.property)⟩
def aggregateMass {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ) (a : Assignment X) : ℝ :=
  ∑ h : Fiber k a, p.mass k h.val
def aggregateSelect {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ) (a : Assignment X)
    (i : Available a) : ℝ := ∑ h : Fiber k a, p.select k h.val (fiberUnread h i)
def aggregateResult {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ) (a : Assignment X)
    (i : Available a) (x : X i.val) : ℝ :=
  ∑ h : Fiber k a, p.result k h.val (fiberUnread h i) x

/-- Actual incoming conservation follows by summing the unique last-coordinate partition. -/
theorem aggregate_incoming {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ) (a : Assignment X) :
    aggregateMass p (k+1) a = ∑ i : Assigned a,
      aggregateResult p k (delete a i.val) ⟨i.val, by simp [delete]⟩ (value a i) := by
  unfold aggregateMass aggregateResult
  rw [← (incomingEquiv k a).sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  exact p.child_mass k h.val (fiberUnread h ⟨i.val, by simp [delete]⟩) (value a i)

/-- A lifted selection row factors through the erased node, including null nodes. -/
theorem lift_aggregateSelect {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (a : Assignment X) (i : Available a) :
    aggregateSelect (o.lift hr) k a i = aggregateMass (o.lift hr) k a * o.sigma a i := by
  unfold aggregateSelect aggregateMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rcases h with ⟨h,he⟩
  subst a
  rfl

/-- A lifted result row factors through the global state row, including null selections. -/
theorem lift_aggregateResult {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (a : Assignment X) (i : Available a) (x : X i.val) :
    aggregateResult (o.lift hr) k a i x =
      aggregateMass (o.lift hr) k a * o.sigma a i * o.q a i x := by
  unfold aggregateResult aggregateMass
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rcases h with ⟨h,he⟩
  subst a
  rfl

/-- Rank induction recovers every prescribed occupancy node mass, not only a terminal law. -/
theorem lift_aggregateMass {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (a : Assignment X) (ha : rank a = k) :
    aggregateMass (o.lift hr) k a = o.mass a := by
  induction k generalizing a with
  | zero =>
    have he : a = empty := (rank_zero_iff a).mp ha
    subst a
    let h0 : Fiber 0 (empty : Assignment X) := ⟨root,erase_root⟩
    haveI : Unique (Fiber 0 (empty : Assignment X)) :=
      { default := h0, uniq := fun h => Subsingleton.elim _ _ }
    rw [aggregateMass,Fintype.sum_unique,o.root_mass]
    rfl
  | succ k ih =>
    have hn : a ≠ empty := by intro he; subst a; simp at ha
    rw [aggregate_incoming,o.incoming a hn]
    apply Finset.sum_congr rfl
    intro i _
    rw [lift_aggregateResult,ih (delete a i.val) (by have hd := delete_rank a i; omega)]
    rw [o.weighted_sigma _ (by
      have hs : rank a ≤ Fintype.card I := Finset.card_le_card (Finset.subset_univ _)
      have hd := delete_rank a i
      omega),o.weighted_q]

/-- The constructive lift is a right inverse in all three mass families. -/
theorem lift_all_masses {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    (∀ a, aggregateMass (o.lift hr) (rank a) a = o.mass a) ∧
    (∀ a (ha : rank a < Fintype.card I) i,
      aggregateSelect (o.lift hr) (rank a) a i = o.select a i) ∧
    (∀ a (ha : rank a < Fintype.card I) i x,
      aggregateResult (o.lift hr) (rank a) a i x = o.result a i x) := by
  refine ⟨fun a => lift_aggregateMass o hr _ a rfl,?_,?_⟩
  · intro a ha i
    rw [lift_aggregateSelect,lift_aggregateMass o hr _ a rfl,o.weighted_sigma a ha i]
  · intro a ha i x
    rw [lift_aggregateResult,lift_aggregateMass o hr _ a rfl,o.weighted_sigma a ha i,o.weighted_q]

/-- The fiber's coordinate correspondence is a bijection, without any renaming. -/
def fiberUnreadEquiv {k : ℕ} {a : Assignment X} (h : Fiber k a) :
    Available a ≃ Unread h.val := by
  rcases h with ⟨h,he⟩
  subst a
  exact (unreadEquiv h).symm

theorem aggregate_select_sum {r : I → ℝ} (p : Flow (X := X) r)
    (k : ℕ) (hk : k < Fintype.card I) (a : Assignment X) :
    ∑ i, aggregateSelect p k a i = aggregateMass p k a := by
  unfold aggregateSelect aggregateMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have he : (fun i : Available a => p.select k h.val (fiberUnread h i)) =
      fun i => p.select k h.val (fiberUnreadEquiv h i) := by
    rcases h with ⟨h,hh⟩; subst a; rfl
  rw [he,(fiberUnreadEquiv h).sum_comp,p.select_sum k hk h.val]

theorem aggregate_result_sum {r : I → ℝ} (p : Flow (X := X) r)
    (k : ℕ) (a : Assignment X) (i : Available a) :
    ∑ x, aggregateResult p k a i x = aggregateSelect p k a i := by
  unfold aggregateResult aggregateSelect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  exact p.result_sum k h.val (fiberUnread h i)

/-- Summation over the actual order-erasure fibers yields all occupancy constraints. -/
def aggregate {r : I → ℝ} (p : Flow (X := X) r) : OccupancyFlow (X := X) r where
  mass a := aggregateMass p (rank a) a
  select a i := aggregateSelect p (rank a) a i
  result a i x := aggregateResult p (rank a) a i x
  mass_nonneg a := Finset.sum_nonneg (fun h _ => p.mass_nonneg _ _)
  select_nonneg a i := Finset.sum_nonneg (fun h _ => p.select_nonneg _ _ _)
  result_nonneg a i x := Finset.sum_nonneg (fun h _ => p.result_nonneg _ _ _ _)
  root_mass := by
    rw [empty_rank]
    let h0 : Fiber 0 (empty : Assignment X) := ⟨root,erase_root⟩
    letI : Unique (Fiber 0 (empty : Assignment X)) :=
      { default := h0, uniq := fun h => Subsingleton.elim _ _ }
    rw [aggregateMass,Fintype.sum_unique]
    exact p.root_mass
  select_sum a ha := aggregate_select_sum p _ ha a
  result_sum a i := aggregate_result_sum p _ a i
  result_cap a i x := by
    unfold aggregateResult aggregateSelect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun h _ => p.result_cap _ _ _ _)
  incoming a hn := by
    have hz : rank a ≠ 0 := fun hh => hn ((rank_zero_iff a).mp hh)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [hk,aggregate_incoming]
    apply Finset.sum_congr rfl
    intro i _
    have hd : rank (delete a i.val) = k := by have he := delete_rank a i; omega
    rw [hd]

/-- The aggregate is literally equal to the original occupancy flow in every mass field. -/
theorem aggregate_lift {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) : aggregate (o.lift hr) = o := by
  apply OccupancyFlow.ext
  · funext a; exact (lift_all_masses o hr).1 a
  · funext a i
    have ha : rank a < Fintype.card I := by
      have hs : support a ≠ univ := by
        intro hs
        have hm : i.val ∈ support a := by rw [hs]; exact mem_univ _
        rw [mem_support,i.property] at hm
        simp at hm
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,hs⟩)
    exact (lift_all_masses o hr).2.1 a ha i
  · funext a i x
    have ha : rank a < Fintype.card I := by
      have hs : support a ≠ univ := by
        intro hs
        have hm : i.val ∈ support a := by rw [hs]; exact mem_univ _
        rw [mem_support,i.property] at hm
        simp at hm
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,hs⟩)
    exact (lift_all_masses o hr).2.2 a ha i x

/-- A complete assignment is still a literal partial assignment with no missing coordinate. -/
def complete (v : (i : I) → X i) : Assignment X := fun i => some (v i)
@[simp] theorem complete_rank (v : (i : I) → X i) : rank (complete v) = Fintype.card I := by
  simp [rank,support,complete]

/-- At the full layer, erasure agrees with the frozen named terminal assignment. -/
theorem erase_terminal (h : History X (Fintype.card I)) :
    erase h = complete (terminalAssignment h) := by
  let e : Fin (Fintype.card I) ≃ I :=
    Equiv.ofBijective (fun j => (h.val j).1)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨h.property, by simp⟩)
  funext i
  change erase h i = some ((e.apply_symm_apply i) ▸ (h.val (e.symm i)).2)
  apply (erase_some_iff _ _ _).mpr
  refine ⟨e.symm i,?_⟩
  have hc : ∀ (z : Sigma X) (c : I) (he : z.1 = c), z = ⟨c,he ▸ z.2⟩ := by
    rintro ⟨c,y⟩ d he; cases he; rfl
  exact hc _ _ (e.apply_symm_apply i)

/-- Fiber summation at a complete assignment is the original ordered terminal projection. -/
theorem aggregate_terminal {r : I → ℝ} (p : Flow (X := X) r) (v : (i : I) → X i) :
    aggregateMass p (Fintype.card I) (complete v) = terminalProjection p v := by
  unfold aggregateMass terminalProjection
  rw [← Finset.sum_subtype (univ.filter (fun h : History X (Fintype.card I) => erase h = complete v))
    (by intro h; simp) (p.mass (Fintype.card I)),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  have he : erase h = complete v ↔ terminalAssignment h = v := by
    rw [erase_terminal]
    constructor
    · intro he
      funext i
      exact Option.some.inj (congrArg (fun a : Assignment X => a i) he)
    · rintro rfl; rfl
  simp only [he]

/-- Terminal probabilities are the occupancy masses at literal complete named assignments. -/
def occupancyTerminalLaw {r : I → ℝ} (o : OccupancyFlow (X := X) r) :
    ((i : I) → X i) → ℝ := fun v => o.mass (complete v)

local instance scheduleMeasurableSpace (k : ℕ) :
    MeasurableSpace (ScheduleTable (X := X) k) := ⊤
local instance resultMeasurableSpace (k : ℕ) :
    MeasurableSpace (ResultTable (X := X) k) := ⊤
local instance scheduleMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (ScheduleTable (X := X) k) := ⟨fun _ => trivial⟩
local instance resultMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (ResultTable (X := X) k) := ⟨fun _ => trivial⟩

/-- Actual erased-state events are the disjoint unions of their ordered-history fibers. -/
def stateNode {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) (k : ℕ) (a : Assignment X) :
    Set (Sample (X := X)) := ⋃ h : Fiber k a, (canonicalArchivePath p hr).nodeEvent k h.val
def stateSelect {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) (k : ℕ) (a : Assignment X)
    (i : Available a) : Set (Sample (X := X)) :=
  ⋃ h : Fiber k a, (canonicalArchivePath p hr).selectEvent h.val (fiberUnread h i)
def stateResult {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) (k : ℕ) (a : Assignment X)
    (i : Available a) (x : X i.val) : Set (Sample (X := X)) :=
  ⋃ h : Fiber k a, (canonicalArchivePath p hr).resultEvent h.val (fiberUnread h i) x

private theorem node_disjoint {r : I → ℝ} (p : Flow (X := X) r) hr k a :
    Pairwise (Disjoint on fun h : Fiber k a => (canonicalArchivePath p hr).nodeEvent k h.val) := by
  intro h g hne
  apply Set.disjoint_left.mpr
  rintro ω ⟨hk, hh⟩ ⟨hk', hg⟩
  exact hne (Subtype.ext (hh.symm.trans hg))
private theorem select_disjoint {r : I → ℝ} (p : Flow (X := X) r) hr k a (i : Available a) :
    Pairwise (Disjoint on fun h : Fiber k a =>
      (canonicalArchivePath p hr).selectEvent h.val (fiberUnread h i)) := by
  intro h g hne
  apply Set.disjoint_left.mpr
  intro ω hh hg
  exact hne (Subtype.ext (congrArg Sigma.fst (hh.symm.trans hg)))
private theorem result_disjoint {r : I → ℝ} (p : Flow (X := X) r) hr k a (i : Available a) (x : X i.val) :
    Pairwise (Disjoint on fun h : Fiber k a =>
      (canonicalArchivePath p hr).resultEvent h.val (fiberUnread h i) x) := by
  intro h g hne
  apply Set.disjoint_left.mpr
  intro ω hh hg
  exact hne (Subtype.ext (congrArg Sigma.fst (hh.symm.trans hg)))

private theorem indicator_union {T : Type*} [Fintype T] {Ω : Type*}
    (e : T → Set Ω) (hd : Pairwise (Disjoint on e)) (c : ℝ) :
    (⋃ t, e t).indicator (fun _ => c) = ∑ t, (e t).indicator (fun _ => c) := by
  funext ω
  simp only [Finset.sum_apply]
  by_cases he : ∃ t, ω ∈ e t
  · obtain ⟨t, ht⟩ := he
    rw [Set.indicator_of_mem (Set.mem_iUnion.mpr ⟨t, ht⟩)]
    rw [Finset.sum_eq_single t]
    · exact (Set.indicator_of_mem ht (fun _ => c)).symm
    · intro u hu hut
      exact Set.indicator_of_notMem (fun h => (Set.disjoint_left.mp (hd hut) h ht)) _
    · simp
  · have hn : ∀ t, ω ∉ e t := by simpa using he
    simp [Set.indicator_of_notMem, hn, show ω ∉ ⋃ t, e t by simpa using he]

/-- Literal erasure, named selection, and actual value characterize the three disjoint fiber events. -/
private theorem state_event_fibers {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k < Fintype.card I) (a : Assignment X) (i : Available a) (x : X i.val) :
    stateNode p hr k a = {ω | erase ((canonicalArchivePath p hr).history k (Nat.le_of_lt hk) ω) = a} ∧
    stateSelect p hr k a i = {ω |
      erase (forgetResult ((canonicalArchivePath p hr).step k hk ω)).1 = a ∧
      (forgetResult ((canonicalArchivePath p hr).step k hk ω)).2.val = i.val} ∧
    stateResult p hr k a i x = {ω |
      erase ((canonicalArchivePath p hr).step k hk ω).1 = a ∧
      ((canonicalArchivePath p hr).step k hk ω).2.1.val = i.val ∧
      HEq ((canonicalArchivePath p hr).step k hk ω).2.2 x} := by
  refine ⟨?_, ?_, ?_⟩
  · ext ω
    simp only [stateNode, Set.mem_iUnion, ArchivePath.nodeEvent, Set.mem_setOf_eq]
    change (∃ h : Fiber k a, ∃ hk', (canonicalArchivePath p hr).history k hk' ω = h.val) ↔ _
    constructor
    · rintro ⟨h, hk', hh⟩
      exact (congrArg erase hh).trans h.property
    · intro hh
      exact ⟨⟨_, hh⟩, Nat.le_of_lt hk, rfl⟩
  · ext ω
    simp only [stateSelect, Set.mem_iUnion, ArchivePath.selectEvent, Set.mem_setOf_eq]
    change (∃ h : Fiber k a,
      forgetResult ((canonicalArchivePath p hr).step k hk ω) = ⟨h.val, fiberUnread h i⟩) ↔ _
    constructor
    · rintro ⟨h, hh⟩
      rw [hh]
      exact ⟨h.property, rfl⟩
    · rintro ⟨hh, hi⟩
      let e := forgetResult ((canonicalArchivePath p hr).step k hk ω)
      refine ⟨⟨e.1, hh⟩, ?_⟩
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hi))
  · ext ω
    simp only [stateResult, Set.mem_iUnion, ArchivePath.resultEvent, Set.mem_setOf_eq]
    change (∃ h : Fiber k a,
      (canonicalArchivePath p hr).step k hk ω = ⟨h.val, fiberUnread h i, x⟩) ↔ _
    constructor
    · rintro ⟨h, hh⟩
      rw [hh]
      exact ⟨h.property, rfl, HEq.rfl⟩
    · rintro ⟨hh, hi, hx⟩
      let e := (canonicalArchivePath p hr).step k hk ω
      refine ⟨⟨e.1, hh⟩, ?_⟩
      have hj : e.2.1 = fiberUnread ⟨e.1, hh⟩ i := Subtype.ext hi
      exact Sigma.ext rfl (heq_of_eq (Sigma.ext hj hx))

/-- The probabilities of the three literal events are precisely the prescribed occupancy variables. -/
theorem state_event_masses {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    (∀ a, (innovationLaw (o.lift hr)).real (stateNode (o.lift hr) hr (rank a) a) = o.mass a) ∧
    (∀ a (ha : rank a < Fintype.card I) i,
      (innovationLaw (o.lift hr)).real (stateSelect (o.lift hr) hr (rank a) a i) = o.select a i) ∧
    (∀ a (ha : rank a < Fintype.card I) i x,
      (innovationLaw (o.lift hr)).real (stateResult (o.lift hr) hr (rank a) a i x) = o.result a i x) := by
  haveI := (table_trace_realization (o.lift hr) hr).1
  have hf := (realize_ordered_flow (o.lift hr) hr).2
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [stateNode, measureReal_iUnion_fintype (node_disjoint _ _ _ _)
      (fun _ => (Set.toFinite _).measurableSet)]
    change aggregateMass (canonicalArchivePath (o.lift hr) hr).toFlow (rank a) a = _
    rw [hf]; exact (lift_all_masses o hr).1 a
  · intro a ha i
    rw [stateSelect, measureReal_iUnion_fintype (select_disjoint _ _ _ _ _)
      (fun _ => (Set.toFinite _).measurableSet)]
    change aggregateSelect (canonicalArchivePath (o.lift hr) hr).toFlow (rank a) a i = _
    rw [hf]; exact (lift_all_masses o hr).2.1 a ha i
  · intro a ha i x
    rw [stateResult, measureReal_iUnion_fintype (result_disjoint _ _ _ _ _ _)
      (fun _ => (Set.toFinite _).measurableSet)]
    change aggregateResult (canonicalArchivePath (o.lift hr) hr).toFlow (rank a) a i x = _
    rw [hf]; exact (lift_all_masses o hr).2.2 a ha i x

private theorem canonical_select_fiber {r : I → ℝ} (p : Flow (X := X) r) hr
    (k : ℕ) (hk : k < Fintype.card I) (h : History X k) (i : Unread h) :
    (canonicalArchivePath p hr).selectEvent h i =
      {ω | interpret k (beforeTables k (Nat.le_of_lt hk) ω) = h ∧
        (currentBlock k hk ω).1 h = i} := by
  ext ω
  simp only [ArchivePath.selectEvent, canonicalArchivePath, selection_fiber,
    Equiv.symm_apply_eq, Set.mem_setOf_eq]
  have hp : Fin.snoc (beforeTables k (Nat.le_of_lt hk) ω) (currentBlock k hk ω) =
      beforeTables (k+1) (Nat.succ_le_of_lt hk) ω := by
    change Fin.snoc (Fin.init (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω))
      ((beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) (Fin.last k)) = _
    exact Fin.snoc_init_self _
  change (∃ x, interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) = append h i x) ↔ _
  rw [← hp]
  simp only [interpret_snoc_fiber]
  constructor
  · rintro ⟨x, hh, hi, hx⟩; exact ⟨hh, hi⟩
  · rintro ⟨hh, hi⟩; exact ⟨(currentBlock k hk ω).2 h i, hh, hi, rfl⟩

private theorem indicator_as_ite {Ω : Type*} (s : Set Ω) (c : ℝ) :
    s.indicator (fun _ => c) = fun ω => if ω ∈ s then c else 0 := by
  funext ω
  exact Set.indicator_apply s (fun _ => c) ω

/-- The complete pre-schedule archive has the prescribed ordered scheduler kernel. -/
private theorem conditional_selection_before {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k < Fintype.card I) (h : History X k) (i : Unread h) :
    (innovationLaw p)[((canonicalArchivePath p hr).selectEvent h i).indicator
      (fun _ => (1 : ℝ)) | (canonicalArchivePath p hr).F k] =ᵐ[innovationLaw p]
    ((canonicalArchivePath p hr).nodeEvent k h).indicator (fun _ => schedulerRow p h i) := by
  haveI := (table_trace_realization p hr).1
  let cut := beforeTables (X := X) k (Nat.le_of_lt hk)
  let g (w : TableTrace (X := X) k) : ℝ := if interpret k w = h then schedulerRow p h i else 0
  have hF : (canonicalArchivePath p hr).F k = MeasurableSpace.comap cut inferInstance := by
    simp only [canonicalArchivePath, dif_pos (Nat.le_of_lt hk)]; rfl
  have he : (canonicalArchivePath p hr).nodeEvent k h = {ω | interpret k (cut ω) = h} := by
    ext ω; simp [ArchivePath.nodeEvent, canonicalArchivePath, cut, Nat.le_of_lt hk]
  rw [hF, he, canonical_select_fiber p hr k hk h i]
  simp_rw [indicator_as_ite, Set.mem_setOf_eq]
  change (innovationLaw p)[(fun ω => if interpret k (cut ω) = h ∧
    (currentBlock k hk ω).1 h = i then (1 : ℝ) else 0) | _] =ᵐ[innovationLaw p] fun ω => g (cut ω)
  symm
  have hm := (measurable_of_finite cut).comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
  · intro s hs hsμ; exact Integrable.of_finite
  · intro s hs hsμ
    have hsm := hm s hs
    obtain ⟨S, hS, rfl⟩ := hs
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    simp only [Set.indicator, Set.mem_preimage]
    rw [next_block_integral p hr k hk (fun w _ _ => if w ∈ S then g w else 0),
      next_block_integral p hr k hk (fun w a _ => if w ∈ S then
        (if interpret k w = h ∧ a h = i then (1 : ℝ) else 0) else 0)]
    apply Finset.sum_congr rfl
    intro w hw
    congr 1
    have hb := (table_laws p hr hk).2.2
    have ha := (table_laws p hr hk).1.2
    by_cases hs : w ∈ S
    · by_cases hh : interpret k w = h
      · have marginal := product_row_marginal (fun h j => schedulerRow p h j)
          (fun h => (scheduler_law p hk h).2) h (fun j => if j = i then (1 : ℝ) else 0)
        have marginal' : (∑ a : ScheduleTable (X := X) k,
            scheduleDensity p k a * (if a h = i then (1 : ℝ) else 0)) = schedulerRow p h i := by
          simpa [scheduleDensity] using marginal
        simpa [hs, hh, g, ← Finset.sum_mul, hb, ha] using marginal'.symm
      · simp [hs, hh, g]
    · simp [hs]
  · exact (((measurable_of_finite g).comp (comap_measurable cut)).stronglyMeasurable).aestronglyMeasurable

/-- Weighted ordered rows agree with the global state rows without cancelling null masses. -/
private theorem lift_weighted_rows {r : I → ℝ} (o : OccupancyFlow (X := X) r) hr
    {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) :
    (o.lift hr).mass k h * schedulerRow (o.lift hr) h i =
      (o.lift hr).mass k h * o.sigma (erase h) (unreadEquiv h i) ∧
    (o.lift hr).select k h i * resultRow (o.lift hr) h i x =
      (o.lift hr).select k h i * o.q (erase h) (unreadEquiv h i) x := by
  constructor
  · by_cases hm : (o.lift hr).mass k h = 0
    · simp [hm]
    · simp only [schedulerRow, hm, if_false]
      rw [mul_div_cancel₀ _ hm]; rfl
  · by_cases hm : (o.lift hr).select k h i = 0
    · simp [hm]
    · simp only [resultRow, hm, if_false]
      rw [mul_div_cancel₀ _ hm]; rfl

private theorem null_row_replace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (s : Set Ω) (m u v : ℝ) (hm : μ.real s = m)
    (hw : m * u = m * v) : s.indicator (fun _ => u) =ᵐ[μ] s.indicator (fun _ => v) := by
  by_cases hz : m = 0
  · have hs : μ s = 0 := (measureReal_eq_zero_iff).mp (hm.trans hz)
    have hn : ∀ᵐ ω ∂μ, ω ∉ s := by simpa [ae_iff] using hs
    filter_upwards [hn] with ω hω
    simp [Set.indicator_of_notMem hω]
  · have huv : u = v := mul_left_cancel₀ hz hw
    rw [huv]

private theorem conditional_result_after {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k < Fintype.card I) (h : History X k) (i : Unread h) (x : X i.val) :
    (innovationLaw p)[((canonicalArchivePath p hr).resultEvent h i x).indicator
      (fun _ => (1 : ℝ)) | (canonicalArchivePath p hr).G k] =ᵐ[innovationLaw p]
    ((canonicalArchivePath p hr).selectEvent h i).indicator (fun _ => resultRow p h i x) := by
  have hg : (canonicalArchivePath p hr).G k = scheduleArchive k hk := by
    simp only [canonicalArchivePath, dif_pos hk]
  have he : (canonicalArchivePath p hr).resultEvent h i x =
      {ω | interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) = append h i x} := by
    ext ω
    simp only [ArchivePath.resultEvent, canonicalArchivePath, Equiv.symm_apply_eq]
    rfl
  rw [hg, he, canonical_select_fiber p hr k hk h i]
  simp_rw [indicator_as_ite, Set.mem_setOf_eq]
  exact conditional_child_given_schedule p hr k hk h i x

private theorem conditional_union {T : Type*} [Fintype T]
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (e f : T → Set Ω)
    (he : Pairwise (Disjoint on e)) (hf : Pairwise (Disjoint on f)) (c : ℝ)
    (hc : ∀ t, μ[(e t).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
      (f t).indicator (fun _ => c)) :
    μ[(⋃ t, e t).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
      (⋃ t, f t).indicator (fun _ => c) := by
  rw [indicator_union e he 1, indicator_union f hf c]
  refine (condExp_finsetSum (fun _ _ => Integrable.of_finite) m).trans ?_
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => hω t)

private theorem fiber_sigma {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    {k : ℕ} {a : Assignment X} (h : Fiber k a) (i : Available a) :
    o.sigma (erase h.val) (unreadEquiv h.val (fiberUnread h i)) = o.sigma a i := by
  rcases h with ⟨h, hh⟩
  subst a
  rfl
private theorem fiber_q {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    {k : ℕ} {a : Assignment X} (h : Fiber k a) (i : Available a) (x : X i.val) :
    o.q (erase h.val) (unreadEquiv h.val (fiberUnread h i)) x = o.q a i x := by
  rcases h with ⟨h, hh⟩
  subst a
  rfl

/-- On the fresh reverse archive, scheduling depends on the erased state under the full F archive. -/
theorem state_scheduler_kernel {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (a : Assignment X) (ha : rank a < Fintype.card I) (i : Available a) :
    (innovationLaw (o.lift hr))[(stateSelect (o.lift hr) hr (rank a) a i).indicator
      (fun _ => (1 : ℝ)) | (canonicalArchivePath (o.lift hr) hr).F (rank a)] =ᵐ[innovationLaw (o.lift hr)]
    (stateNode (o.lift hr) hr (rank a) a).indicator (fun _ => o.sigma a i) := by
  haveI := (table_trace_realization (o.lift hr) hr).1
  apply conditional_union _ _ _ _ (select_disjoint _ _ _ _ _) (node_disjoint _ _ _ _) (o.sigma a i)
  intro h
  refine (conditional_selection_before (o.lift hr) hr _ ha h.val (fiberUnread h i)).trans ?_
  have hf := (realize_ordered_flow (o.lift hr) hr).2
  have hm : (innovationLaw (o.lift hr)).real ((canonicalArchivePath (o.lift hr) hr).nodeEvent (rank a) h.val) =
      (o.lift hr).mass (rank a) h.val := congrArg (fun p => p.mass (rank a) h.val) hf
  have hw := (lift_weighted_rows o hr h.val (fiberUnread h i)
    (Classical.choice (inferInstance : Nonempty (X i.val)))).1
  have hs := fiber_sigma o h i
  rw [hs] at hw
  exact null_row_replace _ _ _ _ _ hm hw

/-- On the same archive, the state result row is valid after the full scheduler disclosure G. -/
theorem state_result_kernel {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (a : Assignment X) (ha : rank a < Fintype.card I) (i : Available a) (x : X i.val) :
    (innovationLaw (o.lift hr))[(stateResult (o.lift hr) hr (rank a) a i x).indicator
      (fun _ => (1 : ℝ)) | (canonicalArchivePath (o.lift hr) hr).G (rank a)] =ᵐ[innovationLaw (o.lift hr)]
    (stateSelect (o.lift hr) hr (rank a) a i).indicator (fun _ => o.q a i x) := by
  haveI := (table_trace_realization (o.lift hr) hr).1
  apply conditional_union _ _ _ _ (result_disjoint _ _ _ _ _ _) (select_disjoint _ _ _ _ _) (o.q a i x)
  intro h
  refine (conditional_result_after (o.lift hr) hr _ ha h.val (fiberUnread h i) x).trans ?_
  have hf := (realize_ordered_flow (o.lift hr) hr).2
  have hm : (innovationLaw (o.lift hr)).real ((canonicalArchivePath (o.lift hr) hr).selectEvent h.val (fiberUnread h i)) =
      (o.lift hr).select (rank a) h.val (fiberUnread h i) :=
    congrArg (fun p => p.select (rank a) h.val (fiberUnread h i)) hf
  have hw := (lift_weighted_rows o hr h.val (fiberUnread h i) x).2
  have hq := fiber_q o h i x
  rw [hq] at hw
  exact null_row_replace _ _ _ _ _ hm hw

/-- Fresh ordered innovations realize every occupancy mass and its entire terminal joint law. -/
theorem realize_occupancy_flow {r : I → ℝ} (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    IsProbabilityMeasure (innovationLaw (o.lift hr)) ∧
    (letI := (table_trace_realization (o.lift hr) hr).1
     aggregate (canonicalArchivePath (o.lift hr) hr).toFlow = o ∧
     (canonicalArchivePath (o.lift hr) hr).terminalLaw = occupancyTerminalLaw o) := by
  haveI := (table_trace_realization (o.lift hr) hr).1
  obtain ⟨hμ,hf⟩ := realize_ordered_flow (o.lift hr) hr
  refine ⟨hμ,?_,?_⟩
  · rw [hf]; exact aggregate_lift o hr
  · rw [← (canonicalArchivePath (o.lift hr) hr).terminalLaw_projection,hf]
    funext v
    rw [← aggregate_terminal,← complete_rank v]
    exact (lift_all_masses o hr).1 (complete v)

/-- Full state-policy realization on the same fresh archive, with individual event masses and both full-archive kernels. -/
theorem realize_occupancy_state_strategy [Nonempty I] {r : I → ℝ}
    (o : OccupancyFlow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i ∧ r i ≤ 1) :
    let lower : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i := fun i => (hr i).1
    IsProbabilityMeasure (innovationLaw (o.lift lower)) ∧
    (letI := (table_trace_realization (o.lift lower) lower).1
     aggregate (canonicalArchivePath (o.lift lower) lower).toFlow = o ∧
     (canonicalArchivePath (o.lift lower) lower).terminalLaw = occupancyTerminalLaw o ∧
     (∀ a, (innovationLaw (o.lift lower)).real (stateNode (o.lift lower) lower (rank a) a) = o.mass a) ∧
     (∀ a (ha : rank a < Fintype.card I) i,
       (innovationLaw (o.lift lower)).real (stateSelect (o.lift lower) lower (rank a) a i) = o.select a i) ∧
     (∀ a (ha : rank a < Fintype.card I) i x,
       (innovationLaw (o.lift lower)).real (stateResult (o.lift lower) lower (rank a) a i x) = o.result a i x) ∧
     (∀ a (ha : rank a < Fintype.card I) i,
       (innovationLaw (o.lift lower))[(stateSelect (o.lift lower) lower (rank a) a i).indicator
         (fun _ => (1 : ℝ)) | (canonicalArchivePath (o.lift lower) lower).F (rank a)] =ᵐ[innovationLaw (o.lift lower)]
       fun ω => (stateNode (o.lift lower) lower (rank a) a).indicator (fun _ => (1 : ℝ)) ω * o.sigma a i) ∧
     (∀ a (ha : rank a < Fintype.card I) i x,
       (innovationLaw (o.lift lower))[(stateResult (o.lift lower) lower (rank a) a i x).indicator
         (fun _ => (1 : ℝ)) | (canonicalArchivePath (o.lift lower) lower).G (rank a)] =ᵐ[innovationLaw (o.lift lower)]
       fun ω => (stateSelect (o.lift lower) lower (rank a) a i).indicator (fun _ => (1 : ℝ)) ω * o.q a i x) ∧
     (∀ a (ha : rank a < Fintype.card I) i x,
       stateNode (o.lift lower) lower (rank a) a =
         {ω | erase ((canonicalArchivePath (o.lift lower) lower).history (rank a) (Nat.le_of_lt ha) ω) = a} ∧
       stateSelect (o.lift lower) lower (rank a) a i = {ω |
         erase (forgetResult ((canonicalArchivePath (o.lift lower) lower).step (rank a) ha ω)).1 = a ∧
         (forgetResult ((canonicalArchivePath (o.lift lower) lower).step (rank a) ha ω)).2.val = i.val} ∧
       stateResult (o.lift lower) lower (rank a) a i x = {ω |
         erase ((canonicalArchivePath (o.lift lower) lower).step (rank a) ha ω).1 = a ∧
         ((canonicalArchivePath (o.lift lower) lower).step (rank a) ha ω).2.1.val = i.val ∧
         HEq ((canonicalArchivePath (o.lift lower) lower).step (rank a) ha ω).2.2 x})) := by
  dsimp only
  let lower : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i := fun i => (hr i).1
  have core := realize_occupancy_flow o lower
  have masses := state_event_masses o lower
  refine ⟨core.1, core.2.1, core.2.2, masses.1, masses.2.1, masses.2.2, ?_, ?_, ?_⟩
  · intro a ha i
    simpa only [indicator_as_ite, ite_mul, one_mul, zero_mul] using state_scheduler_kernel o lower a ha i
  · intro a ha i x
    simpa only [indicator_as_ite, ite_mul, one_mul, zero_mul] using state_result_kernel o lower a ha i x
  · intro a ha i x
    exact state_event_fibers (o.lift lower) lower (rank a) ha a i x

/-- Complete theorem 4.9 at the terminal-law level, including arbitrary original archives. -/
theorem occupancy_terminal_law_range [Nonempty I] {r : I → ℝ}
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i ∧ r i ≤ 1)
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Set.range (occupancyTerminalLaw (X := X) (r := r)) = archiveTerminalLaws (X := X) r ∧
    ∀ A : ArchivePath (X := X) r μ,
      occupancyTerminalLaw (aggregate A.toFlow) = A.terminalLaw := by
  have lower : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i := fun i => (hr i).1
  constructor
  · rw [← (ordered_terminal_law_range lower μ).1]
    ext law
    constructor
    · rintro ⟨o,rfl⟩
      refine ⟨o.lift lower,?_⟩
      haveI := (table_trace_realization (o.lift lower) lower).1
      have ht := (realize_occupancy_state_strategy o hr).2.2.1
      rw [← (canonicalArchivePath (o.lift lower) lower).terminalLaw_projection,
        (realize_ordered_flow (o.lift lower) lower).2] at ht
      exact ht
    · rintro ⟨p,rfl⟩
      refine ⟨aggregate p,?_⟩
      funext v
      change aggregateMass p (rank (complete v)) (complete v) = terminalProjection p v
      rw [complete_rank,aggregate_terminal]
  · intro A
    rw [← A.terminalLaw_projection]
    funext v
    change aggregateMass A.toFlow (rank (complete v)) (complete v) = terminalProjection A.toFlow v
    rw [complete_rank,aggregate_terminal]

#print axioms incomingAppend_bijective
#print axioms aggregate_incoming
#print axioms lift_all_masses
#print axioms aggregate_lift
#print axioms state_event_masses
#print axioms state_scheduler_kernel
#print axioms state_result_kernel
#print axioms realize_occupancy_state_strategy
#print axioms realize_occupancy_flow
#print axioms occupancy_terminal_law_range
end D5.S3.Estimation.DataProcessing.PartialAssignmentOccupancyFlow
