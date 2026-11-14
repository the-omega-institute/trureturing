/- GID: D5/S3/Quantum/Routing/HannRouterProfiles
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannRouterProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal internal router localization and active-profile separation. -/

import D5.S3.Quantum.Routing.HannSpatialQram
import D5.S3.Quantum.Routing.HannRouterDephasing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Order
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-! Observations of loaded internal routers and their active address profiles. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace D5.S3.Quantum.Routing.HannRouterProfiles

open HannSpatialQram
open ReversibleQram (Address)

/-- Exactly the internal routers: a root or a router in one of its two children. -/
abbrev Router : ℕ → Type
  | 0 => Empty
  | n + 1 => Option (Bool × Router n)

/-- Read the literal router field, never an incident or output rail. -/
def routerLabel : (n : ℕ) → Tree n → Router n → Qutrit
  | 0, _, v => nomatch v
  | _ + 1, t, none => t.2.1
  | n + 1, t, some (b, v) => routerLabel n (if b then t.2.2.2 else t.2.2.1) v

/-- Append the final bit while preserving the circuit's head-first address order. -/
def snoc : (n : ℕ) → Address n → Bool → Address (n + 1)
  | 0, _, b => (b, ())
  | n + 1, a, b => (a.1, snoc n a.2 b)

/-- The depth-n router reached by a length-n prefix in a tree of depth n+1. -/
def deepest : (n : ℕ) → Address n → Router (n + 1)
  | 0, _ => none
  | n + 1, a => some (a.1, deepest n a.2)

/-- Router labels after the actual sequential load, with any external qutrit bus. -/
def loadedLabel (n : ℕ) (a : Address n) (bus : Qutrit) (v : Router n) : Qutrit :=
  routerLabel n ((load n n) (loading n a bus 0)).2.2 v

private theorem loaded_label (n : ℕ) (a : Address n) (bus : Qutrit) (v : Router n) :
    loadedLabel n a bus v = routerLabel n (programmed n a n) v := by
  unfold loadedLabel
  rw [correctness.1 n a bus n (le_refl n)]
  rfl

private theorem vacuum_label (n : ℕ) (v : Router n) :
    routerLabel n (vacuum n) v = Qutrit.wait := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
      cases v with
      | none => rfl
      | some v => rcases v with ⟨b, v⟩; cases b <;> exact ih v

private theorem deepest_label (n : ℕ) (u i : Address n) (b : Bool) :
    routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1)) (deepest n i) =
      if i = u then encode b else Qutrit.wait := by
  induction n with
  | zero => cases u; cases i; simp [routerLabel, programmed, snoc, deepest]
  | succ n ih =>
      rcases u with ⟨c, u⟩
      rcases i with ⟨d, i⟩
      cases c <;> cases d
      · change routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1))
          (deepest n i) = if (false, i) = (false, u) then encode b else Qutrit.wait
        simpa only [Prod.mk.injEq, eq_self, true_and] using ih u i
      · simp [snoc, deepest, programmed, routerLabel, vacuum_label]
      · simp [snoc, deepest, programmed, routerLabel, vacuum_label]
      · change routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1))
          (deepest n i) = if (true, i) = (true, u) then encode b else Qutrit.wait
        simpa only [Prod.mk.injEq, eq_self, true_and] using ih u i

private theorem sibling_labels (n : ℕ) (u : Address n) (v : Router (n + 1))
    (hv : v ≠ deepest n u) :
    routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
      routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v := by
  induction n with
  | zero => cases v with
      | none => exact (hv rfl).elim
      | some v => exact v.2.elim
  | succ n ih =>
      rcases u with ⟨b, u⟩
      cases v with
      | none => rfl
      | some v =>
          rcases v with ⟨c, v⟩
          cases b <;> cases c
          · change routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
              routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v
            exact ih u v (by simpa [deepest] using hv)
          · simp [snoc, routerLabel, programmed]
          · simp [snoc, routerLabel, programmed]
          · change routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
              routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v
            exact ih u v (by simpa [deepest] using hv)

private theorem snoc_surjective (n : ℕ) (a : Address (n + 1)) :
    ∃ u b, a = snoc n u b := by
  induction n with
  | zero => exact ⟨(), a.1, by cases a with | mk b a => cases a; rfl⟩
  | succ n ih =>
      obtain ⟨u, b, h⟩ := ih a.2
      exact ⟨(a.1, u), b, by cases a; simp_all [snoc]⟩

private theorem snoc_ne (n : ℕ) (u : Address n) : snoc n u false ≠ snoc n u true := by
  induction n with
  | zero => simp [snoc]
  | succ n ih => simpa [snoc] using ih u.2

private theorem encode_injective : Function.Injective encode := by
  intro b c h
  cases b <;> cases c <;> simp_all [encode]

private theorem encode_ne_wait (b : Bool) : encode b ≠ Qutrit.wait := by
  cases b <;> simp [encode]

/-- Two addresses have the same active profile exactly when all observable loaded routers agree.
The two buses may differ; no bus coordinate is observed. -/
def SameProfile (n : ℕ) (q : Router n → ℝ) (a a' : Address n)
    (bus bus' : Qutrit) : Prop :=
  ∀ v, q v < 1 → loadedLabel n a bus v = loadedLabel n a' bus' v

/-- The active physical router profile distinguishes every address. -/
def Separates (n : ℕ) (q : Router n → ℝ) : Prop :=
  ∀ a a' bus bus', SameProfile n q a a' bus bus' → a = a'

/-- Exact all-depth physical separation criterion, including arbitrary independent endpoint rates.
No interval restriction is needed for the stronger combinatorial statement. -/
theorem profile_separation_iff (n : ℕ) (q : Router (n + 1) → ℝ) :
    (∀ (a a' : Address (n + 1)) (bus bus' : Qutrit),
      (∀ v, q v < 1 → loadedLabel (n + 1) a bus v = loadedLabel (n + 1) a' bus' v) →
        a = a') ↔ ∀ u : Address n, q (deepest n u) < 1 := by
  change Separates (n + 1) q ↔ _
  constructor
  · intro h u
    by_contra hq
    apply snoc_ne n u
    apply h (snoc n u false) (snoc n u true) Qutrit.wait Qutrit.wait
    intro v hv
    rw [loaded_label, loaded_label]
    apply sibling_labels
    intro heq
    exact hq (heq ▸ hv)
  · intro hq a a' bus bus' h
    obtain ⟨u, b, rfl⟩ := snoc_surjective n a
    obtain ⟨u', b', rfl⟩ := snoc_surjective n a'
    have he := h (deepest n u) (hq u)
    rw [loaded_label, loaded_label, deepest_label, deepest_label] at he
    have huu : u = u' := by
      by_contra hu
      simp only [ite_true, ite_eq_right hu] at he
      exact encode_ne_wait b he
    subst u'
    simp only [ite_true] at he
    have hb : b = b' := encode_injective he
    subst b'
    rfl

instance routerFintype : (n : ℕ) → Fintype (Router n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => letI := routerFintype n
             inferInstanceAs (Fintype (Option (Bool × Router n)))

/-- One independent common/W/0/1 environment coordinate at each actual router. -/
abbrev Environment (n : ℕ) := Router n → Option Qutrit

instance environmentFintype (n : ℕ) : Fintype (Environment n) := by
  classical
  unfold Environment
  infer_instance

/-- The physical tensor record for an arbitrary spatial tree. -/
def treeRecord (n : ℕ) (q : Router n → ℝ) (t : Tree n) (e : Environment n) : ℂ :=
  ∏ v, HannRouterDephasing.localRecord (q v) (routerLabel n t v) (e v)

/-- The record of the actual completely loaded tree; the bus is unobserved. -/
def record (n : ℕ) (q : Router n → ℝ) (a : Address n) (e : Environment n) : ℂ :=
  ∏ v, HannRouterDephasing.localRecord (q v) (loadedLabel n a Qutrit.wait v) (e v)

/-- Realized active profiles, so no unrealized label assignment is counted. -/
def Profile (n : ℕ) (q : Router n → ℝ) : Type :=
  ↥(Set.range (fun a : Address n => fun v : {v : Router n // q v < 1} =>
    loadedLabel n a Qutrit.wait v.1))

instance profileFintype (n : ℕ) (q : Router n → ℝ) : Fintype (Profile n q) := by
  classical
  unfold Profile
  infer_instance

instance profileDecidableEq (n : ℕ) (q : Router n → ℝ) : DecidableEq (Profile n q) :=
  Classical.decEq _

/-- The surjective physical class map. -/
def profile (n : ℕ) (q : Router n → ℝ) (a : Address n) : Profile n q :=
  ⟨fun v => loadedLabel n a Qutrit.wait v.1, a, rfl⟩

private theorem profile_surjective (n : ℕ) (q : Router n → ℝ) :
    Function.Surjective (profile n q) := by
  rintro ⟨c, a, rfl⟩
  exact ⟨a, rfl⟩

private theorem profile_eq_iff (n : ℕ) (q : Router n → ℝ)
    (a b : Address n) (bus bus' : Qutrit) :
    profile n q a = profile n q b ↔ SameProfile n q a b bus bus' := by
  constructor
  · intro h v hv
    have he := congrFun (congrArg Subtype.val h) ⟨v, hv⟩
    simpa only [profile, loaded_label] using he
  · intro h
    apply Subtype.ext
    funext v
    simpa only [profile, loaded_label] using h v.1 v.2

private theorem record_loaded (n : ℕ) (q : Router n → ℝ) (a : Address n)
    (bus : Qutrit) :
    treeRecord n q ((load n n) (loading n a bus 0)).2.2 = record n q a := by
  funext e
  apply Finset.prod_congr rfl
  intro v _
  change HannRouterDephasing.localRecord (q v) (loadedLabel n a bus v) (e v) = _
  rw [loaded_label, loaded_label]

private theorem record_conj (n : ℕ) (q : Router n → ℝ) (a : Address n)
    (e : Environment n) : conj (record n q a e) = record n q a e := by
  classical
  simp only [record, map_prod]
  apply Finset.prod_congr rfl
  intro v _
  cases e v with
  | none => simp [HannRouterDephasing.localRecord]
  | some s =>
      by_cases h : s = loadedLabel n a Qutrit.wait v <;>
        simp [HannRouterDephasing.localRecord, h]

private theorem record_profile (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (a b : Address n) (h : profile n q a = profile n q b) :
    record n q a = record n q b := by
  classical
  funext e
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : q v < 1
  · rw [(profile_eq_iff n q a b _ _).mp h v hv]
  · have he : q v = 1 := le_antisymm (hq v) (le_of_not_gt hv)
    cases e v <;> simp [HannRouterDephasing.localRecord, he]

/-- The record of a realized class, independent of the selected representative. -/
def classRecord (n : ℕ) (q : Router n → ℝ) (c : Profile n q) : Environment n → ℂ :=
  record n q (Classical.choose c.2)

private theorem representative_profile (n : ℕ) (q : Router n → ℝ) (c : Profile n q) :
    profile n q (Classical.choose c.2) = c := by
  apply Subtype.ext
  exact Classical.choose_spec c.2

private theorem class_record_profile (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) (a : Address n) :
    classRecord n q (profile n q a) = record n q a := by
  apply record_profile n q hq
  exact representative_profile n q _

private def sample (n : ℕ) (q : Router n → ℝ) (c : Profile n q) : Environment n := by
  classical
  exact fun v => if hv : q v < 1 then some (c.1 ⟨v, hv⟩) else none

private def diagonal (n : ℕ) (q : Router n → ℝ) : ℂ := by
  classical
  exact ∏ v, if q v < 1 then (Real.sqrt (1 - q v) : ℂ) else 1

private theorem diagonal_ne_zero (n : ℕ) (q : Router n → ℝ) : diagonal n q ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  split_ifs with h
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (sub_pos.2 h)))
  · exact one_ne_zero

private theorem record_sample (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (a : Address n) (c : Profile n q) :
    record n q a (sample n q c) = if profile n q a = c then diagonal n q else 0 := by
  classical
  by_cases h : profile n q a = c
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : q v < 1
    · have he := congrFun (congrArg Subtype.val h) ⟨v, hv⟩
      simp only [profile] at he
      simp [sample, hv, HannRouterDephasing.localRecord, he, diagonal]
    · have he : q v = 1 := le_antisymm (hq v) (le_of_not_gt hv)
      simp [sample, hv, HannRouterDephasing.localRecord, he]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ : ∃ v, loadedLabel n a Qutrit.wait v.1 ≠ c.1 v := by
      by_contra hn
      apply h
      apply Subtype.ext
      funext v
      exact not_ne_iff.mp (not_exists.mp hn v)
    apply Finset.prod_eq_zero (Finset.mem_univ v.1)
    simp [sample, v.2, HannRouterDephasing.localRecord, Ne.symm hv]

private theorem class_record_sample (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (c d : Profile n q) :
    classRecord n q c (sample n q d) = if c = d then diagonal n q else 0 := by
  simpa only [classRecord, representative_profile] using
    record_sample n q hq (Classical.choose c.2) d

private theorem class_records_independent (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) : LinearIndependent ℂ (classRecord n q) := by
  classical
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro x y h
  funext c
  have he := congrFun h (sample n q c)
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, class_record_sample n q hq] at he
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  exact mul_right_cancel₀ (diagonal_ne_zero n q) he

/-- Physical complex Gram, with the density-matrix convention of the event. -/
def gram (n : ℕ) (q : Router n → ℝ) : Matrix (Address n) (Address n) ℂ :=
  fun a b => ∑ e, record n q a e * conj (record n q b e)

private def recordMatrix (n : ℕ) (q : Router n → ℝ) :
    Matrix (Environment n) (Address n) ℂ := fun e a => record n q a e

private theorem gram_factor (n : ℕ) (q : Router n → ℝ) :
    gram n q = (recordMatrix n q)ᴴ * recordMatrix n q := by
  ext a b
  change (∑ e, record n q a e * conj (record n q b e)) =
    ∑ e, conj (record n q a e) * record n q b e
  simp only [record_conj]

private theorem record_rank (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1) :
    (recordMatrix n q).rank = Fintype.card (Profile n q) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hr : Set.range (recordMatrix n q).col = Set.range (classRecord n q) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨profile n q a, class_record_profile n q hq a⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Classical.choose c.2, rfl⟩
  rw [hr]
  exact (linearIndependent_iff_card_eq_finrank_span.mp
    (class_records_independent n q hq)).symm

/-- Coefficients pushed forward to their actual profile classes. -/
def classSum {R : Type} [AddCommMonoid R] (n : ℕ) (q : Router n → ℝ)
    (x : Address n → R) (c : Profile n q) : R := by
  classical
  exact ∑ a, if profile n q a = c then x a else 0

private theorem record_combination (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) (x : Address n → ℂ) (e : Environment n) :
    (∑ a, x a * record n q a e) =
      ∑ c, classSum n q x c * classRecord n q c e := by
  classical
  simp only [classSum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [class_record_profile n q hq]

private theorem record_kernel (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (x : Address n → ℂ) :
    (recordMatrix n q).mulVec x = 0 ↔ ∀ c, classSum n q x c = 0 := by
  classical
  constructor
  · intro h c
    have he := congrFun h (sample n q c)
    change (∑ a, record n q a (sample n q c) * x a) = 0 at he
    simp only [record_sample n q hq, ite_mul, zero_mul] at he
    have he' : diagonal n q * classSum n q x c = 0 := by
      simpa only [classSum, Finset.mul_sum, mul_ite, mul_zero] using he
    exact (mul_eq_zero.mp he').resolve_left (diagonal_ne_zero n q)
  · intro h
    funext e
    change (∑ a, record n q a e * x a) = 0
    simp_rw [mul_comm (record n q _ e)]
    rw [record_combination n q hq]
    simp [h]

private theorem gram_kernel (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (x : Address n → ℂ) :
    (gram n q).mulVec x = 0 ↔ ∀ c, classSum n q x c = 0 := by
  rw [gram_factor]
  have hk := Matrix.ker_mulVecLin_conjTranspose_mul_self (recordMatrix n q)
  have he : ((recordMatrix n q)ᴴ * recordMatrix n q).mulVec x = 0 ↔
      (recordMatrix n q).mulVec x = 0 := by
    change x ∈ LinearMap.ker ((recordMatrix n q)ᴴ * recordMatrix n q).mulVecLin ↔
      x ∈ LinearMap.ker (recordMatrix n q).mulVecLin
    rw [hk]
  exact he.trans (record_kernel n q hq x)

private theorem gram_rank (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1) :
    (gram n q).rank = Fintype.card (Profile n q) := by
  rw [gram_factor, Matrix.rank_conjTranspose_mul_self, record_rank n q hq]

private theorem address_card (n : ℕ) : Fintype.card (Address n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Address, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

private theorem full_rank_iff (n : ℕ) (q : Router (n + 1) → ℝ)
    (hq : ∀ v, q v ≤ 1) :
    (gram (n + 1) q).rank = 2 ^ (n + 1) ↔ ∀ u, q (deepest n u) < 1 := by
  rw [gram_rank (n + 1) q hq, ← address_card]
  have hc : Fintype.card (Profile (n + 1) q) = Fintype.card (Address (n + 1)) ↔
      Function.Injective (profile (n + 1) q) := by
    constructor
    · intro h
      exact ((Fintype.bijective_iff_surjective_and_card _).2
        ⟨profile_surjective _ q, h.symm⟩).1
    · intro h
      exact (Fintype.card_of_bijective ⟨h, profile_surjective _ q⟩).symm
  rw [hc, ← profile_separation_iff]
  constructor
  · intro h a b bus bus' hab
    exact h ((profile_eq_iff _ q a b bus bus').mpr hab)
  · intro h a b hab
    exact h a b Qutrit.wait Qutrit.wait
      ((profile_eq_iff _ q a b _ _).mp hab)

private theorem zero_rank (q : Router 0 → ℝ) : (gram 0 q).rank = 1 := by
  have he : gram 0 q = (1 : Matrix (Address 0) (Address 0) ℂ) := by
    ext a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simp [gram, record, Router]
  rw [he, Matrix.rank_one]
  rfl

#print axioms gram_rank
#print axioms gram_kernel
#print axioms full_rank_iff
#print axioms zero_rank

#print axioms profile_separation_iff

end D5.S3.Quantum.Routing.HannRouterProfiles
