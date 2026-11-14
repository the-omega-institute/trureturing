/- GID: D5/S3/Quantum/Routing/HannRouterProfiles
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannRouterProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Heterogeneous physical router profiles, complex Gram kernel and all fidelity minimizers. -/

import D5.S3.Quantum.Routing.HannSpatialQram
import D5.S3.Quantum.Routing.HannRouterDephasing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Order
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-! Independent records of actual loaded routers, profile rank and complete minimizer fibers. -/

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
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : q v < 1
    · have he := congrFun (congrArg Subtype.val h) ⟨v, hv⟩
      simp only [profile] at he
      simp [sample, hv, HannRouterDephasing.localRecord, he]
    · have he : q v = 1 := le_antisymm (hq v) (le_of_not_gt hv)
      simp [sample, HannRouterDephasing.localRecord, he]
  · rw [ite_eq_right h]
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

private theorem full_rank_iff (n : ℕ) (q : Router (n + 1) → ℝ)
    (hq : ∀ v, q v ≤ 1) :
    (gram (n + 1) q).rank = 2 ^ (n + 1) ↔ ∀ u, q (deepest n u) < 1 := by
  rw [gram_rank (n + 1) q hq, ← HannRouterDephasing.address_card]
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

/-- The physical address quadratic form, on arbitrary real coefficients. -/
def addressEnergy (n : ℕ) (q : Router n → ℝ) (p : Address n → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * p b * (gram n q a b).re

private def classAmplitude (n : ℕ) (q : Router n → ℝ)
    (x : Profile n q → ℝ) (e : Environment n) : ℂ :=
  ∑ c, (x c : ℂ) * classRecord n q c e

/-- The class quadratic form is the squared norm of the physical record superposition. -/
def classEnergy (n : ℕ) (q : Router n → ℝ) (x : Profile n q → ℝ) : ℝ :=
  ∑ e, Complex.normSq (classAmplitude n q x e)

private theorem class_energy_pos (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) (x : Profile n q → ℝ) (hx : x ≠ 0) :
    0 < classEnergy n q x := by
  classical
  by_contra hn
  have hz : classEnergy n q x = 0 := le_antisymm (le_of_not_gt hn)
    (Finset.sum_nonneg (fun e _ => Complex.normSq_nonneg _))
  have he : classAmplitude n q x = 0 := by
    funext e
    apply Complex.normSq_eq_zero.mp
    apply le_antisymm _ (Complex.normSq_nonneg _)
    exact (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg
      (classAmplitude n q x i)) (Finset.mem_univ e)).trans_eq hz
  have hi := (class_records_independent n q hq).fintypeLinearCombination_injective
  have hcomplex : Fintype.linearCombination ℂ (classRecord n q) (fun c => (x c : ℂ)) =
      Fintype.linearCombination ℂ (classRecord n q) 0 := by
    ext e
    simpa only [classAmplitude, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
      using congrFun he e
  apply hx
  funext c
  have hh : (x c : ℂ) = 0 := congrFun (hi hcomplex) c
  exact Complex.ofReal_eq_zero.mp hh

private theorem class_energy_midpoint (n : ℕ) (q : Router n → ℝ)
    (x y : Profile n q → ℝ) :
    classEnergy n q (fun c => (x c + y c) / 2) =
      (classEnergy n q x + classEnergy n q y) / 2 - classEnergy n q (x - y) / 4 := by
  have ha (e : Environment n) :
      classAmplitude n q (fun c => (x c + y c) / 2) e =
        (classAmplitude n q x e + classAmplitude n q y e) / 2 := by
    simp only [classAmplitude, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
      add_div, div_mul_eq_mul_div, add_mul, Finset.sum_add_distrib, Finset.sum_div]
  have hb (e : Environment n) : classAmplitude n q (x - y) e =
      classAmplitude n q x e - classAmplitude n q y e := by
    simp [classAmplitude, sub_mul, Finset.sum_sub_distrib]
  have hm (z w : ℂ) : Complex.normSq ((z + w) / 2) =
      (Complex.normSq z + Complex.normSq w) / 2 - Complex.normSq (z - w) / 4 := by
    rw [Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub]
    norm_num
    ring
  simp only [classEnergy, ha, hb, hm, Finset.sum_sub_distrib]
  simp only [← Finset.sum_div, Finset.sum_add_distrib]

/-- Bundled probability masses on the realized profile classes. -/
abbrev ClassDistribution (n : ℕ) (q : Router n → ℝ) :=
  Convexity.StdSimplex ℝ (Profile n q)

/-- Bundled arbitrary address probability distributions. -/
abbrev AddressDistribution (n : ℕ) := Convexity.StdSimplex ℝ (Address n)

/-- Physical class masses, including all boundary distributions. -/
def classMass (n : ℕ) (q : Router n → ℝ) (p : AddressDistribution n) :
    ClassDistribution n q := p.map (profile n q)

private theorem class_mass_weights (n : ℕ) (q : Router n → ℝ)
    (p : AddressDistribution n) (c : Profile n q) :
    (classMass n q p).weights c = classSum n q p.weights c := by
  classical
  change p.weights.mapDomain (profile n q) c = _
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.single_apply, classSum]

private theorem class_mass_surjective (n : ℕ) (q : Router n → ℝ) :
    Function.Surjective (classMass n q) := by
  intro x
  apply (Convexity.StdSimplex.mem_range_map_iff (profile n q) x).mpr
  intro c hc
  exact (hc (profile_surjective n q c)).elim

private theorem gram_real (n : ℕ) (q : Router n → ℝ) (a b : Address n) :
    ((gram n q a b).re : ℂ) = gram n q a b := by
  apply Complex.conj_eq_iff_re.mp
  simp only [gram, map_sum, map_mul, record_conj]

private theorem energy_factor (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1)
    (p : Address n → ℝ) :
    addressEnergy n q p = classEnergy n q (classSum n q p) := by
  classical
  have hsum (e : Environment n) :
      classAmplitude n q (classSum n q p) e = ∑ a, (p a : ℂ) * record n q a e := by
    rw [record_combination n q hq]
    unfold classAmplitude
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    simp [classSum, Complex.ofReal_sum, apply_ite]
  apply Complex.ofReal_injective
  simp only [addressEnergy, classEnergy, hsum, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [gram_real]
  simp only [Complex.normSq_eq_conj_mul_self, map_sum, map_mul,
    Complex.conj_ofReal, record_conj, gram, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem distribution_energy (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) (p : AddressDistribution n) :
    addressEnergy n q p.weights = classEnergy n q (classMass n q p).weights := by
  rw [energy_factor n q hq]
  congr 1
  funext c
  exact (class_mass_weights n q p c).symm

private theorem class_minimizer_unique (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, q v ≤ 1) :
    ∃! x : ClassDistribution n q, ∀ y : ClassDistribution n q,
      classEnergy n q x.weights ≤ classEnergy n q y.weights := by
  classical
  have hne : Nonempty (ClassDistribution n q) := by
    have ha : Nonempty (Address n) := by
      clear q hq
      induction n with
      | zero => exact ⟨()⟩
      | succ n ih => exact ⟨(false, Classical.choice ih)⟩
    exact ⟨.single (profile n q (Classical.choice ha))⟩
  have hc : Continuous (fun x : ClassDistribution n q => classEnergy n q x.weights) := by
    unfold classEnergy classAmplitude
    fun_prop
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (ClassDistribution n q)).Nonempty) hc.continuousOn
  refine ⟨x, fun y => hx (Set.mem_univ y), ?_⟩
  intro y hy
  by_contra hne
  have hw : (fun c => y.weights c - x.weights c) ≠ 0 := by
    intro he
    apply hne
    ext c
    exact sub_eq_zero.mp (congrFun he c)
  let m : ClassDistribution n q := Convexity.convexCombPair (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) y x
  have hm : (m.weights : Profile n q → ℝ) = fun c => (y.weights c + x.weights c) / 2 := by
    funext c
    simp only [m, Convexity.StdSimplex.weights_convexCombPair, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    ring
  have hmid := class_energy_midpoint n q y.weights x.weights
  have hp := class_energy_pos n q hq (fun c => y.weights c - x.weights c) hw
  have hxm := hx (Set.mem_univ m)
  have hxy := hx (Set.mem_univ y)
  have hyx := hy x
  change classEnergy n q x.weights ≤ classEnergy n q m.weights at hxm
  rw [hm] at hxm
  change 0 < classEnergy n q (y.weights - x.weights) at hp
  linarith

private theorem all_minimizers (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1) :
    ∃ x : ClassDistribution n q,
      (∀ y : ClassDistribution n q, classEnergy n q x.weights ≤ classEnergy n q y.weights) ∧
      (∀ y : ClassDistribution n q,
        (∀ z : ClassDistribution n q, classEnergy n q y.weights ≤ classEnergy n q z.weights) →
          y = x) ∧
      (∀ p : AddressDistribution n,
        (∀ r : AddressDistribution n, addressEnergy n q p.weights ≤ addressEnergy n q r.weights) ↔
          classMass n q p = x) ∧
      Function.Surjective (classMass n q) := by
  obtain ⟨x, hx, hu⟩ := class_minimizer_unique n q hq
  refine ⟨x, hx, hu, ?_, class_mass_surjective n q⟩
  intro p
  simp_rw [distribution_energy n q hq]
  constructor
  · intro hp
    apply hu
    intro y
    obtain ⟨r, rfl⟩ := class_mass_surjective n q y
    exact hp r
  · intro hp r
    rw [hp]
    exact hx _

private theorem tree_record_overlap (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq' : ∀ v, q v ≤ 1) (t u : Tree n) :
    (∑ e, treeRecord n q t e * conj (treeRecord n q u e)) =
      ∏ v, if routerLabel n t v = routerLabel n u v then 1 else (q v : ℂ) := by
  classical
  calc
    _ = ∑ e : Environment n, ∏ v,
        (HannRouterDephasing.localRecord (q v) (routerLabel n t v) (e v) *
          conj (HannRouterDephasing.localRecord (q v) (routerLabel n u v) (e v))) := by
      simp only [treeRecord, map_prod, Finset.prod_mul_distrib]
    _ = ∏ v, ∑ s : Option Qutrit,
        HannRouterDephasing.localRecord (q v) (routerLabel n t v) s *
          conj (HannRouterDephasing.localRecord (q v) (routerLabel n u v) s) :=
      (Fintype.prod_sum (fun (v : Router n) (s : Option Qutrit) =>
        HannRouterDephasing.localRecord (q v) (routerLabel n t v) s *
          conj (HannRouterDephasing.localRecord (q v) (routerLabel n u v) s))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      have he := (HannRouterDephasing.result 0 (q v) (hq v) (hq' v) (fun _ => false)).1
        (fun _ _ => 1) (routerLabel n t v) (routerLabel n u v)
      by_cases h : routerLabel n t v = routerLabel n u v <;> simpa [h] using he

/-- Actual heterogeneous hold followed by exactly the existing ideal continuation. -/
def jointOutput (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (s : State n) (e : Environment n) : ℂ :=
  initialized n ψ ((load n n).symm ((HannRouterDephasing.postLoad n D).symm s)) *
    treeRecord n q ((HannRouterDephasing.postLoad n D).symm s).2.2 e

/-- The complete system density matrix, tracing precisely the independent router environments. -/
def noisyOutput (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) : Matrix (State n) (State n) ℂ :=
  fun s t => ∑ e, jointOutput n q D ψ s e * conj (jointOutput n q D ψ t e)

/-- Pure-state fidelity with the unchanged ideal output, over the whole physical system. -/
def squaredFidelity (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) : ℂ :=
  ∑ s, ∑ t, conj (HannRouterDephasing.idealOutput n D ψ s) *
    noisyOutput n q D ψ s t * HannRouterDephasing.idealOutput n D ψ t

private theorem joint_output_basis (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (a : Address n) (b : Bool) (e : Environment n) :
    jointOutput n q D ψ (HannRouterDephasing.outputBasis n D (a, b)) e =
      ψ (a, b) * record n q a e := by
  have hpre : (HannRouterDephasing.postLoad n D).symm
      (HannRouterDephasing.outputBasis n D (a, b)) = load n n (clean n a b) := by
    apply (HannRouterDephasing.postLoad n D).injective
    rw [Equiv.apply_symm_apply]
    exact (correctness.2.2.1 n D a b).symm
  simp only [jointOutput, hpre, Equiv.symm_apply_apply, HannRouterDephasing.initialized_clean]
  change ψ (a, b) * treeRecord n q ((load n n) (loading n a (encode b) 0)).2.2 e = _
  rw [record_loaded n q a (encode b)]

private theorem noisy_output_basis (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool) :
    noisyOutput n q D ψ (HannRouterDephasing.outputBasis n D (a, b))
      (HannRouterDephasing.outputBasis n D (a', b')) =
        ψ (a, b) * conj (ψ (a', b')) * gram n q a a' := by
  simp only [noisyOutput, joint_output_basis, map_mul, gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem fidelity_formula (n : ℕ) (q : Router n → ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) :
    squaredFidelity n q D ψ =
      (addressEnergy n q (HannRouterDephasing.addressProbability n ψ) : ℂ) := by
  unfold squaredFidelity HannRouterDephasing.idealOutput
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [HannRouterDephasing.sum_ket_conj]
  simp_rw [mul_comm (noisyOutput n q D ψ _ _), HannRouterDephasing.sum_ket, Finset.mul_sum]
  have he (ab cd : Address n × Bool) :
      noisyOutput n q D ψ (HannRouterDephasing.outputBasis n D ab)
        (HannRouterDephasing.outputBasis n D cd) =
          ψ ab * conj (ψ cd) * gram n q ab.1 cd.1 :=
    noisy_output_basis n q D ψ ab.1 cd.1 ab.2 cd.2
  simp_rw [he]
  have hm (x y z : ℂ) : conj x * (y * (x * conj y * z)) =
      (Complex.normSq x : ℂ) * (Complex.normSq y : ℂ) * z := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  simp_rw [hm]
  simp only [addressEnergy, HannRouterDephasing.addressProbability, Fintype.sum_prod_type,
    Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [gram_real, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  rw [Finset.sum_comm]

/-- The address law of any normalized, jointly entangled address/bus input. -/
def inputDistribution (n : ℕ) (ψ : Address n × Bool → ℂ)
    (hψ : HannRouterDephasing.Normalized n ψ) : AddressDistribution n where
  weights := Finsupp.equivFunOnFinite.symm (HannRouterDephasing.addressProbability n ψ)
  nonneg a := by
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, HannRouterDephasing.addressProbability]
    exact Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ ab, Complex.normSq (ψ ab)) = 1 at hψ
    simpa only [Finsupp.equivFunOnFinite_symm_apply_apply,
      HannRouterDephasing.addressProbability, Fintype.sum_prod_type] using hψ

private theorem input_weights (n : ℕ) (ψ : Address n × Bool → ℂ)
    (hψ : HannRouterDephasing.Normalized n ψ) :
    ((inputDistribution n ψ hψ).weights : Address n → ℝ) =
      HannRouterDephasing.addressProbability n ψ := by
  simp [inputDistribution]

/-- Every address distribution is physically realizable, with a fixed clean bus. -/
def distributionInput (n : ℕ) (p : AddressDistribution n) (ab : Address n × Bool) : ℂ :=
  if ab.2 then 0 else (Real.sqrt (p.weights ab.1) : ℂ)

private theorem distribution_probability (n : ℕ) (p : AddressDistribution n) (a : Address n) :
    HannRouterDephasing.addressProbability n (distributionInput n p) a = p.weights a := by
  simp [HannRouterDephasing.addressProbability, distributionInput, Complex.normSq_ofReal,
    Real.mul_self_sqrt (p.weights_nonneg a)]

private theorem distribution_normalized (n : ℕ) (p : AddressDistribution n) :
    HannRouterDephasing.Normalized n (distributionInput n p) := by
  change (∑ ab, Complex.normSq (distributionInput n p ab)) = 1
  rw [Fintype.sum_prod_type]
  change (∑ a, HannRouterDephasing.addressProbability n (distributionInput n p) a) = 1
  simp_rw [distribution_probability]
  exact p.total_of_fintype

private theorem distribution_realizes (n : ℕ) (p : AddressDistribution n) :
    inputDistribution n (distributionInput n p) (distribution_normalized n p) = p := by
  ext a
  simp [inputDistribution, distribution_probability]

private theorem ideal_pullback (n : ℕ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (s : State n) :
    HannRouterDephasing.idealOutput n D ψ s =
      initialized n ψ ((load n n).symm ((HannRouterDephasing.postLoad n D).symm s)) := by
  unfold HannRouterDephasing.idealOutput initialized
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hc : HannRouterDephasing.postLoad n D (load n n (clean n a b)) =
      HannRouterDephasing.outputBasis n D (a, b) := correctness.2.2.1 n D a b
  simp only [Equiv.symm_apply_eq, hc]

private theorem tree_record_norm (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq' : ∀ v, q v ≤ 1) (t : Tree n) :
    (∑ e, Complex.normSq (treeRecord n q t e)) = 1 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, ← Complex.mul_conj, Complex.ofReal_one]
  simpa only [ite_true, Finset.prod_const_one] using tree_record_overlap n q hq hq' t t

private theorem ideal_norm (n : ℕ) (D : Address n → Bool) (ψ : Address n × Bool → ℂ)
    (hψ : HannRouterDephasing.Normalized n ψ) :
    (∑ s, Complex.normSq (HannRouterDephasing.idealOutput n D ψ s)) = 1 := by
  have he := HannRouterDephasing.result n 0 (by norm_num) (by norm_num) D
  rcases he with ⟨_, _, _, _, _, _, hi, _⟩
  exact (hi ψ hψ).1

private theorem joint_norm (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq' : ∀ v, q v ≤ 1) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (hψ : HannRouterDephasing.Normalized n ψ) :
    (∑ s, ∑ e, Complex.normSq (jointOutput n q D ψ s e)) = 1 := by
  simp only [jointOutput, Complex.normSq_mul, ← Finset.mul_sum,
    tree_record_norm n q hq hq', mul_one, ← ideal_pullback]
  exact ideal_norm n D ψ hψ

/-- At zero depth there is no deepest router constraint. -/
def DeepestActive : (n : ℕ) → (Router n → ℝ) → Prop
  | 0, _ => True
  | n + 1, q => ∀ u : Address n, q (deepest n u) < 1

private theorem rank_deepest (n : ℕ) (q : Router n → ℝ) (hq : ∀ v, q v ≤ 1) :
    (gram n q).rank = 2 ^ n ↔ DeepestActive n q := by
  cases n with
  | zero => rw [zero_rank q]; simp [DeepestActive]
  | succ n => exact full_rank_iff n q hq

/-- Complete heterogeneous physical profile event, including every ideal-output fidelity minimizer.
The optimizing class law can have zero coordinates. No common router rate is assumed. -/
theorem physical_profile_event (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq' : ∀ v, q v ≤ 1) (D : Address n → Bool) :
    (∀ (a : Address n) (bus : Qutrit),
      treeRecord n q ((load n n) (loading n a bus 0)).2.2 = record n q a) ∧
    (∀ t : Tree n, (∑ e, Complex.normSq (treeRecord n q t e)) = 1) ∧
    (∀ (a b : Address n) (bus bus' : Qutrit),
      profile n q a = profile n q b ↔
        ∀ v, q v < 1 → loadedLabel n a bus v = loadedLabel n b bus' v) ∧
    LinearIndependent ℂ (classRecord n q) ∧
    (gram n q).rank = Fintype.card (Profile n q) ∧
    (∀ x : Address n → ℂ, (gram n q).mulVec x = 0 ↔ ∀ c, classSum n q x c = 0) ∧
    ((gram n q).rank = 2 ^ n ↔ DeepestActive n q) ∧
    (n = 0 → (gram n q).rank = 1) ∧
    (∀ p : AddressDistribution n,
      addressEnergy n q p.weights = classEnergy n q (classMass n q p).weights) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s : State n),
      HannRouterDephasing.idealOutput n D ψ s =
        initialized n ψ ((load n n).symm ((HannRouterDephasing.postLoad n D).symm s))) ∧
    (∀ (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool),
      noisyOutput n q D ψ (HannRouterDephasing.outputBasis n D (a, b))
        (HannRouterDephasing.outputBasis n D (a', b')) =
          ψ (a, b) * conj (ψ (a', b')) * gram n q a a') ∧
    (∀ ψ : Address n × Bool → ℂ, squaredFidelity n q D ψ =
      (addressEnergy n q (HannRouterDephasing.addressProbability n ψ) : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ), HannRouterDephasing.Normalized n ψ →
      (∑ s, ∑ e, Complex.normSq (jointOutput n q D ψ s e)) = 1 ∧
      (∑ s, Complex.normSq (HannRouterDephasing.idealOutput n D ψ s)) = 1) ∧
    (∀ p : AddressDistribution n,
      ∃ h : HannRouterDephasing.Normalized n (distributionInput n p),
        inputDistribution n (distributionInput n p) h = p) ∧
    ∃ x : ClassDistribution n q,
      (∀ y : ClassDistribution n q, classEnergy n q x.weights ≤ classEnergy n q y.weights) ∧
      (∀ y : ClassDistribution n q,
        (∀ z : ClassDistribution n q, classEnergy n q y.weights ≤ classEnergy n q z.weights) →
          y = x) ∧
      Function.Surjective (classMass n q) ∧
      (∀ p : AddressDistribution n,
        (∀ r : AddressDistribution n, addressEnergy n q p.weights ≤ addressEnergy n q r.weights) ↔
          classMass n q p = x) ∧
      (∀ (ψ : Address n × Bool → ℂ) (hψ : HannRouterDephasing.Normalized n ψ),
        (∀ (φ : Address n × Bool → ℂ), HannRouterDephasing.Normalized n φ →
          (squaredFidelity n q D ψ).re ≤ (squaredFidelity n q D φ).re) ↔
            classMass n q (inputDistribution n ψ hψ) = x) := by
  refine ⟨record_loaded n q, tree_record_norm n q hq hq', profile_eq_iff n q,
    class_records_independent n q hq', gram_rank n q hq', gram_kernel n q hq',
    rank_deepest n q hq', ?_, distribution_energy n q hq', ideal_pullback n D,
    noisy_output_basis n q D, fidelity_formula n q D, ?_, ?_, ?_⟩
  · intro h
    subst n
    exact zero_rank q
  · intro ψ hψ
    exact ⟨joint_norm n q hq hq' D ψ hψ, ideal_norm n D ψ hψ⟩
  · intro p
    exact ⟨distribution_normalized n p, distribution_realizes n p⟩
  · obtain ⟨x, hx, hu, hm, hs⟩ := all_minimizers n q hq'
    refine ⟨x, hx, hu, hs, hm, ?_⟩
    have hf (ψ : Address n × Bool → ℂ) (hψ : HannRouterDephasing.Normalized n ψ) :
        (squaredFidelity n q D ψ).re = addressEnergy n q (inputDistribution n ψ hψ).weights := by
      rw [fidelity_formula, Complex.ofReal_re, input_weights]
    intro ψ hψ
    constructor
    · intro hmin
      apply (hm (inputDistribution n ψ hψ)).mp
      intro p
      have hh := hmin (distributionInput n p) (distribution_normalized n p)
      rw [hf ψ hψ, hf _ (distribution_normalized n p), distribution_realizes] at hh
      exact hh
    · intro hmass φ hφ
      rw [hf ψ hψ, hf φ hφ]
      exact (hm (inputDistribution n ψ hψ)).mpr hmass (inputDistribution n φ hφ)



#print axioms gram_rank
#print axioms gram_kernel
#print axioms full_rank_iff
#print axioms zero_rank

#print axioms profile_separation_iff
#print axioms physical_profile_event

end D5.S3.Quantum.Routing.HannRouterProfiles
