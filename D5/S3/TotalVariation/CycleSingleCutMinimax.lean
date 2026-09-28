/- GID: D5/S3/TotalVariation/CycleSingleCutMinimax
   generality: G
   mirror-B: D5/B/S3/TotalVariation/CycleSingleCutMinimax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single cuts attain the exact marginal-constrained error budget of a permutation cycle. -/

import D5.S3.TotalVariation.Metric
import Mathlib.Analysis.Convex.Combination

namespace D5.S3.TotalVariation.CycleSingleCutMinimax

open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable
universe u

/-- Finite probability tables, including tables with zero entries. -/
def Probability {A : Type*} [Fintype A] (p : A → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Pushforward of a finite real table. -/
noncomputable def push {A C : Type u} [Fintype A] (f : A → C) (p : A → ℝ) (z : C) : ℝ :=
  ∑ x, if f x = z then p x else 0

/-- All node marginals are the specified probability table. -/
def Joint {B : Type*} [Fintype B] {n : ℕ} (μ : B → ℝ)
    (P : (Fin (n + 1) → B) → ℝ) : Prop :=
  Probability P ∧ ∀ j, push (fun y => y j) P = μ

/-- The next node, including the closing edge. -/
def next {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n then ⟨i.val + 1, by omega⟩ else 0

/-- Identity on internal edges and the permutation on the closing edge. -/
def transport {B : Type*} {n : ℕ} (g : Equiv.Perm B) (i : Fin (n + 1)) : B → B :=
  if i.val = n then g else id

/-- The cut at edge `k`, parametrized by its first coordinate. -/
noncomputable def cut {B : Type*} {n : ℕ} (g : Equiv.Perm B)
    (k : Fin (n + 1)) (x : B) (j : Fin (n + 1)) : B :=
  if j ≤ k then x else g.symm x

/-- The single-cut pushforward. -/
noncomputable def cutLaw {B : Type*} [Fintype B] {n : ℕ}
    (μ : B → ℝ) (g : Equiv.Perm B) (k : Fin (n + 1)) := push (cut g k) μ

/-- Mixture over the cut position. -/
noncomputable def mixture {B : Type*} [Fintype B] {n : ℕ}
    (μ : B → ℝ) (g : Equiv.Perm B) (π : Fin (n + 1) → ℝ) (y : Fin (n + 1) → B) : ℝ :=
  ∑ k, π k * cutLaw μ g k y

/-- Graph total variation, with the actual pair marginal as its first argument. -/
noncomputable def error {B : Type*} [Fintype B] {n : ℕ}
    (μ : B → ℝ) (g : Equiv.Perm B) (P : (Fin (n + 1) → B) → ℝ) (i : Fin (n + 1)) : ℝ :=
  totalVariation (push (fun y => (y i, y (next i))) P)
    (fun z : B × B => if z.2 = transport g i z.1 then μ z.1 else 0)

/-- Mass moved by the permutation. -/
noncomputable def moved {B : Type*} [Fintype B] (μ : B → ℝ) (g : Equiv.Perm B) : ℝ :=
  ∑ x, if g x ≠ x then μ x else 0

/-- The largest of the finitely many edge errors. -/
noncomputable def worst {B : Type*} [Fintype B] {n : ℕ}
    (μ : B → ℝ) (g : Equiv.Perm B) (P : (Fin (n + 1) → B) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (error μ g P)

/-- A convex full-support admissibility class can still exclude every sharp law. -/
def RestrictedCounterexample : Prop :=
  ∃ (μ : Bool → ℝ) (g : Equiv.Perm Bool)
    (A : Set (((Fin 3 → Bool) → ℝ))),
    Probability μ ∧ (∀ x, μ (g x) = μ x) ∧ moved μ g = 1 ∧ Convex ℝ A ∧
    (∀ P ∈ A, Joint μ P) ∧
    (∀ y : Fin 3 → Bool, ∃ P ∈ A, 0 < P y) ∧
    (∀ P ∈ A, ∀ i, error μ g P i = 1 / 2) ∧
    ¬ ∃ P ∈ A, ∀ i, error μ g P i ≤ 1 / 3

set_option maxHeartbeats 800000 in
-- The joint-law argument combines several finite pushforwards and an explicit eight-tuple sum.
/-- Exact single-cut errors and their universal obstruction for arbitrary joint laws. -/
theorem cycle_single_cut_minimax {B : Type u} [Fintype B]
    (n : ℕ) (μ : B → ℝ) (g : Equiv.Perm B)
    (hμ : Probability μ) (hinv : ∀ x, μ (g x) = μ x) :
    (∀ k : Fin (n + 1), Joint μ (cutLaw μ g k) ∧
      ∀ i, error μ g (cutLaw μ g k) i = if i = k then moved μ g else 0) ∧
    (∀ π : Fin (n + 1) → ℝ, Probability π → Joint μ (mixture μ g π) ∧
      ∀ i, error μ g (mixture μ g π) i = moved μ g * π i) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → ∀ i, error μ g P i =
      ∑ y, if y (next i) ≠ transport g i (y i) then P y else 0) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → moved μ g ≤ ∑ i, error μ g P i) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
      ((∃ P, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
    IsLeast {t | ∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ worst μ g P = t}
      (moved μ g / (n + 1)) ∧
    ((∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ ∀ i, error μ g P i ≤ 0) ↔ moved μ g = 0) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) → moved μ g ≤ ∑ i, ε i →
      0 < moved μ g →
      Probability (fun i => ε i / ∑ j, ε j) ∧
      Joint μ (mixture μ g (fun i => ε i / ∑ j, ε j)) ∧
      (∀ i, error μ g (mixture μ g (fun i => ε i / ∑ j, ε j)) i ≤ ε i) ∧
      (∀ i, ε i = 0 → ε i / (∑ j, ε j) = 0)) ∧
    (∀ A : Set (((Fin (n + 1) → B) → ℝ)), Convex ℝ A →
      (∀ k, cutLaw μ g k ∈ A) →
      (∀ π, Probability π → mixture μ g π ∈ A) ∧
      (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
        ((∃ P ∈ A, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
      IsLeast {t | ∃ P ∈ A, Joint μ P ∧ worst μ g P = t} (moved μ g / (n + 1))) ∧
    RestrictedCounterexample := by
  classical
  have hpush {A C : Type u} [Fintype A] [Fintype C]
      (f : A → C) (p : A → ℝ) (u : C → ℝ) :
      ∑ z, push f p z * u z = ∑ x, p x * u (f x) := by
    simp only [push, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [ite_mul]
  have hmass {A C : Type u} [Fintype A] [Fintype C] (f : A → C) (p : A → ℝ) :
      ∑ z, push f p z = ∑ x, p x := by simpa using hpush f p (fun _ => 1)
  have hnonneg {A C : Type u} [Fintype A] (f : A → C) (p : A → ℝ)
      (hp : ∀ x, 0 ≤ p x) (z : C) : 0 ≤ push f p z :=
    by
      unfold push
      exact Finset.sum_nonneg fun x _ => ite_nonneg (hp x) le_rfl
  have hcomp {A C E : Type u} [Fintype A] [Fintype C]
      (f : A → C) (q : C → E) (p : A → ℝ) :
      push q (push f p) = push (q ∘ f) p := by
    funext z
    simpa only [push, mul_ite, mul_one, mul_zero, Function.comp_def] using
      hpush f p (fun c => if q c = z then 1 else 0)
  have hcut_joint (k : Fin (n + 1)) : Joint μ (cutLaw μ g k) := by
    refine ⟨⟨hnonneg _ _ hμ.1, (hmass _ _).trans hμ.2⟩, ?_⟩
    intro j
    rw [cutLaw, hcomp]
    funext z
    by_cases hj : j ≤ k
    · simp [push, cut, hj]
    · have he : (fun x => if g.symm x = z then μ x else 0) =
          (fun x => if x = g z then μ x else 0) := by
        funext x
        rw [g.symm_apply_eq]
      simp only [push, Function.comp_def, cut, if_neg hj, he, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hinv]
  have hbridge (P : (Fin (n + 1) → B) → ℝ) (hP : Joint μ P) (i : Fin (n + 1)) :
      error μ g P i = ∑ y, if y (next i) ≠ transport g i (y i) then P y else 0 := by
    let t := push (fun y => (y i, y (next i))) P
    let f := transport g i
    let M := fun z : B × B => if z.2 = f z.1 then μ z.1 else 0
    have ht (z) : 0 ≤ t z := hnonneg _ _ hP.1.1 z
    have hrow (x) : ∑ z, t (x,z) = μ x := by
      have hp := congrFun (hP.2 i) x
      dsimp [push] at hp
      dsimp [t, push]
      rw [Finset.sum_comm]
      simpa [Prod.mk.injEq, ite_and] using hp
    have hdom (x) : t (x, f x) ≤ μ x := by
      rw [← hrow x]
      exact Finset.single_le_sum (fun z _ => ht (x,z)) (Finset.mem_univ _)
    have hm : ∑ z, t z = ∑ z, M z := by
      simp only [Fintype.sum_prod_type, M]
      simp_rw [hrow]
      simp
    change totalVariation t M = _
    rw [total_variation_eq_sum_positive t M hm, Finset.sum_filter]
    calc
      (∑ z, if M z ≤ t z then t z - M z else 0) =
          ∑ z, t z * (if z.2 ≠ f z.1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z.2 = f z.1
        · have hd : t z ≤ μ z.1 := by simpa [← hz] using hdom z.1
          dsimp [M]
          simp only [hz, if_true, not_true_eq_false, if_false, mul_zero]
          split_ifs with hh <;> linarith
        · simp [M, hz, ht z]
      _ = _ := by
        simpa only [mul_ite, mul_one, mul_zero] using
          hpush (fun y => (y i, y (next i))) P (fun z => if z.2 ≠ f z.1 then 1 else 0)
  have hcut_bad (k i : Fin (n + 1)) (x : B) :
      (cut g k x (next i) ≠ transport g i (cut g k x i)) ↔ i = k ∧ g x ≠ x := by
    by_cases hi : i.val = n
    · have hil : i = Fin.last n := Fin.ext hi
      have hnk : (next i : Fin (n + 1)) = 0 := by simp [next, hi]
      have hz : (0 : Fin (n + 1)) ≤ k := Fin.zero_le _
      by_cases hik : i = k
      · subst k
        simp [cut, transport, hi, hnk, hz, eq_comm]
      · have hki : ¬ i ≤ k := by
          intro h
          apply hik
          apply Fin.ext
          have := k.isLt
          simp only [Fin.le_iff_val_le_val] at h
          omega
        simp [cut, transport, hi, hnk, hz, hki, hik]
    · have hi' : i.val < n := by omega
      have hnext : (next i).val = i.val + 1 := by simp [next, hi']
      by_cases hik : i = k
      · subst k
        have hni : ¬ next i ≤ i := by simp only [Fin.le_iff_val_le_val]; omega
        simp only [cut, le_refl, if_true, if_neg hni, transport, if_neg hi, id_eq,
          true_and]
        apply not_congr
        constructor
        · intro h
          simpa [h] using g.apply_symm_apply x
        · intro h
          exact (g.symm_apply_eq).2 h.symm
      · have hle : (next i ≤ k) ↔ i ≤ k := by
          simp only [Fin.le_iff_val_le_val]
          have hv : i.val ≠ k.val := fun h => hik (Fin.ext h)
          omega
        simp [cut, transport, hi, hle, hik]
  have hcut_error (k i : Fin (n + 1)) :
      error μ g (cutLaw μ g k) i = if i = k then moved μ g else 0 := by
    rw [hbridge _ (hcut_joint k)]
    have he := hpush (cut g k) μ
      (fun y => if y (next i) ≠ transport g i (y i) then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at he
    rw [show (∑ y, if y (next i) ≠ transport g i (y i) then cutLaw μ g k y else 0) =
      ∑ x, if cut g k x (next i) ≠ transport g i (cut g k x i) then μ x else 0 from he]
    simp_rw [hcut_bad]
    by_cases hik : i = k <;> simp [hik, moved]
  have hmix (π : Fin (n + 1) → ℝ) (hπ : Probability π) :
      Joint μ (mixture μ g π) ∧ ∀ i, error μ g (mixture μ g π) i = moved μ g * π i := by
    have hj : Joint μ (mixture μ g π) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro y
        exact Finset.sum_nonneg fun k _ => mul_nonneg (hπ.1 k) ((hcut_joint k).1.1 y)
      · simp only [mixture]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, (hcut_joint _).1.2, mul_one]
        exact hπ.2
      · intro j
        funext x
        change (∑ y, if y j = x then ∑ k, π k * cutLaw μ g k y else 0) = μ x
        have he : (∑ y, if y j = x then ∑ k, π k * cutLaw μ g k y else 0) =
            ∑ k, π k * push (fun y => y j) (cutLaw μ g k) x := by
          simp only [push, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> simp
        rw [he]
        simp_rw [(hcut_joint _).2 j]
        rw [← Finset.sum_mul, hπ.2, one_mul]
    refine ⟨hj, fun i => ?_⟩
    rw [hbridge _ hj]
    have he : (∑ y, if y (next i) ≠ transport g i (y i) then mixture μ g π y else 0) =
        ∑ k, π k * error μ g (cutLaw μ g k) i := by
      simp_rw [hbridge _ (hcut_joint _)]
      simp only [mixture, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    rw [he]
    simp_rw [hcut_error]
    simp [mul_ite, mul_comm]
  have hobstruction (P : (Fin (n + 1) → B) → ℝ) (hP : Joint μ P) :
      moved μ g ≤ ∑ i, error μ g P i := by
    have hfail (y : Fin (n + 1) → B) (hy : g (y 0) ≠ y 0) :
        ∃ i, y (next i) ≠ transport g i (y i) := by
      by_contra! hall
      have hconstant : ∀ j : Fin (n + 1), y j = y 0 := by
        intro j
        induction j using Fin.induction with
        | zero => rfl
        | succ j ih =>
          have hj : j.castSucc.val < n := j.isLt
          have he := hall j.castSucc
          have hnext : next j.castSucc = j.succ := by
            apply Fin.ext
            simp [next]
          have ht : transport g j.castSucc = id := by
            unfold transport
            exact if_neg (Nat.ne_of_lt j.isLt)
          rw [hnext, ht] at he
          exact he.trans ih
      have he := hall (Fin.last n)
      have hl : (next (Fin.last n) : Fin (n + 1)) = 0 := by simp [next]
      exact hy (by simpa [hl, transport, hconstant] using he.symm)
    have hm : moved μ g = ∑ y, if g (y 0) ≠ y 0 then P y else 0 := by
      have he := hpush (fun y : Fin (n + 1) → B => y 0) P (fun x => if g x ≠ x then 1 else 0)
      rw [hP.2 0] at he
      simpa only [moved, mul_ite, mul_one, mul_zero] using he
    rw [hm]
    simp_rw [hbridge _ hP]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : g (y 0) ≠ y 0
    · obtain ⟨i, hi⟩ := hfail y hy
      simp only [if_pos hy]
      calc
        P y = (if y (next i) ≠ transport g i (y i) then P y else 0) := (if_pos hi).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : Fin (n + 1) => if y (next j) ≠ transport g j (y j) then P y else 0)
          (fun j _ => ite_nonneg (hP.1.1 y) le_rfl) (Finset.mem_univ i)
    · simp only [if_neg hy]
      exact Finset.sum_nonneg fun i _ => ite_nonneg (hP.1.1 y) le_rfl
  have ha : 0 ≤ moved μ g := Finset.sum_nonneg fun x _ => ite_nonneg (hμ.1 x) le_rfl
  have hN : (0 : ℝ) < n + 1 := by positivity
  let uniform : Fin (n + 1) → ℝ := fun _ => 1 / (n + 1)
  have hu : Probability uniform := by
    refine ⟨fun _ => le_of_lt (one_div_pos.mpr hN), ?_⟩
    simp [uniform, div_eq_mul_inv, hN.ne']
  have hnormalized (ε : Fin (n + 1) → ℝ) (hε : ∀ i, 0 ≤ ε i)
      (hs : moved μ g ≤ ∑ i, ε i) (hpos : 0 < ∑ i, ε i) :
      Probability (fun i => ε i / ∑ j, ε j) ∧
        ∀ i, error μ g (mixture μ g (fun i => ε i / ∑ j, ε j)) i ≤ ε i := by
    have hp : Probability (fun i => ε i / ∑ j, ε j) := by
      exact ⟨fun i => div_nonneg (hε i) hpos.le, by rw [← Finset.sum_div, div_self hpos.ne']⟩
    refine ⟨hp, fun i => ?_⟩
    rw [(hmix _ hp).2, ← mul_div_assoc]
    exact (div_le_iff₀ hpos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hs (hε i)])
  have hclass (A : Set (((Fin (n + 1) → B) → ℝ)))
      (hm : ∀ π, Probability π → mixture μ g π ∈ A) :
      (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
        ((∃ P ∈ A, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
      IsLeast {t | ∃ P ∈ A, Joint μ P ∧ worst μ g P = t} (moved μ g / (n + 1)) := by
    constructor
    · intro ε hε
      constructor
      · rintro ⟨P, _, hP, he⟩
        exact (hobstruction P hP).trans (Finset.sum_le_sum fun i _ => he i)
      · intro hs
        by_cases hp : 0 < ∑ i, ε i
        · obtain ⟨hπ, he⟩ := hnormalized ε hε hs hp
          exact ⟨_, hm _ hπ, (hmix _ hπ).1, he⟩
        · have hz : moved μ g = 0 := le_antisymm (hs.trans (le_of_not_gt hp)) ha
          refine ⟨_, hm _ hu, (hmix _ hu).1, fun i => ?_⟩
          simpa [(hmix _ hu).2, hz] using hε i
    · have he : worst μ g (mixture μ g uniform) = moved μ g / (n + 1) := by
        unfold worst
        simp_rw [(hmix _ hu).2]
        simp [uniform, div_eq_mul_inv]
      refine ⟨⟨_, hm _ hu, (hmix _ hu).1, he⟩, ?_⟩
      rintro t ⟨P, _, hP, rfl⟩
      apply (div_le_iff₀ hN).mpr
      calc
        moved μ g ≤ ∑ i, error μ g P i := hobstruction P hP
        _ ≤ ∑ _i : Fin (n + 1), worst μ g P :=
          Finset.sum_le_sum fun i _ => Finset.le_sup' (error μ g P) (Finset.mem_univ i)
        _ = worst μ g P * (n + 1) := by simp [mul_comm]
  have hfull := hclass Set.univ (fun _ _ => Set.mem_univ _)
  have hb : ∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
      ((∃ P, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i) := by
    simpa using hfull.1
  refine ⟨fun k => ⟨hcut_joint k, hcut_error k⟩, hmix, hbridge, hobstruction,
    hb, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hfull.2
  · simpa only [Finset.sum_const_zero, le_antisymm_iff, ha, and_true] using
      hb (fun _ => 0) (fun _ => le_rfl)
  · intro ε hε hs hpos
    obtain ⟨hπ, he⟩ := hnormalized ε hε hs (hpos.trans_le hs)
    exact ⟨hπ, (hmix _ hπ).1, he, fun i hi => by rw [hi, zero_div]⟩
  · intro A hA hcuts
    have hm : ∀ π, Probability π → mixture μ g π ∈ A := by
      intro π hπ
      have hh := hA.sum_mem (t := Finset.univ) (w := π) (z := cutLaw μ g)
        (fun i _ => hπ.1 i) hπ.2 (fun i _ => hcuts i)
      have heq : (∑ i, π i • cutLaw μ g i) = mixture μ g π := by
        funext y
        simp [mixture]
      rwa [heq] at hh
    exact ⟨hm, hclass A hm⟩
  -- Full tuple support in a convex class does not supply the sharp cut mixtures.
  · let ν : Bool → ℝ := fun _ => 1 / 2
    let σ : Equiv.Perm Bool :=
      { toFun := Bool.not
        invFun := Bool.not
        left_inv := Bool.not_not
        right_inv := Bool.not_not }
    let J : (Fin 3 → Bool) → ℝ := fun _ => 1 / 8
    let e : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
      { toFun := fun y => (y 0, y 1, y 2)
        invFun := fun z => ![z.1, z.2.1, z.2.2]
        left_inv := by intro y; funext i; fin_cases i <;> rfl
        right_inv := by intro z; rfl }
    have hsum (f : (Fin 3 → Bool) → ℝ) :
        (∑ y, f y) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
      rw [← e.symm.sum_comp]
      simp only [Fintype.sum_prod_type]
      rfl
    have hj : Joint ν J := by
      refine ⟨⟨fun _ => by norm_num [J], ?_⟩, ?_⟩
      · norm_num [J]
      · intro j
        funext x
        fin_cases j <;> cases x <;> norm_num [push, hsum, Fintype.sum_bool, J, ν]
    have he (i : Fin 3) : error ν σ J i = 1 / 2 := by
      fin_cases i <;>
        norm_num [error, totalVariation, push, hsum, Fintype.sum_bool,
          Fintype.sum_prod_type, J, ν, σ, next, transport]
    refine ⟨ν, σ, {J}, ?_, ?_, ?_, convex_singleton J, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x; norm_num [ν]
      · norm_num [ν, Fintype.sum_bool]
    · intro x; rfl
    · norm_num [moved, ν, σ, Fintype.sum_bool]
    · intro P hP
      simpa only [Set.mem_singleton_iff.mp hP] using hj
    · intro y
      exact ⟨J, Set.mem_singleton J, by norm_num [J]⟩
    · intro P hP i
      simpa only [Set.mem_singleton_iff.mp hP] using he i
    · rintro ⟨P, hP, hbudget⟩
      have h := hbudget 0
      rw [Set.mem_singleton_iff.mp hP, he] at h
      norm_num at h

#print axioms cycle_single_cut_minimax

end D5.S3.TotalVariation.CycleSingleCutMinimax
