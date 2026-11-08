/- GID: D5/S1/Dynamics/Symbolic/GardenOfEdenCollar
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/GardenOfEdenCollar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite collisions admit context-independent replacement after adjoining a finite collar. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
import Mathlib.Tactic

/-! Finite-collar replacement for arbitrary two-sided local rules. -/

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.GardenOfEdenCollar

open Set Function
open PermutativeLifts.BipermutativeLift
open PermutativeLifts.BipermutativePreinjectivity

variable {A : Type*} {k : ℕ} {h : (Fin (k + 2) → A) → A}

private theorem code_piecewise_of_collar
    {x y z : ℤ → A} {a b : ℤ}
    (hout : ∀ i, i ∉ Icc a b → x i = y i)
    (hcode : code h x = code h y)
    (hcontext : ∀ i ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)), z i = x i) :
    code h ((Icc a b).piecewise y z) = code h z := by
  classical
  funext i
  by_cases htouch : ∃ j : Fin (k + 2), i + (j : ℕ) ∈ Icc a b
  · obtain ⟨j, hj⟩ := htouch
    have hjbound := j.isLt
    have hcollar (t : Fin (k + 2)) :
        i + (t : ℕ) ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)) := by
      have ht := t.isLt
      simp only [mem_Icc] at hj ⊢
      omega
    have hz : window (k := k) z i = window x i := by
      funext t
      exact hcontext _ (hcollar t)
    have hw : window (k := k) ((Icc a b).piecewise y z) i = window y i := by
      funext t
      change (Icc a b).piecewise y z (i + (t : ℕ)) = y (i + (t : ℕ))
      by_cases ht : i + (t : ℕ) ∈ Icc a b
      · exact piecewise_eq_of_mem _ _ _ ht
      · rw [piecewise_eq_of_notMem _ _ _ ht]
        exact (hcontext _ (hcollar t)).trans (hout _ ht)
    change h (window ((Icc a b).piecewise y z) i) = h (window z i)
    rw [hw, hz]
    exact (congrFun hcode i).symm
  · apply congrArg h
    funext t
    change (Icc a b).piecewise y z (i + (t : ℕ)) = z (i + (t : ℕ))
    exact piecewise_eq_of_notMem _ _ _ (fun ht => htouch ⟨t, ht⟩)

/-- A failure of native preinjectivity supplies a finite interval containing
two distinct patterns which can be interchanged in every ambient context
realizing the first pattern. The replacement changes finitely many sites,
is nontrivial, and preserves the entire two-sided code image. No finiteness
or nonemptiness hypothesis on the alphabet is needed. -/
theorem exists_context_independent_collision (hnot : ¬ Preinjective h) :
    ∃ l u : ℤ, l ≤ u ∧ ∃ x y : ℤ → A,
      (∃ i ∈ Icc l u, x i ≠ y i) ∧
      ∀ z : ℤ → A, (∀ i ∈ Icc l u, z i = x i) →
        FiniteDifference ((Icc l u).piecewise y z) z ∧
        (Icc l u).piecewise y z ≠ z ∧
        code h ((Icc l u).piecewise y z) = code h z := by
  classical
  obtain ⟨x, y, hfin, hcode, hne⟩ :
      ∃ x y : ℤ → A, FiniteDifference x y ∧ code h x = code h y ∧ x ≠ y := by
    simpa only [Preinjective, not_forall, not_imp] using hnot
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hne
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨b, hb⟩ := hfin.bddAbove
  have hab : a ≤ b := (ha hi).trans (hb hi)
  have hout : ∀ j, j ∉ Icc a b → x j = y j := by
    intro j hj
    by_contra hxy
    exact hj ⟨ha hxy, hb hxy⟩
  let l := a - (k + 1 : ℕ)
  let u := b + (k + 1 : ℕ)
  have hsub : Icc a b ⊆ Icc l u := by
    intro j hj
    dsimp [l, u]
    simp only [mem_Icc] at hj ⊢
    omega
  refine ⟨l, u, by dsimp [l, u]; omega, x, y, ⟨i, hsub ⟨ha hi, hb hi⟩, hi⟩, ?_⟩
  intro z hz
  refine ⟨?_, ?_, ?_⟩
  · apply (finite_Icc l u).subset
    intro j hj
    by_contra hjout
    exact hj (piecewise_eq_of_notMem _ _ _ hjout)
  · intro he
    have heq := congrFun he i
    rw [piecewise_eq_of_mem _ _ _ (hsub ⟨ha hi, hb hi⟩), hz i (hsub ⟨ha hi, hb hi⟩)] at heq
    exact hi heq.symm
  · have hpatch : (Icc l u).piecewise y z = (Icc a b).piecewise y z := by
      funext j
      by_cases hj : j ∈ Icc a b
      · rw [piecewise_eq_of_mem _ _ _ hj, piecewise_eq_of_mem _ _ _ (hsub hj)]
      · rw [piecewise_eq_of_notMem _ _ _ hj]
        by_cases hjlu : j ∈ Icc l u
        · rw [piecewise_eq_of_mem _ _ _ hjlu]
          exact (hout j hj).symm.trans (hz j hjlu).symm
        · exact piecewise_eq_of_notMem _ _ _ hjlu
    rw [hpatch]
    exact code_piecewise_of_collar hout hcode hz

end D5.S1.Dynamics.Symbolic.GardenOfEdenCollar
