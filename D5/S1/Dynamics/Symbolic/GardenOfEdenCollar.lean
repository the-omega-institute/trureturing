/- GID: D5/S1/Dynamics/Symbolic/GardenOfEdenCollar
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/GardenOfEdenCollar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite collars allow local collision replacement in every ambient context. -/

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
private theorem exists_context_independent_collision (hnot : ¬ Preinjective h) :
    ∃ l u : ℤ, l ≤ u ∧ ∃ x y : ℤ → A,
      (∃ i ∈ Icc l u, x i ≠ y i) ∧
      ∀ z : ℤ → A, (∀ i ∈ Icc l u, z i = x i) →
        FiniteDifference ((Icc l u).piecewise y z) z ∧
        (Icc l u).piecewise y z ≠ z ∧
        code h ((Icc l u).piecewise y z) = code h z := by
  classical
  obtain ⟨x, y, hfin, hcode, hne⟩ :
      ∃ x y : ℤ → A, FiniteDifference x y ∧ code h x = code h y ∧ x ≠ y := by
    simpa only [Preinjective, not_forall, not_imp, exists_prop] using hnot
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

/-- Insert a finite word at an arbitrary integer site, retaining the ambient
configuration outside the half-open insertion interval. -/
def writeWord {n : ℕ} (p : Fin n → A) (t : ℤ) (z : ℤ → A) : ℤ → A :=
  fun i => if hi : t ≤ i ∧ i < t + n then p ⟨(i - t).toNat, by omega⟩ else z i

private theorem writeWord_at {n : ℕ} (p : Fin n → A) (t : ℤ) (z : ℤ → A)
    (j : Fin n) : writeWord p t z (t + (j : ℕ)) = p j := by
  have hj := j.isLt
  simp only [writeWord]
  split_ifs with hi
  · congr 1
    apply Fin.ext
    change (t + (j : ℕ) - t).toNat = j.val
    omega
  · omega

/-- Nonpreinjectivity yields distinct words of positive common length such
that every occurrence of the first can be replaced by the second without
changing any coordinate of the full two-sided code image. -/
theorem exists_erasable_words (hnot : ¬ Preinjective h) :
    ∃ n : ℕ, 0 < n ∧ ∃ p q : Fin n → A, p ≠ q ∧
      ∀ (t : ℤ) (z : ℤ → A), (∀ j : Fin n, z (t + (j : ℕ)) = p j) →
        code h (writeWord q t z) = code h z := by
  classical
  obtain ⟨l, u, hlu, x, y, ⟨i, hi, hxy⟩, hreplace⟩ :=
    exists_context_independent_collision hnot
  let n := (u - l + 1).toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hlen : (n : ℤ) = u - l + 1 := by dsimp [n]; omega
  let p : Fin n → A := fun j => x (l + (j : ℕ))
  let q : Fin n → A := fun j => y (l + (j : ℕ))
  have hpq : p ≠ q := by
    intro he
    let j : Fin n := ⟨(i - l).toNat, by simp only [mem_Icc] at hi; omega⟩
    have hj : l + (j : ℕ) = i := by dsimp [j]; simp only [mem_Icc] at hi; omega
    have heq := congrFun he j
    exact hxy (by simpa only [p, q, hj] using heq)
  refine ⟨n, hn, p, q, hpq, ?_⟩
  intro t z hz
  let z' : ℤ → A := fun j => z (t + (j - l))
  have hz' : ∀ j ∈ Icc l u, z' j = x j := by
    intro j hj
    let a : Fin n := ⟨(j - l).toNat, by simp only [mem_Icc] at hj; omega⟩
    have ha : l + (a : ℕ) = j := by dsimp [a]; simp only [mem_Icc] at hj; omega
    have hja : (a : ℤ) = j - l := by omega
    calc
      z' j = z (t + (a : ℕ)) := by dsimp [z']; rw [hja]
      _ = x (l + (a : ℕ)) := hz a
      _ = x j := by rw [ha]
  have he := (hreplace z' hz').2.2
  have hpaste : (Icc l u).piecewise y z' =
      SymbolicDynamics.FullShift.shift (t - l) (writeWord q t z) := by
    funext j
    simp only [SymbolicDynamics.FullShift.shift_apply, writeWord]
    by_cases hj : j ∈ Icc l u
    · rw [piecewise_eq_of_mem _ _ _ hj]
      have hji : t ≤ t - l + j ∧ t - l + j < t + n := by
        simp only [mem_Icc] at hj
        omega
      rw [dite_eq_left hji]
      dsimp only [q]
      congr 1
      omega
    · rw [piecewise_eq_of_notMem _ _ _ hj]
      have hji : ¬ (t ≤ t - l + j ∧ t - l + j < t + n) := by
        simp only [mem_Icc] at hj
        omega
      rw [dite_eq_right hji]
      dsimp [z']
      congr 1
      omega
  have hzshift : z' = SymbolicDynamics.FullShift.shift (t - l) z := by
    funext j
    simp only [z', SymbolicDynamics.FullShift.shift_apply]
    congr 1
    omega
  rw [hpaste, hzshift, code_shift, code_shift] at he
  funext j
  have heq := congrFun he (j - (t - l))
  simpa only [SymbolicDynamics.FullShift.shift_apply, add_sub_cancel] using heq

end D5.S1.Dynamics.Symbolic.GardenOfEdenCollar
