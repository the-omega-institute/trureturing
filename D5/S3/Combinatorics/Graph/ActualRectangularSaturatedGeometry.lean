/- GID: D5/S3/Combinatorics/Graph/ActualRectangularSaturatedGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ActualRectangularSaturatedGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual blank vertices and saturated-tile separation from rectangular feasibility. -/

import D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ActualRectangularSaturatedGeometry

open D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 3000000 in
open Classical in
/-- Actual saturated geometry of the original feasible rectangular realization. -/
theorem actual_even_rectangular_saturated_geometry
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Type*) [Fintype E] [DecidableEq E]
    (src dst : E → Fin (2 * a) × Fin (2 * b))
    (T : Finset (Fin (2 * a) × Fin (2 * b)))
    (hadj : ∀ e, squareGrid.Adj
      ((src e).1.val, (src e).2.val) ((dst e).1.val, (dst e).2.val))
    (hinj : Function.Injective (fun z : E × Bool => endpoint src dst z.1 z.2))
    (hdisjoint : ∀ e, src e ∉ T ∧ dst e ∉ T)
    (hfeas : ∀ x ∈ T,
      (((T ∪ Finset.univ.image src) ∪ Finset.univ.image dst).filter
        (fun y => squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val))).card ≤ 1) :
    let κ : Fin (2 * a) × Fin (2 * b) → Fin a × Fin b := fun x =>
      (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
       ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)
    let t : Fin a × Fin b → ℕ := fun Q => (T.filter (fun x => κ x = Q)).card
    let h : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E => κ (src e) = Q ∧ κ (dst e) = Q)).card
    let s : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E =>
        (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
        (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2))).card
    let r : Fin a × Fin b → ℕ := fun Q => 2 - (t Q + h Q + s Q)
    let ER := {e : E // κ (src e) ≠ κ (dst e) ∧
      t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2}
    let rs : ER → Fin a × Fin b := fun e => κ (src e.val)
    let rd : ER → Fin a × Fin b := fun e => κ (dst e.val)
    let χ : Fin a × Fin b → Bool := fun Q => decide (Odd (Q.1.val + Q.2.val))
    let A := (T ∪ Finset.univ.image src) ∪ Finset.univ.image dst
    let corner : (Fin a × Fin b) → (Fin 2 × Fin 2) →
        Fin (2 * a) × Fin (2 * b) := fun Q ij =>
      (⟨2 * Q.1.val + ij.1.val, by have := Q.1.isLt; have := ij.1.isLt; omega⟩,
       ⟨2 * Q.2.val + ij.2.val, by have := Q.2.isLt; have := ij.2.isLt; omega⟩)
    let flip : Fin 2 → Fin 2 := fun i => ⟨1 - i.val, by have := i.isLt; omega⟩
    (T ⊆ A) ∧
    (∀ e, src e ∈ A ∧ dst e ∈ A) ∧
    (∀ x ∈ T, ∀ y z, y ∈ A → z ∈ A →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      squareGrid.Adj (x.1.val, x.2.val) (z.1.val, z.2.val) → y = z) ∧
    (∀ Q ij, κ (corner Q ij) = Q) ∧
    (∀ Q, Function.Injective (corner Q)) ∧
    (∀ Q x, κ x = Q ↔ ∃ ij, corner Q ij = x) ∧
    (∀ Q ij kl,
      squareGrid.Adj ((corner Q ij).1.val, (corner Q ij).2.val)
        ((corner Q kl).1.val, (corner Q kl).2.val) ↔
      (ij.1 = kl.1 ∧ ij.2 ≠ kl.2) ∨ (ij.2 = kl.2 ∧ ij.1 ≠ kl.1)) ∧
    (∀ e : ER, rs e ≠ rd e ∧
      squareGrid.Adj ((rs e).1.val, (rs e).2.val) ((rd e).1.val, (rd e).2.val) ∧
      χ (rs e) ≠ χ (rd e)) ∧
    (∀ Q, t Q ≤ 2) ∧
    (∀ Q, t Q =
      (if corner Q (0,0) ∈ T then 1 else 0) +
      (if corner Q (0,1) ∈ T then 1 else 0) +
      (if corner Q (1,0) ∈ T then 1 else 0) +
      (if corner Q (1,1) ∈ T then 1 else 0)) ∧
    (∀ Q (i j k : Fin 2 × Fin 2), j ≠ k →
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) →
      corner Q i ∈ T → corner Q j ∈ A → corner Q k ∈ A → False) ∧
    (∀ i, flip i ≠ i) ∧
    (∀ i j : Fin 2 × Fin 2,
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      j = (flip i.1,i.2) ∨ j = (i.1,flip i.2)) ∧
    (∀ Q Q' (i j : Fin 2 × Fin 2), Q ≠ Q' →
      squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val)
        ((corner Q' j).1.val, (corner Q' j).2.val) →
      t Q = 2 → corner Q i ∈ A → corner Q i ∉ T →
      ∃ z w : Fin (2 * a) × Fin (2 * b),
        z ∈ T ∧ κ z = Q ∧ κ w = Q' ∧
        squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val) (z.1.val, z.2.val) ∧
        squareGrid.Adj ((corner Q' j).1.val, (corner Q' j).2.val) (w.1.val, w.2.val) ∧
        squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) ∧ w ∉ A) ∧
    (∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y → squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → t (κ y) = 2 →
      x ∈ A → x ∉ T → y ∈ A → y ∉ T → False) ∧
    (∀ e : E, κ (src e) ≠ κ (dst e) →
      ¬ (t (κ (src e)) = 2 ∧ t (κ (dst e)) = 2)) ∧
    (∀ Q, t Q = 2 → h Q = 0) ∧
    (∀ Q, t Q = 2 → s Q = 0) ∧
    (∀ Q, t Q = 2 → degree rs rd Q = 0) ∧
    (∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → x ∈ A → x ∉ T →
      ∃ w : Fin (2 * a) × Fin (2 * b), κ w = κ y ∧
        squareGrid.Adj (y.1.val, y.2.val) (w.1.val, w.2.val) ∧ w ∉ A) := by
  classical
  intro κ t h s r ER rs rd χ A corner flip
  have hTA : T ⊆ A := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hPA : ∀ e, src e ∈ A ∧ dst e ∈ A := by
    intro e
    constructor
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
  have htwo : ∀ x ∈ T, ∀ y z, y ∈ A → z ∈ A →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      squareGrid.Adj (x.1.val, x.2.val) (z.1.val, z.2.val) → y = z := by
    intro x hx y z hy hz hxy hxz
    exact (Finset.card_le_one.mp (hfeas x hx)) y
      (Finset.mem_filter.mpr ⟨hy, hxy⟩) z (Finset.mem_filter.mpr ⟨hz, hxz⟩)
  have hcorner : ∀ Q ij, κ (corner Q ij) = Q := by
    intro Q ij
    apply Prod.ext <;> apply Fin.ext
    · dsimp [κ, corner]
      have := ij.1.isLt
      omega
    · dsimp [κ, corner]
      have := ij.2.isLt
      omega
  have hcornerinj : ∀ Q, Function.Injective (corner Q) := by
    intro Q ij kl he
    have he1 := congrArg (fun x : Fin (2 * a) × Fin (2 * b) => x.1.val) he
    have he2 := congrArg (fun x : Fin (2 * a) × Fin (2 * b) => x.2.val) he
    apply Prod.ext <;> apply Fin.ext <;> dsimp [corner] at he1 he2 <;> omega
  have hfibre : ∀ Q x, κ x = Q ↔ ∃ ij, corner Q ij = x := by
    intro Q x
    constructor
    · intro hx
      have hx1 := congrArg (fun Q : Fin a × Fin b => Q.1.val) hx
      have hx2 := congrArg (fun Q : Fin a × Fin b => Q.2.val) hx
      refine ⟨(⟨x.1.val % 2, Nat.mod_lt _ (by omega)⟩,
        ⟨x.2.val % 2, Nat.mod_lt _ (by omega)⟩), ?_⟩
      apply Prod.ext <;> apply Fin.ext <;> dsimp [corner, κ] at hx1 hx2 ⊢ <;> omega
    · rintro ⟨ij, rfl⟩
      exact hcorner Q ij
  have hcorneradj : ∀ Q ij kl,
      squareGrid.Adj ((corner Q ij).1.val, (corner Q ij).2.val)
        ((corner Q kl).1.val, (corner Q kl).2.val) ↔
      (ij.1 = kl.1 ∧ ij.2 ≠ kl.2) ∨ (ij.2 = kl.2 ∧ ij.1 ≠ kl.1) := by
    intro Q ij kl
    dsimp [squareGrid, corner]
    have := ij.1.isLt
    have := ij.2.isLt
    have := kl.1.isLt
    have := kl.2.isLt
    simp only [Fin.ext_iff]
    omega
  have hcoarse : ∀ x y : Fin (2 * a) × Fin (2 * b),
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) → κ x ≠ κ y →
      squareGrid.Adj ((κ x).1.val, (κ x).2.val) ((κ y).1.val, (κ y).2.val) := by
    intro x y hxy hne
    have hne' : x.1.val / 2 ≠ y.1.val / 2 ∨ x.2.val / 2 ≠ y.2.val / 2 := by
      by_contra hh
      push Not at hh
      apply hne
      apply Prod.ext <;> apply Fin.ext
      · exact hh.1
      · exact hh.2
    dsimp [squareGrid, κ] at hxy ⊢
    omega
  have hflip : ∀ Q Q' : Fin a × Fin b,
      squareGrid.Adj (Q.1.val, Q.2.val) (Q'.1.val, Q'.2.val) → χ Q ≠ χ Q' := by
    intro Q Q' hQQ'
    dsimp [squareGrid] at hQQ'
    by_cases hQ : Odd (Q.1.val + Q.2.val) <;>
      by_cases hQ' : Odd (Q'.1.val + Q'.2.val)
    all_goals simp only [Nat.odd_iff] at hQ hQ'
    all_goals first | omega | simp [χ, Nat.odd_iff, hQ, hQ']
  have hresidual : ∀ e : ER, rs e ≠ rd e ∧
      squareGrid.Adj ((rs e).1.val, (rs e).2.val) ((rd e).1.val, (rd e).2.val) ∧
      χ (rs e) ≠ χ (rd e) := by
    intro e
    have hc := hcoarse (src e.val) (dst e.val) (hadj e.val) e.property.1
    exact ⟨e.property.1, hc, hflip _ _ hc⟩
  have ht : ∀ Q, t Q ≤ 2 := by
    intro Q
    let S : Finset (Fin 2 × Fin 2) := Finset.univ.filter (fun ij => corner Q ij ∈ T)
    have himage : S.image (corner Q) = T.filter (fun x => κ x = Q) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S]
      constructor
      · rintro ⟨ij, hij, rfl⟩
        exact ⟨hij, hcorner Q ij⟩
      · rintro ⟨hx, hxQ⟩
        obtain ⟨ij, rfl⟩ := (hfibre Q x).mp hxQ
        exact ⟨ij, hx, rfl⟩
    have hc : t Q = S.card := by
      change (T.filter (fun x => κ x = Q)).card = S.card
      rw [← himage, Finset.card_image_of_injective _ (hcornerinj Q)]
    have htrip : ∀ i j k : Fin 2 × Fin 2,
        i ∈ S → j ∈ S → k ∈ S → j ≠ k →
        ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
        ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) → False := by
      intro i j k hi hj hk hjk hij hik
      have hiT := (Finset.mem_filter.mp hi).2
      have hjT := (Finset.mem_filter.mp hj).2
      have hkT := (Finset.mem_filter.mp hk).2
      exact hjk (hcornerinj Q (htwo (corner Q i) hiT (corner Q j) (corner Q k)
        (hTA hjT) (hTA hkT) ((hcorneradj Q i j).mpr hij) ((hcorneradj Q i k).mpr hik)))
    have hn0 : ¬ ((0,0) ∈ S ∧ (0,1) ∈ S ∧ (1,0) ∈ S) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (0,0) (0,1) (1,0) h0 h1 h2 (by decide) (by decide) (by decide)
    have hn1 : ¬ ((0,0) ∈ S ∧ (0,1) ∈ S ∧ (1,1) ∈ S) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (0,1) (0,0) (1,1) h1 h0 h2 (by decide) (by decide) (by decide)
    have hn2 : ¬ ((0,0) ∈ S ∧ (1,0) ∈ S ∧ (1,1) ∈ S) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (1,0) (0,0) (1,1) h1 h0 h2 (by decide) (by decide) (by decide)
    have hn3 : ¬ ((0,1) ∈ S ∧ (1,0) ∈ S ∧ (1,1) ∈ S) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (1,1) (0,1) (1,0) h2 h0 h1 (by decide) (by decide) (by decide)
    have hu : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0,0), (0,1), (1,0), (1,1)} := by decide
    have hSc : S.card = (if (0,0) ∈ S then 1 else 0) +
        (if (0,1) ∈ S then 1 else 0) + (if (1,0) ∈ S then 1 else 0) +
        (if (1,1) ∈ S then 1 else 0) := by
      calc
        S.card = (Finset.univ.filter (fun ij => ij ∈ S)).card := by simp
        _ = ∑ ij : Fin 2 × Fin 2, if ij ∈ S then 1 else 0 :=
          Finset.card_filter _ _
        _ = _ := by
          rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
          omega
    rw [hc, hSc]
    split_ifs <;> first
    | omega
    | exact False.elim (hn0 ⟨by assumption, by assumption, by assumption⟩)
    | exact False.elim (hn1 ⟨by assumption, by assumption, by assumption⟩)
    | exact False.elim (hn2 ⟨by assumption, by assumption, by assumption⟩)
    | exact False.elim (hn3 ⟨by assumption, by assumption, by assumption⟩)
  have hTsum : ∀ Q, t Q =
      (if corner Q (0,0) ∈ T then 1 else 0) +
      (if corner Q (0,1) ∈ T then 1 else 0) +
      (if corner Q (1,0) ∈ T then 1 else 0) +
      (if corner Q (1,1) ∈ T then 1 else 0) := by
    intro Q
    let S := Finset.univ.filter (fun ij : Fin 2 × Fin 2 => corner Q ij ∈ T)
    have he : S.image (corner Q) = T.filter (fun x => κ x = Q) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S]
      constructor
      · rintro ⟨ij,hij,rfl⟩
        exact ⟨hij,hcorner Q ij⟩
      · rintro ⟨hx,hxQ⟩
        obtain ⟨ij,rfl⟩ := (hfibre Q x).mp hxQ
        exact ⟨ij,hx,rfl⟩
    have hu : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0,0), (0,1), (1,0), (1,1)} := by decide
    change (T.filter (fun x => κ x = Q)).card = _
    rw [← he, Finset.card_image_of_injective _ (hcornerinj Q)]
    change (Finset.univ.filter (fun ij => corner Q ij ∈ T)).card = _
    rw [Finset.card_filter, hu]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    omega
  have hbad : ∀ Q (i j k : Fin 2 × Fin 2), j ≠ k →
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) →
      corner Q i ∈ T → corner Q j ∈ A → corner Q k ∈ A → False := by
    intro Q i j k hjk hij hik hi hj hk
    exact hjk (hcornerinj Q (htwo (corner Q i) hi (corner Q j) (corner Q k)
      hj hk ((hcorneradj Q i j).mpr hij) ((hcorneradj Q i k).mpr hik)))
  have hsat : ∀ Q (i : Fin 2 × Fin 2), t Q = 2 →
      corner Q i ∈ A → corner Q i ∉ T →
      corner Q (flip i.1, i.2) ∈ T ∧ corner Q (i.1, flip i.2) ∈ T ∧
      corner Q (flip i.1, flip i.2) ∉ A := by
    intro Q i hs hi hn
    have hc := hTsum Q
    rw [hs] at hc
    have hb00 := hbad Q (0,0) (0,1) (1,0) (by decide) (by decide) (by decide)
    have hb01 := hbad Q (0,1) (0,0) (1,1) (by decide) (by decide) (by decide)
    have hb10 := hbad Q (1,0) (0,0) (1,1) (by decide) (by decide) (by decide)
    have hb11 := hbad Q (1,1) (0,1) (1,0) (by decide) (by decide) (by decide)
    have hi00 : corner Q (0,0) ∈ T → corner Q (0,0) ∈ A := fun h => hTA h
    have hi01 : corner Q (0,1) ∈ T → corner Q (0,1) ∈ A := fun h => hTA h
    have hi10 : corner Q (1,0) ∈ T → corner Q (1,0) ∈ A := fun h => hTA h
    have hi11 : corner Q (1,1) ∈ T → corner Q (1,1) ∈ A := fun h => hTA h
    clear hTA hPA htwo hcorner hcornerinj hfibre hcorneradj hcoarse hflip hresidual
      ht hTsum hbad hadj hinj hdisjoint hfeas
    clear_value κ t A corner
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j
    · change corner Q (0,0) ∈ A at hi
      change corner Q (0,0) ∉ T at hn
      change corner Q (1,0) ∈ T ∧ corner Q (0,1) ∈ T ∧ corner Q (1,1) ∉ A
      have hn1 : corner Q (1,0) ∈ T := by
        by_contra hnt
        have hother : corner Q (0,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (1,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb01 hother hi (hi11 hopp)
      have hn2 : corner Q (0,1) ∈ T := by
        by_contra hnt
        have hother : corner Q (1,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (1,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb10 hother hi (hi11 hopp)
      refine ⟨hn1,hn2,?_⟩
      intro hopp
      exact hb10 hn1 hi hopp
    · change corner Q (0,1) ∈ A at hi
      change corner Q (0,1) ∉ T at hn
      change corner Q (1,1) ∈ T ∧ corner Q (0,0) ∈ T ∧ corner Q (1,0) ∉ A
      have hn1 : corner Q (1,1) ∈ T := by
        by_contra hnt
        have hother : corner Q (0,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (1,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb00 hother hi (hi10 hopp)
      have hn2 : corner Q (0,0) ∈ T := by
        by_contra hnt
        have hother : corner Q (1,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (1,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb11 hother hi (hi10 hopp)
      refine ⟨hn1,hn2,?_⟩
      intro hopp
      exact hb11 hn1 hi hopp
    · change corner Q (1,0) ∈ A at hi
      change corner Q (1,0) ∉ T at hn
      change corner Q (0,0) ∈ T ∧ corner Q (1,1) ∈ T ∧ corner Q (0,1) ∉ A
      have hn1 : corner Q (0,0) ∈ T := by
        by_contra hnt
        have hother : corner Q (1,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (0,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb11 hother (hi01 hopp) hi
      have hn2 : corner Q (1,1) ∈ T := by
        by_contra hnt
        have hother : corner Q (0,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (0,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb00 hother (hi01 hopp) hi
      refine ⟨hn1,hn2,?_⟩
      intro hopp
      exact hb00 hn1 hopp hi
    · change corner Q (1,1) ∈ A at hi
      change corner Q (1,1) ∉ T at hn
      change corner Q (0,1) ∈ T ∧ corner Q (1,0) ∈ T ∧ corner Q (0,0) ∉ A
      have hn1 : corner Q (0,1) ∈ T := by
        by_contra hnt
        have hother : corner Q (1,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (0,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb10 hother (hi00 hopp) hi
      have hn2 : corner Q (1,0) ∈ T := by
        by_contra hnt
        have hother : corner Q (0,1) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        have hopp : corner Q (0,0) ∈ T := by
          by_contra hno
          simp only [if_neg hn, if_neg hnt, if_neg hno] at hc
          split_ifs at hc <;> omega
        exact hb01 hother (hi00 hopp) hi
      refine ⟨hn1,hn2,?_⟩
      intro hopp
      exact hb01 hn1 hopp hi
  have hflipne : ∀ i, flip i ≠ i := by
    intro i
    fin_cases i <;> simp [flip]
  have hnbits : ∀ i j : Fin 2 × Fin 2,
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      j = (flip i.1,i.2) ∨ j = (i.1,flip i.2) := by
    intro i j hij
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    rcases hij with ⟨he,hn⟩ | ⟨he,hn⟩
    · right
      refine Prod.ext he.symm ?_
      apply Fin.ext
      have hnval : i.2.val ≠ j.2.val := fun hv => hn (Fin.ext hv)
      dsimp [flip]
      omega
    · left
      refine Prod.ext ?_ he.symm
      apply Fin.ext
      have hnval : i.1.val ≠ j.1.val := fun hv => hn (Fin.ext hv)
      dsimp [flip]
      omega
  have hsatinternal : ∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x = κ y → t (κ x) = 2 → x ∈ A → x ∉ T → y ∈ A → y ∉ T →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) → False := by
    intro x y hsame hs hxA hxT hyA hyT hxy
    obtain ⟨i,hi⟩ := (hfibre (κ x) x).mp rfl
    obtain ⟨j,hj⟩ := (hfibre (κ x) y).mp hsame.symm
    have hsi := hsat (κ x) i hs (by simpa [hi] using hxA) (by simpa [hi] using hxT)
    have hbits := hnbits i j ((hcorneradj (κ x) i j).mp (by simpa [hi,hj] using hxy))
    apply hyT
    rw [← hj]
    rcases hbits with rfl | rfl
    · exact hsi.1
    · exact hsi.2.1
  have hblank : ∀ Q Q' (i j : Fin 2 × Fin 2), Q ≠ Q' →
      squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val)
        ((corner Q' j).1.val, (corner Q' j).2.val) →
      t Q = 2 → corner Q i ∈ A → corner Q i ∉ T →
      ∃ z w : Fin (2 * a) × Fin (2 * b),
        z ∈ T ∧ κ z = Q ∧ κ w = Q' ∧
        squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val) (z.1.val, z.2.val) ∧
        squareGrid.Adj ((corner Q' j).1.val, (corner Q' j).2.val) (w.1.val, w.2.val) ∧
        squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) ∧ w ∉ A := by
    intro Q Q' i j hQQ' hxy hs hi hn
    have hsi := hsat Q i hs hi hn
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    have hforce : ∀ z w : Fin (2 * a) × Fin (2 * b),
        z ∈ T → κ w = Q' →
        squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val) (z.1.val, z.2.val) →
        squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) → w ∉ A := by
      intro z w hz hw hxz hzw hwA
      have he := congrArg κ (htwo z hz (corner Q i) w hi hwA hxz.symm hzw)
      rw [hcorner Q i, hw] at he
      exact hQQ' he
    by_cases hrow : (corner Q i).1.val = (corner Q' j).1.val
    · let z := corner Q (flip i.1, i.2)
      let w := corner Q' (flip j.1, j.2)
      have hxz : squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val)
          (z.1.val, z.2.val) :=
        (hcorneradj Q i (flip i.1, i.2)).mpr (Or.inr ⟨rfl, (hflipne _).symm⟩)
      have hyw : squareGrid.Adj ((corner Q' j).1.val, (corner Q' j).2.val)
          (w.1.val, w.2.val) :=
        (hcorneradj Q' j (flip j.1, j.2)).mpr (Or.inr ⟨rfl, (hflipne _).symm⟩)
      have hzw : squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) := by
        dsimp [squareGrid, z, w, corner, flip] at hxy hrow ⊢
        omega
      exact ⟨z,w,hsi.1,hcorner _ _,hcorner _ _,hxz,hyw,hzw,
        hforce z w hsi.1 (hcorner _ _) hxz hzw⟩
    · let z := corner Q (i.1, flip i.2)
      let w := corner Q' (j.1, flip j.2)
      have hxz : squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val)
          (z.1.val, z.2.val) :=
        (hcorneradj Q i (i.1, flip i.2)).mpr (Or.inl ⟨rfl, (hflipne _).symm⟩)
      have hyw : squareGrid.Adj ((corner Q' j).1.val, (corner Q' j).2.val)
          (w.1.val, w.2.val) :=
        (hcorneradj Q' j (j.1, flip j.2)).mpr (Or.inl ⟨rfl, (hflipne _).symm⟩)
      have hzw : squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) := by
        dsimp [squareGrid, z, w, corner, flip] at hxy hrow ⊢
        omega
      exact ⟨z,w,hsi.2.1,hcorner _ _,hcorner _ _,hxz,hyw,hzw,
        hforce z w hsi.2.1 (hcorner _ _) hxz hzw⟩
  have hsatsep : ∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y → squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → t (κ y) = 2 →
      x ∈ A → x ∉ T → y ∈ A → y ∉ T → False := by
    intro x y hne hxy hx2 hy2 hxA hxT hyA hyT
    obtain ⟨i,hi⟩ := (hfibre (κ x) x).mp rfl
    obtain ⟨j,hj⟩ := (hfibre (κ y) y).mp rfl
    obtain ⟨z,w,hz,hzQ,hwQ,hxz,hyw,hzw,hwA⟩ :=
      hblank (κ x) (κ y) i j hne (by simpa [hi,hj] using hxy)
        hx2 (by simpa [hi] using hxA) (by simpa [hi] using hxT)
    obtain ⟨k,hk⟩ := (hfibre (κ y) w).mp hwQ
    have hyclass := hsat (κ y) j hy2 (by simpa [hj] using hyA) (by simpa [hj] using hyT)
    have hkj := hnbits j k ((hcorneradj (κ y) j k).mp (by simpa [hk] using hyw))
    have hwT : w ∈ T := by
      rw [← hk]
      rcases hkj with rfl | rfl
      · exact hyclass.1
      · exact hyclass.2.1
    exact hwA (hTA hwT)
  have hnosats : ∀ e : E, κ (src e) ≠ κ (dst e) →
      ¬ (t (κ (src e)) = 2 ∧ t (κ (dst e)) = 2) := by
    rintro e hne ⟨hs,hd⟩
    exact hsatsep (src e) (dst e) hne (hadj e) hs hd
      (hPA e).1 (hdisjoint e).1 (hPA e).2 (hdisjoint e).2
  have hhzero : ∀ Q, t Q = 2 → h Q = 0 := by
    intro Q hQ
    change (Finset.univ.filter (fun e : E => κ (src e) = Q ∧ κ (dst e) = Q)).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hs,hd⟩ := (Finset.mem_filter.mp he).2
    exact hsatinternal (src e) (dst e) (hs.trans hd.symm) (by rw [hs]; exact hQ)
      (hPA e).1 (hdisjoint e).1 (hPA e).2 (hdisjoint e).2 (hadj e)
  have hszero : ∀ Q, t Q = 2 → s Q = 0 := by
    intro Q hQ
    change (Finset.univ.filter (fun e : E =>
      (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
      (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2))).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨hs,hd,htd⟩ | ⟨hd,hs,hts⟩
    · exact hnosats e (by intro he; exact hd (he.symm.trans hs))
        ⟨by rw [hs]; exact hQ, htd⟩
    · exact hnosats e (by intro he; exact hs (he.trans hd))
        ⟨hts, by rw [hd]; exact hQ⟩
  have hdsat : ∀ Q, t Q = 2 → degree rs rd Q = 0 := by
    intro Q hQ
    change Fintype.card {x : ER × Bool // endpoint rs rd x.1 x.2 = Q} = 0
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨?_⟩
    rintro ⟨⟨e,bb⟩,he⟩
    cases bb
    · change rs e = Q at he
      have hh := e.property.2.1
      change t (rs e) < 2 at hh
      rw [he,hQ] at hh
      omega
    · change rd e = Q at he
      have hh := e.property.2.2
      change t (rd e) < 2 at hh
      rw [he,hQ] at hh
      omega
  have hattachment : ∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → x ∈ A → x ∉ T →
      ∃ w : Fin (2 * a) × Fin (2 * b), κ w = κ y ∧
        squareGrid.Adj (y.1.val, y.2.val) (w.1.val, w.2.val) ∧ w ∉ A := by
    intro x y hne hxy hs hxA hxT
    obtain ⟨i,hi⟩ := (hfibre (κ x) x).mp rfl
    obtain ⟨j,hj⟩ := (hfibre (κ y) y).mp rfl
    obtain ⟨z,w,hz,hzQ,hwQ,hxz,hyw,hzw,hwA⟩ :=
      hblank (κ x) (κ y) i j hne (by simpa only [hi,hj] using hxy)
        hs (by simpa only [hi] using hxA) (by simpa only [hi] using hxT)
    exact ⟨w,hwQ,by simpa only [hj] using hyw,hwA⟩
  exact ⟨hTA, hPA, htwo, hcorner, hcornerinj, hfibre, hcorneradj,
    hresidual, ht, hTsum, hbad, hflipne, hnbits, hblank,
    hsatsep, hnosats, hhzero, hszero, hdsat, hattachment⟩

#print axioms actual_even_rectangular_saturated_geometry

end

end D5.S3.Combinatorics.Graph.ActualRectangularSaturatedGeometry
