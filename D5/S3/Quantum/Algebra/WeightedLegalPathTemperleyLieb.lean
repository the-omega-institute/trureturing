/- GID: D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact weighted legal-path matrices satisfy the Temperley-Lieb projection laws. -/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic


set_option autoImplicit false
set_option maxRecDepth 2048

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- A finite path with both endpoints fixed and every consecutive pair related. -/
def LegalPath (R : L → L → Prop) (n : ℕ) (s t : L) : Type _ :=
  {x : Fin (n + 1) → L //
    x 0 = s ∧ x (Fin.last n) = t ∧
      ∀ k : Fin n, R (x k.castSucc) (x k.succ)}

noncomputable instance (R : L → L → Prop) (n : ℕ) (s t : L) :
    Fintype (LegalPath R n s t) := by
  classical
  unfold LegalPath
  infer_instance

/-- The entry in FT.12, with the square root kept in its literal form. -/
def pathProjection (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s t : L) (i : ℕ) (hi : 0 < i ∧ i < n) :
    Matrix (LegalPath R n s t) (LegalPath R n s t) ℂ :=
  fun x y =>
    if (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
        x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ then
      ((Real.sqrt (d (x.1 ⟨i, by omega⟩) * d (y.1 ⟨i, by omega⟩)) /
        (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) else 0

/-- Replace one interior label when its two new incident edges are legal. -/
def replacePath (R : L → L → Prop) (n : ℕ) (s t : L)
    (x : LegalPath R n s t) (i : ℕ) (hi : 0 < i ∧ i < n) (b : L)
    (hleft : R (x.1 ⟨i - 1, by omega⟩) b)
    (hright : R b (x.1 ⟨i + 1, by omega⟩)) : LegalPath R n s t := by
  refine ⟨Function.update x.1 ⟨i, by omega⟩ b, ?_, ?_, ?_⟩
  · have hne : (0 : Fin (n + 1)) ≠ ⟨i, by omega⟩ := by
      apply Fin.ne_of_val_ne
      simp only [Fin.val_zero, Fin.val_mk]
      omega
    simpa [Function.update_of_ne hne] using x.2.1
  · have hne : Fin.last n ≠ ⟨i, by omega⟩ := by
      apply Fin.ne_of_val_ne
      simp only [Fin.val_last, Fin.val_mk]
      omega
    simpa [Function.update_of_ne hne] using x.2.2.1
  · intro k
    by_cases hleftIdx : k.val + 1 = i
    · have hfirst : k.castSucc ≠ (⟨i, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ne_of_val_ne
        simp only [Fin.val_castSucc, Fin.val_mk]
        omega
      have hsecond : k.succ = (⟨i, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simpa using hleftIdx
      simp only [Function.update_of_ne hfirst, hsecond, Function.update_self]
      have hprev : k.castSucc = (⟨i - 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_mk]
        omega
      simpa only [hprev] using hleft
    · by_cases hrightIdx : k.val = i
      · have hfirst : k.castSucc = (⟨i, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          simpa using hrightIdx
        have hsecond : k.succ ≠ (⟨i, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ne_of_val_ne
          simp only [Fin.val_succ, Fin.val_mk]
          omega
        simp only [hfirst, Function.update_self, Function.update_of_ne hsecond]
        have hnext : k.succ = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_mk]
          omega
        simpa only [hnext] using hright
      · have hfirst : k.castSucc ≠ (⟨i, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ne_of_val_ne
          simp only [Fin.val_castSucc, Fin.val_mk]
          omega
        have hsecond : k.succ ≠ (⟨i, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ne_of_val_ne
          simp only [Fin.val_succ, Fin.val_mk]
          omega
        simpa only [Function.update_of_ne hfirst, Function.update_of_ne hsecond]
          using x.2.2.2 k

/-- A local path fiber is exactly the set of neighbors of its common flank. -/
def fiberEquiv (R : L → L → Prop) (hR : Std.Symm R)
    (n : ℕ) (s t : L) (x : LegalPath R n s t)
    (i : ℕ) (hi : 0 < i ∧ i < n)
    (hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) :
    {z : LegalPath R n s t //
        ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k} ≃
      {b : L // R (x.1 ⟨i - 1, by omega⟩) b} := by
  let mid : Fin (n + 1) := ⟨i, by omega⟩
  let prev : Fin (n + 1) := ⟨i - 1, by omega⟩
  let edge : Fin n := ⟨i - 1, by omega⟩
  have hedgePrev : edge.castSucc = prev := by
    apply Fin.ext
    simp [edge, prev]
  have hedgeMid : edge.succ = mid := by
    apply Fin.ext
    simp [edge, mid]
    omega
  refine {
    toFun := fun z => ⟨z.1.1 mid, ?_⟩
    invFun := fun b => ⟨replacePath R n s t x i hi b.1 b.2 ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · have hpath := z.1.2.2.2 edge
    rw [hedgePrev, hedgeMid] at hpath
    simpa only [prev] using (z.2 prev (by simp [prev]; omega)) ▸ hpath
  · exact hflank ▸ hR.symm _ _ b.2
  · intro k hk
    have hne : k ≠ mid := by
      apply Fin.ne_of_val_ne
      simpa only [mid] using hk
    change Function.update x.1 mid b.1 k = x.1 k
    exact Function.update_of_ne hne b.1 x.1
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    funext k
    by_cases hk : k = mid
    · subst k
      simp [replacePath, mid]
    · have hv : k.val ≠ i := by
        simpa only [mid] using Fin.val_ne_of_ne hk
      change Function.update x.1 mid (z.1.1 mid) k = z.1.1 k
      rw [Function.update_of_ne hk]
      exact (z.2 k hv).symm
  · intro b
    apply Subtype.ext
    simp [replacePath, mid]

/-- FT.13 for all fixed-endpoint legal path spaces, including empty ones. -/
theorem weighted_legal_path_temperley_lieb
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a)
    (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (n : ℕ) (s t : L) :
    (∀ (i : ℕ) (hi : 0 < i ∧ i < n),
      (pathProjection R d δ n s t i hi).conjTranspose =
        pathProjection R d δ n s t i hi ∧
      pathProjection R d δ n s t i hi * pathProjection R d δ n s t i hi =
        pathProjection R d δ n s t i hi) ∧
    (∀ (i : ℕ) (hi : 0 < i ∧ i + 1 < n),
      pathProjection R d δ n s t i ⟨hi.1, by omega⟩ *
          pathProjection R d δ n s t (i + 1) ⟨by omega, hi.2⟩ *
          pathProjection R d δ n s t i ⟨hi.1, by omega⟩ =
        ((δ⁻¹ : ℂ) ^ 2) •
          pathProjection R d δ n s t i ⟨hi.1, by omega⟩) ∧
    (∀ (i j : ℕ) (hi : 0 < i ∧ i < n) (hj : 0 < j ∧ j < n),
      i + 2 ≤ j ∨ j + 2 ≤ i →
      pathProjection R d δ n s t i hi * pathProjection R d δ n s t j hj =
        pathProjection R d δ n s t j hj * pathProjection R d δ n s t i hi) := by
  have local_ext (i : ℕ) (hi : 0 < i ∧ i < n)
      (x y : LegalPath R n s t)
      (haway : ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k)
      (hcenter : x.1 ⟨i, by omega⟩ = y.1 ⟨i, by omega⟩) : x = y := by
    apply Subtype.ext
    funext k
    by_cases hk : k.val = i
    · have hk' : k = (⟨i, by omega⟩ : Fin (n + 1)) := Fin.ext hk
      simpa only [hk'] using hcenter
    · exact haway k hk
  have edge_left (x : LegalPath R n s t) (i : ℕ) (hi : 0 < i ∧ i < n) :
      R (x.1 ⟨i - 1, by omega⟩) (x.1 ⟨i, by omega⟩) := by
    let k : Fin n := ⟨i - 1, by omega⟩
    have hfirst : k.castSucc = (⟨i - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [k]
    have hsecond : k.succ = (⟨i, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [k]
      omega
    simpa only [hfirst, hsecond] using x.2.2.2 k
  have edge_right (x : LegalPath R n s t) (i : ℕ) (hi : 0 < i ∧ i < n) :
      R (x.1 ⟨i, by omega⟩) (x.1 ⟨i + 1, by omega⟩) := by
    let k : Fin n := ⟨i, by omega⟩
    have hfirst : k.castSucc = (⟨i, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [k]
    have hsecond : k.succ = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [k]
    simpa only [hfirst, hsecond] using x.2.2.2 k
  have fiber_weight_sum (i : ℕ) (hi : 0 < i ∧ i < n)
      (x : LegalPath R n s t)
      (hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) :
      (∑ z : LegalPath R n s t,
        if ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k then
          d (z.1 ⟨i, by omega⟩) else 0) =
        δ * d (x.1 ⟨i - 1, by omega⟩) := by
    classical
    let e := fiberEquiv R hR n s t x i hi hflank
    calc
      _ = ∑ z ∈ (Finset.univ.filter fun z : LegalPath R n s t =>
            ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k),
            d (z.1 ⟨i, by omega⟩) := by
        simp only [Finset.sum_filter]
      _ = ∑ z : {z : LegalPath R n s t //
            ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k},
            d (z.1.1 ⟨i, by omega⟩) :=
        Finset.sum_subtype _ (by simp) _
      _ = ∑ b : {b : L // R (x.1 ⟨i - 1, by omega⟩) b}, d b.1 := by
        apply Fintype.sum_equiv e
        intro z
        rfl
      _ = ∑ b : L with R (x.1 ⟨i - 1, by omega⟩) b, d b := by
        exact (Finset.sum_subtype _ (by simp) d).symm
      _ = _ := hPF _
  have fiber_normalized_sum (i : ℕ) (hi : 0 < i ∧ i < n)
      (x : LegalPath R n s t)
      (hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) :
      (∑ z : LegalPath R n s t,
        if ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k then
          ((d (z.1 ⟨i, by omega⟩) /
            (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) else 0) = 1 := by
    classical
    have hden : δ * d (x.1 ⟨i - 1, by omega⟩) ≠ 0 :=
      mul_ne_zero (ne_of_gt hδ) (ne_of_gt (hd _))
    have hsum := fiber_weight_sum i hi x hflank
    calc
      _ = (((∑ z : LegalPath R n s t,
            if ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k then
              d (z.1 ⟨i, by omega⟩) else 0) /
          (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        push_cast
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = 1 := by rw [hsum]; simp [hden]
  have coeff_identity (a b c w : L) :
      ((Real.sqrt (d a * d c) / (δ * d w) : ℝ) : ℂ) *
          ((Real.sqrt (d c * d b) / (δ * d w) : ℝ) : ℂ) =
        ((Real.sqrt (d a * d b) / (δ * d w) : ℝ) : ℂ) *
          ((d c / (δ * d w) : ℝ) : ℂ) := by
    have hsqrt : Real.sqrt (d a * d c) * Real.sqrt (d c * d b) =
        Real.sqrt (d a * d b) * d c := by
      rw [Real.sqrt_mul (le_of_lt (hd a)), Real.sqrt_mul (le_of_lt (hd c)),
        Real.sqrt_mul (le_of_lt (hd a))]
      calc
        _ = Real.sqrt (d a) * Real.sqrt (d b) *
              (Real.sqrt (d c) ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt (le_of_lt (hd c))]
    have hreal :
        Real.sqrt (d a * d c) / (δ * d w) *
            (Real.sqrt (d c * d b) / (δ * d w)) =
          Real.sqrt (d a * d b) / (δ * d w) *
            (d c / (δ * d w)) := by
      calc
        _ = (Real.sqrt (d a * d c) * Real.sqrt (d c * d b)) /
              ((δ * d w) ^ 2) := by ring
        _ = (Real.sqrt (d a * d b) * d c) / ((δ * d w) ^ 2) := by
          rw [hsqrt]
        _ = _ := by ring
    exact_mod_cast hreal
  have adjacent_first_survivor (i : ℕ) (hi : 0 < i ∧ i + 1 < n)
      (x : LegalPath R n s t)
      (hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) :
      ∃ z : LegalPath R n s t,
        (∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k) ∧
        z.1 ⟨i, by omega⟩ = x.1 ⟨i + 2, by omega⟩ ∧
        ∀ v u : LegalPath R n s t,
          pathProjection R d δ n s t i ⟨hi.1, by omega⟩ x v *
              pathProjection R d δ n s t (i + 1) ⟨by omega, hi.2⟩ v u ≠ 0 →
            v = z := by
    have hedge : R (x.1 ⟨i + 1, by omega⟩)
        (x.1 ⟨i + 2, by omega⟩) := by
      let k : Fin n := ⟨i + 1, by omega⟩
      have hfirst : k.castSucc = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp [k]
      have hsecond : k.succ = (⟨i + 2, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp [k]
      simpa only [hfirst, hsecond] using x.2.2.2 k
    have hleft : R (x.1 ⟨i - 1, by omega⟩)
        (x.1 ⟨i + 2, by omega⟩) := by
      rw [hflank]
      exact hedge
    have hright : R (x.1 ⟨i + 2, by omega⟩)
        (x.1 ⟨i + 1, by omega⟩) := hR.symm _ _ hedge
    let z : LegalPath R n s t :=
      replacePath R n s t x i ⟨hi.1, by omega⟩
        (x.1 ⟨i + 2, by omega⟩) hleft hright
    have hzaway : ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k := by
      intro k hk
      have hne : k ≠ (⟨i, by omega⟩ : Fin (n + 1)) :=
        Fin.ne_of_val_ne (by simpa only [Fin.val_mk] using hk)
      change Function.update x.1 ⟨i, by omega⟩
        (x.1 ⟨i + 2, by omega⟩) k = x.1 k
      exact Function.update_of_ne hne _ _
    have hzcenter : z.1 ⟨i, by omega⟩ = x.1 ⟨i + 2, by omega⟩ := by
      change Function.update x.1 ⟨i, by omega⟩
        (x.1 ⟨i + 2, by omega⟩) ⟨i, by omega⟩ = _
      exact Function.update_self _ _ _
    refine ⟨z, hzaway, hzcenter, ?_⟩
    intro v u hnon
    have hfirst : pathProjection R d δ n s t i ⟨hi.1, by omega⟩ x v ≠ 0 := by
      intro he
      exact hnon (by rw [he, zero_mul])
    have hsecond : pathProjection R d δ n s t (i + 1)
        ⟨by omega, hi.2⟩ v u ≠ 0 := by
      intro he
      exact hnon (by rw [he, mul_zero])
    have hsi : (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = v.1 k) ∧
        x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ := by
      by_contra hn
      apply hfirst
      unfold pathProjection
      rw [if_neg hn]
    have hsj : (∀ k : Fin (n + 1), k.val ≠ i + 1 → v.1 k = u.1 k) ∧
        v.1 ⟨i + 1 - 1, by omega⟩ = v.1 ⟨i + 1 + 1, by omega⟩ := by
      by_contra hn
      apply hsecond
      unfold pathProjection
      rw [if_neg hn]
    have hvcenter : v.1 ⟨i, by omega⟩ = z.1 ⟨i, by omega⟩ := by
      calc
        _ = v.1 ⟨i + 2, by omega⟩ := by simpa only [Nat.add_sub_cancel_right] using hsj.2
        _ = x.1 ⟨i + 2, by omega⟩ :=
          (hsi.1 ⟨i + 2, by omega⟩ (by simp only [Fin.val_mk]; omega)).symm
        _ = _ := hzcenter.symm
    have haway_vz : ∀ k : Fin (n + 1), k.val ≠ i → v.1 k = z.1 k := by
      intro k hk
      exact (hsi.1 k hk).symm.trans (hzaway k hk).symm
    exact local_ext i ⟨hi.1, by omega⟩ v z haway_vz hvcenter
  have adjacent_second_survivor (i : ℕ) (hi : 0 < i ∧ i + 1 < n)
      (x z : LegalPath R n s t)
      (hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩)
      (hzaway : ∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k)
      (y u : LegalPath R n s t)
      (hnon : pathProjection R d δ n s t (i + 1) ⟨by omega, hi.2⟩ z u *
          pathProjection R d δ n s t i ⟨hi.1, by omega⟩ u y ≠ 0) : u = z := by
    have hfirst : pathProjection R d δ n s t (i + 1)
        ⟨by omega, hi.2⟩ z u ≠ 0 := by
      intro he
      exact hnon (by rw [he, zero_mul])
    have hsecond : pathProjection R d δ n s t i
        ⟨hi.1, by omega⟩ u y ≠ 0 := by
      intro he
      exact hnon (by rw [he, mul_zero])
    have hzu : (∀ k : Fin (n + 1), k.val ≠ i + 1 → z.1 k = u.1 k) ∧
        z.1 ⟨i + 1 - 1, by omega⟩ = z.1 ⟨i + 1 + 1, by omega⟩ := by
      by_contra hn
      apply hfirst
      unfold pathProjection
      rw [if_neg hn]
    have huy : (∀ k : Fin (n + 1), k.val ≠ i → u.1 k = y.1 k) ∧
        u.1 ⟨i - 1, by omega⟩ = u.1 ⟨i + 1, by omega⟩ := by
      by_contra hn
      apply hsecond
      unfold pathProjection
      rw [if_neg hn]
    have hcenter : u.1 ⟨i + 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩ := by
      calc
        _ = u.1 ⟨i - 1, by omega⟩ := huy.2.symm
        _ = z.1 ⟨i - 1, by omega⟩ :=
          (hzu.1 ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)).symm
        _ = x.1 ⟨i - 1, by omega⟩ :=
          hzaway ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        _ = x.1 ⟨i + 1, by omega⟩ := hflank
        _ = _ := (hzaway ⟨i + 1, by omega⟩
          (by simp only [Fin.val_mk]; omega)).symm
    have haway : ∀ k : Fin (n + 1), k.val ≠ i + 1 → u.1 k = z.1 k := by
      intro k hk
      exact (hzu.1 k hk).symm
    exact local_ext (i + 1) ⟨by omega, hi.2⟩ u z haway hcenter
  constructor
  · intro i hi
    constructor
    · ext x y
      have hxy :
          ((∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
              x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) ↔
            ((∀ k : Fin (n + 1), k.val ≠ i → y.1 k = x.1 k) ∧
              y.1 ⟨i - 1, by omega⟩ = y.1 ⟨i + 1, by omega⟩) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨fun k hk => (ha k hk).symm, ?_⟩
          rw [← ha ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega),
            ← ha ⟨i + 1, by omega⟩ (by simp only [Fin.val_mk]; omega)]
          exact hb
        · rintro ⟨ha, hb⟩
          refine ⟨fun k hk => (ha k hk).symm, ?_⟩
          rw [← ha ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega),
            ← ha ⟨i + 1, by omega⟩ (by simp only [Fin.val_mk]; omega)]
          exact hb
      by_cases h : (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
          x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩
      · have h' := hxy.mp h
        have hflank := h.1 ⟨i - 1, by omega⟩
          (by simp only [Fin.val_mk]; omega)
        change star (pathProjection R d δ n s t i hi y x) =
          pathProjection R d δ n s t i hi x y
        unfold pathProjection
        rw [if_pos h', if_pos h]
        rw [Complex.star_def, Complex.conj_ofReal]
        rw [hflank]
        congr 1
        ring
      · have h' : ¬ ((∀ k : Fin (n + 1), k.val ≠ i → y.1 k = x.1 k) ∧
            y.1 ⟨i - 1, by omega⟩ = y.1 ⟨i + 1, by omega⟩) := by
          exact fun hh => h (hxy.mpr hh)
        change star (pathProjection R d δ n s t i hi y x) =
          pathProjection R d δ n s t i hi x y
        unfold pathProjection
        rw [if_neg h', if_neg h, star_zero]
    · ext x y
      change (pathProjection R d δ n s t i hi *
        pathProjection R d δ n s t i hi) x y =
          pathProjection R d δ n s t i hi x y
      rw [Matrix.mul_apply]
      by_cases hxy :
          (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
            x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩
      · have hnorm :
            (∑ z : LegalPath R n s t,
              if ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k then
                ((d (z.1 ⟨i, by omega⟩) /
                  (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) else 0) = 1 := by
          convert fiber_normalized_sum i hi x hxy.2 using 1
          apply Finset.sum_congr rfl
          intro z _
          have heq :
              (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k) ↔
                (∀ k : Fin (n + 1), k.val ≠ i → z.1 k = x.1 k) := by
            constructor <;> intro h k hk <;> exact (h k hk).symm
          simp only [heq]
        have hterm (z : LegalPath R n s t) :
            pathProjection R d δ n s t i hi x z *
                pathProjection R d δ n s t i hi z y =
              if ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k then
                ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                    d (y.1 ⟨i, by omega⟩)) /
                  (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) *
                  ((d (z.1 ⟨i, by omega⟩) /
                    (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ)
              else 0 := by
          by_cases hxz : ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k
          · have hzx :
                (∀ k : Fin (n + 1), k.val ≠ i → z.1 k = y.1 k) ∧
                  z.1 ⟨i - 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩ := by
              constructor
              · intro k hk
                exact (hxz k hk).symm.trans (hxy.1 k hk)
              · rw [← hxz ⟨i - 1, by omega⟩
                  (by simp only [Fin.val_mk]; omega),
                  ← hxz ⟨i + 1, by omega⟩
                    (by simp only [Fin.val_mk]; omega)]
                exact hxy.2
            have hprev := hxz ⟨i - 1, by omega⟩
              (by simp only [Fin.val_mk]; omega)
            unfold pathProjection
            rw [if_pos ⟨hxz, hxy.2⟩, if_pos hzx, if_pos hxz]
            rw [← hprev]
            exact coeff_identity _ _ _ _
          · have hnsupport : ¬ ((∀ k : Fin (n + 1), k.val ≠ i →
                x.1 k = z.1 k) ∧
                x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) :=
              fun hz => hxz hz.1
            unfold pathProjection
            rw [if_neg hnsupport, zero_mul, if_neg hxz]
        calc
          (∑ z : LegalPath R n s t,
              pathProjection R d δ n s t i hi x z *
                pathProjection R d δ n s t i hi z y) =
              ∑ z : LegalPath R n s t,
                if ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k then
                  ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                    d (y.1 ⟨i, by omega⟩)) /
                    (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) *
                    ((d (z.1 ⟨i, by omega⟩) /
                      (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ)
                else 0 := by simp only [hterm]
          _ = ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                d (y.1 ⟨i, by omega⟩)) /
                (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
              calc
                _ = ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                      d (y.1 ⟨i, by omega⟩)) /
                      (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) *
                    (∑ z : LegalPath R n s t,
                      if ∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k then
                        ((d (z.1 ⟨i, by omega⟩) /
                          (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) else 0) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro z _
                    split_ifs <;> simp
                _ = _ := by rw [hnorm, mul_one]
          _ = pathProjection R d δ n s t i hi x y := by
              unfold pathProjection
              rw [if_pos hxy]
      · have hterm (z : LegalPath R n s t) :
            pathProjection R d δ n s t i hi x z *
                pathProjection R d δ n s t i hi z y = 0 := by
          by_cases hxz :
              (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k) ∧
                x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩
          · have hnzy : ¬ ((∀ k : Fin (n + 1), k.val ≠ i →
                z.1 k = y.1 k) ∧
                z.1 ⟨i - 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩) := by
              intro hzy
              apply hxy
              refine ⟨?_, hxz.2⟩
              intro k hk
              exact (hxz.1 k hk).trans (hzy.1 k hk)
            unfold pathProjection
            rw [if_pos hxz, if_neg hnzy, mul_zero]
          · unfold pathProjection
            rw [if_neg hxz, zero_mul]
        simp only [hterm, Finset.sum_const_zero]
        unfold pathProjection
        rw [if_neg hxy]
  constructor
  · intro i hi
    let Pi := pathProjection R d δ n s t i ⟨hi.1, by omega⟩
    let Pj := pathProjection R d δ n s t (i + 1) ⟨by omega, hi.2⟩
    ext x y
    change ((Pi * Pj) * Pi) x y = (((δ⁻¹ : ℂ) ^ 2) • Pi) x y
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩
    · obtain ⟨z, hzaway, hzcenter, hfirst⟩ :=
        adjacent_first_survivor i hi x hflank
      have hinner (u : LegalPath R n s t) :
          (Pi * Pj) x u = Pi x z * Pj z u := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_single z
        · intro v _ hvz
          have hzero : Pi x v * Pj v u = 0 := by
            by_contra hnon
            exact hvz (hfirst v u hnon)
          exact hzero
        · intro hznot
          exact (hznot (Finset.mem_univ z)).elim
      have houter : ((Pi * Pj) * Pi) x y =
          (Pi x z * Pj z z) * Pi z y := by
        rw [Matrix.mul_apply]
        simp_rw [hinner]
        apply Finset.sum_eq_single z
        · intro u _ huz
          have hzero : Pj z u * Pi u y = 0 := by
            by_contra hnon
            exact huz (adjacent_second_survivor i hi x z hflank hzaway y u hnon)
          calc
            (Pi x z * Pj z u) * Pi u y = Pi x z * (Pj z u * Pi u y) := by ring
            _ = 0 := by rw [hzero, mul_zero]
        · intro hznot
          exact (hznot (Finset.mem_univ z)).elim
      rw [houter]
      have hzflank : z.1 ⟨i - 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩ := by
        calc
          _ = x.1 ⟨i - 1, by omega⟩ :=
            hzaway _ (by simp only [Fin.val_mk]; omega)
          _ = x.1 ⟨i + 1, by omega⟩ := hflank
          _ = _ := (hzaway _ (by simp only [Fin.val_mk]; omega)).symm
      have hsupport :
          ((∀ k : Fin (n + 1), k.val ≠ i → z.1 k = y.1 k) ∧
              z.1 ⟨i - 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩) ↔
            ((∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
              x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩) := by
        constructor
        · intro hz
          refine ⟨?_, hflank⟩
          intro k hk
          exact (hzaway k hk).symm.trans (hz.1 k hk)
        · intro hx
          refine ⟨?_, hzflank⟩
          intro k hk
          exact (hzaway k hk).trans (hx.1 k hk)
      by_cases hxy : (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = y.1 k) ∧
          x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩
      · have hxz : (∀ k : Fin (n + 1), k.val ≠ i → x.1 k = z.1 k) ∧
            x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ :=
          ⟨fun k hk => (hzaway k hk).symm, hflank⟩
        have hzy := hsupport.mpr hxy
        have hdiag :
            (∀ k : Fin (n + 1), k.val ≠ i + 1 → z.1 k = z.1 k) ∧
              z.1 ⟨i + 1 - 1, by omega⟩ = z.1 ⟨i + 1 + 1, by omega⟩ := by
          refine ⟨fun _ _ => rfl, ?_⟩
          have hlast := hzaway ⟨i + 2, by omega⟩
            (by simp only [Fin.val_mk]; omega)
          simpa only [Nat.add_sub_cancel_right] using hzcenter.trans hlast.symm
        have hPixz : Pi x z =
            ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                d (x.1 ⟨i + 2, by omega⟩)) /
              (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
          unfold Pi pathProjection
          rw [if_pos hxz, hzcenter]
        have hPizy : Pi z y =
            ((Real.sqrt (d (x.1 ⟨i + 2, by omega⟩) *
                d (y.1 ⟨i, by omega⟩)) /
              (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
          unfold Pi pathProjection
          rw [if_pos hzy, hzcenter,
            hzaway ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)]
        have hPixy : Pi x y =
            ((Real.sqrt (d (x.1 ⟨i, by omega⟩) *
                d (y.1 ⟨i, by omega⟩)) /
              (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
          unfold Pi pathProjection
          rw [if_pos hxy]
        have hmid : z.1 ⟨i + 1, by omega⟩ = x.1 ⟨i - 1, by omega⟩ := by
          calc
            _ = x.1 ⟨i + 1, by omega⟩ :=
              hzaway _ (by simp only [Fin.val_mk]; omega)
            _ = _ := hflank.symm
        have hPjzz : Pj z z =
            ((d (x.1 ⟨i - 1, by omega⟩) /
              (δ * d (x.1 ⟨i + 2, by omega⟩)) : ℝ) : ℂ) := by
          unfold Pj pathProjection
          rw [if_pos hdiag, hmid]
          have hden : z.1 ⟨i + 1 - 1, by omega⟩ =
              x.1 ⟨i + 2, by omega⟩ := by
            simpa only [Nat.add_sub_cancel_right] using hzcenter
          rw [hden, Real.sqrt_mul_self (le_of_lt (hd _))]
        have hpair : Pi x z * Pi z y =
            Pi x y *
              ((d (x.1 ⟨i + 2, by omega⟩) /
                (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) := by
          rw [hPixz, hPizy, hPixy]
          exact coeff_identity _ _ _ _
        have hscalar :
            ((d (x.1 ⟨i + 2, by omega⟩) /
              (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ) *
              ((d (x.1 ⟨i - 1, by omega⟩) /
                (δ * d (x.1 ⟨i + 2, by omega⟩)) : ℝ) : ℂ) =
              (δ⁻¹ : ℂ) ^ 2 := by
          have hδne : δ ≠ 0 := ne_of_gt hδ
          have ha : d (x.1 ⟨i - 1, by omega⟩) ≠ 0 := ne_of_gt (hd _)
          have hb : d (x.1 ⟨i + 2, by omega⟩) ≠ 0 := ne_of_gt (hd _)
          have hreal :
              d (x.1 ⟨i + 2, by omega⟩) /
                  (δ * d (x.1 ⟨i - 1, by omega⟩)) *
                (d (x.1 ⟨i - 1, by omega⟩) /
                  (δ * d (x.1 ⟨i + 2, by omega⟩))) =
                (δ⁻¹ : ℝ) ^ 2 := by
            field_simp
          exact_mod_cast hreal
        calc
          (Pi x z * Pj z z) * Pi z y = (Pi x z * Pi z y) * Pj z z := by ring
          _ = (Pi x y *
              ((d (x.1 ⟨i + 2, by omega⟩) /
                (δ * d (x.1 ⟨i - 1, by omega⟩)) : ℝ) : ℂ)) * Pj z z := by
            rw [hpair]
          _ = Pi x y * (δ⁻¹ : ℂ) ^ 2 := by
            rw [hPjzz, mul_assoc, hscalar]
          _ = (δ⁻¹ : ℂ) ^ 2 * Pi x y := by ring
      · have hzy : ¬ ((∀ k : Fin (n + 1), k.val ≠ i → z.1 k = y.1 k) ∧
            z.1 ⟨i - 1, by omega⟩ = z.1 ⟨i + 1, by omega⟩) := by
          exact fun hz => hxy (hsupport.mp hz)
        have hzeroZ : Pi z y = 0 := by
          unfold Pi pathProjection
          rw [if_neg hzy]
        have hzeroX : Pi x y = 0 := by
          unfold Pi pathProjection
          rw [if_neg hxy]
        rw [hzeroZ, hzeroX, mul_zero, mul_zero]
    · have hzero (v : LegalPath R n s t) : Pi x v = 0 := by
        unfold Pi pathProjection
        rw [if_neg (fun h => hflank h.2)]
      have hleft : ((Pi * Pj) * Pi) x y = 0 := by
        simp [Matrix.mul_apply, hzero]
      have hright : Pi x y = 0 := hzero y
      rw [hleft, hright, mul_zero]
  · have ordered (i j : ℕ) (hi : 0 < i ∧ i < n) (hj : 0 < j ∧ j < n)
        (hij : i + 2 ≤ j) :
        pathProjection R d δ n s t i hi * pathProjection R d δ n s t j hj =
          pathProjection R d δ n s t j hj * pathProjection R d δ n s t i hi := by
      let Pi := pathProjection R d δ n s t i hi
      let Pj := pathProjection R d δ n s t j hj
      have support (k : ℕ) (hk : 0 < k ∧ k < n)
          (u v : LegalPath R n s t)
          (hnon : pathProjection R d δ n s t k hk u v ≠ 0) :
          (∀ r : Fin (n + 1), r.val ≠ k → u.1 r = v.1 r) ∧
            u.1 ⟨k - 1, by omega⟩ = u.1 ⟨k + 1, by omega⟩ := by
        by_contra hn
        apply hnon
        unfold pathProjection
        rw [if_neg hn]
      ext x y
      rw [Matrix.mul_apply, Matrix.mul_apply]
      let H : Prop :=
        (∀ k : Fin (n + 1), k.val ≠ i → k.val ≠ j → x.1 k = y.1 k) ∧
          x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ ∧
          x.1 ⟨j - 1, by omega⟩ = x.1 ⟨j + 1, by omega⟩
      have forward (z : LegalPath R n s t) (hnon : Pi x z * Pj z y ≠ 0) : H := by
        have hix : Pi x z ≠ 0 := by
          intro he
          exact hnon (by rw [he, zero_mul])
        have hjz : Pj z y ≠ 0 := by
          intro he
          exact hnon (by rw [he, mul_zero])
        have hsi := support i hi x z hix
        have hsj := support j hj z y hjz
        refine ⟨?_, hsi.2, ?_⟩
        · intro k hki hkj
          exact (hsi.1 k hki).trans (hsj.1 k hkj)
        · calc
            x.1 ⟨j - 1, by omega⟩ = z.1 ⟨j - 1, by omega⟩ :=
              hsi.1 _ (by simp only [Fin.val_mk]; omega)
            _ = z.1 ⟨j + 1, by omega⟩ := hsj.2
            _ = x.1 ⟨j + 1, by omega⟩ :=
              (hsi.1 _ (by simp only [Fin.val_mk]; omega)).symm
      have reverse (z : LegalPath R n s t) (hnon : Pj x z * Pi z y ≠ 0) : H := by
        have hjx : Pj x z ≠ 0 := by
          intro he
          exact hnon (by rw [he, zero_mul])
        have hiz : Pi z y ≠ 0 := by
          intro he
          exact hnon (by rw [he, mul_zero])
        have hsj := support j hj x z hjx
        have hsi := support i hi z y hiz
        refine ⟨?_, ?_, hsj.2⟩
        · intro k hki hkj
          exact (hsj.1 k hkj).trans (hsi.1 k hki)
        · calc
            x.1 ⟨i - 1, by omega⟩ = z.1 ⟨i - 1, by omega⟩ :=
              hsj.1 _ (by simp only [Fin.val_mk]; omega)
            _ = z.1 ⟨i + 1, by omega⟩ := hsi.2
            _ = x.1 ⟨i + 1, by omega⟩ :=
              (hsj.1 _ (by simp only [Fin.val_mk]; omega)).symm
      by_cases hH : H
      · have make (k : ℕ) (hk : 0 < k ∧ k < n)
            (hprev : x.1 ⟨k - 1, by omega⟩ = y.1 ⟨k - 1, by omega⟩)
            (hnext : x.1 ⟨k + 1, by omega⟩ = y.1 ⟨k + 1, by omega⟩) :
            ∃ z : LegalPath R n s t,
              (∀ r : Fin (n + 1), r.val ≠ k → z.1 r = x.1 r) ∧
                z.1 ⟨k, by omega⟩ = y.1 ⟨k, by omega⟩ := by
          have hleft : R (x.1 ⟨k - 1, by omega⟩) (y.1 ⟨k, by omega⟩) := by
            rw [hprev]
            exact edge_left y k hk
          have hright : R (y.1 ⟨k, by omega⟩) (x.1 ⟨k + 1, by omega⟩) := by
            rw [hnext]
            exact edge_right y k hk
          let z := replacePath R n s t x k hk (y.1 ⟨k, by omega⟩) hleft hright
          refine ⟨z, ?_, ?_⟩
          · intro r hr
            have hne : r ≠ (⟨k, by omega⟩ : Fin (n + 1)) :=
              Fin.ne_of_val_ne (by simpa only [Fin.val_mk] using hr)
            change Function.update x.1 ⟨k, by omega⟩
              (y.1 ⟨k, by omega⟩) r = x.1 r
            exact Function.update_of_ne hne _ _
          · change Function.update x.1 ⟨k, by omega⟩
              (y.1 ⟨k, by omega⟩) ⟨k, by omega⟩ = _
            exact Function.update_self _ _ _
        have hprevI : x.1 ⟨i - 1, by omega⟩ = y.1 ⟨i - 1, by omega⟩ :=
          hH.1 _ (by simp only [Fin.val_mk]; omega)
            (by simp only [Fin.val_mk]; omega)
        have hnextI : x.1 ⟨i + 1, by omega⟩ = y.1 ⟨i + 1, by omega⟩ :=
          hH.1 _ (by simp only [Fin.val_mk]; omega)
            (by simp only [Fin.val_mk]; omega)
        have hprevJ : x.1 ⟨j - 1, by omega⟩ = y.1 ⟨j - 1, by omega⟩ :=
          hH.1 _ (by simp only [Fin.val_mk]; omega)
            (by simp only [Fin.val_mk]; omega)
        have hnextJ : x.1 ⟨j + 1, by omega⟩ = y.1 ⟨j + 1, by omega⟩ :=
          hH.1 _ (by simp only [Fin.val_mk]; omega)
            (by simp only [Fin.val_mk]; omega)
        obtain ⟨zi, hziaway, hzicenter⟩ := make i hi hprevI hnextI
        obtain ⟨zj, hzjaway, hzjcenter⟩ := make j hj hprevJ hnextJ
        have hxi : (∀ r : Fin (n + 1), r.val ≠ i → x.1 r = zi.1 r) ∧
            x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ :=
          ⟨fun r hr => (hziaway r hr).symm, hH.2.1⟩
        have hxj : (∀ r : Fin (n + 1), r.val ≠ j → x.1 r = zj.1 r) ∧
            x.1 ⟨j - 1, by omega⟩ = x.1 ⟨j + 1, by omega⟩ :=
          ⟨fun r hr => (hzjaway r hr).symm, hH.2.2⟩
        have hzjy : (∀ r : Fin (n + 1), r.val ≠ j → zi.1 r = y.1 r) ∧
            zi.1 ⟨j - 1, by omega⟩ = zi.1 ⟨j + 1, by omega⟩ := by
          constructor
          · intro r hrj
            by_cases hri : r.val = i
            · have hr' : r = (⟨i, by omega⟩ : Fin (n + 1)) := Fin.ext hri
              simpa only [hr'] using hzicenter
            · exact (hziaway r hri).trans (hH.1 r hri hrj)
          · calc
              zi.1 ⟨j - 1, by omega⟩ = x.1 ⟨j - 1, by omega⟩ :=
                hziaway _ (by simp only [Fin.val_mk]; omega)
              _ = x.1 ⟨j + 1, by omega⟩ := hH.2.2
              _ = zi.1 ⟨j + 1, by omega⟩ :=
                (hziaway _ (by simp only [Fin.val_mk]; omega)).symm
        have hziy : (∀ r : Fin (n + 1), r.val ≠ i → zj.1 r = y.1 r) ∧
            zj.1 ⟨i - 1, by omega⟩ = zj.1 ⟨i + 1, by omega⟩ := by
          constructor
          · intro r hri
            by_cases hrj : r.val = j
            · have hr' : r = (⟨j, by omega⟩ : Fin (n + 1)) := Fin.ext hrj
              simpa only [hr'] using hzjcenter
            · exact (hzjaway r hrj).trans (hH.1 r hri hrj)
          · calc
              zj.1 ⟨i - 1, by omega⟩ = x.1 ⟨i - 1, by omega⟩ :=
                hzjaway _ (by simp only [Fin.val_mk]; omega)
              _ = x.1 ⟨i + 1, by omega⟩ := hH.2.1
              _ = zj.1 ⟨i + 1, by omega⟩ :=
                (hzjaway _ (by simp only [Fin.val_mk]; omega)).symm
        have uniqI (v : LegalPath R n s t) (hnon : Pi x v * Pj v y ≠ 0) : v = zi := by
          have ha : Pi x v ≠ 0 := by intro he; exact hnon (by rw [he, zero_mul])
          have hb : Pj v y ≠ 0 := by intro he; exact hnon (by rw [he, mul_zero])
          have hsi := support i hi x v ha
          have hsj := support j hj v y hb
          have haway : ∀ r : Fin (n + 1), r.val ≠ i → v.1 r = zi.1 r := by
            intro r hr
            exact (hsi.1 r hr).symm.trans (hziaway r hr).symm
          have hcenter : v.1 ⟨i, by omega⟩ = zi.1 ⟨i, by omega⟩ := by
            calc
              v.1 ⟨i, by omega⟩ = y.1 ⟨i, by omega⟩ :=
                hsj.1 _ (by simp only [Fin.val_mk]; omega)
              _ = zi.1 ⟨i, by omega⟩ := hzicenter.symm
          exact local_ext i hi v zi haway hcenter
        have uniqJ (v : LegalPath R n s t) (hnon : Pj x v * Pi v y ≠ 0) : v = zj := by
          have ha : Pj x v ≠ 0 := by intro he; exact hnon (by rw [he, zero_mul])
          have hb : Pi v y ≠ 0 := by intro he; exact hnon (by rw [he, mul_zero])
          have hsj := support j hj x v ha
          have hsi := support i hi v y hb
          have haway : ∀ r : Fin (n + 1), r.val ≠ j → v.1 r = zj.1 r := by
            intro r hr
            exact (hsj.1 r hr).symm.trans (hzjaway r hr).symm
          have hcenter : v.1 ⟨j, by omega⟩ = zj.1 ⟨j, by omega⟩ := by
            calc
              v.1 ⟨j, by omega⟩ = y.1 ⟨j, by omega⟩ :=
                hsi.1 _ (by simp only [Fin.val_mk]; omega)
              _ = zj.1 ⟨j, by omega⟩ := hzjcenter.symm
          exact local_ext j hj v zj haway hcenter
        have hsumI : (∑ v : LegalPath R n s t, Pi x v * Pj v y) =
            Pi x zi * Pj zi y := by
          apply Finset.sum_eq_single zi
          · intro v _ hv
            by_contra hnon
            exact hv (uniqI v hnon)
          · intro hznot
            exact (hznot (Finset.mem_univ zi)).elim
        have hsumJ : (∑ v : LegalPath R n s t, Pj x v * Pi v y) =
            Pj x zj * Pi zj y := by
          apply Finset.sum_eq_single zj
          · intro v _ hv
            by_contra hnon
            exact hv (uniqJ v hnon)
          · intro hznot
            exact (hznot (Finset.mem_univ zj)).elim
        have hcoefI : Pi x zi = Pi zj y := by
          unfold Pi pathProjection
          rw [if_pos hxi, if_pos hziy, hzicenter,
            hzjaway ⟨i, by omega⟩ (by simp only [Fin.val_mk]; omega),
            hzjaway ⟨i - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)]
        have hcoefJ : Pj zi y = Pj x zj := by
          unfold Pj pathProjection
          rw [if_pos hzjy, if_pos hxj,
            hziaway ⟨j, by omega⟩ (by simp only [Fin.val_mk]; omega),
            hziaway ⟨j - 1, by omega⟩ (by simp only [Fin.val_mk]; omega),
            hzjcenter]
        calc
          (∑ v : LegalPath R n s t, Pi x v * Pj v y) = Pi x zi * Pj zi y := hsumI
          _ = Pj x zj * Pi zj y := by rw [hcoefI, hcoefJ]; ring
          _ = ∑ v : LegalPath R n s t, Pj x v * Pi v y := hsumJ.symm
      · have hleft (z : LegalPath R n s t) : Pi x z * Pj z y = 0 := by
          by_contra hnon
          exact hH (forward z hnon)
        have hright (z : LegalPath R n s t) : Pj x z * Pi z y = 0 := by
          by_contra hnon
          exact hH (reverse z hnon)
        calc
          (∑ z : LegalPath R n s t, Pi x z * Pj z y) = 0 := by
            apply Finset.sum_eq_zero
            intro z _
            exact hleft z
          _ = ∑ z : LegalPath R n s t, Pj x z * Pi z y := by
            symm
            apply Finset.sum_eq_zero
            intro z _
            exact hright z
    intro i j hi hj hdist
    rcases hdist with hij | hji
    · exact ordered i j hi hj hij
    · exact (ordered j i hj hi hji).symm

#print axioms weighted_legal_path_temperley_lieb

end D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
