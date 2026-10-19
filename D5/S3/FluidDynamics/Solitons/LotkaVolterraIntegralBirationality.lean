/- GID: D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lotka–Volterra integrals and the last coordinate generate the rational function field -/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The rational integrals of Marquette–van der Kamp–Quispel, Section 3,
with the distinguished last coordinate. All coordinate indices below are zero-based;
the integral indices remain one-based. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FluidDynamics.Solitons.LotkaVolterraIntegralBirationality

open scoped BigOperators
open Finset

noncomputable section

/-- The rational function field in `n` independent variables over `F`. -/
abbrev FunctionField (F : Type*) [Field F] (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) F)

private def coordPoly (F : Type*) [Field F] (n i : ℕ) : MvPolynomial (Fin n) F :=
  if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0

/-- `x F n i` is the source coordinate `x_{i+1}`; it is zero when `n ≤ i`. -/
def x (F : Type*) [Field F] (n i : ℕ) : FunctionField F n :=
  algebraMap _ _ (coordPoly F n i)

/-- `S F n i` is the source partial sum `x_1 + ⋯ + x_i`. -/
def S (F : Type*) [Field F] (n i : ℕ) : FunctionField F n :=
  ∑ j ∈ range i, x F n j

/-- The number `m = ⌊(n+1)/2⌋` of forward integrals. -/
def half (n : ℕ) : ℕ := (n + 1) / 2

/-- The source `F_k`, for `1 ≤ k ≤ m`. For odd `n`, the factors have zero-based
indices `(2s, 2s-1)`; for even `n`, they have indices `(2s+1, 2s)`. -/
def Fk (F : Type*) [Field F] (n k : ℕ) : FunctionField F n :=
  if n % 2 = 1 then
    S F n (2 * k - 1) * ∏ s ∈ Ico k (half n), x F n (2 * s) / x F n (2 * s - 1)
  else
    S F n (2 * k) * ∏ s ∈ Ico k (half n), x F n (2 * s + 1) / x F n (2 * s)

/-- The reversed source integral `G_k`, for `1 ≤ k ≤ m`. Reindexing its product by
`t = m-1-s` gives the displayed prefix product in both parities. Its initial
sum becomes `H - S_{2(m-k)}`. Integral indices are one-based. -/
def Gk (F : Type*) [Field F] (n k : ℕ) : FunctionField F n :=
  (S F n n - S F n (2 * (half n - k))) *
    ∏ s ∈ range (half n - k), x F n (2 * s) / x F n (2 * s + 1)

/-- The `n` source inputs: `F_1,…,F_m`, then `G_2,…,G_{m-1}` for odd `n`
or `G_1,…,G_{m-1}` for even `n`, followed by `x_n`. -/
def inputs (F : Type*) [Field F] (n : ℕ) (i : Fin n) : FunctionField F n :=
  if i.val < half n then Fk F n (i.val + 1)
  else if i.val + 1 < n then
    Gk F n (i.val - half n + if n % 2 = 1 then 2 else 1)
  else x F n (n - 1)

/-- In every dimension at least two, over every characteristic-zero field, the
specified integrals and last coordinate generate the full rational function field. -/
def claim : Prop := ∀ (F : Type*) [Field F] [CharZero F] (n : ℕ), 2 ≤ n →
  IntermediateField.adjoin F (Set.range (inputs F n)) = ⊤

variable {F : Type*} [Field F] {n : ℕ}

private theorem x_ne_zero {i : ℕ} (hi : i < n) : x F n i ≠ 0 := by
  intro hz
  have hp : coordPoly F n i = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin n) F) (FunctionField F n)
      (hz.trans (map_zero _).symm)
  rw [coordPoly, dite_eq_left hi] at hp
  exact MvPolynomial.X_ne_zero _ hp

private theorem S_succ (i : ℕ) : S F n (i + 1) = S F n i + x F n i :=
  sum_range_succ _ _

private theorem S_interval {a b : ℕ} (h : a ≤ b) :
    S F n b - S F n a = ∑ i ∈ Ico a b, x F n i := by
  have := sum_range_add_sum_Ico (x F n) h
  dsimp [S] at *
  linear_combination -this

private theorem interval_ne_zero {a b : ℕ} (hab : a < b) (hbn : b ≤ n) :
    S F n b - S F n a ≠ 0 := by
  classical
  rw [S_interval (Nat.le_of_lt hab)]
  intro hz
  have hp : (∑ i ∈ Ico a b, coordPoly F n i) = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin n) F) (FunctionField F n)
    simpa only [map_sum, map_zero, x] using hz
  let t : Finset (Fin n) := univ.filter (fun i => a ≤ i.val ∧ i.val < b)
  have hs : (∑ i ∈ t, MvPolynomial.X i : MvPolynomial (Fin n) F) =
      ∑ i ∈ Ico a b, coordPoly F n i := by
    apply sum_bij (fun i _hi => i.val)
    · intro i hi
      exact mem_Ico.mpr (mem_filter.mp hi).2
    · intro i _ j _ he
      exact Fin.ext he
    · intro i hi
      have hin : i < n := by have := mem_Ico.mp hi; omega
      exact ⟨⟨i, hin⟩, mem_filter.mpr ⟨mem_univ _, mem_Ico.mp hi⟩, rfl⟩
    · intro i _hi
      simp only [coordPoly, dite_eq_left i.isLt, Fin.eta]
  have hzero : ∑ i ∈ t, (1 : F) • (MvPolynomial.X i : MvPolynomial (Fin n) F) = 0 := by
    simpa only [one_smul] using hs.trans hp
  have hi : (⟨a, by omega⟩ : Fin n) ∈ t :=
    mem_filter.mpr ⟨mem_univ _, le_rfl, hab⟩
  exact one_ne_zero ((linearIndependent_iff'.mp (MvPolynomial.linearIndependent_X (Fin n) F))
    t (fun _ => 1) hzero _ hi)

private theorem S_ne_zero {i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    S F n i ≠ 0 := by
  have := interval_ne_zero (F := F) (n := n) hi hin
  simpa [S] using this

private def A (F : Type*) [Field F] (n k : ℕ) : FunctionField F n :=
  ∏ s ∈ range k, x F n (2 * s) / x F n (2 * s + 1)

private theorem A_succ (k : ℕ) :
    A F n (k + 1) = A F n k * (x F n (2 * k) / x F n (2 * k + 1)) :=
  prod_range_succ _ _

private theorem A_ne_zero {k : ℕ} (hk : 2 * k ≤ n) : A F n k ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i hi
  have hi := mem_range.mp hi
  exact div_ne_zero (x_ne_zero (by omega)) (x_ne_zero (by omega))

private theorem odd_product {m k : ℕ} (hm : 2 * m < n) (hk : k ≤ m) :
    (∏ s ∈ Ico (k + 1) (m + 1), x F n (2 * s) / x F n (2 * s - 1)) *
      A F n k * x F n (2 * k) = A F n m * x F n (2 * m) := by
  induction m generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ m ih =>
      by_cases hkm : k = m + 1
      · subst k
        simp
      · have hle : k ≤ m := by omega
        rw [prod_Ico_succ_top (by omega : k + 1 ≤ m + 1)]
        have he : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [he, A_succ]
        have hnz := x_ne_zero (F := F) (n := n) (i := 2 * m + 1) (by omega)
        have hh := ih (by omega) hle
        field_simp
        linear_combination x F n (2 * (m + 1)) * hh

private theorem even_product {m k : ℕ} (hm : 2 * m ≤ n) (hk : k ≤ m) :
    (∏ s ∈ Ico k m, x F n (2 * s + 1) / x F n (2 * s)) * A F n m = A F n k := by
  let u := ∏ s ∈ Ico k m, x F n (2 * s) / x F n (2 * s + 1)
  have hc : A F n k * u = A F n m :=
    prod_range_mul_prod_Ico _ hk
  have hinv : (∏ s ∈ Ico k m, x F n (2 * s + 1) / x F n (2 * s)) * u = 1 := by
    rw [show u = ∏ s ∈ Ico k m, x F n (2 * s) / x F n (2 * s + 1) from rfl,
      ← prod_mul_distrib]
    apply prod_eq_one
    intro i hi
    have hi := mem_Ico.mp hi
    have h0 := x_ne_zero (F := F) (n := n) (i := 2 * i) (by omega)
    have h1 := x_ne_zero (F := F) (n := n) (i := 2 * i + 1) (by omega)
    field_simp
  rw [← hc]
  calc
    _ = A F n k * ((∏ s ∈ Ico k m, x F n (2 * s + 1) / x F n (2 * s)) * u) := by ring
    _ = _ := by rw [hinv, mul_one]

private theorem odd_F {m k : ℕ} (hn : n = 2 * m + 1) (hk : k ≤ m) :
    Fk F n (k + 1) * A F n k * x F n (2 * k) =
      S F n (2 * k + 1) * (A F n m * x F n (2 * m)) := by
  have hp := odd_product (F := F) (n := n) (by omega : 2 * m < n) hk
  have hhalf : half n = m + 1 := by dsimp [half]; omega
  have hodd : n % 2 = 1 := by omega
  rw [Fk, ite_eq_left hodd, hhalf, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  linear_combination S F n (2 * k + 1) * hp

private theorem even_F {m k : ℕ} (hn : n = 2 * m) (hk : k ≤ m) :
    Fk F n k * A F n m = S F n (2 * k) * A F n k := by
  have hp := even_product (F := F) (n := n) (by omega : 2 * m ≤ n) hk
  have hhalf : half n = m := by dsimp [half]; omega
  have heven : ¬ n % 2 = 1 := by omega
  rw [Fk, ite_eq_right heven, hhalf]
  linear_combination S F n (2 * k) * hp

private theorem G_eq {m k : ℕ} (hm : half n = m) (hk : k ≤ m) :
    Gk F n (m - k) = (S F n n - S F n (2 * k)) * A F n k := by
  have h : m - (m - k) = k := by omega
  simp only [Gk, hm, h, A]

private theorem F_top (hn : 2 ≤ n) : Fk F n (half n) = S F n n := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  by_cases ho : n % 2 = 1
  · have h : 2 * half n - 1 = n := by dsimp [half]; omega
    simp only [Fk, ite_eq_left ho, h, Ico_self, prod_empty, mul_one]
  · have h : 2 * half n = n := by dsimp [half]; omega
    simp only [Fk, ite_eq_right ho, h, Ico_self, prod_empty, mul_one]

private abbrev generated (F : Type*) [Field F] (n : ℕ) :=
  IntermediateField.adjoin F (Set.range (inputs F n))

private theorem F_mem (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ half n) :
    Fk F n k ∈ generated F n := by
  have hm : half n ≤ n := by dsimp [half]; omega
  have hi : k - 1 < n := by omega
  have he : inputs F n ⟨k - 1, hi⟩ = Fk F n k := by
    rw [inputs, ite_eq_left (by dsimp; omega)]
    congr 1
    change k - 1 + 1 = k
    omega
  rw [← he]
  exact IntermediateField.subset_adjoin F _ ⟨_, rfl⟩

private theorem H_mem (hn : 2 ≤ n) : S F n n ∈ generated F n := by
  rw [← F_top hn]
  exact F_mem hn (by dsimp [half]; omega) le_rfl

private theorem last_mem (hn : 2 ≤ n) : x F n (n - 1) ∈ generated F n := by
  have hi : n - 1 < n := by omega
  have hm : half n ≤ n - 1 := by dsimp [half]; omega
  have he : inputs F n ⟨n - 1, hi⟩ = x F n (n - 1) := by
    rw [inputs, ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega)]
  rw [← he]
  exact IntermediateField.subset_adjoin F _ ⟨_, rfl⟩

private theorem G_mem (hn : 2 ≤ n) {k : ℕ}
    (hk : (if n % 2 = 1 then 2 else 1) ≤ k) (hkm : k < half n) :
    Gk F n k ∈ generated F n := by
  let b := if n % 2 = 1 then 2 else 1
  have hb : 1 ≤ b ∧ b ≤ 2 := by dsimp [b]; split <;> omega
  have hm : 2 * half n + 1 - b = n := by
    dsimp [half, b]
    split <;> omega
  let j := half n + k - b
  have hj : j < n := by dsimp [j]; omega
  have he : inputs F n ⟨j, hj⟩ = Gk F n k := by
    rw [inputs, ite_eq_right (by dsimp [j]; omega), ite_eq_left (by dsimp [j]; omega)]
    congr 1
    change j - half n + b = k
    dsimp [j]
    omega
  rw [← he]
  exact IntermediateField.subset_adjoin F _ ⟨_, rfl⟩

private theorem odd_C {m : ℕ} (hn : n = 2 * m + 1) :
    Fk F n 1 = A F n m * x F n (2 * m) := by
  have hh := odd_F (F := F) hn (k := 0) (by omega)
  simp only [Nat.zero_add, Nat.mul_zero, show A F n 0 = 1 by simp [A], mul_one,
    S, sum_range_one] at hh
  change Fk F n 1 * x F n 0 = x F n 0 * (A F n m * x F n (2 * m)) at hh
  apply mul_right_cancel₀ (x_ne_zero (by omega : 0 < n))
  linear_combination hh

private theorem odd_G_mem {m k : ℕ} (hn : n = 2 * m + 1) (hn2 : 2 ≤ n)
    (hk : 1 ≤ k) (hkm : k ≤ m + 1) : Gk F n k ∈ generated F n := by
  have hm : half n = m + 1 := by dsimp [half]; omega
  by_cases htop : k = m + 1
  · subst k
    simpa only [Gk, hm, Nat.sub_self, Nat.mul_zero, S, range_zero, sum_empty,
      sub_zero, prod_empty, mul_one] using H_mem (F := F) hn2
  by_cases hone : k = 1
  · subst k
    have he : Gk F n 1 = Fk F n 1 := by
      rw [odd_C hn]
      have hs := S_succ (F := F) (n := n) (2 * m)
      rw [← hn] at hs
      rw [Gk, hm, show m + 1 - 1 = m by omega, hs]
      change (S F n (2 * m) + x F n (2 * m) - S F n (2 * m)) * A F n m = _
      ring
    rw [he]
    exact F_mem hn2 le_rfl (by omega)
  exact G_mem hn2 (by rw [ite_eq_left (by omega : n % 2 = 1)]; omega) (by omega)

private theorem recover_previous (L : IntermediateField F (FunctionField F n))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) {d : FunctionField F n}
    (hd : d * x F n (i - 1) = S F n (i - 1) * (S F n n - S F n i))
    (hmH : S F n n ∈ L) (hmd : d ∈ L) (hmi : S F n i ∈ L) :
    S F n (i - 1) ∈ L := by
  have hs : S F n i = S F n (i - 1) + x F n (i - 1) := by
    have hh := S_succ (F := F) (n := n) (i - 1)
    rwa [show i - 1 + 1 = i by omega] at hh
  have hprod : (S F n n - S F n i + d) * x F n (i - 1) =
      (S F n n - S F n i) * S F n i := by
    linear_combination hd - (S F n n - S F n i) * hs
  have hden : S F n n - S F n i + d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact (mul_ne_zero (interval_ne_zero hin le_rfl)
      (S_ne_zero (by omega) (by omega))) hprod.symm
  have he : S F n (i - 1) = d * S F n i / (S F n n - S F n i + d) := by
    apply (eq_div_iff hden).2
    linear_combination -hd - d * hs
  rw [he]
  exact L.div_mem (L.mul_mem hmd hmi) (L.add_mem (L.sub_mem hmH hmi) hmd)

private theorem odd_d_odd {m k : ℕ} (hn : n = 2 * m + 1) (hk : k ≤ m) :
    (Fk F n (k + 1) * Gk F n (m + 1 - k) /
      (A F n m * x F n (2 * m)) - S F n n) * x F n (2 * k) =
      S F n (2 * k) * (S F n n - S F n (2 * k + 1)) := by
  have hm : half n = m + 1 := by dsimp [half]; omega
  rw [G_eq hm (by omega : k ≤ m + 1)]
  have hf := odd_F (F := F) hn hk
  rw [S_succ] at hf ⊢
  have ham := A_ne_zero (F := F) (n := n) (k := m) (by omega)
  have hxm := x_ne_zero (F := F) (n := n) (i := 2 * m) (by omega)
  field_simp [ham, hxm]
  linear_combination (S F n n - S F n (2 * k)) * hf

private theorem odd_d_even {m k : ℕ} (hn : n = 2 * m + 1) (hk : k < m) :
    (Fk F n (k + 1) * Gk F n (m - k) /
      (A F n m * x F n (2 * m))) * x F n (2 * k + 1) =
      S F n (2 * k + 1) * (S F n n - S F n (2 * k + 2)) := by
  have hm : half n = m + 1 := by dsimp [half]; omega
  have hj : m - k = m + 1 - (k + 1) := by omega
  rw [hj, G_eq hm (by omega : k + 1 ≤ m + 1), A_succ]
  have hf := odd_F (F := F) hn (by omega : k ≤ m)
  have hx := x_ne_zero (F := F) (n := n) (i := 2 * k + 1) (by omega)
  have he : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [he]
  have ham := A_ne_zero (F := F) (n := n) (k := m) (by omega)
  have hxm := x_ne_zero (F := F) (n := n) (i := 2 * m) (by omega)
  field_simp [ham, hxm]
  linear_combination (S F n n - S F n (2 * k + 2)) * hf

private theorem odd_coordinates {m : ℕ} (hn : n = 2 * m + 1) (hn2 : 2 ≤ n) :
    ∀ i < n, x F n i ∈ generated F n := by
  let L := generated F n
  have hm : half n = m + 1 := by dsimp [half]; omega
  have hH : S F n n ∈ L := H_mem hn2
  have hC : A F n m * x F n (2 * m) ∈ L := by
    rw [← odd_C hn]
    exact F_mem hn2 le_rfl (by omega)
  have hd (i : ℕ) (hi : 2 ≤ i) (hin : i < n) :
      ∃ d ∈ L, d * x F n (i - 1) = S F n (i - 1) * (S F n n - S F n i) := by
    by_cases ho : i % 2 = 1
    · let k := i / 2
      have he : i = 2 * k + 1 := by dsimp [k]; omega
      have hk : k ≤ m := by omega
      have hf : Fk F n (k + 1) ∈ L := F_mem hn2 (by omega) (by omega)
      have hg : Gk F n (m + 1 - k) ∈ L := odd_G_mem hn hn2 (by omega) (by omega)
      refine ⟨_, L.sub_mem (L.div_mem (L.mul_mem hf hg) hC) hH, ?_⟩
      simpa only [he, show 2 * k + 1 - 1 = 2 * k by omega] using odd_d_odd hn hk
    · let k := i / 2 - 1
      have he : i = 2 * k + 2 := by dsimp [k]; omega
      have hk : k < m := by omega
      have hf : Fk F n (k + 1) ∈ L := F_mem hn2 (by omega) (by omega)
      have hg : Gk F n (m - k) ∈ L := odd_G_mem hn hn2 (by omega) (by omega)
      refine ⟨_, L.div_mem (L.mul_mem hf hg) hC, ?_⟩
      simpa only [he, show 2 * k + 2 - 1 = 2 * k + 1 by omega] using odd_d_even hn hk
  have hS : ∀ i, i ≤ n - 1 → 1 ≤ i → S F n i ∈ L := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
        intro _
        have he : S F n (n - 1) = S F n n - x F n (n - 1) := by
          have hs := S_succ (F := F) (n := n) (n - 1)
          rw [show n - 1 + 1 = n by omega] at hs
          linear_combination -hs
        rw [he]
        exact L.sub_mem hH (last_mem hn2)
    | of_succ j hj ih =>
        intro hj0
        obtain ⟨d, hdm, hde⟩ := hd (j + 1) (by omega) (by omega)
        simpa only [Nat.add_sub_cancel] using
          recover_previous L (by omega : 1 ≤ j + 1) (by omega : j + 1 < n)
            hde hH hdm (ih (by omega))
  intro i hi
  have hp : S F n i ∈ L := by
    by_cases hz : i = 0
    · subst i; simp [S]
    · exact hS i (by omega) (by omega)
  have hq : S F n (i + 1) ∈ L := by
    by_cases he : i + 1 = n
    · rw [he]; exact hH
    · exact hS (i + 1) (by omega) (by omega)
  have he : x F n i = S F n (i + 1) - S F n i := by rw [S_succ]; ring
  rw [he]
  exact L.sub_mem hq hp

private theorem even_P_mem {m : ℕ} (hn : n = 2 * m) (hm2 : 2 ≤ m) :
    (A F n m)⁻¹ ∈ generated F n := by
  let L := generated F n
  have hn2 : 2 ≤ n := by omega
  have hm : half n = m := by dsimp [half]; omega
  let u := x F n (2 * m - 1)
  let v := x F n (2 * m - 2)
  let t := S F n (2 * (m - 1))
  let a := A F n (m - 1)
  let b := A F n m
  let f := Fk F n (m - 1)
  let H := S F n n
  have hb : b ≠ 0 := A_ne_zero (by omega)
  have hu : u ≠ 0 := x_ne_zero (by omega)
  have hs : H = t + v + u := by
    have h1 := S_succ (F := F) (n := n) (2 * m - 2)
    have h2 := S_succ (F := F) (n := n) (2 * m - 1)
    have he1 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
    have he2 : 2 * m - 1 + 1 = n := by omega
    have he3 : 2 * m - 2 = 2 * (m - 1) := by omega
    rw [he1] at h1
    conv_rhs at h1 => lhs; rw [he3]
    rw [he2, h1] at h2
    exact h2
  have ha : b * u = a * v := by
    have hh := A_succ (F := F) (n := n) (m - 1)
    rw [show m - 1 + 1 = m by omega,
      show 2 * (m - 1) = 2 * m - 2 by omega,
      show 2 * m - 2 + 1 = 2 * m - 1 by omega] at hh
    change b = a * (v / u) at hh
    rw [hh]
    field_simp
  have hf : f * b = t * a := even_F hn (by omega : m - 1 ≤ m)
  have hg : Gk F n 1 = (H - t) * a := by
    have hh := G_eq (F := F) hm (by omega : m - 1 ≤ m)
    simpa only [show m - (m - 1) = 1 by omega] using hh
  have hid : Gk F n 1 * (H - u) = b * u * (H + f) := by
    rw [hg, hs]
    linear_combination -(t + v + u) * ha - u * hf
  have hG : Gk F n 1 ≠ 0 := by
    rw [hg]
    exact mul_ne_zero (interval_ne_zero (by omega) le_rfl) (A_ne_zero (by omega))
  have hHu : H - u ≠ 0 := by
    have he : H - u = S F n (n - 1) := by
      have hh := S_succ (F := F) (n := n) (n - 1)
      rw [show n - 1 + 1 = n by omega] at hh
      change S F n n - x F n (2 * m - 1) = _
      rw [show 2 * m - 1 = n - 1 by omega]
      linear_combination hh
    rw [he]
    exact S_ne_zero (by omega) (by omega)
  have he : b⁻¹ = u * (H + f) / (Gk F n 1 * (H - u)) := by
    apply (eq_div_iff (mul_ne_zero hG hHu)).2
    rw [hid]
    field_simp
  change b⁻¹ ∈ L
  rw [he]
  have hmu : u ∈ L := by
    change x F n (2 * m - 1) ∈ L
    rw [show 2 * m - 1 = n - 1 by omega]
    exact last_mem hn2
  have hmf : f ∈ L := F_mem hn2 (by omega) (by omega)
  have hmH : H ∈ L := H_mem hn2
  have hmG : Gk F n 1 ∈ L :=
    G_mem hn2 (by rw [ite_eq_right (by omega : ¬n % 2 = 1)]) (by omega)
  exact L.div_mem (L.mul_mem hmu (L.add_mem hmH hmf))
    (L.mul_mem hmG (L.sub_mem hmH hmu))

private theorem even_sums_mem {m : ℕ} (hn : n = 2 * m) (hm2 : 2 ≤ m)
    {k : ℕ} (hk : k ≤ m) : S F n (2 * k) ∈ generated F n := by
  let L := generated F n
  have hn2 : 2 ≤ n := by omega
  have hm : half n = m := by dsimp [half]; omega
  by_cases h0 : k = 0
  · subst k; simp [S]
  by_cases htop : k = m
  · subst k; rw [← hn]; exact H_mem hn2
  let b := A F n m
  let a := A F n k
  let f := Fk F n k
  let g := Gk F n (m - k)
  let H := S F n n
  let T := S F n (2 * k)
  let d := f + b⁻¹ * g
  have hb : b ≠ 0 := A_ne_zero (by omega)
  have hf : f * b = T * a := even_F hn hk
  have hg : g = (H - T) * a := G_eq hm hk
  have hd : d * b = H * a := by
    dsimp [d]
    rw [add_mul, hf, hg]
    field_simp
    ring
  have hdn : d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd
    exact (mul_ne_zero (S_ne_zero (by omega) le_rfl) (A_ne_zero (by omega))) hd.symm
  have he : T = H * f / d := by
    apply (eq_div_iff hdn).2
    apply mul_right_cancel₀ hb
    linear_combination T * hd - H * hf
  change T ∈ L
  rw [he]
  have hmf : f ∈ L := F_mem hn2 (by omega) (by omega)
  have hmg : g ∈ L := G_mem hn2
    (by rw [ite_eq_right (by omega : ¬n % 2 = 1)]; omega) (by omega)
  exact L.div_mem (L.mul_mem (H_mem hn2) hmf)
    (L.add_mem hmf (L.mul_mem (even_P_mem hn hm2) hmg))

private theorem even_A_mem {m : ℕ} (hn : n = 2 * m) (hm2 : 2 ≤ m)
    {k : ℕ} (hk : k ≤ m) : A F n k ∈ generated F n := by
  let L := generated F n
  have hm : half n = m := by dsimp [half]; omega
  by_cases h0 : k = 0
  · subst k; simp [A]
  by_cases htop : k = m
  · subst k
    simpa only [inv_inv] using L.inv_mem (even_P_mem hn hm2)
  have he : A F n k = Gk F n (m - k) / (S F n n - S F n (2 * k)) := by
    apply (eq_div_iff (interval_ne_zero (by omega : 2 * k < n) le_rfl)).2
    rw [G_eq hm hk]
    ring
  rw [he]
  exact L.div_mem (G_mem (by omega)
    (by rw [ite_eq_right (by omega : ¬n % 2 = 1)]; omega) (by omega))
    (L.sub_mem (H_mem (by omega)) (even_sums_mem hn hm2 hk))

private theorem even_coordinates {m : ℕ} (hn : n = 2 * m) (hn2 : 2 ≤ n) :
    ∀ i < n, x F n i ∈ generated F n := by
  let L := generated F n
  by_cases hm1 : m = 1
  · subst m
    have he : n = 2 := by omega
    intro i hi
    have hlast : x F n 1 ∈ L := by simpa only [he] using last_mem (F := F) hn2
    have hfirst : x F n 0 ∈ L := by
      have hh := L.sub_mem (H_mem (F := F) hn2) hlast
      simpa only [he, S, sum_range_succ, sum_range_zero, zero_add,
        add_sub_cancel_right] using hh
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact hfirst
    · exact hlast
  have hm2 : 2 ≤ m := by omega
  intro i hi
  let k := i / 2
  have hk : k < m := by dsimp [k]; omega
  let a := A F n k
  let b := A F n (k + 1)
  let v := x F n (2 * k)
  let u := x F n (2 * k + 1)
  let t := S F n (2 * (k + 1)) - S F n (2 * k)
  have ht : t = v + u := by
    have h1 := S_succ (F := F) (n := n) (2 * k)
    have h2 := S_succ (F := F) (n := n) (2 * k + 1)
    have he : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    dsimp [t, v, u]
    rw [he, h2, h1]
    ring
  have hu : u ≠ 0 := x_ne_zero (by omega)
  have ha : b * u = a * v := by
    change A F n (k + 1) * u = a * v
    rw [A_succ]
    change (a * (v / u)) * u = a * v
    field_simp
  have hd : (b + a) * u = a * t := by rw [ht]; linear_combination ha
  have hdn : b + a ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd
    exact (mul_ne_zero (A_ne_zero (by omega))
      (interval_ne_zero (by omega) (by omega))) hd.symm
  have he : u = t * a / (b + a) := by
    apply (eq_div_iff hdn).2
    linear_combination hd
  have hma : a ∈ L := even_A_mem hn hm2 (by omega)
  have hmb : b ∈ L := even_A_mem hn hm2 (by omega)
  have hmt : t ∈ L := L.sub_mem (even_sums_mem hn hm2 (by omega))
    (even_sums_mem hn hm2 (by omega))
  have hmu : u ∈ L := by rw [he]; exact L.div_mem (L.mul_mem hmt hma) (L.add_mem hmb hma)
  have hmv : v ∈ L := by
    have he : v = t - u := by rw [ht]; ring
    rw [he]
    exact L.sub_mem hmt hmu
  by_cases hmod : i % 2 = 0
  · have he : i = 2 * k := by dsimp [k]; omega
    rw [he]; exact hmv
  · have he : i = 2 * k + 1 := by dsimp [k]; omega
    rw [he]; exact hmu

/-- The specified Lotka–Volterra integrals and final coordinate generate the field. -/
theorem result : claim := by
  intro F _ _ n hn
  let L := generated F n
  have hx : ∀ i < n, x F n i ∈ L := by
    by_cases ho : n % 2 = 1
    · exact odd_coordinates (by omega : n = 2 * (n / 2) + 1) hn
    · exact even_coordinates (by omega : n = 2 * (n / 2)) hn
  have hp (p : MvPolynomial (Fin n) F) : algebraMap _ (FunctionField F n) p ∈ L := by
    induction p using MvPolynomial.induction_on with
    | C a =>
        simpa only [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F)
          (FunctionField F n), MvPolynomial.algebraMap_eq] using L.algebraMap_mem a
    | add p q hpm hqm => simpa only [map_add] using L.add_mem hpm hqm
    | mul_X p i hpm =>
        rw [map_mul]
        apply L.mul_mem hpm
        have hh := hx i.val i.isLt
        simpa only [x, coordPoly, dite_eq_left i.isLt, Fin.eta] using hh
  apply top_unique
  intro z _
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) F) z
  exact L.div_mem (hp p) (hp q)

end

end D5.S3.FluidDynamics.Solitons.LotkaVolterraIntegralBirationality
