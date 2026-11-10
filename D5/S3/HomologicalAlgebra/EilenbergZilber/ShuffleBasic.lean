/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite lattice shuffles, inversion signs and zero-direction shuffles. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import Mathlib.Tactic -- shake: keep
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Order.Fin.Basic

/-!
# Shuffles

A `(p, q)`-shuffle is an injective monotone map `Fin (p + q + 1) → Fin (p + 1) × Fin (q + 1)`,
i.e. a lattice path from `(0, 0)` to `(p, q)` taking unit left and right steps. This file develops
the combinatorics of shuffles needed for the Eilenberg–Zilber shuffle map: inversion counts and
signs, the boundary decomposition of a shuffle into insertions of left/right steps, and the
sign-reversing involution `swapDiagonalSteps` that cancels the diagonal boundary terms.
-/

@[expose] public section

noncomputable section

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

/-! ### Shuffles -/


/-- The finite chain object `0 ≤ 1 ≤ ··· ≤ k` in `PoSet`, represented by `Fin (k+1)`. -/
abbrev Index (k : ℕ) := Fin (k + 1)

/-- A `(p,q)`-shuffle as an injective monotone map
`Index (p + q) ⟶ Index p × Index q` in `PoSet`. -/
abbrev Shuffle (p q : ℕ) :=
  { φ : Index (p + q) →o (Index p × Index q) // Function.Injective φ }

namespace Shuffle

/-- There are finitely many (p,q)-shuffles: exactly `Nat.choose (p + q) p`. -/
noncomputable instance instFintype (p q : ℕ) : Fintype (Shuffle p q) := by
  classical
  have : Finite (Index (p + q) →o (Index p × Index q)) := by
    classical
    refine Finite.of_injective (fun f : Index (p + q) →o (Index p × Index q) => f.toFun) ?_
    intro f g h
    ext x
    repeat simp at h; simp [h]
  exact Fintype.ofFinite (Shuffle p q)

/-- The **number of inversions** of a shuffle. -/
def invCount {p q : ℕ} (μ : Shuffle p q) : ℕ :=
  ∑ r : Fin (p + q),
    if ((μ.1 (Fin.castSucc r)).1 < (μ.1 (Fin.succ r)).1) then
      ((μ.1 (Fin.castSucc r)).2).1
    else 0

/-- The sign of a shuffle: `(-1)^k` where `k` is the number of inversions. -/
def sign {p q : ℕ} (μ : Shuffle p q) : ℤ :=
  (-1 : ℤ) ^ μ.invCount

/-- Swap the two coordinates of a shuffle, yielding a `(q,p)`-shuffle. -/
def swap {p q : ℕ} (μ : Shuffle p q) : Shuffle q p := by
  classical
  let e : Index (q + p) ≃o Index (p + q) :=
    Fin.castOrderIso (by simp [Nat.add_comm, Nat.add_assoc])
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun x => (μ.1 (e x)).swap
        monotone' := ?_ }
    intro a b hab
    have h := μ.1.monotone (e.monotone hab)
    rcases h with ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · intro a b hab
    have hab' : μ.1 (e a) = μ.1 (e b) := Prod.swap_injective hab
    have : e a = e b := μ.2 hab'
    exact e.injective this

@[grind =, simp]
theorem swap_swap {p q : ℕ} (μ : Shuffle p q) : swap (swap μ) = μ := by
  classical
  apply Subtype.ext
  ext x
  repeat simp [swap]

/-- Swapping coordinates gives an equivalence `Shuffle p q ≃ Shuffle q p`. -/
def swapEquiv (p q : ℕ) : Shuffle p q ≃ Shuffle q p where
  toFun := swap
  invFun := swap
  left_inv μ := by simp
  right_inv μ := by simp

/-! #### Lattice path structure -/

/-- The coordinate sum `fst + snd` is strictly monotone along a shuffle path. -/
private lemma coordSum_lt {p q : ℕ} (u : Shuffle p q)
    {i j : Fin (p + q + 1)} (hij : i < j) :
    (u.1 i).1.val + (u.1 i).2.val < (u.1 j).1.val + (u.1 j).2.val := by
  have hmono := u.1.monotone (le_of_lt hij)
  have hinj : u.1 i ≠ u.1 j := fun h => (ne_of_lt hij) (u.2 h)
  obtain ⟨h1, h2⟩ := hmono
  -- Extract val-level inequalities for omega
  rcases Nat.lt_or_eq_of_le h1 with h1' | h1'
  · grind only []
  · rcases Nat.lt_or_eq_of_le h2 with h2' | h2'
    · grind only []
    · exact absurd (Prod.ext (Fin.ext h1') (Fin.ext h2')) hinj

/-- At every position `r`, the coordinate sum equals `r.val`. -/
@[grind =]
lemma coordSum_eq {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q + 1)) :
    (u.1 r).1.val + (u.1 r).2.val = r.val := by
  have castSucc_lt_succ : ∀ i : Fin (p + q), i.castSucc < i.succ := by
    intro i; simp [Fin.lt_def]
  apply le_antisymm
  · -- Upper bound by reverse induction: g(last) ≤ p + q, g(r) < g(r+1) ≤ r+1
    induction r using Fin.reverseInduction with
    | last =>
      have := (u.1 (Fin.last (p + q))).1.isLt
      have := (u.1 (Fin.last (p + q))).2.isLt
      simp [Fin.val_last]; omega
    | cast i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega
  · -- Lower bound by forward induction: g(0) ≥ 0, g(r+1) > g(r) ≥ r
    induction r using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega

/-- At each step of a shuffle, exactly one coordinate increases by 1. -/
lemma shuffle_step {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    ((u.1 r.castSucc).1.val + 1 = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val = (u.1 r.succ).2.val) ∨
    ((u.1 r.castSucc).1.val = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val + 1 = (u.1 r.succ).2.val) := by
  have hmono := u.1.monotone (show r.castSucc ≤ r.succ from by simp [Fin.le_def])
  obtain ⟨h1, h2⟩ := hmono
  have h1v : (u.1 r.castSucc).1.val ≤ (u.1 r.succ).1.val := h1
  have h2v : (u.1 r.castSucc).2.val ≤ (u.1 r.succ).2.val := h2
  have hsum1 := coordSum_eq u r.castSucc
  have hsum2 := coordSum_eq u r.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at hsum1 hsum2
  omega

/-- First coordinate increases iff second doesn't at each step. -/
lemma shuffle_fst_lt_iff_not_snd_lt {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.castSucc).1.val < (u.1 r.succ).1.val ↔
    ¬ ((u.1 r.castSucc).2.val < (u.1 r.succ).2.val) := by
  rcases shuffle_step u r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega


/-- A shuffle path crosses every intermediate `snd`-level: for `i + 1 ≤ q` there is a step `a`
that is a **`q`-step at level `i`** — the second coordinate goes `i → i + 1` while the first
coordinate is fixed. This is the degeneracy analog of the face-insertion step lemmas, and is what
lets the Eilenberg–Zilber map carry a one-direction degeneracy to a diagonal one. -/
lemma exists_snd_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ q) :
    ∃ a : Fin (p + q), (μ.1 a.castSucc).2.val = i ∧ (μ.1 a.succ).2.val = i + 1 ∧
      (μ.1 a.castSucc).1 = (μ.1 a.succ).1 := by
  classical
  let S : Finset (Fin (p + q + 1)) := Finset.univ.filter (fun r => i + 1 ≤ (μ.1 r).2.val)
  have hlast : Fin.last (p + q) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := coordSum_eq μ (Fin.last (p + q))
    have h1 := (μ.1 (Fin.last (p + q))).1.isLt
    have h2 := (μ.1 (Fin.last (p + q))).2.isLt
    simp only [Fin.val_last] at hsum
    omega
  have hSne : S.Nonempty := ⟨_, hlast⟩
  set a0 := S.min' hSne with ha0_def
  have ha0 : i + 1 ≤ (μ.1 a0).2.val := by
    grind [Finset.min'_mem]
  have ha0pos : 0 < a0.val := by
    refine Or.resolve_left (Nat.eq_zero_or_pos a0.val) ?_
    grind [(coordSum_eq μ a0)]
  set a : Fin (p + q) := ⟨a0.val - 1, by have := a0.isLt; omega⟩ with ha_def
  have ha_val : a.val = a0.val - 1 := rfl
  have hsucc : a.succ = a0 := Fin.ext (by rw [Fin.val_succ, ha_val]; omega)
  have hcast_lt : a.castSucc < a0 := by
    rw [Fin.lt_def, Fin.val_castSucc, ha_val]; omega
  have hcast_notin : a.castSucc ∉ S := fun h => absurd (S.min'_le _ h) (not_le.mpr hcast_lt)
  have hcast_le : (μ.1 a.castSucc).2.val ≤ i := by
    by_contra h
    exact hcast_notin
      (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hsucc_ge : i + 1 ≤ (μ.1 a.succ).2.val := by rw [hsucc]; grind [Finset.min'_mem]
  rcases shuffle_step μ a with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact absurd hs (by omega)
  · exact ⟨a, by omega, by omega, Fin.ext hf⟩

/-- The first-coordinate analog of `exists_snd_step`: for `i + 1 ≤ p` there is a **`p`-step at
level `i`** — the first coordinate goes `i → i + 1` while the second coordinate is fixed. Used for
the outer (horizontal) Eilenberg–Zilber degeneracy kill. -/
lemma exists_fst_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ p) :
    ∃ a : Fin (p + q), (μ.1 a.castSucc).1.val = i ∧ (μ.1 a.succ).1.val = i + 1 ∧
      (μ.1 a.castSucc).2 = (μ.1 a.succ).2 := by
  classical
  let S : Finset (Fin (p + q + 1)) := Finset.univ.filter (fun r => i + 1 ≤ (μ.1 r).1.val)
  have hlast : Fin.last (p + q) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := coordSum_eq μ (Fin.last (p + q))
    have h1 := (μ.1 (Fin.last (p + q))).1.isLt
    have h2 := (μ.1 (Fin.last (p + q))).2.isLt
    simp only [Fin.val_last] at hsum
    omega
  have hSne : S.Nonempty := ⟨_, hlast⟩
  set a0 := S.min' hSne with ha0_def
  have ha0S : a0 ∈ S := S.min'_mem hSne
  have ha0 : i + 1 ≤ (μ.1 a0).1.val := by
    have h := ha0S; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
  have ha0pos : 0 < a0.val := by
    rcases Nat.eq_zero_or_pos a0.val with h | h
    · exfalso
      have hsum := coordSum_eq μ a0
      rw [h] at hsum
      omega
    · exact h
  set a : Fin (p + q) := ⟨a0.val - 1, by have := a0.isLt; omega⟩ with ha_def
  have ha_val : a.val = a0.val - 1 := rfl
  have hsucc : a.succ = a0 := Fin.ext (by rw [Fin.val_succ, ha_val]; omega)
  have hcast_lt : a.castSucc < a0 := by
    rw [Fin.lt_def, Fin.val_castSucc, ha_val]; omega
  have hcast_notin : a.castSucc ∉ S := fun h => absurd (S.min'_le _ h) (not_le.mpr hcast_lt)
  have hcast_le : (μ.1 a.castSucc).1.val ≤ i := by
    by_contra h
    exact hcast_notin
      (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hsucc_ge : i + 1 ≤ (μ.1 a.succ).1.val := by rw [hsucc]; exact ha0
  rcases shuffle_step μ a with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact ⟨a, by omega, by omega, Fin.ext hs⟩
  · exact absurd hf (by omega)

/-- The swap of a shuffle at position x gives the swapped coordinates of u at the same position. -/
lemma swap_apply_fst {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).1.val = (u.1 (x.cast (by omega))).2.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

private lemma swap_apply_snd {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).2.val = (u.1 (x.cast (by omega))).1.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

/-- Reindex swap's invCount to a sum over `Fin (p + q)` in terms of u's coordinates. -/
private lemma invCount_swap_eq {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ s : Fin (p + q),
      if (u.1 (Fin.castSucc s)).2 < (u.1 (Fin.succ s)).2
      then (u.1 (Fin.castSucc s)).1.val
      else 0 := by
  simp only [invCount]
  -- Establish Fin-level equalities for swap's coordinates
  have hswap1 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).1 = (u.1 (x.cast (by omega))).2 :=
    fun x => Fin.ext (swap_apply_fst u x)
  have hswap2 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).2 = (u.1 (x.cast (by omega))).1 :=
    fun x => Fin.ext (swap_apply_snd u x)
  simp_rw [hswap1, hswap2]
  -- Reindex from Fin(q+p) to Fin(p+q) via finCongr
  refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun s => ?_
  have hcs : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.castSucc =
             (finCongr (show q + p = p + q from by omega) s).castSucc :=
    Fin.ext (by simp [finCongr])
  have hss : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.succ =
             (finCongr (show q + p = p + q from by omega) s).succ :=
    Fin.ext (by simp [finCongr])
  simp_rw [hcs, hss]

/- Total inversions of a shuffle and its swap equal `p * q`. -/
section

/-
A shuffle path starts at (0,0).
-/
lemma apply_zero {p q : ℕ} (u : Shuffle p q) : u.1 0 = (0, 0) := by
  have h := Nat.add_eq_zero_iff.mp (coordSum_eq u 0)
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-
A shuffle path ends at (p,q).
-/
lemma apply_last {p q : ℕ} (u : Shuffle p q) : u.1 (Fin.last (p + q)) = (Fin.last p,
    Fin.last q) := by
  have hsum := coordSum_eq u (Fin.last (p + q))
  have h1 := (u.1 (Fin.last (p + q))).1.isLt
  have h2 := (u.1 (Fin.last (p + q))).2.isLt
  exact Prod.ext (Fin.ext (by simp only [Fin.val_last] at hsum ⊢; omega))
    (Fin.ext (by simp only [Fin.val_last] at hsum ⊢; omega))

/-
Express invCount as a sum of y * dx.
-/
lemma invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    u.invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1
        r.castSucc).1.val) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have := shuffle_step u i;
      grind only []

/-
Express swap.invCount as a sum of x * dy.
-/
lemma swap_invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1
        r.castSucc).2.val) := by
      rw [ invCount_swap_eq, Finset.sum_congr rfl ];
      intro x hx; split_ifs <;> simp_all +decide [] ;
      have := shuffle_step u x;
      grind only []

/-
The change in the product of coordinates equals y*dx + x*dy.
-/
lemma xy_diff_eq_sum_mixed {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.succ).1.val * (u.1 r.succ).2.val - (u.1 r.castSucc).1.val * (u.1 r.castSucc).2.val =
    (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val) +
    (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val) := by
  rcases shuffle_step u r with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · rw [← hf, ← hs]
    simp only [Nat.add_mul, one_mul, Nat.add_sub_cancel_left, Nat.sub_self,
      mul_one, mul_zero, add_zero]
  · rw [← hf, ← hs]
    simp only [Nat.mul_add, mul_one, Nat.add_sub_cancel_left, Nat.sub_self,
      mul_zero, zero_add]

end

lemma invCount_add_invCount_swap {p q : ℕ} (u : Shuffle p q) :
    u.invCount + (u.swap).invCount = p * q := by
  -- The sum of the differences in the product of coordinates is a telescoping sum, so most terms
  -- cancel out.
  have h_telescope : ∑ r : Fin (p + q), ((u.1 (Fin.succ r)).1.val * (u.1 (Fin.succ r)).2.val - (u.1
      (Fin.castSucc r)).1.val * (u.1 (Fin.castSucc r)).2.val) = (u.1 (Fin.last (p +
      q))).1.val * (u.1 (Fin.last (p + q))).2.val - (u.1 0).1.val * (u.1 0).2.val := by
    have h_telescope_int : ∀ (n : ℕ) (f : Fin (n + 1) → ℤ),
        ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
      intro n f
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.succ_castSucc]
        rw [ih (fun i => f i.castSucc)]
        simp
    have h_telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ),
        (∀ i : Fin n, f i.castSucc ≤ f i.succ) →
        ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
      intro n f hf
      have hmono : Monotone f := Fin.monotone_iff_le_succ.mpr hf
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub (hmono (Fin.zero_le _)), Nat.cast_sum]
      simp_rw [Nat.cast_sub (hf _)]
      exact h_telescope_int n (fun i => (f i : ℤ))
    convert h_telescope ( p + q ) ( fun i => ( u.1 i ).1.val * ( u.1 i ).2.val ) _ using 1;
    exact fun i => mul_le_mul' ( u.1.monotone ( Nat.le_succ _ ) |>.1 ) ( u.1.monotone ( Nat.le_succ
        _ ) |>.2 );
  convert h_telescope using 1;
  · rw [ Shuffle.invCount_eq_sum_mul_diff, Shuffle.swap_invCount_eq_sum_mul_diff,
        ← Finset.sum_add_distrib ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ Shuffle.xy_diff_eq_sum_mixed ];
  · rw [ eq_tsub_iff_add_eq_of_le ] <;> norm_num [ Shuffle.apply_zero, Shuffle.apply_last ]

/-- Swapping a `(p,q)`-shuffle changes the sign by the Koszul factor `(-1)^(p*q)`. -/
theorem sign_eq_negOnePow_mul_swap_sign {p q : ℕ} (u : Shuffle p q) :
    u.sign = (-1 : ℤ) ^ (p * q) * (u.swap).sign := by
  have h := invCount_add_invCount_swap u
  simp only [sign]
  conv_rhs => rw [show (p * q : ℕ) = u.invCount + (u.swap).invCount from h.symm]
  rw [pow_add, mul_assoc]
  suffices (-1 : ℤ) ^ (u.swap).invCount * (-1 : ℤ) ^ (u.swap).invCount = 1 by
    rw [this, mul_one]
  rw [← mul_pow]
  norm_num

/-- The **staircase** `(r,m)`-shuffle `k ↦ (min(k,r), k - r)`: it goes right `r` steps then up
`m` steps. Its front-`r` face and back-`m` face
recover the identity, so it is the unique shuffle contributing the identity summand to the
diagonal Eilenberg–Zilber/Alexander–Whitney pairing. -/
def trivialShuffle (r m : ℕ) : Shuffle r m :=
  ⟨OrderHom.prod
      ⟨fun k => ⟨min k.val r, by omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩
      ⟨fun k => ⟨k.val - r, by have := k.isLt; omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩,
    fun a b hab => by
      have h1 : min a.val r = min b.val r := congrArg (fun p => (p.1 : ℕ)) hab
      have h2 : a.val - r = b.val - r := congrArg (fun p => (p.2 : ℕ)) hab
      apply Fin.ext
      have ha := a.isLt; have hb := b.isLt
      omega⟩

/-- The coordinates of the staircase shuffle: `fst = min(·, r)`, `snd = · - r`. -/
@[simp] lemma trivialShuffle_apply (r m : ℕ) (k : Index (r + m)) :
    (trivialShuffle r m).1 k = (⟨min k.val r, by omega⟩, ⟨k.val - r, by have := k.isLt; omega⟩) :=
  rfl

/-- The staircase shuffle has no inversions, hence sign `1`. -/
lemma sign_trivialShuffle (r m : ℕ) : (trivialShuffle r m).sign = 1 := by
  have hinv : (trivialShuffle r m).invCount = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [trivialShuffle_apply, Fin.val_succ, Fin.val_castSucc, Fin.mk_lt_mk]
    split_ifs with h
    · -- `fst` strictly increases at step `i` ⟹ `i < r` ⟹ `snd = i - r = 0`.
      omega
    · rfl
  rw [sign, hinv, pow_zero]

/-! #### Face-shuffle decomposition (Leibniz rule infrastructure)

**Why "remove step" doesn't work.**  An earlier attempt defined `removeLeftStep μ r`
by removing vertex `r` from the shuffle path whenever step `r` is a left step.
This is wrong: the face map `δ_r` removes **vertex** `r`, which merges the steps
on either side of `r`. If those steps have different types (one left, one right),
the merged step is a **diagonal** (both coordinates increase), which cannot be a
valid shuffle step.

Example: the `(1,1)`-shuffle `(0,0) → (1,0) → (1,1)` has step 0 = Left,
step 1 = Right.  Removing vertex 1 = `(1,0)` gives `(0,0) → (1,1)`, a diagonal.
This doesn't factor as `ν ≫ (δⱼ × id)` for any shuffle `ν`.  The factorization
only works for "LL" vertices (both adjacent steps are left) or "RR" vertices.

**The insert approach.**  Instead of decomposing the LHS face terms, we work from
the RHS and **inject** into the LHS.  Given a `(p, q+1)`-shuffle `ν` and a face
index `j : Fin (p+2)`, we construct a `(p+1, q+1)`-shuffle `insertLeftStep ν j`
by lifting ν's first coordinate via `Fin.succAbove j` (skipping value `j`) and
inserting a new left step where the first coordinate crosses `j`.

The proof of `universalSimplexCrossProduct_boundary` then proceeds:
1. Show the RHS terms inject into the LHS via `insertLeftStep` / `insertRightStep`.
2. Show the remaining LHS terms (diagonal terms) cancel via a sign-reversing
   involution `swapDiagonalSteps`.
-/

/-- Whether step `r` of shuffle `μ` is a "left step" (first coordinate increments). -/
def isLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) : Prop :=
  (μ.1 r.castSucc).1.val < (μ.1 r.succ).1.val

instance decidableIsLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) :
    Decidable (isLeftStep μ r) :=
  inferInstanceAs (Decidable (_ < _))


end Shuffle

instance uniqueShuffleNZero {n : ℕ} : Unique (Shuffle n 0) where
  default := ⟨⟨fun i => (i, 0), fun i j h => ⟨h, by simp⟩⟩, fun i j h => congrArg Prod.fst h⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    ext
    · have hmono : StrictMono (fun i => (f i).1) := by
        intro a b hab
        have h_le := hf hab.le
        have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
        have h_le_1 : (f a).1 ≤ (f b).1 := h_le.1
        cases eq_or_lt_of_le h_le_1 with
        | inl heq =>
          exfalso
          apply h_neq
          ext
          · exact congrArg Fin.val heq
          · simp
        | inr hlt => exact hlt
      have heq : ∀ i, (f i).1 = i := by
        intro i
        exact le_antisymm (StrictMono.le_id hmono i) (StrictMono.id_le hmono i)
      exact congrArg Fin.val (heq i)
    · simp

attribute [grind =] OrderHom.coe_mk


instance uniqueShuffleZeroN {n : ℕ} : Unique (Shuffle 0 n) where
  default := ⟨⟨fun i => (0, i.cast (by omega)),
    fun i j h => ⟨by simp, by simpa using h⟩⟩,
    fun i j h => Fin.cast_injective (by omega) (congrArg Prod.snd h)⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext; apply OrderHom.ext; funext i
    have hmono : StrictMono (fun i => (f i).2) := by
      intro a b hab
      have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
      cases eq_or_lt_of_le (hf hab.le).2 with
      | inl heq =>
        exact absurd (Prod.ext (by simp [Fin.eq_zero])
          (Fin.ext (congrArg Fin.val heq))) h_neq
      | inr hlt => exact hlt
    let g : Fin (n + 1) → Fin (n + 1) := fun j => (f (j.cast (by omega))).2
    have hg : StrictMono g := fun a b h =>
      -- grind
      hmono (show a.cast _ < b.cast _ by exact_mod_cast h)
    have hg_eq : ∀ j, g j = j :=
      fun j => le_antisymm (StrictMono.le_id hg j) (StrictMono.id_le hg j)
    apply Prod.ext (Fin.eq_zero _)
    simp only [OrderHom.coe_mk, Fin.isValue]
    grind
    -- grind only [= Fin.val_cast, = Lean.Grind.toInt_fin, = OrderHom.coe_mk]
    -- exact Prod.ext (Fin.eq_zero _) h2

/-- The unique `(n,0)`-shuffle has sign `1`. -/
lemma Shuffle.sign_default_zero_right {n : ℕ} : (default : Shuffle n 0).sign = 1 := by
  simp [Shuffle.sign, Shuffle.invCount]

/-- The unique `(0,n)`-shuffle has sign `1`. -/
lemma Shuffle.sign_default_zero_left {n : ℕ} : (default : Shuffle 0 n).sign = 1 := by
  have h := sign_eq_negOnePow_mul_swap_sign (u := (default : Shuffle 0 n))
  have hswap : (default : Shuffle 0 n).swap = (default : Shuffle n 0) := by
    exact Subsingleton.elim _ _
  rw [Nat.zero_mul, pow_zero, one_mul, hswap, Shuffle.sign_default_zero_right] at h
  exact h


end D5.S3.HomologicalAlgebra.EilenbergZilber
