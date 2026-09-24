/- GID: D5/S3/Combinatorics/FairWindowMinimizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FairWindowMinimizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed word orderings and binary labels give exact fair-window defect averages. -/

import D5.S3.Combinatorics.FairWindowDefect
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FairWindowMinimizer

open scoped BigOperators
open D5.S3.Combinatorics.FairWindowDefect
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
open private prod_paritySign_cases from D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

/-- The length-m word beginning at position i in a complete finite block. -/
def word {m k : ℕ} (v : Fin (m + k) → Fin 2) (i : Fin (k + 1)) : Fin m → Fin 2 :=
  fun j => v ⟨i.val + j.val, by omega⟩

/-- The leftmost position with minimal rank. -/
noncomputable def select {n : ℕ} (q : Fin (n + 1) → ℕ) : Fin (n + 1) :=
  (Finset.univ.filter (fun i => q i = Finset.univ.inf' Finset.univ_nonempty q)).min'
    (by
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)

/-- A complete ordering of word types, represented by a permutation followed by
the fixed enumeration of all words. -/
noncomputable def rank {m : ℕ} (ρ : Equiv.Perm (Fin m → Fin 2)) (w : Fin m → Fin 2) : ℕ :=
  (Fintype.equivFin (Fin m → Fin 2) (ρ w)).val

/-- A single deterministic strict-window table: choose the least word type and
transport its fixed label through the remainder of the window. -/
noncomputable def table (m k : ℕ) (ρ : Equiv.Perm (Fin m → Fin 2))
    (β : (Fin m → Fin 2) → Fin 2) (v : Fin (m + k) → Fin 2) : Fin 2 :=
  let a := select (fun i => rank ρ (word v i))
  let s := paritySign (β (word v a)) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin (m + k) => a.val + m ≤ j.val), paritySign (v j)
  if s = 1 then 1 else 0

/-- For every positive word length and every window slack, the offline average
of the actual transport defect on a collision-free complete context is exactly
the reciprocal of the number of candidate endpoints in the two-window union. -/
theorem good_context_average (m k : ℕ) (hm : 0 < m)
    (v : Fin (m + k + 1) → Fin 2)
    (hv : Function.Injective (word (m := m) (k := k + 1) v)) :
    (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
      𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v) =
        1 / (k + 2 : ℚ) := by
  classical
  have hselect {n : ℕ} (q : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
      q (select q) ≤ q i := by
    have h := Finset.min'_mem
      (Finset.univ.filter (fun i => q i = Finset.univ.inf' Finset.univ_nonempty q))
      (by obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
          exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)
    have he := (Finset.mem_filter.mp h).2
    change q (select q) = _ at he
    rw [he]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have hrank (ρ : Equiv.Perm (Fin m → Fin 2)) : Function.Injective (rank ρ) := by
    intro x y h
    exact ρ.injective ((Fintype.equivFin _).injective (Fin.ext h))
  have hunique {n : ℕ} (q : Fin (n + 1) → ℕ) (hq : Function.Injective q)
      (i : Fin (n + 1)) (hi : ∀ j, q i ≤ q j) : select q = i := by
    exact hq (le_antisymm (hselect q i) (hi _))
  let W := word (m := m) (k := k + 1) v
  let q (ρ : Equiv.Perm (Fin m → Fin 2)) : Fin (k + 2) → ℕ := fun i => rank ρ (W i)
  have hq (ρ : Equiv.Perm (Fin m → Fin 2)) : Function.Injective (q ρ) :=
    (hrank ρ).comp hv
  let z (ρ : Equiv.Perm (Fin m → Fin 2)) := select (q ρ)
  have hz (ρ : Equiv.Perm (Fin m → Fin 2)) (i : Fin (k + 2)) :
      q ρ (z ρ) ≤ q ρ i := hselect _ _
  have horder (i : Fin (k + 2)) :
      (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), if z ρ = i then (1 : ℚ) else 0) =
        1 / (k + 2 : ℚ) := by
    have hequal (j : Fin (k + 2)) :
        (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), if z ρ = i then (1 : ℚ) else 0) =
        (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), if z ρ = j then (1 : ℚ) else 0) := by
      let τ := Equiv.swap (W i) (W j)
      let e : Equiv.Perm (Equiv.Perm (Fin m → Fin 2)) :=
        ⟨fun ρ => τ.trans ρ, fun ρ => τ.trans ρ,
          fun ρ => by ext w; simp [τ], fun ρ => by ext w; simp [τ]⟩
      have htrans (ρ : Equiv.Perm (Fin m → Fin 2)) (l : Fin (k + 2)) :
          q (e ρ) l = q ρ (Equiv.swap i j l) := by
        dsimp [q, e, rank, τ]
        rw [hv.swap_apply]
      have hez (ρ : Equiv.Perm (Fin m → Fin 2)) :
          z (e ρ) = Equiv.swap i j (z ρ) := by
        apply hunique _ (hq _) _
        intro l
        rw [htrans, Equiv.swap_apply_self, htrans]
        exact hz _ _
      apply Fintype.expect_equiv e
      intro ρ
      rw [hez]
      have heq : Equiv.swap i j (z ρ) = j ↔ z ρ = i := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      simp only [heq]
    have hsum : (k + 2 : ℚ) *
        (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), if z ρ = i then (1 : ℚ) else 0) = 1 := by
      calc
        _ = ∑ j : Fin (k + 2),
            (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), if z ρ = j then (1 : ℚ) else 0) := by
          simp_rw [← hequal]
          simp
        _ = 𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
            ∑ j : Fin (k + 2), if z ρ = j then (1 : ℚ) else 0 :=
          (Finset.expect_sum_comm _ _ _).symm
        _ = 1 := by simp
    apply (eq_div_iff (by positivity : (k + 2 : ℚ) ≠ 0)).mpr
    simpa [mul_comm] using hsum
  let v₀ : Fin (m + k) → Fin 2 := fun i => v i.castSucc
  let v₁ : Fin (m + k) → Fin 2 := fun i => v i.succ
  have hword₀ (i : Fin (k + 1)) : word v₀ i = W i.castSucc := by
    funext j
    rfl
  have hword₁ (i : Fin (k + 1)) : word v₁ i = W i.succ := by
    funext j
    apply congrArg v
    apply Fin.ext
    simp
    omega
  let a (ρ : Equiv.Perm (Fin m → Fin 2)) := select (fun i : Fin (k + 1) => q ρ i.castSucc)
  let b (ρ : Equiv.Perm (Fin m → Fin 2)) := select (fun i : Fin (k + 1) => q ρ i.succ)
  have ha (ρ : Equiv.Perm (Fin m → Fin 2)) (i : Fin (k + 1)) :
      q ρ (a ρ).castSucc ≤ q ρ i.castSucc := hselect (fun j : Fin (k + 1) => q ρ j.castSucc) i
  have hb (ρ : Equiv.Perm (Fin m → Fin 2)) (i : Fin (k + 1)) :
      q ρ (b ρ).succ ≤ q ρ i.succ := hselect (fun j : Fin (k + 1) => q ρ j.succ) i
  have hswitch (ρ : Equiv.Perm (Fin m → Fin 2)) :
      (a ρ).castSucc ≠ (b ρ).succ ↔ z ρ = 0 ∨ z ρ = Fin.last (k + 1) := by
    have hsame (h : (a ρ).castSucc = (b ρ).succ) : z ρ = (a ρ).castSucc := by
      apply hunique _ (hq _) _
      intro j
      induction j using Fin.lastCases with
      | last => rw [h]; exact hb ρ (Fin.last k)
      | cast j => exact ha ρ j
    constructor
    · intro h
      by_contra hn
      push Not at hn
      have hz0 : 0 < (z ρ).val := by
        have := hn.1
        contrapose! this
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      let x : Fin (k + 1) := ⟨(z ρ).val, by
        have ht := (z ρ).isLt
        have hl := hn.2
        have : (z ρ).val ≠ k + 1 := fun h => hl (Fin.ext h)
        omega⟩
      let y : Fin (k + 1) := ⟨(z ρ).val - 1, by have := (z ρ).isLt; omega⟩
      have hx : x.castSucc = z ρ := Fin.ext rfl
      have hy : y.succ = z ρ := Fin.ext (by dsimp [y]; omega)
      have hax : a ρ = x := hunique _ ((hq ρ).comp (Fin.castSucc_injective _)) _
        (fun j => by change q ρ x.castSucc ≤ q ρ j.castSucc; rw [hx]; exact hz _ _)
      have hby : b ρ = y := hunique _ ((hq ρ).comp (Fin.succ_injective _)) _
        (fun j => by change q ρ y.succ ≤ q ρ j.succ; rw [hy]; exact hz _ _)
      exact h (by rw [hax, hby, hx, hy])
    · intro h he
      have hs := hsame he
      rcases h with h | h
      · have : (b ρ).succ = 0 := he.symm.trans (hs.symm.trans h)
        exact Fin.succ_ne_zero _ this
      · exact Fin.castSucc_ne_last _ (hs.symm.trans h)
  -- The label average is evaluated on the same complete context.
  have hlabels (ρ : Equiv.Perm (Fin m → Fin 2)) :
      (𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v) =
        if (a ρ).castSucc = (b ρ).succ then 0 else (1 / 2 : ℚ) := by
    let A := W (a ρ).castSucc
    let B := W (b ρ).succ
    let T₀ : ℤ := ∏ j ∈ Finset.univ.filter
      (fun j : Fin (m + k) => (a ρ).val + m ≤ j.val), paritySign (v₀ j)
    let T₁ : ℤ := ∏ j ∈ Finset.univ.filter
      (fun j : Fin (m + k) => (b ρ).val + m ≤ j.val), paritySign (v₁ j)
    have hsign (β : (Fin m → Fin 2) → Fin 2) (w : Fin (m + k) → Fin 2) :
        paritySign (table m k ρ β w) =
          paritySign (β (word w (select (fun i => rank ρ (word w i))))) *
          ∏ j ∈ Finset.univ.filter (fun j : Fin (m + k) =>
            (select (fun i => rank ρ (word w i))).val + m ≤ j.val), paritySign (w j) := by
      let c := select (fun i => rank ρ (word w i))
      have hp := prod_paritySign_cases
        (Finset.univ.filter (fun j : Fin (m + k) => c.val + m ≤ j.val)) w
      have hbval : β (word w c) = 0 ∨ β (word w c) = 1 := by omega
      dsimp [c] at hp hbval
      rcases hp with hp | hp <;> rcases hbval with hbval | hbval <;>
        simp only [table, hp, hbval] <;> norm_num [paritySign]
    have hD (β : (Fin m → Fin 2) → Fin 2) :
        defect (table m k ρ β) v =
          if paritySign (β B) * T₁ =
            paritySign (v (Fin.last (m + k))) * (paritySign (β A) * T₀)
          then 0 else 1 := by
      unfold defect
      rw [hsign β v₁, hsign β v₀]
      simp_rw [hword₀, hword₁]
      rfl
    by_cases hab : (a ρ).castSucc = (b ρ).succ
    · have habval : (a ρ).val = (b ρ).val + 1 := congrArg Fin.val hab
      have hAB : A = B := congrArg W hab
      have hT : T₁ = paritySign (v (Fin.last (m + k))) * T₀ := by
        let g : Fin (m + k + 1) → ℤ := fun j =>
          if (a ρ).val + m ≤ j.val then paritySign (v j) else 1
        have hfull₀ : (∏ j, g j) = T₀ * paritySign (v (Fin.last (m + k))) := by
          rw [Fin.prod_univ_castSucc]
          have he : g (Fin.last (m + k)) = paritySign (v (Fin.last (m + k))) := by
            simp [g, show (a ρ).val + m ≤ m + k by have := (a ρ).isLt; omega]
          rw [he]
          congr 1
          simp only [T₀, Finset.prod_filter]
          rfl
        have hfull₁ : (∏ j, g j) = T₁ := by
          rw [Fin.prod_univ_succ]
          have hzero : g 0 = 1 := by simp [g, show ¬ (a ρ).val + m ≤ 0 by omega]
          rw [hzero, one_mul]
          simp only [T₁, Finset.prod_filter]
          apply Finset.prod_congr rfl
          intro j _
          have hj : (a ρ).val + m ≤ j.succ.val ↔ (b ρ).val + m ≤ j.val := by
            simp only [Fin.val_succ]; omega
          simp only [g, hj, v₁]
        rw [← hfull₁, hfull₀, mul_comm]
      have hzero (β : (Fin m → Fin 2) → Fin 2) : defect (table m k ρ β) v = 0 := by
        rw [hD, hT, hAB]
        have he : paritySign (β B) * (paritySign (v (Fin.last (m + k))) * T₀) =
            paritySign (v (Fin.last (m + k))) * (paritySign (β B) * T₀) := by ring
        rw [if_pos he]
      simp [hab, hzero]
    · have hAB : A ≠ B := fun h => hab (hv h)
      let flip (β : (Fin m → Fin 2) → Fin 2) :=
        Function.update β B (Equiv.swap (0 : Fin 2) 1 (β B))
      have hflipflip (β : (Fin m → Fin 2) → Fin 2) : flip (flip β) = β := by
        funext w
        by_cases hw : w = B
        · subst w; simp [flip]
        · simp [flip, hw]
      have hflipbij : Function.Bijective flip :=
        Function.Involutive.bijective hflipflip
      have hpair (β : (Fin m → Fin 2) → Fin 2) :
          defect (table m k ρ β) v + defect (table m k ρ (flip β)) v = 1 := by
        rw [hD, hD]
        have hfa : flip β A = β A := by simp [flip, hAB]
        have hfb : flip β B = Equiv.swap (0 : Fin 2) 1 (β B) := by simp [flip]
        rw [hfa, hfb]
        have ht₀ : T₀ = -1 ∨ T₀ = 1 := prod_paritySign_cases _ _
        have ht₁ : T₁ = -1 ∨ T₁ = 1 := prod_paritySign_cases _ _
        have hba : β A = 0 ∨ β A = 1 := by omega
        have hbb : β B = 0 ∨ β B = 1 := by omega
        have hlast : v (Fin.last (m + k)) = 0 ∨ v (Fin.last (m + k)) = 1 := by omega
        rcases ht₀ with ht₀ | ht₀ <;> rcases ht₁ with ht₁ | ht₁ <;>
          rcases hba with hba | hba <;> rcases hbb with hbb | hbb <;>
          rcases hlast with hlast | hlast <;>
          norm_num [ht₀, ht₁, hba, hbb, hlast, paritySign]
      have heq : (𝔼 β, defect (table m k ρ (flip β)) v) =
          𝔼 β, defect (table m k ρ β) v :=
        Fintype.expect_bijective flip hflipbij _ _ (fun _ => rfl)
      have hsum : (𝔼 β, defect (table m k ρ β) v) +
          (𝔼 β, defect (table m k ρ β) v) = 1 := by
        calc
          _ = (𝔼 β, defect (table m k ρ β) v) +
              (𝔼 β, defect (table m k ρ (flip β)) v) := by rw [heq]
          _ = 𝔼 β, (defect (table m k ρ β) v +
              defect (table m k ρ (flip β)) v) := (Finset.expect_add_distrib ..).symm
          _ = 1 := by simp_rw [hpair]; exact Fintype.expect_const _
      rw [if_neg hab]
      linarith
  simp_rw [hlabels]
  have hind (ρ : Equiv.Perm (Fin m → Fin 2)) :
      (if (a ρ).castSucc = (b ρ).succ then (0 : ℚ) else 1 / 2) =
        ((if z ρ = 0 then 1 else 0) +
          (if z ρ = Fin.last (k + 1) then 1 else 0)) / 2 := by
    have hn : (0 : Fin (k + 2)) ≠ Fin.last (k + 1) := by
      intro h; have := congrArg Fin.val h; simp at this
    by_cases h : (a ρ).castSucc = (b ρ).succ
    · have hs : ¬ (z ρ = 0 ∨ z ρ = Fin.last (k + 1)) := by
        intro hh; exact (hswitch ρ).mpr hh h
      simp only [not_or] at hs
      simp [h, hs.1, hs.2]
    · rcases (hswitch ρ).mp h with h0 | hL
      · simp [h, h0, hn]
      · simp [h, hL, Ne.symm hn]
  simp_rw [hind, div_eq_mul_inv]
  rw [← Finset.expect_mul, Finset.expect_add_distrib, horder, horder]
  ring

#print axioms good_context_average

end D5.S3.Combinatorics.FairWindowMinimizer
