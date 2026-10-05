/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleReduced
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleReduced
   mirror-E: none(waiver:actual-reduced-graph-kernel-construction)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Rectangle synthesis constructs the kernel of the actual reduced adjacency block. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleDefs
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduced

open BlumTriangleDefs Finset Matrix

/-- Delete precisely the leftward edges at rows `4i + 1` on the reflection axis. -/
def reducedAdj (k : ℕ) (u v : Vertex (4 * k)) : Prop :=
  Adj u v ∧
    ¬ (u.1.1.val % 4 = 1 ∧ u.1.2.val = 4 * k - 1 ∧ v.1.2.val < 4 * k - 1) ∧
    ¬ (v.1.1.val % 4 = 1 ∧ v.1.2.val = 4 * k - 1 ∧ u.1.2.val < 4 * k - 1)

set_option maxHeartbeats 4000000 in
-- Neighbor case analysis and both coordinate bijections share this elaboration budget.
open Classical in
/-- The rectangle vectors form a basis of the kernel of the actual even-to-odd reduced
adjacency block. Diagonal evaluation inverts synthesis; rank-nullity gives full column rank. -/
theorem reduced_kernel_basis {K : Type*} [Field K] [CharP K 2] (k : ℕ) :
    let E := {u : Vertex (4 * k) // u.1.1.val % 2 = 0}
    let O := {u : Vertex (4 * k) // u.1.1.val % 2 = 1}
    let C : Matrix E O K := fun u v => if reducedAdj k u.1 v.1 then 1 else 0
    ∃ e : (Fin (2 * k) → K) ≃ₗ[K] LinearMap.ker Cᵀ.mulVecLin,
      (∀ t u, (e t).1 u = ∑ j : Fin (2 * k),
        if u.1.1.1.val / 2 ≤ j.val ∧ j.val ≤ u.1.1.2.val / 2 ∧
          u.1.1.2.val / 2 ≤
            (if j.val % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j.val)
        then t j else 0) ∧ Function.Injective C.mulVecLin := by
  classical
  let E := {u : Vertex (4 * k) // u.1.1.val % 2 = 0}
  let O := {u : Vertex (4 * k) // u.1.1.val % 2 = 1}
  let C : Matrix E O K := fun u v => if reducedAdj k u.1 v.1 then 1 else 0
  let D : ℕ → ℕ → Prop := fun a b => a < 2 * k ∧ a ≤ b ∧ a + b < 4 * k
  let mk : ∀ a b, D a b → E := fun a b hd =>
    ⟨⟨(⟨2 * a, by dsimp [D] at hd; omega⟩,
        ⟨2 * b, by dsimp [D] at hd; omega⟩), by
      dsimp [D] at hd
      change 2 * a ≤ 2 * b ∧ 2 * b + 2 * a ≤ 2 * (4 * k - 1) ∧
        (2 * a) % 2 = (2 * b) % 2
      omega⟩, by simp⟩
  let ev : (E → K) → ℕ → ℕ → K := fun f a b =>
    if hd : D a b then f (mk a b hd) else 0
  have coord (u : E) :
      2 * (u.1.1.1.val / 2) = u.1.1.1.val ∧
      2 * (u.1.1.2.val / 2) = u.1.1.2.val ∧
      D (u.1.1.1.val / 2) (u.1.1.2.val / 2) := by
    have hu := u.1.2
    have hp := u.2
    have hr := u.1.1.1.isLt
    dsimp [D]
    omega
  have mk_coord (u : E) : mk _ _ (coord u).2.2 = u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact (coord u).1
    · exact (coord u).2.1
  have ev_coord (f : E → K) (u : E) :
      ev f (u.1.1.1.val / 2) (u.1.1.2.val / 2) = f u := by
    dsimp only [ev]
    rw [dif_pos (coord u).2.2, mk_coord]
  have delta (f : E → K) (a b : ℕ) :
      (∑ u : E, if u.1.1.1.val = 2 * a ∧ u.1.1.2.val = 2 * b then f u else 0) =
        ev f a b := by
    by_cases hd : D a b
    · dsimp only [ev]
      rw [dif_pos hd]
      rw [sum_eq_single (mk a b hd)]
      · simp [mk]
      · intro u _ hne
        apply if_neg
        intro hu
        apply hne
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · exact hu.1
        · exact hu.2
      · simp
    · dsimp only [ev]
      rw [dif_neg hd]
      apply sum_eq_zero
      intro u _
      apply if_neg
      intro hcoord
      have hu := u.1.2
      have hr := u.1.1.1.isLt
      apply hd
      dsimp [D]
      omega
  have odd_sum (f : E → K) (v : O) (a b : ℕ)
      (hr : v.1.1.1.val = 2 * a + 1) (hc : v.1.1.2.val = 2 * b + 1) :
      (Cᵀ *ᵥ f) v =
        if a % 2 = 0 ∧ b = 2 * k - 1 then
          ev f a (b + 1) + ev f (a + 1) (b + 1)
        else ev f a b + ev f (a + 1) b +
          ev f a (b + 1) + ev f (a + 1) (b + 1) := by
    have hv := v.1.2
    have hvr := v.1.1.1.isLt
    have classifies (u : E) : reducedAdj k u.1 v.1 ↔
        (u.1.1.1.val = 2 * a ∨ u.1.1.1.val = 2 * (a + 1)) ∧
          (if a % 2 = 0 ∧ b = 2 * k - 1 then u.1.1.2.val = 2 * (b + 1)
          else u.1.1.2.val = 2 * b ∨ u.1.1.2.val = 2 * (b + 1)) := by
      have hu := u.1.2
      have hup := u.2
      simp only [reducedAdj, Adj, Step, hr, hc]
      split_ifs <;> omega
    change (∑ u : E, (if reducedAdj k u.1 v.1 then 1 else 0) * f u) = _
    by_cases hd : a % 2 = 0 ∧ b = 2 * k - 1
    · rw [if_pos hd, ← delta f a (b + 1), ← delta f (a + 1) (b + 1),
        ← sum_add_distrib]
      apply sum_congr rfl
      intro u _
      rw [classifies]
      rw [if_pos hd]
      by_cases h0 : u.1.1.1.val = 2 * a
      · simp [h0]
      · simp [h0]
    · rw [if_neg hd, ← delta f a b, ← delta f (a + 1) b,
        ← delta f a (b + 1), ← delta f (a + 1) (b + 1)]
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro u _
      rw [classifies, if_neg hd]
      by_cases h0 : u.1.1.1.val = 2 * a
      · by_cases hx : u.1.1.2.val = 2 * b
        · simp [h0, hx]
        · simp [h0, hx]
      · by_cases hx : u.1.1.2.val = 2 * b
        · simp [h0, hx]
        · simp [h0, hx]
  let R : ℕ → ℕ := fun j => if j % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j
  let S : (Fin (2 * k) → K) → E → K := fun t u => ∑ j : Fin (2 * k),
    if u.1.1.1.val / 2 ≤ j.val ∧ j.val ≤ u.1.1.2.val / 2 ∧
      u.1.1.2.val / 2 ≤ R j.val then t j else 0
  have synthesis (t : Fin (2 * k) → K) (a b : ℕ) :
      ev (S t) a b = ∑ j : Fin (2 * k),
        if a ≤ j.val ∧ j.val ≤ b ∧ b ≤ R j.val then t j else 0 := by
    by_cases hd : D a b
    · simp [ev, hd, S, mk]
    · rw [show ev (S t) a b = 0 from dif_neg hd]
      symm
      apply sum_eq_zero
      intro j _
      apply if_neg
      intro hj
      have hjlt := j.isLt
      apply hd
      dsimp [D, R] at *
      split_ifs at hj <;> omega
  have synthesis_kernel (t : Fin (2 * k) → K) : Cᵀ *ᵥ S t = 0 := by
    funext v
    let a := v.1.1.1.val / 2
    let b := v.1.1.2.val / 2
    have hv := v.1.2
    have hp := v.2
    have hvr := v.1.1.1.isLt
    have hr : v.1.1.1.val = 2 * a + 1 := by dsimp [a]; omega
    have hc : v.1.1.2.val = 2 * b + 1 := by dsimp [b]; omega
    have ha : a < 2 * k := by omega
    have hab : a ≤ b := by omega
    have hb : a + b + 1 < 4 * k := by omega
    rw [odd_sum (S t) v a b hr hc]
    by_cases hd : a % 2 = 0 ∧ b = 2 * k - 1
    · rw [if_pos hd, synthesis, synthesis, ← sum_add_distrib]
      apply sum_eq_zero
      intro j _
      by_cases hj : j.val = a
      · have hn : ¬ (a ≤ j.val ∧ j.val ≤ b + 1 ∧ b + 1 ≤ R j.val) := by
          simp only [R, hj, if_pos hd.1]
          omega
        have hn' : ¬ (a + 1 ≤ j.val ∧ j.val ≤ b + 1 ∧ b + 1 ≤ R j.val) := by
          omega
        rw [if_neg hn, if_neg hn', add_zero]
      · have hle : a ≤ j.val ↔ a + 1 ≤ j.val := by omega
        simp only [hle]
        exact CharTwo.add_self_eq_zero _
    · rw [if_neg hd, synthesis, synthesis, synthesis, synthesis]
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_eq_zero
      intro j _
      by_cases hj : j.val = a
      · simp only [hj, show ¬ a + 1 ≤ a by omega, false_and, if_false, add_zero]
        by_cases hp : a % 2 = 0
        · by_cases hbc : b < 2 * k - 1
          · have hbc' : b + 1 ≤ R a := by simp [R, hp]; omega
            have hbc'' : b ≤ R a := by omega
            simp [hab, show a ≤ b + 1 by omega, hbc', hbc'',
              CharTwo.add_self_eq_zero]
          · have hbc' : ¬ b ≤ R a := by simp [R, hp]; omega
            have hbc'' : ¬ b + 1 ≤ R a := by omega
            simp [hbc', hbc'']
        · have hbc' : b + 1 ≤ R a := by simp [R, hp]; omega
          have hbc'' : b ≤ R a := by omega
          simp [hab, show a ≤ b + 1 by omega, hbc', hbc'',
            CharTwo.add_self_eq_zero]
      · have hle : a ≤ j.val ↔ a + 1 ≤ j.val := by omega
        simp only [hle]
        rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  have synthesis_diagonal (t : Fin (2 * k) → K) (j : Fin (2 * k)) :
      ev (S t) j.val j.val = t j := by
    rw [synthesis]
    rw [sum_eq_single j]
    · have hR : j.val ≤ R j.val := by
        have hj := j.isLt
        dsimp [R]
        split_ifs <;> omega
      simp [hR]
    · intro i _ hij
      apply if_neg
      intro hi
      exact hij (Fin.ext (by omega))
    · simp
  let L : (Fin (2 * k) → K) →ₗ[K] LinearMap.ker Cᵀ.mulVecLin :=
    { toFun := fun t => ⟨S t, synthesis_kernel t⟩
      map_add' := fun t t' => by
        apply Subtype.ext
        funext u
        dsimp [S]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        split_ifs <;> simp
      map_smul' := fun c t => by
        apply Subtype.ext
        funext u
        dsimp [S]
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        split_ifs <;> simp }
  have linjective : Function.Injective L := by
    intro t t' ht
    have he := congrArg Subtype.val ht
    funext j
    have he' := congrArg (fun f : E → K => ev f j.val j.val) he
    change ev (S t) j.val j.val = ev (S t') j.val j.val at he'
    simpa only [synthesis_diagonal] using he'
  have lsurjective : Function.Surjective L := by
    intro f
    let t : Fin (2 * k) → K := fun j => ev f.1 j.val j.val
    refine ⟨t, ?_⟩
    apply Subtype.ext
    funext u
    have support (a b : ℕ) (hd : ¬ (a < 2 * k ∧ a ≤ b ∧ a + b < 4 * k)) :
        ev f.1 a b = 0 := dif_neg hd
    have equations (a b : ℕ) (ha : a < 2 * k) (hab : a ≤ b)
        (hb : a + b + 1 < 4 * k) :
        (if a % 2 = 0 ∧ b = 2 * k - 1 then
          ev f.1 a (b + 1) + ev f.1 (a + 1) (b + 1)
        else ev f.1 a b + ev f.1 (a + 1) b +
          ev f.1 a (b + 1) + ev f.1 (a + 1) (b + 1)) = 0 := by
      let v : O := ⟨⟨(⟨2 * a + 1, by omega⟩, ⟨2 * b + 1, by omega⟩), by
        change 2 * a + 1 ≤ 2 * b + 1 ∧
          2 * b + 1 + (2 * a + 1) ≤ 2 * (4 * k - 1) ∧
          (2 * a + 1) % 2 = (2 * b + 1) % 2
        omega⟩, by simp⟩
      have hf := congrFun f.2 v
      exact (odd_sum f.1 v a b rfl rfl).symm.trans hf
    have expansion := BlumTriangleKernel.reduced_kernel_expansion k (ev f.1)
      support equations (u.1.1.1.val / 2) (u.1.1.2.val / 2)
    rw [ev_coord] at expansion
    exact expansion.symm
  let e := LinearEquiv.ofBijective L ⟨linjective, lsurjective⟩
  refine ⟨e, (fun _ _ => rfl), ?_⟩
  -- Each even row has exactly one more vertex than the corresponding odd row.
  let boundary : E → Prop := fun u => u.1.1.1.val + u.1.1.2.val = 2 * (4 * k - 1)
  let eB : Fin (2 * k) ≃ {u : E // boundary u} :=
    { toFun := fun j => ⟨mk j.val (4 * k - 1 - j.val) (by
        have hj := j.isLt
        dsimp [D]
        omega), by
        have hj := j.isLt
        dsimp [boundary, mk]
        omega⟩
      invFun := fun u => ⟨u.1.1.1.1.val / 2, by
        have hr := u.1.1.1.1.isLt
        omega⟩
      left_inv := fun j => by
        apply Fin.ext
        simp [mk]
      right_inv := fun u => by
        have hc := coord u.1
        have hb := u.2
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · exact hc.1
        · dsimp [mk, boundary] at *
          omega }
  let shift : {u : E // ¬ boundary u} → O := fun u =>
    ⟨⟨(⟨u.1.1.1.1.val + 1, by
        have hr := u.1.1.1.1.isLt
        have hp := u.1.2
        omega⟩, ⟨u.1.1.1.2.val + 1, by
        have hx := u.1.1.1.2.isLt
        have hp := u.1.1.2
        have he := u.1.2
        omega⟩), by
      have hv := u.1.1.2
      have hn := u.2
      have he := u.1.2
      change u.1.1.1.1.val + 1 ≤ u.1.1.1.2.val + 1 ∧
        u.1.1.1.2.val + 1 + (u.1.1.1.1.val + 1) ≤ 2 * (4 * k - 1) ∧
        (u.1.1.1.1.val + 1) % 2 = (u.1.1.1.2.val + 1) % 2
      dsimp [boundary] at hn
      omega⟩, by
      change (u.1.1.1.1.val + 1) % 2 = 1
      have he := u.1.2
      omega⟩
  let unshift : O → {u : E // ¬ boundary u} := fun v =>
    ⟨mk (v.1.1.1.val / 2) (v.1.1.2.val / 2) (by
      have hv := v.1.2
      have he := v.2
      have hr := v.1.1.1.isLt
      dsimp [D]
      omega), by
      have hv := v.1.2
      have he := v.2
      dsimp [boundary, mk]
      omega⟩
  let eI : {u : E // ¬ boundary u} ≃ O :=
    { toFun := shift
      invFun := unshift
      left_inv := fun u => by
        have he := u.1.2
        have hv := u.1.1.2
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp [shift, unshift, mk] <;> omega
      right_inv := fun v => by
        have he := v.2
        have hv := v.1.2
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp [shift, unshift, mk] <;> omega }
  have hcard : Fintype.card E = 2 * k + Fintype.card O := by
    have h := Fintype.card_congr (Equiv.sumCompl boundary)
    rw [Fintype.card_sum, ← Fintype.card_congr eB, Fintype.card_fin,
      Fintype.card_congr eI] at h
    exact h.symm
  have hker := e.finrank_eq
  simp only [Module.finrank_pi, Fintype.card_fin] at hker
  have hnull := Cᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Cᵀ.rank + Module.finrank K (LinearMap.ker Cᵀ.mulVecLin) =
    Module.finrank K (E → K) at hnull
  rw [rank_transpose, ← hker, Module.finrank_pi, hcard] at hnull
  have hnull' := C.mulVecLin.finrank_range_add_finrank_ker
  change C.rank + Module.finrank K (LinearMap.ker C.mulVecLin) =
    Module.finrank K (O → K) at hnull'
  rw [Module.finrank_pi] at hnull'
  have hz : Module.finrank K (LinearMap.ker C.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduced
