/- GID: D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Hirota form D_x(D_x^3 + a1 D_t + a2 D_y)^(2k+1) satisfies the four-soliton condition identically only for k = 0. -/

/-
proof_shape: result: content
escape_witness: form (2) — at the wave numbers (1, 3, 4, 5) the four-soliton condition equals
  48 · 1360488960000^m · F(m), and F(m) < 0 for every odd m ≥ 3 (the local sign estimate
  `negF` inside `result`)
admission_basis: open-problem-resolution (issue #10059)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FluidDynamics.Solitons.GursesPekcanFourSoliton

/-- The polynomial `P(k, ω, l) = k (k³ + α₁ ω + α₂ l)^m` of the Hirota operator
`D_x (D_x³ + α₁ D_t + α₂ D_y)^m`, at the soliton parameters `p = (k, ω, l)`. -/
def hirotaP (α₁ α₂ : ℝ) (m : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  p.1 * (p.1 ^ 3 + α₁ * p.2.1 + α₂ * p.2.2) ^ m

/-- The dispersion relation `k³ + α₁ ω + α₂ l = 0` of a one-soliton `e^{kx + ωt + ly}`. -/
def dispersion (α₁ α₂ : ℝ) (p : ℝ × ℝ × ℝ) : Prop :=
  p.1 ^ 3 + α₁ * p.2.1 + α₂ * p.2.2 = 0

/-- The four-soliton condition (4SC) of Gürses–Pekcan's introduction (Hietarinta's form, the
eight terms with `σ₁ = +1`), for a polynomial `P` and parameters `p₁, …, p₄ = p 0, …, p 3`.
The last factor of the fifth term is `P(p₁ + p₂ + p₃ − p₄)`; the source prints
`P(p₁ − p₂ + p₃ − p₄)`, which repeats the last factor of the seventh term. -/
def fourSC {E : Type*} [AddCommGroup E] (P : E → ℝ) (p : Fin 4 → E) : ℝ :=
  P (p 0 - p 1) * P (p 0 - p 2) * P (p 0 - p 3) * P (p 1 - p 2) * P (p 1 - p 3) *
      P (p 2 - p 3) * P (p 0 + p 1 + p 2 + p 3)
    - P (p 1 - p 2) * P (p 1 - p 3) * P (p 2 - p 3) * P (p 0 + p 2) * P (p 0 + p 1) *
      P (p 0 + p 3) * P (p 0 - p 1 - p 2 - p 3)
    - P (p 0 - p 2) * P (p 0 - p 3) * P (p 2 - p 3) * P (p 0 + p 1) * P (p 1 + p 2) *
      P (p 1 + p 3) * P (p 0 - p 1 + p 2 + p 3)
    - P (p 0 - p 1) * P (p 0 - p 3) * P (p 1 - p 3) * P (p 0 + p 2) * P (p 1 + p 2) *
      P (p 2 + p 3) * P (p 0 + p 1 - p 2 + p 3)
    - P (p 0 - p 1) * P (p 0 - p 2) * P (p 1 - p 2) * P (p 0 + p 3) * P (p 1 + p 3) *
      P (p 2 + p 3) * P (p 0 + p 1 + p 2 - p 3)
    + P (p 0 - p 1) * P (p 2 - p 3) * P (p 0 + p 2) * P (p 0 + p 3) * P (p 1 + p 2) *
      P (p 1 + p 3) * P (p 0 + p 1 - p 2 - p 3)
    + P (p 0 - p 2) * P (p 1 - p 3) * P (p 0 + p 1) * P (p 0 + p 3) * P (p 1 + p 2) *
      P (p 2 + p 3) * P (p 0 - p 1 + p 2 - p 3)
    + P (p 0 - p 3) * P (p 1 - p 2) * P (p 0 + p 1) * P (p 0 + p 2) * P (p 1 + p 3) *
      P (p 2 + p 3) * P (p 0 - p 1 - p 2 + p 3)

/-- Gürses–Pekcan (arXiv:2511.18466), the conjectured lemma after Remark 3: the equation
`D_x (D_x³ + α₁ D_t + α₂ D_y)^{2k+1} {f · f} = 0` satisfies the four-soliton condition
identically on the dispersion relation for `k = 0`, and for every `k ≥ 1` it does not. -/
def claim : Prop :=
  (∀ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) → ∀ p : Fin 4 → ℝ × ℝ × ℝ,
      (∀ i, dispersion α₁ α₂ (p i)) → fourSC (hirotaP α₁ α₂ 1) p = 0) ∧
    ∀ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) → ∀ k : ℕ, 1 ≤ k →
      ∃ p : Fin 4 → ℝ × ℝ × ℝ, (∀ i, dispersion α₁ α₂ (p i)) ∧
        fourSC (hirotaP α₁ α₂ (2 * k + 1)) p ≠ 0

set_option maxHeartbeats 8000000 in
theorem result : claim := by
  -- `Q m (x, e) = x (x³ + e)^m`: the polynomial after the parameters `α₁ ω + α₂ l` are merged.
  let Q : ℕ → ℝ × ℝ → ℝ := fun m v => v.1 * (v.1 ^ 3 + v.2) ^ m
  -- α-elimination: `P = Q ∘ L` for the additive map `L (k, ω, l) = (k, α₁ ω + α₂ l)`, so on the
  -- dispersion relation the condition depends only on the wave numbers.
  have reduce : ∀ (α₁ α₂ : ℝ) (m : ℕ) (p : Fin 4 → ℝ × ℝ × ℝ),
      (∀ i, dispersion α₁ α₂ (p i)) →
        fourSC (hirotaP α₁ α₂ m) p = fourSC (Q m) (fun i => ((p i).1, -((p i).1 ^ 3))) := by
    intro α₁ α₂ m p hp
    let L : ℝ × ℝ × ℝ →+ ℝ × ℝ :=
      { toFun := fun v => (v.1, α₁ * v.2.1 + α₂ * v.2.2)
        map_zero' := by simp
        map_add' := by
          intro x y
          refine Prod.ext (by simp) ?_
          simp only [Prod.snd_add, Prod.fst_add]
          ring }
    have hPQ : hirotaP α₁ α₂ m = fun v => Q m (L v) := by
      funext v
      simp only [hirotaP, Q, L, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      ring
    have hLp : ∀ i, L (p i) = ((p i).1, -((p i).1 ^ 3)) := by
      intro i
      have h := hp i
      simp only [dispersion] at h
      simp only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq, true_and]
      linarith
    rw [hPQ]
    simp only [fourSC, map_add, map_sub, hLp]
  refine ⟨?_, ?_⟩
  · -- k = 0: the four-soliton condition is a polynomial identity in the wave numbers.
    intro α₁ α₂ _ p hp
    rw [reduce α₁ α₂ 1 p hp]
    simp only [fourSC, Q, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    ring
  · intro α₁ α₂ hα k hk
    -- The wave numbers (1, 3, 4, 5) and one solution of the dispersion relation for each.
    let kk : Fin 4 → ℝ := ![1, 3, 4, 5]
    obtain ⟨p, hp, hpk⟩ : ∃ p : Fin 4 → ℝ × ℝ × ℝ,
        (∀ i, dispersion α₁ α₂ (p i)) ∧ ∀ i, (p i).1 = kk i := by
      by_cases h1 : α₁ = 0
      · have h2 : α₂ ≠ 0 := by
          intro h2
          exact hα (by rw [h1, h2])
        refine ⟨fun i => (kk i, 0, -(kk i) ^ 3 / α₂), fun i => ?_, fun i => rfl⟩
        simp only [dispersion]
        field_simp
        ring
      · refine ⟨fun i => (kk i, -(kk i) ^ 3 / α₁, 0), fun i => ?_, fun i => rfl⟩
        simp only [dispersion]
        field_simp
        ring
    refine ⟨p, hp, ?_⟩
    rw [reduce α₁ α₂ _ p hp]
    have hw : (fun i => ((p i).1, -((p i).1 ^ 3))) = fun i => (kk i, -(kk i) ^ 3) := by
      funext i
      rw [hpk i]
    rw [hw]
    set m := 2 * k + 1 with hm
    -- Each term is a product of seven factors `x (x³ + e)^m`.
    have hterm : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ,
        x₁ * y₁ ^ m * (x₂ * y₂ ^ m) * (x₃ * y₃ ^ m) * (x₄ * y₄ ^ m) * (x₅ * y₅ ^ m) *
            (x₆ * y₆ ^ m) * (x₇ * y₇ ^ m) =
          x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇) ^ m := by
      intros
      simp only [mul_pow]
      ring
    let F : ℝ := 13 * 11 ^ m - 55 * (-31) ^ m + 392 * 56 ^ m + 525 * 21 ^ m + 162 * 18 ^ m -
      350 * 14 ^ m - 567 * 63 ^ m - 120 * (-24) ^ m
    have key : fourSC (Q m) (fun i => (kk i, -(kk i) ^ 3)) =
        48 * (1360488960000 : ℝ) ^ m * F := by
      simp only [fourSC, Q, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      rw [hterm, hterm, hterm, hterm, hterm, hterm, hterm, hterm]
      simp only [kk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      norm_num
      rw [show (14965378560000 : ℝ) = 1360488960000 * 11 by norm_num,
        show (-42175157760000 : ℝ) = 1360488960000 * (-31) by norm_num,
        show (76187381760000 : ℝ) = 1360488960000 * 56 by norm_num,
        show (28570268160000 : ℝ) = 1360488960000 * 21 by norm_num,
        show (24488801280000 : ℝ) = 1360488960000 * 18 by norm_num,
        show (19046845440000 : ℝ) = 1360488960000 * 14 by norm_num,
        show (85710804480000 : ℝ) = 1360488960000 * 63 by norm_num,
        show (-32651735040000 : ℝ) = 1360488960000 * (-24) by norm_num]
      simp only [mul_pow, F]
      ring
    -- The sign estimate: `F < 0` for every odd `m ≥ 3`.
    have hodd : Odd m := ⟨k, by omega⟩
    have negF : F < 0 := by
      have e31 : (-31 : ℝ) ^ m = -(31 ^ m) := hodd.neg_pow 31
      have e24 : (-24 : ℝ) ^ m = -(24 ^ m) := hodd.neg_pow 24
      simp only [F, e31, e24]
      rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h
      · rw [hm, h]; norm_num
      · rw [hm, h]; norm_num
      · have hm7 : 7 ≤ m := by omega
        have b11 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) (by norm_num : (11 : ℝ) ≤ 56) m
        have b31 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31) (by norm_num : (31 : ℝ) ≤ 56) m
        have b21 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 21) (by norm_num : (21 : ℝ) ≤ 56) m
        have b18 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 18) (by norm_num : (18 : ℝ) ≤ 56) m
        have b24 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 56) m
        have p14 : (0 : ℝ) ≤ 14 ^ m := by positivity
        have dom : ∀ j : ℕ, 7 ≤ j → (1267 : ℝ) * 56 ^ j < 567 * 63 ^ j := by
          intro j hj
          induction j, hj using Nat.le_induction with
          | base => norm_num
          | succ j _ ih =>
            have h63 : (0 : ℝ) < 63 ^ j := by positivity
            rw [pow_succ, pow_succ]
            nlinarith
        have := dom m hm7
        nlinarith
    rw [key]
    have hg : (0 : ℝ) < 1360488960000 ^ m := by positivity
    have : 48 * (1360488960000 : ℝ) ^ m * F < 0 := by
      have := mul_pos (by norm_num : (0 : ℝ) < 48) hg
      nlinarith
    exact this.ne

#print axioms result

end D5.S3.FluidDynamics.Solitons.GursesPekcanFourSoliton
