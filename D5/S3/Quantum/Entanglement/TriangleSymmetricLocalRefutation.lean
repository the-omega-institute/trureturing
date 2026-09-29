/- GID: D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.claim; result=D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result; claim=D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.claim
   digest: A fully symmetric triangle-local distribution has p(A=B=C) = 41/144 > 1/4. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  reduction `hint` of the triangle integral over [0,1]^3 to a count over the 12 source cells (with
  the cell measure `hcellInt` and the cell expansion `hexp`) and the kernel-checked count `hcount`
admission_basis: open-problem-resolution (issue #11256)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation

/-!
E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner, *Exploring the local landscape in the
triangle network*, arXiv:2405.08939 (Phys. Rev. A 111, 052453 (2025)). A distribution `p(a, b, c)`
with four outcomes per party is local in the triangle network if
`p(a,b,c) = ∫_{[0,1]³} p_A(a|β,γ) p_B(b|γ,α) p_C(c|α,β) dα dβ dγ`, and fully symmetric if it is
invariant under permutations of the parties and joint relabellings of the outcomes. The paper's
best local fully symmetric construction has `p(A = B = C) = 1/4`, and its conclusion asks whether
some local fully symmetric distribution has `p(A = B = C) > 1/4`. The answer is yes: each source
sends one of the 12 ordered pairs of distinct outcomes, and every party outputs the second entry
of its first source if that entry occurs in its second source, and the first entry otherwise.
This distribution is fully symmetric and has `p(A = B = C) = 41/144`.
-/

open MeasureTheory Set

/-- Eq. (trilocal) of arXiv:2405.08939: sources `α, β, γ` uniform on `[0,1]`, and conditional
distributions `p_A(a|β,γ)`, `p_B(b|γ,α)`, `p_C(c|α,β)`; here `t = (α, (β, γ))`. -/
def IsTriangleLocal (p : Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  ∃ pA pB pC : Fin 4 → ℝ → ℝ → ℝ,
    (∀ a, Measurable (Function.uncurry (pA a))) ∧ (∀ b, Measurable (Function.uncurry (pB b))) ∧
    (∀ c, Measurable (Function.uncurry (pC c))) ∧
    (∀ a x y, 0 ≤ pA a x y) ∧ (∀ b x y, 0 ≤ pB b x y) ∧ (∀ c x y, 0 ≤ pC c x y) ∧
    (∀ x y, ∑ a, pA a x y = 1) ∧ (∀ x y, ∑ b, pB b x y = 1) ∧ (∀ x y, ∑ c, pC c x y = 1) ∧
    ∀ a b c, p a b c = ∫ t in Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      pA a t.2.1 t.2.2 * pB b t.2.2 t.1 * pC c t.1 t.2.1

/-- Invariance under every permutation of the parties and every joint relabelling of the four
outcomes. -/
def FullySymmetric (p : Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ π : Equiv.Perm (Fin 3), ∀ o : Fin 3 → Fin 4,
      p (o (π 0)) (o (π 1)) (o (π 2)) = p (o 0) (o 1) (o 2)) ∧
    ∀ σ : Equiv.Perm (Fin 4), ∀ a b c, p (σ a) (σ b) (σ c) = p a b c

/-- `s₁₁₁(p) = p(A = B = C)`. -/
def s111 (p : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ := ∑ k, p k k k

/-- The negative answer to the open problem: every local fully symmetric distribution has
`p(A = B = C) ≤ 1/4`. -/
def claim : Prop := ∀ p, IsTriangleLocal p → FullySymmetric p → s111 p ≤ 1 / 4

/-- First entry of the ordered pair of distinct outcomes coded by `i`. -/
private def first (i : Fin 12) : Fin 4 := ⟨i.val / 3, by omega⟩

/-- Second entry of the ordered pair of distinct outcomes coded by `i`. -/
private def second (i : Fin 12) : Fin 4 :=
  ⟨i.val % 3 + if i.val / 3 ≤ i.val % 3 then 1 else 0, by split_ifs <;> omega⟩

/-- The 12-symbol response: `f(x, y) = x₂` if `x₂ ∈ {y₁, y₂}`, and `x₁` otherwise. -/
private def rule (x y : Fin 12) : Fin 4 :=
  if second x = first y ∨ second x = second y then second x else first x

/-- Source triples `(α, β, γ)` with outputs `(a, b, c)`. -/
private def count (a b c : Fin 4) : ℕ :=
  ((Finset.univ : Finset (Fin 12 × Fin 12 × Fin 12)).filter fun t =>
    rule t.2.1 t.2.2 = a ∧ rule t.2.2 t.1 = b ∧ rule t.1 t.2.1 = c).card

/-- The count by the number of distinct outcomes. -/
private def byDistinct (m : ℕ) : ℕ := if m = 1 then 123 else if m = 2 then 19 else 23

theorem result : ¬ claim := by
  intro h
  -- the cell of `t`: `q t = min ⌊12 t⌋ 11`
  let q : ℝ → Fin 12 := fun t => ⟨min ⌊12 * t⌋₊ 11, by omega⟩
  have hq : Measurable q := by
    have h1 : Measurable fun t : ℝ => ⌊12 * t⌋₊ := (measurable_id.const_mul 12).nat_floor
    have h2 : Measurable fun n : ℕ => (⟨min n 11, by omega⟩ : Fin 12) := measurable_from_nat
    exact h2.comp h1
  let resp : Fin 4 → ℝ → ℝ → ℝ := fun a x y => if rule (q x) (q y) = a then 1 else 0
  have hmeas : ∀ a, Measurable (Function.uncurry (resp a)) := by
    intro a
    have hc : Measurable fun ij : Fin 12 × Fin 12 => if rule ij.1 ij.2 = a then (1 : ℝ) else 0 :=
      measurable_of_countable _
    exact hc.comp ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))
  have hnonneg : ∀ a x y, 0 ≤ resp a x y := by
    intro a x y
    simp only [resp]
    split_ifs <;> norm_num
  have hsum : ∀ x y, ∑ a, resp a x y = 1 := by
    intro x y
    simp [resp, Finset.sum_ite_eq]
  -- the cell indicator and its integral over `[0,1]`
  let e : Fin 12 → ℝ → ℝ := fun i t => ({t | q t = i} : Set ℝ).indicator 1 t
  have hcell : ∀ i : Fin 12, MeasurableSet ({t | q t = i} : Set ℝ) :=
    fun i => hq (measurableSet_singleton i)
  have hcellInt : ∀ i : Fin 12, ∫ t, e i t ∂(volume.restrict (Icc (0 : ℝ) 1)) = 1 / 12 := by
    intro i
    rw [integral_indicator_one (hcell i), measureReal_restrict_apply (hcell i)]
    by_cases hi : i.val < 11
    · have hset : {t | q t = i} ∩ Icc (0 : ℝ) 1 = Ico ((i.val : ℝ) / 12) ((i.val + 1) / 12) := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ico, q, Fin.ext_iff]
        constructor
        · rintro ⟨hqt, h0, h1⟩
          have hfl : ⌊12 * t⌋₊ = i.val := by omega
          rw [Nat.floor_eq_iff (by linarith)] at hfl
          constructor <;> [rw [div_le_iff₀ (by norm_num)]; rw [lt_div_iff₀ (by norm_num)]] <;>
            linarith
        · rintro ⟨h0, h1⟩
          rw [div_le_iff₀ (by norm_num)] at h0
          rw [lt_div_iff₀ (by norm_num)] at h1
          have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
          have hfl : ⌊12 * t⌋₊ = i.val := by
            rw [Nat.floor_eq_iff (by linarith)]
            constructor <;> linarith
          have hi' : (i.val : ℝ) + 1 ≤ 11 := by exact_mod_cast hi
          refine ⟨by omega, by linarith, by linarith⟩
      rw [hset, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      ring
    · have hi11 : i.val = 11 := by omega
      have hset : {t | q t = i} ∩ Icc (0 : ℝ) 1 = Icc ((11 : ℝ) / 12) 1 := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, q, Fin.ext_iff, hi11]
        constructor
        · rintro ⟨hqt, h0, h1⟩
          have hfl : 11 ≤ ⌊12 * t⌋₊ := by omega
          rw [Nat.le_floor_iff (by linarith)] at hfl
          refine ⟨?_, h1⟩
          rw [div_le_iff₀ (by norm_num)]
          push_cast at hfl
          linarith
        · rintro ⟨h0, h1⟩
          rw [div_le_iff₀ (by norm_num)] at h0
          have hfl : 11 ≤ ⌊12 * t⌋₊ := by
            rw [Nat.le_floor_iff (by linarith)]
            push_cast
            linarith
          refine ⟨by omega, by linarith, h1⟩
      rw [hset, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num
  have hcellI : ∀ i : Fin 12, Integrable (e i) (volume.restrict (Icc (0 : ℝ) 1)) :=
    fun i => (integrable_const (1 : ℝ)).indicator (hcell i)
  -- expansion of a function of the three cells over the cells
  have hexp : ∀ (F : Fin 12 × Fin 12 × Fin 12 → ℝ) (α β γ : ℝ),
      F (q α, q β, q γ) = ∑ n, F n * (e n.1 α * (e n.2.1 β * e n.2.2 γ)) := by
    intro F α β γ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (q α)]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single (q β)]
      · rw [Finset.sum_eq_single (q γ)]
        · simp [e]
        · intro k _ hk
          simp [e, Ne.symm hk]
        · simp
      · intro j _ hj
        simp [e, Ne.symm hj]
      · simp
    · intro i _ hi
      simp [e, Ne.symm hi]
    · simp
  -- the integral of a function of the three cells
  have hint : ∀ F : Fin 12 × Fin 12 × Fin 12 → ℝ,
      ∫ t in Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), F (q t.1, q t.2.1, q t.2.2) =
        (∑ n, F n) / 1728 := by
    intro F
    have hμ : (volume : Measure (ℝ × ℝ × ℝ)).restrict
        (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) =
        (volume.restrict (Icc (0 : ℝ) 1)).prod
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
      rw [Measure.prod_restrict, Measure.prod_restrict]
      rfl
    rw [hμ]
    simp_rw [hexp F]
    rw [integral_finsetSum _ fun n _ =>
      ((hcellI n.1).mul_prod ((hcellI n.2.1).mul_prod (hcellI n.2.2))).const_mul (F n)]
    have hterm : ∀ n : Fin 12 × Fin 12 × Fin 12,
        ∫ t, F n * (e n.1 t.1 * (e n.2.1 t.2.1 * e n.2.2 t.2.2)) ∂((volume.restrict
          (Icc (0 : ℝ) 1)).prod ((volume.restrict (Icc (0 : ℝ) 1)).prod
            (volume.restrict (Icc (0 : ℝ) 1)))) = F n / 1728 := by
      intro n
      rw [integral_const_mul]
      rw [integral_prod_mul (f := e n.1) (g := fun w : ℝ × ℝ => e n.2.1 w.1 * e n.2.2 w.2)]
      rw [integral_prod_mul, hcellInt, hcellInt, hcellInt]
      ring
    rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_div]
  -- the kernel-checked count, by the number of distinct outcomes
  have hcount : ∀ a b c : Fin 4, count a b c = byDistinct ({a, b, c} : Finset (Fin 4)).card := by
    decide +kernel
  let p : Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c => (count a b c : ℝ) / 1728
  have hp : ∀ a b c, p a b c = (byDistinct ({a, b, c} : Finset (Fin 4)).card : ℝ) / 1728 := by
    intro a b c
    simp only [p, hcount]
  have hloc : IsTriangleLocal p := by
    refine ⟨resp, resp, resp, hmeas, hmeas, hmeas, hnonneg, hnonneg, hnonneg, hsum, hsum, hsum,
      fun a b c => ?_⟩
    let F : Fin 12 × Fin 12 × Fin 12 → ℝ := fun n =>
      if rule n.2.1 n.2.2 = a ∧ rule n.2.2 n.1 = b ∧ rule n.1 n.2.1 = c then 1 else 0
    have hF : ∀ t : ℝ × ℝ × ℝ,
        resp a t.2.1 t.2.2 * resp b t.2.2 t.1 * resp c t.1 t.2.1 = F (q t.1, q t.2.1, q t.2.2) := by
      intro t
      simp only [resp, F]
      split_ifs <;> simp_all
    simp_rw [hF]
    rw [hint F]
    simp only [p, count, F]
    rw [Finset.sum_boole]
  have himage : ∀ x : Fin 3 → Fin 4, ({x 0, x 1, x 2} : Finset (Fin 4)) = Finset.univ.image x := by
    intro x
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | h | h) <;> exact ⟨_, h.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hsym : FullySymmetric p := by
    refine ⟨fun π o => ?_, fun σ a b c => ?_⟩
    · have h1 := himage fun i => o (π i)
      have h2 : (Finset.univ.image fun i => o (π i)) = Finset.univ.image o := by
        rw [show (fun i => o (π i)) = o ∘ π from rfl, ← Finset.image_image,
          Finset.image_univ_equiv]
      rw [hp, hp, h1, h2, himage o]
    · rw [hp, hp]
      have : ({σ a, σ b, σ c} : Finset (Fin 4)) = ({a, b, c} : Finset (Fin 4)).image σ := by
        simp [Finset.image_insert, Finset.image_singleton]
      rw [this, Finset.card_image_of_injective _ σ.injective]
  have hs : s111 p = 41 / 144 := by
    simp only [s111, hp, Finset.insert_eq_of_mem, Finset.mem_singleton, Finset.card_singleton]
    simp [byDistinct]
    norm_num
  have := h p hloc hsym
  rw [hs] at this
  norm_num at this

end D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation
