/- GID: D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TriangleInequalityL1Refutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.claim; result=D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result; claim=D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.claim
   digest: A triangle-local model with s111 = 11/36 and Delta_1 = 0 refutes eq. ineq_l1. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  reduction `hint` of the triangle integral over [0,1]^3 to a count over the 24 source cells (with
  the cell measure `hcellInt` and the cell expansion `hexp`), the kernel-checked counts
  `checkPair_*` bridged by `hcountR`, and the vanishing penalty `hdelta`
admission_basis: open-problem-resolution (issue #11263)
Direct frozen dependencies: D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation (module
  statement_id sha256:26a81b4ab22f4c2a4d7b9f52ab319384d08eb0dea0b33b5ab91b298667c902cd):
  `IsTriangleLocal` (sha256:6b553395b1171be8c3a9c520cc992a1bc67b6abe283df4f95374c2296672c347),
  `s111` (sha256:c40ca860b36e25effc0d7a9a5ebe9414be4ca337073eb7d21c6bf0770406f3b2)
-/

import D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TriangleInequalityL1Refutation

/-!
E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner, *Exploring the local landscape in the
triangle network*, arXiv:2405.08939 (Phys. Rev. A 111, 052453 (2025)), penalise the asymmetry of a
four-outcome distribution by `Δ_l = Σ_X Σ_{(a,b,c) ∈ I_X} |M_X − p(a,b,c)|^l`, where `I_X` are the
outcome triples of type `111`, `112` and `123` (4, 36 and 24 of them) and `M_X` is the mean of `p`
over `I_X`. From neural-network estimates they state that approximately
`s₁₁₁(p) − 0.475 Δ_{l=1}(p) ≤ 0.289` (eq. `ineq_l1`) should hold for all local models. It fails:
each source sends one of the 24 orderings of the four outcomes, and a fixed response rule gives a
local distribution that is constant on each outcome type, so `Δ_{l=1} = 0`, with
`s₁₁₁ = 11/36 > 0.289`.
-/

open MeasureTheory Set
open D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation (IsTriangleLocal s111)

/-- The type of an outcome triple: the number of distinct outcomes among `a, b, c`
(1 for `111`, 2 for `112`, 3 for `123`). -/
def outcomeType (a b c : Fin 4) : ℕ := ({a, b, c} : Finset (Fin 4)).card

/-- `M_X`: the mean of `p` over the outcome triples of type `m`. -/
noncomputable def typeMean (p : Fin 4 → Fin 4 → Fin 4 → ℝ) (m : ℕ) : ℝ :=
  (∑ t ∈ (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).filter
      (fun t => outcomeType t.1 t.2.1 t.2.2 = m), p t.1 t.2.1 t.2.2) /
    ((Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).filter
      (fun t => outcomeType t.1 t.2.1 t.2.2 = m)).card

/-- `Δ_{l=1}`: the absolute deviations of `p` from the mean of its outcome type, summed over all
outcome triples. -/
noncomputable def deltaL1 (p : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, |typeMean p (outcomeType a b c) - p a b c|

/-- Eq. (`ineq_l1`) of arXiv:2405.08939: `s₁₁₁(p) − 0.475 Δ_{l=1}(p) ≤ 0.289` for every
local `p`. -/
def claim : Prop :=
  ∀ p, IsTriangleLocal p → s111 p - 475 / 1000 * deltaL1 p ≤ 289 / 1000

/-- First entry of the ordering of the four outcomes coded by `i < 24`. -/
private def first (i : ℕ) : ℕ := i / 6

/-- Second entry of the ordering coded by `i`. -/
private def second (i : ℕ) : ℕ := (i % 6) / 2 + if i / 6 ≤ (i % 6) / 2 then 1 else 0

/-- The smaller outcome not among the first two entries. -/
private def rest (i : ℕ) : ℕ :=
  if min (first i) (second i) > 0 then 0 else if max (first i) (second i) > 1 then 1 else 2

/-- Third entry of the ordering coded by `i`. -/
private def third (i : ℕ) : ℕ :=
  if i % 2 = 0 then rest i else 6 - first i - second i - rest i

/-- Position of the outcome `v` in the ordering coded by `j`. -/
private def pos (v j : ℕ) : ℕ :=
  if first j = v then 0 else if second j = v then 1 else if third j = v then 2 else 3

/-- The 24-symbol response: the earlier of `x₁, x₂` in `y` when one of them is in the first two
places of `y`, and otherwise `x₁` if it precedes `x₂` in `y`, and `x₃` if not. -/
private def rule (i j : ℕ) : ℕ :=
  if min (pos (first i) j) (pos (second i) j) ≤ 1 then
    (if pos (first i) j < pos (second i) j then first i else second i)
  else (if pos (first i) j < pos (second i) j then first i else third i)

/-- Source triples `(α, β, γ)` with outputs `(a, b, c)`. -/
private def count (a b c : ℕ) : ℕ :=
  ((List.range 24).map fun α => ((List.range 24).map fun β => ((List.range 24).map fun γ =>
    if rule β γ = a ∧ rule γ α = b ∧ rule α β = c then 1 else 0).sum).sum).sum

/-- The count by the number of distinct outputs. -/
private def byType (m : ℕ) : ℕ := if m = 1 then 1056 else if m = 2 then 148 else 178

/-- The four counts with first two outputs `a, b`. -/
private def checkPair (a b : ℕ) : Bool :=
  [0, 1, 2, 3].all fun c =>
    count a b c == byType (if a = b ∧ b = c then 1 else if a = b ∨ b = c ∨ a = c then 2 else 3)

private theorem checkPair_0_0 : checkPair 0 0 = true := by decide +kernel

private theorem checkPair_0_1 : checkPair 0 1 = true := by decide +kernel

private theorem checkPair_0_2 : checkPair 0 2 = true := by decide +kernel

private theorem checkPair_0_3 : checkPair 0 3 = true := by decide +kernel

private theorem checkPair_1_0 : checkPair 1 0 = true := by decide +kernel

private theorem checkPair_1_1 : checkPair 1 1 = true := by decide +kernel

private theorem checkPair_1_2 : checkPair 1 2 = true := by decide +kernel

private theorem checkPair_1_3 : checkPair 1 3 = true := by decide +kernel

private theorem checkPair_2_0 : checkPair 2 0 = true := by decide +kernel

private theorem checkPair_2_1 : checkPair 2 1 = true := by decide +kernel

private theorem checkPair_2_2 : checkPair 2 2 = true := by decide +kernel

private theorem checkPair_2_3 : checkPair 2 3 = true := by decide +kernel

private theorem checkPair_3_0 : checkPair 3 0 = true := by decide +kernel

private theorem checkPair_3_1 : checkPair 3 1 = true := by decide +kernel

private theorem checkPair_3_2 : checkPair 3 2 = true := by decide +kernel

private theorem checkPair_3_3 : checkPair 3 3 = true := by decide +kernel

/-- Every response is one of the four outcomes. -/
private def ruleBound : Bool :=
  (List.range 24).all fun i => (List.range 24).all fun j => decide (rule i j < 4)

private theorem ruleBound_eq : ruleBound = true := by decide +kernel

theorem result : ¬ claim := by
  intro h
  -- the kernel-checked facts, read off the four row checks and the bound check
  have hbound : ∀ i < 24, ∀ j < 24, rule i j < 4 := by
    intro i hi j hj
    have h1 := List.all_eq_true.mp ruleBound_eq i (List.mem_range.mpr hi)
    have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
    simpa using h2
  have hrow : ∀ a < 4, ∀ b < 4, ∀ c < 4, count a b c =
      byType (if a = b ∧ b = c then 1 else if a = b ∨ b = c ∨ a = c then 2 else 3) := by
    intro a ha b hb c hc
    have hr : checkPair a b = true := by
      interval_cases a <;> interval_cases b
      exacts [checkPair_0_0, checkPair_0_1, checkPair_0_2, checkPair_0_3, checkPair_1_0,
        checkPair_1_1, checkPair_1_2, checkPair_1_3, checkPair_2_0, checkPair_2_1, checkPair_2_2,
        checkPair_2_3, checkPair_3_0, checkPair_3_1, checkPair_3_2, checkPair_3_3]
    have hc' : c ∈ [0, 1, 2, 3] := by interval_cases c <;> simp
    have h1 := List.all_eq_true.mp hr c hc'
    simpa using h1
  -- the cell of `t`: `q t = min ⌊24 t⌋ 23`
  let q : ℝ → Fin 24 := fun t => ⟨min ⌊24 * t⌋₊ 23, by omega⟩
  have hq : Measurable q := by
    have h1 : Measurable fun t : ℝ => ⌊24 * t⌋₊ := (measurable_id.const_mul 24).nat_floor
    have h2 : Measurable fun n : ℕ => (⟨min n 23, by omega⟩ : Fin 24) := measurable_from_nat
    exact h2.comp h1
  let resp : Fin 4 → ℝ → ℝ → ℝ := fun a x y => if rule (q x).val (q y).val = a.val then 1 else 0
  have hmeas : ∀ a, Measurable (Function.uncurry (resp a)) := by
    intro a
    have hc : Measurable fun ij : Fin 24 × Fin 24 =>
        if rule ij.1.val ij.2.val = a.val then (1 : ℝ) else 0 :=
      measurable_of_countable _
    exact hc.comp ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))
  have hnonneg : ∀ a x y, 0 ≤ resp a x y := by
    intro a x y
    simp only [resp]
    split_ifs <;> norm_num
  have hsum : ∀ x y, ∑ a, resp a x y = 1 := by
    intro x y
    have hr := hbound _ (q x).isLt _ (q y).isLt
    simp only [resp]
    generalize rule (q x).val (q y).val = r at hr ⊢
    rw [Fin.sum_univ_four]
    interval_cases r <;> norm_num
  -- the cell indicator and its integral over `[0,1]`
  let e : Fin 24 → ℝ → ℝ := fun i t => ({t | q t = i} : Set ℝ).indicator 1 t
  have hcell : ∀ i : Fin 24, MeasurableSet ({t | q t = i} : Set ℝ) :=
    fun i => hq (measurableSet_singleton i)
  have hcellInt : ∀ i : Fin 24, ∫ t, e i t ∂(volume.restrict (Icc (0 : ℝ) 1)) = 1 / 24 := by
    intro i
    rw [integral_indicator_one (hcell i), measureReal_restrict_apply (hcell i)]
    by_cases hi : i.val < 23
    · have hset : {t | q t = i} ∩ Icc (0 : ℝ) 1 = Ico ((i.val : ℝ) / 24) ((i.val + 1) / 24) := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ico, q, Fin.ext_iff]
        constructor
        · rintro ⟨hqt, h0, h1⟩
          have hfl : ⌊24 * t⌋₊ = i.val := by omega
          rw [Nat.floor_eq_iff (by linarith)] at hfl
          constructor <;> [rw [div_le_iff₀ (by norm_num)]; rw [lt_div_iff₀ (by norm_num)]] <;>
            linarith
        · rintro ⟨h0, h1⟩
          rw [div_le_iff₀ (by norm_num)] at h0
          rw [lt_div_iff₀ (by norm_num)] at h1
          have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
          have hfl : ⌊24 * t⌋₊ = i.val := by
            rw [Nat.floor_eq_iff (by linarith)]
            constructor <;> linarith
          have hi' : (i.val : ℝ) + 1 ≤ 23 := by exact_mod_cast hi
          refine ⟨by omega, by linarith, by linarith⟩
      rw [hset, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      ring
    · have hi23 : i.val = 23 := by omega
      have hset : {t | q t = i} ∩ Icc (0 : ℝ) 1 = Icc ((23 : ℝ) / 24) 1 := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, q, Fin.ext_iff, hi23]
        constructor
        · rintro ⟨hqt, h0, h1⟩
          have hfl : 23 ≤ ⌊24 * t⌋₊ := by omega
          rw [Nat.le_floor_iff (by linarith)] at hfl
          refine ⟨?_, h1⟩
          rw [div_le_iff₀ (by norm_num)]
          push_cast at hfl
          linarith
        · rintro ⟨h0, h1⟩
          rw [div_le_iff₀ (by norm_num)] at h0
          have hfl : 23 ≤ ⌊24 * t⌋₊ := by
            rw [Nat.le_floor_iff (by linarith)]
            push_cast
            linarith
          refine ⟨by omega, by linarith, h1⟩
      rw [hset, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num
  have hcellI : ∀ i : Fin 24, Integrable (e i) (volume.restrict (Icc (0 : ℝ) 1)) :=
    fun i => (integrable_const (1 : ℝ)).indicator (hcell i)
  -- expansion of a function of the three cells over the cells
  have hexp : ∀ (F : Fin 24 × Fin 24 × Fin 24 → ℝ) (α β γ : ℝ),
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
  have hint : ∀ F : Fin 24 × Fin 24 × Fin 24 → ℝ,
      ∫ t in Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), F (q t.1, q t.2.1, q t.2.2) =
        (∑ n, F n) / 13824 := by
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
    have hterm : ∀ n : Fin 24 × Fin 24 × Fin 24,
        ∫ t, F n * (e n.1 t.1 * (e n.2.1 t.2.1 * e n.2.2 t.2.2)) ∂((volume.restrict
          (Icc (0 : ℝ) 1)).prod ((volume.restrict (Icc (0 : ℝ) 1)).prod
            (volume.restrict (Icc (0 : ℝ) 1)))) = F n / 13824 := by
      intro n
      rw [integral_const_mul]
      rw [integral_prod_mul (f := e n.1) (g := fun w : ℝ × ℝ => e n.2.1 w.1 * e n.2.2 w.2)]
      rw [integral_prod_mul, hcellInt, hcellInt, hcellInt]
      ring
    rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_div]
  -- the triangle sum of a count indicator is the list count
  have hlist : ∀ (f : ℕ → ℕ) (n : ℕ), ((List.range n).map f).sum = ∑ x ∈ Finset.range n, f x := by
    intro f n
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
      Multiset.sum_coe]
  have hcountR : ∀ a b c : Fin 4, (∑ n : Fin 24 × Fin 24 × Fin 24,
      if rule n.2.1.val n.2.2.val = a.val ∧ rule n.2.2.val n.1.val = b.val ∧
        rule n.1.val n.2.1.val = c.val then (1 : ℝ) else 0) = (count a.val b.val c.val : ℝ) := by
    intro a b c
    simp only [count, hlist]
    simp_rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_prod_type]
    push_cast
    rfl
  have htype : ∀ a b c : Fin 4,
      (if a.val = b.val ∧ b.val = c.val then 1
        else if a.val = b.val ∨ b.val = c.val ∨ a.val = c.val then 2 else 3) =
        outcomeType a b c := by
    decide +kernel
  let p : Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c => (byType (outcomeType a b c) : ℝ) / 13824
  have hloc : IsTriangleLocal p := by
    refine ⟨resp, resp, resp, hmeas, hmeas, hmeas, hnonneg, hnonneg, hnonneg, hsum, hsum, hsum,
      fun a b c => ?_⟩
    let F : Fin 24 × Fin 24 × Fin 24 → ℝ := fun n =>
      if rule n.2.1.val n.2.2.val = a.val ∧ rule n.2.2.val n.1.val = b.val ∧
        rule n.1.val n.2.1.val = c.val then 1 else 0
    have hF : ∀ t : ℝ × ℝ × ℝ,
        resp a t.2.1 t.2.2 * resp b t.2.2 t.1 * resp c t.1 t.2.1 = F (q t.1, q t.2.1, q t.2.2) := by
      intro t
      simp only [resp, F]
      by_cases hA : rule (q t.2.1).val (q t.2.2).val = a.val <;>
        by_cases hB : rule (q t.2.2).val (q t.1).val = b.val <;>
          by_cases hC : rule (q t.1).val (q t.2.1).val = c.val <;>
            simp only [hA, hB, hC, if_true, if_false, and_self, and_true, and_false, mul_one,
              mul_zero]
    simp_rw [hF]
    rw [hint F, hcountR a b c, hrow _ a.isLt _ b.isLt _ c.isLt, htype]
  have hdelta : deltaL1 p = 0 := by
    have hmean : ∀ a b c : Fin 4, typeMean p (outcomeType a b c) = p a b c := by
      intro a b c
      simp only [typeMean]
      rw [Finset.sum_congr rfl fun t ht => show p t.1 t.2.1 t.2.2 = p a b c by
        simp only [p, (Finset.mem_filter.mp ht).2], Finset.sum_const, nsmul_eq_mul]
      have hne : ((Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).filter
          (fun t => outcomeType t.1 t.2.1 t.2.2 = outcomeType a b c)).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨(a, b, c), by simp⟩
      field_simp
    simp [deltaL1, hmean]
  have hs : s111 p = 11 / 36 := by
    have hk : ∀ k : Fin 4, outcomeType k k k = 1 := by
      intro k
      simp [outcomeType]
    simp only [s111, p, hk, Fin.sum_univ_four]
    norm_num [byType]
  have := h p hloc
  rw [hs, hdelta] at this
  norm_num at this

end D5.S3.Quantum.Entanglement.TriangleInequalityL1Refutation
