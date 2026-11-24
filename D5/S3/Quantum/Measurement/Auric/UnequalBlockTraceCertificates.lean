/- GID: D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Direct and complementary spectral entropy certificates for strict traces. -/

import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Tuple.Sort

/-! # Trace certificates for three effects with unequal rank caps -/

namespace D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private def allowedRows (c : Fin 4) : Finset (Fin 3) :=
  univ.filter (fun j => c ≠ j.castSucc)

private theorem mem_allowedRows (c : Fin 4) (j : Fin 3) :
    j ∈ allowedRows c ↔ c ≠ j.castSucc := by
  simp [allowedRows]

private theorem last_mem_allowedRows (j : Fin 3) : j ∈ allowedRows (Fin.last 3) :=
  (mem_allowedRows _ _).2 (Fin.castSucc_ne_last j).symm

private theorem allowedRows_nonempty (c : Fin 4) : (allowedRows c).Nonempty := by
  fin_cases c <;> decide

private theorem multiplicity_last (l : Fin 3 → ℕ) (b : ℕ) :
    multiplicity l b (Fin.last 3) = b := rfl

private def priceObjective (l : Fin 3 → ℕ) (b : ℕ) (τ : Fin 3 → ℝ)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ) (u : Fin 3 → ℝ) : ℝ :=
  (∑ c, (multiplicity l b c : ℝ) * G c u) - ∑ j, τ j * u j

private theorem priceObjective_shift (l : Fin 3 → ℕ) (b : ℕ) (d : ℝ) (τ : Fin 3 → ℝ)
    (hd : (b : ℝ) + ∑ j, (l j : ℝ) = d) (hτ : ∑ j, τ j = d)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ)
    (hG : ∀ c u a, G c (fun j => u j + a) = G c u + a)
    (u : Fin 3 → ℝ) (a : ℝ) :
    priceObjective l b τ G (fun j => u j + a) = priceObjective l b τ G u := by
  unfold priceObjective
  simp only [hG, mul_add, sum_add_distrib, ← sum_mul, hτ]
  have hc : (∑ c, (multiplicity l b c : ℝ)) = d := by
    rw [Fin.sum_univ_castSucc]
    simp only [multiplicity_missing, multiplicity_last, add_comm _ (b : ℝ), hd]
  rw [hc]
  ring

/-- A column potential that dominates each allowed price gives a uniform
lower bound in terms of the largest difference of row prices. -/
private theorem price_coercivity (l : Fin 3 → ℕ) (b : ℕ) (d : ℝ) (τ : Fin 3 → ℝ)
    (hd : (b : ℝ) + ∑ j, (l j : ℝ) = d) (hτ : ∑ j, τ j = d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < d - l j)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ)
    (hG : ∀ c u j, j ∈ allowedRows c → u j ≤ G c u) :
    ∃ δ > 0, ∀ u i k, δ * (u i - u k) ≤ priceObjective l b τ G u := by
  classical
  let margin (j : Fin 3) := min (τ j) (d - l j - τ j)
  obtain ⟨r, _, hr⟩ := univ.exists_min_image margin Finset.univ_nonempty
  let δ := margin r
  have hδ : 0 < δ := lt_min (hpos r) (sub_pos.mpr (hupper r))
  have hδτ (j : Fin 3) : δ ≤ τ j :=
    (hr j (mem_univ j)).trans (min_le_left _ _)
  have hδcap (j : Fin 3) : δ ≤ d - l j - τ j :=
    (hr j (mem_univ j)).trans (min_le_right _ _)
  refine ⟨δ, hδ, fun u i k => ?_⟩
  obtain ⟨j, _, hj⟩ := univ.exists_max_image u Finset.univ_nonempty
  let rest := (univ : Finset (Fin 3)).erase j
  have hrest : rest.Nonempty := by
    fin_cases j <;> decide
  obtain ⟨s, hs, hsecond⟩ := rest.exists_max_image u hrest
  have hsne : s ≠ j := (mem_erase.mp hs).1
  have hsj : u s ≤ u j := hj s (mem_univ s)
  have hfull : u j ≤ G (Fin.last 3) u := hG _ _ _ (last_mem_allowedRows j)
  have hmissing : ∑ a, (l a : ℝ) * (if a = j then u s else u j) ≤
      ∑ a, (l a : ℝ) * G a.castSucc u := by
    apply sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    by_cases ha : a = j
    · subst a
      exact (ite_eq_left rfl).trans_le (hG _ _ _ ((mem_allowedRows _ _).2
        (fun h => hsne (Fin.castSucc_injective _ h.symm))))
    · exact (ite_eq_right ha).trans_le (hG _ _ _ ((mem_allowedRows _ _).2
        (fun h => ha (Fin.castSucc_injective _ h))))
  have hsplit (f : Fin 3 → ℝ) : (∑ a ∈ rest, f a) + f j = ∑ a, f a :=
    sum_erase_add _ _ (mem_univ j)
  have hsum_l : (b : ℝ) + ∑ a ∈ rest, (l a : ℝ) = d - l j := by
    linarith [hsplit (fun a => (l a : ℝ))]
  have hsum_τ : ∑ a ∈ rest, τ a = d - τ j := by
    linarith [hsplit τ]
  rw [← hsplit (fun a => (l a : ℝ) * (if a = j then u s else u j))] at hmissing
  have hmissing' : (∑ a ∈ rest, (l a : ℝ)) * u j + l j * u s ≤
      ∑ a, (l a : ℝ) * G a.castSucc u := by
    rw [Finset.sum_mul]
    have hrw : (∑ a ∈ rest, (l a : ℝ) * (if a = j then u s else u j)) =
        ∑ a ∈ rest, (l a : ℝ) * u j := by
      apply sum_congr rfl
      intro a ha
      rw [ite_eq_right (mem_erase.mp ha).1]
    rw [hrw] at hmissing
    simpa using hmissing
  have hdecomp :
      (d - l j - τ j) * (u j - u s) + ∑ a ∈ rest, τ a * (u s - u a) ≤
        priceObjective l b τ G u := by
    unfold priceObjective
    rw [Fin.sum_univ_castSucc, ← hsplit (fun a => τ a * u a)]
    simp only [multiplicity_missing, multiplicity_last, mul_sub, sum_sub_distrib,
      ← Finset.sum_mul, hsum_τ]
    have hfull' := mul_le_mul_of_nonneg_left hfull (Nat.cast_nonneg b)
    have hl := congrArg (fun x : ℝ => x * u j) hsum_l
    linarith only [hmissing', hfull', hl]
  have hgap := mul_le_mul_of_nonneg_right (hδcap j) (sub_nonneg.mpr hsj)
  have hterms (a : Fin 3) (ha : a ∈ rest) : 0 ≤ τ a * (u s - u a) :=
    mul_nonneg (hpos a).le (sub_nonneg.mpr (hsecond a ha))
  have htop : δ * (u j - u k) ≤ priceObjective l b τ G u := by
    by_cases hk : k = j
    · subst k
      simp only [sub_self, mul_zero]
      exact (add_nonneg (mul_nonneg (sub_pos.mpr (hupper j)).le (sub_nonneg.mpr hsj))
        (sum_nonneg hterms)).trans hdecomp
    · have hk' : k ∈ rest := mem_erase.mpr ⟨hk, mem_univ k⟩
      have hkterm := mul_le_mul_of_nonneg_right (hδτ k) (sub_nonneg.mpr (hsecond k hk'))
      have hsum := single_le_sum hterms hk'
      linarith only [hgap, hkterm, hsum, hdecomp]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (hj i (mem_univ i)) _) hδ.le).trans htop

private theorem exists_minimum_prices (F : (Fin 3 → ℝ) → ℝ) (hF : Continuous F)
    (hshift : ∀ u a, F (fun j => u j + a) = F u)
    {δ : ℝ} (hδ : 0 < δ) (hbound : ∀ u i k, δ * (u i - u k) ≤ F u) :
    ∃ u, ∀ v, F u ≤ F v := by
  let S : Set (Fin 3 → ℝ) := {u | u 0 = 0 ∧ F u ≤ F 0}
  let R := F 0 / δ
  have hclosed : IsClosed S :=
    (isClosed_eq (continuous_apply 0) continuous_const).inter
      (isClosed_le hF continuous_const)
  have hcompact : IsCompact S := by
    apply (isCompact_Icc (a := fun _ : Fin 3 => -R) (b := fun _ => R)).of_isClosed_subset hclosed
    intro u hu
    change u 0 = 0 ∧ F u ≤ F 0 at hu
    constructor
    · intro i
      have h := (hbound u 0 i).trans hu.2
      rw [hu.1, zero_sub] at h
      have h' : -u i ≤ R := (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using h)
      linarith
    · intro i
      have h := (hbound u i 0).trans hu.2
      rw [hu.1, sub_zero] at h
      exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using h)
  have hzero : (0 : Fin 3 → ℝ) ∈ S := ⟨rfl, le_rfl⟩
  obtain ⟨u, _, hu⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hF.continuousOn
  refine ⟨u, fun v => ?_⟩
  by_cases hv : F v ≤ F 0
  · let v' : Fin 3 → ℝ := fun j => v j + -v 0
    have hs : F v' = F v := hshift v _
    rw [← hs]
    exact hu (show v' ∈ S from ⟨by simp [v'], hs.trans_le hv⟩)
  · exact (hu hzero).trans (le_of_not_ge hv)

private def expSum (c : Fin 4) (u : Fin 3 → ℝ) : ℝ :=
  ∑ j ∈ allowedRows c, Real.exp (u j)

private theorem expSum_pos (c : Fin 4) (u : Fin 3 → ℝ) : 0 < expSum c u :=
  sum_pos (fun j _ => Real.exp_pos (u j)) (allowedRows_nonempty c)

private theorem le_log_expSum (c : Fin 4) (u : Fin 3 → ℝ) (j : Fin 3)
    (hj : j ∈ allowedRows c) : u j ≤ Real.log (expSum c u) := by
  rw [← Real.log_exp (u j)]
  exact Real.log_le_log (Real.exp_pos _) (single_le_sum (fun i _ => (Real.exp_pos (u i)).le) hj)

private theorem expSum_last (u : Fin 3 → ℝ) :
    expSum (Fin.last 3) u = ∑ j, Real.exp (u j) := by
  unfold expSum allowedRows
  rw [filter_eq_self.mpr]
  exact fun j _ => (mem_allowedRows _ _).1 (last_mem_allowedRows j)

private theorem expSum_castSucc (u : Fin 3 → ℝ) (j : Fin 3) :
    expSum j.castSucc u = expSum (Fin.last 3) u - Real.exp (u j) := by
  rw [expSum_last, eq_sub_iff_add_eq]
  unfold expSum allowedRows
  have h : univ.filter (fun a : Fin 3 => j.castSucc ≠ a.castSucc) = univ.erase j := by
    ext a
    simp [Fin.ext_iff, ne_comm]
  rw [h]
  exact sum_erase_add _ _ (mem_univ j)

private theorem columnDenominator_castSucc (w : Fin 3 → ℝ) (j : Fin 3) :
    columnDenominator w j.castSucc = 1 - w j := by
  fin_cases j <;> rfl

private theorem derivative_log_expSum (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4)
    (w : Fin 3 → ℝ) (hw : ∀ i, w i = Real.exp (u i) / expSum (Fin.last 3) u) :
    HasDerivAt (fun t : ℝ => Real.log (expSum c (fun i => u i + if i = j then t else 0)))
      (allocation (weightEntries w) j c) 0 := by
  classical
  have hd (i : Fin 3) : HasDerivAt
      (fun t : ℝ => Real.exp (u i + if i = j then t else 0))
      (if i = j then Real.exp (u i) else 0) 0 := by
    by_cases hij : i = j
    · simpa [hij] using (((hasDerivAt_id (0 : ℝ)).const_add (u i)).exp)
    · simpa [hij] using (hasDerivAt_const (0 : ℝ) (Real.exp (u i)))
  have hz (i : Fin 3) : u i + (if i = j then (0 : ℝ) else 0) = u i := by simp
  have h := (HasDerivAt.fun_sum (u := allowedRows c) (fun i _ => hd i)).log
    (by simpa only [hz, expSum] using (expSum_pos c u).ne')
  simp only [hz, Finset.sum_ite_eq', mem_allowedRows] at h
  change HasDerivAt (fun t : ℝ =>
    Real.log (∑ i ∈ allowedRows c, Real.exp (u i + if i = j then t else 0))) _ 0
  have hden : expSum c u = columnDenominator w c * expSum (Fin.last 3) u := by
    refine Fin.lastCases ?_ (fun a => ?_) c
    · change _ = 1 * _
      rw [one_mul]
    · rw [expSum_castSucc]
      rw [columnDenominator_castSucc, hw, sub_mul, one_mul,
        div_mul_cancel₀ _ (expSum_pos _ _).ne']
  have heq : ((if c ≠ j.castSucc then Real.exp (u j) else 0) / expSum c u) =
      allocation (weightEntries w) j c := by
    by_cases hc : c = j.castSucc
    · simp [allocation, hc]
    · simp [allocation, weightEntries, hc, hw, hden, div_div, mul_comm]
  rw [← heq]
  exact h

/-- Every strictly admissible trace triple admits positive normalized direct
entropy weights. The row equations use the original labels. -/
theorem exists_direct_certificate (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hcap : ∑ j, (d - m j) ≤ d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (htotal : ∑ j, τ j = d) :
    ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧ (∑ j, w j = 1) ∧
      ∀ j, weightMass (fun j => d - m j) (d - ∑ i, (d - m i)) w j = τ j := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ i, l i
  let G (c : Fin 4) (u : Fin 3 → ℝ) := Real.log (expSum c u)
  let F := priceObjective l b τ G
  have hcount : (b : ℝ) + ∑ j, (l j : ℝ) = d := by
    exact_mod_cast Nat.sub_add_cancel hcap
  obtain ⟨δ, hδ, hbound⟩ := price_coercivity l b d τ hcount htotal hpos hupper G le_log_expSum
  have hF : Continuous F := by
    have hG (c : Fin 4) : Continuous (G c) := by
      apply Continuous.log
      · exact continuous_finsetSum _ (fun j _ => Real.continuous_exp.comp (continuous_apply j))
      · exact fun u => (expSum_pos c u).ne'
    exact (continuous_finsetSum _ (fun c _ => continuous_const.mul (hG c))).sub
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
  have hshift (u : Fin 3 → ℝ) (a : ℝ) (c : Fin 4) :
      G c (fun j => u j + a) = G c u + a := by
    change Real.log (∑ j ∈ allowedRows c, Real.exp (u j + a)) = Real.log (expSum c u) + a
    simp only [Real.exp_add, ← Finset.sum_mul]
    change Real.log (expSum c u * Real.exp a) = _
    rw [Real.log_mul (expSum_pos c u).ne' (Real.exp_pos a).ne', Real.log_exp]
  obtain ⟨u, hu⟩ := exists_minimum_prices F hF
    (priceObjective_shift l b d τ hcount htotal G (fun c u a => hshift u a c)) hδ hbound
  let w (j : Fin 3) := Real.exp (u j) / expSum (Fin.last 3) u
  refine ⟨w, fun j => div_pos (Real.exp_pos _) (expSum_pos _ _), ?_, fun j => ?_⟩
  · change (∑ j, Real.exp (u j) / expSum (Fin.last 3) u) = 1
    rw [← Finset.sum_div, ← expSum_last, div_self (expSum_pos _ _).ne']
  · let line (t : ℝ) (i : Fin 3) := u i + if i = j then t else 0
    have hlin (i : Fin 3) : HasDerivAt (fun t => τ i * line t i)
        (if i = j then τ i else 0) 0 := by
      by_cases hij : i = j
      · simpa [line, hij] using (((hasDerivAt_id (0 : ℝ)).const_add (u i)).const_mul (τ i))
      · simpa [line, hij] using (hasDerivAt_const (0 : ℝ) (τ i * u i))
    have hD := (HasDerivAt.fun_sum (u := univ) (fun c _ =>
      (derivative_log_expSum u j c w (fun _ => rfl)).const_mul (multiplicity l b c : ℝ))).sub
        (HasDerivAt.fun_sum (u := univ) (fun i _ => hlin i))
    simp only [Finset.sum_ite_eq', mem_univ, ite_true] at hD
    have hMin : IsMinOn (fun t => F (line t)) Set.univ 0 := by
      intro t _
      have h0 : line 0 = u := by funext i; simp [line]
      change F (line 0) ≤ F (line t)
      rw [h0]
      exact hu (line t)
    have hzero := hMin.isLocalMin (by simp)
    exact sub_eq_zero.mp (hD.deriv.symm.trans hzero.deriv_eq_zero)

private theorem weightMass_relabel (e : Equiv.Perm (Fin 3)) (l : Fin 3 → ℕ) (b : ℕ)
    (w : Fin 3 → ℝ) (j : Fin 3) :
    weightMass (l ∘ e) b (w ∘ e) j = weightMass l b w (e j) := by
  have hlast (v : Fin 3 → ℝ) (i : Fin 3) :
      allocation (weightEntries v) i (Fin.last 3) = v i := by
    have h := (mem_allowedRows _ _).1 (last_mem_allowedRows i)
    change (if Fin.last 3 = i.castSucc then 0 else v i / 1) = v i
    rw [ite_eq_right h, div_one]
  have hmiss (v : Fin 3 → ℝ) (i k : Fin 3) :
      allocation (weightEntries v) i k.castSucc = if k = i then 0 else v i / (1 - v k) := by
    simp [allocation, weightEntries, columnDenominator_castSucc, Fin.ext_iff]
  unfold weightMass
  conv_lhs => rw [Fin.sum_univ_castSucc]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [multiplicity_missing, multiplicity_last, hlast, hmiss, Function.comp_apply]
  congr 1
  simpa only [e.apply_eq_iff_eq] using Equiv.sum_comp e
    (fun k => (l k : ℝ) * (if k = e j then 0 else w (e j) / (1 - w k)))

private theorem feasible_relabel (e : Equiv.Perm (Fin 3)) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A) :
    Feasible (m ∘ e) (τ ∘ e) (A ∘ e) :=
  ⟨fun j => hA.1 (e j), (Equiv.sum_comp e A).trans hA.2.1, fun j => hA.2.2.1 (e j),
    fun j => hA.2.2.2 (e j)⟩

private theorem spectralValues_relabel (e : Equiv.Perm (Fin 3)) (f : ℝ → ℝ)
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) :
    {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible (m ∘ e) (τ ∘ e) A,
      spectralSum f A hA.1 = v} =
    {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum f A hA.1 = v} := by
  ext v
  constructor <;> rintro ⟨A, hA, rfl⟩
  · have h := feasible_relabel e.symm _ _ A hA
    have h' : Feasible m τ (A ∘ e.symm) := by simpa [Function.comp_def] using h
    exact ⟨_, h', Equiv.sum_comp e.symm
      (fun j => ∑ i, f ((hA.1 j).isHermitian.eigenvalues i))⟩
  · refine ⟨_, feasible_relabel e m τ A hA, ?_⟩
    exact Equiv.sum_comp e (fun j => ∑ i, f ((hA.1 j).isHermitian.eigenvalues i))

/-- The direct entropy maximum for strictly admissible traces is attained by
the proportional allocation after sorting the weights and relabeling the rows. -/
theorem exists_isGreatest_direct (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hcap : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (Fintype.card n : ℝ) - (Fintype.card n - m j : ℕ))
    (htotal : ∑ j, τ j = Fintype.card n) :
    ∃ (e : Equiv.Perm (Fin 3)) (w : Fin 3 → ℝ), Antitone w ∧
      IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
        spectralSum Real.negMulLog A hA.1 = v}
        (allocationValue Real.negMulLog (fun j => Fintype.card n - m (e j))
          (Fintype.card n - ∑ j, (Fintype.card n - m j)) (weightEntries w)) := by
  let l (j : Fin 3) := Fintype.card n - m j
  obtain ⟨w, hw, hwt, hr⟩ :=
    exists_direct_certificate (Fintype.card n) m τ hcap hpos hupper htotal
  let e := Tuple.sort (fun j => -w j)
  have he : Antitone (w ∘ e) := fun _ _ hij =>
    neg_le_neg_iff.mp (Tuple.monotone_sort (fun j => -w j) hij)
  have hc : (∑ j, l (e j)) = ∑ j, l j := Equiv.sum_comp e l
  have hcap' : (∑ j, l (e j)) ≤ Fintype.card n := hc.trans_le hcap
  have hr' (j : Fin 3) : weightMass (l ∘ e)
      (Fintype.card n - ∑ i, l (e i)) (w ∘ e) j = τ (e j) := by
    rw [hc, weightMass_relabel]
    exact hr (e j)
  have hm := isGreatest_direct (n := n) (m ∘ e) (τ ∘ e) (w ∘ e) hcap'
    (fun j => hw (e j)) ((Equiv.sum_comp e w).trans hwt) he hr'
  change IsGreatest _ (allocationValue Real.negMulLog (l ∘ e)
    (Fintype.card n - ∑ j, l (e j)) (weightEntries (w ∘ e))) at hm
  rw [spectralValues_relabel, hc] at hm
  exact ⟨e, w ∘ e, he, hm⟩

private def pairWeight (w : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin 3)).erase j, w i

private theorem pairWeight_eq (w : Fin 3 → ℝ) (j : Fin 3) :
    pairWeight w j = (∑ i, w i) - w j :=
  eq_sub_iff_add_eq.2 (sum_erase_add _ _ (mem_univ j))

private theorem pairWeight_pos (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (j : Fin 3) :
    0 < pairWeight w j := by
  apply sum_pos (fun i _ => hw i)
  fin_cases j <;> decide

private def complementScales (w : Fin 3 → ℝ) (c : Fin 4) : ℝ :=
  Fin.lastCases
    (max (2 / ∑ i, w i) (univ.sup' univ_nonempty (fun i => (pairWeight w i)⁻¹)))
    (fun i => (pairWeight w i)⁻¹) c

private theorem complementScales_pos (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (c : Fin 4) :
    0 < complementScales w c := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · exact (div_pos two_pos (sum_pos (fun i _ => hw i) univ_nonempty)).trans_le (le_max_left _ _)
  · simpa only [complementScales, Fin.lastCases_castSucc] using inv_pos.mpr (pairWeight_pos w hw i)

private theorem clipped_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    max 0 (1 - a * (a + b)⁻¹) + max 0 (1 - b * (a + b)⁻¹) = 1 := by
  have hab := add_pos ha hb
  have h (x : ℝ) (hx : x ≤ a + b) : 0 ≤ 1 - x * (a + b)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact sub_nonneg.mpr ((div_le_one hab).2 hx)
  rw [max_eq_right (h a (by linarith)), max_eq_right (h b (by linarith))]
  field_simp
  ring

private theorem clipped_triple {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hac : a ≤ c) (hbc : b ≤ c) :
    let k := max (2 / (a + b + c)) (a + b)⁻¹
    max 0 (1 - a * k) + max 0 (1 - b * k) + max 0 (1 - c * k) = 1 := by
  dsimp only
  have hab := add_pos ha hb
  have hsum := add_pos hab hc
  by_cases ht : c ≤ a + b
  · have hk : (a + b)⁻¹ ≤ 2 / (a + b + c) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hab hsum]
      linarith
    have h (x : ℝ) (hx : x ≤ c) : 0 ≤ 1 - x * (2 / (a + b + c)) := by
      rw [← mul_div_assoc]
      exact sub_nonneg.mpr ((div_le_one hsum).2 (by linarith))
    rw [max_eq_left hk, max_eq_right (h a hac), max_eq_right (h b hbc), max_eq_right (h c le_rfl)]
    field_simp
    ring
  · have ht' := le_of_not_ge ht
    have hk : 2 / (a + b + c) ≤ (a + b)⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hsum hab]
      linarith
    have h : 1 - c * (a + b)⁻¹ ≤ 0 := by
      rw [← div_eq_mul_inv]
      exact sub_nonpos.mpr ((one_le_div hab).2 ht')
    rw [max_eq_right hk, max_eq_left h, add_zero]
    exact clipped_pair ha hb

private theorem complement_columns (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (c : Fin 4) :
    ∑ j, allocation (complementEntries w (complementScales w)) j c = 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · let e := Tuple.sort w
    have he (j : Fin 3) : w (e j) ≤ w (e 2) :=
      Tuple.monotone_sort w (by omega : j ≤ 2)
    have he' (j : Fin 3) : w j ≤ w (e 2) := by simpa using he (e.symm j)
    have hsum : (∑ j, w j) = w (e 0) + w (e 1) + w (e 2) := by
      rw [← Equiv.sum_comp e w, Fin.sum_univ_three]
    have hpair :
        univ.sup' univ_nonempty (fun i => (pairWeight w i)⁻¹) = (pairWeight w (e 2))⁻¹ := by
      refine le_antisymm (sup'_le _ _ fun j _ => ?_)
        (le_sup' (fun i => (pairWeight w i)⁻¹) (mem_univ (e 2)))
      apply inv_anti₀ (pairWeight_pos w hw (e 2))
      rw [pairWeight_eq, pairWeight_eq]
      exact sub_le_sub_left (he' j) _
    have hpair' : pairWeight w (e 2) = w (e 0) + w (e 1) := by
      rw [pairWeight_eq, hsum]
      ring
    have hLast (j : Fin 3) : Fin.last 3 ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    simp only [allocation, ite_eq_right (hLast _), complementEntries, complementScales,
      Fin.lastCases_last, hsum, hpair, hpair']
    rw [← Equiv.sum_comp e, Fin.sum_univ_three]
    exact clipped_triple (hw _) (hw _) (hw _) (he 0) (he 1)
  · have h0 : pairWeight w 0 = w 1 + w 2 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 0 = {1, 2} by decide]
      simp
    have h1 : pairWeight w 1 = w 0 + w 2 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 1 = {0, 2} by decide]
      simp
    have h2 : pairWeight w 2 = w 0 + w 1 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]
      simp
    unfold allocation complementEntries
    simp only [complementScales, Fin.lastCases_castSucc]
    fin_cases i <;> simp [Fin.sum_univ_three, Fin.ext_iff, h0, h1, h2]
    · exact clipped_pair (hw 1) (hw 2)
    · exact clipped_pair (hw 0) (hw 2)
    · exact clipped_pair (hw 0) (hw 1)

private def complementWeights (u : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  Real.exp (-u j - 1)

private def complementPoint (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4) : ℝ :=
  allocation (complementEntries (complementWeights u) (complementScales (complementWeights u))) j c

private theorem complementPoint_zero (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4)
    (h : c = j.castSucc) : complementPoint u j c = 0 := by
  simp [complementPoint, allocation, h]

private theorem complementPoint_unit (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4) :
    complementPoint u j c ∈ Set.Icc (0 : ℝ) 1 := by
  unfold complementPoint allocation
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (sub_le_self _
      (mul_pos (Real.exp_pos _) (complementScales_pos _ (fun _ => Real.exp_pos _) _)).le)⟩

private theorem continuous_complementPoint (j : Fin 3) (c : Fin 4) :
    Continuous fun u => complementPoint u j c := by
  have hw (i : Fin 3) : Continuous fun u => complementWeights u i :=
    Real.continuous_exp.comp ((continuous_apply i).neg.sub continuous_const)
  have hp (i : Fin 3) : Continuous fun u => (pairWeight (complementWeights u) i)⁻¹ :=
    (continuous_finsetSum _ fun j _ => hw j).inv₀
      (fun u => (pairWeight_pos _ (fun _ => Real.exp_pos _) i).ne')
  have hk (c : Fin 4) : Continuous fun u => complementScales (complementWeights u) c := by
    refine Fin.lastCases ?_ (fun i => ?_) c
    · exact (continuous_const.div (continuous_finsetSum _ fun j _ => hw j)
        (fun u => (sum_pos (fun i _ => Real.exp_pos (-u i - 1)) univ_nonempty).ne')).max
        (Continuous.finset_sup'_apply univ_nonempty fun i _ => hp i)
    · simpa only [complementScales, Fin.lastCases_castSucc] using hp i
  by_cases h : c = j.castSucc
  · simpa [complementPoint, allocation, h] using
      (continuous_const : Continuous fun _ : Fin 3 → ℝ => (0 : ℝ))
  · simp only [complementPoint, allocation, ite_eq_right h, complementEntries]
    exact continuous_const.max (continuous_const.sub ((hw j).mul (hk c)))

private def complementScore (u x : Fin 3 → ℝ) : ℝ :=
  ∑ j, (Real.negMulLog (1 - x j) + u j * x j)

private def complementPotential (c : Fin 4) (u : Fin 3 → ℝ) : ℝ :=
  complementScore u (fun j => complementPoint u j c)

private theorem complementPotential_ge_score (c : Fin 4) (u x : Fin 3 → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, x j = 1)
    (hzero : ∀ j, c = j.castSucc → x j = 0) :
    complementScore u x ≤ complementPotential c u := by
  let k := complementScales (complementWeights u) c
  let y (j : Fin 3) := complementPoint u j c
  have hs (j : Fin 3) :
      Real.negMulLog (1 - x j) + u j * x j ≤
        Real.negMulLog (1 - y j) + u j * y j + Real.log k * (x j - y j) := by
    by_cases h : c = j.castSucc
    · rw [hzero j h, show y j = 0 from complementPoint_zero u j c h]
      simp
    · have hk : 0 < k := complementScales_pos _ (fun _ => Real.exp_pos _) _
      have hlog : Real.log (complementWeights u j * k) + 1 = -u j + Real.log k := by
        unfold complementWeights
        rw [Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]
        ring
      have hsup := complement_support (mul_pos (Real.exp_pos (-u j - 1)) hk) (hx j)
      dsimp only at hsup
      change Real.negMulLog (1 - x j) ≤
        (Real.log (complementWeights u j * k) + 1) * x j +
          (Real.negMulLog (1 - max 0 (1 - complementWeights u j * k)) -
            (Real.log (complementWeights u j * k) + 1) *
              max 0 (1 - complementWeights u j * k)) at hsup
      have hy : y j = max 0 (1 - complementWeights u j * k) := by
        simp only [y, complementPoint, allocation, ite_eq_right h, complementEntries, k]
      rw [hlog, ← hy] at hsup
      linarith only [hsup]
  have hy : ∑ j, y j = 1 := complement_columns _ (fun _ => Real.exp_pos _) c
  have h := sum_le_sum (s := (univ : Finset (Fin 3))) (fun j _ => hs j)
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, hsum, hy, sub_self, mul_zero,
    add_zero] at h
  simpa only [complementScore, complementPotential, sum_add_distrib, y] using h

private theorem le_complementPotential (c : Fin 4) (u : Fin 3 → ℝ) (j : Fin 3)
    (hj : j ∈ allowedRows c) : u j ≤ complementPotential c u := by
  let vertex (i : Fin 3) : ℝ := if i = j then 1 else 0
  have hv (i : Fin 3) : vertex i ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : i = j <;> simp [vertex, h]
  have hs : ∑ i, vertex i = 1 := by simp [vertex]
  have hz (i : Fin 3) (h : c = i.castSucc) : vertex i = 0 := by
    have hi : i ≠ j := fun hij => (mem_allowedRows _ _).1 hj (hij ▸ h)
    simp [vertex, hi]
  refine le_trans ?_ (complementPotential_ge_score c u vertex hv hs hz)
  have hvertex (i : Fin 3) : Real.negMulLog (1 - vertex i) + u i * vertex i =
      (if i = j then u i else 0) := by
    by_cases h : i = j <;> simp [vertex, h]
  simp [complementScore, hvertex]

private theorem complementScore_shift (u x : Fin 3 → ℝ) (a : ℝ) (hx : ∑ j, x j = 1) :
    complementScore (fun j => u j + a) x = complementScore u x + a := by
  unfold complementScore
  simp only [add_mul, ← add_assoc, sum_add_distrib, ← mul_sum, hx, mul_one]

private theorem complementPotential_shift (c : Fin 4) (u : Fin 3 → ℝ) (a : ℝ) :
    complementPotential c (fun j => u j + a) = complementPotential c u + a := by
  let v : Fin 3 → ℝ := fun j => u j + a
  have h (p : Fin 3 → ℝ) : ∑ j, complementPoint p j c = 1 :=
    complement_columns _ (fun _ => Real.exp_pos _) c
  have h₁ := complementPotential_ge_score c u (fun j => complementPoint v j c)
    (fun j => complementPoint_unit v j c) (h v) (fun j => complementPoint_zero v j c)
  have h₂ := complementPotential_ge_score c v (fun j => complementPoint u j c)
    (fun j => complementPoint_unit u j c) (h u) (fun j => complementPoint_zero u j c)
  refine le_antisymm ?_ ?_
  · change complementScore (fun j => u j + a) _ ≤ _
    rw [complementScore_shift _ _ _ (h v)]
    exact add_le_add h₁ le_rfl
  · change complementScore (fun j => u j + a) (fun j => complementPoint u j c) ≤ _ at h₂
    rw [complementScore_shift _ _ _ (h u)] at h₂
    exact h₂

open Filter Topology in
private theorem exists_complement_weights (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hcap : ∑ j, (d - m j) ≤ d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (htotal : ∑ j, τ j = d) :
    ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧
      ∀ j, (∑ c, (multiplicity (fun j => d - m j) (d - ∑ i, (d - m i)) c : ℝ) *
        allocation (complementEntries w (complementScales w)) j c) = τ j := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ i, l i
  let F := priceObjective l b τ complementPotential
  have hcount : (b : ℝ) + ∑ j, (l j : ℝ) = d := by
    exact_mod_cast Nat.sub_add_cancel hcap
  obtain ⟨δ, hδ, hbound⟩ := price_coercivity l b d τ hcount htotal hpos hupper _
    le_complementPotential
  have hG (c : Fin 4) : Continuous (complementPotential c) := by
    unfold complementPotential complementScore
    apply continuous_finsetSum
    intro j _
    apply Continuous.add
    · exact Real.continuous_negMulLog.comp
        (continuous_const.sub (continuous_complementPoint j c))
    · exact (continuous_apply j).mul (continuous_complementPoint j c)
  have hF : Continuous F :=
    (continuous_finsetSum _ (fun c _ => continuous_const.mul (hG c))).sub
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
  obtain ⟨u, hu⟩ := exists_minimum_prices F hF
    (priceObjective_shift l b d τ hcount htotal _ complementPotential_shift) hδ hbound
  refine ⟨complementWeights u, fun _ => Real.exp_pos _, fun j => ?_⟩
  let line (t : ℝ) (i : Fin 3) := u i + if i = j then t else 0
  let mass (p : Fin 3 → ℝ) : ℝ :=
    ∑ c, (multiplicity l b c : ℝ) * complementPoint p j c
  change mass u = τ j
  have hcompare (t : ℝ) (c : Fin 4) :
      complementPotential c (line t) ≤
        complementPotential c u + t * complementPoint (line t) j c := by
    let x (i : Fin 3) := complementPoint (line t) i c
    have h := complementPotential_ge_score c u x (fun i => complementPoint_unit _ i c)
      (complement_columns _ (fun _ => Real.exp_pos _) _) (fun i => complementPoint_zero _ i c)
    have hscore : complementScore (line t) x = complementScore u x + t * x j := by
      simp only [complementScore, line, add_mul, ← add_assoc, sum_add_distrib, ite_mul,
        zero_mul, sum_ite_eq', mem_univ, ite_true]
    exact hscore.trans_le (add_le_add h le_rfl)
  have hineq (t : ℝ) : 0 ≤ t * (mass (line t) - τ j) := by
    have h := sum_le_sum (s := (univ : Finset (Fin 4))) fun c _ =>
      mul_le_mul_of_nonneg_left (hcompare t c) (Nat.cast_nonneg (multiplicity l b c))
    simp only [mul_add, sum_add_distrib, mul_left_comm _ t, ← mul_sum] at h
    have hmin := hu (line t)
    have hτ : (∑ i, τ i * line t i) = (∑ i, τ i * u i) + τ j * t := by
      simp only [line, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    unfold F priceObjective at hmin
    rw [hτ] at hmin
    change (∑ c, (multiplicity l b c : ℝ) * complementPotential c (line t)) ≤
      (∑ c, (multiplicity l b c : ℝ) * complementPotential c u) + t * mass (line t) at h
    linarith only [hmin, h]
  have hcts : Continuous (fun t => mass (line t)) := by
    have hline : Continuous line := continuous_pi fun i => by
      by_cases hi : i = j
      · simp only [line, hi, ite_true]
        exact continuous_const.add continuous_id
      · simpa [line, hi] using (continuous_const : Continuous fun _ : ℝ => u i)
    exact (continuous_finsetSum _ (fun c _ =>
      continuous_const.mul (continuous_complementPoint j c))).comp hline
  have h0 : line 0 = u := by funext i; simp [line]
  have hlim : Tendsto (fun t => mass (line t)) (𝓝 0) (𝓝 (mass u)) := by
    simpa only [h0] using hcts.continuousAt (x := (0 : ℝ)).tendsto
  refine le_antisymm ?_ ?_
  · apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0)))
    filter_upwards [self_mem_nhdsWithin (s := Set.Iio (0 : ℝ))] with t ht
    have ht' : t < 0 := ht
    have h := hineq t
    by_contra! hn
    exact (mul_neg_of_neg_of_pos ht' (sub_pos.mpr hn)).not_ge h
  · apply ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with t ht
    have ht' : 0 < t := ht
    have h := hineq t
    by_contra! hn
    exact (mul_neg_of_pos_of_neg ht' (sub_neg.mpr hn)).not_ge h

/-- Every strictly admissible trace triple admits a complementary entropy
certificate with the original row labels and positive row and column parameters. -/
theorem exists_complement_certificate (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hcap : ∑ j, (d - m j) ≤ d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (htotal : ∑ j, τ j = d) :
    ∃ (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), (∀ j, 0 < w j) ∧ (∀ c, 0 < k c) ∧
      (∀ c, ∑ j, allocation (complementEntries w k) j c = 1) ∧
      ∀ j, (∑ c, (multiplicity (fun j => d - m j) (d - ∑ i, (d - m i)) c : ℝ) *
        allocation (complementEntries w k) j c) = τ j := by
  obtain ⟨w, hw, hr⟩ := exists_complement_weights d m τ hcap hpos hupper htotal
  exact ⟨w, complementScales w, hw, complementScales_pos w hw, complement_columns w hw, hr⟩

/-- The complementary entropy maximum for strictly admissible traces is attained by
the clipped allocation after sorting the weights and relabeling the rows. -/
theorem exists_isGreatest_complement (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hcap : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (Fintype.card n : ℝ) - (Fintype.card n - m j : ℕ))
    (htotal : ∑ j, τ j = Fintype.card n) :
    ∃ (e : Equiv.Perm (Fin 3)) (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), Monotone k ∧
      IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
        spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 = v}
        (allocationValue (fun x => Real.negMulLog (1 - x)) (fun j => Fintype.card n - m (e j))
          (Fintype.card n - ∑ j, (Fintype.card n - m j)) (complementEntries w k)) := by
  let l (j : Fin 3) := Fintype.card n - m j
  let b := Fintype.card n - ∑ j, l j
  obtain ⟨w, hw, hr⟩ := exists_complement_weights (Fintype.card n) m τ hcap hpos hupper htotal
  let e := Tuple.sort w
  let q := finSuccEquiv' (Fin.last 3)
  let p : Equiv.Perm (Fin 4) := (q.trans (Equiv.optionCongr e)).trans q.symm
  have hp (i : Fin 3) : p i.castSucc = (e i).castSucc := by
    change q.symm (Option.map e (q i.castSucc)) = (e i).castSucc
    rw [show q i.castSucc = some i from finSuccEquiv'_last_apply_castSucc i]
    exact Fin.succAbove_last_apply (e i)
  have hlast : p (Fin.last 3) = Fin.last 3 := by simp [p, q]
  let k := complementScales w
  let k' := k ∘ p
  have hord : Monotone k' := by
    intro a c
    refine Fin.lastCases (fun h => ?_) (fun i => ?_) a
    · have hc : c = Fin.last 3 := le_antisymm (Fin.le_last c) h
      rw [hc]
    · refine Fin.lastCases ?_ (fun j => ?_) c
      · intro _
        simp only [k', Function.comp_apply, hp, hlast, k, complementScales,
          Fin.lastCases_castSucc, Fin.lastCases_last]
        exact (le_sup' (fun i => (pairWeight w i)⁻¹) (mem_univ (e i))).trans (le_max_right _ _)
      · intro hij
        simp only [k', Function.comp_apply, hp, k, complementScales, Fin.lastCases_castSucc]
        apply inv_anti₀ (pairWeight_pos w hw (e j))
        rw [pairWeight_eq, pairWeight_eq]
        exact sub_le_sub_left (Tuple.monotone_sort w (Fin.castSucc_le_castSucc_iff.mp hij)) _
  have ha (j : Fin 3) (c : Fin 4) :
      allocation (complementEntries (w ∘ e) k') j c =
        allocation (complementEntries w k) (e j) (p c) := by
    simp only [allocation, complementEntries, Function.comp_apply, k', ← hp, p.apply_eq_iff_eq]
  have hl (c : Fin 4) : multiplicity (l ∘ e) b c = multiplicity l b (p c) := by
    refine Fin.lastCases ?_ (fun i => ?_) c
    · rw [hlast, multiplicity_last, multiplicity_last]
    · rw [hp, multiplicity_missing, multiplicity_missing]
      rfl
  have hc : (∑ j, l (e j)) = ∑ j, l j := Equiv.sum_comp e l
  have hcap' : (∑ j, l (e j)) ≤ Fintype.card n := hc.trans_le hcap
  have hcol' (c : Fin 4) : ∑ j, allocation (complementEntries (w ∘ e) k') j c = 1 := by
    simp_rw [ha]
    exact (Equiv.sum_comp e _).trans (complement_columns w hw (p c))
  have hr' (j : Fin 3) :
      (∑ c, (multiplicity (l ∘ e) (Fintype.card n - ∑ i, l (e i)) c : ℝ) *
        allocation (complementEntries (w ∘ e) k') j c) = τ (e j) := by
    rw [hc]
    change (∑ c, (multiplicity (l ∘ e) b c : ℝ) *
      allocation (complementEntries (w ∘ e) k') j c) = τ (e j)
    simp_rw [hl, ha]
    exact (Equiv.sum_comp p _).trans (hr (e j))
  have hm := isGreatest_complement (n := n) (m ∘ e) (τ ∘ e) (w ∘ e) k' hcap'
    (fun j => hw (e j)) (fun c => complementScales_pos w hw (p c)) hord hcol' hr'
  change IsGreatest _ (allocationValue (fun x => Real.negMulLog (1 - x)) (l ∘ e)
    (Fintype.card n - ∑ j, l (e j)) (complementEntries (w ∘ e) k')) at hm
  rw [spectralValues_relabel, hc] at hm
  exact ⟨e, w ∘ e, k', hord, hm⟩

#print axioms exists_isGreatest_complement

#print axioms exists_complement_certificate

#print axioms exists_isGreatest_direct

#print axioms exists_direct_certificate

end
end D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
