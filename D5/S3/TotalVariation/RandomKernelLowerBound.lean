/- GID: D5/S3/TotalVariation/RandomKernelLowerBound
   generality: G
   mirror-B: D5/B/S3/TotalVariation/RandomKernelLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Deletion of zero-diagonal matrix weights gives sharp stochastic-kernel lower bounds. -/

import D5.S3.TotalVariation.RandomKernelExtremum

open scoped BigOperators
noncomputable section
namespace D5.S3.TotalVariation.RandomKernelLowerBound
open D5.S3.TotalVariation.RandomKernelExtremum
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric

/-- The ordered-pair weight induced by a finite vertex set. -/
def pairWeight {V : Type*} (w : V → V → ℝ) (T : Finset V) : ℝ :=
  ∑ i ∈ T, ∑ j ∈ T, w i j

private theorem erase_weight {V : Type*} [DecidableEq V] (w : V → V → ℝ)
    (hw : ∀ i, w i i = 0) (T : Finset V) (v : V) (hv : v ∈ T) :
    pairWeight w (T.erase v) = pairWeight w T - (∑ j ∈ T, w v j) - ∑ i ∈ T, w i v := by
  have hr (i : V) := Finset.sum_erase_add (s := T) (f := w i) hv
  have hmain := Finset.sum_erase_add (s := T) (f := fun i => ∑ j ∈ T, w i j) hv
  have hc := Finset.sum_erase_add (s := T) (f := fun i => w i v) hv
  have hrows : (∑ i ∈ T.erase v, ∑ j ∈ T, w i j) =
      pairWeight w (T.erase v) + ∑ i ∈ T.erase v, w i v := by
    simp_rw [← hr, Finset.sum_add_distrib]
    rfl
  rw [hrows] at hmain
  rw [hw, add_zero] at hc
  dsimp [pairWeight] at hmain ⊢
  linarith only [hmain, hc]

private theorem deletion_identity {V : Type*} [DecidableEq V] (w : V → V → ℝ)
    (hw : ∀ i, w i i = 0) (T : Finset V) :
    (∑ v ∈ T, pairWeight w (T.erase v)) = ((T.card : ℝ) - 2) * pairWeight w T := by
  calc
    _ = ∑ v ∈ T, (pairWeight w T - (∑ j ∈ T, w v j) - ∑ i ∈ T, w i v) :=
      Finset.sum_congr rfl (fun v hv => erase_weight w hw T v hv)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hcomm : (∑ v ∈ T, ∑ i ∈ T, w i v) = pairWeight w T := Finset.sum_comm
      rw [hcomm]
      change (T.card : ℝ) * pairWeight w T - pairWeight w T - pairWeight w T = _
      ring

/-- A lower bound on every k-vertex induced ordered-pair sum propagates to every
larger finite set, without sign assumptions on the weights or on the bound. -/
private theorem hereditary_pair_sum_bound {V : Type*} [DecidableEq V]
    (w : V → V → ℝ) (hw : ∀ i, w i i = 0) (U : Finset V)
    (k : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hbase : ∀ S ⊆ U, S.card = k → B ≤ pairWeight w S)
    (T : Finset V) (hTU : T ⊆ U) (hkT : k ≤ T.card) :
    (T.card : ℝ) * (T.card - 1) * B ≤ (k : ℝ) * (k - 1) * pairWeight w T := by
  classical
  revert hTU hkT
  refine Finset.strongInductionOn T ?_
  intro T ih hTU hkT
  by_cases heq : T.card = k
  · have h := mul_le_mul_of_nonneg_left (hbase T hTU heq)
      (show (0 : ℝ) ≤ (k : ℝ) * (k - 1) by
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        exact mul_nonneg (by linarith) (by linarith))
    simpa [heq] using h
  · have hn : k < T.card := lt_of_le_of_ne hkT (Ne.symm heq)
    have hnR : (2 : ℝ) < T.card := by exact_mod_cast (lt_of_le_of_lt hk hn)
    have hc (v : V) (hv : v ∈ T) : ((T.erase v).card : ℝ) = (T.card : ℝ) - 1 := by
      have h := Finset.card_erase_add_one hv
      have h' : ((T.erase v).card : ℝ) + 1 = T.card := by exact_mod_cast h
      linarith
    have hstep (v : V) (hv : v ∈ T) :
        ((T.card : ℝ) - 1) * (T.card - 2) * B ≤
          (k : ℝ) * (k - 1) * pairWeight w (T.erase v) := by
      have herase : k ≤ (T.erase v).card := by
        have h := Finset.card_erase_add_one hv
        omega
      have h := ih (T.erase v) (Finset.erase_ssubset hv)
        (Finset.Subset.trans (Finset.erase_subset v T) hTU) herase
      rw [hc v hv] at h
      convert h using 1 <;> ring
    have hs := Finset.sum_le_sum hstep
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
    rw [deletion_identity w hw T] at hs
    apply (mul_le_mul_iff_left₀ (sub_pos.mpr hnR)).mp
    convert hs using 1 <;> ring
/-- Uniform mass on the diagonal indexed by a chosen finite subset. -/
def matchingLaw {d : ℕ} (S : Finset (Fin d)) : Option (Fin d × Fin d) → ℝ
  | none => 0
  | some z => if z.1 = z.2 then (if z.1 ∈ S then 1 / (S.card : ℝ) else 0) else 0

/-- Active off-diagonal pairs internal to S, as an actual output event. -/
def matchingEvent {d : ℕ} (S : Finset (Fin d)) : Finset (Option (Fin d × Fin d)) :=
  ((S ×ˢ S).filter (fun z => z.1 ≠ z.2)).map ⟨some, Option.some_injective _⟩

private theorem matching_probability {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    (∀ z, 0 ≤ matchingLaw S z) ∧ ∑ z, matchingLaw S z = 1 := by
  classical
  have hn : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  constructor
  · intro z; cases z <;> simp only [matchingLaw] <;> positivity
  · simp only [Fintype.sum_option, matchingLaw, zero_add, Fintype.sum_prod_type]
    simp [hn.ne']

private theorem matching_completion {d : ℕ} (S : Finset (Fin d)) :
    completion (matchingLaw S) = fun z => match z with
      | none => 0
      | some z => (if z.1 ∈ S then 1 / (S.card : ℝ) else 0) *
        (if z.2 ∈ S then 1 / (S.card : ℝ) else 0) := by
  funext z
  cases z with
  | none => rfl
  | some z => simp [completion, matchingLaw]

private theorem completion_matching_mass {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    ∑ z, completion (matchingLaw S) z = 1 := by
  classical
  have hn : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  rw [matching_completion]
  simp only [Fintype.sum_option, zero_add, Fintype.sum_prod_type]
  have hs : (∑ i : Fin d, if i ∈ S then 1 / (S.card : ℝ) else 0) = 1 := by
    simp [hn.ne']
  calc
    _ = (∑ i : Fin d, if i ∈ S then 1 / (S.card : ℝ) else 0) *
        (∑ j : Fin d, if j ∈ S then 1 / (S.card : ℝ) else 0) :=
      (Fintype.sum_mul_sum _ _).symm
    _ = 1 := by rw [hs]; norm_num

private theorem event_mass {d : ℕ} (S : Finset (Fin d)) (q : Option (Fin d × Fin d) → ℝ) :
    (∑ z ∈ matchingEvent S, q z) =
      ∑ r ∈ S, ∑ s ∈ S, if r = s then 0 else q (some (r,s)) := by
  classical
  simp [matchingEvent, Finset.sum_map, Finset.sum_filter, Finset.sum_product, ite_not]

private theorem matching_event_completion {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    (∑ z ∈ matchingEvent S, completion (matchingLaw S) z) =
      ((S.card : ℝ) - 1) / S.card := by
  classical
  have hn : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  rw [event_mass, matching_completion]
  have heq (r : Fin d) (hr : r ∈ S) :
      (∑ s ∈ S, if r = s then (0 : ℝ) else
        (if r ∈ S then 1 / (S.card : ℝ) else 0) *
          (if s ∈ S then 1 / (S.card : ℝ) else 0)) =
      (S.card : ℝ) / (S.card : ℝ)^2 - 1 / (S.card : ℝ)^2 := by
    calc
      _ = ∑ s ∈ S, (1 / (S.card : ℝ)^2 - if r = s then 1 / (S.card : ℝ)^2 else 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases h : r = s <;> simp [hr, hs, h, one_div, pow_two]
      _ = _ := by simp [Finset.sum_sub_distrib, hr, nsmul_eq_mul, div_eq_mul_inv]
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  <;> ring

private theorem matching_output {d : ℕ} (S : Finset (Fin d))
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) (z) :
    kernelOutput K (matchingLaw S) z =
      (1 / (S.card : ℝ)) * ∑ i ∈ S, K z (some (i,i)) := by
  classical
  simp [kernelOutput, matchingLaw, Fintype.sum_option, Fintype.sum_prod_type,
    mul_ite, Finset.mul_sum, mul_comm]

private theorem kernel_mass {d : ℕ}
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (hK : ∀ y, ∑ x, K x y = 1)
    (p : Option (Fin d × Fin d) → ℝ) (hp : ∑ z, p z = 1) :
    ∑ z, kernelOutput K p z = 1 := by
  simp only [kernelOutput]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, hK, hp]

private theorem event_gap {d : ℕ}
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (hK : ∀ y, ∑ x, K x y = 1) (e : ℝ)
    (he : ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ e)
    (S : Finset (Fin d)) (hS : S.Nonempty) (E : Finset (Option (Fin d × Fin d))) :
    |(∑ z ∈ E, completion (matchingLaw S) z) -
      (∑ z ∈ E, kernelOutput K (matchingLaw S) z)| ≤ e := by
  have hmass := (completion_matching_mass S hS).trans
    (kernel_mass K hK _ (matching_probability S hS).2).symm
  have hgap := (total_variation_eq_sup_event_gap (completion (matchingLaw S))
    (kernelOutput K (matchingLaw S)) hmass).2 (Set.mem_range_self E)
  rw [total_variation_comm] at hgap
  exact hgap.trans (he _ (matching_probability S hS).1 (matching_probability S hS).2)

private theorem support_coefficient_lower {d k : ℕ} (hd : 2 ≤ d)
    (hk : 2 ≤ k) (hkd : k ≤ d)
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (hK0 : ∀ x y, 0 ≤ K x y) (hK1 : ∀ y, ∑ x, K x y = 1) (e : ℝ)
    (he : ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ e) :
    ((d : ℝ) - 1) * coefficient d k ≤ e := by
  classical
  let w : Fin d → Fin d → ℝ := fun r s =>
    if r = s then 0 else ∑ i, K (some (r,s)) (some (i,i))
  have hw : ∀ i, w i i = 0 := by intro i; simp [w]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase (S : Finset (Fin d)) (_hS : S ⊆ Finset.univ) (hc : S.card = k) :
      ((k : ℝ) - 1) - k * e ≤ pairWeight w S := by
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hgap := event_gap K hK1 e he S hS (matchingEvent S)
    rw [matching_event_completion S hS, hc] at hgap
    have hout : (∑ z ∈ matchingEvent S, kernelOutput K (matchingLaw S) z) ≤
        (1 / (k : ℝ)) * pairWeight w S := by
      rw [event_mass]
      calc
        _ = (1 / (k : ℝ)) * ∑ r ∈ S, ∑ s ∈ S,
            if r = s then 0 else ∑ i ∈ S, K (some (r,s)) (some (i,i)) := by
          simp_rw [matching_output, hc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          split_ifs <;> simp [Finset.mul_sum]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro r hr
          apply Finset.sum_le_sum
          intro s hs
          by_cases hrs : r = s
          · simp [w, hrs]
          · simp only [if_neg hrs, w]
            exact Finset.sum_le_univ_sum_of_nonneg (fun i => hK0 _ _)
    have hdiff := (le_abs_self _).trans hgap
    have h := mul_le_mul_of_nonneg_left (show ((k : ℝ)-1)/k -
        (1 / (k : ℝ)) * pairWeight w S ≤ e by linarith) (show (0 : ℝ) ≤ k by linarith)
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp at h
    nlinarith only [h]
  have hpoint (i : Fin d) :
      (∑ r : Fin d, ∑ s : Fin d, if r = s then (0 : ℝ) else
        K (some (r,s)) (some (i,i))) ≤ e := by
    have hgap := event_gap K hK1 e he {i} (by simp) (matchingEvent Finset.univ)
    have hzero : (∑ z ∈ matchingEvent Finset.univ, completion (matchingLaw {i}) z) = 0 := by
      rw [event_mass, matching_completion]
      simp [Finset.sum_ite, Finset.sum_ite_irrel]
    rw [hzero, zero_sub, abs_neg] at hgap
    have hout : (∑ z ∈ matchingEvent Finset.univ, kernelOutput K (matchingLaw {i}) z) =
        ∑ r : Fin d, ∑ s : Fin d, if r = s then (0 : ℝ) else
          K (some (r,s)) (some (i,i)) := by
      rw [event_mass]
      simp [matching_output]
    rw [hout] at hgap
    exact (le_abs_self _).trans hgap
  have htotal : pairWeight w Finset.univ ≤ d * e := by
    calc
      _ = ∑ i : Fin d, ∑ r : Fin d, ∑ s : Fin d,
          if r = s then (0 : ℝ) else K (some (r,s)) (some (i,i)) := by
        dsimp [pairWeight, w]
        have hs (r s : Fin d) : (if r = s then (0 : ℝ) else
            ∑ i, K (some (r,s)) (some (i,i))) =
            ∑ i : Fin d, if r = s then 0 else K (some (r,s)) (some (i,i)) := by
          split_ifs <;> simp
        simp_rw [hs]
        calc
          _ = ∑ r : Fin d, ∑ i : Fin d, ∑ s : Fin d,
              if r = s then (0 : ℝ) else K (some (r,s)) (some (i,i)) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      _ ≤ ∑ _i : Fin d, e := Finset.sum_le_sum fun i _ => hpoint i
      _ = _ := by simp
  have hher := hereditary_pair_sum_bound w hw Finset.univ k hk
    (((k : ℝ)-1)-k*e) hbase Finset.univ (by rfl) (by simpa using hkd)
  simp only [Finset.card_univ, Fintype.card_fin] at hher
  have hmul := mul_le_mul_of_nonneg_left htotal
    (show (0 : ℝ) ≤ (k : ℝ) * (k-1) by nlinarith)
  have hpoly : ((d : ℝ)-1)*((k : ℝ)-1) ≤ (k : ℝ)*((d : ℝ)+k-2)*e := by
    have h := hher.trans hmul
    have hd0 : (0 : ℝ) < d := by linarith
    apply (mul_le_mul_iff_left₀ hd0).mp
    nlinarith only [h]
  have hden : (0 : ℝ) < (k : ℝ) * ((d : ℝ)+k-2) := by
    apply mul_pos <;> linarith
  dsimp [coefficient]
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm e] using hpoly)

/-- Any column-stochastic kernel satisfying a uniform error bound must have
that bound at least rho(d). The tests use only uniform diagonal subset laws. -/
private theorem sharp_uniform_kernel_lower_bound {d : ℕ} (hd : 2 ≤ d)
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (hK : (∀ x y, 0 ≤ K x y) ∧ ∀ y, ∑ x, K x y = 1) (e : ℝ)
    (he : ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ e) :
    rho d ≤ e := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  have hp := matching_probability ({i} : Finset (Fin d)) (by simp)
  have he0 : 0 ≤ e := (total_variation_nonneg _ _).trans (he _ hp.1 hp.2)
  obtain ⟨k, hkm, hkeq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (d+1)) (by simp) (coefficient d)
  change ((d : ℝ)-1) * (Finset.range (d+1)).sup' (by simp) (coefficient d) ≤ e
  rw [hkeq]
  by_cases hk : 2 ≤ k
  · exact support_coefficient_lower hd hk (by have := Finset.mem_range.mp hkm; omega)
      K hK.1 hK.2 e he
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> simpa [coefficient] using he0

private theorem completion_probability {d : ℕ}
    (p : Option (Fin d × Fin d) → ℝ) (hp : ∀ z, 0 ≤ p z) (hm : ∑ z, p z = 1) :
    (∀ z, 0 ≤ completion p z) ∧ ∑ z, completion p z = 1 := by
  classical
  have hmass : ∑ z : Fin d × Fin d, p (some z) = 1-p none := by
    simp only [Fintype.sum_option] at hm
    linarith only [hm]
  have hr0 : 0 ≤ 1-p none := by
    rw [← hmass]
    exact Finset.sum_nonneg fun z _ => hp (some z)
  have hrow : (∑ i : Fin d, ∑ j : Fin d, p (some (i,j))) = 1-p none := by
    simpa [Fintype.sum_prod_type] using hmass
  have hcol : (∑ j : Fin d, ∑ i : Fin d, p (some (i,j))) = 1-p none := by
    rw [Finset.sum_comm]
    exact hrow
  constructor
  · intro z
    cases z with
    | none => exact hp none
    | some z =>
      simp only [completion]
      split_ifs
      · exact div_nonneg (mul_nonneg
          (Finset.sum_nonneg fun j _ => hp _) (Finset.sum_nonneg fun i _ => hp _)) hr0
      · rfl
  · simp only [Fintype.sum_option, completion]
    by_cases hr : 0 < 1-p none
    · simp only [if_pos hr, Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
      rw [← Fintype.sum_mul_sum, hrow, hcol]
      field_simp
      <;> nlinarith
    · have hz : 1-p none = 0 := le_antisymm (le_of_not_gt hr) hr0
      simp [hr]
      linarith only [hz]

private theorem worst_error_bounds {d : ℕ}
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ)
    (hK : (∀ x y, 0 ≤ K x y) ∧ ∀ y, ∑ x, K x y = 1) :
    ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ worstError K := by
  classical
  have hbdd : BddAbove {e : ℝ | ∃ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧
      e = totalVariation (kernelOutput K p) (completion p)} := by
    refine ⟨1, ?_⟩
    rintro e ⟨p, hp, hm, rfl⟩
    apply total_variation_le_one _ _ ?_ (completion_probability p hp hm)
    exact ⟨fun z => Finset.sum_nonneg fun y _ => mul_nonneg (hK.1 z y) (hp y),
      kernel_mass K hK.2 p hm⟩
  intro p hp hm
  exact le_csSup hbdd ⟨p, hp, hm, rfl⟩

/-- The explicit kernel realizes the least possible worst-source total-variation
error among all column-stochastic kernels, namely rho(d). -/
theorem stochastic_kernel_minimax {d : ℕ} (hd : 2 ≤ d) :
    IsLeast {e : ℝ | ∃ K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ,
      ((∀ x y, 0 ≤ K x y) ∧ ∀ y, ∑ x, K x y = 1) ∧ e = worstError K} (rho d) := by
  refine ⟨⟨optimalKernel d, (optimal_kernel_upper_bound hd).1,
    (optimal_kernel_attains hd).2.symm⟩, ?_⟩
  rintro e ⟨K, hK, rfl⟩
  exact sharp_uniform_kernel_lower_bound hd K hK (worstError K) (worst_error_bounds K hK)

private theorem optimal_matching_event {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    (∑ z ∈ matchingEvent S, kernelOutput (optimalKernel d) (matchingLaw S) z) =
      ((S.card : ℝ)-1) * beta d := by
  classical
  have hn : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hentry (r s i : Fin d) (hrs : r ≠ s) :
      optimalKernel d (some (r,s)) (some (i,i)) =
        (if s = i then beta d / 2 else 0) + (if r = i then beta d / 2 else 0) := by
    by_cases hr : r = i <;> by_cases hs : s = i
    all_goals simp [optimalKernel, replacement, hr, hs, hrs] at * <;> ring
  have hout (r s : Fin d) (hr : r ∈ S) (hs : s ∈ S) (hrs : r ≠ s) :
      kernelOutput (optimalKernel d) (matchingLaw S) (some (r,s)) = beta d / S.card := by
    rw [matching_output]
    have hsum : (∑ i ∈ S, optimalKernel d (some (r,s)) (some (i,i))) = beta d := by
      simp_rw [hentry r s _ hrs, Finset.sum_add_distrib]
      simp [hr, hs]
    rw [hsum]
    ring
  rw [event_mass]
  have hrow (r : Fin d) (hr : r ∈ S) :
      (∑ s ∈ S, if r = s then (0 : ℝ) else
        kernelOutput (optimalKernel d) (matchingLaw S) (some (r,s))) =
      ((S.card : ℝ)-1) * (beta d / S.card) := by
    calc
      _ = ∑ s ∈ S, (beta d / S.card - if r = s then beta d / S.card else 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hrs : r = s
        · simp [hrs]
        · simp [hrs, hout r s hr hs hrs]
      _ = _ := by simp [Finset.sum_sub_distrib, hr, nsmul_eq_mul]; ring
  rw [Finset.sum_congr rfl hrow]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  <;> ring

/-- Every uniform diagonal matching whose support size maximizes the defining
finite expression attains the error rho(d) of the explicit kernel. -/
theorem maximizing_matching_attains {d : ℕ} (hd : 2 ≤ d)
    (S : Finset (Fin d)) (hk : 2 ≤ S.card)
    (hmax : beta d = coefficient d S.card) :
    totalVariation (kernelOutput (optimalKernel d) (matchingLaw S))
      (completion (matchingLaw S)) = rho d := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hp := matching_probability S hS
  have hu := optimal_kernel_upper_bound hd
  apply le_antisymm (hu.2 _ hp.1 hp.2)
  have hmass := (completion_matching_mass S hS).trans
    (kernel_mass _ hu.1.2 _ hp.2).symm
  have hgap := (total_variation_eq_sup_event_gap (completion (matchingLaw S))
    (kernelOutput (optimalKernel d) (matchingLaw S)) hmass).2
    (Set.mem_range_self (matchingEvent S))
  rw [total_variation_comm] at hgap
  have h := (le_abs_self _).trans hgap
  rw [matching_event_completion S hS, optimal_matching_event S hS] at h
  have hkR : (2 : ℝ) ≤ S.card := by exact_mod_cast hk
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk0 : (S.card : ℝ) ≠ 0 := by linarith
  have hid : ((S.card : ℝ)-1) / S.card - ((S.card : ℝ)-1)*beta d = rho d := by
    have ht : (d : ℝ) + S.card - 2 ≠ 0 := by linarith
    rw [rho, hmax, coefficient]
    field_simp [hk0, ht]
    <;> ring
  rw [hid] at h
  exact h

#print axioms maximizing_matching_attains

#print axioms sharp_uniform_kernel_lower_bound
#print axioms stochastic_kernel_minimax

#print axioms hereditary_pair_sum_bound
end D5.S3.TotalVariation.RandomKernelLowerBound
