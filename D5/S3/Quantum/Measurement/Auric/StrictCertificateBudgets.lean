/- GID: D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/StrictCertificateBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every strict certificate in the original labels gives the sharp spectral maximum. -/

import D5.S3.Quantum.Measurement.Auric.UnequalPhysicalTargets
import D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates

/-! The strict spectral maxima in the original labels, for every supplied certificate. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (entropyIntegrand)

noncomputable section

private def relabelColumns (e : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  let q := finSuccEquiv' (Fin.last 3)
  (q.trans (Equiv.optionCongr e)).trans q.symm

private theorem relabelColumns_missing (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    relabelColumns e j.castSucc = (e j).castSucc := by
  let q := finSuccEquiv' (Fin.last 3)
  change q.symm (Option.map e (q j.castSucc)) = (e j).castSucc
  rw [show q j.castSucc = some j from finSuccEquiv'_last_apply_castSucc j]
  exact Fin.succAbove_last_apply (e j)

private theorem relabelColumns_last (e : Equiv.Perm (Fin 3)) :
    relabelColumns e (Fin.last 3) = Fin.last 3 := by
  simp [relabelColumns]

private theorem multiplicity_relabelColumns (e : Equiv.Perm (Fin 3))
    (l : Fin 3 → ℕ) (b : ℕ) (c : Fin 4) :
    multiplicity (l ∘ e) b c = multiplicity l b (relabelColumns e c) := by
  refine Fin.lastCases ?_ (fun j => ?_) c
  · rw [relabelColumns_last] <;> rfl
  · rw [relabelColumns_missing, multiplicity_missing, multiplicity_missing] <;> rfl

private theorem allocation_relabelColumns (e : Equiv.Perm (Fin 3))
    {old new : Fin 3 → Fin 4 → ℝ}
    (h : ∀ j c, new j c = old (e j) (relabelColumns e c)) (j : Fin 3) (c : Fin 4) :
    allocation new j c = allocation old (e j) (relabelColumns e c) := by
  simp only [allocation, h, ← relabelColumns_missing e, (relabelColumns e).apply_eq_iff_eq]

private theorem allocationValue_relabelColumns (e : Equiv.Perm (Fin 3))
    (f : ℝ → ℝ) (l : Fin 3 → ℕ) (b : ℕ) {old new : Fin 3 → Fin 4 → ℝ}
    (h : ∀ j c, new j c = old (e j) (relabelColumns e c)) :
    allocationValue f (l ∘ e) b new = allocationValue f l b old := by
  unfold allocationValue
  simp_rw [multiplicity_relabelColumns e l b, allocation_relabelColumns e h]
  calc
    _ = ∑ j, ∑ c, (multiplicity l b c : ℝ) * f (allocation old (e j) c) :=
      sum_congr rfl fun j _ => Equiv.sum_comp (relabelColumns e) _
    _ = _ := Equiv.sum_comp e (fun j => ∑ c, (multiplicity l b c : ℝ) *
      f (allocation old j c))

/-- Row sorting preserves the value of the given direct certificate. -/
theorem direct_certificate_maximum (d : ℕ) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ)
    (w : Fin 3 → ℝ) (hcap : ∑ j, (d - m j) ≤ d)
    (hw : ∀ j, 0 < w j) (hwt : ∑ j, w j = 1)
    (hrow : ∀ j, weightMass (fun j => d - m j) (d - ∑ i, (d - m i)) w j = t j) :
    IsGreatest (effectValues false d m t)
      (allocationValue (entropyIntegrand false) (fun j => d - m j)
        (d - ∑ j, (d - m j)) (weightEntries w)) := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ j, l j
  let e := Tuple.sort (fun j => -w j)
  have he : Antitone (w ∘ e) := fun _ _ hij =>
    neg_le_neg_iff.mp (Tuple.monotone_sort (fun j => -w j) hij)
  have hc : (∑ j, l (e j)) = ∑ j, l j := Equiv.sum_comp e l
  have hcap' : (∑ j, l (e j)) ≤ d := hc.trans_le hcap
  have hrow' (j : Fin 3) : weightMass (l ∘ e)
      (d - ∑ i, l (e i)) (w ∘ e) j = t (e j) := by
    rw [hc, weightMass_relabel]
    exact hrow (e j)
  have hentries (j : Fin 3) (c : Fin 4) :
      weightEntries (w ∘ e) j c = weightEntries w (e j) (relabelColumns e c) := by
    refine Fin.lastCases ?_ (fun i => ?_) c
    · rw [relabelColumns_last] <;> rfl
    · rw [relabelColumns_missing]
      simp only [weightEntries, columnDenominator_castSucc, Function.comp_apply]
  have hmax := isGreatest_direct (n := Fin d) (m ∘ e) (t ∘ e) (w ∘ e)
    (by simpa only [Fintype.card_fin, l, Function.comp_apply] using hcap')
    (fun j => hw (e j)) ((Equiv.sum_comp e w).trans hwt) he
    (by simpa only [Fintype.card_fin, l, Function.comp_def] using hrow')
  simp only [Fintype.card_fin] at hmax
  change IsGreatest _ (allocationValue Real.negMulLog (l ∘ e)
    (d - ∑ j, l (e j)) (weightEntries (w ∘ e))) at hmax
  rw [spectralValues_relabel, hc, allocationValue_relabelColumns e _ l b hentries] at hmax
  exact hmax

private theorem strict_column_of_scales (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (k₁ k₂ : Fin 4 → ℝ) (c : Fin 4) (hlt : k₁ c < k₂ c)
    (hsum : ∑ j, allocation (complementEntries w k₂) j c = 1) :
    (∑ j, allocation (complementEntries w k₂) j c) <
      ∑ j, allocation (complementEntries w k₁) j c := by
  have hmass : ∃ j, 0 < allocation (complementEntries w k₂) j c := by
    by_contra! hn
    have h := sum_nonpos (fun j (_ : j ∈ (univ : Finset (Fin 3))) => hn j)
    rw [hsum] at h
    exact (not_le_of_gt zero_lt_one) h
  obtain ⟨j, hj⟩ := hmass
  have hallowed : c ≠ j.castSucc := by
    intro he
    simp [allocation, he] at hj
  have hstep (i : Fin 3) : 1 - w i * k₂ c < 1 - w i * k₁ c :=
    sub_lt_sub_left (mul_lt_mul_of_pos_left hlt (hw i)) 1
  apply sum_lt_sum
  · intro i _
    by_cases hi : c = i.castSucc
    · simp [allocation, hi]
    · simpa only [allocation, if_neg hi, complementEntries] using
        (max_le_max le_rfl (hstep i).le :
          max 0 (1 - w i * k₂ c) ≤ max 0 (1 - w i * k₁ c))
  · refine ⟨j, mem_univ j, ?_⟩
    simp only [allocation, if_neg hallowed, complementEntries] at hj ⊢
    have hpositive : 0 < 1 - w j * k₂ c :=
      lt_of_not_ge fun hn => (lt_irrefl (0 : ℝ)) (by simpa only [max_eq_left hn] using hj)
    rw [max_eq_right hpositive.le, max_eq_right (hpositive.trans (hstep j)).le]
    exact hstep j

private theorem complement_scales_eq (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (k : Fin 4 → ℝ) (hcol : ∀ c, ∑ j, allocation (complementEntries w k) j c = 1) :
    k = complementScales w := by
  funext c
  apply le_antisymm
  · by_contra! h
    have hc := strict_column_of_scales w hw (complementScales w) k c h (hcol c)
    rw [hcol c, complement_columns w hw c] at hc
    exact lt_irrefl _ hc
  · by_contra! h
    have hc := strict_column_of_scales w hw k (complementScales w) c h
      (complement_columns w hw c)
    rw [hcol c, complement_columns w hw c] at hc
    exact lt_irrefl _ hc

/-- Normalized clipped columns force their scales, and row sorting preserves the value. -/
theorem complement_certificate_maximum (d : ℕ) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ)
    (w : Fin 3 → ℝ) (k : Fin 4 → ℝ) (hcap : ∑ j, (d - m j) ≤ d)
    (hw : ∀ j, 0 < w j) (hk : ∀ c, 0 < k c)
    (hcol : ∀ c, ∑ j, allocation (complementEntries w k) j c = 1)
    (hrow : ∀ j, (∑ c, (multiplicity (fun j => d - m j) (d - ∑ i, (d - m i)) c : ℝ) *
      allocation (complementEntries w k) j c) = t j) :
    IsGreatest (effectValues true d m t)
      (allocationValue (entropyIntegrand true) (fun j => d - m j)
        (d - ∑ j, (d - m j)) (complementEntries w k)) := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ j, l j
  let e := Tuple.sort w
  let p := relabelColumns e
  let k' := k ∘ p
  have hp (i : Fin 3) : p i.castSucc = (e i).castSucc := relabelColumns_missing e i
  have hlast : p (Fin.last 3) = Fin.last 3 := relabelColumns_last e
  have hkcanonical := complement_scales_eq w hw k hcol
  have hord : Monotone k' := by
    intro a c
    refine Fin.lastCases (fun h => ?_) (fun i => ?_) a
    · have hc : c = Fin.last 3 := le_antisymm (Fin.le_last c) h
      rw [hc]
    · refine Fin.lastCases ?_ (fun j => ?_) c
      · intro _
        simp only [k', Function.comp_apply, hp, hlast, hkcanonical, complementScales,
          Fin.lastCases_castSucc, Fin.lastCases_last]
        exact (le_sup' (fun i => (pairWeight w i)⁻¹) (mem_univ (e i))).trans (le_max_right _ _)
      · intro hij
        simp only [k', Function.comp_apply, hp, hkcanonical, complementScales,
          Fin.lastCases_castSucc]
        apply inv_anti₀ (pairWeight_pos w hw (e j))
        rw [pairWeight_eq, pairWeight_eq]
        exact sub_le_sub_left (Tuple.monotone_sort w (Fin.castSucc_le_castSucc_iff.mp hij)) _
  have hentries (j : Fin 3) (c : Fin 4) :
      complementEntries (w ∘ e) k' j c = complementEntries w k (e j) (p c) := rfl
  have ha (j : Fin 3) (c : Fin 4) :
      allocation (complementEntries (w ∘ e) k') j c =
        allocation (complementEntries w k) (e j) (p c) :=
    allocation_relabelColumns e hentries j c
  have hl (c : Fin 4) : multiplicity (l ∘ e) b c = multiplicity l b (p c) :=
    multiplicity_relabelColumns e l b c
  have hc : (∑ j, l (e j)) = ∑ j, l j := Equiv.sum_comp e l
  have hcap' : (∑ j, l (e j)) ≤ d := hc.trans_le hcap
  have hcol' (c : Fin 4) : ∑ j, allocation (complementEntries (w ∘ e) k') j c = 1 := by
    simp_rw [ha]
    exact (Equiv.sum_comp e _).trans (hcol (p c))
  have hrow' (j : Fin 3) :
      (∑ c, (multiplicity (l ∘ e) (d - ∑ i, l (e i)) c : ℝ) *
        allocation (complementEntries (w ∘ e) k') j c) = t (e j) := by
    rw [hc]
    change (∑ c, (multiplicity (l ∘ e) b c : ℝ) *
      allocation (complementEntries (w ∘ e) k') j c) = t (e j)
    simp_rw [hl, ha]
    exact (Equiv.sum_comp p _).trans (hrow (e j))
  have hmax := isGreatest_complement (n := Fin d) (m ∘ e) (t ∘ e) (w ∘ e) k'
    (by simpa only [Fintype.card_fin, l, Function.comp_apply] using hcap')
    (fun j => hw (e j)) (fun c => hk (p c)) hord hcol'
    (by simpa only [Fintype.card_fin, l, Function.comp_def] using hrow')
  simp only [Fintype.card_fin] at hmax
  change IsGreatest _ (allocationValue (fun x => Real.negMulLog (1 - x)) (l ∘ e)
    (d - ∑ j, l (e j)) (complementEntries (w ∘ e) k')) at hmax
  rw [spectralValues_relabel, hc, allocationValue_relabelColumns e _ l b hentries] at hmax
  exact hmax

end

end D5.S3.Quantum.Measurement.Auric
