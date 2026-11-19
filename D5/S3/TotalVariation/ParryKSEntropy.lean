/- GID: D5/S3/TotalVariation/ParryKSEntropy
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryKSEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov–Sinai entropy of the bilateral Parry reset shift. -/

import D5.S3.TotalVariation.ParryInducedEntropy
import D5.S3.Entropy.KolmogorovSinai.Generator
import D5.S3.Divergence.GrandmotherTheorem

/-! Finite-word entropy estimates for the bilateral Parry reset shift. -/

namespace D5.S3.TotalVariation.ParryKSEntropy

open Filter Function MeasureTheory MeasurableSpace Set Topology
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Entropy.KolmogorovSinai
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryFirstReturn
open D5.S3.TotalVariation.ParryInducedEntropy
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.TwistedResetPaths
open scoped ENNReal BigOperators

variable {k : ℕ}

private theorem kernel_nonneg (hk : 2 ≤ k) (i j : Fin k) :
    0 ≤ suffixKernel k i j := by
  have hparam := parry_stationary_law k hk
  have hp : 0 < parryParameter k := lt_trans (by norm_num) hparam.1.1
  have hw (i : Fin k) := hp.le.trans (hparam.2.1 i).1
  unfold suffixKernel
  split
  · exact div_nonneg hp.le (hw i)
  · split
    · exact div_nonneg (mul_nonneg hp.le (hw j)) (hw i)
    · exact le_rfl

private theorem kernel_log_on_edge (hk : 2 ≤ k) (i j : Fin k)
    (h : j.val = 0 ∨ j.val = i.val + 1) :
    0 < suffixKernel k i j ∧
      Real.log (suffixKernel k i j) =
        Real.log (parryParameter k) + Real.log (suffixWeight k (parryParameter k) j) -
          Real.log (suffixWeight k (parryParameter k) i) := by
  let p := parryParameter k
  let R := suffixWeight k p
  have hparam := parry_stationary_law k hk
  have hp : 0 < p := lt_trans (by norm_num) hparam.1.1
  have hR (i : Fin k) : 0 < R i := hp.trans_le (hparam.2.1 i).1
  have hfactor : suffixKernel k i j = p * R j / R i := by
    rcases h with hz | hs
    · have hRz : R j = 1 := by simpa [R, suffixWeight, hz, rootSum] using hparam.1.2.2
      simp [suffixKernel, hz, hRz, p, R]
    · simp [suffixKernel, hs, p, R]
  rw [hfactor, Real.log_div (mul_pos hp (hR j)).ne' (hR i).ne',
    Real.log_mul hp.ne' (hR j).ne']
  exact ⟨div_pos (mul_pos hp (hR j)) (hR i), rfl⟩

private noncomputable def wordMass {n : ℕ} (w : Fin (n + 1) → Fin k) : ℝ :=
  suffixLaw k (w 0) * ∏ i : Fin n, suffixKernel k (w i.castSucc) (w i.succ)

private theorem suffixLaw_pos (hk : 2 ≤ k) (i : Fin k) : 0 < suffixLaw k i := by
  have hparam := parry_stationary_law k hk
  have hp : 0 < parryParameter k := lt_trans (by norm_num) hparam.1.1
  unfold suffixLaw
  exact div_pos (mul_pos (pow_pos hp _) (hp.trans_le (hparam.2.1 i).1))
    (zero_lt_one.trans_le hparam.2.2.1)

private theorem wordMass_log (hk : 2 ≤ k) {n : ℕ} (w : Fin (n + 1) → Fin k)
    (hedge : ∀ i : Fin n, (w i.succ).val = 0 ∨ (w i.succ).val = (w i.castSucc).val + 1) :
    0 < wordMass w ∧
      Real.log (wordMass w) = (n : ℝ) * Real.log (parryParameter k) +
        Real.log (suffixLaw k (w 0)) +
          Real.log (suffixWeight k (parryParameter k) (w (Fin.last n))) -
          Real.log (suffixWeight k (parryParameter k) (w 0)) := by
  let F (i : Fin n) := suffixKernel k (w i.castSucc) (w i.succ)
  let L (j : Fin (n + 1)) := Real.log (suffixWeight k (parryParameter k) (w j))
  have hF (i : Fin n) : 0 < F i := (kernel_log_on_edge hk _ _ (hedge i)).1
  have hprod : 0 < ∏ i, F i := Finset.prod_pos fun i _ => hF i
  have hsum : (∑ i : Fin n, L i.succ) - (∑ i : Fin n, L i.castSucc) =
      L (Fin.last n) - L 0 := by
    linarith only [Fin.sum_univ_succ L, Fin.sum_univ_castSucc L]
  refine ⟨mul_pos (suffixLaw_pos hk _) hprod, ?_⟩
  change Real.log (suffixLaw k (w 0) * ∏ i, F i) = _
  rw [Real.log_mul (suffixLaw_pos hk _).ne' hprod.ne',
    Real.log_prod fun i _ => (hF i).ne']
  have hlog (i : Fin n) : Real.log (F i) =
      Real.log (parryParameter k) + L i.succ - L i.castSucc :=
    (kernel_log_on_edge hk _ _ (hedge i)).2
  simp_rw [hlog]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change _ = (n : ℝ) * Real.log (parryParameter k) + Real.log (suffixLaw k (w 0)) +
    L (Fin.last n) - L 0
  linarith only [hsum]


private noncomputable def wordError (k : ℕ) : ℝ :=
  (∑ j : Fin k, |Real.log (suffixLaw k j)|) +
    2 * ∑ j : Fin k, |Real.log (suffixWeight k (parryParameter k) j)|

private theorem wordMass_log_error (hk : 2 ≤ k) {n : ℕ} (w : Fin (n + 1) → Fin k)
    (hedge : ∀ i : Fin n, (w i.succ).val = 0 ∨ (w i.succ).val = (w i.castSucc).val + 1) :
    |Real.log (wordMass w) - (n : ℝ) * Real.log (parryParameter k)| ≤ wordError k := by
  classical
  let R (j : Fin k) := Real.log (suffixWeight k (parryParameter k) j)
  let q := Real.log (suffixLaw k (w 0))
  have ha : |q| ≤ ∑ j : Fin k, |Real.log (suffixLaw k j)| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (Real.log (suffixLaw k j))) (Finset.mem_univ _)
  have hR (j : Fin k) : |R j| ≤ ∑ i : Fin k, |R i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (R i)) (Finset.mem_univ j)
  rw [(wordMass_log hk w hedge).2]
  change |(n : ℝ) * Real.log (parryParameter k) + q + R (w (Fin.last n)) - R (w 0) -
      (n : ℝ) * Real.log (parryParameter k)| ≤ _
  rw [show (n : ℝ) * Real.log (parryParameter k) + q + R (w (Fin.last n)) - R (w 0) -
      (n : ℝ) * Real.log (parryParameter k) = q + R (w (Fin.last n)) + -R (w 0) by ring]
  unfold wordError
  have ht := (abs_add_le (q + R (w (Fin.last n))) (-R (w 0))).trans
    (add_le_add (abs_add_le q (R (w (Fin.last n)))) le_rfl)
  rw [abs_neg] at ht
  change _ ≤ (∑ j : Fin k, |Real.log (suffixLaw k j)|) + 2 * ∑ j : Fin k, |R j|
  linarith only [ht, ha, hR (w (Fin.last n)), hR (w 0)]

private theorem entropy_of_reference_mass {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1)
    (hb : (∀ i, 0 ≤ b i) ∧ ∑ i, b i = 1)
    (hac : ∀ i, b i = 0 → a i = 0) (c C : ℝ)
    (herr : ∀ i, b i ≠ 0 → |Real.log (b i) + c| ≤ C) :
    (∑ i, Real.negMulLog (a i)) ≤ c + C ∧
      c - C ≤ ∑ i, Real.negMulLog (b i) := by
  have upper_term (i : ι) : a i * (-Real.log (b i)) ≤ a i * (c + C) := by
    by_cases hzero : b i = 0
    · simp [hac i hzero]
    · have hi := (abs_le.mp (herr i hzero)).1
      exact mul_le_mul_of_nonneg_left (by linarith only [hi]) (ha.1 i)
  have lower_term (i : ι) : b i * (c - C) ≤ Real.negMulLog (b i) := by
    by_cases hzero : b i = 0
    · simp [hzero]
    · have hi := (abs_le.mp (herr i hzero)).2
      rw [Real.negMulLog, neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (by linarith only [hi]) (hb.1 i)
  have hkl : 0 ≤ klDivergence a b := kl_divergence_nonneg a b ha hb hac
  have hrewrite (i : ι) : a i * Real.log (a i / b i) =
      a i * (-Real.log (b i)) - Real.negMulLog (a i) := by
    by_cases hzero : a i = 0
    · simp [hzero]
    · rw [Real.log_div hzero (fun h => hzero (hac i h)), Real.negMulLog]
      ring
  unfold klDivergence at hkl
  simp_rw [hrewrite, Finset.sum_sub_distrib] at hkl
  constructor
  · calc
      (∑ i, Real.negMulLog (a i)) ≤ ∑ i, a i * (-Real.log (b i)) := sub_nonneg.mp hkl
      _ ≤ ∑ i, a i * (c + C) := Finset.sum_le_sum fun i _ => upper_term i
      _ = c + C := by rw [← Finset.sum_mul, ha.2, one_mul]
  · calc
      c - C = ∑ i, b i * (c - C) := by rw [← Finset.sum_mul, hb.2, one_mul]
      _ ≤ ∑ i, Real.negMulLog (b i) := Finset.sum_le_sum fun i _ => lower_term i


private def suffixBlock (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (start : ℤ) (n : ℕ) (r : RelationPath k) (i : Fin n) : Fin k :=
  ((e (false, r)).val (start + i.val)).2

private theorem measurable_suffixBlock (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (start : ℤ) (n : ℕ) : Measurable (suffixBlock e start n) := by
  refine Measurable.of_eval fun i => ?_
  exact measurable_snd.comp ((measurable_pi_apply (start + (i.val : ℤ))).comp
    (measurable_subtype_coe.comp (e.measurable.comp (measurable_const.prodMk measurable_id))))

private noncomputable def blockPartition (μ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (start : ℤ) (n : ℕ) :=
  fiberPartition μ (suffixBlock e start n) (measurable_suffixBlock e start n)

private theorem block_entropy_bounds (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ ρ : ProbabilityMeasure (RelationPath k))
    (hcyl : ∀ (start : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
      (μ : Measure (RelationPath k)) {r | suffixBlock e start (n + 1) r = w} =
        ENNReal.ofReal (suffixLaw k (w 0)) *
          ∏ i : Fin n, ENNReal.ofReal (suffixKernel k (w i.castSucc) (w i.succ)))
    (start : ℤ) (n : ℕ) :
    entropy ρ (blockPartition ρ e start (n + 1)).cells ≤
      (n : ℝ) * (-Real.log (parryParameter k)) + wordError k ∧
    (n : ℝ) * (-Real.log (parryParameter k)) - wordError k ≤
      entropy μ (blockPartition μ e start (n + 1)).cells := by
  let P := blockPartition ρ e start (n + 1)
  let Q := blockPartition μ e start (n + 1)
  let a (w : Fin (n + 1) → Fin k) := ((ρ : Measure (RelationPath k)) (P.cells w)).toReal
  let b (w : Fin (n + 1) → Fin k) := ((μ : Measure (RelationPath k)) (Q.cells w)).toReal
  have hb (w : Fin (n + 1) → Fin k) : b w = wordMass w := by
    change ((μ : Measure (RelationPath k)) {r | suffixBlock e start (n + 1) r = w}).toReal = _
    rw [hcyl, ENNReal.toReal_mul, ENNReal.toReal_ofReal (suffixLaw_pos hk _).le,
      ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_ofReal (kernel_nonneg hk _ _)]
    rfl
  have hedge (w : Fin (n + 1) → Fin k) (r : RelationPath k)
      (hr : suffixBlock e start (n + 1) r = w) (i : Fin n) :
      (w i.succ).val = 0 ∨ (w i.succ).val = (w i.castSucc).val + 1 := by
    rw [← hr]
    simp only [suffixBlock, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact suffix_edge e r (start + i.val)
  have hac (w : Fin (n + 1) → Fin k) (hz : b w = 0) : a w = 0 := by
    have he : P.cells w = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun r hr => ?_
      change suffixBlock e start (n + 1) r = w at hr
      exact (wordMass_log hk w (hedge w r hr)).1.ne' ((hb w).symm.trans hz)
    simp [a, he]
  have herr (w : Fin (n + 1) → Fin k) (hz : b w ≠ 0) :
      |Real.log (b w) + (n : ℝ) * (-Real.log (parryParameter k))| ≤ wordError k := by
    have hn : (Q.cells w).Nonempty := by
      refine Set.nonempty_iff_ne_empty.2 fun he => ?_
      exact hz (by simp [b, he])
    obtain ⟨r, hr⟩ := hn
    rw [hb, mul_neg, ← sub_eq_add_neg]
    exact wordMass_log_error hk w (hedge w r hr)
  exact entropy_of_reference_mass a b ⟨fun _ => ENNReal.toReal_nonneg, P.sum_toReal_measure_eq_one⟩
    ⟨fun _ => ENNReal.toReal_nonneg, Q.sum_toReal_measure_eq_one⟩ hac _ _ herr


private def suffixAt (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (t : ℤ) (r : RelationPath k) : Fin k :=
  ((e (false, r)).val t).2

private theorem measurable_suffixAt (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (t : ℤ) : Measurable (suffixAt e t) :=
  measurable_snd.comp ((measurable_pi_apply t).comp
    (measurable_subtype_coe.comp (e.measurable.comp (measurable_const.prodMk measurable_id))))

private noncomputable def suffixPartition (ρ : Measure (RelationPath k))
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k) (t : ℤ) : MeasurePartition ρ (Fin k) :=
  fiberPartition ρ (suffixAt e t) (measurable_suffixAt e t)

private theorem block_saturations (ρ : Measure (RelationPath k))
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hbits : ∀ r : RelationPath k, ∀ t : ℤ, (suffixAt e t r).val = 0 ↔ r.val (t - 1) = false)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r) :
    let σ (radius : ℕ) := ⨆ n : ℕ, generatedSigmaAlgebra ρ
      (ksJoin T (suffixPartition ρ e (-(radius : ℤ))) n)
    Monotone σ ∧ (⨆ radius, σ radius) = (inferInstance : MeasurableSpace (RelationPath k)) := by
  let σ (r : ℕ) := ⨆ n : ℕ, MeasurableSpace.comap (suffixAt e (-(r : ℤ) + n)) inferInstance
  have hσ (r : ℕ) : (⨆ n : ℕ, generatedSigmaAlgebra ρ
      (ksJoin T (suffixPartition ρ e (-(r : ℤ))) n)) = σ r := by
    rw [iSup_generatedSigmaAlgebra_ksJoin_eq T]
    simp only [suffixPartition, generatedSigma_fiberPartition, MeasurableSpace.comap_comp]
    apply congrArg iSup
    funext n
    exact congrArg (fun f : RelationPath k → Fin k => MeasurableSpace.comap f inferInstance)
      (funext fun x => hshift x n _)
  dsimp only
  simp_rw [hσ]
  constructor
  · intro a b hab
    refine iSup_le fun n => ?_
    have hindex : -(a : ℤ) + n = -(b : ℤ) + ((n + (b - a) : ℕ) : ℤ) := by omega
    rw [hindex]
    exact le_iSup (fun j : ℕ => MeasurableSpace.comap (suffixAt e (-(b : ℤ) + j)) _) _
  · refine le_antisymm (iSup_le fun r => ?_) ?_
    · rw [← hσ]
      exact iSup_le fun n => generatedSigmaAlgebra_le _
    · change MeasurableSpace.comap (Subtype.val : RelationPath k → ℤ → Bool) _ ≤ _
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      refine iSup_le fun t => ?_
      let r := (t + 1).natAbs
      let n := (t + 1 + r).toNat
      let read (j : Fin k) : Bool := decide (j.val ≠ 0)
      have hindex : -(r : ℤ) + n = t + 1 := by dsimp [r, n]; omega
      have hcoord : (fun x : ℤ → Bool => x t) ∘ Subtype.val =
          read ∘ suffixAt e (-(r : ℤ) + n) := by
        funext x
        simp only [Function.comp_apply, read, hindex]
        have hz := hbits x (t + 1)
        rw [show t + 1 - 1 = t by omega] at hz
        cases ht : x.val t <;> simp_all
      rw [hcoord, ← MeasurableSpace.comap_comp]
      exact (MeasurableSpace.comap_mono (measurable_of_finite read).comap_le).trans
        ((le_iSup (fun j : ℕ => MeasurableSpace.comap (suffixAt e (-(r : ℤ) + j)) _) n).trans
          (le_iSup σ r))

private theorem suffix_seq_eq_block {ρ : Measure (RelationPath k)}
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (t : ℤ) (n : ℕ) :
    ksEntropySeq T (suffixPartition ρ e t) n = entropy ρ (blockPartition ρ e t n).cells := by
  unfold ksEntropySeq suffixPartition
  rw [ksJoin_fiber_cells]
  congr 1
  funext f
  ext r
  simp only [fiberPartition, blockPartition, Set.mem_preimage, Set.mem_singleton_iff]
  have hname : (fun i : Fin n => suffixAt e t (relationShift^[i.val] r)) =
      suffixBlock e t n r := funext fun i => hshift r i.val t
  rw [hname]

private theorem block_entropy_eq_origin {ρ : Measure (RelationPath k)}
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r)
    (r n : ℕ) :
    entropy ρ (blockPartition ρ e (-(r : ℤ)) n).cells =
      entropy ρ (blockPartition ρ e 0 n).cells := by
  rw [entropy_def, entropy_def]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  have hpre : (relationShift^[r]) ⁻¹' (blockPartition ρ e (-(r : ℤ)) n).cells w =
      (blockPartition ρ e 0 n).cells w := by
    ext x
    change (suffixBlock e (-(r : ℤ)) n (relationShift^[r] x) = w) ↔
      (suffixBlock e 0 n x = w)
    have hname : suffixBlock e (-(r : ℤ)) n (relationShift^[r] x) = suffixBlock e 0 n x := by
      funext i
      change suffixAt e (-(r : ℤ) + i.val) (relationShift^[r] x) = suffixAt e (0 + i.val) x
      rw [hshift, show -(r : ℤ) + i.val + r = 0 + i.val by omega]
    exact hname ▸ Iff.rfl
  rw [← hpre, (T.iterate r).measure_preimage
    ((blockPartition ρ e (-(r : ℤ)) n).measurable w).nullMeasurableSet]

private theorem ks_eq_suffix_partition {ρ : Measure (RelationPath k)} [IsProbabilityMeasure ρ]
    (T : MeasurePreserving (@relationShift k) ρ ρ)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hbits : ∀ r : RelationPath k, ∀ t : ℤ, (suffixAt e t r).val = 0 ↔ r.val (t - 1) = false)
    (hshift : ∀ r : RelationPath k, ∀ n : ℕ, ∀ t : ℤ,
      suffixAt e t (relationShift^[n] r) = suffixAt e (t + n) r) :
    ksEntropy T = (ksEntropyPartition T (suffixPartition ρ e 0) : EReal) := by
  have : StandardBorelSpace (RelationPath k) := relationPath_standardBorel
  apply le_antisymm ?_ (le_ksEntropy T _)
  have hσ := block_saturations ρ T e hbits hshift
  refine ksEntropy_le_of_increasing_partition_saturations T
    (fun r => suffixPartition ρ e (-(r : ℤ))) hσ.1 hσ.2 _ fun r => le_of_eq ?_
  have heq (n : ℕ) : ksEntropySeq T (suffixPartition ρ e (-(r : ℤ))) n =
      ksEntropySeq T (suffixPartition ρ e 0) n := by
    simp only [suffix_seq_eq_block T e hshift, block_entropy_eq_origin T e hshift]
  exact tendsto_nhds_unique (tendsto_ksEntropySeq T (suffixPartition ρ e (-(r : ℤ))))
    ((tendsto_ksEntropySeq T (suffixPartition ρ e 0)).congr fun n => by rw [heq])


private theorem div_affine_tendsto (h C : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h + C) / n) atTop (𝓝 h) := by
  have hlim : Tendsto (fun n : ℕ => h + C / (n : ℝ)) atTop (𝓝 h) := by
    simpa using (tendsto_const_nhds (x := h)).add
      (tendsto_const_div_atTop_nhds_zero_nat C)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnonzero : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [add_div, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hnonzero]

private theorem partition_le_of_affine_upper {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) (h C : ℝ)
    (hbound : ∀ m : ℕ, 1 ≤ m → ksEntropySeq hT P m ≤ (m : ℝ) * h + C) :
    ksEntropyPartition hT P ≤ h := by
  refine le_of_tendsto_of_tendsto (tendsto_ksEntropySeq hT P) (div_affine_tendsto h C) ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact div_le_div_of_nonneg_right (hbound m hm) (Nat.cast_nonneg m)

private theorem le_partition_of_affine_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) (h C : ℝ)
    (hbound : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * h + C ≤ ksEntropySeq hT P m) :
    h ≤ ksEntropyPartition hT P := by
  refine le_of_tendsto_of_tendsto (div_affine_tendsto h C) (tendsto_ksEntropySeq hT P) ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact div_le_div_of_nonneg_right (hbound m hm) (Nat.cast_nonneg m)

/-- The native bilateral Parry probability attains the full entropy bound for
all probability-preserving laws on the actual relation space. The maximizing
law here has the suffix cylinders of the bilateral Parry coding. -/
theorem bilateral_parry_entropy (k : ℕ) (hk : 2 ≤ k) :
    ∃ (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
      (μ : ProbabilityMeasure (RelationPath k))
      (Tμ : MeasurePreserving (@relationShift k) μ μ),
      (∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
        (μ : Measure (RelationPath k))
          {r | (fun i : Fin (n + 1) => ((e (false, r)).val (t + i.val)).2) = w} =
          ENNReal.ofReal (suffixLaw k (w 0)) *
            ∏ i : Fin n, ENNReal.ofReal (suffixKernel k (w i.castSucc) (w i.succ))) ∧
      ksEntropy Tμ = ((-Real.log (parryParameter k) : ℝ) : EReal) ∧
      (∀ (ρ : ProbabilityMeasure (RelationPath k))
        (Tρ : MeasurePreserving (@relationShift k) ρ ρ),
        ksEntropy Tρ ≤ ((-Real.log (parryParameter k) : ℝ) : EReal)) := by
  obtain ⟨e, μ, ν, _, hsuffix, _, _, hinv, _, _, _, hcyl⟩ := bilateral_parry_law k hk
  let Tμ : MeasurePreserving (@relationShift k) μ μ := ⟨measurable_relationShift, hinv⟩
  let h := -Real.log (parryParameter k)
  let C := wordError k
  have hbits (r : RelationPath k) (t : ℤ) :=
    suffix_zero_iff e hsuffix r t
  have hshift (r : RelationPath k) (n : ℕ) (t : ℤ) :=
    suffix_iterate_shift e hsuffix r n t
  have upper (ρ : ProbabilityMeasure (RelationPath k))
      (Tρ : MeasurePreserving (@relationShift k) ρ ρ) : ksEntropy Tρ ≤ (h : EReal) := by
    let Pρ : MeasurePartition (ρ : Measure (RelationPath k)) (Fin k) := suffixPartition ρ e 0
    have hupper : ksEntropyPartition Tρ Pρ ≤ h := by
      refine partition_le_of_affine_upper Tρ Pρ h (C - h) ?_
      intro m hm
      have hm' : m - 1 + 1 = m := by omega
      have hbound := (block_entropy_bounds hk e μ ρ hcyl 0 (m - 1)).1
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast hm'
      rw [hm'] at hbound
      dsimp only [Pρ]
      rw [suffix_seq_eq_block Tρ e hshift]
      change _ ≤ ((m - 1 : ℕ) : ℝ) * h + C at hbound
      linarith only [hbound, congrArg (· * h) hcast]
    exact (ks_eq_suffix_partition Tρ e hbits hshift).le.trans (EReal.coe_le_coe_iff.mpr hupper)
  have lower : (h : EReal) ≤ ksEntropy Tμ := by
    let Pμ : MeasurePartition (μ : Measure (RelationPath k)) (Fin k) := suffixPartition μ e 0
    have hlower : h ≤ ksEntropyPartition Tμ Pμ := by
      refine le_partition_of_affine_lower Tμ Pμ h (-C - h) ?_
      intro m hm
      have hm' : m - 1 + 1 = m := by omega
      have hbound := (block_entropy_bounds hk e μ μ hcyl 0 (m - 1)).2
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast hm'
      rw [hm'] at hbound
      dsimp only [Pμ]
      rw [suffix_seq_eq_block Tμ e hshift]
      change ((m - 1 : ℕ) : ℝ) * h - C ≤ _ at hbound
      linarith only [hbound, congrArg (· * h) hcast]
    exact (EReal.coe_le_coe_iff.mpr hlower).trans (ks_eq_suffix_partition Tμ e hbits hshift).ge
  exact ⟨e, μ, Tμ, hcyl, le_antisymm (upper μ Tμ) lower, upper⟩

end D5.S3.TotalVariation.ParryKSEntropy
