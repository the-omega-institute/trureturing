import D5.S3.Arith.ModularForms.RademacherRectangularConvergence

/-!
# Quantitative quadratic tails of the rectangular Rademacher sum

The vertical-strip estimate retains both bottom-row coordinates. The sum over
the second coordinate then gains one inverse power of the first coordinate.
The vertical tail can instead be bounded by a product of inverse-square sums.
-/

set_option autoImplicit false

open scoped UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherRectangularConvergence

open RademacherVacuum (cutoffPairs mem_cutoffPairs denominator quadraticRemainder
  norm_quadraticRemainder_le remainderCutoff)

noncomputable section

private def invSq (n : ℕ) : ℝ := ((n : ℝ) ^ 2)⁻¹

private theorem invSq_nonneg (n : ℕ) : 0 ≤ invSq n := by
  unfold invSq
  positivity

private theorem summable_invSq : Summable invSq :=
  Real.summable_nat_pow_inv.mpr (by decide)

private theorem invSq_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    invSq b ≤ invSq a := by
  unfold invSq
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact (inv_le_inv₀ (pow_pos (ha'.trans_le hab') 2) (pow_pos ha' 2)).mpr
    (pow_le_pow_left₀ ha'.le hab' 2)

private theorem tsum_invSq_add_le {M : ℕ} (hM : 0 < M) :
    (∑' n : ℕ, invSq (n + M)) ≤ 2 / (M : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => invSq_nonneg _)
  intro k
  have hM1 : M - 1 + 1 = M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hM1
  have hI : Finset.Ico M (M + k) = Finset.Ioo (M - 1) (M + k) := by
    simpa only [hM1] using
      (Finset.Ico_add_one_left_eq_Ioo (M - 1) (M + k))
  calc
    _ = ∑ n ∈ Finset.Ico M (M + k), invSq n := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      simp only [Nat.add_comm]
    _ = ∑ n ∈ Finset.Ioo (M - 1) (M + k), invSq n := by rw [hI]
    _ ≤ _ := by
      simpa only [invSq, hcast] using
        (sum_Ioo_inv_sq_le (α := ℝ) (M - 1) (M + k))

private theorem summable_nat_indicator_ge {f : ℕ → ℝ} (hf : Summable f) (M : ℕ) :
    Summable (fun n : ℕ => if M ≤ n then f n else 0) := by
  convert hf.indicator (Set.Ici M) using 1
  ext n
  simp only [Set.indicator_apply, Set.mem_Ici]

private theorem tsum_nat_indicator_ge {f : ℕ → ℝ} (hf : Summable f) (M : ℕ) :
    (∑' n : ℕ, if M ≤ n then f n else 0) = ∑' n : ℕ, f (n + M) := by
  let g : ℕ → ℝ := fun n => if M ≤ n then f n else 0
  have hg : Summable g := summable_nat_indicator_ge hf M
  have hsmall : ∑ n ∈ Finset.range M, g n = 0 :=
    Finset.sum_eq_zero fun n hn => ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hn))
  simpa only [hsmall, zero_add, g, Nat.le_add_left, ite_true] using
    (hg.sum_add_tsum_nat_add M).symm

private theorem tsum_invSq_le : (∑' c : ℕ, invSq c) ≤ 2 := by
  rw [← summable_invSq.sum_add_tsum_nat_add 1, Finset.sum_range_one]
  simpa [invSq] using tsum_invSq_add_le (M := 1) (by decide)

private theorem summable_invSq_natAbs : Summable (fun d : ℤ => invSq d.natAbs) := by
  simpa only [invSq, Nat.cast_natAbs, Int.cast_abs, sq_abs, inv_eq_one_div] using
    ((Real.summable_one_div_int_pow (p := 2)).mpr (by decide))

private def rowKernel (c : ℕ) (d : ℤ) : ℝ := invSq (max c d.natAbs)

private theorem summable_rowKernel {c : ℕ} (hc : 0 < c) : Summable (rowKernel c) := by
  have hOne : Summable (rowKernel 1) := by
    apply summable_invSq_natAbs.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with d hd
    have h : 1 ≤ d.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd)
    simp [rowKernel, max_eq_right h]
  exact hOne.of_nonneg_of_le (fun d => invSq_nonneg _)
    (fun d => invSq_antitone (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      (max_le_max hc (le_refl _)))

private theorem tsum_rowKernel_le {c : ℕ} (hc : 0 < c) :
    (∑' d : ℤ, rowKernel c d) ≤ 6 / (c : ℝ) := by
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hs := summable_rowKernel hc
  have heven : (rowKernel c).Even := fun d => by simp [rowKernel]
  have hnat : Summable (fun n : ℕ => invSq (max c n)) := by
    refine (hs.comp_injective (Nat.cast_injective (R := ℤ))).congr ?_
    intro n
    change rowKernel c (n : ℤ) = _
    simp only [rowKernel, Int.natAbs_natCast]
  have hsum : (∑' n : ℕ, invSq (max c n)) ≤ 3 / (c : ℝ) := by
    rw [← hnat.sum_add_tsum_nat_add c]
    have hsmall : ∑ n ∈ Finset.range c, invSq (max c n) = 1 / (c : ℝ) := by
      calc
        _ = ∑ _n ∈ Finset.range c, invSq c :=
          Finset.sum_congr rfl fun n hn =>
            congrArg invSq (max_eq_left (Finset.mem_range.mp hn).le)
        _ = _ := by
          simp [invSq, nsmul_eq_mul]
          field_simp
    simp only [hsmall, max_eq_right (Nat.le_add_left c _)]
    calc
      _ ≤ 1 / (c : ℝ) + 2 / (c : ℝ) := add_le_add_right (tsum_invSq_add_le hc) _
      _ = _ := by ring
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => rowKernel c (n : ℤ))]
  simp only [rowKernel, Int.natAbs_natCast, Int.natAbs_zero, max_zero, two_smul]
  have heq := hnat.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, max_zero] at heq
  calc
    _ ≤ 2 * (∑' n : ℕ, invSq (max c n)) := by
      rw [← heq]
      linarith only [invSq_nonneg c]
    _ ≤ 2 * (3 / (c : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

private def verticalKernel (D : ℕ) (d : ℤ) : ℝ :=
  if D ≤ d.natAbs then invSq d.natAbs else 0

private theorem verticalKernel_nonneg (D : ℕ) (d : ℤ) : 0 ≤ verticalKernel D d := by
  unfold verticalKernel
  split
  · exact invSq_nonneg _
  · exact le_rfl

private theorem summable_verticalKernel (D : ℕ) : Summable (verticalKernel D) := by
  exact summable_invSq_natAbs.of_nonneg_of_le (verticalKernel_nonneg D)
    (fun d => by unfold verticalKernel; split <;> simp [invSq_nonneg])

private theorem tsum_verticalKernel_le {D : ℕ} (hD : 0 < D) :
    (∑' d : ℤ, verticalKernel D d) ≤ 4 / (D : ℝ) := by
  have heven : (verticalKernel D).Even := fun d => by simp [verticalKernel]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_verticalKernel D),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => verticalKernel D (n : ℤ))]
  simp only [verticalKernel, Int.natAbs_zero, hD.not_ge, ite_false, zero_add,
    Int.natAbs_natCast, two_smul]
  have hg := summable_nat_indicator_ge summable_invSq D
  have heq := hg.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hD.not_ge, ite_false, zero_add] at heq
  rw [heq, tsum_nat_indicator_ge summable_invSq D]
  calc
    _ ≤ 2 * (2 / (D : ℝ)) := by
      rw [← two_mul]
      exact mul_le_mul_of_nonneg_left (tsum_invSq_add_le hD) (by norm_num)
    _ = _ := by ring

/-- Retaining the maximum of both row coordinates improves the compact majorant. -/
theorem quadraticRemainder_compact_max_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ c d : ℤ, 0 < c →
      ‖quadraticRemainder c d τ‖ ≤
        C / ((c : ℝ) ^ 2 * (max (c : ℝ) |(d : ℝ)|) ^ 2) := by
  obtain ⟨A, η, hη, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  let r := EisensteinSeries.r ⟨⟨A, η⟩, hη⟩
  let B := (2 * Real.pi) ^ 2 * Real.exp (2 * Real.pi / η)
  have hr : 0 < r := EisensteinSeries.r_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B / r ^ 2, by positivity, ?_⟩
  intro τ hτ c d hc
  let x : Fin 2 → ℤ := ![c, d]
  have hx : x ≠ 0 := by
    intro h
    exact hc.ne' (by simpa [x] using congrFun h (0 : Fin 2))
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hnorm : ‖x‖ = max (c : ℝ) |(d : ℝ)| := by
    simp [x, EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max, Nat.cast_natAbs,
      abs_of_pos hc']
  have hden : r * ‖x‖ ≤ ‖denominator c d τ‖ := by
    refine (mul_le_mul_of_nonneg_right
      (EisensteinSeries.r_lower_bound_on_verticalStrip τ hη (hstrip hτ))
      (norm_nonneg _)).trans ?_
    simpa [x, denominator] using EisensteinSeries.r_mul_max_le τ hx
  have hmul : 0 < r * ‖x‖ := mul_pos hr (norm_pos_iff.mpr hx)
  calc
    _ ≤ B / ((c : ℝ) ^ 2 * ‖denominator c d τ‖ ^ 2) :=
      norm_quadraticRemainder_le hc d τ hη ((hstrip hτ).2)
    _ ≤ B / ((c : ℝ) ^ 2 * (r * ‖x‖) ^ 2) :=
      div_le_div_of_nonneg_left hB.le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmul.le hden 2) (sq_nonneg _))
    _ = _ := by rw [hnorm]; simp only [mul_pow, div_div]; congr 1; ring

private def horizontalWeight (M : ℕ) (p : ℕ × ℤ) : ℝ :=
  if M ≤ p.1 then invSq p.1 * rowKernel p.1 p.2 else 0

private theorem horizontalWeight_nonneg (M : ℕ) (p : ℕ × ℤ) :
    0 ≤ horizontalWeight M p := by
  unfold horizontalWeight
  split
  · exact mul_nonneg (invSq_nonneg _) (invSq_nonneg _)
  · exact le_rfl

private theorem horizontalWeight_bound {M : ℕ} (hM : 0 < M) :
    Summable (horizontalWeight M) ∧ (∑' p, horizontalWeight M p) ≤ 12 / (M : ℝ) ^ 2 := by
  let g : ℕ → ℝ := fun c => if M ≤ c then invSq c else 0
  have hg : Summable g := summable_nat_indicator_ge summable_invSq M
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hfiber (c : ℕ) : Summable (fun d : ℤ => horizontalWeight M (c, d)) := by
    by_cases h : M ≤ c
    · simpa only [horizontalWeight, ite_eq_left h] using
        (summable_rowKernel (hM.trans_le h)).mul_left (invSq c)
    · simp [horizontalWeight, h]
  have hrow (c : ℕ) : (∑' d : ℤ, horizontalWeight M (c, d)) ≤ (6 / (M : ℝ)) * g c := by
    by_cases h : M ≤ c
    · have hc : 0 < c := hM.trans_le h
      have hcast : (M : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
      simp only [horizontalWeight, g, h, ite_true]
      rw [(summable_rowKernel hc).tsum_mul_left]
      calc
        _ ≤ invSq c * (6 / (c : ℝ)) :=
          mul_le_mul_of_nonneg_left (tsum_rowKernel_le hc) (invSq_nonneg _)
        _ ≤ invSq c * (6 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) hM' hcast)
            (invSq_nonneg _)
        _ = _ := mul_comm _ _
    · simp [horizontalWeight, g, h]
  have hrows : Summable (fun c : ℕ => ∑' d : ℤ, horizontalWeight M (c, d)) :=
    (hg.mul_left _).of_nonneg_of_le
      (fun c => tsum_nonneg fun d => horizontalWeight_nonneg M (c, d)) hrow
  have hs : Summable (horizontalWeight M) :=
    (summable_prod_of_nonneg (horizontalWeight_nonneg M)).mpr ⟨hfiber, hrows⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  calc
    _ ≤ ∑' c : ℕ, (6 / (M : ℝ)) * g c := hrows.tsum_le_tsum hrow (hg.mul_left _)
    _ = (6 / (M : ℝ)) * (∑' n : ℕ, invSq (n + M)) := by
      rw [hg.tsum_mul_left, tsum_nat_indicator_ge summable_invSq M]
    _ ≤ (6 / (M : ℝ)) * (2 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (tsum_invSq_add_le hM) (by positivity)
    _ = _ := by ring

private def verticalWeight (D : ℕ) (p : ℕ × ℤ) : ℝ :=
  invSq p.1 * verticalKernel D p.2

private theorem verticalWeight_nonneg (D : ℕ) (p : ℕ × ℤ) : 0 ≤ verticalWeight D p :=
  mul_nonneg (invSq_nonneg _) (verticalKernel_nonneg _ _)

private theorem verticalWeight_bound {D : ℕ} (hD : 0 < D) :
    Summable (verticalWeight D) ∧ (∑' p, verticalWeight D p) ≤ 8 / (D : ℝ) := by
  have hkernel := summable_verticalKernel D
  have hs : Summable (verticalWeight D) :=
    summable_invSq.mul_of_nonneg hkernel invSq_nonneg (verticalKernel_nonneg D)
  refine ⟨hs, ?_⟩
  change (∑' p : ℕ × ℤ, invSq p.1 * verticalKernel D p.2) ≤ _
  rw [← summable_invSq.tsum_mul_tsum hkernel hs]
  calc
    _ ≤ 2 * (4 / (D : ℝ)) :=
      mul_le_mul tsum_invSq_le (tsum_verticalKernel_le hD)
        (tsum_nonneg (verticalKernel_nonneg D)) (by norm_num)
    _ = _ := by ring

/-- The total absolute quadratic contribution omitted by independent strict
horizontal and vertical cutoffs on primitive rows. Both threshold values belong
to the omitted set. -/
theorem tsum_norm_quadraticRemainder_outside_rectangle_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ M D : ℕ, 1 ≤ M → 1 ≤ D →
      (∑' p : {p : PrimitiveRow // (M : ℤ) ≤ p.val.1 ∨ (D : ℤ) ≤ |p.val.2|},
        ‖quadraticRemainder p.val.val.1 p.val.val.2 τ‖) ≤
        C * ((1 / (M : ℝ) ^ 2) + (1 / (D : ℝ))) := by
  obtain ⟨B, hB, hmajor⟩ := quadraticRemainder_compact_max_bound hK
  refine ⟨12 * B, by positivity, ?_⟩
  intro τ hτ M D hM hD
  let Omitted := {p : PrimitiveRow // (M : ℤ) ≤ p.val.1 ∨ (D : ℤ) ≤ |p.val.2|}
  let e : Omitted → ℕ × ℤ := fun p => (p.val.val.1.toNat, p.val.val.2)
  have hcast (p : Omitted) : ((e p).1 : ℤ) = p.val.val.1 :=
    Int.toNat_of_nonneg p.val.property.1.le
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rw [← hcast p, ← hcast q, h]) ?_
    exact congrArg (fun r : ℕ × ℤ => r.2) h
  let H := horizontalWeight M
  let V := verticalWeight D
  have hH := horizontalWeight_bound hM
  have hV := verticalWeight_bound hD
  have hnonneg (r : ℕ × ℤ) : 0 ≤ B * (H r + V r) :=
    mul_nonneg hB.le (add_nonneg (horizontalWeight_nonneg _ _) (verticalWeight_nonneg _ _))
  have hbound (p : Omitted) :
      ‖quadraticRemainder p.val.val.1 p.val.val.2 τ‖ ≤ B * (H (e p) + V (e p)) := by
    obtain ⟨⟨⟨c, d⟩, hc, _⟩, hout⟩ := p
    let n := c.toNat
    have hn : (n : ℤ) = c := Int.toNat_of_nonneg hc.le
    have hcr : (c : ℝ) = (n : ℝ) := by exact_mod_cast hn.symm
    have hdr : |(d : ℝ)| = (d.natAbs : ℝ) := by simp [Nat.cast_natAbs, Int.cast_abs]
    change ‖quadraticRemainder c d τ‖ ≤ B * (H (n, d) + V (n, d))
    calc
      _ ≤ B / ((c : ℝ) ^ 2 * (max (c : ℝ) |(d : ℝ)|) ^ 2) := hmajor τ hτ c d hc
      _ = B * (invSq n * rowKernel n d) := by
        simp only [invSq, rowKernel, hcr, hdr, Nat.cast_max, div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        rcases hout with h | h
        · change (M : ℤ) ≤ c at h
          have hMn : M ≤ n := by exact_mod_cast (hn.symm ▸ h)
          exact (le_of_eq (by simp [H, horizontalWeight, hMn])).trans
            (le_add_of_nonneg_right (verticalWeight_nonneg D (n, d)))
        · change (D : ℤ) ≤ |d| at h
          have hDn : D ≤ d.natAbs := by exact_mod_cast (show (D : ℤ) ≤ (d.natAbs : ℤ) by
            simpa only [Int.abs_eq_natAbs] using h)
          have hnD : 0 < d.natAbs := Nat.le_trans hD hDn
          have hk : rowKernel n d ≤ invSq d.natAbs :=
            invSq_antitone hnD (le_max_right _ _)
          exact (mul_le_mul_of_nonneg_left hk (invSq_nonneg _)).trans
            (show invSq n * invSq d.natAbs ≤ H (n, d) + V (n, d) by
              simpa only [V, verticalWeight, verticalKernel, hDn, ite_true] using
                le_add_of_nonneg_left (horizontalWeight_nonneg M (n, d)))
  have hs := (summable_norm_quadraticRemainder τ).subtype
    (fun p : PrimitiveRow => (M : ℤ) ≤ p.val.1 ∨ (D : ℤ) ≤ |p.val.2|)
  have hsum : Summable (fun r => B * (H r + V r)) := (hH.1.add hV.1).mul_left B
  calc
    _ ≤ ∑' r : ℕ × ℤ, B * (H r + V r) :=
      Summable.tsum_le_tsum_of_inj e he (fun r _ => hnonneg r) hbound hs hsum
    _ = B * ((∑' r, H r) + ∑' r, V r) := by
      rw [(hH.1.add hV.1).tsum_mul_left, hH.1.tsum_add hV.1]
    _ ≤ B * (12 / (M : ℝ) ^ 2 + 8 / (D : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hH.2 hV.2) hB.le
    _ ≤ B * (12 / (M : ℝ) ^ 2 + 12 / (D : ℝ)) := by
      gcongr
      norm_num
    _ = _ := by ring

private theorem remainderCutoff_eq_sum_cutoffRows (N : ℕ) (τ : ℍ) :
    remainderCutoff N τ = ∑ p ∈ cutoffRows N, quadraticRemainder p.val.1 p.val.2 τ := by
  symm
  exact Finset.sum_subtype_of_mem (fun p : ℤ × ℤ => quadraticRemainder p.1 p.2 τ)
    (fun ⟨c, d⟩ hp => ⟨(mem_cutoffPairs.mp hp).1, (mem_cutoffPairs.mp hp).2.2.2⟩)

/-- Compact-uniform inverse-square error for the literal physical rectangle
(0<c<N, |d|<N^2), including (N=1). -/
theorem norm_remainderLimit_sub_remainderCutoff_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ N : ℕ, 1 ≤ N →
      ‖remainderLimit τ - remainderCutoff N τ‖ ≤ C / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, htail⟩ := tsum_norm_quadraticRemainder_outside_rectangle_le hK
  refine ⟨2 * C, by positivity, ?_⟩
  intro τ hτ N hN
  have hpred (p : PrimitiveRow) :
      p ∉ cutoffRows N ↔ (N : ℤ) ≤ p.val.1 ∨ ((N ^ 2 : ℕ) : ℤ) ≤ |p.val.2| := by
    rw [mem_cutoffRows, mem_cutoffPairs]
    simp only [Nat.cast_pow, p.property.1, p.property.2, true_and, and_true,
      not_and_or, not_lt]
  let e : {p : PrimitiveRow // p ∉ cutoffRows N} ≃
      {p : PrimitiveRow // (N : ℤ) ≤ p.val.1 ∨ ((N ^ 2 : ℕ) : ℤ) ≤ |p.val.2|} :=
    Equiv.subtypeEquivRight hpred
  have hs := summable_norm_quadraticRemainder τ
  have hout := hs.subtype (fun p : PrimitiveRow => p ∉ cutoffRows N)
  rw [remainderCutoff_eq_sum_cutoffRows, remainderLimit,
    ← hs.of_norm.sum_add_tsum_subtype_compl (cutoffRows N), add_sub_cancel_left]
  calc
    _ ≤ ∑' p : {p : PrimitiveRow // p ∉ cutoffRows N},
        ‖quadraticRemainder p.val.val.1 p.val.val.2 τ‖ := norm_tsum_le_tsum_norm hout
    _ = ∑' p : {p : PrimitiveRow // (N : ℤ) ≤ p.val.1 ∨ ((N ^ 2 : ℕ) : ℤ) ≤ |p.val.2|},
        ‖quadraticRemainder p.val.val.1 p.val.val.2 τ‖ :=
      e.tsum_eq (fun p => ‖quadraticRemainder p.val.val.1 p.val.val.2 τ‖)
    _ ≤ C * (1 / (N : ℝ) ^ 2 + 1 / ((N ^ 2 : ℕ) : ℝ)) :=
      htail τ hτ N (N ^ 2) hN (Nat.one_le_pow 2 N hN)
    _ = _ := by push_cast; ring

end

end D5.S3.Arith.ModularForms.RademacherRectangularConvergence
