/- GID: D5/S3/Arith/ModularForms/RademacherRectangularConvergence
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local uniform convergence and translation invariance of the normalized rectangular Rademacher sum. -/

import D5.S3.Arith.ModularForms.RademacherLinearTailConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Order.Compact

/-!
# The normalized rectangular Rademacher limit

The genuine rectangular vacuum cutoff converges locally uniformly after subtraction of `12`.
The limit is the polar seed, the positive-power principal-value Fourier tail, and an
absolutely convergent sum of quadratic remainders over primitive positive rows.
Translation by one preserves the limit.
-/

open Filter
open scoped BigOperators Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherRectangularConvergence

open D5.S3.Arith.ModularForms.RademacherVacuum
open D5.S3.Arith.ModularForms.RademacherLinearCutoff
  (linearPhase linearRectangularCutoff linearPrincipalValueCutoff strictDenominators
    linearRectangularCutoff_sub_tendstoUniformlyOn)
open D5.S3.Arith.ModularForms.RademacherPhaseRamanujan
  (linearPhase_eq_vacuumPhase linearConstantCutoff tendsto_linearConstantCutoff
    linearPrincipalValueQTail linearPrincipalValueCutoff_eq_constant_add_qTail)
open D5.S3.Arith.ModularForms.RademacherLinearTailConvergence
  (linearPrincipalValueQTailLimit tendstoLocallyUniformly_linearPrincipalValueQTail)

set_option autoImplicit false

/-- Bottom rows with positive first entry and coprime entries. -/
abbrev PrimitiveRow := {p : ℤ × ℤ // 0 < p.1 ∧ Int.gcd p.1 p.2 = 1}

/-- The literal rectangle viewed as a finite subset of the primitive positive rows. -/
def cutoffRows (N : ℕ) : Finset PrimitiveRow :=
  (cutoffPairs N).subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1)

theorem mem_cutoffRows {N : ℕ} {p : PrimitiveRow} :
    p ∈ cutoffRows N ↔ (p : ℤ × ℤ) ∈ cutoffPairs N :=
  Finset.mem_subtype

theorem eventually_mem_cutoffPairs (p : PrimitiveRow) :
    ∀ᶠ N : ℕ in atTop, (p : ℤ × ℤ) ∈ cutoffPairs N := by
  rcases p with ⟨⟨c, d⟩, hc, hprim⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max c |d|)
  filter_upwards [eventually_ge_atTop n] with N hN
  have hcast : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmax := hn.trans_le hcast
  exact mem_cutoffPairs.mpr
    ⟨hc, (le_max_left _ _).trans_lt hmax,
      ((le_max_right _ _).trans_lt hmax).trans_le (Int.le_self_sq _), hprim⟩

/-- Every finite set of primitive positive rows lies in all sufficiently large rectangles. -/
theorem tendsto_cutoffRows : Tendsto cutoffRows atTop atTop := by
  refine tendsto_atTop.2 (fun s => ?_)
  have h : ∀ᶠ N in atTop, ∀ p ∈ s, p ∈ cutoffRows N :=
    s.eventually_all.2 (fun p _ =>
      (eventually_mem_cutoffPairs p).mono (fun _ hp => mem_cutoffRows.mpr hp))
  exact h.mono (fun _ hN p hp => hN p hp)

noncomputable section

/-- The sum of quadratic remainders indexed by the primitive positive rows. -/
def remainderLimit (τ : ℍ) : ℂ :=
  ∑' p : PrimitiveRow, quadraticRemainder p.val.1 p.val.2 τ

theorem summable_norm_quadraticRemainder (τ : ℍ) :
    Summable (fun p : PrimitiveRow => ‖quadraticRemainder p.val.1 p.val.2 τ‖) := by
  obtain ⟨C, _, hsum, hbound⟩ :=
    quadraticRemainder_compact_majorant (isCompact_singleton (x := τ))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => hbound τ (Set.mem_singleton τ) p.val.1 p.val.2 p.property.1)
    (hsum.subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1))

/-- The M-test along the literal cutoff `cutoffPairs N`. -/
theorem tendstoUniformlyOn_remainderCutoff {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn remainderCutoff remainderLimit atTop K := by
  obtain ⟨C, _, hsum, hbound⟩ := quadraticRemainder_compact_majorant hK
  have hM := tendstoUniformlyOn_tsum
    (f := fun (p : PrimitiveRow) (τ : ℍ) => quadraticRemainder p.val.1 p.val.2 τ)
    (s := K) (hsum.subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1))
    (fun p τ hτ => hbound τ hτ p.val.1 p.val.2 p.property.1)
  have hcut : TendstoUniformlyOn
      (fun N τ => ∑ p ∈ cutoffRows N, quadraticRemainder p.val.1 p.val.2 τ)
      remainderLimit atTop K :=
    fun u hu => tendsto_cutoffRows.eventually (hM u hu)
  apply hcut.congr
  refine Eventually.of_forall (fun N τ _ => ?_)
  exact Finset.sum_subtype_of_mem (fun p : ℤ × ℤ => quadraticRemainder p.1 p.2 τ)
    (fun ⟨c, d⟩ hp =>
      ⟨(mem_cutoffPairs.mp hp).1, (mem_cutoffPairs.mp hp).2.2.2⟩)

/-- The quadratic cutoff is locally uniform on the upper half-plane. -/
theorem tendstoLocallyUniformly_remainderCutoff :
    TendstoLocallyUniformly remainderCutoff remainderLimit atTop :=
  tendstoLocallyUniformly_iff_forall_isCompact.mpr
    (fun _ hK => tendstoUniformlyOn_remainderCutoff hK)

private theorem vacuumPhase_eq_of_modEq {c d e : ℤ} (hc : 0 < c)
    (hd : Int.gcd c d = 1) (he : Int.gcd c e = 1) (hde : d ≡ e [ZMOD c]) :
    vacuumPhase c d = vacuumPhase c e := by
  obtain ⟨hd₀, hdc, hdInv⟩ := inverseResidue_spec hc hd
  obtain ⟨he₀, hec, heInv⟩ := inverseResidue_spec hc he
  have hdInv' : e * inverseResidue c d ≡ 1 [ZMOD c] :=
    (hde.symm.mul_right _).trans hdInv
  have h₁ : inverseResidue c d ≡ inverseResidue c d * (e * inverseResidue c e) [ZMOD c] := by
    simpa only [mul_one] using heInv.symm.mul_left (inverseResidue c d)
  have h₂ : inverseResidue c d * (e * inverseResidue c e) ≡ inverseResidue c e [ZMOD c] := by
    rw [show inverseResidue c d * (e * inverseResidue c e) =
      inverseResidue c e * (e * inverseResidue c d) by ring]
    simpa only [mul_one] using hdInv'.mul_left (inverseResidue c e)
  have hinv : inverseResidue c d = inverseResidue c e := by
    simpa only [Int.emod_eq_of_lt hd₀ hdc, Int.emod_eq_of_lt he₀ hec] using
      (h₁.trans h₂).eq
  simp only [vacuumPhase, hinv]

private theorem linearPhase_mod_eq_vacuumPhase {c d : ℤ} (hc : 0 < c) (hd : d.gcd c = 1) :
    linearPhase c (d % c) = vacuumPhase c d := by
  have hmod : (d % c).gcd c = 1 := (Int.gcd_emod d c).trans hd
  exact (linearPhase_eq_vacuumPhase hc hmod).trans
    (vacuumPhase_eq_of_modEq hc ((Int.gcd_comm _ _).trans hmod)
      ((Int.gcd_comm _ _).trans hd) (Int.mod_modEq d c))

private theorem mem_strictDenominators {M c d : ℤ} :
    d ∈ strictDenominators M c ↔ |d| < M ∧ Int.gcd c d = 1 := by
  simp only [strictDenominators, Finset.mem_filter, Finset.mem_Ioo, abs_lt, Int.gcd_comm d c]

/-- The two finite linear sums use the same strict rectangle and the same complex phase. -/
theorem linearCutoff_eq_linearRectangularCutoff (N : ℕ) (τ : ℍ) :
    linearCutoff N τ = linearRectangularCutoff N (τ : ℂ) := by
  unfold linearCutoff linearRectangularCutoff
  rw [Finset.sum_sigma']
  let toSigma (p : ℤ × ℤ) : Σ _ : ℕ, ℤ := ⟨p.1.toNat, p.2⟩
  let toRow (p : Σ _ : ℕ, ℤ) : ℤ × ℤ := ((p.1 : ℤ), p.2)
  refine Finset.sum_nbij' toSigma toRow ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, hcN, hd, hprim⟩ := mem_cutoffPairs.mp hp
    have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
    apply Finset.mem_sigma.mpr
    change c.toNat ∈ (Finset.range N).erase 0 ∧
      d ∈ strictDenominators ((N : ℤ) ^ 2) (c.toNat : ℤ)
    rw [hcCast, mem_strictDenominators, Finset.mem_erase, Finset.mem_range]
    have hcNat : 0 < c.toNat := by omega
    exact ⟨⟨hcNat.ne', by omega⟩, hd, hprim⟩
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hc₀, hcN⟩ := Finset.mem_erase.mp hc
    obtain ⟨hd, hprim⟩ := mem_strictDenominators.mp hd
    change ((c : ℤ), d) ∈ cutoffPairs N
    exact mem_cutoffPairs.mpr
      ⟨by exact_mod_cast Nat.pos_of_ne_zero hc₀, by exact_mod_cast Finset.mem_range.mp hcN,
        hd, hprim⟩
  · rintro ⟨c, d⟩ hp
    change ((c.toNat : ℤ), d) = (c, d)
    rw [Int.toNat_of_nonneg (mem_cutoffPairs.mp hp).1.le]
  · rintro ⟨c, d⟩ _
    change (⟨(c : ℤ).toNat, d⟩ : Σ _ : ℕ, ℤ) = ⟨c, d⟩
    rw [Int.toNat_natCast]
  · rintro ⟨c, d⟩ hp
    obtain ⟨hc, _, _, hprim⟩ := mem_cutoffPairs.mp hp
    change linearSummand c d τ = linearPhase (c.toNat : ℤ) (d % (c.toNat : ℤ)) *
      (2 * (Real.pi : ℂ) * Complex.I /
        ((c.toNat : ℂ) * ((c.toNat : ℂ) * (τ : ℂ) + (d : ℂ))))
    have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
    have hcC : (c.toNat : ℂ) = (c : ℂ) := by exact_mod_cast hcCast
    rw [hcCast, hcC,
      linearPhase_mod_eq_vacuumPhase hc ((Int.gcd_comm _ _).trans hprim)]
    simp only [linearSummand, vacuumArgument, denominator, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

private theorem tendstoUniformlyOn_linearCutoff_sub_twelve {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N τ => linearCutoff N τ - 12)
      linearPrincipalValueQTailLimit atTop K := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_norm.comp UpperHalfPlane.continuous_coe).continuousOn
  have herror := (linearRectangularCutoff_sub_tendstoUniformlyOn B).comp
    (fun τ : ℍ => (τ : ℂ))
  have hK' : K ⊆ (fun τ : ℍ => (τ : ℂ)) ⁻¹' {z : ℂ | ‖z‖ ≤ B ∧ 0 < z.im} :=
    fun τ hτ => ⟨hB (Set.mem_image_of_mem _ hτ), τ.im_pos⟩
  have hconst := tendsto_linearConstantCutoff.tendstoUniformlyOn_const K
  have h12 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (12 : ℂ)) atTop (𝓝 12))
    |>.tendstoUniformlyOn_const K
  have htail := tendstoLocallyUniformly_iff_forall_isCompact.mp
    tendstoLocallyUniformly_linearPrincipalValueQTail K hK
  have h := (((herror.mono hK').add hconst).sub h12).add htail
  refine (h.congr (F' := fun N τ => linearCutoff N τ - 12) ?_).congr_right ?_
  · refine Eventually.of_forall (fun N τ _ => ?_)
    change linearRectangularCutoff N (τ : ℂ) - linearPrincipalValueCutoff N (τ : ℂ) +
      linearConstantCutoff N - 12 + linearPrincipalValueQTail N τ = linearCutoff N τ - 12
    rw [linearCutoff_eq_linearRectangularCutoff, linearPrincipalValueCutoff_eq_constant_add_qTail]
    abel
  · intro τ _
    change (0 : ℂ) + 12 - 12 + linearPrincipalValueQTailLimit τ =
      linearPrincipalValueQTailLimit τ
    abel

/-- The normalized limit in terms of the polar seed and the two convergent series. -/
def rademacherLimit (τ : ℍ) : ℂ :=
  (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ + linearPrincipalValueQTailLimit τ + remainderLimit τ

private theorem qParam_inv_eq (τ : ℍ) :
    (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ =
      Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul]

/-- The normalized rectangular Rademacher sum converges uniformly on every compact set. -/
theorem tendstoUniformlyOn_rademacherCutoff_sub_twelve {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N τ => rademacherCutoff N τ - 12) rademacherLimit atTop K := by
  have hpole : TendstoUniformlyOn (fun (_ : ℕ) (τ : ℍ) =>
      (Function.Periodic.qParam 1 (τ : ℂ))⁻¹)
      (fun τ => (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) atTop K := by
    exact Metric.tendstoUniformlyOn_iff.2
      (fun ε hε => Eventually.of_forall (fun _ τ _ => by simpa only [dist_self] using hε))
  have h := (hpole.add (tendstoUniformlyOn_linearCutoff_sub_twelve hK)).add
    (tendstoUniformlyOn_remainderCutoff hK)
  apply h.congr
  refine Eventually.of_forall (fun N τ _ => ?_)
  change (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ + (linearCutoff N τ - 12) +
    remainderCutoff N τ = rademacherCutoff N τ - 12
  rw [qParam_inv_eq, rademacherCutoff_eq]
  abel

/-- Local uniform convergence for the original strict rectangles with subtraction of `12`. -/
theorem tendstoLocallyUniformly_rademacherCutoff_sub_twelve :
    TendstoLocallyUniformly (fun N τ => rademacherCutoff N τ - 12) rademacherLimit atTop :=
  tendstoLocallyUniformly_iff_forall_isCompact.mpr
    (fun _ hK => tendstoUniformlyOn_rademacherCutoff_sub_twelve hK)

private def shiftRow : PrimitiveRow ≃ PrimitiveRow where
  toFun p := ⟨(p.val.1, p.val.2 + p.val.1), p.property.1,
    (Int.gcd_add_self_right _ _).trans p.property.2⟩
  invFun p := ⟨(p.val.1, p.val.2 - p.val.1), p.property.1, by
    have h := Int.gcd_add_self_right p.val.1 (p.val.2 - p.val.1)
    rw [sub_add_cancel] at h
    exact h.symm.trans p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, p.val.2 + p.val.1 - p.val.1) = p.val
    exact Prod.ext rfl (add_sub_cancel_right _ _)
  right_inv p := by
    apply Subtype.ext
    change (p.val.1, p.val.2 - p.val.1 + p.val.1) = p.val
    exact Prod.ext rfl (sub_add_cancel _ _)

private theorem quadraticRemainder_one_vadd {c d : ℤ} (hc : 0 < c)
    (hd : Int.gcd c d = 1) (τ : ℍ) :
    quadraticRemainder c d ((1 : ℝ) +ᵥ τ) = quadraticRemainder c (d + c) τ := by
  have hmod : d ≡ d + c [ZMOD c] :=
    Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  have hphase := vacuumPhase_eq_of_modEq hc hd
    ((Int.gcd_add_self_right c d).trans hd) hmod
  have hdenom : denominator c d ((1 : ℝ) +ᵥ τ) = denominator c (d + c) τ := by
    simp only [denominator, UpperHalfPlane.coe_vadd, Complex.ofReal_one, Int.cast_add]
    ring
  simp only [quadraticRemainder, vacuumArgument, hdenom, hphase]

/-- Translation by one reindexes the actual absolutely convergent remainder by `d ↦ d + c`. -/
theorem remainderLimit_one_vadd (τ : ℍ) :
    remainderLimit ((1 : ℝ) +ᵥ τ) = remainderLimit τ := by
  unfold remainderLimit
  calc
    _ = ∑' p : PrimitiveRow, quadraticRemainder (shiftRow p).val.1 (shiftRow p).val.2 τ := by
      apply tsum_congr
      intro p
      exact quadraticRemainder_one_vadd p.property.1 p.property.2 τ
    _ = _ := (shiftRow.hasSum_iff.mpr (summable_norm_quadraticRemainder τ).of_norm.hasSum).tsum_eq

private theorem qParam_one_vadd (τ : ℍ) :
    Function.Periodic.qParam 1 (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) := by
  simp only [UpperHalfPlane.coe_vadd, Function.Periodic.qParam, Complex.ofReal_one, div_one,
    mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

/-- The independent rectangular limit is invariant under `T : τ ↦ τ + 1`. -/
theorem rademacherLimit_one_vadd (τ : ℍ) :
    rademacherLimit ((1 : ℝ) +ᵥ τ) = rademacherLimit τ := by
  have htail : linearPrincipalValueQTailLimit ((1 : ℝ) +ᵥ τ) =
      linearPrincipalValueQTailLimit τ := by
    unfold linearPrincipalValueQTailLimit
    rw [qParam_one_vadd]
  unfold rademacherLimit
  rw [qParam_one_vadd, htail, remainderLimit_one_vadd]

end

end D5.S3.Arith.ModularForms.RademacherRectangularConvergence
