/- GID: D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite
   mirror-E: none(waiver:structural-nonvacuity-characterization-only)
   anchors: []
   digest: ZeroData is inhabited exactly when the nontrivial zeta-zero set is infinite. -/

import D5.S3.Weil.ZeroSum
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ComplexConjugate

namespace D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite

open D5.S3.Weil.Convention D5.S3.Weil.ZeroSum

private abbrev NontrivialZeroSet : Set ℂ := {rho | IsNontrivialZero rho}

private lemma nontrivialZeroSet_subset : NontrivialZeroSet ⊆ riemannZetaZeros :=
  fun _ h => h.1

private theorem infinite_of_zeroData (Z : ZeroData) : NontrivialZeroSet.Infinite :=
  Set.infinite_of_injective_forall_mem Z.zero_injective Z.zero_isNontrivial

private theorem countable_riemannZetaZeros : riemannZetaZeros.Countable :=
  isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete isDiscrete_riemannZetaZeros

private theorem countable_nontrivialZeroSet : NontrivialZeroSet.Countable :=
  countable_riemannZetaZeros.mono nontrivialZeroSet_subset

private lemma spectralRadius_eq (rho : ℂ) :
    D5.S3.Weil.ZeroSum.spectralRadius rho =
      ‖rho - (criticalAbscissa : ℂ)‖ := by
  simp [D5.S3.Weil.ZeroSum.spectralRadius, spectralParameter]

private theorem finite_nontrivialZeroSet_spectralRadius_le (T : ℝ) :
    {rho | IsNontrivialZero rho ∧ spectralRadius rho ≤ T}.Finite := by
  have hK : IsCompact (Metric.closedBall ((criticalAbscissa : ℂ)) T) :=
    isCompact_closedBall _ _
  refine hK.inter_riemannZetaZeros_finite.subset ?_
  rintro rho ⟨h1, h2⟩
  refine ⟨?_, h1.1⟩
  rw [Metric.mem_closedBall, dist_eq_norm, ← spectralRadius_eq]
  exact h2

private lemma ne_one_of_isNontrivialZero {rho : ℂ} (h : IsNontrivialZero rho) : rho ≠ 1 := by
  rintro rfl
  simp [IsNontrivialZero] at h

private lemma ne_neg_nat_of_isNontrivialZero {rho : ℂ} (h : IsNontrivialZero rho)
    (n : ℕ) : rho ≠ -n := by
  rintro rfl
  have hpos := h.2.1
  simp at hpos
  exact (not_lt.mpr (Nat.cast_nonneg n)) hpos

private theorem exists_multiplicity {rho : ℂ} (h : IsNontrivialZero rho) :
    ∃ m, HasZetaZeroMultiplicity rho m := by
  have hrho1 : rho ≠ 1 := ne_one_of_isNontrivialZero h
  have han : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrho1
  have hne : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    refine analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected (x := 2)
      (by simp) hrho1 ?_
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact h2 htop.self_of_nhds
  obtain ⟨g, hg, hg0, hfg⟩ := han.analyticOrderAt_ne_top.1 hne
  refine ⟨analyticOrderNatAt riemannZeta rho, ?_, g, hg, hg0, ?_⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    have horder : analyticOrderAt riemannZeta rho = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hne, h0]
      rfl
    rw [analyticOrderAt_eq_zero] at horder
    rcases horder with horder | horder
    · exact horder han
    · exact horder h.1
  · simpa [Filter.EventuallyEq, smul_eq_mul] using hfg

private theorem multiplicity_unique {rho : ℂ} {m n : ℕ}
    (hm : HasZetaZeroMultiplicity rho m) (hn : HasZetaZeroMultiplicity rho n) : m = n := by
  obtain ⟨_, u, hu, hu0, hfu⟩ := hm
  obtain ⟨_, v, hv, hv0, hfv⟩ := hn
  exact AnalyticAt.unique_eventuallyEq_pow_smul_nonzero (f := riemannZeta) (z₀ := rho)
    ⟨u, hu, hu0, by simpa [Filter.EventuallyEq, smul_eq_mul] using hfu⟩
    ⟨v, hv, hv0, by simpa [Filter.EventuallyEq, smul_eq_mul] using hfv⟩

private theorem isNontrivialZero_one_sub {rho : ℂ} (h : IsNontrivialZero rho) :
    IsNontrivialZero (1 - rho) := by
  refine ⟨?_, ?_, ?_⟩
  · show riemannZeta (1 - rho) = 0
    rw [riemannZeta_one_sub (ne_neg_nat_of_isNontrivialZero h)
      (ne_one_of_isNontrivialZero h)]
    have hz : riemannZeta rho = 0 := h.1
    rw [hz, mul_zero]
  · simp
    linarith [h.2.2]
  · simp
    linarith [h.2.1]

private theorem isNontrivialZero_conj {rho : ℂ} (h : IsNontrivialZero rho) :
    IsNontrivialZero (conj rho) := by
  refine ⟨?_, ?_, ?_⟩
  · show riemannZeta (conj rho) = 0
    have hz : riemannZeta rho = 0 := h.1
    rw [riemannZeta_conj, hz, map_zero]
  · simpa using h.2.1
  · simpa using h.2.2

private noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
    Complex.cos ((Real.pi : ℂ) * s / 2)

private lemma ne_neg_nat_of_strip {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (n : ℕ) :
    s ≠ -n := by
  rintro rfl
  have hpos := hs.1
  simp at hpos
  exact (not_lt.mpr (Nat.cast_nonneg n)) hpos

private lemma ne_one_of_strip {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) : s ≠ 1 := by
  rintro rfl
  have hlt := hs.2
  simp at hlt

private theorem differentiableAt_chi {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    DifferentiableAt ℂ chi s := by
  unfold chi
  refine (((differentiableAt_const _).mul ?_).mul
    (Complex.differentiableAt_Gamma s (ne_neg_nat_of_strip hs))).mul ?_
  · exact (differentiableAt_id.neg).const_cpow (Or.inl (by norm_num [Real.pi_ne_zero]))
  · exact Complex.differentiable_cos.differentiableAt.comp s
      (((differentiableAt_const _).mul differentiableAt_id).div_const _)

private theorem chi_ne_zero {rho : ℂ} (h : IsNontrivialZero rho) : chi rho ≠ 0 := by
  unfold chi
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num [Real.pi_ne_zero]))
  · exact Complex.Gamma_ne_zero_of_re_pos h.2.1
  · intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h1 : (Real.pi : ℂ) * rho = (Real.pi : ℂ) * (2 * k + 1) := by
      linear_combination 2 * hk
    have hrho : rho = 2 * k + 1 := mul_left_cancel₀ hpi h1
    have h2 := h.2.1
    have h3 := h.2.2
    rw [hrho] at h2 h3
    simp at h2 h3
    have hk1 : (k : ℝ) < 0 := by linarith
    have hk2 : (-1 : ℝ) < k := by linarith
    have hk1' : k < 0 := by exact_mod_cast hk1
    have hk2' : -1 < k := by exact_mod_cast hk2
    omega

private theorem hasZetaZeroMultiplicity_one_sub {rho : ℂ} {m : ℕ}
    (h : IsNontrivialZero rho) (hm : HasZetaZeroMultiplicity rho m) :
    HasZetaZeroMultiplicity (1 - rho) m := by
  obtain ⟨hm0, u, hu, hu0, hfu⟩ := hm
  have htend : Tendsto (fun w : ℂ => 1 - w) (nhds (1 - rho)) (nhds rho) := by
    have hc : Continuous (fun w : ℂ => 1 - w) := continuous_const.sub continuous_id
    simpa using hc.tendsto (1 - rho)
  have hstrip : ∀ᶠ s in nhds rho, 0 < s.re ∧ s.re < 1 := by
    have ho : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    exact ho.mem_nhds ⟨h.2.1, h.2.2⟩
  refine ⟨hm0, fun w => (-1 : ℂ) ^ m * chi (1 - w) * u (1 - w), ?_, ?_, ?_⟩
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have h1 : ∀ᶠ z in nhds rho, DifferentiableAt ℂ u z :=
      hu.eventually_analyticAt.mono fun z hz => hz.differentiableAt
    filter_upwards [htend.eventually h1, htend.eventually hstrip] with w hw hws
    have hsub : DifferentiableAt ℂ (fun w : ℂ => 1 - w) w :=
      (differentiableAt_const _).sub differentiableAt_id
    exact (((differentiableAt_chi hws).comp w hsub).const_mul _).mul (hw.comp w hsub)
  · simp only [sub_sub_cancel]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (chi_ne_zero h)) hu0
  · filter_upwards [htend.eventually hfu, htend.eventually hstrip] with w hw hws
    have hfe : riemannZeta w = chi (1 - w) * riemannZeta (1 - w) := by
      have hfe' := riemannZeta_one_sub (ne_neg_nat_of_strip hws) (ne_one_of_strip hws)
      rw [sub_sub_cancel] at hfe'
      exact hfe'
    show riemannZeta w = _
    rw [hfe]
    have hw' : riemannZeta (1 - w) = ((1 - w) - rho) ^ m * u (1 - w) := hw
    rw [hw']
    have hneg : 1 - w - rho = -(w - (1 - rho)) := by ring
    rw [hneg, neg_pow]
    ring

private theorem hasZetaZeroMultiplicity_conj {rho : ℂ} {m : ℕ}
    (hm : HasZetaZeroMultiplicity rho m) : HasZetaZeroMultiplicity (conj rho) m := by
  obtain ⟨hm0, u, hu, hu0, hfu⟩ := hm
  have htend : Tendsto (conj : ℂ → ℂ) (nhds (conj rho)) (nhds rho) := by
    simpa using Complex.continuous_conj.tendsto (conj rho)
  refine ⟨hm0, conj ∘ u ∘ conj, ?_, ?_, ?_⟩
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have h1 : ∀ᶠ z in nhds rho, DifferentiableAt ℂ u z :=
      hu.eventually_analyticAt.mono fun z hz => hz.differentiableAt
    exact (htend.eventually h1).mono fun w hw => differentiableAt_conj_conj_iff.mpr hw
  · simp [hu0]
  · filter_upwards [htend.eventually hfu] with w hw
    have hzw : riemannZeta w = conj (riemannZeta (conj w)) := by
      rw [riemannZeta_conj]
      simp
    show riemannZeta w = _
    rw [hzw]
    have hw' : riemannZeta (conj w) = (conj w - rho) ^ m * u (conj w) := hw
    rw [hw']
    simp [map_mul, map_pow, map_sub]

private noncomputable def mult (rho : ℂ) (h : IsNontrivialZero rho) : ℕ :=
  Classical.choose (exists_multiplicity h)

private theorem mult_spec (rho : ℂ) (h : IsNontrivialZero rho) :
    HasZetaZeroMultiplicity rho (mult rho h) :=
  Classical.choose_spec (exists_multiplicity h)

private theorem mult_congr {rho rho' : ℂ} (e : rho = rho') (h : IsNontrivialZero rho)
    (h' : IsNontrivialZero rho') : mult rho h = mult rho' h' := by
  subst e
  rfl

private theorem mult_one_sub (rho : ℂ) (h : IsNontrivialZero rho) :
    mult (1 - rho) (isNontrivialZero_one_sub h) = mult rho h :=
  multiplicity_unique (mult_spec _ _) (hasZetaZeroMultiplicity_one_sub h (mult_spec rho h))

private theorem mult_conj (rho : ℂ) (h : IsNontrivialZero rho) :
    mult (conj rho) (isNontrivialZero_conj h) = mult rho h :=
  multiplicity_unique (mult_spec _ _) (hasZetaZeroMultiplicity_conj (mult_spec rho h))

private def reflS (x : NontrivialZeroSet) : NontrivialZeroSet :=
  ⟨1 - x.1, isNontrivialZero_one_sub x.2⟩

private theorem reflS_involutive : Function.Involutive reflS := by
  intro x
  apply Subtype.ext
  simp [reflS]

private def conjS (x : NontrivialZeroSet) : NontrivialZeroSet :=
  ⟨conj x.1, isNontrivialZero_conj x.2⟩

private theorem conjS_involutive : Function.Involutive conjS := by
  intro x
  apply Subtype.ext
  simp [conjS]

private theorem nonempty_zeroData_of_infinite (hinf : NontrivialZeroSet.Infinite) :
    Nonempty ZeroData := by
  have : Countable NontrivialZeroSet := countable_nontrivialZeroSet.to_subtype
  have : Infinite NontrivialZeroSet := hinf.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable NontrivialZeroSet
  let e : ℕ ≃ NontrivialZeroSet := (Denumerable.eqv NontrivialZeroSet).symm
  let zero : ℕ → ℂ := fun n => (e n).1
  have zero_inj : Function.Injective zero := fun _ _ hab => e.injective (Subtype.ext hab)
  have zero_nt : ∀ n, IsNontrivialZero (zero n) := fun n => (e n).2
  let refl : Equiv.Perm ℕ := (e.trans reflS_involutive.toPerm).trans e.symm
  let cnj : Equiv.Perm ℕ := (e.trans conjS_involutive.toPerm).trans e.symm
  have zero_refl : ∀ n, zero (refl n) = 1 - zero n := fun n => by
    simp [zero, refl, reflS]
  have zero_cnj : ∀ n, zero (cnj n) = conj (zero n) := fun n => by
    simp [zero, cnj, conjS]
  refine ⟨{
    zero := zero
    multiplicity := fun n => mult (zero n) (zero_nt n)
    zero_injective := zero_inj
    zero_isNontrivial := zero_nt
    zero_exhaustive := fun {rho} hrho => ⟨e.symm ⟨rho, hrho⟩, by simp [zero]⟩
    multiplicity_spec := fun n => mult_spec _ _
    reflection := refl
    zero_reflection := zero_refl
    multiplicity_reflection := fun n => by
      rw [mult_congr (zero_refl n) (zero_nt (refl n))
        (isNontrivialZero_one_sub (zero_nt n))]
      exact mult_one_sub _ _
    conjugation := cnj
    zero_conjugation := zero_cnj
    multiplicity_conjugation := fun n => by
      rw [mult_congr (zero_cnj n) (zero_nt (cnj n))
        (isNontrivialZero_conj (zero_nt n))]
      exact mult_conj _ _
    locallyFinite := fun T => by
      refine ((finite_nontrivialZeroSet_spectralRadius_le T).preimage zero_inj.injOn).subset ?_
      intro n hn
      exact ⟨zero_nt n, hn⟩ }⟩

/-!
This characterization does not prove that the nontrivial zero set is infinite,
exhibit a zero, or establish O-6 nonvacuity. It isolates the remaining
nonvacuity question as precisely the open infinitude statement.
-/

/-- `ZeroData` is inhabited exactly when the set of nontrivial zeta zeros is infinite. -/
theorem nonempty_zeroData_iff_infinite :
    Nonempty ZeroData ↔ {rho : ℂ | IsNontrivialZero rho}.Infinite :=
  ⟨fun ⟨Z⟩ => infinite_of_zeroData Z, nonempty_zeroData_of_infinite⟩

-- The theorem has no hypotheses; this checks the empty hypothesis context.
example : True := trivial

-- The carrier quantified by the set-builder on the right is inhabited.
example : Nonempty ℂ := ⟨0⟩

#print axioms nonempty_zeroData_iff_infinite

end D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
