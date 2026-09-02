/- GID: D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite
   mirror-E: none(waiver:structural-nonvacuity-characterization-only)
   anchors: []
   digest: ZeroData is inhabited exactly when the nontrivial zeta-zero set is infinite. -/

import D5.S3.Weil.ZeroSum
import D5.S3.Weil.ZetaSeam.ZetaReflect
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

private theorem hasZetaZeroMultiplicity_iff_analyticOrderAt_eq {rho : ℂ}
    (h : IsNontrivialZero rho) {m : ℕ} :
    HasZetaZeroMultiplicity rho m ↔ analyticOrderAt riemannZeta rho = m := by
  have hrho1 : rho ≠ 1 := ne_one_of_isNontrivialZero h
  have han : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrho1
  constructor
  · rintro ⟨_, u, hu, hu0, hfu⟩
    apply han.analyticOrderAt_eq_natCast.mpr
    refine ⟨u, hu, hu0, ?_⟩
    simpa [Filter.EventuallyEq, classicalZeta, smul_eq_mul] using hfu
  · intro horder
    have hm0 : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm
      subst m
      have hzeta_ne : riemannZeta rho ≠ 0 :=
        han.analyticOrderAt_eq_zero.mp (by simpa using horder)
      exact hzeta_ne (by simpa [classicalZeta] using h.1)
    obtain ⟨u, hu, hu0, hfu⟩ := han.analyticOrderAt_eq_natCast.mp horder
    refine ⟨hm0, u, hu, hu0, ?_⟩
    simpa [Filter.EventuallyEq, classicalZeta, smul_eq_mul] using hfu

private theorem hasZetaZeroMultiplicity_one_sub {rho : ℂ} {m : ℕ}
    (h : IsNontrivialZero rho) (hm : HasZetaZeroMultiplicity rho m) :
    HasZetaZeroMultiplicity (1 - rho) m := by
  apply (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq
    (isNontrivialZero_one_sub h)).mpr
  rw [Zeta23.analyticOrderAt_zeta_one_sub h.2.1 h.2.2]
  exact (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq h).mp hm

private theorem hasZetaZeroMultiplicity_conj {rho : ℂ} {m : ℕ}
    (h : IsNontrivialZero rho) (hm : HasZetaZeroMultiplicity rho m) :
    HasZetaZeroMultiplicity (conj rho) m := by
  apply (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq
    (isNontrivialZero_conj h)).mpr
  rw [Zeta23.analyticOrderAt_zeta_conj (ne_one_of_isNontrivialZero h)]
  exact (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq h).mp hm

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
  multiplicity_unique (mult_spec _ _) (hasZetaZeroMultiplicity_conj h (mult_spec rho h))

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
