/- GID: D5/S3/Quantum/Measurement/BoundedAdaptiveLowInstrumentSpan
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/BoundedAdaptiveLowInstrumentSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual event effects with bounded forward calls satisfy the low-sandwich recurrence. -/

import D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
  NonUnitalContinuousFunctionalCalculus

namespace D5.S3.Quantum.Measurement.BoundedAdaptiveLowInstrumentSpan

open AdaptiveLowInstrumentSpan

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

variable {a h : Type*} [Fintype a] [DecidableEq a]
  [Fintype h] [DecidableEq h]

/-- The largest number of forward ticks in a recorded branch. Instruments are free;
their hidden Kraus indices neither select continuations nor contribute to the maximum. -/
def worstBranchCalls : Event a → ℕ
  | .stop _ => 0
  | .tick next => 1 + worstBranchCalls next
  | .observe _I next => Finset.univ.sup (fun y => worstBranchCalls (next y))

/-- The complex span of actual event effects whose worst recorded branch respects
the budget. The joint matrix acts by the existing Heisenberg recursion. -/
def boundedEffectSpan (W : CStarMatrix (a × h) (a × h) ℂ) (N : ℕ) :
    Submodule ℂ (CStarMatrix (a × h) (a × h) ℂ) :=
  Submodule.span ℂ {X | ∃ e : Event a,
    worstBranchCalls e ≤ N ∧ X = effect (tensorLow h) W e}

/-- One more forward call adds precisely the low sandwiches of pulled-back
bounded effects. This algebraic identity requires no unitarity assumption. -/
theorem actual_bounded_effect_span_recurrence [Nonempty a] [Nonempty h]
    (W : CStarMatrix (a × h) (a × h) ℂ) (N : ℕ) :
    let low := tensorLow (a := a) h
    let S := boundedEffectSpan W
    S (N + 1) = Submodule.span ℂ
      ((S N : Set (CStarMatrix (a × h) (a × h) ℂ)) ∪
        {Y | ∃ K : CStarMatrix a a ℂ,
          ∃ X : CStarMatrix (a × h) (a × h) ℂ,
            X ∈ S N ∧ Y = star (low K) * (star W * X * W) * low K}) := by
  classical
  let low := tensorLow (a := a) h
  let S := boundedEffectSpan W
  let R := Submodule.span ℂ
    ((S N : Set (CStarMatrix (a × h) (a × h) ℂ)) ∪
      {Y | ∃ K : CStarMatrix a a ℂ,
        ∃ X : CStarMatrix (a × h) (a × h) ℂ,
          X ∈ S N ∧ Y = star (low K) * (star W * X * W) * low K})
  change S (N + 1) = R
  have generator (n : ℕ) (e : Event a) (he : worstBranchCalls e ≤ n) :
      effect low W e ∈ S n := Submodule.subset_span ⟨e, he, rfl⟩
  have actualFilter (K : CStarMatrix a a ℂ) (e : Event a) :
      ∃ (f : Event a) (c : ℂ), c ≠ 0 ∧
        worstBranchCalls f = worstBranchCalls e ∧
        effect low W f = c • (star (low K) * effect low W e * low K) := by
    let : NonUnitalContinuousFunctionalCalculus ℂ (CStarMatrix a a ℂ) IsStarNormal :=
      (IsStarNormal.instNonUnitalContinuousFunctionalCalculus
        (A := CStarMatrix a a ℂ)).toNonUnitalContinuousFunctionalCalculus
    let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix a a ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    let : NonnegSpectrumClass ℝ (CStarMatrix a a ℂ) :=
      CStarAlgebra.instNonnegSpectrumClass'
    let eps : ℂ := ((‖K‖ + 1)⁻¹ : ℝ)
    have hepspos : 0 < (‖K‖ + 1)⁻¹ := inv_pos.mpr (by positivity)
    have heps : eps ≠ 0 := by
      dsimp [eps]
      exact_mod_cast (ne_of_gt hepspos)
    let Z := eps • K
    have hnorm : ‖Z‖ ≤ 1 := by
      rw [show ‖Z‖ = (‖K‖ + 1)⁻¹ * ‖K‖ by
        simp only [Z, norm_smul, eps, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hepspos]]
      rw [inv_mul_le_iff₀ (by positivity : 0 < ‖K‖ + 1)]
      linarith
    have hdefect : 0 ≤ (1 : CStarMatrix a a ℂ) - star Z * Z := by
      apply sub_nonneg.mpr
      apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star Z * Z)
        (star_mul_self_nonneg Z)).mp
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg Z]
    let F := CFC.sqrt ((1 : CStarMatrix a a ℂ) - star Z * Z)
    have hF : star F * F = (1 : CStarMatrix a a ℂ) - star Z * Z := by
      dsimp [F]
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self _ hdefect]
    let I : LowInstrument a :=
      { outcomes := 2
        multiplicity := 1
        kraus := fun y _ => if y = 0 then Z else F
        complete := by
          simp only [Fin.sum_univ_two, Fin.sum_univ_one]
          change star Z * Z + star F * F = 1
          rw [hF]
          abel }
    let f := Event.observe I (fun y => if y = 0 then e else .stop false)
    refine ⟨f, star eps * eps, mul_ne_zero (star_ne_zero.mpr heps) heps, ?_, ?_⟩
    · change (Finset.univ.sup (fun y : Fin 2 =>
          worstBranchCalls (if y = 0 then e else .stop false))) = worstBranchCalls e
      apply le_antisymm
      · apply Finset.sup_le
        intro y _
        by_cases hy : y = 0 <;> simp [hy, worstBranchCalls]
      · simpa using (Finset.le_sup (f := fun y : Fin 2 =>
          worstBranchCalls (if y = 0 then e else .stop false)) (Finset.mem_univ 0))
    · simp [f, effect, I, Z, map_smul, star_smul, smul_smul,
        Fin.sum_univ_two, mul_comm]
  have filterBound (n : ℕ) (K : CStarMatrix a a ℂ) :
      ∀ X ∈ S n, star (low K) * X * low K ∈ S n := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨e, he, rfl⟩ := hX
        obtain ⟨f, c, hc, hcost, heffect⟩ := actualFilter K e
        have hf := generator n f (hcost ▸ he)
        rw [heffect] at hf
        simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using
          (S n).smul_mem c⁻¹ hf
    | zero => simp
    | add X Y _ _ hX hY => simpa [mul_add, add_mul] using (S n).add_mem hX hY
    | smul z X _ hX =>
        simpa only [mul_smul_comm, smul_mul_assoc] using (S n).smul_mem z hX
  have smallR (X : CStarMatrix (a × h) (a × h) ℂ) (hX : X ∈ S N) : X ∈ R :=
    Submodule.subset_span (Or.inl hX)
  have filterR (K : CStarMatrix a a ℂ) :
      ∀ X ∈ R, star (low K) * X * low K ∈ R := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        rcases hX with hX | hX
        · exact smallR _ (filterBound N K X hX)
        · obtain ⟨L, E, hE, rfl⟩ := hX
          apply Submodule.subset_span
          exact Or.inr ⟨L * K, E, hE, by simp only [map_mul, star_mul, mul_assoc]⟩
    | zero => simp
    | add X Y _ _ hX hY => simpa [mul_add, add_mul] using R.add_mem hX hY
    | smul z X _ hX =>
        simpa only [mul_smul_comm, smul_mul_assoc] using R.smul_mem z hX
  have eventR (e : Event a) : worstBranchCalls e ≤ N + 1 → effect low W e ∈ R := by
    induction e with
    | stop accepted =>
        intro _
        exact smallR _ (generator N (.stop accepted) (Nat.zero_le N))
    | tick next ih =>
        intro hc
        have hn : worstBranchCalls next ≤ N := by
          simp only [worstBranchCalls] at hc
          omega
        have h : star (low 1) * (star W * effect low W next * W) * low 1 ∈ R :=
          Submodule.subset_span
          (Or.inr ⟨(1 : CStarMatrix a a ℂ), effect low W next,
            generator N next hn, rfl⟩)
        simpa only [effect, map_one, star_one, one_mul, mul_one] using h
    | observe I next ih =>
        intro hc
        change ∑ y, ∑ r, star (low (I.kraus y r)) *
          effect low W (next y) * low (I.kraus y r) ∈ R
        apply R.sum_mem
        intro y _
        apply R.sum_mem
        intro r _
        apply filterR
        apply ih y
        exact (Finset.le_sup (Finset.mem_univ y)).trans hc
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ⟨e, he, rfl⟩
    exact eventR e he
  · have inclusion : S N ≤ S (N + 1) := by
      apply Submodule.span_le.mpr
      rintro X ⟨e, he, rfl⟩
      exact generator (N + 1) e (he.trans (Nat.le_succ N))
    have tickBound : ∀ X ∈ S N, star W * X * W ∈ S (N + 1) := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem X hX =>
          obtain ⟨e, he, rfl⟩ := hX
          apply generator (N + 1) (.tick e)
          simp only [worstBranchCalls]
          omega
      | zero => simp
      | add X Y _ _ hX hY =>
          simpa [mul_add, add_mul] using (S (N + 1)).add_mem hX hY
      | smul z X _ hX =>
          simpa only [mul_smul_comm, smul_mul_assoc] using (S (N + 1)).smul_mem z hX
    apply Submodule.span_le.mpr
    intro X hX
    rcases hX with hX | hX
    · exact inclusion hX
    · obtain ⟨K, E, hE, rfl⟩ := hX
      exact filterBound (N + 1) K _ (tickBound E hE)

#print axioms actual_bounded_effect_span_recurrence

end D5.S3.Quantum.Measurement.BoundedAdaptiveLowInstrumentSpan
