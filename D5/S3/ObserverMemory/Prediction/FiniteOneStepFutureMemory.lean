/- GID: D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-laws one-step future-memory closure, quotient lower bound, and attainment. -/
/- The complete finite-state, all-laws one-step future-memory theorem. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Prediction.FiniteOneStepFutureMemory

abbrev StateFn (Ω : Type*) [Fintype Ω] := EuclideanSpace ℝ Ω

def constantFn {Ω : Type*} [Fintype Ω] (c : ℝ) : StateFn Ω :=
  WithLp.toLp 2 (fun _ => c)

def IsProbabilityLaw {Ω : Type*} [Fintype Ω] (p : StateFn Ω) : Prop :=
  (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

def expectation {Ω : Type*} [Fintype Ω] (p f : StateFn Ω) : ℝ :=
  ∑ ω, p ω * f ω

def pullback {Ω A : Type*} [Fintype Ω]
    (T : A → Ω → Ω) (a : A) (f : StateFn Ω) : StateFn Ω :=
  WithLp.toLp 2 (fun ω => f.ofLp (T a ω))

def futureGenerators {Ω A : Type*} [Fintype Ω]
    (V : Submodule ℝ (StateFn Ω)) (T : A → Ω → Ω) : Set (StateFn Ω) :=
  {g | ∃ a f, f ∈ V ∧ g = pullback T a f}

def oneStepClosure {Ω A : Type*} [Fintype Ω]
    (V : Submodule ℝ (StateFn Ω)) (T : A → Ω → Ω) :
    Submodule ℝ (StateFn Ω) :=
  V ⊔ Submodule.span ℝ (futureGenerators V T)

def oneStepDetermines {Ω A : Type*} [Fintype Ω]
    (V W : Submodule ℝ (StateFn Ω)) (T : A → Ω → Ω) : Prop :=
  V ≤ W ∧
    ∀ p q, IsProbabilityLaw p → IsProbabilityLaw q →
      (∀ g, g ∈ W → expectation p g = expectation q g) →
      ∀ a f, f ∈ V →
        expectation p (pullback T a f) = expectation q (pullback T a f)

def oneStepFutureClosed {Ω A : Type*} [Fintype Ω]
    (V W : Submodule ℝ (StateFn Ω)) (T : A → Ω → Ω) : Prop :=
  V ≤ W ∧ ∀ a f, f ∈ V → pullback T a f ∈ W

def quotientDimension {Ω : Type*} [Fintype Ω]
    (V W : Submodule ℝ (StateFn Ω)) (hVW : V ≤ W) : ℕ :=
  Module.finrank ℝ (W ⧸ V.comap W.subtype)

private lemma separating_laws {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (W : Submodule ℝ (StateFn Ω))
    (constantsInW : ∀ c, constantFn c ∈ W)
    (target : StateFn Ω) (targetNotInW : target ∉ W) :
    ∃ p q, IsProbabilityLaw p ∧ IsProbabilityLaw q ∧
      (∀ g, g ∈ W → expectation p g = expectation q g) ∧
      expectation p target ≠ expectation q target := by
  classical
  have existsResidual : ∃ r : StateFn Ω, r ∈ Wᗮ ∧ inner ℝ r target ≠ 0 := by
    by_contra h
    push_neg at h
    have targetOrthogonal : target ∈ (Wᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro r hr
      have hzero := h r hr
      simpa [real_inner_comm] using hzero
    rw [Submodule.orthogonal_orthogonal] at targetOrthogonal
    exact targetNotInW targetOrthogonal
  obtain ⟨r, hrW, hrTarget⟩ := existsResidual
  have hsumR : ∑ ω, r ω = 0 := by
    have hinner := (Submodule.mem_orthogonal' W r).mp hrW
      (constantFn 1) (constantsInW 1)
    simpa [constantFn, PiLp.inner_apply] using hinner
  let s : ℝ := ∑ ω, |r ω|
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hri (ω : Ω) : |r ω| ≤ s := by
    dsimp [s]
    exact Finset.single_le_sum (fun i hi => abs_nonneg (r i)) (Finset.mem_univ ω)
  have hnNat : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
  have hn : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hnNat
  let δ : ℝ := 1 / (2 * (Fintype.card Ω : ℝ) * (s + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδs : δ * s ≤ 1 / (2 * (Fintype.card Ω : ℝ)) := by
    dsimp [δ]
    have hden : 0 < 2 * (Fintype.card Ω : ℝ) * (s + 1) := by positivity
    have hfrac : s / (2 * (Fintype.card Ω : ℝ) * (s + 1)) ≤
        1 / (2 * (Fintype.card Ω : ℝ)) := by
      apply (div_le_iff₀ hden).2
      calc
        s ≤ s + 1 := by linarith
        _ = (1 / (2 * (Fintype.card Ω : ℝ))) *
            (2 * (Fintype.card Ω : ℝ) * (s + 1)) := by
          field_simp
    convert hfrac using 1 <;> ring
  have hriLower (ω : Ω) : -s ≤ r ω := by
    have ha := neg_abs_le (r ω)
    linarith [hri ω]
  have hriUpper (ω : Ω) : r ω ≤ s := by
    have ha := le_abs_self (r ω)
    linarith [hri ω]
  let p : StateFn Ω := WithLp.toLp 2 (fun ω =>
    1 / (Fintype.card Ω : ℝ) + δ * r ω)
  let q : StateFn Ω := WithLp.toLp 2 (fun ω =>
    1 / (Fintype.card Ω : ℝ) - δ * r ω)
  have hpNonneg : ∀ ω, 0 ≤ p ω := by
    intro ω
    have hmul := mul_le_mul_of_nonneg_left (hriLower ω) (le_of_lt hδ)
    have hhalf : 0 ≤ 1 / (2 * (Fintype.card Ω : ℝ)) := by positivity
    have hhalfEq : 1 / (2 * (Fintype.card Ω : ℝ)) =
        (1 / (Fintype.card Ω : ℝ)) / 2 := by field_simp
    dsimp [p]
    nlinarith [hδs, hhalfEq]
  have hqNonneg : ∀ ω, 0 ≤ q ω := by
    intro ω
    have hmul := mul_le_mul_of_nonneg_left (hriUpper ω) (le_of_lt hδ)
    have hhalf : 0 ≤ 1 / (2 * (Fintype.card Ω : ℝ)) := by positivity
    have hhalfEq : 1 / (2 * (Fintype.card Ω : ℝ)) =
        (1 / (Fintype.card Ω : ℝ)) / 2 := by field_simp
    dsimp [q]
    nlinarith [hδs, hhalfEq]
  have hsumConst : ∑ (_ω : Ω), (1 / (Fintype.card Ω : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hpLaw : IsProbabilityLaw p := by
    refine ⟨hpNonneg, ?_⟩
    dsimp [p]
    rw [Finset.sum_add_distrib, hsumConst]
    rw [← Finset.mul_sum, hsumR]
    ring
  have hqLaw : IsProbabilityLaw q := by
    refine ⟨hqNonneg, ?_⟩
    dsimp [q]
    rw [Finset.sum_sub_distrib, hsumConst]
    rw [← Finset.mul_sum, hsumR]
    ring
  have hWEqual : ∀ g, g ∈ W → expectation p g = expectation q g := by
    intro g hg
    have hinner := (Submodule.mem_orthogonal' W r).mp hrW g hg
    have hsum : ∑ ω, r ω * g ω = 0 := by
      simpa [PiLp.inner_apply, mul_comm] using hinner
    apply sub_eq_zero.mp
    calc
      expectation p g - expectation q g =
          2 * δ * (∑ ω, r ω * g ω) := by
            dsimp [expectation, p, q]
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            ring
      _ = 0 := by rw [hsum]; ring
  have hTargetDiff : expectation p target - expectation q target =
      2 * δ * inner ℝ r target := by
    have hsum : ∑ ω, r ω * target ω = inner ℝ r target := by
      rw [PiLp.inner_apply]
      simp [mul_comm]
    calc
      expectation p target - expectation q target =
          2 * δ * (∑ ω, r ω * target ω) := by
            dsimp [expectation, p, q]
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            ring
      _ = 2 * δ * inner ℝ r target := by rw [hsum]
  refine ⟨p, q, hpLaw, hqLaw, hWEqual, ?_⟩
  apply sub_ne_zero.mp
  rw [hTargetDiff]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hδ)) hrTarget

/-- All genuine finite-state laws determine every one-step target exactly iff the
same observation space contains the current constants and every deterministic
pullback of every current observable. The same closure supplies the quotient
lower bound and is itself feasible with equality. -/
theorem finite_one_step_future_memory
    {Ω A : Type*} [Fintype Ω]
    (V W : Submodule ℝ (StateFn Ω))
    (T : A → Ω → Ω)
    (constantsInV : ∀ c, constantFn c ∈ V) :
    (oneStepDetermines V W T ↔ oneStepFutureClosed V W T) ∧
      (oneStepFutureClosed V W T ↔
        V ≤ W ∧ oneStepClosure V T ≤ W) ∧
      (∀ hW : oneStepFutureClosed V W T,
        quotientDimension V W hW.1 ≥
          quotientDimension V (oneStepClosure V T) (by
            intro f hf
            exact (show V ≤ oneStepClosure V T from le_sup_left) hf)) ∧
      oneStepFutureClosed V (oneStepClosure V T) T ∧
      quotientDimension V (oneStepClosure V T) (by
        intro f hf
        exact (show V ≤ oneStepClosure V T from le_sup_left) hf) =
        quotientDimension V (oneStepClosure V T) (by
          intro f hf
          exact (show V ≤ oneStepClosure V T from le_sup_left) hf) := by
  classical
  have targetMembership :
      ∀ {U : Submodule ℝ (StateFn Ω)},
        oneStepDetermines V U T →
        ∀ a f, f ∈ V → pullback T a f ∈ U := by
    intro U hDet a f hf
    by_cases hΩ : Nonempty Ω
    · letI := hΩ
      by_contra hnot
      obtain ⟨p, q, hp, hq, hW, htarget⟩ :=
        separating_laws U (fun c => hDet.1 (constantsInV c))
          (pullback T a f) hnot
      exact htarget (hDet.2 p q hp hq hW a f hf)
    · letI : IsEmpty Ω := not_nonempty_iff.mp hΩ
      have heq : pullback T a f = constantFn 0 := by
        exact Subsingleton.elim _ _
      exact heq ▸ hDet.1 (constantsInV 0)
  have closureCharacterization :
      oneStepFutureClosed V W T ↔ V ≤ W ∧ oneStepClosure V T ≤ W := by
    constructor
    · rintro ⟨hVW, hfuture⟩
      refine ⟨hVW, sup_le hVW ?_⟩
      rw [Submodule.span_le]
      intro g hg
      change ∃ a f, f ∈ V ∧ g = pullback T a f at hg
      rcases hg with ⟨a, f, hf, rfl⟩
      exact hfuture a f hf
    · rintro ⟨hVW, hC⟩
      refine ⟨hVW, ?_⟩
      intro a f hf
      apply hC
      exact (show Submodule.span ℝ (futureGenerators V T) ≤ oneStepClosure V T from le_sup_right)
        (Submodule.subset_span (show pullback T a f ∈ futureGenerators V T from
          ⟨a, f, hf, rfl⟩))
  have determinationIff : oneStepDetermines V W T ↔ oneStepFutureClosed V W T := by
    constructor
    · intro hDet
      exact ⟨hDet.1, targetMembership hDet⟩
    · rintro ⟨hVW, hfuture⟩
      refine ⟨hVW, ?_⟩
      intro p q hp hq heq a f hf
      exact heq (pullback T a f) (hfuture a f hf)
  refine ⟨determinationIff, closureCharacterization, ?_, ?_, rfl⟩
  · intro hW
    have hC := closureCharacterization.mp hW
    have hVC : V ≤ oneStepClosure V T := by
      exact (show V ≤ V ⊔ Submodule.span ℝ (futureGenerators V T) from le_sup_left)
    have hfinrank : Module.finrank ℝ (oneStepClosure V T) ≤
        Module.finrank ℝ W := Submodule.finrank_mono hC.2
    have hqW : quotientDimension V W hW.1 =
        Module.finrank ℝ W - Module.finrank ℝ V := by
      dsimp [quotientDimension]
      rw [Submodule.finrank_quotient]
      rw [(Submodule.comapSubtypeEquivOfLe hW.1).finrank_eq]
    have hqC : quotientDimension V (oneStepClosure V T) hVC =
        Module.finrank ℝ (oneStepClosure V T) - Module.finrank ℝ V := by
      dsimp [quotientDimension]
      rw [Submodule.finrank_quotient]
      rw [(Submodule.comapSubtypeEquivOfLe hVC).finrank_eq]
    rw [hqW, hqC]
    omega
  · refine ⟨?_, ?_⟩
    · exact (show V ≤ V ⊔ Submodule.span ℝ (futureGenerators V T) from le_sup_left)
    · intro a f hf
      exact (show Submodule.span ℝ (futureGenerators V T) ≤ oneStepClosure V T from le_sup_right)
        (Submodule.subset_span (show pullback T a f ∈ futureGenerators V T from
          ⟨a, f, hf, rfl⟩))

#print axioms finite_one_step_future_memory

end D5.S3.ObserverMemory.Prediction.FiniteOneStepFutureMemory
