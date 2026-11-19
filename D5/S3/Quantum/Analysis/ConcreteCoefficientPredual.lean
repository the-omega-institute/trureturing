/- GID: D5/S3/Quantum/Analysis/ConcreteCoefficientPredual
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ConcreteCoefficientPredual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete coefficient closure and internal directed normality. -/

import D5.S3.Quantum.Analysis.NormalMomentFamily
import D5.S3.Quantum.Measurements.DirectedPositiveNet
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Concrete coefficient functionals and internal normality -/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ComplexOrder InnerProductSpace
open D5.S3.Quantum.Analysis.NormalFunctionals
open D5.S3.Quantum.Measurements.DirectedPositiveNet

namespace D5.S3.Quantum.Analysis.ConcreteCoefficientPredual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)

/-- The actual restriction of a vector coefficient to the concrete algebra. -/
def coefficient (ξ η : H) : StrongDual ℂ M.toStarSubalgebra :=
  (show M.toStarSubalgebra →ₗ[ℂ] ℂ from
    { toFun := fun a => ⟪ξ, (a : H →L[ℂ] H) η⟫_ℂ
      map_add' := fun a b => by simp [inner_add_right]
      map_smul' := fun c a => by simp [inner_smul_right] }).mkContinuous (‖ξ‖ * ‖η‖) (by
        intro a
        exact (norm_inner_le_norm _ _).trans (by
          calc
            ‖ξ‖ * ‖(a : H →L[ℂ] H) η‖ ≤ ‖ξ‖ * (‖a‖ * ‖η‖) :=
              mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm η) (norm_nonneg ξ)
            _ = (‖ξ‖ * ‖η‖) * ‖a‖ := by ring))

/-- The inherited-dual-norm closed complex span of restricted vector coefficients. -/
def coefficientSpace : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range fun p : H × H => coefficient M p.1 p.2)).topologicalClosure

/-- Left translation by b-star, bounded for the actual dual norm. -/
def leftTranslate {A : Type*} [CStarAlgebra A] (b : A) :
    StrongDual ℂ A →L[ℂ] StrongDual ℂ A :=
  (ContinuousLinearMap.compL ℂ A A ℂ).flip (ContinuousLinearMap.mul ℂ A (star b))

/-- The closed coefficient space is stable under left translation. -/
theorem leftTranslate_mem (b : M.toStarSubalgebra)
    {φ : StrongDual ℂ M.toStarSubalgebra} (hφ : φ ∈ coefficientSpace M) :
    leftTranslate b φ ∈ coefficientSpace M := by
  have hc (ξ η : H) : leftTranslate b (coefficient M ξ η) =
      coefficient M ((b : H →L[ℂ] H) ξ) η := by
    ext a
    change ⟪ξ, (star (b : H →L[ℂ] H)) ((a : H →L[ℂ] H) η)⟫_ℂ = _
    exact ContinuousLinearMap.adjoint_inner_right (b : H →L[ℂ] H) ξ
      ((a : H →L[ℂ] H) η)
  have hspan : Submodule.span ℂ (Set.range fun p : H × H => coefficient M p.1 p.2) ≤
      (coefficientSpace M).comap (leftTranslate b).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    change leftTranslate b (coefficient M ξ η) ∈ coefficientSpace M
    rw [hc]
    exact Submodule.subset_span ⟨(((b : H →L[ℂ] H) ξ), η), rfl⟩ |>
      (Submodule.le_topologicalClosure _)
  exact Submodule.topologicalClosure_minimal _ hspan
    ((Submodule.isClosed_topologicalClosure _).preimage (leftTranslate b).continuous) hφ

section Heredity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Positive domination is inherited by every dual-norm closed complex submodule
stable under left translation. The proof uses the actual GNS completion of phi. -/
theorem positive_mem_of_domination
    (E : Submodule ℂ (StrongDual ℂ A)) (hE : IsClosed (E : Set (StrongDual ℂ A)))
    (hstable : ∀ b : A, ∀ φ ∈ E, leftTranslate b φ ∈ E)
    (φ ψ : StrongDual ℂ A) (hφ : φ ∈ E)
    (hφpos : ∀ a : A, 0 ≤ a → 0 ≤ φ a)
    (hψ : ∀ a : A, 0 ≤ a → 0 ≤ ψ a ∧ ψ a ≤ φ a) : ψ ∈ E := by
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ φ.toLinearMap hφpos
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ψ.toLinearMap (fun a ha => (hψ a ha).1)
  have hbound (a : f.PreGNS) : ‖ψ (f.ofPreGNS a)‖ ≤ Real.sqrt ‖ψ 1‖ * ‖a‖ := by
    have hsq : ‖ψ (star (f.ofPreGNS a) * f.ofPreGNS a)‖ ≤
        ‖φ (star (f.ofPreGNS a) * f.ofPreGNS a)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (hψ _ (star_mul_self_nonneg _)).2 (hψ _ (star_mul_self_nonneg _)).1
    calc
      _ ≤ Real.sqrt ‖ψ 1‖ *
          Real.sqrt ‖ψ (star (f.ofPreGNS a) * f.ofPreGNS a)‖ := by
        have h := PositiveLinearMap.cauchy_schwarz_star_mul g 1 (f.ofPreGNS a)
        change ‖ψ (star (1 : A) * f.ofPreGNS a)‖ ≤
          Real.sqrt ‖ψ (star (1 : A) * 1)‖ *
            Real.sqrt ‖ψ (star (f.ofPreGNS a) * f.ofPreGNS a)‖ at h
        simpa only [star_one, one_mul] using h
      _ ≤ Real.sqrt ‖ψ 1‖ * Real.sqrt ‖φ (star (f.ofPreGNS a) * f.ofPreGNS a)‖ :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
      _ = Real.sqrt ‖ψ 1‖ * ‖a‖ := by rw [f.preGNS_norm_def']; rfl
  let l : f.PreGNS →L[ℂ] ℂ :=
    (ψ.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous (Real.sqrt ‖ψ 1‖) hbound
  let w : f.GNS := (InnerProductSpace.toDual ℂ f.GNS).symm l.fromCompletion
  have hw (a : A) : ⟪w, (f.toPreGNS a : f.GNS)⟫_ℂ = ψ a := by
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hq (a : A) : ‖(f.toPreGNS a : f.GNS)‖ ≤
      ‖a‖ * ‖(f.toPreGNS 1 : f.GNS)‖ := by
    simp only [UniformSpace.Completion.norm_coe]
    have hn : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
      dsimp only [PositiveLinearMap.leftMulMapPreGNS]
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
    simpa using ((f.leftMulMapPreGNS a).le_opNorm (f.toPreGNS 1)).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  change ψ ∈ (E : Set (StrongDual ℂ A))
  rw [← hE.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hdense : w ∈ closure (Set.range ((↑) : f.PreGNS → f.GNS)) :=
    UniformSpace.Completion.denseRange_coe w
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hdense
    (ε / (‖(f.toPreGNS 1 : f.GNS)‖ + 1)) (by positivity)
  let χ := leftTranslate (f.ofPreGNS b) φ
  refine ⟨χ, hstable _ _ hφ, ?_⟩
  have herr : ‖ψ - χ‖ ≤ ‖w - (b : f.GNS)‖ * ‖(f.toPreGNS 1 : f.GNS)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    have hid : (ψ - χ) a = ⟪w - (b : f.GNS), (f.toPreGNS a : f.GNS)⟫_ℂ := by
      rw [inner_sub_left, hw, UniformSpace.Completion.inner_coe]
      rfl
    rw [hid]
    calc
      _ ≤ ‖w - (b : f.GNS)‖ * ‖(f.toPreGNS a : f.GNS)‖ := norm_inner_le_norm _ _
      _ ≤ ‖w - (b : f.GNS)‖ * (‖a‖ * ‖(f.toPreGNS 1 : f.GNS)‖) := by
        gcongr; exact hq a
      _ = (‖w - (b : f.GNS)‖ * ‖(f.toPreGNS 1 : f.GNS)‖) * ‖a‖ := by ring
  rw [dist_eq_norm] at hb ⊢
  have hsmall := (lt_div_iff₀ (by positivity : 0 < ‖(f.toPreGNS 1 : f.GNS)‖ + 1)).mp hb
  exact herr.trans_lt (by nlinarith [norm_nonneg (w - (b : f.GNS))])

end Heredity

/-- Positive heredity for the actual closed coefficient space. -/
theorem coefficientSpace_hereditary (φ ψ : StrongDual ℂ M.toStarSubalgebra)
    (hφ : φ ∈ coefficientSpace M) (hφpos : ∀ a, 0 ≤ a → 0 ≤ φ a)
    (hψ : ∀ a, 0 ≤ a → 0 ≤ ψ a ∧ ψ a ≤ φ a) : ψ ∈ coefficientSpace M :=
  positive_mem_of_domination (coefficientSpace M) (Submodule.isClosed_topologicalClosure _)
    (fun b φ hφ => leftTranslate_mem M b hφ) φ ψ hφ hφpos hψ


/-- Every continuous coordinate of a positive map with unit in E belongs to E. -/
private theorem continuous_mem_coefficientSpace
    (J : C(NormalMomentFamily.Interval, ℂ) →ₗ[ℂ] StrongDual ℂ M.toStarSubalgebra)
    (hpos : ∀ g, (∀ t, 0 ≤ g t) → ∀ a, 0 ≤ a → 0 ≤ J g a)
    (hu : J 1 ∈ coefficientSpace M) (g : C(NormalMomentFamily.Interval, ℂ)) :
    J g ∈ coefficientSpace M := by
  let E := coefficientSpace M
  have hpositive (f : C(NormalMomentFamily.Interval, ℂ)) (hf : ∀ x, 0 ≤ f x) :
      J f ∈ E := by
    apply coefficientSpace_hereditary M ((‖f‖ : ℂ) • J 1) (J f) (E.smul_mem _ hu)
    · intro a ha
      exact mul_nonneg (by exact_mod_cast norm_nonneg f) (hpos 1 (by simp) a ha)
    · intro a ha
      refine ⟨hpos f hf a ha, ?_⟩
      have hle (x : NormalMomentFamily.Interval) : f x ≤ (‖f‖ : ℂ) := by
        apply Complex.le_def.mpr
        exact ⟨(Complex.re_le_norm _).trans (f.norm_coe_le_norm x),
          (Complex.nonneg_iff.mp (hf x)).2.symm⟩
      have h := hpos ((‖f‖ : ℂ) • 1 - f)
        (fun x => by simpa using sub_nonneg.mpr (hle x)) a ha
      apply sub_nonneg.mp
      simpa only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] using h
  let lift : C(NormalMomentFamily.Interval, ℝ) → C(NormalMomentFamily.Interval, ℂ) :=
    fun f => ⟨fun x => (f x : ℂ), by fun_prop⟩
  let u : C(NormalMomentFamily.Interval, ℝ) := ⟨fun x => max (g x).re 0, by fun_prop⟩
  let v : C(NormalMomentFamily.Interval, ℝ) := ⟨fun x => max (-(g x).re) 0, by fun_prop⟩
  let s : C(NormalMomentFamily.Interval, ℝ) := ⟨fun x => max (g x).im 0, by fun_prop⟩
  let t : C(NormalMomentFamily.Interval, ℝ) := ⟨fun x => max (-(g x).im) 0, by fun_prop⟩
  have he : lift u - lift v + Complex.I • (lift s - lift t) = g := by
    ext x
    apply Complex.ext <;>
      simp [lift, u, v, s, t, max_zero_sub_max_neg_zero_eq_self,
        Complex.mul_re, Complex.mul_im]
  have hreal (w : C(NormalMomentFamily.Interval, ℝ)) (hw : ∀ x, 0 ≤ w x) : J (lift w) ∈ E :=
    hpositive _ (fun x => by change (0 : ℂ) ≤ (w x : ℂ); exact_mod_cast hw x)
  rw [← he, map_add, map_sub, map_smul, map_sub]
  exact E.add_mem
    (E.sub_mem (hreal u (fun _ => le_max_right _ _)) (hreal v (fun _ => le_max_right _ _)))
    (E.smul_mem _
      (E.sub_mem (hreal s (fun _ => le_max_right _ _)) (hreal t (fun _ => le_max_right _ _))))

/-- Every whole-L1 value of the realized posterior map is in E. This applies to
any actual Gamma agreeing with F; it does not assume range membership. -/
theorem posterior_L1_range {ρ σ : StrongDual ℂ M.toStarSubalgebra}
    (hu : ρ + σ ∈ coefficientSpace M) (F : NormalMomentFamily.Family ρ σ)
    (Γ : (NormalMomentFamily.Interval →₁[NormalMomentFamily.scalarMeasure F] ℂ) →L[ℂ]
      StrongDual ℂ M.toStarSubalgebra)
    (hagree : ∀ g : C(NormalMomentFamily.Interval, ℂ),
      Γ (ContinuousMap.toLp 1 (NormalMomentFamily.scalarMeasure F) ℂ g) =
        NormalMomentFamily.linearMap F g) :
    ∀ h, Γ h ∈ coefficientSpace M := by
  have hJE : ∀ g, NormalMomentFamily.linearMap F g ∈ coefficientSpace M :=
    continuous_mem_coefficientSpace M (NormalMomentFamily.linearMap F) F.property.2.2.1
      (by rwa [NormalMomentFamily.unit_value])
  let e := (ContinuousMap.toLp 1 (NormalMomentFamily.scalarMeasure F) ℂ (E := ℂ)).toLinearMap
  have hd : DenseRange e :=
    ContinuousMap.toLp_denseRange ℂ (NormalMomentFamily.scalarMeasure F) ℂ (by simp)
  intro h
  refine hd.induction_on h ((Submodule.isClosed_topologicalClosure _).preimage Γ.continuous) ?_
  intro g
  change Γ (ContinuousMap.toLp 1 (NormalMomentFamily.scalarMeasure F) ℂ g) ∈ coefficientSpace M
  rw [hagree]
  exact hJE g

/-- A least upper bound internal to M is the strong limit of its directed positive set.
The ambient least upper bound is constructed from an upper bound, not assumed. -/
theorem internal_lub_strong (s : Set M.toStarSubalgebra) (a : M.toStarSubalgebra)
    (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ x ∈ s, 0 ≤ x) (ha : IsLUB s a) :
    letI : Nonempty s := hs.to_subtype
    letI : IsDirectedOrder s := ⟨fun i j => by
      obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
      exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
    ∀ v : H, Tendsto (fun x : s => (x.val : H →L[ℂ] H) v) atTop
      (𝓝 ((a : H →L[ℂ] H) v)) := by
  classical
  letI : Nonempty s := hs.to_subtype
  letI : IsDirectedOrder s := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  let X : s → H →L[ℂ] H := fun x => x.val.val
  obtain ⟨S, hS, _, ht⟩ := exists_lub_strong_of_bdd X a.val
    (fun x => hp x.val x.property) (fun i j hij => hij)
    (fun x => ha.1 x.property)
  have hmem : S ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hb
    ext v
    have he (j : s) : b (X j v) = X j (b v) := by
      exact congrArg (fun T : H →L[ℂ] H => T v)
        ((VonNeumannAlgebra.mem_commutant_iff.mp hb) j.val.val j.val.property).symm
    have hleft := b.continuous.continuousAt.tendsto.comp (ht v)
    have hright := ht (b v)
    simp only [Function.comp_def, he] at hleft
    exact tendsto_nhds_unique hleft hright
  have heq : S = (a : H →L[ℂ] H) := by
    apply le_antisymm
    · apply hS.2
      rintro _ ⟨j, rfl⟩
      exact ha.1 j.property
    · change (a : H →L[ℂ] H) ≤ (⟨S, hmem⟩ : M.toStarSubalgebra)
      apply ha.2
      intro x hx
      exact hS.1 ⟨⟨x, hx⟩, rfl⟩
  intro v
  simpa only [heq] using ht v

/-- Restricted vector coefficients preserve all M-internal positive directed suprema. -/
theorem coefficient_order_normal (ξ η : H) : IsOrderNormal (coefficient M ξ η) := by
  intro s a hs hd hp ha ε hε
  letI : Nonempty s := hs.to_subtype
  letI : IsDirectedOrder s := ⟨fun i j => by
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
  have ht := internal_lub_strong M s a hs hd hp ha η
  have hz : Tendsto (fun x : s => ‖coefficient M ξ η (a - x.val)‖) atTop (𝓝 0) := by
    have h : Tendsto (fun x : s => ⟪ξ, a.val η - x.val.val η⟫_ℂ) atTop
        (𝓝 (0 : ℂ)) := by
      simpa using (tendsto_const_nhds (x := ξ)).inner (𝕜 := ℂ)
        ((tendsto_const_nhds (x := a.val η)).sub ht)
    simpa [coefficient] using h.norm
  obtain ⟨b, hb⟩ := eventually_atTop.mp ((tendsto_order.mp hz).2 ε hε)
  exact ⟨b.val, b.property, fun x hx hbx => hb ⟨x, hx⟩ hbx⟩

/-- The entire norm-closed coefficient space is intrinsically order-normal. -/
theorem coefficientSpace_le_normalDual : coefficientSpace M ≤ normalDual := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro φ ⟨⟨ξ, η⟩, rfl⟩
    exact coefficient_order_normal M ξ η
  · exact isClosed_setOf_isOrderNormal

#print axioms positive_mem_of_domination
#print axioms leftTranslate_mem
#print axioms coefficientSpace_hereditary
#print axioms posterior_L1_range
#print axioms internal_lub_strong
#print axioms coefficient_order_normal
#print axioms coefficientSpace_le_normalDual

end D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
