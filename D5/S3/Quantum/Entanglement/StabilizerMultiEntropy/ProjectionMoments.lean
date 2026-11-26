/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interpolate every scalar function of a finite-field column span from physical density moments of its quotient codes. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset LinearMap Submodule
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments

section Poset

variable {P : Type*} [Fintype P] [PartialOrder P]

noncomputable def upperZeta (a : P → ℝ) (U : P) : ℝ := by
  classical
  exact ∑ L : P, if U ≤ L then a L else 0

private theorem upperZeta_zero (a : P → ℝ) (h : ∀ U, upperZeta a U=0) : a=0 := by
  classical
  funext U
  induction U using (Finite.wellFounded_of_trans_of_irrefl (fun x y : P => y<x)).induction with
  | h U ih =>
    change a U = 0
    have he : upperZeta a U = a U := by
      unfold upperZeta
      rw [Finset.sum_eq_single U]
      · simp
      · intro L _ hLU
        by_cases hUL : U ≤ L
        · rw [ite_eq_left hUL, ih L (lt_of_le_of_ne hUL hLU.symm)]; rfl
        · simp [hUL]
      · simp
    rw [← he, h]

noncomputable def semanticKernel (w : P → ℝ) (W L : P) : ℝ := by
  classical
  exact ∑ U : P, if U ≤ W ∧ U ≤ L then w U else 0

noncomputable def kernelOperator (w : P → ℝ) : (P → ℝ) →ₗ[ℝ] P → ℝ where
  toFun a W := ∑ L : P, semanticKernel w W L * a L
  map_add' a b := by
    funext W
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext W
    simp [Finset.mul_sum, mul_left_comm]

private theorem kernel_quadratic (w a : P → ℝ) :
    (∑ W : P, a W * kernelOperator w a W) =
      ∑ U : P, w U * (upperZeta a U)^2 := by
  classical
  change (∑ W : P, a W * ∑ L : P, semanticKernel w W L * a L) = _
  simp only [semanticKernel, mul_sum, sum_mul]
  conv_lhs =>
    arg 2
    intro W
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  unfold upperZeta
  rw [pow_two, sum_mul, mul_sum]
  apply sum_congr rfl
  intro W _
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro L _
  by_cases hW : U ≤ W <;> by_cases hL : U ≤ L <;> simp [hW,hL] <;> ring

private theorem kernelOperator_surj (w : P → ℝ) (hw : ∀ U,0<w U) :
    Function.Surjective (kernelOperator w) := by
  classical
  apply LinearMap.injective_iff_surjective.mp
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a ha
  change a = 0
  apply upperZeta_zero a
  have hz : kernelOperator w a = 0 := LinearMap.mem_ker.mp ha
  have hn : (∑ U : P, w U * (upperZeta a U)^2) = 0 := by
    rw [← kernel_quadratic, hz]
    simp
  intro U
  have hU : w U * (upperZeta a U)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun X _ => mul_nonneg (hw X).le (sq_nonneg _))).mp hn U (mem_univ _)
  simpa only [pow_two, mul_self_eq_zero] using ((mul_eq_zero.mp hU).resolve_left (hw U).ne')

end Poset

#print axioms upperZeta_zero
#print axioms kernel_quadratic
#print axioms kernelOperator_surj
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments

open Finset LinearMap Submodule
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Fintype V] [Fintype (Submodule F V)]

abbrev Sample (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  Fin (Module.finrank F V) → V

noncomputable def tupleSpan (v : Sample F V) : Submodule F V :=
  Submodule.span F (Set.range v)

noncomputable def spanWeight (W : Submodule F V) : ℝ := by
  classical
  exact (#(univ.filter (fun v : Sample F V => tupleSpan v = W)) : ℝ)

omit [Fintype F] [Fintype V] [Fintype (Submodule F V)] in
private theorem tupleSpan_surj : Function.Surjective (tupleSpan (F:=F) (V:=V)) := by
  classical
  intro W
  let b := Module.finBasis F W
  let v : Sample F V := fun i =>
    if hi : i.val < Module.finrank F W then (b ⟨i.val,hi⟩ : V) else 0
  have h₁ : tupleSpan v ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    unfold v
    split <;> simp
  have h₂ : W ≤ tupleSpan v := by
    have hW : Submodule.span F (Set.range fun i => (b i : V)) = W := by
      calc
        _ = (Submodule.span F (Set.range b)).map W.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        _ = W := by rw [b.span_eq, ← LinearMap.range_eq_map, Submodule.range_subtype]
    rw [← hW]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    refine ⟨⟨i.val, i.isLt.trans_le (Submodule.finrank_le W)⟩, ?_⟩
    simp [v,i.isLt]
  exact ⟨v, le_antisymm h₁ h₂⟩

private theorem spanWeight_pos (W : Submodule F V) : 0 < spanWeight W := by
  classical
  obtain ⟨v,hv⟩ := tupleSpan_surj W
  have hm : v ∈ univ.filter (fun x : Sample F V => tupleSpan x = W) := by simp [hv]
  unfold spanWeight
  exact_mod_cast Finset.card_pos.mpr ⟨v, hm⟩

private theorem span_kernel_card (W L : Submodule F V) :
    semanticKernel spanWeight W L = (Nat.card (Fin (Module.finrank F V) → (W ⊓ L : Submodule F V)) : ℝ) := by
  classical
  let T := W ⊓ L
  let s : Finset (Sample F V) := univ.filter (fun v => tupleSpan v ≤ T)
  have hc : Nat.card (Fin (Module.finrank F V) → T) = #s := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_ofFinset s (p:=fun v => tupleSpan v ≤ T) (by intro v; change v ∈ s ↔ tupleSpan v ≤ T; simp [s])]
    apply Fintype.card_congr
    have help (v : Sample F V) : tupleSpan v ≤ T ↔ ∀ i, v i ∈ T := by
      rw [tupleSpan, Submodule.span_le, Set.range_subset_iff]; rfl
    exact { toFun := fun v => ⟨fun i => v i, (help _).mpr fun i => (v i).prop⟩
            invFun := fun v i => ⟨v.val i,(help _).mp v.prop i⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  change _ = (Nat.card (Fin (Module.finrank F V) → T) : ℝ)
  rw [hc]
  unfold semanticKernel
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [← Finset.sum_fiberwise s tupleSpan (fun _ => (1:ℝ))]
  apply sum_congr rfl
  intro U _
  rw [spanWeight]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  by_cases h : U ≤ W ∧ U ≤ L
  · rw [ite_eq_left h]
    have he : s.filter (fun v => tupleSpan v = U) = univ.filter (fun v => tupleSpan v = U) := by
      ext v
      simp only [s,mem_filter,mem_univ,true_and,T]
      exact ⟨And.right, fun e => ⟨le_inf (e ▸ h.1) (e ▸ h.2), e⟩⟩
    rw [he]
  · rw [ite_eq_right h]
    have hs : s.filter (fun v => tupleSpan v = U) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      simp only [s,T,mem_filter,mem_univ,true_and] at hv
      exact h (le_inf_iff.mp (hv.2 ▸ hv.1))
    simp [hs]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments

open Finset LinearMap Submodule
open scoped BigOperators Classical
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments

variable {F V E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype V]
  [Fintype (Submodule F V)] [∀ L : Submodule F V, Fintype (Module.Dual F (V ⧸ L))]
  [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype (Submodule F V)] [∀ L : Submodule F V, Fintype (Module.Dual F (V ⧸ L))]
  [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E] [FiniteDimensional F V] in
private theorem quotient_columns (ell : E → V) (S : Finset E) (L : Submodule F V) :
    columns (F:=F) (L.mkQ ∘ ell) S = (columns (F:=F) ell S).map L.mkQ := by
  unfold columns
  rw [Submodule.map_span, Set.image_image]
  rfl

omit [Fintype V] [Fintype (Submodule F V)] [∀ L : Submodule F V, Fintype (Module.Dual F (V ⧸ L))]
  [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E] in
private theorem quotient_column_rank_add (ell : E → V) (S : Finset E) (L : Submodule F V) :
    Module.finrank F (columns (F:=F) (L.mkQ ∘ ell) S) +
    Module.finrank F ↥(columns (F:=F) ell S ⊓ L : Submodule F V) = Module.finrank F (columns (F:=F) ell S) := by
  let W := columns (F:=F) ell S
  rw [quotient_columns]
  have h := LinearMap.finrank_range_add_finrank_ker (L.mkQ.comp W.subtype)
  rw [LinearMap.range_comp,Submodule.range_subtype] at h
  rw [← Submodule.finrank_map_subtype_eq W (L.mkQ.comp W.subtype).ker,
    LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype] at h
  exact h

noncomputable def spanNormalizer (W : Submodule F V) : ℝ :=
  (Fintype.card F : ℝ)^(Module.finrank F V * Module.finrank F W)

private theorem moment_scaled_is_intersection (ell : E → V) (S : Finset E) (L : Submodule F V) :
    spanNormalizer (columns (F:=F) ell S) *
      readMoment (F:=F) (L.mkQ ∘ ell) ((Module.finrank F V : ℝ)+1) S =
    semanticKernel spanWeight (columns (F:=F) ell S) L := by
  classical
  let m := Module.finrank F V
  let W := columns (F:=F) ell S
  let T := W ⊓ L
  let r := Module.finrank F (columns (F:=F) (L.mkQ ∘ ell) S)
  have hq : 0<(Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : 0 < (m:ℝ)+1 := by positivity
  have hr : r+Module.finrank F T = Module.finrank F W := quotient_column_rank_add ell S L
  rw [span_kernel_card, readMoment, actual_column_moment _ _ hw]
  change spanNormalizer W * ((Fintype.card F:ℝ)^(1-((m:ℝ)+1)))^r =
    (Nat.card (Fin m → T):ℝ)
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Module.card_eq_pow_finrank (K:=F) (V:=T)]
  simp only [Fintype.card_fin, Nat.cast_pow, ← pow_mul, spanNormalizer]
  rw [show 1-((m:ℝ)+1)=-(m:ℝ) by ring, Real.rpow_neg hq.le, Real.rpow_natCast, inv_pow,
    ← pow_mul, show m=Module.finrank F V by rfl, ← hr, Nat.mul_add]
  rw [pow_add, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), one_mul, Nat.mul_comm]

/-- Every scalar function of the actual column span is reconstructed by one
common set of real coefficients from quotient-code physical marginal moments.
The moment order is only the dimension of the label space plus one. -/
theorem physical_lattice_reconstruction (ell : E → V) (f : Submodule F V → ℝ) :
    ∃ a : Submodule F V → ℝ, ∀ S : Finset E,
    (∑ L : Submodule F V, a L *
      readMoment (F:=F) (L.mkQ ∘ ell) ((Module.finrank F V : ℝ)+1) S) =
      f (columns (F:=F) ell S) := by
  classical
  obtain ⟨a,ha⟩ := kernelOperator_surj spanWeight spanWeight_pos
    (fun W : Submodule F V => spanNormalizer W * f W)
  refine ⟨a, fun S => ?_⟩
  let W := columns (F:=F) ell S
  have hW : 0 < spanNormalizer W := by
    have hq : 0<(Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    unfold spanNormalizer
    positivity
  apply mul_left_cancel₀ hW.ne'
  calc
    _ = kernelOperator spanWeight a W := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro L _
      rw [mul_left_comm, moment_scaled_is_intersection]
      ring
    _ = _ := congrFun ha W

#print axioms quotient_column_rank_add
#print axioms moment_scaled_is_intersection
#print axioms physical_lattice_reconstruction
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
