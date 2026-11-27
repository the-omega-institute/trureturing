/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent shifts, the normal Fock folium, and disjoint infrared memory representations. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockFactorDisjointness
import D5.S3.Quantum.Analysis.NullConeGravity.NullMemoryBMS4D
import OmegaMath.OperatorAlgebra.BoundedOperatorFamily
import OmegaMath.OperatorAlgebra.UnitaryIntertwining
import OmegaMath.Analysis.PlanarGaussian
import Mathlib.Analysis.Real.Cardinality

/-! Coherent shifts of the finite-mode Weyl algebra and disjoint dyadic memory sectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Complex MeasureTheory ContinuousLinearMap NullConeGravity
open Omega.PlanarGaussian Omega.HilbertBasisFiniteModes
open Omega.SquareSummableProjection Omega.UnitaryIntertwining
open D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockFactorDisjointness
open scoped ComplexConjugate InnerProductSpace Topology BigOperators

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRCoherentMemorySectors

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The coherent characteristic function on the indicated finite set of modes. -/
def coherentShiftChar (F : Finset I) (h : I → ℂ) (w : F → ℂ) : ℂ :=
  Complex.exp (2 * Complex.I * (∑ i : F, (conj (h i) * w i).im) -
    (1 / 2 : ℂ) * ∑ i : F, (‖w i‖ ^ 2 : ℝ))

private theorem shift_memℓp {h : I → ℂ} (hh : Summable (fun i => ‖h i‖ ^ 2)) : Memℓp h 2 :=
  memℓp_gen (by simpa using hh)

private theorem coherent_weyl_conjugation (b : HilbertBasis I ℂ H) (η z : H) (ψ : BosonFock I) :
    (fockWeyl b η).symm (fockWeyl b z (fockWeyl b η ψ)) =
      Complex.exp (2 * Complex.I * (⟪η, z⟫_ℂ).im) • fockWeyl b z ψ := by
  rw [fockWeyl_symm, fockWeyl_mul b z η, map_smul, fockWeyl_mul b (-η), smul_smul,
    ← Complex.exp_add, show -η + (z + η) = z by abel]
  congr 2
  have hsymm : (⟪z, η⟫_ℂ).im = -(⟪η, z⟫_ℂ).im := by
    simpa only [RCLike.im_eq_complex_im] using inner_im_symm (𝕜 := ℂ) z η
  have hself : (⟪η, η⟫_ℂ).im = 0 := by
    simpa only [RCLike.im_eq_complex_im] using inner_self_im (𝕜 := ℂ) η
  simp only [inner_neg_left, inner_add_right, add_im, neg_im, hself,
    hsymm, Complex.ofReal_neg, mul_neg, neg_neg]
  push_cast
  ring

/-- Square-summable shifts are realized by the corresponding normalized coherent vector. -/
theorem coherentShiftChar_eq_weyl_vacuum_of_summable
    (b : HilbertBasis I ℂ H) (h : I → ℂ) (hh : Summable (fun i => ‖h i‖ ^ 2)) :
    let η := b.repr.symm ⟨h, shift_memℓp hh⟩
    let ψ := fockWeyl b η (fockVacuum I)
    ‖ψ‖ = 1 ∧ ∀ (F : Finset I) (w : F → ℂ),
      ⟪ψ, fockWeyl b (modeEmbed b F w) ψ⟫_ℂ = coherentShiftChar F h w := by
  dsimp only
  refine ⟨((fockWeyl b _).norm_map _).trans (fockVacuum_norm I), fun F w => ?_⟩
  let η := b.repr.symm ⟨h, shift_memℓp hh⟩
  let W := fockWeyl b η
  let z := modeEmbed b F w
  change ⟪W (fockVacuum I), fockWeyl b z (W (fockVacuum I))⟫_ℂ = _
  have hinner := W.inner_map_map (fockVacuum I) (W.symm (fockWeyl b z (W (fockVacuum I))))
  rw [W.apply_symm_apply] at hinner
  rw [hinner]
  dsimp only [W]
  rw [coherent_weyl_conjugation, inner_smul_right, fockWeyl_vacuum_inner, ← Complex.exp_add,
    inner_modeEmbed, ← Complex.ofReal_pow, modeEmbed_norm_sq]
  simp only [η, LinearIsometryEquiv.apply_symm_apply, coherentShiftChar, Complex.im_sum]
  congr 1
  ring

/-- The normalized planar average is the product of the coherent vacuum probabilities. -/
theorem coherentShiftChar_gaussian_avg (F : Finset I) (h : I → ℂ) :
    (Real.pi : ℂ)⁻¹ ^ F.card * (∫ w : F → ℂ, (weight w : ℂ) * coherentShiftChar F h w) =
      ∏ i : F, (Real.exp (-‖h i‖ ^ 2) : ℂ) := by
  classical
  let u (i : F) : ℂ := -2 * Complex.I * (h i).im
  let v (i : F) : ℂ := 2 * Complex.I * (h i).re
  have he (w : F → ℂ) : (weight w : ℂ) * coherentShiftChar F h w =
      ∏ i : F, planarGaussian 1 1 (u i) (v i) (w i) := by
    have hpoint (i : F) :
        -(1 : ℂ) * (w i).re ^ 2 + u i * (w i).re +
            (-(1 : ℂ) * (w i).im ^ 2 + v i * (w i).im) =
          2 * Complex.I * (conj (h i) * w i).im - (‖w i‖ ^ 2 : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [u, v, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [weight, Complex.ofReal_exp, coherentShiftChar, ← Complex.exp_add]
    simp only [planarGaussian, realGaussian, ← Complex.exp_add, ← Complex.exp_sum,
      Complex.ofReal_one, hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    congr 1
    ring
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod, ← Fintype.card_coe F, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [integral_planarGaussian zero_lt_one zero_lt_one, div_one,
    Real.mul_self_sqrt Real.pi_pos.le, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul, Complex.ofReal_exp]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [u, v, Complex.ofReal_one, mul_one, Complex.ofReal_neg, Complex.ofReal_add,
    Complex.ofReal_mul, mul_pow, Complex.I_sq]
  ring

/-- The countable normal vector folium tested on every finite-mode displacement. -/
def CoherentShiftInFockFolium (b : HilbertBasis I ℂ H) (h : I → ℂ) : Prop :=
  ∃ ψ : ℕ → BosonFock I, HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ) ∧
    ∀ (F : Finset I) (w : F → ℂ),
      HasSum (fun n => ⟪ψ n, fockWeyl b (modeEmbed b F w) (ψ n)⟫_ℂ)
        (coherentShiftChar F h w)

private theorem single_folium (b : HilbertBasis I ℂ H) (h : I → ℂ) (ψ : BosonFock I)
    (hn : ‖ψ‖ = 1) (hψ : ∀ (F : Finset I) (w : F → ℂ),
      ⟪ψ, fockWeyl b (modeEmbed b F w) ψ⟫_ℂ = coherentShiftChar F h w) :
    CoherentShiftInFockFolium b h := by
  refine ⟨fun n => if n = 0 then ψ else 0, ?_, ?_⟩
  · convert hasSum_ite_eq (0 : ℕ) (1 : ℝ) using 1
    funext n
    by_cases hn' : n = 0 <;> simp [hn', hn]
  · intro F w
    convert hasSum_ite_eq 0 (coherentShiftChar F h w) using 1
    funext n
    by_cases hn' : n = 0 <;> simp [hn', hψ F w]

/-- Finitely many occupations capture half the mass of the countable vector ensemble. -/
private theorem coherent_tight_vacuum {ψ : ℕ → BosonFock I}
    (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ)) :
    ∃ S : Finset I, ∀ F : Finset I, Disjoint F S →
      1 / 2 ≤ ∑' n, ‖vacuumProj F (ψ n)‖ ^ 2 := by
  classical
  let a (p : ℕ × Occupation I) := ‖ψ p.1 p.2‖ ^ 2
  have ha : Summable a := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun n => (lp_sq (ψ n)).1, hψ.summable.congr (fun n => (lp_sq (ψ n)).2.symm)⟩
  have hv : HasSum a (1 : ℝ) := by
    apply ha.hasSum_iff.mpr
    rw [ha.tsum_prod]
    simpa only [a, (lp_sq _).2] using hψ.tsum_eq
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    (hv.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)))
  refine ⟨E.biUnion (fun p => p.2.support), fun F hF => ?_⟩
  let g (p : ℕ × Occupation I) := ‖vacuumProj F (ψ p.1) p.2‖ ^ 2
  have hg (p : ℕ × Occupation I) : g p ≤ a p := by
    dsimp only [a, g, vacuumProj]
    rw [cut_apply]
    split_ifs <;> simp
  have hgs : Summable g := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hg ha
  have hEq : ∑ p ∈ E, a p = ∑ p ∈ E, g p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hd := hF.symm.mono_left (Finset.subset_biUnion_of_mem (fun p => p.2.support) hp)
    dsimp only [a, g, vacuumProj]
    rw [cut_apply, ite_eq_left hd]
  calc
    1 / 2 ≤ ∑ p ∈ E, a p := (hE E le_rfl).le
    _ = ∑ p ∈ E, g p := hEq
    _ ≤ ∑' p, g p := hgs.sum_le_tsum E (fun _ _ => sq_nonneg _)
    _ = ∑' n, ‖vacuumProj F (ψ n)‖ ^ 2 := by
      rw [hgs.tsum_prod]
      exact tsum_congr (fun n => (lp_sq (vacuumProj F (ψ n))).2)

private theorem coherent_average_folium (b : HilbertBasis I ℂ H) (h : I → ℂ) (F : Finset I)
    {ψ : ℕ → BosonFock I} (hn : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ))
    (hψ : ∀ w : F → ℂ, HasSum (fun n => ⟪ψ n, fockWeyl b (modeEmbed b F w) (ψ n)⟫_ℂ)
        (coherentShiftChar F h w)) :
    (∑' n, ‖vacuumProj F (ψ n)‖ ^ 2) = ∏ i : F, Real.exp (-‖h i‖ ^ 2) := by
  let f (n : ℕ) (w : F → ℂ) := (weight w : ℂ) * ⟪ψ n, fockWeyl b (modeEmbed b F w) (ψ n)⟫_ℂ
  have hf (n : ℕ) : Integrable (f n) := by
    have hc (x : BosonFock I) : Continuous (fun w : F → ℂ => fockWeyl b (modeEmbed b F w) x) :=
      (fockWeyl_strongContinuous b x).comp (by unfold modeEmbed; fun_prop)
    simpa only [innerSL_apply_apply, inner_smul_right, f] using
      (innerSL ℂ (ψ n)).integrable_comp (weighted_integrable _ hc (ψ n))
  have hb (n : ℕ) (w : F → ℂ) : ‖f n w‖ ≤ weight w * ‖ψ n‖ ^ 2 := by
    dsimp only [f]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ weight w from (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    simpa only [LinearIsometryEquiv.norm_map, pow_two] using
      norm_inner_le_norm (𝕜 := ℂ) (ψ n) (fockWeyl b (modeEmbed b F w) (ψ n))
  have hs : Summable (fun n => ∫ w, ‖f n w‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      (hn.summable.mul_left (∫ w : F → ℂ, weight w))
    intro n
    rw [← integral_mul_const]
    exact integral_mono (hf n).norm (weight_integrable.mul_const _) (hb n)
  let c : ℂ := (Real.pi : ℂ)⁻¹ ^ F.card
  have he (w : F → ℂ) : (∑' n, f n w) = (weight w : ℂ) * coherentShiftChar F h w := by
    simp only [f, tsum_mul_left, (hψ w).tsum_eq]
  have hp (n : ℕ) : c * (∫ w, f n w) = ((‖vacuumProj F (ψ n)‖ ^ 2 : ℝ) : ℂ) :=
    fockWeyl_gaussian_avg_eq_vacuumProj b F (ψ n)
  have hsum := congrArg (c * ·) (integral_tsum_of_summable_integral_norm hf hs)
  simp only [← tsum_mul_left, hp, he, c, coherentShiftChar_gaussian_avg] at hsum
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_prod, Complex.ofReal_tsum] using hsum

/-- A classical shift belongs to the countable Fock folium exactly when it is square-summable. -/
theorem coherentShift_in_fock_folium_iff (b : HilbertBasis I ℂ H) (h : I → ℂ) :
    CoherentShiftInFockFolium b h ↔ Summable (fun i => ‖h i‖ ^ 2) := by
  classical
  constructor
  · rintro ⟨ψ, hn, hψ⟩
    obtain ⟨S, hS⟩ := coherent_tight_vacuum hn
    have hbound (F : Finset I) (hF : Disjoint F S) : ∑ i ∈ F, ‖h i‖ ^ 2 ≤ Real.log 2 := by
      have havg := hS F hF
      rw [coherent_average_folium b h F hn (hψ F),
        Finset.prod_coe_sort (s := F) (f := fun i => Real.exp (-‖h i‖ ^ 2)),
        ← Real.exp_sum, Finset.sum_neg_distrib, Real.exp_neg] at havg
      apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).2
      have he := Real.exp_pos (∑ i ∈ F, ‖h i‖ ^ 2)
      rw [← one_div, le_div_iff₀ he] at havg
      linarith
    apply summable_of_sum_le (c := Real.log 2 + ∑ i ∈ S, ‖h i‖ ^ 2) (fun _ => sq_nonneg _)
    intro F
    rw [← Finset.sum_sdiff (s₁ := S ∩ F) (s₂ := F) Finset.inter_subset_right,
      Finset.sdiff_inter_self_right]
    exact add_le_add (hbound (F \ S) Finset.disjoint_sdiff.symm)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun _ _ _ => sq_nonneg _))
  · intro hh
    exact single_folium b h _ (coherentShiftChar_eq_weyl_vacuum_of_summable b h hh).1
      (coherentShiftChar_eq_weyl_vacuum_of_summable b h hh).2

theorem coherentShift_not_in_fock_folium_of_not_summable
    (b : HilbertBasis I ℂ H) {h : I → ℂ} (hh : ¬ Summable (fun i => ‖h i‖ ^ 2)) :
    ¬ CoherentShiftInFockFolium b h :=
  fun hf => hh ((coherentShift_in_fock_folium_iff b h).mp hf)

/-- Zero extension of a finite tuple to a finitely supported displacement. -/
def finiteModeDisplacement (F : Finset I) (w : F → ℂ) : I →₀ ℂ := by
  classical
  exact Finsupp.onFinset F (fun i => if hi : i ∈ F then w ⟨i, hi⟩ else 0)
    (fun i hi => by by_contra h; exact hi (dite_eq_right h))

/-- Hilbert-basis synthesis of a finitely supported displacement. -/
def finiteModeSynthesis (b : HilbertBasis I ℂ H) : (I →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun i => b i)

private theorem displacement_finiteMode (b : HilbertBasis I ℂ H) (F : Finset I) (w : F → ℂ) :
    finiteModeSynthesis b (finiteModeDisplacement F w) = modeEmbed b F w := by
  classical
  rw [finiteModeSynthesis, finiteModeDisplacement, Finsupp.linearCombination_onFinset, modeEmbed]
  rw [← Finset.attach_eq_univ]
  rw [← Finset.sum_attach F]
  exact Finset.sum_congr rfl fun i _ => by simp

private theorem finiteModeDisplacement_support (d : I →₀ ℂ) :
    finiteModeDisplacement d.support (fun i => d i) = d := by
  classical
  ext i
  change (if hi : i ∈ d.support then d i else 0) = d i
  split_ifs with hi
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hi).symm

private def shiftPair (h : I → ℂ) : (I →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun i => conj (h i))

private def shiftPhase (h : I → ℂ) (d : I →₀ ℂ) : ℂ :=
  Complex.exp (2 * Complex.I * (shiftPair h d).im)

private theorem shiftPhase_norm (h : I → ℂ) (d : I →₀ ℂ) : ‖shiftPhase h d‖ = 1 := by
  simp [shiftPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem shiftPhase_add (h : I → ℂ) (d e : I →₀ ℂ) :
    shiftPhase h (d + e) = shiftPhase h d * shiftPhase h e := by
  simp only [shiftPhase, map_add, Complex.add_im, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem shiftPhase_sub_profile (h₁ h₂ : I → ℂ) (d : I →₀ ℂ) :
    shiftPhase (fun i => h₂ i - h₁ i) d * shiftPhase h₁ d = shiftPhase h₂ d := by
  have hpair : shiftPair (fun i => h₂ i - h₁ i) d = shiftPair h₂ d - shiftPair h₁ d := by
    simp only [shiftPair, Finsupp.linearCombination_apply, map_sub, smul_eq_mul, mul_sub,
      Finsupp.sum, Finset.sum_sub_distrib]
  simp only [shiftPhase, hpair, Complex.sub_im, Complex.ofReal_sub, ← Complex.exp_add]
  congr 1
  ring

/-- The finitely supported Weyl representation twisted by a classical shift character. -/
def shiftedFockRep (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ) :
    BosonFock I →L[ℂ] BosonFock I :=
  shiftPhase h d • weylMap b (finiteModeSynthesis b d)

theorem shiftedFockRep_mul (b : HilbertBasis I ℂ H) (h : I → ℂ) (d e : I →₀ ℂ) :
    shiftedFockRep b h d * shiftedFockRep b h e =
      Complex.exp (-(Complex.I * (⟪finiteModeSynthesis b d, finiteModeSynthesis b e⟫_ℂ).im)) •
        shiftedFockRep b h (d + e) := by
  apply ContinuousLinearMap.ext
  intro x
  change shiftPhase h d • fockWeyl b (finiteModeSynthesis b d)
    (shiftPhase h e • fockWeyl b (finiteModeSynthesis b e) x) = _
  rw [map_smul, fockWeyl_mul]
  simp only [shiftedFockRep, shiftPhase_add, map_add, smul_apply, smul_smul]
  congr 1
  ring

private theorem shiftedFockRep_norm (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ)
    (x : BosonFock I) : ‖shiftedFockRep b h d x‖ = ‖x‖ := by
  simp [shiftedFockRep, weylMap, norm_smul, shiftPhase_norm]

private theorem shiftedFockRep_bound (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ) :
    ‖shiftedFockRep b h d‖ ≤ 1 :=
  (shiftedFockRep b h d).opNorm_le_bound zero_le_one (fun x => by rw [shiftedFockRep_norm, one_mul])

/-- Evaluation at a shift profile represents the common norm-closed Weyl algebra on Fock space. -/
def shiftedFockCStarRep (b : HilbertBasis I ℂ H) (h : I → ℂ) :=
  Omega.BoundedOperatorFamily.evaluate (shiftedFockRep b) (shiftedFockRep_bound b) h

private theorem weylMap_apply (b : HilbertBasis I ℂ H) (z : H) (x : BosonFock I) :
    weylMap b z x = fockWeyl b z x := rfl

private theorem shiftedFockRep_left_unitary (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ) :
    (shiftedFockRep b h d).adjoint * shiftedFockRep b h d = 1 := by
  exact (norm_map_iff_adjoint_comp_self _).mp (shiftedFockRep_norm b h d)

private theorem shiftedFockRep_right_unitary (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ) :
    shiftedFockRep b h d * (shiftedFockRep b h d).adjoint = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hs : shiftPhase h d ≠ 0 := Complex.exp_ne_zero _
  let y := (fockWeyl b (finiteModeSynthesis b d)).symm ((shiftPhase h d)⁻¹ • x)
  have hy : shiftedFockRep b h d y = x := by
    simp [shiftedFockRep, weylMap_apply, y, smul_smul, hs]
  rw [← hy]
  change shiftedFockRep b h d ((shiftedFockRep b h d).adjoint (shiftedFockRep b h d y)) =
    shiftedFockRep b h d y
  exact congrArg (shiftedFockRep b h d) (DFunLike.congr_fun (shiftedFockRep_left_unitary b h d) y)

theorem shiftedFockRep_vacuum_inner (b : HilbertBasis I ℂ H) (h : I → ℂ)
    (F : Finset I) (w : F → ℂ) :
    ⟪fockVacuum I, shiftedFockRep b h (finiteModeDisplacement F w) (fockVacuum I)⟫_ℂ =
      coherentShiftChar F h w := by
  classical
  have hpair : shiftPair h (finiteModeDisplacement F w) = ∑ i : F, conj (h i) * w i := by
    rw [shiftPair, finiteModeDisplacement, Finsupp.linearCombination_onFinset,
      ← Finset.attach_eq_univ]
    simp_rw [smul_eq_mul, mul_comm _ (conj _)]
    rw [← Finset.sum_attach F]
    exact Finset.sum_congr rfl fun i _ => by simp
  simp only [shiftedFockRep, smul_apply, inner_smul_right, weylMap_apply, fockWeyl_vacuum_inner,
    displacement_finiteMode, shiftPhase, hpair, ← Complex.exp_add, coherentShiftChar]
  congr 1
  rw [← Complex.ofReal_pow, modeEmbed_norm_sq, Complex.ofReal_sum]
  rw [Complex.im_sum]
  push_cast
  ring

private theorem dense_displacement (b : HilbertBasis I ℂ H) : DenseRange (finiteModeSynthesis b) :=
  dense_range_of_modeEmbed b fun F w => ⟨finiteModeDisplacement F w, displacement_finiteMode b F w⟩

/-- A classical character twist leaves the scalar commutant of the finite Weyl family unchanged. -/
theorem shiftedFockRep_scalar_commutant (b : HilbertBasis I ℂ H) (h : I → ℂ) :
    ScalarCommutant (shiftedFockRep b h) := by
  intro T hT
  apply fockWeyl_commutant_scalar b T
  intro z x
  refine (dense_displacement b).induction ?_ (isClosed_eq
    (T.continuous.comp (fockWeyl_strongContinuous b x)) (fockWeyl_strongContinuous b (T x))) z
  rintro _ ⟨d, rfl⟩
  have hc := DFunLike.congr_fun (hT d) x
  change T (shiftPhase h d • fockWeyl b (finiteModeSynthesis b d) x) =
    shiftPhase h d • fockWeyl b (finiteModeSynthesis b d) (T x) at hc
  rw [map_smul] at hc
  exact (smul_right_injective (BosonFock I) (Complex.exp_ne_zero _)) hc

/-- The vacuum is cyclic for every classical shift on the finite Weyl family. -/
theorem shiftedFockRep_cyclic (b : HilbertBasis I ℂ H) (h : I → ℂ) :
    Dense (Submodule.span ℂ (range fun d => shiftedFockRep b h d (fockVacuum I)) :
      Set (BosonFock I)) := by
  let K := Submodule.span ℂ (range fun d => shiftedFockRep b h d (fockVacuum I))
  change Dense (K : Set (BosonFock I))
  apply Dense.of_closure
  apply (fockExponential_dense_span b).mono
  change Submodule.span ℂ (range (fockExponential b)) ≤ K.topologicalClosure
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨z, rfl⟩
  change fockExponential b z ∈ closure (↑K : Set _)
  refine (dense_displacement b).induction ?_
    (isClosed_closure.preimage (fockExponential_continuous b)) z
  rintro _ ⟨d, rfl⟩
  have hm : shiftedFockRep b h d (fockVacuum I) ∈ K :=
    Submodule.subset_span (s := range fun d => shiftedFockRep b h d (fockVacuum I)) ⟨d, rfl⟩
  rw [shiftedFockRep, smul_apply, weylMap_apply, ← fockExponential_zero b, fockWeyl_exponential,
    inner_zero_right, sub_zero, add_zero, smul_smul] at hm
  let c := shiftPhase h d * Complex.exp (-(‖finiteModeSynthesis b d‖ : ℂ) ^ 2 / 2)
  have hc : c ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hs := Submodule.smul_mem K c⁻¹ hm
  change c⁻¹ • (c • fockExponential b (finiteModeSynthesis b d)) ∈ K at hs
  apply subset_closure
  change fockExponential b (finiteModeSynthesis b d) ∈ K
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs

theorem shiftedFockRep_zero (b : HilbertBasis I ℂ H) (h : I → ℂ) :
    shiftedFockRep b h 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [shiftedFockRep, shiftPhase, weylMap_apply, fockWeyl_zero]

theorem shiftedFockRep_adjoint (b : HilbertBasis I ℂ H) (h : I → ℂ) (d : I →₀ ℂ) :
    (shiftedFockRep b h d).adjoint = shiftedFockRep b h (-d) := by
  have hmul : shiftedFockRep b h d * shiftedFockRep b h (-d) = 1 := by
    rw [shiftedFockRep_mul]
    simp [inner_neg_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, shiftedFockRep_zero]
  calc
    _ = (shiftedFockRep b h d).adjoint * (shiftedFockRep b h d * shiftedFockRep b h (-d)) := by
      rw [hmul, mul_one]
    _ = _ := by rw [← mul_assoc, shiftedFockRep_left_unitary, one_mul]

/-- Distinct shifts with nonsummable squared difference have no nonzero bounded intertwiner. -/
theorem shiftedFockRep_disjoint_of_diff_not_summable (b : HilbertBasis I ℂ H) (h₁ h₂ : I → ℂ)
    (hr : ¬ Summable (fun i => ‖h₁ i - h₂ i‖ ^ 2))
    (T : BosonFock I →L[ℂ] BosonFock I)
    (hT : ∀ d, T.comp (shiftedFockRep b h₁ d) = (shiftedFockRep b h₂ d).comp T) :
    T = 0 := by
  rcases irreducible_intertwiner_isometry_or_zero (shiftedFockRep b h₁) (shiftedFockRep b h₂)
      (shiftedFockRep_right_unitary b h₁) (shiftedFockRep_left_unitary b h₂)
      (shiftedFockRep_scalar_commutant b h₁) (shiftedFockRep_scalar_commutant b h₂) T hT with
    hzero | ⟨_, U, _, _, hU⟩
  · exact hzero
  exfalso
  let ψ := U.symm (fockVacuum I)
  have hψ : U ψ = fockVacuum I := U.apply_symm_apply _
  have hd (d : I →₀ ℂ) : U (fockWeyl b (finiteModeSynthesis b d) ψ) =
      shiftedFockRep b (fun i => h₂ i - h₁ i) d (fockVacuum I) := by
    have he := hU d ψ
    change U (shiftPhase h₁ d • fockWeyl b (finiteModeSynthesis b d) ψ) =
      shiftedFockRep b h₂ d (U ψ) at he
    rw [map_smul, hψ] at he
    apply smul_right_injective (BosonFock I) (show shiftPhase h₁ d ≠ 0 from Complex.exp_ne_zero _)
    change shiftPhase h₁ d • U (fockWeyl b (finiteModeSynthesis b d) ψ) =
      shiftPhase h₁ d • shiftedFockRep b (fun i => h₂ i - h₁ i) d (fockVacuum I)
    rw [he]
    simp only [shiftedFockRep, smul_apply, smul_smul, mul_comm (shiftPhase h₁ d),
      shiftPhase_sub_profile]
  have hn : ¬ Summable (fun i => ‖h₂ i - h₁ i‖ ^ 2) := by
    simpa only [norm_sub_rev] using hr
  apply coherentShift_not_in_fock_folium_of_not_summable b hn
  apply single_folium b _ ψ (U.symm.norm_map _ |>.trans (fockVacuum_norm I))
  intro F w
  rw [← U.inner_map_map, hψ, ← displacement_finiteMode, hd, shiftedFockRep_vacuum_inner]

open Physicslib4.GNS in
private theorem shiftedFockRep_equiv_of_cyclic
    {A Y : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    {σ : (I →₀ ℂ) →ₗ[ℝ] (I →₀ ℂ) →ₗ[ℝ] ℝ} (W : WeylSystem (A := A) σ)
    (b : HilbertBasis I ℂ H) (hσ : ∀ d e, σ d e =
      2 * (⟪finiteModeSynthesis b d, finiteModeSynthesis b e⟫_ℂ).im)
    (h : I → ℂ) (π : A →⋆ₐ[ℂ] (Y →L[ℂ] Y)) (Ω : Y)
    (hcyc : IsCyclicVector π Ω)
    (hchar : ∀ (F : Finset I) (w : F → ℂ),
      ⟪Ω, π (W.weyl (finiteModeDisplacement F w)) Ω⟫_ℂ = coherentShiftChar F h w) :
    ∃ U : BosonFock I ≃ₗᵢ[ℂ] Y, ∀ d x, U (shiftedFockRep b h d x) = π (W.weyl d) (U x) := by
  let v (d : I →₀ ℂ) := shiftedFockRep b h d (fockVacuum I)
  let w (d : I →₀ ℂ) := π (W.weyl d) Ω
  have hv := shiftedFockRep_cyclic b h
  have hw : Dense (Submodule.span ℂ (range w) : Set Y) := by
    let L : A →L[ℂ] Y := (ContinuousLinearMap.apply ℂ Y Ω).comp
      ⟨π.toLinearMap, NonUnitalStarAlgHom.instContinuousLinearMapClassComplex.map_continuous π⟩
    apply Dense.of_closure (hcyc.mono ?_)
    rintro _ ⟨a, rfl⟩
    change L a ∈ closure (Submodule.span ℂ (range w) : Set Y)
    refine W.dense_span.induction ?_ (isClosed_closure.preimage L.continuous) a
    intro t ht
    have hmap := Submodule.mem_map_of_mem (f := L.toLinearMap) ht
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    exact subset_closure hmap
  have hm (d e : I →₀ ℂ) : π (W.weyl d) * π (W.weyl e) =
      Complex.exp (-(Complex.I * (⟪finiteModeSynthesis b d, finiteModeSynthesis b e⟫_ℂ).im)) •
        π (W.weyl (d + e)) := by
    rw [← map_mul, W.weyl_mul, hσ, map_smul]
    push_cast
    congr 2
    ring
  have hgram (d e : I →₀ ℂ) : ⟪w d, w e⟫_ℂ = ⟪v d, v e⟫_ℂ := by
    have hc (r : I →₀ ℂ) : ⟪Ω, π (W.weyl r) Ω⟫_ℂ = ⟪fockVacuum I, v r⟫_ℂ := by
      simpa only [finiteModeDisplacement_support] using
        (hchar r.support (fun i => r i)).trans
          (shiftedFockRep_vacuum_inner b h r.support (fun i => r i)).symm
    dsimp [w, v]
    rw [← adjoint_inner_right, ← star_eq_adjoint, ← map_star, W.weyl_star, ← mul_apply_eq_comp,
      hm, ← adjoint_inner_right, shiftedFockRep_adjoint, ← mul_apply_eq_comp,
      shiftedFockRep_mul, smul_apply, smul_apply, inner_smul_right, inner_smul_right, hc]
  let V := Finsupp.linearCombination ℂ v
  let Z := Finsupp.linearCombination ℂ w
  have hV : DenseRange V := by
    change DenseRange (Finsupp.linearCombination ℂ v)
    simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hv
  have hZ : DenseRange Z := by
    change DenseRange (Finsupp.linearCombination ℂ w)
    simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hw
  have hn (c : (I →₀ ℂ) →₀ ℂ) : ‖Z c‖ = ‖V c‖ := by
    have h : ⟪Z c, Z c⟫_ℂ = ⟪V c, V c⟫_ℂ := by
      simp only [Z, V, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram]
    simp only [inner_self_eq_norm_sq_to_K] at h
    have hs : ‖Z c‖ ^ 2 = ‖V c‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  let U := (LinearEquiv.refl ℂ ((I →₀ ℂ) →₀ ℂ)).extendOfIsometry V Z hV hZ hn
  have hU (d : I →₀ ℂ) : U (v d) = w d := by
    simpa only [U, V, Z, LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul] using
      LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ ((I →₀ ℂ) →₀ ℂ)) V Z hV hZ hn
        (Finsupp.single d 1)
  refine ⟨U, fun d x => ?_⟩
  let L := (U : BosonFock I →L[ℂ] Y)
  have he : L.comp (shiftedFockRep b h d) = (π (W.weyl d)).comp L := by
    apply ContinuousLinearMap.ext_on hv
    rintro _ ⟨e, rfl⟩
    change U (shiftedFockRep b h d (v e)) = π (W.weyl d) (U (v e))
    rw [hU]
    change U ((shiftedFockRep b h d * shiftedFockRep b h e) (fockVacuum I)) =
      (π (W.weyl d) * π (W.weyl e)) Ω
    rw [shiftedFockRep_mul, hm, smul_apply, smul_apply, map_smul, hU]
  exact DFunLike.congr_fun he x

open Physicslib4.GNS in
/-- The coherent coefficients determine each cyclic realization of the finite-mode Weyl system.
A nonsummable shift difference forces the two realizations to be disjoint. -/
theorem coherentShift_gns_disjoint_of_diff_not_summable
    {A Y₁ Y₂ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup Y₁] [InnerProductSpace ℂ Y₁] [CompleteSpace Y₁]
    [NormedAddCommGroup Y₂] [InnerProductSpace ℂ Y₂] [CompleteSpace Y₂]
    {σ : (I →₀ ℂ) →ₗ[ℝ] (I →₀ ℂ) →ₗ[ℝ] ℝ} (W : WeylSystem (A := A) σ)
    (b : HilbertBasis I ℂ H) (hσ : ∀ d e, σ d e =
      2 * (⟪finiteModeSynthesis b d, finiteModeSynthesis b e⟫_ℂ).im)
    (h₁ h₂ : I → ℂ) (hr : ¬ Summable (fun i => ‖h₁ i - h₂ i‖ ^ 2))
    (π₁ : A →⋆ₐ[ℂ] (Y₁ →L[ℂ] Y₁)) (π₂ : A →⋆ₐ[ℂ] (Y₂ →L[ℂ] Y₂))
    (Ω₁ : Y₁) (Ω₂ : Y₂) (hcyc₁ : IsCyclicVector π₁ Ω₁) (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hchar₁ : ∀ (F : Finset I) (w : F → ℂ),
      ⟪Ω₁, π₁ (W.weyl (finiteModeDisplacement F w)) Ω₁⟫_ℂ = coherentShiftChar F h₁ w)
    (hchar₂ : ∀ (F : Finset I) (w : F → ℂ),
      ⟪Ω₂, π₂ (W.weyl (finiteModeDisplacement F w)) Ω₂⟫_ℂ = coherentShiftChar F h₂ w)
    (T : Y₁ →L[ℂ] Y₂) (hT : ∀ d, T.comp (π₁ (W.weyl d)) = (π₂ (W.weyl d)).comp T) : T = 0 := by
  obtain ⟨U₁, hU₁⟩ := shiftedFockRep_equiv_of_cyclic W b hσ h₁ π₁ Ω₁ hcyc₁ hchar₁
  obtain ⟨U₂, hU₂⟩ := shiftedFockRep_equiv_of_cyclic W b hσ h₂ π₂ Ω₂ hcyc₂ hchar₂
  let R := (U₂.symm : Y₂ →L[ℂ] BosonFock I).comp (T.comp (U₁ : BosonFock I →L[ℂ] Y₁))
  have hR : R = 0 := by
    apply shiftedFockRep_disjoint_of_diff_not_summable b h₁ h₂ hr R
    intro d
    apply ContinuousLinearMap.ext
    intro x
    apply U₂.injective
    change U₂ (U₂.symm (T (U₁ (shiftedFockRep b h₁ d x)))) =
      U₂ (shiftedFockRep b h₂ d (U₂.symm (T (U₁ x))))
    rw [hU₁, hU₂, U₂.apply_symm_apply, U₂.apply_symm_apply]
    exact DFunLike.congr_fun (hT d) (U₁ x)
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hR (U₁.symm x)
  change U₂.symm (T (U₁ (U₁.symm x))) = 0 at hx
  rw [U₁.apply_symm_apply] at hx
  exact U₂.symm.injective (hx.trans U₂.symm.map_zero.symm)

private def memoryBasis : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ => ℂ) 2))

/-- The finite-mode Weyl representation for a real dyadic memory amplitude. -/
def memorySectorRep (m : ℝ) (F : Finset ℕ) (w : F → ℂ) :
    BosonFock ℕ →L[ℂ] BosonFock ℕ :=
  shiftedFockCStarRep memoryBasis (dyadicMemoryProfile m)
    (Omega.BoundedOperatorFamily.generator _ _ (finiteModeDisplacement F w))

/-- Real memory amplitudes produce an uncountable family with pairwise zero intertwiner spaces. -/
theorem uncountable_pairwise_disjoint_memory_sectors :
    Uncountable (Set.range (memorySectorRep)) ∧
      ∀ m₁ m₂ : ℝ, m₁ ≠ m₂ → ∀ T : BosonFock ℕ →L[ℂ] BosonFock ℕ,
        (∀ (F : Finset ℕ) (w : F → ℂ),
          T.comp (memorySectorRep m₁ F w) = (memorySectorRep m₂ F w).comp T) → T = 0 := by
  have hdisjoint (m₁ m₂ : ℝ) (hm : m₁ ≠ m₂) (T : BosonFock ℕ →L[ℂ] BosonFock ℕ)
      (hT : ∀ (F : Finset ℕ) (w : F → ℂ),
        T.comp (memorySectorRep m₁ F w) = (memorySectorRep m₂ F w).comp T) : T = 0 := by
    refine shiftedFockRep_disjoint_of_diff_not_summable memoryBasis
      (dyadicMemoryProfile m₁) (dyadicMemoryProfile m₂)
      (fun h => hm ((dyadic_memory_diff_summable_sq_iff m₁ m₂).mp h)) T ?_
    intro d
    simpa only [memorySectorRep, shiftedFockCStarRep, Omega.BoundedOperatorFamily.evaluate_generator,
      finiteModeDisplacement_support] using hT d.support (fun i => d i)
  refine ⟨?_, hdisjoint⟩
  apply Function.Injective.uncountable (f := fun m : ℝ => ⟨memorySectorRep m, ⟨m, rfl⟩⟩)
  intro m₁ m₂ he
  by_contra hm
  have hrep : memorySectorRep m₁ = memorySectorRep m₂ := congrArg Subtype.val he
  have hz := hdisjoint m₁ m₂ hm (ContinuousLinearMap.id ℂ (BosonFock ℕ)) (by
    intro F w
    rw [hrep, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id])
  have h := DFunLike.congr_fun hz (fockVacuum ℕ)
  change fockVacuum ℕ = 0 at h
  simpa [h] using fockVacuum_norm ℕ

end D5.S3.Quantum.Analysis.NullConeGravity.CCRCoherentMemorySectors
