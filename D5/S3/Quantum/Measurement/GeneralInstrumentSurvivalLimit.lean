/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival effects of a general instrument decrease to the largest fixed effect below the identity. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

variable {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]

/-- **The survival effects decrease to the largest fixed effect.** For no-click Kraus operators
`Q_a` and click Kraus operators `L_i` with `∑ₐ Q_aᴴ Q_a + ∑ᵢ L_iᴴ L_i = I`, the survival effects
`S_N = 𝒜ᴺ(I)` satisfy `0 ≤ S_{N+1} ≤ S_N ≤ I` in the Loewner order and converge to an effect `F`
with `0 ≤ F ≤ S_N`, `𝒜(F) = F`; every effect `0 ≤ H ≤ I` with `𝒜(H) = H` lies below `F`; and
`Tr(ρ S_N) → Tr(ρ F)` for every `ρ`. -/
theorem survival_tendsto_maximal_fixed_effect (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1) :
    ∃ F : Matrix (Fin d) (Fin d) ℂ,
      Tendsto (survival Q) atTop (𝓝 F) ∧
      (∀ N, 0 ≤ survival Q N ∧ survival Q (N + 1) ≤ survival Q N ∧ survival Q N ≤ 1 ∧
        F ≤ survival Q N) ∧
      0 ≤ F ∧ F ≤ 1 ∧ noClickDual Q F = F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℂ, 0 ≤ H → H ≤ 1 → noClickDual Q H = H → H ≤ F) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * survival Q N).trace) atTop (𝓝 (ρ * F).trace) := by
  classical
  -- (i) the dual map is linear, positive and monotone
  have hsub : ∀ X Y, noClickDual Q (X - Y) = noClickDual Q X - noClickDual Q Y := by
    intro X Y
    simp only [noClickDual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  have hpos : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.PosSemidef → (noClickDual Q X).PosSemidef :=
    fun X hX => posSemidef_sum _ fun a _ => hX.conjTranspose_mul_mul_same (Q a)
  have hmono : ∀ X Y : Matrix (Fin d) (Fin d) ℂ, X ≤ Y → noClickDual Q X ≤ noClickDual Q Y := by
    intro X Y h
    rw [Matrix.le_iff, ← hsub]
    exact hpos _ (Matrix.le_iff.mp h)
  have hS : ∀ N, survival Q (N + 1) = noClickDual Q (survival Q N) := fun N => rfl
  have hnonneg : ∀ N, 0 ≤ survival Q N := by
    intro N
    induction N with
    | zero => exact Matrix.nonneg_iff_posSemidef.mpr PosSemidef.one
    | succ N ih => exact Matrix.nonneg_iff_posSemidef.mpr (hpos _ (Matrix.nonneg_iff_posSemidef.mp ih))
  have hdecr : ∀ N, survival Q (N + 1) ≤ survival Q N := by
    intro N
    induction N with
    | zero =>
        rw [Matrix.le_iff]
        have h1 : survival Q 0 - survival Q (0 + 1) = ∑ i, (L i)ᴴ * L i := by
          simp only [survival, noClickDual, Matrix.mul_one]
          rw [← hcomp]
          abel
        rw [h1]
        exact posSemidef_sum _ fun i _ => posSemidef_conjTranspose_mul_self (L i)
    | succ N ih => exact hmono _ _ ih
  have hanti : Antitone (survival Q) := antitone_nat_of_succ_le hdecr
  have hle1 : ∀ N, survival Q N ≤ 1 := fun N => hanti (Nat.zero_le N)
  -- (ii) the quadratic forms converge, and polarization gives the entries
  let c : Matrix (Fin d) (Fin d) ℂ → (Fin d → ℂ) → ℂ := fun A v => star v ⬝ᵥ (A *ᵥ v)
  have hcre : ∀ N v, (c (survival Q N) v).im = 0 ∧ 0 ≤ (c (survival Q N) v).re := by
    intro N v
    have h := (Matrix.nonneg_iff_posSemidef.mp (hnonneg N)).dotProduct_mulVec_nonneg v
    rw [Complex.nonneg_iff] at h
    exact ⟨h.2.symm, h.1⟩
  have hcanti : ∀ v, Antitone fun N => (c (survival Q N) v).re := by
    intro v M N hMN
    have h := (Matrix.le_iff.mp (hanti hMN)).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.nonneg_iff] at h
    simp only [Complex.sub_re] at h
    linarith [h.1]
  let ℓ : (Fin d → ℂ) → ℝ := fun v => ⨅ N, (c (survival Q N) v).re
  have hℓ : ∀ v, Tendsto (fun N => c (survival Q N) v) atTop (𝓝 (ℓ v : ℂ)) := by
    intro v
    have hre : Tendsto (fun N => (c (survival Q N) v).re) atTop (𝓝 (ℓ v)) :=
      tendsto_atTop_ciInf (hcanti v) ⟨0, by rintro _ ⟨N, rfl⟩; exact (hcre N v).2⟩
    have heq : (fun N => c (survival Q N) v) = fun N => ((c (survival Q N) v).re : ℂ) := by
      funext N
      exact Complex.ext (by simp) (by simp [(hcre N v).1])
    rw [heq]
    exact (Complex.continuous_ofReal.tendsto _).comp hre
  let e : Fin d → Fin d → ℂ := fun i => Pi.single i 1
  have hpol : ∀ (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d), A i j =
      (1 / 4 : ℂ) * (c A (e i + e j) - c A (e i - e j) - Complex.I * c A (e i + Complex.I • e j) +
        Complex.I * c A (e i - Complex.I • e j)) := by
    intro A i j
    have hB : ∀ u w : Fin d → ℂ, c A (u + w) = c A u + star u ⬝ᵥ (A *ᵥ w) +
        star w ⬝ᵥ (A *ᵥ u) + c A w := by
      intro u w
      simp only [c, Matrix.mulVec_add, star_add, dotProduct_add, add_dotProduct]
      ring
    have hneg : ∀ u w : Fin d → ℂ, c A (u - w) = c A u - star u ⬝ᵥ (A *ᵥ w) -
        star w ⬝ᵥ (A *ᵥ u) + c A w := by
      intro u w
      simp only [c, Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct]
      ring
    have hsmul : ∀ (z : ℂ) (u w : Fin d → ℂ), star u ⬝ᵥ (A *ᵥ (z • w)) = z * (star u ⬝ᵥ (A *ᵥ w)) ∧
        star (z • w) ⬝ᵥ (A *ᵥ u) = star z * (star w ⬝ᵥ (A *ᵥ u)) ∧
        c A (z • w) = star z * z * c A w := by
      intro z u w
      refine ⟨?_, ?_, ?_⟩
      · rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
      · rw [star_smul, smul_dotProduct, smul_eq_mul]
      · simp only [c, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
        ring
    have hentry : star (e i) ⬝ᵥ (A *ᵥ e j) = A i j := by
      simp [e, Matrix.mulVec_single, dotProduct, Pi.single_apply]
    rw [hB, hneg, hB, hneg, (hsmul _ _ _).1, (hsmul _ _ _).2.1, (hsmul _ 0 _).2.2, hentry]
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    rw [hI]
    linear_combination (1 / 2 : ℂ) * (A i j - star (e j) ⬝ᵥ (A *ᵥ e i)) * Complex.I_sq
  let F : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j =>
    (1 / 4 : ℂ) * ((ℓ (e i + e j) : ℂ) - (ℓ (e i - e j) : ℂ) -
      Complex.I * (ℓ (e i + Complex.I • e j) : ℂ) + Complex.I * (ℓ (e i - Complex.I • e j) : ℂ))
  have hlim : Tendsto (survival Q) atTop (𝓝 F) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (((hℓ (e i + e j)).sub (hℓ (e i - e j))).sub
      ((hℓ (e i + Complex.I • e j)).const_mul Complex.I)).add
        ((hℓ (e i - Complex.I • e j)).const_mul Complex.I)
    have h' := h.const_mul (1 / 4 : ℂ)
    simp only [F, Matrix.of_apply]
    refine h'.congr fun N => ?_
    exact (hpol (survival Q N) i j).symm
  -- (iii) closedness of the cone of positive semidefinite matrices
  have hclosed : ∀ (f : ℕ → Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℂ),
      Tendsto f atTop (𝓝 A) → (∀ᶠ N in atTop, (f N).PosSemidef) → A.PosSemidef := by
    intro f A hf hpsd
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · have hc : IsClosed {X : Matrix (Fin d) (Fin d) ℂ | Xᴴ = X} :=
        isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
      exact hc.mem_of_tendsto hf (hpsd.mono fun N hN => hN.1)
    · have hcont : Continuous fun X : Matrix (Fin d) (Fin d) ℂ => star v ⬝ᵥ (X *ᵥ v) :=
        continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
      exact ge_of_tendsto ((hcont.tendsto A).comp hf)
        (hpsd.mono fun N hN => hN.dotProduct_mulVec_nonneg v)
  have hFle : ∀ N, F ≤ survival Q N := by
    intro N
    rw [Matrix.le_iff]
    exact hclosed (fun M => survival Q N - survival Q M) _ (tendsto_const_nhds.sub hlim)
      (eventually_atTop.mpr ⟨N, fun M hM => Matrix.le_iff.mp (hanti hM)⟩)
  have hF0 : 0 ≤ F := Matrix.nonneg_iff_posSemidef.mpr
    (hclosed _ _ hlim (Eventually.of_forall fun N => Matrix.nonneg_iff_posSemidef.mp (hnonneg N)))
  have hcontA : Continuous (noClickDual Q) := by
    unfold noClickDual
    exact continuous_finsetSum _ fun a _ =>
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hfix : noClickDual Q F = F := by
    have h1 : Tendsto (fun N => survival Q (N + 1)) atTop (𝓝 F) :=
      (tendsto_add_atTop_iff_nat 1).mpr hlim
    have h2 : Tendsto (fun N => survival Q (N + 1)) atTop (𝓝 (noClickDual Q F)) := by
      simp only [hS]
      exact (hcontA.tendsto F).comp hlim
    exact tendsto_nhds_unique h2 h1
  -- (iv) maximality
  have hmax : ∀ H : Matrix (Fin d) (Fin d) ℂ, 0 ≤ H → H ≤ 1 → noClickDual Q H = H → H ≤ F := by
    intro H _ hH1 hHfix
    have hbelow : ∀ N, H ≤ survival Q N := by
      intro N
      induction N with
      | zero => exact hH1
      | succ N ih => rw [← hHfix, hS]; exact hmono _ _ ih
    rw [Matrix.le_iff]
    exact hclosed (fun N => survival Q N - H) _ (hlim.sub tendsto_const_nhds)
      (Eventually.of_forall fun N => Matrix.le_iff.mp (hbelow N))
  refine ⟨F, hlim, fun N => ⟨hnonneg N, hdecr N, hle1 N, hFle N⟩, hF0, hFle 0, hfix, hmax,
    fun ρ => ?_⟩
  exact ((continuous_const.matrix_mul continuous_id).matrix_trace.tendsto F).comp hlim

#print axioms survival_tendsto_maximal_fixed_effect

end D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
