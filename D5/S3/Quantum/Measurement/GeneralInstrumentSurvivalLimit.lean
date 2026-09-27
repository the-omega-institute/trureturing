/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival effects of a general instrument decrease to the largest fixed effect below the identity. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
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
    let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) Aᴴ
    have hquadE : ∀ z : Fin d → ℂ,
        inner ℂ (T.toLinearMap (WithLp.toLp 2 z)) (WithLp.toLp 2 z) = c A z := by
      intro z
      change inner ℂ (T (WithLp.toLp 2 z)) (WithLp.toLp 2 z) = star z ⬝ᵥ (A *ᵥ z)
      rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
        Matrix.star_mulVec, conjTranspose_conjTranspose, dotProduct_comm, dotProduct_mulVec]
    have hentryE :
        inner ℂ (T.toLinearMap (WithLp.toLp 2 (e i))) (WithLp.toLp 2 (e j)) = A i j := by
      change inner ℂ (T (WithLp.toLp 2 (e i))) (WithLp.toLp 2 (e j)) = _
      rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
        Matrix.star_mulVec, conjTranspose_conjTranspose, dotProduct_comm]
      simp only [e, Pi.star_single, star_one, Matrix.single_one_vecMul, dotProduct_single_one]
      rfl
    have h := inner_map_polarization' T.toLinearMap (WithLp.toLp 2 (e i)) (WithLp.toLp 2 (e j))
    simp only [← WithLp.toLp_smul, ← WithLp.toLp_add, ← WithLp.toLp_sub] at h
    rw [hentryE, hquadE, hquadE, hquadE, hquadE] at h
    rw [div_eq_mul_inv] at h
    rw [div_eq_mul_inv, one_mul]
    exact h.trans (mul_comm _ _)
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
  have hclosed : IsClosed {X : Matrix (Fin d) (Fin d) ℂ | X.PosSemidef} := by
    cases isEmpty_or_nonempty (Fin d) with
    | inl hempty =>
        let _ := hempty
        have hset : {X : Matrix (Fin d) (Fin d) ℂ | X.PosSemidef} = Set.univ := by
          ext X
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          rw [Subsingleton.elim X 0]
          exact PosSemidef.zero
        rw [hset]
        exact isClosed_univ
    | inr hnonempty =>
        let _ := hnonempty
        have hset : {X : Matrix (Fin d) (Fin d) ℂ | X.PosSemidef} = Set.Ici 0 := by
          ext X
          exact Matrix.nonneg_iff_posSemidef.symm
        rw [hset]
        exact isClosed_Ici
  have hFle : ∀ N, F ≤ survival Q N := by
    intro N
    rw [Matrix.le_iff]
    exact hclosed.mem_of_tendsto (tendsto_const_nhds.sub hlim)
      (eventually_atTop.mpr ⟨N, fun M hM => Matrix.le_iff.mp (hanti hM)⟩)
  have hF0 : 0 ≤ F := Matrix.nonneg_iff_posSemidef.mpr
    (hclosed.mem_of_tendsto hlim
      (Eventually.of_forall fun N => Matrix.nonneg_iff_posSemidef.mp (hnonneg N)))
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
    exact hclosed.mem_of_tendsto (hlim.sub tendsto_const_nhds)
      (Eventually.of_forall fun N => Matrix.le_iff.mp (hbelow N))
  refine ⟨F, hlim, fun N => ⟨hnonneg N, hdecr N, hle1 N, hFle N⟩, hF0, hFle 0, hfix, hmax,
    fun ρ => ?_⟩
  exact ((continuous_const.matrix_mul continuous_id).matrix_trace.tendsto F).comp hlim

#print axioms survival_tendsto_maximal_fixed_effect

end D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
