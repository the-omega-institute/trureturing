/- GID: D5/S3/Quantum/Measurement/ExactConditionalPreparationCost
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ExactConditionalPreparationCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact universal conditional preparation has spectral-ratio optimal worst-case success. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Measurement.FiniteKrausInstrumentBornMarginal
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Center

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.ExactConditionalPreparationCost

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Foundation.FiniteKrausChannel

local notation "kact" => fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X

def TraceNonincreasing {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (K : Fin m → Matrix ι ι ℂ) : Prop :=
  (1 - ∑ j, (K j)ᴴ * K j).PosSemidef

def ExactPreparationContract {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (R : Matrix ι ι ℂ) (K : Fin m → Matrix ι ι ℂ) : Prop :=
  ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
    0 < (kact K ρ).trace.re ∧
    kact K ρ =
      ((kact K ρ).trace / (R * ρ).trace) •
        (CFC.sqrt R * ρ * CFC.sqrt R) ∧
    TraceNonincreasing K

noncomputable def leastEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (R : Matrix ι ι ℂ) (hR : R.PosDef) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hR.isHermitian.eigenvalues

noncomputable def greatestEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (R : Matrix ι ι ℂ) (hR : R.PosDef) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hR.isHermitian.eigenvalues

/-- The exact universal conditional preparation operations are scalar square-root filters;
their optimal worst-case success is the ratio of the least and greatest eigenvalues, and
deterministic preparation is possible exactly for positive scalar effects. -/
theorem exact_conditional_preparation_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (R : Matrix ι ι ℂ) (hR : R.PosDef) :
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      ∃ c : ℝ, 0 < c ∧ ∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) ∧
    (∀ c : ℝ, 0 < c →
      let Kc : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (Real.sqrt c) • CFC.sqrt R;
      (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
        0 < (kact Kc ρ).trace.re ∧
        kact Kc ρ = ((kact Kc ρ).trace / (R * ρ).trace) •
          (CFC.sqrt R * ρ * CFC.sqrt R)) ∧
      (TraceNonincreasing Kc ↔ (1 - c • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ) (c : ℝ), 0 < c →
      (∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) →
      (TraceNonincreasing K ↔ (1 - (c : ℂ) • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      TraceNonincreasing K → ∃ ρ : Matrix ι ι ℂ,
        ρ.PosSemidef ∧ ρ.trace = 1 ∧
        (kact K ρ).trace.re ≤
          leastEigenvalue R hR / greatestEigenvalue R hR) ∧
    (let Kopt : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (((1 / Real.sqrt (greatestEigenvalue R hR) : ℝ) : ℂ) • CFC.sqrt R);
      let Kfail : Matrix ι ι ℂ :=
        CFC.sqrt (1 - ((1 / greatestEigenvalue R hR : ℝ) : ℂ) • R);
      ExactPreparationContract R Kopt ∧ TraceNonincreasing Kopt ∧
        (Kopt 0)ᴴ * Kopt 0 + Kfailᴴ * Kfail = 1 ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          leastEigenvalue R hR / greatestEigenvalue R hR ≤
            (kact Kopt ρ).trace.re) ∧
    ((∃ (m : ℕ) (K : Fin m → Matrix ι ι ℂ),
        ExactPreparationContract R K ∧ TraceNonincreasing K ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (kact K ρ).trace = 1) ↔
      ∃ scalar : ℝ, 0 < scalar ∧ R = (scalar : ℂ) • 1) := by
  classical
  let G : Matrix ι ι ℂ := CFC.sqrt R
  have hRnonneg : (0 : Matrix ι ι ℂ) ≤ R := hR.posSemidef.nonneg
  have hGstar : Gᴴ = G := by
    simpa [G, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hGunit : IsUnit G := by
    exact (CFC.isUnit_sqrt_iff R hRnonneg).mpr hR.isUnit
  have hrigid {m : ℕ} (K : Fin m → Matrix ι ι ℂ)
      (hcontract : ExactPreparationContract R K) :
      ∃ c : ℝ, 0 < c ∧ ∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (G * X * G) := by
    unfold ExactPreparationContract at hcontract
    simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk] at hcontract ⊢
    have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGunit
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGdet
    have hGGinv : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGdet
    have hsandwich (A : Matrix ι ι ℂ) (w : ι → ℂ) (q : ℂ) :
        A * (q • rankOneDensity w) * Aᴴ = q • rankOneDensity (A *ᵥ w) := by
      rw [rankOneDensity, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
      rfl
    have hparallel (j : Fin m) (ψ : ι → ℂ) :
        ∃ a : ℂ, K j *ᵥ ψ = a • (G *ᵥ ψ) := by
      by_cases hψ : ψ = 0
      · exact ⟨0, by simp [hψ]⟩
      have hnormpos : 0 < (star ψ ⬝ᵥ ψ).re :=
        (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hψ)).1
      have hnormreal : star ψ ⬝ᵥ ψ = ((star ψ ⬝ᵥ ψ).re : ℂ) :=
        Complex.ext rfl
          (by simpa using ((Complex.nonneg_iff.mp (dotProduct_star_self_nonneg ψ)).2).symm)
      let q : ℂ := (((star ψ ⬝ᵥ ψ).re)⁻¹ : ℝ)
      let ρ : Matrix ι ι ℂ := q • rankOneDensity ψ
      have hqpos : (0 : ℂ) ≤ q := Complex.zero_le_real.mpr (inv_nonneg.mpr hnormpos.le)
      have hqne : q ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hnormpos.ne')
      have hρpsd : ρ.PosSemidef :=
        (posSemidef_vecMulVec_self_star ψ).smul hqpos
      have hρtrace : ρ.trace = 1 := by
        simp only [ρ, rankOneDensity, Matrix.trace_smul, smul_eq_mul]
        rw [Matrix.trace_vecMulVec, dotProduct_comm ψ (star ψ), hnormreal]
        simp only [q]
        exact_mod_cast inv_mul_cancel₀ hnormpos.ne'
      let x : ι → ℂ := K j *ᵥ ψ
      let y : ι → ℂ := G *ᵥ ψ
      have hyne : y ≠ 0 := by
        intro hy
        apply hψ
        calc
          ψ = (1 : Matrix ι ι ℂ) *ᵥ ψ := by simp
          _ = (G⁻¹ * G) *ᵥ ψ := by rw [hGinvG]
          _ = G⁻¹ *ᵥ y := by rw [Matrix.mulVec_mulVec]
          _ = 0 := by rw [hy, Matrix.mulVec_zero]
      have hyinnerne : star y ⬝ᵥ y ≠ 0 :=
        ne_of_gt (dotProduct_star_self_pos_iff.mpr hyne)
      let a : ℂ := (star y ⬝ᵥ x) / (star y ⬝ᵥ y)
      let z : ι → ℂ := x - a • y
      have hyz : star y ⬝ᵥ z = 0 := by
        dsimp only [z]
        dsimp only [a]
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        exact sub_eq_zero.mpr (div_mul_cancel₀ _ hyinnerne).symm
      have hGρG : G * ρ * G = q • rankOneDensity y := by
        calc
          G * ρ * G = G * ρ * Gᴴ := by rw [hGstar]
          _ = q • rankOneDensity y := hsandwich G ψ q
      have hrankyzero : rankOneDensity y *ᵥ z = 0 := by
        rw [rankOneDensity, Matrix.vecMulVec_mulVec]
        simp only [hyz, MulOpposite.op_zero, zero_smul]
      have hGρGzero : (G * ρ * G) *ᵥ z = 0 := by
        rw [hGρG, Matrix.smul_mulVec, hrankyzero, smul_zero]
      have hEzero : (∑ k, K k * ρ * (K k)ᴴ) *ᵥ z = 0 := by
        rw [(hcontract ρ hρpsd hρtrace).2.1, Matrix.smul_mulVec,
          hGρGzero, smul_zero]
      have htermpsd (k : Fin m) : (K k * ρ * (K k)ᴴ).PosSemidef :=
        hρpsd.mul_mul_conjTranspose_same (K k)
      have hquad : ∑ k, star z ⬝ᵥ ((K k * ρ * (K k)ᴴ) *ᵥ z) = 0 := by
        rw [← dotProduct_sum, ← Matrix.sum_mulVec, hEzero, dotProduct_zero]
      have hquadj : star z ⬝ᵥ ((K j * ρ * (K j)ᴴ) *ᵥ z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
          (htermpsd k).dotProduct_mulVec_nonneg z).mp hquad j (Finset.mem_univ j)
      have htermzero : (K j * ρ * (K j)ᴴ) *ᵥ z = 0 :=
        ((htermpsd j).dotProduct_mulVec_zero_iff z).mp hquadj
      have hrankxzero : rankOneDensity x *ᵥ z = 0 := by
        rw [hsandwich (K j) ψ q, Matrix.smul_mulVec] at htermzero
        exact (smul_eq_zero.mp htermzero).resolve_left hqne
      have hxz : star x ⬝ᵥ z = 0 := by
        by_cases hx : x = 0
        · simp [hx]
        rw [rankOneDensity, Matrix.vecMulVec_mulVec] at hrankxzero
        have hop : MulOpposite.op (star x ⬝ᵥ z) = 0 :=
          (smul_eq_zero.mp hrankxzero).resolve_right hx
        exact MulOpposite.op_injective (by simpa using hop)
      have hzx : star z ⬝ᵥ x = 0 := by
        rw [Matrix.star_dotProduct] at hxz
        exact star_eq_zero.mp hxz
      have hzy : star z ⬝ᵥ y = 0 := by
        rw [Matrix.star_dotProduct] at hyz
        exact star_eq_zero.mp hyz
      have hzz : star z ⬝ᵥ z = 0 := by
        calc
          star z ⬝ᵥ z = star z ⬝ᵥ (x - a • y) := by rfl
          _ = (star z ⬝ᵥ x) - (star z ⬝ᵥ (a • y)) := by
            rw [dotProduct_sub]
          _ = 0 := by rw [dotProduct_smul, hzx, hzy, smul_eq_mul, mul_zero, sub_zero]
      have hz : z = 0 := dotProduct_star_self_eq_zero.mp hzz
      exact ⟨a, sub_eq_zero.mp hz⟩
    have hscalar (j : Fin m) : ∃ a : ℂ, G⁻¹ * K j = a • 1 := by
      let f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := Matrix.toLin' (G⁻¹ * K j)
      have hf (ψ : ι → ℂ) : ∃ a : ℂ, f ψ = a • ψ := by
        obtain ⟨a, ha⟩ := hparallel j ψ
        refine ⟨a, ?_⟩
        calc
          f ψ = G⁻¹ *ᵥ (K j *ᵥ ψ) := by
            dsimp only [f]
            rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
          _ = G⁻¹ *ᵥ (a • (G *ᵥ ψ)) := by rw [ha]
          _ = a • (G⁻¹ *ᵥ (G *ᵥ ψ)) := by rw [Matrix.mulVec_smul]
          _ = a • ((G⁻¹ * G) *ᵥ ψ) := by rw [Matrix.mulVec_mulVec]
          _ = a • ψ := by rw [hGinvG, Matrix.one_mulVec]
      have hdep (ψ : ι → ℂ) : ¬LinearIndependent ℂ ![ψ, f ψ] := by
        by_cases hψ : ψ = 0
        · subst ψ
          intro hli
          exact (hli.ne_zero 0) rfl
        obtain ⟨a, ha⟩ := hf ψ
        rw [LinearIndependent.pair_iff' hψ]
        push Not
        exact ⟨a, ha.symm⟩
      obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
      refine ⟨a, Matrix.toLin'.injective ?_⟩
      dsimp only [f] at ha
      simpa only [map_smul, Matrix.toLin'_one, Module.End.one_eq_id] using ha
    choose a ha using hscalar
    have hK (j : Fin m) : K j = a j • G := by
      calc
        K j = (1 : Matrix ι ι ℂ) * K j := by rw [Matrix.one_mul]
        _ = (G * G⁻¹) * K j := by rw [hGGinv]
        _ = G * (G⁻¹ * K j) := Matrix.mul_assoc _ _ _
        _ = G * (a j • 1) := by rw [ha j]
        _ = a j • G := by simp
    let c : ℝ := ∑ j, Complex.normSq (a j)
    have haction (X : Matrix ι ι ℂ) :
        (∑ j, K j * X * (K j)ᴴ) = (c : ℂ) • (G * X * G) := by
      simp only [hK, Matrix.conjTranspose_smul, hGstar, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      rw [← Finset.sum_smul]
      dsimp only [c]
      push_cast
      rfl
    have hcpos : 0 < c := by
      let i : ι := Classical.choice inferInstance
      let ψ : ι → ℂ := Pi.single i 1
      let ρ : Matrix ι ι ℂ := rankOneDensity ψ
      have hψnorm : star ψ ⬝ᵥ ψ = 1 := by simp [ψ]
      have hρpsd : ρ.PosSemidef := posSemidef_vecMulVec_self_star ψ
      have hρtrace : ρ.trace = 1 := by
        dsimp only [ρ]
        rw [rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm, hψnorm]
      have houtpos := (hcontract ρ hρpsd hρtrace).1
      rw [haction] at houtpos
      by_contra hc
      have hc0 : c = 0 := le_antisymm (le_of_not_gt hc)
        (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (a j))
      rw [hc0] at houtpos
      norm_num at houtpos
    exact ⟨c, hcpos, haction⟩
  let hH : R.IsHermitian := hR.isHermitian
  let rMin : ℝ := leastEigenvalue R hR
  let rMax : ℝ := greatestEigenvalue R hR
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hRspec : R = U * D * Uᴴ := by
    simpa only [U, D, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_apply] using hH.spectral_theorem
  have hU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hrMinPos : 0 < rMin := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty hH.eigenvalues
    dsimp only [rMin, leastEigenvalue]
    rw [hi]
    exact hR.eigenvalues_pos i
  have hrMaxPos : 0 < rMax := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty hH.eigenvalues
    dsimp only [rMax, greatestEigenvalue]
    rw [hi]
    exact hR.eigenvalues_pos i
  have hLower : (R - (rMin : ℂ) • 1).PosSemidef := by
    have hdiag :
        (Matrix.diagonal (fun i => ((hH.eigenvalues i - rMin : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr
        (Finset.inf'_le (s := (Finset.univ : Finset ι))
          hH.eigenvalues (Finset.mem_univ i)))
    have hdiagEq : Matrix.diagonal (fun i => ((hH.eigenvalues i - rMin : ℝ) : ℂ)) =
        D - (rMin : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [D, hij]
    have hconj := hdiag.mul_mul_conjTranspose_same U
    rw [hdiagEq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU, ← hRspec] at hconj
    exact hconj
  have hUpper : ((rMax : ℂ) • 1 - R).PosSemidef := by
    have hdiag :
        (Matrix.diagonal (fun i => ((rMax - hH.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr
        (Finset.le_sup' (s := (Finset.univ : Finset ι)) hH.eigenvalues
          (Finset.mem_univ i)))
    have hdiagEq : Matrix.diagonal (fun i => ((rMax - hH.eigenvalues i : ℝ) : ℂ)) =
        (rMax : ℂ) • 1 - D := by
      ext i j
      by_cases hij : i = j <;> simp [D, hij]
    have hconj := hdiag.mul_mul_conjTranspose_same U
    rw [hdiagEq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU, ← hRspec] at hconj
    exact hconj
  have hGsq : G * G = R := CFC.sqrt_mul_sqrt_self R hRnonneg
  have hGtrace (X : Matrix ι ι ℂ) : (G * X * G).trace = (R * X).trace := by
    calc
      (G * X * G).trace = (X * G * G).trace :=
        (Matrix.trace_mul_cycle X G G).symm
      _ = (X * (G * G)).trace := by rw [Matrix.mul_assoc]
      _ = (X * R).trace := by rw [hGsq]
      _ = (R * X).trace := Matrix.trace_mul_comm X R
  have heffect {m : ℕ} (K : Fin m → Matrix ι ι ℂ) (c : ℝ)
      (haction : ∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (G * X * G)) :
      (∑ j, (K j)ᴴ * K j) = (c : ℂ) • R := by
    rw [Matrix.ext_iff_trace_mul_left]
    intro X
    calc
      (X * ∑ j, (K j)ᴴ * K j).trace =
          ∑ j, (K j * X * (K j)ᴴ).trace := by
            simp only [Matrix.mul_sum, Matrix.trace_sum]
            apply Finset.sum_congr rfl
            intro j _
            simpa only [Matrix.mul_assoc] using
              Matrix.trace_mul_cycle X (K j)ᴴ (K j)
      _ = (kact K X).trace := by
            simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
              LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum]
      _ = ((c : ℂ) • (G * X * G)).trace := by rw [haction]
      _ = (X * ((c : ℂ) • R)).trace := by
            rw [Matrix.trace_smul, hGtrace, Matrix.mul_smul, Matrix.trace_smul,
              Matrix.trace_mul_comm R X]
  let v : ι → ι → ℂ := fun i => (hH.eigenvectorBasis i).ofLp
  let eigenDensity : ι → Matrix ι ι ℂ := fun i => rankOneDensity (v i)
  have hvnorm (i : ι) : star (v i) ⬝ᵥ v i = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simpa only [v, if_pos] using
      (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal i i)
  have heigenPsd (i : ι) : (eigenDensity i).PosSemidef :=
    posSemidef_vecMulVec_self_star (v i)
  have heigenTrace (i : ι) : (eigenDensity i).trace = 1 := by
    dsimp only [eigenDensity]
    rw [rankOneDensity, Matrix.trace_vecMulVec,
      dotProduct_comm, hvnorm]
  have hReigenTrace (i : ι) : (R * eigenDensity i).trace = hH.eigenvalues i := by
    dsimp only [eigenDensity]
    rw [rankOneDensity, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, dotProduct_comm, hH.mulVec_eigenvectorBasis,
      dotProduct_smul, hvnorm]
    norm_num
  have hLowerExpectation (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
      (hρtrace : ρ.trace = 1) : rMin ≤ (R * ρ).trace.re := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef hρ hLower
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_mul_comm ρ R, hρtrace] at h
    norm_num at h ⊢
    exact h
  have hUpperExpectation (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
      (hρtrace : ρ.trace = 1) : (R * ρ).trace.re ≤ rMax := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef hρ hUpper
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_mul_comm ρ R, hρtrace] at h
    norm_num at h ⊢
    exact h
  have hscalarAction (c : ℝ) (hc : 0 < c) :
      ∀ X : Matrix ι ι ℂ,
        kact (fun _ : Fin 1 => (Real.sqrt c • G)) X =
          (c : ℂ) • (G * X * G) := by
    intro X
    simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_one,
      Matrix.conjTranspose_smul, hGstar, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [star_trivial, Real.mul_self_sqrt hc.le]
    rfl
  have hscalarConditional (c : ℝ) (hc : 0 < c) :
      ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
        0 < (kact (fun _ : Fin 1 => (Real.sqrt c • G)) ρ).trace.re ∧
        kact (fun _ : Fin 1 => (Real.sqrt c • G)) ρ =
          ((kact (fun _ : Fin 1 => (Real.sqrt c • G)) ρ).trace /
            (R * ρ).trace) • (G * ρ * G) := by
    intro ρ hρ hρtrace
    have hdenLower := hLowerExpectation ρ hρ hρtrace
    have hdenPos : 0 < (R * ρ).trace.re := lt_of_lt_of_le hrMinPos hdenLower
    have hdenNe : (R * ρ).trace ≠ 0 := fun h => by
      rw [h] at hdenPos
      norm_num at hdenPos
    have htrace :
        (kact (fun _ : Fin 1 => (Real.sqrt c • G)) ρ).trace =
          (c : ℂ) * (R * ρ).trace := by
      rw [hscalarAction c hc, Matrix.trace_smul, hGtrace, smul_eq_mul]
    constructor
    · rw [htrace, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_pos hc hdenPos
    · rw [hscalarAction c hc, Matrix.trace_smul, hGtrace, smul_eq_mul]
      have hquot :
          (((c : ℂ) * (R * ρ).trace) / (R * ρ).trace) = (c : ℂ) :=
        mul_div_cancel_right₀ _ hdenNe
      rw [hquot]
  have hscalarTni (c : ℝ) (hc : 0 < c) :
      TraceNonincreasing (fun _ : Fin 1 => (Real.sqrt c • G)) ↔
        (1 - c • R).PosSemidef := by
    unfold TraceNonincreasing
    rw [heffect _ c (hscalarAction c hc)]
    rfl
  constructor
  · intro m K hcontract
    simpa only [G] using hrigid K hcontract
  constructor
  · intro c hc
    dsimp
    constructor
    · simpa only [G] using hscalarConditional c hc
    · simpa only [G] using hscalarTni c hc
  constructor
  · intro m K c _ haction
    unfold TraceNonincreasing
    rw [heffect K c (by simpa only [G] using haction)]
  constructor
  · intro m K hcontract htni
    obtain ⟨c, hc, haction⟩ := hrigid K hcontract
    have heff := heffect K c haction
    have hcomp : (1 - (c : ℂ) • R).PosSemidef := by
      unfold TraceNonincreasing at htni
      rwa [heff] at htni
    obtain ⟨imax, _, himax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty hH.eigenvalues
    have himax' : rMax = hH.eigenvalues imax := by
      simpa only [rMax, greatestEigenvalue] using himax
    have hcmax := RHLinalg.trace_mul_nonneg_of_posSemidef (heigenPsd imax) hcomp
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, heigenTrace, Matrix.trace_mul_comm (eigenDensity imax) R,
      hReigenTrace, ← himax'] at hcmax
    norm_num at hcmax
    have hcle : c ≤ 1 / rMax := (le_div_iff₀ hrMaxPos).mpr hcmax
    obtain ⟨imin, _, himin⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty hH.eigenvalues
    have himin' : rMin = hH.eigenvalues imin := by
      simpa only [rMin, leastEigenvalue] using himin
    refine ⟨eigenDensity imin, heigenPsd imin, heigenTrace imin, ?_⟩
    rw [haction, Matrix.trace_smul, hGtrace, hReigenTrace, ← himin']
    norm_num
    calc
      c * rMin ≤ (1 / rMax) * rMin := mul_le_mul_of_nonneg_right hcle hrMinPos.le
      _ = rMin / rMax := by ring
  let b : ℝ := 1 / Real.sqrt rMax
  let Kopt : Fin 1 → Matrix ι ι ℂ := fun _ => (b : ℂ) • G
  let Kfail : Matrix ι ι ℂ :=
    CFC.sqrt (1 - ((1 / rMax : ℝ) : ℂ) • R)
  have hbpos : 0 < b := div_pos one_pos (Real.sqrt_pos.mpr hrMaxPos)
  have hbsq : b * b = 1 / rMax := by
    dsimp only [b]
    field_simp [Real.sqrt_ne_zero'.mpr hrMaxPos]
    rw [Real.sq_sqrt hrMaxPos.le]
  have hoptAction (X : Matrix ι ι ℂ) :
      kact Kopt X = (((1 / rMax : ℝ) : ℂ) • (G * X * G)) := by
    simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_one, Kopt,
      Matrix.conjTranspose_smul,
      hGstar, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [← Complex.ofReal_mul, hbsq]
  have hfailPsd :
      (1 - ((1 / rMax : ℝ) : ℂ) • R).PosSemidef := by
    have hscale : (0 : ℂ) ≤ ((1 / rMax : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (div_nonneg zero_le_one hrMaxPos.le)
    have hscaled := hUpper.smul hscale
    convert hscaled using 1
    simp only [smul_sub, smul_smul]
    have hcoef : (((1 / rMax : ℝ) : ℂ) * (rMax : ℂ)) = 1 := by
      exact_mod_cast div_mul_cancel₀ 1 hrMaxPos.ne'
    rw [hcoef, one_smul]
  have hfailStar : Kfailᴴ = Kfail := by
    simpa only [Kfail, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg (1 - ((1 / rMax : ℝ) : ℂ) • R)).isSelfAdjoint.star_eq
  have hfailSq : Kfailᴴ * Kfail =
      1 - ((1 / rMax : ℝ) : ℂ) • R := by
    rw [hfailStar]
    exact CFC.sqrt_mul_sqrt_self _ hfailPsd.nonneg
  have hoptTni : TraceNonincreasing Kopt := by
    unfold TraceNonincreasing
    rw [heffect Kopt (1 / rMax) hoptAction]
    have hscale : (0 : ℂ) ≤ ((1 / rMax : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (div_nonneg zero_le_one hrMaxPos.le)
    have hscaled := hUpper.smul hscale
    convert hscaled using 1
    simp only [smul_sub, smul_smul]
    have hcoef : (((1 / rMax : ℝ) : ℂ) * (rMax : ℂ)) = 1 := by
      exact_mod_cast div_mul_cancel₀ 1 hrMaxPos.ne'
    rw [hcoef, one_smul]
  have hoptContract : ExactPreparationContract R Kopt := by
    intro ρ hρ hρtrace
    have hdenLower := hLowerExpectation ρ hρ hρtrace
    have hdenPos : 0 < (R * ρ).trace.re := lt_of_lt_of_le hrMinPos hdenLower
    have hdenNe : (R * ρ).trace ≠ 0 := fun h => by
      rw [h] at hdenPos
      norm_num at hdenPos
    have htrace : (kact Kopt ρ).trace =
        ((1 / rMax : ℝ) : ℂ) * (R * ρ).trace := by
      rw [hoptAction, Matrix.trace_smul, hGtrace, smul_eq_mul]
    constructor
    · rw [htrace, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_pos (div_pos one_pos hrMaxPos) hdenPos
    constructor
    · rw [hoptAction, Matrix.trace_smul, hGtrace, smul_eq_mul]
      have hquot :
          (((((1 / rMax : ℝ) : ℂ) * (R * ρ).trace) / (R * ρ).trace)) =
            ((1 / rMax : ℝ) : ℂ) := by
        exact mul_div_cancel_right₀ _ hdenNe
      rw [hquot]
    · exact hoptTni
  have hoptLower (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
      (hρtrace : ρ.trace = 1) :
      rMin / rMax ≤ (kact Kopt ρ).trace.re := by
    rw [hoptAction, Matrix.trace_smul, hGtrace]
    norm_num
    rw [div_eq_mul_inv, mul_comm rMax⁻¹]
    exact (div_le_div_iff_of_pos_right hrMaxPos).mpr
      (hLowerExpectation ρ hρ hρtrace)
  have hKoptEffect : (Kopt 0)ᴴ * Kopt 0 =
      ((1 / rMax : ℝ) : ℂ) • R := by
    have h := heffect Kopt (1 / rMax) hoptAction
    simpa only [Fin.sum_univ_one] using h
  have hTP : (Kopt 0)ᴴ * Kopt 0 + Kfailᴴ * Kfail = 1 := by
    rw [hKoptEffect, hfailSq]
    abel
  constructor
  · change ExactPreparationContract R Kopt ∧ TraceNonincreasing Kopt ∧
      (Kopt 0)ᴴ * Kopt 0 + Kfailᴴ * Kfail = 1 ∧
      ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
        rMin / rMax ≤ (kact Kopt ρ).trace.re
    exact ⟨hoptContract, hoptTni, hTP, hoptLower⟩
  · constructor
    · rintro ⟨m, K, hcontract, _, hdet⟩
      obtain ⟨c, hc, haction⟩ := hrigid K hcontract
      have heig (i : ι) : hH.eigenvalues i = 1 / c := by
        have hi := hdet (eigenDensity i) (heigenPsd i) (heigenTrace i)
        rw [haction, Matrix.trace_smul, hGtrace, hReigenTrace] at hi
        have hireal : c * hH.eigenvalues i = 1 := by
          norm_num [smul_eq_mul] at hi
          exact_mod_cast hi
        exact (eq_div_iff hc.ne').mpr (by simpa [mul_comm] using hireal)
      refine ⟨1 / c, div_pos one_pos hc, ?_⟩
      have hD : D = (((1 / c : ℝ) : ℂ) • 1) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [D, heig]
        · simp [D, hij]
      rw [hRspec, hD, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hU]
    · rintro ⟨scalar, hscalar, hRscalar⟩
      have heig (i : ι) : hH.eigenvalues i = scalar := by
        rw [hH.eigenvalues_eq]
        have hm : R *ᵥ (hH.eigenvectorBasis i).ofLp =
            (scalar : ℂ) • (hH.eigenvectorBasis i).ofLp := by
          calc
            R *ᵥ (hH.eigenvectorBasis i).ofLp =
                ((scalar : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ
                  (hH.eigenvectorBasis i).ofLp :=
              congrArg (fun M : Matrix ι ι ℂ =>
                M *ᵥ (hH.eigenvectorBasis i).ofLp) hRscalar
            _ = (scalar : ℂ) • (hH.eigenvectorBasis i).ofLp := by
              rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [hm, dotProduct_smul]
        have hn := hvnorm i
        dsimp only [v] at hn
        rw [hn, smul_eq_mul, mul_one]
        norm_num
      have hrMaxEq : rMax = scalar := by
        dsimp only [rMax, greatestEigenvalue]
        simpa only [heig] using
          (Finset.sup'_const (s := (Finset.univ : Finset ι))
            Finset.univ_nonempty scalar)
      refine ⟨1, Kopt, hoptContract, hoptTni, ?_⟩
      intro ρ hρ hρtrace
      rw [hoptAction, Matrix.trace_smul, hGtrace, hRscalar,
        Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hρtrace, hrMaxEq]
      norm_num
      exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hscalar.ne')

#print axioms exact_conditional_preparation_cost

end D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
