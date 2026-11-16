/- GID: D5/S3/Quantum/Hiai/SupportPowerLimits
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/SupportPowerLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite spectral support decompositions and positive matrix power limits. -/

import D5.S3.Quantum.Hiai.InverseMeanVariational
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Hiai.SupportPowerLimits

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Filter Topology Matrix
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Hiai.InverseMeanVariational
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

theorem cfc_eigenmatrix {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (V : Matrix ι κ ℂ) (lam : κ → ℝ)
    (hAV : A * V = V * diagonal (fun i => (lam i : ℂ))) (f : ℝ → ℝ) :
    hA.cfc f * V = V * diagonal (fun i => (f (lam i) : ℂ)) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hs : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, U]
      using hA.spectral_theorem
  have hR : diagonal (fun i => (hA.eigenvalues i : ℂ)) * (Uᴴ * V) =
      (Uᴴ * V) * diagonal (fun i => (lam i : ℂ)) := by
    have h := congrArg (fun M => Uᴴ * M) hAV
    rw [hs] at h
    simp only [Matrix.mul_assoc] at h
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul] at h
    simpa only [Matrix.mul_assoc] using h
  have hfR : diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (Uᴴ * V) =
      (Uᴴ * V) * diagonal (fun i => (f (lam i) : ℂ)) := by
    ext i j
    have h := congrArg (fun M : Matrix ι κ ℂ => M i j) hR
    simp only [diagonal_mul, mul_diagonal] at h ⊢
    by_cases he : hA.eigenvalues i = lam j
    · rw [he, mul_comm]
    · have hn : (hA.eigenvalues i : ℂ) - (lam j : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast he)
      have hz : (Uᴴ * V) i j = 0 :=
        (mul_eq_zero.mp (show ((hA.eigenvalues i : ℂ) - (lam j : ℂ)) * (Uᴴ * V) i j = 0
          by linear_combination h)).resolve_left hn
      rw [hz, mul_zero, zero_mul]
  have h := congrArg (fun M => U * M) hfR
  simp only [Matrix.mul_assoc] at h
  rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul] at h
  simpa only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose,
    U, Matrix.mul_assoc] using h

lemma support_rpow_shift_tendsto {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {q : ℝ} (hq : q ≠ 0) :
    Tendsto (fun ε : ℝ =>
      cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q) A)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (A ^ q)) := by
  have hscalar : ∀ x : ℝ, x ∈ spectrum ℝ A →
      Tendsto (fun ε : ℝ => if x = 0 then 0 else (x + ε) ^ q)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (x ^ q)) := by
    intro x hx
    by_cases hzero : x = 0
    · simp [hzero, Real.zero_rpow hq]
    · have hx' : 0 < x := by
        rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hzero)
      have hsum : Tendsto (fun ε : ℝ => x + ε)
          (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 x) := by
        have hid : Tendsto (fun ε : ℝ => ε)
            (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
          (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
            nhdsWithin_le_nhds
        simpa only [add_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => x)
            (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 x)).add hid
      simp only [if_neg hzero]
      exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx'))).tendsto.comp hsum
  have hunif : TendstoUniformlyOn
      (fun ε : ℝ => fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q)
      (fun x : ℝ => x ^ q) (𝓝[Set.Ioi (0 : ℝ)] 0) (spectrum ℝ A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    apply A.finite_real_spectrum.eventually_all.mpr
    intro x hx
    simpa [dist_comm] using (Metric.tendsto_nhds.1 (hscalar x hx)) δ hδ
  have hcont (ε : ℝ) :
      ContinuousOn (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q)
        (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn _
  have hc := tendsto_cfc_fun hunif
    (Filter.Eventually.of_forall hcont)
  simpa only [← CFC.rpow_eq_cfc_real hA.nonneg] using hc


lemma kernel_projection_data {A B : Matrix d d ℂ}
    (hA : A.PosSemidef)
    (hker : ∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0) :
    let Q := 1 - spectralSupport A
    Qᴴ = Q ∧ Q * Q = Q ∧ Q.PosSemidef ∧ A * Q = 0 ∧ B * Q = 0 := by
  let Q := 1 - spectralSupport A
  have hQ : Q = cfc (fun x : ℝ => if x = 0 then 1 else 0) A := by
    unfold Q spectralSupport
    rw [← cfc_const_one ℝ A hA.isHermitian.isSelfAdjoint,
      ← cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => if x = 0 then 0 else 1) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  have hsa : Qᴴ = Q := by
    rw [hQ]
    exact (cfc_predicate _ A : IsSelfAdjoint _).star_eq
  have hqq : Q * Q = Q := by
    rw [hQ, ← cfc_mul (fun x : ℝ => if x = 0 then 1 else 0)
      (fun x : ℝ => if x = 0 then 1 else 0) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  have hqpos : Q.PosSemidef := by
    rw [hQ]
    apply Matrix.nonneg_iff_posSemidef.mp
    exact cfc_nonneg (by intro x hx; split_ifs <;> norm_num)
  have haq : A * Q = 0 := by
    conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    rw [hQ, ← cfc_mul (fun x : ℝ => x)
      (fun x : ℝ => if x = 0 then 1 else 0) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    calc
      _ = cfc (fun _ : ℝ => 0) A := by
        apply cfc_congr
        intro x hx
        by_cases h : x = 0 <;> simp [h]
      _ = 0 := cfc_const_zero ℝ A
  have hbq : B * Q = 0 := by
    ext i j
    have ha : A *ᵥ (fun k => Q k j) = 0 := by
      ext k
      exact congrArg (fun M : Matrix d d ℂ => M k j) haq
    have hb := hker (fun k => Q k j) ha
    exact congrFun hb i
  exact ⟨hsa, hqq, hqpos, haq, hbq⟩

lemma rpow_on_eigenmatrix {X V : Matrix d d ℂ}
    (hX : X.PosSemidef) (c q : ℝ) (hXV : X * V = c • V) :
    X ^ q * V = c ^ q • V := by

  let e := Fintype.equivFin d
  let φ : Matrix d d ℂ ≃⋆ₐ[ℝ] Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) ℂ :=
    { __ := Matrix.reindexAlgEquiv ℝ ℂ e
      map_star' := fun M => by rfl
      map_smul' := fun r M => by rfl }
  have hφ : Continuous φ := by
    change Continuous (fun M : Matrix d d ℂ => M.submatrix e.symm e.symm)
    fun_prop
  have hX' : (φ X).IsHermitian := hX.isHermitian.submatrix e.symm
  have hmap : φ (cfc (fun x : ℝ => x ^ q) X) =
      cfc (fun x : ℝ => x ^ q) (φ X) :=
    StarAlgHomClass.map_cfc φ _ X (X.finite_real_spectrum.continuousOn _) hφ
      hX.isHermitian.isSelfAdjoint hX'.isSelfAdjoint
  have hXV' : φ X * φ V = φ V * diagonal (fun _ => (c : ℂ)) := by
    have hdiag : diagonal (fun _ => (c : ℂ)) = c • (1 : Matrix (Fin (Fintype.card d))
        (Fin (Fintype.card d)) ℂ) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, smul_eq_mul]
    rw [← map_mul, hXV, map_smul]
    rw [hdiag, Matrix.mul_smul, Matrix.mul_one]
  have h := cfc_eigenmatrix hX' (φ V) (fun _ => c) hXV' (fun x : ℝ => x ^ q)
  rw [← hX'.cfc_eq] at h
  have hdiag : diagonal (fun _ => ((c ^ q : ℝ) : ℂ)) =
      c ^ q • (1 : Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, smul_eq_mul]
  have heq : φ (X ^ q * V) = φ (c ^ q • V) := by
    rw [map_mul, map_smul, CFC.rpow_eq_cfc_real hX.nonneg, hmap]
    simpa only [hdiag, Matrix.mul_smul, Matrix.mul_one] using h
  exact φ.injective heq

lemma shifted_rpow_formula {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (q : ℝ) :
    (A + ε • (1 : Matrix d d ℂ)) ^ q =
      cfc (fun x : ℝ => (x + ε) ^ q) A := by
  have hpos (x : ℝ) (hx : x ∈ spectrum ℝ A) : 0 < x + ε := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    linarith [hA.eigenvalues_nonneg i]
  have haff : cfc (fun x : ℝ => x + ε) A = A + ε • (1 : Matrix d d ℂ) := by
    rw [cfc_add_const ε (fun x : ℝ => x) A
        (A.finite_real_spectrum.continuousOn _) hA.isHermitian.isSelfAdjoint,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  rw [← haff]
  exact CFC.cfc_rpow hpos (A.finite_real_spectrum.continuousOn _)
    hA.isHermitian.isSelfAdjoint

lemma inverse_shift_split {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (q : ℝ) :
    (A + ε • (1 : Matrix d d ℂ)) ^ q =
      cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q) A +
        ε ^ q • (1 - spectralSupport A) := by
  rw [shifted_rpow_formula hA hε]
  have hQ : 1 - spectralSupport A =
      cfc (fun x : ℝ => if x = 0 then 1 else 0) A := by
    unfold spectralSupport
    rw [← cfc_const_one ℝ A hA.isHermitian.isSelfAdjoint,
      ← cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => if x = 0 then 0 else 1) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  rw [hQ,
    ← cfc_smul (ε ^ q) (fun x : ℝ => if x = 0 then 1 else 0) A
      (A.finite_real_spectrum.continuousOn _),
    ← cfc_add A (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q)
      (fun x : ℝ => ε ^ q • (if x = 0 then 1 else 0))
      (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases h : x = 0 <;> simp [h]

lemma tendsto_positive_rpow {ι : Type*} {l : Filter ι}
    {F : ι → Matrix d d ℂ} {M : Matrix d d ℂ} {q : ℝ}
    (hq : 0 < q) (hM : M.PosSemidef) (hF : ∀ᶠ i in l, (F i).PosSemidef)
    (hlim : Tendsto F l (𝓝 M)) :
    Tendsto (fun i => F i ^ q) l (𝓝 (M ^ q)) := by
  let r : NNReal := ⟨q, hq.le⟩
  have h := (CFC.continuousOn_nnrpow (A := Matrix d d ℂ) r M hM.nonneg).tendsto
  have hl : Tendsto F l (𝓝[Set.Ici 0] M) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hF.mono fun i hi => hi.nonneg⟩
  have hn : Tendsto (fun i => CFC.nnrpow (F i) r) l (𝓝 (CFC.nnrpow M r)) :=
    h.comp hl
  have heq (N : Matrix d d ℂ) : CFC.nnrpow N r = N ^ q :=
    CFC.nnrpow_eq_rpow (a := N) (x := r) (show 0 < r from hq)
  rw [heq M] at hn
  exact hn.congr' (.of_forall fun i => heq (F i))

lemma psd_nested_rpow {A : Matrix d d ℂ} (hA : A.PosSemidef)
    (p q : ℝ) : (A ^ p) ^ q = A ^ (p * q) := by
  rw [CFC.rpow_eq_cfc_real (CFC.rpow_nonneg (a := A) (y := p))]
  simp only [CFC.rpow_eq_cfc_real hA.nonneg]
  rw [← cfc_comp' (fun x : ℝ => x ^ q) (fun x : ℝ => x ^ p) A
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA.isHermitian.isSelfAdjoint]
  · apply cfc_congr
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (Real.rpow_mul (hA.eigenvalues_nonneg i) p q).symm

lemma tendsto_tracePower {ι : Type*} {l : Filter ι}
    {F : ι → Matrix d d ℂ} {M : Matrix d d ℂ} {q : ℝ}
    (hq : 0 < q) (hM : M.PosSemidef) (hF : ∀ᶠ i in l, (F i).PosSemidef)
    (hlim : Tendsto F l (𝓝 M)) :
    Tendsto (fun i => tracePower q (F i)) l (𝓝 (tracePower q M)) := by
  have hpow : Tendsto (fun i => F i ^ q) l (𝓝 (M ^ q)) :=
    tendsto_positive_rpow hq hM hF hlim
  have hc : Continuous (fun N : Matrix d d ℂ => (Matrix.trace N).re) :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  exact hc.continuousAt.tendsto.comp hpow

end D5.S3.Quantum.Hiai.SupportPowerLimits
