/- GID: D5/S3/Quantum/Hiai/GeometricTraceConvexity
   generality: I
   mirror-B: D5/B/S3/Quantum/Hiai/GeometricTraceConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint convexity of Hiai's original CFC geometric trace on supported PSD pairs. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Hiai.InverseGeometricIdentification
import D5.S3.Quantum.Hiai.CarlenLiebConvexity
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

noncomputable section
namespace D5.S3.Quantum.Hiai.GeometricTraceConvexity

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Filter Topology
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open private cfc_eigenmatrix cfc_intertwining from
  D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
open Matrix InverseMeanVariational PsiMeanTraceConcavity GeneralizedPerspectiveFunction
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- Hiai (2.1)/(2.2): the first powered input is the geometric-mean base. -/
def geometricTrace (α p : ℝ) (A B : Matrix d d ℂ) : ℝ :=
  tracePower (1 / p) (geometricMean α (A ^ p) (B ^ p))

/-- The fixed congruence objective used by the inverse variational formula. -/
def variationalObjective (p θ : ℝ) (Z A B : Matrix d d ℂ) : ℝ :=
  2 * tracePower (1 / (2 * p)) (Zᴴ * (B ^ (2 * p)) * Z) - psi p θ Z A B

private lemma mean_posDef {X Y : Matrix d d ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    (θ : ℝ) : (geometricMean θ X Y).PosDef := by
  have hI := hX.isStrictlyPositive.rpow X (-1 / 2)
  have hS := hX.isStrictlyPositive.rpow X (1 / 2)
  have hinner : (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)).PosDef := by
    simpa only [hI.isSelfAdjoint.star_eq] using
      (hI.isUnit.posDef_star_left_conjugate_iff (x := Y)).mpr hY
  have hpower := (hinner.isStrictlyPositive.rpow _ θ).posDef
  simpa only [geometricMean, hS.isSelfAdjoint.star_eq] using
    (hS.isUnit.posDef_star_right_conjugate_iff
      (x := (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)) ^ θ)).mpr hpower

private lemma original_mean_inverse {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (α p : ℝ) :
    geometricMean α (A ^ p) (B ^ p) =
      B ^ p * (geometricMean (α - 1) (B ^ p) (A ^ p))⁻¹ * B ^ p := by
  have hAp := (hA.isStrictlyPositive.rpow A p).posDef
  have hBp := (hB.isStrictlyPositive.rpow B p).posDef
  rw [(InverseGeometricIdentification.geometricMean_identification hAp hBp α).1,
    show 1 - α = -(α - 1) by ring,
    (InverseGeometricIdentification.geometricMean_identification hBp hAp (α - 1)).2,
    Matrix.nonsing_inv_eq_ringInverse]

private lemma objective_identification {A B : Matrix d d ℂ} (hB : B.PosDef)
    (p θ : ℝ) (Z : Matrix d d ℂ) :
    objective (1 / p) (B ^ p) (geometricMean θ (B ^ p) (A ^ p)) Z =
      variationalObjective p θ Z A B := by
  have hsquare : B ^ p * B ^ p = B ^ (2 * p) := by
    rw [← CFC.rpow_add hB.isUnit]
    congr 1
    ring
  have hexponent : (1 / p) / 2 = 1 / (2 * p) := by field_simp
  simp only [objective, variationalObjective, psi, hsquare, hexponent]

private lemma objective_jointly_convex {p θ : ℝ}
    (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (Z : Matrix d d ℂ) (hZ : IsUnit Z) :
    JointlyConvexOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (variationalObjective p θ Z) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hC := CarlenLiebConvexity.fixed_congruence_trace_convex
    (a := 2 * p) ⟨by linarith [hp.1], by linarith [hp.2]⟩ Z hZ
  have hPsi := psi_jointly_concave hp0 hp.2 hθ Z hZ
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hc := hC.2 hB₀ hB₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  have hpsi := hPsi hA₀ hA₁ hB₀ hB₁ ht0 ht1
  simp only [smul_eq_mul] at hc hpsi ⊢
  unfold variationalObjective
  linarith

private lemma variational_formula {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (α : ℝ) {p : ℝ} (hp : 0 < p) :
    ∃ Z₀ : Matrix d d ℂ, IsUnit Z₀ ∧
      variationalObjective p (α - 1) Z₀ A B = geometricTrace α p A B ∧
      ∀ Z : Matrix d d ℂ,
        variationalObjective p (α - 1) Z A B ≤ geometricTrace α p A B := by
  have hAp := (hA.isStrictlyPositive.rpow A p).posDef
  have hBp := (hB.isStrictlyPositive.rpow B p).posDef
  obtain ⟨Z₀, hZ₀, _, heq, hbound⟩ :=
    variational_bound_and_attainment hBp (mean_posDef hBp hAp (α - 1))
      (one_div_pos.mpr hp)
  have htarget : tracePower (1 / p)
      (B ^ p * (geometricMean (α - 1) (B ^ p) (A ^ p))⁻¹ * B ^ p) =
      geometricTrace α p A B := by
    rw [geometricTrace, original_mean_inverse hA hB α p]
  rw [htarget, objective_identification hB p] at heq
  refine ⟨Z₀, hZ₀, heq, fun Z => ?_⟩
  simpa only [htarget, objective_identification hB p] using hbound Z

/-- Joint convexity of the original CFC geometric trace for every finite complex matrix
dimension, including empty, all noncommuting SPD inputs, and both parameter boundaries.
Only the attained optimizer at the mixed point is chosen. -/
theorem geometric_trace_jointly_convex {α p : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2) (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) :
    JointlyConvexOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (geometricTrace α p) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hθ : α - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hdomain := (CarlenLiebConvexity.fixed_congruence_trace_convex
    (d := d) (a := 1) (by norm_num) 1 isUnit_one).1
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hAm := hdomain hA₀ hA₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  have hBm := hdomain hB₀ hB₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  obtain ⟨Zm, hZm, heqm, _⟩ := variational_formula hAm hBm α hp0
  have hc := objective_jointly_convex hp hθ Zm hZm hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hb₀ := (variational_formula hA₀ hB₀ α hp0).elim (fun _ h => h.2.2 Zm)
  have hb₁ := (variational_formula hA₁ hB₁ α hp0).elim (fun _ h => h.2.2 Zm)
  rw [heqm] at hc
  simp only [smul_eq_mul] at hc ⊢
  exact hc.trans (add_le_add
    (mul_le_mul_of_nonneg_left hb₀ (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left hb₁ ht0))

/- The support condition is coupled: it is preserved by mixing two pairs, but
   cannot be represented by separate Cartesian input sets. -/
private lemma support_pair_mix
    {A₀ A₁ B₀ B₁ : Matrix d d ℂ}
    (hA₀ : A₀.PosSemidef) (hA₁ : A₁.PosSemidef)
    (hB₀ : B₀.PosSemidef) (hB₁ : B₁.PosSemidef)
    (hker₀ : ∀ x : d → ℂ, A₀ *ᵥ x = 0 → B₀ *ᵥ x = 0)
    (hker₁ : ∀ x : d → ℂ, A₁ *ᵥ x = 0 → B₁ *ᵥ x = 0)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ((1 - t) • A₀ + t • A₁).PosSemidef ∧
      ((1 - t) • B₀ + t • B₁).PosSemidef ∧
      (∀ x : d → ℂ, ((1 - t) • A₀ + t • A₁) *ᵥ x = 0 →
        ((1 - t) • B₀ + t • B₁) *ᵥ x = 0) := by
  have hA : ((1 - t) • A₀ + t • A₁).PosSemidef :=
    (hA₀.smul (by positivity)).add (hA₁.smul ht₀)
  have hB : ((1 - t) • B₀ + t • B₁).PosSemidef :=
    (hB₀.smul (by positivity)).add (hB₁.smul ht₀)
  refine ⟨hA, hB, ?_⟩
  intro x hx
  by_cases ht : t = 0
  · simpa [ht] using hker₀ x (by simpa [ht] using hx)
  by_cases ht' : t = 1
  · simpa [ht'] using hker₁ x (by simpa [ht'] using hx)
  have htpos : 0 < t := lt_of_le_of_ne ht₀ (Ne.symm ht)
  have hlt : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht₁ ht')
  have hq : star x ⬝ᵥ (((1 - t) • A₀ + t • A₁) *ᵥ x) = 0 :=
    (hA.dotProduct_mulVec_zero_iff (x := x)).mpr hx
  have hq' : (1 - t) * RCLike.re (star x ⬝ᵥ (A₀ *ᵥ x)) +
      t * RCLike.re (star x ⬝ᵥ (A₁ *ᵥ x)) = 0 := by
    have := congrArg RCLike.re hq
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, map_add, map_smul] using this
  have hq₀ : RCLike.re (star x ⬝ᵥ (A₀ *ᵥ x)) = 0 := by
    have h₀ := hA₀.re_dotProduct_nonneg x
    have h₁ := hA₁.re_dotProduct_nonneg x
    nlinarith
  have hq₁ : RCLike.re (star x ⬝ᵥ (A₁ *ᵥ x)) = 0 := by
    have h₀ := hA₀.re_dotProduct_nonneg x
    have h₁ := hA₁.re_dotProduct_nonneg x
    nlinarith
  have hA₀x : A₀ *ᵥ x = 0 := (hA₀.dotProduct_mulVec_zero_iff (x := x)).mp (by
    apply RCLike.ext
    · exact hq₀
    · exact hA₀.isHermitian.im_star_dotProduct_mulVec_self x)
  have hA₁x : A₁ *ᵥ x = 0 := (hA₁.dotProduct_mulVec_zero_iff (x := x)).mp (by
    apply RCLike.ext
    · exact hq₁
    · exact hA₁.isHermitian.im_star_dotProduct_mulVec_self x)
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hker₀ x hA₀x, hker₁ x hA₁x]



private lemma support_rpow_shift_tendsto {A : Matrix d d ℂ} (hA : A.PosSemidef)
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


private lemma kernel_projection_data {A B : Matrix d d ℂ}
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

private lemma rpow_on_eigenmatrix {X V : Matrix d d ℂ}
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

private lemma shifted_rpow_formula {A : Matrix d d ℂ} (hA : A.PosSemidef)
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

private lemma inverse_shift_split {A : Matrix d d ℂ} (hA : A.PosSemidef)
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

private lemma tendsto_positive_rpow {ι : Type*} {l : Filter ι}
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

private lemma psd_nested_rpow {A : Matrix d d ℂ} (hA : A.PosSemidef)
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

private lemma regularized_inner_split {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    let R := cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ (-p / 2)) A
    (A + ε • (1 : Matrix d d ℂ)) ^ (-p / 2) *
      (B + ε • (1 : Matrix d d ℂ)) ^ p *
      (A + ε • (1 : Matrix d d ℂ)) ^ (-p / 2) =
        R * (B + ε • (1 : Matrix d d ℂ)) ^ p * R + (1 - spectralSupport A) := by
  let Q := 1 - spectralSupport A
  let R := cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ (-p / 2)) A
  let W := (B + ε • (1 : Matrix d d ℂ)) ^ p
  obtain ⟨hqs, hqq, hqpos, haq, hbq⟩ := kernel_projection_data hA hker
  have hQ : Q = cfc (fun x : ℝ => if x = 0 then 1 else 0) A := by
    unfold Q spectralSupport
    rw [← cfc_const_one ℝ A hA.isHermitian.isSelfAdjoint,
      ← cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => if x = 0 then 0 else 1) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  have hrq : R * Q = 0 := by
    rw [hQ]
    unfold R
    rw [← cfc_mul _ _ A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    calc
      _ = cfc (fun _ : ℝ => 0) A := by
        apply cfc_congr
        intro x hx
        by_cases h : x = 0 <;> simp [h]
      _ = 0 := cfc_const_zero ℝ A
  have hrs : Rᴴ = R := (cfc_predicate _ A : IsSelfAdjoint R).star_eq
  have hqr : Q * R = 0 := by
    have h := congrArg Matrix.conjTranspose hrq
    simpa [Q, Matrix.conjTranspose_mul, hrs, hqs] using h
  have hBe : (B + ε • (1 : Matrix d d ℂ)).PosSemidef :=
    hB.add (Matrix.PosSemidef.one.smul hε.le)
  have hwq : W * Q = ε ^ p • Q := by
    apply rpow_on_eigenmatrix hBe
    simp [Matrix.add_mul, Matrix.smul_mul, hbq, Q]
  have hwqs : Q * W = ε ^ p • Q := by
    have h := congrArg Matrix.conjTranspose hwq
    have hws : Wᴴ = W := (CFC.rpow_nonneg (a := B + ε • 1) (y := p)).isSelfAdjoint.star_eq
    simpa [Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hqs, hws] using h
  have hrwq : R * W * Q = 0 := by
    rw [Matrix.mul_assoc, hwq, Matrix.mul_smul, hrq, smul_zero]
  have hqwr : Q * W * R = 0 := by
    rw [hwqs, Matrix.smul_mul, hqr, smul_zero]
  have hqwq : Q * W * Q = ε ^ p • Q := by
    rw [hwqs, Matrix.smul_mul, hqq]
  have hc : ε ^ (-p / 2) * ε ^ p * ε ^ (-p / 2) = 1 := by
    rw [← Real.rpow_add hε, ← Real.rpow_add hε]
    have he : -p / 2 + p + -p / 2 = 0 := by ring
    rw [he, Real.rpow_zero]
  simp only [inverse_shift_split hA hε]
  change (R + ε ^ (-p / 2) • Q) * W * (R + ε ^ (-p / 2) • Q) =
    R * W * R + Q
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    hrwq, hqwr, hqwq, smul_zero, zero_add, add_zero, smul_smul]
  rw [show ε ^ (-p / 2) * (ε ^ (-p / 2) * ε ^ p) = 1 by nlinarith [hc], one_smul]


private lemma support_power_sandwich {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) {p : ℝ} (hp : 0 < p) (α : ℝ) :
    let U := A ^ (p / 2)
    let S := A ^ (-p / 2) * B ^ p * A ^ (-p / 2)
    U * (S + (1 - spectralSupport A)) ^ α * U = U * S ^ α * U := by
  let Q := 1 - spectralSupport A
  let P := 1 - Q
  let U := A ^ (p / 2)
  let R := A ^ (-p / 2)
  let S := R * B ^ p * R
  obtain ⟨hqs, hqq, hqpos, haq, hbq⟩ := kernel_projection_data (B := A) hA (fun _ hx => hx)
  have huq : U * Q = 0 := by
    simpa [U, Real.zero_rpow (by positivity : p / 2 ≠ 0)] using
      rpow_on_eigenmatrix hA 0 (p / 2) (by simpa using haq)
  have hrq : R * Q = 0 := by
    simpa [R, Real.zero_rpow (by linarith : -p / 2 ≠ 0)] using
      rpow_on_eigenmatrix hA 0 (-p / 2) (by simpa using haq)
  have hus : Uᴴ = U := (CFC.rpow_nonneg (a := A) (y := p / 2)).isSelfAdjoint.star_eq
  have hrs : Rᴴ = R := (CFC.rpow_nonneg (a := A) (y := -p / 2)).isSelfAdjoint.star_eq
  have hqu : Q * U = 0 := by
    simpa [Q, Matrix.conjTranspose_mul, hus, hqs] using congrArg Matrix.conjTranspose huq
  have hqr : Q * R = 0 := by
    simpa [Q, Matrix.conjTranspose_mul, hrs, hqs] using congrArg Matrix.conjTranspose hrq
  have hsq : S * Q = 0 := by simp [S, Matrix.mul_assoc, hrq]
  have hqs' : Q * S = 0 := by simp [S, ← Matrix.mul_assoc, hqr]
  have hup : U * P = U := by simp [P, Matrix.mul_sub, huq]
  have hpu : P * U = U := by simp [P, Matrix.sub_mul, hqu]
  have hspos : S.PosSemidef := by
    simpa [S, hrs] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B) (y := p))).mul_mul_conjTranspose_same R
  have htpos : (S + Q).PosSemidef := hspos.add hqpos
  have hrel : (S + Q) * P = P * S := by
    calc
      (S + Q) * P = S + Q - Q * Q := by
        simp [P, Matrix.mul_sub, Matrix.add_mul, hsq]
      _ = S := by
        rw [show Q * Q = Q from hqq, add_sub_cancel_right]
      _ = P * S := by
        change S = (1 - Q) * S
        rw [sub_mul, one_mul, hqs', sub_zero]

  let e := Fintype.equivFin d
  let φ : Matrix d d ℂ ≃⋆ₐ[ℝ] Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) ℂ :=
    { __ := Matrix.reindexAlgEquiv ℝ ℂ e
      map_star' := fun M => by rfl
      map_smul' := fun r M => by rfl }
  have hφ : Continuous φ := by
    change Continuous (fun M : Matrix d d ℂ => M.submatrix e.symm e.symm)
    fun_prop
  have hmap (M : Matrix d d ℂ) (hM : M.IsHermitian) :
      φ (cfc (fun x : ℝ => x ^ α) M) = cfc (fun x : ℝ => x ^ α) (φ M) :=
    StarAlgHomClass.map_cfc φ _ M (M.finite_real_spectrum.continuousOn _) hφ
      hM.isSelfAdjoint (hM.submatrix e.symm).isSelfAdjoint
  have ht' : (φ (S + Q)).IsHermitian := htpos.isHermitian.submatrix e.symm
  have hs' : (φ S).IsHermitian := hspos.isHermitian.submatrix e.symm
  have hrel' : φ (S + Q) * φ P = φ P * φ S := by
    rw [← map_mul, ← map_mul, hrel]
  have hi' := cfc_intertwining ht' hs' (φ P) hrel' (fun x : ℝ => x ^ α)
  rw [← Matrix.IsHermitian.cfc_eq, ← Matrix.IsHermitian.cfc_eq] at hi'
  have hi : (S + Q) ^ α * P = P * S ^ α := by
    have heq : φ ((S + Q) ^ α * P) = φ (P * S ^ α) := by
      rw [map_mul, map_mul]
      rw [CFC.rpow_eq_cfc_real htpos.nonneg, CFC.rpow_eq_cfc_real hspos.nonneg]
      rw [hmap (S + Q) htpos.isHermitian, hmap S hspos.isHermitian]
      exact hi'
    exact φ.injective heq
  change U * (S + Q) ^ α * U = U * S ^ α * U
  calc
    _ = U * ((S + Q) ^ α * P) * U := by simp [Matrix.mul_assoc, hpu]
    _ = U * (P * S ^ α) * U := by rw [hi]
    _ = U * S ^ α * U := by rw [← Matrix.mul_assoc, hup]

set_option maxHeartbeats 800000 in
-- The finite-spectrum CFC transport and the two-sided matrix limit elaborate together.
private lemma geometric_mean_regularization_tendsto {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    {α p : ℝ} (hα : 0 < α) (hp : 0 < p) :
    Tendsto (fun ε : ℝ => geometricMean α
      ((A + ε • (1 : Matrix d d ℂ)) ^ p)
      ((B + ε • (1 : Matrix d d ℂ)) ^ p))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (geometricMean α (A ^ p) (B ^ p))) := by
  let Q := 1 - spectralSupport A
  let R (ε : ℝ) :=
    cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ (-p / 2)) A
  let W (ε : ℝ) := (B + ε • (1 : Matrix d d ℂ)) ^ p
  let S (ε : ℝ) := R ε * W ε * R ε + Q
  let U (ε : ℝ) := (A + ε • (1 : Matrix d d ℂ)) ^ (p / 2)
  let R₀ := A ^ (-p / 2)
  let U₀ := A ^ (p / 2)
  let S₀ := R₀ * B ^ p * R₀ + Q
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hadd (M : Matrix d d ℂ) :
      Tendsto (fun ε : ℝ => M + ε • (1 : Matrix d d ℂ))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 M) := by
    have hconst : Tendsto (fun _ : ℝ => M) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 M) :=
      tendsto_const_nhds
    have hone : Tendsto (fun _ : ℝ => (1 : Matrix d d ℂ))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (1 : Matrix d d ℂ)) := tendsto_const_nhds
    simpa using hconst.add (he.smul hone)
  have hshift (M : Matrix d d ℂ) (hM : M.PosSemidef) :
      ∀ᶠ (ε : ℝ) in (𝓝[Set.Ioi (0 : ℝ)] 0), (M + ε • (1 : Matrix d d ℂ)).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hM.add (Matrix.PosSemidef.one.smul (le_of_lt hε))
  have hR : Tendsto R (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 R₀) :=
    support_rpow_shift_tendsto hA (by linarith)
  have hW : Tendsto W (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (B ^ p)) :=
    tendsto_positive_rpow hp hB (hshift B hB) (hadd B)
  have hU : Tendsto U (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 U₀) :=
    tendsto_positive_rpow (by positivity) hA (hshift A hA) (hadd A)
  have hS : Tendsto S (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 S₀) :=
    ((hR.mul hW).mul hR).add_const Q
  obtain ⟨hqs, hqq, hqpos, haq, hbq⟩ := kernel_projection_data hA hker
  have hSpos : ∀ᶠ (ε : ℝ) in (𝓝[Set.Ioi (0 : ℝ)] 0), (S ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hr : (R ε)ᴴ = R ε := (cfc_predicate _ A : IsSelfAdjoint (R ε)).star_eq
    have hw : (W ε).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    exact (by simpa [S, hr] using (hw.mul_mul_conjTranspose_same (R ε)).add hqpos)
  have hS₀pos : S₀.PosSemidef := by
    have hr : R₀ᴴ = R₀ := (CFC.rpow_nonneg (a := A) (y := -p / 2)).isSelfAdjoint.star_eq
    have hw : (B ^ p).PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    simpa [S₀, hr] using (hw.mul_mul_conjTranspose_same R₀).add hqpos
  have hpow := tendsto_positive_rpow hα hS₀pos hSpos hS
  have hlim := (hU.mul hpow).mul hU
  have heq : ∀ᶠ (ε : ℝ) in (𝓝[Set.Ioi (0 : ℝ)] 0),
      geometricMean α ((A + ε • (1 : Matrix d d ℂ)) ^ p)
        ((B + ε • (1 : Matrix d d ℂ)) ^ p) = U ε * (S ε) ^ α * U ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAe : (A + ε • (1 : Matrix d d ℂ)).PosSemidef :=
      hA.add (Matrix.PosSemidef.one.smul (le_of_lt hε))
    simp only [geometricMean, psd_nested_rpow hAe]
    simp only [show p * (1 / 2 : ℝ) = p / 2 by ring,
      show p * (-1 / 2 : ℝ) = -p / 2 by ring]
    rw [regularized_inner_split hA hB hker hε]
  have htarget : U₀ * S₀ ^ α * U₀ = geometricMean α (A ^ p) (B ^ p) := by
    rw [support_power_sandwich hA hp]
    simp only [geometricMean, psd_nested_rpow hA]
    simp [U₀, R₀, S₀, show p * (1 / 2 : ℝ) = p / 2 by ring,
      show p * (-1 / 2 : ℝ) = -p / 2 by ring]
    ring_nf
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [heq] with ε hε
  exact hε.symm


private lemma mean_posSemidef (X Y : Matrix d d ℂ) (α : ℝ) : (geometricMean α X Y).PosSemidef := by
  have hs : (X ^ (1 / 2 : ℝ))ᴴ = X ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg (a := X) (y := 1 / 2)).isSelfAdjoint.star_eq
  have hpow : ((X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)) ^ α).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have h := hpow.mul_mul_conjTranspose_same (X ^ (1 / 2 : ℝ))
  rw [geometricMean]
  rw [hs] at h
  exact h

private lemma tendsto_tracePower {ι : Type*} {l : Filter ι}
    {F : ι → Matrix d d ℂ} {M : Matrix d d ℂ} {q : ℝ}
    (hq : 0 < q) (hM : M.PosSemidef) (hF : ∀ᶠ i in l, (F i).PosSemidef)
    (hlim : Tendsto F l (𝓝 M)) :
    Tendsto (fun i => tracePower q (F i)) l (𝓝 (tracePower q M)) := by
  have hpow : Tendsto (fun i => F i ^ q) l (𝓝 (M ^ q)) :=
    tendsto_positive_rpow hq hM hF hlim
  have hc : Continuous (fun N : Matrix d d ℂ => (Matrix.trace N).re) :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  exact hc.continuousAt.tendsto.comp hpow

private lemma geometric_trace_regularization_tendsto {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    {α p : ℝ} (hα : 0 < α) (hp : 0 < p) :
    Tendsto (fun ε : ℝ => geometricTrace α p
      (A + ε • (1 : Matrix d d ℂ)) (B + ε • (1 : Matrix d d ℂ)))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (geometricTrace α p A B)) := by
  apply tendsto_tracePower (one_div_pos.mpr hp)
  · exact mean_posSemidef (A ^ p) (B ^ p) α
  · exact .of_forall fun ε => mean_posSemidef
      ((A + ε • (1 : Matrix d d ℂ)) ^ p)
      ((B + ε • (1 : Matrix d d ℂ)) ^ p) α
  · exact geometric_mean_regularization_tendsto hA hB hker hα hp


/-- PSD pairs with the second input supported on the first input's support. -/
def supportPairDomain : Set (Matrix d d ℂ × Matrix d d ℂ) :=
  {z | z.1.PosSemidef ∧ z.2.PosSemidef ∧
    ∀ x : d → ℂ, z.1 *ᵥ x = 0 → z.2 *ᵥ x = 0}

private lemma geometric_trace_support_convex_of_regularization
    {α p : ℝ} (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hreg : ∀ {A B : Matrix d d ℂ}, A.PosSemidef → B.PosSemidef →
      (∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0) →
      Tendsto (fun ε : ℝ => geometricTrace α p
        (A + ε • (1 : Matrix d d ℂ)) (B + ε • (1 : Matrix d d ℂ)))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (geometricTrace α p A B))) :
    ConvexOn ℝ supportPairDomain
      (fun z : Matrix d d ℂ × Matrix d d ℂ => geometricTrace α p z.1 z.2) := by
  refine ⟨?_, ?_⟩
  · intro z₀ hz₀ z₁ hz₁ a b ha hb hab
    obtain ⟨hA, hB, hk⟩ := support_pair_mix hz₀.1 hz₁.1 hz₀.2.1 hz₁.2.1
      hz₀.2.2 hz₁.2.2 hb (by linarith)
    have hea : a = 1 - b := by linarith
    simpa [supportPairDomain, hea] using And.intro hA (And.intro hB hk)
  intro z₀ hz₀ z₁ hz₁ a b ha hb hab
  rcases hz₀ with ⟨hA₀, hB₀, hker₀⟩
  rcases hz₁ with ⟨hA₁, hB₁, hker₁⟩
  have ht₁ : b ≤ 1 := by linarith
  have hea : a = 1 - b := by linarith
  let Aₘ := (1 - b) • z₀.1 + b • z₁.1
  let Bₘ := (1 - b) • z₀.2 + b • z₁.2
  obtain ⟨hAm, hBm, hkerm⟩ :=
    support_pair_mix hA₀ hA₁ hB₀ hB₁ hker₀ hker₁ hb ht₁
  have hpd (X : Matrix d d ℂ) (hX : X.PosSemidef) (ε : ℝ) (hε : 0 < ε) :
      (X + ε • (1 : Matrix d d ℂ)).PosDef := by
    exact (Matrix.PosDef.one.smul hε).posSemidef_add hX
  have hineq : ∀ᶠ (ε : ℝ) in (𝓝[Set.Ioi (0 : ℝ)] 0),
      geometricTrace α p (Aₘ + ε • (1 : Matrix d d ℂ))
        (Bₘ + ε • (1 : Matrix d d ℂ)) ≤
      (1 - b) * geometricTrace α p (z₀.1 + ε • (1 : Matrix d d ℂ))
          (z₀.2 + ε • (1 : Matrix d d ℂ)) +
        b * geometricTrace α p (z₁.1 + ε • (1 : Matrix d d ℂ))
          (z₁.2 + ε • (1 : Matrix d d ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hspd : JointlyConvexOn {A : Matrix d d ℂ | A.PosDef}
        {B : Matrix d d ℂ | B.PosDef} (geometricTrace α p) :=
      geometric_trace_jointly_convex hα hp
    have h0 := hspd
      (A₁ := z₀.1 + ε • (1 : Matrix d d ℂ))
      (A₂ := z₁.1 + ε • (1 : Matrix d d ℂ))
      (B₁ := z₀.2 + ε • (1 : Matrix d d ℂ))
      (B₂ := z₁.2 + ε • (1 : Matrix d d ℂ)) (θ := b)
      (hpd _ hA₀ ε hε) (hpd _ hA₁ ε hε)
      (hpd _ hB₀ ε hε) (hpd _ hB₁ ε hε) hb ht₁
    have hm (M N : Matrix d d ℂ) :
        (1 - b) • (M + ε • 1) + b • (N + ε • 1) =
          (1 - b) • M + b • N + ε • 1 := by module
    rw [hm, hm] at h0
    simpa only [smul_eq_mul] using h0
  have hL := (hreg hA₀ hB₀ hker₀).const_mul (1 - b) |>.add
    ((hreg hA₁ hB₁ hker₁).const_mul b)
  have hR : Tendsto
      (fun ε : ℝ => geometricTrace α p (Aₘ + ε • (1 : Matrix d d ℂ))
        (Bₘ + ε • (1 : Matrix d d ℂ)))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (geometricTrace α p Aₘ Bₘ)) :=
    hreg hAm hBm hkerm
  have hlim := le_of_tendsto_of_tendsto hR hL hineq
  simpa [hea, Aₘ, Bₘ, smul_eq_mul, Pi.smul_apply] using hlim


/-- Hiai's original geometric trace is convex on the coupled PSD support domain,
with the finite-spectrum Moore–Penrose power convention and both closed parameter intervals. -/
theorem geometric_trace_support_convex {α p : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2) (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ConvexOn ℝ supportPairDomain
      (fun z : Matrix d d ℂ × Matrix d d ℂ => geometricTrace α p z.1 z.2) := by
  apply geometric_trace_support_convex_of_regularization hα hp
  intro A B hA hB hker
  exact geometric_trace_regularization_tendsto hA hB hker
    (by linarith [hα.1]) (by linarith [hp.1])

#print axioms geometric_trace_support_convex
#print axioms geometric_trace_jointly_convex
end D5.S3.Quantum.Hiai.GeometricTraceConvexity
