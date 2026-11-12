/- GID: D5/S3/Quantum/Schatten/Partition
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/Partition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full finite complex Schatten partition inequality from Carlen-Lieb convexity. -/

import D5.S3.Quantum.Hiai.CarlenLiebConvexity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Sra, arXiv:2610.15889v1, Theorem 1.2. Published mathematics; originalKPI=0.
Alternative proof: degree-one Carlen-Lieb convexity gives subadditivity of
Re Tr((Z* A^q Z)^(1/q)), 1<=q<=2. Positive regularization extends the trace
inequality to the PSD cone. Taking q=2/p and Z=sqrt(H^(-1/p)XX*H^(-1/p))
gives the partition inequality, including arbitrary rectangular X. No
Schatten interpolation premise or operator-valued concavity is used.

Admission: escape-witness. The new consumed analytic supplier is homogeneous
trace-root subadditivity on the full PSD cone. CFC scaling, the regularized
limit and the rectangular Gram reconstruction are on its live proof path.
-/

noncomputable section
open Matrix Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace D5.S3.Quantum.Schatten.Partition

open D5.S3.Quantum.Hiai
open InverseMeanVariational

variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private lemma rpow_smul {A : Matrix d d ℂ} (hA : A.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (q : ℝ) : (c • A) ^ q = c ^ q • (A ^ q) := by
  rw [CFC.rpow_eq_cfc_real (smul_nonneg hc hA.nonneg),
    ← cfc_comp_smul c (fun x : ℝ => x ^ q) A
      ((A.finite_real_spectrum.image (fun x : ℝ => c • x)).continuousOn _)
      hA.isHermitian.isSelfAdjoint,
    CFC.rpow_eq_cfc_real hA.nonneg, ← cfc_smul (c ^ q) (fun x : ℝ => x ^ q) A
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow hc (spectrum_nonneg_of_nonneg hA.nonneg hx)

/-- The homogeneous fixed-congruence trace-root functional. -/
def rootTrace (q : ℝ) (Z A : Matrix d d ℂ) : ℝ :=
  tracePower (1 / q) (Zᴴ * (A ^ q) * Z)

private lemma rootTrace_smul {A : Matrix d d ℂ} (hA : A.PosSemidef)
    (Z : Matrix d d ℂ) {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    rootTrace q Z (c • A) = c * rootTrace q Z A := by
  have hG : (Zᴴ * (A ^ q) * Z).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).conjTranspose_mul_mul_same Z
  unfold rootTrace tracePower
  rw [rpow_smul hA c hc.le, Matrix.mul_smul, Matrix.smul_mul,
    rpow_smul hG (c ^ q) (Real.rpow_nonneg hc.le _) (1 / q),
    ← Real.rpow_mul hc.le, mul_one_div_cancel hq.ne', Real.rpow_one,
    Matrix.trace_smul]
  simp

private lemma rootTrace_add_posDef {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (Z : Matrix d d ℂ) (hZ : IsUnit Z)
    {q : ℝ} (hq : q ∈ Set.Icc 1 2) :
    rootTrace q Z (A + B) ≤ rootTrace q Z A + rootTrace q Z B := by
  have h := (CarlenLiebConvexity.fixed_congruence_trace_convex hq Z hZ).2
    hA hB (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  change rootTrace q Z ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B) ≤
    (1 / 2 : ℝ) * rootTrace q Z A + (1 / 2 : ℝ) * rootTrace q Z B at h
  rw [← smul_add, rootTrace_smul (hA.add hB).posSemidef Z
    (by linarith [hq.1]) (by norm_num : (0 : ℝ) < 1 / 2)] at h
  linarith

set_option backward.isDefEq.respectTransparency false in
private lemma rootTrace_tendsto {α : Type*} {l : Filter α}
    {A Z : Matrix d d ℂ} {As Zs : α → Matrix d d ℂ}
    (hA : A.PosSemidef) (hAs : ∀ᶠ i in l, (As i).PosSemidef)
    (hlimA : Tendsto As l (𝓝 A)) (hlimZ : Tendsto Zs l (𝓝 Z))
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun i => rootTrace q (Zs i) (As i)) l (𝓝 (rootTrace q Z A)) := by
  have hcont {r : ℝ} (hr : 0 < r) :
      ContinuousOn (fun N : Matrix d d ℂ => N ^ r) {N | N.PosSemidef} := by
    let rn : NNReal := ⟨r, hr.le⟩
    have hrn : 0 < rn := hr
    have h := CFC.continuousOn_nnrpow (A := Matrix d d ℂ) rn
    simp only [Matrix.nonneg_iff_posSemidef] at h
    convert! h using 1
    funext N
    exact (CFC.nnrpow_eq_rpow (a := N) hrn).symm
  have hpow := (hcont hq A hA).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlimA, hAs⟩)
  have hstar : Tendsto (fun i => (Zs i)ᴴ) l (𝓝 Zᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose] using hlimZ.star
  have hinner := (hstar.mul hpow).mul hlimZ
  have hpos : (Zᴴ * (A ^ q) * Z).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).conjTranspose_mul_mul_same Z
  have hpowers := (hcont (one_div_pos.mpr hq) _ hpos).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hinner, .of_forall fun i =>
      (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).conjTranspose_mul_mul_same (Zs i)⟩)
  exact (Complex.continuous_re.comp continuous_id.matrix_trace).continuousAt.tendsto.comp hpowers

/-- Subadditivity on the full PSD cone, retaining singular congruence and empty dimension. -/
theorem rootTrace_add {A B Z : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hZ : Z.PosSemidef)
    {q : ℝ} (hq : q ∈ Set.Icc 1 2) :
    rootTrace q Z (A + B) ≤ rootTrace q Z A + rootTrace q Z B := by
  let R := fun (M : Matrix d d ℂ) (ε : ℝ) => M + ε • (1 : Matrix d d ℂ)
  have hpd (M : Matrix d d ℂ) (hM : M.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
      (R M ε).PosDef := Matrix.PosDef.posSemidef_add hM (Matrix.PosDef.one.smul hε)
  have hlim (M : Matrix d d ℂ) : Tendsto (R M) (𝓝[Set.Ioi 0] 0) (𝓝 M) := by
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi 0] 0) (𝓝 0) :=
      tendsto_id'.mpr inf_le_left
    have hc : Tendsto (fun _ : ℝ => M) (𝓝[Set.Ioi 0] 0) (𝓝 M) := tendsto_const_nhds
    simpa only [zero_smul, add_zero] using hc.add (ht.smul_const (1 : Matrix d d ℂ))
  have hpsd (M : Matrix d d ℂ) (hM : M.PosSemidef) :
      ∀ᶠ ε in (𝓝[Set.Ioi (0 : ℝ)] 0), (R M ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hpd M hM hε).posSemidef
  have he : ∀ᶠ ε in (𝓝[Set.Ioi (0 : ℝ)] 0),
      rootTrace q (R Z ε) (R A ε + R B ε) ≤
        rootTrace q (R Z ε) (R A ε) + rootTrace q (R Z ε) (R B ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact rootTrace_add_posDef (hpd A hA hε) (hpd B hB hε)
      (R Z ε) (hpd Z hZ hε).isUnit hq
  have hq0 : 0 < q := by linarith [hq.1]
  exact le_of_tendsto_of_tendsto
    (rootTrace_tendsto (hA.add hB)
      (((hpsd A hA).and (hpsd B hB)).mono fun _ hi => hi.1.add hi.2)
      ((hlim A).add (hlim B)) (hlim Z) hq0)
    ((rootTrace_tendsto hA (hpsd A hA) (hlim A) (hlim Z) hq0).add
      (rootTrace_tendsto hB (hpsd B hB) (hlim B) (hlim Z) hq0)) he

/-- Finite PSD trace-root subadditivity, with arbitrary finite families including empty ones. -/
theorem rootTrace_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix d d ℂ)
    (hA : ∀ j ∈ s, (A j).PosSemidef) {Z : Matrix d d ℂ} (hZ : Z.PosSemidef)
    {q : ℝ} (hq : q ∈ Set.Icc 1 2) :
    rootTrace q Z (∑ j ∈ s, A j) ≤ ∑ j ∈ s, rootTrace q Z (A j) := by
  classical
  have hq0 : q ≠ 0 := by linarith [hq.1]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (Matrix.trace (CFC.rpow (Zᴴ * CFC.rpow 0 q * Z) (1 / q))).re ≤ 0
    rw [CFC.zero_rpow (A := Matrix d d ℂ) hq0, Matrix.mul_zero, Matrix.zero_mul,
      CFC.zero_rpow (A := Matrix d d ℂ) (one_div_ne_zero hq0)]
    simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : (∑ i ∈ s, A i).PosSemidef := by
      exact Matrix.posSemidef_sum s (fun i hi => hA i (Finset.mem_insert_of_mem hi))
    exact (rootTrace_add (hA j (Finset.mem_insert_self _ _)) hs hZ hq).trans
      (add_le_add le_rfl (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))))

/-- Actual rectangular Schatten functional, expressed through its row Gram square root.
Its pth power is Tr(XX*)^(p/2); zero singular values are retained. -/
def rectangularNorm {c : Type*} [Fintype c] (X : Matrix d c ℂ) (p : ℝ) : ℝ :=
  schattenNorm (CFC.sqrt (X * Xᴴ)) p

lemma rectangularNorm_rpow {c : Type*} [Fintype c]
    (X : Matrix d c ℂ) {p : ℝ} (hp : 0 < p) :
    rectangularNorm X p ^ p = tracePower (p / 2) (X * Xᴴ) := by
  rw [rectangularNorm, norm_rpow_gram _ hp]
  have hS : (CFC.sqrt (X * Xᴴ))ᴴ = CFC.sqrt (X * Xᴴ) :=
    (CFC.sqrt_nonneg (X * Xᴴ)).isSelfAdjoint.star_eq
  rw [hS, CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose X).nonneg]

private lemma rectangularNorm_square (X : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    rectangularNorm X p = schattenNorm X p := by
  apply (Real.rpow_left_inj (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _) hp.ne').mp
  change rectangularNorm X p ^ p = schattenNorm X p ^ p
  rw [rectangularNorm_rpow X hp, norm_rpow_rowGram X hp]

private lemma square_power {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) : A ^ r * A ^ r = A ^ (2 * r) := by
  calc
    _ = (A ^ r) ^ (2 : ℕ) := (pow_two _).symm
    _ = CFC.rpow (A ^ r) 2 := (CFC.rpow_natCast (A ^ r) 2).symm
    _ = A ^ (r * 2) := CFC.rpow_rpow_of_exponent_nonneg A r 2 hr (by norm_num) hA.nonneg
    _ = A ^ (2 * r) := by congr 1; ring

private lemma rootTrace_as_gram {A M : Matrix d d ℂ}
    (hA : A.PosSemidef) (hM : M.PosSemidef) {p : ℝ} (hp : 0 < p) :
    rootTrace (2 / p) (CFC.sqrt M) A =
      tracePower (p / 2) (A ^ (1 / p) * M * A ^ (1 / p)) := by
  let T := A ^ (1 / p) * CFC.sqrt M
  have hS : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  have hP : (A ^ (1 / p))ᴴ = A ^ (1 / p) := CFC.rpow_nonneg.isSelfAdjoint.star_eq
  have hnorm := (norm_rpow_gram T hp).symm.trans (norm_rpow_rowGram T hp)
  have hAA : A ^ (1 / p) * A ^ (1 / p) = A ^ (2 / p) := by
    convert square_power hA (show 0 ≤ 1 / p by positivity) using 1
    congr 1
    ring
  have hG : Tᴴ * T = CFC.sqrt M * A ^ (2 / p) * CFC.sqrt M := by
    simp only [T, Matrix.conjTranspose_mul, hS, hP]
    calc
      _ = CFC.sqrt M * (A ^ (1 / p) * A ^ (1 / p)) * CFC.sqrt M := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAA]
  have hR : T * Tᴴ = A ^ (1 / p) * M * A ^ (1 / p) := by
    simp only [T, Matrix.conjTranspose_mul, hS, hP]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt M),
      CFC.sqrt_mul_sqrt_self M hM.nonneg]
    simp only [Matrix.mul_assoc]
  rw [hG, hR] at hnorm
  simpa only [rootTrace, hS, one_div_div] using hnorm

/-- Sra Theorem 1.2 for every compatible rectangular complex matrix and every
real 1<=p<=2. PSD summands may be singular; all index types may be empty. -/
theorem partition_rectangular {ι c : Type*} [Fintype ι] [Fintype c]
    (Hj : ι → Matrix d d ℂ) (hHj : ∀ j, (Hj j).PosSemidef)
    (hH : (∑ j, Hj j).PosDef) (X : Matrix d c ℂ)
    {p : ℝ} (hp : p ∈ Set.Icc 1 2) :
    rectangularNorm X p ^ p ≤
      ∑ j, rectangularNorm (Hj j ^ (1 / p) * (∑ j, Hj j) ^ (-(1 / p)) * X) p ^ p := by
  let H := ∑ j, Hj j
  let K := H ^ (-(1 / p))
  let M := K * (X * Xᴴ) * K
  have hp0 : 0 < p := by linarith [hp.1]
  have hK : Kᴴ = K := CFC.rpow_nonneg.isSelfAdjoint.star_eq
  have hM : M.PosSemidef := by
    simpa only [M, hK] using
      (Matrix.posSemidef_self_mul_conjTranspose X).mul_mul_conjTranspose_same K
  have hq : 2 / p ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hp0).mpr (by simpa using hp.2)
    · exact (div_le_iff₀ hp0).mpr (by linarith [hp.1])
  have h := rootTrace_sum Finset.univ Hj (fun j _ => hHj j)
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)) hq
  rw [rootTrace_as_gram hH.posSemidef hM hp0] at h
  simp_rw [rootTrace_as_gram (hHj _) hM hp0] at h
  have hcancel : H ^ (1 / p) * K = 1 := CFC.rpow_mul_rpow_neg (1 / p) hH.isStrictlyPositive
  have hcancel' : K * H ^ (1 / p) = 1 := CFC.rpow_neg_mul_rpow (1 / p) hH.isStrictlyPositive
  have hcenter : H ^ (1 / p) * M * H ^ (1 / p) = X * Xᴴ := by
    calc
      _ = (H ^ (1 / p) * K) * (X * Xᴴ) * (K * H ^ (1 / p)) := by
        simp only [M, Matrix.mul_assoc]
      _ = X * Xᴴ := by rw [hcancel, hcancel', Matrix.one_mul, Matrix.mul_one]
  rw [hcenter, ← rectangularNorm_rpow X hp0] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [rectangularNorm_rpow _ hp0]
  congr 1
  have hP : (Hj j ^ (1 / p))ᴴ = Hj j ^ (1 / p) :=
    CFC.rpow_nonneg.isSelfAdjoint.star_eq
  change (Hj j ^ (1 / p) * K * X) * (Hj j ^ (1 / p) * K * X)ᴴ =
    Hj j ^ (1 / p) * M * Hj j ^ (1 / p)
  simp only [Matrix.conjTranspose_mul, hK, hP, M, Matrix.mul_assoc]

/-- The full square-matrix statement in the existing, attributed Schatten functional. -/
theorem partition {ι : Type*} [Fintype ι]
    (Hj : ι → Matrix d d ℂ) (hHj : ∀ j, (Hj j).PosSemidef)
    (hH : (∑ j, Hj j).PosDef) (X : Matrix d d ℂ)
    {p : ℝ} (hp : p ∈ Set.Icc 1 2) :
    schattenNorm X p ^ p ≤
      ∑ j, schattenNorm (Hj j ^ (1 / p) * (∑ j, Hj j) ^ (-(1 / p)) * X) p ^ p := by
  have hp0 : 0 < p := by linarith [hp.1]
  have h := partition_rectangular Hj hHj hH X hp
  simp (config := { singlePass := true }) only [rectangularNorm_square _ hp0] at h
  exact h

#print axioms rootTrace_add
#print axioms rootTrace_sum
#print axioms partition_rectangular
#print axioms partition

end D5.S3.Quantum.Schatten.Partition
