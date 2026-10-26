/- GID: D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim; result=D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result; claim=D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim
   digest: One qubit measurement permits one-copy pseudo-broadcasting but is contextual. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Measurements.VisibleStateSpaceDimension

/-! One finite qubit measurement generates a contextual one-copy pseudo-broadcastable subtheory. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

namespace D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation

def Subtheory {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  Convex ℝ t ∧ (∀ ρ ∈ t, IsDensity ρ) ∧ Convex ℝ a ∧
    (∀ e ∈ a, e.PosSemidef ∧ (1 - e).PosSemidef) ∧
    1 ∈ a ∧ ∀ e ∈ a, 1 - e ∈ a

def postprocessings {d m : ℕ} (p : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    Set (Matrix (Fin d) (Fin d) ℂ) :=
  {e | ∃ c : Fin m → ℝ, (∀ o, 0 ≤ c o ∧ c o ≤ 1) ∧ e = ∑ o, (c o : ℂ) • p o}

def GeneratedBy {d : ℕ} (a : Set (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) : Prop :=
  ∃ (m : Fin k → ℕ) (p : ∀ j, Fin (m j) → Matrix (Fin d) (Fin d) ℂ),
    (∀ j, IsPOVM (p j)) ∧ a = convexHull ℝ (⋃ j, postprocessings (p j))

def partialTraceKeep {d n : ℕ} (i : Fin n)
    (x : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (x.submatrix
    (fun z : Fin d × ({j : Fin n // j ≠ i} → Fin d) =>
      fun j => if h : j = i then z.1 else z.2 ⟨j, h⟩)
    (fun z : Fin d × ({j : Fin n // j ≠ i} → Fin d) =>
      fun j => if h : j = i then z.1 else z.2 ⟨j, h⟩))

def PseudoBroadcastable {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) (n : ℕ) :
    Prop :=
  ∃ ξ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
    (∀ x, (ξ x).trace = x.trace) ∧
    (∀ i, ∀ ρ ∈ t, ∀ e ∈ a, (e * partialTraceKeep i (ξ ρ)).trace = (e * ρ).trace) ∧
    ∀ ρ ∈ t, ∀ e : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, e i ∈ a) → 0 ≤ (ξ ρ * productMap (fun _ => Fin d) e).trace

def Noncontextual {d : ℕ} (t a : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∃ (ι : Type) (g s : ι → Matrix (Fin d) (Fin d) ℂ),
    (∀ l, ∀ ρ ∈ t, 0 ≤ (ρ * g l).trace) ∧
    (∀ ρ ∈ t, HasSum (fun l => (ρ * g l).trace) 1) ∧
    (∀ l, ∀ e ∈ a, 0 ≤ (s l * e).trace) ∧ (∀ l, (s l).trace = 1) ∧
    ∀ ρ ∈ t, ∀ e ∈ a,
      HasSum (fun l => (ρ * g l).trace * (s l * e).trace) (ρ * e).trace

def claim : Prop :=
  ∀ (d k : ℕ) (t a : Set (Matrix (Fin d) (Fin d) ℂ)),
    Subtheory t a → GeneratedBy a k → (PseudoBroadcastable t a k ↔ Noncontextual t a)

private def rho (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 10 : ℝ) • Matrix.vecMulVec
    (![![3, 1], ![1, 3], ![3, -1], ![1, -3]] j : Fin 2 → ℂ)
    (star (![![3, 1], ![1, 3], ![3, -1], ![1, -3]] j : Fin 2 → ℂ))

private def measurement (o : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (![1 / 4, 1 / 4, 1 / 2, 1 / 2] o : ℝ) • Matrix.vecMulVec
    (![![1, 1], ![1, -1], ![1, 0], ![0, 1]] o : Fin 2 → ℂ)
    (star (![![1, 1], ![1, -1], ![1, 0], ![0, 1]] o : Fin 2 → ℂ))

private def preparations : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  convexHull ℝ (Set.range rho)

private def effects : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  convexHull ℝ (postprocessings measurement)

private lemma rho_density (j : Fin 4) : IsDensity (rho j) := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 10), ?_⟩
  fin_cases j <;>
    simp only [rho, Matrix.trace_fin_two, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] <;> norm_num [Complex.real_smul]

private lemma measurement_povm : IsPOVM measurement := by
  constructor
  · intro o
    apply (Matrix.posSemidef_vecMulVec_self_star _).smul
    fin_cases o <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [measurement, Fin.sum_univ_succ, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Matrix.sum_apply, Complex.real_smul]

private lemma postprocessings_convex {d m : ℕ}
    (p : Fin m → Matrix (Fin d) (Fin d) ℂ) : Convex ℝ (postprocessings p) := by
  let F : (Fin m → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    ∑ o, (LinearMap.proj o).smulRight (p o)
  convert (convex_Icc (0 : Fin m → ℝ) 1).linear_image F using 1
  ext e
  simp only [Set.mem_image, Set.mem_Icc, Pi.le_def,
    Pi.zero_apply, Pi.one_apply, ← forall_and]
  refine exists_congr fun c => ?_
  simp only [F, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have heq : (∑ o, c o • p o) = ∑ o, (c o : ℂ) • p o := by
    apply Finset.sum_congr rfl
    intro o _
    exact (algebraMap_smul ℂ (c o) (p o)).symm
  rw [heq]
  exact and_congr_right fun _ => eq_comm

private lemma postprocessings_complement {d m : ℕ}
    {p : Fin m → Matrix (Fin d) (Fin d) ℂ} (hp : IsPOVM p)
    {e : Matrix (Fin d) (Fin d) ℂ} (he : e ∈ postprocessings p) :
    1 - e ∈ postprocessings p := by
  rcases he with ⟨c, hc, rfl⟩
  refine ⟨fun o => 1 - c o, fun o => Set.Icc.one_sub_mem (hc o), ?_⟩
  rw [← hp.2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]

private lemma postprocessings_positive {d m : ℕ}
    {p : Fin m → Matrix (Fin d) (Fin d) ℂ} (hp : IsPOVM p)
    {e : Matrix (Fin d) (Fin d) ℂ} (he : e ∈ postprocessings p) : e.PosSemidef := by
  rcases he with ⟨c, hc, rfl⟩
  exact Matrix.posSemidef_sum _ (fun o _ => (hp.1 o).smul
    (Complex.real_le_real.mpr (hc o).1))

private lemma measurement_member (o : Fin 4) : measurement o ∈ effects := by
  apply subset_convexHull ℝ _
  refine ⟨fun j => if j = o then 1 else 0, fun j => ?_, ?_⟩
  · by_cases h : j = o <;> simp [h]
  · simp

private lemma witness_subtheory : Subtheory preparations effects := by
  have ha : effects = postprocessings measurement := (postprocessings_convex _).convexHull_eq
  refine ⟨convex_convexHull _ _, ?_, convex_convexHull _ _, ?_, ?_, ?_⟩
  · exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact rho_density j)
      (D5.S3.Quantum.Measurements.VisibleStateSpaceDimension.density_matrix_set_compact_convex 2).2
  · intro e he
    rw [ha] at he
    exact ⟨postprocessings_positive measurement_povm he,
      postprocessings_positive measurement_povm
        (postprocessings_complement measurement_povm he)⟩
  · rw [ha]
    exact ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩, by simpa using measurement_povm.2.symm⟩
  · intro e he
    rw [ha] at he ⊢
    exact postprocessings_complement measurement_povm he

private lemma witness_generated : GeneratedBy effects 1 := by
  refine ⟨fun _ => 4, fun _ => measurement, fun _ => measurement_povm, ?_⟩
  change convexHull ℝ (postprocessings measurement) = _
  simp only [Set.iUnion_const]

private lemma one_copy {d : ℕ} {t a : Set (Matrix (Fin d) (Fin d) ℂ)}
    (h : Subtheory t a) : PseudoBroadcastable t a 1 := by
  let e : (Fin 1 → Fin d) ≃ Fin d := Equiv.funUnique _ _
  let ξ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap
  have tr (x : Matrix (Fin d) (Fin d) ℂ) : (ξ x).trace = x.trace :=
    e.sum_comp (fun j => x j j)
  have marginal (x : Matrix (Fin d) (Fin d) ℂ) (i : Fin 1) :
      partialTraceKeep i (ξ x) = x := by
    have empty : Fintype.card {j : Fin 1 // j ≠ i} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    ext a b
    change (∑ z : ({j : Fin 1 // j ≠ i} → Fin d),
      x (if h : (0 : Fin 1) = i then a else z ⟨0, h⟩)
        (if h : (0 : Fin 1) = i then b else z ⟨0, h⟩)) = x a b
    simp only [show (0 : Fin 1) = i from Subsingleton.elim _ _, dite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, empty,
      pow_zero, one_smul]
  refine ⟨ξ, tr, ?_, ?_⟩
  · intro i ρ hρ f hf
    rw [marginal]
  · intro ρ hρ f hf
    have hp : productMap (fun _ : Fin 1 => Fin d) f = (f 0).submatrix e e := by
      ext x y
      change (∏ i : Fin 1, f i (x i) (y i)) = f 0 (x 0) (y 0)
      exact Fin.prod_univ_one _
    rw [hp]
    change 0 ≤ (ρ.submatrix e e * (f 0).submatrix e e).trace
    rw [Matrix.submatrix_mul_equiv ρ (f 0) e e e]
    change 0 ≤ (ξ (ρ * f 0)).trace
    rw [tr]
    exact (h.2.1 ρ hρ).1.trace_mul_nonneg (h.2.2.2.1 _ (hf 0)).1

private lemma corner_bound (u v w z x y : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (ht : u + z = v + w) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : x ≤ 1 / 2) (hy' : y ≤ 1 / 2) :
    (u * (x + y) + v * (x + (1 / 2 - y)) +
      w * ((1 / 2 - x) + y) + z * ((1 / 2 - x) + (1 / 2 - y))) / 4 ≤
      3 / 8 * (u + z) := by
  by_cases hc : 0 ≤ u + v - w - z
  · by_cases hd : 0 ≤ u + w - v - z
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx') hc,
        mul_nonneg (sub_nonneg.mpr hy') hd]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx') hc,
        mul_nonpos_of_nonneg_of_nonpos hy (le_of_not_ge hd)]
  · by_cases hd : 0 ≤ u + w - v - z
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hc),
        mul_nonneg (sub_nonneg.mpr hy') hd]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hc),
        mul_nonpos_of_nonneg_of_nonpos hy (le_of_not_ge hd)]

private lemma witness_relations :
    rho 0 + rho 3 = 1 ∧ rho 1 + rho 2 = 1 ∧
    measurement 0 + measurement 1 = (1 / 2 : ℂ) • 1 ∧
    measurement 2 + measurement 3 = (1 / 2 : ℂ) • 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [rho.eq_1, measurement.eq_1, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Matrix.cons_val_zero, Pi.star_apply] <;> norm_num [Complex.real_smul]

private lemma born_sum (j : Fin 4) :
    (rho j * measurement (![0, 0, 1, 1] j)).trace +
      (rho j * measurement (![2, 3, 2, 3] j)).trace = 17 / 20 := by
  fin_cases j <;>
    simp only [rho, measurement, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply] <;> norm_num [Complex.real_smul]

private lemma witness_contextual : ¬ Noncontextual preparations effects := by
  rintro ⟨ι, g, s, hn, hm, hr, ht, hb⟩
  let μ (j : Fin 4) (l : ι) := (rho j * g l).trace
  let r (o : Fin 4) (l : ι) := (s l * measurement o).trace
  let ix : Fin 4 → Fin 4 := ![0, 0, 1, 1]
  let iz : Fin 4 → Fin 4 := ![2, 3, 2, 3]
  have mem (j : Fin 4) : rho j ∈ preparations := subset_convexHull ℝ _ ⟨j, rfl⟩
  have nonneg (j : Fin 4) (l : ι) : 0 ≤ μ j l := hn l _ (mem j)
  have response (o : Fin 4) (l : ι) : 0 ≤ r o l := hr l _ (measurement_member o)
  have sums (j : Fin 4) : HasSum (μ j) 1 := hm _ (mem j)
  have reproduce (j o : Fin 4) :
      HasSum (fun l => μ j l * r o l) (rho j * measurement o).trace :=
    hb _ (mem j) _ (measurement_member o)
  have relations (l : ι) : μ 0 l + μ 3 l = μ 1 l + μ 2 l := by
    change (rho 0 * g l).trace + (rho 3 * g l).trace =
      (rho 1 * g l).trace + (rho 2 * g l).trace
    rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.trace_add, ← Matrix.add_mul,
      witness_relations.1, witness_relations.2.1]
  have responses (l : ι) :
      r 0 l + r 1 l = 1 / 2 ∧ r 2 l + r 3 l = 1 / 2 := by
    constructor
    · change (s l * measurement 0).trace + (s l * measurement 1).trace = _
      rw [← Matrix.trace_add, ← Matrix.mul_add, witness_relations.2.2.1,
        Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, ht l]
      simp
    · change (s l * measurement 2).trace + (s l * measurement 3).trace = _
      rw [← Matrix.trace_add, ← Matrix.mul_add, witness_relations.2.2.2,
        Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, ht l]
      simp
  have bound (l : ι) :
      (1 / 4 : ℝ) * ∑ j, (μ j l * (r (ix j) l + r (iz j) l)).re ≤
        (3 / 8 : ℝ) * ((μ 0 l).re + (μ 3 l).re) := by
    have hn' (j) := (Complex.nonneg_iff.mp (nonneg j l)).1
    have hr' (o) := (Complex.nonneg_iff.mp (response o l)).1
    have hi (j) : (μ j l).im = 0 := (Complex.nonneg_iff.mp (nonneg j l)).2.symm
    have hrel := congrArg Complex.re (relations l)
    have hx := congrArg Complex.re (responses l).1
    have hy := congrArg Complex.re (responses l).2
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hrel hx hy
    have hx1 : (r 1 l).re = 1 / 2 - (r 0 l).re := by linarith
    have hy1 : (r 3 l).re = 1 / 2 - (r 2 l).re := by linarith
    have h := corner_bound (μ 0 l).re (μ 1 l).re (μ 2 l).re (μ 3 l).re
      (r 0 l).re (r 2 l).re (hn' 0) (hn' 1) (hn' 2) (hn' 3) hrel (hr' 0) (hr' 2)
      (by linarith [hr' 1]) (by linarith [hr' 3])
    convert h using 1
    simp [Fin.sum_univ_succ, ix, iz, Complex.mul_re, Complex.add_re, hi, hx1, hy1]
    ring
  have total : HasSum (fun l => (μ 0 l).re + (μ 3 l).re) 2 := by
    convert (Complex.hasSum_re (sums 0)).add (Complex.hasSum_re (sums 3)) using 1
    norm_num
  have score (j : Fin 4) :
      HasSum (fun l => (μ j l * (r (ix j) l + r (iz j) l)).re) (17 / 20 : ℝ) := by
    have h := (reproduce j (ix j)).add (reproduce j (iz j))
    change HasSum _ ((rho j * measurement (![0, 0, 1, 1] j)).trace +
      (rho j * measurement (![2, 3, 2, 3] j)).trace) at h
    rw [born_sum] at h
    convert Complex.hasSum_re h using 1
    · funext l
      rw [mul_add]
    · norm_num
  have score_total : HasSum
      (fun l => (1 / 4 : ℝ) * ∑ j, (μ j l * (r (ix j) l + r (iz j) l)).re)
      (17 / 20 : ℝ) := by
    convert (hasSum_sum (s := Finset.univ) (fun j _ => score j)).mul_left (1 / 4 : ℝ) using 1
    norm_num [Fin.sum_univ_succ]
  have h := hasSum_le bound score_total (total.mul_left (3 / 8 : ℝ))
  norm_num at h

theorem result : ¬ claim := by
  intro h
  exact witness_contextual ((h 2 1 preparations effects witness_subtheory witness_generated).mp
    (one_copy witness_subtheory))

end D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation
