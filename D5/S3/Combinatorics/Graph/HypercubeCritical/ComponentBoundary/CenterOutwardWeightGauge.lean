/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Diagonal weight transport and separation of two centered Huang outward images. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardDifference

/-! Diagonal weight transport for the actual centered outward Huang differentials.
For nonzero coordinate weights it identifies the kernels on any fixed column support.
Two distinct centers have disjoint outward images by the difference-energy identity
and square-zero property. The application is to Hong–Wu–Xia, arXiv:2610.09483v1,
Section 7, Problem 2. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardWeightGauge

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip flip_apply_same gamma_apply)
open CenterOutwardDifference (outward outward_sub_energy outward_sq)

/-- The product of weights in the coordinates separating the vertex from its center. -/
def monomial {n : ℕ} (w : Fin n → ℝ) (c x : Q n) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => x i ≠ c i), w i

/-- An outward flip removes precisely one factor. All weights are allowed to vanish. -/
private theorem monomial_flip {n : ℕ} (w : Fin n → ℝ) (c x : Q n) (i : Fin n)
    (hi : x i ≠ c i) : w i * monomial w c (flip x i) = monomial w c x := by
  have hset : Finset.univ.filter (fun j => flip x i j ≠ c j) =
      (Finset.univ.filter (fun j => x j ≠ c j)).erase i := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [hi]
    · have hf : flip x i j = x j := Function.update_of_ne hj _ _
      simp [hj, hf]
  have hm : i ∈ Finset.univ.filter (fun j => x j ≠ c j) := by simp [hi]
  unfold monomial
  rw [hset]
  exact Finset.mul_prod_erase _ _ hm

/-- Exact intertwining of the weighted and unit-weight outward operators by
pointwise multiplication with the center monomial, including singular weights. -/
theorem outward_monomial_mul {n : ℕ} (w : Fin n → ℝ) (c : Q n)
    (z : Q n → ℝ) :
    outward w c (monomial w c * z) =
      monomial w c * outward (fun _ => 1) c z := by
  funext x
  change outward w c (monomial w c * z) x =
    monomial w c x * outward (fun _ => 1) c z x
  rw [outward, outward, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≠ c i
  · simp only [ite_eq_left hi, one_mul]
    calc
      _ = (w i * monomial w c (flip x i)) * BalancedCriticalSpectrum.gamma i z x := by
        simp only [gamma_apply, Pi.mul_apply]
        ring
      _ = _ := by rw [monomial_flip w c x i hi]
  · simp [hi]

private theorem monomial_ne_zero {n : ℕ} (w : Fin n → ℝ) (c x : Q n)
    (hw : ∀ i, w i ≠ 0) : monomial w c x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)

private theorem outward_zero {n : ℕ} (w : Fin n → ℝ) (c : Q n) :
    outward w c (0 : Q n → ℝ) = 0 := by
  funext x
  simp [outward]

private theorem outward_add {n : ℕ} (w : Fin n → ℝ) (c : Q n)
    (z t : Q n → ℝ) : outward w c (z + t) = outward w c z + outward w c t := by
  funext x
  simp only [outward, map_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≠ c i <;> simp [hi, mul_add]

private theorem outward_smul {n : ℕ} (w : Fin n → ℝ) (c : Q n)
    (a : ℝ) (z : Q n → ℝ) :
    outward w c (a • z) = a • outward w c z := by
  funext x
  change outward w c (a • z) x = a * outward w c z x
  simp only [outward, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≠ c i <;> simp [hi] <;> ring

/-- Kernel of the outward differential restricted to the fixed set of input columns. -/
def supportedKernel {n : ℕ} (w : Fin n → ℝ) (c : Q n) (S : Set (Q n)) :
    Submodule ℝ (Q n → ℝ) where
  carrier := {z | (∀ x ∉ S, z x = 0) ∧ outward w c z = 0}
  zero_mem' := ⟨fun _ _ => rfl, outward_zero w c⟩
  add_mem' := by
    intro z t hz ht
    change (∀ x ∉ S, z x = 0) ∧ outward w c z = 0 at hz
    change (∀ x ∉ S, t x = 0) ∧ outward w c t = 0 at ht
    change (∀ x ∉ S, (z + t) x = 0) ∧ outward w c (z + t) = 0
    refine ⟨?_, ?_⟩
    · intro x hx
      change z x + t x = 0
      rw [hz.1 x hx, ht.1 x hx, add_zero]
    · rw [outward_add, hz.2, ht.2, add_zero]
  smul_mem' := by
    intro a z hz
    change (∀ x ∉ S, z x = 0) ∧ outward w c z = 0 at hz
    change (∀ x ∉ S, (a • z) x = 0) ∧ outward w c (a • z) = 0
    refine ⟨?_, ?_⟩
    · intro x hx
      change a * z x = 0
      rw [hz.1 x hx, mul_zero]
    · rw [outward_smul, hz.2, smul_zero]

private theorem mem_supportedKernel {n : ℕ} (w : Fin n → ℝ) (c : Q n) (S : Set (Q n))
    (z : Q n → ℝ) : z ∈ supportedKernel w c S ↔
      (∀ x ∉ S, z x = 0) ∧ outward w c z = 0 := Iff.rfl

/-- Diagonal scaling preserves both the input column support and the full kernel
condition when the weights are nonzero. -/
private theorem monomial_mul_mem_supportedKernel_iff {n : ℕ} (w : Fin n → ℝ)
    (c : Q n) (S : Set (Q n)) (hw : ∀ i, w i ≠ 0) (z : Q n → ℝ) :
    monomial w c * z ∈ supportedKernel w c S ↔
      z ∈ supportedKernel (fun _ => 1) c S := by
  rw [mem_supportedKernel, mem_supportedKernel, outward_monomial_mul]
  constructor
  · rintro ⟨hs, hk⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (mul_eq_zero.mp (hs x hx)).resolve_left (monomial_ne_zero w c x hw)
    · funext x
      have h := congrFun hk x
      change monomial w c x * outward (fun _ => 1) c z x = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (monomial_ne_zero w c x hw)
  · rintro ⟨hs, hk⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      change monomial w c x * z x = 0
      rw [hs x hx, mul_zero]
    · rw [hk, mul_zero]

/-- The diagonal monomial and its pointwise inverse give a linear equivalence
of the unit-weight and weighted kernels on exactly the same column support. -/
def supportedKernelEquiv {n : ℕ} (w : Fin n → ℝ) (c : Q n)
    (S : Set (Q n)) (hw : ∀ i, w i ≠ 0) :
    supportedKernel (fun _ => 1) c S ≃ₗ[ℝ] supportedKernel w c S := by
  let lower (z : Q n → ℝ) : Q n → ℝ := fun x => (monomial w c x)⁻¹ * z x
  have hright (z : Q n → ℝ) : monomial w c * lower z = z := by
    funext x
    change monomial w c x * ((monomial w c x)⁻¹ * z x) = z x
    rw [← mul_assoc, mul_inv_cancel₀ (monomial_ne_zero w c x hw), one_mul]
  have hleft (z : Q n → ℝ) : lower (monomial w c * z) = z := by
    funext x
    change (monomial w c x)⁻¹ * (monomial w c x * z x) = z x
    rw [← mul_assoc, inv_mul_cancel₀ (monomial_ne_zero w c x hw), one_mul]
  have hmem (z : Q n → ℝ) :=
    monomial_mul_mem_supportedKernel_iff w c S hw z
  exact
    { toFun := fun z => ⟨monomial w c * (z : Q n → ℝ), (hmem z).2 z.property⟩
      invFun := fun z => ⟨lower z, (hmem (lower z)).1 (by
        rw [hright]
        exact z.property)⟩
      left_inv := fun z => Subtype.ext (hleft z)
      right_inv := fun z => Subtype.ext (hright z)
      map_add' := by
        intro z t
        apply Subtype.ext
        funext x
        change monomial w c x * (z.val x + t.val x) =
          monomial w c x * z.val x + monomial w c x * t.val x
        exact mul_add _ _ _
      map_smul' := by
        intro a z
        apply Subtype.ext
        funext x
        change monomial w c x * (a * z.val x) =
          a * (monomial w c x * z.val x)
        ring }

/-- Injectivity on a fixed column support at unit weights implies triviality of
the weighted supported kernel for every nonvanishing weight tuple. -/
private theorem weighted_kernel_eq_zero {n : ℕ} (w : Fin n → ℝ) (c : Q n)
    (S : Set (Q n)) (hw : ∀ i, w i ≠ 0)
    (hinj : Set.InjOn (outward (fun _ => 1) c)
      {z : Q n → ℝ | ∀ x ∉ S, z x = 0})
    (z : Q n → ℝ) (hs : ∀ x ∉ S, z x = 0) (hk : outward w c z = 0) :
    z = 0 := by
  let t : supportedKernel w c S := ⟨z, (mem_supportedKernel w c S z).2 ⟨hs, hk⟩⟩
  let e := supportedKernelEquiv w c S hw
  have hpre := (mem_supportedKernel (fun _ => 1) c S (e.symm t)).1 (e.symm t).property
  have h0 : (0 : Q n → ℝ) ∈ {f : Q n → ℝ | ∀ x ∉ S, f x = 0} := by
    intro x hx
    rfl
  have ht : e.symm t = 0 := by
    apply Subtype.ext
    change (e.symm t : Q n → ℝ) = 0
    exact hinj hpre.1 h0 (hpre.2.trans (outward_zero (fun _ => 1) c).symm)
  have hzero : t = 0 := by
    apply e.symm.injective
    simpa only [map_zero] using ht
  exact congrArg (fun v : supportedKernel w c S => (v : Q n → ℝ)) hzero

/-- Positive weighted squared center distance separates two closed residuals
whose sum vanishes. Zero weights in directions outside the distance are allowed. -/
theorem closed_pair_eq_zero {n : ℕ} (w : Fin n → ℝ) (c d : Q n)
    (z t : Q n → ℝ)
    (hdist : 0 < ∑ i ∈ Finset.univ.filter (fun i => c i ≠ d i), w i ^ 2)
    (hz : outward w c z = 0) (ht : outward w d t = 0) (hcancel : z + t = 0) :
    z = 0 ∧ t = 0 := by
  have hcommon : outward w c t = 0 := by
    have h := outward_add w c z t
    rw [hcancel, outward_zero, hz, zero_add] at h
    exact h.symm
  have hprod : (∑ i ∈ Finset.univ.filter (fun i => c i ≠ d i), w i ^ 2) *
      (∑ x, t x ^ 2) = 0 := calc
    _ = ∑ x, (outward w c t x - outward w d t x) ^ 2 :=
      (outward_sub_energy w c d t).symm
    _ = 0 := by simp [hcommon, ht]
  have hsum : (∑ x, t x ^ 2) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hdist)
  have htzero : t = 0 := by
    funext x
    exact (Finset.sum_sq_eq_zero_iff Finset.univ t).mp hsum x (Finset.mem_univ x)
  exact ⟨by simpa [htzero] using hcancel, htzero⟩

/-- Nonzero weights give positive squared distance for distinct centers. -/
private theorem weighted_center_distance_pos {n : ℕ} (w : Fin n → ℝ) (c d : Q n)
    (hw : ∀ i, w i ≠ 0) (hcd : c ≠ d) :
    0 < ∑ i ∈ Finset.univ.filter (fun i => c i ≠ d i), w i ^ 2 := by
  have hdiff : ∃ i, c i ≠ d i := by
    by_contra! h
    exact hcd (funext h)
  obtain ⟨i, hi⟩ := hdiff
  apply Finset.sum_pos' (fun j _ => sq_nonneg (w j))
  exact ⟨i, by simp [hi], sq_pos_of_ne_zero (hw i)⟩

/-- The weighted two-center sum of outward operators is injective on the
product of two specified column supports if the two unit-weight operators
are injective on their respective supports, expressed here by triviality of the
kernel of the sum. -/
theorem weighted_pair_eq_zero {n : ℕ} (w : Fin n → ℝ) (c d : Q n)
    (S T : Set (Q n)) (hw : ∀ i, w i ≠ 0) (hcd : c ≠ d)
    (hc : Set.InjOn (outward (fun _ => 1) c)
      {z : Q n → ℝ | ∀ x ∉ S, z x = 0})
    (hd : Set.InjOn (outward (fun _ => 1) d)
      {t : Q n → ℝ | ∀ x ∉ T, t x = 0})
    (z t : Q n → ℝ) (hz : ∀ x ∉ S, z x = 0) (ht : ∀ x ∉ T, t x = 0)
    (hcancel : outward w c z + outward w d t = 0) : z = 0 ∧ t = 0 := by
  obtain ⟨hcres, hdres⟩ :=
    closed_pair_eq_zero w c d (outward w c z) (outward w d t)
      (weighted_center_distance_pos w c d hw hcd)
      (outward_sq w c z) (outward_sq w d t) hcancel
  exact ⟨weighted_kernel_eq_zero w c S hw hc z hz hcres,
    weighted_kernel_eq_zero w d T hw hd t ht hdres⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardWeightGauge
