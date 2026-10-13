/- GID: D5/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform marginals and total-variation control of physical EJM source noise. -/

import D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise

/-
The existing physical Born law supplies positive normalized endpoint laws and
their exact independent-source expansion. This module bounds the complete
64-outcome law and computes its three exact one-party marginals.
admission_basis: escape-witness
ejm_noise_l1_bound: proof_shape: content; escape_witness: the physical independent
mixture dominates its ideal endpoint with weight x*y*z; normalization controls
the remaining mass, giving an L1 bound without a global affine-noise proxy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds

open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
open scoped BigOperators

/-- L1 distance of the full physical noisy law from its ideal three-singlet law. -/
def l1Deviation (x y z : ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    |ejmProbability x y z a b c - ejmProbability 1 1 1 a b c|

private theorem physical_distribution (x y z : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a b c, 0 ≤ ejmProbability x y z a b c) ∧
      (∑ a, ∑ b, ∑ c, ejmProbability x y z a b c = 1) := by
  have h := triangle_noise_distribution whiteNoise singlet whiteNoise singlet
    whiteNoise singlet ejm ejm ejm x y z hx hy hz
  exact ⟨h.1, h.2.1⟩

private theorem endpoint_eq (i j k : Bool) (a b c : Fin 4) :
    triangleBorn (stateMatrix (if i then singlet else whiteNoise))
      (stateMatrix (if j then singlet else whiteNoise))
      (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c =
        ejmProbability (if i then 1 else 0) (if j then 1 else 0)
          (if k then 1 else 0) a b c := by
  cases i <;> cases j <;> cases k <;>
    simp [ejmProbability, noisyTriangle, sourceNoise]

private theorem endpoint_nonnegative (i j k : Bool) (a b c : Fin 4) :
    0 ≤ triangleBorn (stateMatrix (if i then singlet else whiteNoise))
      (stateMatrix (if j then singlet else whiteNoise))
      (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c := by
  rw [endpoint_eq]
  exact (physical_distribution _ _ _ (by cases i <;> norm_num)
    (by cases j <;> norm_num) (by cases k <;> norm_num)).1 a b c

private theorem weight_nonnegative (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (i : Bool) : 0 ≤ sourceWeight x i := by
  cases i <;> simp only [sourceWeight, Bool.false_eq_true, ↓reduceIte]
  · linarith [hx.2]
  · exact hx.1

/-- The ideal endpoint is a genuine subprobability component of the physical
independent-source mixture, with its actual product visibility. -/
theorem ideal_component_dominated (x y z : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (a b c : Fin 4) :
    x * y * z * ejmProbability 1 1 1 a b c ≤ ejmProbability x y z a b c := by
  have h := (triangle_noise_distribution whiteNoise singlet whiteNoise singlet
    whiteNoise singlet ejm ejm ejm x y z hx hy hz).2.2 a b c
  change x * y * z * ejmProbability 1 1 1 a b c ≤
    noisyTriangle whiteNoise singlet whiteNoise singlet whiteNoise singlet
      ejm ejm ejm x y z a b c
  rw [h]
  have hnonneg : ∀ i j k : Bool,
      0 ≤ (sourceWeight x i * sourceWeight y j * sourceWeight z k) *
        triangleBorn (stateMatrix (if i then singlet else whiteNoise))
          (stateMatrix (if j then singlet else whiteNoise))
          (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c := by
    intro i j k
    exact mul_nonneg (mul_nonneg (mul_nonneg (weight_nonnegative x hx i)
      (weight_nonnegative y hy j)) (weight_nonnegative z hz k))
      (endpoint_nonnegative i j k a b c)
  calc
    _ = (sourceWeight x true * sourceWeight y true * sourceWeight z true) *
        triangleBorn (stateMatrix (if true then singlet else whiteNoise))
          (stateMatrix (if true then singlet else whiteNoise))
          (stateMatrix (if true then singlet else whiteNoise)) ejm ejm ejm a b c := by
      simp only [sourceWeight, ↓reduceIte]
      congr 1
      simpa using (endpoint_eq true true true a b c).symm
    _ ≤ ∑ k : Bool, (sourceWeight x true * sourceWeight y true * sourceWeight z k) *
        triangleBorn (stateMatrix (if true then singlet else whiteNoise))
          (stateMatrix (if true then singlet else whiteNoise))
          (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c :=
      Finset.single_le_sum (fun k _ => hnonneg true true k) (Finset.mem_univ true)
    _ ≤ ∑ j : Bool, ∑ k : Bool,
        (sourceWeight x true * sourceWeight y j * sourceWeight z k) *
          triangleBorn (stateMatrix (if true then singlet else whiteNoise))
            (stateMatrix (if j then singlet else whiteNoise))
            (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => hnonneg true j k))
        (Finset.mem_univ true)
    _ ≤ _ := Finset.single_le_sum (fun i _ => Finset.sum_nonneg
      (fun j _ => Finset.sum_nonneg (fun k _ => hnonneg i j k))) (Finset.mem_univ true)

private theorem finite_l1_of_domination {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (t : ℝ) (hq : ∀ i, 0 ≤ q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (ht : t ≤ 1) (hdom : ∀ i, t * q i ≤ p i) :
    ∑ i, |p i - q i| ≤ 2 * (1 - t) := by
  calc
    _ ≤ ∑ i, ((p i - t * q i) + (1 - t) * q i) := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ : 0 ≤ p i - t * q i := sub_nonneg.mpr (hdom i)
      have h₂ : 0 ≤ (1 - t) * q i := mul_nonneg (sub_nonneg.mpr ht) (hq i)
      calc
        _ = |(p i - t * q i) - (1 - t) * q i| := by congr 1 <;> ring
        _ ≤ |p i - t * q i| + |(1 - t) * q i| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hp_sum, hq_sum]
      ring

/-- Physical independent-source replacement costs at most twice the sum of
the three visibility deficits in L1 distance (once that sum in total variation). -/
theorem ejm_noise_l1_bound (x y z : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    l1Deviation x y z ≤ 2 * ((1 - x) + (1 - y) + (1 - z)) := by
  have hp := physical_distribution x y z hx hy hz
  have hq := physical_distribution 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hxy : 0 ≤ x * y := mul_nonneg hx.1 hy.1
  have hxy_le : x * y ≤ 1 := by
    nlinarith [hy.2, mul_nonneg (sub_nonneg.mpr hx.2) hy.1]
  have ht : x * y * z ≤ 1 := by
    nlinarith [hz.2, mul_nonneg (sub_nonneg.mpr hxy_le) hz.1]
  have h := finite_l1_of_domination
    (fun o : Fin 4 × (Fin 4 × Fin 4) => ejmProbability x y z o.1 o.2.1 o.2.2)
    (fun o : Fin 4 × (Fin 4 × Fin 4) => ejmProbability 1 1 1 o.1 o.2.1 o.2.2)
    (x * y * z) (fun o => hq.1 _ _ _)
    (by simpa only [Fintype.sum_prod_type] using hp.2)
    (by simpa only [Fintype.sum_prod_type] using hq.2) ht
    (fun o => ideal_component_dominated x y z hx hy hz _ _ _)
  have hprod : 1 - x * y * z ≤ (1 - x) + (1 - y) + (1 - z) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
    have h₂ := mul_nonneg (sub_nonneg.mpr hxy_le) (sub_nonneg.mpr hz.2)
    nlinarith
  have h' : l1Deviation x y z ≤ 2 * (1 - x * y * z) := by
    simpa only [l1Deviation, Fintype.sum_prod_type] using h
  exact h'.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))

/-- The A marginal remains exactly uniform under all three independent source
visibilities. This is consumed by the actual singleton inflation-score blocks. -/
theorem ejm_noise_marginal_A (x y z : ℝ) (a : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, ejmProbability x y z a b c) = 1 / 4 := by
  simp_rw [ejm_noise_probability]
  fin_cases a <;> simp only [Fin.sum_univ_four, ejmNoiseTable] <;>
    norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
      and_true, and_false, true_and, false_and] <;>
    simp only [ite_true, ite_false] <;> ring

theorem ejm_noise_marginal_B (x y z : ℝ) (b : Fin 4) :
    (∑ a : Fin 4, ∑ c : Fin 4, ejmProbability x y z a b c) = 1 / 4 := by
  simp_rw [ejm_noise_probability]
  fin_cases b <;> simp only [Fin.sum_univ_four, ejmNoiseTable] <;>
    norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
      and_true, and_false, true_and, false_and] <;>
    simp only [ite_true, ite_false] <;> ring

#print axioms ejm_noise_l1_bound
#print axioms ejm_noise_marginal_A
#print axioms ejm_noise_marginal_B

end D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
