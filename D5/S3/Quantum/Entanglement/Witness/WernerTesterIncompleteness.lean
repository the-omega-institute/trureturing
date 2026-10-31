/- GID: D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim; result=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result; claim=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim
   digest: Entangled Werner states need not be detected by any pair of complex testers. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound

open scoped BigOperators ComplexOrder TensorProduct
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments

namespace D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness

noncomputable section

/-- A complex tester has trace-norm to Euclidean operator norm exactly one. -/
def IsTester {d n : ℕ}
    (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ x, ‖e x‖ ≤ traceNorm x) ∧ ∃ x, x ≠ 0 ∧ ‖e x‖ = traceNorm x

/-- The pure tensor of the two Euclidean tester outputs, indexed by `Bool`. -/
def tensorPair {n₁ n₂ : ℕ} :
    EuclideanSpace ℂ (Fin n₁) →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂) →ₗ[ℂ]
      ⨂[ℂ] s : Bool, EuclideanSpace ℂ (Fin (cond s n₂ n₁)) :=
  LinearMap.mk₂ ℂ (fun a b => PiTensorProduct.tprod ℂ (Bool.rec a b))
    (by
      intro a a' b
      convert (PiTensorProduct.tprod ℂ
        (s := fun s : Bool => EuclideanSpace ℂ (Fin (cond s n₂ n₁)))).map_update_add
          (Bool.rec a b) false a a' using 1
      <;> congr 2 <;> funext s <;> cases s <;> simp)
    (by
      intro c a b
      convert (PiTensorProduct.tprod ℂ
        (s := fun s : Bool => EuclideanSpace ℂ (Fin (cond s n₂ n₁)))).map_update_smul
          (Bool.rec a b) false c a using 1
      <;> congr 2 <;> funext s <;> cases s <;> simp)
    (by
      intro a b b'
      convert (PiTensorProduct.tprod ℂ
        (s := fun s : Bool => EuclideanSpace ℂ (Fin (cond s n₂ n₁)))).map_update_add
          (Bool.rec a b) true b b' using 1
      <;> congr 2 <;> funext s <;> cases s <;> simp)
    (by
      intro c a b
      convert (PiTensorProduct.tprod ℂ
        (s := fun s : Bool => EuclideanSpace ℂ (Fin (cond s n₂ n₁)))).map_update_smul
          (Bool.rec a b) true c b using 1
      <;> congr 2 <;> funext s <;> cases s <;> simp)

/-- The tensor product of two complex linear testers applied through matrix units. -/
def testerImage {d₁ d₂ n₁ n₂ : ℕ}
    (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    ⨂[ℂ] s : Bool, EuclideanSpace ℂ (Fin (cond s n₂ n₁)) :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    ρ (i, j) (k, l) • tensorPair (e₁ (Matrix.single i k 1)) (e₂ (Matrix.single j l 1))

/-- Separable density matrices form the convex hull of all product density matrices. -/
def Separable {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) : Prop :=
  ρ ∈ convexHull ℝ {σ | ∃ (ρ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ρ₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
    ρ₁.PosSemidef ∧ ρ₁.trace = 1 ∧ ρ₂.PosSemidef ∧ ρ₂.trace = 1 ∧
    σ = Matrix.kroneckerMap (· * ·) ρ₁ ρ₂}

/-- Werner's symmetric and antisymmetric mixture, with the flip on the two factors. -/
def werner (d : ℕ) (μ : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (μ / ((d : ℝ) * (d + 1))) •
      (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))) +
    ((1 - μ) / ((d : ℝ) * (d - 1))) •
      (1 - Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)))

/-- The bipartite completeness question for complex testers without index permutations. -/
def claim : Prop :=
  ∀ (d₁ d₂ : ℕ) (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ),
    ρ.PosSemidef → ρ.trace = 1 → ¬ Separable ρ →
    ∃ (n₁ n₂ : ℕ)
      (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
      (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂)),
      IsTester e₁ ∧ IsTester e₂ ∧ 1 < ‖testerImage e₁ e₂ ρ‖

private theorem flip_product_trace {d : ℕ} (a b : Matrix (Fin d) (Fin d) ℂ) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
      Matrix.kroneckerMap (· * ·) a b).trace = (a * b).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, replicaSwap_apply, Prod.swap_prod_mk, Prod.mk.injEq,
    Matrix.kroneckerMap_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i j : Fin d => a j i * b i j)

private def flipReadout (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap (Fin d × Fin d) ℝ ℂ).comp
    (LinearMap.mulLeft ℝ (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)))))

private theorem separable_flip_nonneg {d : ℕ}
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (h : Separable ρ) :
    0 ≤ flipReadout d ρ := by
  apply convexHull_min (t := (flipReadout d) ⁻¹' Set.Ici 0) ?_
    ((convex_Ici (0 : ℝ)).linear_preimage (flipReadout d)) h
  rintro σ ⟨a, b, ha, _, hb, _, rfl⟩
  change 0 ≤ (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
    Matrix.kroneckerMap (· * ·) a b).trace.re
  rw [flip_product_trace]
  exact RHLinalg.trace_mul_nonneg_of_posSemidef ha hb

private theorem tester_image_decomposition {d₁ d₂ n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]
    (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (a : ι → Matrix (Fin d₁) (Fin d₁) ℂ) (b : ι → Matrix (Fin d₂) (Fin d₂) ℂ) :
    testerImage e₁ e₂ (∑ t, Matrix.kroneckerMap (· * ·) (a t) (b t)) =
      ∑ t, tensorPair (e₁ (a t)) (e₂ (b t)) := by
  classical
  have hex {d n : ℕ}
      (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (x : Matrix (Fin d) (Fin d) ℂ) :
      e x = ∑ i, ∑ k, x i k • e (Matrix.single i k 1) := by
    have hs (i k : Fin d) : Matrix.single i k (x i k) =
        x i k • Matrix.single i k (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum, hs, map_smul]
  rw [testerImage.eq_1]
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_smul]
  conv_rhs =>
    arg 2
    ext t
    rw [hex e₁ (a t), hex e₂ (b t)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₁)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₁)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset (Fin d₁)))]
  simp only [mul_comm]

private theorem projective_decomposition_bound {n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → EuclideanSpace ℂ (Fin n₁)) (b : ι → EuclideanSpace ℂ (Fin n₂))
    (ha : ∑ t, ‖a t‖ ^ 2 ≤ 1) (hb : ∑ t, ‖b t‖ ^ 2 ≤ 1) :
    ‖∑ t, tensorPair (a t) (b t)‖ ≤ 1 := by
  classical
  have hc : (∑ t, ‖a t‖ * ‖b t‖) ≤ 1 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun t => ‖a t‖) (fun t => ‖b t‖)
    have hp : (∑ t, ‖a t‖ ^ 2) * (∑ t, ‖b t‖ ^ 2) ≤ (1 : ℝ) := by
      nlinarith [Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) => sq_nonneg ‖a t‖),
        Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) => sq_nonneg ‖b t‖)]
    have hn : 0 ≤ ∑ t, ‖a t‖ * ‖b t‖ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  apply le_trans (b := ∑ t, ‖a t‖ * ‖b t‖) ?_ hc
  calc
    ‖∑ t, tensorPair (a t) (b t)‖ ≤ ∑ t, ‖tensorPair (a t) (b t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t, ‖a t‖ * ‖b t‖ := by
      apply Finset.sum_le_sum
      intro t _
      rw [tensorPair.eq_1]
      simpa [Fintype.prod_bool, mul_comm] using
        (PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℂ)
          (Bool.rec (a t) (b t) :
            (s : Bool) → EuclideanSpace ℂ (Fin (cond s n₂ n₁))))

private abbrev DesignIndex (d : ℕ) := Fin d ⊕ (Fin d → Fin 4)

private def designWeight (d : ℕ) : DesignIndex d → ℝ :=
  Sum.elim (fun _ => 1 / ((d : ℝ) * (d + 1)))
    (fun _ => (d : ℝ) / ((d + 1) * 4 ^ d))

private def designProjector (d : ℕ) : DesignIndex d → Matrix (Fin d) (Fin d) ℂ :=
  Sum.elim
    (fun a => Matrix.vecMulVec (fun i => if i = a then 1 else 0)
      (star (fun i => if i = a then 1 else 0)))
    (fun z => (1 / (d : ℝ)) • Matrix.vecMulVec (fun i => phase (z i))
      (star (fun i => phase (z i))))

def designAverage (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (1 / (d : ℝ)) • 1

private def designCentered (d : ℕ) (t : DesignIndex d) : Matrix (Fin d) (Fin d) ℂ :=
  designProjector d t - designAverage d

private theorem design_weight_nonneg (d : ℕ) (t : DesignIndex d) : 0 ≤ designWeight d t := by
  rw [designWeight.eq_1]
  cases t <;> dsimp <;> positivity

private theorem design_weight_sum {d : ℕ} (hd : 0 < d) : ∑ t, designWeight d t = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha : (d : ℝ) + 1 ≠ 0 := by positivity
  simp [designWeight, Fintype.sum_sum_type]
  field_simp
  <;> ring

private theorem design_density {d : ℕ} (hd : 0 < d) (t : DesignIndex d) :
    (designProjector d t).PosSemidef ∧ (designProjector d t).trace = 1 := by
  classical
  simp only [designProjector.eq_1]
  cases t with
  | inl a =>
    constructor
    · exact Matrix.posSemidef_vecMulVec_self_star _
    · simp [designProjector, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
        Pi.star_apply]
  | inr z =>
    constructor
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity : 0 ≤ 1 / (d : ℝ))
    · have hu (s : Fin 4) : phase s * (starRingEnd ℂ) (phase s) = 1 := by
        simpa only [mul_comm] using phase_unit s
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      simp [designProjector, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
        Pi.star_apply, hu, Complex.real_smul, hd']

private theorem design_four {d : ℕ} (i j k l : Fin d) :
    designSum (fun z => star (z k) * z i * star (z l) * z j) =
      (4 : ℂ) ^ d * ((if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) := by
  classical
  simpa only [starRingEnd_apply, eq_comm, and_comm] using
    (D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.design_four k i l j)

private theorem design_second_entry {d : ℕ} (hd : 0 < d) (i j k l : Fin d) :
    (∑ t, (designWeight d t : ℂ) * designProjector d t i k * designProjector d t j l) =
      (1 / ((d : ℂ) * (d + 1))) * ((if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) := by
  classical
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have h4 : (4 : ℂ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  let c : ℂ := 1 / ((d : ℂ) * (d + 1) * 4 ^ d)
  have he : (∑ t, (designWeight d t : ℂ) *
        designProjector d t i k * designProjector d t j l) =
      c * designSum (fun z => star (z k) * z i * star (z l) * z j) := by
    rw [Fintype.sum_sum_type, designSum, mul_add]
    rw [← mul_assoc c ((4 : ℂ) ^ d)]
    simp only [Finset.mul_sum]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro z _
      dsimp [designWeight, designProjector, c]
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Complex.real_smul]
      push_cast
      field_simp (discharger := first | assumption | norm_num)
      <;> simp only [starRingEnd_apply]
      <;> ring
    · apply Finset.sum_congr rfl
      intro a _
      dsimp [designWeight, designProjector, c]
      simp only [Matrix.vecMulVec_apply, Pi.star_apply]
      push_cast
      field_simp (discharger := first | assumption | norm_num)
      <;> simp only [starRingEnd_apply]
      <;> ring
  rw [he, design_four]
  dsimp [c]
  field_simp (discharger := first | assumption | norm_num)
  <;> ring

private theorem design_first {d : ℕ} (hd : 0 < d) :
    ∑ t, designWeight d t • designProjector d t = designAverage d := by
  classical
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have he (i k : Fin d) :
      (∑ t, (designWeight d t : ℂ) * designProjector d t i k) = designAverage d i k := by
    calc
      _ = ∑ t, ∑ j : Fin d, (designWeight d t : ℂ) *
          designProjector d t i k * designProjector d t j j := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.mul_sum]
        have ht := (design_density hd t).2
        change ∑ j, designProjector d t j j = 1 at ht
        rw [ht, mul_one]
      _ = ∑ j : Fin d, ∑ t, (designWeight d t : ℂ) *
          designProjector d t i k * designProjector d t j j := Finset.sum_comm
      _ = designAverage d i k := by
        simp_rw [design_second_entry hd]
        by_cases hik : i = k
        · subst k
          simp [designAverage.eq_1, Matrix.one_apply, eq_comm, mul_add,
            Finset.sum_add_distrib, Complex.real_smul]
          field_simp
          <;> ring
        · have hh (j : Fin d) : ¬ (i = j ∧ j = k) := by
            rintro ⟨rfl, rfl⟩
            exact hik rfl
          simp [hik, hh, designAverage, Matrix.one_apply]
  ext i k
  simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] using he i k

private theorem flip_facts (d : ℕ) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))).IsHermitian ∧
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
        Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) = 1 := by
  exact ⟨D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.swapHermitian,
    D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.swapSquare⟩

private theorem werner_density {d : ℕ} {μ : ℝ} (hd : 1 < d)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    (werner d μ).PosSemidef ∧ (werner d μ).trace = 1 := by
  let f := Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))
  obtain ⟨hn, hp⟩ :=
    D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper.involution_binary f
      (flip_facts d).1 (by simpa only [pow_two] using (flip_facts d).2)
  have hdℝ : (1 : ℝ) < d := by exact_mod_cast hd
  have hdmℝ : 0 < (d : ℝ) - 1 := sub_pos.mpr hdℝ
  constructor
  · exact (hp.smul (div_nonneg hμ₀ (by positivity))).add
      (hn.smul (div_nonneg (sub_nonneg.mpr hμ₁) (by positivity)))
  · have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have ha : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
    have hb : (d : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hd))
    simp only [werner.eq_1, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
      D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.traceSwap,
      Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Complex.real_smul]
    push_cast
    field_simp
    <;> ring

private theorem werner_readout {d : ℕ} (hd : 1 < d) (μ : ℝ) :
    flipReadout d (werner d μ) = 2 * μ - 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have ha : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have hb : (d : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hd))
  have ht : (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
      werner d μ).trace = ((2 * μ - 1 : ℝ) : ℂ) := by
    simp only [werner.eq_1, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
      (flip_facts d).2, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
      D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.traceSwap,
      Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Complex.real_smul]
    push_cast
    field_simp
    <;> ring
  change (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
    werner d μ).trace.re = _
  rw [ht]
  simp

private theorem werner_entangled {d : ℕ} {μ : ℝ} (hd : 1 < d) (hμ : μ < 1 / 2) :
    ¬ Separable (werner d μ) := by
  intro h
  have hn := separable_flip_nonneg _ h
  rw [werner_readout hd] at hn
  linarith

private def correlation (d : ℕ) (μ : ℝ) : ℝ :=
  ((d : ℝ) + 1 - 2 * μ * d) / (d - 1)

set_option maxRecDepth 4096 in
private theorem werner_decomposition {d : ℕ} (hd : 1 < d) (μ : ℝ) :
    werner d μ = Matrix.kroneckerMap (· * ·) (designAverage d) (designAverage d) -
      correlation d μ • ∑ t, designWeight d t •
        Matrix.kroneckerMap (· * ·) (designCentered d t) (designCentered d t) := by
  classical
  have hd₀ : 0 < d := by omega
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have ha : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have hb : (d : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hd))
  have hfirst (i k : Fin d) :
      (∑ t, (designWeight d t : ℂ) * designProjector d t i k) = designAverage d i k := by
    have h := congrArg (fun m : Matrix (Fin d) (Fin d) ℂ => m i k) (design_first hd₀)
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] using h
  have hmass : ∑ t, (designWeight d t : ℂ) = 1 := by exact_mod_cast design_weight_sum hd₀
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.sum_apply, Complex.real_smul, designCentered]
  change werner d μ (i, j) (k, l) = designAverage d i k * designAverage d j l -
    (correlation d μ : ℂ) * ∑ t, (designWeight d t : ℂ) *
      ((designProjector d t i k - designAverage d i k) *
        (designProjector d t j l - designAverage d j l))
  have he (t : DesignIndex d) : (designWeight d t : ℂ) *
      ((designProjector d t i k - designAverage d i k) *
        (designProjector d t j l - designAverage d j l)) =
      (designWeight d t : ℂ) * designProjector d t i k * designProjector d t j l -
      (designWeight d t : ℂ) * designProjector d t i k * designAverage d j l -
      (designWeight d t : ℂ) * designProjector d t j l * designAverage d i k +
      (designWeight d t : ℂ) * designAverage d i k * designAverage d j l := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hfirst, hmass, one_mul, design_second_entry hd₀]
  simp only [werner.eq_1, designAverage, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, replicaSwap_apply, Prod.swap_prod_mk,
    Prod.mk.injEq, Complex.real_smul, correlation]
  push_cast
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    by_cases hil : i = l <;> by_cases hjk : j = k <;>
    by_cases hkl : k = l <;> simp [*, eq_comm] <;> field_simp <;> ring

private theorem design_second_moment {d n : ℕ} (hd : 0 < d)
    (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (h : ∀ x, ‖e x‖ ≤ traceNorm x) :
    ‖e (designAverage d)‖ ^ 2 +
      ∑ t, designWeight d t * ‖e (designCentered d t)‖ ^ 2 ≤ 1 := by
  classical
  have hm : ∑ t, designWeight d t • e (designProjector d t) = e (designAverage d) := by
    rw [← design_first hd]
    simp only [map_sum, LinearMap.map_smul_of_tower]
  have hx : (∑ t, designWeight d t * inner ℝ (e (designProjector d t))
      (e (designAverage d))) = ‖e (designAverage d)‖ ^ 2 := by
    rw [← hm, ← real_inner_self_eq_norm_sq]
    simp only [sum_inner, real_inner_smul_left]
  have hv : ‖e (designAverage d)‖ ^ 2 +
      ∑ t, designWeight d t * ‖e (designCentered d t)‖ ^ 2 =
      ∑ t, designWeight d t * ‖e (designProjector d t)‖ ^ 2 := by
    have hp (t : DesignIndex d) : designWeight d t * ‖e (designCentered d t)‖ ^ 2 =
        designWeight d t * ‖e (designProjector d t)‖ ^ 2 -
        2 * (designWeight d t * inner ℝ (e (designProjector d t)) (e (designAverage d))) +
        designWeight d t * ‖e (designAverage d)‖ ^ 2 := by
      rw [designCentered, map_sub, norm_sub_sq_real]
      ring
    simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hx, design_weight_sum hd]
    ring
  rw [hv]
  calc
    _ ≤ ∑ t, designWeight d t * 1 := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (design_weight_nonneg d t)
      have ht : traceNorm (designProjector d t) = 1 := by
        have ht := traceNorm_of_posSemidef (design_density hd t).1
        rw [(design_density hd t).2] at ht
        exact Complex.ofReal_eq_one.mp ht
      have hc := h (designProjector d t)
      rw [ht] at hc
      nlinarith [norm_nonneg (e (designProjector d t))]
    _ = 1 := by simpa using design_weight_sum hd

private theorem correlation_range {d : ℕ} {μ : ℝ} (hd : 1 < d)
    (hμ₀ : 1 / (d : ℝ) ≤ μ) (hμ₁ : μ < 1 / 2) :
    0 ≤ correlation d μ ∧ correlation d μ ≤ 1 := by
  rw [correlation.eq_1]
  have hdℝ : (1 : ℝ) < d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := by linarith
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hl : 1 ≤ μ * d := (div_le_iff₀ hd₀).mp hμ₀
  have hu := mul_lt_mul_of_pos_right hμ₁ hd₀
  constructor
  · apply div_nonneg _ hdm.le
    nlinarith
  · apply (div_le_iff₀ hdm).mpr
    nlinarith

private theorem werner_bound {d n₁ n₂ : ℕ} {μ : ℝ} (hd : 1 < d)
    (hμ₀ : 1 / (d : ℝ) ≤ μ) (hμ₁ : μ < 1 / 2)
    (e₁ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (h₁ : ∀ x, ‖e₁ x‖ ≤ traceNorm x) (h₂ : ∀ x, ‖e₂ x‖ ≤ traceNorm x) :
    ‖testerImage e₁ e₂ (werner d μ)‖ ≤ 1 := by
  classical
  have hd₀ : 0 < d := by omega
  have hr := correlation_range hd hμ₀ hμ₁
  let a : Unit ⊕ DesignIndex d → Matrix (Fin d) (Fin d) ℂ :=
    Sum.elim (fun _ => designAverage d)
      (fun t => Real.sqrt (correlation d μ * designWeight d t) • designCentered d t)
  let b : Unit ⊕ DesignIndex d → Matrix (Fin d) (Fin d) ℂ :=
    Sum.elim (fun _ => designAverage d)
      (fun t => (-Real.sqrt (correlation d μ * designWeight d t)) • designCentered d t)
  have hρ : werner d μ = ∑ t, Matrix.kroneckerMap (· * ·) (a t) (b t) := by
    rw [werner_decomposition hd μ]
    conv_rhs => rw [Fintype.sum_sum_type]
    simp only [a, b, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
      Finset.smul_sum, smul_smul]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ext p q
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul, Complex.ofReal_neg]
    have hs : (Real.sqrt (correlation d μ * designWeight d t) : ℂ) ^ 2 =
        ((correlation d μ * designWeight d t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt
        (mul_nonneg hr.1 (design_weight_nonneg d t))]
    linear_combination (designCentered d t p.1 q.1 * designCentered d t p.2 q.2) * hs
  have hscale {n : ℕ} (r : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
      ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hs {n : ℕ}
      (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (h : ∀ x, ‖e x‖ ≤ traceNorm x) :
      ‖e (designAverage d)‖ ^ 2 +
        ∑ t, (correlation d μ * designWeight d t) * ‖e (designCentered d t)‖ ^ 2 ≤ 1 := by
    apply le_trans _ (design_second_moment hd₀ e h)
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t _
    have hc := mul_le_mul_of_nonneg_right hr.2
      (mul_nonneg (design_weight_nonneg d t) (sq_nonneg ‖e (designCentered d t)‖))
    simpa only [one_mul, mul_assoc] using hc
  have ha : ∑ t, ‖e₁ (a t)‖ ^ 2 ≤ 1 := by
    simpa only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique, LinearMap.map_smul_of_tower, hscale,
      Real.sq_sqrt (mul_nonneg hr.1 (design_weight_nonneg d _))] using hs e₁ h₁
  have hb : ∑ t, ‖e₂ (b t)‖ ^ 2 ≤ 1 := by
    simpa only [b, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique, LinearMap.map_smul_of_tower, hscale, neg_sq,
      Real.sq_sqrt (mul_nonneg hr.1 (design_weight_nonneg d _))] using hs e₂ h₂
  rw [hρ, tester_image_decomposition]
  exact projective_decomposition_bound (fun t => e₁ (a t)) (fun t => e₂ (b t)) ha hb

/-- These Werner states are entangled density matrices undetected by every pair of contractions. -/
theorem werner_family (d : ℕ) (μ : ℝ) (hd : 3 ≤ d)
    (hμ₀ : 1 / (d : ℝ) ≤ μ) (hμ₁ : μ < 1 / 2) :
    (werner d μ).PosSemidef ∧ (werner d μ).trace = 1 ∧ ¬ Separable (werner d μ) ∧
      ∀ (n₁ n₂ : ℕ)
        (e₁ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
        (e₂ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂)),
        (∀ x, ‖e₁ x‖ ≤ traceNorm x) → (∀ x, ‖e₂ x‖ ≤ traceNorm x) →
          ‖testerImage e₁ e₂ (werner d μ)‖ ≤ 1 := by
  have hd₁ : 1 < d := by omega
  have hμ : 0 ≤ μ := le_trans (by positivity) hμ₀
  obtain ⟨hp, ht⟩ := werner_density hd₁ hμ (by linarith : μ ≤ 1)
  refine ⟨hp, ht, werner_entangled hd₁ hμ₁, ?_⟩
  intro n₁ n₂ e₁ e₂ h₁ h₂
  exact werner_bound hd₁ hμ₀ hμ₁ e₁ e₂ h₁ h₂

/-- The qutrit Werner state at parameter one third refutes tester completeness. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hp, ht, he, hb⟩ := werner_family 3 (1 / 3) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨n₁, n₂, e₁, e₂, h₁, h₂, hdet⟩ := h 3 3 (werner 3 (1 / 3)) hp ht he
  exact (not_lt_of_ge (hb n₁ n₂ e₁ e₂ h₁.1 h₂.1)) hdet

end

end D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
