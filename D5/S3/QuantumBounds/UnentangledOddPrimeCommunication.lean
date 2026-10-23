/- GID: D5/S3/QuantumBounds/UnentangledOddPrimeCommunication
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/UnentangledOddPrimeCommunication
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unentangled odd-prime communication has sharp score bound 2/(d+1). -/

import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import D5.S3.Fourier.FullBispectrumStability
import D5.S3.Fourier.SparseGeneratorFamily

noncomputable section
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Matrix.CartesianVariance
namespace D5.S3.QuantumBounds.UnentangledOddPrimeCommunication

def tensor {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (m * n)) (Fin (m * n)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B)

def phase {d : ℕ} (s : ZMod d) (z : Option (ZMod d))
    (x : ZMod d × ZMod d) : ZMod d :=
  z.elim (s * x.1) (fun t => x.2 - 2 * s * t * x.1)

def win {d : ℕ} (z : Option (ZMod d)) (x y : ZMod d × ZMod d) : ZMod d :=
  phase 1 z x + phase (-1) z y

def Valid {d : ℕ} [NeZero d]
    (α β : ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : Prop :=
  (∀ x, (α x).PosSemidef ∧ Matrix.trace (α x) = 1) ∧
  (∀ y, (β y).PosSemidef ∧ Matrix.trace (β y) = 1) ∧
  (∀ z c, (M z c).PosSemidef) ∧ (∀ z, ∑ c : ZMod d, M z c = 1)

def score {d : ℕ} [NeZero d]
    (α β : ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : ℝ :=
  (1 / ((d : ℝ) ^ 4 * ((d : ℝ) + 1))) *
    ∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d, ∑ z : Option (ZMod d),
      (Matrix.trace (tensor (α x) (β y) * M z (win z x y))).re

def mixtureScore {d L : ℕ} [NeZero d] (q : Fin L → ℝ)
    (α β : Fin L → ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin L → Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : ℝ :=
  ∑ l : Fin L, q l * score (α l) (β l) (M l)

def claim : Prop :=
  ∀ (d : ℕ) (hp : d.Prime), Odd d →
    letI : NeZero d := ⟨hp.ne_zero⟩
    ((∀ α β M, Valid (d := d) α β M → score (d := d) α β M ≤ 2 / ((d : ℝ) + 1)) ∧
     (∀ (L : ℕ) (q : Fin L → ℝ) α β M, (∀ l, 0 ≤ q l) → ∑ l, q l = 1 →
        (∀ l, Valid (d := d) (α l) (β l) (M l)) →
          mixtureScore (d := d) q α β M ≤ 2 / ((d : ℝ) + 1))) ∧
    (∃ α β M, Valid (d := d) α β M ∧ score (d := d) α β M = 2 / ((d : ℝ) + 1))

private theorem tensor_trace {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (tensor A B) = Matrix.trace A * Matrix.trace B := by
  rw [tensor.eq_1, ← Matrix.trace_kronecker]
  exact (Fintype.sum_equiv finProdFinEquiv _ _
    (fun p => by simp -congrConsts [Matrix.reindex_apply])).symm

private theorem tensor_frobSq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    RHLinalg.frobSq (tensor A B) = RHLinalg.frobSq A * RHLinalg.frobSq B := by
  simp -congrConsts only [frobSq_eq_sum]
  rw [← (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).sum_comp]
  simp -congrConsts only [tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  simp_rw -congrConsts [← (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).sum_comp]
  simp -congrConsts only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply,
    Complex.normSq_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  simp -congrConsts only [← Finset.mul_sum, ← Finset.sum_mul]

private theorem tensor_weighted_sum {m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) (A : ι → Matrix (Fin m) (Fin m) ℂ)
    (B : κ → Matrix (Fin n) (Fin n) ℂ) :
    tensor (∑ i, a i • A i) (∑ j, b j • B j) =
      ∑ i, ∑ j, (a i * b j) • tensor (A i) (B j) := by
  calc
    _ = Matrix.reindex finProdFinEquiv finProdFinEquiv
        (∑ i, ∑ j, (a i * b j) • Matrix.kronecker (A i) (B j)) := by
      apply congrArg (Matrix.reindex finProdFinEquiv finProdFinEquiv)
      change Matrix.kroneckerBilinear (R := ℂ) (∑ i, a i • A i) (∑ j, b j • B j) = _
      rw [LinearMap.map_sum₂]
      simp -congrConsts only [map_sum, map_smul, LinearMap.smul_apply, smul_smul]
      simp -congrConsts only [mul_comm]
      rfl
    _ = _ := by
      ext p q
      simp -congrConsts only [tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.sum_apply,
        Matrix.smul_apply]

private theorem density_frobSq_le_one {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) : RHLinalg.frobSq ρ ≤ 1 := by
  unfold RHLinalg.frobSq
  rw [hρ.isHermitian.eq]
  simpa -congrConsts [hTrace] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.psd_trace_sq ρ hρ

private theorem trace_tensor_le_energy {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (hC : RHLinalg.frobSq C ≤ (d : ℝ) ^ 2) :
    (Matrix.trace (tensor A B * C)).re ≤
      ((d : ℝ) / 2) * (RHLinalg.frobSq A + RHLinalg.frobSq B) := by
  have ha := frobSq_nonneg A
  have hb := frobSq_nonneg B
  have hc := trace_product_cauchy (tensor A B) C
  rw [tensor_frobSq] at hc
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht : (Matrix.trace (tensor A B * C)).re ^ 2 ≤
      (d : ℝ) ^ 2 * (RHLinalg.frobSq A * RHLinalg.frobSq B) := by
    calc
      _ ≤ Complex.normSq (Matrix.trace (tensor A B * C)) := by
        simpa -congrConsts only [pow_two] using Complex.re_sq_le_normSq _
      _ ≤ _ := hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hC (mul_nonneg ha hb)])
  have hsum : 0 ≤ (d : ℝ) / 2 * (RHLinalg.frobSq A + RHLinalg.frobSq B) :=
    mul_nonneg (div_nonneg hd (by norm_num)) (add_nonneg ha hb)
  apply le_of_sq_le_sq _ hsum
  nlinarith [sq_nonneg ((d : ℝ) * (RHLinalg.frobSq A - RHLinalg.frobSq B))]

private theorem povm_weighted_frobSq_le {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Matrix (Fin n) (Fin n) ℂ) (u : ι → ℂ)
    (hP : ∀ c, (P c).PosSemidef) (hSum : ∑ c, P c = 1) (hu : ∀ c, ‖u c‖ = 1) :
    RHLinalg.frobSq (∑ c, u c • P c) ≤ (n : ℝ) := by
  classical
  have hexp : RHLinalg.frobSq (∑ c, u c • P c) =
      ∑ c, ∑ b, (star (u c) * u b).re * (Matrix.trace (P c * P b)).re := by
    simp -congrConsts only [RHLinalg.frobSq, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, RCLike.re_eq_complex_re, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    rw [(hP c).isHermitian.eq]
    calc
      _ = ((star (u c) * u b) * Matrix.trace (P c * P b)).re :=
        congrArg Complex.re (by ring)
      _ = _ := by
        rw [Complex.mul_re,
          D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
            (P c) (P b) (hP c).isHermitian (hP b).isHermitian]
        ring
  rw [hexp]
  calc
    _ ≤ ∑ c, ∑ b, (Matrix.trace (P c * P b)).re := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro b _
      have hcoef : (star (u c) * u b).re ≤ 1 := by
        calc
          _ ≤ ‖star (u c) * u b‖ := Complex.re_le_norm _
          _ = 1 := by rw [norm_mul, norm_star, hu c, hu b, one_mul]
      simpa -congrConsts only [one_mul, RCLike.re_eq_complex_re] using
        mul_le_mul_of_nonneg_right hcoef
        (RHLinalg.trace_mul_nonneg_of_posSemidef (hP c) (hP b))
    _ = (Matrix.trace ((∑ c, P c) * (∑ b, P b))).re := by
      simp -congrConsts only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      rw [Finset.sum_comm]
    _ = n := by simp -congrConsts [hSum]

private def frequency {d : ℕ} (s : ZMod d) (z : Option (ZMod d))
    (k : ZMod d) : ZMod d × ZMod d :=
  z.elim (s * k, 0) (fun t => (-2 * s * t * k, k))

private def matrixFourier {d n : ℕ} [NeZero d]
    (ρ : ZMod d × ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (u : ZMod d × ZMod d) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ x : ZMod d × ZMod d, ZMod.stdAddChar (u.1 * x.1 + u.2 * x.2) • ρ x

private def stateMode {d n : ℕ} [NeZero d]
    (ρ : ZMod d × ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (s : ZMod d) (z : Option (ZMod d)) (k : ZMod d) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ x : ZMod d × ZMod d, ZMod.stdAddChar (k * phase s z x) • ρ x

private def measurementMode {d : ℕ} [NeZero d]
    (M : Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (z : Option (ZMod d)) (k : ZMod d) : Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  ∑ c : ZMod d, ZMod.stdAddChar (-(k * c)) • M z c

private theorem delta_expansion {d : ℕ} [NeZero d] (c w : ZMod d) :
    (if c = w then (1 : ℂ) else 0) =
      (d : ℂ)⁻¹ * ∑ k : ZMod d, ZMod.stdAddChar (k * (w - c)) := by
  simp_rw -congrConsts [mul_comm _ (w - c)]
  rw [D5.S3.Fourier.SparseGeneratorGapObstruction.char_sum]
  by_cases h : c = w
  · simp -congrConsts [h, NeZero.ne (d : ℂ)]
  · simp -congrConsts [h, sub_eq_zero, Ne.symm h]

private theorem scalar_parseval {d : ℕ} [NeZero d] (f : ZMod d × ZMod d → ℂ) :
    (∑ u : ZMod d × ZMod d, Complex.normSq
      (∑ x : ZMod d × ZMod d, ZMod.stdAddChar (u.1 * x.1 + u.2 * x.2) * f x)) =
      (d : ℝ) ^ 2 * ∑ x : ZMod d × ZMod d, Complex.normSq (f x) := by
  classical
  have hparse (g : ZMod d → ℂ) :
      (∑ u : ZMod d, Complex.normSq (∑ x : ZMod d, ZMod.stdAddChar (u * x) * g x)) =
        (d : ℝ) * ∑ x : ZMod d, Complex.normSq (g x) := by
    have hp := D5.S3.Fourier.FullBispectrumStability.cyclic_parseval g
    rw [Fintype.expect_eq_sum_div_card, ZMod.card] at hp
    have he := (eq_div_iff (NeZero.ne (d : ℝ))).mp hp
    calc
      _ = ∑ u : ZMod d, Complex.normSq (ZMod.dft g u) :=
        Fintype.sum_equiv (Equiv.neg _) _ _ (fun u => by
          simp -congrConsts only [Equiv.neg_apply, ZMod.dft_apply, mul_neg, neg_neg,
            smul_eq_mul, mul_comm])
      _ = _ := by simpa -congrConsts only [Complex.normSq_eq_norm_sq, mul_comm] using he.symm
  simp_rw -congrConsts [Fintype.sum_prod_type, AddChar.map_add_eq_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw -congrConsts [hparse, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw -congrConsts [← Finset.mul_sum, hparse]
  simp -congrConsts only [Finset.mul_sum, pow_two, mul_assoc]

private theorem matrix_parseval {d n : ℕ} [NeZero d]
    (ρ : ZMod d × ZMod d → Matrix (Fin n) (Fin n) ℂ) :
    (∑ u : ZMod d × ZMod d, RHLinalg.frobSq (matrixFourier ρ u)) =
      (d : ℝ) ^ 2 * ∑ x : ZMod d × ZMod d, RHLinalg.frobSq (ρ x) := by
  simp -congrConsts only [frobSq_eq_sum, matrixFourier, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  simp_rw -congrConsts [Finset.sum_comm (γ := ZMod d × ZMod d), scalar_parseval]
  simp -congrConsts only [Finset.mul_sum]

private theorem stateMode_eq_matrixFourier {d n : ℕ} [NeZero d]
    (ρ : ZMod d × ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (s : ZMod d) (z : Option (ZMod d)) (k : ZMod d) :
    stateMode ρ s z k = matrixFourier ρ (frequency s z k) := by
  rw [stateMode.eq_1, matrixFourier.eq_1]
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  cases z <;> rw [phase.eq_1] <;>
    simp -congrConsts only [frequency, Option.elim_none, Option.elim_some] <;> ring

private theorem frequency_ne_zero {d : ℕ} [NeZero d] [Fact d.Prime]
    (s : ZMod d) (hs : s ≠ 0) (z : Option (ZMod d)) (k : ZMod d) (hk : k ≠ 0) :
    frequency s z k ≠ 0 := by
  intro h
  cases z with
  | none => exact (mul_ne_zero hs hk) (congrArg Prod.fst h)
  | some t => exact hk (congrArg Prod.snd h)

private theorem frequency_bijective {d : ℕ} [NeZero d] [Fact d.Prime]
    (h2 : (2 : ZMod d) ≠ 0) (s : ZMod d) (hs : s ≠ 0) :
    Function.Bijective (fun p : Option (ZMod d) × {k : ZMod d // k ≠ 0} =>
      (⟨frequency s p.1 p.2.1, frequency_ne_zero s hs p.1 p.2.1 p.2.2⟩ :
        {u : ZMod d × ZMod d // u ≠ 0})) := by
  constructor
  · rintro ⟨z, k, hk⟩ ⟨w, l, hl⟩ h
    have he := congrArg Subtype.val h
    cases z with
    | none =>
      cases w with
      | none =>
        have hkl := mul_left_cancel₀ hs (congrArg Prod.fst he)
        simp_all -congrConsts
      | some t => exact (hl (congrArg Prod.snd he).symm).elim
    | some t =>
      cases w with
      | none => exact (hk (congrArg Prod.snd he)).elim
      | some r =>
        have hkl : k = l := congrArg Prod.snd he
        subst l
        have htr : t = r := mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr h2) hs)
          (mul_right_cancel₀ hk (congrArg Prod.fst he))
        subst r
        rfl
  · intro u
    by_cases hv : u.1.2 = 0
    · have hu : u.1.1 ≠ 0 := by
        intro h
        exact u.2 (Prod.ext h hv)
      refine ⟨(none, ⟨u.1.1 / s, div_ne_zero hu hs⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · dsimp only
        rw [frequency.eq_1]
        dsimp only [Option.elim_none]
        field_simp (disch := assumption)
      · exact hv.symm
    · refine ⟨(some (-u.1.1 / (2 * s * u.1.2)), ⟨u.1.2, hv⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · dsimp only
        rw [frequency.eq_1]
        dsimp only [Option.elim_some]
        field_simp (disch := solve | assumption | exact mul_ne_zero h2 hs |
          exact mul_ne_zero (mul_ne_zero h2 hs) hv)
      · rfl

private theorem sloped_parseval {d n : ℕ} [NeZero d] [Fact d.Prime]
    (h2 : (2 : ZMod d) ≠ 0) (s : ZMod d) (hs : s ≠ 0)
    (ρ : ZMod d × ZMod d → Matrix (Fin n) (Fin n) ℂ) :
    (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
      RHLinalg.frobSq (stateMode ρ s z k.1)) =
      (d : ℝ) ^ 2 * ∑ x : ZMod d × ZMod d, RHLinalg.frobSq (ρ x) -
        RHLinalg.frobSq (∑ x : ZMod d × ZMod d, ρ x) := by
  classical
  have hreindex : (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
      RHLinalg.frobSq (stateMode ρ s z k.1)) =
      ∑ u : {u : ZMod d × ZMod d // u ≠ 0}, RHLinalg.frobSq (matrixFourier ρ u.1) := by
    calc
      _ = ∑ p : Option (ZMod d) × {k : ZMod d // k ≠ 0},
          RHLinalg.frobSq (stateMode ρ s p.1 p.2.1) :=
        (Fintype.sum_prod_type _).symm
      _ = _ := Fintype.sum_equiv (Equiv.ofBijective _ (frequency_bijective h2 s hs)) _ _
        (fun p => congrArg RHLinalg.frobSq (stateMode_eq_matrixFourier ρ s p.1 p.2.1))
  rw [hreindex]
  have herase := Finset.sum_subtype (F := inferInstance) (Finset.univ.erase (0 : ZMod d × ZMod d))
    (by simp -congrConsts : ∀ u, u ∈ Finset.univ.erase (0 : ZMod d × ZMod d) ↔ u ≠ 0)
    (fun u => RHLinalg.frobSq (matrixFourier ρ u))
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun u => RHLinalg.frobSq (matrixFourier ρ u)) (Finset.mem_univ (0 : ZMod d × ZMod d))
  rw [herase, matrix_parseval] at hsplit
  have hzero : matrixFourier ρ (0 : ZMod d × ZMod d) = ∑ x, ρ x := by
    simp -congrConsts [matrixFourier]
  rw [hzero] at hsplit
  linarith

private theorem state_energy_le {d : ℕ} [NeZero d] [Fact d.Prime]
    (h2 : (2 : ZMod d) ≠ 0) (s : ZMod d) (hs : s ≠ 0)
    (ρ : ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ x, (ρ x).PosSemidef ∧ Matrix.trace (ρ x) = 1) :
    (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
      RHLinalg.frobSq (stateMode ρ s z k.1)) ≤ (d : ℝ) ^ 4 - (d : ℝ) ^ 3 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp : (∑ x : ZMod d × ZMod d, RHLinalg.frobSq (ρ x)) ≤ (d : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ x : ZMod d × ZMod d, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => density_frobSq_le_one (ρ x) (hρ x).1 (hρ x).2
      _ = _ := by simp -congrConsts [ZMod.card, pow_two]
  have htr : Matrix.trace (∑ x : ZMod d × ZMod d, ρ x) = (d : ℂ) ^ 2 := by
    simp -congrConsts [Matrix.trace_sum, fun x => (hρ x).2, ZMod.card, pow_two]
  have hc := trace_product_cauchy (∑ x : ZMod d × ZMod d, ρ x) (1 : Matrix (Fin d) (Fin d) ℂ)
  have hone : RHLinalg.frobSq (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
    simp -congrConsts [RHLinalg.frobSq]
  rw [Matrix.mul_one, htr, hone] at hc
  simp -congrConsts only [map_pow, Complex.normSq_natCast] at hc
  rw [sloped_parseval h2 s hs ρ]
  have hl : (d : ℝ) ^ 3 ≤ RHLinalg.frobSq (∑ x : ZMod d × ZMod d, ρ x) := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith [hc]
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (d : ℝ))]

private theorem score_fourier_expansion {d : ℕ} [NeZero d]
    (α β : ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (h : Valid α β M) :
    score α β M = 1 / (d : ℝ) + (1 / ((d : ℝ) ^ 5 * ((d : ℝ) + 1))) *
      ∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
        (Matrix.trace (tensor (stateMode α 1 z k.1) (stateMode β (-1) z k.1) *
          measurementMode M z k.1)).re := by
  classical
  have hmode (z : Option (ZMod d)) (k : ZMod d) :
      Matrix.trace (tensor (stateMode α 1 z k) (stateMode β (-1) z k) *
        measurementMode M z k) =
      ∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d, ∑ c : ZMod d,
        ZMod.stdAddChar (k * (win z x y - c)) *
          Matrix.trace (tensor (α x) (β y) * M z c) := by
    simp -congrConsts only [stateMode, measurementMode, tensor_weighted_sum, Matrix.sum_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro c _
    rw [show k * (win z x y - c) =
      k * phase 1 z x + k * phase (-1) z y + -(k * c) by unfold win; ring]
    simp -congrConsts only [AddChar.map_add_eq_mul]
    ring
  have hxy (x y : ZMod d × ZMod d) (z : Option (ZMod d)) :
      Matrix.trace (tensor (α x) (β y) * M z (win z x y)) =
      (d : ℂ)⁻¹ * ∑ k : ZMod d, ∑ c : ZMod d,
        ZMod.stdAddChar (k * (win z x y - c)) *
          Matrix.trace (tensor (α x) (β y) * M z c) := by
    calc
      _ = ∑ c : ZMod d, (if c = win z x y then (1 : ℂ) else 0) *
          Matrix.trace (tensor (α x) (β y) * M z c) := by simp -congrConsts
      _ = _ := by
        simp_rw -congrConsts [delta_expansion, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
  have hz (z : Option (ZMod d)) :
      (∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d,
        Matrix.trace (tensor (α x) (β y) * M z (win z x y))) =
      (d : ℂ)⁻¹ * ∑ k : ZMod d,
        Matrix.trace (tensor (stateMode α 1 z k) (stateMode β (-1) z k) *
          measurementMode M z k) := by
    simp_rw -congrConsts [hxy, ← Finset.mul_sum, hmode]
    congr 1
    exact Finset.sum_comm_cycle
  have hzero (z : Option (ZMod d)) :
      Matrix.trace (tensor (stateMode α 1 z 0) (stateMode β (-1) z 0) *
        measurementMode M z 0) = (d : ℂ) ^ 4 := by
    simp -congrConsts only [stateMode, measurementMode, zero_mul, neg_zero, AddChar.map_zero_eq_one,
      one_smul, h.2.2.2 z, Matrix.mul_one, tensor_trace, Matrix.trace_sum,
      fun x => (h.1 x).2, fun y => (h.2.1 y).2]
    simp -congrConsts [ZMod.card, pow_succ, mul_assoc]
  have hsplit (z : Option (ZMod d)) :
      (∑ k : ZMod d, (Matrix.trace
        (tensor (stateMode α 1 z k) (stateMode β (-1) z k) * measurementMode M z k)).re) =
      (d : ℝ) ^ 4 + ∑ k : {k : ZMod d // k ≠ 0}, (Matrix.trace
        (tensor (stateMode α 1 z k.1) (stateMode β (-1) z k.1) *
          measurementMode M z k.1)).re := by
    have herase := Finset.sum_subtype (F := inferInstance) (Finset.univ.erase (0 : ZMod d))
      (by simp -congrConsts : ∀ k, k ∈ Finset.univ.erase (0 : ZMod d) ↔ k ≠ 0)
      (fun k => (Matrix.trace (tensor (stateMode α 1 z k) (stateMode β (-1) z k) *
        measurementMode M z k)).re)
    have hh := Finset.sum_erase_add Finset.univ
      (fun k => (Matrix.trace (tensor (stateMode α 1 z k) (stateMode β (-1) z k) *
        measurementMode M z k)).re) (Finset.mem_univ (0 : ZMod d))
    rw [herase, hzero] at hh
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re] at hh
    linarith only [hh]
  have hreal (z : Option (ZMod d)) :
      (∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d,
        (Matrix.trace (tensor (α x) (β y) * M z (win z x y))).re) =
      (d : ℝ)⁻¹ * ((d : ℝ) ^ 4 + ∑ k : {k : ZMod d // k ≠ 0}, (Matrix.trace
        (tensor (stateMode α 1 z k.1) (stateMode β (-1) z k.1) *
          measurementMode M z k.1)).re) := by
    rw [← hsplit]
    have hr := congrArg Complex.re (hz z)
    simpa -congrConsts using hr
  have horder : (∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d,
      ∑ z : Option (ZMod d), (Matrix.trace (tensor (α x) (β y) * M z (win z x y))).re) =
      ∑ z : Option (ZMod d), ∑ x : ZMod d × ZMod d, ∑ y : ZMod d × ZMod d,
        (Matrix.trace (tensor (α x) (β y) * M z (win z x y))).re := by
    exact Finset.sum_comm_cycle
  rw [score, horder]
  simp_rw -congrConsts [hreal, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp -congrConsts only [Finset.sum_const, Finset.card_univ, Fintype.card_option, ZMod.card,
    nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  have hd : (d : ℝ) ≠ 0 := NeZero.ne _
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  generalize (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
    (Matrix.trace (tensor (stateMode α 1 z k.1) (stateMode β (-1) z k.1) *
      measurementMode M z k.1)).re) = t
  field_simp (disch := positivity)

private theorem fixed_score_le {d : ℕ} [NeZero d] [Fact d.Prime]
    (h2 : (2 : ZMod d) ≠ 0)
    (α β : ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (h : Valid α β M) : score α β M ≤ 2 / ((d : ℝ) + 1) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hm (z : Option (ZMod d)) (k : ZMod d) :
      RHLinalg.frobSq (measurementMode M z k) ≤ (d : ℝ) ^ 2 := by
    rw [measurementMode.eq_1]
    simpa -congrConsts [pow_two] using povm_weighted_frobSq_le (M z)
      (fun c => ZMod.stdAddChar (-(k * c))) (h.2.2.1 z) (h.2.2.2 z)
      (fun c => AddChar.norm_apply _ _)
  have ht : (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
      (Matrix.trace (tensor (stateMode α 1 z k.1) (stateMode β (-1) z k.1) *
        measurementMode M z k.1)).re) ≤
      (d : ℝ) * ((d : ℝ) ^ 4 - (d : ℝ) ^ 3) := by
    calc
      _ ≤ ∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
          ((d : ℝ) / 2) * (RHLinalg.frobSq (stateMode α 1 z k.1) +
            RHLinalg.frobSq (stateMode β (-1) z k.1)) :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun k _ =>
          trace_tensor_le_energy _ _ _ (hm z k.1)
      _ = ((d : ℝ) / 2) *
          ((∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
            RHLinalg.frobSq (stateMode α 1 z k.1)) +
           (∑ z : Option (ZMod d), ∑ k : {k : ZMod d // k ≠ 0},
            RHLinalg.frobSq (stateMode β (-1) z k.1))) := by
        simp -congrConsts only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ _ := by
        have ha := state_energy_le h2 1 one_ne_zero α h.1
        have hb := state_energy_le h2 (-1) (neg_ne_zero.mpr one_ne_zero) β h.2.1
        calc
          _ ≤ ((d : ℝ) / 2) *
              (((d : ℝ) ^ 4 - (d : ℝ) ^ 3) + ((d : ℝ) ^ 4 - (d : ℝ) ^ 3)) :=
            mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
          _ = _ := by ring
  rw [score_fourier_expansion α β M h]
  calc
    _ ≤ 1 / (d : ℝ) + (1 / ((d : ℝ) ^ 5 * ((d : ℝ) + 1))) *
        ((d : ℝ) * ((d : ℝ) ^ 4 - (d : ℝ) ^ 3)) := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ht
        (show 0 ≤ 1 / ((d : ℝ) ^ 5 * ((d : ℝ) + 1)) by positivity))
    _ = _ := by field_simp (disch := positivity); ring

private theorem mixture_score_le {d L : ℕ} [NeZero d] [Fact d.Prime]
    (h2 : (2 : ZMod d) ≠ 0) (q : Fin L → ℝ)
    (α β : Fin L → ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin L → Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (hq : ∀ l, 0 ≤ q l) (hSum : (∑ l : Fin L, q l) = 1)
    (hValid : ∀ l, Valid (α l) (β l) (M l)) :
    mixtureScore q α β M ≤ 2 / ((d : ℝ) + 1) := by
  calc
    _ ≤ ∑ l : Fin L, q l * (2 / ((d : ℝ) + 1)) := Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_left (fixed_score_le h2 (α l) (β l) (M l) (hValid l)) (hq l)
    _ = _ := by rw [← Finset.sum_mul, hSum, one_mul]

private def classicalEncoding {d : ℕ} [NeZero d] :
    ZMod d × ZMod d → Matrix (Fin d) (Fin d) ℂ :=
  fun x => Matrix.diagonal (fun i : Fin d =>
    if ZMod.finEquiv d i = x.1 then (1 : ℂ) else 0)

private def differenceLabel {d : ℕ} [NeZero d] (p : Fin (d * d)) : ZMod d :=
  ZMod.finEquiv d (((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).1) -
    ZMod.finEquiv d (((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).2)

private def classicalMeasurement {d : ℕ} [NeZero d] :
    Option (ZMod d) → ZMod d → Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  fun z c => z.elim
    (Matrix.diagonal (fun p : Fin (d * d) =>
      if differenceLabel p = c then (1 : ℂ) else 0))
    (fun _ => (1 / (d : ℝ)) • (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ))

private theorem classical_valid {d : ℕ} [NeZero d] :
    Valid (classicalEncoding (d := d)) classicalEncoding classicalMeasurement := by
  classical
  have hstate (x : ZMod d × ZMod d) :
      (classicalEncoding x).PosSemidef ∧ Matrix.trace (classicalEncoding x) = 1 := by
    constructor
    · apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      by_cases hi : ZMod.finEquiv d i = x.1 <;> simp -congrConsts [hi]
    · change Matrix.trace (Matrix.diagonal (fun i : Fin d =>
        if ZMod.finEquiv d i = x.1 then (1 : ℂ) else 0)) = 1
      rw [Matrix.trace_diagonal]
      simpa -congrConsts using (ZMod.finEquiv d).toEquiv.sum_comp
        (fun c : ZMod d => if c = x.1 then (1 : ℂ) else 0)
  refine ⟨hstate, hstate, ?_, ?_⟩
  · intro z c
    cases z with
    | none =>
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro p
      by_cases hi : differenceLabel p = c <;> simp -congrConsts [hi]
    | some t => exact Matrix.PosSemidef.one.smul (by positivity : 0 ≤ 1 / (d : ℝ))
  · intro z
    cases z with
    | none =>
      ext p q
      by_cases hpq : p = q
      · subst q
        simp -congrConsts [classicalMeasurement, Matrix.sum_apply]
      · simp -congrConsts [classicalMeasurement, Matrix.sum_apply, hpq]
    | some t =>
      change (∑ _ : ZMod d, (1 / (d : ℝ)) •
        (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)) = 1
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul]
      simp -congrConsts [NeZero.ne (d : ℝ)]

private theorem classical_win_probability {d : ℕ} [NeZero d]
    (x y : ZMod d × ZMod d) (z : Option (ZMod d)) :
    (Matrix.trace (tensor (classicalEncoding x) (classicalEncoding y) *
      classicalMeasurement z (win z x y))).re = z.elim (1 : ℝ) (fun _ => 1 / (d : ℝ)) := by
  have hx := (classical_valid (d := d)).1 x |>.2
  have hy := (classical_valid (d := d)).2.1 y |>.2
  cases z with
  | none =>
    have hdiag : tensor (classicalEncoding x) (classicalEncoding y) =
        Matrix.diagonal (fun p : Fin (d * d) =>
          (if ZMod.finEquiv d ((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).1 =
              x.1 then (1 : ℂ) else 0) *
          (if ZMod.finEquiv d ((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).2 =
              y.1 then (1 : ℂ) else 0)) := by
      unfold tensor classicalEncoding
      simp -congrConsts only [Matrix.kronecker]
      rw [Matrix.diagonal_kronecker_diagonal]
      simpa -congrConsts only [Matrix.reindex_apply, Function.comp_def] using
        (Matrix.submatrix_diagonal_equiv
          (fun p : Fin d × Fin d =>
            (if ZMod.finEquiv d p.1 = x.1 then (1 : ℂ) else 0) *
            (if ZMod.finEquiv d p.2 = y.1 then (1 : ℂ) else 0))
          (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm)
    have hmul : tensor (classicalEncoding x) (classicalEncoding y) *
        classicalMeasurement none (win none x y) =
          tensor (classicalEncoding x) (classicalEncoding y) := by
      rw [hdiag]
      change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext p
      rw [differenceLabel.eq_1, win.eq_1]
      simp -congrConsts only [phase, Option.elim_none, one_mul, neg_one_mul]
      by_cases hpx : ZMod.finEquiv d
        ((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).1 = x.1 <;>
        by_cases hpy : ZMod.finEquiv d
          ((finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm p).2 = y.1 <;>
        simp_all -congrConsts [sub_eq_add_neg]
    rw [hmul, tensor_trace, hx, hy]
    simp -congrConsts
  | some t =>
    rw [classicalMeasurement.eq_1]
    simp -congrConsts [Matrix.trace_smul, tensor_trace, hx, hy]

private theorem classical_score {d : ℕ} [NeZero d] :
    score (classicalEncoding (d := d)) classicalEncoding classicalMeasurement =
      2 / ((d : ℝ) + 1) := by
  unfold score
  simp_rw -congrConsts [classical_win_probability]
  simp -congrConsts [univ_option, Finset.sum_insertNone, ZMod.card, NeZero.ne (d : ℝ)]
  field_simp (disch := first | exact NeZero.ne (d : ℝ) | positivity)
  norm_num

theorem result : claim := by
  intro d hp hodd
  let : NeZero d := ⟨hp.ne_zero⟩
  let : Fact d.Prime := ⟨hp⟩
  have h2 : (2 : ZMod d) ≠ 0 := by
    intro he
    have hdiv : d ∣ 2 := (CharP.cast_eq_zero_iff (ZMod d) d 2).mp (by simpa using he)
    have hd : d = 2 := (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.ne_one
    subst d
    norm_num at hodd
  exact ⟨⟨fun α β M h => fixed_score_le h2 α β M h,
    fun L q α β M hq hsum hv => mixture_score_le h2 q α β M hq hsum hv⟩,
    ⟨classicalEncoding, classicalEncoding, classicalMeasurement, classical_valid, classical_score⟩⟩

end D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
