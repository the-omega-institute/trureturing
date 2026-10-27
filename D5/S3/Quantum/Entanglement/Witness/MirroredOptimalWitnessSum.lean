/- GID: D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Distinct optimal witnesses have an optimal sum and overlapping detection sets. -/
import D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import D5.S3.QuantumBounds.PeritoTsirelson
import D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation

/-! # Optimal witnesses with an optimal sum

A uniform four-entry family has spanning zero product vectors. Its members and their sums
are optimal, and normalized diagonal superpositions separate their detection sets.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (blockPositive)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction (tensor)
open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace (trace_rank_one)
open D5.S3.QuantumBounds.PeritoTsirelson (maxEntangledVector maxEntangled max_entangled_density)
open D5.S3.QuantumBounds.CHSHWitness (complex_sqrt_two_ne_zero)
open D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence (probes construction)
open D5.S3.Observer.Existence.EmpiricalReflexiveSeparation (complex_sqrt_two_sq)

/-- A Hermitian block-positive operator detecting a density matrix. -/
def IsWitness {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  A.IsHermitian ∧ blockPositive A ∧
    ∃ ρ, IsDensity ρ ∧ (A * ρ).trace.re < 0

/-- Membership in the detection set of an operator. -/
def Detects {d : ℕ} (A ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsDensity ρ ∧ (A * ρ).trace.re < 0

/-- No nonzero positive semidefinite subtraction preserves block positivity. -/
def IsOptimalWitness {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsWitness A ∧ ∀ ε : ℝ, 0 < ε →
    ∀ P, P.PosSemidef → P ≠ 0 → ¬ blockPositive (A - (ε : ℂ) • P)

/-- Optimal witnesses with an optimal sum and intersecting, distinct detection sets for d ≥ 3. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ W M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      IsOptimalWitness W ∧ IsOptimalWitness M ∧ IsOptimalWitness (W + M) ∧
      (∃ ρ, Detects W ρ ∧ ¬ Detects M ρ) ∧
      (∃ ρ, Detects M ρ ∧ ¬ Detects W ρ) ∧
      (∃ ρ, Detects W ρ ∧ Detects M ρ)

private def wr {d : ℕ} [NeZero d] (r : Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  single (0, r) (0, r) 1 + single (r, 0) (r, 0) 1 -
    single (0, 0) (r, r) 1 - single (r, r) (0, 0) 1

private def pairVector {d : ℕ} [NeZero d] (r : Fin d) : Fin d × Fin d → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Pi.single (0, 0) 1 + Pi.single (r, r) 1)

private theorem wr_hermitian {d : ℕ} [NeZero d] (r : Fin d) : (wr r).IsHermitian := by
  change (wr r)ᴴ = wr r
  simp only [wr, conjTranspose_sub, conjTranspose_add, conjTranspose_single, star_one]
  abel

private theorem wr_expectation {d : ℕ} [NeZero d] (r : Fin d)
    (v : Fin d × Fin d → ℂ) :
    star v ⬝ᵥ (wr r *ᵥ v) =
      star (v (0, r)) * v (0, r) + star (v (r, 0)) * v (r, 0) -
        star (v (0, 0)) * v (r, r) - star (v (r, r)) * v (0, 0) := by
  simp only [wr, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
    single_mulVec_eq, dotProduct_smul, dotProduct_single, Pi.star_apply, smul_eq_mul, mul_one,
    one_mul]
  ring

private theorem product_expectation {d : ℕ} [NeZero d] (r : Fin d) (x y : Fin d → ℂ) :
    star (tensor x y) ⬝ᵥ (wr r *ᵥ tensor x y) =
      (Complex.normSq (x 0 * star (y r) - x r * star (y 0)) : ℂ) := by
  rw [wr_expectation, Complex.normSq_eq_conj_mul_self]
  simp only [tensor, vecMulVec_apply, star_mul, Complex.star_def, map_sub, map_mul,
    Complex.conj_conj]
  ring

private theorem wr_blockPositive {d : ℕ} [NeZero d] (r : Fin d) :
    blockPositive (wr r) := by
  intro x y
  change 0 ≤ star (tensor x y) ⬝ᵥ (wr r *ᵥ tensor x y)
  rw [product_expectation, Complex.zero_le_real]
  exact Complex.normSq_nonneg _

private theorem pair_density {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    IsDensity (vecMulVec (pairVector r) (star (pairVector r))) := by
  refine ⟨posSemidef_vecMulVec_self_star _, ?_⟩
  rw [trace_vecMulVec, dotProduct_comm]
  simpa only [probes, Prod.mk.injEq, true_and, false_and, Ne.symm hr, ite_false,
    pairVector] using
    (construction (fun _ : Unit => ((0 : Fin d), (0 : Fin d)))
      (fun _ : Unit => (r, r))).1 (.inr ())

private theorem pair_expectation {d : ℕ} [NeZero d] (r s : Fin d)
    (hr : r ≠ 0) :
    (wr r * vecMulVec (pairVector s) (star (pairVector s))).trace =
      if r = s then -1 else 0 := by
  rw [trace_rank_one, wr_expectation]
  have hz : (Real.sqrt 2 : ℂ) ≠ 0 := complex_sqrt_two_ne_zero
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := complex_sqrt_two_sq
  by_cases h : r = s
  · subst s
    simp [pairVector, hr, Ne.symm hr]
    field_simp
    linear_combination hsq
  · simp [pairVector, hr, h]

private theorem omega_density {d : ℕ} [NeZero d] :
    IsDensity (maxEntangled (Fin d)) := by
  refine ⟨posSemidef_vecMulVec_self_star _, ?_⟩
  exact (max_entangled_density (Fin d)).2

private theorem omega_expectation {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    (wr r * maxEntangled (Fin d)).trace = -2 / (d : ℂ) := by
  rw [maxEntangled, trace_rank_one, wr_expectation]
  have hz : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d) : (0 : ℝ) < d)))
  have hsq : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)
  simp only [maxEntangledVector, Fintype.card_fin, Complex.ofReal_inv, hr, Ne.symm hr,
    ite_false, ite_true, star_zero, mul_zero, add_zero, zero_sub, Complex.star_def,
    map_inv₀, Complex.conj_ofReal]
  rw [div_eq_mul_inv, ← hsq]
  field_simp
  ring

/-- Complex linear combinations of conjugate product vectors recover every basis vector. -/
private theorem conjugate_products_span (d : ℕ) :
    Submodule.span ℂ (Set.range (fun x : Fin d → ℂ => tensor x (star x))) = ⊤ := by
  classical
  let V := Submodule.span ℂ (Set.range (fun x : Fin d → ℂ => tensor x (star x)))
  have hv (x : Fin d → ℂ) : tensor x (star x) ∈ V :=
    Submodule.subset_span ⟨x, rfl⟩
  have hp (x y : Fin d → ℂ) :
      tensor x (star y) = (1 / 2 : ℂ) •
        (tensor (x + y) (star (x + y)) - tensor x (star x) - tensor y (star y) +
          Complex.I • (tensor (x + Complex.I • y) (star (x + Complex.I • y)) -
            tensor x (star x) - tensor y (star y))) := by
    ext p
    simp only [tensor, vecMulVec_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.star_apply,
      smul_eq_mul, star_add, star_mul, Complex.star_def, Complex.conj_I]
    ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_three] <;> ring
  have he (i j : Fin d) : Pi.single (i, j) (1 : ℂ) ∈ V := by
    have hid : tensor (Pi.single i (1 : ℂ)) (star (Pi.single j (1 : ℂ))) =
        Pi.single (i, j) (1 : ℂ) := by
      rw [Pi.star_single, star_one]
      change Function.uncurry (vecMulVec (Pi.single i (1 : ℂ)) (Pi.single j 1)) = _
      rw [← single_eq_single_vecMulVec_single, single_eq_of_single_single]
      exact Pi.uncurry_single_single i j 1
    rw [← hid, hp]
    exact V.smul_mem _ (V.add_mem (V.sub_mem (V.sub_mem (hv _) (hv _)) (hv _))
      (V.smul_mem _ (V.sub_mem (V.sub_mem (hv _) (hv _)) (hv _))))
  apply top_unique
  intro v _
  rw [pi_eq_sum_univ' v]
  exact V.sum_mem (fun p _ => V.smul_mem _ (he p.1 p.2))

/-- A spanning set of zero product vectors forbids every nonzero PSD subtraction. -/
private theorem spanning_optimal {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hA : IsWitness A)
    (S : Set (Fin d × Fin d → ℂ)) (hS : Submodule.span ℂ S = ⊤)
    (hzero : ∀ v ∈ S, ∃ x y, v = tensor x y ∧ star v ⬝ᵥ (A *ᵥ v) = 0) :
    IsOptimalWitness A := by
  refine ⟨hA, ?_⟩
  intro ε hε P hP hPn hBP
  have hk (v : Fin d × Fin d → ℂ) (hv : v ∈ S) : P *ᵥ v = 0 := by
    obtain ⟨x, y, rfl, hz⟩ := hzero v hv
    have h := hBP x y
    change 0 ≤ star (tensor x y) ⬝ᵥ ((A - (ε : ℂ) • P) *ᵥ tensor x y) at h
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hz] at h
    have hq := hP.dotProduct_mulVec_nonneg (tensor x y)
    apply hP.dotProduct_mulVec_zero_iff.mp
    apply Complex.ext
    · have h₁ := (Complex.nonneg_iff.mp h).1
      have h₂ := (Complex.nonneg_iff.mp hq).1
      simp only [smul_eq_mul, Complex.sub_re, Complex.zero_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h₁
      simp only [Complex.zero_re]
      exact le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hε) h₂
    · exact (Complex.nonneg_iff.mp hq).2.symm
  have hl : P.mulVecLin = 0 :=
    (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hS).mpr (fun v => hk v v.property)
  apply hPn
  exact Matrix.toLin'.injective (hl.trans Matrix.mulVecLin_zero.symm)

private theorem wr_zero {d : ℕ} [NeZero d] (r : Fin d) (x : Fin d → ℂ) :
    star (tensor x (star x)) ⬝ᵥ (wr r *ᵥ tensor x (star x)) = 0 := by
  rw [product_expectation]
  simp only [Pi.star_apply, star_star, mul_comm (x 0) (x r), sub_self,
    Complex.normSq_zero, Complex.ofReal_zero]

private theorem wr_optimal {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    IsOptimalWitness (wr r) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hw : IsWitness (wr r) := by
    refine ⟨wr_hermitian r, wr_blockPositive r, maxEntangled (Fin d),
      omega_density, ?_⟩
    rw [omega_expectation r hr]
    simpa using div_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0) hd
  apply spanning_optimal (wr r) hw
    (Set.range (fun x : Fin d → ℂ => tensor x (star x))) (conjugate_products_span d)
  rintro v ⟨x, rfl⟩
  exact ⟨x, star x, rfl, wr_zero r x⟩

private theorem sum_optimal {d : ℕ} [NeZero d] (r s : Fin d) (hr : r ≠ 0) (hs : s ≠ 0) :
    IsOptimalWitness (wr r + wr s) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hBP : blockPositive (wr r + wr s) := by
    intro x y
    rw [add_mulVec, dotProduct_add]
    exact add_nonneg (wr_blockPositive r x y) (wr_blockPositive s x y)
  have hw : IsWitness (wr r + wr s) := by
    refine ⟨(wr_hermitian r).add (wr_hermitian s), hBP,
      maxEntangled (Fin d), omega_density, ?_⟩
    rw [add_mul, trace_add, omega_expectation r hr, omega_expectation s hs]
    have hneg : (-2 / (d : ℂ)).re < 0 := by
      simpa using div_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0) hd
    simpa only [Complex.add_re] using add_neg hneg hneg
  apply spanning_optimal (wr r + wr s) hw
    (Set.range (fun x : Fin d → ℂ => tensor x (star x))) (conjugate_products_span d)
  rintro v ⟨x, rfl⟩
  refine ⟨x, star x, rfl, ?_⟩
  rw [add_mulVec, dotProduct_add, wr_zero, wr_zero, add_zero]

private theorem detection_separation {d : ℕ} [NeZero d] (r s : Fin d)
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    (∃ ρ, Detects (wr r) ρ ∧ ¬ Detects (wr s) ρ) ∧
    (∃ ρ, Detects (wr s) ρ ∧ ¬ Detects (wr r) ρ) ∧
    (∃ ρ, Detects (wr r) ρ ∧ Detects (wr s) ρ) := by
  have hneg : (-2 / (d : ℂ)).re < 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    simpa using div_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0) hd
  refine ⟨⟨vecMulVec (pairVector r) (star (pairVector r)), ?_, ?_⟩,
    ⟨vecMulVec (pairVector s) (star (pairVector s)), ?_, ?_⟩,
    ⟨maxEntangled (Fin d), ?_, ?_⟩⟩
  · exact ⟨pair_density r hr, by rw [pair_expectation r r hr]; norm_num⟩
  · rintro ⟨_, h⟩
    rw [pair_expectation s r hs, ite_eq_right hrs.symm] at h
    simp at h
  · exact ⟨pair_density s hs, by rw [pair_expectation s s hs]; norm_num⟩
  · rintro ⟨_, h⟩
    rw [pair_expectation r s hr, ite_eq_right hrs] at h
    simp at h
  · exact ⟨omega_density, by rw [omega_expectation r hr]; exact hneg⟩
  · exact ⟨omega_density, by rw [omega_expectation s hs]; exact hneg⟩

/-- Optimal witnesses can have an optimal sum and incomparable, overlapping detection sets. -/
theorem result : claim := by
  intro d hd
  let : NeZero d := ⟨by omega⟩
  let r : Fin d := ⟨1, by omega⟩
  let s : Fin d := ⟨2, by omega⟩
  have hr : r ≠ 0 := by intro h; have := congrArg Fin.val h; simp [r] at this
  have hs : s ≠ 0 := by intro h; have := congrArg Fin.val h; simp [s] at this
  have hrs : r ≠ s := by intro h; have := congrArg Fin.val h; simp [r, s] at this
  exact ⟨wr r, wr s, wr_optimal r hr, wr_optimal s hs, sum_optimal r s hr hs,
    detection_separation r s hr hs hrs⟩

end D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
