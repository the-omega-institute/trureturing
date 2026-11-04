/- GID: D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/CoolingMapThermalOperationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim; result=D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result; claim=D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim
   digest: A four-level cooling transition excludes every finite ground-space thermal operation. -/

import D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

/-! A cooling-map transition obstructed by finite ground-space unitary Gram relations. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.SLDSpectralEnergy
open D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer (Pm)

namespace D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation

/-- A source cooling Kraus operator in increasing energy order. -/
def IsCoolingKraus {d : ℕ} (K : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  K.IsDiag ∨ ∃ j k : Fin d, j < k ∧ ∃ c : ℂ, K = c • Matrix.single j k 1

/-- Feasibility of a transition through a finite cooling Kraus channel. -/
def IsCoolingMap {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (n : ℕ) (K : Fin n → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, IsCoolingKraus (K i)) ∧ (∑ i, (K i)ᴴ * K i) = 1 ∧
      MatrixMap.of_kraus K K ρ = σ

/-- All coordinates attaining the least ancilla energy, including degeneracy. -/
def groundSet {m : ℕ} (e : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun a => ∀ b, e a ≤ e b)

/-- The normalized projector onto the full ancilla ground eigenspace. -/
def groundState {m : ℕ} (e : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun a => if a ∈ groundSet e then ((groundSet e).card : ℂ)⁻¹ else 0)

/-- Commutation with the diagonal total Hamiltonian. -/
def IsEnergyConserving {d m : ℕ} (E : Fin d → ℝ) (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) : Prop :=
  U * diagonal (fun x => ((E x.1 + e x.2 : ℝ) : ℂ)) =
    diagonal (fun x => ((E x.1 + e x.2 : ℝ) : ℂ)) * U

/-- The paper's idealized low-temperature thermal output. -/
def thermalOutput {d m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (U * Matrix.kronecker ρ (groundState e) * Uᴴ)

/-- Conjecture 1 under the preregistered finite ground-space reading. -/
def claim : Prop :=
  ∀ (d : ℕ) (E : Fin d → ℝ), StrictMono E →
    (∀ i j k l : Fin d, i < j → k < l → E j - E i = E l - E k →
      i = k ∧ j = l) →
    ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
      IsCoolingMap ρ σ →
      ∃ (m : ℕ) (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin d × Fin m) ℂ),
        0 < m ∧ IsEnergyConserving E e U ∧ thermalOutput e U ρ = σ

private def levels : Fin 4 → ℝ := ![0, 1, 3, 7]

private def factor : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0; 0, 1; 3 / 5, 4 / 5; 3 / 5, 4 * Complex.I / 5]

private def sigma : Matrix (Fin 4) (Fin 4) ℂ := (1 / 4 : ℝ) • (factor * factorᴴ)

private def kraus (a : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  diagonal (fun i => factor i a)

private lemma levels_valid : StrictMono levels ∧
    (∀ i j k l : Fin 4, i < j → k < l → levels j - levels i = levels l - levels k →
      i = k ∧ j = l) := by
  norm_num [StrictMono, Fin.forall_fin_succ, levels.eq_1]

private lemma kraus_complete : (∑ i, (kraus i)ᴴ * kraus i) = 1 := by
  simp only [kraus.eq_1]
  apply D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.diagonal_kraus_complete
  intro i
  fin_cases i <;> norm_num [factor.eq_1, Fin.sum_univ_two, Complex.sq_norm,
    Complex.normSq_apply]

private lemma sigma_diagonal (j : Fin 4) : sigma j j = 1 / 4 := by
  fin_cases j <;>
    norm_num [sigma.eq_1, factor.eq_1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.star_def, Matrix.vecMul, dotProduct, map_ofNat,
      map_div₀, map_mul]
  all_goals ring_nf
  all_goals norm_num

private lemma instance_density : IsDensity Pm ∧ IsDensity sigma := by
  change (Pm.PosSemidef ∧ trace Pm = 1) ∧ (sigma.PosSemidef ∧ trace sigma = 1)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · convert posSemidef_vecMulVec_self_star (fun _ : Fin 4 => (1 / 2 : ℂ)) using 1
    ext i j
    norm_num [Pm, vecMulVec]
  · norm_num [trace, Pm, Fin.sum_univ_four]
  · exact (posSemidef_self_mul_conjTranspose factor).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
  · change (∑ j, sigma j j) = 1
    simp only [sigma_diagonal]
    norm_num

private lemma instance_cooling : IsCoolingMap Pm sigma := by
  refine ⟨2, kraus, ?_, kraus_complete, ?_⟩
  · intro i
    left
    fin_cases i <;> exact Matrix.isDiag_diagonal _
  · change (∑ a, kraus a * Pm * (kraus a)ᴴ) = sigma
    ext i j
    calc
      (∑ a, kraus a * Pm * (kraus a)ᴴ) i j =
          (∑ a, star (factor j a) * factor i a) * Pm i j := by
        simpa [kraus] using
          (D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.diagonal_kraus_entry
            (record := factor) (rho := Pm) i j)
      _ = sigma i j := by
        fin_cases i <;> fin_cases j <;>
          norm_num [Pm, sigma, factor, Matrix.mul_apply,
            Fin.sum_univ_two, Matrix.conjTranspose_apply, Pi.star_apply,
            Complex.star_def, Matrix.vecMul, dotProduct, map_ofNat, map_div₀, map_mul]
        <;> ring

private lemma ground_nonempty {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ) :
    (groundSet e).Nonempty := by
  classical
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image Finset.univ e
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, fun b => hmin b (Finset.mem_univ b)⟩⟩

private lemma energy_entry {d m : ℕ} (E : Fin d → ℝ) (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (h : IsEnergyConserving E e U) (j k : Fin d) (a b : Fin m)
    (hE : E j + e b ≠ E k + e a) : U (j, b) (k, a) = 0 := by
  have he := congrArg (fun M : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ =>
    M (j, b) (k, a)) h
  simp only [mul_diagonal, diagonal_mul] at he
  change U (j, b) (k, a) * ((E k + e a : ℝ) : ℂ) =
    ((E j + e b : ℝ) : ℂ) * U (j, b) (k, a) at he
  have hz : U (j, b) (k, a) * (((E k + e a : ℝ) : ℂ) -
      ((E j + e b : ℝ) : ℂ)) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr
    (fun heq => hE (Complex.ofReal_injective heq.symm)))

private lemma energy_downward {d m : ℕ} (E : Fin d → ℝ) (hE : StrictMono E)
    (e : Fin m → ℝ) (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (h : IsEnergyConserving E e U) (j k : Fin d) (a b : Fin m)
    (ha : a ∈ groundSet e) (hjk : k < j) : U (j, b) (k, a) = 0 := by
  apply energy_entry E e U h j k a b
  have hmin : e a ≤ e b := (Finset.mem_filter.mp ha).2 b
  have hlt := hE hjk
  linarith

private lemma thermal_entries {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ) (i j : Fin 4) :
    thermalOutput e U Pm i j =
      ((1 / 4 : ℂ) * ((groundSet e).card : ℂ)⁻¹) *
        ∑ b : Fin m, ∑ l : Fin 4, ∑ a ∈ groundSet e, ∑ k : Fin 4,
          U (i, b) (k, a) * star (U (j, b) (l, a)) := by
  classical
  change (∑ b : Fin m, ∑ p : Fin 4 × Fin m,
    (∑ q : Fin 4 × Fin m, U (i, b) q *
      ((1 / 4 : ℂ) * (if q.2 = p.2 then
        (if q.2 ∈ groundSet e then ((groundSet e).card : ℂ)⁻¹ else 0) else 0))) *
      star (U (j, b) p)) = _
  simp only [Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul, Finset.mul_sum, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma thermal_populations {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (j : Fin 4) :
    (thermalOutput e U Pm j j).re =
      (1 / (4 * (groundSet e).card : ℝ)) *
        ∑ k : Fin 4, ∑ a ∈ groundSet e, ∑ b : Fin m, Complex.normSq (U (j, b) (k, a)) := by
  have he := thermal_entries e U j j
  have hdiag (b a : Fin m) (l : Fin 4) :
      (∑ k : Fin 4, U (j, b) (k, a) * star (U (j, b) (l, a))) =
        (Complex.normSq (U (j, b) (l, a)) : ℂ) := by
    rw [Finset.sum_eq_single l]
    · exact Complex.mul_conj _
    · intro k _ hkl
      by_cases hk : levels j + e b = levels k + e a
      · have hl : levels j + e b ≠ levels l + e a := by
          intro hl
          apply hkl
          apply levels_valid.1.injective
          linarith
        rw [energy_entry levels e U h j l a b hl, star_zero, mul_zero]
      · rw [energy_entry levels e U h j k a b hk, zero_mul]
    · simp
  have hsum :
      (∑ b : Fin m, ∑ l : Fin 4, ∑ a ∈ groundSet e, ∑ k : Fin 4,
        U (j, b) (k, a) * star (U (j, b) (l, a))) =
      ∑ b : Fin m, ∑ l : Fin 4, ∑ a ∈ groundSet e,
        (Complex.normSq (U (j, b) (l, a)) : ℂ) := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro a _
    exact hdiag b a l
  rw [hsum] at he
  have hswap :
      (∑ b : Fin m, ∑ l : Fin 4, ∑ a ∈ groundSet e,
        (Complex.normSq (U (j, b) (l, a)) : ℂ)) =
      ∑ k : Fin 4, ∑ a ∈ groundSet e, ∑ b : Fin m,
        (Complex.normSq (U (j, b) (k, a)) : ℂ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact Finset.sum_comm
  rw [hswap] at he
  have hc : ((1 / 4 : ℂ) * ((groundSet e).card : ℂ)⁻¹) =
      ((1 / (4 * (groundSet e).card : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hc] at he
  have hr := congrArg Complex.re he
  simpa only [← Complex.ofReal_sum, Complex.mul_re, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_div, zero_mul, mul_zero, sub_zero] using hr

private lemma triangular_transport (T : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (hn : ∀ j k, 0 ≤ T j k) (hr : ∀ j, ∑ k, T j k = g)
    (hc : ∀ k, ∑ j, T j k = g) (ht : ∀ j k, k < j → T j k = 0) :
    ∀ j k, j ≠ k → T j k = 0 := by
  have h10 := ht 1 0 (by decide)
  have h20 := ht 2 0 (by decide)
  have h21 := ht 2 1 (by decide)
  have h30 := ht 3 0 (by decide)
  have h31 := ht 3 1 (by decide)
  have h32 := ht 3 2 (by decide)
  have r0 := hr 0
  have c0 := hc 0
  have r1 := hr 1
  have c1 := hc 1
  have r2 := hr 2
  have c2 := hc 2
  simp only [Fin.sum_univ_four, h10, h20, h21, h30, h31, h32, add_zero, zero_add]
    at r0 c0 r1 c1 r2 c2
  have h01 : T 0 1 = 0 := by linarith [hn 0 1, hn 0 2, hn 0 3]
  have h02 : T 0 2 = 0 := by linarith [hn 0 1, hn 0 2, hn 0 3]
  have h03 : T 0 3 = 0 := by linarith [hn 0 1, hn 0 2, hn 0 3]
  have h12 : T 1 2 = 0 := by linarith [hn 1 2, hn 1 3]
  have h13 : T 1 3 = 0 := by linarith [hn 1 2, hn 1 3]
  have h23 : T 2 3 = 0 := by linarith
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp_all

private lemma population_support {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (hout : thermalOutput e U Pm = sigma) :
    ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → (U : Matrix _ _ ℂ) (j, b) (k, a) = 0 := by
  have hp := thermal_populations e U h
  have hd := energy_downward levels levels_valid.1 e U h
  have hg := ground_nonempty hm e
  have hg0 : (0 : ℝ) < (groundSet e).card := by
    exact_mod_cast Finset.card_pos.mpr hg
  let T : Matrix (Fin 4) (Fin 4) ℝ := fun j k =>
    ∑ a ∈ groundSet e, ∑ b : Fin m, Complex.normSq (U (j, b) (k, a))
  have hn : ∀ j k, 0 ≤ T j k := by
    intro j k
    exact Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))
  have hr : ∀ j, ∑ k, T j k = (groundSet e).card := by
    intro j
    have hj := hp j
    rw [hout, sigma_diagonal] at hj
    norm_num at hj
    change (1 / 4 : ℝ) = ((groundSet e).card : ℝ)⁻¹ * (1 / 4) * (∑ k, T j k) at hj
    field_simp [ne_of_gt hg0] at hj
    linarith
  have hc : ∀ k, ∑ j, T j k = (groundSet e).card := by
    intro k
    have hcol (a : Fin m) :
        (∑ p : Fin 4 × Fin m, Complex.normSq (U p (k, a))) = 1 := by
      simpa only [RHLinalg.normSqMatrix, Matrix.of_apply, Complex.sq_norm] using
        (sum_col_of_mem_doublyStochastic
          (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary U.property) (k, a))
    change (∑ j : Fin 4, ∑ a ∈ groundSet e, ∑ b : Fin m,
      Complex.normSq (U (j, b) (k, a))) = _
    rw [Finset.sum_comm]
    calc
      (∑ a ∈ groundSet e, ∑ j : Fin 4, ∑ b : Fin m,
        Complex.normSq (U (j, b) (k, a))) = ∑ a ∈ groundSet e, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (Fintype.sum_prod_type
            (fun p : Fin 4 × Fin m => Complex.normSq (U p (k, a)))).symm.trans (hcol a)
      _ = _ := by simp
  have ht : ∀ j k, k < j → T j k = 0 := by
    intro j k hjk
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b _
    rw [hd j k a b ha hjk, Complex.normSq_zero]
  have hT := triangular_transport T (groundSet e).card hn hr hc ht
  have off (j k : Fin 4) (a b : Fin m) (ha : a ∈ groundSet e) (hjk : j ≠ k) :
      (U : Matrix _ _ ℂ) (j, b) (k, a) = 0 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))).mp (hT j k hjk)
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => Complex.normSq_nonneg _)).mp (hz a ha) b (Finset.mem_univ b)
    exact Complex.normSq_eq_zero.mp hz'
  intro j k a b ha hbad
  by_cases hjk : j = k
  · subst j
    have hb : b ∉ groundSet e := hbad.resolve_left (not_not_intro rfl)
    apply energy_entry levels e U h k k a b
    intro heq
    have heba : e b = e a := by linarith
    apply hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, fun c => by
      rw [heba]
      exact (Finset.mem_filter.mp ha).2 c⟩
  · exact off j k a b ha hjk

private def block {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ) (k : Fin 4) :
    Matrix {a // a ∈ groundSet e} {a // a ∈ groundSet e} ℂ :=
  U.submatrix (fun a => (k, a.1)) (fun a => (k, a.1))

private lemma block_unitary {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (hs : ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → (U : Matrix _ _ ℂ) (j, b) (k, a) = 0)
    (k : Fin 4) : block e U k ∈ Matrix.unitaryGroup _ ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose]
  ext a c
  have hu := congrArg
    (fun M : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ => M (k, a.1) (k, c.1))
    (Matrix.mem_unitaryGroup_iff'.mp U.2)
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type] at hu
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, block.eq_1]
  calc
    (∑ b : {a // a ∈ groundSet e}, star (U (k, b.1) (k, a.1)) * U (k, b.1) (k, c.1)) =
        ∑ b ∈ groundSet e, star (U (k, b) (k, a.1)) * U (k, b) (k, c.1) :=
      Finset.sum_coe_sort (groundSet e)
        (fun b : Fin m => star (U (k, b) (k, a.1)) * U (k, b) (k, c.1))
    _ = ∑ b : Fin m, star (U (k, b) (k, a.1)) * U (k, b) (k, c.1) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [hs k k a.1 b a.2 (Or.inr hb), star_zero, zero_mul]
    _ = ∑ j : Fin 4, ∑ b : Fin m, star (U (j, b) (k, a.1)) * U (j, b) (k, c.1) := by
      symm
      apply Finset.sum_eq_single k
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro b _
        rw [hs j k a.1 b a.2 (Or.inl hj), star_zero, zero_mul]
      · simp
    _ = (1 : Matrix _ _ ℂ) a c := by
      simpa only [Matrix.one_apply, Prod.mk.injEq, true_and, Subtype.ext_iff] using hu

private lemma block_coherences {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ)
    (hs : ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → U (j, b) (k, a) = 0)
    (hout : thermalOutput e U Pm = sigma) (i j : Fin 4) :
    trace (block e U i * (block e U j)ᴴ) =
      ((groundSet e).card : ℂ) * (factor * factorᴴ) i j := by
  have he := thermal_entries e U i j
  have hsum (b : Fin m) :
      (∑ l : Fin 4, ∑ a ∈ groundSet e, ∑ k : Fin 4,
        U (i, b) (k, a) * star (U (j, b) (l, a))) =
      ∑ a ∈ groundSet e, U (i, b) (i, a) * star (U (j, b) (j, a)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · intro k _ hki
        rw [hs i k a b ha (Or.inl hki.symm), zero_mul]
      · simp
    · intro l _ hlj
      rw [hs j l a b ha (Or.inl hlj.symm), star_zero]
      simp
    · simp
  simp_rw [hsum] at he
  have htrace :
      (∑ b : Fin m, ∑ a ∈ groundSet e,
        U (i, b) (i, a) * star (U (j, b) (j, a))) =
      trace (block e U i * (block e U j)ᴴ) := by
    change _ = ∑ b : {a // a ∈ groundSet e}, ∑ a : {a // a ∈ groundSet e},
      U (i, b.1) (i, a.1) * star (U (j, b.1) (j, a.1))
    calc
      _ = ∑ b ∈ groundSet e, ∑ a ∈ groundSet e,
          U (i, b) (i, a) * star (U (j, b) (j, a)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b _ hb
        apply Finset.sum_eq_zero
        intro a ha
        rw [hs i i a b ha (Or.inr hb), zero_mul]
      _ = _ := by
        symm
        rw [Finset.sum_coe_sort (groundSet e) (fun b : Fin m =>
          ∑ a : {a // a ∈ groundSet e}, U (i, b) (i, a.1) * star (U (j, b) (j, a.1)))]
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_coe_sort (groundSet e)
          (fun a : Fin m => U (i, b) (i, a) * star (U (j, b) (j, a)))
  rw [htrace, hout] at he
  by_cases hg : (groundSet e).Nonempty
  · have hcne : ((groundSet e).card : ℂ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hg
    change (((1 / 4 : ℝ) : ℂ) * (factor * factorᴴ) i j) = _ at he
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at he
    field_simp [hcne] at he
    linear_combination -he
  · have hz : groundSet e = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    rw [← htrace]
    simp only [hz, Finset.sum_empty, Finset.sum_const_zero, Finset.card_empty,
      Nat.cast_zero, zero_mul]

private lemma gram_null {n : Type*} [Fintype n]
    (A : Fin 4 → Matrix n n ℂ)
    (h : ∀ i j, trace (A i * (A j)ᴴ) = (Fintype.card n : ℂ) * (factor * factorᴴ) i j) :
    A 2 = (3 / 5 : ℂ) • A 0 + (4 / 5 : ℂ) • A 1 ∧
      A 3 = (3 / 5 : ℂ) • A 0 + (4 * Complex.I / 5 : ℂ) • A 1 := by
  constructor
  · apply sub_eq_zero.mp
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, sub_mul, mul_sub, add_mul, mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, h]
    norm_num [factor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, Matrix.vecMul, dotProduct, map_ofNat, map_div₀, map_mul]
    ring
  · apply sub_eq_zero.mp
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, sub_mul, mul_sub, add_mul, mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, h]
    norm_num [factor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, Matrix.vecMul, dotProduct, map_ofNat, map_div₀, map_mul]
    ring

private lemma unitary_obstruction {n : Type*} [Fintype n] [DecidableEq n]
    (hn : Nonempty n) (A : Fin 4 → Matrix n n ℂ)
    (hU : ∀ k, A k ∈ Matrix.unitaryGroup n ℂ)
    (h2 : A 2 = (3 / 5 : ℂ) • A 0 + (4 / 5 : ℂ) • A 1)
    (h3 : A 3 = (3 / 5 : ℂ) • A 0 + (4 * Complex.I / 5 : ℂ) • A 1) : False := by
  have h0 : A 0 * (A 0)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp (hU 0)
  have h1 : A 1 * (A 1)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp (hU 1)
  have q2 : A 2 * (A 2)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp (hU 2)
  have q3 : A 3 * (A 3)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp (hU 3)
  rw [h2] at q2
  rw [h3] at q3
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, h1] at q2 q3
  have hx : A 0 * (A 1)ᴴ = 0 := by
    ext i j
    have r := congrArg (fun M : Matrix n n ℂ => M i j) q2
    have s := congrArg (fun M : Matrix n n ℂ => M i j) q3
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at r s
    norm_num [Complex.star_def, map_ofNat, map_div₀, map_mul] at r s
    change (A 0 * (A 1)ᴴ) i j = 0
    linear_combination (norm := ring_nf)
      (25 / 24 : ℂ) * r + (25 * Complex.I / 24 : ℂ) * s
    simp only [Complex.I_sq, Complex.I_pow_three]
    ring
  let : Nonempty n := hn
  exact (Unitary.isUnit_coe (U :=
    (⟨A 0, hU 0⟩ : Matrix.unitaryGroup n ℂ) *
      star (⟨A 1, hU 1⟩ : Matrix.unitaryGroup n ℂ))).ne_zero hx

private lemma thermal_impossible {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (hout : thermalOutput e U Pm = sigma) : False := by
  have hs := population_support hm e U h hout
  have hU := block_unitary e U hs
  have hG := block_coherences e U hs hout
  obtain ⟨h2, h3⟩ := gram_null (block e U) (by simpa using hG)
  obtain ⟨a, ha⟩ := ground_nonempty hm e
  exact unitary_obstruction ⟨⟨a, ha⟩⟩ (block e U) hU h2 h3

theorem result : ¬ claim := by
  intro h
  obtain ⟨m, e, U, hm, hE, hout⟩ :=
    h 4 levels levels_valid.1 levels_valid.2 Pm sigma
      instance_density.1 instance_density.2 instance_cooling
  exact thermal_impossible hm e U hE hout

end D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation
