/- GID: D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.exists_fixedBathHamiltonian; premises=D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.uniform_selected,D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.five_selected
   digest: Fixed orthogonal coordinate baths select five modes on open real and complex Hamiltonian sets in every dimension at least five. -/

/- Fixed-coordinate-bath Hamiltonian construction.
Scientific construction: Haobo Ma and Wenlin Zhang, CC BY 4.0.
Model: Schnell–Ketzmerick–Eckardt (2018); signed Pfaffian method: Knebel et al. (2015).
The original asymmetry, selection predicate and Pfaffian proofs are reused.
The construction uses the particular cubic exponent and five-mode certificates;
it does not assert the corresponding construction for arbitrary exponents or support sizes.
-/

import D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

/-! Uniform fixed orthogonal baths for the cubic asymmetry.
The physical predicate is imported from the pinned refutation.
The new construction uses the first five energies and allows arbitrary extra energies above five.
-/

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators
open Matrix
open D5.S3.Geometry

open D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation (spow)

private noncomputable def oldEnergy : Fin 5 → ℝ := ![1, 2, 3, 4, 5]
private noncomputable def oldF : Fin 5 → ℝ := ![25/464, 25/464, 25/464, 25/116, 225/464]
private noncomputable def oldG : Fin 5 → ℝ := ![25/377, 25921/30537, 13/2349, 52/2349, 13/261]

private noncomputable def oldOccupation : Fin 5 → ℝ :=
  fun i => (![2066989123199, 11682807236100, 9292388902650, 1489507236225,
    18634875975] : Fin 5 → ℝ) i / 24550327374149

private noncomputable def weightsF (k : ℕ) : Fin (5 + k) → ℝ :=
  Fin.append oldF (fun _ => 4 / (29 * (k : ℝ)))

private noncomputable def weightsG (k : ℕ) : Fin (5 + k) → ℝ :=
  Fin.append oldG (fun _ => 25 / (3393 * (k : ℝ)))

private noncomputable def occupation (k : ℕ) : Fin (5 + k) → ℝ :=
  Fin.append oldOccupation (fun _ => 0)

private def support (k : ℕ) : Finset (Fin (5 + k)) :=
  Finset.univ.map (Fin.castAddEmb k)

private theorem left_mem {k : ℕ} (i : Fin 5) : Fin.castAdd k i ∈ support k :=
  Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

private theorem right_not_mem {k : ℕ} (i : Fin k) : Fin.natAdd 5 i ∉ support k := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have hj' := congrArg Fin.val hj
  simp at hj'
  omega

private theorem oldF_pos (i : Fin 5) : 0 < oldF i := by fin_cases i <;> norm_num [oldF]
private theorem oldG_pos (i : Fin 5) : 0 < oldG i := by fin_cases i <;> norm_num [oldG]
private theorem oldOccupation_pos (i : Fin 5) : 0 < oldOccupation i := by
  fin_cases i <;> norm_num [oldOccupation]

private theorem old_ratio (i : Fin 5) : oldG i < 16 * oldF i := by
  fin_cases i <;> norm_num [oldF, oldG]

private theorem old_energy_le (i : Fin 5) : oldEnergy i ≤ 5 := by
  fin_cases i <;> norm_num [oldEnergy]

private theorem old_kernel (i : Fin 5) :
    (∑ j : Fin 5, (oldEnergy j - oldEnergy i)^3 *
      (oldF i * oldF j - oldG i * oldG j) * oldOccupation j) = 0 := by
  fin_cases i <;>
    norm_num [oldEnergy, oldF, oldG, oldOccupation, Fin.sum_univ_succ]

private theorem sumF {k : ℕ} (hk : 0 < k) : ∑ i, weightsF k i = 1 := by
  rw [Fin.sum_univ_add]
  simp only [weightsF, Fin.append_left, Fin.append_right, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  norm_num [oldF, Fin.sum_univ_succ]
  field_simp
  ring

private theorem sumG {k : ℕ} (hk : 0 < k) : ∑ i, weightsG k i = 1 := by
  rw [Fin.sum_univ_add]
  simp only [weightsG, Fin.append_left, Fin.append_right, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  norm_num [oldG, Fin.sum_univ_succ]
  field_simp
  ring

private theorem sumOccupation (k : ℕ) : ∑ i, occupation k i = 1 := by
  rw [Fin.sum_univ_add]
  simp [occupation, oldOccupation, Fin.sum_univ_succ]
  norm_num

private theorem drift {k : ℕ} (hk : 0 < k) (E : Fin k → ℝ) (i : Fin (5 + k)) :
    (asym 3 (Fin.append oldEnergy E) (weightsF k) (weightsG k) *ᵥ occupation k) i =
      ∑ j : Fin 5, (oldEnergy j - Fin.append oldEnergy E i)^3 *
        (weightsF k i * oldF j - weightsG k i * oldG j) * oldOccupation j := by
  have hF (x) : FiniteCoordinateTruncation.normalize (weightsF k) x = weightsF k x := by
    simp [FiniteCoordinateTruncation.normalize, sumF hk]
  have hG (x) : FiniteCoordinateTruncation.normalize (weightsG k) x = weightsG k x := by
    simp [FiniteCoordinateTruncation.normalize, sumG hk]
  simp only [Matrix.mulVec, dotProduct, asym, spectral_three, hF, hG]
  simp [Fin.sum_univ_add, occupation, weightsF, weightsG]

/-- For every positive number of extra levels and all their energies above five, the physical
cubic asymmetry with the given normalized baths selects exactly the first five levels. -/
theorem uniform_selected {k : ℕ} (hk : 0 < k) (E : Fin k → ℝ) (hE : ∀ i, 5 < E i) :
    (∀ i, 0 < weightsF k i) ∧ (∀ i, 0 < weightsG k i) ∧
    (∑ i, weightsF k i) = 1 ∧ (∑ i, weightsG k i) = 1 ∧
    (∑ i, occupation k i) = 1 ∧ (support k).card = 5 ∧
    IsSelected (asym 3 (Fin.append oldEnergy E) (weightsF k) (weightsG k))
      (support k) (occupation k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_, sumF hk, sumG hk, sumOccupation k, by simp [support], ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [weightsF] using oldF_pos j
    · simp only [weightsF, Fin.append_right]; positivity
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [weightsG] using oldG_pos j
    · simp only [weightsG, Fin.append_right]; positivity
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine ⟨fun _ => ⟨by simpa [occupation] using oldOccupation_pos j, ?_⟩,
        fun h => (h (left_mem j)).elim⟩
      rw [drift hk]
      simpa [weightsF, weightsG] using old_kernel j
    · refine ⟨fun h => (right_not_mem j h).elim, fun _ => ⟨by simp [occupation], ?_⟩⟩
      rw [drift hk]
      refine Finset.sum_neg (fun l _ => ?_) Finset.univ_nonempty
      simp only [Fin.append_right, weightsF, weightsG]
      have hnew : 16 * (25 / (3393 * (k : ℝ))) < 4 / (29 * (k : ℝ)) := by
        field_simp
        linarith
      have hp : 0 < 25 / (3393 * (k : ℝ)) := by positivity
      have hdiff : 0 < 4 / (29 * (k : ℝ)) * oldF l -
          25 / (3393 * (k : ℝ)) * oldG l := by
        apply sub_pos.mpr
        calc
          _ < (25 / (3393 * (k : ℝ))) * (16 * oldF l) :=
            mul_lt_mul_of_pos_left (old_ratio l) hp
          _ = (16 * (25 / (3393 * (k : ℝ)))) * oldF l := by ring
          _ < _ := mul_lt_mul_of_pos_right hnew (oldF_pos l)
      have hgap : oldEnergy l - E j < 0 :=
        sub_neg.mpr (lt_of_le_of_lt (old_energy_le l) (hE j))
      have hcubic : (oldEnergy l - E j)^3 < 0 := by
        rw [pow_succ]
        exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hgap.ne) hgap
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcubic hdiff) (oldOccupation_pos l)

private noncomputable def a : Fin 5 → ℝ := ![1/4, -1/4, -1/4, -2/4, -3/4]
private noncomputable def b : Fin 5 → ℝ := ![-3/12, 11/12, -1/12, -2/12, -3/12]

private noncomputable def occupationFive : Fin 5 → ℝ :=
  fun i => (![40, 288, 189, 18, 1] : Fin 5 → ℝ) i / 536

/-- The five-level witness uses the original two orthogonal rows and a separate certificate. -/
theorem five_selected :
    (∑ i, a i ^ 2) = 1 ∧ (∑ i, b i ^ 2) = 1 ∧ (∑ i, a i * b i) = 0 ∧
    (∑ i, occupationFive i) = 1 ∧
    IsSelected (asym 3 oldEnergy (fun i => a i ^ 2) (fun i => b i ^ 2))
      Finset.univ occupationFive := by
  have ha : (∑ i, a i ^ 2) = 1 := by norm_num [a, Fin.sum_univ_succ]
  have hb : (∑ i, b i ^ 2) = 1 := by norm_num [b, Fin.sum_univ_succ]
  refine ⟨ha, hb, by norm_num [a, b, Fin.sum_univ_succ],
    by norm_num [occupationFive, Fin.sum_univ_succ], ?_⟩
  intro i
  refine ⟨fun _ => ⟨?_, ?_⟩, fun h => (h (Finset.mem_univ i)).elim⟩
  · fin_cases i <;> norm_num [occupationFive]
  · simp only [Matrix.mulVec, dotProduct, asym, spectral_three,
      FiniteCoordinateTruncation.normalize, ha, hb, div_one]
    fin_cases i <;> norm_num [oldEnergy, a, b, occupationFive, Fin.sum_univ_succ]

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators InnerProductSpace
open Matrix
open D5.S3.Geometry

private noncomputable def t (k : ℕ) : ℝ := 1 / (100 * (k : ℝ))

/-- The first bath row after normalizing the extended vector. -/
private noncomputable def rowF (k : ℕ) : Fin (5 + k) → ℝ :=
  fun i => Fin.append a (fun _ => 4 * Real.sqrt (t k)) i / Real.sqrt (29/25)

/-- The second bath row after subtracting its projection on the first. -/
private noncomputable def rowG (k : ℕ) : Fin (5 + k) → ℝ :=
  fun i => Fin.append (fun j => b j - a j / 29)
    (fun _ => (25/29) * Real.sqrt (t k)) i / Real.sqrt (117/116)

private theorem rowF_sq (k : ℕ) (i : Fin (5 + k)) : rowF k i ^ 2 = weightsF k i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> norm_num [rowF, weightsF, a, oldF, div_pow, Real.sq_sqrt]
  · simp only [rowF, weightsF, Fin.append_right, div_pow, mul_pow]
    rw [Real.sq_sqrt (by unfold t; positivity : 0 ≤ t k), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 29/25)]
    unfold t
    ring

private theorem rowG_sq (k : ℕ) (i : Fin (5 + k)) : rowG k i ^ 2 = weightsG k i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> norm_num [rowG, weightsG, a, b, oldG, div_pow, Real.sq_sqrt]
  · simp only [rowG, weightsG, Fin.append_right, div_pow, mul_pow]
    rw [Real.sq_sqrt (by unfold t; positivity : 0 ≤ t k), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 117/116)]
    unfold t
    ring

private theorem row_cross {k : ℕ} (hk : 0 < k) :
    (∑ i, rowF k i * rowG k i) = 0 := by
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsq := Real.sq_sqrt (by unfold t; positivity : 0 ≤ t k)
  simp only [rowF, rowG, div_mul_div_comm, ← Finset.sum_div, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  suffices h : (∑ j : Fin 5, a j * (b j - a j / 29)) +
      (k : ℝ) * ((4 * Real.sqrt (t k)) * ((25/29) * Real.sqrt (t k))) = 0 by rw [h, zero_div]
  calc
    _ = (∑ j : Fin 5, a j * (b j - a j / 29)) +
        (k : ℝ) * (4 * (25/29) * (Real.sqrt (t k))^2) := by ring
    _ = 0 := by
      rw [hsq]
      norm_num [a, b, Fin.sum_univ_succ, t]
      field_simp
      ring

/-- The amplitudes realize the normalized bath weights as two orthonormal real rows. -/
private theorem orthonormal_rows {k : ℕ} (hk : 0 < k) :
    Orthonormal ℝ
      (![WithLp.toLp 2 (rowF k), WithLp.toLp 2 (rowG k)] :
        Fin 2 → EuclideanSpace ℝ (Fin (5 + k))) ∧
    (∀ i, rowF k i ^ 2 = weightsF k i) ∧ (∀ i, rowG k i ^ 2 = weightsG k i) := by
  obtain ⟨_, _, hF, hG, _, _, _⟩ :=
    uniform_selected hk (fun _ => 6) (fun _ => by norm_num)
  refine ⟨?_, rowF_sq k, rowG_sq k⟩
  have hFF : (∑ i, rowF k i ^ 2) = 1 := by
    simpa only [rowF_sq] using hF
  have hGG : (∑ i, rowG k i ^ 2) = 1 := by
    simpa only [rowG_sq] using hG
  have hGF : (∑ i, rowG k i * rowF k i) = 0 := by
    simpa only [mul_comm (rowG k _) (rowF k _)] using row_cross hk
  rw [orthonormal_iff_ite]
  intro r s
  fin_cases r <;> fin_cases s <;>
    rw [PiLp.inner_apply] <;>
    norm_num [real_inner_comm, hFF, hGG, row_cross hk, hGF]

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators InnerProductSpace

private theorem basis_of_real_rows {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hx : (∑ i, x i ^ 2) = 1) (hy : (∑ i, y i ^ 2) = 1)
    (hxy : (∑ i, x i * y i) = 0) (𝕜 : Type*) [RCLike 𝕜] :
    ∃ q : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)),
      (∀ j, q ⟨0, by omega⟩ j = RCLike.ofReal (x j)) ∧
      (∀ j, q ⟨1, by omega⟩ j = RCLike.ofReal (y j)) := by
  let emb (u : Fin n → ℝ) : EuclideanSpace 𝕜 (Fin n) :=
    WithLp.toLp 2 (fun j => RCLike.ofReal (u j))
  have hi (u v : Fin n → ℝ) :
      ⟪emb u, emb v⟫_𝕜 = RCLike.ofReal (∑ j, u j * v j) := by
    change (∑ j, ⟪(RCLike.ofReal (u j) : 𝕜), RCLike.ofReal (v j)⟫_𝕜) = _
    simp only [RCLike.inner_apply', RCLike.conj_ofReal, RCLike.ofReal_mul, RCLike.ofReal_sum]
  have hxx : ⟪emb x, emb x⟫_𝕜 = 1 := by rw [hi]; simp only [← pow_two, hx, RCLike.ofReal_one]
  have hyy : ⟪emb y, emb y⟫_𝕜 = 1 := by rw [hi]; simp only [← pow_two, hy, RCLike.ofReal_one]
  have hXY : ⟪emb x, emb y⟫_𝕜 = 0 := by simp [hi, hxy]
  have hYX : ⟪emb y, emb x⟫_𝕜 = 0 := by simp [hi, mul_comm (y _) (x _), hxy]
  let v (i : Fin n) := if i.val = 0 then emb x else emb y
  let s : Set (Fin n) := {i | i.val < 2}
  have hv : Orthonormal 𝕜 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪v i.val, v j.val⟫_𝕜 = if i = j then 1 else 0
    have hi2 : i.val.val < 2 := i.property
    have hj2 : j.val.val < 2 := j.property
    have heq : i = j ↔ i.val.val = j.val.val :=
      ⟨fun h => congrArg (fun z : s => z.val.val) h, fun h => Subtype.ext (Fin.ext h)⟩
    by_cases hi0 : i.val.val = 0 <;> by_cases hj0 : j.val.val = 0
    · rw [ite_eq_left (heq.mpr (by omega))]
      simpa only [v, ite_eq_left hi0, ite_eq_left hj0] using hxx
    · rw [ite_eq_right (fun h => hj0 ((heq.mp h).symm.trans hi0))]
      simpa only [v, ite_eq_left hi0, ite_eq_right hj0] using hXY
    · rw [ite_eq_right (fun h => hi0 ((heq.mp h).trans hj0))]
      simpa only [v, ite_eq_right hi0, ite_eq_left hj0] using hYX
    · rw [ite_eq_left (heq.mpr (by omega))]
      simpa only [v, ite_eq_right hi0, ite_eq_right hj0] using hyy
  obtain ⟨q, hq⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := 𝕜) (ι := Fin n))
  have h0 : (⟨0, by omega⟩ : Fin n) ∈ s := by change 0 < 2; decide
  have h1 : (⟨1, by omega⟩ : Fin n) ∈ s := by change 1 < 2; decide
  refine ⟨q, fun j => ?_, fun j => ?_⟩
  · rw [hq _ h0]
    rfl
  · rw [hq _ h1]
    rfl

/-- The two constructed real rows can be completed in either real or complex Euclidean space.
The basis vectors labelled zero and one retain the exact fixed-bath amplitudes. -/
private theorem uniform_rows_basis {k : ℕ} (hk : 0 < k) (𝕜 : Type*) [RCLike 𝕜] :
    ∃ q : OrthonormalBasis (Fin (5 + k)) 𝕜 (EuclideanSpace 𝕜 (Fin (5 + k))),
      (∀ j, q ⟨0, by omega⟩ j = RCLike.ofReal (rowF k j)) ∧
      (∀ j, q ⟨1, by omega⟩ j = RCLike.ofReal (rowG k j)) := by
  obtain ⟨hrows, _, _⟩ := orthonormal_rows hk
  have h := orthonormal_iff_ite.mp hrows
  have hF := h 0 0
  have hG := h 1 1
  have hcross := h 1 0
  rw [PiLp.inner_apply] at hF hG hcross
  apply basis_of_real_rows (by omega) (rowF k) (rowG k) _ _ _ 𝕜
  · simpa [Real.inner_apply, pow_two] using hF
  · simpa [Real.inner_apply, pow_two] using hG
  · simpa [Real.inner_apply] using hcross

/-- Completion of the original two bath rows in the five-dimensional construction. -/
private theorem five_rows_basis (𝕜 : Type*) [RCLike 𝕜] :
    ∃ q : OrthonormalBasis (Fin 5) 𝕜 (EuclideanSpace 𝕜 (Fin 5)),
      (∀ j, q 0 j = RCLike.ofReal (a j)) ∧
      (∀ j, q 1 j = RCLike.ofReal (b j)) := by
  obtain ⟨ha, hb, hab, _, _⟩ := five_selected
  exact basis_of_real_rows (by decide) a b ha hb hab 𝕜

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open Matrix
open scoped BigOperators

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The fixed rank-one coordinate projection, with no dependence on the Hamiltonian. -/
def coordinateProjector (r : Fin n) : Matrix (Fin n) (Fin n) 𝕜 :=
  diagonal (Pi.single r 1)

private theorem coordinateProjector_hermitian (r : Fin n) :
    (coordinateProjector (𝕜 := 𝕜) r).IsHermitian := by
  rw [coordinateProjector, isHermitian_diagonal_iff]
  intro i
  by_cases h : i = r <;> simp [h, IsSelfAdjoint]

private theorem coordinateProjector_mulVec (r : Fin n) (v : Fin n → 𝕜) :
    coordinateProjector r *ᵥ v = Pi.single r (v r) := by
  ext i
  rw [coordinateProjector, mulVec_diagonal]
  by_cases h : i = r <;> simp [h]

private theorem coordinateProjector_mul (r s : Fin n) :
    coordinateProjector (𝕜 := 𝕜) r * coordinateProjector s =
      if r = s then coordinateProjector r else 0 := by
  rw [coordinateProjector, coordinateProjector, diagonal_mul_diagonal]
  ext i j
  by_cases h : r = s
  · subst s
    by_cases hi : i = r <;> simp [diagonal_apply, Pi.single_apply, hi]
  · by_cases hi : i = r
    · subst i
      simp [h, diagonal_apply, Pi.single_apply]
    · simp [h, hi, diagonal_apply, Pi.single_apply]

/-- The weight is the expectation of the fixed coordinate projection in the eigenstate. -/
def coordinateWeight (r : Fin n) (v : Fin n → 𝕜) : ℝ :=
  RCLike.re (star v ⬝ᵥ (coordinateProjector r *ᵥ v))

theorem coordinateWeight_eq (r : Fin n) (v : Fin n → 𝕜) :
    coordinateWeight r v = ‖v r‖ ^ 2 := by
  rw [coordinateWeight, coordinateProjector_mulVec, dotProduct_single]
  change RCLike.re (star (v r) * v r) = _
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The columns of the adjoint of the matrix of the given row basis. -/
private def unitaryOfRows (q : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    Matrix.unitaryGroup (Fin n) 𝕜 :=
  star ⟨(EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix q.toBasis,
    (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary q⟩

private theorem unitaryOfRows_apply (q : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    (r i : Fin n) : unitaryOfRows q r i = star (q r i) := rfl

/-- An actual Hamiltonian given by a unitary diagonalization. -/
def spectralMatrix (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i => RCLike.ofReal (e i)) *
    (U : Matrix (Fin n) (Fin n) 𝕜)ᴴ

private theorem spectralMatrix_hermitian (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) :
    (spectralMatrix U e).IsHermitian := by
  apply isHermitian_mul_mul_conjTranspose
  rw [isHermitian_diagonal_iff]
  simp [IsSelfAdjoint, RCLike.star_def]

private theorem spectralMatrix_eigenvector (U : Matrix.unitaryGroup (Fin n) 𝕜)
    (e : Fin n → ℝ) (i : Fin n) :
    spectralMatrix U e *ᵥ (fun r => U r i) =
      (RCLike.ofReal (e i) : 𝕜) • (fun r => U r i) := by
  let V := (U : Matrix (Fin n) (Fin n) 𝕜)
  have hv : V *ᵥ Pi.single i 1 = (fun r => U r i) := by
    rw [mulVec_single_one]
    rfl
  have hu : Vᴴ * V = 1 := Unitary.coe_star_mul_self U
  rw [← hv]
  change (V * diagonal (fun i => RCLike.ofReal (e i)) * Vᴴ) *ᵥ (V *ᵥ Pi.single i 1) = _
  rw [mulVec_mulVec, mul_assoc (_ * _) Vᴴ V, hu, mul_one, ← mulVec_mulVec,
    diagonal_mulVec_single, mul_one]
  have hsingle : Pi.single i (RCLike.ofReal (e i) : 𝕜) =
      (RCLike.ofReal (e i) : 𝕜) • Pi.single i (1 : 𝕜) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [hsingle, mulVec_smul]

theorem spectralMatrix_charpoly (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) :
    (spectralMatrix U e).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (RCLike.ofReal (e i) : 𝕜)) := by
  unfold spectralMatrix
  rw [charpoly_mul_comm, ← mul_assoc]
  change ((star (U : Matrix (Fin n) (Fin n) 𝕜) * U) * _).charpoly = _
  rw [Unitary.coe_star_mul_self U, one_mul, charpoly_diagonal]

private theorem coordinateWeight_unitaryOfRows
    (q : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n))) (r : Fin n)
    (x : Fin n → ℝ) (h : ∀ j, q r j = RCLike.ofReal (x j)) (i : Fin n) :
    coordinateWeight r (fun j => unitaryOfRows q j i) = x i ^ 2 := by
  rw [coordinateWeight_eq, unitaryOfRows_apply, h i, RCLike.star_def, RCLike.norm_conj,
    RCLike.norm_ofReal, sq_abs]

end

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open Matrix
open scoped BigOperators

theorem asym_cubic_transpose {n : ℕ} (e F G : Fin n → ℝ) :
    (asym 3 e F G)ᵀ = -asym 3 e F G := by
  ext i j
  exact asym_skew e F G i j

/-- Strict drift and skew symmetry force every selected solution to have the same support. -/
theorem selected_support_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = -A) {s t : Finset (Fin n)} {w v : Fin n → ℝ}
    (hw : IsSelected A s w) (hv : IsSelected A t v) : s = t := by
  have hprod {s t : Finset (Fin n)} {w v : Fin n → ℝ}
      (hw : IsSelected A s w) (hv : IsSelected A t v) (i : Fin n) :
      w i * (A *ᵥ v) i ≤ 0 := by
    by_cases hi : i ∈ s
    · have hvle : (A *ᵥ v) i ≤ 0 := by
        by_cases hj : i ∈ t
        · exact le_of_eq ((hv i).1 hj).2
        · exact ((hv i).2 hj).2.le
      exact mul_nonpos_of_nonneg_of_nonpos ((hw i).1 hi).1.le hvle
    · rw [((hw i).2 hi).1, zero_mul]
  have hsub {s t : Finset (Fin n)} {w v : Fin n → ℝ}
      (hw : IsSelected A s w) (hv : IsSelected A t v) : s ⊆ t := by
    intro i hi
    by_contra hit
    have hneg : w i * (A *ᵥ v) i < 0 :=
      mul_neg_of_pos_of_neg ((hw i).1 hi).1 ((hv i).2 hit).2
    have hlt : w ⬝ᵥ (A *ᵥ v) < 0 := by
      unfold dotProduct
      calc
        _ < ∑ _j : Fin n, (0 : ℝ) :=
          Finset.sum_lt_sum (fun j _ => hprod hw hv j) ⟨i, Finset.mem_univ i, hneg⟩
        _ = 0 := by simp
    have hle : v ⬝ᵥ (A *ᵥ w) ≤ 0 := Finset.sum_nonpos (fun j _ => hprod hv hw j)
    have he := dotProduct_transpose_mulVec A w v
    rw [hA, neg_mulVec, dotProduct_neg] at he
    linarith
  exact Finset.Subset.antisymm (hsub hw hv) (hsub hv hw)

private theorem det_skew_four (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i j, A j i = -A i j) :
    A.det = (A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2) ^ 2 := by
  have hd (i : Fin 4) : A i i = 0 := CharZero.eq_neg_self_iff.mp (h i i)
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_three, submatrix_apply]
  norm_num [Fin.succAbove, Fin.castSucc, Fin.succ]
  simp only [hd, h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]
  ring

private theorem fivePfaffian_minor (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, A j i = -A i j) :
    (A.submatrix Fin.castSucc Fin.castSucc).det = pfaffianVector A (Fin.last 4) ^ 2 := by
  rw [det_skew_four (A.submatrix Fin.castSucc Fin.castSucc) (fun i j => h i.castSucc j.castSucc)]
  rfl

theorem rank_four_of_fivePfaffian (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, A j i = -A i j) (hp : pfaffianVector A (Fin.last 4) ≠ 0) :
    A.rank = 4 := by
  have hminor : (A.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
    rw [fivePfaffian_minor A h]
    exact pow_ne_zero _ hp
  have hlow : 4 ≤ A.rank := by
    have hh := rank_submatrix_le A Fin.castSucc Fin.castSucc
    rwa [rank_of_det_ne_zero hminor, Fintype.card_fin] at hh
  have hhigh : A.rank ≤ 5 := by simpa using A.rank_le_card_width
  have hne : A.rank ≠ 5 := by
    intro hr
    have hsurj : Function.Surjective A.mulVec :=
      mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hr)
    have hinj : Function.Injective A.mulVecLin :=
      LinearMap.injective_iff_surjective.mpr hsurj
    have he : pfaffianVector A = 0 := hinj (by simpa using pfaffian_kernel A h)
    exact hp (congrFun he (Fin.last 4))
  omega

private theorem restrict_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin 5 ↪ Fin n) (x : Fin n → ℝ)
    (hx : ∀ i ∉ Finset.univ.map f, x i = 0) (i : Fin 5) :
    (A.submatrix f f *ᵥ (x ∘ f)) i = (A *ᵥ x) (f i) := by
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
  calc
    _ = ∑ j ∈ Finset.univ.map f, A (f i) j * x j := by simp only [Finset.sum_map]
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by simp [hx j hj])

private theorem five_kernel_proportional (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, A j i = -A i j) {x y : Fin 5 → ℝ}
    (hx : A *ᵥ x = 0) (hy : A *ᵥ y = 0) (hlast : y (Fin.last 4) ≠ 0)
    (hp : pfaffianVector A (Fin.last 4) ≠ 0) :
    x = (x (Fin.last 4) / y (Fin.last 4)) • y := by
  let c := x (Fin.last 4) / y (Fin.last 4)
  let z := x - c • y
  have hz : A *ᵥ z = 0 := by simp [z, mulVec_sub, mulVec_smul, hx, hy]
  have hzlast : z (Fin.last 4) = 0 := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c, div_mul_cancel₀ _ hlast, sub_self]
  have hminor : (A.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
    rw [fivePfaffian_minor A h]
    exact pow_ne_zero _ hp
  have hsmall : (A.submatrix Fin.castSucc Fin.castSucc) *ᵥ (z ∘ Fin.castSucc) = 0 := by
    funext i
    have he := congrFun hz i.castSucc
    change (∑ j, A i.castSucc j * z j) = 0 at he
    rw [Fin.sum_univ_castSucc, hzlast, mul_zero, add_zero] at he
    exact he
  have hsmall' : z ∘ Fin.castSucc = 0 := by
    apply mulVec_injective_of_det_ne_zero hminor
    simpa using hsmall
  have hzero : z = 0 := by
    funext i
    refine Fin.lastCases hzlast (fun j => congrFun hsmall' j) i
  exact sub_eq_zero.mp hzero

/-- One nonzero principal four-by-four minor and strict selection give uniqueness, including
against competitors with arbitrary supports. -/
theorem selected_normalized_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = -A) (f : Fin 5 ↪ Fin n) {w : Fin n → ℝ}
    (hw : IsSelected A (Finset.univ.map f) w) (hwsum : ∑ i, w i = 1)
    (hp : pfaffianVector (A.submatrix f f) (Fin.last 4) ≠ 0)
    {t : Finset (Fin n)} {v : Fin n → ℝ} (hv : IsSelected A t v) (hvsum : ∑ i, v i = 1) :
    t = Finset.univ.map f ∧ v = w := by
  have ht := selected_support_eq hA hv hw
  subst t
  refine ⟨rfl, ?_⟩
  have hm (i : Fin 5) : f i ∈ Finset.univ.map f := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hoffw (i) (hi : i ∉ Finset.univ.map f) := ((hw i).2 hi).1
  have hoffv (i) (hi : i ∉ Finset.univ.map f) := ((hv i).2 hi).1
  have hker (x : Fin n → ℝ) (hx : IsSelected A (Finset.univ.map f) x) :
      A.submatrix f f *ᵥ (x ∘ f) = 0 := by
    funext i
    rw [restrict_mulVec A f x (fun j hj => ((hx j).2 hj).1) i]
    exact ((hx (f i)).1 (hm i)).2
  have hsk (i j : Fin 5) : (A.submatrix f f) j i = -(A.submatrix f f) i j :=
    congrFun (congrFun hA (f i)) (f j)
  let c := v (f (Fin.last 4)) / w (f (Fin.last 4))
  have he := five_kernel_proportional _ hsk (hker v hv) (hker w hw)
    (ne_of_gt ((hw _).1 (hm _)).1) hp
  have hvw : v = c • w := by
    funext i
    by_cases hi : i ∈ Finset.univ.map f
    · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact congrFun he j
    · simp [hoffv i hi, hoffw i hi]
  have hc : c = 1 := by
    rw [hvw] at hvsum
    change (∑ i, c * w i) = 1 at hvsum
    rwa [← Finset.mul_sum, hwsum, mul_one] at hvsum
  simpa [hc] using hvw

/-- All five signed Pfaffians of the original five-level cubic block are positive. -/
private theorem five_cubic_pfaffian_pos (i : Fin 5) :
    0 < pfaffianVector (asym 3 oldEnergy (fun j => a j ^ 2) (fun j => b j ^ 2)) i := by
  have ha : (∑ j, a j ^ 2) = 1 := five_selected.1
  have hb : (∑ j, b j ^ 2) = 1 := five_selected.2.1
  simp only [pfaffianVector, asym, spectral_three,
    D5.S3.Geometry.FiniteCoordinateTruncation.normalize, ha, hb, div_one]
  fin_cases i <;> norm_num [a, b, oldEnergy]

/-- All five signed Pfaffians of the common cubic block in dimensions above five are positive. -/
private theorem uniform_cubic_pfaffian_pos {k : ℕ} (hk : 0 < k) (E : Fin k → ℝ)
    (hE : ∀ i, 5 < E i) (i : Fin 5) :
    0 < pfaffianVector
      ((asym 3 (Fin.append oldEnergy E) (weightsF k) (weightsG k)).submatrix
        (Fin.castAdd k) (Fin.castAdd k)) i := by
  obtain ⟨_, _, hF, hG, _, _, _⟩ := uniform_selected hk E hE
  have he :
      ((asym 3 (Fin.append oldEnergy E) (weightsF k) (weightsG k)).submatrix
        (Fin.castAdd k) (Fin.castAdd k)) =
        (fun x y => (oldEnergy y - oldEnergy x)^3 * (oldF x * oldF y - oldG x * oldG y)) := by
    ext x y
    simp only [submatrix_apply, asym, spectral_three,
      D5.S3.Geometry.FiniteCoordinateTruncation.normalize, hF, hG, div_one, Fin.append_left]
    simp only [weightsF, weightsG, Fin.append_left]
  rw [he]
  fin_cases i <;> norm_num [pfaffianVector, oldEnergy, oldF, oldG]

/-- Extend a five-mode vector by zero along a specified embedding. -/
noncomputable def liftFive {n : ℕ} (f : Fin 5 ↪ Fin n) (x : Fin 5 → ℝ) (i : Fin n) : ℝ :=
  if h : ∃ j, f j = i then x (Classical.choose h) else 0

@[simp] private theorem liftFive_apply {n : ℕ} (f : Fin 5 ↪ Fin n) (x : Fin 5 → ℝ) (i : Fin 5) :
    liftFive f x (f i) = x i := by
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  rw [liftFive, dite_eq_left h, f.injective (Classical.choose_spec h)]

private theorem liftFive_off {n : ℕ} (f : Fin 5 ↪ Fin n) (x : Fin 5 → ℝ) {i : Fin n}
    (hi : i ∉ Finset.univ.map f) : liftFive f x i = 0 := by
  rw [liftFive, dite_eq_right]
  rintro ⟨j, hj⟩
  exact hi (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hj⟩)

/-- Strict inequalities on the five signed Pfaffians and the drifts of their zero extension. -/
def StrictFiveCertificate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f : Fin 5 ↪ Fin n) : Prop :=
  let p := pfaffianVector (A.submatrix f f)
  (∀ i, 0 < p i) ∧ (∀ i ∉ Finset.univ.map f, (A *ᵥ liftFive f p) i < 0)

theorem strictFiveCertificate_of_selected {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = -A) (f : Fin 5 ↪ Fin n) {w : Fin n → ℝ}
    (hw : IsSelected A (Finset.univ.map f) w)
    (hp : ∀ i, 0 < pfaffianVector (A.submatrix f f) i) :
    StrictFiveCertificate A f := by
  let B := A.submatrix f f
  let p := pfaffianVector B
  have hs (i : Fin 5) : f i ∈ Finset.univ.map f := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hsk (i j : Fin 5) : B j i = -B i j := congrFun (congrFun hA (f i)) (f j)
  have hker : B *ᵥ (w ∘ f) = 0 := by
    funext i
    exact (restrict_mulVec A f w (fun j hj => ((hw j).2 hj).1) i).trans ((hw _).1 (hs i)).2
  let c : ℝ := p (Fin.last 4) / w (f (Fin.last 4))
  have hc : 0 < c := div_pos (hp _) ((hw _).1 (hs _)).1
  have hprop : p = c • (w ∘ f) :=
    five_kernel_proportional B hsk (pfaffian_kernel B hsk) hker
      ((hw _).1 (hs _)).1.ne' (hp _).ne'
  have hlift : liftFive f p = c • w := by
    funext i
    by_cases hi : i ∈ Finset.univ.map f
    · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      rw [liftFive_apply]
      exact congrFun hprop j
    · simp [liftFive_off f p hi, ((hw i).2 hi).1]
  refine ⟨hp, fun i hi => ?_⟩
  change (A *ᵥ liftFive f p) i < 0
  rw [hlift, mulVec_smul]
  exact mul_neg_of_pos_of_neg hc ((hw i).2 hi).2

/-- A strict certificate gives a normalized selected occupation, rank four, and uniqueness. -/
theorem StrictFiveCertificate.selected {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = -A) {f : Fin 5 ↪ Fin n} (h : StrictFiveCertificate A f) :
    ∃ w : Fin n → ℝ, (∑ i, w i) = 1 ∧ IsSelected A (Finset.univ.map f) w ∧
      (A.submatrix f f).rank = 4 ∧
      ∀ s v, IsSelected A s v → (∑ i, v i) = 1 → s = Finset.univ.map f ∧ v = w := by
  let B := A.submatrix f f
  let p := pfaffianVector B
  let x := liftFive f p
  let T := ∑ i, x i
  have hp (i : Fin 5) : 0 < p i := h.1 i
  have hsum : T = ∑ j, p j := by
    symm
    calc
      _ = ∑ j ∈ Finset.univ.map f, x j := by simp only [Finset.sum_map, x, liftFive_apply]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => liftFive_off f p hi)
  have hT : 0 < T := hsum.symm ▸ Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
  have hsk (i j : Fin 5) : B j i = -B i j := congrFun (congrFun hA (f i)) (f j)
  let w : Fin n → ℝ := T⁻¹ • x
  have hw : ∑ i, w i = 1 := by
    change (∑ i, T⁻¹ * x i) = 1
    rw [← Finset.mul_sum, inv_mul_cancel₀ hT.ne']
  have hsel : IsSelected A (Finset.univ.map f) w := by
    intro i
    have hdrift : A *ᵥ w = T⁻¹ • (A *ᵥ x) := mulVec_smul _ _ _
    constructor
    · intro hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      have hker := congrFun (pfaffian_kernel B hsk) j
      have he : x ∘ f = p := funext (liftFive_apply f p)
      change (B *ᵥ p) j = 0 at hker
      rw [← he, restrict_mulVec A f x (fun k hk => liftFive_off f p hk) j] at hker
      refine ⟨?_, ?_⟩
      · change 0 < T⁻¹ * x (f j)
        rw [show x (f j) = p j from liftFive_apply f p j]
        exact mul_pos (inv_pos.mpr hT) (hp j)
      · rw [hdrift]
        change T⁻¹ * (A *ᵥ x) (f j) = 0
        rw [show (A *ᵥ x) (f j) = 0 from hker, mul_zero]
    · intro hi
      refine ⟨by change T⁻¹ * x i = 0; rw [show x i = 0 from liftFive_off f p hi, mul_zero], ?_⟩
      rw [hdrift]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr hT) (h.2 i hi)
  exact ⟨w, hw, hsel, rank_four_of_fivePfaffian B hsk (hp _).ne',
    fun _ _ hv hs => selected_normalized_unique hA f hsel hw (hp _).ne' hv hs⟩

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The same first coordinate bath for every matrix of a given dimension. -/
def bathF (𝕜 : Type*) [RCLike 𝕜] (hn : 5 ≤ n) : Matrix (Fin n) (Fin n) 𝕜 :=
  coordinateProjector ⟨0, by omega⟩

/-- The same second coordinate bath for every matrix of a given dimension. -/
def bathG (𝕜 : Type*) [RCLike 𝕜] (hn : 5 ≤ n) : Matrix (Fin n) (Fin n) 𝕜 :=
  coordinateProjector ⟨1, by omega⟩

theorem fixed_baths (𝕜 : Type*) [RCLike 𝕜] (hn : 5 ≤ n) :
    (bathF 𝕜 hn).IsHermitian ∧ (bathG 𝕜 hn).IsHermitian ∧
    bathF 𝕜 hn * bathF 𝕜 hn = bathF 𝕜 hn ∧ bathG 𝕜 hn * bathG 𝕜 hn = bathG 𝕜 hn ∧
    bathF 𝕜 hn * bathG 𝕜 hn = 0 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
    exact Nat.zero_ne_one (congrArg Fin.val h)
  exact ⟨coordinateProjector_hermitian _, coordinateProjector_hermitian _,
    by simp [bathF, coordinateProjector_mul], by simp [bathG, coordinateProjector_mul],
    by simp [bathF, bathG, coordinateProjector_mul, h01]⟩

/-- Inclusion of the first five levels in increasing spectral order. -/
def fiveEmbedding (hn : 5 ≤ n) : Fin 5 ↪ Fin n :=
  ⟨Fin.castLE hn, Fin.castLE_injective hn⟩

def firstFive (hn : 5 ≤ n) : Finset (Fin n) :=
  Finset.univ.map (fiveEmbedding hn)

@[simp] private theorem firstFive_card (hn : 5 ≤ n) : (firstFive hn).card = 5 := by
  simp [firstFive]

/-- The cubic rate matrix from the actual expectations of the fixed projectors
in the columns of an ordered unitary eigenbasis. -/
def fixedBathRates {𝕜 : Type*} [RCLike 𝕜] (hn : 5 ≤ n)
    (d : ℝ) (e : Fin n → ℝ) (U : Matrix.unitaryGroup (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) ℝ :=
  asym d e
    (fun i => RCLike.re (star (fun r => U r i) ⬝ᵥ (bathF 𝕜 hn *ᵥ (fun r => U r i))))
    (fun i => RCLike.re (star (fun r => U r i) ⬝ᵥ (bathG 𝕜 hn *ᵥ (fun r => U r i))))

private theorem firstFive_support (k : ℕ) : firstFive (n := 5 + k) (by omega) = support k := by
  rfl

theorem fixedBathRates_transpose {𝕜 : Type*} [RCLike 𝕜] (hn : 5 ≤ n)
    (e : Fin n → ℝ) (U : Matrix.unitaryGroup (Fin n) 𝕜) :
    (fixedBathRates hn 3 e U)ᵀ = -fixedBathRates hn 3 e U :=
  asym_cubic_transpose _ _ _

private theorem firstFive_all : firstFive (n := 5) (by decide) = Finset.univ := by
  ext i
  simp only [firstFive, Finset.mem_map, Finset.mem_univ, true_and, iff_true]
  exact ⟨i, rfl⟩

private theorem oldEnergy_eq (i : Fin 5) : oldEnergy i = (i.val : ℝ) + 1 := by
  fin_cases i <;> norm_num [oldEnergy]

private theorem energy_append (k : ℕ) :
    Fin.append oldEnergy (fun j : Fin k => (j.val : ℝ) + 6) =
      (fun i : Fin (5 + k) => (i.val : ℝ) + 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, oldEnergy_eq]
    rfl
  · rw [Fin.append_right, Fin.val_natAdd, Nat.cast_add]
    push_cast; ring

private theorem certify {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (hn : 5 ≤ n)
    (e : Fin n → ℝ) (U : Matrix.unitaryGroup (Fin n) 𝕜) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) :
    let A := fixedBathRates hn 3 e U
    let B := A.submatrix (fiveEmbedding hn) (fiveEmbedding hn)
    IsSelected A (firstFive hn) w →
    (∀ i, 0 < pfaffianVector B i) →
    IsSelected A (firstFive hn) w ∧ (∀ i, 0 < pfaffianVector B i) ∧ B.rank = 4 ∧
    (∀ s v, IsSelected A s v → (∑ i, v i) = 1 → s = firstFive hn ∧ v = w) := by
  intro A B hs hp
  have hsk (i j : Fin 5) : B j i = -B i j :=
    congrFun (congrFun (fixedBathRates_transpose hn e U) (fiveEmbedding hn i)) (fiveEmbedding hn j)
  exact ⟨hs, hp, rank_four_of_fivePfaffian B hsk (hp _).ne',
    fun _ _ hv hvsum => selected_normalized_unique (fixedBathRates_transpose hn e U)
      (fiveEmbedding hn) hs hw (hp _).ne' hv hvsum⟩

set_option maxHeartbeats 1000000 in
/-- Every dimension at least five has a Hermitian witness (in particular real symmetric over
ℝ and Hermitian over ℂ). Its spectrum is 1 through n in increasing order. The two baths
are the fixed coordinate projectors and the normalized cubic occupation selects the first five
levels. The factorization is through a unitary matrix, so the columns form a full eigenbasis. -/
theorem exists_fixedBathHamiltonian (𝕜 : Type*) [RCLike 𝕜] (hn : 5 ≤ n) :
    ∃ H : Matrix (Fin n) (Fin n) 𝕜, H.IsHermitian ∧
      ((bathF 𝕜 hn).IsHermitian ∧ (bathG 𝕜 hn).IsHermitian ∧
        bathF 𝕜 hn * bathF 𝕜 hn = bathF 𝕜 hn ∧ bathG 𝕜 hn * bathG 𝕜 hn = bathG 𝕜 hn ∧
        bathF 𝕜 hn * bathG 𝕜 hn = 0) ∧
      ∃ (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) (w : Fin n → ℝ),
        H = spectralMatrix U e ∧
        (∀ i, e i = (i.val : ℝ) + 1) ∧ StrictMono e ∧
        (∀ i, H *ᵥ (fun r => U r i) = (RCLike.ofReal (e i) : 𝕜) • (fun r => U r i)) ∧
        H.charpoly = (∏ i, (Polynomial.X - Polynomial.C (RCLike.ofReal (e i) : 𝕜))) ∧
        (∑ i, w i) = 1 ∧ (firstFive hn).card = 5 ∧
        let A := fixedBathRates hn 3 e U
        let B := A.submatrix (fiveEmbedding hn) (fiveEmbedding hn)
        IsSelected A (firstFive hn) w ∧
        (∀ i, 0 < pfaffianVector B i) ∧ B.rank = 4 ∧
        (∀ s v, IsSelected A s v → (∑ i, v i) = 1 → s = firstFive hn ∧ v = w) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  by_cases hk : k = 0
  · subst k
    obtain ⟨q, hqF, hqG⟩ := five_rows_basis 𝕜
    obtain ⟨_, _, _, hw, hsel⟩ := five_selected
    let U := unitaryOfRows q
    have hF : (fun i => coordinateWeight (⟨0, by decide⟩ : Fin 5) (fun r => U r i)) =
        (fun i => a i ^ 2) := funext (coordinateWeight_unitaryOfRows q 0 a hqF)
    have hG : (fun i => coordinateWeight (⟨1, by decide⟩ : Fin 5) (fun r => U r i)) =
        (fun i => b i ^ 2) := funext (coordinateWeight_unitaryOfRows q 1 b hqG)
    refine ⟨_, spectralMatrix_hermitian U oldEnergy, fixed_baths 𝕜 hn, U, oldEnergy, occupationFive, rfl,
      oldEnergy_eq, ?_, spectralMatrix_eigenvector U oldEnergy, spectralMatrix_charpoly U oldEnergy,
      hw, firstFive_card hn, ?_⟩
    · intro i j hij
      simp only [oldEnergy_eq, add_lt_add_iff_right]
      exact_mod_cast hij
    · apply certify hn oldEnergy U occupationFive hw
      · change IsSelected (asym 3 oldEnergy
          (fun i => coordinateWeight ⟨0, by omega⟩ (fun r => U r i))
          (fun i => coordinateWeight ⟨1, by omega⟩ (fun r => U r i))) (firstFive hn) occupationFive
        rw [hF, hG, firstFive_all]
        exact hsel
      · change ∀ i, 0 < pfaffianVector ((asym 3 oldEnergy
          (fun i => coordinateWeight ⟨0, by omega⟩ (fun r => U r i))
          (fun i => coordinateWeight ⟨1, by omega⟩ (fun r => U r i))).submatrix
          (fiveEmbedding hn) (fiveEmbedding hn)) i
        rw [hF, hG]
        exact five_cubic_pfaffian_pos
  · have hk' : 0 < k := Nat.pos_of_ne_zero hk
    let E (j : Fin k) : ℝ := (j.val : ℝ) + 6
    let e := Fin.append oldEnergy E
    have he : ∀ i, e i = (i.val : ℝ) + 1 := congrFun (energy_append k)
    obtain ⟨q, hqF, hqG⟩ := uniform_rows_basis hk' 𝕜
    obtain ⟨_, hrowF, hrowG⟩ := orthonormal_rows hk'
    have hE (i : Fin k) : 5 < E i := by
      dsimp [E]
      linarith [Nat.cast_nonneg (α := ℝ) i.val]
    obtain ⟨_, _, _, _, hw, _, hsel⟩ := uniform_selected hk' E hE
    let U := unitaryOfRows q
    have hF : (fun i => coordinateWeight (⟨0, by omega⟩ : Fin (5 + k)) (fun r => U r i)) =
        weightsF k := funext fun i => (coordinateWeight_unitaryOfRows q _ _ hqF i).trans (hrowF i)
    have hG : (fun i => coordinateWeight (⟨1, by omega⟩ : Fin (5 + k)) (fun r => U r i)) =
        weightsG k := funext fun i => (coordinateWeight_unitaryOfRows q _ _ hqG i).trans (hrowG i)
    refine ⟨_, spectralMatrix_hermitian U e, fixed_baths 𝕜 hn, U, e, occupation k, rfl,
      he, ?_, spectralMatrix_eigenvector U e, spectralMatrix_charpoly U e,
      hw, firstFive_card hn, ?_⟩
    · intro i j hij
      simp only [he, add_lt_add_iff_right]
      exact_mod_cast hij
    · apply certify hn e U (occupation k) hw
      · change IsSelected (asym 3 e
          (fun i => coordinateWeight ⟨0, by omega⟩ (fun r => U r i))
          (fun i => coordinateWeight ⟨1, by omega⟩ (fun r => U r i))) (firstFive hn) (occupation k)
        rw [hF, hG, firstFive_support]
        exact hsel
      · change ∀ i, 0 < pfaffianVector ((asym 3 e
          (fun i => coordinateWeight ⟨0, by omega⟩ (fun r => U r i))
          (fun i => coordinateWeight ⟨1, by omega⟩ (fun r => U r i))).submatrix
          (fiveEmbedding hn) (fiveEmbedding hn)) i
        rw [hF, hG]
        exact uniform_cubic_pfaffian_pos hk' E hE

end

end D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction
