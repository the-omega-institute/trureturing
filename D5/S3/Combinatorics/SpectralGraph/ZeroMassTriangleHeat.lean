/- GID: D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential]
   utility: none
   digest: Positive triangles with a common massless Schur reduction have distinct collocated heat at the hidden-mass time scale. -/

import D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Heat on a triangle with one vanishing vertex mass

The triangle, modal decomposition, and scaled heat difference come from the
heat calculation in the research note “An exact zero-mass heat and control
separation on a positive triangle” (`triangle-exact-control.txt`, 2026-11-24).
Its vertices 1, 2, and 3 are numbered 0, 1, and 2 here. The stiffness
and impulse-response conventions are shared with `UnequalMassPortHeatResistance`.
The algebraic elimination uses the Schur complement of the weighted Laplacian,
as in Dörfler and Bullo, “Kron Reduction of Graphs With Applications to Electrical
Networks,” §2.1, doi:10.1109/TCSI.2012.2215780.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix BigOperators Topology

namespace D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat

open UnequalMassPortHeatResistance
  (Mat Weights stiffness PositiveWeights edgeWeights stiffness_edges
    inverseRootMassFor normalizedWith physicalHeatWith)
open NormedSpace (exp)

noncomputable section

/-- Vertices 0 and 1 are retained. Vertex 2 has mass ε. -/
def mass (ε : ℝ) : Fin 3 → ℝ := ![1, 1, ε]

/-- The retained edge has conductance k - c/2. Both edges to vertex 2 have conductance c. -/
def weights (k c : ℝ) : Weights := edgeWeights (k - c / 2) c c

private theorem weights_positive (k c : ℝ) (hc : 0 < c) (hck : c < 2 * k) :
    PositiveWeights (weights k c) := by
  intro i j hij
  change i ≠ j at hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    norm_num [weights, edgeWeights, Sym2.lift_mk]
    linarith only [hc, hck]

private theorem stiffness_entries (k c : ℝ) :
    stiffness (weights k c) =
      !![k + c / 2, -(k - c / 2), -c;
         -(k - c / 2), k + c / 2, -c;
         -c, -c, 2 * c] := by
  rw [weights, stiffness_edges]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

/-- The stiffness after eliminating the third vertex by a Schur complement. -/
def masslessStiffness (k c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let L := stiffness (weights k c)
  Matrix.of fun i j =>
    L i.castSucc j.castSucc - L i.castSucc 2 * (L 2 2)⁻¹ * L 2 j.castSucc

private theorem massless_stiffness (k c : ℝ) (hc : 0 < c) :
    masslessStiffness k c = !![k, -k; -k, k] := by
  rw [masslessStiffness, stiffness_entries]
  have h₀ : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have h₁ : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.of_apply, h₀, h₁] <;>
    field_simp [hc.ne'] <;> ring

/-- With zero mass and no injection at vertex 2, its harmonic temperature is
eliminated. The retained masses are one, so the reduced stiffness generates
their physical impulse response. -/
def masslessHeat (k c t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  exp ((-t) • masslessStiffness k c)

private def inverseRootAt (r : ℝ) : Mat :=
  Matrix.diagonal ![1, 1, r⁻¹]

def inverseRootMass (ε : ℝ) : Mat :=
  inverseRootMassFor fun i => Real.sqrt (mass ε i)

private theorem inverse_root_mass_eq (ε : ℝ) :
    inverseRootMass ε = inverseRootAt (Real.sqrt ε) := by
  unfold inverseRootMass inverseRootMassFor inverseRootAt
  congr 1
  funext i
  fin_cases i <;> norm_num [mass]

def normalized (k c ε : ℝ) : Mat :=
  normalizedWith (inverseRootMass ε) (weights k c)

/-- Temperature at the row vertex per unit heat impulse at the column vertex. -/
def physicalHeat (k c ε t : ℝ) : Mat :=
  physicalHeatWith (inverseRootMass ε) (weights k c) t

def fastRate (c ε : ℝ) : ℝ := c * (1 + 2 / ε)

def fastWeight (ε : ℝ) : ℝ := ε / (2 + ε)

private theorem fast_rate_mul_mass (c ε : ℝ) (hε : 0 < ε) :
    fastRate c ε * ε = c * (ε + 2) := by
  unfold fastRate
  field_simp [hε.ne']

private theorem fast_weight_complement (ε : ℝ) (hε : 0 < ε) :
    1 - fastWeight ε = 2 / (2 + ε) := by
  have hd : 2 + ε ≠ 0 := by positivity
  unfold fastWeight
  field_simp [hd]
  ring

/-- The columns are the zero, antisymmetric, and positive symmetric modes.
Here r is the positive square root of the third mass. -/
private def modeBasis (r : ℝ) : Mat :=
  !![1, 1, r;
     1, -1, r;
     r, 0, -2]

private def inverseModeNormSq (r : ℝ) : Fin 3 → ℝ :=
  ![(2 + r ^ 2)⁻¹, 1 / 2, (2 * (2 + r ^ 2))⁻¹]

private def dualBasis (r : ℝ) : Mat :=
  Matrix.diagonal (inverseModeNormSq r) * (modeBasis r)ᵀ

private theorem dual_basis_mul_basis (r : ℝ) : dualBasis r * modeBasis r = 1 := by
  have hd : 2 + r ^ 2 ≠ 0 := by positivity
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [dualBasis, inverseModeNormSq, modeBasis, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.one_apply, Fin.sum_univ_three, Fin.ext_iff] <;>
    field_simp [hd] <;> ring

def modeRates (k c ε : ℝ) : Fin 3 → ℝ :=
  ![0, 2 * k, fastRate c ε]

private theorem generator_mul_basis (k c r : ℝ) (hr : r ≠ 0) :
    (inverseRootAt r * stiffness (weights k c) * inverseRootAt r) * modeBasis r =
      modeBasis r * Matrix.diagonal (modeRates k c (r ^ 2)) := by
  rw [stiffness_entries]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [inverseRootAt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three, modeBasis, modeRates, fastRate] <;>
    field_simp [hr] <;> ring

private theorem basis_mul_dual_basis (r : ℝ) : modeBasis r * dualBasis r = 1 :=
  mul_eq_one_comm.mp (dual_basis_mul_basis r)

private def inModeBasis (r : ℝ) (d : Fin 3 → ℝ) : Mat :=
  modeBasis r * Matrix.diagonal d * dualBasis r

private theorem generator_in_basis (k c r : ℝ) (hr : r ≠ 0) :
    inverseRootAt r * stiffness (weights k c) * inverseRootAt r =
      inModeBasis r (modeRates k c (r ^ 2)) := by
  let H : Mat := inverseRootAt r * stiffness (weights k c) * inverseRootAt r
  change H = _
  calc
    H = H * (modeBasis r * dualBasis r) := by rw [basis_mul_dual_basis, mul_one]
    _ = (H * modeBasis r) * dualBasis r := (mul_assoc H _ _).symm
    _ = _ := congrArg (· * dualBasis r) (generator_mul_basis k c r hr)

private theorem in_mode_basis_mul (r : ℝ) (d e : Fin 3 → ℝ) :
    inModeBasis r d * inModeBasis r e = inModeBasis r (d * e) := by
  unfold inModeBasis
  calc
    _ = modeBasis r * Matrix.diagonal d * (dualBasis r * modeBasis r) *
          Matrix.diagonal e * dualBasis r := by simp only [mul_assoc]
    _ = _ := by
      rw [dual_basis_mul_basis, mul_one, mul_assoc (modeBasis r) (Matrix.diagonal d),
        Matrix.diagonal_mul_diagonal]
      rfl

private theorem in_mode_basis_smul (r a : ℝ) (d : Fin 3 → ℝ) :
    inModeBasis r (a • d) = a • inModeBasis r d := by
  simp only [inModeBasis, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

private theorem in_mode_basis_add (r : ℝ) (d e : Fin 3 → ℝ) :
    inModeBasis r d + inModeBasis r e = inModeBasis r (d + e) := by
  simp only [inModeBasis, ← add_mul, ← mul_add, Matrix.diagonal_add]
  rfl

/-- The normalized orthogonal projections onto the zero, antisymmetric, and symmetric modes. -/
def spectralProjector (ε : ℝ) (i : Fin 3) : Mat :=
  inModeBasis (Real.sqrt ε) (Pi.single i 1)

/-- The spectral projections resolve the identity, with no distinct-rate hypothesis. -/
theorem spectral_projectors (k c ε : ℝ) (hε : 0 < ε) :
    (∀ i, (spectralProjector ε i)ᵀ = spectralProjector ε i) ∧
    (∀ i j, spectralProjector ε i * spectralProjector ε j =
      if i = j then spectralProjector ε i else 0) ∧
    (∑ i, spectralProjector ε i) = 1 ∧
    ∀ i, normalized k c ε * spectralProjector ε i =
      modeRates k c ε i • spectralProjector ε i := by
  let r := Real.sqrt ε
  have hnorm : normalized k c ε = inModeBasis r (modeRates k c ε) := by
    have hr : r ≠ 0 := (Real.sqrt_pos.2 hε).ne'
    rw [normalized, normalizedWith, inverse_root_mass_eq, generator_in_basis k c r hr,
      Real.sq_sqrt hε.le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    let N := Matrix.diagonal (inverseModeNormSq r)
    let E : Mat := Matrix.diagonal (Pi.single i 1)
    change (modeBasis r * E * (N * (modeBasis r)ᵀ))ᵀ =
      modeBasis r * E * (N * (modeBasis r)ᵀ)
    have hN : Nᵀ = N := Matrix.diagonal_transpose _
    have hE : Eᵀ = E := Matrix.diagonal_transpose _
    have hcomm : N * E = E * N :=
      (Matrix.commute_diagonal (inverseModeNormSq r) (Pi.single i (1 : ℝ))).eq
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hN, hE]
    calc
      _ = modeBasis r * (N * E) * (modeBasis r)ᵀ := by simp only [mul_assoc]
      _ = _ := by
        rw [hcomm]
        simp only [mul_assoc]
  · intro i j
    unfold spectralProjector
    rw [in_mode_basis_mul]
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
      congr 1
      funext n
      by_cases hn : n = i <;> simp [hn]
    · rw [ite_eq_right h]
      have hd : (Pi.single i 1 : Fin 3 → ℝ) * (Pi.single j 1 : Fin 3 → ℝ) = 0 := by
        funext n
        by_cases hn : n = i
        · subst n
          simp [h]
        · simp [Pi.single_apply, hn]
      rw [hd]
      simp [inModeBasis]
  · rw [Fin.sum_univ_three]
    simp only [spectralProjector, in_mode_basis_add]
    have hd : (Pi.single 0 1 : Fin 3 → ℝ) + (Pi.single 1 1 : Fin 3 → ℝ) +
        (Pi.single 2 1 : Fin 3 → ℝ) = 1 := by
      funext i
      fin_cases i <;> norm_num [Pi.single_apply, Pi.add_apply, Pi.one_apply, Fin.ext_iff]
    rw [hd, inModeBasis, Matrix.diagonal_one', mul_one, basis_mul_dual_basis]
  · intro i
    rw [hnorm, spectralProjector, in_mode_basis_mul, ← in_mode_basis_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp [smul_eq_mul]
    · simp [hj]

private theorem heat_in_basis (k c r t : ℝ) (hr : r ≠ 0) :
    exp ((-t) • (inverseRootAt r * stiffness (weights k c) * inverseRootAt r)) =
      inModeBasis r ![1, Real.exp (-(2 * k) * t),
        Real.exp (-(fastRate c (r ^ 2)) * t)] := by
  have hPQ := basis_mul_dual_basis r
  have hu : IsUnit (dualBasis r) :=
    (Matrix.isUnit_iff_isUnit_det (dualBasis r)).2 (Matrix.isUnit_det_of_left_inverse hPQ)
  have hexp (A : Mat) :
      exp (modeBasis r * A * dualBasis r) = modeBasis r * exp A * dualBasis r := by
    simpa only [Matrix.inv_eq_left_inv hPQ] using Matrix.exp_conj' (dualBasis r) A hu
  have hentries :
      (fun i : Fin 3 => exp (((-t) • modeRates k c (r ^ 2)) i)) =
        ![1, Real.exp (-(2 * k) * t), Real.exp (-(fastRate c (r ^ 2)) * t)] := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Real.exp_eq_exp_ℝ]
    fin_cases i <;> norm_num [modeRates] <;> ring
  rw [generator_in_basis k c r hr, ← in_mode_basis_smul]
  simp only [inModeBasis, hexp, Matrix.exp_diagonal, Pi.exp_def, hentries]

/-- The physical image of the orthogonal projection onto the zero mode. -/
def zeroPart (ε : ℝ) : Mat :=
  (2 + ε)⁻¹ • Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℝ) ![1, 1, 1]

/-- The antisymmetric mode is supported on the retained vertices. -/
def antisymmetricPart : Mat :=
  (1 / 2 : ℝ) • Matrix.vecMulVec (![1, -1, 0] : Fin 3 → ℝ) ![1, -1, 0]

/-- The physical image of the orthogonal projection onto the positive symmetric mode. -/
def symmetricPart (ε : ℝ) : Mat :=
  (fastWeight ε / 2) •
    Matrix.vecMulVec (![1, 1, -2 / ε] : Fin 3 → ℝ) ![1, 1, -2 / ε]

private theorem physical_diagonal (r a b d : ℝ) (hr : r ≠ 0) :
    inverseRootAt r * inModeBasis r ![a, b, d] * inverseRootAt r =
      a • zeroPart (r ^ 2) + b • antisymmetricPart + d • symmetricPart (r ^ 2) := by
  have hd : 2 + r ^ 2 ≠ 0 := by positivity
  ext i j
  simp only [inverseRootAt, inModeBasis, Matrix.mul_diagonal, Matrix.diagonal_mul,
    zeroPart, antisymmetricPart, symmetricPart, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [modeBasis, dualBasis, inverseModeNormSq, Matrix.diagonal_mul, Matrix.transpose_apply,
      fastWeight] <;>
    field_simp [hr, hd]

theorem physical_projector_images (ε : ℝ) (hε : 0 < ε) :
    let D := inverseRootMass ε
    D * spectralProjector ε 0 * D = zeroPart ε ∧
    D * spectralProjector ε 1 * D = antisymmetricPart ∧
    D * spectralProjector ε 2 * D = symmetricPart ε := by
  have hr : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  have h₀ : Pi.single (0 : Fin 3) (1 : ℝ) = ![1, 0, 0] := by
    funext i
    fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]
  have h₁ : Pi.single (1 : Fin 3) (1 : ℝ) = ![0, 1, 0] := by
    funext i
    fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]
  have h₂ : Pi.single (2 : Fin 3) (1 : ℝ) = ![0, 0, 1] := by
    funext i
    fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]
  dsimp only
  simp only [inverse_root_mass_eq, spectralProjector, h₀, h₁, h₂,
    physical_diagonal _ _ _ _ hr, Real.sq_sqrt hε.le, one_smul, zero_smul, add_zero, zero_add,
    and_self]

/-- The three projections are obtained by conjugating the diagonal coordinate projections.
Both positive contributions are present when their rates coincide. -/
theorem physical_heat_modes (k c ε t : ℝ) (hε : 0 < ε) :
    physicalHeat k c ε t =
      zeroPart ε + Real.exp (-(2 * k) * t) • antisymmetricPart +
        Real.exp (-(fastRate c ε) * t) • symmetricPart ε := by
  have hr : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  unfold physicalHeat physicalHeatWith normalizedWith
  rw [inverse_root_mass_eq, heat_in_basis k c (Real.sqrt ε) t hr,
    physical_diagonal _ _ _ _ hr, Real.sq_sqrt hε.le, one_smul]

private theorem collocated_heat (k c ε t : ℝ) (hε : 0 < ε) :
    physicalHeat k c ε t 0 0 =
      (Real.exp (-(2 * k) * t) + (1 - fastWeight ε) +
        fastWeight ε * Real.exp (-(fastRate c ε) * t)) / 2 := by
  rw [physical_heat_modes k c ε t hε, fast_weight_complement ε hε]
  norm_num [zeroPart, antisymmetricPart, symmetricPart, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem coinciding_rates (k c : ℝ) (hc : 0 < c) (hck : c < 2 * k) :
    0 < 2 * c / (2 * k - c) ∧ fastRate c (2 * c / (2 * k - c)) = 2 * k := by
  have hg : 0 < 2 * k - c := sub_pos.mpr hck
  have hm : 0 < 2 * c / (2 * k - c) := div_pos (by positivity) hg
  refine ⟨hm, ?_⟩
  unfold fastRate
  field_simp [hg.ne', hm.ne', hc.ne']
  ring

/-- The two positive mode projections combine at a repeated eigenvalue. -/
theorem coincident_positive_projector (k c ε : ℝ) (hε : 0 < ε)
    (hRate : fastRate c ε = 2 * k) :
    let P := spectralProjector ε 1 + spectralProjector ε 2
    Pᵀ = P ∧ P * P = P ∧ normalized k c ε = (2 * k) • P := by
  obtain ⟨hs, hm, hsum, he⟩ := spectral_projectors k c ε hε
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.transpose_add, hs]
  · norm_num [add_mul, mul_add, hm, Fin.ext_iff]
  · calc
      normalized k c ε = normalized k c ε * (∑ i, spectralProjector ε i) := by
        rw [hsum, mul_one]
      _ = _ := by
        simp only [Fin.sum_univ_three, mul_add, he]
        change (0 : ℝ) • spectralProjector ε 0 + (2 * k) • spectralProjector ε 1 +
          fastRate c ε • spectralProjector ε 2 =
            (2 * k) • (spectralProjector ε 1 + spectralProjector ε 2)
        rw [hRate, zero_smul, zero_add, smul_add]

theorem physical_heat_at_coincidence (k c ε t : ℝ) (hε : 0 < ε)
    (hRate : fastRate c ε = 2 * k) :
    physicalHeat k c ε t =
      zeroPart ε + Real.exp (-(2 * k) * t) • (antisymmetricPart + symmetricPart ε) := by
  rw [physical_heat_modes k c ε t hε, hRate, smul_add, add_assoc]

theorem collocated_heat_at_coincidence (k c ε t : ℝ) (hε : 0 < ε)
    (hRate : fastRate c ε = 2 * k) :
    physicalHeat k c ε t 0 0 =
      (1 - fastWeight ε) / 2 + (1 + fastWeight ε) / 2 * Real.exp (-(2 * k) * t) := by
  rw [collocated_heat k c ε t hε, hRate]
  ring

private theorem collocated_difference (k c₁ c₂ ε t : ℝ) (hε : 0 < ε) :
    physicalHeat k c₁ ε t 0 0 - physicalHeat k c₂ ε t 0 0 =
      fastWeight ε / 2 *
        (Real.exp (-(fastRate c₁ ε) * t) - Real.exp (-(fastRate c₂ ε) * t)) := by
  rw [collocated_heat k c₁ ε t hε, collocated_heat k c₂ ε t hε]
  ring

theorem collocated_difference_at_mass_time (k c₁ c₂ ε s : ℝ) (hε : 0 < ε) :
    (physicalHeat k c₁ ε (ε * s) 0 0 - physicalHeat k c₂ ε (ε * s) 0 0) / ε =
      (Real.exp (-c₁ * (ε + 2) * s) - Real.exp (-c₂ * (ε + 2) * s)) /
        (2 * (2 + ε)) := by
  have phase (c : ℝ) : -(fastRate c ε) * (ε * s) = -c * (ε + 2) * s := by
    calc
      _ = -(fastRate c ε * ε) * s := by ring
      _ = _ := by rw [fast_rate_mul_mass c ε hε]; ring
  have hd : 2 + ε ≠ 0 := by positivity
  rw [collocated_difference k c₁ c₂ ε (ε * s) hε, phase c₁, phase c₂]
  unfold fastWeight
  field_simp [hd, hε.ne']

private theorem exp_difference_ne_zero (c₁ c₂ a s : ℝ) (ha : a ≠ 0) (hs : s ≠ 0)
    (hc : c₁ ≠ c₂) : Real.exp (-c₁ * a * s) - Real.exp (-c₂ * a * s) ≠ 0 := by
  refine sub_ne_zero.mpr ?_
  intro he
  have hn : -c₁ = -c₂ :=
    mul_right_cancel₀ ha (mul_right_cancel₀ hs (Real.exp_injective he))
  exact hc (by linarith only [hn])

/-- Different hidden-edge conductances give different actual port temperatures
at the positive time on the hidden-mass scale. -/
private theorem collocated_heat_ne_at_mass_time (k c₁ c₂ ε s : ℝ)
    (hε : 0 < ε) (hs : 0 < s) (hc : c₁ ≠ c₂) :
    physicalHeat k c₁ ε (ε * s) 0 0 ≠ physicalHeat k c₂ ε (ε * s) 0 0 := by
  have ha : ε + 2 ≠ 0 := by positivity
  have hd : 2 * (2 + ε) ≠ 0 := by positivity
  have hne := div_ne_zero (exp_difference_ne_zero c₁ c₂ (ε + 2) s ha hs.ne' hc) hd
  intro he
  have hdiff := collocated_difference_at_mass_time k c₁ c₂ ε s hε
  rw [he, sub_self, zero_div] at hdiff
  exact hne hdiff.symm

/-- The full exactly massless heat operator is common to the positive
conductance family. At positive hidden mass, one retained port separates the
conductances at time εs. -/
theorem same_schur_distinct_heat_at_mass_time (k ε s : ℝ) (hε : 0 < ε) (hs : 0 < s) :
    (∀ c ∈ Set.Ioo 0 (2 * k),
      PositiveWeights (weights k c) ∧
      masslessStiffness k c = !![k, -k; -k, k] ∧
      ∀ t : ℝ, masslessHeat k c t = exp ((-t) • (!![k, -k; -k, k] :
        Matrix (Fin 2) (Fin 2) ℝ))) ∧
    Set.InjOn (fun c : ℝ => physicalHeat k c ε (ε * s) 0 0) (Set.Ioo 0 (2 * k)) := by
  constructor
  · intro c hc
    have hSchur := massless_stiffness k c hc.1
    exact ⟨weights_positive k c hc.1 hc.2, hSchur, fun t => by rw [masslessHeat, hSchur]⟩
  · intro c₁ _ c₂ _ he
    by_contra hc
    exact collocated_heat_ne_at_mass_time k c₁ c₂ ε s hε hs hc he

theorem collocated_difference_limit (k c₁ c₂ s : ℝ) (hs : 0 < s) (hc : c₁ ≠ c₂) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (physicalHeat k c₁ ε (ε * s) 0 0 - physicalHeat k c₂ ε (ε * s) 0 0) / ε)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 ((Real.exp (-c₁ * 2 * s) - Real.exp (-c₂ * 2 * s)) / 4)) ∧
    (Real.exp (-c₁ * 2 * s) - Real.exp (-c₂ * 2 * s)) / 4 ≠ 0 := by
  constructor
  · let g : ℝ → ℝ := fun ε =>
      (Real.exp (-c₁ * (ε + 2) * s) - Real.exp (-c₂ * (ε + 2) * s)) /
        (2 * (2 + ε))
    have hg : ContinuousAt g 0 := by
      dsimp only [g]
      apply ContinuousAt.div₀
      · fun_prop
      · fun_prop
      · norm_num
    have hg₀ : g 0 = (Real.exp (-c₁ * 2 * s) - Real.exp (-c₂ * 2 * s)) / 4 := by
      norm_num [g]
    have hlim : Filter.Tendsto g (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 ((Real.exp (-c₁ * 2 * s) - Real.exp (-c₂ * 2 * s)) / 4)) := by
      rw [← hg₀]
      exact hg.tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [eventually_mem_nhdsWithin
      (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))] with ε hε
    exact (collocated_difference_at_mass_time k c₁ c₂ ε s hε).symm
  · exact div_ne_zero (exp_difference_ne_zero c₁ c₂ 2 s (by norm_num) hs.ne' hc) (by norm_num)

/-- The physical input and output direction on the two retained vertices. -/
def symmetricPort : Fin 3 → ℝ := ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0]

def symmetricRead (A : Mat) : ℝ :=
  dotProduct symmetricPort (A *ᵥ symmetricPort)

private theorem symmetric_read_entries (A : Mat) :
    symmetricRead A = (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2 := by
  have hroot : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi : ((Real.sqrt (2 : ℝ))⁻¹) ^ 2 = 2⁻¹ := by rw [inv_pow, hroot]
  have h₀ : symmetricPort 0 = (Real.sqrt 2)⁻¹ := rfl
  have h₁ : symmetricPort 1 = (Real.sqrt 2)⁻¹ := rfl
  have h₂ : symmetricPort 2 = 0 := rfl
  calc
    symmetricRead A =
        ((Real.sqrt (2 : ℝ))⁻¹) ^ 2 * (A 0 0 + A 0 1 + A 1 0 + A 1 1) := by
      simp only [symmetricRead, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        h₀, h₁, h₂, mul_zero, zero_mul, add_zero]
      ring
    _ = _ := by rw [hi]; ring

theorem symmetric_port_heat (k c ε t : ℝ) (hε : 0 < ε) :
    symmetricRead (physicalHeat k c ε t) =
      1 - fastWeight ε + fastWeight ε * Real.exp (-(fastRate c ε) * t) := by
  rw [symmetric_read_entries, physical_heat_modes k c ε t hε, fast_weight_complement ε hε]
  norm_num [zeroPart, antisymmetricPart, symmetricPart, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end

end D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat
