/- GID: D5/S3/Quantum/Semigroups/WuCubicHellingerMatrix
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicHellingerMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit Wu cubic spectral matrices imply the physical Hellinger margin. -/

import D5.S3.Quantum.Semigroups.WuCubicHellingerReplay
import Mathlib.LinearAlgebra.Matrix.PosDef
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The real spectral tests used by the 103-box upper focal certificate for
Wu v1 (3.54). Matrix entries use the direct formulas of `verify.py`. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicOccupationTaylor (gibbsLevels cubicMass massDisplacement occupationEnergyFactor
  occupationEdgeSum occupationTaylorCoefficient)
open WuCubicGibbsScaledCoefficients
open WuCubicHellingerReplay (normalized_deficit_ge_of_signed_forms)
open private gamma c e bias cutA cutB from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private adjacentFactor from D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients

abbrev Vec3 := Fin 3 → ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The three nonzero rows of the direction basis used in the certificate. -/
def basis : Mat3 := ![![1, 0, 0], ![1 / 2, 1, -1], ![1 / 2, 1, 1]]

def coordinates (h : Fin 4 → ℝ) : Vec3 :=
  ![h 0, (h 1 + h 2 - h 0) / 2, (h 2 - h 1) / 2]

def displacement (d : ℝ) (h : Fin 4 → ℝ) : Vec3 :=
  fun i => d * h i.castSucc

def levels (r : ℝ) (y : Vec3) : Vec3 :=
  fun i => gibbsLevels r i.castSucc + y i

/-- The three offsets from the box coordinates `(y₀, y₁, blend)`. -/
def focalOffsets (y₀ y₁ blend : ℝ) : Vec3 :=
  ![y₀, y₁, y₁ + (1 / 128 - y₁) * blend]

theorem focalOffsets_gap (y₀ y₁ blend : ℝ) :
    focalOffsets y₀ y₁ blend 2 - focalOffsets y₀ y₁ blend 1 =
      (1 / 128 - y₁) * blend := by
  change (y₁ + (1 / 128 - y₁) * blend) - y₁ = _
  ring

def quadratic (M : Mat3) (v : Vec3) : ℝ := dotProduct v (M *ᵥ v)

private theorem cast_zero : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
private theorem cast_one : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
private theorem cast_two : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl

theorem basis_coordinates (h : Fin 4 → ℝ) (i : Fin 3) :
    dotProduct (basis i) (coordinates h) = h i.castSucc := by
  fin_cases i <;>
    norm_num [basis, coordinates, dotProduct, Fin.sum_univ_three,
      cast_zero, cast_one, cast_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

private def edgeRows (r : ℝ) : Fin 4 → Vec3 :=
  ![fun i => r * basis 0 i - basis 1 i, fun i => r * basis 0 i - basis 2 i,
    fun i => r * basis 1 i, fun i => r * basis 2 i]

private def edgeWeights (r : ℝ) (y : Vec3) : Fin 4 → ℝ :=
  let x := levels r y
  ![r * x 0 + x 1, r * x 0 + x 2, r * x 1 + 1, r * x 2 + 1]

private def entropyWeights (r : ℝ) (y : Vec3) : Vec3 :=
  fun i => gibbsLevels r i.castSucc + y i + (1 / 3) * (y i) ^ 2

private def massWeights (r : ℝ) (y : Vec3) : Vec3 :=
  fun i =>
    let g := gibbsLevels r i.castSucc
    3 * g ^ 2 + y i * (3 * g + y i)

private def massChange (r : ℝ) (y : Vec3) : ℝ :=
  ∑ k, y k * massWeights r y k

private def massRow (r : ℝ) (y : Vec3) : Vec3 :=
  fun i => ∑ k, massWeights r y k * basis k i

private def gibbsMass (r : ℝ) : ℝ := (1 + (r ^ 3)⁻¹) ^ 2

/-- The occupation matrix `O₀ + d O₁`, in the certificate's basis. -/
def occupationMatrix (r : ℝ) (y : Vec3) : Mat3 :=
  fun i j =>
    gamma r * (∑ k, edgeWeights r y k * edgeRows r k i * edgeRows r k j) -
    (9 / 4) * (∑ k, entropyWeights r y k * basis k i * basis k j) +
    ((1 - massChange r y / (3 * gibbsMass r)) / (4 * gibbsMass r)) *
      massRow r y i * massRow r y j

set_option maxHeartbeats 800000 in
private theorem quadratic_rankOne_sums (a b : ℝ) (w : Fin 4 → ℝ) (u : Fin 4 → Vec3)
    (f : Vec3) (B : Mat3) (μ v : Vec3) :
    quadratic (fun i j =>
      a * (∑ k, w k * u k i * u k j) -
      (9 / 4) * (∑ k, f k * B k i * B k j) + b * μ i * μ j) v =
      a * (∑ k, w k * (dotProduct (u k) v) ^ 2) -
      (9 / 4) * (∑ k, f k * (dotProduct (B k) v) ^ 2) + b * (dotProduct μ v) ^ 2 := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem edgeRows_dot (r : ℝ) (h : Fin 4 → ℝ) :
    (fun i => dotProduct (edgeRows r i) (coordinates h)) =
      ![r * h 0 - h 1, r * h 0 - h 2, r * h 1, r * h 2] := by
  funext i
  fin_cases i <;>
    norm_num [edgeRows, basis, coordinates, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

private theorem edge_energy_eq {r : ℝ} (hr : 0 < r) (d : ℝ)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    gamma r * (∑ k, edgeWeights r (displacement d h) k *
      (dotProduct (edgeRows r k) (coordinates h)) ^ 2) =
      occupationEnergyFactor r d h := by
  have hg₀ : r * (r ^ 2)⁻¹ = r⁻¹ := by field_simp [hr.ne'] <;> ring
  have hg₁ : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hrow (k : Fin 4) :
      dotProduct (edgeRows r k) (coordinates h) =
        ![r * h 0 - h 1, r * h 0 - h 2, r * h 1, r * h 2] k :=
    congrFun (edgeRows_dot r h) k
  unfold occupationEnergyFactor
  apply congrArg (fun E : ℝ => gamma r * E)
  simp only [hrow, Fin.sum_univ_four]
  norm_num [edgeWeights, occupationEdgeSum, levels, displacement,
    gibbsLevels, cast_zero, cast_one, cast_two, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    simp only [mul_add, hg₀, hg₁] <;> ring

private theorem entropy_sum_eq (r d : ℝ) (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    (∑ k, entropyWeights r (displacement d h) k * (dotProduct (basis k) (coordinates h)) ^ 2) =
      (∑ i, gibbsLevels r i * h i ^ 2) + d * (∑ i, h i ^ 3) +
        (1 / 3) * d ^ 2 * (∑ i, h i ^ 4) := by
  simp only [basis_coordinates, entropyWeights, displacement, Fin.sum_univ_three,
    Fin.sum_univ_four, cast_zero, cast_one, cast_two, hh]
  ring

private theorem massRow_dot (r : ℝ) (y : Vec3) (h : Fin 4 → ℝ) :
    dotProduct (massRow r y) (coordinates h) = ∑ k, massWeights r y k * h k.castSucc := by
  calc
    _ = ∑ k, massWeights r y k * dotProduct (basis k) (coordinates h) := by
      simp only [massRow, dotProduct, Fin.sum_univ_three]
      ring
    _ = _ := by simp only [basis_coordinates]

private theorem mass_row_eq (r d : ℝ) (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    dotProduct (massRow r (displacement d h)) (coordinates h) =
      massDisplacement (gibbsLevels r) h d := by
  rw [massRow_dot]
  simp only [massWeights, massDisplacement, displacement, Fin.sum_univ_three, Fin.sum_univ_four,
    cast_zero, cast_one, cast_two, hh]
  ring

private theorem mass_change_eq (r d : ℝ) (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    massChange r (displacement d h) = d * massDisplacement (gibbsLevels r) h d := by
  rw [← mass_row_eq r d h hh, massRow_dot]
  simp only [massChange, Finset.mul_sum, displacement]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem gibbs_mass_eq {r : ℝ} (hr : 0 < r) :
    cubicMass (gibbsLevels r) = gibbsMass r := by
  norm_num [cubicMass, gibbsLevels, gibbsMass, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp [hr.ne'] <;> ring

private theorem mass_factor {T : ℝ} (hT : T ≠ 0) (d μ : ℝ) :
    ((1 - d * μ / (3 * T)) / (4 * T)) * μ ^ 2 =
      μ ^ 2 / (4 * T) - d * μ ^ 3 / (12 * T ^ 2) := by
  field_simp [hT] <;> ring

/-- The actual Taylor coefficient equals the direct occupation quadratic of
the certificate, including at zero displacement. -/
theorem occupationTaylorCoefficient_eq_quadratic {r : ℝ} (hr : 0 < r) (d : ℝ)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    occupationTaylorCoefficient r d h =
      quadratic (occupationMatrix r (displacement d h)) (coordinates h) := by
  have hT : gibbsMass r ≠ 0 := by unfold gibbsMass; positivity
  let y := displacement d h
  change occupationTaylorCoefficient r d h = quadratic (occupationMatrix r y) (coordinates h)
  change occupationTaylorCoefficient r d h = quadratic (fun i j =>
    gamma r * (∑ k, edgeWeights r y k * edgeRows r k i * edgeRows r k j) -
      (9 / 4) * (∑ k, entropyWeights r y k * basis k i * basis k j) +
      ((1 - massChange r y / (3 * gibbsMass r)) / (4 * gibbsMass r)) *
        massRow r y i * massRow r y j) (coordinates h)
  rw [quadratic_rankOne_sums (gamma r)
    ((1 - massChange r y / (3 * gibbsMass r)) / (4 * gibbsMass r))
    (edgeWeights r y) (edgeRows r) (entropyWeights r y) basis (massRow r y),
    edge_energy_eq hr d h hh,
    entropy_sum_eq r d h hh, mass_change_eq r d h hh, mass_row_eq r d h hh,
    mass_factor hT]
  simp only [occupationTaylorCoefficient, gibbs_mass_eq hr]
  ring

/-- The debit represents `‖h‖²/64 + 3 h₀ (h₂ - h₁)/2` in the same basis. -/
def debitMatrix : Mat3 :=
  let cross : Mat3 := ![![0, 0, 3 / 2], ![0, 0, 0], ![3 / 2, 0, 0]]
  fun i j => (∑ k, basis k i * basis k j) / 64 + cross i j

theorem debit_quadratic (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    quadratic debitMatrix (coordinates h) = (∑ i, h i ^ 2) / 64 +
      (3 / 2) * h 0 * (h 2 - h 1) := by
  norm_num [quadratic, debitMatrix, basis, coordinates, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_four, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

private def leftGap (r : ℝ) (y : Vec3) : ℝ :=
  (r ^ 2)⁻¹ + (y 1 - y 0) / (r - 1)

private def middleGap (r : ℝ) (y : Vec3) : ℝ :=
  (y 2 - y 1) / (r - 1)

private def rightGap (r : ℝ) (y : Vec3) : ℝ :=
  r⁻¹ - y 2 / (r - 1)

private def fieldOverGap (r : ℝ) : ℝ :=
  2 * gamma r * r * (r ^ 2 + 4 * r + 1) / (3 * (r ^ 2 + r + 1))

private def scaledMixture (r : ℝ) (y : Vec3) : ℝ :=
  let n := levels r y 1
  let q := levels r y 2
  let s := middleGap r y
  s * (fieldOverGap r * (n ^ 2 + n * q + q ^ 2) / 2 +
    e r * (r - 1) * s ^ 2 - c r * s * (n + q))

/-- The lower matched weight after division by `(r - 1)^2`. -/
def lowerWeight (r : ℝ) (y : Vec3) : ℝ :=
  let m := levels r y 0
  let n := levels r y 1
  let q := levels r y 2
  let l := leftGap r y
  let s := middleGap r y
  (c r * l ^ 2 * (m + n) +
    l * s * (c r * (m + 2 * n + q) - 3 * e r * (r - 1) * (l + s)) -
    scaledMixture r y) / 2

/-- The upper matched weight after division by `(r - 1)^2`. -/
def upperWeight (r : ℝ) (y : Vec3) : ℝ :=
  let n := levels r y 1
  let q := levels r y 2
  let s := middleGap r y
  let u := rightGap r y
  (c r * u ^ 2 * (q + 1) +
    u * s * (c r * (n + 2 * q + 1) - 3 * e r * (r - 1) * (s + u)) -
    scaledMixture r y) / 2

def weightSum (r : ℝ) (y : Vec3) : ℝ := lowerWeight r y + upperWeight r y

/-- The long coefficient `4κ` after division by `(r - 1)^2`. -/
def longCrossing (r : ℝ) (y : Vec3) : ℝ :=
  let x := levels r y
  let l := leftGap r y
  let s := middleGap r y
  let u := rightGap r y
  l * u * (c r * (x 0 + x 1 + x 2 + 1) - 3 * e r * (r - 1) * (l + u + 2 * s))

private abbrev matchedLower (r m n q : ℝ) : ℝ :=
  (cutEnergy r m n q 0 + lowerCoeff r m n q -
    matchedMixture (cutEnergy r m n q) (cutBias r m n q)) / 2

private abbrev matchedUpper (r m n q : ℝ) : ℝ :=
  (cutEnergy r m n q 2 + upperCoeff r n q -
    matchedMixture (cutEnergy r m n q) (cutBias r m n q)) / 2

private theorem gap_scaling {r : ℝ} (hr : 1 < r) (y : Vec3) :
    levels r y 1 - levels r y 0 = (r - 1) * leftGap r y ∧
    levels r y 2 - levels r y 1 = (r - 1) * middleGap r y ∧
    1 - levels r y 2 = (r - 1) * rightGap r y := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have ht := (sub_pos.mpr hr).ne'
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [levels, gibbsLevels, leftGap, middleGap, rightGap, cast_zero, cast_one,
      cast_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> field_simp [hr₀.ne', ht] <;> ring

private theorem bias_scaling (r : ℝ) : bias r = (r - 1) * fieldOverGap r := by
  simp only [bias, fieldOverGap, div_eq_mul_inv]
  ring

private theorem cut_scaling {r : ℝ} (hr : 1 < r) (y : Vec3) :
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    matchedLower r m n q = (r - 1) ^ 2 * lowerWeight r y ∧
    matchedUpper r m n q = (r - 1) ^ 2 * upperWeight r y ∧
    longCoeff r m n q = (r - 1) ^ 2 * longCrossing r y := by
  intro m n q
  obtain ⟨hl, hs, hu⟩ := gap_scaling hr y
  change n - m = _ at hl
  change q - n = _ at hs
  change 1 - q = _ at hu
  have hmix : matchedMixture (cutEnergy r m n q) (cutBias r m n q) =
      (r - 1) ^ 2 * scaledMixture r y := by
    rw [matched_mixture_eq]
    unfold matchedMixtureScaled middleBiasScaled middleEnergyScaled
    rw [hs, bias_scaling]
    unfold scaledMixture
    change _ = (r - 1) ^ 2 *
      (middleGap r y * (fieldOverGap r * (n ^ 2 + n * q + q ^ 2) / 2 +
        e r * (r - 1) * (middleGap r y) ^ 2 - c r * middleGap r y * (n + q)))
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (cutA r m n + lowerCoeff r m n q -
      matchedMixture (cutEnergy r m n q) (cutBias r m n q)) / 2 = _
    rw [hmix, lower_coeff_eq]
    simp only [cutA, lowerCoeffScaled, adjacentFactor, hl, hs, lowerWeight]
    change _ = (r - 1) ^ 2 *
      ((c r * (leftGap r y) ^ 2 * (m + n) +
        leftGap r y * middleGap r y * (c r * (m + 2 * n + q) -
          3 * e r * (r - 1) * (leftGap r y + middleGap r y)) - scaledMixture r y) / 2)
    ring
  · change (cutA r q 1 + upperCoeff r n q -
      matchedMixture (cutEnergy r m n q) (cutBias r m n q)) / 2 = _
    rw [hmix, upper_coeff_eq]
    simp only [cutA, upperCoeffScaled, adjacentFactor, hs, hu, upperWeight]
    change _ = (r - 1) ^ 2 *
      ((c r * (rightGap r y) ^ 2 * (q + 1) +
        rightGap r y * middleGap r y * (c r * (n + 2 * q + 1) -
          3 * e r * (r - 1) * (middleGap r y + rightGap r y)) - scaledMixture r y) / 2)
    ring
  · rw [long_coeff_eq, hl, hs, hu]
    change _ = (r - 1) ^ 2 *
      (leftGap r y * rightGap r y * (c r * (m + n + q + 1) -
        3 * e r * (r - 1) * (leftGap r y + rightGap r y + 2 * middleGap r y)))
    ring

private def endpointLinear (r v w : ℝ) : ℝ :=
  r * (r + 2) * v + (2 * r + 1) * w

private def endpointField (r : ℝ) : ℝ := gamma r * r / (r ^ 2 + r + 1)

private def endpointWeight (r v w : ℝ) : ℝ :=
  endpointField r * ((w - v) * endpointLinear r v w)

private theorem cut_endpoint_factor (r : ℝ) (v w : ℝ) :
    cutB r v w / 2 - cutA r v w = endpointWeight r v w * (r * v - w) := by
  have hD : r ^ 2 + r + 1 ≠ 0 :=
    ne_of_gt (by nlinarith only [sq_nonneg (r + 1 / 2)])
  unfold cutB cutA endpointWeight endpointField endpointLinear bias c e
  generalize hden : r ^ 2 + r + 1 = D at hD ⊢
  field_simp [hD]
  subst D
  ring

set_option maxHeartbeats 800000 in
/-- The telescoping identity from `WuCubicGibbsUpperUniform.matched_endpoint_tilts`,
extended to zero displacement. -/
private theorem matched_endpoint_tilts {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    let x := levels r (displacement d h)
    g0scaled r d h = endpointWeight r (x 0) (x 2) * (r * h 0 - h 2) ∧
    g2scaled r d h = endpointWeight r (x 1) 1 * (r * h 1) := by
  rcases eq_or_lt_of_le hd with hzero | hd
  · subst d
    have hT : 1 + r ^ 3 ≠ 0 := by positivity
    have hD : r ^ 2 + r + 1 ≠ 0 := by positivity
    have hE : r ^ 2 - r + 1 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg (r - 1 / 2)])
    have hC : gradientCoefficient r =
        27 * (r - 1) * (r + 1) / (4 * (1 + r ^ 3) * (r ^ 2 + r + 1)) := by
      unfold gradientCoefficient
      apply (div_eq_div_iff
        (mul_ne_zero (mul_ne_zero (by norm_num) hE) hD)
        (mul_ne_zero (mul_ne_zero (by norm_num) hT) hD)).2
      rw [show 1 + r ^ 3 = (r + 1) * (r ^ 2 - r + 1) by ring]
      ring
    constructor <;>
      simp only [g0scaled, g2scaled, zero_mul, add_zero, hC] <;>
      norm_num [endpointWeight, endpointField,
        endpointLinear, gamma, levels, displacement, gibbsLevels, cast_zero, cast_one, cast_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
      generalize htotal : 1 + r ^ 3 = T at hT ⊢ <;>
      generalize hden : r ^ 2 + r + 1 = D at hD ⊢ <;>
      field_simp [hr.ne', hT, hD] <;> subst T <;> subst D <;> ring
  · intro x
    let m := x 0
    let n := x 1
    let q := x 2
    obtain ⟨h₀, h₂⟩ := gibbs_endpoint_linear_costs_eq hr d h hh
    change cutBias r m n q 0 / 2 - 2 * matchedLower r m n q = d * g0scaled r d h at h₀
    change cutBias r m n q 2 / 2 - 2 * matchedUpper r m n q = d * g2scaled r d h at h₂
    have htel₀ : cutBias r m n q 0 / 2 - 2 * matchedLower r m n q =
        cutB r m q / 2 - cutA r m q := by
      change cutB r m n / 2 - 2 * ((cutA r m n + lowerCoeff r m n q -
        (cutB r n q / 2 - cutA r n q)) / 2) = _
      rw [lower_coeff_eq]
      simp only [cutB, cutA, lowerCoeffScaled, adjacentFactor]
      ring
    have htel₂ : cutBias r m n q 2 / 2 - 2 * matchedUpper r m n q =
        cutB r n 1 / 2 - cutA r n 1 := by
      change cutB r q 1 / 2 - 2 * ((cutA r q 1 + upperCoeff r n q -
        (cutB r n q / 2 - cutA r n q)) / 2) = _
      rw [upper_coeff_eq]
      simp only [cutB, cutA, upperCoeffScaled, adjacentFactor]
      ring
    have hgap₀ : r * m - q = d * (r * h 0 - h 2) := by
      change r * ((r ^ 2)⁻¹ + d * h 0) - (r⁻¹ + d * h 2) = _
      field_simp [hr.ne'] <;> ring
    have hgap₂ : r * n - 1 = d * (r * h 1) := by
      change r * (r⁻¹ + d * h 1) - 1 = _
      field_simp [hr.ne'] <;> ring
    rw [htel₀, cut_endpoint_factor, hgap₀, ← mul_assoc, mul_comm (endpointWeight r m q) d,
      mul_assoc] at h₀
    rw [htel₂, cut_endpoint_factor, hgap₂, ← mul_assoc, mul_comm (endpointWeight r n 1) d,
      mul_assoc] at h₂
    exact ⟨(mul_left_cancel₀ hd.ne' h₀).symm, (mul_left_cancel₀ hd.ne' h₂).symm⟩

private def lowerTiltFactor (r : ℝ) (y : Vec3) : ℝ :=
  endpointField r * ((r ^ 2)⁻¹ + (y 2 - y 0) / (r - 1)) *
    endpointLinear r (levels r y 0) (levels r y 2)

private def upperTiltFactor (r : ℝ) (y : Vec3) : ℝ :=
  endpointField r * (r⁻¹ - y 1 / (r - 1)) * endpointLinear r (levels r y 1) 1 * r

/-- The two tilt rows are divided by `r - 1`. -/
def lowerTilt (r : ℝ) (y : Vec3) : Vec3 := fun i => lowerTiltFactor r y * edgeRows r 1 i

def upperTilt (r : ℝ) (y : Vec3) : Vec3 := fun i => upperTiltFactor r y * basis 1 i

private theorem dot_scale (a : ℝ) (u v : Vec3) :
    dotProduct (fun i => a * u i) v = a * dotProduct u v := by
  simp only [dotProduct, Fin.sum_univ_three]
  ring

private theorem lowerTilt_dot (r : ℝ) (y : Vec3) (h : Fin 4 → ℝ) :
    dotProduct (lowerTilt r y) (coordinates h) = lowerTiltFactor r y * (r * h 0 - h 2) := by
  change dotProduct (fun i => lowerTiltFactor r y * edgeRows r 1 i) (coordinates h) = _
  rw [dot_scale (lowerTiltFactor r y) (edgeRows r 1)]
  exact congrArg (fun a => lowerTiltFactor r y * a) (congrFun (edgeRows_dot r h) 1)

private theorem upperTilt_dot (r : ℝ) (y : Vec3) (h : Fin 4 → ℝ) :
    dotProduct (upperTilt r y) (coordinates h) = upperTiltFactor r y * h 1 := by
  change dotProduct (fun i => upperTiltFactor r y * basis 1 i) (coordinates h) = _
  rw [dot_scale (upperTiltFactor r y) (basis 1), basis_coordinates, cast_one]

private theorem tilt_scaling {r d : ℝ} (hr : 1 < r) (hd : 0 ≤ d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    let y := displacement d h
    g0scaled r d h = (r - 1) * dotProduct (lowerTilt r y) (coordinates h) ∧
    g2scaled r d h = (r - 1) * dotProduct (upperTilt r y) (coordinates h) := by
  intro y
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have ht := (sub_pos.mpr hr).ne'
  obtain ⟨h₀, h₂⟩ := matched_endpoint_tilts hr₀ hd h hh
  change g0scaled r d h = endpointWeight r (levels r y 0) (levels r y 2) * _ at h₀
  change g2scaled r d h = endpointWeight r (levels r y 1) 1 * _ at h₂
  have hlo : levels r y 2 - levels r y 0 =
      (r - 1) * ((r ^ 2)⁻¹ + (y 2 - y 0) / (r - 1)) := by
    change r⁻¹ + y 2 - ((r ^ 2)⁻¹ + y 0) = _
    field_simp [hr₀.ne', ht] <;> ring
  have hup : 1 - levels r y 1 = (r - 1) * (r⁻¹ - y 1 / (r - 1)) := by
    change 1 - (r⁻¹ + y 1) = _
    field_simp [hr₀.ne', ht] <;> ring
  constructor
  · rw [h₀, lowerTilt_dot, endpointWeight, hlo, lowerTiltFactor]
    ring
  · rw [h₂, upperTilt_dot, endpointWeight, hup, upperTiltFactor]
    ring

def signedRow (sign r : ℝ) (y : Vec3) : Vec3 :=
  fun i =>
    weightSum r y * (lowerTilt r y i + upperTilt r y i) +
      sign * ((upperWeight r y * lowerTilt r y i - lowerWeight r y * upperTilt r y i) / 3)

/-- The two matrices are obtained with `sign = -1` and `sign = 1` in that order. -/
def signedMatrix (sign r : ℝ) (y : Vec3) : Mat3 :=
  fun i j =>
    4 * (weightSum r y) ^ 3 * (occupationMatrix r y i j - debitMatrix i j) -
      signedRow sign r y i * signedRow sign r y j

theorem signedMatrix_isSymm (sign r : ℝ) (y : Vec3) :
    (signedMatrix sign r y).IsSymm := by
  change (signedMatrix sign r y)ᵀ = signedMatrix sign r y
  apply Matrix.ext
  intro i j
  change signedMatrix sign r y j i = signedMatrix sign r y i j
  have hocc : occupationMatrix r y j i = occupationMatrix r y i j := by
    simp only [occupationMatrix, Fin.sum_univ_three, Fin.sum_univ_four]
    ring
  have hdebit : debitMatrix j i = debitMatrix i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [debitMatrix, basis, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [signedMatrix, hocc, hdebit]
  ring

private theorem signedRow_dot (sign r : ℝ) (y v : Vec3) :
    dotProduct (signedRow sign r y) v =
      weightSum r y * (dotProduct (lowerTilt r y) v + dotProduct (upperTilt r y) v) +
      sign * ((upperWeight r y * dotProduct (lowerTilt r y) v -
        lowerWeight r y * dotProduct (upperTilt r y) v) / 3) := by
  simp only [signedRow, dotProduct, Fin.sum_univ_three]
  ring

private theorem signedMatrix_quadratic (sign r : ℝ) (y v : Vec3) :
    quadratic (signedMatrix sign r y) v =
      4 * (weightSum r y) ^ 3 *
        (quadratic (occupationMatrix r y) v - quadratic debitMatrix v) -
      (dotProduct (signedRow sign r y) v) ^ 2 := by
  simp only [quadratic, signedMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- Each direct matrix quadratic is the corresponding physical signed form
with the common thermal factor removed. -/
theorem signedMatrix_quadratic_eq (sign : ℝ) {r d : ℝ} (hr : 1 < r) (hd : 0 ≤ d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    let y := displacement d h
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let P₀ := matchedLower r m n q
    let P₂ := matchedUpper r m n q
    let p := P₀ + P₂
    let g₀ := g0scaled r d h
    let g₂ := g2scaled r d h
    let z := (P₂ * g₀ - P₀ * g₂) / 3
    let debit := (∑ i, h i ^ 2) / 64 + (3 / 2) * h 0 * (h 2 - h 1)
    (r - 1) ^ 6 * quadratic (signedMatrix sign r y) (coordinates h) =
      4 * p ^ 3 * (occupationTaylorCoefficient r d h - debit) -
        (p * (g₀ + g₂) + sign * z) ^ 2 := by
  intro y m n q P₀ P₂ p g₀ g₂ z debit
  obtain ⟨hP₀, hP₂, _⟩ := cut_scaling hr y
  obtain ⟨hg₀, hg₂⟩ := tilt_scaling hr hd h hh
  change P₀ = _ at hP₀
  change P₂ = _ at hP₂
  change g₀ = (r - 1) * dotProduct (lowerTilt r y) (coordinates h) at hg₀
  change g₂ = (r - 1) * dotProduct (upperTilt r y) (coordinates h) at hg₂
  have hp : p = (r - 1) ^ 2 * weightSum r y := by
    change P₀ + P₂ = _
    rw [hP₀, hP₂, weightSum]
    ring
  change _ = 4 * p ^ 3 * (occupationTaylorCoefficient r d h -
    ((∑ i, h i ^ 2) / 64 + (3 / 2) * h 0 * (h 2 - h 1))) -
    (p * (g₀ + g₂) + sign * ((P₂ * g₀ - P₀ * g₂) / 3)) ^ 2
  rw [signedMatrix_quadratic, ← occupationTaylorCoefficient_eq_quadratic
    (zero_lt_one.trans hr) d h hh, debit_quadratic h hh, signedRow_dot,
    hp, hP₀, hP₂, hg₀, hg₂]
  ring

/-- The divided residual used in the scalar long-crossing pair. -/
def residual (r : ℝ) (y : Vec3) : ℝ :=
  let t := r - 1
  2 * (upperWeight r y * lowerTiltFactor r y * (r * (y 0 / t) - y 2 / t) -
    lowerWeight r y * upperTiltFactor r y * (y 1 / t))

def longTest (sign r : ℝ) (y : Vec3) : ℝ :=
  longCrossing r y * weightSum r y + sign * (4 * residual r y)

private theorem long_tests_imply {r d : ℝ} (hr : 1 < r) (hd : 0 ≤ d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    let y := displacement d h
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let P₀ := matchedLower r m n q
    let P₂ := matchedUpper r m n q
    let G₀ := cutBias r m n q 0 / 2 - 2 * P₀
    let G₂ := cutBias r m n q 2 / 2 - 2 * P₂
    let R := G₀ - G₂ - (P₀ - P₂) / (P₀ + P₂) * (G₀ + G₂)
    0 < P₀ → 0 < P₂ → 0 < longTest (-1) r y → 0 < longTest 1 r y →
      4 * |R| < 4 * (longCoeff r m n q / 4) := by
  intro y m n q P₀ P₂ G₀ G₂ R hP₀ hP₂ hminus hplus
  have ht : 0 < r - 1 := sub_pos.mpr hr
  have hp := add_pos hP₀ hP₂
  obtain ⟨h₀, h₂, hlong⟩ := cut_scaling hr y
  change P₀ = _ at h₀
  change P₂ = _ at h₂
  change longCoeff r m n q = _ at hlong
  have hpScale : P₀ + P₂ = (r - 1) ^ 2 * weightSum r y := by
    rw [h₀, h₂, weightSum]
    ring
  obtain ⟨hG₀, hG₂⟩ := gibbs_endpoint_linear_costs_eq (zero_lt_one.trans hr) d h hh
  change G₀ = _ at hG₀
  change G₂ = _ at hG₂
  obtain ⟨hg₀, hg₂⟩ := tilt_scaling hr hd h hh
  change g0scaled r d h = (r - 1) * dotProduct (lowerTilt r y) (coordinates h) at hg₀
  change g2scaled r d h = (r - 1) * dotProduct (upperTilt r y) (coordinates h) at hg₂
  have hy₀ : y 0 = d * h 0 := rfl
  have hy₁ : y 1 = d * h 1 := rfl
  have hy₂ : y 2 = d * h 2 := rfl
  have hres : (r - 1) * residual r y =
      2 * d * (upperWeight r y * dotProduct (lowerTilt r y) (coordinates h) -
        lowerWeight r y * dotProduct (upperTilt r y) (coordinates h)) := by
    rw [residual, hy₀, hy₁, hy₂, lowerTilt_dot, upperTilt_dot]
    field_simp [ht.ne'] <;> ring
  have hprod : (P₀ + P₂) * R = (r - 1) ^ 4 * residual r y := calc
    _ = 2 * (P₂ * G₀ - P₀ * G₂) := by
      change (P₀ + P₂) * (G₀ - G₂ - (P₀ - P₂) / (P₀ + P₂) * (G₀ + G₂)) = _
      field_simp [hp.ne'] <;> ring
    _ = (r - 1) ^ 3 * ((r - 1) * residual r y) := by
      rw [h₀, h₂, hG₀, hG₂, hg₀, hg₂, hres]
      ring
    _ = _ := by ring
  have htest : 4 * |residual r y| < longCrossing r y * weightSum r y := by
    simp only [longTest, neg_one_mul, one_mul] at hminus hplus
    rcases le_total 0 (residual r y) with hres₀ | hres₀
    · rw [abs_of_nonneg hres₀]
      linarith only [hminus]
    · rw [abs_of_nonpos hres₀]
      linarith only [hplus]
  have hscaled : 4 * |(P₀ + P₂) * R| < (P₀ + P₂) * longCoeff r m n q := calc
    _ = (r - 1) ^ 4 * (4 * |residual r y|) := by
      rw [hprod, abs_mul, abs_of_nonneg (pow_nonneg ht.le 4)]
      ring
    _ < (r - 1) ^ 4 * (longCrossing r y * weightSum r y) :=
      mul_lt_mul_of_pos_left htest (pow_pos ht 4)
    _ = _ := by rw [hpScale, hlong]; ring
  rw [abs_mul, abs_of_pos hp] at hscaled
  have hcancel : (P₀ + P₂) * (4 * |R|) < (P₀ + P₂) * longCoeff r m n q := calc
    _ = 4 * ((P₀ + P₂) * |R|) := by ring
    _ < _ := hscaled
  rw [show 4 * (longCoeff r m n q / 4) = longCoeff r m n q by ring]
  exact lt_of_mul_lt_mul_left hcancel hp.le

/-- Consume the two positive semidefinite matrices and the scalar
long-crossing pair in the physical normalized-deficit theorem. -/
theorem normalized_deficit_ge_of_matrix_tests {r d : ℝ} (U : unitary Mat)
    (hr : 1 < r) (hd : 0 ≤ d) (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (h₀ : 0 ≤ h 0) (h₁₂ : h 1 ≤ h 2)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let y := displacement d h
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let L₀ := matchedMixture (cutEnergy r m n q) (cutBias r m n q)
    let P₀ := matchedLower r m n q
    let P₂ := matchedUpper r m n q
    m ≤ n → n ≤ q → q ≤ 1 →
    0 ≤ L₀ → L₀ ≤ lowerCoeff r m n q → L₀ ≤ upperCoeff r n q →
    0 < P₀ → 0 < P₂ → 0 ≤ P₀ * P₂ / (P₀ + P₂) - L₀ / 4 →
    0 < longTest (-1) r y → 0 < longTest 1 r y →
    (signedMatrix (-1) r y).PosSemidef → (signedMatrix 1 r y).PosSemidef →
    (d ^ 2 / 64) * (∑ i, h i ^ 2) ≤ normalizedDeficit r U m n q := by
  intro y m n q L₀ P₀ P₂ hmn hnq hq1 hL₀ hleft hright hP₀ hP₂ hj hlminus hlplus hmminus hmplus
  have hsign (sign : ℝ) (hm : (signedMatrix sign r y).PosSemidef) :
      ((P₀ + P₂) * (g0scaled r d h + g2scaled r d h) +
        sign * ((P₂ * g0scaled r d h - P₀ * g2scaled r d h) / 3)) ^ 2 ≤
      4 * (P₀ + P₂) ^ 3 * (occupationTaylorCoefficient r d h -
        ((∑ i, h i ^ 2) / 64 + (3 / 2) * h 0 * (h 2 - h 1))) := by
    have hq : 0 ≤ quadratic (signedMatrix sign r y) (coordinates h) := by
      simpa only [quadratic, star_trivial] using hm.dotProduct_mulVec_nonneg (coordinates h)
    have hform := mul_nonneg (pow_nonneg (sub_nonneg.mpr hr.le) 6) hq
    have heq := signedMatrix_quadratic_eq sign hr hd h hh
    change (r - 1) ^ 6 * quadratic (signedMatrix sign r y) (coordinates h) = _ at heq
    rw [heq] at hform
    exact sub_nonneg.mp hform
  have hlong := long_tests_imply hr hd h hh hP₀ hP₂ hlminus hlplus
  refine normalized_deficit_ge_of_signed_forms U hr.le hd h hh h₀ h₁₂ hx hg
    hmn hnq hq1 hL₀ hleft hright hP₀ hP₂ hj hlong ?_ ?_
  · change ((P₀ + P₂) * (g0scaled r d h + g2scaled r d h) -
        (P₂ * g0scaled r d h - P₀ * g2scaled r d h) / 3) ^ 2 ≤
      4 * (P₀ + P₂) ^ 3 * (occupationTaylorCoefficient r d h -
        ((∑ i, h i ^ 2) / 64 + (3 / 2) * h 0 * (h 2 - h 1)))
    simpa only [neg_one_mul, sub_eq_add_neg] using hsign (-1) hmminus
  · change ((P₀ + P₂) * (g0scaled r d h + g2scaled r d h) +
        (P₂ * g0scaled r d h - P₀ * g2scaled r d h) / 3) ^ 2 ≤
      4 * (P₀ + P₂) ^ 3 * (occupationTaylorCoefficient r d h -
        ((∑ i, h i ^ 2) / 64 + (3 / 2) * h 0 * (h 2 - h 1)))
    simpa only [one_mul] using hsign 1 hmplus

#print axioms occupationTaylorCoefficient_eq_quadratic
#print axioms signedMatrix_quadratic_eq
#print axioms normalized_deficit_ge_of_matrix_tests

end D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
