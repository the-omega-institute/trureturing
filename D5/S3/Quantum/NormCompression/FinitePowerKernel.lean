/- GID: D5/S3/Quantum/NormCompression/FinitePowerKernel
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Exact actual Hessian radial kernel on every coupled rank two support face. -/

import D5.S3.Quantum.NormCompression.FinitePowerConcavity
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace D5.S3.Quantum.NormCompression.FinitePowerConcavity
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : Type*} [Fintype m] [DecidableEq m]
open private root_power_cancel hessian_column_coefficients sym2 spectralTrace spectralTrace_hasDerivAt sym2_posDef_low_eigenvalue_pos gramDiagonal gramOffDiagonal power_root_sq rowGram_sym2 gramDiagonalVelocity gramOffDiagonalVelocity spectralVelocity spectralVelocity_hasDerivAt from
  D5.S3.Quantum.NormCompression.FinitePowerSpectral
open private diagonal_kernel_scalar whitened_gram_moments inverse_metric_from_moments spectralAcceleration gramDiagonalAcceleration gramOffDiagonalAcceleration spectralAcceleration_decomposition from
  D5.S3.Quantum.NormCompression.FinitePowerMetric
open private local_quadratic_duality_support local_quadratic_radial_support positive_gram_rotation normalized_diagonal_jets normalized_offDiagonal_jets rotated_velocity_moments positive_half_power_sq from
  D5.S3.Quantum.NormCompression.FinitePowerConcavity

/- Exact fixed-support affine derivatives; zero entries are constant along
   allowed tangents, so no derivative of a nonconstant root at zero is used. -/
private theorem affine_rpow_hasDerivAt_support (w v t r : ℝ)
    (hface : w + t * v = 0 → v = 0) :
    HasDerivAt (fun u : ℝ => (w + u * v) ^ r)
      (v * r * (w + t * v) ^ (r - 1)) t := by
  by_cases hz : w + t * v = 0
  · have hv := hface hz
    have hw : w = 0 := by simpa only [hv, mul_zero, add_zero] using hz
    simpa only [hw, hv, mul_zero, add_zero, zero_mul] using
      (hasDerivAt_const t ((0 : ℝ) ^ r))
  · have hd : HasDerivAt (fun u : ℝ => w + u * v) v t := by
      simpa only [Pi.add_apply, id_eq, one_mul, zero_add] using
        ((hasDerivAt_id t).mul_const v).const_add w
    exact hd.rpow_const (Or.inl hz)

private theorem product_rpow_hasDerivAt_support (w₀ w₁ v₀ v₁ t r : ℝ)
    (hface₀ : w₀ + t * v₀ = 0 → v₀ = 0)
    (hface₁ : w₁ + t * v₁ = 0 → v₁ = 0) :
    HasDerivAt (fun u : ℝ => ((w₀ + u * v₀) * (w₁ + u * v₁)) ^ r)
      ((v₀ * (w₁ + t * v₁) + (w₀ + t * v₀) * v₁) * r *
        ((w₀ + t * v₀) * (w₁ + t * v₁)) ^ (r - 1)) t := by
  by_cases hz : (w₀ + t * v₀) * (w₁ + t * v₁) = 0
  · rcases mul_eq_zero.mp hz with h₀ | h₁
    · have hv := hface₀ h₀
      have hw : w₀ = 0 := by simpa only [hv, mul_zero, add_zero] using h₀
      simpa only [hw, hv, mul_zero, zero_mul, zero_add, add_zero] using
        (hasDerivAt_const t ((0 : ℝ) ^ r))
    · have hv := hface₁ h₁
      have hw : w₁ = 0 := by simpa only [hv, mul_zero, add_zero] using h₁
      simpa only [hw, hv, mul_zero, zero_mul, zero_add, add_zero] using
        (hasDerivAt_const t ((0 : ℝ) ^ r))
  · have hd₀ : HasDerivAt (fun u : ℝ => w₀ + u * v₀) v₀ t := by
      simpa only [Pi.add_apply, id_eq, one_mul, zero_add] using
        ((hasDerivAt_id t).mul_const v₀).const_add w₀
    have hd₁ : HasDerivAt (fun u : ℝ => w₁ + u * v₁) v₁ t := by
      simpa only [Pi.add_apply, id_eq, one_mul, zero_add] using
        ((hasDerivAt_id t).mul_const v₁).const_add w₁
    exact (hd₀.mul hd₁).rpow_const (Or.inl hz)

private theorem affine_support_eventually {t : ℝ} (W V : Matrix (Fin 2) m ℝ)
    (hW : ∀ b j, 0 ≤ (W + t • V) b j)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0) :
    ∀ᶠ u : ℝ in nhds t, ∀ b j,
      0 ≤ (W + u • V) b j ∧ ((W + u • V) b j = 0 → V b j = 0) := by
  apply Filter.eventually_all.mpr
  intro b
  apply Filter.eventually_all.mpr
  intro j
  by_cases hz : (W + t • V) b j = 0
  · have hv := hface b j hz
    have hw : W b j = 0 := by
      change W b j + t * V b j = 0 at hz
      simpa only [hv, mul_zero, add_zero] using hz
    exact Filter.Eventually.of_forall (fun u => by
      change 0 ≤ W b j + u * V b j ∧ (W b j + u * V b j = 0 → V b j = 0)
      simp only [hw, hv, mul_zero, add_zero, le_refl, implies_true, and_self])
  · have hp : 0 < (W + t • V) b j := (hW b j).lt_of_ne' hz
    have hc : Continuous (fun u : ℝ => (W + u • V) b j) := by fun_prop
    filter_upwards [(hc.tendsto t).eventually (Ioi_mem_nhds hp)] with u hu
    exact ⟨hu.le, fun hz => (hu.ne' hz).elim⟩

private theorem gramDiagonal_hasDerivAt_face {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0) (b : Fin 2) :
    HasDerivAt (fun u : ℝ => gramDiagonal q (W + u • V) b)
      (gramDiagonalVelocity q (W + t • V) V b) t := by
  unfold gramDiagonal gramDiagonalVelocity
  apply HasDerivAt.fun_sum
  intro j _
  exact affine_rpow_hasDerivAt_support (W b j) (V b j) t (1 / q) (hface b j)

private theorem gramOffDiagonal_hasDerivAt_face {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0) :
    HasDerivAt (fun u : ℝ => gramOffDiagonal q (W + u • V))
      (gramOffDiagonalVelocity q (W + t • V) V) t := by
  unfold gramOffDiagonal gramOffDiagonalVelocity
  apply HasDerivAt.fun_sum
  intro j _
  exact product_rpow_hasDerivAt_support (W 0 j) (W 1 j) (V 0 j) (V 1 j)
    t (1 / (2 * q)) (hface 0 j) (hface 1 j)

private theorem gramDiagonalVelocity_hasDerivAt_face {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0) (b : Fin 2) :
    HasDerivAt (fun u : ℝ => gramDiagonalVelocity q (W + u • V) V b)
      (gramDiagonalAcceleration q (W + t • V) V b) t := by
  unfold gramDiagonalVelocity gramDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have hd := (affine_rpow_hasDerivAt_support (W b j) (V b j) t
    (1 / q - 1) (hface b j)).const_mul (V b j * (1 / q))
  convert hd using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq,
      show 1 / q - 1 - 1 = 1 / q - 2 by ring] <;> ring

private theorem gramOffDiagonalVelocity_hasDerivAt_face {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0) :
    HasDerivAt (fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V)
      (gramOffDiagonalAcceleration q (W + t • V) V) t := by
  unfold gramOffDiagonalVelocity gramOffDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have h₀ := (hasDerivAt_const t (W 0 j)).add ((hasDerivAt_id t).mul_const (V 0 j))
  have h₁ := (hasDerivAt_const t (W 1 j)).add ((hasDerivAt_id t).mul_const (V 1 j))
  have hlin := ((h₁.const_mul (V 0 j)).add (h₀.mul_const (V 1 j))).mul_const (1 / (2 * q))
  have hpow := product_rpow_hasDerivAt_support (W 0 j) (W 1 j) (V 0 j) (V 1 j)
    t (1 / (2 * q) - 1) (hface 0 j) (hface 1 j)
  convert! hlin.mul hpow using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq,
      show 1 / (2 * q) - 1 - 1 = 1 / (2 * q) - 2 by ring] <;>
    first | rfl | (funext u; simp only [Pi.mul_apply, Pi.add_apply]; rfl) | ring


private theorem Fq_affine_hasDerivAt_face {q t : ℝ} (hq : 0 < q)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ (W + t • V) b j)
    (hface : ∀ b j, (W + t • V) b j = 0 → V b j = 0)
    (hdisc : 0 < (gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
      4 * gramOffDiagonal q (W + t • V) ^ 2)
    (hlo : 0 < (gramDiagonal q (W + t • V) 0 + gramDiagonal q (W + t • V) 1 -
      Real.sqrt ((gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
        4 * gramOffDiagonal q (W + t • V) ^ 2)) / 2) :
    let a := gramDiagonal q (W + t • V) 0
    let b := gramOffDiagonal q (W + t • V)
    let c := gramDiagonal q (W + t • V) 1
    let da := gramDiagonalVelocity q (W + t • V) V 0
    let db := gramOffDiagonalVelocity q (W + t • V) V
    let dc := gramDiagonalVelocity q (W + t • V) V 1
    let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
    let dδ := (2 * (a - c) * (da - dc) + 8 * b * db) / (2 * δ)
    HasDerivAt (fun u : ℝ => Fq q (W + u • V))
      (((da + dc + dδ) / 2) * q * ((a + c + δ) / 2) ^ (q - 1) +
        ((da + dc - dδ) / 2) * q * ((a + c - δ) / 2) ^ (q - 1)) t := by
  have hpos := affine_support_eventually W V hW hface
  have heq : (fun u : ℝ => Fq q (W + u • V)) =ᶠ[nhds t]
      (fun u => spectralTrace q (gramDiagonal q (W + u • V) 0)
        (gramOffDiagonal q (W + u • V)) (gramDiagonal q (W + u • V) 1)) := by
    filter_upwards [hpos] with u hu
    exact Fq_eq_two_eigenvalue_formula hq _ (fun b j => (hu b j).1)
  exact (spectralTrace_hasDerivAt (gramDiagonal_hasDerivAt_face W V hface 0)
    (gramOffDiagonal_hasDerivAt_face W V hface) (gramDiagonal_hasDerivAt_face W V hface 1)
    hdisc hlo).congr_of_eventuallyEq heq

private theorem Fq_affine_second_hasDerivAt_face {q : ℝ} (hq : 0 < q)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j)
    (hface : ∀ b j, W b j = 0 → V b j = 0)
    (hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2)
    (hlo : 0 < (gramDiagonal q W 0 + gramDiagonal q W 1 -
      Real.sqrt ((gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
        4 * gramOffDiagonal q W ^ 2)) / 2) :
    HasDerivAt (deriv (fun u : ℝ => Fq q (W + u • V)))
      (spectralAcceleration q (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)
        (gramDiagonalVelocity q W V 0) (gramOffDiagonalVelocity q W V)
        (gramDiagonalVelocity q W V 1) (gramDiagonalAcceleration q W V 0)
        (gramOffDiagonalAcceleration q W V) (gramDiagonalAcceleration q W V 1)) 0 := by
  let a := fun u : ℝ => gramDiagonal q (W + u • V) 0
  let b := fun u : ℝ => gramOffDiagonal q (W + u • V)
  let c := fun u : ℝ => gramDiagonal q (W + u • V) 1
  let da := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 0
  let db := fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V
  let dc := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 1
  have hdiag (k : Fin 2) : Continuous (fun u : ℝ => gramDiagonal q (W + u • V) k) := by
    unfold gramDiagonal
    apply continuous_finset_sum
    intro j _
    exact (continuous_const.add (continuous_id.mul_const (V k j))).rpow_const
      (fun _ => Or.inr (by positivity))
  have hb : Continuous b := by
    dsimp only [b, gramOffDiagonal]
    apply continuous_finset_sum
    intro j _
    exact ((continuous_const.add (continuous_id.mul_const (V 0 j))).mul
      (continuous_const.add (continuous_id.mul_const (V 1 j)))).rpow_const
        (fun _ => Or.inr (by positivity))
  have ha : Continuous a := hdiag 0
  have hc : Continuous c := hdiag 1
  have hdiscC : Continuous (fun u : ℝ => (a u - c u) ^ 2 + 4 * b u ^ 2) := by fun_prop
  have hloC : Continuous (fun u : ℝ => (a u + c u -
      Real.sqrt ((a u - c u) ^ 2 + 4 * b u ^ 2)) / 2) := by fun_prop
  have hW₀ : ∀ k j, 0 ≤ (W + (0 : ℝ) • V) k j := by simpa using hW
  have hface₀ : ∀ k j, (W + (0 : ℝ) • V) k j = 0 → V k j = 0 := by
    simpa only [zero_smul, add_zero] using hface
  have hpos := affine_support_eventually W V hW₀ hface₀
  have hdisc' : 0 < (a 0 - c 0) ^ 2 + 4 * b 0 ^ 2 := by simpa [a, b, c] using hdisc
  have hlo' : 0 < (a 0 + c 0 - Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)) / 2 := by
    simpa [a, b, c] using hlo
  have heq : deriv (fun u : ℝ => Fq q (W + u • V)) =ᶠ[nhds 0]
      (fun u => spectralVelocity q (a u) (b u) (c u) (da u) (db u) (dc u)) := by
    filter_upwards [hpos, (hdiscC.tendsto 0).eventually (Ioi_mem_nhds hdisc'),
      (hloC.tendsto 0).eventually (Ioi_mem_nhds hlo')] with u hu hd hl
    exact (Fq_affine_hasDerivAt_face hq W V (fun k j => (hu k j).1)
      (fun k j => (hu k j).2) hd hl).deriv
  have h := spectralVelocity_hasDerivAt (q := q) (gramDiagonal_hasDerivAt_face W V hface₀ 0)
    (gramOffDiagonal_hasDerivAt_face W V hface₀) (gramDiagonal_hasDerivAt_face W V hface₀ 1)
    (gramDiagonalVelocity_hasDerivAt_face W V hface₀ 0)
    (gramOffDiagonalVelocity_hasDerivAt_face W V hface₀)
    (gramDiagonalVelocity_hasDerivAt_face W V hface₀ 1) hdisc' hlo'
  convert h.congr_of_eventuallyEq heq using 1 <;>
    simp only [spectralAcceleration, a, b, c, da, db, dc, zero_smul, add_zero]



/- Strict inverse-metric source fragment for the fixed-support kernel.
   Axial columns have h=0 and require their actual support tangent. -/
private theorem whitened_metric_radial_kernel {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (y₀ y₁ v₀ v₁ h : m → ℝ) (hh : ∀ j, 0 ≤ h j)
    (hn : ∀ j, 0 < y₀ j ^ 2 + y₁ j ^ 2)
    (hface : ∀ j, h j = 0 → y₁ j * v₀ j - y₀ j * v₁ j = 0)
    (hpair : ∀ j k, 0 < y₀ j * y₀ k + y₁ j * y₁ k)
    (h₀ : ∑ j, y₀ j ^ 2 = ξ ^ (s + 1))
    (h₁ : ∑ j, y₁ j ^ 2 = η ^ (s + 1))
    (hcross : ∑ j, y₀ j * y₁ j = 0)
    (hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + h j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1))
    (heq :
      (∑ j, s * (v₀ j ^ 2 + v₁ j ^ 2 +
        (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2 / h j)) =
      s / ξ ^ (s + 1) * (∑ j, y₀ j * v₀ j) ^ 2 +
      s / η ^ (s + 1) * (∑ j, y₁ j * v₁ j) ^ 2 +
      4 * s / (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) *
        ((∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2) ^ 2) :
    ∃ τ : ℝ, ∀ j, v₀ j = τ * y₀ j ∧ v₁ j = τ * y₁ j := by
  let A := ξ ^ (s + 1)
  let B := η ^ (s + 1)
  let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
  let E₀₀ := ∑ j, y₀ j * v₀ j
  let E₁₁ := ∑ j, y₁ j * v₁ j
  let E₀₁ := (∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2
  let N₀₀ := s / A * E₀₀
  let N₁₁ := s / B * E₁₁
  let N₀₁ := 2 * s / D * E₀₁
  let wt := fun j => y₀ j ^ 2 + y₁ j ^ 2 + h j
  let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
  let dual := fun j => (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / wt j)
  let pair := fun j => (N₀₀ * y₀ j + N₀₁ * y₁ j) * v₀ j +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) * v₁ j
  let cost := fun j => s * (v₀ j ^ 2 + v₁ j ^ 2 +
    (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2 / h j)
  let M := s / A * E₀₀ ^ 2 + s / B * E₁₁ ^ 2 + 4 * s / D * E₀₁ ^ 2
  let localGap := fun j => cost j - 2 * pair j + dual j
  have hξ : 0 < ξ := hη.trans hξη
  have hA : 0 < A := Real.rpow_pos_of_pos hξ _
  have hB : 0 < B := Real.rpow_pos_of_pos hη _
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity) (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs))
  have hwt (j : m) : 0 < wt j := add_pos_of_pos_of_nonneg (hn j) (hh j)
  have hmetric : (1 / s) * (A * N₀₀ ^ 2 + B * N₁₁ ^ 2 + D * N₀₁ ^ 2) = M := by
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    field_simp [hs.ne', hA.ne', hB.ne', hD.ne']
    <;> ring
  have hpairSum : ∑ j, pair j = M := by
    have hid : ∑ j, pair j = N₀₀ * E₀₀ + N₁₁ * E₁₁ + 2 * N₀₁ * E₀₁ := by
      dsimp only [pair, E₀₀, E₁₁, E₀₁]
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hid]
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    ring
  have hnum (j : m) : y₁ j * (N₀₀ * y₀ j + N₀₁ * y₁ j) -
      y₀ j * (N₀₁ * y₀ j + N₁₁ * y₁ j) = g j := by dsimp only [g]; ring
  have hscaled (j : m) : s * localGap j =
      (N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 + (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 -
      (g j) ^ 2 / wt j -
      2 * ((N₀₀ * y₀ j + N₀₁ * y₁ j) * (s * v₀ j) +
        (N₀₁ * y₀ j + N₁₁ * y₁ j) * (s * v₁ j)) +
      (s * v₀ j) ^ 2 + (s * v₁ j) ^ 2 +
      (y₁ j * (s * v₀ j) - y₀ j * (s * v₁ j)) ^ 2 / h j := by
    dsimp only [localGap, cost, pair, dual]
    field_simp [hs.ne']
    <;> ring
  have hlocal (j : m) : 0 ≤ localGap j := by
    have hf : h j = 0 → y₁ j * (s * v₀ j) - y₀ j * (s * v₁ j) = 0 := by
      intro hz
      linear_combination s * (hface j hz)
    have hq := local_quadratic_duality_support (hn j) (hh j)
      (N₀₀ * y₀ j + N₀₁ * y₁ j) (N₀₁ * y₀ j + N₁₁ * y₁ j)
      (s * v₀ j) (s * v₁ j) hf
    rw [hnum, ← hscaled] at hq
    exact nonneg_of_mul_nonneg_right hq hs
  have hgap := inverse_metric_from_moments hs hs1 hη hξη y₀ y₁ wt hwt
    h₀ h₁ hcross hwsum N₀₀ N₀₁ N₁₁
  have hgapnonneg : 0 ≤ M - ∑ j, dual j := by
    convert hgap.1 using 1
    exact congrArg (fun r : ℝ => r - ∑ j, dual j) hmetric.symm
  have hsum : 0 ≤ ∑ j, localGap j := Finset.sum_nonneg (fun j _ => hlocal j)
  have hsumid : ∑ j, localGap j = -M + ∑ j, dual j := by
    dsimp only [localGap]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hdouble : (∑ j, 2 * pair j) = 2 * M := by rw [← Finset.mul_sum, hpairSum]
    rw [hdouble]
    change (∑ j, cost j) = M at heq
    rw [heq]
    ring
  have hgapzero : M - ∑ j, dual j = 0 := by rw [hsumid] at hsum; linarith
  have hsumzero : ∑ j, localGap j = 0 := by rw [hsumid]; linarith
  have hG : (1 / s) * (ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + D * N₀₁ ^ 2) -
      ∑ j, dual j = 0 := by rw [hmetric]; exact hgapzero
  obtain ⟨hN, hg⟩ := hgap.2 hG
  have hdiag : N₀₀ = N₁₁ := by
    apply diagonal_kernel_scalar y₀ y₁ hA hB h₀ h₁ hpair
    intro j
    have h := hg j
    simpa only [hN, zero_mul, add_zero] using h
  refine ⟨N₀₀ / s, ?_⟩
  intro j
  have hj : localGap j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hlocal j)).mp hsumzero j (Finset.mem_univ j)
  have hscale := hscaled j
  simp only [hj, mul_zero, hN, ← hdiag,
    zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, zero_mul, add_zero, zero_add] at hscale
  have hgzero : g j = 0 := hg j
  rw [hgzero] at hscale
  have hperp : y₁ j * (N₀₀ * y₀ j) - y₀ j * (N₀₀ * y₁ j) = 0 := by ring
  have hrad := local_quadratic_radial_support (y₀ := y₀ j) (y₁ := y₁ j)
    (h := h j) (τ := N₀₀) (r₀ := s * v₀ j) (r₁ := s * v₁ j) (hh j) (by simpa only [hperp, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using hscale.symm)
  constructor
  · calc
      v₀ j = (N₀₀ * y₀ j) / s := (eq_div_iff hs.ne').mpr (by rw [mul_comm]; exact hrad.1)
      _ = (N₀₀ / s) * y₀ j := by ring
  · calc
      v₁ j = (N₀₀ * y₁ j) / s := (eq_div_iff hs.ne').mpr (by rw [mul_comm]; exact hrad.2)
      _ = (N₀₀ / s) * y₁ j := by ring


/- Strict fixed-support metric assembly, including axial nonzero columns. -/
private theorem rotated_hessian_kernel_support {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (a b z w : m → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hnonzero : ∀ j, 0 < a j + b j)
    (hza : ∀ j, a j = 0 → z j = 0) (hwb : ∀ j, b j = 0 → w j = 0)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ^ 2 + v ^ 2 = 1)
    (h₀ : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (h₁ : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hc : ∑ j, a j * b j = (ξ - η) * u * v)
    (heq :
      (∑ j, (s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * ((ξ ^ s - η ^ s) * u * v) * z j * w j +
        (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * ((ξ ^ s - η ^ s) * u * v) / (2 * a j * b j) *
          (b j * z j - a j * w j) ^ 2)) =
      s * ξ ^ (s - 1) *
        (u ^ 2 * (∑ j, a j * z j) + u * v * (∑ j, (a j * w j + b j * z j)) +
          v ^ 2 * (∑ j, b j * w j)) ^ 2 +
      s * η ^ (s - 1) *
        (v ^ 2 * (∑ j, a j * z j) - u * v * (∑ j, (a j * w j + b j * z j)) +
          u ^ 2 * (∑ j, b j * w j)) ^ 2 +
      2 * ((ξ ^ s - η ^ s) / (ξ - η)) *
        (-u * v * (∑ j, a j * z j) + (u ^ 2 - v ^ 2) *
          ((∑ j, (a j * w j + b j * z j)) / 2) + u * v * (∑ j, b j * w j)) ^ 2) :
    ∃ τ : ℝ, ∀ j, z j = τ * a j ∧ w j = τ * b j := by
  let r := ξ ^ (s / 2)
  let t := η ^ (s / 2)
  let L := (ξ ^ s - η ^ s) * u * v
  let h := fun j => 2 * s * (r * t) ^ 2 / ((2 * s + 1) * L) * (a j * b j)
  let y₀ := fun j => r * (u * a j + v * b j)
  let y₁ := fun j => t * (-v * a j + u * b j)
  let z₀ := fun j => r * (u * z j + v * w j)
  let z₁ := fun j => t * (-v * z j + u * w j)
  have hξ : 0 < ξ := hη.trans hξη
  have hr : 0 < r := Real.rpow_pos_of_pos hξ _
  have ht : 0 < t := Real.rpow_pos_of_pos hη _
  have hr₂ : r ^ 2 = ξ ^ s := positive_half_power_sq ξ hξ s
  have ht₂ : t ^ 2 = η ^ s := positive_half_power_sq η hη s
  have hrt : (r * t) ^ 2 = (ξ * η) ^ s := by
    rw [mul_pow, hr₂, ht₂, Real.mul_rpow hξ.le hη.le]
  have hL : 0 < L :=
    mul_pos (mul_pos (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)) hu) hv
  have hden : 0 < (2 * s + 1) * L := by positivity
  have hh (j : m) : 0 ≤ h j := by
    dsimp only [h]
    exact mul_nonneg (div_nonneg (by positivity) hden.le) (mul_nonneg (ha j) (hb j))
  have hy (j : m) : 0 < y₀ j ^ 2 + y₁ j ^ 2 := by
    have hp : 0 < u * a j + v * b j := by
      rcases lt_or_eq_of_le (ha j) with haj | haj
      · exact add_pos_of_pos_of_nonneg (mul_pos hu haj) (mul_nonneg hv.le (hb j))
      · have hbj : 0 < b j := by have := hnonzero j; linarith
        exact add_pos_of_nonneg_of_pos (mul_nonneg hu.le (ha j)) (mul_pos hv hbj)
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (mul_pos hr hp)) (sq_nonneg _)
  have hcross (j : m) : y₁ j * z₀ j - y₀ j * z₁ j = r * t * (b j * z j - a j * w j) := by
    dsimp only [y₀, y₁, z₀, z₁]
    calc
      _ = r * t * (u ^ 2 + v ^ 2) * (b j * z j - a j * w j) := by ring
      _ = _ := by rw [huv]; ring
  have hface (j : m) (hj : h j = 0) : y₁ j * z₀ j - y₀ j * z₁ j = 0 := by
    rw [hcross]
    by_cases haj : a j = 0
    · rw [haj, hza j haj]; ring
    by_cases hbj : b j = 0
    · rw [hbj, hwb j hbj]; ring
    have hp : 0 < h j := by
      have haj' := (ha j).lt_of_ne' haj
      have hbj' := (hb j).lt_of_ne' hbj
      dsimp only [h]
      positivity
    exact (hp.ne' hj).elim
  obtain ⟨hy₀, hy₁, hyc⟩ := whitened_gram_moments a b u v hξ hη s huv h₀ h₁ hc
  have hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + h j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1) := by
    dsimp only [h]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hy₀, hy₁, ← Finset.mul_sum, hc, hrt]
    dsimp only [L]
    field_simp [hu.ne', hv.ne', (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne']
    <;> ring
  have hpair (j k : m) : 0 < y₀ j * y₀ k + y₁ j * y₁ k := by
    have hid : y₀ j * y₀ k + y₁ j * y₁ k =
        (ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * a j * a k +
        L * (a j * b k + b j * a k) +
        (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * b j * b k := by
      dsimp only [y₀, y₁, L]
      linear_combination (u * a j + v * b j) * (u * a k + v * b k) * hr₂ +
        (-v * a j + u * b j) * (-v * a k + u * b k) * ht₂
    rw [hid]
    have hS₀ : 0 < ξ ^ s * u ^ 2 + η ^ s * v ^ 2 := by positivity
    have hS₁ : 0 < ξ ^ s * v ^ 2 + η ^ s * u ^ 2 := by positivity
    have haj := ha j; have hbj := hb j; have hak := ha k; have hbk := hb k
    have hj : 0 < a j ∨ 0 < b j := by have := hnonzero j; rcases lt_or_eq_of_le haj with h | h; exact Or.inl h; exact Or.inr (by linarith)
    have hk : 0 < a k ∨ 0 < b k := by have := hnonzero k; rcases lt_or_eq_of_le hak with h | h; exact Or.inl h; exact Or.inr (by linarith)
    rcases hj with hj | hj <;> rcases hk with hk | hk <;> positivity
  have hcost (j : m) : s * (z₀ j ^ 2 + z₁ j ^ 2 +
      (y₁ j * z₀ j - y₀ j * z₁ j) ^ 2 / h j) =
      s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * L * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2 := by
    rw [hcross]
    have hnorm : z₀ j ^ 2 + z₁ j ^ 2 =
        (ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * L * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2 := by
      dsimp only [z₀, z₁, L]
      linear_combination (u * z j + v * w j) ^ 2 * hr₂ + (-v * z j + u * w j) ^ 2 * ht₂
    rw [hnorm]
    by_cases haj : a j = 0
    · simp only [h, haj, hza j haj, mul_zero, zero_mul, zero_sub, sub_zero, zero_div, div_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    by_cases hbj : b j = 0
    · simp only [h, hbj, hwb j hbj, mul_zero, zero_mul, zero_sub, sub_zero, zero_div, div_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    dsimp only [h]
    field_simp [hs.ne', hr.ne', ht.ne', haj, hbj, hL.ne', show 2 * s + 1 ≠ 0 by positivity]
    <;> ring
  have hmetric :
      s / ξ ^ (s + 1) * (∑ j, y₀ j * z₀ j) ^ 2 +
      s / η ^ (s + 1) * (∑ j, y₁ j * z₁ j) ^ 2 +
      4 * s / (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) *
        ((∑ j, (y₀ j * z₁ j + y₁ j * z₀ j)) / 2) ^ 2 =
      (∑ j, s * (z₀ j ^ 2 + z₁ j ^ 2 + (y₁ j * z₀ j - y₀ j * z₁ j) ^ 2 / h j)) := by
    rw [Finset.sum_congr rfl (fun j _ => hcost j)]
    obtain ⟨hz₀, hz₁, hzc⟩ := rotated_velocity_moments a b z w u v r t
    dsimp only [y₀, y₁, z₀, z₁]
    rw [hz₀, hz₁, hzc, hr₂, ht₂]
    have hp (x : ℝ) (hx : 0 < x) : x ^ (s + 1) = x ^ s * x := by rw [Real.rpow_add hx, Real.rpow_one]
    have hm (x : ℝ) (hx : 0 < x) : x ^ (s - 1) = x ^ s / x := by rw [Real.rpow_sub hx, Real.rpow_one]
    convert heq.symm using 1
    rw [hp ξ hξ, hp η hη, hm ξ hξ, hm η hη, Real.mul_rpow hξ.le hη.le]
    simp only [mul_pow, div_pow, hr₂, ht₂]
    field_simp [hξ.ne', hη.ne', (Real.rpow_pos_of_pos hξ s).ne', (Real.rpow_pos_of_pos hη s).ne',
      (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne', (sub_pos.mpr hξη).ne', hs.ne']
    <;> ring
  obtain ⟨τ, hτ⟩ := whitened_metric_radial_kernel hs hs1 hη hξη y₀ y₁ z₀ z₁ h hh hy hface hpair hy₀ hy₁ hyc hwsum hmetric.symm
  refine ⟨τ, fun j => ?_⟩
  have hj₀ : u * z j + v * w j = τ * (u * a j + v * b j) := by
    have hj := (hτ j).1
    dsimp only [z₀, y₀] at hj
    exact (mul_left_cancel₀ hr.ne') (by linear_combination hj)
  have hj₁ : -v * z j + u * w j = τ * (-v * a j + u * b j) := by
    have hj := (hτ j).2
    dsimp only [z₁, y₁] at hj
    exact (mul_left_cancel₀ ht.ne') (by linear_combination hj)
  constructor
  · linear_combination u * hj₀ - v * hj₁ - (z j - τ * a j) * huv
  · linear_combination v * hj₀ + u * hj₁ - (w j - τ * b j) * huv


private theorem hessian_column_coefficients_support (s S₀₀ S₁₁ ℓ a b u v : ℝ)
    (hza : a = 0 → u = 0) (hvb : b = 0 → v = 0) :
    -s * S₀₀ * u ^ 2 - s * S₁₁ * v ^ 2 +
        2 * ℓ * (u * v / 2 - (2 * s + 1) / 4 *
          (b / a * u ^ 2 + a / b * v ^ 2)) =
      -(s * (S₀₀ * u ^ 2 + 2 * ℓ * u * v + S₁₁ * v ^ 2) +
        (2 * s + 1) * ℓ / (2 * a * b) * (b * u - a * v) ^ 2) := by
  by_cases ha : a = 0
  · simp only [ha, hza ha, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero,
      zero_div, div_zero, zero_sub, sub_zero, add_zero, zero_add, neg_zero]
    <;> ring
  by_cases hb : b = 0
  · simp only [hb, hvb hb, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero,
      zero_div, div_zero, zero_sub, sub_zero, add_zero, zero_add, neg_zero]
    <;> ring
  exact hessian_column_coefficients s S₀₀ S₁₁ ℓ a b u v ha hb

private theorem spectralAcceleration_zero_radial_support {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (a b z w : m → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hnonzero : ∀ j, 0 < a j + b j)
    (hza : ∀ j, a j = 0 → z j = 0) (hwb : ∀ j, b j = 0 → w j = 0)
    (hoverlap : 0 < ∑ j, a j * b j)
    (hlo : 0 < ((∑ j, a j ^ 2) + (∑ j, b j ^ 2) -
      Real.sqrt (((∑ j, a j ^ 2) - (∑ j, b j ^ 2)) ^ 2 +
        4 * (∑ j, a j * b j) ^ 2)) / 2)
    (hzero : spectralAcceleration (s + 1) (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      (∑ j, a j * z j) ((∑ j, (a j * w j + b j * z j)) / 2) (∑ j, b j * w j)
      (∑ j, -s * z j ^ 2)
      (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
      (∑ j, -s * w j ^ 2) = 0) :
    ∃ τ : ℝ, ∀ j, z j = τ * a j ∧ w j = τ * b j := by
  obtain ⟨u, v, ξ, η, hu, hv, hη, hξη, huv, h₀, h₁, hc⟩ :=
    positive_gram_rotation (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      hoverlap hlo
  let A := ∑ j, a j * z j
  let B := (∑ j, (a j * w j + b j * z j)) / 2
  let C := ∑ j, b j * w j
  let d := u ^ 2 - v ^ 2
  let e := 2 * u * v
  let S₀ := ξ ^ s * u ^ 2 + η ^ s * v ^ 2
  let S₁ := ξ ^ s * v ^ 2 + η ^ s * u ^ 2
  let L := (ξ ^ s - η ^ s) * u * v
  let Q := ∑ j, (s * (S₀ * z j ^ 2 + 2 * L * z j * w j + S₁ * w j ^ 2) +
    (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2)
  let H := s * ξ ^ (s - 1) * (u ^ 2 * A + 2 * u * v * B + v ^ 2 * C) ^ 2 +
    s * η ^ (s - 1) * (v ^ 2 * A - 2 * u * v * B + u ^ 2 * C) ^ 2 +
    2 * ((ξ ^ s - η ^ s) / (ξ - η)) *
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2
  have hsum : (∑ j, a j ^ 2) + (∑ j, b j ^ 2) = ξ + η := by
    rw [h₀, h₁]
    linear_combination (ξ + η) * huv
  have hdiff : (∑ j, a j ^ 2) - (∑ j, b j ^ 2) = (ξ - η) * d := by
    rw [h₀, h₁]; dsimp only [d]; ring
  have hoff : 2 * (∑ j, a j * b j) = (ξ - η) * e := by rw [hc]; dsimp only [e]; ring
  have hunit : d ^ 2 + e ^ 2 = 1 := by
    calc
      _ = (u ^ 2 + v ^ 2) ^ 2 := by dsimp only [d, e]; ring
      _ = 1 := by rw [huv]; norm_num
  have hd₀ : (1 + d) / 2 = u ^ 2 := by dsimp only [d]; linarith
  have hd₁ : (1 - d) / 2 = v ^ 2 := by dsimp only [d]; linarith
  have hE₀ : (A + C + d * (A - C) + 2 * e * B) / 2 =
      u ^ 2 * A + 2 * u * v * B + v ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hE₁ : (A + C - d * (A - C) - 2 * e * B) / 2 =
      v ^ 2 * A - 2 * u * v * B + u ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hK : (e * (A - C) / 2 - d * B) ^ 2 =
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2 := by
    dsimp only [d, e]; ring
  have hcost : S₀ * (∑ j, -s * z j ^ 2) +
      (ξ ^ s - η ^ s) * e *
        (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
          (b j / a j * z j ^ 2 + a j / b j * w j ^ 2))) +
      S₁ * (∑ j, -s * w j ^ 2) = -Q := by
    have he : (ξ ^ s - η ^ s) * e = 2 * L := by dsimp only [e, L]; ring
    rw [he]
    dsimp only [Q]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination hessian_column_coefficients_support s S₀ S₁ L (a j) (b j) (z j) (w j)
      (hza j) (hwb j)
  have heq := spectralAcceleration_decomposition s (∑ j, a j ^ 2) (∑ j, a j * b j)
    (∑ j, b j ^ 2) ξ η d e A B C
    (∑ j, -s * z j ^ 2)
    (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
      (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
    (∑ j, -s * w j ^ 2) hξη hsum hdiff hoff hunit
  dsimp only at heq
  rw [hd₀, hd₁, hE₀, hE₁, hK] at heq
  change _ = (s + 1) * _ + (s + 1) * H at heq
  rw [hcost] at heq
  rw [heq] at hzero
  change (s + 1) * (-Q) + (s + 1) * H = 0 at hzero
  have hequal : Q = H := by
    have hp : s + 1 ≠ 0 := (by linarith : (0 : ℝ) < s + 1).ne'
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (s + 1) * (Q - H) = 0 by linear_combination -hzero)).resolve_left hp
  exact rotated_hessian_kernel_support hs hs1 hη hξη a b z w ha hb hnonzero hza hwb
    u v hu hv huv h₀ h₁ hc (by convert hequal using 1 <;> dsimp only [Q, H, A, B, C, S₀, S₁, L] <;> ring)



private theorem normalized_diagonal_jets_face {q w : ℝ} (hq : 0 < q) (hw : 0 ≤ w) (v : ℝ) (hface : w = 0 → v = 0) :
    v * (1 / q) * w ^ (1 / q - 1) =
      w ^ (1 / (2 * q)) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ∧
    v ^ 2 * (1 / q) * (1 / q - 1) * w ^ (1 / q - 2) =
      -(q - 1) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ^ 2 := by
  by_cases hz : w = 0
  · simp only [hz, hface hz, zero_mul, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero, and_self]
  · exact normalized_diagonal_jets hq (hw.lt_of_ne' hz) v

private theorem normalized_offDiagonal_jets_face {q w₀ w₁ : ℝ}
    (hq : 0 < q) (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (v₀ v₁ : ℝ)
    (hface₀ : w₀ = 0 → v₀ = 0) (hface₁ : w₁ = 0 → v₁ = 0) :
    let a := w₀ ^ (1 / (2 * q))
    let b := w₁ ^ (1 / (2 * q))
    let z₀ := v₀ / (q * a ^ (2 * q - 1))
    let z₁ := v₁ / (q * b ^ (2 * q - 1))
    (v₀ * w₁ + w₀ * v₁) * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) =
      (a * z₁ + b * z₀) / 2 ∧
    2 * v₀ * v₁ * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) +
      (v₀ * w₁ + w₀ * v₁) ^ 2 * (1 / (2 * q)) * (1 / (2 * q) - 1) *
        (w₀ * w₁) ^ (1 / (2 * q) - 2) =
      z₀ * z₁ / 2 - (2 * q - 1) / 4 * (b / a * z₀ ^ 2 + a / b * z₁ ^ 2) := by
  have hr : (1 : ℝ) / (2 * q) ≠ 0 := by positivity
  by_cases hz₀ : w₀ = 0
  · dsimp only
    rw [hz₀, hface₀ hz₀, Real.zero_rpow hr]
    simp
  by_cases hz₁ : w₁ = 0
  · dsimp only
    rw [hz₁, hface₁ hz₁, Real.zero_rpow hr]
    simp
  exact normalized_offDiagonal_jets hq (hw₀.lt_of_ne' hz₀) (hw₁.lt_of_ne' hz₁) v₀ v₁

private theorem Fq_affine_second_zero_radial_nonzero_columns {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j)
    (hface : ∀ b j, W b j = 0 → V b j = 0)
    (hcolumns : ∀ j, 0 < W 0 j + W 1 j)
    (hoverlap : 0 < gramOffDiagonal q W)
    (hR : (Aq q W * (Aq q W)ᴴ).PosDef) :
    deriv (deriv (fun t : ℝ => Fq q (W + t • V))) 0 = 0 →
      ∃ c : ℝ, V = c • W := by
  intro hzero
  have hq : 0 < q := by linarith
  let a := fun j => W 0 j ^ (1 / (2 * q))
  let b := fun j => W 1 j ^ (1 / (2 * q))
  let z := fun j => V 0 j / (q * (a j) ^ (2 * q - 1))
  let w := fun j => V 1 j / (q * (b j) ^ (2 * q - 1))
  have ha (j : m) : 0 ≤ a j := Real.rpow_nonneg (hW 0 j) _
  have hb (j : m) : 0 ≤ b j := Real.rpow_nonneg (hW 1 j) _
  have hd₀ : (∑ j, a j ^ 2) = gramDiagonal q W 0 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 0 j)
  have hd₁ : (∑ j, b j ^ 2) = gramDiagonal q W 1 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 1 j)
  have hc : (∑ j, a j * b j) = gramOffDiagonal q W := by
    unfold gramOffDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact (Real.mul_rpow (hW 0 j) (hW 1 j)).symm
  have hR' : (sym2 (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)).PosDef := by
    rw [← rowGram_sym2 hq W hW]
    exact hR
  have hlo := sym2_posDef_low_eigenvalue_pos _ _ _ hR'
  have hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2 := by positivity
  have hderiv := (Fq_affine_second_hasDerivAt_face hq W V hW hface hdisc hlo).deriv
  rw [hderiv] at hzero
  have hjet₀ (j : m) := normalized_diagonal_jets_face hq (hW 0 j) (V 0 j) (hface 0 j)
  have hjet₁ (j : m) := normalized_diagonal_jets_face hq (hW 1 j) (V 1 j) (hface 1 j)
  have hjet (j : m) := normalized_offDiagonal_jets_face hq (hW 0 j) (hW 1 j) (V 0 j) (V 1 j) (hface 0 j) (hface 1 j)
  have hv₀ : gramDiagonalVelocity q W V 0 = ∑ j, a j * z j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).1)
  have hv₁ : gramDiagonalVelocity q W V 1 = ∑ j, b j * w j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).1)
  have hv : gramOffDiagonalVelocity q W V = (∑ j, (a j * w j + b j * z j)) / 2 := by
    unfold gramOffDiagonalVelocity
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => (hjet j).1)
  have hvv₀ : gramDiagonalAcceleration q W V 0 = ∑ j, -(q - 1) * z j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).2)
  have hvv₁ : gramDiagonalAcceleration q W V 1 = ∑ j, -(q - 1) * w j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).2)
  have hvv : gramOffDiagonalAcceleration q W V =
      ∑ j, (z j * w j / 2 - (2 * (q - 1) + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)) := by
    unfold gramOffDiagonalAcceleration
    apply Finset.sum_congr rfl
    intro j _
    convert (hjet j).2 using 1 <;> dsimp only [a, b, z, w] <;> ring
  rw [hv₀, hv₁, hv, hvv₀, hvv₁, hvv] at hzero
  have hza (j : m) (hj : a j = 0) : z j = 0 := by
    have hw : W 0 j = 0 := by
      by_contra hw
      exact (Real.rpow_pos_of_pos ((hW 0 j).lt_of_ne' hw) _).ne' hj
    dsimp only [z]
    rw [hface 0 j hw, zero_div]
  have hwb (j : m) (hj : b j = 0) : w j = 0 := by
    have hw : W 1 j = 0 := by
      by_contra hw
      exact (Real.rpow_pos_of_pos ((hW 1 j).lt_of_ne' hw) _).ne' hj
    dsimp only [w]
    rw [hface 1 j hw, zero_div]
  have hn (j : m) : 0 < a j + b j := by
    by_cases hz : W 0 j = 0
    · have hp : 0 < W 1 j := by have := hcolumns j; linarith
      exact add_pos_of_nonneg_of_pos (ha j) (Real.rpow_pos_of_pos hp _)
    · exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos ((hW 0 j).lt_of_ne' hz) _) (hb j)
  obtain ⟨τ, hτ⟩ := spectralAcceleration_zero_radial_support (by linarith : 0 < q - 1)
    (by linarith : q - 1 < 1) a b z w ha hb hn hza hwb (by rwa [hc])
    (by rwa [hd₀, hd₁, hc]) (by simpa only [hd₀, hd₁, hc, sub_add_cancel] using hzero)
  refine ⟨q * τ, ?_⟩
  have hentry (b' : Fin 2) (j : m)
      (ht : V b' j / (q * (W b' j ^ (1 / (2 * q))) ^ (2 * q - 1)) =
        τ * W b' j ^ (1 / (2 * q))) : V b' j = (q * τ) * W b' j := by
    by_cases hz : W b' j = 0
    · rw [hz, hface b' j hz]; ring
    have hp := (hW b' j).lt_of_ne' hz
    have hx := (Real.rpow_pos_of_pos hp (1 / (2 * q))).ne'
    rw [root_power_cancel hq hp] at ht
    field_simp [hq.ne', hz, hx] at ht
    calc
      V b' j = q * W b' j * τ := ht
      _ = (q * τ) * W b' j := by ring
  ext b' j
  fin_cases b'
  · exact hentry 0 j (hτ j).1
  · exact hentry 1 j (hτ j).2



private theorem rowGram_restrict_columns {q : ℝ} (hq : 0 < q)
    (p : m → Prop) [DecidablePred p] (W : Matrix (Fin 2) m ℝ)
    (hzero : ∀ b j, ¬p j → W b j = 0) :
    Aq q (fun b (j : {j // p j}) => W b j) *
        (Aq q (fun b (j : {j // p j}) => W b j))ᴴ = Aq q W * (Aq q W)ᴴ := by
  ext b c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hz (j : m) (hj : ¬p j) : Aq q W b j * star (Aq q W c j) = 0 := by
    simp only [Aq, hzero b j hj, Real.zero_rpow (by positivity : (1 : ℝ) / (2 * q) ≠ 0), Complex.ofReal_zero, zero_mul]
  have hsum : (∑ j : {j // ¬p j}, Aq q W b j * star (Aq q W c j)) = 0 :=
    Finset.sum_eq_zero (fun j _ => hz j j.property)
  have h := Fintype.sum_subtype_add_sum_subtype p (fun j => Aq q W b j * star (Aq q W c j))
  rw [hsum, add_zero] at h
  exact h

private theorem Fq_restrict_columns {q : ℝ} (hq : 0 < q)
    (p : m → Prop) [DecidablePred p] (W : Matrix (Fin 2) m ℝ)
    (hzero : ∀ b j, ¬p j → W b j = 0) :
    Fq q (fun b (j : {j // p j}) => W b j) = Fq q W := by
  rw [Fq_eq_trace_rpow hq, Fq_eq_trace_rpow hq, rowGram_restrict_columns hq p W hzero]

/-- Exact fixed-support Hessian kernel at rank-two tables with positive row
coupling. Zero columns and axial columns are retained through their actual
support tangents. No radial assertion is made for purely axial tables. -/
theorem radial_hessian_kernel {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j)
    (hface : ∀ b j, W b j = 0 → V b j = 0)
    (hoverlap : ∃ j, 0 < W 0 j ∧ 0 < W 1 j)
    (hR : (Aq q W * (Aq q W)ᴴ).PosDef) :
    deriv (deriv (fun t : ℝ => Fq q (W + t • V))) 0 = 0 ↔
      ∃ c : ℝ, V = c • W := by
  have hq : 0 < q := by linarith
  constructor
  · intro hzero
    let p := fun j : m => 0 < W 0 j + W 1 j
    let W' : Matrix (Fin 2) {j // p j} ℝ := fun b j => W b j
    let V' : Matrix (Fin 2) {j // p j} ℝ := fun b j => V b j
    have hz (b : Fin 2) (j : m) (hj : ¬p j) : W b j = 0 := by
      have hj' : W 0 j + W 1 j ≤ 0 := le_of_not_gt hj
      have h₀ := hW 0 j
      have h₁ := hW 1 j
      have hz₀ : W 0 j = 0 := le_antisymm (by linarith only [hj', h₁]) h₀
      have hz₁ : W 1 j = 0 := le_antisymm (by linarith only [hj', h₀]) h₁
      fin_cases b
      · exact hz₀
      · exact hz₁
    have hWP : ∀ b j, 0 ≤ W' b j := fun b j => hW b j
    have hVP : ∀ b j, W' b j = 0 → V' b j = 0 := fun b j => hface b j
    have hcols : ∀ j, 0 < W' 0 j + W' 1 j := fun j => j.property
    have hgram := rowGram_restrict_columns hq p W hz
    have hRP : (Aq q W' * (Aq q W')ᴴ).PosDef := by
      change (Aq q (fun b (j : {j // p j}) => W b j) *
        (Aq q (fun b (j : {j // p j}) => W b j))ᴴ).PosDef
      rw [hgram]
      exact hR
    have hOP : 0 < gramOffDiagonal q W' := by
      obtain ⟨j, hj₀, hj₁⟩ := hoverlap
      let k : {j // p j} := ⟨j, add_pos hj₀ hj₁⟩
      unfold gramOffDiagonal
      apply Finset.sum_pos'
      · intro i _
        exact Real.rpow_nonneg (mul_nonneg (hW 0 i) (hW 1 i)) _
      · exact ⟨k, Finset.mem_univ _, Real.rpow_pos_of_pos (mul_pos hj₀ hj₁) _⟩
    have hfun : (fun t : ℝ => Fq q (W' + t • V')) =
        (fun t : ℝ => Fq q (W + t • V)) := by
      funext t
      exact Fq_restrict_columns hq p (W + t • V) (fun b j hj => by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hz b j hj,
          hface b j (hz b j hj), mul_zero, add_zero])
    have hP : deriv (deriv (fun t : ℝ => Fq q (W' + t • V'))) 0 = 0 := by rw [hfun]; exact hzero
    obtain ⟨c, hc⟩ := Fq_affine_second_zero_radial_nonzero_columns hq1 hq2 W' V' hWP hVP hcols hOP hRP hP
    refine ⟨c, ?_⟩
    ext b j
    by_cases hj : p j
    · exact congrFun (congrFun hc b) ⟨j, hj⟩
    · simp only [Matrix.smul_apply, smul_eq_mul, hz b j hj, hface b j (hz b j hj), mul_zero]
  · rintro ⟨c, rfl⟩
    have heq : (fun t : ℝ => Fq q (W + t • (c • W))) =
        (fun t : ℝ => Fq q ((1 + t * c) • W)) := by
      funext t
      congr 1
      module
    rw [heq]
    exact radial_second_derivative_zero hq c W hW

#print axioms radial_hessian_kernel

end D5.S3.Quantum.NormCompression.FinitePowerConcavity
