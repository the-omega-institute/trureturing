/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/PositiveGramSupport
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed support inequality gives positive three-spectrum Gram allocations. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGramFiniteSums
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Separation

/-! The sharp support inequality gives all three PSD allocations for the
four-copy Gram reduction. -/

noncomputable section

open Metric Set Matrix
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Pointwise

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

section Separation

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

-- The pointwise support proof from EllipsoidShape, where it is private.
private theorem support_maximum (L : E →L[ℝ] H) (y : H) :
    ∃ u ∈ closedBall (0 : E) 1, ⟪y, L u⟫_ℝ = ‖L.adjoint y‖ := by
  by_cases hz : L.adjoint y = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hz]
  have hn := norm_pos_iff.mpr hz
  refine ⟨‖L.adjoint y‖⁻¹ • L.adjoint y, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    simp [norm_smul, hz]
  · rw [← L.adjoint_inner_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- A point bounded in every direction by the sum of the three supports is
a sum of three images of vectors in the Euclidean unit balls. -/
theorem exists_three_ball_witnesses_of_support
    (L01 L02 L12 : E →L[ℝ] H) (target : H)
    (hs : ∀ y : H,
      ⟪y, target⟫_ℝ ≤ ‖L01.adjoint y‖ + ‖L02.adjoint y‖ + ‖L12.adjoint y‖) :
    ∃ u01 u02 u12 : E,
      u01 ∈ closedBall (0 : E) 1 ∧
      u02 ∈ closedBall (0 : E) 1 ∧
      u12 ∈ closedBall (0 : E) 1 ∧
      L01 u01 + L02 u02 + L12 u12 = target := by
  let I (L : E →L[ℝ] H) : Set H := L '' closedBall (0 : E) 1
  have hc (L : E →L[ℝ] H) : Convex ℝ (I L) :=
    (convex_closedBall (0 : E) (1 : ℝ)).linear_image L.toLinearMap
  have hk (L : E →L[ℝ] H) : IsCompact (I L) :=
    (isCompact_closedBall (0 : E) 1).image L.continuous
  have hmem : target ∈ I L01 + I L02 + I L12 := by
    by_contra hnot
    obtain ⟨φ, r, hφ, htarget⟩ := geometric_hahn_banach_closed_point
      (((hc L01).add (hc L02)).add (hc L12))
      (((hk L01).add (hk L02)).add (hk L12)).isClosed hnot
    let y := (InnerProductSpace.toDual ℝ H).symm φ
    have hy (v : H) : ⟪y, v⟫_ℝ = φ v := InnerProductSpace.toDual_symm_apply
    obtain ⟨u01, hu01, h01⟩ := support_maximum L01 y
    obtain ⟨u02, hu02, h02⟩ := support_maximum L02 y
    obtain ⟨u12, hu12, h12⟩ := support_maximum L12 y
    have hsum : L01 u01 + L02 u02 + L12 u12 ∈ I L01 + I L02 + I L12 :=
      Set.add_mem_add
        (Set.add_mem_add (show L01 u01 ∈ I L01 from ⟨u01, hu01, rfl⟩)
          (show L02 u02 ∈ I L02 from ⟨u02, hu02, rfl⟩))
        (show L12 u12 ∈ I L12 from ⟨u12, hu12, rfl⟩)
    have hmax : ⟪y, L01 u01 + L02 u02 + L12 u12⟫_ℝ =
        ‖L01.adjoint y‖ + ‖L02.adjoint y‖ + ‖L12.adjoint y‖ := by
      simp only [inner_add_right, h01, h02, h12]
    have hle := hs y
    rw [← hmax, hy target, hy (L01 u01 + L02 u02 + L12 u12)] at hle
    exact hle.not_gt ((hφ _ hsum).trans htarget)
  obtain ⟨v, hv, v12, ⟨u12, hu12, rfl⟩, htotal⟩ := Set.mem_add.mp hmem
  obtain ⟨v01, ⟨u01, hu01, rfl⟩, v02, ⟨u02, hu02, rfl⟩, rfl⟩ := Set.mem_add.mp hv
  exact ⟨u01, u02, u12, hu01, hu02, hu12, htotal⟩

end Separation

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₃" => EuclideanSpace ℝ (Fin 3)

/-- The three prescribed row sums of the allocation. -/
def rowTarget (d : Kernel) : V₃ :=
  WithLp.toLp 2 ![h d 0 1 2, h d 1 0 2, h d 2 0 1]

/-- The quadratic form of the top block scaled by the complementary
diagonal coefficient, embedded on coordinates i and j. -/
def edgeQuadratic (d : Kernel) (i j k : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  h d k i j * (f d i j * (y i)^2 + g d i j * y i * y j + f d j i * (y j)^2)

/-- The support inequality in every signed direction, in the normalization
of the shared four-slot kernel. -/
def SharpSupport (d : Kernel) : Prop :=
  ∀ y : Fin 3 → ℝ, h d 0 1 2 * y 0 + h d 1 0 2 * y 1 + h d 2 0 1 * y 2 ≤
    Real.sqrt (edgeQuadratic d 0 1 2 y) + Real.sqrt (edgeQuadratic d 0 2 1 y) +
      Real.sqrt (edgeQuadratic d 1 2 0 y)

/-- A certificate with a positive common denominator cleared retains
the support bound for the original kernel. -/
theorem sharpSupport_of_pos_scale (d : Kernel) {r : ℝ} (hr : 0 < r)
    (hs : SharpSupport (fun i j k l ↦ r * d i j k l)) : SharpSupport d := by
  intro y
  let scaled : Kernel := fun i j k l ↦ r * d i j k l
  change SharpSupport scaled at hs
  have hquad (i j k : Fin 3) : edgeQuadratic scaled i j k y = r^2 * edgeQuadratic d i j k y := by
    simp only [edgeQuadratic, scaled, h, f, g]
    ring
  have hroot (i j k : Fin 3) :
      Real.sqrt (edgeQuadratic scaled i j k y) = r * Real.sqrt (edgeQuadratic d i j k y) := by
    rw [hquad, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  apply (mul_le_mul_iff_of_pos_left hr).mp
  calc
    r * (h d 0 1 2 * y 0 + h d 1 0 2 * y 1 + h d 2 0 1 * y 2) =
        h scaled 0 1 2 * y 0 + h scaled 1 0 2 * y 1 + h scaled 2 0 1 * y 2 := by
      simp only [scaled, h]
      ring
    _ ≤ Real.sqrt (edgeQuadratic scaled 0 1 2 y) + Real.sqrt (edgeQuadratic scaled 0 2 1 y) +
        Real.sqrt (edgeQuadratic scaled 1 2 0 y) := hs y
    _ = _ := by rw [hroot 0 1 2, hroot 0 2 1, hroot 1 2 0]; ring

private theorem inner_rowTarget (d : Kernel) (y : V₃) :
    ⟪y, rowTarget d⟫_ℝ =
      h d 0 1 2 * y 0 + h d 1 0 2 * y 1 + h d 2 0 1 * y 2 := by
  simp [rowTarget, PiLp.inner_apply, PiLp.toLp_apply, Fin.sum_univ_three, Real.inner_apply,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The pivots of the binary top block and the complementary diagonal sign. -/
structure EdgePivots (d : Kernel) (i j k : Fin 3) : Prop where
  first_pos : 0 < f d i j
  second_pos : 0 < f d j i - (g d i j / 2)^2 / f d i j
  last_nonneg : 0 ≤ h d k i j

private def ballMap (i j : Fin 3) (a x b c : ℝ) : V₂ →L[ℝ] V₃ :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight
    (EuclideanSpace.single i (Real.sqrt c * Real.sqrt a) +
      EuclideanSpace.single j (Real.sqrt c * (x / Real.sqrt a))) +
  (EuclideanSpace.proj (1 : Fin 2)).smulRight
    (EuclideanSpace.single j (Real.sqrt c * Real.sqrt (b - x^2 / a)))

/-- The image of the two-dimensional unit ball under the scaled
Cholesky factor on one edge. -/
def edgeBallMap (d : Kernel) (i j k : Fin 3) : V₂ →L[ℝ] V₃ :=
  ballMap i j (f d i j) (g d i j / 2) (f d j i) (h d k i j)

private theorem ballMap_adjoint (i j : Fin 3) (a x b c : ℝ) (y : V₃) :
    (ballMap i j a x b c).adjoint y =
      WithLp.toLp 2 ![Real.sqrt c * (Real.sqrt a * y i + (x / Real.sqrt a) * y j),
        Real.sqrt c * Real.sqrt (b - x^2 / a) * y j] := by
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = u 0 * (Real.sqrt c * Real.sqrt a * y i +
          Real.sqrt c * (x / Real.sqrt a) * y j) +
        u 1 * (Real.sqrt c * Real.sqrt (b - x^2 / a) * y j) := by
      simp [ballMap, inner_add_right, real_inner_smul_right, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real] <;> ring
    _ = _ := by
      simp [PiLp.inner_apply, Fin.sum_univ_two] <;> ring_nf <;> simp

/-- The exact support of an edge ball in a signed direction. -/
theorem edgeBallMap_support (d : Kernel) (i j k : Fin 3)
    (hp : EdgePivots d i j k) (y : V₃) :
    ‖(edgeBallMap d i j k).adjoint y‖ = Real.sqrt (edgeQuadratic d i j k y.ofLp) := by
  let a := f d i j
  let x := g d i j / 2
  let b := f d j i
  let c := h d k i j
  have ha : 0 < a := hp.first_pos
  have hb : 0 ≤ b - x^2/a := hp.second_pos.le
  have hc : 0 ≤ c := hp.last_nonneg
  have hcross : Real.sqrt a * (x / Real.sqrt a) = x := by
    field_simp [(Real.sqrt_pos.2 ha).ne'] <;> ring
  have hdiv : (x / Real.sqrt a)^2 = x^2/a := by
    rw [div_pow, Real.sq_sqrt ha.le]
  have hquad : ‖(ballMap i j a x b c).adjoint y‖^2 = edgeQuadratic d i j k y.ofLp := by
    rw [ballMap_adjoint, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      _ = (Real.sqrt c)^2 *
          ((Real.sqrt a)^2 * (y i)^2 +
            2 * (Real.sqrt a * (x / Real.sqrt a)) * y i * y j +
            ((x / Real.sqrt a)^2 + (Real.sqrt (b - x^2/a))^2) * (y j)^2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt hc, Real.sq_sqrt ha.le, hcross, hdiv, Real.sq_sqrt hb]
        unfold edgeQuadratic
        dsimp only [a, x, b, c]
        ring
  change ‖(ballMap i j a x b c).adjoint y‖ = Real.sqrt (edgeQuadratic d i j k y.ofLp)
  rw [← hquad, Real.sqrt_sq (norm_nonneg _)]

/-- The three two-dimensional witnesses for the specified BMV edges. -/
theorem exists_edgeBall_witnesses_of_support (d : Kernel)
    (hp01 : EdgePivots d 0 1 2) (hp02 : EdgePivots d 0 2 1) (hp12 : EdgePivots d 1 2 0)
    (hs : SharpSupport d) :
    ∃ u01 u02 u12 : V₂,
      u01 ∈ closedBall (0 : V₂) 1 ∧
      u02 ∈ closedBall (0 : V₂) 1 ∧
      u12 ∈ closedBall (0 : V₂) 1 ∧
      edgeBallMap d 0 1 2 u01 + edgeBallMap d 0 2 1 u02 + edgeBallMap d 1 2 0 u12 =
        rowTarget d := by
  apply exists_three_ball_witnesses_of_support
  intro y
  rw [inner_rowTarget, edgeBallMap_support d 0 1 2 hp01, edgeBallMap_support d 0 2 1 hp02,
    edgeBallMap_support d 1 2 0 hp12]
  exact hs y.ofLp

private theorem ballMap_apply_left {i j : Fin 3} (hij : i ≠ j)
    (a x b c : ℝ) (u : V₂) :
    ballMap i j a x b c u i = Real.sqrt c * (Real.sqrt a * u 0) := by
  simp [ballMap, PiLp.single_apply, hij, Ne.symm hij, smul_eq_mul] <;> ring

private theorem ballMap_apply_right {i j : Fin 3} (hij : i ≠ j)
    (a x b c : ℝ) (u : V₂) :
    ballMap i j a x b c u j =
      Real.sqrt c * ((x / Real.sqrt a) * u 0 + Real.sqrt (b - x^2/a) * u 1) := by
  simp [ballMap, PiLp.single_apply, hij, Ne.symm hij, smul_eq_mul] <;> ring

private theorem ballMap_apply_off {i j l : Fin 3} (hli : l ≠ i) (hlj : l ≠ j)
    (a x b c : ℝ) (u : V₂) :
    ballMap i j a x b c u l = 0 := by
  simp [ballMap, PiLp.single_apply, hli, hlj, Ne.symm hli, Ne.symm hlj]

open Separated (block block_psd_of_schur)

/-- An edge ball supplies the two coefficients of a PSD Gram block. -/
theorem edgeBallMap_block_psd (d : Kernel) {i j k : Fin 3} (hij : i ≠ j)
    (hp : EdgePivots d i j k) {u : V₂} (hu : u ∈ closedBall (0 : V₂) 1) :
    (block (f d i j) (g d i j / 2) (f d j i)
      (edgeBallMap d i j k u i) (edgeBallMap d i j k u j) (h d k i j)).PosSemidef := by
  let a := f d i j
  let x := g d i j / 2
  let b := f d j i
  let c := h d k i j
  have ha : 0 < a := hp.first_pos
  have hb : 0 < b - x^2/a := hp.second_pos
  have hc : 0 ≤ c := hp.last_nonneg
  change (block a x b (ballMap i j a x b c u i) (ballMap i j a x b c u j) c).PosSemidef
  rw [ballMap_apply_left hij, ballMap_apply_right hij]
  apply block_psd_of_schur _ _ _ _ _ _ ha hb
  have hnorm : (u 0)^2 + (u 1)^2 ≤ 1 := by
    have hn := mem_closedBall_zero_iff.mp hu
    have hsq := (sq_le_sq₀ (norm_nonneg u) zero_le_one).2 hn
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using hsq
  have hsplit : c * (u 1)^2 ≤ c - c * (u 0)^2 := by
    have hm := mul_le_mul_of_nonneg_left hnorm hc
    rw [mul_add, mul_one] at hm
    linarith only [hm]
  have hquot : x * Real.sqrt a / a = x / Real.sqrt a := by
    calc
      _ = x * Real.sqrt a / (Real.sqrt a)^2 := by rw [Real.sq_sqrt ha.le]
      _ = _ := by field_simp [(Real.sqrt_pos.2 ha).ne'] <;> ring
  let y := Real.sqrt c * (Real.sqrt a * u 0)
  let z := Real.sqrt c * ((x / Real.sqrt a) * u 0 + Real.sqrt (b - x^2/a) * u 1)
  have hy : y^2/a = c * (u 0)^2 := by
    dsimp only [y]
    rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt ha.le]
    field_simp [ha.ne'] <;> ring
  have hz : z - x*y/a = Real.sqrt c * Real.sqrt (b - x^2/a) * u 1 := by
    calc
      _ = Real.sqrt c *
          ((x / Real.sqrt a - x * Real.sqrt a / a) * u 0 + Real.sqrt (b - x^2/a) * u 1) := by
        dsimp only [y, z]
        ring
      _ = _ := by rw [hquot, sub_self, zero_mul, zero_add]; ring
  change (z - x*y/a)^2 ≤ (b - x^2/a) * (c - y^2/a)
  rw [hz, hy]
  calc
    _ = (b - x^2/a) * (c * (u 1)^2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hb.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsplit hb.le

private theorem gramBlock_eq_block (d : Kernel) (alloc : Fin 3 → Fin 3 → ℝ) (i j k : Fin 3) :
    gramBlock d alloc i j k =
      block (f d i j) (g d i j / 2) (f d j i) (alloc i j) (alloc j i) (h d k i j) := by
  simp [gramBlock, block, Complex.ofReal_div]

/-- The support test produces the exact shared `Allocation`, with its
three row sums and its three complex PSD conditions. -/
theorem allocation_of_sharpSupport (d : Kernel)
    (hp01 : EdgePivots d 0 1 2) (hp02 : EdgePivots d 0 2 1) (hp12 : EdgePivots d 1 2 0)
    (hs : SharpSupport d) :
    ∃ alloc : Fin 3 → Fin 3 → ℝ, Allocation d alloc := by
  obtain ⟨u01, u02, u12, hu01, hu02, hu12, hsum⟩ :=
    exists_edgeBall_witnesses_of_support d hp01 hp02 hp12 hs
  let v01 := edgeBallMap d 0 1 2 u01
  let v02 := edgeBallMap d 0 2 1 u02
  let v12 := edgeBallMap d 1 2 0 u12
  let alloc : Fin 3 → Fin 3 → ℝ :=
    ![![0, v01 0, v02 0], ![v01 1, 0, v12 1], ![v02 2, v12 2, 0]]
  change v01 + v02 + v12 = rowTarget d at hsum
  have hv01 : v01 2 = 0 :=
    ballMap_apply_off (i := 0) (j := 1) (l := 2) (by decide) (by decide) _ _ _ _ _
  have hv02 : v02 1 = 0 :=
    ballMap_apply_off (i := 0) (j := 2) (l := 1) (by decide) (by decide) _ _ _ _ _
  have hv12 : v12 0 = 0 :=
    ballMap_apply_off (i := 1) (j := 2) (l := 0) (by decide) (by decide) _ _ _ _ _
  refine ⟨alloc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := congrArg (fun v : V₃ ↦ v 0) hsum
    simpa [alloc, rowTarget, hv12, PiLp.toLp_apply] using hr
  · have hr := congrArg (fun v : V₃ ↦ v 1) hsum
    simpa [alloc, rowTarget, hv02, PiLp.toLp_apply, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hr
  · have hr := congrArg (fun v : V₃ ↦ v 2) hsum
    simpa [alloc, rowTarget, hv01, PiLp.toLp_apply, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hr
  · rw [gramBlock_eq_block]
    exact edgeBallMap_block_psd d (by decide) hp01 hu01
  · rw [gramBlock_eq_block]
    exact edgeBallMap_block_psd d (by decide) hp02 hu02
  · rw [gramBlock_eq_block]
    exact edgeBallMap_block_psd d (by decide) hp12 hu12

theorem spectral_edgePivots (p : ℕ) (s : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (i j k : Fin 3)
    (hbinary : (g (spectralDefect p s) i j)^2 <
      2 * f (spectralDefect p s) i j * f (spectralDefect p s) j i) :
    EdgePivots (spectralDefect p s) i j k := by
  let d := spectralDefect p s
  change (g d i j)^2 < 2 * f d i j * f d j i at hbinary
  have ha : 0 ≤ f d i j := FourCopyGap.gapDefect_nonneg p (hs i) (hs i) (hs i) (hs j)
  have ha' : 0 < f d i j := by
    refine lt_of_le_of_ne ha ?_
    intro heq
    have hneg : (g d i j)^2 < 0 := by simpa only [← heq, mul_zero, zero_mul] using hbinary
    exact hneg.not_ge (sq_nonneg _)
  have hc : 0 ≤ h d k i j := FourCopyGap.gapDefect_nonneg p (hs k) (hs k) (hs i) (hs j)
  refine ⟨ha', sub_pos.2 ((div_lt_iff₀ ha').2 ?_), hc⟩
  nlinarith only [hbinary, sq_nonneg (g d i j)]

open private FourCopyGap.balanced FourCopyGap.cyclicSurplus FourCopyGap.cyclicSurplus_nonneg
  FourCopyGap.gapDefect_eq_sum FourCopyGap.monomial FourCopyGap.rotate FourCopyGap.rotateBack
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap in
/-- A composition concentrated in one slot gives strict AM–GM whenever
the first and third entries differ. -/
theorem gapDefect_pos_of_first_ne_third (p : ℕ) (hp : 0 < p) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hac : a ≠ c) :
    0 < FourCopyGap.gapDefect p a b c d := by
  let z : Fin 4 → ℝ := ![a^p, b^p, c^p, d^p]
  have hweights : ∑ i : Fin 4, (1/4 : ℝ) = 1 := by norm_num [Fin.sum_univ_four]
  have hz : ∀ i : Fin 4, 0 ≤ z i := by
    intro i
    fin_cases i <;> simp [z, pow_nonneg, ha, hb, hc, hd]
  have hunequal : z 0 ≠ z 2 := by
    change a^p ≠ c^p
    intro h
    exact hac ((pow_left_strictMonoOn₀ hp.ne').injOn ha hc h)
  have hstrict :=
    (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 4))
      (fun _ => (1/4 : ℝ)) z (fun _ _ => by norm_num) hweights
      (fun i _ => hz i)).mpr ⟨0, Finset.mem_univ 0, 2, Finset.mem_univ 2, hunequal⟩
  have hmean : FourCopyGap.balanced p a b c d < (a^p + b^p + c^p + d^p)/4 := by
    calc
      FourCopyGap.balanced p a b c d = ∏ i : Fin 4, z i ^ (1/4 : ℝ) := by
        simp [FourCopyGap.balanced, z, Fin.prod_univ_four, ← Real.rpow_natCast_mul ha,
          ← Real.rpow_natCast_mul hb, ← Real.rpow_natCast_mul hc,
          ← Real.rpow_natCast_mul hd, div_eq_mul_inv]
      _ < ∑ i : Fin 4, (1/4 : ℝ) * z i := hstrict
      _ = _ := by simp [z, Fin.sum_univ_four] <;> ring
  let witness : FourCopyGap.Gap := (p, 0, 0, 0)
  have hwitness : witness ∈ FourCopyGap.gaps p := by
    simp [witness, FourCopyGap.mem_gaps]
  rw [FourCopyGap.gapDefect_eq_sum]
  apply (Finset.sum_pos_iff_of_nonneg (fun _ hg =>
    FourCopyGap.cyclicSurplus_nonneg hg ha hb hc hd)).mpr
  refine ⟨witness, hwitness, sub_pos.mpr ?_⟩
  convert hmean using 1
  simp [witness, FourCopyGap.monomial, FourCopyGap.rotate, FourCopyGap.rotateBack] <;> ring

/-- The binary conditioning inequalities and the signed support test give an
allocation for the actual four-slot spectral kernel. -/
theorem spectral_allocation_of_sharpSupport (p : ℕ) (s : Fin 3 → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hbinary : ∀ i j : Fin 3, i < j → (g (spectralDefect p s) i j)^2 <
      2 * f (spectralDefect p s) i j * f (spectralDefect p s) j i)
    (hsupport : SharpSupport (spectralDefect p s)) :
    ∃ alloc : Fin 3 → Fin 3 → ℝ, Allocation (spectralDefect p s) alloc :=
  allocation_of_sharpSupport _
    (spectral_edgePivots p s hs 0 1 2 (hbinary 0 1 (by decide)))
    (spectral_edgePivots p s hs 0 2 1 (hbinary 0 2 (by decide)))
    (spectral_edgePivots p s hs 1 2 0 (hbinary 1 2 (by decide))) hsupport

/-- The four-copy trace bound consumes the support and binary certificates
directly, with any spectral multiplicities. -/
theorem product_bound_of_spectrum_subset_of_sharpSupport
    {n : Type*} [Fintype n] [DecidableEq n] (p : ℕ) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hspectrum : ∀ a, ∃ i, hA.isHermitian.eigenvalues a = s i)
    (hbinary : ∀ i j : Fin 3, i < j → (g (spectralDefect p s) i j)^2 <
      2 * f (spectralDefect p s) i j * f (spectralDefect p s) j i)
    (hsupport : SharpSupport (spectralDefect p s)) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  obtain ⟨alloc, halloc⟩ := spectral_allocation_of_sharpSupport p s hs hbinary hsupport
  exact product_bound_of_spectrum_subset p A B hA hB s hs hspectrum alloc halloc

open private gapDefect_scale
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation

/-- Two fourth-root spectral ratios suffice for the certificate. -/
theorem sharpSupport_of_normalized_positive_spectrum (p : ℕ) (s : Fin 3 → ℝ)
    (hs : ∀ i, 0 < s i) (horder : StrictMono s)
    (hunit : ∀ r t : ℝ, 0 < r → r < 1 → 0 < t → t < 1 →
      SharpSupport (spectralDefect p ![r^4*t^4, t^4, 1])) :
    SharpSupport (spectralDefect p s) := by
  let r := (s 0 / s 1) ^ (1/4 : ℝ)
  let t := (s 1 / s 2) ^ (1/4 : ℝ)
  have h01 : 0 < s 0 / s 1 := div_pos (hs 0) (hs 1)
  have h12 : 0 < s 1 / s 2 := div_pos (hs 1) (hs 2)
  have hr : 0 < r := Real.rpow_pos_of_pos h01 _
  have ht : 0 < t := Real.rpow_pos_of_pos h12 _
  have hr1 : r < 1 := Real.rpow_lt_one h01.le
    ((div_lt_one (hs 1)).mpr (horder (by decide))) (by norm_num)
  have ht1 : t < 1 := Real.rpow_lt_one h12.le
    ((div_lt_one (hs 2)).mpr (horder (by decide))) (by norm_num)
  have hr4 : r^4 = s 0 / s 1 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast h01.le]
    norm_num
  have ht4 : t^4 = s 1 / s 2 := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast h12.le]
    norm_num
  let v : Fin 3 → ℝ := ![r^4*t^4, t^4, 1]
  have hv0 (i : Fin 3) : 0 ≤ v i := by
    fin_cases i <;> simp [v] <;> positivity
  have hvals (i : Fin 3) : s i = s 2 * v i := by
    fin_cases i <;> simp [v, hr4, ht4] <;> field_simp [(hs 1).ne', (hs 2).ne']
  let scale := (s 2)^p
  have hscale : 0 < scale := pow_pos (hs 2) p
  have hk : (fun i j k l ↦ scale⁻¹ * spectralDefect p s i j k l) = spectralDefect p v := by
    funext i j k l
    simp only [spectralDefect]
    rw [hvals i, hvals j, hvals k, hvals l,
      gapDefect_scale p (hs 2).le (hv0 i) (hv0 j) (hv0 k) (hv0 l)]
    change scale⁻¹ * (scale * _) = _
    simp [← mul_assoc, hscale.ne']
  apply sharpSupport_of_pos_scale _ (inv_pos.mpr hscale)
  rw [hk]
  exact hunit r t hr hr1 ht ht1

#print axioms exists_three_ball_witnesses_of_support
#print axioms allocation_of_sharpSupport
#print axioms spectral_allocation_of_sharpSupport
#print axioms product_bound_of_spectrum_subset_of_sharpSupport

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
