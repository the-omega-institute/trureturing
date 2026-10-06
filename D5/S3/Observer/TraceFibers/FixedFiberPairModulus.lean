/- GID: D5/S3/Observer/TraceFibers/FixedFiberPairModulus
   generality: I
   mirror-B: D5/B/S3/Observer/TraceFibers/FixedFiberPairModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed executed shear history has exact same-pair scalar and matrix moduli. -/

import D5.S3.Observer.GoldenCoding.GoldenModularStandardPair
import D5.S3.Observer.HyperbolicTransport.GoldenDualTimeRenormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

noncomputable section

namespace D5.S3.Observer.TraceFibers.FixedFiberPairModulus

/-- Atomic operations in chronological execution order. -/
inductive Action where
  | advance
  | exchange
  deriving DecidableEq

/-- The actual matrices of the two permitted operations. -/
def actionMatrix : Action → Matrix (Fin 2) (Fin 2) ℝ
  | .advance => GoldenCoding.GoldenModularStandardPair.goldenModularStep
  | .exchange => HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix

/-- Later operations multiply on the left; no inverse operation is introduced. -/
def wordMatrix (word : List Action) : Matrix (Fin 2) (Fin 2) ℝ :=
  (word.map actionMatrix).reverse.prod

/-- `true` is the upper shear, `false` the lower shear. -/
def secondMatrix (upper : Bool) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if upper then (actionMatrix .exchange * actionMatrix .advance) ^ k
  else (actionMatrix .advance * actionMatrix .exchange) ^ k

/-- Positive entries with the rank-one relation, in the original source coordinates. -/
def positiveSource (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, 0 < R i j) ∧ R 0 0 * R 1 1 = R 0 1 * R 1 0

/-- The two actual observed fibers, parametrized by their lower diagonal entry. -/
def source (upper : Bool) (x ζ s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if upper then !![x - s, s * (x - s) / ζ; ζ, s]
  else !![x - s, ζ; s * (x - s) / ζ, s]

/-- Initial, second, and third raw reads on one cumulative execution. -/
def readings (executed continuation : List Action) (R : Matrix (Fin 2) (Fin 2) ℝ) : List ℝ :=
  [Matrix.trace (1 * R), Matrix.trace (wordMatrix executed * R),
    Matrix.trace (wordMatrix (executed ++ continuation) * R)]

/-- Maximum absolute entry, with all four entries included. -/
def maxEntry (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  max (max |Q 0 0| |Q 0 1|) (max |Q 1 0| |Q 1 1|)

/-- One selected third matrix owns this set of common source pairs. Equal pairs are allowed. -/
def feasiblePairs (upper : Bool) (x ζ : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (τ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < x ∧ 0 < p.2 ∧ p.2 < x ∧
    |Matrix.trace (B * source upper x ζ p.1) -
      Matrix.trace (B * source upper x ζ p.2)| ≤ τ}

/-- A genuine supremum of source spacing over the common feasible-pair set. -/
def scalarModulus (upper : Bool) (x ζ : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (τ : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => |p.1 - p.2|) '' feasiblePairs upper x ζ B τ)

/-- A genuine supremum of matrix distance over exactly the same feasible pairs. -/
def matrixModulus (upper : Bool) (x ζ : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (τ : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => maxEntry
    (source upper x ζ p.1 - source upper x ζ p.2)) '' feasiblePairs upper x ζ B τ)

/-- The geometric envelope for the maximum-entry objective. -/
def geometry (x ζ w : ℝ) : ℝ :=
  max w (min w (x / 2) * (x - min w (x / 2)) / ζ)

/-- The upper shear power in source coordinates. -/
theorem upper_shear_power (k : ℕ) : (actionMatrix .exchange * actionMatrix .advance) ^ k =
    (!![1, (k : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℤ =>
    Q.map (Int.castRingHom ℝ)) (ModularGroup.coe_T_zpow (k : ℤ))
  simp only [zpow_natCast, Matrix.SpecialLinearGroup.coe_pow, Matrix.map_pow,
    ModularGroup.coe_T] at h
  have hstep : actionMatrix .exchange * actionMatrix .advance =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [actionMatrix, GoldenCoding.GoldenModularStandardPair.goldenModularStep,
        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  rw [hstep]
  convert h using 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- The lower shear power in source coordinates. -/
theorem lower_shear_power (k : ℕ) : (actionMatrix .advance * actionMatrix .exchange) ^ k =
    (!![1, 0; (k : ℝ), 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hs : actionMatrix .advance * actionMatrix .exchange =
      (actionMatrix .exchange * actionMatrix .advance).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [actionMatrix, GoldenCoding.GoldenModularStandardPair.goldenModularStep,
        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [hs, ← Matrix.transpose_pow, upper_shear_power k]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Exact scalar and maximum-entry suprema on the positive rank-one fiber of a
fixed executed shear history. The initial read and the literal sunk action cost
are retained, and one continuation is fixed before candidate sources are quantified. -/
theorem result (upper : Bool) (executed continuation : List Action) (k : ℕ)
    (x ζ τ : ℝ) (hx : 0 < x) (hζ : 0 < ζ) (hk : 1 ≤ k)
    (hexecuted : wordMatrix executed = secondMatrix upper k)
    (hτ : 0 ≤ τ)
    (he : 0 < (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
      else (wordMatrix continuation * wordMatrix executed) 0 1))
    (hμ : 0 ≤ |(wordMatrix continuation * wordMatrix executed) 1 1 -
      (wordMatrix continuation * wordMatrix executed) 0 0| -
      (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
        else (wordMatrix continuation * wordMatrix executed) 0 1) / ζ * x) :
    let B := wordMatrix continuation * wordMatrix executed
    let e := if upper then B 1 0 else B 0 1
    let D := B 1 1 - B 0 0
    let α := e / ζ
    let μ := |D| - α * x
    let r := (Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)
    let w := min x r
    wordMatrix (executed ++ continuation) = B ∧
    (executed ++ continuation).length = executed.length + continuation.length ∧
    (∀ R, (readings executed continuation R).length = 3) ∧
    (∀ R, positiveSource R → ∃ c ℓ : Fin 2 → ℝ,
      (∀ i, 0 < c i) ∧ (∀ j, 0 < ℓ j) ∧ R = Matrix.vecMulVec c ℓ ∧
      ∀ A : Matrix (Fin 2) (Fin 2) ℝ, Matrix.trace (A * R) = ℓ ⬝ᵥ (A *ᵥ c)) ∧
    (∀ s, 0 < s → s < x → readings executed continuation (source upper x ζ s) =
      [x, x + (k : ℝ) * ζ, Matrix.trace (B * source upper x ζ s)]) ∧
    (∀ R, (positiveSource R ∧ Matrix.trace R = x ∧
      Matrix.trace (wordMatrix executed * R) = x + (k : ℝ) * ζ) ↔
      ∃ s, 0 < s ∧ s < x ∧ R = source upper x ζ s) ∧
    0 < α ∧ 0 ≤ r ∧ μ * r + α * r ^ 2 = τ ∧
    0 ≤ w ∧ w ≤ x ∧ μ * w + α * w ^ 2 ≤ τ ∧
    (0 < τ → 0 < w) ∧
    (∀ u v, |Matrix.trace (B * source upper x ζ u) -
      Matrix.trace (B * source upper x ζ v)| =
      |u - v| * |D + α * (x - u - v)|) ∧
    (∀ u v, maxEntry (source upper x ζ u - source upper x ζ v) =
      max |u - v| (|u - v| * |x - u - v| / ζ)) ∧
    (∀ l, 0 < l → l < w → ∀ c, c < l * (x - l) / ζ →
      ∃ u v, (u, v) ∈ feasiblePairs upper x ζ B τ ∧
        |u - v| = l ∧ c < maxEntry (source upper x ζ u - source upper x ζ v)) ∧
    scalarModulus upper x ζ B τ = w ∧ matrixModulus upper x ζ B τ = geometry x ζ w ∧
    (0 < τ → 0 < w ∧ 0 < geometry x ζ w ∧
      ∀ p ∈ feasiblePairs upper x ζ B τ,
        |p.1 - p.2| < w ∧ maxEntry (source upper x ζ p.1 - source upper x ζ p.2) <
          geometry x ζ w) ∧
    (τ = 0 → scalarModulus upper x ζ B τ = 0 ∧ matrixModulus upper x ζ B τ = 0 ∧
      (x / 2, x / 2) ∈ feasiblePairs upper x ζ B τ ∧
      |x / 2 - x / 2| = 0 ∧ maxEntry (source upper x ζ (x / 2) -
        source upper x ζ (x / 2)) = 0) := by
  classical
  dsimp only
  let B := wordMatrix continuation * wordMatrix executed
  let e : ℝ := if upper then B 1 0 else B 0 1
  let D := B 1 1 - B 0 0
  let α := e / ζ
  let μ := |D| - α * x
  let r := (Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)
  let w := min x r
  have hα : 0 < α := div_pos he hζ
  have hζ0 : ζ ≠ 0 := ne_of_gt hζ
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hμ0 : 0 ≤ μ := hμ
  have hword : wordMatrix (executed ++ continuation) = B := by
    simp [wordMatrix, List.map_append, List.reverse_append, List.prod_append, B]
  have hsecond : wordMatrix executed =
      if upper then !![1, (k : ℝ); 0, 1] else !![1, 0; (k : ℝ), 1] := by
    rw [hexecuted]
    cases upper <;> simp [secondMatrix, upper_shear_power, lower_shear_power]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hfiber : ∀ R, (positiveSource R ∧ Matrix.trace R = x ∧
      Matrix.trace (wordMatrix executed * R) = x + (k : ℝ) * ζ) ↔
      ∃ s, 0 < s ∧ s < x ∧ R = source upper x ζ s := by
    intro R
    constructor
    · rintro ⟨⟨hpos, hrank⟩, htrace, hread⟩
      have ht : R 0 0 + R 1 1 = x := by simpa [Matrix.trace_fin_two] using htrace
      have hoff : (if upper then R 1 0 else R 0 1) = ζ := by
        cases upper <;>
          simp [hsecond, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at hread ⊢ <;>
          apply (mul_left_cancel₀ hk0) <;> linarith only [hread, ht]
      refine ⟨R 1 1, hpos 1 1, by linarith only [ht, hpos 0 0], ?_⟩
      have hp : R 0 0 = x - R 1 1 := by linarith only [ht]
      cases upper <;> simp at hoff <;>
        rw [hp, hoff] at hrank <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> simp [source, hp, hoff] <;>
        apply (eq_div_iff hζ0).2 <;> nlinarith only [hrank]
    · rintro ⟨s, hs, hsx, rfl⟩
      have hxs : 0 < x - s := sub_pos.mpr hsx
      have hprod : 0 < s * (x - s) / ζ := div_pos (mul_pos hs hxs) hζ
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro i j
        cases upper <;> fin_cases i <;> fin_cases j <;> simp [source] <;> assumption
      · cases upper <;> simp [source] <;> field_simp <;> ring
      · cases upper <;> simp [source, Matrix.trace_fin_two]
      · cases upper <;>
          simp [hsecond, source, Matrix.trace_fin_two] <;> ring
  have hfactor : ∀ R, positiveSource R → ∃ c ℓ : Fin 2 → ℝ,
      (∀ i, 0 < c i) ∧ (∀ j, 0 < ℓ j) ∧ R = Matrix.vecMulVec c ℓ ∧
      ∀ A : Matrix (Fin 2) (Fin 2) ℝ, Matrix.trace (A * R) = ℓ ⬝ᵥ (A *ᵥ c) := by
    intro R hR
    let c : Fin 2 → ℝ := ![R 0 0, R 1 0]
    let ℓ : Fin 2 → ℝ := ![1, R 0 1 / R 0 0]
    have hp0 : R 0 0 ≠ 0 := ne_of_gt (hR.1 0 0)
    have hmat : R = Matrix.vecMulVec c ℓ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c, ℓ, Matrix.vecMulVec] <;>
        field_simp <;> nlinarith only [hR.2]
    refine ⟨c, ℓ, ?_, ?_, hmat, ?_⟩
    · intro i; fin_cases i <;> simp [c] <;> exact hR.1 _ _
    · intro j; fin_cases j <;> simp [ℓ]
      exact div_pos (hR.1 0 1) (hR.1 0 0)
    · intro A
      rw [hmat, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  have hreads : ∀ s, 0 < s → s < x → readings executed continuation (source upper x ζ s) =
      [x, x + (k : ℝ) * ζ, Matrix.trace (B * source upper x ζ s)] := by
    intro s hs hsx
    obtain ⟨_, hfirst, hsecondread⟩ := (hfiber (source upper x ζ s)).mpr ⟨s, hs, hsx, rfl⟩
    simp only [readings, one_mul, hword, hfirst, hsecondread]
  have htrace : ∀ u v, |Matrix.trace (B * source upper x ζ u) -
      Matrix.trace (B * source upper x ζ v)| = |u - v| * |D + α * (x - u - v)| := by
    intro u v
    rw [← abs_mul]
    congr 1
    cases upper <;>
      simp [source, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, D, α, e] <;>
      ring
  have hnorm : ∀ u v, maxEntry (source upper x ζ u - source upper x ζ v) =
      max |u - v| (|u - v| * |x - u - v| / ζ) := by
    intro u v
    have hp : u * (x - u) / ζ - v * (x - v) / ζ =
        (u - v) * (x - u - v) / ζ := by ring
    have hdiag : |v - u| = |u - v| := abs_sub_comm v u
    cases upper <;>
      simp [maxEntry, source, Matrix.sub_apply, hp, hdiag, abs_div, abs_mul,
        abs_of_pos hζ, max_comm, abs_nonneg]
  have hrad : 0 ≤ μ ^ 2 + 4 * α * τ := by positivity
  have hsq := Real.sq_sqrt hrad
  have hsqrt := Real.sqrt_nonneg (μ ^ 2 + 4 * α * τ)
  have hmroot : μ ≤ Real.sqrt (μ ^ 2 + 4 * α * τ) := by nlinarith only [hsq, hsqrt, hμ0, mul_nonneg hα.le hτ]
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hmroot) (by positivity)
  have hre : 2 * α * r = Real.sqrt (μ ^ 2 + 4 * α * τ) - μ := by
    dsimp [r]
    field_simp
  have hφr : μ * r + α * r ^ 2 = τ := by
    have hsum : 2 * α * r + μ = Real.sqrt (μ ^ 2 + 4 * α * τ) := by
      linarith only [hre]
    have hs : (2 * α * r + μ) ^ 2 = μ ^ 2 + 4 * α * τ := by rw [hsum, hsq]
    have hp : (4 * α) * (μ * r + α * r ^ 2 - τ) = 0 := by linear_combination hs
    have hq := (mul_eq_zero.mp hp).resolve_left (by positivity : 4 * α ≠ 0)
    linarith only [hq]
  have hw0 : 0 ≤ w := le_min hx.le hr0
  have hwx : w ≤ x := min_le_left _ _
  have hwr : w ≤ r := min_le_right _ _
  have hφw : μ * w + α * w ^ 2 ≤ τ := by
    nlinarith only [hφr, mul_nonneg hμ0 (sub_nonneg.mpr hwr),
      mul_nonneg hα.le (mul_nonneg (sub_nonneg.mpr hwr) (by linarith only [hr0, hw0] : 0 ≤ r + w))]
  have hwpos : 0 < τ → 0 < w := by
    intro ht
    have hrpos : 0 < r := by
      by_contra hn
      have : r = 0 := le_antisymm (le_of_not_gt hn) hr0
      rw [this] at hφr
      nlinarith only [hφr, ht]
    exact lt_min hx hrpos
  have hD : |D| = μ + α * x := by dsimp [μ]; ring
  have hDne : D ≠ 0 := by
    intro hd
    have hp := mul_pos hα hx
    rw [hd, abs_zero] at hD
    linarith only [hD, hμ0, hp]
  have hslack : ∀ l, 0 < l → l < w → μ * l + α * l ^ 2 < τ := by
    intro l hl hlw
    have hp := mul_pos hα (mul_pos (sub_pos.mpr hlw) (by linarith only [hw0, hl] : 0 < w + l))
    have hp' := mul_nonneg hμ0 (sub_nonneg.mpr hlw.le)
    nlinarith only [hp, hp', hφw]
  have hpair : ∀ l, 0 < l → l < w → ∀ c, c < l * (x - l) / ζ →
      ∃ u v, (u, v) ∈ feasiblePairs upper x ζ B τ ∧
        |u - v| = l ∧ c < maxEntry (source upper x ζ u - source upper x ζ v) := by
    intro l hl hlw c hc
    have hlx : l < x := lt_of_lt_of_le hlw hwx
    have hsl := hslack l hl hlw
    let ε := min ((x - l) / 4)
      (min ((τ - (μ * l + α * l ^ 2)) / (4 * α * l))
        (ζ * (l * (x - l) / ζ - c) / (4 * l)))
    have hε : 0 < ε := by
      apply lt_min (by positivity)
      apply lt_min (div_pos (sub_pos.mpr hsl) (by positivity))
      exact div_pos (mul_pos hζ (sub_pos.mpr hc)) (by positivity)
    have hεdom : ε ≤ (x - l) / 4 := min_le_left _ _
    have hεread : ε ≤ (τ - (μ * l + α * l ^ 2)) / (4 * α * l) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hεobj : ε ≤ ζ * (l * (x - l) / ζ - c) / (4 * l) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hread : μ * l + α * l ^ 2 + 2 * α * ε * l < τ := by
      have hb := (le_div_iff₀ (by positivity : 0 < 4 * α * l)).mp hεread
      nlinarith only [hb, mul_pos hα (mul_pos hε hl)]
    have hobj : c < l * (x - l - 2 * ε) / ζ := by
      have hb := (le_div_iff₀ (by positivity : 0 < 4 * l)).mp hεobj
      have heq : ζ * (l * (x - l) / ζ - c) = l * (x - l) - ζ * c := by
        field_simp
      rw [heq] at hb
      apply (lt_div_iff₀ hζ).2
      nlinarith only [hb, mul_pos hε hl]
    have hzpos : 0 < x - l - 2 * ε := by linarith only [hεdom, hlx]
    have hcommon (u v : ℝ) (hu : 0 < u) (hv : v < x) (hvu : v - u = l)
        (hgap : |D + α * (x - u - v)| = μ + α * l + 2 * α * ε)
        (hz : |x - u - v| = x - l - 2 * ε) :
        (u, v) ∈ feasiblePairs upper x ζ B τ ∧ |u - v| = l ∧
          c < maxEntry (source upper x ζ u - source upper x ζ v) := by
      have huv : |u - v| = l := by rw [abs_sub_comm, abs_of_pos (by linarith only [hvu, hl])]; exact hvu
      refine ⟨⟨hu, by linarith only [hvu, hv, hl], by linarith only [hu, hvu, hl], hv, ?_⟩, huv, ?_⟩
      · rw [htrace, huv, hgap]
        nlinarith only [hread]
      · rw [hnorm, huv, hz]
        exact lt_of_lt_of_le hobj (le_max_right _ _)
    rcases lt_or_gt_of_ne hDne with hneg | hpos
    · have hd : D = -(μ + α * x) := by rw [abs_of_neg hneg] at hD; linarith only [hD]
      refine ⟨ε, ε + l, hcommon ε (ε + l) hε (by linarith only [hεdom, hlx]) (by ring) ?_ ?_⟩
      · rw [hd, abs_of_neg (by nlinarith only [hμ0, mul_pos hα hε, mul_pos hα hl] :
          -(μ + α * x) + α * (x - ε - (ε + l)) < 0)]
        ring
      · rw [abs_of_pos (by linarith only [hzpos] : 0 < x - ε - (ε + l))]
        ring
    · have hd : D = μ + α * x := by rw [abs_of_pos hpos] at hD; exact hD
      refine ⟨x - ε - l, x - ε,
        hcommon (x - ε - l) (x - ε) (by linarith only [hεdom, hlx]) (by linarith only [hε]) (by ring) ?_ ?_⟩
      · rw [hd, abs_of_pos (by nlinarith only [hμ0, mul_pos hα hε, mul_pos hα hl] :
          μ + α * x + α * (x - (x - ε - l) - (x - ε)) > 0)]
        ring
      · rw [abs_of_neg (by linarith only [hzpos] : x - (x - ε - l) - (x - ε) < 0)]
        ring
  let b := min w (x / 2)
  let H := b * (x - b) / ζ
  let S := geometry x ζ w
  have hS : S = max w H := rfl
  have hb0 : 0 ≤ b := le_min hw0 (by positivity)
  have hbw : b ≤ w := min_le_left _ _
  have hbx : b ≤ x / 2 := min_le_right _ _
  have hH0 : 0 ≤ H := div_nonneg (mul_nonneg hb0 (by linarith only [hbx, hx])) hζ.le
  have hS0 : 0 ≤ S := le_trans hw0 (le_max_left _ _)
  have hquadratic : ∀ l, 0 ≤ l → l ≤ w → l * (x - l) / ζ ≤ H := by
    intro l hl hlw
    apply (div_le_div_iff_of_pos_right hζ).2
    by_cases hw : w ≤ x / 2
    · have hb : b = w := min_eq_left hw
      rw [hb]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hlw) (by linarith only [hw, hlw] :
        0 ≤ x - w - l)]
    · have hb : b = x / 2 := min_eq_right (le_of_not_ge hw)
      rw [hb]
      nlinarith only [sq_nonneg (l - x / 2)]
  have hgeom : ∀ u v, 0 < u → u < x → 0 < v → v < x →
      |u - v| < x ∧ |x - u - v| < x - |u - v| := by
    intro u v hu hux hv hvx
    rcases le_total u v with huv | hvu
    · rw [abs_of_nonpos (sub_nonpos.mpr huv)]
      constructor
      · linarith only [hu, hvx]
      · apply abs_lt.mpr; constructor <;> linarith only [hu, hvx]
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      constructor
      · linarith only [hv, hux]
      · apply abs_lt.mpr; constructor <;> linarith only [hv, hux]
  have hbounds : ∀ p ∈ feasiblePairs upper x ζ B τ,
      |p.1 - p.2| ≤ w ∧ maxEntry (source upper x ζ p.1 - source upper x ζ p.2) ≤ S ∧
      (p.1 ≠ p.2 → |p.1 - p.2| < w ∧
        maxEntry (source upper x ζ p.1 - source upper x ζ p.2) < S) := by
    rintro ⟨u, v⟩ ⟨hu, hux, hv, hvx, hgap⟩
    dsimp only
    by_cases huv : u = v
    · subst v
      rw [hnorm]
      simp only [sub_self, abs_zero, zero_mul, zero_div, max_self]
      exact ⟨hw0, hS0, fun hn => False.elim (hn rfl)⟩
    · let l := |u - v|
      have hl : 0 < l := abs_pos.mpr (sub_ne_zero.mpr huv)
      obtain ⟨hlx, hz⟩ := hgeom u v hu hux hv hvx
      have htri : |D| ≤ |D + α * (x - u - v)| + α * |x - u - v| := by
        calc
          |D| = |(D + α * (x - u - v)) + -(α * (x - u - v))| := by congr 1; ring
          _ ≤ |D + α * (x - u - v)| + |-(α * (x - u - v))| := abs_add_le _ _
          _ = |D + α * (x - u - v)| + α * |x - u - v| := by
            rw [abs_neg, abs_mul, abs_of_pos hα]
      have hstrict : μ * l + α * l ^ 2 <
          l * |D + α * (x - u - v)| := by
        have hp := mul_pos hα (sub_pos.mpr hz)
        have hq := mul_pos hl hp
        have ht := mul_le_mul_of_nonneg_left htri hl.le
        rw [hD] at ht
        nlinarith only [hq, ht]
      rw [htrace] at hgap
      have hlt : μ * l + α * l ^ 2 < τ := lt_of_lt_of_le hstrict hgap
      have hlr : l < r := by
        by_contra hn
        have hrle : r ≤ l := le_of_not_gt hn
        have ht := mul_nonneg hμ0 (sub_nonneg.mpr hrle)
        have hq := mul_nonneg hα.le (mul_nonneg (sub_nonneg.mpr hrle)
          (by linarith only [hl, hr0] : 0 ≤ l + r))
        nlinarith only [ht, hq, hlt, hφr]
      have hlw : l < w := lt_min hlx hlr
      have hquad := hquadratic l hl.le hlw.le
      have hquadstrict : l * |x - u - v| / ζ < H := by
        apply lt_of_lt_of_le _ hquad
        exact (div_lt_div_iff_of_pos_right hζ).2 (mul_lt_mul_of_pos_left hz hl)
      have hlin : l < S := lt_of_lt_of_le hlw (le_max_left _ _)
      have hn : maxEntry (source upper x ζ u - source upper x ζ v) < S := by
        rw [hnorm]
        exact max_lt hlin (lt_of_lt_of_le hquadstrict (le_max_right _ _))
      exact ⟨hlw.le, hn.le, fun _ => ⟨hlw, hn⟩⟩
  have hequal : (x / 2, x / 2) ∈ feasiblePairs upper x ζ B τ := by
    exact ⟨by linarith only [hx], by linarith only [hx], by linarith only [hx],
      by linarith only [hx], by simpa using hτ⟩
  have hequalnorm : maxEntry (source upper x ζ (x / 2) - source upper x ζ (x / 2)) = 0 := by
    rw [hnorm]; simp
  have hscalar : scalarModulus upper x ζ B τ = w := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨0, ⟨(x / 2, x / 2), hequal, by simp⟩⟩
    · rintro a ⟨p, hp, rfl⟩
      exact (hbounds p hp).1
    · intro c hcw
      by_cases hc : c < 0
      · exact ⟨0, ⟨(x / 2, x / 2), hequal, by simp⟩, hc⟩
      · have hc0 : 0 ≤ c := le_of_not_gt hc
        let l := (c + w) / 2
        have hl : 0 < l := by dsimp [l]; linarith only [hc0, hcw]
        have hlw : l < w := by dsimp [l]; linarith only [hcw]
        have hlx : l < x := lt_of_lt_of_le hlw hwx
        obtain ⟨u, v, hp, huv, _⟩ := hpair l hl hlw 0 (by positivity)
        exact ⟨l, ⟨(u, v), hp, huv⟩, by dsimp [l]; linarith only [hcw]⟩
  have hmatrix : matrixModulus upper x ζ B τ = S := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨0, ⟨(x / 2, x / 2), hequal, hequalnorm⟩⟩
    · rintro a ⟨p, hp, rfl⟩
      exact (hbounds p hp).2.1
    · intro c hcS
      by_cases hc : c < 0
      · exact ⟨0, ⟨(x / 2, x / 2), hequal, hequalnorm⟩, hc⟩
      · have hc0 : 0 ≤ c := le_of_not_gt hc
        by_cases hcw : c < w
        · let l := (c + w) / 2
          have hl : 0 < l := by dsimp [l]; linarith only [hc0, hcw]
          have hlw : l < w := by dsimp [l]; linarith only [hcw]
          have hlx : l < x := lt_of_lt_of_le hlw hwx
          obtain ⟨u, v, hp, huv, _⟩ := hpair l hl hlw 0 (by positivity)
          refine ⟨maxEntry (source upper x ζ u - source upper x ζ v),
            ⟨(u, v), hp, rfl⟩, ?_⟩
          rw [hnorm, huv]
          apply lt_of_lt_of_le _ (le_max_left _ _)
          dsimp [l]; linarith only [hcw]
        · have hcH : c < H := by
            rw [hS, lt_max_iff] at hcS
            exact hcS.resolve_left hcw
          have hbpos : 0 < b := by
            by_contra hn
            have hb : b = 0 := le_antisymm (le_of_not_gt hn) hb0
            have hHzero : H = 0 := by simp [H, hb]
            linarith only [hcH, hHzero, hc0]
          let δ := min (b / 2) (ζ * (H - c) / (4 * x))
          let l := b - δ
          have hδ : 0 < δ := lt_min (by positivity)
            (div_pos (mul_pos hζ (sub_pos.mpr hcH)) (by positivity))
          have hδb : δ ≤ b / 2 := min_le_left _ _
          have hδH : δ ≤ ζ * (H - c) / (4 * x) := min_le_right _ _
          have hl : 0 < l := by dsimp [l]; linarith only [hbpos, hδb]
          have hlw : l < w := by dsimp [l]; linarith only [hδ, hbw]
          have hδbx : δ < b := by linarith only [hbpos, hδb]
          have hdiff : ζ * (H - l * (x - l) / ζ) = δ * (x - 2 * b + δ) := by
            dsimp [H, l]
            field_simp
            ring
          have hbudget := (le_div_iff₀ (by positivity : 0 < 4 * x)).mp hδH
          have hprod := mul_nonneg hδ.le (sub_nonneg.mpr hδbx.le)
          have hmargin : c < l * (x - l) / ζ := by
            have hbound : ζ * (H - l * (x - l) / ζ) ≤ δ * x := by
              nlinarith only [hdiff, hprod, mul_nonneg hδ.le hb0]
            have hm : ζ * c < ζ * (l * (x - l) / ζ) := by
              nlinarith only [hbound, hbudget, mul_pos hζ (sub_pos.mpr hcH)]
            exact (mul_lt_mul_iff_right₀ hζ).mp hm
          obtain ⟨u, v, hp, _, hn⟩ := hpair l hl hlw c hmargin
          exact ⟨maxEntry (source upper x ζ u - source upper x ζ v),
            ⟨(u, v), hp, rfl⟩, hn⟩
  have hpositive : 0 < τ → 0 < w ∧ 0 < S ∧
      ∀ p ∈ feasiblePairs upper x ζ B τ,
        |p.1 - p.2| < w ∧ maxEntry (source upper x ζ p.1 - source upper x ζ p.2) < S := by
    intro ht
    have hwp := hwpos ht
    have hSp : 0 < S := lt_of_lt_of_le hwp (le_max_left w H)
    refine ⟨hwp, hSp, ?_⟩
    intro p hp
    by_cases hpeq : p.1 = p.2
    · rw [hpeq, sub_self, abs_zero, hnorm, sub_self, abs_zero]
      simpa using And.intro hwp hSp
    · exact (hbounds p hp).2.2 hpeq
  have hzero : τ = 0 → scalarModulus upper x ζ B τ = 0 ∧ matrixModulus upper x ζ B τ = 0 ∧
      (x / 2, x / 2) ∈ feasiblePairs upper x ζ B τ ∧ |x / 2 - x / 2| = 0 ∧
      maxEntry (source upper x ζ (x / 2) - source upper x ζ (x / 2)) = 0 := by
    intro ht
    have hr : r = 0 := by
      by_contra hn
      have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hn)
      have hq := mul_pos hα (sq_pos_of_pos hrp)
      have hm := mul_nonneg hμ0 hr0
      rw [ht] at hφr
      nlinarith only [hq, hm, hφr]
    have hw : w = 0 := by simp [w, hr, hx.le]
    have hSz : S = 0 := by simp [S, geometry, hw, min_eq_left (by positivity : 0 ≤ x / 2)]
    exact ⟨hscalar.trans hw, hmatrix.trans hSz, hequal, by simp, hequalnorm⟩
  exact ⟨hword, List.length_append, fun _ => rfl, hfactor, hreads, hfiber, hα, hr0, hφr,
    hw0, hwx, hφw, hwpos, htrace, hnorm, hpair, hscalar, hmatrix, hpositive, hzero⟩

end D5.S3.Observer.TraceFibers.FixedFiberPairModulus
