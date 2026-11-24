/- GID: D5/S3/Arith/ModularForms/RademacherVacuum
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/RademacherVacuum
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Rectangular Rademacher vacuum cutoffs and compact summability of the quadratic remainder. -/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Tactic

/-!
# The quadratic remainder of the Rademacher vacuum sum

For the polar seed $q^{-1}$, split the normalized summand at each primitive bottom row
into its linear exponential term and its quadratic remainder. On any compact subset of
the upper half-plane, the latter is dominated by a constant times the summable product
of $1/c^2$ and $1/\max(1,d^2)$. The linear term uses the rectangular cutoff.
-/

open Filter
open scoped BigOperators Matrix Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherVacuum

/-- The primitive bottom rows with `0 < c < N` and `|d| < N^2`. -/
def cutoffPairs (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Ioo 0 (N : ℤ)).product
    (Finset.Ioo (-((N : ℤ) ^ 2)) ((N : ℤ) ^ 2))).filter
      fun p => Int.gcd p.1 p.2 = 1

theorem mem_cutoffPairs {N : ℕ} {c d : ℤ} :
    (c, d) ∈ cutoffPairs N ↔
      0 < c ∧ c < (N : ℤ) ∧ |d| < (N : ℤ) ^ 2 ∧ Int.gcd c d = 1 := by
  simp only [cutoffPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Ioo, abs_lt]
  tauto

/-- The extended-GCD coefficient of `d`, reduced modulo `c`.
For `c = 1` the residue is zero. -/
def inverseResidue (c d : ℤ) : ℤ :=
  Int.gcdB c d % c

theorem inverseResidue_spec {c d : ℤ} (hc : 0 < c) (hprimitive : Int.gcd c d = 1) :
    0 ≤ inverseResidue c d ∧ inverseResidue c d < c ∧
      d * inverseResidue c d ≡ 1 [ZMOD c] := by
  refine ⟨Int.emod_nonneg _ (ne_of_gt hc), Int.emod_lt_of_pos _ hc, ?_⟩
  refine ((Int.mod_modEq (Int.gcdB c d) c).mul_left d).trans ?_
  apply Int.modEq_iff_dvd.mpr
  have hbez : (1 : ℤ) = c * Int.gcdA c d + d * Int.gcdB c d := by
    simpa only [hprimitive, Nat.cast_one] using Int.gcd_eq_gcd_ab c d
  exact ⟨Int.gcdA c d, by rw [hbez, add_sub_cancel_right]⟩

noncomputable section

/-- The automorphy denominator for the bottom row `(c, d)`. -/
def denominator (c d : ℤ) (τ : ℍ) : ℂ :=
  (c : ℂ) * (τ : ℂ) + (d : ℂ)

/-- The difference of the vacuum exponents at `τ` and at the cusp. -/
def vacuumArgument (c d : ℤ) (τ : ℍ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * Complex.I / ((c : ℂ) * denominator c d τ)

/-- The phase determined by the inverse residue. -/
def vacuumPhase (c d : ℤ) : ℂ :=
  Complex.exp (((-2 * Real.pi * (inverseResidue c d : ℝ) / (c : ℝ) : ℝ) : ℂ) * Complex.I)

theorem norm_vacuumPhase (c d : ℤ) : ‖vacuumPhase c d‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The normalized nonidentity vacuum summand. -/
def vacuumSummand (c d : ℤ) (τ : ℍ) : ℂ :=
  vacuumPhase c d * (Complex.exp (vacuumArgument c d τ) - 1)

/-- The first-order term of the normalized summand. -/
def linearSummand (c d : ℤ) (τ : ℍ) : ℂ :=
  vacuumPhase c d * vacuumArgument c d τ

/-- The remainder after removal of the constant and linear exponential terms. -/
def quadraticRemainder (c d : ℤ) (τ : ℍ) : ℂ :=
  vacuumPhase c d * (Complex.exp (vacuumArgument c d τ) - 1 - vacuumArgument c d τ)

/-- The finite first-order contribution at the original rectangular cutoff. -/
def linearCutoff (N : ℕ) (τ : ℍ) : ℂ :=
  ∑ p ∈ cutoffPairs N, linearSummand p.1 p.2 τ

/-- The finite quadratic contribution at the original rectangular cutoff. -/
def remainderCutoff (N : ℕ) (τ : ℍ) : ℂ :=
  ∑ p ∈ cutoffPairs N, quadraticRemainder p.1 p.2 τ

/-- The rectangular Rademacher vacuum sum with its identity contribution. -/
def rademacherCutoff (N : ℕ) (τ : ℍ) : ℂ :=
  Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) +
    ∑ p ∈ cutoffPairs N, vacuumSummand p.1 p.2 τ

theorem rademacherCutoff_eq (N : ℕ) (τ : ℍ) :
    rademacherCutoff N τ =
      Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) +
        linearCutoff N τ + remainderCutoff N τ := by
  have hsplit (p : ℤ × ℤ) :
      vacuumSummand p.1 p.2 τ = linearSummand p.1 p.2 τ + quadraticRemainder p.1 p.2 τ := by
    unfold vacuumSummand linearSummand quadraticRemainder
    ring
  simp only [rademacherCutoff, linearCutoff, remainderCutoff, hsplit,
    Finset.sum_add_distrib, add_assoc]

private theorem im_mul_le_norm_denominator (c d : ℤ) (τ : ℍ) :
    (c : ℝ) * τ.im ≤ ‖denominator c d τ‖ := by
  simpa [denominator, ← Complex.ofReal_intCast, Complex.im_ofReal_mul] using
    Complex.im_le_norm (denominator c d τ)

private theorem norm_vacuumArgument {c : ℤ} (hc : 0 < c) (d : ℤ) (τ : ℍ) :
    ‖vacuumArgument c d τ‖ = (2 * Real.pi) / ((c : ℝ) * ‖denominator c d τ‖) := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  simp only [vacuumArgument, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_of_nonneg hπ, Complex.norm_int_of_nonneg hc.le]

private theorem norm_vacuumArgument_le {c : ℤ} (hc : 0 < c) (d : ℤ) (τ : ℍ)
    {η : ℝ} (hη : 0 < η) (hτ : η ≤ τ.im) :
    ‖vacuumArgument c d τ‖ ≤ 2 * Real.pi / η := by
  have hc' : (1 : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ c by omega)
  have hnorm : η ≤ ‖denominator c d τ‖ :=
    hτ.trans ((le_mul_of_one_le_left τ.im_pos.le hc').trans
      (im_mul_le_norm_denominator c d τ))
  have hden : η ≤ (c : ℝ) * ‖denominator c d τ‖ :=
    hnorm.trans (le_mul_of_one_le_left (norm_nonneg _) hc')
  rw [norm_vacuumArgument hc]
  exact div_le_div_of_nonneg_left (by positivity) hη hden

/-- A quadratic pointwise estimate using any positive lower bound on `τ.im`. -/
theorem norm_quadraticRemainder_le {c : ℤ} (hc : 0 < c) (d : ℤ) (τ : ℍ)
    {η : ℝ} (hη : 0 < η) (hτ : η ≤ τ.im) :
    ‖quadraticRemainder c d τ‖ ≤
      (2 * Real.pi) ^ 2 * Real.exp (2 * Real.pi / η) /
        ((c : ℝ) ^ 2 * ‖denominator c d τ‖ ^ 2) := by
  let z := vacuumArgument c d τ
  have htail : (∑ m ∈ Finset.range 2, z ^ m / (m.factorial : ℂ)) = 1 + z := by
    rw [Finset.sum_range_succ _ 1, Finset.sum_range_one]
    simp
  calc
    ‖quadraticRemainder c d τ‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
      change ‖vacuumPhase c d * (Complex.exp z - 1 - z)‖ ≤ _
      rw [norm_mul, norm_vacuumPhase, one_mul, sub_sub, ← htail]
      exact Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
    _ ≤ ‖z‖ ^ 2 * Real.exp (2 * Real.pi / η) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (norm_vacuumArgument_le hc d τ hη hτ)) (sq_nonneg _)
    _ = _ := by
      dsimp only [z]
      rw [norm_vacuumArgument hc, div_pow, mul_pow (c : ℝ) ‖denominator c d τ‖ 2]
      simp only [div_eq_mul_inv]
      ring

/-- The separated majorant on the integer lattice. Its `c = 0` value is zero. -/
def remainderWeight (p : ℤ × ℤ) : ℝ :=
  (1 / (p.1 : ℝ) ^ 2) * (1 / max 1 ((p.2 : ℝ) ^ 2))

private theorem summable_remainderWeight : Summable remainderWeight := by
  have hc : Summable (fun c : ℤ => 1 / (c : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide)
  have hd : Summable (fun d : ℤ => 1 / max 1 ((d : ℝ) ^ 2)) := by
    apply hc.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with d hd
    have hd' : (1 : ℝ) ≤ |(d : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hd)
    have hdSq : (1 : ℝ) ≤ (d : ℝ) ^ 2 :=
      (one_le_sq_iff_one_le_abs _).mpr hd'
    rw [max_eq_right hdSq]
  exact hc.mul_of_nonneg hd (fun c => by positivity)
    (fun d => div_nonneg zero_le_one ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left _ _)))

private theorem strip_denominator_sq_bound {A η : ℝ} (hη : 0 < η) {τ : ℍ}
    (hτ : τ ∈ UpperHalfPlane.verticalStrip A η) {c : ℤ} (hc : 0 < c) (d : ℤ) :
    EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ ^ 2 * max 1 ((d : ℝ) ^ 2) ≤
      ‖denominator c d τ‖ ^ 2 := by
  let x : Fin 2 → ℤ := ![c, d]
  have hx : x ≠ 0 := by
    intro he
    have hcZero : c = 0 := by simpa [x] using congrFun he (0 : Fin 2)
    exact (ne_of_gt hc) hcZero
  have hc' : (1 : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ c by omega)
  have hcNorm : (c : ℝ) ≤ ‖x‖ := by
    simpa only [x, abs_of_pos hc, Int.cast_abs, abs_of_pos (zero_lt_one.trans_le hc')] using
      EisensteinSeries.abs_le_left_of_norm d c
  have hdNorm : |(d : ℝ)| ≤ ‖x‖ := by
    simpa only [x, Int.cast_abs] using EisensteinSeries.abs_le_right_of_norm d c
  have hmax : max 1 ((d : ℝ) ^ 2) ≤ ‖x‖ ^ 2 := by
    refine max_le ?_ ?_
    · simpa only [one_pow] using
        pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) (hc'.trans hcNorm) 2
    · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdNorm 2
  have hlinear : EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ * ‖x‖ ≤ ‖denominator c d τ‖ := by
    have hstrip := EisensteinSeries.r_lower_bound_on_verticalStrip τ hη hτ
    refine (mul_le_mul_of_nonneg_right hstrip (norm_nonneg x)).trans ?_
    simpa [x, denominator] using EisensteinSeries.r_mul_max_le τ hx
  calc
    _ ≤ EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmax (sq_nonneg _)
    _ = (EisensteinSeries.r ⟨⟨A, η⟩, hη⟩ * ‖x‖) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ _ := pow_le_pow_left₀
      (mul_nonneg (EisensteinSeries.r_pos _).le (norm_nonneg _)) hlinear 2

/-- A single summable majorant works throughout each compact set and for every positive
bottom-left entry. In particular it bounds all primitive rows in every rectangular cutoff. -/
theorem quadraticRemainder_compact_majorant {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ Summable (fun p : ℤ × ℤ => C * remainderWeight p) ∧
      ∀ τ ∈ K, ∀ c d : ℤ, 0 < c → ‖quadraticRemainder c d τ‖ ≤ C * remainderWeight (c, d) := by
  obtain ⟨A, η, hη, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  let r := EisensteinSeries.r ⟨⟨A, η⟩, hη⟩
  have hr : 0 < r := EisensteinSeries.r_pos _
  let B := (2 * Real.pi) ^ 2 * Real.exp (2 * Real.pi / η)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B / r ^ 2, div_pos hB (pow_pos hr _), summable_remainderWeight.mul_left _, ?_⟩
  intro τ hτ c d hc
  have hcReal : 0 < (c : ℝ) := by exact_mod_cast hc
  have hτ' := hstrip hτ
  have him : η ≤ τ.im := ((UpperHalfPlane.mem_verticalStrip_iff A η τ).mp hτ').2
  have hden : r ^ 2 * max 1 ((d : ℝ) ^ 2) ≤ ‖denominator c d τ‖ ^ 2 :=
    strip_denominator_sq_bound hη hτ' hc d
  have hd : (0 : ℝ) < max 1 ((d : ℝ) ^ 2) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hpositive : 0 < (c : ℝ) ^ 2 * (r ^ 2 * max 1 ((d : ℝ) ^ 2)) :=
    mul_pos (pow_pos hcReal _) (mul_pos (pow_pos hr _) hd)
  calc
    ‖quadraticRemainder c d τ‖ ≤ B / ((c : ℝ) ^ 2 * ‖denominator c d τ‖ ^ 2) :=
      norm_quadraticRemainder_le hc d τ hη him
    _ ≤ B / ((c : ℝ) ^ 2 * (r ^ 2 * max 1 ((d : ℝ) ^ 2))) :=
      div_le_div_of_nonneg_left hB.le hpositive
        (mul_le_mul_of_nonneg_left hden (sq_nonneg _))
    _ = B / r ^ 2 * remainderWeight (c, d) := by
      simp only [remainderWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

/-- Bottom rows with positive first entry and coprime entries. -/
abbrev PrimitiveRow := {p : ℤ × ℤ // 0 < p.1 ∧ Int.gcd p.1 p.2 = 1}

/-- The literal rectangle viewed as a finite subset of the primitive positive rows. -/
def cutoffRows (N : ℕ) : Finset PrimitiveRow :=
  (cutoffPairs N).subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1)

theorem mem_cutoffRows {N : ℕ} {p : PrimitiveRow} :
    p ∈ cutoffRows N ↔ (p : ℤ × ℤ) ∈ cutoffPairs N :=
  Finset.mem_subtype

theorem eventually_mem_cutoffPairs (p : PrimitiveRow) :
    ∀ᶠ N : ℕ in atTop, (p : ℤ × ℤ) ∈ cutoffPairs N := by
  rcases p with ⟨⟨c, d⟩, hc, hprim⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max c |d|)
  filter_upwards [eventually_ge_atTop n] with N hN
  have hcast : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmax := hn.trans_le hcast
  exact mem_cutoffPairs.mpr
    ⟨hc, (le_max_left _ _).trans_lt hmax,
      ((le_max_right _ _).trans_lt hmax).trans_le (Int.le_self_sq _), hprim⟩

/-- Every finite set of primitive positive rows lies in all sufficiently large rectangles. -/
theorem tendsto_cutoffRows : Tendsto cutoffRows atTop atTop := by
  refine tendsto_atTop.2 (fun s => ?_)
  have h : ∀ᶠ N in atTop, ∀ p ∈ s, p ∈ cutoffRows N :=
    s.eventually_all.2 (fun p _ =>
      (eventually_mem_cutoffPairs p).mono (fun _ hp => mem_cutoffRows.mpr hp))
  exact h.mono (fun _ hN p hp => hN p hp)

/-- The sum of quadratic remainders indexed by the primitive positive rows. -/
def remainderLimit (τ : ℍ) : ℂ :=
  ∑' p : PrimitiveRow, quadraticRemainder p.val.1 p.val.2 τ

theorem summable_norm_quadraticRemainder (τ : ℍ) :
    Summable (fun p : PrimitiveRow => ‖quadraticRemainder p.val.1 p.val.2 τ‖) := by
  obtain ⟨C, _, hsum, hbound⟩ :=
    quadraticRemainder_compact_majorant (isCompact_singleton (x := τ))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => hbound τ (Set.mem_singleton τ) p.val.1 p.val.2 p.property.1)
    (hsum.subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1))

/-- The M-test along the literal cutoff `cutoffPairs N`. -/
theorem tendstoUniformlyOn_remainderCutoff {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn remainderCutoff remainderLimit atTop K := by
  obtain ⟨C, _, hsum, hbound⟩ := quadraticRemainder_compact_majorant hK
  have hM := tendstoUniformlyOn_tsum
    (f := fun (p : PrimitiveRow) (τ : ℍ) => quadraticRemainder p.val.1 p.val.2 τ)
    (s := K) (hsum.subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1))
    (fun p τ hτ => hbound τ hτ p.val.1 p.val.2 p.property.1)
  have hcut : TendstoUniformlyOn
      (fun N τ => ∑ p ∈ cutoffRows N, quadraticRemainder p.val.1 p.val.2 τ)
      remainderLimit atTop K :=
    fun u hu => tendsto_cutoffRows.eventually (hM u hu)
  apply hcut.congr
  refine Eventually.of_forall (fun N τ _ => ?_)
  exact Finset.sum_subtype_of_mem (fun p : ℤ × ℤ => quadraticRemainder p.1 p.2 τ)
    (fun ⟨c, d⟩ hp =>
      ⟨(mem_cutoffPairs.mp hp).1, (mem_cutoffPairs.mp hp).2.2.2⟩)

/-- The quadratic cutoff is locally uniform on the upper half-plane. -/
theorem tendstoLocallyUniformly_remainderCutoff :
    TendstoLocallyUniformly remainderCutoff remainderLimit atTop :=
  tendstoLocallyUniformly_iff_forall_isCompact.mpr
    (fun _ hK => tendstoUniformlyOn_remainderCutoff hK)

end

end D5.S3.Arith.ModularForms.RademacherVacuum
