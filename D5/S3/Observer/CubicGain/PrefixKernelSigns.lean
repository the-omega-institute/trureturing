/- GID: D5/S3/Observer/CubicGain/PrefixKernelSigns
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/PrefixKernelSigns
   mirror-E: none(waiver:uniform-legal-prefix-kernel-geometry)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: Oriented rank-one legal-prefix kernels have signed entries and positive trace, and the full prefix trace map is invertible. -/

import D5.S3.Observer.CubicGain.LegalMatrixMonoid
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Whole-class kernel geometry for three arbitrary cumulative native words. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.PrefixKernelSigns

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open scoped Matrix

/-- The first i chronological multipliers, concatenated without a length bound. -/
def prefixWord (w : Fin 3 → List Bool) (i : Fin 4) : List Bool :=
  ((List.ofFn w).take i.val).flatten

/-- Actual cumulative endpoints, with index zero equal to the identity. -/
def prefixMatrix (w : Fin 3 → List Bool) (i : Fin 4) : Mat :=
  futureProduct (prefixWord w i)

/-- The original three prefix differences, indexed by the endpoints 1,2,3. -/
def prefixDifference (w : Fin 3 → List Bool) : Mat →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X i := Matrix.trace (prefixMatrix w i.succ * X) - Matrix.trace X
  map_add' X Y := by ext i; simp [Matrix.mul_add, Matrix.trace_add]; ring
  map_smul' c X := by ext i; simp [Matrix.mul_smul, Matrix.trace_smul]; ring

/-- All four original traces, on the entire real matrix space. -/
def prefixTrace (w : Fin 3 → List Bool) : Mat →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun X i := Matrix.trace (prefixMatrix w i * X)
  map_add' X Y := by ext i; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by ext i; simp [Matrix.mul_smul, Matrix.trace_smul]

/-- The determinant polar on full real matrices. -/
def determinantPolar (X Y : Mat) : ℝ := (X + Y).det - X.det - Y.det

/-- Strictly positive entries and actual matrix rank one. -/
def PositiveRankOne (S : Mat) : Prop := (∀ i j, 0 < S i j) ∧ S.rank = 1

/-- An arbitrary positively oriented generator of the original class G.
No signs, trace conclusion or trace-map injectivity are assumed. -/
structure OrientedKernelGenerator (w : Fin 3 → List Bool) (N : Mat) : Prop where
  nonzero : N ≠ 0
  rank_one : N.rank = 1
  kernel_line : ∀ X, prefixDifference w X = 0 ↔ ∃ v : ℝ, X = v • N
  positive_polar : ∀ S, PositiveRankOne S → 0 < determinantPolar S N

private theorem affine_halfline {a b : ℝ}
    (h : ∀ x : ℝ, 0 < x → 0 ≤ a + b * x) : 0 ≤ a ∧ 0 ≤ b := by
  have hb : 0 ≤ b := by
    by_contra hn
    have hb : b < 0 := lt_of_not_ge hn
    let x := (|a| + 1) / (-b)
    have hx : 0 < x := div_pos (by positivity) (by linarith)
    have he : b * x = -(|a| + 1) := by
      dsimp [x]
      field_simp [ne_of_lt hb]
      <;> ring
    have hh := h x hx
    rw [he] at hh
    linarith [le_abs_self a]
  refine ⟨?_, hb⟩
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  let x := (-a) / (2 * (b + 1))
  have hx : 0 < x := div_pos (by linarith) (by positivity)
  have he : x * (2 * (b + 1)) = -a :=
    div_mul_cancel₀ _ (by positivity)
  have hh := h x hx
  nlinarith

private theorem positive_test (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    PositiveRankOne (!![u*v,u;v,1] : Mat) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp <;> positivity
  · let S : Mat := !![u*v,u;v,1]
    have he : S = Matrix.vecMulVec (![u,1] : Fin 2 → ℝ) (![v,1] : Fin 2 → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.vecMulVec]
    have hle : S.rank ≤ 1 := by rw [he]; exact Matrix.rank_vecMulVec_le _ _
    have hs : S.submatrix (fun _ : Fin 1 => (1 : Fin 2))
        (fun _ : Fin 1 => (1 : Fin 2)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [S, Matrix.submatrix]
    have hge := Matrix.rank_submatrix_le S (fun _ : Fin 1 => (1 : Fin 2))
      (fun _ : Fin 1 => (1 : Fin 2))
    rw [hs, Matrix.rank_one] at hge
    change S.rank = 1
    norm_num at hge
    omega

private theorem polar_signs {w : Fin 3 → List Bool} {N : Mat}
    (h : OrientedKernelGenerator w N) :
    0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0 := by
  have hp (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      0 < (N 0 0 - N 1 0 * u) + (N 1 1 * u - N 0 1) * v := by
    have hh := h.positive_polar _ (positive_test u v hu hv)
    simp [determinantPolar, Matrix.det_fin_two] at hh
    nlinarith
  have hab (u : ℝ) (hu : 0 < u) := affine_halfline (fun v hv => (hp u v hu hv).le)
  have ha := affine_halfline (a := N 0 0) (b := -N 1 0) (by
    intro u hu
    simpa only [neg_mul, sub_eq_add_neg] using (hab u hu).1)
  have hb := affine_halfline (a := -N 0 1) (b := N 1 1) (by
    intro u hu
    linarith [(hab u hu).2])
  exact ⟨ha.1, hb.2, by linarith [hb.1], by linarith [ha.2]⟩

private theorem triangular_diagonals (u : List Bool)
    (ht : futureProduct u 0 1 * futureProduct u 1 0 = 0) :
    futureProduct u 0 0 = 1 ∧ futureProduct u 1 1 = 1 := by
  obtain ⟨he, hd⟩ := (legal_matrix_monoid (futureProduct u)).mp ⟨u, rfl⟩
  obtain ⟨ha, a, haeq⟩ := he 0 0
  obtain ⟨hdn, d, hdeq⟩ := he 1 1
  have hprod : futureProduct u 0 0 * futureProduct u 1 1 = 1 := by
    rcases hd with hd | hd <;> rw [Matrix.det_fin_two, ht, sub_zero] at hd
    · exact hd
    · nlinarith [mul_nonneg ha hdn]
  have ha0 : (0 : ℤ) ≤ a := by exact_mod_cast (haeq ▸ ha)
  have hd0 : (0 : ℤ) ≤ d := by exact_mod_cast (hdeq ▸ hdn)
  have had : a * d = (1 : ℤ) := by
    rw [haeq, hdeq] at hprod
    exact_mod_cast hprod
  have hane : a ≠ 0 := by intro hz; simp [hz] at had
  have hdne : d ≠ 0 := by intro hz; simp [hz] at had
  have ha1 : 1 ≤ a := by omega
  have hd1 : 1 ≤ d := by omega
  have hae : a = 1 := by nlinarith
  have hde : d = 1 := by nlinarith
  simp [haeq, hdeq, hae, hde]

private theorem positive_trace {w : Fin 3 → List Bool} {N : Mat}
    (h : OrientedKernelGenerator w N)
    (hs : 0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0) :
    0 < Matrix.trace N := by
  by_contra hn
  have ht : N 0 0 + N 1 1 ≤ 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using le_of_not_gt hn
  have h00 : N 0 0 = 0 := by linarith [hs.1, hs.2.1]
  have h11 : N 1 1 = 0 := by linarith [hs.1, hs.2.1]
  have hsome : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply h.nonzero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, hh.1, hh.2]
  have hker : prefixDifference w N = 0 :=
    (h.kernel_line N).mpr ⟨1, by simp⟩
  have hdiag (i : Fin 3) : prefixMatrix w i.succ 0 0 = 1 ∧
      prefixMatrix w i.succ 1 1 = 1 := by
    let A := prefixMatrix w i.succ
    have he := ((legal_matrix_monoid A).mp ⟨prefixWord w i.succ, rfl⟩).1
    have hlevel := congrFun hker i
    change Matrix.trace (A * N) - Matrix.trace N = 0 at hlevel
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
      Pi.zero_apply, h00, h11, mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hlevel
    have htA : A 0 1 * A 1 0 = 0 := by
      rcases hsome with hb | hc
      · have hbneg : N 0 1 < 0 := lt_of_le_of_ne hs.2.2.1 hb
        have hp := mul_nonpos_of_nonneg_of_nonpos (he 0 1).1 hs.2.2.2
        have hz : A 1 0 = 0 := by nlinarith [(he 1 0).1]
        simp [hz]
      · have hcneg : N 1 0 < 0 := lt_of_le_of_ne hs.2.2.2 hc
        have hp := mul_nonpos_of_nonneg_of_nonpos (he 1 0).1 hs.2.2.1
        have hz : A 0 1 = 0 := by nlinarith [(he 0 1).1]
        simp [hz]
    exact triangular_diagonals (prefixWord w i.succ) htA
  let E : Mat := !![1,0;0,0]
  have hE : prefixDifference w E = 0 := by
    ext i
    change Matrix.trace (prefixMatrix w i.succ * E) - Matrix.trace E = 0
    simp [E, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, (hdiag i).1]
  obtain ⟨v, hv⟩ := (h.kernel_line E).mp hE
  have hz := congrArg (fun X : Mat => X 0 0) hv
  norm_num [E, h00] at hz

/-- Every actual legal cumulative prefix in G has the full sign pattern,
strictly positive generator trace, and a bijective four-index trace map. -/
theorem kernel_signs_positive_trace_invertible
    (w : Fin 3 → List Bool) (N : Mat) (h : OrientedKernelGenerator w N) :
    (0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0) ∧
      0 < Matrix.trace N ∧ Function.Bijective (prefixTrace w) := by
  have hs := polar_signs h
  have ht := positive_trace h hs
  refine ⟨hs, ht, ?_⟩
  have hinj : Function.Injective (prefixTrace w) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro X hX
      change prefixTrace w X = 0 at hX
      have hx0 := congrFun hX 0
      have htr : Matrix.trace X = 0 := by
        simpa [prefixTrace, prefixMatrix, prefixWord, futureProduct] using hx0
      have hdiff : prefixDifference w X = 0 := by
        ext i
        have hi := congrFun hX i.succ
        change Matrix.trace (prefixMatrix w i.succ * X) - Matrix.trace X = 0
        change Matrix.trace (prefixMatrix w i.succ * X) = 0 at hi
        rw [hi, htr, sub_self]
      obtain ⟨v, rfl⟩ := (h.kernel_line X).mp hdiff
      have hv : v = 0 := by
        rw [Matrix.trace_smul] at htr
        simp only [smul_eq_mul] at htr
        exact (mul_eq_zero.mp htr).resolve_right (ne_of_gt ht)
      simp [hv]
    · exact bot_le
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := prefixTrace w) ?_).mp hinj
  simp [Mat, Module.finrank_matrix]

#print axioms kernel_signs_positive_trace_invertible


end D5.S3.Observer.CubicGain.PrefixKernelSigns
