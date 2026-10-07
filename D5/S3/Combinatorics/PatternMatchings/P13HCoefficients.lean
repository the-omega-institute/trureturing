/- GID: D5/S3/Combinatorics/PatternMatchings/P13HCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13HCoefficients
   mirror-E: none(waiver:actual-catalytic-coefficient-extraction)
   anchors: []
   utility: none
   digest: The actual transformed matching series has triangular support and exact boundary and bulk coefficient laws. -/
import D5.S3.Combinatorics.PatternMatchings.P13CatalyticH
import D5.S3.Combinatorics.PatternMatchings.P13Scalar
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH
open PowerSeries PowerSeries.WithPiTopology
open scoped PowerSeries.WithPiTopology BigOperators
local instance : UniformSpace ℚ := ⊥
local instance : UniformSpace (Polynomial ℚ) := ⊥
abbrev PS := PowerSeries ℚ
local notation "Q" => (PowerSeries.X : PS)

/-- Embed a series without an inner marker. -/
def scalarEmbed : PS →+* S := PowerSeries.map Polynomial.C

/-- Transpose a fixed inner coefficient into an ordinary q-series. -/
def row (k : ℕ) : S →+ PS where
  toFun f := PowerSeries.mk fun n => (PowerSeries.coeff n f).coeff k
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

@[simp] theorem coeff_row (k n : ℕ) (f : S) :
    PowerSeries.coeff n (row k f) = (PowerSeries.coeff n f).coeff k := by simp [row]

theorem row_scalar_mul (k : ℕ) (a : PS) (f : S) :
    row k (scalarEmbed a * f) = a * row k f := by
  ext n
  simp only [coeff_row, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff,
    scalarEmbed, PowerSeries.coeff_map, Polynomial.coeff_C_mul]

theorem row_t_mul_zero (f : S) : row 0 (t*f) = 0 := by
  ext n
  simp [t, coeff_row, PowerSeries.coeff_C_mul]

theorem row_t_mul_succ (k : ℕ) (f : S) : row (k+1) (t*f) = row k f := by
  ext n
  simp [t, coeff_row, PowerSeries.coeff_C_mul]

@[simp] theorem scalarEmbed_Q : scalarEmbed Q = q := by simp [scalarEmbed, q]
@[simp] theorem scalarEmbed_C (r : ℚ) : scalarEmbed (C r) = C (Polynomial.C r) := by
  simp [scalarEmbed]

private theorem polynomial_shift (p : Polynomial ℚ) :
    Polynomial.eval₂RingHom (C.comp Polynomial.C) (q*t) p =
      PowerSeries.rescale Polynomial.X (scalarEmbed (p : PS)) := by
  have he : Polynomial.eval₂RingHom (C.comp Polynomial.C) (q*t) =
      (PowerSeries.rescale Polynomial.X).comp
        (scalarEmbed.comp Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, scalarEmbed]
      apply PowerSeries.ext
      intro n
      by_cases hn : n=0 <;> simp [PowerSeries.coeff_C, hn]
    · simp [q, t, scalarEmbed, PowerSeries.rescale_X, mul_comm]
  exact DFunLike.congr_fun he p

private theorem shift_coeff (f : S) (N : ℕ) :
    PowerSeries.coeff N (shift f) =
      ∑ d ∈ Finset.range (N+1), Polynomial.monomial (N-d)
        ((PowerSeries.coeff d f).coeff (N-d)) := by
  classical
  let e : Polynomial ℚ →+* S := Polynomial.eval₂RingHom (C.comp Polynomial.C) (q*t)
  have hs := (hasSum_iff_hasSum_coeff (Polynomial ℚ)).mp
    (hasSum_eval₂ (show Continuous e from continuous_of_discreteTopology)
      (HasEval.X (R := Polynomial ℚ)) f) N
  have hf := hasSum_sum_of_ne_finset_zero
    (L := SummationFilter.unconditional ℕ) (s := Finset.range (N+1))
    (f := fun d => PowerSeries.coeff N (e (PowerSeries.coeff d f) * X^d))
    (by intro d hd; rw [PowerSeries.coeff_mul_X_pow', if_neg];
        simp only [Finset.mem_range] at hd; omega)
  have he : PowerSeries.coeff N (shift f) =
      ∑ d ∈ Finset.range (N+1),
        PowerSeries.coeff N (e (PowerSeries.coeff d f) * X^d) := by
    change PowerSeries.coeff N (jointEval (q*t) X (HasEval.X (R := Polynomial ℚ)) f) = _
    simp only [jointEval, coe_eval₂Hom]
    with_unfolding_all exact hs.unique hf
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd
  have hdN : d ≤ N := by have hd' := Finset.mem_range.mp hd; omega
  rw [PowerSeries.coeff_mul_X_pow', if_pos hdN]
  rw [show e (PowerSeries.coeff d f) =
    PowerSeries.rescale Polynomial.X (scalarEmbed ((PowerSeries.coeff d f : Polynomial ℚ) : PS))
    from polynomial_shift _]
  simp only [PowerSeries.coeff_rescale, scalarEmbed, PowerSeries.coeff_map,
    Polynomial.coeff_coe]
  rw [mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

/-- The actual substitution t -> qt acts diagonally on transposed coefficients. -/
theorem row_shift (k : ℕ) (f : S) : row k (shift f) = Q^k * row k f := by
  classical
  ext N
  rw [coeff_row, shift_coeff, Polynomial.finsetSum_coeff, PowerSeries.coeff_X_pow_mul']
  simp only [Polynomial.coeff_monomial]
  by_cases hk : k ≤ N
  · rw [if_pos hk, Finset.sum_eq_single (N-k)]
    · simp [show N-(N-k)=k by omega, coeff_row]
    · intro d hd hne
      have hdN := Finset.mem_range.mp hd
      rw [if_neg (by omega : N-d ≠ k)]
    · intro hd
      exact (hd (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg (by omega : N-d ≠ k)]

/-- The actual coefficients, rather than a family defined by a recurrence. -/
def h (k : ℕ) : PS := row k H

/-- The inverse exists because 1+q has constant coefficient one. -/
def invPlus : PS := PowerSeries.invOfUnit (1+Q) 1
theorem invPlus_unit : (1+Q)*invPlus = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ (by simp)

/-- The legitimate zero-constant substitution q/(1+q)^2. -/
def Z : PS := Q*invPlus^2
theorem Z_hasEval : HasEval Z :=
  HasEval.mul_right (invPlus^2) (HasEval.X (R := ℚ))
theorem Z_clear : Z*(1+Q)^2 = Q := by
  calc
    _ = Q*((1+Q)*invPlus)^2 := by unfold Z; ring
    _ = Q := by rw [invPlus_unit]; ring

private theorem embed_invPlus : scalarEmbed invPlus = invCq := by
  have ha : Cq * scalarEmbed invPlus = 1 := by
    simpa [map_mul, Cq] using congrArg scalarEmbed invPlus_unit
  have hb := catalytic_H_bridge.1
  calc
    scalarEmbed invPlus = scalarEmbed invPlus*(Cq*invCq) := by rw [hb, mul_one]
    _ = (Cq*scalarEmbed invPlus)*invCq := by ring
    _ = invCq := by rw [ha, one_mul]

theorem scalarEmbed_Z : scalarEmbed Z = zeta := by
  simp only [Z, zeta, map_mul, map_pow, scalarEmbed_Q, embed_invPlus]

private theorem continuous_scalarEmbed : Continuous scalarEmbed := by
  rw [continuous_iff_continuousAt]
  intro a
  apply (tendsto_iff_coeff_tendsto (Polynomial ℚ) _ _ _).mpr
  intro d
  simp only [scalarEmbed, PowerSeries.coeff_map]
  exact (continuous_of_discreteTopology : Continuous (Polynomial.C : ℚ → Polynomial ℚ)).continuousAt.comp
    (continuous_coeff ℚ d).continuousAt

/-- A(zeta), evaluated on the actual perfect-matching counting series. -/
def A : PS := eval₂Hom (show Continuous (C : ℚ →+* PS) from PowerSeries.WithPiTopology.continuous_C)
  Z_hasEval actualSeries

/-- The supplier's embedded Aq is exactly the actual A-series at zeta. -/
theorem Aq_actual : Aq = scalarEmbed A := by
  let e : Polynomial ℚ →+* S := Polynomial.eval₂RingHom (C.comp Polynomial.C) (u t)
  have hz : HasEval zeta := HasEval.mul_right (invCq^2) (HasEval.X (R := Polynomial ℚ))
  have hs := hasSum_eval₂ (show Continuous e from continuous_of_discreteTopology) hz
    (actualSeries.map Polynomial.C)
  have hs' : HasSum (fun d => C (Polynomial.C (PowerSeries.coeff d actualSeries))*zeta^d) Aq := by
    unfold Aq jointEval
    rw [coe_eval₂Hom]
    have hs0 := hs
    simp only [e, PowerSeries.coeff_map, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, RingHom.comp_apply] at hs0
    with_unfolding_all exact hs0
  have ht := (hasSum_eval₂ (show Continuous (C : ℚ →+* PS) from PowerSeries.WithPiTopology.continuous_C)
    Z_hasEval actualSeries).map scalarEmbed continuous_scalarEmbed
  change HasSum (fun d => scalarEmbed (C (PowerSeries.coeff d actualSeries)*Z^d))
    (scalarEmbed (eval₂ C Z actualSeries)) at ht
  have ht' : HasSum (fun d => C (Polynomial.C (PowerSeries.coeff d actualSeries))*zeta^d)
      (scalarEmbed A) := by
    simpa only [Function.comp_apply, map_mul, map_pow, scalarEmbed_Z,
      scalarEmbed_C, A, coe_eval₂Hom] using ht
  exact hs'.unique ht'

theorem row_scalar (k : ℕ) (a : PS) :
    row k (scalarEmbed a) = if k=0 then a else 0 := by
  ext n
  simp only [coeff_row, scalarEmbed, PowerSeries.coeff_map, Polynomial.coeff_C]
  split_ifs <;> simp

private theorem equation_expanded :
    scalarEmbed Q * shift H - t*(scalarEmbed (2*Q)*shift H) +
      t*(t*(scalarEmbed Q*shift H)) + t*(scalarEmbed ((1-Q)^2)*H) =
      scalarEmbed ((1+Q)*(A-1)) + t*(scalarEmbed ((1+Q)^2-4*Q*A)) +
        t*(t*(scalarEmbed (Q*(1+Q)*(A-1)))) := by
  have he := catalytic_H_equation
  rw [Aq_actual] at he
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
    scalarEmbed_Q] at *
  unfold Cq delta at *
  linear_combination he

theorem h_boundary_zero : Q*h 0 = (1+Q)*(A-1) := by
  have he := congrArg (row 0) equation_expanded
  simp only [map_add, map_sub, row_t_mul_zero, row_scalar_mul, row_shift,
    row_scalar] at he
  simpa [h] using he

theorem h_boundary_one :
    Q^2*h 1 + ((1-Q)^2-2*Q)*h 0 = (1+Q)^2-4*Q*A := by
  have he := congrArg (row 1) equation_expanded
  simp only [map_add, map_sub, row_t_mul_succ, row_t_mul_zero,
    row_scalar_mul, row_shift, row_scalar] at he
  norm_num at he
  simp only [h]
  linear_combination he

/-- The t^2 boundary retains the indispensable q(1-q)h0 term. -/
theorem h_boundary_two :
    Q^3*h 2 + ((1-Q)^2-2*Q^2)*h 1 + Q*(1-Q)*h 0 = 0 := by
  have he := congrArg (row 2) equation_expanded
  simp only [map_add, map_sub, row_t_mul_succ, row_scalar_mul, row_shift,
    row_scalar] at he
  norm_num at he
  have h0 := h_boundary_zero
  simp only [h] at h0 ⊢
  linear_combination he - Q*h0

/-- All-index bulk law on the actual carrier, with precisely the j>=2 boundary. -/
theorem h_bulk (j : ℕ) (hj : 2 ≤ j) :
    Q^(j+2)*h (j+1) + ((1-Q)^2-2*Q^(j+1))*h j + Q^j*h (j-1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j=k+2 := ⟨j-2, by omega⟩
  have he := congrArg (row (k+3)) equation_expanded
  simp only [show k+3=(k+2)+1 by omega, show k+2=(k+1)+1 by omega,
    map_add, map_sub, row_t_mul_succ,
    row_scalar_mul, row_shift, row_scalar] at he
  simp only [if_neg (by omega : k+3 ≠ 0), if_neg (by omega : k+2 ≠ 0),
    if_neg (by omega : k+1 ≠ 0), add_zero, zero_add] at he
  simp only [show k+2+1=k+3 by omega, show k+2-1=k+1 by omega]
  simp only [h]
  simp only [pow_succ] at *
  linear_combination he

/-- Divisibility is deduced from the actual equation, canceling only the unit delta. -/
theorem h_dvd (k : ℕ) : Q^k ∣ h k := by
  have hu : IsUnit ((1-Q)^2) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp : IsUnit
      (PowerSeries.constantCoeff (1-Q)))).pow 2
  cases k with
  | zero => simp
  | succ k =>
    apply hu.dvd_mul_left.mp
    cases k with
    | zero =>
      refine ⟨2*Q*h 1-Q^2*h 2-(1-Q)*h 0, ?_⟩
      simp only [pow_succ, pow_zero, one_mul]
      linear_combination h_boundary_two
    | succ k =>
      refine ⟨2*Q*h (k+1+1)-Q^2*h (k+1+1+1)-h (k+1+1-1), ?_⟩
      have he := h_bulk (k+1+1) (by omega)
      simp only [pow_succ] at *
      linear_combination he

/-- Direct instantiation of the existing scalar supplier's exact Bulk contract. -/
theorem actual_Bulk : D5.S3.Combinatorics.PatternMatchings.P13Scalar.Bulk h := by
  intro j hj
  exact h_bulk j hj

/-- The existing minimal-solution theorem now has a proved actual-H consumer. -/
theorem h_minimal_solution (j : ℕ) (hj : 2 ≤ j) :
    (1-Q)^2 * D5.S3.Combinatorics.PatternMatchings.P13Scalar.Phi j * h j +
      Q^j * D5.S3.Combinatorics.PatternMatchings.P13Scalar.Phi (j+1) * h (j-1) = 0 :=
  D5.S3.Combinatorics.PatternMatchings.P13Scalar.minimal_solution h actual_Bulk j hj

end D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH
