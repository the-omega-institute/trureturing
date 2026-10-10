/- GID: D5/S1/Recurrence/Algebraic/DelannoySquareRoots
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/DelannoySquareRoots
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original Delannoy paths and their triangular matrix square. -/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Finset
open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.DelannoySquareRoots

/-- The three allowed lattice steps, east, north and northeast. -/
inductive Step
  | east | north | northeast
  deriving DecidableEq

/-- The endpoint of a path written in its order of traversal. -/
def endpoint : List Step → ℕ × ℕ
  | [] => (0, 0)
  | .east :: p => (1 + (endpoint p).1, (endpoint p).2)
  | .north :: p => ((endpoint p).1, 1 + (endpoint p).2)
  | .northeast :: p => (1 + (endpoint p).1, 1 + (endpoint p).2)

/-- All paths whose endpoint has coordinate sum n. A northeast step uses
two units of this sum; an east or north step uses one. -/
def paths : ℕ → Finset (List Step)
  | 0 => {[]}
  | n + 1 =>
      (paths n).image (Step.east :: ·) ∪
      (paths n).image (Step.north :: ·) ∪
      if n = 0 then ∅ else (paths (n - 1)).image (Step.northeast :: ·)
termination_by n => n

/-- The original Delannoy triangle, zero above the diagonal. -/
def delannoy (n k : ℕ) : ℕ :=
  ((paths n).filter fun p => (endpoint p).2 = k).card

/-- The ordinary triangular matrix square D squared. -/
def squareEntry (n k : ℕ) : ℕ :=
  ∑ j ∈ Icc k n, delannoy n j * delannoy j k

/-- The row-generating polynomial of the original matrix square. -/
noncomputable def squareRow (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ range (n + 1), Polynomial.C (squareEntry n k : ℤ) * Polynomial.X ^ k

/-- The selected original all-degree root assertion. Row zero is included. -/
def negativeRoots : Prop :=
  ∀ (n : ℕ) (z : ℂ), (squareRow n).eval₂ (Int.castRingHom ℂ) z = 0 →
    z.im = 0 ∧ z.re < 0

/-- The ordinary row polynomial obtained by counting the actual paths. -/
noncomputable def ordinaryRow (n : ℕ) : Polynomial ℤ :=
  ∑ p ∈ paths n, Polynomial.X ^ (endpoint p).2

/-- The formal series of the actual squared rows, at the scalar x. -/
noncomputable def squareSeries : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk squareRow

/-- The denominator of the source bivariate generating function. The polynomial
variable is the row variable, and the power-series variable is the row index. -/
noncomputable def squareDenominator : PowerSeries (Polynomial ℤ) :=
  (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) -
    PowerSeries.C Polynomial.X * PowerSeries.X * (1 + PowerSeries.X) *
      (1 + PowerSeries.X ^ 2)

set_option maxHeartbeats 1600000 in
-- Path induction and coefficientwise series substitution are elaborated together in this proof.
/-- Actual Delannoy paths give the source generating function for the ordinary
triangular matrix square, its divided difference and the nonvanishing
root-count threshold, in every degree. -/
theorem source_correspondence :
    (∀ (n : ℕ) (p : List Step), p ∈ paths n ↔
      (endpoint p).1 + (endpoint p).2 = n) ∧
    squareDenominator * squareSeries = 1 - PowerSeries.X ∧
    (∀ n : ℕ, (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (1 - Real.sqrt 2) ≠ 0) ∧
    ∀ (u v y : ℂ), u ≠ 0 → v ≠ 0 → u + v + u * v = 1 → y * u * v = 1 →
      ∀ n : ℕ, y * (v - u) * (-1) ^ n *
        (squareRow n).eval₂ (Int.castRingHom ℂ) (-y) =
        (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u) / u ^ (n + 1) -
          (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-v) / v ^ (n + 1) := by
  have hpaths : ∀ (n : ℕ) (p : List Step),
      p ∈ paths n ↔ (endpoint p).1 + (endpoint p).2 = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p
      cases n with
      | zero =>
        cases p with
        | nil => simp [paths, endpoint]
        | cons s p => cases s <;> simp [paths, endpoint]
      | succ n =>
        cases p with
        | nil =>
          rw [paths]
          split_ifs <;> simp [endpoint]
        | cons s p =>
          cases n with
          | zero =>
            have hz := ih 0 (by omega) p
            simp only [paths, mem_singleton] at hz
            cases s <;> simp [paths, endpoint]
            all_goals first | rw [hz]; omega | omega
          | succ n =>
            have h1 := ih (n + 1) (by omega) p
            have h0 := ih n (by omega) p
            rw [paths]
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
              Nat.add_sub_cancel]
            cases s <;> simp [endpoint]
            all_goals first | rw [h1]; omega | rw [h0]; omega

  have hrec : ∀ n : ℕ, ordinaryRow (n + 2) =
      (1 + Polynomial.X) * ordinaryRow (n + 1) + Polynomial.X * ordinaryRow n := by
    intro n
    have hd : ∀ (a b : Step) (s t : Finset (List Step)), a ≠ b →
        Disjoint (s.image (a :: ·)) (t.image (b :: ·)) := by
      intro a b s t hab
      apply disjoint_left.mpr
      intro p hp hq
      obtain ⟨u, _, rfl⟩ := mem_image.mp hp
      obtain ⟨v, _, hv⟩ := mem_image.mp hq
      exact hab (List.cons.inj hv).1.symm
    have hi : ∀ (a : Step) (s : Finset (List Step)),
        Set.InjOn (a :: ·) s := by
      intro a s u _ v _ huv
      exact (List.cons.inj huv).2
    unfold ordinaryRow
    rw [paths]
    simp only [show n + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    rw [sum_union (disjoint_union_left.mpr
      ⟨hd _ _ _ _ (by decide), hd _ _ _ _ (by decide)⟩),
      sum_union (hd _ _ _ _ (by decide))]
    rw [sum_image (hi _ _), sum_image (hi _ _), sum_image (hi _ _)]
    simp only [endpoint, pow_add, pow_one]
    simp_rw [mul_comm (Polynomial.X : Polynomial ℤ), ← sum_mul]
    ring
  let col := fun k => PowerSeries.mk fun n => (ordinaryRow n).coeff k
  have hcolrec : ∀ k : ℕ, (1 - PowerSeries.X) * col (k + 1) =
      PowerSeries.X * (1 + PowerSeries.X) * col k := by
    dsimp only [col]
    intro k
    have hrow0 : ordinaryRow 0 = 1 := by simp [ordinaryRow, paths, endpoint]
    have hrow1 : ordinaryRow 1 = 1 + Polynomial.X := by
      simp [ordinaryRow, paths, endpoint, add_comm]
    rw [show (1 - PowerSeries.X) *
        PowerSeries.mk (fun n => (ordinaryRow n).coeff (k + 1)) =
        PowerSeries.mk (fun n => (ordinaryRow n).coeff (k + 1)) -
          PowerSeries.X * PowerSeries.mk (fun n => (ordinaryRow n).coeff (k + 1))
        by ring]
    rw [show PowerSeries.X * (1 + PowerSeries.X) *
        PowerSeries.mk (fun n => (ordinaryRow n).coeff k) =
        PowerSeries.X * PowerSeries.mk (fun n => (ordinaryRow n).coeff k) +
          PowerSeries.X * (PowerSeries.X *
            PowerSeries.mk (fun n => (ordinaryRow n).coeff k)) by ring]
    ext n
    cases n with
    | zero => simp [hrow0, Polynomial.coeff_one]
    | succ n =>
      simp only [map_sub, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
      cases n with
      | zero => simp [hrow0, hrow1, Polynomial.coeff_one, Polynomial.coeff_X]
      | succ n =>
        simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
        rw [show n + 1 + 1 = n + 2 by omega, hrec]
        simp only [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul]
        ring
  have hconst : ∀ n : ℕ, (ordinaryRow n).coeff 0 = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [ordinaryRow, paths, endpoint, Polynomial.coeff_one]
      | succ n =>
        cases n with
        | zero => simp [ordinaryRow, paths, endpoint]
        | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega, hrec]
          simp only [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero,
            add_zero]
          exact ih (n + 1) (by omega)
  let g : PowerSeries ℤ := PowerSeries.invUnitsSub 1
  let f : PowerSeries ℤ := PowerSeries.X * (1 + PowerSeries.X) * g
  have hg : g * (1 - PowerSeries.X) = 1 := by
    simpa [g] using PowerSeries.invUnitsSub_mul_sub (1 : ℤˣ)
  have hcol : ∀ k : ℕ, col k = g * f ^ k := by
    intro k
    induction k with
    | zero =>
      ext n
      simp [col, g, hconst]
    | succ k ih =>
      calc
        col (k + 1) = g * ((1 - PowerSeries.X) * col (k + 1)) := by
          rw [← mul_assoc, hg, one_mul]
        _ = g * (PowerSeries.X * (1 + PowerSeries.X) * col k) :=
          congrArg (g * ·) (hcolrec k)
        _ = g * f ^ (k + 1) := by rw [ih]; dsimp only [f]; ring
  have hcoeff : ∀ n k : ℕ, (ordinaryRow n).coeff k = (delannoy n k : ℤ) := by
    intro n k
    simp [ordinaryRow, delannoy, eq_comm]
  have hcolumns : ∀ n k : ℕ, (delannoy n k : ℤ) = PowerSeries.coeff n
      (PowerSeries.invUnitsSub (1 : ℤˣ) *
        (PowerSeries.X * (1 + PowerSeries.X) *
          PowerSeries.invUnitsSub (1 : ℤˣ)) ^ k) := by
    intro n k
    rw [← hcoeff, ← PowerSeries.coeff_mk n (fun n => (ordinaryRow n).coeff k)]
    exact congrArg (PowerSeries.coeff n) (hcol k)
  have hsquare : ∀ n : ℕ, squareRow n = ∑ j ∈ range (n + 1),
      Polynomial.C (delannoy n j : ℤ) * ordinaryRow j := by
    have hzero : ∀ n k : ℕ, n < k → delannoy n k = 0 := by
      intro n k hnk
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp, hk⟩ := mem_filter.mp hp
      have hn := (hpaths n p).mp hp
      omega
    have hcoeff : ∀ n k : ℕ, (ordinaryRow n).coeff k = (delannoy n k : ℤ) := by
      intro n k
      simp [ordinaryRow, delannoy, eq_comm]
    intro n
    ext k
    simp only [squareRow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, hcoeff]
    have hs : ∑ j ∈ Icc k n, (delannoy n j : ℤ) * (delannoy j k : ℤ) =
        ∑ j ∈ range (n + 1), (delannoy n j : ℤ) * (delannoy j k : ℤ) := by
      apply sum_subset
      · intro j hj
        simp only [mem_Icc] at hj
        simp only [mem_range]
        omega
      · intro j hj hjnot
        simp only [mem_range] at hj
        simp only [mem_Icc, not_and_or, not_le] at hjnot
        rw [hzero j k (by omega), Nat.cast_zero, mul_zero]
    rw [← hs]
    by_cases hk : k < n + 1
    · rw [sum_eq_single k]
      · simp [squareEntry]
      · intro j hj hjk
        simp [hjk.symm]
      · exact fun h => (h (mem_range.mpr hk)).elim
    · have hsum : ∑ j ∈ Icc k n,
          (delannoy n j : ℤ) * (delannoy j k : ℤ) = 0 := by
        apply sum_eq_zero
        intro j hj
        simp only [mem_Icc] at hj
        omega
      rw [hsum]
      apply sum_eq_zero
      intro j hj
      simp only [mem_range] at hj
      simp [show k ≠ j by omega]
  have hcomposed :
      let g := PowerSeries.map (Polynomial.C : ℤ →+* Polynomial ℤ)
        (PowerSeries.invUnitsSub (1 : ℤˣ))
      let f := PowerSeries.X * (1 + PowerSeries.X) * g
      squareSeries = g * (PowerSeries.mk ordinaryRow).subst f := by
    dsimp only
    let g : PowerSeries (Polynomial ℤ) := PowerSeries.map Polynomial.C
      (PowerSeries.invUnitsSub (1 : ℤˣ))
    let f : PowerSeries (Polynomial ℤ) := PowerSeries.X * (1 + PowerSeries.X) * g
    let T : PowerSeries (Polynomial ℤ) := PowerSeries.mk ordinaryRow
    change squareSeries = g * T.subst f
    have hf : PowerSeries.HasSubst f :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [f])
    have hcolR : ∀ n k : ℕ, PowerSeries.coeff n (g * f ^ k) =
        Polynomial.C (delannoy n k : ℤ) := by
      intro n k
      have h := congrArg (Polynomial.C : ℤ →+* Polynomial ℤ) (hcolumns n k)
      rw [← PowerSeries.coeff_map] at h
      simpa only [PowerSeries.coeff_map, map_mul, map_pow, PowerSeries.map_X,
        map_add, map_one] using h.symm
    have hvan : ∀ a j : ℕ, a < j → PowerSeries.coeff a (f ^ j) = 0 := by
      intro a j haj
      dsimp only [f]
      rw [mul_assoc, mul_pow, PowerSeries.coeff_X_pow_mul']
      simp [Nat.not_le.mpr haj]
    apply PowerSeries.ext
    intro n
    have hsubst : ∀ a : ℕ, a ≤ n → PowerSeries.coeff a (T.subst f) =
        ∑ j ∈ range (n + 1), ordinaryRow j * PowerSeries.coeff a (f ^ j) := by
      intro a han
      rw [PowerSeries.coeff_subst' hf]
      simp only [T, PowerSeries.coeff_mk, smul_eq_mul]
      apply finsum_eq_sum_of_support_subset
      intro j hj
      simp only [Function.mem_support, ne_eq, mem_coe, mem_range] at hj ⊢
      by_contra hjn
      have hj0 := hvan a j (by omega)
      simp [hj0] at hj
    rw [squareSeries, PowerSeries.coeff_mk, hsquare, PowerSeries.coeff_mul]
    symm
    calc
      ∑ ab ∈ Finset.antidiagonal n,
          PowerSeries.coeff ab.1 g * PowerSeries.coeff ab.2 (T.subst f) =
          ∑ ab ∈ Finset.antidiagonal n, ∑ j ∈ range (n + 1),
            PowerSeries.coeff ab.1 g *
              (ordinaryRow j * PowerSeries.coeff ab.2 (f ^ j)) := by
        apply sum_congr rfl
        intro ab hab
        rw [hsubst ab.2 (by have := mem_antidiagonal.mp hab; omega), mul_sum]
      _ = ∑ j ∈ range (n + 1), ∑ ab ∈ Finset.antidiagonal n,
          PowerSeries.coeff ab.1 g *
            (ordinaryRow j * PowerSeries.coeff ab.2 (f ^ j)) := sum_comm
      _ = ∑ j ∈ range (n + 1), Polynomial.C (delannoy n j : ℤ) * ordinaryRow j := by
        apply sum_congr rfl
        intro j hj
        simp_rw [show ∀ a b : Polynomial ℤ, a * (ordinaryRow j * b) =
          ordinaryRow j * (a * b) by intros; ring]
        rw [← mul_sum, ← PowerSeries.coeff_mul, hcolR]
        ring
  have hT : (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X -
      PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) *
      PowerSeries.mk ordinaryRow = 1 := by
    have hrow0 : ordinaryRow 0 = 1 := by simp [ordinaryRow, paths, endpoint]
    have hrow1 : ordinaryRow 1 = 1 + Polynomial.X := by
      simp [ordinaryRow, paths, endpoint, add_comm]
    rw [show (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X -
        PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) * PowerSeries.mk ordinaryRow =
        PowerSeries.mk ordinaryRow - PowerSeries.C (1 + Polynomial.X) *
          (PowerSeries.X * PowerSeries.mk ordinaryRow) -
        PowerSeries.C Polynomial.X *
          (PowerSeries.X * (PowerSeries.X * PowerSeries.mk ordinaryRow)) by ring]
    apply PowerSeries.ext
    intro n
    simp only [map_sub, PowerSeries.coeff_C_mul]
    cases n with
    | zero => simp [hrow0]
    | succ n =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
      cases n with
      | zero => simp [hrow0, hrow1]
      | succ n =>
        simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
        rw [show n + 1 + 1 = n + 2 by omega, hrec]
        simp only [PowerSeries.coeff_one, show n + 2 ≠ 0 by omega, if_false]
        ring
  let gR : PowerSeries (Polynomial ℤ) := PowerSeries.map Polynomial.C
    (PowerSeries.invUnitsSub (1 : ℤˣ))
  let fR : PowerSeries (Polynomial ℤ) := PowerSeries.X * (1 + PowerSeries.X) * gR
  let T : PowerSeries (Polynomial ℤ) := PowerSeries.mk ordinaryRow
  have hcomp : squareSeries = gR * T.subst fR := hcomposed
  have hgR : gR * (1 - PowerSeries.X) = 1 := by
    simpa [gR] using congrArg (PowerSeries.map (Polynomial.C : ℤ →+* Polynomial ℤ))
      (PowerSeries.invUnitsSub_mul_sub (1 : ℤˣ))
  have hfR : PowerSeries.HasSubst fR :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [fR])
  have hsub : (1 - PowerSeries.C (1 + Polynomial.X) * fR -
      PowerSeries.C Polynomial.X * fR ^ 2) * T.subst fR = 1 := by
    let : Algebra (Polynomial ℤ) (PowerSeries (Polynomial ℤ)) := MvPowerSeries.instAlgebra
    let φ : PowerSeries (Polynomial ℤ) →+* PowerSeries (Polynomial ℤ) :=
      (PowerSeries.substAlgHom (R := Polynomial ℤ) hfR).toRingHom
    have h : φ ((1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X -
        PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) * T) = φ 1 := congrArg φ hT
    simp only [map_mul, map_sub, map_one, map_pow] at h
    have hC : ∀ a : Polynomial ℤ, φ (PowerSeries.C a) = PowerSeries.C a := by
      intro a
      rw [show φ (PowerSeries.C a) = (PowerSeries.C a).subst fR from
        congrFun (PowerSeries.coe_substAlgHom (R := Polynomial ℤ) hfR) (PowerSeries.C a)]
      exact PowerSeries.subst_C (a := fR) a
    have hX : φ PowerSeries.X = fR := by
      rw [show φ PowerSeries.X = PowerSeries.X.subst fR from
        congrFun (PowerSeries.coe_substAlgHom (R := Polynomial ℤ) hfR) PowerSeries.X]
      exact PowerSeries.subst_X hfR
    have hφT : φ T = T.subst fR :=
      congrFun (PowerSeries.coe_substAlgHom (R := Polynomial ℤ) hfR) T
    simpa only [hC, hX, hφT] using h
  have hQ : squareDenominator * gR = (1 - PowerSeries.X) *
      (1 - PowerSeries.C (1 + Polynomial.X) * fR -
        PowerSeries.C Polynomial.X * fR ^ 2) := by
    dsimp only [squareDenominator, fR]
    simp only [map_add, map_one]
    linear_combination
      ((1 - PowerSeries.X) +
        PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 2 * gR) * hgR
  have hGF : squareDenominator * squareSeries = 1 - PowerSeries.X := by
    rw [hcomp, ← mul_assoc, hQ, mul_assoc, hsub, mul_one]
  have hDD : ∀ (u v y : ℂ), u ≠ 0 → v ≠ 0 → u + v + u * v = 1 → y * u * v = 1 →
      ∀ n : ℕ, y * (v - u) * (-1) ^ n *
        (squareRow n).eval₂ (Int.castRingHom ℂ) (-y) =
        (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u) / u ^ (n + 1) -
          (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-v) / v ^ (n + 1) := by
    intro u v y hu hv hrel hy
    let q := fun a : ℂ => (X^2 + (C a - 1)*X + C a : PowerSeries ℂ)
    let A := fun a : ℂ => PowerSeries.mk fun n =>
      (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-a) / a^(n+1)
    have hA : ∀ a : ℂ, a ≠ 0 → q a * A a = 1 := by
      intro a ha
      rw [show q a * A a = X*(X*A a) + C (a-1)*(X*A a) + C a*A a by
        dsimp only [q]; rw [map_sub, map_one]; ring]
      ext n
      simp only [map_add, coeff_C_mul]
      cases n with
      | zero => simp [A, ordinaryRow, paths, endpoint, ha]
      | succ n =>
        simp only [coeff_succ_X_mul]
        cases n with
        | zero =>
          simp [A, ordinaryRow, paths, endpoint]
          field_simp
          ring
        | succ n =>
          simp only [A, coeff_succ_X_mul, coeff_mk]
          rw [show n+1+1 = n+2 by omega, hrec]
          simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
            Polynomial.eval₂_one, Polynomial.eval₂_X, coeff_one,
            show n+2 ≠ 0 by omega, if_false]
          simp only [pow_succ]
          field_simp
          ring
    let e := Polynomial.eval₂RingHom (Int.castRingHom ℂ) (-y)
    let φ := (rescale (-1 : ℂ)).comp (PowerSeries.map e)
    let P := φ squareSeries
    let Q : PowerSeries ℂ := (1+X)*(1+2*X-X^2)-C y*X*(1-X)*(1+X^2)
    have hC : ∀ a : ℂ, rescale (-1 : ℂ) (C a) = C a := by
      intro a
      ext n
      simp [coeff_rescale, coeff_C]
      split_ifs <;> simp_all
    have hφQ : φ squareDenominator = Q := by
      simp only [φ, RingHom.comp_apply, squareDenominator, map_sub, map_mul,
        map_add, map_one, map_pow, map_ofNat, PowerSeries.map_X, PowerSeries.map_C,
        rescale_neg_one_X, hC]
      simp only [e, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      dsimp only [Q]
      simp only [map_neg]
      ring
    have hP : Q*P = 1+X := by
      have h := congrArg φ hGF
      rw [map_mul, hφQ] at h
      simpa [P, φ, RingHom.comp_apply] using h
    have hfac : Q = C y*q u*q v := by
      have hr := congrArg (C : ℂ →+* PowerSeries ℂ) hrel
      have hyr := congrArg (C : ℂ →+* PowerSeries ℂ) hy
      simp only [map_add, map_mul, map_one] at hr hyr
      dsimp only [Q, q]
      linear_combination -(1+3*X+X^2-X^3)*hyr + C y*X*(1-X^2)*hr
    have hdiff : q v - q u = C (v-u)*(1+X) := by
      dsimp only [q]
      rw [map_sub]
      ring
    have hunit : IsUnit Q := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [Q]
    have hseries : C (y*(v-u))*P = A u-A v := by
      apply hunit.mul_left_cancel
      calc
        Q*(C (y*(v-u))*P) = C (y*(v-u))*(1+X) := by rw [mul_left_comm, hP]
        _ = C y*(q v-q u) := by rw [hdiff, map_mul]; ring
        _ = Q*(A u-A v) := by
          rw [hfac]
          have hAu := hA u hu
          have hAv := hA v hv
          linear_combination -C y*q v*hAu + C y*q u*hAv
    intro n
    have h := congrArg (PowerSeries.coeff n) hseries
    simp only [coeff_C_mul, map_sub, A, coeff_mk] at h
    dsimp only [P, φ] at h
    simp only [RingHom.comp_apply, coeff_rescale, coeff_map, squareSeries, coeff_mk,
      e, Polynomial.coe_eval₂RingHom] at h
    simpa only [mul_assoc] using h
  refine ⟨hpaths, hGF, ?_, hDD⟩
  have hplus : ∀ n : ℕ,
      0 < (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (1 + Real.sqrt 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [ordinaryRow, paths, endpoint]
      | succ n =>
        cases n with
        | zero =>
          simpa [ordinaryRow, paths, endpoint] using
            (show (0 : ℝ) < 1 + (1 + Real.sqrt 2) by positivity)
        | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega, hrec]
          simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
            Polynomial.eval₂_one, Polynomial.eval₂_X]
          exact add_pos (mul_pos (by positivity) (ih (n + 1) (by omega)))
            (mul_pos (by positivity) (ih n (by omega)))
  have hnonsquare : ∀ m : ℤ, (2 : ℤ) ≠ m * m := by
    intro m hm
    have hm' : m ≤ -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
    rcases hm' with h | h | h | h | h
    · nlinarith [sq_nonneg (m + 1)]
    · norm_num [h] at hm
    · norm_num [h] at hm
    · norm_num [h] at hm
    · nlinarith [sq_nonneg (m - 1)]
  let r : Zsqrtd 2 := ⟨1, -1⟩
  let σ : Zsqrtd 2 →+* ℝ := Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 2)
  let τ : Zsqrtd 2 →+* ℝ := Zsqrtd.lift
    ⟨-Real.sqrt 2, by simpa only [Int.cast_ofNat, neg_mul_neg] using
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)⟩
  have hσ : σ r = 1 - Real.sqrt 2 := by
    simp [σ, r, Zsqrtd.toReal, Zsqrtd.lift_apply_apply, sub_eq_add_neg]
  have hτ : τ r = 1 + Real.sqrt 2 := by
    simp [τ, r, Zsqrtd.lift_apply_apply]
  have hσinj : Function.Injective σ := Zsqrtd.toReal_injective _ hnonsquare
  have hcastσ : σ.comp (Int.castRingHom (Zsqrtd 2)) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  have hcastτ : τ.comp (Int.castRingHom (Zsqrtd 2)) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  intro n hn
  let w := (ordinaryRow n).eval₂ (Int.castRingHom (Zsqrtd 2)) r
  have hwσ : σ w = 0 := by
    dsimp only [w]
    rw [Polynomial.hom_eval₂, hσ, hcastσ]
    simpa using hn
  have hw : w = 0 := hσinj (by simpa using hwσ)
  have hwτ : (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (1 + Real.sqrt 2) = 0 := by
    have h := congrArg τ hw
    dsimp only [w] at h
    rw [Polynomial.hom_eval₂, hτ, hcastτ] at h
    simpa using h
  exact (ne_of_gt (hplus n)) hwτ


set_option maxHeartbeats 1600000 in
/-- Upper-circle phase crossings give distinct actual squared-row roots in the central
positive interval for the transformed variable, in every degree. -/
theorem upper_circle_roots (n : ℕ) :
    ∃ z : Fin n → ℝ, Function.Injective z ∧
      (∀ i, 0 < z i ∧ z i ≠ Real.sqrt 2 - 1) ∧
      (∀ w : ℂ, (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-w) =
        (-1) ^ n * ∏ i, (w - (z i : ℂ))) ∧
      ∃ y : Fin ((univ.filter fun i : Fin n => Real.sqrt 2 - 1 < z i).card) → ℝ,
        Function.Injective y ∧ ∀ i,
          3 - 2 * Real.sqrt 2 < y i ∧ y i < 3 + 2 * Real.sqrt 2 ∧
          (squareRow n).eval₂ (Int.castRingHom ℂ) (-(y i : ℂ)) = 0 := by
  classical
  have hrec : ∀ n : ℕ, ordinaryRow (n + 2) =
      (1 + Polynomial.X) * ordinaryRow (n + 1) + Polynomial.X * ordinaryRow n := by
    intro n
    have hd : ∀ (a b : Step) (s t : Finset (List Step)), a ≠ b →
        Disjoint (s.image (a :: ·)) (t.image (b :: ·)) := by
      intro a b s t hab
      apply disjoint_left.mpr
      intro p hp hq
      obtain ⟨u, _, rfl⟩ := mem_image.mp hp
      obtain ⟨v, _, hv⟩ := mem_image.mp hq
      exact hab (List.cons.inj hv).1.symm
    have hi : ∀ (a : Step) (s : Finset (List Step)),
        Set.InjOn (a :: ·) s := by
      intro a s u _ v _ huv
      exact (List.cons.inj huv).2
    unfold ordinaryRow
    rw [paths]
    simp only [show n + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    rw [sum_union (disjoint_union_left.mpr
      ⟨hd _ _ _ _ (by decide), hd _ _ _ _ (by decide)⟩),
      sum_union (hd _ _ _ _ (by decide))]
    rw [sum_image (hi _ _), sum_image (hi _ _), sum_image (hi _ _)]
    simp only [endpoint, pow_add, pow_one]
    simp_rw [mul_comm (Polynomial.X : Polynomial ℤ), ← sum_mul]
    ring
  have hzero : ordinaryRow 0 = 1 := by simp [ordinaryRow, paths, endpoint]
  have hone : ordinaryRow 1 = 1 + Polynomial.X := by
    simp [ordinaryRow, paths, endpoint, add_comm]
  have hdegree : ∀ m : ℕ, (ordinaryRow m).Monic ∧ (ordinaryRow m).degree = m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => simp [hzero]
    | one => simpa [hone, add_comm] using
        And.intro (Polynomial.monic_X_add_C (1 : ℤ)) (Polynomial.degree_X_add_C (1 : ℤ))
    | more m h0 h1 =>
      rw [hrec]
      have hd1 : ((1 + Polynomial.X) * ordinaryRow (m + 1)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_mul, h1.2]
        rw [show (1 + Polynomial.X : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by simp [add_comm],
          Polynomial.degree_X_add_C]
        norm_num [Nat.cast_add, add_comm, add_left_comm, add_assoc]
      have hd0 : (Polynomial.X * ordinaryRow m).degree = ((m + 1 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_mul, h0.2]
        simp [add_comm]
      have hlt : (Polynomial.X * ordinaryRow m).degree <
          ((1 + Polynomial.X) * ordinaryRow (m + 1)).degree := by
        rw [hd0, hd1]
        exact_mod_cast (show m + 1 < m + 2 by omega)
      have hm : (1 + Polynomial.X : Polynomial ℤ).Monic := by
        simpa [add_comm] using Polynomial.monic_X_add_C (1 : ℤ)
      exact ⟨(hm.mul h1.1).add_of_left hlt,
        (Polynomial.degree_add_eq_left_of_degree_lt hlt).trans hd1⟩
  have hscaled : ∀ (m : ℕ) (u : ℝ), 0 < u →
      (ordinaryRow m).eval₂ (Int.castRingHom ℝ) (-u) =
        Real.sqrt u ^ m * (Polynomial.Chebyshev.U ℝ m).eval
          ((1 - u) / (2 * Real.sqrt u)) := by
    intro m u hu
    have hs : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
    have hsq := Real.sq_sqrt hu.le
    induction m using Nat.twoStepInduction with
    | zero => simp [hzero, Polynomial.Chebyshev.U]
    | one =>
      simp [hone, Polynomial.Chebyshev.U]
      field_simp
      ring
    | more m h0 h1 =>
      rw [hrec]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one,
        Polynomial.eval₂_X, h0, h1]
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
      linear_combination hsq * (Polynomial.Chebyshev.U ℝ m).eval ((1-u)/(Real.sqrt u*2))
  let c : Fin n → ℝ := fun i => Real.cos (((i : ℕ) + 1 : ℝ) * Real.pi / (n + 1))
  let s : Fin n → ℝ := fun i => Real.sqrt (1 + c i ^ 2) - c i
  let z : Fin n → ℝ := fun i => s i ^ 2
  have hs : ∀ i, 0 < s i := by
    intro i
    have ht := Real.sq_sqrt (show 0 ≤ 1 + c i ^ 2 by positivity)
    have ht0 := Real.sqrt_nonneg (1 + c i ^ 2)
    dsimp only [s]
    nlinarith [sq_nonneg (c i)]
  have hz : ∀ i, 0 < z i := fun i => sq_pos_of_pos (hs i)
  have hc : ∀ i, (1 - z i) / (2 * Real.sqrt (z i)) = c i := by
    intro i
    have ht := Real.sq_sqrt (show 0 ≤ 1 + c i ^ 2 by positivity)
    have hsqrt : Real.sqrt (z i) = s i := by
      dsimp only [z]
      exact Real.sqrt_sq (hs i).le
    rw [hsqrt]
    apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) (hs i)))).2
    dsimp only [z, s]
    nlinarith
  have hcinj : Function.Injective c := by
    intro i j hij
    have h := (Finset.range n).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_U_real_nodup n)
    apply Fin.ext
    exact h (by simp) (by simp) hij
  have hzinj : Function.Injective z := by
    intro i j hij
    apply hcinj
    rw [← hc i, ← hc j, hij]
  have hroot : ∀ i, (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (-z i) = 0 := by
    intro i
    rw [hscaled n (z i) (hz i), hc i]
    have hr : c i ∈ (Polynomial.Chebyshev.U ℝ n).roots := by
      rw [Polynomial.Chebyshev.roots_U_real]
      exact Finset.mem_val.mpr (mem_image.mpr ⟨i, by simp, rfl⟩)
    rw [(Polynomial.mem_roots (Polynomial.Chebyshev.U_ne_zero ℝ n (by omega))).mp hr, mul_zero]
  have hthreshold : ∀ i, z i ≠ Real.sqrt 2 - 1 := by
    intro i hi
    have hr := hroot i
    rw [hi, neg_sub] at hr
    exact source_correspondence.2.2.1 n hr
  let T : Polynomial ℝ := (ordinaryRow n).map (Int.castRingHom ℝ)
  let S : Finset ℝ := univ.image fun i => -z i
  have hS : T.roots = S.val := by
    apply Polynomial.roots_eq_of_degree_eq_card
    · intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      simpa only [T, Polynomial.eval_map] using hroot i
    · rw [card_image_of_injective _ (fun i j h => hzinj (neg_injective h)), card_univ,
        Fintype.card_fin]
      dsimp only [T]
      rw [Polynomial.degree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective),
        (hdegree n).2]
  have hmonic : T.Monic := (hdegree n).1.map _
  have hfactor : T = ∏ i : Fin n, (Polynomial.X + Polynomial.C (z i)) := by
    have hcard : T.roots.card = T.natDegree := by
      rw [hS, Finset.card_val]
      dsimp only [S]
      rw [
        card_image_of_injective _ (fun i j h => hzinj (neg_injective h)), card_univ,
        Fintype.card_fin]
      exact (Polynomial.natDegree_eq_of_degree_eq_some (by
        dsimp only [T]
        rw [Polynomial.degree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective),
          (hdegree n).2])).symm
    rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard, hS]
    rw [Finset.prod_map_val]
    dsimp only [S]
    rw [Finset.prod_image]
    · simp [sub_eq_add_neg]
    · intro i _ j _ hij
      exact hzinj (neg_injective hij)
  have hfacC : ∀ w : ℂ, (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-w) =
      (-1) ^ n * ∏ i, (w - (z i : ℂ)) := by
    intro w
    have hf := congrArg (fun p : Polynomial ℝ =>
      p.eval₂ (algebraMap ℝ ℂ) (-w)) hfactor
    simp only [T, Polynomial.eval₂_map, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
    rw [show (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ from
      Subsingleton.elim _ _] at hf
    calc
      (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-w) =
          ∏ i : Fin n, (-w + (algebraMap ℝ ℂ) (z i)) := hf
      _ = ∏ i : Fin n, ((-1 : ℂ) * (w - (z i : ℂ))) := by
        apply prod_congr rfl
        intro i _
        change -w + (z i : ℂ) = -1 * (w - (z i : ℂ))
        ring
      _ = _ := by rw [prod_mul_distrib]; simp

  let u : ℝ → ℂ := fun t => ⟨-1 + Real.sqrt 2 * Real.cos t,
    Real.sqrt 2 * Real.sin t⟩
  let N : ℕ := (univ.filter fun i : Fin n => Real.sqrt 2 - 1 < z i).card
  let ψ : ℝ → ℝ := fun t => ∑ i : Fin n, Complex.arg (u t - (z i : ℂ)) -
    (n + 1 : ℝ) * Complex.arg (u t)
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hucont : Continuous u := by
    have he : u = fun t => ((-1 + Real.sqrt 2 * Real.cos t : ℝ) : ℂ) +
        (Real.sqrt 2 * Real.sin t : ℝ) * Complex.I := by
      funext t
      apply Complex.ext <;> simp only [u, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_self, add_zero, zero_add]
    rw [he]
    fun_prop
  have him : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ (u t).im := by
    intro t ht
    exact mul_nonneg (Real.sqrt_nonneg 2) (Real.sin_nonneg_of_mem_Icc ht)
  have himpos : ∀ t ∈ Set.Ioo (0 : ℝ) Real.pi, 0 < (u t).im := by
    intro t ht
    exact mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hune : ∀ (r : ℝ), 0 ≤ r → r ≠ Real.sqrt 2 - 1 →
      ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, u t - (r : ℂ) ≠ 0 := by
    intro r hr hrt t ht he
    have heR := congrArg Complex.re he
    have heI := congrArg Complex.im he
    by_cases ht0 : t = 0
    · simp [u, ht0] at heR
      exact hrt (by linarith)
    by_cases htp : t = Real.pi
    · simp [u, htp] at heR
      linarith
    have hp := himpos t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
      lt_of_le_of_ne ht.2 htp⟩
    exact hp.ne' (by simpa using heI)
  have hunonzero : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, u t ≠ 0 := by
    intro t ht
    simpa using hune 0 le_rfl (by linarith) t ht
  have hargcont : ∀ (r : ℝ), 0 ≤ r → r ≠ Real.sqrt 2 - 1 →
      ContinuousOn (fun t => Complex.arg (u t - (r : ℂ))) (Set.Icc 0 Real.pi) := by
    intro r hr hrt
    have hf : Continuous (fun t => u t - (r : ℂ)) := hucont.sub continuous_const
    have hc : ContinuousOn (fun t => Real.arccos ((u t - (r : ℂ)).re /
        ‖u t - (r : ℂ)‖)) (Set.Icc 0 Real.pi) :=
      Real.continuous_arccos.comp_continuousOn
        ((Complex.continuous_re.comp hf).continuousOn.div hf.norm.continuousOn
          (fun t ht => norm_ne_zero_iff.mpr (hune r hr hrt t ht)))
    apply hc.congr
    intro t ht
    exact (Complex.arg_of_im_nonneg_of_ne_zero (by simpa using him t ht)
      (hune r hr hrt t ht))
  have hψcont : ContinuousOn ψ (Set.Icc 0 Real.pi) := by
    apply ContinuousOn.sub
    · exact continuousOn_finsetSum _ (fun i _ => hargcont (z i) (hz i).le (hthreshold i))
    · have hc := hargcont 0 le_rfl (by linarith)
      simpa using hc.const_mul (n + 1 : ℝ)
  have hψzero : ψ 0 = (N : ℝ) * Real.pi := by
    have hargs : ∀ i : Fin n, Complex.arg (u 0 - (z i : ℂ)) =
        if Real.sqrt 2 - 1 < z i then Real.pi else 0 := by
      intro i
      by_cases hi : Real.sqrt 2 - 1 < z i
      · rw [if_pos hi]
        apply Complex.arg_eq_pi_iff.mpr
        simp only [u, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨by linarith, by simp⟩
      · rw [if_neg hi]
        apply Complex.arg_eq_zero_iff.mpr
        simp only [u, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨by linarith [le_of_not_gt hi], by simp⟩
    have harg0 : Complex.arg (u 0) = 0 := by
      apply Complex.arg_eq_zero_iff.mpr
      simpa [u] using And.intro (show 0 ≤ -1 + Real.sqrt 2 by linarith) rfl
    dsimp only [ψ]
    rw [harg0, mul_zero, sub_zero]
    simp_rw [hargs]
    simp [N, sum_ite]
  have hψpi : ψ Real.pi = -Real.pi := by
    have hargs : ∀ i : Fin n, Complex.arg (u Real.pi - (z i : ℂ)) = Real.pi := by
      intro i
      apply Complex.arg_eq_pi_iff.mpr
      simp only [u, Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨by linarith [hz i], by simp⟩
    have hargpi : Complex.arg (u Real.pi) = Real.pi := by
      apply Complex.arg_eq_pi_iff.mpr
      simp only [u, Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero]
      exact ⟨by linarith, by trivial⟩
    dsimp only [ψ]
    simp_rw [hargs]
    rw [hargpi]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hcross : ∀ j : Fin N, ∃ t ∈ Set.Ioo (0 : ℝ) Real.pi,
      ψ t = (j : ℕ) * Real.pi := by
    intro j
    have hj : ((j : ℕ) : ℝ) < N := by exact_mod_cast j.isLt
    have hlevel : (j : ℕ) * Real.pi ∈ Set.Ioo (ψ Real.pi) (ψ 0) := by
      rw [hψzero, hψpi]
      constructor
      · have hnonneg : 0 ≤ ((j : ℕ) : ℝ) * Real.pi := by positivity
        linarith [Real.pi_pos]
      · exact mul_lt_mul_of_pos_right hj Real.pi_pos
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo' (le_of_lt Real.pi_pos) hψcont hlevel
    exact ⟨t, ht, he⟩
  choose t ht hphase using hcross
  have htin : Function.Injective t := by
    intro i j hij
    apply Fin.ext
    have he := congrArg ψ hij
    rw [hphase i, hphase j] at he
    exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero he)
  have hreal : ∀ j : Fin N,
      ((ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u (t j)) /
        u (t j) ^ (n + 1)).im = 0 := by
    intro j
    let w := u (t j)
    have hw : w ≠ 0 := hunonzero _ (Set.Ioo_subset_Icc_self (ht j))
    have hpolar : (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-w) / w ^ (n + 1) =
        (-1) ^ n * ((∏ i : Fin n, ‖w - (z i : ℂ)‖ : ℝ) / ‖w‖ ^ (n + 1) : ℝ) *
          Complex.exp ((ψ (t j) : ℂ) * Complex.I) := by
      rw [hfacC]
      have he : Complex.exp ((ψ (t j) : ℂ) * Complex.I) =
          (∏ i : Fin n, Complex.exp (Complex.arg (w - (z i : ℂ)) * Complex.I)) /
            Complex.exp (Complex.arg w * Complex.I) ^ (n + 1) := by
        dsimp only [ψ]
        simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, sub_mul,
          sum_mul, Complex.exp_sub, Complex.exp_sum]
        rw [show ((n : ℂ) + 1) * (Complex.arg w : ℂ) * Complex.I =
          (n + 1 : ℕ) * ((Complex.arg w : ℂ) * Complex.I) by push_cast; ring,
          Complex.exp_nat_mul]
      rw [he]
      have hnum : ∏ i : Fin n, (w - (z i : ℂ)) =
          ((∏ i : Fin n, ‖w - (z i : ℂ)‖ : ℝ) : ℂ) *
            ∏ i : Fin n, Complex.exp (Complex.arg (w - (z i : ℂ)) * Complex.I) := by
        rw [Complex.ofReal_prod, ← prod_mul_distrib]
        apply prod_congr rfl
        intro i _
        exact (Complex.norm_mul_exp_arg_mul_I _).symm
      have hden : w ^ (n + 1) = (‖w‖ : ℂ) ^ (n + 1) *
          Complex.exp (Complex.arg w * Complex.I) ^ (n + 1) := by
        rw [← mul_pow, Complex.norm_mul_exp_arg_mul_I]
      rw [hnum, hden]
      push_cast
      ring
    rw [hpolar, hphase j]
    have he : Complex.exp ((((j : ℕ) : ℝ) * Real.pi : ℝ) * Complex.I) =
        (-1 : ℂ) ^ (j : ℕ) := by
      push_cast
      rw [mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    rw [he]
    rw [show (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
      show (-1 : ℂ) ^ (j : ℕ) = (((-1 : ℝ) ^ (j : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    rfl
  let d : ℝ → ℝ := fun r => 3 - 2 * Real.sqrt 2 * Real.cos r
  let y : ℝ → ℝ := fun r => 1 / d r
  have hnorm : ∀ r : ℝ, Complex.normSq (u r) = d r := by
    intro r
    dsimp only [u, d]
    rw [Complex.normSq_apply]
    have htrig := Real.sin_sq_add_cos_sq r
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hdpos : ∀ r ∈ Set.Icc (0 : ℝ) Real.pi, 0 < d r := by
    intro r hr
    rw [← hnorm]
    exact Complex.normSq_pos.mpr (hunonzero r hr)
  have hrel : ∀ r : ℝ, u r + starRingEnd ℂ (u r) + u r * starRingEnd ℂ (u r) = 1 := by
    intro r
    rw [Complex.mul_conj, hnorm]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.one_re]
      dsimp only [u, d]
      ring
    · simp [Complex.add_im, u]
  have hy : ∀ r ∈ Set.Icc (0 : ℝ) Real.pi,
      (y r : ℂ) * u r * starRingEnd ℂ (u r) = 1 := by
    intro r hr
    rw [mul_assoc, Complex.mul_conj, hnorm]
    change ((1 / d r : ℝ) : ℂ) * (d r : ℂ) = 1
    rw [← Complex.ofReal_mul, one_div_mul_cancel (hdpos r hr).ne']
    rfl
  have hrootcircle : ∀ j : Fin N,
      (squareRow n).eval₂ (Int.castRingHom ℂ) (-(y (t j) : ℂ)) = 0 := by
    intro j
    have hc := Set.Ioo_subset_Icc_self (ht j)
    have hw := hunonzero _ hc
    have hcw : starRingEnd ℂ (u (t j)) ≠ 0 := by simpa using hw
    have hdd := source_correspondence.2.2.2 (u (t j)) (starRingEnd ℂ (u (t j)))
      (y (t j)) hw hcw (hrel _) (hy _ hc) n
    have hconj : (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-starRingEnd ℂ (u (t j))) /
        starRingEnd ℂ (u (t j)) ^ (n + 1) =
        starRingEnd ℂ ((ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u (t j)) /
          u (t j) ^ (n + 1)) := by
      rw [hfacC, hfacC]
      simp
    rw [hconj, (Complex.conj_eq_iff_im.mpr (hreal j)), sub_self] at hdd
    have hdiff : starRingEnd ℂ (u (t j)) - u (t j) ≠ 0 := by
      intro he
      have he' := congrArg Complex.im he
      have hp := himpos _ (ht j)
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at he'
      linarith
    exact (mul_eq_zero.mp hdd).resolve_left
      (mul_ne_zero (mul_ne_zero (by exact_mod_cast (one_div_ne_zero (hdpos _ hc).ne'))
        hdiff) (pow_ne_zero _ (by norm_num)))
  have hdinj : Set.InjOn d (Set.Icc (0 : ℝ) Real.pi) := by
    intro r hr q hq he
    apply Real.strictAntiOn_cos.injOn hr hq
    dsimp only [d] at he
    nlinarith
  have hyinj : Set.InjOn y (Set.Icc (0 : ℝ) Real.pi) := by
    intro r hr q hq he
    apply hdinj hr hq
    exact inv_injective (by simpa only [y, one_div] using he)
  have hybounds : ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      3 - 2 * Real.sqrt 2 < y r ∧ y r < 3 + 2 * Real.sqrt 2 := by
    intro r hr
    have hc := Set.Ioo_subset_Icc_self hr
    have hcos1 : Real.cos r < 1 := by
      simpa using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ hc hr.1
    have hcosm : -1 < Real.cos r := by
      simpa using Real.strictAntiOn_cos hc ⟨Real.pi_pos.le, le_rfl⟩ hr.2
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have ha : 0 < 3 - 2 * Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
    have hab : (3 - 2 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) = 1 := by nlinarith
    have hdlo : 3 - 2 * Real.sqrt 2 < d r := by dsimp [d]; nlinarith
    have hdhi : d r < 3 + 2 * Real.sqrt 2 := by dsimp [d]; nlinarith
    dsimp only [y]
    constructor
    · apply (lt_div_iff₀ (hdpos r hc)).mpr
      nlinarith [mul_lt_mul_of_pos_left hdhi ha]
    · apply (div_lt_iff₀ (hdpos r hc)).mpr
      nlinarith [mul_lt_mul_of_pos_left hdlo (show 0 < 3 + 2 * Real.sqrt 2 by positivity)]
  refine ⟨z, hzinj, fun i => ⟨hz i, hthreshold i⟩, hfacC, y ∘ t, ?_, ?_⟩
  · intro i j hij
    exact htin (hyinj (Set.Ioo_subset_Icc_self (ht i)) (Set.Ioo_subset_Icc_self (ht j)) hij)
  · intro i
    exact ⟨(hybounds _ (ht i)).1, (hybounds _ (ht i)).2, hrootcircle i⟩

#print axioms upper_circle_roots

end D5.S1.Recurrence.Algebraic.DelannoySquareRoots
