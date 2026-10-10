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

end D5.S1.Recurrence.Algebraic.DelannoySquareRoots
