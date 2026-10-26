/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The analytic Hessian closed form and Wormald rational-square theorem. -/

/-
admission_basis: open-problem-resolution (#21941; Proved)
Utility is none: arbitrary finite-dimensional identities and complex C2 local
solutions, not finite certificates. Direct frozen D5 dependencies: none.
Live content: calH_closedForm and result.
Judgments use the bypass test; binding and normalization do not create content.

name | proof_shape | escape_witness | consumers | frozen deps
calH_closedForm | content | local hmat: actual analytic Hessian equals the negative resolvent difference minor; WormaldAnalytic.hessian_of_implicit_coordinates; alpha_second_const | result | frozen deps: none
  Own step and propagation: identify the actual analytic Hessian with the negative difference minor of T, using the implicit-coordinate bridge and alpha_second_const, then take determinants. The analytic-to-matrix identification is live; determinant identities alone do not identify calH.
result | content | calH_closedForm: live analytic-to-quadratic-determinant identity | terminal: Conjecture 6 | frozen deps: none
  Propagation: calH_closedForm supplies the actual analytic determinant needed by both nonvanishing and rational squareness. The algebraic square without this bridge concerns a different expression and cannot bypass it.
-/

module

public import D5.S3.Combinatorics.WormaldTournamentHessian.Derivative


/-! # Regular tournament Hessians: result -/

public section

open scoped Topology ContDiff Matrix Matrix.Norms.Operator
open Matrix Filter
open D5.S3.Combinatorics.WormaldTournamentHessian.Defs
open D5.S3.Combinatorics.WormaldTournamentHessian.Algebra
open D5.S3.Combinatorics.WormaldTournamentHessian.Derivative

namespace D5.S3.Combinatorics.WormaldTournamentHessian.Result

theorem calH_closedForm {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (h : (Fin (d-1) → ℂ) → ℂ) (hh : IsLocalSolution A h) :
    calH h = (d : ℂ) *
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det := by
  cases d with
  | zero => omega
  | succ n =>
    let D : ℂ := ((n+1 : ℕ) : ℂ)
    let b : ℂ := z (n+1)
    let S := (skewAdjacency A).map (Int.castRingHom ℂ)
    let Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := D • 1 - S
    let V := Q⁻¹
    let T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := 1-D • (V+V.transpose)
    let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)
    let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := Matrix.of fun i l =>
      (b^2)⁻¹ * (V i l + V l i) - (if i = l then b⁻¹ else 0)
    let L := appendLastLinear (n+1)
    have hD : D ≠ 0 := by
      dsimp [D]
      exact_mod_cast Nat.succ_ne_zero n
    have hb : b ≠ 0 := div_ne_zero (by norm_num) hD
    have htwo : 2 / b = D := by
      dsimp [b, z, D]
      field_simp
    have hrec : D⁻¹ = b / 2 := by
      dsimp [b, z, D]
      field_simp
      <;> ring
    have hQ : Q.det ≠ 0 := shiftedNegativeDetNeZero A
    have hQeq : inverseQ S (fun _ => b) = Q := by
      ext i j
      simp only [inverseQ, Q, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, htwo]
      split_ifs <;> simp
    have hQi : (inverseQ S (fun _ => b)).det ≠ 0 := by rwa [hQeq]
    have hSr : ∀ i, ∑ j, S i j = 0 := regularSkewRowSum A hd hA
    have hSc : ∀ j, ∑ i, S i j = 0 := regularSkewColSum A hd hA
    have hQr : ∀ i, ∑ j, Q i j = D := by
      intro i
      simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hSr]
    have hQc : ∀ j, ∑ i, Q i j = D := by
      intro j
      simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hSc]
    have hVr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2 := by
      simpa only [hQeq, hrec] using inverse_row_sum Q D hD hQ hQr
    have hVc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2 := by
      simpa only [hQeq, hrec] using inverse_col_sum Q D hD hQ hQc
    have hLsnoc (v : Fin n → ℂ) (s : ℂ) : L (v,s) = Fin.snoc v s := by
      rw [show L = appendLastLinear (n+1) from rfl, appendLastLinearApply]
      ext i
      change (@Fin.snoc n (fun _ => ℂ) v s) (Fin.ofNat (n+1) i.val) =
        (@Fin.snoc n (fun _ => ℂ) v s) i
      congr 1
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    have hL0 : L ((fun _ => b), b) = (fun _ => b) := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    have hLj (j : Fin n) : L (Pi.single j 1, 0) = Pi.single j.castSucc 1 := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp
      · simp [Pi.single_apply]
    have hLl : L (0, 1) = Pi.single (Fin.last n) 1 := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [Pi.single_apply]
    have hα : ContDiffAt ℂ 2 (alpha S) (L ((fun _ => b), b)) := by
      rw [hL0]
      exact alpha_contDiffAt S (fun _ => b) (fun _ => hb) hQi
    have hg : ∀ᶠ y in 𝓝 (fun _ : Fin n => b), alpha S (L (y, h y)) = 1 := by
      have he := localSolution_resolvent_eq A hd hA h hh hQi
      filter_upwards [he] with y hy
      simpa only [show L = appendLastLinear (n+1) from rfl,
        appendLastLinearApply, alpha, inverseQ] using hy
    have hfirst (i : Fin (n+1)) :
        fderiv ℂ (alpha S) (L ((fun _ => b), b)) (Pi.single i 1) = 1/2 := by
      rw [hL0]
      exact alpha_first_const S b hb hQi hVr hVc i
    have hsecond (i l : Fin (n+1)) :
        Defs.WormaldAnalytic.second (𝕜 := ℂ) (alpha S) (L ((fun _ => b), b))
          (Pi.single i 1) (Pi.single l 1) = M i l := by
      rw [hL0]
      simpa only [Defs.WormaldAnalytic.second, M, Matrix.of_apply, hQeq] using
        alpha_second_const S b hb hQi hVr hVc i l
    have hlastne (i : Fin n) : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    have hcastlast (i : Fin n) : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
    have hmat : hessian (d := n+1) h = -H := by
      ext j k
      have he := Derivative.WormaldAnalytic.hessian_of_implicit_coordinates hd hh L
        (fun j : Fin n => j.castSucc) (Fin.last n) hLj hLl
        (alpha S) hα hg (1/2) (by norm_num) hfirst M hsecond j k
      simp only [H, Matrix.neg_apply, Matrix.of_apply]
      rw [he]
      change 1 + (if j = k then 1 else 0) + (b / (1/2)) *
        (M j.castSucc k.castSucc - M j.castSucc (Fin.last n) -
          M (Fin.last n) k.castSucc + M (Fin.last n) (Fin.last n)) =
        -(T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
          T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n))
      simp only [M, T, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.one_apply,
        Fin.castSucc_inj, hcastlast, hlastne, ite_false, ite_true]
      rw [← htwo]
      by_cases hjk : j = k <;> simp only [hjk, ite_true, ite_false]
      <;> field_simp [hb] <;> ring
    have hS : S.transpose = -S := by
      ext i j
      simp [S, skewAdjacency, adjacency]
    have hn : Even n := by
      obtain ⟨r, hr⟩ := regularOdd A hd hA
      refine ⟨r, ?_⟩
      omega
    have hdet := skew_difference_det n S D hD hS (regularOdd A hd hA) hQ hSr
    change (hessian (d := n+1) h).det = D * (D^2 • 1 + S*S).det / (D^2 • 1-S*S).det
    rw [hmat, Matrix.det_neg, Fintype.card_fin]
    simp only [Nat.add_sub_cancel, hn.neg_one_pow, one_mul]
    simpa only [H, T, V, Q, D, Nat.cast_add, Nat.cast_one] using hdet

theorem result : claim := by
  intro d hd A hA
  refine ⟨regularLocalSolution A hd hA, ?_⟩
  intro h hh
  let N : ℂ := ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
    (skewAdjacency A).map (Int.castRingHom ℂ) *
      (skewAdjacency A).map (Int.castRingHom ℂ)).det
  let D : ℂ := ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
    (skewAdjacency A).map (Int.castRingHom ℂ) *
      (skewAdjacency A).map (Int.castRingHom ℂ)).det
  obtain ⟨q, hq0, hq⟩ := regularAlgebraicSquare A hd hA
  change N / D = (q : ℂ)^2 at hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hratio : N / D ≠ 0 := by rw [hq]; exact pow_ne_zero _ hqc
  have hN : N ≠ 0 := by
    intro hn
    exact hratio (by rw [hn, zero_div])
  have hD : D ≠ 0 := by
    intro hd
    exact hratio (by rw [hd, div_zero])
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hclosed : calH h = (d : ℂ) * D / N := calH_closedForm A hd hA h hh
  refine ⟨?_, q, ?_⟩
  · rw [hclosed]
    exact div_ne_zero (mul_ne_zero hd0 hD) hN
  · rw [hclosed, ← hq]
    field_simp [hd0, hN, hD]

end D5.S3.Combinatorics.WormaldTournamentHessian.Result
