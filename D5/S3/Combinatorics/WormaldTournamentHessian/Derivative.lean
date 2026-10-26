/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Derivative
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Derivative
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ImplicitContDiff, mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Misc, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Prod]
   utility: none
   digest: Coordinate slopes, local solutions, and the implicit angular Hessian. -/

/-
admission_basis: escape-witness
Utility is none: arbitrary finite-dimensional identities and complex C2 local
solutions, not finite certificates. Direct frozen D5 dependencies: none.
Live content: WormaldAnalytic.hessian_of_implicit_scalar and hessian_of_implicit_coordinates.
Judgments use the bypass test; binding and normalization do not create content.

name | proof_shape | escape_witness | consumers | frozen deps
polynomialSmooth | bind-only | none | localSolutionOfInvertible, regularLocalSolution | frozen deps: none
  Unfold the determinant polynomial and apply existing smooth finite-sum/product rules.
localSolutionOfInvertible | bind-only | none | regularLocalSolution | frozen deps: none
  Instantiate Mathlib implicitFunction with the supplied invertibility; projections give value, regularity and germ.
det_const_perturb | bind-only | none | det_projection_update | frozen deps: none
  Instantiate the existing rank-one determinant lemma and normalize the Unit determinant.
det_projection_update | bind-only | none | det_doubly_stochastic_cofactor | frozen deps: none
  Instantiate the zero-column-sum cofactor identity and normalize its projection minor.
det_doubly_stochastic_cofactor | bind-only | none | cofactor_eq_of_zero_sums | frozen deps: none
  Apply determinant multiplicativity to the explicit projection and its column update; inverse and sum identities normalize.
cofactor_eq_of_zero_sums | bind-only | none | regularColumnSlopeValue | frozen deps: none
  Shift by the constant projection, normalize row/column sums, and instantiate det_doubly_stochastic_cofactor.
tournamentCoefficientIdentity | bind-only | none | regularColumnSlopeValue, K_resolvent_factorization | frozen deps: none
  Unfold the three possible orientation cases; entrywise normalization.
shiftedNegativeDetNeZero | bind-only | none | regularColumnSlopeValue, regularLocalSolution, calH_closedForm | frozen deps: none
  Transpose the positive shift and invoke shiftedDetNeZero; normalization only.
regularColumnSlopeValue | bind-only | none | regularLocalSolution | frozen deps: none
  Normalize regular row/column sums and the projection-cofactor identity, then apply determinant column linearity; no independent witness is claimed.
appendLastLinear | bind-only (definition) | none | appendLastLinearApply, regularLocalSolution, calH_closedForm | frozen deps: none
  Continuous-linear coordinate-assembly definition; no proved assertion.
appendLastLinearApply | bind-only | none | regularLocalSolution, calH_closedForm | frozen deps: none
  Unfold the two coordinate encodings; extensional normalization.
appendLast_update | bind-only | none | regularLocalSolution | frozen deps: none
  Unfold snoc/update and normalize the last-index cases.
determinant_column_deriv | bind-only | none | K_coordinate_deriv | frozen deps: none
  Use determinant column linearity and the existing affine derivative theorem.
K_coordinate_deriv | bind-only | none | regularLocalSolution | frozen deps: none
  Normalize K under a coordinate update and instantiate determinant_column_deriv.
scalar_map_invertible | bind-only | none | scalar_partial_invertible | frozen deps: none
  Supply the scalar inverse to the existing IsInvertible.of_inverse theorem; both identities normalize.
scalar_partial_invertible | bind-only | none | regularLocalSolution | frozen deps: none
  Instantiate the chain rule and derivative uniqueness; then use the consumed scalar inverse helper.
det_rank_one_sub | bind-only | none | K_resolvent_factorization | frozen deps: none
  Instantiate the existing rank-one determinant formula with Unit factors; normalize the sum of inverse entries.
K_resolvent_factorization | bind-only | none | K_eq_zero_iff_resolvent_sum | frozen deps: none
  Normalize the matrix factorization using tournamentCoefficientIdentity and apply the existing determinant and rank-one laws.
K_eq_zero_iff_resolvent_sum | bind-only | none | localSolution_resolvent_eq | frozen deps: none
  Cancel the proved nonzero factors in K_resolvent_factorization; scalar logical normalization.
localSolution_resolvent_eq | bind-only | none | calH_closedForm | frozen deps: none
  Use existing continuity/eventual-nonzero rules to instantiate K_eq_zero_iff_resolvent_sum on the equation germ.
regularSkewRowSum | bind-only | none | regularSkewColSum, calH_closedForm | frozen deps: none
  Normalize the orientation pair sums and regularDegree into equality of the two degrees.
regularSkewColSum | bind-only | none | calH_closedForm | frozen deps: none
  Transpose the skew row-sum identity; normalization.
regularLocalSolution | bind-only | none | result | frozen deps: none
  Instantiate the supplied IFT helper after the consumed exact slope and smoothness interfaces; no additional escape witness.
WormaldAnalytic.hessian_of_implicit_scalar | content | WormaldAnalytic.actual_hessian: live actual-angular derivative relation; local dh2: elimination of the second implicit derivative | WormaldAnalytic.hessian_of_implicit_coordinates | frozen deps: none
  Own step and propagation: solve the first and second local-equation constraints to eliminate Dh and D2h in the actual angular Hessian; actual_hessian remains live. The conclusion cannot follow by just replacing the local equation with its value at one point.
WormaldAnalytic.hessian_of_implicit_coordinates | content | WormaldAnalytic.hessian_of_implicit_scalar: local-equation-to-angular-Hessian bridge | calH_closedForm | frozen deps: none
  Propagation: the content relation hessian_of_implicit_scalar is consumed before bilinear coordinate normalization; removing it leaves the actual angular Hessian unidentified.
-/

module

public import D5.S3.Combinatorics.WormaldTournamentHessian.Algebra

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Regular tournament Hessians: derivative -/

public section

open scoped Topology ContDiff Matrix Matrix.Norms.Operator
open Matrix Filter
open D5.S3.Combinatorics.WormaldTournamentHessian.Defs
open D5.S3.Combinatorics.WormaldTournamentHessian.Algebra

namespace D5.S3.Combinatorics.WormaldTournamentHessian.Derivative

private theorem polynomialSmooth {d : ℕ} (A : Fin d → Fin d → Bool) :
    ContDiff ℂ 2 (K A) := by
  classical
  unfold K
  simp only [Matrix.det_apply, Matrix.sub_apply, Matrix.mul_diagonal]
  fun_prop

private theorem localSolutionOfInvertible {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (hi : (fderiv ℂ
      (fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2))
      ((fun _ => z d), z d) ∘L
        ContinuousLinearMap.inr ℂ (Fin (d-1) → ℂ) ℂ).IsInvertible) :
    ∃ h, IsLocalSolution A h := by
  have happ : appendLast (fun _ : Fin (d-1) => z d) (z d) = (fun _ => z d) := by
    funext i
    simp [appendLast, Fin.snoc]
  have hK : K A (appendLast (fun _ => z d) (z d)) = 0 := by
    rw [happ]
    exact determinantAtBase A hd hA
  have hc : ContDiffAt ℂ 2
      (fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2))
      ((fun _ => z d), z d) := by
    apply (polynomialSmooth A).contDiffAt.comp
    apply contDiffAt_pi.2
    intro i
    unfold appendLast Fin.snoc
    split_ifs <;> simp only [cast_eq] <;> fun_prop
  have hn : (2 : ℕ∞ω) ≠ 0 := by norm_num
  refine ⟨hc.implicitFunction hn hi, hc.implicitFunction_apply_self hn hi,
    hc.contDiffAt_implicitFunction hn hi, ?_⟩
  have he := hc.eventually_apply_implicitFunction hn hi
  simpa only [hK] using he

private theorem det_const_perturb (n : ℕ) (c : ℂ) :
    (1 + (Matrix.of (fun _ _ : Fin n => c)) : Matrix (Fin n) (Fin n) ℂ).det = 1 + n * c := by
  have he : (Matrix.of (fun _ _ : Fin n => c)) =
      Matrix.replicateCol Unit (fun _ : Fin n => c) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]

private theorem det_projection_update (n : ℕ) (l : Fin (n+1)) (v : Fin (n+1) → ℂ) :
    ((1 - (Matrix.of (fun _ _ : Fin (n+1) => (1 / (n+1 : ℂ)))) :
      Matrix (Fin (n+1)) (Fin (n+1)) ℂ).updateCol l v).det =
      (∑ i, v i) / (n+1 : ℂ) := by
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    (1 - (Matrix.of (fun _ _ : Fin (n+1) => (1 / (n+1 : ℂ))))).updateCol l v
  have hc : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hcol : ∀ j ≠ l, ∑ i, M i j = 0 := by
    intro j hj
    simp [M, Matrix.updateCol_apply, hj, Matrix.sub_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, hc]
  have hh := Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
    M l l hcol
  have hminor : M.submatrix l.succAbove l.succAbove =
      1 + (Matrix.of (fun _ _ : Fin n => -(1 / (n+1 : ℂ)))) := by
    ext i j
    simp [M, Matrix.submatrix_apply, Matrix.updateCol_apply,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Fin.succAbove_ne,
      Fin.succAbove_right_inj, sub_eq_add_neg]
  have hsign : (-1 : ℂ) ^ ((l : ℕ) + (l : ℕ)) = 1 := by
    exact Even.neg_one_pow ⟨l.val, rfl⟩
  dsimp [M] at hh ⊢
  rw [hsign, one_mul, hminor, det_const_perturb] at hh
  simp only [Matrix.updateCol_self] at hh
  rw [hh]
  field_simp
  ring

private theorem det_doubly_stochastic_cofactor (n : ℕ) (l : Fin (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hdet : A.det ≠ 0)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    ((A - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).updateCol l
      (Pi.single l 1)).det = A.det / (n+1 : ℂ) := by
  let P : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    1 - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))
  let v : Fin (n+1) → ℂ := A⁻¹ *ᵥ Pi.single l 1
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hv : A *ᵥ v = Pi.single l 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hsum : ∑ i, v i = 1 := by
    calc
      _ = ∑ i, (A *ᵥ v) i := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hcol, one_mul]
      _ = 1 := by rw [hv]; simp
  have hAP : A * P = A - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [← Finset.sum_mul, hrow, one_mul]
  have he := Matrix.mul_updateCol A P l v
  rw [hv, hAP] at he
  rw [← he, Matrix.det_mul]
  rw [show P = 1 - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) from rfl,
    det_projection_update, hsum]
  ring

private theorem cofactor_eq_of_zero_sums (n : ℕ) (l : Fin (n+1))
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hdet : (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det ≠ 0)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0) :
    (B.updateCol l (Pi.single l 1)).det =
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det / (n+1 : ℂ) := by
  have hc : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have ha : ∀ i, (∑ j : Fin (n+1),
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) i j) = 1 := by
    intro i
    simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib, hrow, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hb : ∀ j, (∑ i : Fin (n+1),
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) i j) = 1 := by
    intro j
    simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib, hcol, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  simpa only [add_sub_cancel_right] using
    det_doubly_stochastic_cofactor n l (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) hdet ha hb

private theorem tournamentCoefficientIdentity {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) :
    (2 : ℂ) • ((1/2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) =
        Matrix.of (fun _ _ => 1) + (skewAdjacency A).map (Int.castRingHom ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, hA.1, adjacency, skewAdjacency]
  · have h := hA.2.1 i j hij
    cases hai : A i j <;> cases haj : A j i <;>
      simp_all [Matrix.smul_apply, Matrix.one_apply, adjacency, skewAdjacency] <;> norm_num


theorem shiftedNegativeDetNeZero {d : ℕ} (A : Fin d → Fin d → Bool) :
    ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0 := by
  let S := (skewAdjacency A).map (Int.castRingHom ℂ)
  have hs : S.transpose = -S := by
    ext i j
    simp [S, skewAdjacency, adjacency]
  have ht : (S + (d : ℂ) • 1).transpose = (d : ℂ) • 1 - S := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hs]
    abel
  rw [← ht, Matrix.det_transpose]
  exact shiftedDetNeZero A (d : ℂ) (Complex.norm_natCast d)


private theorem regularColumnSlopeValue {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) (l : Fin d) :
    ((1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) * diagonal (fun _ => z d)).updateCol l
        (fun i => ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) i l)).det =
      (((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det) / (2 * (d : ℂ)^d) := by
  cases d with
  | zero => omega
  | succ n =>
    obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
    let C : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      (1 / 2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
    let B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      1 - C * diagonal (fun _ => z (n+1))
    let S := (skewAdjacency A).map (Int.castRingHom ℂ)
    have hd0 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hdc : (n+1 : ℂ) = 2 * r + 1 := by exact_mod_cast hdr
    have hrowC : ∀ i, ∑ j, C i j = 1 / 2 + (r : ℂ) := by
      intro i
      have hi : (∑ j, ((adjacency A i j : ℤ) : ℂ)) = r := by exact_mod_cast hr i
      simp only [C, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.map_apply]
      simpa [Matrix.one_apply] using congrArg (fun x : ℂ => 1 / 2 + x) hi
    have hpair : ∀ i j, C i j + C j i = 1 := by
      intro i j
      by_cases hij : i = j
      · subst j
        norm_num [C, adjacency, hA.1]
      · have h := hA.2.1 i j hij
        cases hai : A i j <;> cases haj : A j i <;>
          simp_all [C, Matrix.one_apply, adjacency, hij, Ne.symm hij]
    have hcolC : ∀ j, ∑ i, C i j = 1 / 2 + (r : ℂ) := by
      intro j
      have hh : (∑ i, C i j) + (∑ i, C j i) = (n+1 : ℂ) := by
        rw [← Finset.sum_add_distrib]
        simp_rw [hpair]
        simp
      rw [hrowC] at hh
      linear_combination hh + hdc
    have hnorm : (1 / 2 + (r : ℂ)) * z (n+1) = 1 := by
      unfold z
      push_cast
      field_simp
      linear_combination -hdc
    have hrowB : ∀ i, ∑ j, B i j = 0 := by
      intro i
      simp only [B, Matrix.sub_apply, Matrix.mul_diagonal, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hrowC, hnorm]
      simp [Matrix.one_apply]
    have hcolB : ∀ j, ∑ i, B i j = 0 := by
      intro j
      simp only [B, Matrix.sub_apply, Matrix.mul_diagonal, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hcolC, hnorm]
      simp [Matrix.one_apply]
    have htwo : ∀ i j, 2 * C i j = 1 + S i j := by
      intro i j
      simpa only [C, S, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.of_apply] using congrArg (fun M => M i j) (tournamentCoefficientIdentity A hA)
    have hmat : B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) =
        (1 / (n+1 : ℂ)) • ((n+1 : ℂ) • 1 - S) := by
      ext i j
      simp only [B, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.smul_apply, smul_eq_mul]
      unfold z
      push_cast
      field_simp
      linear_combination -(htwo i j)
    have hdetQ : ((n+1 : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S).det ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using shiftedNegativeDetNeZero A
    have hdetB : (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det ≠ 0 := by
      rw [hmat, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (div_ne_zero one_ne_zero hd0)) hdetQ
    have hcof := cofactor_eq_of_zero_sums n l B hdetB hrowB hcolB
    have hB : B.det = 0 := determinantAtBase A hd hA
    have he : (Pi.single l 1 : Fin (n+1) → ℂ) =
        (fun i => B i l) + z (n+1) • (fun i => C i l) := by
      ext i
      simp [B, Matrix.mul_diagonal, Matrix.one_apply, Pi.single_apply, eq_comm] <;> ring
    have hlinear : (B.updateCol l (Pi.single l 1)).det =
        z (n+1) * (B.updateCol l (fun i => C i l)).det := by
      rw [he, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
        Matrix.updateCol_eq_self, hB, zero_add]
    have hz0 : z (n+1) ≠ 0 := by
      simpa only [z, Nat.cast_add, Nat.cast_one] using
        div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hd0
    simp only [Nat.cast_add, Nat.cast_one]
    change (B.updateCol l (fun i => C i l)).det =
      (((n+1 : ℂ) • 1 - S).det) / (2 * (n+1 : ℂ)^(n+1))
    apply (mul_left_cancel₀ hz0)
    calc
      z (n+1) * (B.updateCol l (fun i => C i l)).det =
          (B.updateCol l (Pi.single l 1)).det := hlinear.symm
      _ = (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det / (n+1 : ℂ) := hcof
      _ = z (n+1) * (((n+1 : ℂ) • 1 - S).det /
          (2 * (n+1 : ℂ) ^ (n+1))) := by
        rw [hmat, Matrix.det_smul, Fintype.card_fin, one_div_pow]
        unfold z
        push_cast
        field_simp
        <;> ring


@[expose]
noncomputable def appendLastLinear (d : ℕ) :
    ((Fin (d-1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    @Fin.snoc (d-1) (fun _ => ((Fin (d-1) → ℂ) × ℂ) →L[ℂ] ℂ)
      (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _))
      (ContinuousLinearMap.snd ℂ _ _) (Fin.ofNat (d-1+1) i.val)

theorem appendLastLinearApply {d : ℕ} (p : (Fin (d-1) → ℂ) × ℂ) :
    appendLastLinear d p = appendLast p.1 p.2 := by
  ext i
  simp only [appendLastLinear, ContinuousLinearMap.pi_apply, appendLast]
  unfold Fin.snoc
  split_ifs <;> rfl

private theorem appendLast_update {d : ℕ} (hd : 1 ≤ d) (t : ℂ) :
    appendLast (fun _ => z d) t =
      Function.update (fun _ => z d) (⟨d-1, by omega⟩ : Fin d) t := by
  classical
  ext i
  have hd' : d - 1 + 1 = d := by omega
  have hi : i.val < d-1+1 := by omega
  by_cases h : i.val < d-1
  · have hn : i ≠ (⟨d-1, by omega⟩ : Fin d) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = d-1 at hv
      omega
    simp [appendLast, Fin.snoc, Fin.ofNat, Nat.mod_eq_of_lt hi, h, hn]
  · have he : i = (⟨d-1, by omega⟩ : Fin d) := by
      apply Fin.ext
      change i.val = d-1
      omega
    rw [he]
    simp [appendLast, Fin.snoc, Fin.ofNat, Nat.mod_eq_of_lt hi]

private theorem determinant_column_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (j : n) (u v : n → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => (B.updateCol j (u + s • v)).det)
      (B.updateCol j v).det t := by
  simp_rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  simpa using ((hasDerivAt_id t).mul_const (B.updateCol j v).det).const_add
    (B.updateCol j u).det

private theorem K_coordinate_deriv {d : ℕ} (A : Fin d → Fin d → Bool)
    (y : Fin d → ℂ) (j : Fin d) (t : ℂ) :
    HasDerivAt (fun s : ℂ => K A (Function.update y j s))
      (-((1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) * diagonal y).updateCol j
        (fun i => ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) i j)).det) t := by
  let C : Matrix (Fin d) (Fin d) ℂ :=
    (1 / 2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
  let B : Matrix (Fin d) (Fin d) ℂ := 1 - C * diagonal y
  have he (s : ℂ) : K A (Function.update y j s) =
      (B.updateCol j ((fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) +
        s • (fun i => -C i j))).det := by
    change (1 - C * diagonal (Function.update y j s)).det = _
    congr 1
    ext i k
    by_cases hk : k = j
    · subst k
      simp [K, B, Matrix.updateCol, Matrix.mul_diagonal, C]
      ring
    · simp [K, B, Matrix.updateCol, Matrix.mul_diagonal, hk, Ne.symm hk, C]
  simp_rw [he]
  convert determinant_column_deriv B j (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j)
    (fun i => -C i j) t using 1
  symm
  have hneg : (fun i => -C i j) = (-1 : ℂ) • (fun i => C i j) := by ext i; simp
  rw [hneg, Matrix.det_updateCol_smul]
  simp [B, C]

private theorem scalar_map_invertible (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) :
    L.IsInvertible := by
  have hx (x : ℂ) : L x = x * L 1 := by simpa using L.map_smul x 1
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [hx ((L 1)⁻¹ * x)]
    field_simp [hL]
    <;> ring
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [hx x]
    field_simp [hL]
    <;> ring

private theorem scalar_partial_invertible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E × ℂ → ℂ) (y : E) (t c : ℂ)
    (hF : DifferentiableAt ℂ F (y,t))
    (hc : HasDerivAt (fun s : ℂ => F (y,s)) c t) (hc0 : c ≠ 0) :
    (fderiv ℂ F (y,t) ∘L ContinuousLinearMap.inr ℂ E ℂ).IsInvertible := by
  apply scalar_map_invertible
  have he := hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  have hu := he.unique hc
  simpa using hu.trans_ne hc0

private theorem det_rank_one_sub {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q.det ≠ 0) :
    (Q - Matrix.of (fun _ _ => 1)).det =
      Q.det * (1 - ∑ i, ∑ j, Q⁻¹ i j) := by
  have he : (Q - Matrix.of (fun _ _ => 1)) = Q +
      Matrix.replicateCol Unit (fun _ : Fin d => (-1 : ℂ)) *
        Matrix.replicateRow Unit (fun _ : Fin d => (1 : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [he, Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hQ)]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, Finset.sum_neg_distrib, Finset.sum_comm, sub_eq_add_neg]


private theorem K_resolvent_factorization {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) (y : Fin d → ℂ) (hy : ∀ j, y j ≠ 0)
    (hQ : (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    K A y = (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det *
      (1 - ∑ i, ∑ j, (diagonal (fun j => 2 / y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j) * ∏ j, (y j / 2) := by
  let C : Matrix (Fin d) (Fin d) ℂ :=
    (1/2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
  let Q := diagonal (fun j => 2 / y j) -
    (skewAdjacency A).map (Int.castRingHom ℂ)
  have hf : 1 - C * diagonal y =
      (diagonal (fun j => 2 / y j) - (2 : ℂ) • C) * diagonal (fun j => y j / 2) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Matrix.one_apply_eq]
      field_simp [hy i]
      <;> ring
    · simp only [hij, ite_false, Matrix.one_apply_ne hij]
      ring
  have hc : (2 : ℂ) • C = Matrix.of (fun _ _ => 1) +
      (skewAdjacency A).map (Int.castRingHom ℂ) := tournamentCoefficientIdentity A hA
  change (1 - C * diagonal y).det = _
  rw [hf, hc]
  have he : diagonal (fun j => 2 / y j) -
      (Matrix.of (fun _ _ => 1) + (skewAdjacency A).map (Int.castRingHom ℂ)) =
        Q - Matrix.of (fun _ _ => 1) := by dsimp [Q]; abel
  rw [he, Matrix.det_mul, det_rank_one_sub Q hQ, Matrix.det_diagonal]

private theorem K_eq_zero_iff_resolvent_sum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) (y : Fin d → ℂ) (hy : ∀ j, y j ≠ 0)
    (hQ : (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    K A y = 0 ↔ ∑ i, ∑ j, (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j = 1 := by
  rw [K_resolvent_factorization A hA y hy hQ]
  have hp : (∏ j, y j / 2) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ =>
    div_ne_zero (hy j) (by norm_num)
  simp only [mul_eq_zero, hQ, hp, false_or, or_false, sub_eq_zero]
  exact eq_comm

theorem localSolution_resolvent_eq {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (h : (Fin (d-1) → ℂ) → ℂ) (hh : IsLocalSolution A h)
    (hQ0 : (diagonal (fun _ : Fin d => 2 / z d) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    ∀ᶠ y in 𝓝 (fun _ : Fin (d-1) => z d),
      ∑ i, ∑ j, (diagonal (fun j => 2 / appendLast y (h y) j) -
        (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j = 1 := by
  let g := fun y : Fin (d-1) → ℂ => appendLast y (h y)
  let y0 := fun _ : Fin (d-1) => z d
  have hz0 : z d ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast (by omega : d ≠ 0))
  have hg0 : g y0 = (fun _ => z d) := by
    dsimp [g, y0]
    rw [hh.1]
    ext i
    simp [appendLast, Fin.snoc]
  have hg : ContinuousAt g y0 := by
    apply continuousAt_pi.2
    intro i
    dsimp [g]
    unfold appendLast Fin.snoc
    split_ifs <;> simp only [cast_eq]
    · exact (continuous_apply _).continuousAt
    · exact hh.2.1.continuousAt
  have hn (i : Fin d) : g y0 i ≠ 0 := by rw [hg0]; exact hz0
  have hy : ∀ᶠ y in 𝓝 y0, ∀ i, g y i ≠ 0 :=
    eventually_all.2 fun i => ((continuous_apply i).continuousAt.comp hg).eventually_ne (hn i)
  have hcont : ContinuousAt (fun y =>
      (diagonal (fun j => 2 / g y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det) y0 := by
    apply continuous_id.matrix_det.continuousAt.comp
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact (continuousAt_const.div ((continuous_apply j).continuousAt.comp hg) (hn j)).sub
        continuousAt_const
    · simp only [hij, ite_false]
      exact continuousAt_const
  have hdet : ∀ᶠ y in 𝓝 y0,
      (diagonal (fun j => 2 / g y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0 := by
    apply hcont.eventually_ne
    simpa only [hg0] using hQ0
  filter_upwards [hh.2.2, hy, hdet] with y hK hny hdy
  exact (K_eq_zero_iff_resolvent_sum A hA (g y) hny hdy).mp hK



theorem regularSkewRowSum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∀ i, ∑ j, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j = 0 := by
  obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
  have hpair : ∀ i j, adjacency A i j + adjacency A j i =
      (if i = j then 0 else 1 : ℤ) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [adjacency, hA.1]
    · have h := hA.2.1 i j hij
      cases hai : A i j <;> cases haj : A j i <;> simp_all [adjacency]
  have hcol : ∀ j, ∑ i, adjacency A i j = (r : ℤ) := by
    intro j
    have hpairsum : (∑ i : Fin d, (if i = j then 0 else 1 : ℤ)) = d - 1 := by
      calc
        _ = ∑ i : Fin d, (1 - (if i = j then 1 else 0) : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> simp_all
        _ = _ := by simp [Finset.sum_sub_distrib]
    have hh : (∑ i, adjacency A i j) + (∑ i, adjacency A j i) = (d : ℤ) - 1 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hpair]
      exact hpairsum
    have hdc : (d : ℤ) = 2 * r + 1 := by exact_mod_cast hdr
    rw [hr] at hh
    linarith
  intro i
  have hh : ∑ j, skewAdjacency A i j = 0 := by
    simp only [skewAdjacency, Matrix.sub_apply, Matrix.transpose_apply,
      Finset.sum_sub_distrib, hr, hcol, sub_self]
  change (∑ j, (skewAdjacency A i j : ℂ)) = 0
  exact_mod_cast hh

theorem regularSkewColSum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∀ j, ∑ i, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j = 0 := by
  intro j
  have hs : ∀ i, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j =
      -((skewAdjacency A).map (Int.castRingHom ℂ)) j i := by
    intro i
    simp [skewAdjacency, adjacency]
  simp_rw [hs, Finset.sum_neg_distrib, regularSkewRowSum A hd hA, neg_zero]


theorem regularLocalSolution {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : ∃ h, IsLocalSolution A h := by
  let l : Fin d := ⟨d-1, by omega⟩
  let c : ℂ := -(((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
    (skewAdjacency A).map (Int.castRingHom ℂ)).det / (2 * (d : ℂ)^d))
  have hc : c ≠ 0 := by
    apply neg_ne_zero.mpr
    exact div_ne_zero (shiftedNegativeDetNeZero A)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast (by omega : d ≠ 0))))
  have hlast : HasDerivAt (fun s : ℂ => K A (appendLast (fun _ => z d) s)) c (z d) := by
    have he := K_coordinate_deriv A (fun _ => z d) l (z d)
    rw [regularColumnSlopeValue A hd hA l] at he
    simpa only [appendLast_update (by omega : 1 ≤ d)] using he
  let F := fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2)
  have hF : DifferentiableAt ℂ F ((fun _ => z d), z d) := by
    have he := ((polynomialSmooth A).differentiable (by norm_num)).comp
      (appendLastLinear d).differentiable
    have hp := he.differentiableAt (x := ((fun _ => z d), z d))
    simpa only [Function.comp_def, appendLastLinearApply] using hp
  exact localSolutionOfInvertible A hd hA
    (scalar_partial_invertible F (fun _ => z d) (z d) c hF hlast hc)


open scoped Topology ContDiff
open Filter

namespace WormaldAnalytic

open Defs.WormaldAnalytic

private theorem hessian_of_implicit_scalar {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (L : ((Fin (d - 1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ))
    (α : (Fin d → ℂ) → ℂ)
    (hα : ContDiffAt ℂ 2 α (L ((fun _ => z d), z d)))
    (he : ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), α (L (y, h y)) = 1)
    (c : ℂ) (hc : c ≠ 0)
    (hfirst : ∀ j, fderiv ℂ α (L ((fun _ => z d), z d))
      (L (Pi.single j 1, 0)) = c)
    (hlast : fderiv ℂ α (L ((fun _ => z d), z d)) (L (0, 1)) = c)
    (j k : Fin (d - 1)) :
    hessian h j k = 1 + (if j = k then 1 else 0) + (z d / c) *
      second (𝕜 := ℂ) α (L ((fun _ => z d), z d))
        (L (Pi.single j 1, -1)) (L (Pi.single k 1, -1)) := by
  let x : Fin (d - 1) → ℂ := fun _ => z d
  let F₀ : ((Fin (d - 1) → ℂ) × ℂ) → ℂ := fun p => α (L p) - 1
  change (∀ j, fderiv ℂ α (L (x, z d)) (L (Pi.single j 1, 0)) = c) at hfirst
  change fderiv ℂ α (L (x, z d)) (L (0, 1)) = c at hlast
  have hh0 : h x = z d := hh.1
  have hhC : ContDiffAt ℂ 2 h x := hh.2.1
  have hα' : ContDiffAt ℂ 2 α (L (x, h x)) := by simpa [hh0] using hα
  have hF : ContDiffAt ℂ 2 F₀ (x, h x) := by
    exact (hα'.comp (x, h x) L.contDiff.contDiffAt).sub contDiffAt_const
  have hzero : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he] with y hy
    dsimp [F₀]
    rw [hy, sub_self]
  have dF (v : (Fin (d - 1) → ℂ) × ℂ) :
      fderiv ℂ F₀ (x, h x) v = fderiv ℂ α (L (x, z d)) (L v) := by
    change fderiv ℂ (fun p => α (L p) - 1) (x, h x) v = _
    rw [fderiv_sub_const]
    have hcomp := (hα'.differentiableAt (by norm_num)).hasFDerivAt.comp (x, h x)
      L.hasFDerivAt
    change HasFDerivAt (fun p => α (L p)) _ (x, h x) at hcomp
    rw [hcomp.fderiv]
    simp [hh0]
  have hq : fderiv ℂ F₀ (x, h x) (0, 1) ≠ 0 := by
    rw [dF, hlast]
    exact hc
  have dh (i : Fin (d - 1)) : fderiv ℂ h x (Pi.single i 1) = -1 := by
    have H := implicit_first_scalar hhC hF hzero hq (Pi.single i 1)
    rw [dF, dF, hfirst, hlast] at H
    simpa [hc] using H
  have h2F (v w : (Fin (d - 1) → ℂ) × ℂ) :
      second (𝕜 := ℂ) F₀ (x, h x) v w =
        second (𝕜 := ℂ) α (L (x, z d)) (L v) (L w) := by
    change second (𝕜 := ℂ) (fun p => α (L p) - 1) (x, h x) v w = _
    rw [second_sub_const]
    have H := second_comp_clm L α (x, h x) v w hα'
    change second (𝕜 := ℂ) (fun p => α (L p)) (x, h x) v w = _ at H
    simpa [hh0] using H
  have dh2 := implicit_second_scalar hhC hF hzero hq (Pi.single j 1) (Pi.single k 1)
  rw [dh j, dh k, dF, hlast, h2F] at dh2
  dsimp only [x] at dh dh2
  rw [actual_hessian hd hh, dh j, dh k, dh2]
  split_ifs <;> ring

end WormaldAnalytic

namespace WormaldAnalytic

open Defs.WormaldAnalytic

theorem hessian_of_implicit_coordinates {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (L : ((Fin (d - 1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ))
    (ι : Fin (d - 1) → Fin d) (last : Fin d)
    (hLj : ∀ j, L (Pi.single j 1, 0) = Pi.single (ι j) 1)
    (hLl : L (0, 1) = Pi.single last 1)
    (α : (Fin d → ℂ) → ℂ)
    (hα : ContDiffAt ℂ 2 α (L ((fun _ => z d), z d)))
    (he : ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), α (L (y, h y)) = 1)
    (c : ℂ) (hc : c ≠ 0)
    (hfirst : ∀ i, fderiv ℂ α (L ((fun _ => z d), z d)) (Pi.single i 1) = c)
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hsecond : ∀ i l, second (𝕜 := ℂ) α (L ((fun _ => z d), z d))
      (Pi.single i 1) (Pi.single l 1) = M i l)
    (j k : Fin (d - 1)) :
    hessian h j k = 1 + (if j = k then 1 else 0) + (z d / c) *
      (M (ι j) (ι k) - M (ι j) last - M last (ι k) + M last last) := by
  have hFj (i : Fin (d - 1)) : fderiv ℂ α (L ((fun _ => z d), z d))
      (L (Pi.single i 1, 0)) = c := by rw [hLj]; exact hfirst (ι i)
  have hFl : fderiv ℂ α (L ((fun _ => z d), z d)) (L (0, 1)) = c := by
    rw [hLl]; exact hfirst last
  rw [hessian_of_implicit_scalar hd hh L α hα he c hc hFj hFl]
  have hdiff (i : Fin (d - 1)) : L (Pi.single i 1, -1) =
      Pi.single (ι i) (1 : ℂ) - Pi.single last 1 := by
    have hp : (Pi.single i (1 : ℂ), (-1 : ℂ)) =
        (Pi.single i (1 : ℂ), (0 : ℂ)) - ((0 : Fin (d - 1) → ℂ), (1 : ℂ)) := by simp
    rw [hp, map_sub, hLj, hLl]
  rw [hdiff, hdiff, second_sub_sub hα, hsecond, hsecond, hsecond, hsecond]

end WormaldAnalytic

end D5.S3.Combinatorics.WormaldTournamentHessian.Derivative
