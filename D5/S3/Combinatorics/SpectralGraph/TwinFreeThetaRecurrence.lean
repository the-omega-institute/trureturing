/- GID: D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuant collision exclusion and theta coordinate dimensions. -/

/-
admission_basis: escape-witness
escape_witness: model_nonsingular_finrank
utility: none (unbounded theta-family statements and their consumed helpers).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23310
Frozen dependency declarations:
D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer @ sha256:9c75926175b4e0e95c8a5df62503e74ba85b035e570897bfdc462d1888d30f30
Declaration judgements (definitions carry no independent mathematical claim):
p_zero | proof_shape: bind-only | escape_witness: none | consumer: p_even_growth
p_one | proof_shape: bind-only | escape_witness: none | consumer: p_even_growth
p_step | proof_shape: bind-only | escape_witness: none | consumer: p_even_step
p_invariant | proof_shape: bind-only | escape_witness: none | consumer: forced_values_impossible
p_two | proof_shape: bind-only | escape_witness: none | consumer: forced_values_impossible
quadratic_transport | proof_shape: bind-only | escape_witness: none | consumer: quadratic_collision_excluded
p_even_step | proof_shape: bind-only | escape_witness: none | consumer: p_even_growth
p_even_growth | proof_shape: content | escape_witness: p_even_growth | consumer: p_even_gt_one
p_even_gt_one | proof_shape: content | escape_witness: p_even_growth | consumer: quadratic_collision_excluded
quadratic_collision_excluded | proof_shape: content | escape_witness: p_even_growth | consumer: forced_values_impossible
p_neg_two_odd | proof_shape: bind-only | escape_witness: none | consumer: forced_values_impossible
forced_values_impossible | proof_shape: content | escape_witness: p_even_growth | consumer: endpoints_not_surjective
endpoints_not_surjective | proof_shape: content | escape_witness: p_even_growth | consumer: boundary_model_finrank_le_one
transfer_one_period | proof_shape: bind-only | escape_witness: none | consumer: singular_long_endpoints
transfer_neg_one_period | proof_shape: bind-only | escape_witness: none | consumer: singular_long_endpoints
recurrence_state | proof_shape: content | escape_witness: recurrence_state | consumer: singular_long_endpoints
singular_long_endpoints | proof_shape: content | escape_witness: recurrence_state | consumer: bounded_singular_endpoints
singular_boundary_systems | proof_shape: bind-only | escape_witness: none | consumer: model_singular_laplacian
boundary_model_finrank_le_one | proof_shape: content | escape_witness: p_even_growth | consumer: model_nonsingular_finrank
pathSeq_zero | proof_shape: bind-only | escape_witness: none | consumer: bounded_continuant_endpoint
pathSeq_one | proof_shape: bind-only | escape_witness: none | consumer: bounded_continuant_endpoint
pathSeq_step | proof_shape: bind-only | escape_witness: none | consumer: bounded_continuant_endpoint
pathSeq_formula | proof_shape: bind-only | escape_witness: none | consumer: bounded_continuant_endpoint
bounded_recurrence_unique | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_zero
bounded_singular_endpoints | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_singular_laplacian
bounded_continuant_endpoint | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_nonsingular_finrank
short_path_zero | proof_shape: bind-only | escape_witness: none | consumer: model_endpoint_injective
model_zero | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_signless_singular_finrank
model_endpoint_injective | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_nonsingular_finrank
model_nonsingular_finrank | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: theta_laplacian_multiplicity_upper
model_singular_laplacian | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_laplacian_singular_finrank
model_singular_signless | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: model_signless_singular_finrank
model_laplacian_singular_finrank | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: theta_laplacian_multiplicity_upper
model_signless_singular_finrank | proof_shape: content | escape_witness: bounded_recurrence_unique | consumer: theta_signless_multiplicity_upper
pathSeq | proof_shape: bind-only | escape_witness: none | consumer: pathSeq_step
ThetaCoordinates | proof_shape: bind-only | escape_witness: none | consumer: graph_coordinates_exist
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace

noncomputable section
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

private theorem p_zero (t : ℝ) : ((Chebyshev.S ℝ 0).eval t) = 1 := by simp []
private theorem p_one (t : ℝ) : ((Chebyshev.S ℝ 1).eval t) = t := by simp []
private theorem p_step (n : ℤ) (t : ℝ) :
    ((Chebyshev.S ℝ (n+2)).eval t) = t * ((Chebyshev.S ℝ (n+1)).eval t) - ((Chebyshev.S ℝ n).eval t) := by
  simp [Chebyshev.S_add_two]
private theorem p_invariant (n : ℤ) (t : ℝ) :
    ((Chebyshev.S ℝ n).eval t) ^ 2 + ((Chebyshev.S ℝ (n+1)).eval t) ^ 2 - t * ((Chebyshev.S ℝ n).eval t) * ((Chebyshev.S ℝ (n+1)).eval t) = 1 := by
  have h := congrArg (Polynomial.eval t) (Chebyshev.S_sq_add_S_sq ℝ n)
  simpa [] using h
private theorem p_two (n : ℤ) : ((Chebyshev.S ℝ n).eval 2) = n+1 := by exact Chebyshev.S_eval_two ℝ n

/-- Rational polynomial identities pass between the two conjugate quadratic roots. -/
private theorem quadratic_transport (eQ : ℚ) (heQ : eQ^2 = 1)
    (t T : ℝ) (hq : t^2 + 2*(eQ : ℝ)*t - 1 = 0)
    (hT : T^2 + 2*(eQ : ℝ)*T - 1 = 0)
    (f : ℚ[X]) (hf : aeval t f = 0) : aeval T f = 0 := by
  let q : ℚ[X] := X^2 + C (2*eQ) * X - 1
  have hqm : q.Monic := by
    dsimp [q]
    monicity <;> norm_num
  have hqd : q.natDegree = 2 := by
    dsimp [q]
    compute_degree <;> norm_num
  have hqi : Irreducible q := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hqd]; norm_num
    · intro a ha
      have ha' : a^2 + 2*eQ*a - 1 = 0 := by
        simpa [q, Polynomial.IsRoot] using ha
      have hs : (a+eQ)^2 = 2 := by nlinarith
      have hsR : ((a+eQ : ℚ) : ℝ)^2 = 2 := by exact_mod_cast hs
      have hroot : Real.sqrt 2 = |((a+eQ : ℚ) : ℝ)| := by
        rw [← hsR, Real.sqrt_sq_eq_abs]
      exact irrational_sqrt_two ⟨|a+eQ|, by simpa using hroot.symm⟩
  have hqt : aeval t q = 0 := by simpa [q] using hq
  have hident : q = minpoly ℚ t :=
    minpoly.eq_of_irreducible_of_monic hqi hqt hqm
  exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero
    (hident.symm ▸ minpoly.dvd ℚ t hf) (by simpa [q] using hT)

private theorem p_even_step (n : ℤ) (t : ℝ) :
    ((Chebyshev.S ℝ (n+4)).eval t) = (t^2-2)*((Chebyshev.S ℝ (n+2)).eval t) - ((Chebyshev.S ℝ n).eval t) := by
  have h0 := p_step n t
  have h1 := p_step (n+1) t
  have h2 := p_step (n+2) t
  have h3 : ((Chebyshev.S ℝ (n+1+2)).eval t) = ((Chebyshev.S ℝ (n+2+1)).eval t) := by rw [show n+1+2 = n+2+1 by omega]
  rw [h3,show n+1+1=n+2 by omega] at h1
  have h4 : ((Chebyshev.S ℝ (n+2+2)).eval t) = ((Chebyshev.S ℝ (n+4)).eval t) := by rw [show n+2+2 = n+4 by omega]
  rw [h4] at h2
  linear_combination h2 + t*h1 + h0

private theorem p_even_growth (t : ℝ) (ht : 4 < t^2) (m : ℕ) :
    1 ≤ ((Chebyshev.S ℝ (2*m : ℤ)).eval t) ∧ ((Chebyshev.S ℝ (2*m : ℤ)).eval t) < ((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) := by
  induction m
  case zero =>
      have h := p_step 0 t
      simp only [p_zero, p_one, zero_add] at h
      constructor
      · simp []
      · simpa only [Nat.cast_zero, mul_zero, p_zero, zero_add] using
          (show 1 < ((Chebyshev.S ℝ 2).eval t) by nlinarith)
  case succ m ih =>
      have h := p_even_step (2*m : ℤ) t
      have he : (2*((m+1 : ℕ) : ℤ)) = 2*m+2 := by exact Int.neg_inj.mp rfl
      rw [he]
      constructor
      · linarith [ih.1, ih.2]
      · have hmul : 2*((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) < (t^2-2)*((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) := by
          have hp : 0 < ((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) := by linarith [ih.1, ih.2]
          exact mul_lt_mul_of_pos_right (by linarith : (2 : ℝ) < t^2-2) hp
        rw [show (2*(m : ℤ)+2)+2=2*m+4 by ring]
        linarith [ih.2]

private theorem p_even_gt_one (t : ℝ) (ht : 4 < t^2) (m : ℕ) :
    1 < ((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) := by
  have h := p_even_growth t ht m
  linarith [h.1,h.2]

/-- The two quadratic cases left by the determinant-one obstruction cannot
have the forced consecutive-continuant value. -/
private theorem quadratic_collision_excluded (eQ : ℚ) (heQ : eQ^2 = 1)
    (he : (eQ : ℝ) ≤ 1) (m : ℕ) (t : ℝ)
    (ht : t^2 + 2*(eQ : ℝ)*t - 1 = 0) :
    ((Chebyshev.S ℝ (2*m+2 : ℤ)).eval t) ≠ (eQ : ℝ) := by
  intro hp
  let T : ℝ := -(eQ : ℝ) * (1+Real.sqrt 2)
  have hes : (eQ : ℝ)^2 = 1 := by exact_mod_cast heQ
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hTsq : T^2 = (1+Real.sqrt 2)^2 := by
    dsimp [T]
    rw [mul_pow, neg_sq, hes, one_mul]
  have hprod : 2*(eQ : ℝ)*T = -2*(1+Real.sqrt 2) := by
    calc
      _ = -2*(eQ : ℝ)^2*(1+Real.sqrt 2) := by dsimp [T]; ring
      _ = _ := by rw [hes]; ring
  have hT : T^2 + 2*(eQ : ℝ)*T - 1 = 0 := by rw [hTsq,hprod]; nlinarith
  have hTlarge : 4 < T^2 := by rw [hTsq]; nlinarith
  have hf : aeval t (Chebyshev.S ℚ (2*m+2 : ℤ) - C eQ) = 0 := by
    simpa [sub_eq_zero] using hp
  have htwin := quadratic_transport eQ heQ t T ht hT _ hf
  have hpT : ((Chebyshev.S ℝ (2*m+2 : ℤ)).eval T) = (eQ : ℝ) := by
    simpa [sub_eq_zero] using htwin
  have hbig := p_even_gt_one T hTlarge m
  linarith

private theorem p_neg_two_odd (m : ℕ) :
    ((Chebyshev.S ℝ (2*m+1 : ℤ)).eval (-2)) = -(2*(m : ℝ)+2) := by
  simp only [Chebyshev.S_eval_neg_two]
  rw [Int.negOnePow_two_mul_add_one]
  push_cast
  ring

/-- The forced two-endpoint-surjectivity values contradict the continuant
identity for every long-path length in the proposed congruence class. -/
private theorem forced_values_impossible (k : ℕ) (eQ : ℚ)
    (he : eQ=1 ∨ eQ = -1) (t : ℝ) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hP : 2*((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) = 1-t^2)
    (hR : 2*((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t) =
      -((t+(eQ : ℝ))*(t^2-1)-2*t)) : False := by
  have hi : ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t) ^ 2 + ((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) ^ 2 -
      t*((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t)*((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) = 1 := by
    simpa only [show (6*(k : ℤ)+2)+1=6*k+3 by ring] using
      p_invariant (6*k+2 : ℤ) t
  have hPeq : ((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) = (1-t^2)/2 := by linarith
  have hReq : ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t) = -((t+(eQ : ℝ))*(t^2-1)-2*t)/2 := by linarith
  rw [hPeq,hReq] at hi
  have he2 : eQ^2 = 1 := by exact sq_eq_one_iff.mpr he
  have hele : (eQ : ℝ) ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have hfactor : (t-2*(eQ : ℝ))*(t-1)*(t+1)*
      (t^2+2*(eQ : ℝ)*t-1) = 0 := by
    rcases he with rfl | rfl
    · simp only [Rat.cast_one] at hi ⊢
      linear_combination 4*hi
    · simp only [Rat.cast_neg,Rat.cast_one] at hi ⊢
      linear_combination -4*hi
  rcases mul_eq_zero.mp hfactor with hleft | hquad
  · rcases mul_eq_zero.mp hleft with hleft | hplus
    · rcases mul_eq_zero.mp hleft with hend | hminus
      · have ht : t=2*(eQ : ℝ) := by linarith
        rcases he with rfl | rfl
        · norm_num at ht
          subst t
          rw [p_two] at hP
          norm_num at hP
          have hk : (0 : ℝ) ≤ k := by exact Nat.cast_nonneg' k
          push_cast at hP
          linarith
        · norm_num at ht
          subst t
          have hodd : ((Chebyshev.S ℝ (6*k+3 : ℤ)).eval (-2)) = -(6*(k : ℝ)+4) := by
            have ho := p_neg_two_odd (3*k+1)
            rw [show (2*((3*k+1 : ℕ) : ℤ)+1)=6*k+3 by push_cast; ring] at ho
            push_cast at ho
            convert ho using 1 <;> ring
          rw [hodd] at hP
          have hk : (0 : ℝ) ≤ k := by exact Nat.cast_nonneg' k
          nlinarith
      · exact ht1 (by linarith)
    · exact htm1 (by linarith)
  · have hex := quadratic_collision_excluded eQ he2 hele (3*k) t hquad
    have hreq : ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t) = (eQ : ℝ) := by
      rcases he with rfl | rfl
      · norm_num at hquad hR ⊢
        linear_combination hR/2 - (t-1)/2*hquad
      · norm_num at hquad hR ⊢
        linear_combination hR/2 - (t+1)/2*hquad
    apply hex
    rw [show (2*((3*k : ℕ) : ℤ)+2)=6*k+2 by push_cast; ring]
    exact hreq

/-- The necessary left-boundary equations cannot allow every pair of
endpoint values when t is away from the singular short-path parameters. -/
private theorem endpoints_not_surjective (k : ℕ) (eQ : ℚ)
    (he : eQ=1 ∨ eQ = -1) (t : ℝ) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    ¬ ∀ A D : ℝ, ∃ B C : ℝ,
      t*B=A+C ∧ t*C=B+D ∧
      D=((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) * ((t+(eQ : ℝ))*A-2*B) - ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t)*A := by
  intro hs
  obtain ⟨B0,C0,hB0,hC0,hD0⟩ := hs 0 1
  obtain ⟨B1,C1,hB1,hC1,hD1⟩ := hs 1 0
  let P := ((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t)
  let R := ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t)
  let q := t^2-1
  have hb0 : q*B0=1 := by dsimp [q]; linear_combination t*hB0+hC0
  have hb1 : q*B1=t := by dsimp [q]; linear_combination t*hB1+hC1
  change 1=P*((t+(eQ : ℝ))*0-2*B0)-R*0 at hD0
  change 0=P*((t+(eQ : ℝ))*1-2*B1)-R*1 at hD1
  have hP : 2*P = -q := by
    linear_combination q*hD0 - 2*P*hb0
  have hprod : q*(2*R+(t+(eQ : ℝ))*q-2*t)=0 := by
    linear_combination 2*q*hD1 - 4*P*hb1 +
      (q*(t+(eQ : ℝ))-2*t)*hP
  have hq : q ≠ 0 := left_ne_zero_of_mul_eq_one hb0
  have hR : 2*R = -((t+(eQ : ℝ))*(t^2-1)-2*t) := by
    have hh := (mul_eq_zero.mp hprod).resolve_left hq
    dsimp [q] at hh
    linarith
  apply forced_values_impossible k eQ he t ht1 htm1
  · dsimp [P,q] at hP
    linarith
  · exact hR

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

noncomputable section
open Matrix
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

private theorem transfer_one_period : (transfer (1 : ℝ))^6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transfer,pow_succ,Matrix.mul_apply,Fin.sum_univ_two]

private theorem transfer_neg_one_period : (transfer (-1 : ℝ))^3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transfer,pow_succ,Matrix.mul_apply,Fin.sum_univ_two]

private theorem recurrence_state (t : ℝ) (y : ℕ → ℝ)
    (hy : ∀ j, y (j+2)=t*y (j+1)-y j) (n : ℕ) :
    ![y (n+1),y n] = (transfer t)^n *ᵥ ![y 1,y 0] := by
  induction n
  case zero => simp
  case succ n ih =>
      rw [pow_succ',← Matrix.mulVec_mulVec,← ih]
      ext i
      fin_cases i <;> simp [transfer,Matrix.mulVec,Fin.sum_univ_two,hy,sub_eq_add_neg]

private theorem singular_long_endpoints (k : ℕ) (y : ℕ → ℝ) :
    ((∀ j, y (j+2)=y (j+1)-y j) →
      y (6*k+4) = -y 1 ∧ y (6*k+3) = -y 0) ∧
    ((∀ j, y (j+2)= -y (j+1)-y j) →
      y (6*k+4) = y 1 ∧ y (6*k+3) = y 0) := by
  constructor
  · intro hy
    have hs := recurrence_state 1 y (by simpa using hy) (6*k+3)
    have hp : (transfer (1 : ℝ))^(6*k+3) = (transfer (1 : ℝ))^3 := by
      rw [pow_add,pow_mul,transfer_one_period,one_pow,one_mul]
    rw [hp] at hs
    have h0 := congrFun hs 0
    have h1 := congrFun hs 1
    norm_num [transfer,pow_succ,Matrix.mul_apply,Matrix.mulVec,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail] at h0 h1
    exact ⟨by convert h0 using 1 <;> congr 1 <;> omega,h1⟩
  · intro hy
    have hs := recurrence_state (-1) y (by simpa using hy) (6*k+3)
    have hp : (transfer (-1 : ℝ))^(6*k+3) = 1 := by
      rw [show 6*k+3=3*(2*k+1) by omega,pow_mul,transfer_neg_one_period,one_pow]
    rw [hp,Matrix.one_mulVec] at hs
    have h0 := congrFun hs 0
    have h1 := congrFun hs 1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
    exact ⟨by convert h0 using 1 <;> congr 1 <;> omega,h1⟩

/-- The complete four singular-parameter systems of the symmetric restriction. -/
private theorem singular_boundary_systems (A B C D s last penultimate : ℝ) :
    ((B=A+C ∧ C=B+D ∧ s=2*A-2*B ∧ last = -s ∧ penultimate = -A ∧
        last=D ∧ penultimate=2*D-2*C) ↔
      B=A/2 ∧ C= -A/2 ∧ D= -A ∧ s=A ∧ last= -A ∧ penultimate= -A) ∧
    ((-B=A+C ∧ -C=B+D ∧ s= -2*B ∧ last=s ∧ penultimate=A ∧
        last=D ∧ penultimate= -2*C) ↔
      B= -A/2 ∧ C= -A/2 ∧ D=A ∧ s=A ∧ last=A ∧ penultimate=A) ∧
    ((-B=A+C ∧ -C=B+D ∧ s= -2*A-2*B ∧ last=s ∧ penultimate=A ∧
        last=D ∧ penultimate= -2*D-2*C) ↔
      A=0 ∧ B=0 ∧ C=0 ∧ D=0 ∧ s=0 ∧ last=0 ∧ penultimate=0) ∧
    ((B=A+C ∧ C=B+D ∧ s= -2*B ∧ last = -s ∧ penultimate = -A ∧
        last=D ∧ penultimate= -2*C) ↔
      A=0 ∧ B=0 ∧ C=0 ∧ D=0 ∧ s=0 ∧ last=0 ∧ penultimate=0) := by
  constructor
  · constructor
    · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
      (repeat' apply And.intro) <;> linarith
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      (repeat' apply And.intro) <;> linarith
  constructor
  · constructor
    · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
      (repeat' apply And.intro) <;> linarith
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      (repeat' apply And.intro) <;> linarith
  constructor
  · constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩ <;>
      (repeat' apply And.intro) <;> linarith
  · constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩ <;>
      (repeat' apply And.intro) <;> linarith

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

/-- A finite-dimensional symmetric-coordinate model satisfying the theta
boundary equations has at most one eigenvector degree of freedom. -/
private theorem boundary_model_finrank_le_one
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (eQ : ℚ) (he : eQ=1 ∨ eQ = -1)
    (t : ℝ) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (A D B C : E →ₗ[ℝ] ℝ) (hinj : Function.Injective (A.prod D))
    (hb : ∀ x, t*B x = A x + C x)
    (hc : ∀ x, t*C x = B x + D x)
    (hd : ∀ x, D x = ((Chebyshev.S ℝ (6*k+3 : ℤ)).eval t) * ((t+(eQ : ℝ))*A x-2*B x) -
      ((Chebyshev.S ℝ (6*k+2 : ℤ)).eval t)*A x) : Module.finrank ℝ E ≤ 1 := by
  let ev : E →ₗ[ℝ] ℝ × ℝ := A.prod D
  have hei : Function.Injective ev := hinj
  have hle : Module.finrank ℝ E ≤ 2 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hei
  by_contra hnot
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (ℝ × ℝ) := by
    have heq : Module.finrank ℝ E=2 := by omega
    simpa using heq
  have hes : Function.Surjective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hei
  apply endpoints_not_surjective k eQ he t ht1 htm1
  intro a d
  obtain ⟨x,hx⟩ := hes (a,d)
  change (A x,D x)=(a,d) at hx
  have ha : A x=a := congrArg Prod.fst hx
  have hdd : D x=d := congrArg Prod.snd hx
  exact ⟨B x,C x,by rw [←ha]; exact hb x,
    by rw [←hdd]; exact hc x,by rw [←ha,←hdd]; exact hd x⟩

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

/-- The unique second-order sequence with specified first two values. -/
private def pathSeq (t A s : ℝ) : ℕ → ℝ :=
  (LinearRecurrence.mk 2 ![-1,t]).mkSol ![A,s]

@[simp] private theorem pathSeq_zero (t A s : ℝ) : pathSeq t A s 0 = A :=
  (LinearRecurrence.mk 2 ![-1,t]).mkSol_eq_init ![A,s] 0

@[simp] private theorem pathSeq_one (t A s : ℝ) : pathSeq t A s 1 = s :=
  (LinearRecurrence.mk 2 ![-1,t]).mkSol_eq_init ![A,s] 1

private theorem pathSeq_step (t A s : ℝ) (j : ℕ) :
    pathSeq t A s (j+2) = t * pathSeq t A s (j+1) - pathSeq t A s j := by
  have h := (LinearRecurrence.mk 2 ![-1,t]).is_sol_mkSol ![A,s] j
  simpa [LinearRecurrence.IsSolution, Fin.sum_univ_two, pathSeq,
    sub_eq_add_neg, add_comm] using h

private theorem pathSeq_formula (t A s : ℝ) (n : ℕ) :
    pathSeq t A s (n+1) = ((Chebyshev.S ℝ (n : ℤ)).eval t)*s-((Chebyshev.S ℝ ((n : ℤ)-1)).eval t)*A := by
  let f : ℕ → ℝ := fun j =>
    ((Chebyshev.S ℝ ((j : ℤ)-1)).eval t)*s-
      ((Chebyshev.S ℝ ((j : ℤ)-2)).eval t)*A
  have hf : (LinearRecurrence.mk 2 ![-1,t]).IsSolution f := by
    intro j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, neg_mul, one_mul]
    dsimp [f]
    have h1 : (Chebyshev.S ℝ ((j : ℤ)+1)).eval t =
        t*(Chebyshev.S ℝ (j : ℤ)).eval t-(Chebyshev.S ℝ ((j : ℤ)-1)).eval t := by
      simpa only [show (j : ℤ)-1+2=j+1 by ring,
        show (j : ℤ)-1+1=j by ring] using p_step ((j : ℤ)-1) t
    have h2 : (Chebyshev.S ℝ (j : ℤ)).eval t =
        t*(Chebyshev.S ℝ ((j : ℤ)-1)).eval t-(Chebyshev.S ℝ ((j : ℤ)-2)).eval t := by
      simpa only [show (j : ℤ)-2+2=j by ring,
        show (j : ℤ)-2+1=j-1 by ring] using p_step ((j : ℤ)-2) t
    simp only [show (j : ℤ)+2-1=j+1 by ring, show (j : ℤ)+2-2=j by ring,
      show (j : ℤ)+1-1=j by ring, show (j : ℤ)+1-2=j-1 by ring]
    linear_combination s*h1-A*h2
  have hi : ∀ j : Fin 2, f j = (![A,s]) j := by
    intro j
    fin_cases j <;> simp [f]
  have he := (LinearRecurrence.mk 2 ![-1,t]).eq_mk_of_is_sol_of_eq_init hf hi (n+1)
  simpa only [pathSeq, f, show ((n+1 : ℕ) : ℤ)-1=n by omega,
    show ((n+1 : ℕ) : ℤ)-2=(n : ℤ)-1 by omega] using he.symm

private theorem bounded_recurrence_unique (N : ℕ) (t : ℝ) (y z : ℕ → ℝ)
    (h0 : y 0=z 0) (h1 : y 1=z 1)
    (hy : ∀ j, j+2 ≤ N → y (j+2)=t*y (j+1)-y j)
    (hz : ∀ j, j+2 ≤ N → z (j+2)=t*z (j+1)-z j) :
    ∀ n, n ≤ N → y n=z n := by
  intro n
  induction n using Nat.twoStepInduction
  case zero => intro _; exact h0
  case one => intro _; exact h1
  case more n ih ih1 =>
      intro hn
      rw [hy n hn,hz n hn,ih (by omega),ih1 (by omega)]

private theorem bounded_singular_endpoints (k : ℕ) (y : ℕ → ℝ) :
    ((∀ j, j+2 ≤ 6*k+4 → y (j+2)=y (j+1)-y j) →
      y (6*k+4) = -y 1 ∧ y (6*k+3) = -y 0) ∧
    ((∀ j, j+2 ≤ 6*k+4 → y (j+2)= -y (j+1)-y j) →
      y (6*k+4) = y 1 ∧ y (6*k+3) = y 0) := by
  constructor
  · intro hy
    let z := pathSeq 1 (y 0) (y 1)
    have hz : ∀ j, z (j+2)=z (j+1)-z j := by intro j; simp [z,pathSeq_step]
    have heq := bounded_recurrence_unique (6*k+4) 1 y z (by simp [z]) (by simp [z])
      (by simpa using hy) (by simpa using fun j (_ : j+2 ≤ 6*k+4) => hz j)
    have hp := (singular_long_endpoints k z).1 hz
    rw [←heq (6*k+4) le_rfl,←heq (6*k+3) (by omega)] at hp
    simpa [z] using hp
  · intro hy
    let z := pathSeq (-1) (y 0) (y 1)
    have hz : ∀ j, z (j+2)= -z (j+1)-z j := by intro j; simp [z,pathSeq_step]
    have heq := bounded_recurrence_unique (6*k+4) (-1) y z (by simp [z]) (by simp [z])
      (by simpa using hy) (by simpa using fun j (_ : j+2 ≤ 6*k+4) => hz j)
    have hp := (singular_long_endpoints k z).2 hz
    rw [←heq (6*k+4) le_rfl,←heq (6*k+3) (by omega)] at hp
    simpa [z] using hp

private theorem bounded_continuant_endpoint (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (y : ℕ → ℝ)
    (hy : ∀ j, j+2 ≤ N → y (j+2)=t*y (j+1)-y j) :
    y N=((Chebyshev.S ℝ ((N : ℤ)-1)).eval t)*y 1-((Chebyshev.S ℝ ((N : ℤ)-2)).eval t)*y 0 := by
  let z := pathSeq t (y 0) (y 1)
  have heq := bounded_recurrence_unique N t y z (by simp [z]) (by simp [z]) hy
    (by intro j _; simp [z,pathSeq_step])
  rw [heq N le_rfl]
  have hf := pathSeq_formula t (y 0) (y 1) (N-1)
  simpa [z,show N-1+1=N by omega,Nat.cast_sub hN,show (N : ℤ)-1-1=N-2 by omega] using hf

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

/-- Linear coordinate equations for the two short paths and the long path.
The separation field means that these are the coordinates of the whole vector. -/
structure ThetaCoordinates (E : Type*) [AddCommGroup E] [Module ℝ E]
    (k : ℕ) (t e : ℝ) where
  A : E →ₗ[ℝ] ℝ
  D : E →ₗ[ℝ] ℝ
  B : E →ₗ[ℝ] ℝ
  C : E →ₗ[ℝ] ℝ
  B' : E →ₗ[ℝ] ℝ
  C' : E →ₗ[ℝ] ℝ
  Y : ℕ → E →ₗ[ℝ] ℝ
  first : Y 0=A
  last : Y (6*k+4)=D
  shortB : ∀ x, t*B x=A x+C x
  shortC : ∀ x, t*C x=B x+D x
  shortB' : ∀ x, t*B' x=A x+C' x
  shortC' : ∀ x, t*C' x=B' x+D x
  left : ∀ x, Y 1 x=(t+e)*A x-B x-B' x
  right : ∀ x, Y (6*k+3) x=(t+e)*D x-C x-C' x
  recurrence : ∀ j, j+2 ≤ 6*k+4 → ∀ x,
    Y (j+2) x=t*Y (j+1) x-Y j x
  separates : ∀ x, A x=0 → D x=0 → B x=0 → C x=0 → B' x=0 → C' x=0 →
    (∀ j, j ≤ 6*k+4 → Y j x=0) → x=0

private theorem short_path_zero (t A D B C : ℝ) (ht : t≠1) (ht' : t≠ -1)
    (hA : A=0) (hD : D=0) (hB : t*B=A+C) (hC : t*C=B+D) :
    B=0 ∧ C=0 := by
  have hq : t^2-1 ≠ 0 := sub_ne_zero.mpr (sq_ne_one_iff.mpr ⟨ht,ht'⟩)
  have hp : (t^2-1)*B=0 := by linear_combination t*hB+hC+t*hA+hD
  have hb := (mul_eq_zero.mp hp).resolve_left hq
  exact ⟨hb,by rw [hA,hb] at hB; linarith⟩

private theorem model_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℕ) (t e : ℝ) (m : ThetaCoordinates E k t e) (x : E)
    (ha : m.A x=0) (hd : m.D x=0) (hb : m.B x=0) (hc : m.C x=0)
    (hb' : m.B' x=0) (hc' : m.C' x=0) : x=0 := by
  apply m.separates x ha hd hb hc hb' hc'
  have hy0 : m.Y 0 x=0 := by rw [m.first]; exact ha
  have hy1 : m.Y 1 x=0 := by rw [m.left,ha,hb,hb']; ring
  intro j hj
  exact bounded_recurrence_unique (6*k+4) t (fun n=>m.Y n x) (fun _=>0)
    hy0 hy1 (fun j hj=>m.recurrence j hj x) (by intros; ring) j hj


private theorem model_endpoint_injective
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℕ) (t e : ℝ) (ht : t≠1) (ht' : t≠ -1)
    (m : ThetaCoordinates E k t e) : Function.Injective (m.A.prod m.D) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hx' : (m.A x,m.D x)=(0,0) := hx
  have ha : m.A x=0 := congrArg Prod.fst hx'
  have hd : m.D x=0 := congrArg Prod.snd hx'
  obtain ⟨hb,hc⟩ := short_path_zero t _ _ _ _ ht ht' ha hd (m.shortB x) (m.shortC x)
  obtain ⟨hb',hc'⟩ := short_path_zero t _ _ _ _ ht ht' ha hd (m.shortB' x) (m.shortC' x)
  exact model_zero k t e m x ha hd hb hc hb' hc'

theorem model_nonsingular_finrank
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (eQ : ℚ) (he : eQ=1 ∨ eQ = -1)
    (t : ℝ) (ht : t≠1) (ht' : t≠ -1)
    (m : ThetaCoordinates E k t (eQ : ℝ)) : Module.finrank ℝ E ≤ 1 := by
  have hsame : ∀ x, m.B x=m.B' x ∧ m.C x=m.C' x := by
    intro x
    obtain ⟨hb,hc⟩ := short_path_zero t 0 0 (m.B x-m.B' x) (m.C x-m.C' x)
      ht ht' rfl rfl (by linarith [m.shortB x,m.shortB' x])
      (by linarith [m.shortC x,m.shortC' x])
    exact ⟨by linarith,by linarith⟩
  apply boundary_model_finrank_le_one k eQ he t ht ht' m.A m.D m.B m.C
    (model_endpoint_injective k t (eQ : ℝ) ht ht' m) m.shortB m.shortC
  intro x
  have hy := bounded_continuant_endpoint (6*k+4) (by omega) t (fun j=>m.Y j x)
    (fun j hj=>m.recurrence j hj x)
  rw [m.last,m.first,m.left,←(hsame x).1] at hy
  push_cast at hy
  rw [show (6*(k : ℤ)+4)-1=6*k+3 by ring,
    show (6*(k : ℤ)+4)-2=6*k+2 by ring] at hy
  linear_combination hy

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence

private theorem model_singular_laplacian
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℕ) (t : ℝ) (ht : t=1 ∨ t= -1)
    (m : ThetaCoordinates E k t 1) (x : E) :
    m.D x= -t*m.A x ∧ m.B x+m.B' x=t*m.A x ∧
      m.C x=t*m.B x-m.A x ∧ m.C' x=t*m.B' x-m.A x := by
  let b := (m.B x+m.B' x)/2
  let c := (m.C x+m.C' x)/2
  have h0 : m.Y 0 x=m.A x := by rw [m.first]
  have hlast : m.Y (6*k+4) x=m.D x := by rw [m.last]
  rcases ht with rfl | rfl
  · have hp := (bounded_singular_endpoints k (fun j=>m.Y j x)).1
      (by intro j hj; simpa using m.recurrence j hj x)
    have hs := (singular_boundary_systems (m.A x) b c (m.D x)
      (m.Y 1 x) (m.Y (6*k+4) x) (m.Y (6*k+3) x)).1.mp
      (by dsimp [b,c]; (repeat' apply And.intro) <;>
        linarith [m.shortB x,m.shortC x,m.shortB' x,m.shortC' x,
          m.left x,m.right x,h0,hlast,hp.1,hp.2])
    dsimp [b,c] at hs
    (repeat' apply And.intro) <;> linarith [hs.1,hs.2.1,hs.2.2.1,m.shortB x,m.shortB' x]
  · have hp := (bounded_singular_endpoints k (fun j=>m.Y j x)).2
      (by intro j hj; simpa using m.recurrence j hj x)
    have hs := (singular_boundary_systems (m.A x) b c (m.D x)
      (m.Y 1 x) (m.Y (6*k+4) x) (m.Y (6*k+3) x)).2.1.mp
      (by dsimp [b,c]; (repeat' apply And.intro) <;>
        linarith [m.shortB x,m.shortC x,m.shortB' x,m.shortC' x,
          m.left x,m.right x,h0,hlast,hp.1,hp.2])
    dsimp [b,c] at hs
    (repeat' apply And.intro) <;> linarith [hs.1,hs.2.1,hs.2.2.1,m.shortB x,m.shortB' x]

private theorem model_singular_signless
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℕ) (t : ℝ) (ht : t=1 ∨ t= -1)
    (m : ThetaCoordinates E k t (-1)) (x : E) :
    m.A x=0 ∧ m.D x=0 ∧ m.B' x= -m.B x ∧
      m.C x=t*m.B x ∧ m.C' x= -t*m.B x := by
  let b := (m.B x+m.B' x)/2
  let c := (m.C x+m.C' x)/2
  have h0 : m.Y 0 x=m.A x := by rw [m.first]
  have hlast : m.Y (6*k+4) x=m.D x := by rw [m.last]
  rcases ht with rfl | rfl
  · have hp := (bounded_singular_endpoints k (fun j=>m.Y j x)).1
      (by intro j hj; simpa using m.recurrence j hj x)
    have hs := (singular_boundary_systems (m.A x) b c (m.D x)
      (m.Y 1 x) (m.Y (6*k+4) x) (m.Y (6*k+3) x)).2.2.2.mp
      (by dsimp [b,c]; (repeat' apply And.intro) <;>
        linarith [m.shortB x,m.shortC x,m.shortB' x,m.shortC' x,
          m.left x,m.right x,h0,hlast,hp.1,hp.2])
    dsimp [b,c] at hs
    (repeat' apply And.intro) <;> linarith [hs.1,hs.2.1,hs.2.2.2.1,m.shortB x,m.shortB' x]
  · have hp := (bounded_singular_endpoints k (fun j=>m.Y j x)).2
      (by intro j hj; simpa using m.recurrence j hj x)
    have hs := (singular_boundary_systems (m.A x) b c (m.D x)
      (m.Y 1 x) (m.Y (6*k+4) x) (m.Y (6*k+3) x)).2.2.1.mp
      (by dsimp [b,c]; (repeat' apply And.intro) <;>
        linarith [m.shortB x,m.shortC x,m.shortB' x,m.shortC' x,
          m.left x,m.right x,h0,hlast,hp.1,hp.2])
    dsimp [b,c] at hs
    (repeat' apply And.intro) <;> linarith [hs.1,hs.2.1,hs.2.2.2.1,m.shortB x,m.shortB' x]


theorem model_laplacian_singular_finrank
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (t : ℝ) (ht : t=1 ∨ t= -1)
    (m : ThetaCoordinates E k t 1) : Module.finrank ℝ E ≤ 2 := by
  have hinj : Function.Injective (m.A.prod m.B) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hx' : (m.A x,m.B x)=(0,0) := hx
    have ha : m.A x=0 := congrArg Prod.fst hx'
    have hb : m.B x=0 := congrArg Prod.snd hx'
    have hs := model_singular_laplacian k t ht m x
    have hb' : m.B' x=0 := by
      have hsum := hs.2.1
      rw [ha,hb] at hsum
      simpa using hsum
    exact model_zero k t 1 m x ha (by rw [hs.1,ha]; ring) hb
      (by rw [hs.2.2.1,hb,ha]; ring) hb'
      (by rw [hs.2.2.2,hb',ha]; ring)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem model_signless_singular_finrank
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (t : ℝ) (ht : t=1 ∨ t= -1)
    (m : ThetaCoordinates E k t (-1)) : Module.finrank ℝ E ≤ 1 := by
  have hinj : Function.Injective m.B := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hb : m.B x=0 := hx
    have hs := model_singular_signless k t ht m x
    exact model_zero k t (-1) m x hs.1 hs.2.1 hb
      (by rw [hs.2.2.2.1,hb]; ring)
      (by rw [hs.2.2.1,hb]; ring)
      (by rw [hs.2.2.2.2,hb]; ring)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
