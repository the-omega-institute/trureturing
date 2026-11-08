/- GID: D5/S3/Observer/Hilbert/C117FixedFourteenProjection
   generality: I
   mirror-B: D5/B/S3/Observer/Hilbert/C117FixedFourteenProjection
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: The original C117 braid orbit and fourteen tails supply an ambient rank-24 projection estimate. -/

import D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.Observer.Hilbert.C117FixedFourteenProjection
open scoped InnerProductSpace
open Module
open D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect
open D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

abbrev Word := List (Fin 4)
abbrev Coeff := EuclideanSpace ℂ (Fin 24)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Letters 0,1,2,3 stand for s,s inverse,t,t inverse. -/
def letter (s t : H ≃ₗᵢ[ℂ] H) : Fin 4 → H ≃ₗᵢ[ℂ] H := ![s,s⁻¹,t,t⁻¹]
def wordEval (s t : H ≃ₗᵢ[ℂ] H) (w : Word) : H ≃ₗᵢ[ℂ] H := (w.map (letter s t)).prod

def orbitWords : Fin 24 → Word := ![[],
    [0],
    [1],
    [2],
    [2,0],
    [2,1],
    [0,2],
    [0,2,0],
    [0,2,1],
    [1,2],
    [1,2,0],
    [1,2,1],
    [3],
    [3,0],
    [3,1],
    [0,3],
    [0,3,0],
    [0,3,1],
    [1,3],
    [1,3,0],
    [1,3,1],
    [3,0,3],
    [0,3,0,3],
    [1,3,0,3]]
def tails : Fin 14 → Word := ![[],
    [2],
    [2,0],
    [2,1],
    [3],
    [3,0],
    [3,1],
    [3,0,3],
    [3,1,1],
    [3,3,1],
    [3,3],
    [3,1,1,1],
    [1],
    [3,3,1,1]]
private def columns (a : ℂ) : Fin 2 → Fin 24 → List (ℂ × Fin 24) :=
  ![![[((1),(1:Fin 24))],
    [((-a),(0:Fin 24)),((a),(1:Fin 24)),((1),(2:Fin 24))],
    [((1),(0:Fin 24))],
    [((1),(6:Fin 24))],
    [((1),(7:Fin 24))],
    [((1),(8:Fin 24))],
    [((-a),(3:Fin 24)),((a),(6:Fin 24)),((1),(9:Fin 24))],
    [((-a),(4:Fin 24)),((a),(7:Fin 24)),((1),(10:Fin 24))],
    [((-a),(5:Fin 24)),((a),(8:Fin 24)),((1),(11:Fin 24))],
    [((1),(3:Fin 24))],
    [((1),(4:Fin 24))],
    [((1),(5:Fin 24))],
    [((1),(15:Fin 24))],
    [((1),(16:Fin 24))],
    [((1),(17:Fin 24))],
    [((-a),(12:Fin 24)),((a),(15:Fin 24)),((1),(18:Fin 24))],
    [((-a),(13:Fin 24)),((a),(16:Fin 24)),((1),(19:Fin 24))],
    [((-a),(14:Fin 24)),((a),(17:Fin 24)),((1),(20:Fin 24))],
    [((1),(12:Fin 24))],
    [((1),(13:Fin 24))],
    [((1),(14:Fin 24))],
    [((1),(22:Fin 24))],
    [((-a),(21:Fin 24)),((a),(22:Fin 24)),((1),(23:Fin 24))],
    [((1),(21:Fin 24))]],
    ![[((1),(3:Fin 24))],
    [((1),(4:Fin 24))],
    [((1),(5:Fin 24))],
    [((-a),(0:Fin 24)),((a),(3:Fin 24)),((1),(12:Fin 24))],
    [((-a),(1:Fin 24)),((a),(4:Fin 24)),((1),(13:Fin 24))],
    [((-a),(2:Fin 24)),((a),(5:Fin 24)),((1),(14:Fin 24))],
    [((1),(7:Fin 24))],
    [((-a),(6:Fin 24)),((a),(7:Fin 24)),((1),(8:Fin 24))],
    [((1),(6:Fin 24))],
    [((a),(5:Fin 24)),((-a),(19:Fin 24)),((1),(23:Fin 24))],
    [((a),(10:Fin 24)),((-a),(15:Fin 24)),((1),(21:Fin 24))],
    [((a),(4:Fin 24)),((a^2),(5:Fin 24)),((-a),(6:Fin 24)),((-(a^2)),(9:Fin 24)),((a),(11:Fin 24)),((a^2),(13:Fin 24)),((a),(14:Fin 24)),((-a),(16:Fin 24)),((-a),(18:Fin 24)),((-(a^2)),(19:Fin 24)),((-a),(21:Fin 24)),((1),(22:Fin 24)),((a),(23:Fin 24))],
    [((1),(0:Fin 24))],
    [((1),(1:Fin 24))],
    [((1),(2:Fin 24))],
    [((1),(10:Fin 24))],
    [((-a),(9:Fin 24)),((a),(10:Fin 24)),((1),(11:Fin 24))],
    [((1),(9:Fin 24))],
    [((1),(19:Fin 24))],
    [((-a),(18:Fin 24)),((a),(19:Fin 24)),((1),(20:Fin 24))],
    [((1),(18:Fin 24))],
    [((1),(15:Fin 24))],
    [((-a),(2:Fin 24)),((-(a^2)),(4:Fin 24)),((a),(7:Fin 24)),((a^2),(10:Fin 24)),((-a),(13:Fin 24)),((1),(16:Fin 24)),((a),(19:Fin 24))],
    [((a^2),(2:Fin 24)),((-a),(9:Fin 24)),((-a),(14:Fin 24)),((1),(17:Fin 24)),((-(a^2)),(18:Fin 24)),((a),(20:Fin 24)),((a),(23:Fin 24))]]]
private def errors (a : ℂ) : Fin 2 → Fin 24 → List (ℂ × Word × Fin 14) :=
  ![![[],
    [((1),[1],(0:Fin 14))],
    [],
    [],
    [],
    [],
    [((1),[1],(1:Fin 14))],
    [((1),[1],(2:Fin 14))],
    [((1),[1],(3:Fin 14))],
    [],
    [],
    [],
    [],
    [],
    [],
    [((1),[1],(4:Fin 14))],
    [((1),[1],(5:Fin 14))],
    [((1),[1],(6:Fin 14))],
    [],
    [],
    [],
    [],
    [((1),[1],(7:Fin 14))],
    []],
    ![[],
    [],
    [],
    [((1),[3,0,2],(6:Fin 14))],
    [((1),[3,0,2],(4:Fin 14))],
    [((1),[3,0,2],(8:Fin 14))],
    [],
    [((1),[0,2,1],(0:Fin 14))],
    [],
    [((1),[3,1,1],(6:Fin 14)),((-1),[1,3,1,1],(4:Fin 14)),((-a),[3,3,0,2],(8:Fin 14)),((a),[1,3,3,0,2],(6:Fin 14)),((a),[1,3,1,1],(0:Fin 14)),((-a),[1,1],(6:Fin 14)),((1),[3,0,2],(9:Fin 14))],
    [((1),[3,0,2],(10:Fin 14))],
    [((1),[3,1,1],(8:Fin 14)),((-1),[1,3,1,1],(6:Fin 14)),((-a),[3,3,0,2],(11:Fin 14)),((a),[1,3,3,0,2],(8:Fin 14)),((a),[1,3,1,1],(12:Fin 14)),((-a),[1,1],(8:Fin 14)),((1),[3,0,2],(13:Fin 14)),((1),[1,3,1,1],(6:Fin 14)),((-1),[1,1,3,1,1],(4:Fin 14)),((-a),[1,3,3,0,2],(8:Fin 14)),((a),[1,1,3,3,0,2],(6:Fin 14)),((a),[1,1,3,1,1],(0:Fin 14)),((-a),[1,1,1],(6:Fin 14)),((-1),[1,1],(7:Fin 14)),((-a),[2,1,1],(0:Fin 14)),((a),[1,1],(1:Fin 14)),((a),[1,1],(5:Fin 14))],
    [],
    [],
    [],
    [],
    [((1),[1,2,1],(0:Fin 14))],
    [],
    [],
    [((1),[1,3,1],(0:Fin 14))],
    [],
    [],
    [((-a),[1,1],(2:Fin 14)),((-1),[1,1],(5:Fin 14)),((1),[1,2,1],(4:Fin 14))],
    [((a),[1,3,3,0,2],(6:Fin 14)),((-1),[1,1],(6:Fin 14)),((1),[1,3,1],(4:Fin 14))]]]

def generators (s t : H ≃ₗᵢ[ℂ] H) (g : Fin 2) : H ≃ₗᵢ[ℂ] H :=
  wordEval s t (if g = 0 then [0] else [2])
def residual (a : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (y : H) : H :=
  wordEval s t [0,0,0] y - a • wordEval s t [0,0] y +
    a • wordEval s t [0] y - y
private def columnOrbit (a : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (v : H) (g : Fin 2) (j : Fin 24) : H :=
  ((columns a g j).map fun c => c.1 • wordEval s t (orbitWords c.2) v).sum
private def errorVector (a : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (v : H) (g : Fin 2) (j : Fin 24) : H :=
  ((errors a g j).map fun e => e.1 • wordEval s t e.2.1
    (residual a s t (wordEval s t (tails e.2.2) v))).sum

private theorem environment_columns (s t : H ≃ₗᵢ[ℂ] H) (h : s*t*s=t*s*t)
    (a : ℂ) (v : H) : ∀ g j,
    generators s t g (wordEval s t (orbitWords j) v) =
      columnOrbit a s t v g j + errorVector a s t v g j := by

  let p := s*t
  let d := s*t*s
  let z := d^2
  have hzp : z = p^3 := by
    calc
      z = (s*t*s)*(s*t*s) := by dsimp [z,d]; simp only [pow_succ, pow_zero, mul_one]; group
      _ = (s*t*s)*(t*s*t) := by rw [h]
      _ = p^3 := by dsimp [p]; simp only [pow_succ, pow_zero, mul_one]; group
  have hs : s = z⁻¹ * (p * (p * d)) := by
    rw [hzp]
    dsimp [p,d]
    simp only [pow_succ, pow_zero, mul_one]
    group
  have ht : t = z⁻¹ * (d * (p * p)) := by
    dsimp [z,p,d]
    simp only [pow_succ, pow_zero, mul_one]
    group
  have hsi : s⁻¹ = z⁻¹ * (d * p) := by
    dsimp [z,p,d]
    simp only [pow_succ, pow_zero, mul_one]
    group
  have hti : t⁻¹ = z⁻¹ * (p * d) := by
    rw [hzp]
    dsimp [p,d]
    simp only [pow_succ, pow_zero, mul_one]
    group
  have hdp : d * d = z := by dsimp [z]; simp only [pow_succ, pow_zero, mul_one]; group
  have hpp : p * (p * p) = z := by rw [hzp]; simp only [pow_succ, pow_zero, mul_one]; group
  have hdz : Commute d z := by dsimp [z]; exact Commute.self_pow d 2
  have hpz : Commute p z := by rw [hzp]; exact Commute.self_pow p 3
  have md (x : (H ≃ₗᵢ[ℂ] H)) : d * (z * x) = z * (d * x) := by rw [←mul_assoc, hdz.eq, mul_assoc]
  have mp (x : (H ≃ₗᵢ[ℂ] H)) : p * (z * x) = z * (p * x) := by rw [←mul_assoc, hpz.eq, mul_assoc]
  have mdi (x : (H ≃ₗᵢ[ℂ] H)) : d * (z⁻¹ * x) = z⁻¹ * (d * x) := by rw [←mul_assoc, hdz.inv_right.eq, mul_assoc]
  have mpi (x : (H ≃ₗᵢ[ℂ] H)) : p * (z⁻¹ * x) = z⁻¹ * (p * x) := by rw [←mul_assoc, hpz.inv_right.eq, mul_assoc]
  have dd (x : (H ≃ₗᵢ[ℂ] H)) : d * (d * x) = z * x := by rw [←mul_assoc, hdp]
  have pp (x : (H ≃ₗᵢ[ℂ] H)) : p * (p * (p * x)) = z * x := by simpa only [mul_assoc] using congrArg (fun a => a*x) hpp
  have ha0 : letter s t 0 = z⁻¹ * (p * (p * d)) := hs
  have ha1 : letter s t 1 = z⁻¹ * (d * p) := hsi
  have ha2 : letter s t 2 = z⁻¹ * (d * (p * p)) := ht
  have ha3 : letter s t 3 = z⁻¹ * (p * d) := hti
  have ea (w u : Word) (y : H) : wordEval s t w (wordEval s t u y) =
      wordEval s t (w++u) y := by
    simp only [wordEval, List.map_append, List.prod_append]
    rfl
  intro g j
  fin_cases g <;> fin_cases j <;>
    simp only [generators, orbitWords, tails, columns, errors, columnOrbit, errorVector,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Fin.zero_eta, Fin.reduceFinMk, ite_true, ite_false, one_ne_zero] <;>
    simp only [residual, map_add, map_sub, map_smul, ea] <;>
    simp only [List.cons_append, List.nil_append] <;>
    simp only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      ha0,ha1,ha2,ha3,mul_one,mul_assoc,md,mp,mdi,mpi,dd,pp,hdp,hpp,
      hdz.eq,hpz.eq,hdz.inv_right.eq,hpz.inv_right.eq,
      mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel] <;>
    module

/-- The exact real embedding of the original parameter. -/
def x : ℝ := (Real.sqrt 5 - 1) / 2
def a : ℝ := x ^ 2
private theorem parameter_bounds : 0 ≤ a ∧ a ≤ 1 := by
  have hs := Real.sqrt_nonneg 5
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hx0 : 0 ≤ x := by dsimp [x]; nlinarith
  have hx1 : x ≤ 1 := by dsimp [x]; nlinarith
  constructor
  · exact sq_nonneg x
  · dsimp [a]; nlinarith

private def basis : OrthonormalBasis (Fin 24) ℂ Coeff := EuclideanSpace.basisFun (Fin 24) ℂ
private def synthesis (f : Fin 24 → H) : Coeff →L[ℂ] H :=
  (basis.toBasis.constr ℂ f).toContinuousLinearMap
private theorem synthesis_basis (f : Fin 24 → H) (i : Fin 24) :
    synthesis f (basis i) = f i := by
  exact basis.toBasis.constr_basis ℂ f i

private theorem synthesis_norm_bound (A : Coeff →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ j, ‖A (basis j)‖ ≤ C) : ‖A‖ ≤ C * Real.sqrt 24 := by
  apply ContinuousLinearMap.opNorm_le_bound A (by positivity)
  intro z
  have hz := congrArg A (basis.sum_repr z).symm
  simp only [map_sum, map_smul] at hz
  calc
    ‖A z‖ = ‖∑ i, basis.repr z i • A (basis i)‖ := congrArg norm hz
    _ ≤ ∑ i, ‖basis.repr z i • A (basis i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖basis.repr z i‖ * ‖A (basis i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖basis.repr z i‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hc i) (norm_nonneg _)
    _ = C * ∑ i, ‖z i‖ := by simp [basis, EuclideanSpace.basisFun_repr, Finset.mul_sum, mul_comm]
    _ ≤ C * (Real.sqrt 24 * ‖z‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa using sum_norm_le_sqrt_card_mul_norm z
    _ = (C * Real.sqrt 24) * ‖z‖ := by ring

private def columnVector (z : List (ℂ × Fin 24)) : Coeff :=
  (z.map fun c => c.1 • basis c.2).sum
private theorem column_vector_norm (z : List (ℂ × Fin 24)) :
    ‖columnVector z‖ ≤ (z.map fun c => ‖c.1‖).sum := by
  induction z with
  | nil => simp [columnVector]
  | cons c z ih =>
    change ‖c.1 • basis c.2 + columnVector z‖ ≤ ‖c.1‖ + (z.map fun c => ‖c.1‖).sum
    calc
      _ ≤ ‖c.1 • basis c.2‖ + ‖columnVector z‖ := norm_add_le _ _
      _ ≤ _ := by simpa only [norm_smul, basis.norm_eq_one, mul_one] using add_le_add_right ih ‖c.1‖

private theorem coefficient_column_sum (r : ℂ) (hr : ‖r‖ ≤ 1) :
    ∀ g j, ((columns r g j).map fun c => ‖c.1‖).sum ≤ 13 := by
  have hr0 := norm_nonneg r
  have hr2 : ‖r‖ ^ 2 ≤ 1 := by nlinarith
  intro g j
  fin_cases g <;> fin_cases j <;>
    norm_num [columns, norm_neg, norm_pow] <;> nlinarith

private theorem residual_coefficients (r : ℂ) (hr : ‖r‖ ≤ 1) :
    ∀ g j e, e ∈ errors r g j → ‖e.1‖ ≤ 1 := by
  intro g j
  fin_cases g <;> fin_cases j <;> simp [errors, norm_neg, hr]

private theorem residual_length (r : ℂ) : ∀ g j, (errors r g j).length ≤ 17 := by
  intro g j
  fin_cases g <;> fin_cases j <;> norm_num [errors]

/-- The maximum is over the source's fourteen tails, without any omitted tail. -/
def delta (r : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (v : H) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin 14 => ‖residual r s t (wordEval s t (tails i) v)‖)
private theorem tail_le_delta (r : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (v : H) (i : Fin 14) :
    ‖residual r s t (wordEval s t (tails i) v)‖ ≤ delta r s t v := by
  exact Finset.le_sup' (fun i : Fin 14 => ‖residual r s t (wordEval s t (tails i) v)‖)
    (Finset.mem_univ i)
private theorem delta_nonneg (r : ℂ) (s t : H ≃ₗᵢ[ℂ] H) (v : H) : 0 ≤ delta r s t v :=
  (norm_nonneg _).trans (tail_le_delta r s t v 0)

private theorem error_vector_bound (r : ℂ) (hr : ‖r‖ ≤ 1)
    (s t : H ≃ₗᵢ[ℂ] H) (v : H) (g : Fin 2) (j : Fin 24) :
    ‖errorVector r s t v g j‖ ≤ 17 * delta r s t v := by
  have hall (l : List (ℂ × Word × Fin 14))
      (hl : ∀ e ∈ l, ‖e.1‖ ≤ 1) :
      ‖(l.map fun e => e.1 • wordEval s t e.2.1
        (residual r s t (wordEval s t (tails e.2.2) v))).sum‖ ≤
          l.length * delta r s t v := by
    induction l with
    | nil => simp
    | cons e l ih =>
      have he : ‖e.1 • wordEval s t e.2.1
          (residual r s t (wordEval s t (tails e.2.2) v))‖ ≤ delta r s t v := by
        rw [norm_smul, LinearIsometryEquiv.norm_map]
        exact (mul_le_mul_of_nonneg_right (hl e (by simp)) (norm_nonneg _)).trans
          (by simpa using tail_le_delta r s t v e.2.2)
      have hi := ih (fun e he => hl e (by simp [he]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact (norm_add_le _ _).trans ((add_le_add he hi).trans (le_of_eq (by ring)))
  have h := hall (errors r g j) (residual_coefficients r hr g j)
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast residual_length r g j)
    (delta_nonneg r s t v))

private def synthesisOrbit (s t : H ≃ₗᵢ[ℂ] H) (v : H) : Coeff →L[ℂ] H :=
  synthesis (fun j => wordEval s t (orbitWords j) v)
private def matrixOperator (r : ℂ) (g : Fin 2) : Coeff →L[ℂ] Coeff :=
  synthesis (fun j => columnVector (columns r g j))

private theorem matrix_norm_bound (r : ℂ) (hr : ‖r‖ ≤ 1) (g : Fin 2) :
    ‖matrixOperator r g‖ ≤ 85 := by
  have h := synthesis_norm_bound (matrixOperator r g) 13 (by norm_num)
    (fun j => by
      rw [matrixOperator, synthesis_basis]
      exact (column_vector_norm _).trans (coefficient_column_sum r hr g j))
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)
  have hs0 := Real.sqrt_nonneg 24
  have hsmall : 13 * Real.sqrt 24 ≤ 85 := by nlinarith
  exact h.trans hsmall

private theorem synthesis_column_vector (s t : H ≃ₗᵢ[ℂ] H) (v : H)
    (l : List (ℂ × Fin 24)) :
    synthesisOrbit s t v (columnVector l) =
      (l.map fun c => c.1 • wordEval s t (orbitWords c.2) v).sum := by
  induction l with
  | nil => simp [columnVector]
  | cons c l ih =>
    change synthesisOrbit s t v (c.1 • basis c.2 + columnVector l) = _
    rw [map_add, map_smul, ih]
    simp only [synthesisOrbit, synthesis_basis, List.map_cons, List.sum_cons]

private theorem intertwining_norm_bound (r : ℂ) (hr : ‖r‖ ≤ 1)
    (s t : H ≃ₗᵢ[ℂ] H) (hbraid : s*t*s=t*s*t) (v : H) (g : Fin 2) :
    ‖(generators s t g).toLinearIsometry.toContinuousLinearMap.comp (synthesisOrbit s t v) -
      (synthesisOrbit s t v).comp (matrixOperator r g)‖ ≤ 95 * delta r s t v := by
  have hc (j : Fin 24) :
      ‖((generators s t g).toLinearIsometry.toContinuousLinearMap.comp (synthesisOrbit s t v) -
        (synthesisOrbit s t v).comp (matrixOperator r g)) (basis j)‖ ≤ 17 * delta r s t v := by
    change ‖generators s t g (synthesisOrbit s t v (basis j)) -
      synthesisOrbit s t v (matrixOperator r g (basis j))‖ ≤ _
    rw [matrixOperator, synthesis_basis, synthesis_column_vector]
    simp only [synthesisOrbit, synthesis_basis]
    rw [environment_columns s t hbraid r v]
    change ‖columnOrbit r s t v g j + errorVector r s t v g j - columnOrbit r s t v g j‖ ≤ _
    rw [add_sub_cancel_left]
    exact error_vector_bound r hr s t v g j
  have h := synthesis_norm_bound _ (17 * delta r s t v) (mul_nonneg (by norm_num) (delta_nonneg r s t v)) hc
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)
  have hs0 := Real.sqrt_nonneg 24
  have hsmall : 17 * Real.sqrt 24 ≤ 95 := by nlinarith
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall (delta_nonneg r s t v)])

/-- The original cubic polynomial evaluated at the actual ambient unitary. -/
def cubicOperator (r : ℂ) (s : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  let S := s.toLinearIsometry.toContinuousLinearMap
  S.comp (S.comp S) - r • S.comp S + r • S - ContinuousLinearMap.id ℂ H

/-- The genuine ambient Hilbert-Schmidt root mean square of the two conjugation defects. -/
def defect {β : Type*} (b : HilbertBasis β ℂ H) (S : Submodule ℂ H)
    [S.HasOrthogonalProjection] (s t : H ≃ₗᵢ[ℂ] H) : ℝ :=
  Real.sqrt ((1 / 2 : ℝ) * ∑ g : Fin 2,
    ∑' l, ‖projectionDefect S (generators s t g) (b l)‖ ^ 2)

/-- Complete original C117 Lemma 46.2 on the original arbitrary complex Hilbert ambient.
The hypotheses are only a unitary braid pair and a unit vector. -/
theorem condition_free_projection {β : Type*} (b : HilbertBasis β ℂ H)
    (s t : H ≃ₗᵢ[ℂ] H) (hbraid : s*t*s=t*s*t) (v : H) (hv : ‖v‖ = 1) :
    let δ := Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin 14 => ‖cubicOperator (a : ℂ) s (wordEval s t (tails i) v)‖)
    ∃ S : Submodule ℂ H, ∃ _ : FiniteDimensional ℂ S,
      IsIdempotentElem S.starProjection ∧ S.starProjection.toLinearMap.IsSymmetric ∧
      S.starProjection.range = S ∧
      1 ≤ Module.finrank ℂ S ∧ Module.finrank ℂ S ≤ 24 ∧
      (∀ g, HilbertSchmidt.IsHilbertSchmidt (projectionDefect S (generators s t g))) ∧
      (∀ g, Summable (fun l => ‖projectionDefect S (generators s t g) (b l)‖ ^ 2)) ∧
      (0 < δ ∧ δ < 1 → defect b S s t ≤ 785 * δ ^ (1 / 24 : ℝ)) ∧
      (δ = 0 → defect b S s t = 0 ∧
        ∀ g, projectionDefect S (generators s t g) = 0) := by
  let δ := delta (a : ℂ) s t v
  have hδeq : (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin 14 => ‖cubicOperator (a : ℂ) s (wordEval s t (tails i) v)‖)) = δ := by
    unfold δ delta
    congr 1
  dsimp only
  rw [hδeq]
  have ha : ‖(a : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg parameter_bounds.1]
    exact parameter_bounds.2
  have hT : ∃ z : Coeff, ‖z‖ = 1 ∧ 1 ≤ ‖synthesisOrbit s t v z‖ := by
    refine ⟨basis 0, basis.norm_eq_one 0, ?_⟩
    simp only [synthesisOrbit, synthesis_basis]
    simp [orbitWords, wordEval, hv]
  obtain ⟨S, hS, h1, h24, hHS, hsum, hbound, hz⟩ :=
    exists_rank_twentyfour_projection_bound b (synthesisOrbit s t v) hT
      (generators s t) (matrixOperator (a : ℂ)) δ (delta_nonneg _ _ _ _)
      (matrix_norm_bound (a : ℂ) ha)
      (intertwining_norm_bound (a : ℂ) ha s t hbraid v)
  letI := hS
  refine ⟨S, hS, S.isIdempotentElem_starProjection, S.starProjection_isSymmetric,
    Submodule.range_starProjection S, h1, h24, hHS, hsum, fun _ => hbound, ?_⟩
  intro hzero
  have hh := hz hzero
  refine ⟨?_, hh⟩
  simp [defect, hh]

#print axioms condition_free_projection

end D5.S3.Observer.Hilbert.C117FixedFourteenProjection
