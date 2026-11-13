/- GID: D5/S3/Quantum/Algebra/FixedDiagonalDeterminant
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FixedDiagonalDeterminant
   mirror-E: none(waiver:symbolic-fixed-matrix)
   anchors: []
   utility: none
   digest: Adjugate support for a fixed matrix with independent diagonal parameters. -/

module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic

/-! Fixed coefficients and independent row parameters. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.FixedDiagonalDeterminant

open Matrix MvPolynomial
open scoped Classical

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- The row-parameter matrix; no matrix entry is made into an independent variable. -/
def rowMatrix (N : Matrix ι ι k) : Matrix ι ι (MvPolynomial ι k) :=
  1 + diagonal (fun i => X i) * N.map (C : k →+* MvPolynomial ι k)

/-- Independent diagonal parameters added to the same fixed coefficients. -/
def diagonalMatrix (N : Matrix ι ι k) : Matrix ι ι (MvPolynomial ι k) :=
  diagonal (fun i => X i) + N.map (C : k →+* MvPolynomial ι k)

private lemma reciprocal_matrix {A : Type*} [CommRing A] (f : k →+* A)
    (x : ι → Aˣ) (N : Matrix ι ι k) :
    (rowMatrix N).map (eval₂Hom f (fun i => (x i : A))) =
      diagonal (fun i => (x i : A)) *
        (diagonalMatrix N).map (eval₂Hom f (fun i => ((x i)⁻¹ : Aˣ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rowMatrix, diagonalMatrix, Matrix.diagonal_mul, mul_add]
  · simp [rowMatrix, diagonalMatrix, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.one_apply, hij]

/-- Reciprocal coordinates multiply the diagonal determinant by precisely the
product of the coordinates. The formula applies in any commutative ring when
the coordinates are units, including a Laurent polynomial ring. -/
theorem reciprocal_determinant {A : Type*} [CommRing A] (f : k →+* A)
    (x : ι → Aˣ) (N : Matrix ι ι k) :
    eval₂Hom f (fun i => (x i : A)) (rowMatrix N).det =
      (∏ i, (x i : A)) *
        eval₂Hom f (fun i => ((x i)⁻¹ : Aˣ)) (diagonalMatrix N).det := by
  rw [RingHom.map_det]
  change ((rowMatrix N).map _).det = _
  rw [reciprocal_matrix, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  exact ((eval₂Hom f (fun i => ((x i)⁻¹ : Aˣ))).map_det _).symm

private def derivativeMatrix (i : ι) (M : Matrix ι ι (MvPolynomial ι k)) :=
  M.map (pderiv i)

private lemma derivative_mul (i : ι) (A B : Matrix ι ι (MvPolynomial ι k)) :
    derivativeMatrix i (A * B) = derivativeMatrix i A * B + A * derivativeMatrix i B := by
  apply Matrix.ext
  intro a b
  simp [derivativeMatrix, Matrix.mul_apply, pderiv_mul, Finset.sum_add_distrib, mul_comm, add_comm]

private lemma derivative_adjugate (i : ι) (M : Matrix ι ι (MvPolynomial ι k)) :
    M.adjugate * derivativeMatrix i M * M.adjugate +
      M.det • derivativeMatrix i M.adjugate =
      (pderiv i M.det) • M.adjugate := by
  have h := congrArg (derivativeMatrix i) (Matrix.mul_adjugate M)
  have hd : derivativeMatrix i (M.det • (1 : Matrix ι ι (MvPolynomial ι k))) =
      (pderiv i M.det) • (1 : Matrix ι ι (MvPolynomial ι k)) := by
    apply Matrix.ext
    intro a b
    by_cases hab : a = b <;> simp [derivativeMatrix, hab]
  rw [derivative_mul, hd] at h
  have hh := congrArg (fun A => M.adjugate * A) h
  simpa only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.adjugate_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] using hh

private lemma row_derivative (N : Matrix ι ι k) (i : ι) :
    derivativeMatrix i (rowMatrix N) =
      diagonal (Pi.single i 1) * N.map (C : k →+* MvPolynomial ι k) := by
  apply Matrix.ext
  intro a b
  by_cases hai : a = i
  · subst a
    by_cases hib : i = b <;>
      simp [derivativeMatrix, rowMatrix, Matrix.diagonal_mul, pderiv_mul,
        pderiv_X, Pi.single_apply, Matrix.one_apply, hib]
  · by_cases hab : a = b <;>
      simp [derivativeMatrix, rowMatrix, Matrix.diagonal_mul, pderiv_mul,
        pderiv_X, Pi.single_apply, Matrix.one_apply, hai, hab, eq_comm]

private lemma row_zero (N : Matrix ι ι k) :
    (rowMatrix N).map (eval (fun _ => 0)) = 1 := by
  apply Matrix.ext
  intro a b
  simp [rowMatrix, Matrix.diagonal_mul, Matrix.one_apply]

private lemma adjugate_zero (N : Matrix ι ι k) :
    (rowMatrix N).adjugate.map (eval (fun _ => 0)) = 1 := by
  change (eval (fun _ => 0)).mapMatrix (rowMatrix N).adjugate = _
  rw [RingHom.map_adjugate]
  change ((rowMatrix N).map (eval (fun _ => 0))).adjugate = _
  rw [row_zero, Matrix.adjugate_one]

/-- A zero adjugate entry separates every two-step route in the same adjugate. -/
private theorem adjugate_zero_separates (N : Matrix ι ι k) (i j t : ι)
    (hij : (rowMatrix N).adjugate i j = 0) :
    (rowMatrix N).adjugate i t * (rowMatrix N).adjugate t j = 0 := by
  by_cases htj : t = j
  · subst t
    simp [hij]
  let M := rowMatrix N
  let G := M.adjugate
  have h := congrArg (fun A : Matrix ι ι (MvPolynomial ι k) => A i j)
    (derivative_adjugate t M)
  rw [row_derivative] at h
  have hp : ((G * diagonal (Pi.single t 1) * N.map (C : k →+* MvPolynomial ι k) * G) : Matrix ι ι (MvPolynomial ι k)) i j =
      G i t * (N.map (C : k →+* MvPolynomial ι k) * G) t j := by
    simp [Matrix.mul_assoc, Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
  change ((G * (diagonal (Pi.single t 1) * N.map (C : k →+* MvPolynomial ι k)) * G) : Matrix ι ι (MvPolynomial ι k)) i j +
    M.det * pderiv t (G i j) = pderiv t M.det * G i j at h
  rw [← Matrix.mul_assoc, hp] at h
  change G i j = 0 at hij
  simp only [hij, map_zero, mul_zero, add_zero] at h
  have hm := congrArg (fun A : Matrix ι ι (MvPolynomial ι k) => A t j)
    (Matrix.mul_adjugate M)
  have hm' : (M * G) = G + diagonal (fun a => X a) * (N.map (C : k →+* MvPolynomial ι k) * G) := by
    dsimp [M, rowMatrix]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  change (M * G) t j = M.det * (1 : Matrix ι ι (MvPolynomial ι k)) t j at hm
  rw [hm'] at hm
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.one_apply_ne htj, mul_zero] at hm
  have hx := congrArg (fun p : MvPolynomial ι k => X t * p) h
  calc
    G i t * G t j = G i t * (G t j + X t * (N.map (C : k →+* MvPolynomial ι k) * G) t j) -
        X t * (G i t * (N.map (C : k →+* MvPolynomial ι k) * G) t j) := by ring
    _ = 0 := by rw [hm, hx]; ring

private lemma adjugate_edge (N : Matrix ι ι k) {i j : ι} (hij : i ≠ j)
    (hN : N i j ≠ 0) : (rowMatrix N).adjugate i j ≠ 0 := by
  intro hz
  let M := rowMatrix N
  have h := congrArg (fun A : Matrix ι ι (MvPolynomial ι k) =>
    eval (fun _ => 0) (A i j)) (derivative_adjugate i M)
  rw [row_derivative] at h
  have he := adjugate_zero N
  have he' : ∀ a b, eval (fun _ => 0) (M.adjugate a b) =
      (1 : Matrix ι ι k) a b := fun a b => congrArg (fun A => A a b) he
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    Matrix.mul_apply, map_sum, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply, eval_C] at h
  simp only [he', Matrix.one_apply, Pi.single_apply] at h
  have hdz : derivativeMatrix i M.adjugate i j = 0 := by
    change pderiv i ((rowMatrix N).adjugate i j) = 0
    rw [hz, map_zero]
  simp [hij, hdz, Matrix.diagonal_apply, Pi.single_apply] at h
  exact hN h

/-- Every route in the nonzero support of the fixed coefficients gives a nonzero
entry of the adjugate of the row-parameter matrix. -/
private theorem adjugate_nonzero_of_reachable (N : Matrix ι ι k) {i j : ι}
    (h : Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) :
    (rowMatrix N).adjugate i j ≠ 0 := by
  have hd (a : ι) : (rowMatrix N).adjugate a a ≠ 0 := by
    intro hz
    have he := congrArg (fun A : Matrix ι ι k => A a a) (adjugate_zero N)
    simpa [hz] using he
  induction h with
  | refl => exact hd _
  | @tail b c hab hbc ih =>
    by_cases hbc' : b = c
    · subst c
      exact ih
    · intro hz
      have hp := adjugate_zero_separates N i c b hz
      exact (mul_ne_zero ih (adjugate_edge N hbc' hbc)) hp

private lemma derivative_prod_zero {α : Type*} (t : ι) (s : Finset α)
    (f : α → MvPolynomial ι k) (h : ∀ a ∈ s, pderiv t (f a) = 0) :
    pderiv t (∏ a ∈ s, f a) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]
    simp

private lemma derivative_det_zero (t : ι) (M : Matrix ι ι (MvPolynomial ι k))
    (h : ∀ a b, pderiv t (M a b) = 0) : pderiv t M.det = 0 := by
  rw [Matrix.det_apply, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  have hp := derivative_prod_zero t Finset.univ (fun a => M (σ a) a)
    (fun a _ => h (σ a) a)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs, hp]

private lemma adjugate_column_derivative (N : Matrix ι ι k) (i j : ι) :
    pderiv i ((rowMatrix N).adjugate j i) = 0 := by
  rw [Matrix.adjugate_apply]
  apply derivative_det_zero
  intro a b
  by_cases hai : a = i
  · subst a
    rw [Matrix.updateRow_self]
    by_cases hjb : j = b <;> simp [Pi.single_apply, hjb]
  · rw [Matrix.updateRow_ne hai]
    have hx : pderiv i (X a : MvPolynomial ι k) = 0 := pderiv_X_of_ne hai
    by_cases hab : a = b
    · subst b
      simp [rowMatrix, Matrix.diagonal_mul, pderiv_mul, hx]
    · simp [rowMatrix, Matrix.diagonal_mul, pderiv_mul, hx, Matrix.one_apply, hab]

private lemma determinant_derivative (N : Matrix ι ι k) (i : ι) :
    pderiv i (rowMatrix N).det =
      (N.map (C : k →+* MvPolynomial ι k) * (rowMatrix N).adjugate) i i := by
  let M := rowMatrix N
  have h := congrArg (fun A : Matrix ι ι (MvPolynomial ι k) => A i i)
    (congrArg (derivativeMatrix i) (Matrix.mul_adjugate M))
  rw [derivative_mul, row_derivative] at h
  have hz : (M * derivativeMatrix i M.adjugate) i i = 0 := by
    simp [Matrix.mul_apply, derivativeMatrix, M, adjugate_column_derivative]
  simp only [Matrix.add_apply] at h
  rw [hz, add_zero, Matrix.mul_assoc, Matrix.diagonal_mul] at h
  simpa [derivativeMatrix] using h.symm

private lemma determinant_ne_zero (N : Matrix ι ι k) : (rowMatrix N).det ≠ 0 := by
  intro hz
  have h := congrArg (eval (fun _ => 0)) hz
  rw [RingHom.map_det] at h
  change ((rowMatrix N).map (eval (fun _ => 0))).det = 0 at h
  rw [row_zero, Matrix.det_one] at h
  exact one_ne_zero h

/-- The Rayleigh difference for two distinct parameters is nonzero whenever the
fixed nonzero support connects both directions. -/
private theorem rayleigh_nonzero (N : Matrix ι ι k) {i j : ι} (hij : i ≠ j)
    (hijN : Relation.ReflTransGen (fun a b => N a b ≠ 0) i j)
    (hjiN : Relation.ReflTransGen (fun a b => N a b ≠ 0) j i) :
    pderiv i (rowMatrix N).det * pderiv j (rowMatrix N).det -
      (rowMatrix N).det * pderiv i (pderiv j (rowMatrix N).det) ≠ 0 := by
  let M := rowMatrix N
  let G := M.adjugate
  let A : Matrix ι ι (MvPolynomial ι k) := N.map C
  have hbase := derivative_adjugate i M
  rw [row_derivative] at hbase
  have hdA : derivativeMatrix i A = 0 := by
    apply Matrix.ext
    intro a b
    simp [derivativeMatrix, A]
  have hdAG : derivativeMatrix i (A * G) = A * derivativeMatrix i G := by
    rw [derivative_mul, hdA, Matrix.zero_mul, zero_add]
  have hmat : A * G * diagonal (Pi.single i 1) * (A * G) +
      M.det • (A * derivativeMatrix i G) = pderiv i M.det • (A * G) := by
    calc
      _ = A * (G * (diagonal (Pi.single i 1) * A) * G +
        M.det • derivativeMatrix i G) := by
          simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [hbase]; exact Matrix.mul_smul _ _ _
  have h := congrArg (fun B : Matrix ι ι (MvPolynomial ι k) => B j j) hmat
  have hform : (A * G) j i * (A * G) i j +
      M.det * pderiv i ((A * G) j j) = pderiv i M.det * (A * G) j j := by
    let B := A * G
    have hs : ((B * diagonal (Pi.single i 1) * B) : Matrix ι ι (MvPolynomial ι k)) j j =
        B j i * B i j := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, Finset.mul_sum]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [← hdAG] at h
    rw [hs] at h
    exact h
  have hdiag : ∀ t, pderiv t M.det = (A * G) t t := determinant_derivative N
  have he (a b : ι) (hab : a ≠ b) : X a * (A * G) a b = - G a b := by
    have hh := congrArg (fun B : Matrix ι ι (MvPolynomial ι k) => B a b)
      (Matrix.mul_adjugate M)
    have hm : M * G = G + diagonal (fun a => X a) * (A * G) := by
      dsimp [M, rowMatrix, A]
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hm] at hh
    simpa [Matrix.add_apply, Matrix.diagonal_mul, Matrix.one_apply_ne hab,
      eq_neg_iff_add_eq_zero, add_comm] using hh
  have haij : (A * G) i j ≠ 0 := by
    intro hz
    have hh := he i j hij
    rw [hz, mul_zero, zero_eq_neg] at hh
    exact adjugate_nonzero_of_reachable N hijN hh
  have haji : (A * G) j i ≠ 0 := by
    intro hz
    have hh := he j i hij.symm
    rw [hz, mul_zero, zero_eq_neg] at hh
    exact adjugate_nonzero_of_reachable N hjiN hh
  change pderiv i M.det * pderiv j M.det - M.det * pderiv i (pderiv j M.det) ≠ 0
  rw [hdiag j]
  have heq : pderiv i M.det * (A * G) j j - M.det * pderiv i ((A * G) j j) =
      (A * G) j i * (A * G) i j := by linear_combination -hform
  rw [heq]
  exact mul_ne_zero haji haij

private lemma row_multiaffine (N : Matrix ι ι k) (i : ι) :
    (rowMatrix N).det.degreeOf i ≤ 1 := by
  have he (a b : ι) : (rowMatrix N a b).degreeOf i ≤ if a = i then 1 else 0 := by
    simp only [rowMatrix, Matrix.add_apply, Matrix.diagonal_mul, Matrix.map_apply]
    apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    · apply (degreeOf_mul_C_le _ _ _).trans
      simp [degreeOf_X, eq_comm]
  rw [Matrix.det_apply]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro σ _
  have hp : degreeOf i (∏ a, rowMatrix N (σ a) a) ≤ 1 := by
    apply (degreeOf_prod_le _ _ _).trans
    calc
      ∑ a, degreeOf i (rowMatrix N (σ a) a) ≤ ∑ a, if σ a = i then 1 else 0 :=
        Finset.sum_le_sum (fun a _ => he (σ a) a)
      _ = 1 := by simp [← Equiv.eq_symm_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, degreeOf_neg] using hp

/-- Strong connectivity of the actual nonzero entries suffices for irreducibility
of the row-parameter determinant over any field, in every size at least two. -/
theorem row_determinant_irreducible [Nontrivial ι] (N : Matrix ι ι k)
    (hN : ∀ i j, Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) :
    Irreducible (rowMatrix N).det := by
  classical
  have hf := determinant_ne_zero N
  have hu : ¬ IsUnit (rowMatrix N).det := by
    intro hu
    obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    have hh := rayleigh_nonzero N hij (hN i j) (hN j i)
    simp [hc] at hh
  refine ⟨hu, ?_⟩
  intro f g hfg
  by_contra hn
  obtain ⟨hfu, hgu⟩ := not_or.mp hn
  have hfn : f ≠ 0 := left_ne_zero_of_mul (hfg ▸ hf)
  have hgn : g ≠ 0 := right_ne_zero_of_mul (hfg ▸ hf)
  have hd : Disjoint f.vars g.vars := by
    apply Finset.disjoint_left.mpr
    intro i hif hig
    have hdf := mem_vars_iff_degreeOf_ne_zero.mp hif
    have hdg := mem_vars_iff_degreeOf_ne_zero.mp hig
    have hh := row_multiaffine N i
    rw [hfg, degreeOf_mul_eq hfn hgn] at hh
    omega
  have hv (p : MvPolynomial ι k) (hp : p ≠ 0) (hpu : ¬ IsUnit p) : p.vars.Nonempty := by
    by_contra hn
    have hc := vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
    have hp0 : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp
      simpa [hz] using hc
    exact hpu (hc ▸ (isUnit_iff_ne_zero.mpr hp0).map C)
  obtain ⟨i, hi⟩ := hv f hfn hfu
  obtain ⟨j, hj⟩ := hv g hgn hgu
  have hig : i ∉ g.vars := fun h => Finset.disjoint_left.mp hd hi h
  have hjf : j ∉ f.vars := fun h => Finset.disjoint_left.mp hd h hj
  have hij : i ≠ j := by intro h; exact hig (h ▸ hj)
  have hgi := pderiv_eq_zero_of_notMem_vars hig
  have hfj := pderiv_eq_zero_of_notMem_vars hjf
  have hgfij : pderiv i (pderiv j f) = 0 := by rw [hfj, map_zero]
  have hggij : pderiv i (pderiv j g) = 0 := by rw [pderiv_comm, hgi, map_zero]
  have hh := rayleigh_nonzero N hij (hN i j) (hN j i)
  rw [hfg] at hh
  apply hh
  simp only [pderiv_mul, map_add, hgi, hfj, hgfij, hggij, mul_zero, zero_mul, add_zero, zero_add]
  ring

private abbrev rationalMap : MvPolynomial ι k →+* FractionRing (MvPolynomial ι k) :=
  algebraMap _ _

private def coordinateUnit (i : ι) : (FractionRing (MvPolynomial ι k))ˣ :=
  Units.mk0 (rationalMap (X i))
    (by
      intro hz
      apply X_ne_zero (R := k) i
      exact (IsFractionRing.injective (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)))
        (by simpa only [map_zero] using hz))

private lemma coordinate_eval :
    eval₂Hom (rationalMap.comp C) (fun i => (coordinateUnit (k := k) i :
      FractionRing (MvPolynomial ι k))) = rationalMap := by
  ext <;> simp [coordinateUnit, RingHom.comp_apply]

private lemma diagonal_determinant_ne_zero (N : Matrix ι ι k) :
    (diagonalMatrix N).det ≠ 0 := by
  intro hz
  have h := reciprocal_determinant (rationalMap.comp C) (coordinateUnit (k := k)) N
  rw [coordinate_eval, hz, map_zero, mul_zero] at h
  exact determinant_ne_zero N
    ((IsFractionRing.injective (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)))
      (by simpa only [map_zero] using h))

private lemma diagonal_adjugate_nonzero (N : Matrix ι ι k) {i j : ι}
    (h : Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) :
    (diagonalMatrix N).adjugate i j ≠ 0 := by
  intro hz
  let f := (rationalMap (k := k) (ι := ι)).comp C
  let x := coordinateUnit (k := k) (ι := ι)
  let ε := eval₂Hom f (fun a => ((x a)⁻¹ : (FractionRing (MvPolynomial ι k))ˣ))
  have hr : (rowMatrix N).map rationalMap =
      diagonal (fun a => (x a : FractionRing (MvPolynomial ι k))) *
        (diagonalMatrix N).map ε := by
    have he : eval₂Hom f (fun a => (x a : FractionRing (MvPolynomial ι k))) =
        rationalMap := coordinate_eval
    have hh := reciprocal_matrix f x N
    rw [he] at hh
    exact hh
  have ha : (rowMatrix N).adjugate.map rationalMap =
      (diagonalMatrix N).adjugate.map ε *
        diagonal (fun a => ∏ b ∈ Finset.univ.erase a,
          (x b : FractionRing (MvPolynomial ι k))) := by
    change rationalMap.mapMatrix _ = _
    rw [RingHom.map_adjugate]
    change ((rowMatrix N).map rationalMap).adjugate = _
    rw [hr, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal]
    congr 1
    exact (ε.map_adjugate _).symm
  have hh := congrArg (fun A : Matrix ι ι (FractionRing (MvPolynomial ι k)) => A i j) ha
  simp only [Matrix.map_apply, Matrix.mul_diagonal, hz, map_zero, zero_mul] at hh
  exact adjugate_nonzero_of_reachable N h
    ((IsFractionRing.injective (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)))
      (by simpa only [map_zero] using hh))

private lemma diagonal_derivative (N : Matrix ι ι k) (i : ι) :
    derivativeMatrix i (diagonalMatrix N) = diagonal (Pi.single i 1) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [derivativeMatrix, diagonalMatrix, Pi.single_apply, pderiv_X, eq_comm]
  · simp [derivativeMatrix, diagonalMatrix, Matrix.diagonal_apply, hab]

private lemma diagonal_adjugate_column_derivative (N : Matrix ι ι k) (i j : ι) :
    pderiv i ((diagonalMatrix N).adjugate j i) = 0 := by
  rw [Matrix.adjugate_apply]
  apply derivative_det_zero
  intro a b
  by_cases hai : a = i
  · subst a
    rw [Matrix.updateRow_self]
    by_cases hjb : j = b <;> simp [Pi.single_apply, hjb]
  · rw [Matrix.updateRow_ne hai]
    have hx : pderiv i (X a : MvPolynomial ι k) = 0 := pderiv_X_of_ne hai
    by_cases hab : a = b
    · subst b
      simp only [diagonalMatrix, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.map_apply]
      rw [map_add, hx, pderiv_C, add_zero]
    · simp [diagonalMatrix, Matrix.diagonal_apply, hab]

private lemma diagonal_determinant_derivative (N : Matrix ι ι k) (i : ι) :
    pderiv i (diagonalMatrix N).det = (diagonalMatrix N).adjugate i i := by
  let M := diagonalMatrix N
  have h := congrArg (fun A : Matrix ι ι (MvPolynomial ι k) => A i i)
    (congrArg (derivativeMatrix i) (Matrix.mul_adjugate M))
  rw [derivative_mul, diagonal_derivative] at h
  have hz : (M * derivativeMatrix i M.adjugate) i i = 0 := by
    simp [Matrix.mul_apply, derivativeMatrix, M, diagonal_adjugate_column_derivative]
  simp only [Matrix.add_apply] at h
  rw [hz, add_zero, Matrix.diagonal_mul] at h
  simpa [derivativeMatrix] using h.symm

private lemma diagonal_rayleigh_nonzero (N : Matrix ι ι k) {i j : ι} (hij : i ≠ j)
    (hijN : Relation.ReflTransGen (fun a b => N a b ≠ 0) i j)
    (hjiN : Relation.ReflTransGen (fun a b => N a b ≠ 0) j i) :
    pderiv i (diagonalMatrix N).det * pderiv j (diagonalMatrix N).det -
      (diagonalMatrix N).det * pderiv i (pderiv j (diagonalMatrix N).det) ≠ 0 := by
  let M := diagonalMatrix N
  let G := M.adjugate
  have hbase := derivative_adjugate i M
  rw [diagonal_derivative] at hbase
  have h := congrArg (fun B : Matrix ι ι (MvPolynomial ι k) => B j j) hbase
  have hs : ((G * diagonal (Pi.single i 1) * G) : Matrix ι ι (MvPolynomial ι k)) j j =
      G j i * G i j := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, Finset.mul_sum]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [hs] at h
  change G j i * G i j + M.det * pderiv i (G j j) = pderiv i M.det * G j j at h
  have hd : ∀ a, pderiv a M.det = G a a := diagonal_determinant_derivative N
  have heq : pderiv i M.det * pderiv j M.det - M.det * pderiv i (pderiv j M.det) =
      G j i * G i j := by
    rw [hd j]
    change pderiv i M.det * G j j - M.det * pderiv i (G j j) = _
    linear_combination -h
  change pderiv i M.det * pderiv j M.det - M.det * pderiv i (pderiv j M.det) ≠ 0
  rw [heq]
  exact mul_ne_zero (diagonal_adjugate_nonzero N hjiN) (diagonal_adjugate_nonzero N hijN)

private lemma diagonal_multiaffine (N : Matrix ι ι k) (i : ι) :
    (diagonalMatrix N).det.degreeOf i ≤ 1 := by
  have he (a b : ι) : (diagonalMatrix N a b).degreeOf i ≤ if a = i then 1 else 0 := by
    simp only [diagonalMatrix, Matrix.add_apply, Matrix.map_apply]
    apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · by_cases hab : a = b
      · subst b
        simp [degreeOf_X, eq_comm]
      · simp [Matrix.diagonal_apply, hab]
    · simp
  rw [Matrix.det_apply]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro σ _
  have hp : degreeOf i (∏ a, diagonalMatrix N (σ a) a) ≤ 1 := by
    apply (degreeOf_prod_le _ _ _).trans
    calc
      ∑ a, degreeOf i (diagonalMatrix N (σ a) a) ≤ ∑ a, if σ a = i then 1 else 0 :=
        Finset.sum_le_sum (fun a _ => he (σ a) a)
      _ = 1 := by simp [← Equiv.eq_symm_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, degreeOf_neg] using hp

/-- Strong connectivity of the actual fixed nonzero support suffices for
irreducibility of the determinant with independent diagonal parameters. -/
theorem diagonal_determinant_irreducible [Nontrivial ι] (N : Matrix ι ι k)
    (hN : ∀ i j, Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) :
    Irreducible (diagonalMatrix N).det := by
  classical
  have hf := diagonal_determinant_ne_zero N
  have hu : ¬ IsUnit (diagonalMatrix N).det := by
    intro hu
    obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    have hh := diagonal_rayleigh_nonzero N hij (hN i j) (hN j i)
    simp [hc] at hh
  refine ⟨hu, ?_⟩
  intro f g hfg
  by_contra hn
  obtain ⟨hfu, hgu⟩ := not_or.mp hn
  have hfn : f ≠ 0 := left_ne_zero_of_mul (hfg ▸ hf)
  have hgn : g ≠ 0 := right_ne_zero_of_mul (hfg ▸ hf)
  have hd : Disjoint f.vars g.vars := by
    apply Finset.disjoint_left.mpr
    intro i hif hig
    have hdf := mem_vars_iff_degreeOf_ne_zero.mp hif
    have hdg := mem_vars_iff_degreeOf_ne_zero.mp hig
    have hh := diagonal_multiaffine N i
    rw [hfg, degreeOf_mul_eq hfn hgn] at hh
    omega
  have hv (p : MvPolynomial ι k) (hp : p ≠ 0) (hpu : ¬ IsUnit p) : p.vars.Nonempty := by
    by_contra hn
    have hc := vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
    have hp0 : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp
      simpa [hz] using hc
    exact hpu (hc ▸ (isUnit_iff_ne_zero.mpr hp0).map C)
  obtain ⟨i, hi⟩ := hv f hfn hfu
  obtain ⟨j, hj⟩ := hv g hgn hgu
  have hig : i ∉ g.vars := fun h => Finset.disjoint_left.mp hd hi h
  have hjf : j ∉ f.vars := fun h => Finset.disjoint_left.mp hd h hj
  have hij : i ≠ j := by intro h; exact hig (h ▸ hj)
  have hgi := pderiv_eq_zero_of_notMem_vars hig
  have hfj := pderiv_eq_zero_of_notMem_vars hjf
  have hgfij : pderiv i (pderiv j f) = 0 := by rw [hfj, map_zero]
  have hggij : pderiv i (pderiv j g) = 0 := by rw [pderiv_comm, hgi, map_zero]
  have hh := diagonal_rayleigh_nonzero N hij (hN i j) (hN j i)
  rw [hfg] at hh
  apply hh
  simp only [pderiv_mul, map_add, hgi, hfj, hgfij, hggij, mul_zero, zero_mul, add_zero, zero_add]
  ring

end D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
