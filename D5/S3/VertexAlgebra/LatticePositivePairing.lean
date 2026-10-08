/- GID: D5/S3/VertexAlgebra/LatticePositivePairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticePositivePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Hermitian pairing and all-integer current adjoints on the actual lattice carrier. -/

/-
Released under Apache 2.0. Matrix spectral and inverse results use mathlib.
Dong--Lin, arXiv:1308.2361v1, Definition 2.2 and Theorem 4.12 provide
ordinary lattice Hermitian context. Arguments are reversed to use the
second-linear convention of CKLW, arXiv:1503.01260v4, section 5.1.
The finite coefficient pairing, real Gram pullback and original-basis
current adjoint proofs are repo-derived. No full unitary VOA is asserted.
-/
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.Analysis.Matrix.PosDef
import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.Algebra.MvPolynomial.PDeriv
import D5.S3.VertexAlgebra.LatticeAllStateField
import Mathlib.GroupTheory.Perm.Fin


/-
Real positive Gram data for the unchanged ordinary lattice carrier.
The sole geometric premise is Matrix.PosDef of the real integral Gram.
Spectral and inverse matrix proofs use mathlib (Apache 2.0).
This is a consumed part of the concrete Hermitian construction, not a
standalone unitary-VOA assertion. Rank zero is included.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents Matrix
open scoped BigOperators
noncomputable section

abbrev realGram (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  D.G.map (Int.cast : ℤ → ℝ)

/-- A spectral square root factor, used only to pull back the form. -/
def rootFactor (D : LatticeData) (hD : (realGram D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  diagonal (fun i => Real.sqrt (hD.isHermitian.eigenvalues i)) *
    star (hD.isHermitian.eigenvectorUnitary : Matrix (Fin D.rank) (Fin D.rank) ℝ)

theorem rootFactor_gram (D : LatticeData) (hD : (realGram D).PosDef) :
    (rootFactor D hD)ᵀ * rootFactor D hD = realGram D := by
  let Q := hD.isHermitian.eigenvectorUnitary
  have hs (i : Fin D.rank) :
      Real.sqrt (hD.isHermitian.eigenvalues i) * Real.sqrt (hD.isHermitian.eigenvalues i) =
        hD.isHermitian.eigenvalues i := Real.mul_self_sqrt (hD.eigenvalues_pos i).le
  have hh := hD.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hh
  change realGram D = (Q : Matrix _ _ ℝ) *
    diagonal (fun i => hD.isHermitian.eigenvalues i) * star (Q : Matrix _ _ ℝ) at hh
  rw [hh]
  unfold rootFactor
  rw [Matrix.transpose_mul]
  simp only [Matrix.diagonal_transpose]
  have ht : (star (Q : Matrix (Fin D.rank) (Fin D.rank) ℝ))ᵀ = Q := by
    ext i j
    simp [Matrix.star_apply]
  rw [ht]
  simp only [← Matrix.mul_assoc]
  congr 1
  rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp [hs]

theorem rootFactor_isUnit (D : LatticeData) (hD : (realGram D).PosDef) :
    IsUnit (rootFactor D hD) := by
  have h := hD.isUnit
  rw [← rootFactor_gram D hD] at h
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
  rw [Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hd)

end
end D5.S3.VertexAlgebra.LatticeHermitian

/- Matrix substitution changes only the pairing, on the original oscillator ring.
The original currents, charges, fields and cocycle are never replaced. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def gramSubstitution (D : LatticeData) (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) :
    Oscillator D →+* Oscillator D :=
  eval₂Hom C (fun x => ∑ a : Fin D.rank, (M a x.1 : ℂ) • X (a,x.2))

@[simp] theorem gramSubstitution_C (D : LatticeData)
    (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) (c : ℂ) :
    gramSubstitution D M (C c) = C c := by simp [gramSubstitution]

@[simp] theorem gramSubstitution_X (D : LatticeData)
    (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) (x : Index D) :
    gramSubstitution D M (X x) = ∑ a : Fin D.rank, (M a x.1 : ℂ) • X (a,x.2) := by
  simp [gramSubstitution]

@[simp] theorem gramSubstitution_smul (D : LatticeData)
    (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) (c : ℂ) (p : Oscillator D) :
    gramSubstitution D M (c • p) = c • gramSubstitution D M p := by
  rw [← C_mul', map_mul, gramSubstitution_C, C_mul']

theorem gramSubstitution_one (D : LatticeData) (p : Oscillator D) :
    gramSubstitution D 1 p = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p x hp => simp [hp, Matrix.one_apply, eq_comm]

theorem gramSubstitution_comp (D : LatticeData)
    (M N : Matrix (Fin D.rank) (Fin D.rank) ℝ) (p : Oscillator D) :
    gramSubstitution D M (gramSubstitution D N p) = gramSubstitution D (M*N) p := by
  have hX (x : Index D) :
      gramSubstitution D M (gramSubstitution D N (X x)) =
        gramSubstitution D (M*N) (X x) := by
    simp only [gramSubstitution_X, map_sum, gramSubstitution_smul, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p x hp =>
    simp only [map_mul, hp, hX]

theorem gramSubstitution_injective (D : LatticeData)
    (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) (hM : IsUnit M) :
    Function.Injective (gramSubstitution D M) := by
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (M.isUnit_iff_isUnit_det.mp hM)
  have hleft (p : Oscillator D) : gramSubstitution D M⁻¹ (gramSubstitution D M p) = p := by
    rw [gramSubstitution_comp, hinv, gramSubstitution_one]
  exact Function.LeftInverse.injective hleft

/-- Concrete injective transform from the real positive Gram, with the actual polynomial type. -/
def fockTransform (D : LatticeData) (hD : (realGram D).PosDef) :
    Oscillator D →+* Oscillator D := gramSubstitution D (rootFactor D hD)

theorem fockTransform_injective (D : LatticeData) (hD : (realGram D).PosDef) :
    Function.Injective (fockTransform D hD) :=
  gramSubstitution_injective D _ (rootFactor_isUnit D hD)

end
end D5.S3.VertexAlgebra.LatticeHermitian

/- Finite factorial Fock pairing on the polynomial oscillator ring.
Conjugate-linear FIRST, linear SECOND. No completion or global operator star.
This coefficient construction is new task-local proof code built on mathlib.
Dong--Lin 1308.2361v1 uses the reversed convention; CKLW 1503.01260v4 §5.1
uses this convention. These citations do not serve as Lean premises. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality MvPolynomial
open scoped BigOperators
noncomputable section

def factorialWeight (D : LatticeData) (e : Index D →₀ ℕ) : ℕ :=
  e.prod (fun x n => (x.2+1)^n * n.factorial)

theorem factorialWeight_pos (D : LatticeData) (e : Index D →₀ ℕ) :
    0 < factorialWeight D e := by
  classical
  apply Finset.prod_pos
  intro x hx
  exact Nat.mul_pos (pow_pos (Nat.succ_pos _) _) (Nat.factorial_pos _)

@[simp] theorem factorialWeight_zero (D : LatticeData) : factorialWeight D 0 = 1 := by
  simp [factorialWeight]

/-- Both coefficient supports are finite; a first-support sum suffices. -/
def standardPair (D : LatticeData) (p q : Oscillator D) : ℂ :=
  (AddMonoidAlgebra.coeff p).sum (fun e c =>
    (factorialWeight D e : ℂ) * star c * coeff e q)

theorem standardPair_sum (D : LatticeData) (p q : Oscillator D) :
    standardPair D p q = ∑ e ∈ p.support,
      (factorialWeight D e : ℂ) * star (coeff e p) * coeff e q := by
  exact MvPolynomial.sum_def

@[simp] theorem standardPair_zero_left (D : LatticeData) (q : Oscillator D) :
    standardPair D 0 q = 0 := by simp [standardPair]
@[simp] theorem standardPair_zero_right (D : LatticeData) (p : Oscillator D) :
    standardPair D p 0 = 0 := by simp [standardPair]

theorem standardPair_add_left (D : LatticeData) (p q t : Oscillator D) :
    standardPair D (p+q) t = standardPair D p t + standardPair D q t := by
  classical
  unfold standardPair
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro e; simp
  · intro e a b; simp [mul_add, add_mul]

theorem standardPair_add_right (D : LatticeData) (p q t : Oscillator D) :
    standardPair D p (q+t) = standardPair D p q + standardPair D p t := by
  simp only [standardPair_sum, coeff_add, mul_add, Finset.sum_add_distrib]

theorem standardPair_smul_right (D : LatticeData) (c : ℂ) (p q : Oscillator D) :
    standardPair D p (c • q) = c * standardPair D p q := by
  classical
  simp only [standardPair_sum, coeff_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem standardPair_smul_left (D : LatticeData) (c : ℂ) (p q : Oscillator D) :
    standardPair D (c • p) q = star c * standardPair D p q := by
  classical
  unfold standardPair
  rw [AddMonoidAlgebra.coeff_smul]
  rw [Finsupp.sum_smul_index']
  · simp only [smul_eq_mul, star_mul]
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro e he
    ring
  · intro e; simp

theorem standardPair_on_finset (D : LatticeData) (p q : Oscillator D)
    (S : Finset (Index D →₀ ℕ)) (hp : p.support ⊆ S) :
    standardPair D p q = ∑ e ∈ S,
      (factorialWeight D e : ℂ) * star (coeff e p) * coeff e q := by
  classical
  rw [standardPair_sum]
  apply Finset.sum_subset hp
  intro e he hne
  simp [notMem_support_iff.mp hne]

theorem standardPair_hermitian (D : LatticeData) (p q : Oscillator D) :
    star (standardPair D p q) = standardPair D q p := by
  classical
  rw [standardPair_on_finset D p q (p.support ∪ q.support) Finset.subset_union_left,
    standardPair_on_finset D q p (p.support ∪ q.support) Finset.subset_union_right,
    star_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem standardPair_self_re (D : LatticeData) (p : Oscillator D) :
    (standardPair D p p).re = ∑ e ∈ p.support,
      (factorialWeight D e : ℝ) * Complex.normSq (coeff e p) := by
  rw [standardPair_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring



theorem standardPair_self_nonneg (D : LatticeData) (p : Oscillator D) :
    0 ≤ (standardPair D p p).re := by
  rw [standardPair_self_re]
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem standardPair_self_pos (D : LatticeData) (p : Oscillator D) (hp : p ≠ 0) :
    0 < (standardPair D p p).re := by
  classical
  obtain ⟨e, he⟩ : ∃ e, coeff e p ≠ 0 := by
    by_contra h
    apply hp
    ext e
    simpa using not_exists.mp h e
  rw [standardPair_self_re]
  apply Finset.sum_pos'
  · intro d hd
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · refine ⟨e, mem_support_iff.mpr he, ?_⟩
    exact mul_pos (by exact_mod_cast factorialWeight_pos D e)
      (Complex.normSq_pos.mpr he)

@[simp] theorem standardPair_monomial_left (D : LatticeData)
    (e : Index D →₀ ℕ) (c : ℂ) (q : Oscillator D) :
    standardPair D (monomial e c) q =
      (factorialWeight D e : ℂ) * star c * coeff e q := by
  simp [standardPair, monomial]



@[simp] theorem standardPair_one (D : LatticeData) :
    standardPair D 1 1 = 1 := by
  have h := standardPair_monomial_left D 0 1 (1 : Oscillator D)
  simpa using h

end
end D5.S3.VertexAlgebra.LatticeHermitian

/- Exact factorial coefficient calculation, including every frequency. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality MvPolynomial
open scoped BigOperators
noncomputable section

theorem factorialWeight_successor (D : LatticeData) (e : Index D →₀ ℕ) (x : Index D) :
    factorialWeight D (e + Finsupp.single x 1) =
      (x.2+1) * (e x+1) * factorialWeight D e := by
  classical
  let S := insert x e.support
  have hx : x ∈ S := Finset.mem_insert_self _ _
  have hse : e.support ⊆ S := Finset.subset_insert _ _
  have hses : (e+Finsupp.single x 1).support ⊆ S := by
    intro y hy
    have h := Finsupp.support_add hy
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_insert_of_mem h
    · have heq : y = x := by simpa using h
      subst y; exact hx
  have hprod : (∏ y ∈ S.erase x,
      (y.2+1) ^ ((e+Finsupp.single x 1 : Index D →₀ ℕ) y) * ((e+Finsupp.single x 1 : Index D →₀ ℕ) y).factorial) =
      ∏ y ∈ S.erase x, (y.2+1)^(e y) * (e y).factorial := by
    apply Finset.prod_congr rfl
    intro y hy
    have hn := (Finset.mem_erase.mp hy).1
    simp [Finsupp.single_apply, hn, Ne.symm hn]
  unfold factorialWeight
  rw [Finsupp.prod_of_support_subset _ hses _ (by intros; simp),
      Finsupp.prod_of_support_subset _ hse _ (by intros; simp)]
  rw [← Finset.mul_prod_erase S _ hx, ← Finset.mul_prod_erase S _ hx, hprod]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
  ring

/-- The standard creator at frequency r has adjoint r times its partial derivative. -/
theorem standardPair_X_mul (D : LatticeData) (x : Index D) (p q : Oscillator D) :
    standardPair D (X x * p) q =
      standardPair D p ((x.2+1 : ℂ) • pderiv x q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    have hx : (X x : Oscillator D) * monomial e c =
        monomial (e + Finsupp.single x 1) c := by
      rw [X, monomial_mul]
      simp [add_comm]
    rw [hx, standardPair_monomial_left, standardPair_monomial_left,
      coeff_smul, coeff_pderiv, factorialWeight_successor]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_eq_mul]
    ring
  | add p t hp ht =>
    simp [mul_add, standardPair_add_left, hp, ht]

end
end D5.S3.VertexAlgebra.LatticeHermitian

/- Positive Hermitian pairing on the EXACT charge--polynomial carrier.
Only the form is pulled back along the real spectral factor. Charges, epsilon,
Y, vacuum, translation, and current operators retain their sealed definitions.
Dong--Lin arXiv:1308.2361v1 Def.2.2/Thm.4.12, with arguments reversed to
use the second-linear convention of CKLW arXiv:1503.01260v4 §5.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality LatticeAllStateField MvPolynomial
open scoped BigOperators
noncomputable section

def oscillatorPair (D : LatticeData) (hD : (realGram D).PosDef)
    (p q : Oscillator D) : ℂ :=
  standardPair D (fockTransform D hD p) (fockTransform D hD q)

@[simp] theorem oscillatorPair_zero_left (D : LatticeData) (hD : (realGram D).PosDef)
    (q : Oscillator D) : oscillatorPair D hD 0 q = 0 := by simp [oscillatorPair]
@[simp] theorem oscillatorPair_zero_right (D : LatticeData) (hD : (realGram D).PosDef)
    (p : Oscillator D) : oscillatorPair D hD p 0 = 0 := by simp [oscillatorPair]

theorem oscillatorPair_add_left (D : LatticeData) (hD : (realGram D).PosDef)
    (p q t : Oscillator D) :
    oscillatorPair D hD (p+q) t = oscillatorPair D hD p t + oscillatorPair D hD q t := by
  simp [oscillatorPair, standardPair_add_left]
theorem oscillatorPair_add_right (D : LatticeData) (hD : (realGram D).PosDef)
    (p q t : Oscillator D) :
    oscillatorPair D hD p (q+t) = oscillatorPair D hD p q + oscillatorPair D hD p t := by
  simp [oscillatorPair, standardPair_add_right]
theorem oscillatorPair_smul_left (D : LatticeData) (hD : (realGram D).PosDef)
    (c : ℂ) (p q : Oscillator D) :
    oscillatorPair D hD (c • p) q = star c * oscillatorPair D hD p q := by
  simp [oscillatorPair, fockTransform, standardPair_smul_left]
theorem oscillatorPair_smul_right (D : LatticeData) (hD : (realGram D).PosDef)
    (c : ℂ) (p q : Oscillator D) :
    oscillatorPair D hD p (c • q) = c * oscillatorPair D hD p q := by
  simp [oscillatorPair, fockTransform, standardPair_smul_right]
theorem oscillatorPair_hermitian (D : LatticeData) (hD : (realGram D).PosDef)
    (p q : Oscillator D) : star (oscillatorPair D hD p q) = oscillatorPair D hD q p :=
  standardPair_hermitian D _ _
theorem oscillatorPair_self_nonneg (D : LatticeData) (hD : (realGram D).PosDef)
    (p : Oscillator D) : 0 ≤ (oscillatorPair D hD p p).re :=
  standardPair_self_nonneg D _
theorem oscillatorPair_self_pos (D : LatticeData) (hD : (realGram D).PosDef)
    (p : Oscillator D) (hp : p ≠ 0) : 0 < (oscillatorPair D hD p p).re := by
  apply standardPair_self_pos
  exact (fockTransform_injective D hD).ne_iff' (map_zero _ ) |>.mpr hp
@[simp] theorem oscillatorPair_one (D : LatticeData) (hD : (realGram D).PosDef) :
    oscillatorPair D hD 1 1 = 1 := by simp [oscillatorPair]

/-- Orthogonal charge sectors, each with the explicit factorial pullback. -/
def latticePair (D : LatticeData) (hD : (realGram D).PosDef) (u v : Carrier D) : ℂ :=
  u.sum (fun a p => oscillatorPair D hD p (v a))

@[simp] theorem latticePair_zero_left (D : LatticeData) (hD : (realGram D).PosDef)
    (v : Carrier D) : latticePair D hD 0 v = 0 := by simp [latticePair]
@[simp] theorem latticePair_zero_right (D : LatticeData) (hD : (realGram D).PosDef)
    (u : Carrier D) : latticePair D hD u 0 = 0 := by simp [latticePair]

theorem latticePair_add_left (D : LatticeData) (hD : (realGram D).PosDef)
    (u v t : Carrier D) :
    latticePair D hD (u+v) t = latticePair D hD u t + latticePair D hD v t := by
  apply Finsupp.sum_add_index'
  · intro a; simp
  · intro a p q; exact oscillatorPair_add_left D hD p q (t a)
theorem latticePair_add_right (D : LatticeData) (hD : (realGram D).PosDef)
    (u v t : Carrier D) :
    latticePair D hD u (v+t) = latticePair D hD u v + latticePair D hD u t := by
  simp [latticePair, Finsupp.sum, oscillatorPair_add_right, Finset.sum_add_distrib]
theorem latticePair_on_finset (D : LatticeData) (hD : (realGram D).PosDef)
    (u v : Carrier D) (S : Finset (Charge D)) (hu : u.support ⊆ S) :
    latticePair D hD u v = ∑ a ∈ S, oscillatorPair D hD (u a) (v a) := by
  classical
  unfold latticePair Finsupp.sum
  apply Finset.sum_subset hu
  intro a ha hne
  simp [Finsupp.notMem_support_iff.mp hne]

theorem latticePair_hermitian (D : LatticeData) (hD : (realGram D).PosDef)
    (u v : Carrier D) : star (latticePair D hD u v) = latticePair D hD v u := by
  classical
  rw [latticePair_on_finset D hD u v (u.support ∪ v.support) Finset.subset_union_left,
      latticePair_on_finset D hD v u (u.support ∪ v.support) Finset.subset_union_right,
      star_sum]
  exact Finset.sum_congr rfl (fun a ha => oscillatorPair_hermitian D hD _ _)

theorem latticePair_self_im (D : LatticeData) (hD : (realGram D).PosDef)
    (u : Carrier D) : (latticePair D hD u u).im = 0 := by
  have hi := congrArg Complex.im (latticePair_hermitian D hD u u)
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem latticePair_self_pos (D : LatticeData) (hD : (realGram D).PosDef)
    (u : Carrier D) (hu : u ≠ 0) : 0 < (latticePair D hD u u).re := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
    by_contra h
    apply hu
    apply Finsupp.ext
    intro a
    simpa using not_exists.mp h a
  unfold latticePair Finsupp.sum
  rw [Complex.re_sum]
  apply Finset.sum_pos'
  · intro b hb
    exact oscillatorPair_self_nonneg D hD (u b)
  · exact ⟨a, Finsupp.mem_support_iff.mpr ha, oscillatorPair_self_pos D hD (u a) ha⟩

@[simp] theorem latticePair_single_left (D : LatticeData) (hD : (realGram D).PosDef)
    (a : Charge D) (p : Oscillator D) (v : Carrier D) :
    latticePair D hD (Finsupp.single a p) v = oscillatorPair D hD p (v a) := by
  simp [latticePair]

theorem latticePair_single_single (D : LatticeData) (hD : (realGram D).PosDef)
    (a b : Charge D) (p q : Oscillator D) :
    latticePair D hD (Finsupp.single a p) (Finsupp.single b q) =
      if a = b then oscillatorPair D hD p q else 0 := by
  classical
  by_cases h : a = b
  · subst b; simp
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem latticePair_vacuum (D : LatticeData) (hD : (realGram D).PosDef) :
    latticePair D hD (vacuum D) (vacuum D) = 1 := by
  simp [vacuum]

/-- Algebraic adjoint PAIR: a relation on actual End, not an everywhere-defined star. -/
def AdjPair (D : LatticeData) (hD : (realGram D).PosDef)
    (A B : Module.End ℂ (Carrier D)) : Prop :=
  ∀ u v, latticePair D hD (A u) v = latticePair D hD u (B v)

end
end D5.S3.VertexAlgebra.LatticeHermitian

/- Actual all-integer current adjoints for the constructed non-diagonal form.
This is an algebraic adjoint pair on the unchanged finite-state carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeHermitian
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents MvPolynomial
open scoped BigOperators
noncomputable section

theorem gramSubstitution_pderiv (D : LatticeData)
    (M : Matrix (Fin D.rank) (Fin D.rank) ℝ) (a : Fin D.rank) (r : ℕ)
    (p : Oscillator D) :
    pderiv (a,r) (gramSubstitution D M p) =
      ∑ j : Fin D.rank, (M a j : ℂ) • gramSubstitution D M (pderiv (j,r) p) := by
  classical
  have hX (x : Index D) : pderiv (a,r) (gramSubstitution D M (X x)) =
      if r = x.2 then C (M a x.1 : ℂ) else 0 := by
    by_cases h : r = x.2
    · subst r
      simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, eq_comm, smul_eq_C_mul]
    · simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq,map_add,smul_add,Finset.sum_add_distrib]
  | mul_X p x hp =>
    rcases x with ⟨j,s⟩
    simp only [map_mul, pderiv_mul, map_add, gramSubstitution_X,
      gramSubstitution_smul, pderiv_X, hp, hX, smul_add, Finset.sum_add_distrib]
    congr 1
    · simp [Finset.sum_mul, mul_smul_comm]
    · by_cases h : r = s
      · subst r
        simp [Pi.single_apply, Prod.mk.injEq, eq_comm, smul_eq_C_mul, mul_comm]
      · simp [Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]

theorem root_contraction (D : LatticeData) (hD : (realGram D).PosDef)
    (i j : Fin D.rank) :
    ∑ a : Fin D.rank, (rootFactor D hD a i : ℂ) * (rootFactor D hD a j : ℂ) =
      (D.G i j : ℂ) := by
  have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℝ => M i j)
    (rootFactor_gram D hD)
  have hc := congrArg (algebraMap ℝ ℂ) h
  simpa [Matrix.mul_apply, Matrix.transpose_apply, realGram] using hc

theorem fockTransform_weightedPartial (D : LatticeData) (hD : (realGram D).PosDef)
    (i : Fin D.rank) (r : ℕ) (q : Oscillator D) :
    fockTransform D hD (weightedPartial D i r q) =
      ∑ a : Fin D.rank, (rootFactor D hD a i : ℂ) •
        pderiv (a,r) (fockTransform D hD q) := by
  classical
  simp only [fockTransform, gramSubstitution_pderiv, weightedPartial,
    LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    map_sum, gramSubstitution_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, root_contraction]

theorem oscillatorPair_X_mul (D : LatticeData) (hD : (realGram D).PosDef)
    (i : Fin D.rank) (r : ℕ) (p q : Oscillator D) :
    oscillatorPair D hD (X (i,r) * p) q =
      oscillatorPair D hD p ((r+1 : ℂ) • weightedPartial D i r q) := by
  classical
  unfold oscillatorPair
  simp only [fockTransform, map_mul, gramSubstitution_X, Finset.sum_mul,
    smul_mul_assoc]
  have hsum (S : Finset (Fin D.rank)) :
      standardPair D (∑ a ∈ S, (rootFactor D hD a i : ℂ) •
        (X (a,r) * gramSubstitution D (rootFactor D hD) p))
        (gramSubstitution D (rootFactor D hD) q) =
      ∑ a ∈ S, (rootFactor D hD a i : ℂ) *
        standardPair D (X (a,r) * gramSubstitution D (rootFactor D hD) p)
          (gramSubstitution D (rootFactor D hD) q) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha,standardPair_add_left,
        standardPair_smul_left,ih]
      simp only [Complex.star_def,Complex.conj_ofReal]
  rw [hsum]
  simp_rw [standardPair_X_mul]
  rw [gramSubstitution_smul]
  change _ = standardPair D (fockTransform D hD p)
    ((r+1 : ℂ) • fockTransform D hD (weightedPartial D i r q))
  rw [fockTransform_weightedPartial, Finset.smul_sum]
  have hsumr (S : Finset (Fin D.rank)) :
      standardPair D (fockTransform D hD p)
        (∑ a ∈ S, (r+1 : ℂ) • ((rootFactor D hD a i : ℂ) •
          pderiv (a,r) (fockTransform D hD q))) =
      ∑ a ∈ S, (rootFactor D hD a i : ℂ) *
        standardPair D (fockTransform D hD p)
          ((r+1 : ℂ) • pderiv (a,r) (fockTransform D hD q)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha,standardPair_add_right,ih]
      congr 1
      rw [smul_comm,standardPair_smul_right]
  exact (hsumr Finset.univ).symm

theorem oscillatorPair_current (D : LatticeData) (hD : (realGram D).PosDef)
    (i : Fin D.rank) (b : Charge D) (n : ℤ) (p q : Oscillator D) :
    oscillatorPair D hD (neutralPolynomialMode D i b n p) q =
      oscillatorPair D hD p (neutralPolynomialMode D i b (-n) q) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change oscillatorPair D hD ((bilinear D (unitCharge D i) b : ℂ) • p) q =
        oscillatorPair D hD p ((bilinear D (unitCharge D i) b : ℂ) • q)
      rw [oscillatorPair_smul_left,oscillatorPair_smul_right]
      simp only [star_intCast]
    | succ r =>
      rw [show (Int.ofNat (r+1)) = (r : ℤ)+1 by simp,
        show -((r : ℤ)+1) = -(r : ℤ)-1 by omega]
      rw [neutralPolynomialMode_positive,neutralPolynomialMode_negative]
      have h := congrArg star (oscillatorPair_X_mul D hD i r q p)
      simpa only [oscillatorPair_hermitian, LinearMap.smul_apply,
        LinearMap.mulLeft_apply] using h.symm
  | negSucc r =>
    rw [show (Int.negSucc r) = -(r : ℤ)-1 by omega,
      show -(-(r : ℤ)-1) = (r : ℤ)+1 by omega]
    rw [neutralPolynomialMode_negative,neutralPolynomialMode_positive]
    exact oscillatorPair_X_mul D hD i r p q

/-- All modes, all finite states, arbitrary ordinary finite rank (including zero). -/
theorem actual_current_adjoint (D : LatticeData) (hD : (realGram D).PosDef)
    (i : Fin D.rank) (n : ℤ) :
    AdjPair D hD (neutralMode D i n) (neutralMode D i (-n)) := by
  intro u v
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add,latticePair_add_left,hu,hw]
  | single a p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,latticePair_add_right,hv,hw]
    | single b q =>
      simp only [neutralMode_single,latticePair_single_single]
      by_cases h : a = b
      · subst b
        simpa using oscillatorPair_current D hD i a n p q
      · simp [h]

end
end D5.S3.VertexAlgebra.LatticeHermitian
