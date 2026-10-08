/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian replica integrals define genuine multi-entropy and its squeezing conjecture. -/

import D5.S3.Quantum.Entanglement.GaussianReplicaReduction
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix Kronecker

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic

open GaussianReplicaReduction

/-- The real off-diagonal entry of the fully symmetric state. All subtractions
in the source formula are in ℝ, including those involving the mode count. -/
def eMinus (a : ℝ) (N : ℕ) : ℝ :=
  ((a ^ 2 - 1) * ((N : ℝ) - 2) -
      Real.sqrt (a ^ 2 - 1) *
        Real.sqrt ((a ^ 2 - 1) * (N : ℝ) ^ 2 + 4 * ((N : ℝ) - 1))) /
    (2 * a * ((N : ℝ) - 1))

/-- The fully symmetric matrix on a finite coordinate index. The physical
mode count is N; in applications it is the cardinality of the index. -/
def symmetricMatrix {ι : Type*} [DecidableEq ι] (a : ℝ) (N : ℕ) :
    Matrix ι ι ℝ :=
  fun i j => if i = j then a else eMinus a N

/-- The source matrix W with diagonal a and off-diagonal e⁻. -/
def W (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  symmetricMatrix a N

/-- The density kernel of a pure real Gaussian state with precision M. -/
def gaussianKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (q q' : ι → ℝ) : ℝ :=
  Real.sqrt (Matrix.det (Real.pi⁻¹ • M)) *
    Real.exp (-(q ⬝ᵥ (M *ᵥ q) + q' ⬝ᵥ (M *ᵥ q')) / 2)

/-- A coordinate is a party label together with a local mode label. -/
abbrev Mode (parties : List ℕ) :=
  Σ k : Fin parties.length, Fin (parties.get k)

/-- The fully symmetric state in party coordinates. -/
def partyMatrix (a : ℝ) (parties : List ℕ) :
    Matrix (Mode parties) (Mode parties) ℝ :=
  symmetricMatrix a parties.sum

/-- The primed coordinate of party k in replica i is the unprimed
coordinate of replica g_k(i), with the same local mode label. -/
def primed {R : Type*} (parties : List ℕ)
    (g : Fin parties.length → Equiv.Perm R)
    (x : R → Mode parties → ℝ) (i : R) : Mode parties → ℝ :=
  fun p => x (g p.1 i) p

/-- The twisted replica contraction as a real Lebesgue integral. -/
def Z {R : Type*} [Fintype R] (parties : List ℕ)
    (M : Matrix (Mode parties) (Mode parties) ℝ)
    (g : Fin parties.length → Equiv.Perm R) : ℝ :=
  ∫ x : R → Mode parties → ℝ,
    ∏ i : R, gaussianKernel M (x i) (primed parties g x i)

/-- The replica torus for three parties. -/
abbrev Replica3 (n : ℕ) := Fin n × Fin n

/-- Increment the first coordinate: consecutive cycles in the source. -/
def g_A (n : ℕ) : Equiv.Perm (Replica3 n) :=
  Equiv.prodCongr (finRotate n) (Equiv.refl (Fin n))

/-- Increment the second coordinate: cycles with source stride n. -/
def g_B (n : ℕ) : Equiv.Perm (Replica3 n) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (finRotate n)

/-- The third party has no twist. -/
def g_C (n : ℕ) : Equiv.Perm (Replica3 n) := Equiv.refl _

def twists3 (n : ℕ) : Fin 3 → Equiv.Perm (Replica3 n) :=
  fun k => if k = 0 then g_A n else if k = 1 then g_B n else g_C n

/-- The tripartite replica integral has n² copies. -/
def Z3 (n NA NB NC : ℕ) (a : ℝ) : ℝ :=
  Z [NA, NB, NC] (partyMatrix a [NA, NB, NC]) (twists3 n)

/-- For two parties the first is cycled and the second is untwisted. -/
def twists2 (n : ℕ) : Fin 2 → Equiv.Perm (Fin n) :=
  fun k => if k = 0 then finRotate n else Equiv.refl _

def Z2 (n NL NR : ℕ) (a : ℝ) : ℝ :=
  Z [NL, NR] (partyMatrix a [NL, NR]) (twists2 n)

/-- Sₙ⁽³⁾ includes the factor 1/n and the n²-th power of Z₁. -/
def S3 (n NA NB NC : ℕ) (a : ℝ) : ℝ :=
  (1 / (1 - (n : ℝ))) * (1 / (n : ℝ)) *
    Real.log (Z3 n NA NB NC a / (Z3 1 NA NB NC a) ^ (n ^ 2))

/-- Sₙ⁽²⁾ includes the n-th power of Z₁. -/
def S2 (n NL NR : ℕ) (a : ℝ) : ℝ :=
  (1 / (1 - (n : ℝ))) * Real.log (Z2 n NL NR a / (Z2 1 NL NR a) ^ n)

/-- Genuine tripartite multi-entropy subtracts half the three bipartite entropies. -/
def GM3 (n NA NB NC : ℕ) (a : ℝ) : ℝ :=
  S3 n NA NB NC a -
    (1 / 2) * (S2 n (NA + NB) NC a + S2 n (NB + NC) NA a +
      S2 n (NC + NA) NB a)

example (a : ℝ) : ℝ := GM3 2 1 1 1 a

/-- The orthogonal projection onto the constant coordinates. -/
def uniformProjection {ι : Type*} [Fintype ι] : Matrix ι ι ℝ :=
  fun _ _ => (Fintype.card ι : ℝ)⁻¹

/-- The constant-mode projection in party coordinates. -/
def P (parties : List ℕ) : Matrix (Mode parties) (Mode parties) ℝ :=
  uniformProjection

/-- The coordinate permutation giving the primed replica variables. -/
def replicaPermutation {R : Type*} (parties : List ℕ)
    (g : Fin parties.length → Equiv.Perm R) : Equiv.Perm (R × Mode parties) where
  toFun z := (g z.2.1 z.1, z.2)
  invFun z := ((g z.2.1).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The precision matrix of the flattened replica Gaussian. -/
def replicaPrecision {R ι : Type*} [Fintype R] [DecidableEq R]
    (M : Matrix ι ι ℝ) (e : Equiv.Perm (R × ι)) : Matrix (R × ι) (R × ι) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix R R ℝ) ⊗ₖ M +
    ((1 : Matrix R R ℝ) ⊗ₖ M).submatrix e.symm e.symm)

/-- The mean of the untwisted and twisted constant-mode projections. -/
def T {R : Type*} [Fintype R] [DecidableEq R] (parties : List ℕ)
    (g : Fin parties.length → Equiv.Perm R) :
    Matrix (R × Mode parties) (R × Mode parties) ℝ :=
  replicaPrecision (P parties) (replicaPermutation parties g)

/-- The normalized replica precision matrix. -/
def H {R : Type*} [Fintype R] [DecidableEq R] (parties : List ℕ)
    (g : Fin parties.length → Equiv.Perm R) (ε : ℝ) :
    Matrix (R × Mode parties) (R × Mode parties) ℝ :=
  1 - (1 - ε) • T parties g

lemma mode_card (parties : List ℕ) : Fintype.card (Mode parties) = parties.sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← List.sum_ofFn, List.ofFn_get]

lemma quadratic_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι ℝ) (e : κ ≃ ι) (x : κ → ℝ) :
    x ⬝ᵥ (M.submatrix e e *ᵥ x) =
      (x ∘ e.symm) ⬝ᵥ (M *ᵥ (x ∘ e.symm)) := by
  rw [Matrix.submatrix_mulVec_equiv]
  exact (comp_equiv_symm_dotProduct x (M *ᵥ (x ∘ e.symm)) e).symm

lemma integral_gaussian_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    (∫ x : ι → ℝ, Real.exp (-(x ⬝ᵥ (M *ᵥ x)))) =
      Real.pi ^ ((Fintype.card ι : ℝ) / 2) / Real.sqrt M.det := by
  let e := (Fintype.equivFin ι).symm
  have hi := GaussianReplicaReduction.integral_exp_neg_quadraticForm_pi
    (M.submatrix e e) (hM.submatrix e.injective)
  rw [Matrix.det_submatrix_equiv_self] at hi
  rw [← (volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id volume)).integral_comp'
    (fun x => Real.exp (-(x ⬝ᵥ (M *ᵥ x))))]
  simpa [quadratic_reindex, MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
    Equiv.arrowCongr, Function.comp_def] using hi

lemma uniform_projection_quadratic {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    x ⬝ᵥ ((uniformProjection : Matrix ι ι ℝ) *ᵥ x) =
      (∑ i, x i) ^ 2 / (Fintype.card ι : ℝ) := by
  simp only [uniformProjection, Matrix.mulVec, dotProduct]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma uniform_precision_pos_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 - (1 - ε) • (uniformProjection : Matrix ι ι ℝ)).PosDef := by
  have hP : (uniformProjection : Matrix ι ι ℝ).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, uniformProjection]
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(Matrix.PosDef.one (n := ι) (R := ℝ)).isHermitian.sub
    (hP.smul (by simp [IsSelfAdjoint])), ?_⟩
  intro x hx
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, uniform_projection_quadratic]
  have hp : 0 < x ⬝ᵥ x := by simpa using (dotProduct_self_star_pos_iff.mpr hx)
  have hc : 0 < (Fintype.card ι : ℝ) := by
    have hne : Nonempty ι := by
      by_contra hn
      have : IsEmpty ι := not_nonempty_iff.mp hn
      exact hx (Subsingleton.elim _ _)
    exact_mod_cast Fintype.card_pos
  have hb : (∑ i, x i) ^ 2 / (Fintype.card ι : ℝ) ≤ x ⬝ᵥ x := by
    apply (div_le_iff₀ hc).mpr
    simpa [dotProduct, pow_two, mul_comm] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
  have hm := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hε1)
  nlinarith

lemma uniform_precision_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (ε : ℝ) :
    (1 - (1 - ε) • (uniformProjection : Matrix ι ι ℝ)).det = ε := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hι.ne'
  have hm : (1 - (1 - ε) • (uniformProjection : Matrix ι ι ℝ)) =
      1 + Matrix.replicateCol Unit (fun _ : ι => -(1 - ε) / (Fintype.card ι : ℝ)) *
        Matrix.replicateRow Unit (fun _ : ι => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply, uniformProjection, sub_eq_add_neg, div_eq_mul_inv]
    ring
  rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hc]
  ring

lemma replica_precision_pos_def {R ι : Type*} [Fintype R] [DecidableEq R]
    [Finite ι] (M : Matrix ι ι ℝ) (hM : M.PosDef)
    (e : Equiv.Perm (R × ι)) : (replicaPrecision M e).PosDef := by
  have hB := (Matrix.PosDef.one (n := R) (R := ℝ)).kronecker hM
  exact (hB.add (hB.submatrix e.symm.injective)).smul (by norm_num)

lemma quadratic_kronecker {R ι : Type*} [Fintype R] [DecidableEq R]
    [Fintype ι] (M : Matrix ι ι ℝ) (x : R × ι → ℝ) :
    x ⬝ᵥ (((1 : Matrix R R ℝ) ⊗ₖ M) *ᵥ x) =
      ∑ i : R, (fun p => x (i,p)) ⬝ᵥ (M *ᵥ (fun p => x (i,p))) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.mul_sum]

lemma replica_precision_quadratic {R : Type*} [Fintype R] [DecidableEq R]
    (parties : List ℕ) (M : Matrix (Mode parties) (Mode parties) ℝ)
    (g : Fin parties.length → Equiv.Perm R) (x : R × Mode parties → ℝ) :
    x ⬝ᵥ (replicaPrecision M (replicaPermutation parties g) *ᵥ x) =
      (∑ i : R, (Function.curry x i) ⬝ᵥ (M *ᵥ (Function.curry x i)) +
        ∑ i : R, (primed parties g (Function.curry x) i) ⬝ᵥ
          (M *ᵥ (primed parties g (Function.curry x) i))) / 2 := by
  unfold replicaPrecision
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec,
    dotProduct_smul, dotProduct_add, smul_eq_mul, quadratic_reindex,
    quadratic_kronecker, Equiv.symm_symm]
  unfold primed Function.curry
  simp only [Function.comp_def, replicaPermutation, Equiv.coe_fn_mk]
  ring

lemma replica_integral_determinant_formula {R : Type*} [Fintype R] [DecidableEq R]
    (parties : List ℕ) (M : Matrix (Mode parties) (Mode parties) ℝ) (hM : M.PosDef)
    (g : Fin parties.length → Equiv.Perm R) :
    Z parties M g = Real.sqrt (M.det ^ Fintype.card R /
      (replicaPrecision M (replicaPermutation parties g)).det) := by
  let Q := replicaPrecision M (replicaPermutation parties g)
  have hQ : Q.PosDef := replica_precision_pos_def M hM _
  have hf : ∀ x : R → Mode parties → ℝ,
      (∏ i : R, gaussianKernel M (x i) (primed parties g x i)) =
        Real.sqrt (Matrix.det (Real.pi⁻¹ • M)) ^ Fintype.card R *
          Real.exp (-(Function.uncurry x ⬝ᵥ (Q *ᵥ Function.uncurry x))) := by
    intro x
    simp only [gaussianKernel, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [replica_precision_quadratic]
    rw [← Finset.sum_div]
    simp only [Function.curry_uncurry, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    ring
  have ht := GaussianReplicaReduction.measurePreserving_curry_symm
    R (Mode parties) ℝ
  have hflat := ht.integral_comp' (fun x : R × Mode parties → ℝ =>
    Real.exp (-(x ⬝ᵥ (Q *ᵥ x))))
  simp only [MeasurableEquiv.coe_curry_symm] at hflat
  rw [Z, integral_congr_ae (Filter.Eventually.of_forall hf), integral_const_mul,
    hflat, integral_gaussian_matrix Q hQ]
  have hd : 0 < Matrix.det (Real.pi⁻¹ • M) :=
    (hM.smul (inv_pos.mpr Real.pi_pos)).det_pos
  have hc : (Real.sqrt (Matrix.det (Real.pi⁻¹ • M)) ^ Fintype.card R) ^ 2 =
      ((Real.pi⁻¹) ^ Fintype.card (Mode parties) * M.det) ^ Fintype.card R := by
    rw [← pow_mul, Nat.mul_comm (Fintype.card R) 2, pow_mul,
      Real.sq_sqrt hd.le, Matrix.det_smul]
  have hpi : (Real.pi ^ ((Fintype.card (R × Mode parties) : ℝ) / 2)) ^ 2 =
      Real.pi ^ Fintype.card (R × Mode parties) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul Real.pi_nonneg]
    norm_num only [Nat.cast_ofNat]
    rw [show ((Fintype.card (R × Mode parties) : ℝ) / 2) * (2 : ℝ) =
      (Fintype.card (R × Mode parties) : ℝ) by ring, Real.rpow_natCast]
  have hp : 0 ≤ Real.sqrt (Matrix.det (Real.pi⁻¹ • M)) ^ Fintype.card R *
      (Real.pi ^ ((Fintype.card (R × Mode parties) : ℝ) / 2) / Real.sqrt Q.det) := by
    positivity
  apply (sq_eq_sq₀ hp (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg (pow_nonneg hM.det_pos.le _) hQ.det_pos.le),
    mul_pow, div_pow, hc, hpi, Real.sq_sqrt hQ.det_pos.le]
  simp only [Fintype.card_prod, mul_pow, inv_pow, ← pow_mul, Nat.mul_comm]
  field_simp [Real.pi_ne_zero, hQ.det_pos.ne']

lemma replica_precision_projection {R ι : Type*} [Fintype R] [DecidableEq R]
    [Fintype ι] [DecidableEq ι] (α ε : ℝ) (e : Equiv.Perm (R × ι)) :
    replicaPrecision (α • (1 - (1 - ε) • (uniformProjection : Matrix ι ι ℝ))) e =
      α • (1 - (1 - ε) • replicaPrecision (uniformProjection : Matrix ι ι ℝ) e) := by
  have hb : (1 : Matrix R R ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) = 1 :=
    Matrix.one_kronecker_one
  have he : (1 : Matrix (R × ι) (R × ι) ℝ).submatrix e.symm e.symm = 1 := by
    simp
  have hm : (1 : Matrix R R ℝ) ⊗ₖ
      (α • (1 - (1 - ε) • (uniformProjection : Matrix ι ι ℝ))) =
      α • (1 - (1 - ε) • ((1 : Matrix R R ℝ) ⊗ₖ uniformProjection)) := by
    ext ⟨r,p⟩ ⟨s,q⟩
    have hi := congrFun (congrFun hb (r,p)) (s,q)
    simp only [Matrix.kronecker_apply] at hi
    simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    rw [← hi]
    ring
  unfold replicaPrecision
  rw [hm]
  ext i j
  have hei := congrFun (congrFun he i) j
  simp only [Matrix.submatrix_apply] at hei
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.submatrix_apply]
  rw [hei]
  ring

theorem replica_integral_projection_formula {R : Type*} [Fintype R] [DecidableEq R]
    (parties : List ℕ) (hN : 0 < parties.sum)
    (g : Fin parties.length → Equiv.Perm R) (α ε : ℝ)
    (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Z parties (α • (1 - (1 - ε) • P parties)) g =
      Real.sqrt (ε ^ Fintype.card R / (H parties g ε).det) := by
  have hM := (uniform_precision_pos_def (ι := Mode parties) ε hε hε1).smul hα
  change Z parties (α • (1 - (1 - ε) •
    (uniformProjection : Matrix (Mode parties) (Mode parties) ℝ))) g = _
  rw [replica_integral_determinant_formula _ _ hM]
  change Real.sqrt ((α • (1 - (1 - ε) • (uniformProjection :
    Matrix (Mode parties) (Mode parties) ℝ))).det ^ Fintype.card R /
      (replicaPrecision (α • (1 - (1 - ε) • uniformProjection))
        (replicaPermutation parties g)).det) = _
  rw [replica_precision_projection, Matrix.det_smul,
    uniform_precision_det (by simpa [mode_card] using hN), Matrix.det_smul]
  change Real.sqrt ((α ^ Fintype.card (Mode parties) * ε) ^ Fintype.card R /
    (α ^ Fintype.card (R × Mode parties) * (H parties g ε).det)) = _
  congr 1
  rw [mul_pow, ← pow_mul, Fintype.card_prod, Nat.mul_comm (Fintype.card R)]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ hα.ne')]

/-- The off-diagonal entry is nonpositive, and the constant-mode eigenvalue is positive. -/
lemma eMinus_bounds (a : ℝ) (N : ℕ) (ha : 1 ≤ a) (hN : 3 ≤ N) :
    eMinus a N ≤ 0 ∧ 0 < a + ((N : ℝ) - 1) * eMinus a N := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha0 : 0 < a := by linarith
  let n : ℝ := N
  let t : ℝ := a ^ 2 - 1
  let s : ℝ := Real.sqrt t * Real.sqrt (t * n ^ 2 + 4 * (n - 1))
  have ht : 0 ≤ t := by dsimp [t]; nlinarith
  have hn1 : 0 < n - 1 := by dsimp [n]; linarith
  have hn2 : 0 ≤ n - 2 := by dsimp [n]; linarith
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hr : 0 ≤ t * n ^ 2 + 4 * (n - 1) := by positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = t * (t * n ^ 2 + 4 * (n - 1)) := by
    dsimp [s]
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hr]
  have hlo : t * (n - 2) ≤ s := by
    apply (sq_le_sq₀ (mul_nonneg ht hn2) hs).mp
    have hid : s ^ 2 - (t * (n - 2)) ^ 2 = 4 * t * (n - 1) * (t + 1) := by
      rw [hs2]; ring
    have hp : 0 ≤ 4 * t * (n - 1) * (t + 1) := by positivity
    linarith
  have hhi : s < 2 + t * n := by
    apply (sq_lt_sq₀ hs (by positivity : 0 ≤ 2 + t * n)).mp
    have hid : (2 + t * n) ^ 2 - s ^ 2 = 4 * (t + 1) := by rw [hs2]; ring
    linarith
  have hden : 0 < 2 * a * (n - 1) := by positivity
  change (t * (n - 2) - s) / (2 * a * (n - 1)) ≤ 0 ∧
    0 < a + (n - 1) * ((t * (n - 2) - s) / (2 * a * (n - 1)))
  refine ⟨div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlo) hden.le, ?_⟩
  have hid : a + (n - 1) * ((t * (n - 2) - s) / (2 * a * (n - 1))) =
      (2 + t * n - s) / (2 * a) := by
    field_simp [ha0.ne', hn1.ne']
    dsimp [t]
    ring
  rw [hid]
  exact div_pos (sub_pos.mpr hhi) (by positivity)

/-- The physical scale and small eigenvalue parameter lie in their required ranges. -/
lemma symmetric_parameters (a : ℝ) (N : ℕ) (ha : 1 ≤ a) (hN : 3 ≤ N) :
    0 < a - eMinus a N ∧
      0 < (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N) ∧
      (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N) ≤ 1 := by
  obtain ⟨he, hlambda⟩ := eMinus_bounds a N ha hN
  have hα : 0 < a - eMinus a N := by linarith
  refine ⟨hα, div_pos hlambda hα, (div_le_one hα).mpr ?_⟩
  have hn : 0 ≤ (N : ℝ) := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hn he]

lemma W_projection_formula (a : ℝ) (N : ℕ) (hN : 0 < N)
    (hα : a - eMinus a N ≠ 0) :
    W a N = (a - eMinus a N) •
      (1 - (1 - (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)) •
        (uniformProjection : Matrix (Fin N) (Fin N) ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  ext i j
  by_cases hij : i = j
  · simp [W, symmetricMatrix, uniformProjection, hij]
    field_simp [hα, hn]
    ring
  · simp [W, symmetricMatrix, uniformProjection, hij]
    field_simp [hα, hn]
    ring

lemma partyMatrix_projection_formula (a : ℝ) (parties : List ℕ)
    (hN : 0 < parties.sum) (hα : a - eMinus a parties.sum ≠ 0) :
    partyMatrix a parties = (a - eMinus a parties.sum) •
      (1 - (1 - (a + ((parties.sum : ℝ) - 1) * eMinus a parties.sum) /
        (a - eMinus a parties.sum)) • P parties) := by
  let e : Mode parties ≃ Fin parties.sum :=
    (Fintype.equivFin (Mode parties)).trans (finCongr (mode_card parties))
  have hw := W_projection_formula a parties.sum hN hα
  ext i j
  have hi := congrFun (congrFun hw (e i)) (e j)
  simpa [W, partyMatrix, symmetricMatrix, uniformProjection, P, mode_card,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply] using hi

theorem replica_integral_symmetric_formula {R : Type*} [Fintype R] [DecidableEq R]
    (parties : List ℕ) (hN : 3 ≤ parties.sum)
    (g : Fin parties.length → Equiv.Perm R) (a : ℝ) (ha : 1 ≤ a) :
    Z parties (partyMatrix a parties) g = Real.sqrt
      (((a + ((parties.sum : ℝ) - 1) * eMinus a parties.sum) /
        (a - eMinus a parties.sum)) ^ Fintype.card R /
        (H parties g ((a + ((parties.sum : ℝ) - 1) * eMinus a parties.sum) /
          (a - eMinus a parties.sum))).det) := by
  obtain ⟨hα, hε, hε1⟩ := symmetric_parameters a parties.sum ha hN
  rw [partyMatrix_projection_formula a parties (by omega) hα.ne']
  exact replica_integral_projection_formula parties (by omega) g _ _ hα hε hε1

/-- A single replica contracts to the trace of the normalized Gaussian state. -/
lemma replica_integral_singleton {R : Type*} [Fintype R] [Unique R]
    (parties : List ℕ) (M : Matrix (Mode parties) (Mode parties) ℝ) (hM : M.PosDef)
    (g : Fin parties.length → Equiv.Perm R) : Z parties M g = 1 := by
  classical
  have he : replicaPermutation parties g = Equiv.refl (R × Mode parties) := by
    apply Equiv.ext
    intro ⟨i,p⟩
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hq : replicaPrecision M (replicaPermutation parties g) =
      (1 : Matrix R R ℝ) ⊗ₖ M := by
    rw [he]
    ext i j
    unfold replicaPrecision; simp [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [replica_integral_determinant_formula parties M hM g, hq, Matrix.det_kronecker]
  simp [hM.det_pos.ne']

/-- The replica precision determinant reduces to the weighted twist overlap on replicas. -/
theorem replica_determinant_reduction {R : Type*} [Fintype R] [DecidableEq R]
    (parties : List ℕ) (hN : 0 < parties.sum)
    (g : Fin parties.length → Equiv.Perm R) (ε : ℝ) (hε : 0 < ε) :
    let Q : Matrix R R ℝ := Matrix.of fun r s => ∑ p : Mode parties,
      if r = g p.1 s then (parties.sum : ℝ)⁻¹ else 0
    (H parties g ε).det =
      (((1 + ε) / 2) ^ 2 • (1 : Matrix R R ℝ) -
        ((1 - ε) / 2) ^ 2 • (Qᵀ * Q)).det := by
  dsimp only
  let c : ℝ := (Real.sqrt (parties.sum : ℝ))⁻¹
  let e := replicaPermutation parties g
  let V₀ : Matrix (R × Mode parties) R ℝ := fun z r => if z.1 = r then c else 0
  let V₁ := V₀.submatrix e.symm id
  have hn : (parties.sum : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : c * c = (parties.sum : ℝ)⁻¹ := by
    dsimp only [c]
    rw [← _root_.mul_inv_rev, ← pow_two, Real.sq_sqrt (by positivity)]
  have h₀ : V₀ᵀ * V₀ = 1 := by
    ext r s
    change (∑ z : R × Mode parties, (if z.1 = r then c else 0) *
      (if z.1 = s then c else 0)) = if r = s then 1 else 0
    rw [Fintype.sum_prod_type]
    by_cases hrs : r = s
    · subst s
      simp [hc]
      simpa only [Nat.cast_list_sum] using mul_inv_cancel₀ hn
    · simp only [hrs, if_false]
      apply Finset.sum_eq_zero
      intro t _
      by_cases ht : t = r
      · subst t; simp [hrs]
      · simp [ht]
  have h₁ : V₁ᵀ * V₁ = 1 := by
    rw [show V₁ᵀ = V₀ᵀ.submatrix id e.symm from rfl,
      Matrix.submatrix_mul_equiv, h₀, Matrix.submatrix_id_id]
  have hp₀ : V₀ * V₀ᵀ = (1 : Matrix R R ℝ) ⊗ₖ P parties := by
    ext ⟨r,p⟩ ⟨s,q⟩
    change (∑ t : R, (if r = t then c else 0) * (if s = t then c else 0)) =
      (if r = s then 1 else 0) * (Fintype.card (Mode parties) : ℝ)⁻¹
    by_cases hrs : r = s
    · subst s
      simp [hc]
    · simp only [hrs, if_false, zero_mul]
      apply Finset.sum_eq_zero
      intro t _
      by_cases ht : r = t
      · subst t; simp [Ne.symm hrs]
      · simp [ht]
  have hp₁ : V₁ * V₁ᵀ =
      ((1 : Matrix R R ℝ) ⊗ₖ P parties).submatrix e.symm e.symm := by
    change V₀.submatrix e.symm (Equiv.refl R) *
      V₀ᵀ.submatrix (Equiv.refl R) e.symm = _
    rw [Matrix.submatrix_mul_equiv, hp₀]
  have hq : V₀ᵀ * V₁ = Matrix.of (fun r s => ∑ p : Mode parties,
      if r = g p.1 s then (parties.sum : ℝ)⁻¹ else 0) := by
    ext r s
    change (∑ z : R × Mode parties, (if z.1 = r then c else 0) *
      (if (g z.2.1).symm z.1 = s then c else 0)) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Equiv.symm_apply_eq, mul_ite, ite_mul, mul_zero, zero_mul]
    simp [hc, eq_comm]
  have hh : H parties g ε = 1 - ((1 - ε) / 2) • (V₀ * V₀ᵀ + V₁ * V₁ᵀ) := by
    rw [hp₀, hp₁]
    unfold H T replicaPrecision
    simp only [smul_smul]
    congr 2
    ring
  rw [hh, GaussianReplicaReduction.paired_projection_determinant V₀ V₁ h₀ h₁ _ (by linarith), hq]
  congr 2
  congr 1
  ring

/-- The exact entropy expression in the normalized replica determinants. -/
def determinantGM3 (n NA NB NC : ℕ) (a : ℝ) : ℝ :=
  let N := NA + NB + NC
  let ε := (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)
  (1 / (1 - (n : ℝ))) * (1 / (n : ℝ)) *
    Real.log (Real.sqrt (ε ^ (n ^ 2) / (H [NA, NB, NC] (twists3 n) ε).det)) -
  (1 / 2) * ((1 / (1 - (n : ℝ))) *
    Real.log (Real.sqrt (ε ^ n / (H [NA + NB, NC] (twists2 n) ε).det)) +
    (1 / (1 - (n : ℝ))) *
    Real.log (Real.sqrt (ε ^ n / (H [NB + NC, NA] (twists2 n) ε).det)) +
    (1 / (1 - (n : ℝ))) *
    Real.log (Real.sqrt (ε ^ n / (H [NC + NA, NB] (twists2 n) ε).det)))

/-- The entropy combination is expressed solely through the replica determinants. -/
theorem multi_entropy_determinant_formula (n NA NB NC : ℕ) (a : ℝ)
    (ha : 1 ≤ a) (hNA : 0 < NA) (hNB : 0 < NB) (hNC : 0 < NC) :
    GM3 n NA NB NC a = determinantGM3 n NA NB NC a := by
  unfold determinantGM3
  let N := NA + NB + NC
  let ε := (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)
  have hN : 3 ≤ N := by dsimp [N]; omega
  have hp (ps : List ℕ) (hs : ps.sum = N) : (partyMatrix a ps).PosDef := by
    have hn : 3 ≤ ps.sum := by omega
    obtain ⟨hα, hε, hε1⟩ := symmetric_parameters a ps.sum ha hn
    rw [partyMatrix_projection_formula a ps (by omega) hα.ne']
    exact (uniform_precision_pos_def _ hε hε1).smul hα
  have hs3 : [NA, NB, NC].sum = N := by simp [N, add_assoc]
  have hn3 : Z3 1 NA NB NC a = 1 := by
    let : Unique (Replica3 1) :=
      { default := (0,0), uniq := fun x => Subsingleton.elim _ _ }
    exact replica_integral_singleton [NA, NB, NC] _ (hp _ hs3) (twists3 1)
  have hn2 (u v : ℕ) (hs : u + v = N) : Z2 1 u v a = 1 :=
    replica_integral_singleton [u, v] _ (hp _ (by simpa using hs)) (twists2 1)
  have hz3 : Z3 n NA NB NC a =
      Real.sqrt (ε ^ (n ^ 2) / (H [NA, NB, NC] (twists3 n) ε).det) := by
    simpa [Z3, ε, hs3, Fintype.card_prod, pow_two] using
      replica_integral_symmetric_formula [NA, NB, NC] (by omega) (twists3 n) a ha
  have hz2 (u v : ℕ) (hs : u + v = N) : Z2 n u v a =
      Real.sqrt (ε ^ n / (H [u, v] (twists2 n) ε).det) := by
    simpa [Z2, ε, hs] using replica_integral_symmetric_formula [u, v]
      (by simpa using (show 3 ≤ u + v by omega)) (twists2 n) a ha
  have hsAB : NA + NB + NC = N := rfl
  have hsBC : NB + NC + NA = N := by dsimp [N]; omega
  have hsCA : NC + NA + NB = N := by dsimp [N]; omega
  simp only [GM3, S3, S2, hn3, hn2 _ _ hsAB, hn2 _ _ hsBC, hn2 _ _ hsCA,
    one_pow, div_one, hz3, hz2 _ _ hsAB, hz2 _ _ hsBC, hz2 _ _ hsCA]
  rfl

set_option maxHeartbeats 2000000 in
-- Reindexing the torus compares all sixteen entries of a symbolic matrix.
/-- At replica order two, the three bipartite determinants multiply to epsilon squared
 times the tripartite determinant. -/
theorem replica_two_determinant_identity (NA NB NC : ℕ)
    (hN : 0 < NA + NB + NC) (ε : ℝ) (hε : 0 < ε) :
    (H [NA + NB, NC] (twists2 2) ε).det *
      (H [NB + NC, NA] (twists2 2) ε).det *
      (H [NC + NA, NB] (twists2 2) ε).det =
      ε ^ 2 * (H [NA, NB, NC] (twists3 2) ε).det := by
  let N := NA + NB + NC
  let x := (NA : ℝ) / N
  let y := (NB : ℝ) / N
  let z := (NC : ℝ) / N
  let a := ((1 + ε) / 2) ^ 2
  let b := ((1 - ε) / 2) ^ 2
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![z, x + y; x + y, z]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![x, y + z; y + z, x]
  let C : Matrix (Fin 2) (Fin 2) ℝ := !![y, z + x; z + x, y]
  let Q : Matrix (Fin 4) (Fin 4) ℝ :=
    !![z, y, x, 0; y, z, 0, x; x, 0, z, y; 0, x, y, z]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : x + y + z = 1 := by
    dsimp only [x, y, z]
    rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add]
    exact div_self hn
  have hab : a - b = ε := by dsimp only [a,b]; ring
  have hq2 (u v : ℕ) :
      (Matrix.of fun r s => ∑ p : Mode [u,v],
        if r = twists2 2 p.1 s then ((u + v : ℕ) : ℝ)⁻¹ else 0) =
        (!![(v : ℝ) / (u + v), (u : ℝ) / (u + v);
          (u : ℝ) / (u + v), (v : ℝ) / (u + v)] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Mode, Fintype.sum_sigma, Fin.sum_univ_succ, twists2, finRotate_apply,
        div_eq_mul_inv, Nat.cast_add]
  have h2 (u v : ℕ) (huv : u + v = N) :
      (H [u,v] (twists2 2) ε).det =
        (a • 1 - b • ((!![(v : ℝ) / N, (u : ℝ) / N;
          (u : ℝ) / N, (v : ℝ) / N] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
          !![(v : ℝ) / N, (u : ℝ) / N; (u : ℝ) / N, (v : ℝ) / N])).det := by
    rw [replica_determinant_reduction [u,v] (by simp; omega) (twists2 2) ε hε]
    simp only [List.sum_cons, List.sum_nil, add_zero, hq2]
    dsimp only [a,b]
    rw [← huv, Nat.cast_add]
  have hAB : (H [NA + NB, NC] (twists2 2) ε).det = (a • 1 - b • (Aᵀ * A)).det := by
    simpa only [A, x, y, z, Nat.cast_add, add_div] using h2 (NA+NB) NC rfl
  have hBC : (H [NB + NC, NA] (twists2 2) ε).det = (a • 1 - b • (Bᵀ * B)).det := by
    simpa only [B, x, y, z, Nat.cast_add, add_div] using h2 (NB+NC) NA (by dsimp [N]; omega)
  have hCA : (H [NC + NA, NB] (twists2 2) ε).det = (a • 1 - b • (Cᵀ * C)).det := by
    simpa only [C, x, y, z, Nat.cast_add, add_div] using h2 (NC+NA) NB (by dsimp [N]; omega)
  let q : Matrix (Replica3 2) (Replica3 2) ℝ := Matrix.of fun r s =>
    ∑ p : Mode [NA,NB,NC], if r = twists3 2 p.1 s then (N : ℝ)⁻¹ else 0
  let e : Replica3 2 ≃ Fin 4 := finProdFinEquiv
  have hq3 : q.submatrix e.symm e.symm = Q := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [q, Q, e, Matrix.submatrix, finProdFinEquiv, Mode, Fintype.sum_sigma,
        Fin.sum_univ_succ, twists3, g_A, g_B, g_C, finRotate_apply, x,y,z, div_eq_mul_inv]
        <;> norm_num [Fin.divNat, Fin.modNat, Fin.add_def]
  have h3 : (H [NA,NB,NC] (twists3 2) ε).det = (a • 1 - b • (Qᵀ * Q)).det := by
    have hs : [NA,NB,NC].sum = N := by simp [N, add_assoc]
    have hr := replica_determinant_reduction [NA,NB,NC] (by simp; omega) (twists3 2) ε hε
    rw [hs] at hr
    change (H [NA,NB,NC] (twists3 2) ε).det = (a • 1 - b • (qᵀ * q)).det at hr
    rw [hr, ← Matrix.det_submatrix_equiv_self e.symm]
    congr 1
    change a • (1 : Matrix (Replica3 2) (Replica3 2) ℝ).submatrix e.symm e.symm -
      b • (qᵀ * q).submatrix e.symm e.symm = _
    rw [Matrix.submatrix_one_equiv, ← Matrix.submatrix_mul_equiv qᵀ q e.symm e.symm e.symm]
    rw [show qᵀ.submatrix e.symm e.symm = (q.submatrix e.symm e.symm)ᵀ from rfl, hq3]
  rw [hAB, hBC, hCA, h3, ← hab]
  exact GaussianReplicaReduction.binary_replica_determinant_identity x y z a b hsum
/-- The determinant entropy expression vanishes at replica order two. -/
theorem determinantGM3_two_eq_zero (NA NB NC : ℕ) (a : ℝ) (ha : 1 ≤ a)
    (hNA : 0 < NA) (hNB : 0 < NB) (hNC : 0 < NC) :
    determinantGM3 2 NA NB NC a = 0 := by
  let N := NA + NB + NC
  let ε := (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)
  obtain ⟨hα, he, he1⟩ := symmetric_parameters a N ha (by dsimp [N]; omega)
  have hp {R : Type} [Fintype R] [DecidableEq R] (ps : List ℕ)
      (g : Fin ps.length → Equiv.Perm R) : 0 < (H ps g ε).det := by
    have hm := replica_precision_pos_def
      ((1 : ℝ) • (1 - (1 - ε) • (uniformProjection : Matrix (Mode ps) (Mode ps) ℝ)))
      ((uniform_precision_pos_def ε he he1).smul (by norm_num)) (replicaPermutation ps g)
    rw [replica_precision_projection] at hm
    unfold replicaPrecision at hm; simp only [one_smul] at hm
    exact hm.det_pos
  have h3 := hp [NA,NB,NC] (twists3 2)
  have hAB := hp [NA+NB,NC] (twists2 2)
  have hBC := hp [NB+NC,NA] (twists2 2)
  have hCA := hp [NC+NA,NB] (twists2 2)
  have hid := replica_two_determinant_identity NA NB NC (by omega) ε he
  have hlog := congrArg Real.log hid
  rw [Real.log_mul (mul_pos hAB hBC).ne' hCA.ne', Real.log_mul hAB.ne' hBC.ne',
    Real.log_mul (pow_pos he 2).ne' h3.ne', Real.log_pow] at hlog
  dsimp only [determinantGM3]
  change (1 / (1 - (2 : ℝ))) * (1 / (2 : ℝ)) *
      Real.log (Real.sqrt (ε ^ (2 ^ 2) / (H [NA,NB,NC] (twists3 2) ε).det)) -
    (1 / 2) * ((1 / (1 - (2 : ℝ))) *
      Real.log (Real.sqrt (ε ^ 2 / (H [NA+NB,NC] (twists2 2) ε).det)) +
      (1 / (1 - (2 : ℝ))) *
      Real.log (Real.sqrt (ε ^ 2 / (H [NB+NC,NA] (twists2 2) ε).det)) +
      (1 / (1 - (2 : ℝ))) *
      Real.log (Real.sqrt (ε ^ 2 / (H [NC+NA,NB] (twists2 2) ε).det))) = 0
  rw [Real.log_sqrt (div_nonneg (pow_nonneg he.le _) h3.le),
    Real.log_sqrt (div_nonneg (pow_nonneg he.le _) hAB.le),
    Real.log_sqrt (div_nonneg (pow_nonneg he.le _) hBC.le),
    Real.log_sqrt (div_nonneg (pow_nonneg he.le _) hCA.le),
    Real.log_div (pow_pos he _).ne' h3.ne',
    Real.log_div (pow_pos he _).ne' hAB.ne',
    Real.log_div (pow_pos he _).ne' hBC.ne',
    Real.log_div (pow_pos he _).ne' hCA.ne']
  simp only [Real.log_pow]
  norm_num only [Nat.cast_ofNat] at *
  linarith

/-- The large-squeezing conjecture for every replica order and positive tripartition. -/
def claim : Prop :=
  ∀ (n NA NB NC : ℕ), 2 ≤ n → 0 < NA → 0 < NB → 0 < NC →
    Asymptotics.IsEquivalent Filter.atTop (GM3 n NA NB NC)
      (fun a : ℝ => ((2 - (n : ℝ)) / (2 * (n : ℝ))) * Real.log a)

theorem result : claim := by
  intro n NA NB NC hn hNA hNB hNC
  have heq : GM3 n NA NB NC =ᶠ[Filter.atTop] determinantGM3 n NA NB NC := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with a ha
    exact multi_entropy_determinant_formula n NA NB NC a ha hNA hNB hNC
  have hdet : Asymptotics.IsEquivalent Filter.atTop (determinantGM3 n NA NB NC)
      (fun a : ℝ => ((2 - (n : ℝ)) / (2 * (n : ℝ))) * Real.log a) := by
    by_cases htwo : n = 2
    · subst n
      have hz : determinantGM3 2 NA NB NC =ᶠ[Filter.atTop] 0 := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with a ha
        exact determinantGM3_two_eq_zero NA NB NC a ha hNA hNB hNC
      norm_num only [Nat.cast_ofNat, sub_self, zero_div, zero_mul]
      exact Asymptotics.isEquivalent_zero_iff_eventually_zero.mpr hz
    · let N := NA + NB + NC
      let ε (a : ℝ) := (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)
      let Q₃ : Matrix (Replica3 n) (Replica3 n) ℝ := Matrix.of fun r s =>
        ∑ p : Mode [NA, NB, NC], if r = twists3 n p.1 s then (N : ℝ)⁻¹ else 0
      let Q₂ (u v : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun r s =>
        ∑ p : Mode [u, v], if r = twists2 n p.1 s then ((u + v : ℕ) : ℝ)⁻¹ else 0
      let D₃ (e : ℝ) :=
        (((1 + e) / 2) ^ 2 • (1 : Matrix (Replica3 n) (Replica3 n) ℝ) -
          ((1 - e) / 2) ^ 2 • (Q₃ᵀ * Q₃)).det
      let D₂ (u v : ℕ) (e : ℝ) :=
        (((1 + e) / 2) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 - e) / 2) ^ 2 • ((Q₂ u v)ᵀ * Q₂ u v)).det
      have hred : determinantGM3 n NA NB NC =ᶠ[Filter.atTop] (fun a =>
          (1 / (1 - (n : ℝ))) * (1 / (n : ℝ)) *
            Real.log (Real.sqrt (ε a ^ (n ^ 2) / D₃ (ε a))) -
          (1 / 2) * ((1 / (1 - (n : ℝ))) *
            Real.log (Real.sqrt (ε a ^ n / D₂ (NA + NB) NC (ε a))) +
            (1 / (1 - (n : ℝ))) *
            Real.log (Real.sqrt (ε a ^ n / D₂ (NB + NC) NA (ε a))) +
            (1 / (1 - (n : ℝ))) *
            Real.log (Real.sqrt (ε a ^ n / D₂ (NC + NA) NB (ε a))))) := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with a ha
        have hN : 3 ≤ N := by dsimp only [N]; omega
        have he : 0 < ε a := (symmetric_parameters a N ha hN).2.1
        have h3 := replica_determinant_reduction [NA, NB, NC]
          (by simp; omega) (twists3 n) (ε a) he
        have h2 (u v : ℕ) (huv : u + v = N) :=
          replica_determinant_reduction [u, v] (by simp; omega) (twists2 n) (ε a) he
        have hs3 : [NA, NB, NC].sum = N := by simp [N, add_assoc]
        rw [hs3] at h3
        dsimp only [determinantGM3]
        rw [show (H [NA, NB, NC] (twists3 n) (ε a)).det = D₃ (ε a) from h3]
        rw [show (H [NA + NB, NC] (twists2 n) (ε a)).det =
          D₂ (NA + NB) NC (ε a) from h2 _ _ rfl]
        rw [show (H [NB + NC, NA] (twists2 n) (ε a)).det =
          D₂ (NB + NC) NA (ε a) from h2 _ _ (by dsimp only [N]; omega)]
        rw [show (H [NC + NA, NB] (twists2 n) (ε a)).det =
          D₂ (NC + NA) NB (ε a) from h2 _ _ (by dsimp only [N]; omega)]
      have hNreal : 2 < (N : ℝ) := by
        dsimp only [N]; exact_mod_cast (show 2 < NA + NB + NC by omega)
      have hscale := GaussianReplicaReduction.symmetric_parameter_scaled_limit (N : ℝ) hNreal
      change Filter.Tendsto (fun a => a ^ 2 * ε a) Filter.atTop
        (nhds (((N : ℝ) - 1) / (N : ℝ) ^ 2)) at hscale
      have : NeZero n := ⟨by omega⟩
      let pA : Mode [NA, NB, NC] := ⟨0, ⟨0, by simpa using hNA⟩⟩
      let pB : Mode [NA, NB, NC] := ⟨1, ⟨0, by simpa using hNB⟩⟩
      let pC : Mode [NA, NB, NC] := ⟨2, ⟨0, by simpa using hNC⟩⟩
      have ht3 := torus_twists_transitive n n (fun p : Mode [NA, NB, NC] => twists3 n p.1)
        pA pB (by simp [pA, twists3, g_A]) (by simp [pB, twists3, g_B])
      have hf3 := permutation_average_determinant_factor
        (fun p : Mode [NA, NB, NC] => twists3 n p.1) pC (by norm_num [pC, twists3, g_C]; rfl) ht3
      simp only [mode_card, List.sum_cons, List.sum_nil, add_zero, ← add_assoc] at hf3
      change ∃ F, Continuous F ∧ 0 < F 0 ∧ ∀ e, D₃ e = e * F e at hf3
      have hf2 (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
          ∃ F, Continuous F ∧ 0 < F 0 ∧ ∀ e, D₂ u v e = e * F e := by
        let pL : Mode [u, v] := ⟨0, ⟨0, by simpa using hu⟩⟩
        let pR : Mode [u, v] := ⟨1, ⟨0, by simpa using hv⟩⟩
        have ht := cyclic_twists_transitive n (fun p : Mode [u, v] => twists2 n p.1)
          pL (by simp [pL, twists2])
        have hh := permutation_average_determinant_factor
          (fun p : Mode [u, v] => twists2 n p.1) pR (by simp [pR, twists2]; rfl) ht
        simpa only [mode_card, List.sum_cons, List.sum_nil, add_zero] using hh
      obtain ⟨F₃, hc₃, hp₃, he₃⟩ := hf3
      obtain ⟨FAB, hcAB, hpAB, heAB⟩ := hf2 (NA + NB) NC (by omega) hNC
      obtain ⟨FBC, hcBC, hpBC, heBC⟩ := hf2 (NB + NC) NA (by omega) hNA
      obtain ⟨FCA, hcCA, hpCA, heCA⟩ := hf2 (NC + NA) NB (by omega) hNB
      simp_rw [he₃, heAB, heBC, heCA] at hred
      have hh := replica_entropy_asymptotic n (by omega) ε _
        (div_pos (by linarith) (pow_pos (by linarith) _)) hscale ![F₃, FAB, FBC, FCA]
        (by intro i; fin_cases i <;> assumption)
        (by intro i; fin_cases i <;> assumption)
      exact hh.congr_left hred.symm
  exact hdet.congr_left heq.symm

end D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
