/- GID: D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.claim; result=D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.result; claim=D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.claim
   digest: Complete pseudo-Pick pairs need not have positive kernel quotient. -/

/-
Luo, McCullough and Tsikalas, arXiv:2607.25088v2, Question 9.3, page 45.
The counterexample has three points, with coordinates 1/10, 1 and 2.
For result:
proof_shape: bind-only.
escape_witness: none.
admission_basis: open-problem-resolution (#25502; Refuted).
Direct frozen dependencies: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The source predicates retain their stated expressions; row flattening uses Function.uncurry, retractions use Function.update, and compression uses Matrix.kronecker.

Per-declaration classification (all escape_witness values are none):
pickMatrix: proof_shape: bind-only.
consumers: CompletePseudoPick, pick_gram_decomposition, source_relations, pick_submatrix,
data_consistent, full_data_constant, datum_contractive, retracted_multiplier.
Direct frozen dependencies: none.
IsContractiveMultiplier: proof_shape: bind-only.
consumers: CompletePseudoPick, constant_multiplier, retracted_multiplier.
Direct frozen dependencies: none.
CompletePseudoPick: proof_shape: bind-only.
consumers: claim, conditional_refutation, counterfamily_complete.
Direct frozen dependencies: none.
claim: proof_shape: bind-only.
consumers: conditional_refutation, result.
Direct frozen dependencies: none.
coreX: proof_shape: bind-only.
consumers: k0, ell0, coreX_star, k0_decomposition, ell0_decomposition, ell0_pos,
k0_nonvanishing, quotient_entries, retractQuotient_factor_0, retractQuotient_factor_1,
retractQuotient_factor_2, pick_gram_decomposition, source_relations, data_consistent,
full_data_constant, datum_contractive.
Direct frozen dependencies: none.
k0: proof_shape: bind-only.
consumers: k0_decomposition, k0_pos, k0_nonvanishing, quotient_entries, quotient_form,
quotient_not_pos, conditional_refutation, retractQuotient, retractQuotient_factor_0,
retractQuotient_factor_1, retractQuotient_factor_2, pick_gram_decomposition, source_relations,
pick_submatrix, data_consistent, full_data_constant, datum_contractive, retracted_multiplier,
counterfamily_complete.
Direct frozen dependencies: none.
ell0: proof_shape: bind-only.
consumers: ell0_decomposition, ell0_pos, quotient_entries, quotient_form, quotient_not_pos,
conditional_refutation, retractQuotient, retractQuotient_factor_0, retractQuotient_factor_1,
retractQuotient_factor_2, constant_multiplier, retracted_multiplier, counterfamily_complete.
Direct frozen dependencies: none.
coreX_star: proof_shape: bind-only.
consumers: k0_decomposition, pick_gram_decomposition.
Direct frozen dependencies: none.
k0_decomposition: proof_shape: bind-only.
consumers: k0_pos.
Direct frozen dependencies: none.
k0_pos: proof_shape: bind-only.
consumers: conditional_refutation.
Direct frozen dependencies: none.
ell0_decomposition: proof_shape: bind-only.
consumers: ell0_pos.
Direct frozen dependencies: none.
ell0_pos: proof_shape: bind-only.
consumers: conditional_refutation, constant_multiplier.
Direct frozen dependencies: none.
k0_nonvanishing: proof_shape: bind-only.
consumers: conditional_refutation, datum_contractive, retracted_multiplier.
Direct frozen dependencies: none.
quotient_entries: proof_shape: bind-only.
consumers: quotient_form.
Direct frozen dependencies: none.
quotient_form: proof_shape: bind-only.
consumers: quotient_not_pos.
Direct frozen dependencies: none.
quotient_not_pos: proof_shape: bind-only.
consumers: conditional_refutation.
Direct frozen dependencies: none.
conditional_refutation: proof_shape: bind-only.
consumers: result.
Direct frozen dependencies: none.
retractQuotient: proof_shape: bind-only.
consumers: retractQuotient_factor_0, retractQuotient_pos_0, retractQuotient_factor_1,
retractQuotient_pos_1, retractQuotient_factor_2, retractQuotient_pos_2, retractQuotient_pos,
retracted_multiplier.
Direct frozen dependencies: none.
qL0: proof_shape: bind-only.
consumers: retractQuotient_factor_0.
Direct frozen dependencies: none.
qD0: proof_shape: bind-only.
consumers: retractQuotient_factor_0, retractQuotient_pos_0.
Direct frozen dependencies: none.
retractQuotient_factor_0: proof_shape: bind-only.
consumers: retractQuotient_pos_0.
Direct frozen dependencies: none.
retractQuotient_pos_0: proof_shape: bind-only.
consumers: retractQuotient_pos.
Direct frozen dependencies: none.
qL1: proof_shape: bind-only.
consumers: retractQuotient_factor_1.
Direct frozen dependencies: none.
qD1: proof_shape: bind-only.
consumers: retractQuotient_factor_1, retractQuotient_pos_1.
Direct frozen dependencies: none.
retractQuotient_factor_1: proof_shape: bind-only.
consumers: retractQuotient_pos_1.
Direct frozen dependencies: none.
retractQuotient_pos_1: proof_shape: bind-only.
consumers: retractQuotient_pos.
Direct frozen dependencies: none.
qL2: proof_shape: bind-only.
consumers: retractQuotient_factor_2.
Direct frozen dependencies: none.
qD2: proof_shape: bind-only.
consumers: retractQuotient_factor_2, retractQuotient_pos_2.
Direct frozen dependencies: none.
retractQuotient_factor_2: proof_shape: bind-only.
consumers: retractQuotient_pos_2.
Direct frozen dependencies: none.
retractQuotient_pos_2: proof_shape: bind-only.
consumers: retractQuotient_pos.
Direct frozen dependencies: none.
retractQuotient_pos: proof_shape: bind-only.
consumers: retracted_multiplier.
Direct frozen dependencies: none.
negative_gram_sum_zero: proof_shape: bind-only.
consumers: gram_compression_zero.
Direct frozen dependencies: none.
gram_compression_zero: proof_shape: bind-only.
consumers: source_relations.
Direct frozen dependencies: none.
dataRows_gram: proof_shape: bind-only.
consumers: weightedRows_gram, pick_gram_decomposition.
Direct frozen dependencies: none.
weightedRows_gram: proof_shape: bind-only.
consumers: pick_gram_decomposition.
Direct frozen dependencies: none.
compression_dataRows: proof_shape: bind-only.
consumers: compression_weightedRows, source_relations.
Direct frozen dependencies: none.
compression_weightedRows: proof_shape: bind-only.
consumers: source_relations.
Direct frozen dependencies: none.
pick_gram_decomposition: proof_shape: bind-only.
consumers: source_relations.
Direct frozen dependencies: none.
source_relations: proof_shape: bind-only.
consumers: data_consistent, full_data_constant.
Direct frozen dependencies: none.
pick_submatrix: proof_shape: bind-only.
consumers: data_consistent, counterfamily_complete.
Direct frozen dependencies: none.
data_consistent: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
full_data_constant: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
datum_contractive: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
constant_multiplier: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
retract_ne: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
retract_fixed: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
retracted_multiplier: proof_shape: bind-only.
consumers: counterfamily_complete.
Direct frozen dependencies: none.
counterfamily_complete: proof_shape: bind-only.
consumers: result.
Direct frozen dependencies: none.
result: proof_shape: bind-only.
consumers: none.
Direct frozen dependencies: none.
-/


import Mathlib.Analysis.Matrix.Order

/-! Binding conventions for Luo, McCullough and Tsikalas, Question 9.3.
Matrix.PosSemidef is the existing Mathlib owner for Hermitian kernels with nonnegative
quadratic forms on every finitely supported vector, including kernels on infinite sets.
The multiplier predicate uses the source's Section 3 norm characterization at C = 1:
the kernel (I - Phi(a) Phi(b)*) ell(a,b) is positive semidefinite.
This is the same-space contractive multiplier, not a multiplier from H_k to H_ell.
The source uses k both for a kernel and for matrix size; m denotes matrix size here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder

namespace D5.S3.HilbertOperators.ReproducingKernels.CompletePseudoPickQuotientRefutation

/-- The full n by n block matrix in Definition 9.2, with each block m by m. -/
def pickMatrix {X : Type} (k : Matrix X X ℂ) {n m : ℕ}
    (z : Fin n → X) (W : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun p q => ((1 - W p.1 * (W q.1).conjTranspose) p.2 q.2) * k (z p.1) (z q.1)

/-- Section 3's norm characterization for a multiplier on H_ell tensor C^m at norm at most 1. -/
def IsContractiveMultiplier {X : Type} (ell : Matrix X X ℂ) (m : ℕ)
    (Phi : X → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Matrix.PosSemidef (fun p q : X × Fin m =>
    ((1 - Phi p.1 * (Phi q.1).conjTranspose) p.2 q.2) * ell p.1 q.1)

/-- Definition 9.2: every finite matrix Pick datum for k extends on H_ell tensor C^m. -/
def CompletePseudoPick {X : Type} (k ell : Matrix X X ℂ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (m : ℕ), 0 < m →
    ∀ (z : Fin n → X) (W : Fin n → Matrix (Fin m) (Fin m) ℂ),
      (pickMatrix k z W).PosSemidef →
      ∃ Phi : X → Matrix (Fin m) (Fin m) ℂ,
        IsContractiveMultiplier ell m Phi ∧ ∀ i : Fin n, Phi (z i) = W i

/-- Question 9.3, with the non-vanishing denominator hypothesis stated for every pair. -/
def claim : Prop :=
  ∀ (X : Type) (k ell : Matrix X X ℂ),
    k.PosSemidef → ell.PosSemidef →
    (∀ (x y : X), k x y ≠ 0) → CompletePseudoPick k ell →
    Matrix.PosSemidef (fun x y : X => ell x y / k x y)

private noncomputable def coreX : Fin 3 → ℂ := ![1/10, 1, 2]
private noncomputable def k0 : Matrix (Fin 3) (Fin 3) ℂ := fun i j => 1 + coreX i * coreX j
private noncomputable def ell0 : Matrix (Fin 3) (Fin 3) ℂ := fun i j => 1 + if i = j then (coreX i)^2 else 0

private lemma coreX_star (i : Fin 3) : star (coreX i) = coreX i := by
  fin_cases i <;> norm_num [coreX, Complex.le_def]

private lemma k0_decomposition : k0 = Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ))
    (star (fun _ : Fin 3 => (1 : ℂ))) + Matrix.vecMulVec coreX (star coreX) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_one, one_mul,
    coreX_star, k0]

private theorem k0_pos : k0.PosSemidef := by
  rw [k0_decomposition]
  exact (Matrix.posSemidef_vecMulVec_self_star _).add
    (Matrix.posSemidef_vecMulVec_self_star _)

private lemma ell0_decomposition : ell0 = Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ))
    (star (fun _ : Fin 3 => (1 : ℂ))) + Matrix.diagonal (fun i => (coreX i)^2) := by
  ext i j
  simp only [ell0, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_one,
    one_mul, Matrix.diagonal_apply]

private theorem ell0_pos : ell0.PosSemidef := by
  rw [ell0_decomposition]
  apply (Matrix.posSemidef_vecMulVec_self_star _).add
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [coreX, Complex.le_def]

private theorem k0_nonvanishing : ∀ x y : Fin 3, k0 x y ≠ 0 := by
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [k0, coreX]

private lemma quotient_entries : (fun i j : Fin 3 => ell0 i j / k0 i j) =
    !![1, 10/11, 5/6; 10/11, 1, 1/3; 5/6, 1/3, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ell0, k0, coreX]

private lemma quotient_form : star (![-2, 1, 1] : Fin 3 → ℂ) ⬝ᵥ
    ((fun i j : Fin 3 => ell0 i j / k0 i j) *ᵥ ![-2, 1, 1]) = -(10/33 : ℂ) := by
  rw [quotient_entries]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_ofNat]

private theorem quotient_not_pos : ¬ Matrix.PosSemidef (fun i j : Fin 3 => ell0 i j / k0 i j) := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (![-2, 1, 1] : Fin 3 → ℂ)
  rw [quotient_form] at hn
  norm_num [Complex.le_def] at hn

private theorem conditional_refutation (hcp : CompletePseudoPick k0 ell0) : ¬ claim := by
  intro hc
  exact quotient_not_pos (hc (Fin 3) k0 ell0 k0_pos ell0_pos k0_nonvanishing hcp)


private noncomputable def retractQuotient (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ell0 i j / k0 ((Function.update id a (if a = 0 then 1 else 0) i)) ((Function.update id a (if a = 0 then 1 else 0) j))

private noncomputable def qL0 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (100/101), 1, 0; (200/303), (1/153), 1]
private noncomputable def qD0 : Fin 3 → ℂ := ![(101/200), (51/101), (358/459)]

private lemma retractQuotient_factor_0 : retractQuotient 0 =
    qL0 * Matrix.diagonal qD0 * qL0.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [retractQuotient, Function.update, ell0, k0, coreX, qL0, qD0,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, map_ofNat]

private lemma retractQuotient_pos_0 : (retractQuotient 0).PosSemidef := by
  rw [retractQuotient_factor_0]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [qD0, Complex.le_def]

private noncomputable def qL1 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (100/101), 1, 0; (5/6), (101/12240), 1]
private noncomputable def qD1 : Fin 3 → ℂ := ![1, (10200/10201), (4487/14688)]

private lemma retractQuotient_factor_1 : retractQuotient 1 =
    qL1 * Matrix.diagonal qD1 * qL1.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [retractQuotient, Function.update, ell0, k0, coreX, qL1, qD1,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, map_ofNat]

private lemma retractQuotient_pos_1 : (retractQuotient 1).PosSemidef := by
  rw [retractQuotient_factor_1]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [qD1, Complex.le_def]

private noncomputable def qL2 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (10/11), 1, 0; (100/101), (110/2121), 1]
private noncomputable def qD2 : Fin 3 → ℂ := ![1, (21/121), (850400/214221)]

private lemma retractQuotient_factor_2 : retractQuotient 2 =
    qL2 * Matrix.diagonal qD2 * qL2.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [retractQuotient, Function.update, ell0, k0, coreX, qL2, qD2,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, map_ofNat]

private lemma retractQuotient_pos_2 : (retractQuotient 2).PosSemidef := by
  rw [retractQuotient_factor_2]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [qD2, Complex.le_def]

private lemma retractQuotient_pos (a : Fin 3) : (retractQuotient a).PosSemidef := by
  fin_cases a
  · exact retractQuotient_pos_0
  · exact retractQuotient_pos_1
  · exact retractQuotient_pos_2


open scoped MatrixOrder
open Matrix

private lemma negative_gram_sum_zero {n m : ℕ} (A B : Matrix (Fin n) (Fin m) ℂ)
    (h : (-(A * Aᴴ + B * Bᴴ)).PosSemidef) : A = 0 ∧ B = 0 := by
  have hA : 0 ≤ A * Aᴴ := (Matrix.posSemidef_self_mul_conjTranspose A).nonneg
  have hB : 0 ≤ B * Bᴴ := (Matrix.posSemidef_self_mul_conjTranspose B).nonneg
  have hs : A * Aᴴ + B * Bᴴ ≤ 0 := by
    change (0 - (A * Aᴴ + B * Bᴴ)).PosSemidef
    simpa only [zero_sub] using h
  have hAz : A * Aᴴ = 0 := le_antisymm ((le_add_of_nonneg_right hB).trans hs) hA
  have hBz : B * Bᴴ = 0 := le_antisymm ((le_add_of_nonneg_left hA).trans hs) hB
  exact ⟨Matrix.self_mul_conjTranspose_eq_zero.mp hAz,
    Matrix.self_mul_conjTranspose_eq_zero.mp hBz⟩

private lemma gram_compression_zero {N : Type} [Fintype N] {m r : ℕ}
    (E F A B : Matrix N (Fin m) ℂ) (C : Matrix (Fin r) N ℂ)
    (h : (E * Eᴴ + F * Fᴴ - (A * Aᴴ + B * Bᴴ)).PosSemidef)
    (hE : C * E = 0) (hF : C * F = 0) : C * A = 0 ∧ C * B = 0 := by
  have hc := h.mul_mul_conjTranspose_same C
  have heq : C * (E * Eᴴ + F * Fᴴ - (A * Aᴴ + B * Bᴴ)) * Cᴴ =
      -((C * A) * (C * A)ᴴ + (C * B) * (C * B)ᴴ) := by
    have hconj (X : Matrix N (Fin m) ℂ) :
        C * (X * Xᴴ) * Cᴴ = (C * X) * (C * X)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      hconj, hE, hF, Matrix.conjTranspose_zero, Matrix.mul_zero,
      zero_add, zero_sub]
  rw [heq] at hc
  exact negative_gram_sum_zero _ _ hc

private lemma dataRows_gram {n m : ℕ} (W : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) :
    ((Matrix.of (Function.uncurry W)) * ((Matrix.of (Function.uncurry W)))ᴴ) p q = (W p.1 * (W q.1)ᴴ) p.2 q.2 :=
  Complex.ext rfl rfl

private lemma weightedRows_gram {n m : ℕ} (x : Fin n → ℂ)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) (p q : Fin n × Fin m) :
    ((Matrix.of (Function.uncurry (fun i => x i • W i))) * ((Matrix.of (Function.uncurry (fun i => x i • W i))))ᴴ) p q =
      x p.1 * star (x q.1) * (W p.1 * (W q.1)ᴴ) p.2 q.2 := by
  rw [dataRows_gram]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul]
  ring

private lemma compression_dataRows {n m : ℕ} (t : Fin n → ℂ)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    ((Matrix.kronecker (Matrix.replicateRow (Fin 1) t) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (fun a => (0, a)) id) * (Matrix.of (Function.uncurry W)) = ∑ i, t i • W i := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.kronecker_apply, Matrix.replicateRow, Matrix.of_apply, Function.uncurry, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ c : Fin m, t i * (1 : Matrix (Fin m) (Fin m) ℂ) a c * W i c b) =
    t i * W i a b
  simp only [mul_assoc, ← Finset.mul_sum]
  change t i * ((1 : Matrix (Fin m) (Fin m) ℂ) * W i) a b = _
  rw [Matrix.one_mul]

private lemma compression_weightedRows {n m : ℕ} (t x : Fin n → ℂ)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    ((Matrix.kronecker (Matrix.replicateRow (Fin 1) t) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (fun a => (0, a)) id) * (Matrix.of (Function.uncurry (fun i => x i • W i))) = ∑ i, (t i * x i) • W i := by
  rw [compression_dataRows]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]

private lemma pick_gram_decomposition {n m : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    pickMatrix k0 z W =
      (Matrix.of (Function.uncurry (fun _ : Fin n => (1 : Matrix (Fin m) (Fin m) ℂ)))) *
        ((Matrix.of (Function.uncurry (fun _ : Fin n => (1 : Matrix (Fin m) (Fin m) ℂ)))))ᴴ +
      (Matrix.of (Function.uncurry (fun i : Fin n => coreX (z i) • (1 : Matrix (Fin m) (Fin m) ℂ)))) *
        ((Matrix.of (Function.uncurry (fun i : Fin n => coreX (z i) • (1 : Matrix (Fin m) (Fin m) ℂ)))))ᴴ -
      ((Matrix.of (Function.uncurry W)) * ((Matrix.of (Function.uncurry W)))ᴴ +
        (Matrix.of (Function.uncurry (fun i => coreX (z i) • W i))) * ((Matrix.of (Function.uncurry (fun i => coreX (z i) • W i))))ᴴ) := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, weightedRows_gram]
  simp only [dataRows_gram, Matrix.sub_apply,
    Matrix.conjTranspose_one, Matrix.one_mul, coreX_star, pickMatrix, k0]
  ring

private lemma source_relations {n m : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) (t : Fin n → ℂ)
    (ht : ∑ i, t i = 0) (htx : ∑ i, t i * coreX (z i) = 0)
    (hp : (pickMatrix k0 z W).PosSemidef) :
    (∑ i, t i • W i) = 0 ∧ (∑ i, (t i * coreX (z i)) • W i) = 0 := by
  rw [pick_gram_decomposition] at hp
  have hE : ((Matrix.kronecker (Matrix.replicateRow (Fin 1) t) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (fun a => (0, a)) id) *
      (Matrix.of (Function.uncurry (fun _ : Fin n => (1 : Matrix (Fin m) (Fin m) ℂ)))) = 0 := by
    rw [compression_dataRows, ← Finset.sum_smul, ht, zero_smul]
  have hF : ((Matrix.kronecker (Matrix.replicateRow (Fin 1) t) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (fun a => (0, a)) id) *
      (Matrix.of (Function.uncurry (fun i : Fin n => coreX (z i) • (1 : Matrix (Fin m) (Fin m) ℂ)))) = 0 := by
    rw [compression_weightedRows, ← Finset.sum_smul, htx, zero_smul]
  have h := gram_compression_zero _ _ _ _ (((Matrix.kronecker (Matrix.replicateRow (Fin 1) t) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (fun a => (0, a)) id)) hp hE hF
  simpa only [compression_dataRows, smul_smul] using h

private lemma pick_submatrix {n m r : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ) (e : Fin r → Fin n)
    (hp : (pickMatrix k0 z W).PosSemidef) :
    (pickMatrix k0 (z ∘ e) (W ∘ e)).PosSemidef := by
  exact hp.submatrix (fun p : Fin r × Fin m => (e p.1, p.2))

private lemma data_consistent {n m : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hp : (pickMatrix k0 z W).PosSemidef) (i j : Fin n) (hz : z i = z j) : W i = W j := by
  let e : Fin 2 → Fin n := ![i, j]
  have hp2 := pick_submatrix z W e hp
  have h0 : ∑ a : Fin 2, (![1, -1] : Fin 2 → ℂ) a = 0 := by
    norm_num [Fin.sum_univ_succ]
  have hx : ∑ a : Fin 2, (![1, -1] : Fin 2 → ℂ) a * coreX ((z ∘ e) a) = 0 := by
    norm_num [Fin.sum_univ_succ, e, hz]
  have hr := (source_relations _ _ ![1, -1] h0 hx hp2).1
  have hrel : W i - W j = 0 := by
    simpa [Fin.sum_univ_succ, e, sub_eq_add_neg] using hr
  exact sub_eq_zero.mp hrel

private lemma full_data_constant {m : ℕ} (W : Fin 3 → Matrix (Fin m) (Fin m) ℂ)
    (hp : (pickMatrix k0 id W).PosSemidef) : ∀ i, W i = W 0 := by
  let t : Fin 3 → ℂ := ![-1, 19/10, -9/10]
  have h0 : ∑ i, t i = 0 := by norm_num [t, Fin.sum_univ_succ]
  have hx : ∑ i, t i * coreX (id i) = 0 := by
    norm_num [t, coreX, Fin.sum_univ_succ]
  obtain ⟨hA, hB⟩ := source_relations id W t h0 hx hp
  intro i
  fin_cases i
  · rfl
  · ext a b
    change W 1 a b = W 0 a b
    have ha := congr_fun (congr_fun hA a) b
    have hb := congr_fun (congr_fun hB a) b
    norm_num [Fin.sum_univ_succ, t, coreX, Matrix.smul_apply] at ha hb
    linear_combination (20/19 : ℂ) * ha - (10/19 : ℂ) * hb
  · ext a b
    change W 2 a b = W 0 a b
    have ha := congr_fun (congr_fun hA a) b
    have hb := congr_fun (congr_fun hB a) b
    norm_num [Fin.sum_univ_succ, t, coreX, Matrix.smul_apply] at ha hb
    linear_combination (10/171 : ℂ) * ha - (100/171 : ℂ) * hb +
      (20/19 : ℂ) * ha - (10/19 : ℂ) * hb

private lemma datum_contractive {n m : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hp : (pickMatrix k0 z W).PosSemidef) (i : Fin n) :
    (1 - W i * (W i)ᴴ).PosSemidef := by
  have hd : 0 ≤ (k0 (z i) (z i))⁻¹ := by
    generalize z i = a
    fin_cases a <;> norm_num [k0, coreX, Complex.le_def]
  have hs := (hp.submatrix (fun a : Fin m => (i, a))).smul hd
  convert hs using 1
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, pickMatrix]
  field_simp [k0_nonvanishing]

private lemma constant_multiplier {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : (1 - U * Uᴴ).PosSemidef) :
    IsContractiveMultiplier ell0 m (fun _ => U) := by
  have heq : (fun p q : Fin 3 × Fin m => (1 - U * Uᴴ) p.2 q.2 * ell0 p.1 q.1) =
      Matrix.kronecker ell0 (1 - U * Uᴴ) := by
    funext p q
    exact mul_comm _ _
  unfold IsContractiveMultiplier
  rw [heq]
  exact ell0_pos.kronecker hU

private lemma retract_ne (a x : Fin 3) : (Function.update id a (if a = 0 then 1 else 0) x) ≠ a := by
  fin_cases a <;> fin_cases x <;> norm_num [Function.update]

private lemma retract_fixed (a x : Fin 3) (hx : x ≠ a) : (Function.update id a (if a = 0 then 1 else 0) x) = x := by
  simp [hx]

private lemma retracted_multiplier {n m : ℕ} (z : Fin n → Fin 3)
    (W : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hp : (pickMatrix k0 z W).PosSemidef) (a : Fin 3) (e : Fin 3 → Fin n)
    (he : ∀ x, z (e x) = (Function.update id a (if a = 0 then 1 else 0) x)) :
    IsContractiveMultiplier ell0 m (fun x => W (e x)) := by
  have hP := hp.submatrix (fun p : Fin 3 × Fin m => (e p.1, p.2))
  have hQ := (retractQuotient_pos a).submatrix (fun p : Fin 3 × Fin m => p.1)
  have heq : (fun p q : Fin 3 × Fin m =>
      (1 - W (e p.1) * (W (e q.1))ᴴ) p.2 q.2 * ell0 p.1 q.1) =
      ((pickMatrix k0 z W).submatrix (fun p : Fin 3 × Fin m => (e p.1, p.2))
        (fun p : Fin 3 × Fin m => (e p.1, p.2))) ⊙
      (retractQuotient a).submatrix (fun p : Fin 3 × Fin m => p.1)
        (fun p : Fin 3 × Fin m => p.1) := by
    ext p q
    simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, pickMatrix,
      retractQuotient, he]
    field_simp [k0_nonvanishing]
  unfold IsContractiveMultiplier
  rw [heq]
  exact hP.hadamard hQ

private theorem counterfamily_complete : CompletePseudoPick k0 ell0 := by
  classical
  intro n hn m hm z W hp
  let i0 : Fin n := ⟨0, hn⟩
  by_cases hconst : ∀ i, z i = z i0
  · refine ⟨fun _ => W i0, constant_multiplier _ (datum_contractive z W hp i0), ?_⟩
    intro i
    exact data_consistent z W hp i0 i (hconst i).symm
  by_cases hsurj : Function.Surjective z
  · choose e he using hsurj
    have hp3 := pick_submatrix z W e hp
    have hze : z ∘ e = id := funext he
    rw [hze] at hp3
    have hr := full_data_constant (W ∘ e) hp3
    refine ⟨fun _ => W (e 0), constant_multiplier _ (datum_contractive z W hp (e 0)), ?_⟩
    intro i
    calc
      W (e 0) = W (e (z i)) := (hr (z i)).symm
      _ = W i := data_consistent z W hp _ _ (he (z i))
  · obtain ⟨a, ha⟩ : ∃ a : Fin 3, ∀ i, z i ≠ a := by
      simpa only [Function.Surjective, not_forall, not_exists] using hsurj
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ z i0 := not_forall.mp hconst
    have hcovered : ∀ x : Fin 3, x ≠ a → ∃ i, z i = x := by
      intro x hx
      by_contra hc
      have h0 : z i0 ≠ x := fun h => hc ⟨i0, h⟩
      have h1 : z j ≠ x := fun h => hc ⟨j, h⟩
      have h2 := ha i0
      have h3 := ha j
      omega
    choose e he using (fun x => hcovered ((Function.update id a (if a = 0 then 1 else 0) x)) (retract_ne a x))
    refine ⟨fun x => W (e x), retracted_multiplier z W hp a e he, ?_⟩
    intro i
    apply data_consistent z W hp
    rw [he, retract_fixed a (z i) (ha i)]

theorem result : ¬ claim := conditional_refutation counterfamily_complete


end D5.S3.HilbertOperators.ReproducingKernels.CompletePseudoPickQuotientRefutation
