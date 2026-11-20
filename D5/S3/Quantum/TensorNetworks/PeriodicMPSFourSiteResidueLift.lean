/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A characteristic-five coefficient minor for the physical four-site residual system. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSystem
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSample
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! A polynomial coefficient minor with a Gaussian-integer witness. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidueLift

open Matrix MvPolynomial
open PeriodicMPSFourSiteResidualFormula PeriodicMPSFourSiteResidualSystem
open PeriodicMPSFourSiteResidualRank
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

local notation "M₃" => Matrix (Fin 3) (Fin 3) R

private def degrees : Fin 3 → ℕ := ![3, 2, 4]

private def rowLabels : Fin 44 → Fin 3 × ℕ × ℕ :=
  ![
    (0, 5, 0), (1, 6, 0), (0, 4, 1), (0, 4, 0), (1, 5, 1), (0, 3, 2),
    (0, 3, 1), (0, 3, 0), (1, 5, 0), (0, 2, 3), (0, 2, 2), (0, 2, 1),
    (0, 2, 0), (1, 4, 2), (0, 1, 4), (0, 1, 3), (0, 1, 2), (0, 1, 1),
    (0, 1, 0), (1, 4, 1), (0, 0, 5), (0, 0, 4), (0, 0, 3), (0, 0, 2),
    (0, 0, 1), (0, 0, 0), (1, 3, 3), (1, 4, 0), (1, 3, 2), (1, 3, 1),
    (1, 2, 4), (1, 2, 3), (1, 2, 2), (1, 1, 5), (1, 1, 4), (1, 1, 3),
    (1, 0, 6), (1, 0, 5), (1, 0, 4), (2, 4, 0), (2, 3, 0), (2, 3, 1),
    (2, 2, 2), (2, 2, 0)]

private def columnPairs : Fin 44 → Fin 9 × Fin 9 :=
  ![
    (7, 1), (7, 0), (6, 2), (6, 1), (6, 0), (5, 3),
    (5, 2), (5, 1), (5, 0), (4, 4), (4, 3), (4, 2),
    (4, 1), (4, 0), (3, 5), (3, 4), (3, 3), (3, 2),
    (3, 1), (3, 0), (2, 6), (2, 5), (2, 4), (2, 3),
    (2, 2), (2, 1), (2, 0), (1, 7), (1, 6), (1, 5),
    (1, 4), (1, 3), (1, 2), (1, 1), (1, 0), (0, 8),
    (0, 7), (0, 6), (0, 5), (0, 4), (0, 3), (0, 2),
    (0, 1), (0, 0)]

private def columns : Fin 44 → Exponent 8 :=
  fun i => ⟨columnPairs i, (by decide : ∀ i, (columnPairs i).1.val + (columnPairs i).2.val ≤ 8) i⟩

private def multiplierDegree (i : Fin 44) : ℕ := 8 - degrees (rowLabels i).1

private lemma row_in_bounds : ∀ i : Fin 44,
    (rowLabels i).2.1 + (rowLabels i).2.2 ≤ multiplierDegree i := by decide

private def rowExponent (i : Fin 44) : Exponent (multiplierDegree i) :=
  ⟨(⟨(rowLabels i).2.1, by have h := row_in_bounds i; omega⟩,
    ⟨(rowLabels i).2.2, by have h := row_in_bounds i; omega⟩), row_in_bounds i⟩

private noncomputable def rowPolynomial (T U : M₃) (i : Fin 44) : MvPolynomial (Fin 3) R :=
  monomial (rowExponent i).toFinsupp 1 * residualEquations T U (rowLabels i).1

/-- The selected degree-eight coefficient matrix. -/
noncomputable def residualMinor (T U : M₃) : Matrix (Fin 44) (Fin 44) R :=
  coefficientMinor (rowPolynomial T U) columns

/-- Specializing the two input triplets specializes the entire coefficient minor. -/
theorem map_residualMinor {S : Type*} [CommRing S] (f : R →+* S) (T U : M₃) :
    f.mapMatrix (residualMinor T U) = residualMinor (f.mapMatrix T) (f.mapMatrix U) := by
  unfold residualMinor
  rw [map_coefficientMinor]
  congr 1
  funext i
  simp only [rowPolynomial, map_mul, map_monomial, map_one,
    congr_fun (map_residualEquations f T U) (rowLabels i).1]

/-- The three generators and their monomial multiples fill all but at most
one dimension of the degree-eight quotient when the selected minor is nonzero. -/
theorem quotient_finrank_le_of_residualMinor {K : Type*} [Field K]
    (T U : Matrix (Fin 3) (Fin 3) K) (h : (residualMinor T U).det ≠ 0) :
    Module.finrank K (LinearMap.range
      ((Ideal.Quotient.mkₐ K (residualIdeal T U)).toLinearMap.comp
        (homogeneousSubmodule (Fin 3) K 8).subtype)) ≤ 1 := by
  refine quotient_finrank_le_of_minor (residualIdeal T U) (rowPolynomial T U) ?_ ?_ columns h
  · intro i
    have he := residualEquations_degree T U (rowLabels i).1
    change (residualEquations T U (rowLabels i).1).IsHomogeneous (degrees (rowLabels i).1) at he
    have hr : ((rowExponent i).toFinsupp : Fin 3 →₀ ℕ).degree = multiplierDegree i := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
      exact Nat.add_sub_of_le (row_in_bounds i)
    have hom := (isHomogeneous_monomial (1 : K) hr).mul he
    have bound (j : Fin 3) : degrees j ≤ 8 := by fin_cases j <;> decide
    have hi := bound (rowLabels i).1
    simpa only [rowPolynomial, multiplierDegree, Nat.sub_add_cancel hi] using hom
  · intro i
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨(rowLabels i).1, rfl⟩

/-- The six cyclic necklace traces as polynomials in the two tensor matrices. -/
def necklaceTuple (A : Fin 2 → Matrix (Fin 2) (Fin 2) R) : Fin 6 → R :=
  let X := A 0
  let Y := A 1
  ![(X ^ 4).trace, (X ^ 3 * Y).trace, (X ^ 2 * Y ^ 2).trace,
    ((X * Y) ^ 2).trace, (X * Y ^ 3).trace, (Y ^ 4).trace]

/-- The periodic triplet block constructed from the tensor entries. -/
def tensorTriplet (A : Fin 2 → Matrix (Fin 2) (Fin 2) R) : M₃ :=
  let a := necklaceTuple A
  triplet (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

private abbrev F₅ := ZMod 5

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def residue : GaussianInt →+* F₅ := Zsqrtd.lift ⟨2, by decide⟩

private def tensorLeft : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![4, 2; 1, 0], !![1, 3; 3, 2]]

private def tensorRight : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![4, 4; 2, 1], !![3, 2; 4, 3]]

/-- The two reductions of this pair and its conjugate realize the chosen
finite-field sample. The roots of minus one used by the reductions are 2 and −2. -/
def gaussianTensor : Fin 2 → Matrix (Fin 2) (Fin 2) GaussianInt :=
  fun i => Matrix.of fun j k => ⟨3 * (tensorLeft i j k + tensorRight i j k),
    4 * (tensorLeft i j k - tensorRight i j k)⟩

private theorem gaussian_residues :
    (fun i => residue.mapMatrix (gaussianTensor i)) = ![!![4, 2; 1, 0], !![1, 3; 3, 2]] ∧
    (fun i => residue.mapMatrix ((gaussianTensor i).map star)) = ![!![4, 4; 2, 1], !![3, 2; 4, 3]] := by
  decide +kernel

private abbrev sampleLeft : Matrix (Fin 3) (Fin 3) F₅ :=
  triplet 2 3 4 1 2 1

private abbrev sampleRight : Matrix (Fin 3) (Fin 3) F₅ :=
  triplet 2 0 1 3 0 4

private def sampleTerms : Fin 3 → List ((ℕ × ℕ × ℕ) × F₅) :=
  ![ [((2, 1, 0), -2), ((2, 0, 1), 1), ((1, 2, 0), 1), ((0, 3, 0), 2),
      ((0, 2, 1), -2), ((0, 0, 3), -2)],
     [((1, 1, 0), 1), ((1, 0, 1), -2), ((0, 2, 0), -1), ((0, 1, 1), -2)],
     [((3, 1, 0), -1), ((3, 0, 1), 1), ((2, 2, 0), 1), ((2, 1, 1), 1),
      ((1, 3, 0), 2), ((1, 2, 1), -2), ((1, 1, 2), 1), ((1, 0, 3), 2),
      ((0, 3, 1), 2)] ]

private def evaluateTerm (q : Fin 3 → F₅) (term : (ℕ × ℕ × ℕ) × F₅) : F₅ :=
  term.2 * q 0 ^ term.1.1 * q 1 ^ term.1.2.1 * q 2 ^ term.1.2.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The exhaustive check evaluates the three scalar formulas over 125 triples.
private theorem sample_residual_values (q : Fin 3 → F₅) :
    let K := pencil (sampleLeft * sampleRight) q
    ![compatibility sampleLeft sampleRight K, leftConic sampleLeft sampleRight K,
      rightConic sampleLeft sampleRight K.adjugate] =
      fun i => ((sampleTerms i).map (evaluateTerm q)).sum := by
  revert q
  decide +kernel

private noncomputable def toExponent (p : ℕ × ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![p.1, p.2.1, p.2.2]

private lemma exponent_degree (p : ℕ × ℕ × ℕ) :
    (toExponent p).degree = p.1 + p.2.1 + p.2.2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
  rfl

private noncomputable def termPolynomial (t : (ℕ × ℕ × ℕ) × F₅) : MvPolynomial (Fin 3) F₅ :=
  monomial (toExponent t.1) t.2

private noncomputable def samplePolynomial (j : Fin 3) : MvPolynomial (Fin 3) F₅ :=
  ((sampleTerms j).map termPolynomial).sum

private lemma termsDegree (j : Fin 3) :
    ∀ t ∈ sampleTerms j, t.1.1 + t.1.2.1 + t.1.2.2 = degrees j := by
  fin_cases j <;> simp [sampleTerms, degrees]

private lemma termListDegree (l : List ((ℕ × ℕ × ℕ) × F₅)) (n : ℕ)
    (h : ∀ t ∈ l, t.1.1 + t.1.2.1 + t.1.2.2 = n) :
    ((l.map termPolynomial).sum).IsHomogeneous n := by
  induction l with
  | nil => exact isHomogeneous_zero _ _ _
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (isHomogeneous_monomial t.2 ((exponent_degree t.1).trans
      (h t (List.mem_cons_self ..)))).add (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

private lemma eval_termPolynomial (q : Fin 3 → F₅) (t : (ℕ × ℕ × ℕ) × F₅) :
    eval q (termPolynomial t) = evaluateTerm q t := by
  rw [termPolynomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_three]
  change t.2 * (q 0 ^ t.1.1 * q 1 ^ t.1.2.1 * q 2 ^ t.1.2.2) = _
  simp [evaluateTerm, mul_assoc]

private lemma sample_residual_polynomial (i : Fin 3) :
    residualEquations sampleLeft sampleRight i = samplePolynomial i := by
  apply IsHomogeneous.funext_of_le_card (residualEquations_degree _ _ i)
    (termListDegree _ _ (termsDegree i))
  · intro q
    rw [show eval q (residualEquations sampleLeft sampleRight i) =
      ((sampleTerms i).map (evaluateTerm q)).sum from
      congr_fun ((eval_residualEquations sampleLeft sampleRight q).trans
        (sample_residual_values q)) i]
    simp only [samplePolynomial, map_list_sum, List.map_map, Function.comp_def, eval_termPolynomial]
  · rw [Cardinal.mk_fintype, ZMod.card]
    have hi : ![3, 2, 4] i ≤ (5 : ℕ) := by fin_cases i <;> decide
    exact_mod_cast hi

private def addExponents (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

private lemma toExponent_add (a b : ℕ × ℕ × ℕ) :
    toExponent a + toExponent b = toExponent (addExponents a b) := by
  ext i
  fin_cases i <;> rfl

private lemma toExponent_injective : Function.Injective toExponent := by
  intro a b he
  have e (i : Fin 3) := congrArg (fun e : Fin 3 →₀ ℕ => e i) he
  exact Prod.ext (e 0) (Prod.ext (e 1) (e 2))

private def exponentTriple {n : ℕ} (p : Exponent n) : ℕ × ℕ × ℕ :=
  (p.val.1.val, p.val.2.val, n - (p.val.1.val + p.val.2.val))

private lemma term_coeff (a b : ℕ × ℕ × ℕ) (t : (ℕ × ℕ × ℕ) × F₅) :
    (monomial (toExponent a) 1 * termPolynomial t).coeff (toExponent b) =
      if addExponents a t.1 = b then t.2 else 0 := by
  rw [termPolynomial, monomial_mul, one_mul, toExponent_add, coeff_monomial]
  simp only [toExponent_injective.eq_iff, eq_comm]

private def residueEntry (i j : Fin 44) : F₅ :=
  ((sampleTerms (rowLabels j).1).map fun t =>
    if addExponents (exponentTriple (rowExponent j)) t.1 = exponentTriple (columns i)
    then t.2 else 0).sum

private lemma residue_entry (i j : Fin 44) :
    residualMinor sampleLeft sampleRight i j = residueEntry i j := by
  change (rowPolynomial sampleLeft sampleRight j).coeff (columns i).toFinsupp =
    residueEntry i j
  rw [rowPolynomial, sample_residual_polynomial, samplePolynomial]
  change (monomial (toExponent (exponentTriple (rowExponent j))) 1 *
    ((sampleTerms (rowLabels j).1).map termPolynomial).sum).coeff
    (toExponent (exponentTriple (columns i))) = _
  unfold residueEntry
  induction sampleTerms (rowLabels j).1 with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, term_coeff, ih]

/- Each natural stores one row in base five. These two tables give the
   specialized coefficient matrix and a right inverse. -/
private def residueRows : Vector ℕ 44 :=
  #v[
    0x178287f49c4a1d6622fb2abc, 0x5e0a1fd2712875988becabd,
    0x2519fe8e06a4f6652f345f912, 0x10e5d1b7d05545216924e69e9,
    0x1d6329f1c35ca4bfabcbd781, 0xc196d78236f24a150c985dc36,
    0x3a0a3fa3e1d6f9a9c2481a569, 0x3988f1b820e2c6ee1342f36f09,
    0xe652cbf07e892d705d97badbe, 0x4048ebc0dca587aeccfd303e6,
    0x4de0625a69e5f1f9324004fd1, 0xf4484caac44a0190de8d0e04c,
    0xf9cae488f4a3a54e99a3d9b79, 0x3ac653e386b9497f6601368a,
    0x5bd5e316af7827391afb52309, 0x9c1eceee21553c378b0002d26,
    0x1fcc4c6aaa51d8ed7be13f6106, 0x30c9a0b14627e6c0d969296612,
    0xe596b7b0c643c7cb1059073c8, 0x1cb2d6f618c878e6a5e14a1e1a,
    0x1970d5ed1804d15feb6f, 0x5bd5efaf875382a643a0af407,
    0x3f0c1819ff0c76e9d2369, 0x1cb2de3dc7dc52eb7b104d49f1,
    0x2a5a3d1573d3087, 0xd3c21bcf58a06a7,
    0x422ca8b35a88318, 0xc6c18744602571a32ca08,
    0x6282e5a5fa9168ad22ee45, 0x1ec8e7c3de4d70b61aea759,
    0x38e007c6f736a1e363c5807, 0xd3cb3663532a49,
    0x422d55e27deb0f3, 0x214e8348c4f,
    0xa688906bd8b, 0x3025f39ef2ef3e58989426,
    0x114da38d1f561c12e419524, 0x568431c19cae8c5e747e9b4,
    0x386c797e4ad72acc314e863, 0x22ba753352c29e8,
    0xada44a009dcd188, 0xce76db1cd49ae36,
    0x27b46536c66c8e3, 0xc685fa11e01ec6f]

private def inverseRows : Vector ℕ 44 :=
  #v[
    0x1988eefa9058b9c5f60ed80cd0, 0x402484ada26a85162b8761eb8e,
    0x4778878a518d3aaf48f1b88862, 0x23c744860f70723843650c3ec0,
    0x3edfcc04a20ec5ea11eabbc057, 0xfe28c7f9cdae29c8d7ac4194f,
    0x463378b6291b3b8d90be18ed1e, 0x36487d3fd12660381a958cd3ee,
    0x3220b0011bfe0a93485a1cfda7, 0x1c9de9a9cbf9ac72d6fd2d3070,
    0x343b4007f4e90594f77909fc6d, 0x2deaf189c1490700926690afda,
    0xe596b7b0c8d985b053dd339cf, 0x2d63668255dd94448ad7973cc1,
    0x2acd6572aefaa42062e96c78f4, 0x2deb05b0e7bc22f7fb856f2d4,
    0xe596cf6b00e191a1e0ed0da2a, 0x314dc6448d9338c15b0a,
    0xf684df56c3e01bc6c732, 0x1e00ce2ecbce3684ff2489d155,
    0x2e5fdce5982ceed558d4e7e7dd, 0x2434c5e075b123c68b5f4e83b5,
    0x2589aa93d08b5670d45a886ee7, 0x2c32221496ce53c44142aa06e1,
    0x5bd5e313828182d6f8a51ecf2, 0x1cb2d6f618c878e32db399a0ba,
    0x46512d74b5143cdbeaa0efd2ac, 0x3e7bef734c1ea0407333980318,
    0x26b28efc2c607cc1da37afd58c, 0x19279def97edef3b0e01269705,
    0x11868a85d87dd3ac3708cf12aa, 0x89b601ebb0ed657f71b0d1a4c,
    0x7a9d1921e099205e90ec58a02, 0x3000d68f8febf64d79289aee4c,
    0x17075fa7d0286285fa18f9c61c, 0x2b65c4dfd3a389f5183000dbf5,
    0x144a5e5481935b94c6390f8708, 0x17c53e23a89df920c742fc6cde,
    0x2f1b221ba57d613f5298cff27f, 0x21d9c36177cd99f8f1bb4eb9fd,
    0x407a1b7c28243d26b9551dc397, 0x1529ccfb5e927c949eab74d5f,
    0x206d84868974ef8d69969ff098, 0x36487cc48eb6b4b378bee84ddb]

private def digit (rows : Vector ℕ 44) (i j : Fin 44) : ℕ :=
  rows.get i / 5 ^ j.val % 5

private def unpack (rows : Vector ℕ 44) : Matrix (Fin 44) (Fin 44) F₅ :=
  fun i j => digit rows i j

private lemma entries_equal : ∀ i j : Fin 44,
    residueEntry i j = unpack residueRows i j := by
  intro i
  fin_cases i <;> decide +kernel

private def productEntry (i j : Fin 44) : ℕ :=
  (List.ofFn (fun k : Fin 44 => digit residueRows i k * digit inverseRows k j)).sum

private lemma checks_inverse : ∀ i j : Fin 44,
    productEntry i j % 5 = if i = j then 1 else 0 := by
  intro i
  fin_cases i <;> decide +kernel

private lemma rightInverse : unpack residueRows * unpack inverseRows = 1 := by
  apply Matrix.ext
  intro i j
  have h : (unpack residueRows * unpack inverseRows) i j = (productEntry i j : F₅) := by
    simp only [Matrix.mul_apply, unpack, productEntry, List.sum_ofFn, Nat.cast_sum, Nat.cast_mul]
  rw [h, ← ZMod.natCast_mod _ 5, checks_inverse, Matrix.one_apply]
  split_ifs <;> simp

private theorem sample_minor_ne_zero : (residualMinor sampleLeft sampleRight).det ≠ 0 := by
  have he : residualMinor sampleLeft sampleRight = unpack residueRows :=
    Matrix.ext fun i j => (residue_entry i j).trans (entries_equal i j)
  rw [he]
  have h := congrArg Matrix.det rightInverse
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul (h.symm ▸ one_ne_zero)

/-- Taking the triplet block commutes with changing the tensor coefficients. -/
theorem map_tensorTriplet {S : Type*} [CommRing S] (f : R →+* S)
    (A : Fin 2 → Matrix (Fin 2) (Fin 2) R) :
    f.mapMatrix (tensorTriplet A) = tensorTriplet (fun i => f.mapMatrix (A i)) := by
  have htrace (M : Matrix (Fin 2) (Fin 2) R) : f M.trace = (f.mapMatrix M).trace := by
    exact AddMonoidHom.map_trace f M
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorTriplet, necklaceTuple, triplet, RingHom.mapMatrix_apply, Matrix.map_apply,
      htrace, map_ofNat, ← Matrix.map_mul, ← Matrix.map_pow]

private theorem sampleTriplets :
    tensorTriplet (![!![4, 2; 1, 0], !![1, 3; 3, 2]] : Fin 2 → Matrix (Fin 2) (Fin 2) F₅) =
      sampleLeft ∧
    tensorTriplet (![!![4, 4; 2, 1], !![3, 2; 4, 3]] : Fin 2 → Matrix (Fin 2) (Fin 2) F₅) =
      sampleRight := by
  decide +kernel

private lemma residue_tensorTriplets :
    residue.mapMatrix (tensorTriplet gaussianTensor) = sampleLeft ∧
      residue.mapMatrix (tensorTriplet (fun i => (gaussianTensor i).map star)) = sampleRight := by
  constructor
  · rw [map_tensorTriplet, gaussian_residues.1]
    exact sampleTriplets.1
  · rw [map_tensorTriplet, gaussian_residues.2]
    exact sampleTriplets.2

private lemma complex_map_star (z : GaussianInt) :
    GaussianInt.toComplex (star z) = star (GaussianInt.toComplex z) := by
  rcases z with ⟨a, b⟩
  change ((star (⟨a, b⟩ : GaussianInt) : GaussianInt) : ℂ) = star ((⟨a, b⟩ : GaussianInt) : ℂ)
  simp [GaussianInt.toComplex_def', Zsqrtd.star_mk, Complex.star_def]

private lemma complex_injective : Function.Injective GaussianInt.toComplex := by
  intro a b h
  rcases a with ⟨ar, ai⟩
  rcases b with ⟨br, bi⟩
  have hre : (ar : ℝ) = (br : ℝ) := by
    simpa [GaussianInt.toComplex_def'] using congrArg Complex.re h
  have him : (ai : ℝ) = (bi : ℝ) := by
    simpa [GaussianInt.toComplex_def'] using congrArg Complex.im h
  exact Zsqrtd.ext (Int.cast_injective hre) (Int.cast_injective him)

/-- Product of the minors and singlet coordinates used in reconstruction. -/
noncomputable def certificateValue (T U : M₃) : R :=
  T.det * U.det * (singlet T * singlet U) *
    (cyclicMatrix (T * U) cyclicVector).det * (residualMinor T U).det

/-- The certificate uses only polynomial operations over the coefficients. -/
theorem map_certificateValue {S : Type*} [CommRing S] (f : R →+* S) (T U : M₃) :
    f (certificateValue T U) = certificateValue (f.mapMatrix T) (f.mapMatrix U) := by
  have hv : f ∘ cyclicVector = (cyclicVector : Fin 3 → S) := by
    funext j
    fin_cases j <;> simp [cyclicVector]
  have hs (M : M₃) : f (singlet M) = singlet (f.mapMatrix M) := by
    simp only [singlet, map_sub, map_mul, map_ofNat, RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [certificateValue, map_mul, f.map_det, hs, map_cyclicMatrix, map_residualMinor, hv]

private lemma sample_block_factors :
    sampleLeft.det * sampleRight.det * (singlet sampleLeft * singlet sampleRight) *
      (cyclicMatrix (sampleLeft * sampleRight) cyclicVector).det ≠ 0 := by
  decide +kernel

/-- The complete coefficient certificate is nonzero on a physical tensor and its
complex conjugate, obtained by lifting the two residue-field tensors together. -/
theorem physical_certificate_nonzero :
    ∃ A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      certificateValue (tensorTriplet A) (tensorTriplet (fun i => (A i).map star)) ≠ 0 := by
  let B := fun i => (gaussianTensor i).map star
  let d := certificateValue (tensorTriplet gaussianTensor) (tensorTriplet B)
  have hd : d ≠ 0 := by
    intro hz
    have h := congrArg residue hz
    have he : residue d = certificateValue sampleLeft sampleRight := by
      change residue (certificateValue (tensorTriplet gaussianTensor) (tensorTriplet B)) = _
      rw [map_certificateValue, residue_tensorTriplets.1, residue_tensorTriplets.2]
    rw [he, map_zero] at h
    exact mul_ne_zero sample_block_factors sample_minor_ne_zero h
  let A := fun i => GaussianInt.toComplex.mapMatrix (gaussianTensor i)
  let V := fun i => (A i).map star
  have hV : (fun i => GaussianInt.toComplex.mapMatrix (B i)) = V := by
    funext i
    apply Matrix.ext
    intro j k
    exact complex_map_star (gaussianTensor i j k)
  refine ⟨A, ?_⟩
  have h := complex_injective.ne hd
  rw [map_zero] at h
  change GaussianInt.toComplex (certificateValue (tensorTriplet gaussianTensor) (tensorTriplet B)) ≠ 0 at h
  rw [map_certificateValue, map_tensorTriplet, map_tensorTriplet, hV] at h
  exact h

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidueLift
