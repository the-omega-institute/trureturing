/- GID: D5/S3/Combinatorics/Matroids/QTransversalRepresentability
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/QTransversalRepresentability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Q-transversal ranks are representable over finite extensions. -/

/- admission_basis: open-problem-resolution (#19965; Proved)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22087
   Module escape_witness: none; admission is the settling result
   Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
   partialProd_eq_prefix: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: code_inj.
   code_inj: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: kronecker_ne_zero.
   kronecker_monomial: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: kronecker_ne_zero.
   kronecker_ne_zero: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: simultaneous_specialization_fin.
   finite_extension_primitive_degree: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: finite_polynomial_avoidance.
   finite_polynomial_avoidance: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: simultaneous_specialization_fin.
   simultaneous_specialization_fin: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: simultaneous_specialization.
   simultaneous_specialization: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: specialized_independent_subspaces.
   IsPartialQTransversal: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: qTransversalRank, specialized_independent_subspaces.
   qTransversalRank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: claim, qRank_eq_imageRank.
   representedRank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: claim, representedRank_matrixOfLinear.
   claim: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: result.
   hall_criterion: proof_shape: content; escape_witness: hall_criterion;
     Direct frozen dependencies: none.
     consumers: restricted_annihilator_hall, generic_minor_nonzero.
   restricted_annihilator_coannihilator: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: restricted_annihilator_finrank.
   restricted_annihilator_finrank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: restricted_annihilator_hall.
   restricted_annihilator_hall: proof_shape: content; escape_witness: restricted_annihilator_hall;
     Direct frozen dependencies: none.
     consumers: generic_minor_nonzero.
   genericRestriction: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: generic_minor_nonzero, specialized_independent_subspaces.
   generic_minor_nonzero: proof_shape: content; escape_witness: generic_minor_nonzero;
     Direct frozen dependencies: none.
     consumers: specialized_independent_subspaces.
   annihilatorMap: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: specialized_independent_subspaces.
   annihilatorMap_zero: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: specialized_independent_subspaces.
   specialized_independent_subspaces: proof_shape: content; escape_witness: specialized_independent_subspaces;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: result.
   imageSpace: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: imageSpace_of_span, partial_of_imageRank, imageRank_attained.
   span_image_span: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: imageSpace_of_span.
   imageSpace_of_span: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: imageSpace_basis, partial_of_imageRank, imageRank_attained.
   imageSpace_basis: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: imageRank_attained, representedRank_matrixOfLinear, result.
   imageSpace_mono: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: qRank_eq_imageRank.
   partial_of_imageRank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: imageRank_attained.
   imageRank_attained: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: qRank_eq_imageRank.
   qRank_eq_imageRank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: result.
   matrixOfLinear: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: matrixOfLinear_apply, representedRank_matrixOfLinear, result.
   matrixOfLinear_apply: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: representedRank_matrixOfLinear.
   representedRank_matrixOfLinear: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: result.
   result: proof_shape: content; escape_witness: result;
     Direct frozen dependencies: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.kroneckerHom [sha256:3fdaa22cbbd32ea2a12192594af0d8e66e17e4b8a566e897bfcedb5f83d12664].
     consumers: settling endpoint.
-/

import D5.S3.Combinatorics.Matroids.LinearRado
import D5.S3.Arith.DiophantineApproximation.GeneralizedWronskian
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Hall.Basic

namespace D5.S3.Combinatorics.Matroids.QTransversalRepresentability

section

private lemma partialProd_eq_prefix {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    Fin.partialProd (fun j => a j + 1) i.castSucc =
      ∏ j : Fin i.val, (a (Fin.castLE i.is_lt.le j) + 1) := by
  change ((List.ofFn (fun j => a j + 1)).take i.val).prod = _
  rw [← Fin.ofFn_take_eq_take_ofFn i.is_lt.le]
  exact Fin.prod_ofFn _

private lemma code_inj {n : ℕ} (a d e : Fin n → ℕ)
    (hd : ∀ i, d i ≤ a i) (he : ∀ i, e i ≤ a i)
    (h : (∑ i, d i * Fin.partialProd (fun j => a j + 1) i.castSucc) =
      ∑ i, e i * Fin.partialProd (fun j => a j + 1) i.castSucc) : d = e := by
  let dd : ∀ i, Fin (a i + 1) := fun i => ⟨d i, Nat.lt_succ_of_le (hd i)⟩
  let ee : ∀ i, Fin (a i + 1) := fun i => ⟨e i, Nat.lt_succ_of_le (he i)⟩
  have heq : finPiFinEquiv dd = finPiFinEquiv ee := by
    apply Fin.ext
    simpa only [finPiFinEquiv_apply, dd, ee, partialProd_eq_prefix] using h
  have heq' := finPiFinEquiv.injective heq
  funext i
  exact congrArg (fun f : ∀ j, Fin (a j + 1) => (f i).val) heq'

end


section
open MvPolynomial

private lemma kronecker_monomial {F : Type*} [Field F] {n : ℕ}
    (a : Fin n → ℕ) (d : Fin n →₀ ℕ) (c : F) :
    (MvPolynomial.kroneckerHom ((fun i : Fin n => Fin.partialProd (fun j => a j + 1) i.castSucc))) (MvPolynomial.monomial d c) = Polynomial.monomial ((fun (a d : Fin _ → ℕ) => ∑ i, d i * Fin.partialProd (fun j => a j + 1) i.castSucc) a d) c := by
  classical
  simp only [MvPolynomial.kroneckerHom, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype]
  · simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    simp only [Nat.mul_comm]
    exact Polynomial.C_mul_X_pow_eq_monomial
  · intro i
    simp

private lemma kronecker_ne_zero {F : Type*} [Field F] {n : ℕ}
    (a : Fin n → ℕ) (p : MvPolynomial (Fin n) F) (hp : p ≠ 0)
    (ha : ∀ d ∈ p.support, ∀ i, d i ≤ a i) : (MvPolynomial.kroneckerHom ((fun i : Fin n => Fin.partialProd (fun j => a j + 1) i.castSucc))) p ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  have hdm : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
  have hc : ((MvPolynomial.kroneckerHom ((fun i : Fin n => Fin.partialProd (fun j => a j + 1) i.castSucc))) p).coeff ((fun (a d : Fin _ → ℕ) => ∑ i, d i * Fin.partialProd (fun j => a j + 1) i.castSucc) a d) = p.coeff d := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum (MvPolynomial.kroneckerHom (R := F) ((fun i : Fin n => Fin.partialProd (fun j => a j + 1) i.castSucc)))]
    simp only [Polynomial.finsetSum_coeff]
    simp only [kronecker_monomial, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single d]
    · simp
    · intro e he hne
      have hcodes : (fun (a d : Fin _ → ℕ) => ∑ i, d i * Fin.partialProd (fun j => a j + 1) i.castSucc) a e ≠ (fun (a d : Fin _ → ℕ) => ∑ i, d i * Fin.partialProd (fun j => a j + 1) i.castSucc) a d := by
        intro h
        apply hne
        exact Finsupp.ext (congrFun (code_inj a e d (ha e he) (ha d hdm) h))
      simp [hcodes]
    · intro h
      exact (h hdm).elim
  intro hz
  rw [hz, Polynomial.coeff_zero] at hc
  exact hd hc.symm

end


section

/-- Finite-field infrastructure needed by the mixed-radix specialization: an
extension of any positive degree has a primitive element of that degree. -/
private theorem finite_extension_primitive_degree
    (F : Type) [Field F] [Fintype F] (D : ℕ) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K)
      (_ : FiniteDimensional F K) (α : K),
      (minpoly F α).degree = D := by
  obtain ⟨p, hp⟩ := CharP.exists F
  letI : CharP F p := hp
  letI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime F p⟩
  letI : NeZero D := ⟨hD⟩
  let K := FiniteField.Extension F p D
  letI : Field K := inferInstance
  letI : Algebra F K := inferInstance
  letI : FiniteDimensional F K := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F K
  refine ⟨K, inferInstance, inferInstance, inferInstance, α, ?_⟩
  exact (Field.primitive_element_iff_minpoly_degree_eq F α).mp hα |>.trans
    (by simpa using (FiniteField.finrank_extension F p D))

end

section

/-- The finite specialization consequence, proved from the primitive element and
minimal-polynomial degree bound. -/
private theorem finite_polynomial_avoidance
    (F : Type) [Field F] [Fintype F] (D : ℕ) (hD : D ≠ 0)
    (P : Finset (Polynomial F))
    (hP : ∀ p ∈ P, p ≠ 0 ∧ p.natDegree < D) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K)
      (_ : FiniteDimensional F K) (α : K),
      ∀ p ∈ P, Polynomial.aeval α p ≠ 0 := by
  obtain ⟨K, hKfield, hKalg, hKfd, α, hαdeg⟩ :=
    finite_extension_primitive_degree F D hD
  refine ⟨K, hKfield, hKalg, hKfd, α, ?_⟩
  intro p hp hzero
  have hpne : p ≠ 0 := (hP p hp).1
  have hdiv : minpoly F α ∣ p := minpoly.dvd F α hzero
  have hle : (minpoly F α).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd hdiv hpne
  have hmin : (minpoly F α).natDegree = D :=
    Polynomial.natDegree_eq_of_degree_eq_some hαdeg
  have : D ≤ p.natDegree := hmin ▸ hle
  exact (Nat.not_le_of_lt (hP p hp).2) this

end


section

private theorem simultaneous_specialization_fin (F : Type) [Field F] [Fintype F] {n : ℕ}
    (P : Finset (MvPolynomial (Fin n) F)) (hP : ∀ p ∈ P, p ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (α : K) (w : Fin n → ℕ), ∀ p ∈ P,
      MvPolynomial.aeval (fun i => α ^ w i) p ≠ 0 := by
  classical
  let S := P.biUnion MvPolynomial.support
  let a : Fin n → ℕ := fun i => S.sup (fun d => d i)
  let w : Fin n → ℕ := fun i => Fin.partialProd (fun j => a j + 1) i.castSucc
  let Q := P.image (MvPolynomial.kroneckerHom (w))
  let D := Q.sup Polynomial.natDegree + 1
  have hQ : ∀ q ∈ Q, q ≠ 0 ∧ q.natDegree < D := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨kronecker_ne_zero a p (hP p hp) ?_, ?_⟩
    · intro d hd i
      change d i ≤ S.sup (fun e => e i)
      exact Finset.le_sup (s := S) (f := fun e : Fin n →₀ ℕ => e i) (show d ∈ S from Finset.mem_biUnion.mpr ⟨p, hp, hd⟩)
    · change _ < Q.sup Polynomial.natDegree + 1
      exact Nat.lt_succ_of_le (Finset.le_sup (s := Q) (f := Polynomial.natDegree) (show (MvPolynomial.kroneckerHom (w)) p ∈ Q from Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  obtain ⟨K, hK, hA, hFD, α, hα⟩ :=
    finite_polynomial_avoidance F D (Nat.succ_ne_zero _) Q hQ
  refine ⟨K, hK, hA, hFD, α, w, ?_⟩
  intro p hp
  have hh := hα ((MvPolynomial.kroneckerHom (w)) p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have he : (Polynomial.aeval (R := F) α).toRingHom.comp ((MvPolynomial.kroneckerHom (R := F) (w)).toRingHom) =
      (MvPolynomial.aeval (R := F) (fun i => α ^ w i)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [MvPolynomial.kroneckerHom]
    · intro i
      simp [MvPolynomial.kroneckerHom]
  change ((MvPolynomial.aeval (R := F) (fun i => α ^ w i)).toRingHom) p ≠ 0
  rw [← he]
  exact hh

private theorem simultaneous_specialization (F : Type) [Field F] [Fintype F]
    {σ : Type} [Fintype σ] (P : Finset (MvPolynomial σ F)) (hP : ∀ p ∈ P, p ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (α : K) (w : σ → ℕ), ∀ p ∈ P,
      MvPolynomial.aeval (fun i => α ^ w i) p ≠ 0 := by
  classical
  let e := Fintype.equivFin σ
  let Q := P.image (MvPolynomial.rename e)
  have hQ : ∀ q ∈ Q, q ≠ 0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (MvPolynomial.rename_eq_zero_iff_of_injective p e.injective).not.mpr (hP p hp)
  obtain ⟨K, hK, hA, hFD, α, w, hw⟩ := simultaneous_specialization_fin F Q hQ
  refine ⟨K, hK, hA, hFD, α, w ∘ e, ?_⟩
  intro p hp
  have hh := hw (MvPolynomial.rename e p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  simpa only [MvPolynomial.aeval_rename, Function.comp_def] using hh

end



/-! Binding conventions for M. Saaltink, "A theory of q-transversals", arXiv:2503.12201v1 (15 March 2025).

* Section 3.2: "Given some n × m matrix G over a field K extending F_q, we can define the q-matroid represented by G
  as follows: if a subspace of F_q^m is the row space of matrix X, then its rank in the matroid is the rank of matrix
  G Xᵀ."
* Definition 14: for a family `X = (X₁, …, X_n)` of subspaces of `V`, a partial q-transversal is a subspace `T` such
  that every vector basis of `T` is a partial avoiding transversal of `X`: there is an injection `f` from the basis
  to the indices with `b ∉ X_{f(b)}`. Theorem 15: the partial q-transversals are the independent subspaces of a
  q-matroid, the q-transversal matroid of `X`; its rank of `U` is the largest dimension of an independent subspace
  of `U`.
* Section 4.2: "Conjecture 3. All q-transversal matroids are representable." -/

section

open Module

variable {F : Type} [Field F] [Fintype F]

/-- Definition 14: `T` is a partial q-transversal of `X`: every vector basis `s` of `T` admits an injection
`f : s → Fin k` with `b ∉ X (f b)` for every `b ∈ s`. -/
def IsPartialQTransversal {m k : ℕ} (X : Fin k → Submodule F (Fin m → F)) (T : Submodule F (Fin m → F)) : Prop :=
  ∀ s : Finset (Fin m → F), LinearIndependent F (fun b : s => (b : Fin m → F)) →
    Submodule.span F (s : Set (Fin m → F)) = T →
      ∃ f : s → Fin k, Function.Injective f ∧ ∀ b : s, (b : Fin m → F) ∉ X (f b)

open Classical in
/-- The rank function of the q-transversal matroid of `X`: the largest dimension of a partial q-transversal
contained in `U`. -/
noncomputable def qTransversalRank {m k : ℕ} (X : Fin k → Submodule F (Fin m → F))
    (U : Submodule F (Fin m → F)) : ℕ :=
  sSup {d | ∃ T : Submodule F (Fin m → F), T ≤ U ∧ IsPartialQTransversal X T ∧ finrank F T = d}

/-- Section 3.2: the rank of `U` in the q-matroid represented by `G`, `rank (G Xᵀ)` where the rows of `X` are a
basis of `U`. -/
noncomputable def representedRank {K : Type} [Field K] [Algebra F K] {r m : ℕ} (G : Matrix (Fin r) (Fin m) K)
    (U : Submodule F (Fin m → F)) : ℕ :=
  (G * Matrix.of fun (j : Fin m) (i : Fin (finrank F U)) =>
      algebraMap F K ((Module.finBasis F U i : Fin m → F) j)).rank

/-- Conjecture 3: every q-transversal matroid is representable, over a finite extension `K` of the base field. -/
def claim : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (m k : ℕ) (X : Fin k → Submodule F (Fin m → F)),
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (r : ℕ)
      (G : Matrix (Fin r) (Fin m) K),
      ∀ U : Submodule F (Fin m → F), representedRank G U = qTransversalRank X U

end

section
open Module Submodule

/-- The source's Hall criterion, retaining the every-basis quantifier. -/
private theorem hall_criterion {F : Type} [Field F] [Fintype F] {m k : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) (T : Submodule F (Fin m → F)) :
    IsPartialQTransversal X T ↔ ∀ J : Finset (Fin k),
      finrank F (↥(T ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1)) + J.card ≤ k := by
  classical
  constructor
  · intro hT J
    let C := T ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1
    let bC := Module.finBasis F C
    let vC : Fin (finrank F C) → (Fin m → F) := fun i => (bC i : Fin m → F)
    have hC : LinearIndependent F vC := bC.linearIndependent.map' C.subtype C.ker_subtype
    have hCT : Set.range vC ⊆ (T : Set (Fin m → F)) := by
      rintro x ⟨i, rfl⟩
      exact (bC i).property.1
    obtain ⟨B, hBT, hCB, hTspan, hBLI⟩ :=
      exists_linearIndepOn_id_extension hC.linearIndepOn_id hCT
    let s : Finset (Fin m → F) := B.toFinset
    have hs : (s : Set (Fin m → F)) = B := Set.coe_toFinset B
    have hsi : LinearIndependent F (fun b : s => (b : Fin m → F)) := by
      change LinearIndepOn F id (s : Set (Fin m → F))
      rw [hs]
      exact hBLI
    have hsSpan : span F (s : Set (Fin m → F)) = T := by
      rw [hs]
      exact le_antisymm (span_le.mpr hBT) hTspan
    obtain ⟨f, hfi, hf⟩ := hT s hsi hsSpan
    let inc : Fin (finrank F C) → s := fun i => ⟨vC i, by
      change vC i ∈ (s : Set (Fin m → F))
      rw [hs]
      exact hCB ⟨i, rfl⟩⟩
    have hinc : Function.Injective inc := by
      intro i j hij
      exact hC.injective (congrArg (fun x : s => (x : Fin m → F)) hij)
    have hfout : ∀ i, f (inc i) ∉ J := by
      intro i hi
      apply hf (inc i)
      exact (Submodule.mem_iInf _).mp (bC i).property.2 ⟨f (inc i), hi⟩
    let g : Fin (finrank F C) → {i : Fin k // i ∉ J} := fun i => ⟨f (inc i), hfout i⟩
    have hgi : Function.Injective g := by
      intro i j hij
      exact hinc (hfi (congrArg Subtype.val hij))
    have hcard := Fintype.card_le_of_injective g hgi
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_coe] at hcard
    have hJcard : J.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ J)
    change finrank F C + J.card ≤ k
    omega
  · intro hall s hsi hsSpan
    let N : s → Finset (Fin k) := fun b => Finset.univ.filter fun i => (b : Fin m → F) ∉ X i
    have hHall : ∀ a : Finset s, a.card ≤ (a.biUnion N).card := by
      intro a
      let R := a.biUnion N
      let J : Finset (Fin k) := Finset.univ \ R
      let C := T ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1
      have hmem : ∀ b : a, (b.1 : Fin m → F) ∈ C := by
        intro b
        constructor
        · rw [← hsSpan]
          exact Submodule.subset_span b.1.2
        · apply (Submodule.mem_iInf _).mpr
          intro i
          by_contra hnot
          have hiR : i.1 ∈ R := Finset.mem_biUnion.mpr
            ⟨b.1, b.2, Finset.mem_filter.mpr ⟨Finset.mem_univ i.1, hnot⟩⟩
          exact (Finset.mem_sdiff.mp i.2).2 hiR
      let va : a → C := fun b => ⟨(b.1 : Fin m → F), hmem b⟩
      have hva : LinearIndependent F va := by
        apply LinearIndependent.of_comp C.subtype
        exact hsi.comp Subtype.val Subtype.val_injective
      have hdim : a.card ≤ finrank F C := by
        simpa only [Fintype.card_coe] using hva.fintype_card_le_finrank
      have hbound := hall J
      change finrank F C + J.card ≤ k at hbound
      have hcard : J.card + R.card = k := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
      change a.card ≤ R.card
      omega
    obtain ⟨f, hfi, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
    exact ⟨f, hfi, fun b => (Finset.mem_filter.mp (hf b)).2⟩

end

section
open Module Submodule

/-- Restricting an annihilator retains exactly the common vanishing vectors. -/
private lemma restricted_annihilator_coannihilator {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (X U : Submodule F V) :
    (X.dualAnnihilator.map U.dualRestrict).dualCoannihilator = X.comap U.subtype := by
  ext u
  rw [Submodule.mem_dualCoannihilator, Submodule.mem_comap]
  constructor
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff X (u : V)).mp
    intro φ hφ
    exact h (U.dualRestrict φ) (Submodule.mem_map.mpr ⟨φ, hφ, rfl⟩)
  · intro hu φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    exact (Submodule.mem_dualAnnihilator ψ).mp hψ (u : V) hu

/-- The dimension bridge from intersections to sums of restricted annihilators. -/
private lemma restricted_annihilator_finrank {F V ι : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (X : ι → Submodule F V) (U : Submodule F V) (J : Finset ι) :
    finrank F (↥(⨆ i : {i : ι // i ∈ J}, (X i.1).dualAnnihilator.map U.dualRestrict)) +
      finrank F (↥(U ⊓ ⨅ i : {i : ι // i ∈ J}, X i.1)) = finrank F U := by
  classical
  let S := ⨆ i : {i : ι // i ∈ J}, (X i.1).dualAnnihilator.map U.dualRestrict
  have hco : S.dualCoannihilator = (⨅ i : {i : ι // i ∈ J}, X i.1).comap U.subtype := by
    rw [Submodule.dualCoannihilator_iSup_eq]
    simp_rw [restricted_annihilator_coannihilator]
    exact (Submodule.comap_iInf _ _).symm
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  have hc : finrank F S.dualCoannihilator =
      finrank F (↥(U ⊓ ⨅ i : {i : ι // i ∈ J}, X i.1)) := by
    rw [← Submodule.finrank_map_subtype_eq U S.dualCoannihilator, hco,
      Submodule.map_comap_subtype]
  rw [hc] at hdim
  exact hdim

/-- Hall's criterion gives precisely the deficit inequalities used by linear Rado. -/
private lemma restricted_annihilator_hall {F : Type} [Field F] [Fintype F] {m k : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) (U : Submodule F (Fin m → F))
    (hU : IsPartialQTransversal X U) (J : Finset (Fin k)) :
    finrank F U + J.card ≤ k +
      finrank F (↥(⨆ i : {i : Fin k // i ∈ J}, (X i.1).dualAnnihilator.map U.dualRestrict)) := by
  have hdim := restricted_annihilator_finrank X U J
  have hbound := (hall_criterion X U).mp hU J
  omega

end


section
open Module Submodule

private noncomputable def genericRestriction {F : Type} [Field F] [Fintype F] {m k : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) (U : Submodule F (Fin m → F)) :
    Matrix (Fin k) (Fin (finrank F U)) (MvPolynomial (((i : Fin k) × Fin (finrank F (X i).dualAnnihilator))) F) := by
  classical
  letI (i : Fin k) : Module.Free F (X i).dualAnnihilator :=
    Module.Free.of_divisionRing F (X i).dualAnnihilator
  exact fun i j => ∑ a : Fin (finrank F (X i).dualAnnihilator),
    MvPolynomial.X ⟨i, a⟩ * MvPolynomial.C
      ((Module.finBasis F (X i).dualAnnihilator a : Module.Dual F (Fin m → F))
        (Module.finBasis F U j : Fin m → F))

/-- Every partial q-transversal has a nonzero generic maximal minor. -/
private theorem generic_minor_nonzero {F : Type} [Field F] [Fintype F] {m k : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) (U : Submodule F (Fin m → F))
    (hU : IsPartialQTransversal X U) :
    ∃ f : Fin (finrank F U) → Fin k, Function.Injective f ∧
      ((genericRestriction X U).submatrix f id).det ≠ 0 := by
  classical
  letI (i : Fin k) : Module.Free F (X i).dualAnnihilator :=
    Module.Free.of_divisionRing F (X i).dualAnnihilator
  have ht : finrank F U ≤ k := by
    have h := (hall_criterion X U).mp hU ∅
    have hC : (U ⊓ ⨅ i : {i : Fin k // i ∈ (∅ : Finset (Fin k))}, X i.1) = U := by
      rw [iInf_of_isEmpty, sInf_empty, inf_top_eq]
    rw [hC, Finset.card_empty, add_zero] at h
    exact h
  let L : Fin k → Submodule F (Module.Dual F U) := fun i =>
    (X i).dualAnnihilator.map U.dualRestrict
  have ht' : finrank F (Module.Dual F U) ≤ k := by
    rw [Subspace.dual_finrank_eq]
    exact ht
  have hh : ∀ J : Finset (Fin k), finrank F (Module.Dual F U) + J.card ≤ k +
      finrank F (↥(⨆ i : {i : Fin k // i ∈ J}, L i.1)) := by
    intro J
    rw [Subspace.dual_finrank_eq]
    exact restricted_annihilator_hall X U hU J
  obtain ⟨l, hl, hlspan⟩ := D5.S3.Combinatorics.Matroids.LinearRado.spanning_representatives L ht' hh
  let bU := Module.finBasis F U
  let ev : Module.Dual F U →ₗ[F] (Fin (finrank F U) → F) := {
    toFun := fun φ j => φ (bU j)
    map_add' := by intro φ ψ; ext j; rfl
    map_smul' := by intro a φ; ext j; rfl }
  have hev : Function.Surjective ev := by
    intro c
    refine ⟨bU.constr F c, ?_⟩
    ext j
    exact bU.constr_basis F c j
  let M : Matrix (Fin k) (Fin (finrank F U)) F := fun i j => l i (bU j)
  have hM : Submodule.span F (Set.range M.row) = ⊤ := by
    have hm := congrArg (Submodule.map ev) hlspan
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr hev] at hm
    exact hm
  obtain ⟨f, hfi, hdet⟩ := D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows M hM
  have hlift : ∀ i : Fin k, ∃ ψ : (X i).dualAnnihilator,
      U.dualRestrict (ψ : Module.Dual F (Fin m → F)) = l i := by
    intro i
    obtain ⟨ψ, hψ, hψeq⟩ := hl i
    exact ⟨⟨ψ, hψ⟩, hψeq⟩
  choose ψ hψ using hlift
  let coeff : ((i : Fin k) × Fin (finrank F (X i).dualAnnihilator)) → F := fun v =>
    (Module.finBasis F (X v.1).dualAnnihilator).repr (ψ v.1) v.2
  have hcoeff (i : Fin k) (j : Fin (finrank F U)) :
      (∑ a : Fin (finrank F (X i).dualAnnihilator), coeff ⟨i, a⟩ *
        ((Module.finBasis F (X i).dualAnnihilator a : Module.Dual F (Fin m → F))
          (bU j : Fin m → F))) = M i j := by
    have hs := congrArg (fun x : (X i).dualAnnihilator =>
      (x : Module.Dual F (Fin m → F)))
      ((Module.finBasis F (X i).dualAnnihilator).sum_repr (ψ i))
    have hv := congrArg (fun φ : Module.Dual F (Fin m → F) => φ (bU j : Fin m → F)) hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] at hv
    calc
      _ = (ψ i : Module.Dual F (Fin m → F)) (bU j : Fin m → F) := hv
      _ = M i j := congrArg (fun φ : Module.Dual F U => φ (bU j)) (hψ i)
  have heval : (genericRestriction X U).map (MvPolynomial.eval coeff) = M := by
    ext i j
    simp only [genericRestriction, Matrix.map_apply, map_sum, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    exact hcoeff i j
  refine ⟨f, hfi, ?_⟩
  have hmat : (MvPolynomial.eval coeff).mapMatrix ((genericRestriction X U).submatrix f id) =
      M.submatrix f id := by
    ext i j
    exact congrFun (congrFun heval (f i)) j
  have hEvaldet : (MvPolynomial.eval coeff) (((genericRestriction X U).submatrix f id).det) =
      (M.submatrix f id).det := by
    rw [(MvPolynomial.eval coeff).map_det, hmat]
  intro hzero
  apply hdet
  rw [← hEvaldet, hzero, map_zero]

end


section
open Module Submodule

private noncomputable def annihilatorMap {F K : Type} [Field F] [Field K] [Algebra F K]
    {m k : ℕ} (X : Fin k → Submodule F (Fin m → F)) (c : ((i : Fin k) × Fin (finrank F (X i).dualAnnihilator)) → K) :
    (Fin m → F) →ₗ[F] (Fin k → K) := by
  classical
  letI (i : Fin k) : Module.Free F (X i).dualAnnihilator :=
    Module.Free.of_divisionRing F (X i).dualAnnihilator
  exact LinearMap.pi fun i => ∑ a, c ⟨i, a⟩ •
    (Algebra.linearMap F K).comp
      (Module.finBasis F (X i).dualAnnihilator a : Dual F (Fin m → F))

private lemma annihilatorMap_zero {F K : Type} [Field F] [Field K] [Algebra F K]
    {m k : ℕ} (X : Fin k → Submodule F (Fin m → F)) (c : ((i : Fin k) × Fin (finrank F (X i).dualAnnihilator)) → K)
    (i : Fin k) (v : Fin m → F) (hv : v ∈ X i) : annihilatorMap X c v i = 0 := by
  classical
  letI (i : Fin k) : Module.Free F (X i).dualAnnihilator :=
    Module.Free.of_divisionRing F (X i).dualAnnihilator
  simp only [annihilatorMap, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Algebra.linearMap_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  have hz : (Module.finBasis F (X i).dualAnnihilator a : Dual F (Fin m → F)) v = 0 :=
    ((X i).mem_dualAnnihilator _).mp (Module.finBasis F (X i).dualAnnihilator a).2 v hv
  simp [hz]

private theorem specialized_independent_subspaces {F : Type} [Field F] [Fintype F]
    {m k : ℕ} (X : Fin k → Submodule F (Fin m → F)) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (g : (Fin m → F) →ₗ[F] (Fin k → K)),
      (∀ i v, v ∈ X i → g v i = 0) ∧
      ∀ U, IsPartialQTransversal X U →
        LinearIndependent K (fun j : Fin (finrank F U) =>
          g (Module.finBasis F U j : Fin m → F)) := by
  classical
  letI : Finite (Submodule F (Fin m → F)) :=
    Finite.of_injective (fun U : Submodule F (Fin m → F) => (U : Set (Fin m → F)))
      SetLike.coe_injective
  letI : Fintype (Submodule F (Fin m → F)) := Fintype.ofFinite _
  let f (U : Submodule F (Fin m → F)) (h : IsPartialQTransversal X U) :=
    (generic_minor_nonzero X U h).choose
  let p (U : Submodule F (Fin m → F)) : MvPolynomial (((i : Fin k) × Fin (finrank F (X i).dualAnnihilator))) F :=
    if h : IsPartialQTransversal X U then
      ((genericRestriction X U).submatrix (f U h) id).det else 1
  let P := Finset.univ.image p
  have hP : ∀ q ∈ P, q ≠ 0 := by
    intro q hq
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hq
    dsimp [p]
    split_ifs with h
    · exact (generic_minor_nonzero X U h).choose_spec.2
    · exact one_ne_zero
  obtain ⟨K, hK, hA, hFD, α, w, hw⟩ := simultaneous_specialization F P hP
  let c : ((i : Fin k) × Fin (finrank F (X i).dualAnnihilator)) → K := fun a => α ^ w a
  let g := annihilatorMap X c
  refine ⟨K, hK, hA, hFD, g, annihilatorMap_zero X c, ?_⟩
  intro U hU
  let M : Matrix (Fin k) (Fin (finrank F U)) K := fun i j =>
    g (Module.finBasis F U j : Fin m → F) i
  have hM : (genericRestriction X U).map (MvPolynomial.aeval c) = M := by
    ext i j
    simp [genericRestriction, M, g, annihilatorMap, Matrix.map_apply]
  have hdet : (M.submatrix (f U hU) id).det ≠ 0 := by
    have hh := hw (p U) (Finset.mem_image.mpr ⟨U, Finset.mem_univ U, rfl⟩)
    simp only [p, dif_pos hU] at hh
    have hmat : (MvPolynomial.aeval c).toRingHom.mapMatrix
        ((genericRestriction X U).submatrix (f U hU) id) = M.submatrix (f U hU) id := by
      ext i j
      exact congrFun (congrFun hM (f U hU i)) j
    change (MvPolynomial.aeval c).toRingHom (((genericRestriction X U).submatrix (f U hU) id).det) ≠ 0 at hh
    rwa [RingHom.map_det, hmat] at hh
  have hr : M.rank = finrank F U := by
    have hn := Matrix.rank_of_det_ne_zero hdet
    have hl := M.rank_submatrix_le (f U hU) id
    rw [hn, Fintype.card_fin] at hl
    exact le_antisymm M.rank_le_width hl
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin (finrank F U)) = finrank K (span K (Set.range M.col))
  rw [← Matrix.rank_eq_finrank_span_cols, hr, Fintype.card_fin]

end


section
open Module Submodule
variable {F K : Type} [Field F] [Field K] [Algebra F K] {m k : ℕ}

private noncomputable def imageSpace (g : (Fin m → F) →ₗ[F] (Fin k → K))
    (U : Submodule F (Fin m → F)) : Submodule K (Fin k → K) :=
  span K (g '' (U : Set (Fin m → F)))

private lemma span_image_span (g : (Fin m → F) →ₗ[F] (Fin k → K)) (s : Set (Fin m → F)) :
    span K (g '' (span F s : Set (Fin m → F))) = span K (g '' s) := by
  change span K (((span F s).map g : Submodule F (Fin k → K)) : Set (Fin k → K)) = _
  rw [Submodule.map_span, Submodule.span_span_of_tower]

private lemma imageSpace_of_span (g : (Fin m → F) →ₗ[F] (Fin k → K))
    {ι : Type*} (v : ι → (Fin m → F)) (U : Submodule F (Fin m → F))
    (hv : span F (Set.range v) = U) :
    imageSpace g U = span K (Set.range (g ∘ v)) := by
  rw [imageSpace, ← hv, span_image_span, ← Set.range_comp]

private lemma imageSpace_basis (g : (Fin m → F) →ₗ[F] (Fin k → K))
    (U : Submodule F (Fin m → F)) :
    imageSpace g U = span K (Set.range (fun i : Fin (finrank F U) =>
      g (Module.finBasis F U i : Fin m → F))) := by
  have hs := congrArg (Submodule.map U.subtype) (Module.finBasis F U).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, U.range_subtype] at hs
  exact imageSpace_of_span g (fun i => (Module.finBasis F U i : Fin m → F)) U hs

private lemma imageSpace_mono (g : (Fin m → F) →ₗ[F] (Fin k → K))
    {U T : Submodule F (Fin m → F)} (h : T ≤ U) : imageSpace g T ≤ imageSpace g U :=
  span_mono (Set.image_mono h)

private lemma partial_of_imageRank [Fintype F]
    (X : Fin k → Submodule F (Fin m → F))
    (g : (Fin m → F) →ₗ[F] (Fin k → K))
    (hz : ∀ i v, v ∈ X i → g v i = 0)
    (T : Submodule F (Fin m → F)) (hT : finrank K (imageSpace g T) = finrank F T) :
    IsPartialQTransversal X T := by
  classical
  intro s hs hspan
  have hsrange : Set.range (fun b : s => (b : Fin m → F)) = (s : Set (Fin m → F)) := by
    ext x
    simp
  have hc : Fintype.card s = finrank F T := by
    rw [← hspan, ← hsrange]
    exact (finrank_span_eq_card hs).symm
  have himage : imageSpace g T = span K (Set.range (fun b : s => g (b : Fin m → F))) := by
    apply imageSpace_of_span g _ T
    rw [hsrange]
    exact hspan
  have hli : LinearIndependent K (fun b : s => g (b : Fin m → F)) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card s = finrank K (span K (Set.range _))
    rw [← himage, hT, hc]
  obtain ⟨f, hf, hfn⟩ := D5.S3.Combinatorics.Matroids.LinearRado.independent_support_matching _ hli
  refine ⟨f, hf, ?_⟩
  intro b hb
  exact hfn b (hz (f b) b hb)

private lemma imageRank_attained [Fintype F]
    (X : Fin k → Submodule F (Fin m → F))
    (g : (Fin m → F) →ₗ[F] (Fin k → K))
    (hz : ∀ i v, v ∈ X i → g v i = 0)
    (U : Submodule F (Fin m → F)) :
    ∃ T : Submodule F (Fin m → F), T ≤ U ∧ IsPartialQTransversal X T ∧
      finrank F T = finrank K (imageSpace g U) := by
  classical
  let b := Module.finBasis F U
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun j => g (b j : Fin m → F))
  haveI : Finite ι := hli.finite
  letI : Fintype ι := Fintype.ofFinite ι
  let v : ι → (Fin m → F) := fun i => b (a i)
  let T := span F (Set.range v)
  have hv : LinearIndependent F v :=
    (b.linearIndependent.map' U.subtype U.ker_subtype).comp a ha
  have hdim : finrank F T = Fintype.card ι := finrank_span_eq_card hv
  have heq : imageSpace g T = imageSpace g U := by
    rw [imageSpace_of_span g v T rfl, imageSpace_basis]
    exact hspan
  have hr : finrank K (imageSpace g U) = Fintype.card ι := by
    rw [← heq, imageSpace_of_span g v T rfl]
    exact finrank_span_eq_card hli
  refine ⟨T, ?_, partial_of_imageRank X g hz T ?_, hdim.trans hr.symm⟩
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (b (a i)).2
  · rw [heq, hr, hdim]

private theorem qRank_eq_imageRank [Fintype F]
    (X : Fin k → Submodule F (Fin m → F))
    (g : (Fin m → F) →ₗ[F] (Fin k → K))
    (hz : ∀ i v, v ∈ X i → g v i = 0)
    (hfull : ∀ T, IsPartialQTransversal X T →
      finrank K (imageSpace g T) = finrank F T)
    (U : Submodule F (Fin m → F)) :
    qTransversalRank X U = finrank K (imageSpace g U) := by
  obtain ⟨T, hTU, hT, hdim⟩ := imageRank_attained X g hz U
  unfold qTransversalRank
  apply le_antisymm
  · apply csSup_le
    · exact ⟨finrank F T, T, hTU, hT, rfl⟩
    · rintro d ⟨S, hSU, hS, rfl⟩
      rw [← hfull S hS]
      exact Submodule.finrank_mono (imageSpace_mono g hSU)
  · rw [← hdim]
    apply le_csSup
    · refine ⟨finrank F U, ?_⟩
      rintro d ⟨S, hSU, _, rfl⟩
      exact Submodule.finrank_mono hSU
    · exact ⟨T, hTU, hT, rfl⟩

end


section
open Module Submodule
variable {F K : Type} [Field F] [Field K] [Algebra F K] {m k : ℕ}

private noncomputable def matrixOfLinear (g : (Fin m → F) →ₗ[F] (Fin k → K)) :
    Matrix (Fin k) (Fin m) K :=
  (Pi.basisFun K (Fin k)).toMatrix (fun j => g (Pi.basisFun F (Fin m) j))

private lemma matrixOfLinear_apply (g : (Fin m → F) →ₗ[F] (Fin k → K)) (v : Fin m → F) (i : Fin k) :
    ∑ j, matrixOfLinear g i j * algebraMap F K (v j) = g v i := by
  classical
  have h := congrArg (fun z : Fin m → F => g z i) ((Pi.basisFun F (Fin m)).sum_repr v)
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, map_sum] at h
  simp_rw [g.map_smul] at h
  simp only [Finset.sum_apply, Pi.smul_apply] at h
  simp only [Algebra.smul_def] at h
  simpa only [matrixOfLinear, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
    Pi.basisFun_apply, mul_comm] using h

private lemma representedRank_matrixOfLinear [Fintype F]
    (g : (Fin m → F) →ₗ[F] (Fin k → K)) (U : Submodule F (Fin m → F)) :
    representedRank (matrixOfLinear g) U = finrank K (imageSpace g U) := by
  classical
  have he : matrixOfLinear g * Matrix.of (fun (j : Fin m) (i : Fin (finrank F U)) =>
        algebraMap F K ((Module.finBasis F U i : Fin m → F) j)) =
      Matrix.of (fun (i : Fin k) (j : Fin (finrank F U)) =>
        g (Module.finBasis F U j : Fin m → F) i) := by
    ext i j
    exact matrixOfLinear_apply g (Module.finBasis F U j : Fin m → F) i
  rw [representedRank, he, Matrix.rank_eq_finrank_span_cols, imageSpace_basis]
  rfl

end


section
open Module Submodule

/-- Saaltink's Conjecture 3, with the verbatim binding conventions. -/
theorem result : claim := by
  intro F hF hFin m k X
  obtain ⟨K, hK, hA, hFD, g, hz, hind⟩ := specialized_independent_subspaces X
  refine ⟨K, hK, hA, hFD, k, matrixOfLinear g, ?_⟩
  intro U
  rw [representedRank_matrixOfLinear]
  symm
  apply qRank_eq_imageRank X g hz
  intro T hT
  rw [imageSpace_basis]
  simpa only [Fintype.card_fin] using finrank_span_eq_card (hind T hT)

end

end D5.S3.Combinatorics.Matroids.QTransversalRepresentability
