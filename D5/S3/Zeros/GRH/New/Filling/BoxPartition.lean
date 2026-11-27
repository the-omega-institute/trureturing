/- GID: D5/S3/Zeros/GRH/New/Filling/BoxPartition
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/BoxPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.BoxPartition. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/BoxPartition.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.PartnerAlgebra
import D5.S3.Zeros.GRH.New.Filling.NearTerms
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Agreeing characters force shared vectors up the flag. For a rational element under which the
Poincaré series' unipotent character agrees with its conjugate, a vector shared by the standard
frame and its image forces a normal form, and primes over g modulo which the frames meet divide a
two-by-two determinant of pairings, which sorts the terms of the unfolded second moment. Sorting
relevant double cosets by compatibility of unipotent characters is standard, also for Bessel
subgroups. Related work: Friedberg, Poincaré series for GL(n), 1987; Y. Liu, Relative trace formulae
toward Bessel and Fourier–Jacobi periods, 2014; Furusawa–Shalika, Central critical values of degree
four L-functions for GSp(4), Mem. AMS 782, 2003.

Set-up for this proof: Incoherent and degenerate pairs are negligible. The second moment of the
Poincaré series expands over pairs of rational elements congruent mod g. Discriminant gains, lattice
counts and a weighted Schur test show that degenerate terms and pairs with different Levi parts are
negligible, and that the rest shrink where frames meet mod g; this isolates the main term. Related
work: Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023; Kowalski–Saha–Tsimerman,
Local spectral equidistribution for Siegel modular forms, 2012; Blomer, Density theorems for GL(n),
2023.

Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Positive form on links, lifts to the lattice, dimension and isotropy of links. Primes
where agreeing frames meet divide a determinant; integral Eichler lifts. Integral Eichler
transformations give elements of the level-g unipotent group of a class. Covering lemmas for
weighted sums; counting bounded integral vectors; index of a scaled lattice. Definitions of indices,
discriminants, gauges and class representatives for the crude bounds. Boxed cutoffs for the
arithmetic unipotent group and packing count of boxed frames. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open Fin Module Set AddSubgroup Classical ComplexOrder ENNReal Fintype Function IsAdelic Matrix
  NumberField Pointwise QuotientGroup

namespace Filling

variable {E : Type} [Field E] [CMType E] {σ τ : Type} {𝔰 : Shape} {τ' : Type} [Fintype τ']
  (S : Filling E 𝔰) (v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ' E) {R : Type _} [CommRing R]
  [StarRing R] {T : 𝔰.Form R} {S' : Filling E 𝔰}

/-- Liouville inequality for Gram determinants: let Q be totally positive definite, det(aᴴQb) ≠
0, v, v' invertible finite adelic. If x ≥ 0 and x ≤ [det(vᴴaᴴQbv')], then x² ≤ [det v]²·|N
det(aᴴQa)|·|N det(bᴴQb)|·[det v']², N the norm to ℚ, [·] = `genIndex`. -/
lemma liouville_gram [Fintype σ] [Fintype τ] [StablyUnram E] {Q : Matrix τ τ E} (hQ : ∀ w,
    (Q.map (Φ w)).PosDef) (a b : Matrix τ σ E) (v v' : GL σ (𝔸f E)) (h : (aᴴ * Q * b).det ≠ 0) {x}
    (hx : 0 ≤ x) (i : let δ := (vᴴ * (finAdeleMat (aᴴ * Q * b) * v'.1)).det; IsUnit δ → x ≤
    genIndex δ) : x ^ 2 ≤ genIndex v.1.det ^ 2 * (|↑(Algebra.norm ℚ (aᴴ * Q * a).det)| *
  |↑(Algebra.norm ℚ (bᴴ * Q * b).det)| * genIndex v'.1.det ^ 2) := by
  grw [i] <;> simp [*, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    abs_norm_eq_prod_norm_sq, mul_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  gcongr
  simpa [map_conjTranspose, RingHom.map_det, ← mul_pow, sq_le_sq] using
    norm_det_sq_le_of_posSemidef ((fromBlocks_toBlocks
    _).substr ((hQ _).posSemidef.conjTranspose_mul_mul_same ((a.fromCols b).map _)))

/-- The matrix ½·diag(T,T) + N⁻¹·L*L on two copies of X₀⊕Ez, where L is `Filling.zFormPair` T and *
is the conjugate transpose. -/
def linkMetric := (2⁻¹ : E) • (S.ratMiddle E).fromBlocks 0 0 (S.ratMiddle E) + (S.N :
  E)⁻¹ • ((zFormPair (S.ratMiddle E))ᴴ * zFormPair (S.ratMiddle E))

/-- The number |N det(v*Q₁v)|·[det e]², N the norm to ℚ and Q₁ = `Filling.linkMetric`: the squared
discriminant of the lattice with adelic basis v e. -/
def linkDiscSq (e : GL τ' (𝔸f E)) :=
  |↑(Algebra.norm ℚ (vᴴ * S.linkMetric * v).det)| * genIndex e.1.det ^ 2

section

attribute [local simp] finAdeleMat_conjTranspose besselLatticeBasis Matrix.mul_apply
  Matrix.mul_assoc linkMatrix toBesselH

lemma framePair_last_eq_zFormPair_mul (k : T.G) :
  ((framePair k).submatrix id (.map (fun _ ↦ 𝔰.top) fun _ ↦ 𝔰.top))ᴴ * T.splitGram = zFormPair T *
  linkMatrix k := by have := U.form_mul_inv_eq k; simp_all [← ext_iff, Shape.Form.splitGram.eq_1]

lemma classCoord_eq_fromBlocks {S : Filling E 𝔰} c : S.classCoord c = fromBlocks 1 0 0
    (((S.classCoordX₀ c).fromCols (fromRows 0 1)).fromBlocks 0 0 1) := by simp [classCoordX₀,
  classCoord, classBasis]

variable {σ τ : Type} {S : Filling E 𝔰} (c : S.Classes)
  (t : Matrix 𝔰.BesselIndex σ E) (t' : Matrix 𝔰.BesselIndex τ E) {γ γ' : S.G E}
  {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E} {c' : S.Classes}

/-- The columns of m are the images under `linkMatrix` γ of vectors of the lattice h_cΛ₀ that
are adelic combinations of rational vectors orthogonal to X and γX. -/
def HasIntegralLifts (γ : S.G E) m := ∃ ρ, ∃ (_ : Fintype ρ) (t : Matrix 𝔰.BesselIndex ρ E) (w :
  Matrix ρ τ (𝔸f E)), (isotropicFramePair γ)ᴴ * S.ratGram * t = 0 ∧
  IsIntMatrix (Ô E) (S.classCoord c * finAdeleMat t * w) ∧ finAdeleMat (linkMatrix γ * t) * w = m

lemma finrank_link (γ : S.G E) : finrank E (link γ) = 𝔰.k + 1 := by
  obtain ⟨v, ⟨⟩, e⟩ := exists_basis_matrix (link γ)
  have := (vᴴ * S.linkForm).mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (⟨S.linkForm⁻¹ *ᵥ ‹_›ᴴ *ᵥ ·, by simp_all [middleGram, det_neg,
          ← conjTranspose_mul]⟩), (_ : LinearMap.ker _ = link γ)] at this; simp_all [← two_mul]
  ext; rw [mem_link_iff_orthogonal]; simp [← e, star_mulVec_dotProduct]
  simp [star_dotProduct _ (_ *ᵥ _), dotProduct_eq_zero_iff]

lemma gram_classCoordX₀ : (S.classCoordX₀ c)ᴴ * S.latMiddle (𝔸f E) * S.classCoordX₀ c = 1 := by
  simpa [classCoord_eq_fromBlocks,
    splitGram] using! congr(submatrix $(classCoord_conj_splitGram c) 𝔰.indexX₀ 𝔰.indexX₀)

lemma classCoord_gram : (S.classCoord c * finAdeleMat t)ᴴ * (S.latMiddle (𝔸f E)).splitGram *
  (S.classCoord c * finAdeleMat t') = finAdeleMat (tᴴ * S.ratGram * t') := by
    simp [map_splitGram_ratMiddle, ← classCoord_conj_splitGram c]

lemma linkMetric_posDef w : (S.linkMetric.map (Φ w)).PosDef :=
  (by simp [linkMetric, middleGram, IsDiag, Pairwise] :
  S.linkMetric.IsDiag).diagonal_diag ▸ by simp [linkMetric, middleGram, map_ofNat, field, Ne.pos]

lemma gram_linkForm_eq_zero_of_le_link [Fintype σ] [Fintype τ]
    {u : Matrix _ σ E} (h : colSpan v ≤ link γ) (h' : colSpan u ≤
  link γ) : vᴴ * S.linkForm * u = 0 := by
  simp; ext; apply mem_link_iff_orthogonal.1 <;> solve_by_elim [Exists.intro, mulVec_single_one]

lemma det_gram_linkMetric_ne_zero [Fintype τ] : HasLeftInv v → (vᴴ * S.linkMetric * v).det ≠ 0
  | ⟨_, h⟩ => by apply_fun Φ ofNonempty; simpa [RingHom.map_det, map_conjTranspose] using
    ((linkMetric_posDef _).conjTranspose_mul_mul_same
    (HasLeftInv.mulVec_injective ⟨_, by simpa using congr(Matrix.map $h (Φ _))⟩)).det_pos.ne'

omit [CMType E] in
lemma card_eq_finrank_colSpan [Fintype σ] [Fintype τ]
    {v : Matrix σ τ E} (h : HasLeftInv v) : card τ =
  finrank E (colSpan v) := by simp [v.mulVecLin.finrank_range_of_inj h.mulVec_injective]

lemma gram_linkMatrix_mul {t : Matrix 𝔰.BesselIndex σ E} {t' : Matrix 𝔰.BesselIndex τ E} (h :
  (isotropicFramePair γ)ᴴ * S.ratGram * t = 0) (h' : (isotropicFramePair γ')ᴴ * S.ratGram * t' = 0)
  (a c : E) : (linkMatrix γ * t)ᴴ * (a • S.ratMiddle E).fromBlocks 0 0 (-c • S.ratMiddle E) *
  (linkMatrix γ' * t') =
  a • (tᴴ * S.ratGram * t') - c • (tᴴ * S.ratGram * ((γ * γ'⁻¹).1.1 * t')) := by
  ext i j; obtain ⟨⟩ := isotropicFramePair_mulVec_eq_zero_iff.1 congr($hᵀ i),
    isotropicFramePair_mulVec_eq_zero_iff.1 congr($h'ᵀ j)
  show star (_ *ᵥ _) ᵥ* _ ⬝ᵥ _ *ᵥ _ = a * _ ᵥ* _ ⬝ᵥ _ - c * star (t · i) ᵥ* _ ⬝ᵥ _ *ᵥ _
  simp_all [↓← dotProduct_mulVec, ↓← U.form_mulVec_mulVec γ⁻¹ (t · i), ↓splitGram_mulVec,
    fromBlocks_mulVec, neg_mulVec, dotProduct, mul_add, Finset.mul_sum]; grind

lemma classCoord_mul_framePair {c} : S.classCoord c * finAdeleMat (framePair γ) =
  framePair (S.termPosition c c' γ) := by
  simp [← ext_iff, ↓frameImage_termPosition, classCoord_eq_fromBlocks, forall_fin_succ']

variable {c} {γ : S.G E}

lemma classCoord_mul_isotropicFramePair : S.classCoord c * finAdeleMat (isotropicFramePair γ) =
  isotropicFramePair (S.termPosition c c' γ) := congr(submatrix $classCoord_mul_framePair id _)

lemma isIntMatrix_framePair {k : T.G} {O} : IsIntMatrix O k.1.1 → IsIntMatrix O (framePair k) :=
  (by simp [IsIntMatrix, ite_mem, · _])

end

/-- Let k ∈ K have an agreeing reduction s with `Filling.FixesNormAtLeast` s x (x is a number), and
let two
integral forms vanish on X and kX. If the determinant δ of their pairings with z and kz is an idele,
then x ≤ [δ] = `genIndex` δ.

Here X is spanned by e₁, …, e_ϱ.

Agreeing characters force shared vectors up the flag. -/
lemma le_genIndex_det_of_fixesNormAtLeast [StablyUnram E] {k x} (s :
  S'.Agrees (S'.reduction k)) {t : Matrix 𝔰.BesselIndex τ' _} {P} (ht : IsIntMatrix (Ô E) t)
  (i : (framePair k.1)ᴴ * t = P) (z : P.submatrix (.map castSucc castSucc) id = 0) (ρ :
  τ' ≃ Unit ⊕ Unit) : let g := .map (fun _ ↦ 𝔰.top) (fun _ ↦ 𝔰.top) ∘ ρ
  IsUnit (P.submatrix g id).det → S'.FixesNormAtLeast (S'.reduction k) x → x ≤
    genIndex (P.submatrix g id).det := by
  intro g u ⟨A, F, G⟩; choose l H using S'.exists_reduceAboveG_eq
  let Q := @of _ _ (Ô E) (⟨_, ht.isInt_conjTranspose · ·⟩) * (frameImage 1).fromCols
    (frameImage (intGL.map (.id _) ⟨_, k.2⟩).1)
  obtain rfl : (Q.map (↑))ᴴ = P := by aesop (add simp [mul_apply, star_mul])
  have p := genIndex_pos u.unit; simp [← ext_iff, ← conjTranspose_submatrix] at z u p ⊢
  erw [submatrix_map, ← (Ô E).subtype.map_det,
    genIndex_eq_card isOpen_Ô isCompact_Ô (by simp) u] at *
  refine mod_cast ((F.trans_eq (by simp [Nat.card_pi, card_resField_eq_levelPrime,
    ← A.prod_attach])).trans (Nat.card_congr ((RingHom.pi fun w : A ↦ S'.reduceAboveG
    w.1).quotientKerEquivOfSurjective fun t ↦ ⟨l fun w ↦ dite _ (t ⟨w, ·⟩) fun _ ↦ 0, by
    ext; simp [H]⟩).1).ge).trans (@index_antitone _ _ _ _ ((Ideal.span_singleton_le_iff_mem _).2
    (funext fun ⟨⟨p, b⟩, h⟩ ↦ ((S'.reduceAboveG _).map_det _).trans (by_contra fun n ↦ (G _ h).elim
    fun x h ↦ x.2 (funext ((wellFounded_gt.fix fun a ih x y h ↦ ?_ : ∀ a x y, frameImage 1 *ᵥ x =
    frameImage (intGL.map (S'.reduceAboveG _) ⟨_, k.2⟩).1 *ᵥ y → x a = 0) · _ x (by simpa [←
    intGL_map_reduceAboveG, mul_inclMatrix, Units.smul_def] using! h.symm)))))) ⟨mod_cast p.ne'⟩)
  replace n := by simpa [g, funext_iff, reindex_equiv ρ.symm] using eq_zero_of_mulVec_eq_zero (v :=
    (x ⊕ᵥ -y) ∘ g) n (by simpa [funext_iff, mulVec_eq_sum, sum_univ_castSucc, reindex_equiv ρ.symm,
    g, z] using (by simp [Q, ← mulVec_mulVec, ← submatrix_map, mulVec_neg, add_neg_eq_zero, h]; rfl
    : Q.map (S'.reduceAboveG _) *ᵥ (x ⊕ᵥ -y) = 0))
  cases' a using lastCases with a; simp [n]
  let o t := l (Pi.single (p, b) t) - l 0
  have G q t : S'.reduceAboveG (q, b) (star (o t)) = 0 := by cases b <;> simp_all [o, reduceAboveG]
  refine (exists_mulVec_eq_of_annihilator _ _ (.Iio a.succ) (.Iio 𝔰.top) (cons 0 (init x))
    (cons 0 (init y)) fun m c c' ↦ ?_
    ).elim fun x ⟨_, h, e, _⟩ ↦ (e a.succ (by simp) ▸ ih _ (by simp) _ _ h :)
  let A M x := o ∘ (m ᵥ* frameImage M) ⬝ᵥ cons 0 (init (o ∘ x))
  have' := (S'.inv_gIdele_smul_mem_iff (A 1 x - A _ y)).1
    ((S'.forall_selfDualChar_mul_eq_one_iff _).1 fun r ↦ _) (p, b)
  simpa [A, dotProduct, sum_univ_succ, init, o, H] using this
  -- the Eichler map over Ô of a multiple of a vector of the flag and a form
  have V a x M (hx : ∀ b ≥ a, x b = 0) (c : ∀ b < a, (m ᵥ* frameImage M) b = 0) : ∃ u :
    S'.latStabilizer, u.1 ∈ besselU ∧ simpleRootSum u.1 = r * A M x ∧
    ∀ q, let f := S'.reduceAboveG (q, b); (intGL.map f ⟨u, u.2⟩).1 =
      1 + f r • vecMulVec (frameImage 1 *ᵥ f ∘ o ∘ x) (f ∘ o ∘ (m ᵥ* M)) := by
    obtain ⟨⟨v, Z⟩, _, _, τ, i, _, _, e⟩ :=
      exists_star_vecMul_eq (S'.latMiddle _).splitGram (o ∘ (m ᵥ* M)), exists_skew_unit (A := 𝔸f E)
    have : TraceOne (Ô E) := ⟨⟨τ, i⟩, Subtype.ext e⟩
    have ⟨u, n, w, e⟩ :=
      exists_mem_besselU_eq_eichlerMap a (o ∘ x) r Z (by simp [o, hx · ·]) (by simp_all [o, vecMul])
    use ⟨U.map _ (by simp) (map_splitGram_latMiddle _) u, _, rfl⟩, n.map_mem_unitriangularOn
      _, by simpa [simpleRootSum] using! congr($w.1), fun _ ↦ congr(Matrix.map $e _).trans
      (by simp [eichlerMap, *, vecMulVec_apply, apply_ite, entrywise, vecMul])
  obtain ⟨⟨u, hu, w, e⟩, u', hu', _⟩ := V _ x 1 (ih · · x y h) c, V _ y _ (by simp [n]) c'
  have := s _ _ hu hu' ?_; simpa [unipotentChar, *, Units.smul_def, mul_sub, mul_left_comm r.1,
    AddChar.map_sub_eq_div, (S'.selfDualChar.val_isUnit _).div_eq_one_iff_eq]
  funext j v; apply (S'.idOrInvAdjoint b).injective; obtain rfl | _ := eq_or_ne ⟨j,
    v⟩ p <;> simp [add_mul, o, *, ← intGL_map_reduceAboveG, Units.ext_iff, comp_def, mul_add,
    vecMulVec_mul, mul_vecMulVec, ← Pi.zero_def]
  erw [mul_inclMatrix]

variable {S : Filling E 𝔰} [StablyUnram E] {α ι E' : Type _} [Fintype ι] {A : Set α} [Field E']
  [NumberField E']

section

open MatMul

attribute [local simp] classCoord finAdeleMat_conjTranspose map_splitGram_ratMiddle
  IsHermUnit.conjTranspose_eq Matrix.mul_apply funext_iff inclMatrix

/-- Let x have columns e_{p(b)}, let u have columns in h_cΛ₀ orthogonal to all e_a with a ≤ max
p, and s be integral skew-hermitian. Then 1 + g(x u*J − (u + x(τ u*Ju − s)) x*J) lies in
𝖴_c(g) for some τ ∈ E, and fixes the frame if u is orthogonal to it. -/
lemma exists_mem_classUnip c {m} [Fintype m] (p : m → _) (u : Matrix 𝔰.BesselIndex m E) s {x}
    (h₀ : ∀ a b b', a ≤ p b' → u (eStar a) b = 0) (h : sᴴ = -s) (hu :
  IsIntMatrix (Ô E) (S.classCoord c * finAdeleMat u)) (hs : IsIntMatrix (Ô E) (finAdeleMat s)) (e :
  inclMatrix E (.inl <| p · : _ → 𝔰.BesselIndex) = x) : ∃ γ ∈ S.classUnip c, ((∀ b a,
  (uᴴ * S.ratGram) b (𝔰.besselFrame a) = 0) → γ ∈ S.classUnip₀ c) ∧ ∃ τ : E, γ.1.1 = 1 + (S.g :
  E) • (x * (uᴴ * S.ratGram) - (u + x * (τ • (uᴴ * S.ratGram * u) - s)) * (xᴴ * S.ratGram)) := by
  have ⟨_, τ, _, _, hτ, _⟩ := ‹StablyUnram E›.exists_i_c₀
  have ⟨y, X, w⟩ : (xᴴ * S.ratGram * u, xᴴ * S.ratGram * x) = 0 ∧ IsIntMatrix (Ô E) (S.classCoord
    c * finAdeleMat x) ∧ ∀ b a, (xᴴ * S.ratGram) b (𝔰.besselFrame a) = 0 := by simp [← e, ← ext_iff,
    splitGram, forall_fin_succ', IsIntMatrix, ↓classCoord_eq_fromBlocks, ite_mem]; tauto
  refine ⟨U.of IsHermUnit.isUnit _ ?_, ?k, fun n ↦
    ⟨?k, ?k.1, fun _ ↦ forall_mem_range.2 (by simp [*])⟩, S.g * τ, rfl⟩
  simp [h, ← coe_star_ringOfIntegers, eq_sub_of_add_eq' hτ, by
    simpa using fun v ↦ congr(([v, uᴴ], $y.1 * v, $y.2 * v, $y.1ᴴ * v))]
  module
  refine ⟨mem_besselU.2 ?_, S.principalLevel_eq_unitaryLevel.ge
    (S.isUnimodular_latMiddle.splitGram.mem_unitaryLevel (x := termPosition ..) S.gIdele_mem ?_)⟩
  simp [↓U.val_of_coe, ← e, splitGram, FI.level]
  grind [Finset.sum_eq_zero, star_zero]
  convert ((X.mul hu.isInt_conjTranspose).sub ((hu.add (X.mul (((hu.isInt_conjTranspose.mul
    (S.isUnimodular_latMiddle.splitGram.isIntMatrix.mul hu)).smul (coe_mem_Ô (S.g * τ :))).sub
    hs))).mul X.isInt_conjTranspose)).mul S.isUnimodular_latMiddle.splitGram.isIntMatrix
  simp [↓inv_smul_eq_iff, coe_termPosition, Matrix.map_add, Matrix.map_sub, gIdele, Units.smul_def,
    ← classCoord_conj_splitGram c]

lemma exists_eichler_classUnip c a {l} (h : ∀ j, ¬IsFreeEntry (a, j) → l j = 0) (k :
  algebraMap .. ∘ l ᵥ* (classBasis c).1 ∈ intVectors (Ô E) _) (s : skewAdjoint (𝓞 E)) : ∃ γ :
  S.classUnip c, ∀ b j, j ≠ eStar a ∨ l = 0 → γ.1.1 (.inl
  b) j = ite (.inl b = j) 1 0 + S.g * ite (b = a) (l j + ite (j = eStar a) s.1.val 0) 0 := by
  obtain ⟨u, rfl⟩ := S.ratGram.vecMul_surjective_iff_isUnit.2 IsHermUnit.isUnit l
  have ⟨_, h, _, _, e⟩ := exists_mem_classUnip c ![a] (of ![u])ᴴ !![s.1] (by aesop)
    (Matrix.ext (by simp [← coe_star_ringOfIntegers]))
    (S.isUnimodular_latMiddle.splitGram.isUnit_det_and_isIntMatrix_inv.rec fun _
    i ↦ by simpa [← classCoord_conj_splitGram c, *, -cons_mul] using
    (IsIntMatrix.mul (M := finAdeleMat (of ![u] * S.ratGram) * (classBasis c).1) (fun 0 ↦
    k) i).isInt_conjTranspose) (fun 0 0 ↦ coe_mem_Ô _) rfl
  use ⟨_, h⟩, by simp [e, splitGram, vecMul_eq_sum]; clear * -; aesop

end

/-- Colour A with at most N colours so that elements of one colour are R-related. If every
nonempty subset of A of pairwise R-related elements has total weight at most x, then A has
total weight at most Nx. -/
lemma tsum_le_of_encard_range_le {β} {A : Set α} {R : α → α → Prop} {N x : ℝ≥0∞} {w : α → ℝ≥0∞} (φ :
  A → β) (h : encard (range φ) ≤ N) (r : ∀ a b, φ a = φ b → R a b) (H : ∀ᵉ (B ⊆ A) (_ ∈ B),
  (∀ a ∈ B, ∀ b ∈ B, R a b) → ∑' a : B, w a ≤ x) : ∑' a : A, w a ≤ N * x := by
  grw [← tsum_fiberwise _ (rangeFactorization φ), ← h, ← tsum_set_const, ENNReal.tsum_le_tsum]
  rintro ⟨_, b, ⟨⟩⟩; grw [← tsum_image, H _ _ b] <;> grind [rangeFactorization, InjOn]

lemma tsum_le_of_colouring {β} [AddCommGroup β] (f : α → ι → β) {K K'} (k : relIndex K K' ≠ 0) (h :
  ∀ᵉ (a ∈ A) (i), f a i ∈ K') (w : α → ℝ≥0∞) x : (∀ᵉ (B ⊆ A) (_ ∈ B), (∀ᵉ (a ∈ B) (b ∈ B) (i), f a
  i - f b i ∈ K) → ∑' a : B, w a ≤ x) → ∑' a : A, w a ≤ .ofReal (K.relIndex K' ^ card ι) * x := by
  have := fintypeOfIndexNeZero k
  apply tsum_le_of_encard_range_le (QuotientAddGroup.mk' (K.addSubgroupOf _) ⟨_, h _ ·.2 ·⟩); grw
    [encard_le_card]
  repeat simp [relIndex, index, funext_iff, QuotientAddGroup.eq_iff_sub_mem, mem_addSubgroupOf]

/-- If f maps A injectively to vectors in E^ι whose entries are algebraic integers of absolute
value at most r at every infinite place, then A has at most (1 + 2r)^(2|ι|m) elements, m the
number of infinite places. -/
lemma encard_integral_le [PlaceEmbedding E'] {r} (f : α → ι → E') (o : 0 ≤ r)
    (h : ∀ᵉ (a ∈ A) (i), IsIntegral ℤ (f a i) ∧ ∀ v, ‖Φ v (f a i)‖ ≤ r) (j : InjOn f A) :
    A.encard ≤ ENNReal.ofReal ((1 + 2 * r) ^ (card ι * numInfPlaces E' * 2)) := by
  grw [encard_le_of_separated (f := fun x (i, v) ↦ Φ v (f x i)) _root_.one_pos o fun _ a _ b ↦ by
    simpa [← not_lt, pi_norm_lt_iff] using (j a b ∘ funext ∘ forall_imp fun _ ↦ eq_of_sub_eq_zero ∘
      eq_zero_of_norm_Φ (by grind [IsIntegral.sub])).mt] <;> simp_all [pi_norm_le_iff_of_nonneg]

variable [IsCMField E'] [StablyUnram E'] {c : (𝔸f E')ˣ} (j : Fin (𝔰.ϱ + 2))

lemma submoduleIndex_smul_intVectors (hc : ↑c ∈ Ô E') : submoduleIndex (c • intVectors (Ô E') ι)
  (intVectors ..) = genIndex c.1 ^ card ι := by simpa [colLattice,
  c.smul_def] using! submoduleIndex_colLattice_intVectors (n := ι) (M := c • 1) (.smul hc .one)

lemma submoduleIndex_smul_ne_zero (hc : ↑c ∈ Ô E') :
  submoduleIndex (c • intVectors (Ô E') ι) (intVectors ..) ≠ 0 := mod_cast
  (submoduleIndex_smul_intVectors hc).trans_ne (pow_pos (genIndex_pos c) _).ne'

/-- The set of indices a in {0,…,ϱ−1} with a < j. -/
abbrev IndexBelow := {a : Fin 𝔰.ϱ // a.1 < j}

variable {E : Type} [Field E] [CMType E] [StablyUnram E] {𝔰 : Shape} (S : Filling E 𝔰)
  (c : S.Classes) {R : Type*} (j : Fin (𝔰.ϱ + 2)) (Z : Matrix _ (Fin (𝔰.ϱ + 1)) R) [CommRing R]
  (c' γ γ') (k : S.GFin)

/-- The submatrix of the first ϱ rows of Z, with all columns; for Z = Z(γ), the products of γf
with the basis of X. -/
abbrev xRows {𝔰 : Shape} {R : Type*} (Z : Matrix _ (Fin (𝔰.ϱ + 1)) R) :=
  Z.submatrix (@castSucc 𝔰.ϱ) id

/-- The square matrix whose rows a < j are those of Z and whose other rows are those of the
identity matrix. -/
def paddedLeading := of fun a b ↦ ite (a.1 < ↑j) (Z a b) (ite (a = b) 1 0)

@[simp] lemma det_paddedLeading {j Z} : (@paddedLeading 𝔰 R j Z _).det = leadingMinor Z j := by
  erw [paddedLeading, leadingMinor,
    (Z.submatrix (↑) (↑)).det_submatrix_equiv_self (castLEquiv j.is_le)]
  convert! Z.det_piecewise_one_eq_submatrix_det {a | a.1 < j} <;> aesop

/-- For a matrix γ on V, the submatrix of rows in the X₀⊕Ez block and columns at the frame
indices: the middle coordinates of γf. -/
abbrev frameMiddle γ := (@frameImage R 𝔰 γ).toRows₂.toRows₁

/-- For a class c, the function sending a subspace V of X₀ to the discriminant
`Filling.sublatticeDisc` of L_c ∩ V, L_c the part in X₀ of the lattice of c. -/
def latticeDisc := sublatticeDisc (S.gram_classCoordX₀ c)

/-- The index [M : M ∩ aM'] (0 if infinite): M consists of the (h(kf_l, y))_l for integral y in
h_c⁻¹(V ⊗ 𝔸_f), V ⊂ X₀; M' is spanned by the (h(kf_l, e_i))_l. -/
def frameValueIndex (a : (𝔸f E)ˣ) V := submoduleIndex (a • colLattice _
  (xRows ((S.latMiddle _).frameGram k))ᴴ) (colLattice (Ô E) ((frameMiddle k.1.1)ᴴ * S.latMiddle
  (𝔸f E) * (S.classCoordX₀ c * (sublatticeBasis (gram_classCoordX₀ c) V).1)))

/-- For j and adelic k, the index of the Ô-span of the conjugated first min(j,ϱ) rows of Z(k) in the
Ô-span of the conjugated first ϱ rows (0 if infinite). -/
def xRowsIndex := submoduleIndex (colLattice (Ô E) (((S.latMiddle _).frameGram k).submatrix
  (·.1.castSucc : IndexBelow j → _) id)ᴴ) (colLattice _ (xRows ((S.latMiddle _).frameGram k))ᴴ)

variable (c : S.Classes) (c' : S.Classes) (γ : ↥(S.G E)) (γ₁ : ↥(S.G E)) {S₁ : Filling E 𝔰}
  {j' : Fin (𝔰.ϱ + 2)} {γ₂ : ↥(S₁.G E)}

/-- The index of the Ô-span of the e_a and ke_a in Λ₀ ∩ (X + kX), all adelic. -/
def saturationIndex := submoduleIndex (colLattice (Ô E) (isotropicFramePair k))
  (intVectors .. ⊓ (colSpan (isotropicFramePair k)).restrictScalars _)

/-- The product disc(L_c ∩ T)·o·𝔡, where T = `commonLink` γ γ', k = h_c⁻¹γh_c', o =
`Filling.frameValueIndex` for k, a = 1, V = T, and 𝔡 = `Filling.saturationIndex` k. -/
def pairInvariant c c' γ γ' := S.latticeDisc c (commonLink γ γ') * S.frameValueIndex c
  (S.termPosition c c' γ) 1 (commonLink γ γ') * S.saturationIndex (S.termPosition c c' γ)

/-- For a class c and a pair p = (c',γ), the finite adelic element h_c⁻¹γh_{c'}. -/
abbrev termElem (p : S.Classes × S.G E) := S.termPosition c p.1 p.2

/-- For j ≤ ϱ+1 and γ, the absolute norm to ℚ of the leading minor D_j of Z(γ), divided by
N^{2f} when j = ϱ+1. -/
def minorNorm := |(Algebra.norm ℚ (leadingMinor (S.frameProducts γ₁) j) : ℝ)| / S.N ^
  (2 * (j - 𝔰.ϱ) * numInfPlaces E)

/-- The gauge 𝗀* = max(∏_v|𝗀(γ)|_v, N^f·`Filling.minorNorm` j γ)/(i(k)·i(k⁻¹)), where k = h_c⁻¹γh_c'
and i = `Filling.xRowsIndex` j. -/
def classGauge := (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) /
  (S.xRowsIndex j (S.termPosition c c' γ) * S.xRowsIndex j (S.termPosition c c' γ)⁻¹)

/-- γ is near (`Filling.IsNear`) and is the chosen representative of its double coset 𝖴⁰_c(g) γ
𝖴⁰_c'(g). -/
def IsNearRep := S.IsNear γ ∧ (DoubleCoset.mk (S.classUnip₀ c) (S.classUnip₀ c') γ).out = γ

/-- For p = (c', γ) and a function n with natural values, the weight n(h_c⁻¹γh_c')^(−k), k =
|κ|, in [0, ∞], with the inverse of 0 read as 0. -/
def invPowWeight (n : _ → ℕ) p := ENNReal.ofReal (n (S.termElem c p) ^ 𝔰.k)⁻¹

/-- The weight M_i⁻¹·disc(L_c ∩ V)^(−k−1)·([Ô : gÔ]^min(j,ϱ)·o)^(−k)·𝔡^(−k), with M_i =
`Filling.countWeight` i, o = `Filling.frameValueIndex` (a = 1) at the term p, 𝔡 =
`Filling.saturationIndex` at the term p'. -/
def termWeight i c (p p' : S.Classes × S.G E) V :=
  .ofReal (S.countWeight i)⁻¹ * (.ofReal (S.latticeDisc c V ^ (𝔰.k + 1))⁻¹ *
  (S.invPowWeight c (submoduleIndex (S.gIdele • intVectors (Ô E) (IndexBelow j)) (intVectors ..) *
  S.frameValueIndex c · 1 V) p * S.invPowWeight c S.saturationIndex p'))

/-- For congruent kept terms γ, γ' (`Filling.IsNearRep`) of level j, the weight `Filling.termWeight`
of (γ, γ') for the space T° = `commonLink` γ γ' and its codimension; otherwise 0. -/
def pairWeight c c' γ γ' := ite (S.CongruentTerms c c' γ γ' ∧
  (S.IsNearRep c c' γ ∧ S.HasLevel j γ) ∧ S.IsNearRep c c' γ' ∧ S.HasLevel
  j γ') (S.termWeight j (𝔰.k - finrank E (commonLink γ γ')) c (c', γ) (c', γ') (commonLink γ γ')) 0

/-- For p = (c', γ): `Filling.IsNearRep` holds, γ has level j, and γ lies over (c, s, c') for some s
with S̄-component t in a fixed decomposition 𝖦 ≃ 𝖦/S̄ × S̄. -/
def IsLabelledTerm (t : S.reducedImage besselS) (p : S.Classes × S.G E) :=
  (S.IsNearRep c p.1 p.2 ∧ S.HasLevel j p.2) ∧ ∃ s, p.2 ∈ S.termsOver c
  s p.1 ∧ (Subgroup.groupEquivQuotientProdSubgroup s).2 = t

section

omit [StablyUnram E]

lemma HasLevel.minorNorm_pos (h : S₁.HasLevel j' γ₂) : 0 < S₁.minorNorm j' γ₂ := by simp [minorNorm,
  h.2, zero_lt_iff]

lemma HasLevel.inv {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ} (h : S.HasLevel j γ) : S.HasLevel j
  γ⁻¹ := h.imp .inv (by simp [leadingMinor, frameDisc, ← conjTranspose_submatrix, mul_comm])

lemma HasLevel.paddedLeading_mul_inv (h : S₁.HasLevel j' γ₂) : paddedLeading j'
  (S₁.frameProducts γ₂) * (paddedLeading j' (S₁.frameProducts γ₂))⁻¹ = 1 := by simp [h.2]

/-- Shared vectors: if γ has level j and b ≥ j (indices from 0), the combination of the frame γf
given by column b of the inverse of `Filling.paddedLeading` j Z(γ) lies in the span of the frame
f. -/
lemma HasLevel.exists_shared_frame_vector (h : S₁.HasLevel j' γ₂) {b} (h₀ : ↑j' ≤ b.1) : ∃ w,
  frameImage 1 *ᵥ w = frameImage γ₂.1.1 *ᵥ col (paddedLeading j' (S₁.frameProducts γ₂))⁻¹ b :=
  (exists_frameImage_eq_of_isNormalForm h.1 (col 1 b)).imp fun w ⟨x, s, r⟩ ↦ by simp [r,
  ← mulVec_single_one, h.2, show Pi.single b 1 = paddedLeading j' (S₁.frameProducts γ₂) *ᵥ x by
  have := frameProducts_mulVec_of_frameImage_eq r; simp_all [paddedLeading, mulVec_eq_sum,
    funext_iff]; grind]

end

/-- Let the columns of n be orthogonal to both frames f and kf. Then the adjoint of the first ϱ
rows of Z(k), times minus the e_a-coordinates of n, equals the matrix of T-products of the
middle parts of kf and of n. -/
lemma xRows_conjTranspose_mul_eq {R σ} [CommRing R] [StarRing R] {𝔰 : Shape} {T : 𝔰.Form R} {k :
  T.G} {n : Matrix 𝔰.BesselIndex σ R} : (isotropicFramePair k)ᴴ * T.splitGram * n = 0 →
  zFormPair T * linkMatrix k * n = 0 → (xRows (T.frameGram k))ᴴ * -n.toRows₁ = (frameMiddle
  k.1.1)ᴴ * T * n.toRows₂.toRows₁ := by simp +contextual [← framePair_last_eq_zFormPair_mul,
  ← ext_iff, mul_apply, splitGram, frameGram, forall_fin_succ', neg_eq_iff_add_eq_zero]


attribute [-simp] AddSubgroupClass.coe_norm Set.indicator_of_mem Set.indicator_of_notMem

attribute [local cases_eliminator] lastCases

attribute [local simp] boxedPoints classBasis besselLatticeBasis single_apply entrywise funext_iff
  toBesselH mul_assoc pi_norm_le_iff_of_nonempty

variable {E : Type} [Field E] [CMType E] [StablyUnram E] {𝔰 : Shape} {S : Filling E 𝔰}
  [S.IsAdmissible] {γ γ' : S.G E} (c : S.Classes) (y : NumberField.InfinitePlace E → ↥𝔰.G₁)

omit [StablyUnram E] [S.IsAdmissible] in
lemma frameVector_sub_eq_sum (h : (frameImage γ.1.1).toRows₂ = toRows₂ (frameImage γ')) y v b :
  frameVector ((S.ratToInf γ v)⁻¹ * y) b - frameVector ((S.ratToInf γ' v)⁻¹ * y) b = ∑ a, (Φ v
  ((γ.1.1 - γ') (.inl a) (𝔰.besselFrame b)) * (S.basisScale v (𝔰.besselFrame b) / S.basisScale v
  (𝔰.besselFrame a.castSucc))) • frameVector y
  a.castSucc := by ext; simp_all [frameVector, sub_mul]; grind

open Norms.L2Operator

/-- Under the standing hypotheses, a weight in the sense of `Filling.IsBoxPartition` exists for the
class c: the function chosen by Hilbert's ε has all the properties required there. -/
lemma isBoxPartition_epsilon :
  S.IsBoxPartition c (epsilon (S.IsBoxPartition c)) := have := S.thousand_le_b
  have m (u : S.classUnip c) := u.2.1.ratToInf_mem_unitriangularOn
  have R {t : _ → _} (ht : ∀ v, t v ∈ besselU) (s : Finset (_ × _)) : ∃ u : S.classUnip c, ∀ᵉ (v)
    (p ∈ s), ‖frameMatrix (t v * S.ratToInf u v) p.1 p.2‖ ≤ S.b ^ (60 * 𝔰.ϱ + 91) :=
    s.induction_on_min_value (·.1) (by simp) fun ⟨k, b⟩ s n hs ⟨w, H⟩ ↦ by
    have T v := frameMatrix_unitriangular (mul_mem (ht v) (m w v))
    if h : b ≤ k then use w; simp_all [apply_ite norm]; bound else
      cases' k with k; grind
      choose x o hx using exists_rat_near_of_mem_differentIdeal (mod_cast S.varpi_ne_zero)
        (by simp [S.span_ϖ]) _ 0; simp at T o
      choose u e using exists_eichler_classUnip c k (l :=
        (if · = 𝔰.besselFrame b then -x * S.N else 0)) (by clear * - h; cases b <;> aesop)
        (by cases b <;> simp [intVectors, vecMul, ite_mem, mul_mem, o, apply_ite (algebraMap ..),
        (_ * star S.piBar).mul_inv_of_eq S.piBar_mul_star, -_root_.mul_inv_rev]) 0
      use w * u, fun v ↦ ?_
      let r := S.g * S.N * (S.basisScale v (𝔰.besselFrame b) / S.basisScale v (.inl k))
      erw [map_mul, ← mul_assoc,
        frameMatrix_mul (m u v), show frameMatrix (S.ratToInf u v) = 1 - .single k.castSucc b
        (r * Φ v x) by cases b <;> simp [forall_fin_succ', r, frameMatrix, apply_ite (Φ v),
        apply_inr_of_mem_besselU u.2.1, e] <;> clear * - <;> grind [basisScale_ne_zero], mul_sub]
      simp [ite_and, T] at H ⊢; use ?_, by grind
      grw [← mul_div_cancel₀ (frameMatrix ..), ← mul_sub, norm_mul, hx v,
        S.f_le_b] <;> simp [r, ↓basisScale_besselFrame, basisScale]
      grw [div_le_one_of_le₀ (by gcongr <;> grind [one_le_abs_kappa]), levelPrime_le, levelPrime_le,
        N_le, IsAdmissible.ϖ_le]
      ring_nf; field_simp; repeat bound
  let θ := MonoidHom.toHomUnits ⟨⟨fun (u : S.classUnip c) v ↦ frameMatrix (S.ratToInf u v), by
    simp [frameMatrix, submatrix_one, besselFrame_injective]⟩, by simp [← frameMatrix_mul (m _ _)]⟩
  have := (mk'_surjective θ.ker).countable
  let I y := {q | ∀ v b, ‖∑ a, (kerLift θ q).1 v a b • frameVector (y v) a‖ ≤
    S.b ^ (60 * 𝔰.ϱ + 92) * besselSize (y v)}.indicator (M := ℝ≥0∞) 1
  have _ q : Measurable (I · q) := by apply Measurable.ite <;> measurability
  epsilon_spec ⟨(I · 1) * (∑' q, I · q)⁻¹, by fun_prop, fun y v h r a ↦ by
    simp_all [I]; grw [h.1, r, boxSize, ← pow_add]; gcongr <;> nlinarith [S.ϱ_le], fun y a ha ↦ by
  have f u y v b : ∑ a, (θ u).1 v a b • frameVector y a =
    frameVector ((S.ratToInf u v)⁻¹ * y) b := by simp [frameVector_eq_sum b (m u v), θ]
  rw [show Subgroup.subgroupOf .. = θ.ker by ext u; simp_all [θ, classUnip₀, frameMatrix,
    Subgroup.mem_inf.1 u.2, mem_besselU0_iff, apply_ite, map_eq_one_iff, RingHom.injective]] at ha
  simp [show ∀ (u : S.classUnip c) q, I (S.ratToInf u * y) q = I y (u⁻¹ * q) by simp [forall_mk, I,
    f, indicator, ← mk_mul, -map_mul, -mk_inv, S.ratToInf.map_mul,
    besselSize_besselS_mul (mem_unitriGroup_of_mem_besselU (m _ _))], ha, -mk_inv,
    ← (cosetProdEquiv θ.ker).tsum_eq, (mul_right_injective _).tsum_eq (f := I y), ← image_univ]
  choose w hw r using (exists_norm_le_of_besselSize_le (y := y ·) le_rfl)
  apply ENNReal.mul_inv_cancel _ (mt (tsum_subtype ..).trans _) <;> simp
  exacts [(R hw .univ).imp' (↑) fun u H v b ↦ by grw [kerLift_mk, f, pow_succ', frameVector_eq_sum b
    (mul_mem (hw v) (m _ _)), norm_sum_le, norm_smul_le, H v (_, b), norm_frameVector_le, ← r,
    ← succ_le_b] <;> simp, ((S.finite_classUnip_inter_compact c _ (isCompact_univ_pi fun v ↦
    (isCompact_closedBall 0 _).matrix)).preimage (Units.val_injective.comp (kerLift_injective
    θ)).injOn).subset (forall_mk.2 fun u h ↦ ⟨fun v _ a b ↦ by simpa [besselFrame_injective.eq_iff]
    using! ((norm_sum_le_mul_norm_sum_frameVector (s := 1) (·) _ (𝔰.besselFrame a)).trans (by grw
    [h v b])), u, rfl⟩)], fun _ ↦ div_le_of_le_mul (by simp [ENNReal.le_tsum]), by simp_all [I,
    frameVector_mul, besselSize_besselS_mul (besselU0_sup_besselH_le_besselS _)]⟩

lemma tsum_classCutoff_eq_one : ∑' u : S.classUnip c, S.classCutoff c (S.ratToInf u * y) = 1 := by
  simp [classCutoff, (isBoxPartition_epsilon c).2, (S.exists_cutoff_classUnip _).choose_spec.2.1]

/-- Frame count: let w_p ≤ β_{k_p}(δ_p⁻¹y')·x, with p ↦ (k_p, δ_p) injective. If, where w_p ≠ 0,
γ_p ∈ δ_p𝖴_{k_p}(g) lies over (c,s,k_p), γ_p⁻¹y ∈ `Filling.boxedPoints`, and the frames y⁻¹γ_pf
differ in a real subspace V, then ∑w_p ≤ b^(6(ϱ+1)² dim V)·x. -/
lemma tsum_classCutoff_box_le {c s α y y' x} {k γ δ w : α → _} (hi : ∀ {p q}, k p = k q → δ p = δ
  q → p = q) (H : ∀ p ∈ w.support, γ p ∈ S.termsOver c s (k p) ∧ (δ p)⁻¹ * γ p ∈ S.classUnip (k p) ∧
  (S.ratToInf (γ p))⁻¹ * y ∈ S.boxedPoints ∧ w p ≤ S.classCutoff (k p) ((S.ratToInf (δ p))⁻¹ * y') *
  x) {V : Submodule ℝ _} (hV : let F p v := frameVector ((S.ratToInf (γ p) v)⁻¹ * y v); ∀ᵉ
    (p ∈ w.support) (q ∈ w.support), F p - F q ∈ V) :
  ∑' p, w p ≤ .ofReal (S.b ^ (6 * 𝔰.n ^ 2 * finrank ℝ V)) * x := S.of_size_bounds fun _ _ _ o ↦ by
  intros; rw [← tsum_subtype_support]
  have ⟨r, ε⟩ : 0 < S.boxSize ∧ 0 < S.N * S.boxSize := by simp [boxSize, *]
  generalize w.support = A at *; choose K hδ hB h using Subtype.forall'.1 H
  refine (exists_image_eq_injOn_of_subset_range le_rfl).elim fun u ⟨e, i⟩ ↦
    tsum_le_of_encard_range_le _ (e ▸ i.encard_image ▸ .trans' ?_ (encard_le_of_separated (f :=
    fun p ↦ (⟨_, hV _ (choice ⟨p⟩).2 _ p.2⟩ : V)) (inv_pos.2 ε) (add_pos r r).le (fun p a q b ↦
    Not.imp_symm fun n ↦ i a b (frameImage_inv_mul_eq_iff.1 ?_)) (by simp_all [norm_sub_le_of_le,
    frameBox]))) (K · |> termsOver.eq_and_mem_classUnip₀ <| K ·)
    (R := fun p q ↦ k p = k q ∧ (γ p)⁻¹ * γ q ∈ S.classUnip₀ (k p)) fun B H p a o ↦ by
    grw [← one_mul x, ← tsum_classCutoff_eq_one (k p) (S.ratToInf (γ p)⁻¹ * y'),
      ← tsum_comp_le_tsum_of_injective
      (f := fun q ↦ ⟨_, (o q q.2 p a).1 ▸ mul_mem (hδ ⟨_, H q.2⟩) (o q q.2 p a).2.1⟩)
      fun q r this ↦ Subtype.ext (hi (o _ q.2 _ r.2).1 (by simpa)), ← ENNReal.tsum_mul_right]
    gcongr with q; simpa [o q _ p a] using h ⟨_, H q.2⟩
  grw [pow_mul, N_le, boxSize, ← two_mul, o, o]; simp [← pow_add, ← pow_succ', field]
  grw [one_le_pow₀ ‹_›, ← two_mul, o, ← pow_succ']; gcongr; nlinarith [S.ϱ_le]
  set g := _ * γ q; let F u v := frameVector ((S.ratToInf u v)⁻¹ * ((S.ratToInf (γ p))⁻¹ * y) v)
  have J {f : _ → E} (z : ∀ {s c γ}, γ ∈ S.termsOver _ s c → IsIntegral ℤ (f γ)) a (h : ∀ v, _ ≤ _
    * ‖F g v a - F 1 v a‖) := sub_eq_zero.1 (eq_zero_of_norm_Φ ((@z _ _ g (.mul (.inv (K p))
    (K q))).sub (z (S.classUnip _).one_mem.2)) fun v ↦ (h v).trans_lt
    ((lt_div_iff₀' ε).1 (by simp_all [g, F, pi_norm_lt_iff])))
  suffices _ from Matrix.ext (Sum.rec (WellFoundedGT.fix fun a I b ↦ J (f := (·.1 _ _))
    (by have := termsOver.isIntMatrix_termPosition · (.inl a) (𝔰.besselFrame b); cases b <;>
    simpa [coe_termPosition]) b fun v ↦ by
    choose w hw r using exists_norm_le_of_besselSize_le (hB p v).2
    grw [frameVector_sub_eq_sum (Matrix.ext this),
      ← (div_le_iff₀' _).2 (norm_sum_le_mul_norm_sum_frameVector _ _ (.inl a)),
      r, sum_eq_single a (by clear * - I hw; simp_all [mem_besselU, FI.level]; grind)] <;>
      simp [mem_besselU.1 hw, ↓basisScale_besselFrame, field, ↓Units.norm_pos]
    grw [abs_kappa_le, ← one_le_abs_kappa, ← pow_mul, boxSize, ← S.N_prime.one_le, Nat.sub_le]
    simp [← pow_add]; gcongr; nlinarith [S.ϱ_le]) this)
  have h a b := J (isIntegral_frameProducts · b a) a fun v ↦ by
    grw [mul_assoc, ← (hB p v).1 b, ← norm_inner_J₁_le, map_sub, map_sub, inner_sub_right]
    simp [F, ↓← realFrameGram_eq_inner, ↓realFrameGram_ratToInf, ← mul_sub, ← pow_add,
      field]; bound [S.one_le_abs_kappa]
  rcases congr(diag $(g.2)), (S.eq_zero_of_ratMiddle_form_eq_zero <|
    (g.1.1 - 1).col · ∘ .inr ∘ .inl)
  simp_all [frameGram, splitGram, middleGram, forall_fin_succ']

lemma exists_classUnip_mul_mem_boxedPoints {y} (h : ∀ v, InCut (y v) S.b) : ∃ u ∈ S.classUnip c,
  S.ratToInf u * y ∈ S.boxedPoints := (ENNReal.summable.tsum_ne_zero_iff.1 (tsum_classCutoff_eq_one
  c y ▸ one_ne_zero)).imp' (↑) fun u _ ↦ by simp_all [classCutoff, ↓(isBoxPartition_epsilon c).2,
  besselSize_besselS_mul (mem_unitriGroup_of_mem_besselU (u.2.1.ratToInf_mem_unitriangularOn _))]

@[fun_prop] lemma measurable_classCutoff : Measurable (S.classCutoff c) :=
  classCutoff.eq_1 S _ ▸ (exists_cutoff_classUnip ..).choose_spec.1.mul (isBoxPartition_epsilon c).1
