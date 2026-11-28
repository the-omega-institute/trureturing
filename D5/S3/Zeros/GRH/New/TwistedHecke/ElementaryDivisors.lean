/- GID: D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.TwistedHecke.ElementaryDivisors. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/TwistedHecke/ElementaryDivisors.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Core.CappedMinorWitness
import D5.S3.Zeros.GRH.New.Core.ModuleIndex
import D5.S3.Zeros.GRH.New.TwistedHecke.Counting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! An approximate projector from averages over generic matrices. Conjugation-invariant linear forms
on polynomials in a generic Levi matrix split evaluation at the identity by weight, up to a
controlled power of p, and the resulting approximate projector onto forms nearly obeying the
Frobenius inequalities shows that the two halves of the Hecke operator pair almost perfectly. The
Schur algebra as dual of polynomials in a generic matrix, spanned by finite points in low degree,
and truncation by weights are known. Related work: Benson–Doty, Schur–Weyl duality over finite
fields, 2009; Green, Polynomial representations of GL_n, 1980; Donkin, On Schur algebras and related
algebras I, 1986.

Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Twisted Hecke operator has small elementary divisors; approximate projector; Smith form
of ends. -/

namespace TwistingData

open MvPolynomial Matrix IsLocalRing Function Module PiTensorProduct Finset Fintype Kronecker Equiv
  ClassMean Ideal Pointwise MatMul
attribute [local simp] dotProduct prod_prod_type prod_eq_zero_iff mul_sum sum_mul vecMul
  sum_prod_type mulVec polyOfCoeffs Matrix.map IsConcreteLE.le_iff Submodule.mem_sup_left
attribute [local simp ←] map_mul kroneckerPi_mul Matrix.mul_apply
attribute [-simp] Matrix.one_apply _root_.map_inv
attribute [local grind] dvd_trans deepIndicator twoBlock pow_mul pow_dvd_pow dvd_mul_of_dvd_right
  dvd_def
variable {N k n W O X E H} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [IsDomain O]
  [ValuationRing O] (T : TwistingData N W O) (c : ℕ) {a r : Fin k} [Fintype X]
  [Fintype E] (Q M : Matrix (X × (ZMod N → Monomials (Fin k) n)) E O) (R β : type_of% Qᵀ)

omit [Fintype E] in
lemma card_le_finrank_translatesIn {s G B} (h : ∀ j ∈ s, ∀ i, (R * Q) i j = ite (i = j) 1 0)
    (hs : ∀ j ∈ s, ∀ x, Q.col j ∘ (x, ·) ∈ T.translatesIn n G (maximalIdeal O) B) :
    #s ≤ finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) :=
  card_coe s ▸ LinearIndependent.fintype_card_le_finrank (b := fun j x ↦ ⟨residue O ∘ Q.col j ∘ (x,
  ·), by simp_all [translatesIn, letterRep_map, ← map_sum]⟩)
  (linearIndependent_iff.2 fun g hg i ↦ by simpa [mul_sum _, sum_comm, mul_left_comm, h,
  ← mul_sum, ← map_sum] using congr(∑ y, residue O (R i y) * ($hg y.1).1 y.2))

/-- Let RQ = 1, w be a non-unit and βM ≡ a mod aw. If Qu − Mv = aw·F forces each F(x, ·) into
`TwistingData.translatesIn` n G 𝔪 B, then im(βQ) + z·O^E has index (`IndexDvd`) dividing a^{|E|}z^l,
with |E| + l ≤ |X|·dim of that condition over the residue field. -/
lemma of_pairing a z {w G B} (hR : R * Q = 1) (hw : ¬IsUnit w) (h : ∀ i j, a * w ∣
    (β * M - a • 1 :) i j) (hn : ∀ u v F, Q *ᵥ u - M *ᵥ v = (a * w) • F → ∀ x, F ∘ (x, ·) ∈
    T.translatesIn n G (maximalIdeal O) B) : ∃ l, card E + l ≤
  finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) ∧
  IndexDvd ⊤ (.map (β * Q).mulVecLin ⊤ ⊔ z • ⊤) (a ^ card E * z ^ l) := by
  obtain ⟨⟨U, V⟩, _, G, _, t, e⟩ := isValuationPair_top.smith_normal_form ((Q * R * M - M) * R)
  rw [← G.mul_inv_eq_iff_eq_mul] at e
  choose s _ using (ValuationRing.cond (a * w) <| t ·)
  choose W _ using h
  let A := β * U * (diagonal (a • w • s) - diagonal t)
  refine ⟨_, (T.card_le_finrank_translatesIn (Q.fromCols U) (R.fromRows (V - V * Q * R))
    (by simp_all [V.mul_apply, Q.mul_apply, one_apply, by
    simpa [← ext_iff, ← Matrix.mul_assoc, hR, or_iff_not_imp_right] using
      congr(R * $e)]) ?_).trans_eq' (card_disjSum _ {i | t i ∣ a * w ∧ t i ≠ 0}), .trans
    (.of_det_dvd (A := A * G.1 * Q + β * Q * R * M) ?_ ?_) (.map (.of_det_dvd (by rw [det_diagonal,
    ← prod_const, prod_filter]) le_rfl) A.mulVecLin le_rfl (le_sup_of_le_right ?_))⟩
  simpa using ⟨fun j ↦ hn (Pi.single j _) 0 _ (by aesop), fun _ _ ⟨c, h⟩ _ ↦ hn _ _ _ (by
    simpa [-mulVec_smul, h, ↓ ← mulVec_mulVec, ↓diagonal_mulVec_single,
      ↓op_smul_eq_smul] using! congr($e *ᵥ Pi.single (_, _) c))⟩
  convert ((1 + w • (of W + β * U * diagonal s * G.1 * Q)).det_smul a).dvd.trans _
  ext; simp_all [A, ← e]
  grind
  simp_all [↓det_one_add_smul w, map_mul, ← residue_ne_zero_iff_isUnit, -residue_eq_zero_iff]
  simp [Submodule.add_mem_sup, -mulVec_mulVec]
  simpa using (⟨A *ᵥ ·, by simp [-sub_mulVec, A, funext_iff, -Matrix.mul_assoc]; grind⟩)

/-- The pairing congruence bounds the determinant of a nonzero full minor of `[βQ | zI]`
by divisibility, with the exponent of `z` controlled by the residue dimension. -/
lemma of_pairing_capped_minor a z {w G B} (hR : R * Q = 1) (hw : ¬IsUnit w) (h : ∀ i j, a * w ∣
    (β * M - a • 1 :) i j) (hn : ∀ u v F, Q *ᵥ u - M *ᵥ v = (a * w) • F → ∀ x, F ∘ (x, ·) ∈
    T.translatesIn n G (maximalIdeal O) B) (haw : a * w ≠ 0) (hz : z ≠ 0) :
    ∃ l, card E + l ≤ finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) ∧
      ∃ s : E ↪ E ⊕ E,
        ((Matrix.fromCols (β * Q) (z • (1 : Matrix E E O))).submatrix id s).det ≠ 0 ∧
        ((Matrix.fromCols (β * Q) (z • (1 : Matrix E E O))).submatrix id s).det ∣
          a ^ card E * z ^ l := by
  obtain ⟨⟨U, V⟩, _, K, _, t, e⟩ := isValuationPair_top.smith_normal_form ((Q * R * M - M) * R)
  rw [← K.mul_inv_eq_iff_eq_mul] at e
  have hcount : card E + #{i | t i ∣ a * w ∧ t i ≠ 0} ≤
      finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) := by
    clear haw hz
    refine (T.card_le_finrank_translatesIn (Q.fromCols U) (R.fromRows (V - V * Q * R))
      (by simp_all [V.mul_apply, Q.mul_apply, one_apply, by
      simpa [← ext_iff, ← Matrix.mul_assoc, hR, or_iff_not_imp_right] using
        congr(R * $e)]) ?_).trans_eq' (card_disjSum _ {i | t i ∣ a * w ∧ t i ≠ 0})
    simpa using ⟨fun j ↦ hn (Pi.single j _) 0 _ (by aesop), fun _ _ ⟨c, h⟩ _ ↦ hn _ _ _ (by
      simpa [-mulVec_smul, h, ↓ ← mulVec_mulVec, ↓diagonal_mulVec_single,
        ↓op_smul_eq_smul] using! congr($e *ᵥ Pi.single (_, _) c))⟩
  let S : Finset (X × (ZMod N → Monomials (Fin k) n)) := {i | t i ∣ a * w ∧ t i ≠ 0}
  refine ⟨#S, hcount, ?_⟩
  choose s hs using (ValuationRing.cond (a * w) <| t ·)
  choose W hW using h
  let Aold := β * U * (diagonal (a • w • s) - diagonal t)
  let correction := 1 + w • (of W + β * U * diagonal s * K.1 * Q)
  have hcorrection : Aold * K.1 * Q + β * Q * R * M = a • correction := by
    ext i j
    simp_all [Aold, correction, ← e]
    linear_combination hW i j
  have hunit : IsUnit correction.det := by
    simp_all [correction, ↓det_one_add_smul w, map_mul, ← residue_ne_zero_iff_isUnit,
      -residue_eq_zero_iff]
  have hzero i (hi : i ∉ S) : ∀ j, Aold j i = 0 := by
    have hsi : a * w * s i = t i := by
      rcases hs i with hi' | hi'
      · exact hi'
      · have hdvd : t i ∣ a * w := ⟨s i, hi'.symm⟩
        have ht : t i ≠ 0 := fun ht ↦ haw (by simpa [ht] using hi'.symm)
        exact (hi (mem_filter.mpr ⟨mem_univ _, hdvd, ht⟩)).elim
    have hentry : (a • w • s) i = t i := by
      simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc] using hsi
    intro j
    simp only [Aold, Matrix.mul_sub, Matrix.sub_apply, mul_diagonal, hentry, sub_self]
  let cols : Matrix E S O := Aold.submatrix id Subtype.val
  let rows : Matrix S E O := (K.1 * Q).submatrix Subtype.val id
  have hfactor : cols * rows = Aold * (K.1 * Q) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    let summand k := Aold i k * (K.1 * Q) k j
    change (∑ k : S, summand k) = ∑ k, summand k
    calc
      _ = ∑ k ∈ S, summand k := Finset.sum_coe_sort S summand
      _ = _ := Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ by
        simp only [summand, hzero k hk i, zero_mul]
  simpa only [Fintype.card_coe] using
    D5.S3.Zeros.GRH.New.Core.exists_capped_minor_dvd_of_low_rank_correction
      (β * Q) (R * M) correction cols rows a z
      (by simpa only [hfactor, Matrix.mul_assoc, add_comm] using hcorrection) hunit hz

variable [CharZero O]

/-- Let a<r, all r-depths ≤x, e↦(s(e), g_e⁻¹𝒫) onto, 𝒫 the two-block parahoric. The matrix of
φ↦(w^{depth}ρ(g_e)φ(s(e)))_e is Qd, Q left invertible, det d ∣ w^{|X|∑_{τ<x}dim V_τ} (V_τ: residue
forms with all GL_k(W)-translates of depth ≥τ), and values of Q satisfy `TwistingData.excessCond`
modulo w^c at each e for h≥2c. -/
lemma exists_depth_factorization (ha : a < r) {x} (hm : ∀ β, T.depth k n r β ≤ x) (s : E → X) (g : E
  → _) (hs : Surjective fun e ↦ ((s e, ⟦(g e)⁻¹⟧) : X × _ ⧸ parahoric W (twoBlock k r))) : ∃ (Q d :
  Matrix _ _ O) (R : type_of% Qᵀ), (Q * d = of fun (e, α) (x, β) ↦ ite (s e = x) ((diagonal (T.w ^
  T.depth k n r ·) * T.letterRep n (g e) :) α β) 0) ∧ d.det ∣ T.w ^ ∑ τ ∈ range x,
  finrank (ResidueField O) (X → (map (residue O) T).deepForms k n r τ) ∧ R * Q = 1 ∧
  ∀ j e {h : ℝ}, 2 * c ≤ h → (Q *ᵥ j) ∘ (e, ·) ∈ T.excessCond n a r (span {T.w ^ c}) h := by
  set J := of _
  have hJ φ e : (J *ᵥ φ) ∘ (e, ·) = _ *ᵥ φ ∘ _ := funext (by simp [J, -diagonal_mul]; tauto)
  have hf {z φ} (h : ∀ y, z ∣ (J *ᵥ φ) y) x γ β :
      z ∣ T.w ^ T.depth k n r β * (T.letterRep n γ *ᵥ φ ∘ (x, ·)) β := by
    obtain ⟨e, rfl, he⟩ := by simpa [QuotientGroup.eq] using hs (x, ↑γ⁻¹)
    choose A hA using show ∀ s i j,
      T.w ^ T.deepIndicator r (j, s) ∣ T.w ^ T.deepIndicator r (i, s) * T.letterMatrix s
      (g e * γ⁻¹)⁻¹ i j by grind [p_dvd_letterMatrix_of_mem_parahoric, inv_mem, w_sq]
    rw [← mulVec_diagonal (_ ^ T.depth k n r ·), ← inv_mul_cancel_right γ, map_mul, mulVec_mulVec, ←
      mul_assoc, (?_ : diagonal _ * _ = kroneckerPi (symPowMatrix n ∘ of ∘ A) * _), mul_assoc,
      ← mulVec_mulVec, ← hJ]
    exact dvd_sum (by grind)
    simp [letterRep, diagonal_pow_depth]; congr! 3
    ext; simpa [mul_comm] using hA ..
  have ⟨U, _, D, _, e, _⟩ := isValuationPair_top.hermite
    (.ofSurjective _ ((Prod.fst_surjective.comp hs).prodMap surjective_id)) J
  obtain ⟨K, -, P, -, t, rfl⟩ := isValuationPair_top.smith_normal_form D
  have h0 i := @hf (t i) (P.2ᵀ i) (by simp [e, ← Matrix.mul_assoc])
  choose t' ht using fun i ↦ by simpa using show t i ∣ (P.1 * T.w ^ x • P.2) i i from (dvd_sum
    fun ⟨y, β⟩ _ ↦ by grw [h0 i y 1 β, hm]; simp [-mulVec])
  refine ⟨_, _, U.2.submatrix _ id, e.symm, ?_, by
    simpa [← submatrix_mul] using submatrix_one_embedding _, fun j _ _ _ l hl β ⟨i, h⟩ ↦ ?_⟩
  simp [-finrank_pi_fintype, -prod_prod_type]
  grw [prod_dvd_prod_of_dvd _ (T.w ^ #{τ ∈ range x | ¬t · ∣ T.w ^ τ}) fun i _ ↦ by
    set m := #_
    grind [@card_le_card _ (range (m + 1))]]
  erw [prod_pow_eq_pow_sum, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  gcongr; exact T.card_le_finrank_translatesIn P.2 P.1 (by simp [one_apply]) fun i hi y γ _ β hβ e ↦
    (mem_filter.1 hi).2 ((e.dvd_mul_right.1 (h0 ..)).trans (pow_dvd_pow _ hβ.le))
  -- `J` takes `P⁻¹ t' K⁻¹ j` to `w ^ x` times the value at `j` of the primitive factor
  have hφ := congr($e *ᵥ P.2 *ᵥ diagonal t' *ᵥ K.2 *ᵥ j)
  simp [← mul_assoc (diagonal t), ← ht, ← smul_one_eq_diagonal] at hφ
  rw [mem_span_singleton, ← mul_dvd_mul_iff_left (pow_ne_zero x T.w_ne_zero), ← pow_add, ←
    smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul, ← Pi.smul_comp, ← hφ, ← mulVec_mulVec, hJ,
    mulVec_mulVec, Commute.left_comm, ← map_mul, ← mulVec_mulVec, mulVec_diagonal]
  -- a term least for valuation plus weight `ω` among all translates of `F` weighs at least `x`
  set F := _ ∘ _
  let ω y := T.deepIndicator r y - T.excessWeight i a r y / 2
  choose l L g G using fun γ ↦ @Nat.exists_not_and_succ_of_not_zero_of_exists (fun l ↦ ∃ g, ¬T.w ^
    l ∣ (T.letterRep n g *ᵥ F) γ ∨ ⌈x - (exponentOf γ).weight ω⌉₊ < l) (by simp) ⟨_, 1, .inr .refl⟩
  let ⟨γ, H⟩ := (@Finite.exists_min _ _ _ ⟨β⟩ _ fun γ ↦
    l γ + (exponentOf γ).weight ω).imp fun _ M g δ ↦
    (pow_dvd_pow _ (Nat.ceil_le.2 (sub_le_iff_le_add.2 (M δ)))).trans (by_contra (L δ ⟨g, .inl ·⟩))
  have := (G γ).imp_left fun hg ↦ And.intro (fun d : _ ≤ x ↦ hg (by
    grw [← mul_dvd_mul_iff_left (pow_ne_zero _ T.w_ne_zero), ← @hf (_ ^ x), ← pow_add, ← d]
    simp [hφ, -mulVec])) (T.root_lemma i ha.ne 0 ω _ (f := polyOfCoeffs (T.letterRep n (g γ) *ᵥ F))
    (fun g _ ↦ by simpa [↓polyAction_polyOfCoeffs, -mulVec] using
    (_root_.sum_mem fun _ _ ↦ monomial_mem_gaussFiltration (H ..)))
    (by simpa [coeff_sum]) rfl (by simp [ω, deepIndicator]; grind [excessWeight_mem_Icc]))
  grw [← H, ← pow_add, pow_dvd_pow]
  simp [← add_assoc, ω, depth, Finsupp.weight_eq_sum, mul_sub, mul_div, ← sum_div] at this h ⊢
  rify at *; grind [Nat.le_ceil]
  simp [commute_iff_eq, letterRep, diagonal_pow_depth]; congr! 3
  ext; simp [letterMatrix, -coe_units_inv]; clear * - hl; grind [hl _, inv_mem hl _,
    transpose_apply]

/-- Tensor product of linear forms on polynomial rings: there is a multilinear S into linear
forms on R[X_{ι×σ}] with S(l)(∏_j f_j(X_{j,·})) = ∏_j l_j(f_j) for all l_j and f_j, ι
finite. -/
lemma _root_.exists_tensor_dual ι σ R [Fintype ι] [CommRing R] : ∃ S :
    MultilinearMap R (fun _ : ι ↦ Dual R (MvPolynomial σ R)) (Dual R (MvPolynomial _ R)), ∀ l
    (f : _ → _), S l (∏ j, rename (j, ·) (f j)) = ∏ j, l j (f j) := ⟨((aeval fun (i, v) ↦
    singleAlgHom i (X v)).toLinearMap.dualMap ∘ₗ dualDistrib).compMultilinearMap (tprod R), by
  simp [aeval_rename, comp_def, ← comp_aeval, -singleAlgHom_apply]; simp [← tprod_prod]⟩

/-- Projector modulo w^c. For p a non-unit, a+1 = r, 2ℓ = N, Nnk(ℓ+2)+n+k < P^ℓ there are b, Z with
all ZF in `TwistingData.excessCond` at θ, y·diag(b)ZF ≡ p^{(k+k²)o₀N²} y·F for y in it at θ−(4c+2),
and diag(b)ρ(γᵀ) = ρ(γ)ᵀdiag(b).

An approximate projector from averages over generic matrices. -/
lemma exists_projector (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.1) {ℓ} θ (e : ℓ + ℓ = N)
    (h : N * (n * (k * (ℓ + 2))) + n + k < T.P ^ ℓ) : ∃ b Z, (∀ F, Z *ᵥ F ∈ T.excessCond n a r
    (span {T.w ^ c}) θ) ∧ (∀ y ∈ T.excessCond n a r (span {T.w ^ c}) (θ - (4 * c + 2)), ∀ F,
    T.w ^ c ∣ y ⬝ᵥ (b * Z *ᵥ F) - T.p ^ ((k + k ^ 2) * (T.o₀ * N) * N) * y ⬝ᵥ F) ∧
    ∀ γ α β, b β * T.letterRep n (transposeGL γ) β α = b α * T.letterRep n γ α β := by
  obtain ⟨⟨S, hS⟩, q, b₀, hb, hx⟩ := exists_tensor_dual (ZMod N) (Fin k × Fin k) O, e ▸ Nat.pow_add
    .. ▸ Nat.mul_le_mul_right _ h, exists_invariant_diagonal_form (Fin k) T.prime hp (T.o₀ * N)
  let b (β : ZMod N → Monomials _ n) := ∏ s, b₀ (β s).1
  choose b' hb' using fun β ↦ (prod_dvd_prod_of_dvd _ _ fun s _ ↦
    Dvd.intro_left _ (hb _ (by grind [Monomials.degree_eq])).symm : b β ∣ _)
  have hν l f : S l f = ∑ ν ∈ f.support, f.coeff ν * ∏ j, l j (monomial (ν.curry j) 1) :=
    (congrArg _ f.as_sum).trans (by simp [← hS, monomial_eq, C_mul'])
  let Z := ((LinearMap.mapMatrixLinear O).flip
    (T.frobOperator r ℓ n T.frobGenericMatrix)).compMultilinearMap S
  have key i {m} (l : type_of% m) {g y F} (hg : g ∈ _) (e : ∀ j f, m j f = l j (conjSubst (T.ι j) g
    f)) (H : ∀ β _ ν, univ.prod _ = (0 : O) ∨ _) : y ⬝ᵥ Z m *ᵥ F ∈ span {T.w ^ c} := (by
    rw [(congr(.map _ $(show _ = _ ∘ₗ (aeval _).toLinearMap by
      ext; simp [single_eq_monomial, hν m, e]
      simp [← hS, monomial_eq])) : Z _ = .map (.map ((T.map C).frobOperator _ _ _ _) (eval₂Hom C
      fun (j, v) ↦ rename (j, ·) (conjSubst (T.ι j) g (X v)))) (S l)), frobOperator_map _ _ hg]
    simp_rw [letterRep_map, map_C_mul_mul_C, ← mulVec_mulVec, dotProduct_mulVec y, funext (hν l)]
    exact sum_mem fun β _ ↦ dite _ (mul_mem_right _ _) fun q ↦ mem_span_singleton.2 (.mul_left
      (dvd_sum fun _ _ ↦ .mul_right (dvd_sum fun ν _ ↦ (H β q ν).elim (· ▸ by simp) (And.elim
      (T.pow_dvd_coeff_conj_frobOperator ha i (by lia) (by lia) g (by simp [letterConj, conjSubst,
      linSubst, ← C_mul', map, map_mul,
      mul_apply, mul_assoc, mul_comm (X _)])) · |>.mul_right _)) _) _))
  choose κ h0 h2 h1 h3 using fun P j ↦ exists_mean (twoBlock k r) (T.ι j) T.prime hp (T.o₀ * N)
    (by grind) (D := N * (n * (k * ((ℓ + 2) * T.P ^ ℓ)))) (by grind [card_residueField])
    (T.indexWeight ℓ a r) (P ∨ θ - (2 * c + 1) < ·)
  use b, Z (-κ False + κ True) * diagonal b', fun F g hg β ⟨i, hi⟩ ↦ mulVec_mulVec F (Z _) _ ▸
    key (i - ℓ) (-κ False + κ True) hg (by simp [h0 _ _ g hg]) (by
    simp [one_apply]
    clear * - h1 h2 hi; grind [zero_mem]), fun y hy F ↦ ?_, ?ρ
  have := ?ρ
  let Y := (dotProductBilin O O (b * y) ∘ₗ toLin'.1.flip (b' * F)).compMultilinearMap Z
  have hz : Z (κ True) = (_ :
    O) • (T.frobOperator r ℓ n T.frobGenericMatrix).map
      (eval (vec (1 : Matrix (Fin k) (Fin k) O) ·.2)) :=
    ext fun _ _ ↦ by
    simp [Z, hν, eval_eq']; congr! 1
    simp [h1, T.degree_le_of_coeff_frobOperator (mem_support_iff.1 ‹_›), eval_monomial]
    rw [mul_left_comm]
  simp [↓T.frobOperator_map _ (one_mem _), frobOperator, one_apply,
    T.prime.ne_zero, ite_apply, ← diagonal.eq_1, @eq_comm (Fin k)] at hz hb'
  convert (mem_span_singleton.1 (sum_mem (Finset.induction (by simp) fun s t _ _ _ ↦ ?_))).trans
    (sub_eq_of_eq_add' ((Y.map_add_univ (-κ False) (κ True)).trans
    (sum_eq_add_sum_compl ∅ _))).symm.dvd
  simp [Y]; ac_rfl; simp [Y, hz, add_mul]; grind
  rw [piecewise_insert]
  refine neg_mem (Submodule.mem_span.1 (h3 _ s) (.comap (Y.toLinearMap _ s) (span _)) fun
    | _, ⟨u, h, γ, e, rfl⟩ => And.elim (key s (update (t.piecewise (-κ False) (κ True)) s γ) h) ?_)
  have z β := (mul_mem_left _ (b β) <|
    hy (transposeGL u⁻¹) (swap (inv_mem h · · ·.symm)) β ⟨s + ℓ, ·⟩)
  simp [update, piecewise, DFunLike.ite_apply] at z ⊢; clear * - z e h0 h2 h this; grind
  simp [letterRep, kroneckerPi, b, ← prod_mul_distrib]
  congr! 1; erw [mul_comm, letterMatrix]; bound

/-- Elementary divisors of the twisted Hecke operator (AF)(c) = ∑_b (u_e ⊗ (ρ(g_e) p^{depth}
ρ(γ_b))ᵀ) F(src e), e = (c,b), the γ_b representing the cosets 𝒫γ of the parahoric. Assume p is a
non-unit, `HeckeSizes`, and e ↦ (src e, 𝒫g_eᵀ) injective. If Yf = fA, then Y has type
(z + κm + y)|X||I| at m on im f (`HasType`: Y preserves M = im f, and YM + p^m M has index dividing
p^l for some l at most this number).

A Frobenius-twisted Hecke operator has small elementary divisors. -/
lemma hasType_twisted_hecke (hp : ¬IsUnit (T.p : O)) {r ℓ κ y z} (big : HeckeSizes T.P T.o₀ N k n r
  ℓ κ y z) {I M : Type} [Fintype H] [Fintype (_ ⧸ parahoric W (twoBlock k r))] [Fintype I]
  [AddCommGroup M] [Module O M] (f : (X → I → O) →ₗ[O] M) {Y : End O M} (src :
  X × _ ⧸ parahoric W (twoBlock k r) → X) (g : _ → GL (Fin k) W) (u : _ → GL H O) (J : I ≃ _ × H)
  (hs : Injective fun e ↦ ((src e, ↑(transposeGL (g e))⁻¹) : X × _ ⧸ parahoric W (twoBlock k r)))
  (hY : ∀ F, Y (f F) = f fun c i ↦ ∑ b, ∑ j, u (c, b) (J i).2 (J j).2 * (T.letterRep n (g (c, b)) *
  diagonal ((T.p : O) ^ T.depth k n r ·) * T.letterRep n b.out⁻¹ :) (J j).1 (J i).1 * F (src (c, b))
  j) m : HasType ↑T.p f.range m Y ((z + κ * m + y) * (Nat.card X * Nat.card I)) := by
  have ⟨_, _, _, _, e, h1, _⟩ := big
  set c := 2 * _ + 2
  let S := T.map (residue O)
  have ha : @Fin.val k ⟨r - 1, by lia⟩ + 1 = @Fin.val k ⟨r, by lia⟩ := by lia
  obtain ⟨hu, _, x, hm⟩ := (T.w_sq ▸ hp) ∘ .pow 2, CharP.of_eq_zero S.prime
    ((residue_eq_zero_iff _).2 hp), Finite.exists_le (T.depth k n r)
  obtain ⟨U, U', ⟨b, Z, hZ, hZ', hρ⟩, ⟨Q, d, R, hj, h₀, hR, hQ⟩, Q', d', R', j', h₁, hR', hQ'⟩ :=
    S.index_mul_finrank_excessCond_le ha big, S.sum_finrank_deepForms_le big x, T.exists_projector c
    hp ha y e h1, T.exists_depth_factorization c ha.le hm _ _ ((prodAssoc H ..).symm.surjective.comp
    (surjective_id.prodMap hs.bijective_of_finite.2)), T.exists_depth_factorization c ha.le hm (.map
    id (·.1)) (·.2.2.out⁻¹) (⟨prodAssoc H X _ ·, by simp⟩)
  obtain ⟨l, L, key⟩ := T.of_pairing Q (blockDiagonal (u · |>.2) ⊗ₖ Z * R'ᵀ) R
    (Q'ᵀ * blockDiagonal (u · |>.1) ⊗ₖ diagonal b) (T.w ^ _) (T.p ^ m) hR hu (fun i j ↦ by
    grw [← pow_succ, one_le_two]
    convert univ.dvd_sum fun y _ ↦ hZ' _ (hQ' (Pi.single i 1) y (by bound)) (R' j ⟨y, ·⟩)
    simp [← transpose_eq_one.2 hR', ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, w_sq,
      ← blockDiagonal_mul, mul_apply, diagonal, blockDiagonal_apply, one_apply, mul_assoc, pow_mul])
      fun v _ _ h x γ hγ β hβ e ↦ by simpa [← pow_succ, pow_dvd_pow_iff T.w_ne_zero hu, c, e,
      mem_span_singleton, Pi.smul_comp, -mulVec] using (Set.mem_of_eq_of_mem (congr($h
      ∘ (x, ·)).symm.trans (by
      rw [← mulVec_mulVec, ← (vec_bijective.2 (R'ᵀ *ᵥ _)).choose_spec, kronecker_mulVec_vec]; ext
      simp; rfl)) (sub_mem (hQ v x (by bound)) (hZ _)) γ hγ β hβ)
  let ε := .funCongrLeft O O ((((prodComm ..).trans (J.prodCongr (.refl X))).trans
    (prodAssoc ..)).trans (prodComm ..)) ≪≫ₗ .curry ..
  have := (IndexDvd.of_det_dvd (d'.det_transpose ▸ h₁) le_sup_left).comp le_top
    (key.comp le_top (.of_det_dvd h₀ le_sup_left))
  simp_rw [mul_left_comm, ← mul_pow, ← sq, pow_mul, w_sq, ← pow_mul, ← pow_add] at this
  refine ⟨by simp [hY], _, ?_, this.map (f ∘ₗ ε) (by simp) ?_⟩
  grw [← (by bound : c / 2 ≤ y)]
  simp [Subgroup.index, card_congr J, c, ← mul_sum] at L U U' ⊢; rify at L
  linear_combination (norm := linarith!) ↑m * L + card X * card H * (↑m * U + U')
  simp [← LinearMap.range_comp, -IsConcreteLE.le_iff]
  refine le_sup_of_le_left fun | _, ⟨F, rfl⟩ => ⟨ε ((b ·.2) * F), ?_⟩
  simp [hY]; erw [hj, j']; congr!
  simp [ε, ← J.symm.sum_comp, @sum_prod_type_right _ _ H, ← mulVec_mulVec, sq,
    mul_apply, blockDiagonal, diagonal, ← w_sq, mul_pow, ite_and]
  congr!; rw [sum_comm_cycle]; clear * - hρ; grind
