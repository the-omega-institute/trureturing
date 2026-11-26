import GRH.Lib.GLn.SchurModule.Hook
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n) (known
result; see Lib.Adelic.CuspForms.DeltaForms).

This file: Contravariant form on Weyl's lattice: symmetric, positive, invariant, inverse to the
Fischer product up to the hook number. -/
seal Finset.univ Finset.sum Finset.prod

open MvPolynomial Module PolyRep ComplexOrder Sigma Function Fintype Equiv Finset Matrix
variable {Φ R S} [CommRing R] [CommRing S] [Fintype Φ] {n n'} [∀ τ : Φ, Fintype (n τ)]
  [∀ τ, Fintype (n' τ)] {κ} (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) (φ : R →+* S) (N)
  (ι : ∀ τ, n τ ⊕ Unit ≃ n' τ) (g : ∀ τ, Matrix (n τ) (n τ) R) (ξ η s : _ → R)
  (y : (Σ τ, n τ) × ℕ → R) (h : FitsRanks n n' κ) (z : ∀ τ, Matrix (n' τ) (n τ) R)
attribute [local simp] comp_def weylEval Fin.val_inj ite_and permArray Matrix.mul_apply mul_sum
  minor linearCombination_apply dotProduct Matrix.map mulVec RingHom.map_det detPow tableauPoly
  AlgHom.map_det

namespace PolyRep

/-- For an array y and enumerations e_τ of the rows, the square matrices with (a,b) entry
y((τ,a), e_τ(b)): the first |n_τ| columns of block τ. -/
def squarePart τ := of (y ⟨⟨τ, ·⟩, e τ ·⟩)

lemma schur_squarePart_mulVec : schur κ (squarePart e y) *ᵥ weylEval n κ (permArray e) =
  weylEval n κ y := by simp [funext_iff, ↓schur_mulVec_weylEval_of_detExp_zero, nablaBasis,
  squarePart, -Fin.val_castLE, ← Fin.val_castLE Fin.is_le', ← eq_symm_apply]

/-- Over an infinite domain R, two linear maps L, L' from coordinate vectors of weight κ to a
free module are equal if D(y)L(ev_y) = D(y)L'(ev_y) for all arrays y, where D = ∏_τ
det_τ^{e_τ}. -/
lemma ext_weylEval [IsDomain R] {M} [AddCommGroup M] [Module R M] [Free R M] {L L' : _ →ₗ[R] M} {s}
  e (h : ∀ y ∈ Set.univ.pi fun _ ↦ s, eval y (detPow R n e) ≠ 0 → L (weylEval n κ y) =
  L' (weylEval n κ y)) (hs : s.Infinite := by exact Set.infinite_univ) : L = L' := by
  ext i; exact eval_apply_injective R (LinearMap.ext fun φ ↦
    (linearIndependent_nablaBasis_mul_detPow e).eq_coords_of_eq
    (funext_set _ (by tauto) fun y k ↦ by simpa [← mul_assoc, ← sum_mul, mul_comm _ (φ _),
    imp_iff_or_not] using (congrArg φ <| pi_eq_sum_univ' (weylEval n κ y) ▸ h y k · :)) i)

lemma map_weylKernel : map φ (weylKernel n κ y) =
  weylKernel n κ (φ ∘ y) := by simp [weylKernel, rowSubst, map_bind₁, ← C_mul']

lemma rowSubst_highestPoly : rowSubst (fun τ ↦ of fun i a ↦ y (⟨τ, a⟩, i.1)) (highestPoly R κ N) =
  ∏ τ, ∏ h ∈ range (N τ), (of fun s t : Fin h ↦ ∑ a,
  y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ h := by simp [highestPoly, prod_range, rowSubst]

/-- The kernel K(x, y) = f(yᵀx) of `weylKernel` is symmetric: K(x, y) = K(y, x) for all arrays x,
y over a commutative ring. -/
lemma weylKernel_symm : weylKernel n κ y = eval (C ∘ y) (weylKernel n κ X) := by
  simp [weylKernel, rowSubst_highestPoly, ← C_mul', mul_comm]; congr! 3; apply det_transpose

lemma weylKernel_borelMul b : weylKernel n κ (borelMul fst b y) =
  ((diagramWeight (rankAt n) κ).prod fun p ↦ (b (p.1, p.2, p.2) ^ ·))
  • weylKernel n κ y := by simpa [← C_mul', map_finsuppProd, borelMul, @weylKernel_symm _ R] using!
  (mem_nabla.1 (weylKernel_mem_nablaFam X) _ (C ∘ b) (C ∘ y))

/-- Over any commutative ring, the value at an array y of the polynomial Σ_i (Gξ)_i b_i attached
to ξ equals ev_yᵀ G ξ, where G is the Gram matrix and ev_y the vector of values b_i(y). -/
@[simp ←] lemma eval_toPoly : eval y (toPoly n κ ξ) = weylEval n κ y ⬝ᵥ weylGramOver *ᵥ ξ := by
  simp [toPoly, mul_comm]

lemma nablaCombination_weylGramOver_mulVec : nablaCombination κ (weylGramOver *ᵥ ξ) =
  toPoly n κ ξ := rfl

/-- For square matrices g_τ and scalars s_τ, the block diagonal matrix diag(g_τ,s_τ), reindexed
by n'_τ through the bijection n_τ ⊔ {point} ≅ n'_τ. -/
noncomputable def blockScalar τ := ((g τ).fromBlocks 0 0 (diagonal fun _ ↦ s τ)).reindex (ι τ) (ι τ)

@[grind] lemma diagramWeight_eq_succ_add τ i : diagramWeight N κ (τ, i) = diagramWeight N κ (τ,
  i + 1) + ite (i + 1 < N τ) (κ τ (i + 1)) 0 := by grind [diagramWeight_apply,
  sum_Ioo_add_eq_sum_Ico, =_ Ico_add_one_left_eq_Ioo, Ico_eq_empty]

lemma rowSubst_weylKernel_permArray (hg : ∀ τ, (g τ)ᵀ.BlockTriangular (e τ)) :
  rowSubst g (weylKernel n κ (permArray e)) =
  (∏ τ, ∏ a, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a)) • weylKernel n κ (permArray e) := by
  convert weylKernel_borelMul _ (∏ τ, ∏ a, ∏ b, if · = ⟨τ, e τ a, e τ b⟩ then g τ b a else 1)
  erw [rowSubst_rowSubst]; congr
  simp +instances [funext_iff, ← ext_iff, reindex_equiv (e _), borelMul]; tauto
  simp [← prod_pow, Finsupp.prod_finsetProd_comm, ← and_assoc, ← Prod.ext_iff (y := (_, _))]
  congr!; aesop

include ι

omit [Fintype Φ] in
lemma rankAt_eq_succ τ : rankAt n' τ = rankAt n τ + 1 := by simp [← card_congr (ι _)]

end PolyRep

/-- The polynomial attached by the Gram matrix to the evaluation vector ev_y is the kernel x ↦
f(yᵀx), f the highest weight product of leading minors. -/
@[simp] lemma toPoly_weylEval : toPoly n κ (weylEval n κ y) = weylKernel n κ
  y := by simpa [map_weylKernel, toPoly, weylGram, ← eval_map, aeval_def, ← C_mul'] using
  (congr(mapAlgHom (aeval y) $(congr(∑ i, $(sum_coords_nablaBasis (coord_mem_of_coeff_mem
  (nablaFam ℤ ..).toAddSubgroup 0 rfl (by simp [mem_nabla, aeval_eq_eval₂Hom, ← coeff_map,
  sum_coords_nablaBasis (weylKernel_mem_nablaFam X), map_weylKernel, weylKernel_borelMul]) i)) •
  _).trans (sum_coords_nablaBasis (weylKernel_mem_nablaFam X)))))

/-- The Gram matrix `weylGram` does not depend on the labelling of the places: for a bijection p
from Φ to Ψ, that of (n, κ) is that of the data transported to Ψ, with rows and columns
reindexed along p. -/
lemma PolyRep.weylGram_eq_submatrix {Ψ} [Fintype Ψ] κ (p : Φ ≃ Ψ) : weylGram n κ = (weylGram _
  _).submatrix (p.piCongrLeft' _) (p.piCongrLeft' _) := let e := Prod.map p.symm.sigmaCongrLeft id
  toLin'.injective (ext_weylEval 0 fun y _ _ ↦ nablaCombination_injective (.trans (toPoly_weylEval
    _) (by simpa [toPoly, rowSubst, nablaBasis, e, weylKernel, highestPoly, reindex_equiv p.symm,
    reindex_equiv (p.piCongrLeft' _).symm] using congr(rename e $(toPoly_weylEval (y ∘ e))).symm)))

@[simp] lemma map_toPoly : map φ (toPoly n κ ξ) = toPoly n κ (φ ∘ ξ) := by simp [toPoly, ← C_mul']

include h

lemma PolyRep.vecMul_schur_eq_iff {c x} : c ᵥ* schur κ z = x ↔ rowSubst z (nablaCombination κ c) =
  nablaCombination κ x * detPow R n (schurDetExp n n' κ) := (isRegular_detPow.2.comp
  nablaCombination_injective).eq_iff.symm.trans (by simp [h, vecMul_eq_sum, sum_mul]; rfl)

variable [IsDomain R] [CharZero R]

/-- Over a domain of characteristic zero, if the ranks fit κ (`FitsRanks`), the polynomial
`toPoly` of S_κ(z)ξ is x ↦ (fD)(zᵀx), where f is the polynomial of ξ and D = ∏_τ
det_τ^{d_τ} with d given by `schurDetExp`. -/
@[simp] lemma toPoly_schur z ξ : toPoly n' κ (schur κ z *ᵥ ξ) = rowSubst (fun τ ↦ (z τ)ᵀ) (toPoly n
  κ ξ * detPow R n (schurDetExp n n' κ)) := congr($((ext_weylEval (schurDetExp n n' κ) fun y _ k ↦
  (smul_right_inj k).1 (by
  simp [← map_smul, -map_mul, -detPow, schur_mulVec_weylEval h, weylKernel, mul_comm (z ..)]
  erw [← rowSubst_rowSubst, rowSubst_highestPoly]; congr
  simp [rowSubst_highestPoly, ← C_mul', ← prod_mul_distrib]; congr with τ
  rw [← prod_range_mul_prod_Ico _ (h _).1, schurDetExp, mul_left_comm, ← mul_pow, ← det_transpose,
    ← det_mul, (Ico ..).prod_eq_ite (rankAt n τ) (by simp_all [FitsRanks, lt_of_le_of_ne'])]
  simp [-det_mul, reindex_equiv (rowPos n τ).symm]; rfl) :
    toPoly .. ∘ₗ toLin' _ = (rowSubst fun τ ↦ (z τ)ᵀ).toLinearMap ∘ₗ .mulRight .. ∘ₗ _)) ξ)

omit h

/-- Over a domain of characteristic zero, the Fock pairing of the polynomial Σ_i (Gξ)_i b_i, G
the Gram matrix, with the basis element b_k equals the hook number times the coordinate ξ_k. -/
@[simp] lemma fockPairing_toPoly_nablaBasis k : fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) =
  hookNumber κ (rankAt n) * ξ k := by
  have H j := map_nablaBasis_eq_mul_weylEval (rowPos n) j (fockPairing R
    (weylKernel n κ (permArray (rowPos n)))) fun k τ a ↦ by
    have := fockPairing_rowSubst (fun _ ↦ diagonal (if mk _ · = ⟨τ, a⟩ then 2 else 1))
      (weylKernel n κ (permArray (rowPos n))) (nablaBasis R n κ j)
    simp_all [rowSubst_weylKernel_permArray, schur_diagonal, diagonal_apply]
    norm_cast at *; simp_all
  erw [fockPairing_rowSubst, rowSubst_rowSubst] at H
  simp [rowSubst, ← eq_symm_apply] at H
  exact congr($((ext_weylEval 0 fun y _ ↦ schur_squarePart_mulVec (rowPos n)
    y ▸ by simp [fockPairing_rowSubst, H, hookNumber, map_fockPairing, -eq_intCast, mul_left_comm] :
    (fockPairing _).flip _ ∘ₗ toPoly .. = algebraMap ℤ R _ • .proj k)) ξ)

@[simp] lemma fockPairing_toPoly_toPoly : fockPairing R (toPoly n κ ξ) (toPoly n κ η) =
  hookNumber κ (rankAt n) * ξ ⬝ᵥ
  weylGramOver *ᵥ η := by simp [← nablaCombination_weylGramOver_mulVec η, mul_rotate']

/-- The integer Gram matrix of the kernel f(yᵀx) in the basis of minor products is symmetric. -/
lemma weylGram_isSymm : (weylGram n κ).IsSymm := .ext fun i j ↦ by
  simpa using
    (fockPairing_comm ..).trans (fockPairing_toPoly_toPoly (Pi.single i 1) (Pi.single j (1 : ℤ)))

/-- The integer Gram matrix times the matrix of Fock pairings ⟨b_i,b_j⟩ of the basis minor
products equals the hook number times the identity matrix.

Known result: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n). -/
lemma weylGram_mul_fockPairing : weylGram n κ * (of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i)
  (nablaBasis ℤ n κ j)) = hookNumber κ (rankAt n) • 1 := ext (by simpa [-zsmul_eq_mul, toPoly,
  weylGram_isSymm.apply, eq_comm] using fockPairing_toPoly_nablaBasis <| Pi.single · (1 : ℤ))

/-- Over a domain of characteristic zero, for square matrices g_τ, G·S_κ(g) = S_κ(gᵀ)ᵀ·G with G
the Gram matrix: the Schur matrices of g and gᵀ are adjoint for the bilinear form given by
G. -/
lemma weylGram_mul_schur : weylGramOver * schur κ g = (schur κ fun τ ↦ (g τ)ᵀ)ᵀ * weylGramOver :=
  .symm <| ext_iff_mulVec.2 (by simp [← mulVec_mulVec, mulVec_transpose,
  vecMul_schur_eq_iff, ↓nablaCombination_weylGramOver_mulVec, -Matrix.map])

lemma toPoly_injective : Injective (toPoly (R := R) n κ) :=
  .of_comp (f := (fockPairing R · ∘ nablaBasis R n κ)) fun _ ↦ by simp [funext_iff]

/-- The integer Gram matrix, viewed as a complex matrix, is positive definite. -/
lemma weylGram_posDef : (weylGramOver : Matrix (WeylIndexFam n κ) _ ℂ).PosDef :=
  .of_dotProduct_mulVec_pos (.ext (by simp [weylGram_isSymm.apply])) fun ξ h ↦ by
  simpa [-mul_sum] using fockPairing_star_self_pos ((map_ne_zero_iff _ toPoly_injective).2 h)

/-- Over ℂ, the map ξ ↦ Σ_i (Gξ)_i b_i, with G the Gram matrix and b_i the basis minor products,
has image exactly the module `nablaFam` of Borel semi-invariant polynomials of the weight
given by κ. -/
lemma range_toPoly : (toPoly n κ).range = nablaFam ℂ n κ :=
  ((toLinearEquiv' _ weylGram_posDef.isUnit.invertible).range_comp _).trans span_nablaBasis
