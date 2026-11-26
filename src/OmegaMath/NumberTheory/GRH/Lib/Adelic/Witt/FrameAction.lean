import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ColumnLattices
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Left invertible and primitive matrices, hermitian symmetry, quasi-reflections. Hermite
normal form over valuation-like pairs of rings; primitive bases of flags. Witt's extension theorem
for hermitian forms over a field, by quasi-reflections. Action of the unipotent subgroups on the
frame; transformation of the Gram matrix. -/

section

open IsLocalRing Matrix Finset ValuationRing MatMul

section

variable {R n k} [CommRing R] [Fintype n] (O : Subring R) (X : Matrix n k R) [StarRing R]
  {J : Matrix n n R} (hJ : Jᴴ = J)

/-- The n × k matrix X over R has a left inverse over R. -/
abbrev HasLeftInv := ∃ L : Matrix k n R, L * X = 1

/-- The submodule of R^n spanned by the columns of the matrix X. -/
abbrev colSpan [Fintype k] := X.mulVecLin.range

/-- The matrix X has entries in the subring O and a left inverse with entries in O. -/
def IsPrimitiveMatrix := IsIntMatrix O X ∧ ∃ L : Matrix k n R, IsIntMatrix O L ∧ L * X = 1

noncomputable instance [IsLocalRing R] : StarRing (ResidueField R) := by refine' { star :=
  (.mapEquiv starRingAut), .. } <;> simp [Function.Involutive, residue_surjective.forall, mul_comm]

lemma star_form (hJ : Jᴴ = J) u v : star (star u ⬝ᵥ J *ᵥ v) = star v ⬝ᵥ J *ᵥ u := by
  grind [star_dotProduct, star_mulVec_dotProduct]

/-- The quasi-reflection x ↦ x − v σ⁻¹ h(v, x) in U(J), where h(v, x) = vᴴJx, J is hermitian,
and σ is a unit with σ + σ̄ = h(v, v). -/
noncomputable def quasiReflection (hJ' : IsUnit J) v (σ : Rˣ) (h : σ + star ↑σ =
  star v ⬝ᵥ J *ᵥ v) := U.of hJ' (1 - σ⁻¹.1 • vecMulVec v (star v ᵥ* J)) (by
  simp [sub_mul, mul_sub, vecMulVec_mul, mul_vecMulVec, star_vecMul, vecMulVec_mulVec, ← ext_iff]
  grind [Units.mul_inv, star_mul, star_one, dotProduct_mulVec])

variable {A} {n k : _} [CommRing A] {R : _} [Fintype n] [Fintype k] (val :
  @IsValuationPair A _ R) (M : Matrix k n A) (ι : k ↪ n)

lemma transvectionGL_mem_intGL {i j a} (h : i ≠ j) : a ∈ R → transvectionGL h a ∈ intGL n R := by
  aesop (add simp [mem_intGL, single, transvection, transvectionGL])

lemma isValuationPair_top [IsDomain A] [ValuationRing A] : @IsValuationPair A _ ⊤ := by
  simp [IsValuationPair, mul_left_eq_self₀, ← dvd_def, dvd_total]

include val

/-- Hermite form: if (A, R) satisfies `IsValuationPair` and ι embeds k in n, an n × k matrix y over
A is U_ι D with U ∈ GL_n(R), U_ι its columns at ι, and D = (rows ι of U⁻¹)·y block upper
triangular for wt. -/
lemma IsValuationPair.hermite y (wt : k → ℕ := 0) : ∃ᵉ (U ∈ intGL n R) (D : Matrix k k A),
    D.BlockTriangular wt ∧ y = U.1.submatrix id ι * D ∧ U⁻¹.1.submatrix ι id * y = D :=
  let P s U := U ∈ intGL .. ∧ ∀ j ∈ s, ∀ i ∉ (filter (wt · ≤ wt j) s).map ι, (U.1 * y) i j = 0
  have ⟨U, u, e⟩ : Exists (P univ) := univ.induction_on_max_value wt (by aesop) fun a s _ _ h ↦
    (((insert a s).map ι)ᶜ.induction_on' (motive := (∃ U, P s U ∧ ∀ i ∈ ·, (U.1 * y) i a = 0))
    (by simpa) fun i _ _ _ _ ⟨U, ⟨u, h⟩, _⟩ ↦ by
  obtain ⟨_, _, ⟨_, x, _⟩, _, _, z, _⟩ := by simpa using val ((-U.1 * y) (ι a) a) ((-U.1 * y) i a)
  exists _, ⟨mul_mem (transvectionGL_mem_intGL (.symm ?x) z) (mul_mem (transvectionGL_mem_intGL
    (?x : ι a ≠ i) (add_mem R.one_mem x)) u), ?_⟩ <;> simp at h ⊢ <;> grind +splitImp
    [mem_compl, transvection_mul_apply_same, transvection_mul_apply_of_ne]).imp (by aesop)
  ⟨_, inv_mem u, _, fun _ _ _ ↦ by apply e <;> simp [*], .symm (.trans (ext fun _ _ ↦ by
    apply sum_of_injOn _ ι.2.injOn <;> aesop) (U.1.invOf_mul_cancel_left y)), rfl⟩

/-- If (A, R) satisfies `IsValuationPair` and the n × k matrix X over A has a left inverse, there is
an invertible b, block upper triangular for wt, such that X b has entries in R and a left
inverse with entries in R. -/
lemma IsValuationPair.exists_isPrimitiveMatrix_mul {X : Matrix n k A} (h : HasLeftInv X) (wt :
  k → ℕ := 0) : ∃ b : GL k A, b.1.BlockTriangular wt ∧ IsPrimitiveMatrix R (X * b.1) := by
  obtain ⟨⟨L, _⟩, U, _, D, _, e, f⟩ := h, val.hermite .inr (X.fromRows 0) wt
  cases (congr(toRows₁ $e) : X = U.1.toBlocks₁₂ * D)
  obtain ⟨b, ⟨⟩⟩ := IsUnit.of_mul_eq_one_right _ (by rwa [L.mul_assoc])
  refine ⟨b⁻¹, ?_, ?_, _, ?_, by simpa [← ext_iff, mul_apply] using congr($f * b⁻¹)⟩
    <;> simp_all [IsIntMatrix, mem_intGL, toBlocks₁₂, blockTriangular_inv_of_blockTriangular]

/-- Hermite form: if the subring R of A satisfies `IsValuationPair`, then for a k×n matrix M over A
and an injection ι: k → n, some V in GL_n(R) makes the columns of MV outside the image of ι
vanish. -/
lemma IsValuationPair.exists_mul_clear_cols : ∃ V ∈ intGL n R, ∀ᵉ (a) (j ∉ Set.range ι),
  (M * V.1) a j = 0 := have ⟨k, _, D, _, h, _⟩ := val.hermite ι Mᵀ
  have := h ▸ (k.2.mul_assoc ..).symm.trans congr(submatrix $k.inv_mul _ ι * D)
  ⟨transposeGL k⁻¹, by simp_all [← ext_iff, mul_apply, ne_comm, mul_comm, mem_intGL, transposeGL]⟩

end

variable {R n k} [Field R] [Fintype n] [Fintype k] {X Y : Matrix n k R}

lemma HasLeftInv.mulVec_injective : HasLeftInv X →
  X.mulVec.Injective | ⟨l, _⟩ => .of_comp (f := l.mulVec) (by aesop_cat)

lemma HasLeftInv.of_ker_le_bot : X.mulVecLin.ker ≤ ⊥ → HasLeftInv X := by
  simpa using exists_mul_add_mul_eq (y := diagonal 0) (x := X)

lemma HasLeftInv.of_ne_zero {x : n → R} (h : x ≠ 0) : HasLeftInv (replicateCol Unit x) :=
  .of_ker_le_bot (by simp_all [LE.le, mulVec, funext_iff]; grind)

lemma Filling.exists_basis_matrix (L : Submodule R _) : ∃ x : Matrix n (Fin (Module.finrank R L)) R,
  HasLeftInv x ∧ colSpan x = L := ⟨(L.subtype ∘ₗ (LinearEquiv.ofFinrankEq _ _
  (by simp)).1).toMatrix', by simp [← toLin'_apply', LE.le, colSpan, HasLeftInv.of_ker_le_bot]⟩

variable [StarRing R] (hz : ∃ z : R, IsUnit (z - star z)) {J : Matrix n n R} (hJ : Jᴴ = J)
  (hJ' : IsUnit J) (hX : HasLeftInv X) (hY : HasLeftInv Y) (h : Xᴴ * J * X = Yᴴ * J * Y)

lemma HasLeftInv.of_isUnit_gram : IsUnit (Xᴴ * J * X) → HasLeftInv X :=
  (⟨_, (Matrix.mul_assoc ..).trans ·.unit.4⟩)

include hz hJ hJ' hX hY h

/-- Witt's theorem by quasi-reflections: over a field with involution having some z ≠ z̄, for
invertible hermitian J and a subgroup H of U(J) containing all quasi-reflections, left
invertible X, Y with XᴴJX = YᴴJY satisfy gX = Y for some g in H. -/
lemma witt_of_quasiReflection_mem (H : Subgroup _) (hH : ∀ v σ h,
  quasiReflection hJ hJ' v σ h ∈ H) : ∃ g ∈ H,
  g.1.1 * X = Y := have t : ∀ i j, star _ ᵥ* J ⬝ᵥ Xᵀ j = star _ ᵥ* J ⬝ᵥ Yᵀ j := congrFun₂ h
  (univ.induction ⟨1, by simp⟩ fun j s _ ⟨g, hg, e⟩ ↦ by
  wlog σ : star (Yᵀ j) ⬝ᵥ J *ᵥ (Yᵀ j - g *ᵥ Xᵀ j) ≠ 0 generalizing g
  any_goals refine ⟨_, mul_mem (hH (g *ᵥ Xᵀ j - Yᵀ j) (.mk0 _ σ) ?_) hg, ?_⟩
  have d {X} : HasLeftInv X → ∃ a : n → R, ∀ i, a ⬝ᵥ Xᵀ i = ite (j = i) 1 0 :=
    (⟨_, congrFun₂ ·.choose_spec j⟩)
  obtain ⟨⟨z, ζ⟩, ⟨a, p⟩, b, q⟩ := hz, (vecMul_surjective_of_invertible g).exists.1 (d hX), d hY
  refine ((vecMul_surjective_iff_isUnit.2 hJ').exists.1 (by simp [add_vecMul]; grind : ∃ u ∈
    [a, b, a + b], u ⬝ᵥ Yᵀ j * u ᵥ* g ⬝ᵥ Xᵀ j ≠ 0)).rec fun u _ ↦ this _ (mul_mem
    (hH (star u) (.mk0 (z * (u ⬝ᵥ J *ᵥ star u - star z) / ζ.unit) ?_) ?_) hg) ?_ ?_
  all_goals revert σ t; simp +contextual [← mulVec_mulVec, *, quasiReflection,
    U.form_mulVec_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, ↓op_smul_eq_smul, mulVec_sub] <;>
    grind [add_dotProduct, star_star, IsUnit.ne_zero, star_form, star_eq_zero, dotProduct_mulVec] :
    ∃ g ∈ H, ∀ i ∈ univ, g *ᵥ Xᵀ i = Yᵀ i).imp fun _ ↦ .imp_right (by simpa using! ext_col)

/-- Witt's theorem: over a field with involution having some z − z̄ ≠ 0, for invertible
hermitian J, left invertible X, Y with XᴴJX = YᴴJY satisfy g X = Y for some g in U(J).

Known result: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa
decomposition. -/
lemma witt : ∃ g : U J, g.1.1 * X =
  Y := by simpa using witt_of_quasiReflection_mem hz hJ hJ' hX hY h ⊤

end

open Matrix Fin Sum Function FI
variable {A} [CommRing A] {𝔰 : Shape} {T : 𝔰.Form A} [StarRing A] {x x' γ : T.G} {m n}
  (hx' : x' ∈ besselU)

attribute [local simp] forall_fin_succ' level frameMatrix mem_besselU Matrix.mul_apply frameGram

@[simp] lemma besselFrame_castSucc a : 𝔰.besselFrame a.castSucc = inl a := by simp [besselFrame]

@[simp] lemma besselFrame_last : 𝔰.besselFrame 𝔰.top = 𝔰.z := snoc_last ..

lemma level_besselFrame : ∀ a, level (𝔰.besselFrame a) = a := by simp

lemma besselFrame_injective : 𝔰.besselFrame.Injective := by simp [Injective]

lemma frameMatrix_unitriangular : x ∈ besselU → ∀ a, ∀ b ≤ a, frameMatrix x a b =
  (1 : Matrix ..) a b := by simp; grind

lemma mem_besselU0_iff : x ∈ besselU0 ↔ x ∈ besselU ∧
  frameMatrix x = 1 := by simp [besselU0, ← ext_iff]; grind

include hx'

/-- For x' in 𝖴, the entries in rows outside the first block and columns outside the last block
are those of the identity: x' keeps the span X of the e_a and is trivial on X^⊥/X. -/
lemma apply_inr_of_mem_besselU i j : (∀ a, j ≠ eStar a) → x'.1 (inr i) j = ite (inr i = j) 1 0 := by
  simp_all; grind

/-- An element of the unipotent group 𝖴 that fixes ϱ vectors whose coordinates at e*₁, …, e*_ϱ
form the identity matrix is 1. -/
lemma eq_one_of_mem_besselU_of_fix {B : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) A} (h : x'.1.1 * B = B)
    (e : B.toRows₂.toRows₂ = 1) : x' = 1 := by
  have b a := congrFun₂ x'.2 (eStar a)
  ext : 2; simp_all [↓← ext_iff, splitGram, apply_ite star,
    apply_inr_of_mem_besselU hx', -mem_besselU]

lemma submatrix_mul_besselFrame (M : Matrix m _ A) (e : n → m) :
  (M * x'.1.1).submatrix e 𝔰.besselFrame = M.submatrix e 𝔰.besselFrame * frameMatrix x' :=
  ext (by simp [sum_univ_castSucc, apply_inr_of_mem_besselU hx'])

lemma frameMatrix_mul : frameMatrix (x * x') = frameMatrix x * frameMatrix x' :=
  submatrix_mul_besselFrame hx' ..

lemma frameGram_inv_mul_mul (hx : x ∈ besselU) : T.frameGram (x'⁻¹ * γ * x).1 =
  (frameMatrix x')ᴴ * T.frameGram γ * frameMatrix x
  := by simpa [submatrix_mul_besselFrame hx, ← mul_assoc, ← U.form_mul_inv_eq]
  using congr($(submatrix_mul_besselFrame hx' (T.splitGram * γ.1.1)ᴴ _)ᴴ * _)
