import OmegaMath.NumberTheory.GRH.Lib.Adelic.Witt.MaximalCompact
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Set-up used by: Adeles of a number field: base change, discreteness and compact quotient, modulus.

This file: Integral finite adeles of a CM field with 5040th roots of unity: adelic-ring axioms.
Adelic index of a field element equals its absolute norm (product formula). Saturation, indices,
discriminant of an orthogonal complement in a unimodular adelic lattice. -/

open AddSubgroup Fintype MatMul Matrix Submodule

instance isAdelic_Ô {E} [Field E] [NumberField E] [NumberField.IsCMField E] [StablyUnram E] :
    IsAdelic (Ô E) :=
  ⟨⟨isOpen_Ô, isCompact_Ô⟩, isValuationPair_Ohat, StablyUnram.exists_i_c₀.elim fun i ⟨τ, _⟩ ↦
  ⟨_, coe_mem_Ô i, _, coe_mem_Ô τ, by simp; norm_cast; grind⟩, _, by simp, star_normNegOne_mul_self⟩

variable {E} [Field E] [NumberField E] {A} [CommRing A] {R : Subring A}
  {π σ τ ρ : Type} [Fintype π] [Fintype ρ] {M D K K'} {H J : Matrix π π A}
  {m F : Matrix π σ A} {n : Matrix π τ A} (P : (τ → A) →ₗ[R] σ → A)

@[simp] lemma genIndex_algebraMap (x : E) : genIndex (x : 𝔸f E) = |↑(Algebra.norm ℚ x)| := by
  by_cases x = 0; simp_all [genIndex.map_nonunit]
  simpa using! genIndex_eq_inv_finIdeleAbs (principalIdele (.mk0 x ‹_›))

lemma genIndex_natCast [NumberField.IsCMField E]
    (k : ℕ) : genIndex (k : 𝔸f E) = (k ^ numInfPlaces E) ^ 2 := by
  simpa [Algebra.norm_natCast, finrank_eq_two_mul_card_infinitePlace, pow_mul'] using
    genIndex_algebraMap (k : E)

lemma Filling.submoduleIndex_dvd_of_le (h : D ≤ K.comap P) (h' : K' ≤ M.map P ⊔ K) :
  submoduleIndex K K' ∣ submoduleIndex D M := by
  grw [submoduleIndex, ← relIndex_addSubgroupOf (toAddSubgroup_mono h'),
    relIndex_dvd_index_of_normal]
  simpa [← relIndex.eq_1, sup_toAddSubgroup, map_toAddSubgroup, ← relIndex_comap] using
    relIndex_dvd_of_le_left _ h

lemma ne_zero_and_le_of_dvd {a b} : b ≠ 0 → a ∣ b → a ≠ 0 ∧ a ≤ b :=
  (⟨by aesop, Nat.le_of_dvd ·.pos ·⟩)

attribute [local grind _=_] conjTranspose_mul Matrix.mul_assoc

attribute [local simp] IsIntMatrix fromBlocks_add neg_mulVec sub_eq_add_neg

variable [Fintype σ] [Fintype τ] [StarRing A] [TopologicalSpace A]
  [ad : IsAdelic R] {l : Matrix τ π A}

include R in
lemma genIndex_det_conj [IsTopologicalRing A] [LocallyCompactSpace A] [PolishSpace A] :
    genIndex (Jᴴ * H * J).det =
  genIndex H.det * genIndex J.det ^ 2 := by simp [field]

lemma genIndex_det_conj_of_isIntMatrix [IsTopologicalRing A] [LocallyCompactSpace A] [PolishSpace A]
    (hx : IsIntMatrix R n) (hy : IsIntMatrix R l) (i :
  l * n = 1) (h : n * l = 1) :
  genIndex H.det = genIndex (nᴴ * H * n).det := by grind [=_ det_comm' h i, det_mul,
  genIndex_det_eq_one, ad.exists_topology, isPrimitiveMatrix_iff.1 ⟨hx.mul hx.isInt_conjTranspose,
  _, hy.isInt_conjTranspose.mul hy, by grind [l.one_mul, conjTranspose_one]⟩]

lemma exists_isPrimitiveMatrix_mul_fromBlocks (m : Matrix π (σ ⊕ τ) A) : HasLeftInv m → ∃ᵉ
  (a : GL σ A) (e : GL τ A) (z), IsPrimitiveMatrix R (m * fromBlocks a.1 z 0 e.1) :=
  (have ⟨b, _, h⟩ := ad.isValuationPair.exists_isPrimitiveMatrix_mul · (0 ⊕ᵥ 1)
  have e := (by aesop : toBlocks₂₁ _ = 0) ▸ b.1.fromBlocks_toBlocks
  (isUnit_fromBlocks_zero₂₁'.1 ⟨b, e.symm⟩).elim (⟨·.unit, ·.unit, _, e ▸ h⟩))

/-- For an adelic pair R ⊂ A and a left invertible matrix m over A, there is an invertible a
whose columns span {y | my integral} over R, with ma primitive over R. -/
lemma exists_preimageLattice_eq_colLattice (h : HasLeftInv m) : ∃ a : GL σ A, preimageLattice R m =
  colLattice R a.1 ∧ IsPrimitiveMatrix R (m * a.1) :=
  (ad.isValuationPair.exists_isPrimitiveMatrix_mul h).imp fun a ⟨_, p@⟨i, q, j, k⟩⟩ ↦ ⟨le_antisymm
  (fun _ ↦ (⟨_, j.mulVec ·, by simp_all [mul_eq_one_comm.1]⟩)) (colLattice_le i.isInt_transpose), p⟩

/-- Let J be unimodular, F integral, n primitive, FᴴJn = 0 with complementary sizes, N =
Gram(F|p) plus c on the p-block, and F left invertible or [det N] ≠ 0. Then n^⊥ ⊆ span F and
[det nᴴ(J + c⁻¹JppᴴJ)n]·i²·[c]^|ρ| = [det N], i = [{y | Fy integral} : R^σ]. -/
lemma Filling.jacobi_perp_discriminant [IsTopologicalRing A] [LocallyCompactSpace A] [PolishSpace A]
    {N} (hJ : IsUnimodular R J) (hF : IsIntMatrix R F) (hn :
  IsPrimitiveMatrix R n) (hFn : Fᴴ * J * n = 0) (hπ : card π = card σ + card τ) (p : Matrix π ρ A)
  (c : Aˣ) (hN : N = (fromCols F p)ᴴ * J * fromCols F p + fromBlocks 0 0 0 (c • 1)) (q :
  HasLeftInv F ∨ genIndex N.det ≠ 0) : (∀ u, nᴴ *ᵥ J *ᵥ u = 0 → ∃ v, F *ᵥ v = u) ∧
  genIndex (nᴴ * (J + c⁻¹ • (J * p * pᴴ * J)) * n).det * submoduleIndex
  (intVectors ..) (preimageLattice R F) ^ 2 * genIndex c.1 ^ card ρ = genIndex N.det := by
  obtain ⟨⟨a, h₁, h₀, r, h₂, h₃⟩, ⟨_, l, hl, e⟩, _, u, hu, ⟨⟩⟩ :=
    exists_preimageLattice_eq_colLattice (q.elim id
    fun h ↦ ⟨_, by simpa [← Matrix.mul_assoc, *, -fromRows_mul] using! (congrArg toRows₁
    (N.nonsing_inv_mul_cancel_left (m := σ) (fromRows 1 0) (genIndex.apply_ne_zero_iff.1 h)))⟩),
    hn, hJ
  obtain hP := h₀.isInt_conjTranspose.mul hu.isIntMatrix,
    hu.isIntMatrix_inv.mul h₂.isInt_conjTranspose, submoduleIndex_colLattice_div.symm.trans
    congr($(relIndex_eq_one.2 (h₁.le.trans' fun _ ↦ hF.mulVec)) / _), genIndex_pos a.det
  let P := (F * a.1)ᴴ * u.1; let Q := u.2 * rᴴ
  have k : fromRows P (l - l * Q * P) * fromCols Q n = 1 := by apply_fun (·ᴴ) at h₃; aesop
  have k₁ := (mul_eq_one_comm_of_card_eq _ _ _ (by simpa)).2 k
  have := genIndex_det_conj_of_isIntMatrix (by aesop) (Sum.rec hP (hl.sub ((hl.mul ‹_›).mul hP))) k
    k₁ (H := u.1 * (1 + fromCols (u.2 * Pᴴ - Q) (c⁻¹ • p) * fromRows P (pᴴ * u.1 * (1 - Q * P))))
  simp [← fromBlocks_one'] at k
  use fun v _ ↦ ⟨_, by simpa [← mulVec_mulVec, P, *] using congr((u.2 * $k₁ᴴ * u.1) *ᵥ v)⟩
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, det_mul, det_one_add_mul_comm,
    (_ : 1 + _ = fromBlocks aᴴ 0 (-pᴴ * rᴴ * a.1ᴴ) 1 * N * fromBlocks a 0 0 (c⁻¹ • 1))] at *
  simp [k, ← conjTranspose_mul, c⁻¹.smul_def] at *; grind [genIndex_det_eq_one, ad.exists_topology,
    pow_pos, genIndex_pos]
  simp_all [↓fromRows_mul_fromCols, ← fromBlocks_one', P, Q]; grind
