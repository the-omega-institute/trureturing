import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.CoprimeValuation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius (known
result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Sums over coset representatives are invariant under left translation. Galois descent:
invariants span vectors fixed by a Galois-closed subgroup of finite index (semilinear actions).
Spanning set contains a basis of columns; units along non-unital ring maps. -/

/-- A sum over coset representatives of `G ⧸ H` of a right `H`-invariant function does not
change under left translation. -/
lemma sum_out_mul {G B} [Group G] [AddCommMonoid B] (H : Subgroup G) [Fintype (G ⧸ H)]
    (f : G → B) (hf : ∀ᵉ (x) (y ∈ H), f (x * y) = f x) a : ∑ q : G ⧸ H, f (a * q.out) = ∑ q : G ⧸ H,
    f q.out := Fintype.sum_equiv (MulAction.toPerm a) _ _
    (a • ·.out |> QuotientGroup.mk_out_eq_mul H |>.rec (by aesop (erase smul_eq_mul)))

/-- Galois descent. G acts on a field A, Γ semilinearly on an A-space V through j: Γ → G. If the
subgroup U has finite index and contains the pointwise fixer of A^U, every vector fixed by
j⁻¹(U) lies in the A-span of the Γ-invariants. -/
lemma mem_span_fixed {G Γ A V R} [Group G] [Group Γ] [L : Field A] [AddCommGroup V] [Module A V]
    [MulSemiringAction G A] [Semiring R] [Module R V] (j : Γ →* G) {U : Subgroup G} [Finite (G ⧸ U)]
    (τ : Representation R Γ V) (s : ∀ g (a : A) x, τ g (a • x) = (j g • a) • τ g x) {y}
    (h : ∀ g, j g ∈ U → τ g y = y) (h' : fixingSubgroup G (MulAction.fixedPoints U A) ≤ U) :
  y ∈ Submodule.span A {y | ∀ g, τ g y = y} := let := Subgroup.fintypeOfIndexNeZero ((U.index_comap
    j).trans_ne (Subgroup.index_eq_zero_of_relIndex_eq_zero.mt (by simp)))
  (((Pi.basisFun ..).constr A (τ ·.out y)).map_span_le ..).2 (Set.forall_mem_range.2 fun b ↦
  Submodule.subset_span (by simpa [flip, ← s] using! sum_out_mul _ (τ · _) (by aesop))) ⟨Pi.single
    ⟦1⟧ 1, (span_flip_eq_top_iff_linearIndependent.2 (.comp (linearIndependent_monoidHom ..)
    (fun q : _ ⧸ U.comap j ↦ (MulDistribMulAction.toMonoidHom A (j q.out)).domRestrict
    (FixedPoints.submonoid U A)) fun q r e ↦ Quotient.out_equiv_out.1 (QuotientGroup.leftRel_apply.2
    (h' (by simpa [mul_smul, inv_smul_eq_iff] using! congr($e ·).symm))))).ge ⟨⟩,
  (QuotientGroup.mk_out_eq_mul (U.comap j) 1).rec (by aesop)⟩

/-- For a ring homomorphism f: K → R that need not preserve 1, the homomorphism of unit groups x
↦ 1 + f(x − 1). -/
@[simps! apply_val] def unitsMapNonUnital {K R} [Ring K] [Ring R] (f : K →ₙ+* R) := Units.map
    ⟨⟨fun x ↦ 1 + f (x - 1), by simp⟩, by noncomm_ring [← map_mul, ← map_add, implies_true]⟩

/-- If a set s spans K^n over a field K, some invertible n×n matrix has all its columns in s. -/
lemma exists_GL_col_mem_of_span {K n} [Field K] [Fintype n] s (h : ⊤ ≤ Submodule.span K s) :
  ∃ U : GL n K, ∀ i, U.1.col i ∈ s := ⟨(Matrix.linearIndependent_col_iff_isUnit.1
  ((Module.Basis.linearIndependent _).comp _ ((Pi.basisFun ..).indexEquiv
  (Module.Basis.ofSpan h)).injective)).unit, fun _ ↦ Module.Basis.ofSpan_subset h ⟨_, rfl⟩⟩
