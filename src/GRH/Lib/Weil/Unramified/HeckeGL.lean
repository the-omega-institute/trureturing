import GRH.Lib.Adelic.Unitary.CongruenceLevel
import GRH.Lib.Adelic.Adeles.AdelicModulus
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Cosets of minuscule Hecke operators of GL_n indexed by residue subspaces; local
congruence groups. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open Matrix IsLocalRing Module Valued DoubleCoset Set Finset WithZero Projectivization


variable (n : Type*) {A W E : Type*} [Fintype n] [Field E] [NumberField E] (w :
  FinPlace E) [CommRing A] [AddCommGroup W] [Module A W]

instance : CompactSpace 𝒪[LocField w] := compactSpace_LocInt w

instance : CompactSpace (Kw n w) := (isCompact_Kw w).compactSpace

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- The subgroup of GL_n(O_w) of matrices congruent to 1 modulo 𝔭^(m+1), 𝔭 the maximal ideal of
O_w. -/
def localCongruence (m : ℕ) : Subgroup (GL n (LocField w)) :=
  congruenceGL (v.leSubmodule (exp (-m.succ))) id

variable {n w π j g i g' m} {ϖ : (LocField w)ˣ} {z : Matrix m n (LocField w)}
  (U : Submodule (ResField w) (n → ResField w)) (hg : g ∈ basicDoubleCoset n w j)

lemma isOpen_localCongruence {m} : (localCongruence n w m).IsOpen := isOpen_congruenceGL
  (isOpen_integer _) ((ext fun _ ↦ lt_mul_exp_iff_le (by simp)).subst (isOpen_v_lt ..))

lemma mem_localCongruence_zero : g ∈ localCongruence n w 0 ↔ ∃ h, reduceGL ⟨g, h⟩ = 1 :=
  exists_prop.symm.trans (by
  congr!; erw [intGL.map_eq_one, forall₂_congr fun _ _ ↦ residue_eq_iff_valuation_sub_lt_one]
  simp [← lt_mul_exp_iff_le])

/-- Every neighbourhood s of 1 contains, for all sufficiently large m, the group `localCongruence`
of matrices congruent to 1 modulo 𝔭^(m+1), 𝔭 the prime at w. -/
lemma eventually_localCongruence_subset {s} : s ∈ nhds 1 → ∀ᶠ m in .atTop,
  SetLike.coe (localCongruence n w m) ⊆ s :=
  eventually_congruenceGL_subset ((hasBasis_nhds_zero ..).smallSets.tendsto_right_iff.2 fun _ _ ↦
  Filter.mem_atTop_sets.2 ((exists_exp_neg_natCast_lt (by simp)).imp fun _ hm _ _ _ x ↦
  v.restrict_lt_iff_lt_embedding.2 ((x.trans (by grind [exp_le_exp])).trans_lt hm)))

/-- Lifting the exponent in GL_n(E_w): if the natural number q lies in the prime 𝔭 of w and g ≡
1 mod 𝔭, then g^(q^k) ≡ 1 mod 𝔭^(k+1). -/
lemma pow_pow_mem_localCongruence {q : ℕ} (hq : ↑q ∈ w.1) (h : g ∈ localCongruence n w 0) k :
    g ^ q ^ k ∈ localCongruence n w k := k.rec (by simpa) fun k ih ↦ ⟨pow_mem h.1 _, by
  erw [pow_mul, ← mul_geom_sum]
  use v_matrix_mul_le (d := exp (-1)) ih.2
    (by simpa using! (v.leSubmodule _).matrix.add_mem (sum_mem (t := range q) fun _ _ ↦
    (pow_mem (pow_mem h _) _).2) (y := q) (by erw [diagonal_mem_matrix_iff] <;> simp_all
    [← lt_mul_exp_iff_le, ← w.intValuation_lt_one_iff_mem, ← v_algebraMap_eq_intValuation]))⟩

/-- The map from E_w to the residue field at w that reduces integral elements and sends all
others to 0. -/
def residueOrZero (x : LocField w) : ResField w := if h : v x ≤ 1 then residue _ ⟨x, h⟩ else 0

/-- The kernel, in column vectors over the residue field at w, of the entrywise reduction
`residueOrZero` of the matrix z. -/
abbrev residueKer (z : Matrix m n (LocField w)) := (z.map residueOrZero).mulVecLin.ker

lemma residueOrZero_coe y : residueOrZero y.1 = residue (LocInt w) y := dite_eq_left y.2

@[simp] lemma residueOrZero_eq_zero {x : LocField w} : residueOrZero x = 0 ↔ v x ≠ 1 := by
  fun_cases residueOrZero x; erw [residue_eq_iff_valuation_sub_lt_one]; simp; all_goals grind

set_option synthInstance.maxHeartbeats 200000 in
lemma map_residueOrZero_mul {y : Matrix n n (LocField w)} (hz : ∀ i j, v (z i j) ≤ 1) (hy : ∀ i j,
  v (y i j) ≤ 1) : (z * y).map residueOrZero = z.map residueOrZero * y.map residueOrZero :=
  ext (by simpa [mul_apply, residueOrZero, *] using residueOrZero_coe (w := w) <| ∑ k,
  ⟨_, hz · k⟩ * ⟨_, hy k ·⟩)

lemma card_sub_rank {k} [Field k] (x : Matrix m n k) : Fintype.card n - x.rank = finrank k
  x.mulVecLin.ker := by grind [finrank_pi, rank, x.mulVecLin.finrank_range_add_finrank_ker]

/-- Over a field with q elements, the subgroup H of GL_n of matrices whose i-th column vanishes
off the diagonal (the stabiliser of a line) satisfies qⁿ = [GL_n : H](q − 1) + 1. -/
lemma index_stabilizer_line {F} [Field F] [Finite F] i {H : Subgroup (GL n F)} (h : ∀ g, g ∈ H ↔
    ∀ j ≠ i, g j i = 0) : H.index = ∑ j ∈ range (Fintype.card n), .card F ^ j := (H.ext
  (by simp [mk_eq_mk_iff', funext_iff, Units.smul_def, ite_eq_iff', forall_and]; grind)).substr
  ((@MulAction.index_stabilizer_of_transitive _ _ _ _ (.mk F (Pi.single i 1) (by simp)) (.of_smul_eq
  SpecialLinearGroup.toGL rfl)).trans (card_of_finrank _ _ (finrank_pi _)))

/-- For a uniformiser ϖ of E_w and a set s of indices, the diagonal matrix with ϖ on s and 1
elsewhere lies in the double coset `basicDoubleCoset` with j = #s, and the kernel of its reduction
has dimension #s. -/
lemma diagGL_mem_basicDoubleCoset (h : v ϖ.1 =
  exp (-1)) s : let d := diagGL (if · ∈ s then ϖ else 1)
  d ∈ basicDoubleCoset n w #s ∧ finrank (ResField w)
    (residueKer d.1) = #s := by simp +decide [basicDoubleCoset, -coe_units_inv, ← map_inv,
  diagonal_apply, apply_ite, ↓← card_sub_rank, *, ite_apply, rank_diagonal, ← card_compl]

include hg

lemma mul_mul_mem_basicDoubleCoset {k k'} (hk : k ∈ Kw ..) (hk' : k' ∈ Kw ..) : k * g * k' ∈
  basicDoubleCoset n w j := ⟨v_matrix_mul_le (v_matrix_mul_le hk.isIntMatrix hg.1) hk'.isIntMatrix,
  v_matrix_mul_le hk'.isIntMatrix_inv (v_matrix_mul_le hg.2.1
  hk.isIntMatrix_inv), by erw [mem_intGL_iff_det] at *; simp_all [basicDoubleCoset]⟩

/-- For g in the double coset of diag(ϖ 1_j, 1) in GL_n(E_w) and a matrix z over E_w with n
columns, z g⁻¹ is integral if and only if z is integral and the kernel of g mod w lies in
that of z mod w. -/
lemma v_mul_inv_le_one_iff : (∀ i j, v ((z * g⁻¹.1) i j) ≤ 1) ↔ (∀ i j, v (z i j) ≤ 1) ∧
  residueKer g.1 ≤ residueKer z
  := have c : ∀ i j, v (((uniformizer w).1 • g⁻¹.1) i j) ≤ 1 := by simpa [field] using hg.2.1
  ⟨fun h ↦ by obtain := v_matrix_mul_le h hg.1, map_residueOrZero_mul h hg.1; aesop_cat, fun ⟨hz,
    h⟩ i j ↦ by simpa using v_uniformizer_inv_mul_le_one_iff.2 ((v_matrix_mul_le hz c ..).lt_of_ne
    (residueOrZero_eq_zero.1 (congr($(map_residueOrZero_mul hz c) i j).trans congr($(h
    (congr($(map_residueOrZero_mul hg.1 c)ᵀ j).symm.trans (by aesop))) _))))⟩

lemma mul_inv_mem_Kw_iff (hg' : g' ∈ basicDoubleCoset n w i) : g * g'⁻¹ ∈ Kw .. ↔ residueKer g.1 =
  residueKer g'.1 := by erw [mem_intGL, (v_mul_inv_le_one_iff hg').and
  (v_mul_inv_le_one_iff hg)]; simp_all [basicDoubleCoset, ge_antisymm_iff]

lemma exists_residueKer_mul_eq (h : finrank (ResField w) (residueKer g.1) =
  finrank (ResField w) U) : ∃ k ∈ basicDoubleCoset n w j, residueKer k.1 = U ∧
  k⁻¹ * g ∈ Kw .. := have ⟨e, he⟩ := U.exists_linearEquiv_restrict_eq (.ofFinrankEq U _ h.symm)
  have ⟨⟨l, m⟩, hl⟩ :=
    GeneralLinearGroup.toLin.surjective.comp reduceGL_surjective (.ofLinearEquiv e)
  ⟨_, mul_mul_mem_basicDoubleCoset hg (one_mem _) m, by erw [residueKer, one_mul,
    map_residueOrZero_mul hg.1 m.isIntMatrix, mulVecLin_mul, congr(mulVecLin $(ext
    (residueOrZero_coe ⟨l · ·, _⟩))).trans congr($hl), U.eq_of_le_of_finrank_eq
    (by simp [← he ⟨·, ·⟩]) (h ▸ (e.ofSubmodule' _).finrank_eq.symm)]; rfl, by simpa⟩

/-- For a subspace U of k_w^n, a chosen element of the double coset of diag(ϖ 1_j, 1), j = dim
U, whose reduction modulo w has kernel U. -/
def basicCosetRep := (((exists_subset_card_eq (U.finrank_le.trans_eq (finrank_pi _))).choose_spec.2
  ▸ diagGL_mem_basicDoubleCoset (v_uniformizer w) _).elim (exists_residueKer_mul_eq U)).choose

omit hg in lemma basicCosetRep_spec : basicCosetRep U ∈ basicDoubleCoset n w
  (finrank (ResField w) U) ∧ residueKer (basicCosetRep U).1 = U := by grind [basicCosetRep]

lemma finrank_residueKer : finrank (ResField w) (residueKer g.1) = j :=
  (basicCosetRep_spec _).elim fun h ↦ by
  erw [← mul_inv_mem_Kw_iff h hg, mem_intGL_iff_det]; simp_all [basicDoubleCoset, inv_mul_eq_one₀]

/-- For every g in the set `basicDoubleCoset` of index j, that set is the double coset GL_n(O_w) g
GL_n(O_w). -/
lemma basicDoubleCoset_eq : basicDoubleCoset n w j = doubleCoset g (Kw n w) (Kw n w) := ext fun _ ↦
  .trans ⟨(exists_residueKer_mul_eq _
  · (by grind [finrank_residueKer]) |>.elim fun l ⟨a, d, e⟩ ↦ ⟨_, (mul_inv_mem_Kw_iff a hg).2
  d, _, e, by simp⟩), by simp_all [mul_mul_mem_basicDoubleCoset]⟩ mem_doubleCoset.symm

lemma le_card_of_mem_basicDoubleCoset : j ≤
  Fintype.card n := by simp [← finrank_residueKer hg, ← card_sub_rank]

omit hg

instance : Fintype (Submodule (ResField w) (n → ResField w)) := .ofFinite _

lemma transposeGL_mem_basicDoubleCoset : transposeGL g ∈ basicDoubleCoset n w j ↔
  g ∈ basicDoubleCoset n w j := forall_comm.and (forall_comm.and (by simp))

variable {v : W} (hv : v ∈ levelSpace (A := A) π (Kw n w))

@[simp] lemma isBiInvariant_basicDoubleCoset j : IsBiInvariant (A :=
  A) (Kw ..) ((basicDoubleCoset n w j).indicator 1) := (eq_empty_or_nonempty
  (basicDoubleCoset n w j)).elim (by simp [·, IsBiInvariant,
  HasFiniteCosets]) (basicDoubleCoset_eq ·.some_mem ▸ isBiInvariant_doubleCoset (isOpen_Kw w) _)

include hv

/-- For v fixed by K = GL_n(O_w), the function g ↦ 1_D(g⁻¹), D = `basicDoubleCoset` j, sends v to
∑_U π(γ_U⁻¹)v, over the j-dimensional subspaces U of k_w^n, with k_w the residue field and γ_U =
`basicCosetRep` U. -/
lemma heckeFun_basicDoubleCoset_inv : heckeFun π (Kw ..) ((basicDoubleCoset n w j).indicator 1 ·⁻¹)
  v = ∑ U with finrank (ResField w) (SubmoduleElem U) = j, π (basicCosetRep U)⁻¹
  v := by rw [(heckeFun_eq_sum (by simp) hv _ (r := basicCosetRep⁻¹) (inv_surjective.forall.2 fun g
  _ ↦ ⟨residueKer g.1, _⟩)).2, sum_congr rfl] <;> simp [QuotientGroup.eq,
  indicator, InjOn] <;> grind [finrank_residueKer, basicCosetRep, mul_inv_mem_Kw_iff]

/-- For v fixed by GL_n(O_w) in a representation π of GL_n(E_w), the j-th Hecke operator sends v
to ∑_U π(γ_Uᵀ)v, over the j-dimensional subspaces U of k_w^n, with k_w the residue field and
γ_U = `basicCosetRep` U. -/
lemma heckeGL_eq_sum : heckeGL π j v = ∑ U with finrank (ResField w) (SubmoduleElem U) = j,
  π (transposeGL (basicCosetRep U)) v := by refine' (heckeFun_basicDoubleCoset_inv (π :=
  π.comp invTransposeGL.toMonoidHom) _).subst (heckeFun_comp invTransposeGL.toMonoidHom
  _ _ _ invTransposeGL.surjective _ (by tauto) fun _ ↦
  if_congr transposeGL_mem_basicDoubleCoset.symm _ _) <;> simp_all

/-- Let ϖ be a uniformiser of E_w, n = i + j, and v fixed by GL_n(O_w). Acting on v by the
indicator of the inverse of the double coset of T_i and then by the scalar matrix ϖ gives
T_j v. -/
lemma heckeGL_dual (h : Valued.v ϖ.1 = exp (-1)) (e : Fintype.card n = i + j) : π (.scalar n ϖ)
    (heckeFun π (Kw ..) ((basicDoubleCoset n w i).indicator 1 ·⁻¹) v) = heckeGL π j v := by
  erw [eq_comm, ← π.inv_apply_eq_iff, ← (apply_heckeFun (by simp) (by simp) hv _).2]
  simp [indicator, basicDoubleCoset, -coe_units_inv, ← map_inv, *]; simp [field]; ac_rfl

lemma heckeGL_zero : heckeGL π 0 v = v := by simp [filter_eq', heckeGL_eq_sum hv,
  hv ⟨_, mem_intGL_iff_det.2
  ((transposeGL_mem_basicDoubleCoset.2 (basicCosetRep_spec ⊥).1).imp_right (by simp))⟩]
