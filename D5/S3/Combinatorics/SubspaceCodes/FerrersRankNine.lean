/- GID: D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/FerrersRankNine
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: An optimal dimension-27 rank-nine code for the fixed twelve-column Ferrers diagram. -/

import D5.S3.Combinatorics.SubspaceCodes.FerrersCoefficients
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
import Mathlib.FieldTheory.Finite.Extension

/-! # An optimal rank-nine Ferrers code -/

namespace D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine

open D5.S3.Combinatorics.SubspaceCodes.FerrersCoefficients
open D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
open Module

/-- The number of allowed entries in a column.

Used by
- `FerrersRankNine.codeMap_supported` -/
def height (j : Fin 12) : ℕ := if j.val < 3 then 6 else if j.val < 6 then 9 else 12

/-- Every codeword vanishes below the prescribed column heights.

Used by
- `FerrersRankNine.codeMap_supported` -/
def Supported {F : Type*} [Field F] (C : Submodule F (Matrix (Fin 12) (Fin 12) F)) : Prop :=
  ∀ M ∈ C, ∀ i j : Fin 12, height j ≤ i.val → M i j = 0

/-- The exact example for every finite field in the source’s requested range.

Used by
- `FerrersRankNine.problem1_rank_nine` -/
def Problem1RankNine : Prop :=
  ∀ (F : Type) [Field F] [Fintype F],
    Odd (Fintype.card F) → 3 < Fintype.card F →
      (∃ C : Submodule F (Matrix (Fin 12) (Fin 12) F), Supported C ∧ Module.finrank F C = 27 ∧
        MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C ∧ ∃ M ∈ C, M ≠ 0 ∧ M.rank = 9) ∧
      (∀ D : Submodule F (Matrix (Fin 12) (Fin 12) F), Supported D →
        MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 D → Module.finrank F D ≤ 27)

private abbrev PrefixEntries (k : ℕ) :=
  {ij : Fin 12 × Fin 12 // ij.2.val < k ∧ ij.1.val < height ij.2}

private instance (k : ℕ) : DecidablePred (fun ij : Fin 12 × Fin 12 =>
    ij.2.val < k ∧ ij.1.val < height ij.2) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

private def prefixProjection {F : Type*} [Field F] (k : ℕ) :
    Matrix (Fin 12) (Fin 12) F →ₗ[F] (PrefixEntries k → F) where
  toFun M ij := M ij.val.1 ij.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rank_le_of_prefixProjection_eq_zero {F : Type*} [Field F]
    {C : Submodule F (Matrix (Fin 12) (Fin 12) F)} (hC : Supported C) (M : C) (k : ℕ)
    (h : prefixProjection k M.val = 0) :
    M.val.rank ≤ (Finset.univ.filter (fun j : Fin 12 => k ≤ j.val)).card := by
  rw [← Matrix.rank_transpose]
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro j hj
  have hjk : j.val < k := by
    by_contra! hge
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
  funext i
  by_cases hi : i.val < height j
  · exact congrFun h ⟨(i, j), hjk, hi⟩
  · exact hC M.val M.property i j (Nat.le_of_not_gt hi)

private theorem finrank_le_27_of_supported_of_rank {F : Type*} [Field F] [Fintype F]
    (C : Submodule F (Matrix (Fin 12) (Fin 12) F)) (hC : Supported C)
    (hr : MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C) :
    Module.finrank F C ≤ 27 := by
  let p := (prefixProjection (F := F) 4).comp C.subtype
  have hi : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro M hM
    have hM' : prefixProjection 4 M.val = 0 := hM
    have h8 := rank_le_of_prefixProjection_eq_zero hC M 4 hM'
    have hc : (Finset.univ.filter (fun j : Fin 12 => 4 ≤ j.val)).card = 8 := by decide
    rw [hc] at h8
    by_contra hm
    have hval : M.val ≠ 0 := fun hv => hm (Subtype.ext hv)
    have h9 := hr M.val M.property hval
    omega
  have hle := LinearMap.finrank_le_finrank_of_injective hi
  rw [Module.finrank_fintype_fun_eq_card] at hle
  exact hle.trans (le_of_eq (by decide))

private theorem exists_rank_eq_nine_of_finrank_eq_27 {F : Type*} [Field F] [Fintype F]
    (C : Submodule F (Matrix (Fin 12) (Fin 12) F)) (hC : Supported C)
    (hd : Module.finrank F C = 27) (hr : MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C) :
    ∃ M ∈ C, M ≠ 0 ∧ M.rank = 9 := by
  let p := (prefixProjection (F := F) 3).comp C.subtype
  have hn : ¬ Function.Injective p := by
    intro hi
    have hle := LinearMap.finrank_le_finrank_of_injective hi
    rw [hd, Module.finrank_fintype_fun_eq_card] at hle
    have hc : Fintype.card (PrefixEntries 3) = 18 := by decide
    omega
  have hk : LinearMap.ker p ≠ ⊥ := fun h => hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨M, hM, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hM' : prefixProjection 3 M.val = 0 := hM
  have h9 := rank_le_of_prefixProjection_eq_zero hC M 3 hM'
  have hc : (Finset.univ.filter (fun j : Fin 12 => 3 ≤ j.val)).card = 9 := by decide
  rw [hc] at h9
  have hval : M.val ≠ 0 := fun hv => hne (Subtype.ext hv)
  exact ⟨M.val, M.property, hval, le_antisymm h9 (hr M.val M.property hval)⟩

/-- The existence condition in the projection equivalence.

Used by
- `FerrersRankNine.problem1RankNine_iff_exists_supported_dim27` -/
def SupportedDimension27WithRankLowerBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F],
    Odd (Fintype.card F) → 3 < Fintype.card F →
      ∃ C : Submodule F (Matrix (Fin 12) (Fin 12) F), Supported C ∧ Module.finrank F C = 27 ∧
        MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C

/-- The two projections upgrade existence to exact minimum rank and optimality.

Used by
- `FerrersRankNine.problem1_rank_nine` -/
theorem problem1RankNine_iff_exists_supported_dim27 :
    Problem1RankNine ↔ SupportedDimension27WithRankLowerBound := by
  constructor
  · intro h F _ _ ho hq
    obtain ⟨C, hs, hd, hr, _⟩ := (h F ho hq).1
    exact ⟨C, hs, hd, hr⟩
  · intro h F _ _ ho hq
    obtain ⟨C, hs, hd, hr⟩ := h F ho hq
    exact ⟨⟨C, hs, hd, hr, exists_rank_eq_nine_of_finrank_eq_27 C hs hd hr⟩,
      finrank_le_27_of_supported_of_rank⟩

private theorem fieldRanges_nested {F K L E : Type*} [Field F] [Field K] [Field L] [Field E]
    [Algebra F K] [Algebra F L] [Algebra F E] (f : K →ₐ[F] L) (g : L →ₐ[F] E) :
    (g.comp f).fieldRange ≤ g.fieldRange := by
  apply IntermediateField.toSubalgebra_le_toSubalgebra.mp
  simpa only [AlgHom.fieldRange_toSubalgebra] using AlgHom.range_comp_le_range f g

/-- Realize the degree-three and degree-six extensions inside the degree-twelve field.

Used by
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
private theorem exists_field_tower (F : Type*) [Field F] [Finite F] :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra F E),
      ∃ K L : IntermediateField F E, K ≤ L ∧
        Module.finrank F K = 3 ∧ Module.finrank F L = 6 ∧ Module.finrank F E = 12 := by
  let p := ringChar F
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let K := FiniteField.Extension F p 3
  let L := FiniteField.Extension F p 6
  let E := FiniteField.Extension F p 12
  have hK : Module.finrank F K = 3 := FiniteField.finrank_extension F p 3
  have hL : Module.finrank F L = 6 := FiniteField.finrank_extension F p 6
  have hE : Module.finrank F E = 12 := FiniteField.finrank_extension F p 12
  obtain ⟨f⟩ : Nonempty (K →ₐ[F] L) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by rw [hK, hL]; decide)
  obtain ⟨g⟩ : Nonempty (L →ₐ[F] E) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by rw [hL, hE]; decide)
  exact ⟨E, inferInstance, inferInstance, inferInstance, (g.comp f).fieldRange, g.fieldRange,
    fieldRanges_nested f g, (g.comp f).equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hK,
    g.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hL, hE⟩

private theorem exists_nonfixed {K L : Type*} [Field K] [Fintype K] [Field L] [Finite L]
    [Algebra K L] (h : Module.finrank K L = 2) :
    ∃ b : L, b ^ Fintype.card K - b ≠ 0 := by
  by_contra! hzero
  have heq : FiniteField.frobeniusAlgHom K L = 1 := by
    ext b
    exact sub_eq_zero.mp (hzero b)
  have horder := FiniteField.orderOf_frobeniusAlgHom K L
  rw [heq, orderOf_one, h] at horder
  omega

/-- The two relative degrees over the smallest intermediate field.

Used by
- `FerrersRankNine.finrank_extendScalars_toSubmodule`
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
private theorem nested_relative_finranks {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite E] {K L : IntermediateField F E} (hKL : K ≤ L)
    (hK : Module.finrank F K = 3) (hL : Module.finrank F L = 6)
    (hE : Module.finrank F E = 12) :
    letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    Module.finrank K L = 2 ∧ Module.finrank K E = 4 := by
  let : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algHom (IntermediateField.inclusion hKL)
  have h₁ := Module.finrank_mul_finrank F K L
  have h₂ := Module.finrank_mul_finrank F K E
  rw [hK, hL] at h₁
  rw [hK, hE] at h₂
  exact ⟨by omega, by omega⟩

/-- Choose a vector outside the smaller field with nonzero Frobenius difference.

Used by
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
private theorem exists_b_in_flag_with_nonzero_determinant {F E : Type*}
    [Field F] [Fintype F] [Field E] [Algebra F E] [Finite E]
    {K L : IntermediateField F E} (hKL : K ≤ L)
    (hK : Module.finrank F K = 3) (hL : Module.finrank F L = 6) (hE : Module.finrank F E = 12) :
    ∃ b : L, (b : E) ∉ K ∧ (b : E) ^ Fintype.card F ^ 3 - (b : E) ≠ 0 := by
  let : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨b, hb⟩ := exists_nonfixed (K := K) (L := L)
    (nested_relative_finranks hKL hK hL hE).1
  have hc : Fintype.card K = Fintype.card F ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  have hbE : (b : E) ^ Fintype.card K - (b : E) ≠ 0 := by
    intro hz
    apply hb
    apply L.val.injective
    change ((b ^ Fintype.card K - b : L) : E) = 0
    exact hz
  refine ⟨b, ?_, by rwa [hc] at hbE⟩
  intro hbK
  apply hbE
  exact sub_eq_zero.mpr (by
    have hx := congrArg (fun x : K => (x : E)) (FiniteField.pow_card (⟨(b : E), hbK⟩ : K))
    simpa only [IntermediateField.coe_pow] using hx)

section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Finite E]
variable {K L : IntermediateField F E}

omit [Finite E] in
/-- Extend the ordered pair consisting of one and a vector outside the smaller field.

Used by
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
private theorem exists_ordered_basis_over_K {b : E} (hb : b ∉ K)
    (h : finrank K E = 4) :
    ∃ β : Basis (Fin 4) K E, β 0 = 1 ∧ β 1 = b := by
  let v : Fin 1 → E := fun _ => 1
  have hv : LinearIndependent K v := .of_subsingleton 0 one_ne_zero
  have hb' : b ∉ Submodule.span K (Set.range v) := by
    intro hmem
    have hr : Set.range v = {1} := by ext; simp [v]
    rw [hr, Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    rw [Algebra.smul_def, mul_one] at ha
    exact hb (ha ▸ a.property)
  have hv₂ := hv.finSnoc hb'
  obtain ⟨c, hc⟩ := exists_linearIndependent_snoc_of_lt_finrank hv₂ (by rw [h]; decide)
  obtain ⟨d, hd⟩ := exists_linearIndependent_snoc_of_lt_finrank hc (by rw [h]; decide)
  let β := basisOfLinearIndependentOfCardEqFinrank hd (by simpa using h.symm)
  refine ⟨β, ?_, ?_⟩
  · change β 0 = 1
    rw [show ⇑β = _ from coe_basisOfLinearIndependentOfCardEqFinrank hd _]
    rfl
  · change β 1 = b
    rw [show ⇑β = _ from coe_basisOfLinearIndependentOfCardEqFinrank hd _]
    rfl

private theorem finrank_extendScalars_toSubmodule (hKL : K ≤ L) (hK : finrank F K = 3)
    (hL : finrank F L = 6) (hE : finrank F E = 12) :
    finrank K (IntermediateField.extendScalars hKL).toSubalgebra.toSubmodule = 2 := by
  let : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  rw [Subalgebra.finrank_toSubmodule, IntermediateField.finrank_eq_finrank_subalgebra]
  exact (nested_relative_finranks hKL hK hL hE).1

/-- The first two basis vectors span the larger intermediate field.

Used by
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
private theorem flag_two_eq_extendScalars_toSubmodule (hKL : K ≤ L) (hK : finrank F K = 3)
    (hL : finrank F L = 6) (hE : finrank F E = 12)
    (β : Basis (Fin 4) K E) {b : L} (hβ0 : β 0 = 1) (hβ1 : β 1 = b.val) :
    β.flag 2 = (IntermediateField.extendScalars hKL).toSubalgebra.toSubmodule := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply β.flag_le_iff.mpr
    intro i hi
    fin_cases i
    · exact hβ0 ▸ L.one_mem
    · exact hβ1 ▸ b.property
    · exact (by decide : ¬ ((2 : Fin 4).castSucc < (2 : Fin 5))) hi |>.elim
    · exact (by decide : ¬ ((3 : Fin 4).castSucc < (2 : Fin 5))) hi |>.elim
  · rw [finrank_extendScalars_toSubmodule hKL hK hL hE]
    have he : β '' {i : Fin 4 | i.castSucc < (2 : Fin 5)} =
        Set.range (fun i : Fin 2 => β (Fin.castLE (by decide) i)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i.val, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.castLE (by decide) i, i.isLt, rfl⟩
    unfold Basis.flag
    rw [he]
    have hi : LinearIndependent K (fun i : Fin 2 => β (Fin.castLE (by decide) i)) :=
      β.linearIndependent.comp (Fin.castLE (by decide)) (Fin.castLE_injective _)
    rw [finrank_span_eq_card hi]
    rfl

/-- Order the scalar tower basis in successive triples.

Used by
- `FerrersRankNine.codeMap`
- `FerrersRankNine.codeMap_rank`
- `FerrersRankNine.codeMap_supported` -/
private noncomputable def orderedTowerBasis (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E) :
    Basis (Fin 12) F E :=
  (κ.smulTower' β).reindex finProdFinEquiv

omit [Finite E] in
/-- An input vector is a scaled vector from the upper basis.

Used by
- `FerrersRankNine.codeMap_supported` -/
private theorem orderedTowerBasis_apply (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    (i : Fin 12) :
    orderedTowerBasis κ β i =
      κ ((finProdFinEquiv (m := 4) (n := 3)).symm i).2 •
        β ((finProdFinEquiv (m := 4) (n := 3)).symm i).1 := by
  rw [orderedTowerBasis, Basis.reindex_apply, Basis.smulTower'_apply]

omit [Finite E] in
private theorem orderedTowerBasis_repr (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    (y : E) (i : Fin 12) :
    (orderedTowerBasis κ β).repr y i =
      κ.repr (β.repr y ((finProdFinEquiv (m := 4) (n := 3)).symm i).1)
        ((finProdFinEquiv (m := 4) (n := 3)).symm i).2 := by
  rw [orderedTowerBasis, Basis.repr_reindex_apply, Basis.smulTower'_repr]

omit [Finite E] in
/-- Membership in the upper flag forces zero coordinates after the corresponding triples.

Used by
- `FerrersRankNine.codeMap_supported` -/
private theorem orderedTowerBasis_repr_eq_zero_of_mem_flag
    (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    {y : E} {k : Fin 5} (hy : y ∈ β.flag k) {i : Fin 12} (hi : 3 * k.val ≤ i.val) :
    (orderedTowerBasis κ β).repr y i = 0 := by
  rw [orderedTowerBasis_repr, (β.mem_flag_iff_repr_eq_zero.mp hy)]
  · simp
  · change k.val ≤ i.val / 3
    omega

end

section

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Algebra F E] [Finite E]
variable {K L : IntermediateField F E}

private noncomputable def evaluationMap : (Fin 4 → E) →ₗ[F] (E →ₗ[F] E) where
  toFun := evaluateLinearized F E
  map_add' a b := by
    ext x
    simp [evaluateLinearized_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    ext x
    simp [evaluateLinearized_apply, Algebra.smul_def, mul_assoc]

private noncomputable def codeMap (b : E) (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E) :
    Params K L →ₗ[F] Matrix (Fin 12) (Fin 12) F :=
  let B := orderedTowerBasis κ β
  (LinearMap.toMatrix B B).toLinearMap.comp ((evaluationMap (F := F)).comp
    (paramCoefficients b (β 2)))

omit [Finite E] in
private theorem codeMap_rank (b : E) (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    (p : Params K L) :
    (codeMap b κ β p).rank = finrank F (LinearMap.range
      (evaluateLinearized F E (paramCoefficients b (β 2) p))) := by
  let B := orderedTowerBasis κ β
  rw [Matrix.rank_eq_finrank_range_toLin _ B B]
  change finrank F (LinearMap.range (Matrix.toLin B B
    (LinearMap.toMatrix B B (evaluateLinearized F E (paramCoefficients b (β 2) p))))) = _
  rw [Matrix.toLin_toMatrix]

private theorem codeMap_injective {b : E} (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    (hE : finrank F E = 12) (hb : b ^ Fintype.card F ^ 3 - b ≠ 0)
    (hKL : K ≤ L)
    (hflag : β.flag 2 = (IntermediateField.extendScalars hKL).toSubalgebra.toSubmodule) :
    Function.Injective (codeMap b κ β (L := L)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro p hp
  change codeMap b κ β p = 0 at hp
  by_contra hn
  have hi := paramCoefficients_injective hb β hKL hflag
  have hne : paramCoefficients b (β 2) p ≠ 0 := fun he =>
    hn (hi (he.trans ((paramCoefficients b (β 2)).map_zero).symm))
  have hr := finrank_range_evaluateLinearized_ge_nine F E hE _ hne
  rw [← codeMap_rank b κ β p, hp, Matrix.rank_zero] at hr
  omega

private theorem codeMap_supported {b : L} (κ : Basis (Fin 3) F K) (β : Basis (Fin 4) K E)
    (hK : finrank F K = 3) (hb : (b : E) ^ Fintype.card F ^ 3 - (b : E) ≠ 0)
    (hβ0 : β 0 = 1) (hβ1 : β 1 = (b : E)) (hKL : K ≤ L)
    (hflag : β.flag 2 = (IntermediateField.extendScalars hKL).toSubalgebra.toSubmodule) :
    Supported (LinearMap.range (codeMap b.val κ β (L := L))) := by
  intro M hM i j hij
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hM
  let B := orderedTowerBasis κ β
  let f := evaluateLinearized F E (paramCoefficients b.val (β 2) p)
  change LinearMap.toMatrix B B f i j = 0
  rw [LinearMap.toMatrix_apply]
  let d := (finProdFinEquiv (m := 4) (n := 3)).symm j
  let x : K := κ d.2
  have hBj : B j = x • β d.1 := orderedTowerBasis_apply κ β j
  have hd : d.1.val = j.val / 3 := rfl
  have hmapl (y : E) (hy : y ∈ L) : y ∈ β.flag 2 := by
    rw [hflag]
    exact hy
  have h23 (y : E) (hy : y ∈ L) : y ∈ β.flag 3 :=
    β.flag_mono (by decide : (2 : Fin 5) ≤ 3) (hmapl y hy)
  by_cases hj3 : j.val < 3
  · have hd0 : d.1 = 0 := Fin.ext (by simp only [hd]; omega)
    have he : B j = (x : E) := by
      rw [hBj, hd0, hβ0, Algebra.smul_def, mul_one]
      rfl
    rw [he]
    apply orderedTowerBasis_repr_eq_zero_of_mem_flag (k := 2)
    · apply hmapl
      change evaluateLinearized F E (paramCoefficients b.val (β 2) p) (x : E) ∈ L
      rw [evaluation_on_K hK]
      exact L.add_mem (L.add_mem (L.mul_mem p.1.property (hKL x.property))
        (L.mul_mem p.2.1.property (L.toSubfield.pow_mem (hKL x.property) (Fintype.card F))))
        (L.mul_mem p.2.2.1.property (L.toSubfield.pow_mem (hKL x.property) (Fintype.card F ^ 2)))
    · simpa [height, hj3] using hij
  · by_cases hj6 : j.val < 6
    · have hd1 : d.1 = 1 := Fin.ext (by simp only [hd]; omega)
      have he : B j = (b : E) * (x : E) := by
        rw [hBj, hd1, hβ1, Algebra.smul_def, IntermediateField.algebraMap_apply, mul_comm]
      rw [he]
      apply orderedTowerBasis_repr_eq_zero_of_mem_flag (k := 3)
      · change evaluateLinearized F E (paramCoefficients b.val (β 2) p)
            ((b : E) * (x : E)) ∈ β.flag 3
        rw [evaluation_on_bK hK _ _ hb, add_mul]
        have hm : (b : E) * (x : E) ∈ L := L.mul_mem b.property (hKL x.property)
        have hw : β 2 * (p.2.2.2.2 : E) * (x : E) ∈ β.flag 3 := by
          have ht := (β.flag 3).smul_mem (p.2.2.2.2 * x)
            (β.self_mem_flag (i := 2) (k := 3) (by decide))
          rw [Algebra.smul_def, IntermediateField.algebraMap_apply, mul_comm _ (β 2),
            IntermediateField.coe_mul, ← mul_assoc] at ht
          exact ht
        exact add_mem (add_mem (add_mem
          (h23 _ (L.mul_mem p.2.2.2.1.property (hKL x.property))) hw)
          (h23 _ (L.mul_mem p.2.1.property (L.toSubfield.pow_mem hm (Fintype.card F)))))
          (h23 _ (L.mul_mem p.2.2.1.property (L.toSubfield.pow_mem hm (Fintype.card F ^ 2))))
      · simpa [height, hj3, hj6] using hij
    · simp [height, hj3, hj6] at hij
      omega

private theorem exists_supported_dim27_with_rank (F : Type) [Field F] [Fintype F] :
    ∃ C : Submodule F (Matrix (Fin 12) (Fin 12) F), Supported C ∧ finrank F C = 27 ∧
      MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C := by
  obtain ⟨E, instField, instFinite, instAlg, K, L, hKL, hK, hL, hE⟩ := exists_field_tower F
  obtain ⟨b, hbK, hb⟩ := exists_b_in_flag_with_nonzero_determinant hKL hK hL hE
  obtain ⟨β, hβ0, hβ1⟩ := exists_ordered_basis_over_K hbK
    (nested_relative_finranks hKL hK hL hE).2
  let κ := Module.finBasisOfFinrankEq F K hK
  have hflag := flag_two_eq_extendScalars_toSubmodule hKL hK hL hE β hβ0 hβ1
  let m := codeMap (K := K) (L := L) (b : E) κ β
  have hi := codeMap_injective κ β hE hb hKL hflag
  refine ⟨LinearMap.range m, codeMap_supported κ β hK hb hβ0 hβ1 hKL hflag, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hi]
    change finrank F (L × L × L × L × K) = 27
    simp [Module.finrank_prod, hK, hL]
  · intro M hM hne
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hM
    have hcoeff : paramCoefficients (b : E) (β 2) p ≠ 0 := by
      intro hc
      apply hne
      change LinearMap.toMatrix _ _ (evaluationMap (paramCoefficients (b : E) (β 2) p)) = 0
      rw [hc, map_zero, map_zero]
    exact (codeMap_rank (b : E) κ β p).symm ▸
      finrank_range_evaluateLinearized_ge_nine F E hE _ hcoeff

/-- The rank-nine example in Jin–Ning–Xu–Duan, Problem 1. -/
theorem problem1_rank_nine : Problem1RankNine :=
  problem1RankNine_iff_exists_supported_dim27.mpr
    (fun F _ _ _ _ => exists_supported_dim27_with_rank F)

end

end D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
