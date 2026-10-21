/- GID: D5/S3/Quantum/Codes/CssTDoublingMapImprovement
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/CssTDoublingMapImprovement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A cyclic binary doubling map gives a CSS extension of greater distance than identity. -/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Tactic

/-! A binary circulant improves the distance of an admissible CSS-T doubling construction. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Module

namespace D5.S3.Quantum.Codes.CssTDoublingMapImprovement

/-- The infimum of the weights in the two nontrivial CSS quotient legs. -/
noncomputable def cssDistance {ι : Type*} [Fintype ι]
    (C₂ C₁ : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  sInf ({d | ∃ x, x ∈ C₁ ∧ x ∉ C₂ ∧ hammingNorm x = d} ∪
    {d | ∃ z, z ∈ C₂.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) ∧
      z ∉ C₁.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) ∧ hammingNorm z = d})

/-- The graph embedding used to extend a subcode. -/
def extensionMap {n : ℕ} {C C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : C ≤ C₁) (φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    C →ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2) where
  toFun x := Sum.elim x.val (φ ⟨x.val, h x.property⟩)
  map_add' x y := by
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact congrFun (φ.map_add ⟨x.val, h x.property⟩ ⟨y.val, h y.property⟩) j
  map_smul' a x := by
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact congrFun (φ.map_smul a ⟨x.val, h x.property⟩) j

/-- The extension code consists of pairs `(x, φ x)` with `x` in the subcode. -/
def extension {n : ℕ} {C C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : C ≤ C₁) (φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  LinearMap.range (extensionMap h φ)

/-- The triple-product parity condition characterizing an admissible CSS-T extension. -/
def admissible {n : ℕ} (C₂ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : C₂ ≤ C₁) (φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)) : Prop :=
  ∀ (x y : C₁) (z : C₂),
    (∑ i, x.val i * y.val i * z.val i) +
      (∑ i, φ x i * φ y i * φ ⟨z.val, h z.property⟩ i) = 0

/-- An admissible extension can strictly improve distance at equal length and dimension. -/
def claim : Prop :=
  ∃ (n : ℕ) (C₂ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)) (h : C₂ ≤ C₁),
    finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ ∧
      ∃ φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2), admissible C₂ C₁ h φ ∧
        cssDistance (extension h φ) (extension (le_refl C₁) φ) >
          cssDistance (extension h C₁.subtype) (extension (le_refl C₁) C₁.subtype)

noncomputable section

private def diagonalMap : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 26 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)

private lemma diagonalMap_injective : Function.Injective diagonalMap := by
  apply LinearMap.funLeft_injective_of_surjective
  intro i
  refine ⟨(finProdFinEquiv (m := 2) (n := 13)) (0, i), ?_⟩
  exact congrArg Prod.snd ((finProdFinEquiv (m := 2) (n := 13)).symm_apply_apply (0, i))

private def parityMap : (Fin 13 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id)

private def C₁ := LinearMap.range diagonalMap
private def C₂₀ := LinearMap.ker parityMap
private def diagonalParityMap := diagonalMap.comp C₂₀.subtype
private def C₂ := LinearMap.range diagonalParityMap

private lemma C₂_le_C₁ : C₂ ≤ C₁ :=
  LinearMap.range_comp_le_range C₂₀.subtype diagonalMap

private lemma parity_unit (i : Fin 13) : parityMap (Pi.single i 1) = 1 := by
  exact LinearMap.lsum_piSingle (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2)
    (fun _ => LinearMap.id) i 1

private lemma rank_strict : finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ := by
  have hn : parityMap ≠ 0 := by
    intro h
    have : parityMap (Pi.single 0 1) = 0 := congrArg (fun f => f (Pi.single 0 1)) h
    rw [parity_unit] at this
    exact one_ne_zero this
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have hi : Function.Injective diagonalParityMap := by
    intro x y h
    exact Subtype.ext (diagonalMap_injective h)
  have h₁ := LinearMap.finrank_range_of_inj diagonalMap_injective
  have h₂ := LinearMap.finrank_range_of_inj hi
  change finrank (ZMod 2) C₂₀ + 1 = finrank (ZMod 2) (Fin 13 → ZMod 2) at hk
  change finrank (ZMod 2) C₁ = finrank (ZMod 2) (Fin 13 → ZMod 2) at h₁
  change finrank (ZMod 2) C₂ = finrank (ZMod 2) C₂₀ at h₂
  omega

private def cyclicMap : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2) where
  toFun x i := x i + x (i + 1) + x (i + 2)
  map_add' x y := by ext i; simp only [Pi.add_apply]; ring
  map_smul' a x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def liftedMap (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) :
    C₁ →ₗ[ZMod 2] (Fin 26 → ZMod 2) :=
  (diagonalMap.comp f).comp
    (LinearEquiv.ofInjective diagonalMap diagonalMap_injective).symm.toLinearMap

private lemma liftedMap_apply (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (x : Fin 13 → ZMod 2) :
    liftedMap f ⟨diagonalMap x, ⟨x, rfl⟩⟩ = diagonalMap (f x) := by
  exact congrArg (fun y => diagonalMap (f y))
    ((LinearEquiv.ofInjective diagonalMap diagonalMap_injective).symm_apply_apply x)

private def graphVector (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (x : Fin 13 → ZMod 2) : (Fin 26 ⊕ Fin 26 → ZMod 2) :=
  Sum.elim (diagonalMap x) (diagonalMap (f x))

private lemma mem_extension_upper (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (v : Fin 26 ⊕ Fin 26 → ZMod 2) :
    v ∈ extension (le_refl C₁) (liftedMap f) ↔ ∃ x, graphVector f x = v := by
  constructor
  · rintro ⟨⟨v, x, rfl⟩, rfl⟩
    exact ⟨x, by ext i; cases i <;> simp only [extensionMap, graphVector,
      LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, liftedMap_apply]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨⟨diagonalMap x, ⟨x, rfl⟩⟩, ?_⟩
    ext i
    cases i <;> simp only [extensionMap, graphVector, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, liftedMap_apply]

private lemma mem_extension_lower (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (v : Fin 26 ⊕ Fin 26 → ZMod 2) :
    v ∈ extension C₂_le_C₁ (liftedMap f) ↔
      ∃ x, parityMap x = 0 ∧ graphVector f x = v := by
  constructor
  · rintro ⟨⟨v, ⟨x, hx⟩, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    ext i
    cases i <;> simp only [extensionMap, graphVector, diagonalParityMap,
      LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, liftedMap_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨diagonalMap x, ⟨⟨x, hx⟩, rfl⟩⟩, ?_⟩
    ext i
    cases i <;> simp only [extensionMap, graphVector, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, liftedMap_apply]

private lemma diagonal_eval (x : Fin 13 → ZMod 2) (a : Fin 2) (i : Fin 13) :
    diagonalMap x ((finProdFinEquiv (m := 2) (n := 13)) (a, i)) = x i := by
  exact congrArg (fun p => x p.2)
    ((finProdFinEquiv (m := 2) (n := 13)).symm_apply_apply (a, i))

private lemma sum_blocks {R : Type*} [AddCommMonoid R] (g : Fin 26 → R) :
    (∑ i, g i) = (∑ j, g ((finProdFinEquiv (m := 2) (n := 13)) (0, j))) +
      ∑ j, g ((finProdFinEquiv (m := 2) (n := 13)) (1, j)) := by
  rw [← (finProdFinEquiv (m := 2) (n := 13)).sum_comp g, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma admissible_witness : admissible C₂ C₁ C₂_le_C₁ (liftedMap cyclicMap) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ ⟨_, ⟨z, hz⟩, rfl⟩
  change (∑ i, diagonalMap x i * diagonalMap y i * diagonalMap z i) +
    (∑ i, liftedMap cyclicMap ⟨diagonalMap x, _⟩ i *
      liftedMap cyclicMap ⟨diagonalMap y, _⟩ i *
      liftedMap cyclicMap ⟨diagonalMap z, _⟩ i) = 0
  rw [liftedMap_apply, liftedMap_apply, liftedMap_apply, sum_blocks, sum_blocks]
  simp only [diagonal_eval, CharTwo.add_self_eq_zero]

private lemma lifted_id :
    liftedMap (LinearMap.id : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) = C₁.subtype := by
  apply LinearMap.ext
  rintro ⟨_, x, rfl⟩
  exact liftedMap_apply _ x

private lemma graph_injective (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) :
    Function.Injective (graphVector f) := by
  intro x y h
  apply diagonalMap_injective
  funext i
  exact congrFun h (Sum.inl i)

private lemma weight_one
    (x : Fin 13 → ZMod 2) (h : hammingNorm x = 1) : ∃ i, x = Pi.single i 1 := by
  change (Finset.univ.filter (fun i => x i ≠ 0)).card = 1 at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hs (j : Fin 13) : x j ≠ 0 ↔ j = i := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] using (Finset.ext_iff.mp hi j)
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    rw [show x i = 1 from Fin.eq_one_of_ne_zero (x i) ((hs i).mpr rfl)]
    exact (Pi.single_eq_same (M := fun _ : Fin 13 => ZMod 2) i 1).symm
  · have hz : x j = 0 := by simpa only [not_not] using mt (hs j).mp hj
    rw [hz]
    exact (Pi.single_eq_of_ne (M := fun _ : Fin 13 => ZMod 2) hj 1).symm

private lemma weight_cyclic_unit (i : Fin 13) : hammingNorm (cyclicMap (Pi.single i 1)) = 3 := by
  fin_cases i <;> decide

private lemma cyclic_kernel (x : Fin 13 → ZMod 2) (h : cyclicMap x = 0) : x = 0 := by
  have hz (i : Fin 13) : x i + x (i + 1) + x (i + 2) = 0 := congrFun h i
  have hp (i : Fin 13) : x (i + 3) = x i := by
    have hh := hz (i + 1)
    rw [show i + 1 + 1 = i + 2 by rw [add_assoc]; rfl,
      show i + 1 + 2 = i + 3 by rw [add_assoc]; rfl] at hh
    have he : x i = x (i + 1) + x (i + 2) :=
      CharTwo.add_eq_zero.mp ((add_assoc _ _ _).symm.trans (hz i))
    have hf : x (i + 1) + x (i + 2) = x (i + 3) := CharTwo.add_eq_zero.mp hh
    exact (he.trans hf).symm
  have horbit (k : ℕ) : x (k • (3 : Fin 13)) = x 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simpa only [succ_nsmul] using (hp (k • (3 : Fin 13))).trans ih
  have hc (i : Fin 13) : x i = x 0 := by
    have hi : (9 * i.val) • (3 : Fin 13) = i := by fin_cases i <;> decide
    rw [← hi]
    exact horbit _
  have hzero : x 0 = 0 := by
    have hh := hz 0
    rw [hc (0 + 1), hc (0 + 2), CharTwo.add_self_eq_zero, zero_add] at hh
    exact hh
  funext i
  exact (hc i).trans hzero

private lemma x_weight_bound (x : Fin 13 → ZMod 2) (hx : parityMap x ≠ 0) :
    8 ≤ hammingNorm (graphVector cyclicMap x) := by
  have hn : x ≠ 0 := by intro h; exact hx (h ▸ parityMap.map_zero)
  have ha : cyclicMap x ≠ 0 := fun h => hn (cyclic_kernel x h)
  have hp : 0 < hammingNorm x := hammingNorm_pos_iff.mpr hn
  have hq : 0 < hammingNorm (cyclicMap x) := hammingNorm_pos_iff.mpr ha
  have ht : hammingNorm x ≠ 2 := by
    intro h
    apply hx
    change (∑ i, x i) = 0
    have hp : (∑ i, x i) = (hammingNorm x : ZMod 2) := by
      rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x i = 0
      · rw [hi]; norm_num
      · rw [show x i = 1 from Fin.eq_one_of_ne_zero (x i) hi]; norm_num
    rw [hp, h]
    decide
  have hw : hammingNorm (graphVector cyclicMap x) =
      2 * (hammingNorm x + hammingNorm (cyclicMap x)) := by
    rw [hammingNorm, Finset.card_filter, Fintype.sum_sum_type, sum_blocks, sum_blocks]
    simp only [graphVector, Sum.elim_inl, Sum.elim_inr, diagonal_eval]
    rw [← Finset.card_filter, ← Finset.card_filter]
    change hammingNorm x + hammingNorm x +
      (hammingNorm (cyclicMap x) + hammingNorm (cyclicMap x)) = _
    omega
  rw [hw]
  by_cases hs : hammingNorm x = 1
  · obtain ⟨i, rfl⟩ := weight_one x hs
    rw [weight_cyclic_unit]
    omega
  · omega

private def transposeVector (w : Fin 13 → ZMod 2) :
    (Fin 13 → ZMod 2) := fun i => w i + w (i - 1) + w (i - 2)

private lemma sum_shift (x w : (Fin 13 → ZMod 2)) (k : Fin 13) :
    (∑ i, x (i + k) * w i) = ∑ i, x i * w (i - k) := by
  simpa only [dotProduct, Function.comp_apply, Equiv.coe_addRight, Equiv.addRight_symm,
    sub_eq_add_neg] using (dotProduct_comp_equiv_symm x w (Equiv.addRight k)).symm

private lemma transpose_dot (x w : (Fin 13 → ZMod 2)) :
    dotProduct (cyclicMap x) w = dotProduct x (transposeVector w) := by
  change (∑ i, (x i + x (i + 1) + x (i + 2)) * w i) =
    ∑ i, x i * (w i + w (i - 1) + w (i - 2))
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_shift x w 1, sum_shift x w 2]

private lemma transpose_weight (w : Fin 13 → ZMod 2) :
    hammingNorm (transposeVector w) ≤ 3 * hammingNorm w := by
  have h₁ : hammingNorm (w + fun i => w (i - 1)) ≤
      hammingNorm w + hammingNorm (fun i => w (i - 1)) := by
    have h := hammingDist_triangle (-w) 0 (fun i => w (i - 1))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -w = w := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₂ : hammingNorm (transposeVector w) ≤
      hammingNorm (w + fun i => w (i - 1)) + hammingNorm (fun i => w (i - 2)) := by
    have h := hammingDist_triangle (-(w + fun i => w (i - 1))) 0 (fun i => w (i - 2))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(w + fun i => w (i - 1)) = (w + fun i => w (i - 1)) := by
      ext i
      exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₃ := (Equiv.subRight (1 : Fin 13)).sum_comp
    (fun i => if w i ≠ 0 then (1 : ℕ) else 0)
  have h₄ := (Equiv.subRight (2 : Fin 13)).sum_comp
    (fun i => if w i ≠ 0 then (1 : ℕ) else 0)
  rw [← Finset.card_filter, ← Finset.card_filter] at h₃ h₄
  change hammingNorm (fun i => w (i - 1)) = hammingNorm w at h₃
  change hammingNorm (fun i => w (i - 2)) = hammingNorm w at h₄
  omega

private def leftBlock (z : Fin 26 ⊕ Fin 26 → ZMod 2) (a : Fin 2) : (Fin 13 → ZMod 2) :=
  fun i => z (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (a, i)))

private def rightBlock (z : Fin 26 ⊕ Fin 26 → ZMod 2) (a : Fin 2) : (Fin 13 → ZMod 2) :=
  fun i => z (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (a, i)))

private def leftSum (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    (Fin 13 → ZMod 2) := leftBlock z 0 + leftBlock z 1
private def rightSum (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    (Fin 13 → ZMod 2) := rightBlock z 0 + rightBlock z 1
private def syndrome (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    (Fin 13 → ZMod 2) := leftSum z + transposeVector (rightSum z)

private lemma weight_block_sums (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    hammingNorm (leftSum z) + hammingNorm (rightSum z) ≤ hammingNorm z := by
  have h₁ : hammingNorm (leftSum z) ≤
      hammingNorm (leftBlock z 0) + hammingNorm (leftBlock z 1) := by
    have h := hammingDist_triangle (-(leftBlock z 0)) 0 (leftBlock z 1)
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(leftBlock z 0) = (leftBlock z 0) := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₂ : hammingNorm (rightSum z) ≤
      hammingNorm (rightBlock z 0) + hammingNorm (rightBlock z 1) := by
    have h := hammingDist_triangle (-(rightBlock z 0)) 0 (rightBlock z 1)
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(rightBlock z 0) = (rightBlock z 0) := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  calc
    _ ≤ hammingNorm (leftBlock z 0) + hammingNorm (leftBlock z 1) +
        (hammingNorm (rightBlock z 0) + hammingNorm (rightBlock z 1)) := Nat.add_le_add h₁ h₂
    _ = hammingNorm z := by
      symm
      rw [hammingNorm, Finset.card_filter, Fintype.sum_sum_type, sum_blocks, sum_blocks]
      rw [hammingNorm, Finset.card_filter, hammingNorm, Finset.card_filter,
        hammingNorm, Finset.card_filter, hammingNorm, Finset.card_filter]
      rfl

private lemma graph_dot (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (x : Fin 13 → ZMod 2) (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    dotProduct (graphVector f x) z =
      dotProduct x (leftSum z) + dotProduct (f x) (rightSum z) := by
  have h := sumElim_dotProduct_sumElim (diagonalMap x) (z ∘ Sum.inl)
    (diagonalMap (f x)) (z ∘ Sum.inr)
  rw [Sum.elim_comp_inl_inr] at h
  rw [show dotProduct (graphVector f x) z = _ from h]
  change (∑ i, diagonalMap x i * z (Sum.inl i)) +
    (∑ i, diagonalMap (f x) i * z (Sum.inr i)) = _
  rw [sum_blocks, sum_blocks]
  simp only [diagonal_eval]
  change (∑ i, x i * leftBlock z 0 i) + (∑ i, x i * leftBlock z 1 i) +
    ((∑ i, f x i * rightBlock z 0 i) + (∑ i, f x i * rightBlock z 1 i)) = _
  rw [show leftSum z = leftBlock z 0 + leftBlock z 1 from rfl,
    show rightSum z = rightBlock z 0 + rightBlock z 1 from rfl,
    dotProduct_add, dotProduct_add]
  rfl

private lemma cyclic_graph_dot (x : Fin 13 → ZMod 2) (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    dotProduct (graphVector cyclicMap x) z = dotProduct x (syndrome z) := by
  rw [graph_dot, transpose_dot]
  exact (dotProduct_add x (leftSum z) (transposeVector (rightSum z))).symm

private lemma syndrome_one (z : Fin 26 ⊕ Fin 26 → ZMod 2)
    (h₂ : z ∈ (extension C₂_le_C₁ (liftedMap cyclicMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2)))
    (h₁ : z ∉ (extension (le_refl C₁) (liftedMap cyclicMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2))) :
    syndrome z = fun _ => 1 := by
  have horth (x : Fin 13 → ZMod 2) (hx : parityMap x = 0) : dotProduct x (syndrome z) = 0 := by
    rw [← cyclic_graph_dot]
    exact h₂ _ ((mem_extension_lower _ _).mpr ⟨x, hx, rfl⟩)
  have hc (i : Fin 13) : syndrome z i = syndrome z 0 := by
    have hp : parityMap (Pi.single i 1 + Pi.single 0 1) = 0 := by
      rw [map_add, parity_unit, parity_unit]
      decide
    have hh := horth _ hp
    rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct] at hh
    exact CharTwo.add_eq_zero.mp hh
  have hn : syndrome z 0 ≠ 0 := by
    intro hz
    apply h₁
    intro v hv
    obtain ⟨x, rfl⟩ := (mem_extension_upper _ _).mp hv
    change dotProduct (graphVector cyclicMap x) z = 0
    rw [cyclic_graph_dot]
    have he : syndrome z = 0 := funext (fun i => (hc i).trans hz)
    rw [he, dotProduct_zero]
  have ho : syndrome z 0 = 1 := Fin.eq_one_of_ne_zero _ hn
  exact funext (fun i => (hc i).trans ho)

private lemma z_weight_bound (z : Fin 26 ⊕ Fin 26 → ZMod 2)
    (h₂ : z ∈ (extension C₂_le_C₁ (liftedMap cyclicMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2)))
    (h₁ : z ∉ (extension (le_refl C₁) (liftedMap cyclicMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2))) :
    5 ≤ hammingNorm z := by
  have hs := syndrome_one z h₂ h₁
  have he : leftSum z = fun i => 1 + transposeVector (rightSum z) i := by
    funext i
    have hi := congrFun hs i
    change leftSum z i + transposeVector (rightSum z) i = 1 at hi
    exact CharTwo.add_eq_iff_eq_add.mp hi
  have hb := weight_block_sums z
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => transposeVector (rightSum z) i = 0)
  have hflip (i : Fin 13) :
      1 + transposeVector (rightSum z) i ≠ 0 ↔ transposeVector (rightSum z) i = 0 := by
    by_cases h : transposeVector (rightSum z) i = 0
    · rw [h]; decide
    · rw [show transposeVector (rightSum z) i = 1 from Fin.eq_one_of_ne_zero _ h]
      decide
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [he, hammingNorm] at hb
  have hf : Finset.univ.filter (fun i => 1 + transposeVector (rightSum z) i ≠ 0) =
      Finset.univ.filter (fun i => transposeVector (rightSum z) i = 0) :=
    Finset.filter_congr (fun i _ => hflip i)
  rw [hf] at hb
  have ht := transpose_weight (rightSum z)
  change (Finset.univ.filter (fun i => transposeVector (rightSum z) i = 0)).card +
    hammingNorm (transposeVector (rightSum z)) = 13 at hc
  omega

private lemma graph_nontrivial (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) :
    graphVector f (Pi.single 0 1) ∈ extension (le_refl C₁) (liftedMap f) ∧
      graphVector f (Pi.single 0 1) ∉ extension C₂_le_C₁ (liftedMap f) := by
  refine ⟨(mem_extension_upper _ _).mpr ⟨_, rfl⟩, ?_⟩
  intro h
  obtain ⟨x, hx, he⟩ := (mem_extension_lower _ _).mp h
  have hu := graph_injective f he
  subst x
  rw [parity_unit] at hx
  exact one_ne_zero hx

private lemma improved_distance :
    5 ≤ cssDistance (extension C₂_le_C₁ (liftedMap cyclicMap))
      (extension (le_refl C₁) (liftedMap cyclicMap)) := by
  have hn := graph_nontrivial cyclicMap
  apply le_csInf
    (show ({d | ∃ x, x ∈ extension (le_refl C₁) (liftedMap cyclicMap) ∧
      x ∉ extension C₂_le_C₁ (liftedMap cyclicMap) ∧ hammingNorm x = d} ∪
      {d | ∃ z, z ∈ (extension C₂_le_C₁ (liftedMap cyclicMap)).orthogonalBilin
        (dotProductBilin (ZMod 2) (ZMod 2)) ∧
        z ∉ (extension (le_refl C₁) (liftedMap cyclicMap)).orthogonalBilin
          (dotProductBilin (ZMod 2) (ZMod 2)) ∧ hammingNorm z = d}).Nonempty
      from ⟨_, Or.inl ⟨_, hn.1, hn.2, rfl⟩⟩)
  rintro d (⟨v, hv, hn, rfl⟩ | ⟨z, hz, hn, rfl⟩)
  · obtain ⟨x, rfl⟩ := (mem_extension_upper _ _).mp hv
    have hp : parityMap x ≠ 0 := by
      intro hx
      exact hn ((mem_extension_lower _ _).mpr ⟨x, hx, rfl⟩)
    exact le_trans (by decide : 5 ≤ 8) (x_weight_bound x hp)
  · exact z_weight_bound z hz hn

private lemma identity_distance :
    cssDistance (extension C₂_le_C₁ C₁.subtype) (extension (le_refl C₁) C₁.subtype) ≤ 4 := by
  rw [← lifted_id]
  have hn := graph_nontrivial (LinearMap.id : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
  have hw : hammingNorm (graphVector
      (LinearMap.id : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) (Pi.single 0 1)) = 4 := by
    decide
  exact Nat.sInf_le (Or.inl ⟨_, hn.1, hn.2, hw⟩)

/-- The cyclic length-thirteen map gives a strict improvement over identity doubling. -/
theorem result : claim := by
  refine ⟨26, C₂, C₁, C₂_le_C₁, rank_strict, liftedMap cyclicMap, admissible_witness, ?_⟩
  have hφ := improved_distance
  have hI := identity_distance
  omega

end
end D5.S3.Quantum.Codes.CssTDoublingMapImprovement
