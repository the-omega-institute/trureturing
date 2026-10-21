/- GID: D5/S3/Quantum/Codes/CssTDoublingMapImprovement
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/CssTDoublingMapImprovement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A cyclic binary doubling map gives a CSS code extension with strictly larger distance than identity. -/

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
set_option linter.style.longLine false

open scoped BigOperators
open Module

namespace D5.S3.Quantum.Codes.CssTDoublingMapImprovement

abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2

/-- Hamming weight on a finite binary coordinate set. -/
def weight {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : ℕ := hammingNorm x

/-- The dual code for the standard binary dot product. -/
def dual {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  C.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))

/-- The infimum of the weights in the two nontrivial CSS quotient legs. -/
noncomputable def cssDistance {ι : Type*} [Fintype ι]
    (C₂ C₁ : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  sInf ({d | ∃ x, x ∈ C₁ ∧ x ∉ C₂ ∧ weight x = d} ∪
    {d | ∃ z, z ∈ dual C₂ ∧ z ∉ dual C₁ ∧ weight z = d})

/-- The graph embedding used to extend a subcode. -/
def extensionMap {n : ℕ} {C C₁ : Submodule (ZMod 2) (BinaryVector n)}
    (h : C ≤ C₁) (φ : C₁ →ₗ[ZMod 2] BinaryVector n) :
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
def extension {n : ℕ} {C C₁ : Submodule (ZMod 2) (BinaryVector n)}
    (h : C ≤ C₁) (φ : C₁ →ₗ[ZMod 2] BinaryVector n) :
    Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  LinearMap.range (extensionMap h φ)

/-- The triple-product parity condition characterizing an admissible CSS-T extension. -/
def admissible {n : ℕ} (C₂ C₁ : Submodule (ZMod 2) (BinaryVector n))
    (h : C₂ ≤ C₁) (φ : C₁ →ₗ[ZMod 2] BinaryVector n) : Prop :=
  ∀ (x y : C₁) (z : C₂),
    (∑ i, x.val i * y.val i * z.val i) +
      (∑ i, φ x i * φ y i * φ ⟨z.val, h z.property⟩ i) = 0

/-- An admissible extension can strictly improve distance at equal length and dimension. -/
def claim : Prop :=
  ∃ (n : ℕ) (C₂ C₁ : Submodule (ZMod 2) (BinaryVector n)) (h : C₂ ≤ C₁),
    finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ ∧
      ∃ φ : C₁ →ₗ[ZMod 2] BinaryVector n, admissible C₂ C₁ h φ ∧
        cssDistance (extension h φ) (extension (le_refl C₁) φ) >
          cssDistance (extension h C₁.subtype) (extension (le_refl C₁) C₁.subtype)

noncomputable section

private abbrev V := BinaryVector 13
private abbrev W := Fin 26 ⊕ Fin 26 → ZMod 2
private def prodIndexEquiv : (Fin 2 × Fin 13) ≃ Fin 26 := finProdFinEquiv

private def diagonalMap : V →ₗ[ZMod 2] BinaryVector 26 where
  toFun x i := x (prodIndexEquiv.symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma diagonalMap_injective : Function.Injective diagonalMap := by
  intro x y h
  funext i
  have hh := congrFun h (prodIndexEquiv (0, i))
  change x (prodIndexEquiv.symm (prodIndexEquiv (0, i))).2 =
    y (prodIndexEquiv.symm (prodIndexEquiv (0, i))).2 at hh
  rw [prodIndexEquiv.symm_apply_apply] at hh
  exact hh

private def parityMap : V →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, x i
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private def C₁ := LinearMap.range diagonalMap
private def C₂₀ := LinearMap.ker parityMap
private def diagonalParityMap := diagonalMap.comp C₂₀.subtype
private def C₂ := LinearMap.range diagonalParityMap

private lemma C₂_le_C₁ : C₂ ≤ C₁ := by
  rintro x ⟨u, rfl⟩
  exact ⟨u.val, rfl⟩

private def unitVector (i : Fin 13) : V := Pi.single i 1

private lemma parity_unit (i : Fin 13) : parityMap (unitVector i) = 1 := by
  simp [parityMap, unitVector, Pi.single_apply]

private lemma rank_strict : finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ := by
  have hn : parityMap ≠ 0 := by
    intro h
    have : parityMap (unitVector 0) = 0 := congrArg (fun f => f (unitVector 0)) h
    rw [parity_unit] at this
    exact one_ne_zero this
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have hi : Function.Injective diagonalParityMap := by
    intro x y h
    exact Subtype.ext (diagonalMap_injective h)
  have h₁ := LinearMap.finrank_range_of_inj diagonalMap_injective
  have h₂ := LinearMap.finrank_range_of_inj hi
  change finrank (ZMod 2) C₂₀ + 1 = finrank (ZMod 2) V at hk
  change finrank (ZMod 2) C₁ = finrank (ZMod 2) V at h₁
  change finrank (ZMod 2) C₂ = finrank (ZMod 2) C₂₀ at h₂
  omega

private def cyclicMap : V →ₗ[ZMod 2] V where
  toFun x i := x i + x (i + 1) + x (i + 2)
  map_add' x y := by ext i; simp only [Pi.add_apply]; ring
  map_smul' a x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def liftedMap (f : V →ₗ[ZMod 2] V) : C₁ →ₗ[ZMod 2] BinaryVector 26 :=
  (diagonalMap.comp f).comp
    (LinearEquiv.ofInjective diagonalMap diagonalMap_injective).symm.toLinearMap

private lemma liftedMap_apply (f : V →ₗ[ZMod 2] V) (x : V) :
    liftedMap f ⟨diagonalMap x, ⟨x, rfl⟩⟩ = diagonalMap (f x) := by
  exact congrArg (fun y => diagonalMap (f y))
    ((LinearEquiv.ofInjective diagonalMap diagonalMap_injective).symm_apply_apply x)

private def graphVector (f : V →ₗ[ZMod 2] V) (x : V) : W :=
  Sum.elim (diagonalMap x) (diagonalMap (f x))

private lemma mem_extension_upper (f : V →ₗ[ZMod 2] V) (v : W) :
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

private lemma mem_extension_lower (f : V →ₗ[ZMod 2] V) (v : W) :
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

private lemma diagonal_eval (x : V) (a : Fin 2) (i : Fin 13) :
    diagonalMap x (prodIndexEquiv (a, i)) = x i := by
  change x (prodIndexEquiv.symm (prodIndexEquiv (a, i))).2 = x i
  rw [prodIndexEquiv.symm_apply_apply]

private lemma sum_blocks {R : Type*} [AddCommMonoid R] (g : Fin 26 → R) :
    (∑ i, g i) = (∑ j, g (prodIndexEquiv (0, j))) +
      ∑ j, g (prodIndexEquiv (1, j)) := by
  rw [← prodIndexEquiv.sum_comp g, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma admissible_witness : admissible C₂ C₁ C₂_le_C₁ (liftedMap cyclicMap) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ ⟨_, ⟨z, hz⟩, rfl⟩
  change (∑ i, diagonalMap x i * diagonalMap y i * diagonalMap z i) +
    (∑ i, liftedMap cyclicMap ⟨diagonalMap x, _⟩ i *
      liftedMap cyclicMap ⟨diagonalMap y, _⟩ i *
      liftedMap cyclicMap ⟨diagonalMap z, _⟩ i) = 0
  rw [liftedMap_apply, liftedMap_apply, liftedMap_apply, sum_blocks, sum_blocks]
  simp only [diagonal_eval, CharTwo.add_self_eq_zero]

private lemma weight_sum {ι : Type*} [Fintype ι] (x : ι → ZMod 2) :
    weight x = ∑ i, if x i ≠ 0 then 1 else 0 := by
  simp only [weight, hammingNorm, Finset.sum_boole, Nat.cast_id]

private lemma weight_add_le {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) :
    weight (x + y) ≤ weight x + weight y := by
  have h := hammingDist_triangle (x + y) y 0
  rw [hammingDist_zero_right, hammingDist_zero_right, hammingDist_eq_hammingNorm] at h
  have he : -(x + y) + y = x := by
    ext i
    simp only [Pi.neg_apply, Pi.add_apply, CharTwo.neg_eq, CharTwo.add_cancel_right]
  rw [he] at h
  exact h

private lemma weight_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → ZMod 2) : weight (fun i => x (e i)) = weight x := by
  rw [weight_sum, weight_sum]
  exact e.sum_comp (fun j => if x j ≠ 0 then (1 : ℕ) else 0)

private lemma weight_diagonal (x : V) : weight (diagonalMap x) = 2 * weight x := by
  rw [weight_sum, sum_blocks]
  simp only [diagonal_eval]
  rw [← weight_sum]
  omega

private lemma weight_graph (f : V →ₗ[ZMod 2] V) (x : V) :
    weight (graphVector f x) = 2 * (weight x + weight (f x)) := by
  rw [weight_sum, Fintype.sum_sum_type]
  change (∑ i, if diagonalMap x i ≠ 0 then 1 else 0) +
    (∑ i, if diagonalMap (f x) i ≠ 0 then 1 else 0) = _
  rw [← weight_sum, ← weight_sum, weight_diagonal, weight_diagonal]
  omega

private lemma lifted_id : liftedMap (LinearMap.id : V →ₗ[ZMod 2] V) = C₁.subtype := by
  apply LinearMap.ext
  rintro ⟨_, x, rfl⟩
  exact liftedMap_apply _ x

private lemma graph_injective (f : V →ₗ[ZMod 2] V) : Function.Injective (graphVector f) := by
  intro x y h
  apply diagonalMap_injective
  funext i
  exact congrFun h (Sum.inl i)

private lemma binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h | h
  · left
    have he := ZMod.natCast_zmod_val a
    rw [h, Nat.cast_zero] at he
    exact he.symm
  · right
    have he := ZMod.natCast_zmod_val a
    rw [h, Nat.cast_one] at he
    exact he.symm

private lemma parity_weight (x : V) : parityMap x = (weight x : ZMod 2) := by
  rw [weight_sum, Nat.cast_sum]
  change (∑ i, x i) = ∑ i, ((if x i ≠ 0 then 1 else 0 : ℕ) : ZMod 2)
  apply Finset.sum_congr rfl
  intro i _
  rcases binary_cases (x i) with h | h <;> rw [h] <;> norm_num

private lemma weight_one (x : V) (h : weight x = 1) : ∃ i, x = unitVector i := by
  change (Finset.univ.filter (fun i => x i ≠ 0)).card = 1 at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hs (j : Fin 13) : x j ≠ 0 ↔ j = i := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] using (Finset.ext_iff.mp hi j)
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    rcases binary_cases (x i) with hz | ho
    · exact (hs i |>.mpr rfl hz).elim
    · rw [ho]
      exact (Pi.single_eq_same (M := fun _ : Fin 13 => ZMod 2) i 1).symm
  · have hz : x j = 0 := by simpa only [not_not] using mt (hs j).mp hj
    rw [hz]
    exact (Pi.single_eq_of_ne (M := fun _ : Fin 13 => ZMod 2) hj 1).symm

private lemma weight_cyclic_unit (i : Fin 13) : weight (cyclicMap (unitVector i)) = 3 := by
  fin_cases i <;> decide

private lemma cyclic_kernel (x : V) (h : cyclicMap x = 0) : x = 0 := by
  have hz (i : Fin 13) : x i + x (i + 1) + x (i + 2) = 0 := congrFun h i
  have hp (i : Fin 13) : x (i + 3) = x i := by
    have hh := hz (i + 1)
    rw [show i + 1 + 1 = i + 2 by rw [add_assoc]; rfl, show i + 1 + 2 = i + 3 by rw [add_assoc]; rfl] at hh
    have he : x i = x (i + 1) + x (i + 2) := CharTwo.add_eq_zero.mp ((add_assoc _ _ _).symm.trans (hz i))
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

private lemma x_weight_bound (x : V) (hx : parityMap x ≠ 0) :
    8 ≤ weight (graphVector cyclicMap x) := by
  have hn : x ≠ 0 := by intro h; exact hx (h ▸ parityMap.map_zero)
  have ha : cyclicMap x ≠ 0 := fun h => hn (cyclic_kernel x h)
  have hp : 0 < weight x := hammingNorm_pos_iff.mpr hn
  have hq : 0 < weight (cyclicMap x) := hammingNorm_pos_iff.mpr ha
  have ht : weight x ≠ 2 := by
    intro h
    apply hx
    rw [parity_weight, h]
    decide
  rw [weight_graph]
  by_cases hs : weight x = 1
  · obtain ⟨i, rfl⟩ := weight_one x hs
    rw [weight_cyclic_unit]
    omega
  · omega

private def transposeVector (w : V) : V := fun i => w i + w (i - 1) + w (i - 2)

private lemma sum_shift (x w : V) (k : Fin 13) :
    (∑ i, x (i + k) * w i) = ∑ i, x i * w (i - k) := by
  have h := Equiv.sum_comp (Equiv.addRight k) (fun i => x i * w (i - k))
  change (∑ i, x (i + k) * w (i + k - k)) = _ at h
  simpa only [add_sub_cancel_right] using h

private lemma transpose_dot (x w : V) :
    dotProduct (cyclicMap x) w = dotProduct x (transposeVector w) := by
  change (∑ i, (x i + x (i + 1) + x (i + 2)) * w i) =
    ∑ i, x i * (w i + w (i - 1) + w (i - 2))
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_shift x w 1, sum_shift x w 2]

private lemma transpose_weight (w : V) : weight (transposeVector w) ≤ 3 * weight w := by
  have h₁ := weight_add_le w (fun i => w (i - 1))
  have h₂ := weight_add_le (w + fun i => w (i - 1)) (fun i => w (i - 2))
  have h₃ := weight_reindex (Equiv.subRight (1 : Fin 13)) w
  have h₄ := weight_reindex (Equiv.subRight (2 : Fin 13)) w
  change weight (fun i => w (i - 1)) = weight w at h₃
  change weight (fun i => w (i - 2)) = weight w at h₄
  change weight (transposeVector w) ≤ _ at h₂
  omega

private lemma complement_weight (v : V) :
    weight (fun i => 1 + v i) + weight v = 13 := by
  rw [weight_sum, weight_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : Fin 13, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases binary_cases (v i) with h | h <;> rw [h] <;> decide
    _ = 13 := by simp

private def leftBlock (z : W) (a : Fin 2) : V :=
  fun i => z (Sum.inl (prodIndexEquiv (a, i)))

private def rightBlock (z : W) (a : Fin 2) : V :=
  fun i => z (Sum.inr (prodIndexEquiv (a, i)))

private def leftSum (z : W) : V := leftBlock z 0 + leftBlock z 1
private def rightSum (z : W) : V := rightBlock z 0 + rightBlock z 1
private def syndrome (z : W) : V := leftSum z + transposeVector (rightSum z)

private lemma weight_four_blocks (z : W) :
    weight z = weight (leftBlock z 0) + weight (leftBlock z 1) +
      (weight (rightBlock z 0) + weight (rightBlock z 1)) := by
  rw [weight_sum, Fintype.sum_sum_type, sum_blocks, sum_blocks]
  rw [weight_sum, weight_sum, weight_sum, weight_sum]
  rfl

private lemma weight_block_sums (z : W) :
    weight (leftSum z) + weight (rightSum z) ≤ weight z := by
  have h₁ := weight_add_le (leftBlock z 0) (leftBlock z 1)
  have h₂ := weight_add_le (rightBlock z 0) (rightBlock z 1)
  rw [weight_four_blocks]
  exact Nat.add_le_add h₁ h₂

private lemma graph_dot (f : V →ₗ[ZMod 2] V) (x : V) (z : W) :
    dotProduct (graphVector f x) z =
      dotProduct x (leftSum z) + dotProduct (f x) (rightSum z) := by
  change (∑ i, graphVector f x i * z i) = _
  rw [Fintype.sum_sum_type, sum_blocks, sum_blocks]
  simp only [graphVector, Sum.elim_inl, Sum.elim_inr, diagonal_eval]
  change (∑ i, x i * leftBlock z 0 i) + (∑ i, x i * leftBlock z 1 i) +
    ((∑ i, f x i * rightBlock z 0 i) + (∑ i, f x i * rightBlock z 1 i)) = _
  rw [show leftSum z = leftBlock z 0 + leftBlock z 1 from rfl,
    show rightSum z = rightBlock z 0 + rightBlock z 1 from rfl,
    dotProduct_add, dotProduct_add]
  rfl

private lemma cyclic_graph_dot (x : V) (z : W) :
    dotProduct (graphVector cyclicMap x) z = dotProduct x (syndrome z) := by
  rw [graph_dot, transpose_dot]
  exact (dotProduct_add x (leftSum z) (transposeVector (rightSum z))).symm

private lemma unit_dot (i : Fin 13) (v : V) : dotProduct (unitVector i) v = v i := by
  change Pi.single i (1 : ZMod 2) ⬝ᵥ v = v i
  exact single_one_dotProduct i v

private lemma syndrome_one (z : W)
    (h₂ : z ∈ dual (extension C₂_le_C₁ (liftedMap cyclicMap)))
    (h₁ : z ∉ dual (extension (le_refl C₁) (liftedMap cyclicMap))) :
    syndrome z = fun _ => 1 := by
  have horth (x : V) (hx : parityMap x = 0) : dotProduct x (syndrome z) = 0 := by
    rw [← cyclic_graph_dot]
    exact h₂ _ ((mem_extension_lower _ _).mpr ⟨x, hx, rfl⟩)
  have hc (i : Fin 13) : syndrome z i = syndrome z 0 := by
    have hp : parityMap (unitVector i + unitVector 0) = 0 := by
      rw [map_add, parity_unit, parity_unit]
      decide
    have hh := horth _ hp
    rw [add_dotProduct, unit_dot, unit_dot] at hh
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
  have ho : syndrome z 0 = 1 := (binary_cases _).resolve_left hn
  exact funext (fun i => (hc i).trans ho)

private lemma z_weight_bound (z : W)
    (h₂ : z ∈ dual (extension C₂_le_C₁ (liftedMap cyclicMap)))
    (h₁ : z ∉ dual (extension (le_refl C₁) (liftedMap cyclicMap))) :
    5 ≤ weight z := by
  have hs := syndrome_one z h₂ h₁
  have he : leftSum z = fun i => 1 + transposeVector (rightSum z) i := by
    funext i
    have hi := congrFun hs i
    change leftSum z i + transposeVector (rightSum z) i = 1 at hi
    exact CharTwo.add_eq_iff_eq_add.mp hi
  have hc := complement_weight (transposeVector (rightSum z))
  have ht := transpose_weight (rightSum z)
  have hb := weight_block_sums z
  rw [he] at hb
  omega

private lemma graph_nontrivial (f : V →ₗ[ZMod 2] V) :
    graphVector f (unitVector 0) ∈ extension (le_refl C₁) (liftedMap f) ∧
      graphVector f (unitVector 0) ∉ extension C₂_le_C₁ (liftedMap f) := by
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
      x ∉ extension C₂_le_C₁ (liftedMap cyclicMap) ∧ weight x = d} ∪
      {d | ∃ z, z ∈ dual (extension C₂_le_C₁ (liftedMap cyclicMap)) ∧
        z ∉ dual (extension (le_refl C₁) (liftedMap cyclicMap)) ∧ weight z = d}).Nonempty
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
  have hn := graph_nontrivial (LinearMap.id : V →ₗ[ZMod 2] V)
  have hw : weight (graphVector (LinearMap.id : V →ₗ[ZMod 2] V) (unitVector 0)) = 4 := by
    rw [weight_graph]
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
