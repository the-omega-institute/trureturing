import OmegaMath.NumberTheory.GRH.Lib.Adelic.Reduction.MinkowskiSecond
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Supporting lemmas (textbook or folklore).

Part of: Adelic points of unitary groups, levels and Haar measures (known result; see
Lib.Adelic.Reduction.MinkowskiSecond).

This file: Basic API for rational points, block embeddings and vectors of framed hermitian
spaces. -/

open Matrix Topology


variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E] {n m : Type _} [Fintype n]
  [Fintype m] {s : n → _} {t : m → _}
attribute [local simp] blockGL U.sum Function.comp_def

/-- Let J'' = diag(J,J') and g ∈ U(J''). For J' invertible, g = diag(a,1) with a ∈ U(J) iff its
second block of columns is that of 1; for J invertible, symmetrically for diag(1,a) and the
first block. -/
lemma U.mem_range_sum {R} [CommRing R] [StarRing R] {J J' J''} (h : @fromBlocks n m n m R J 0 0 J' =
  J'') {g} : (IsUnit J' → ((∃ a, sum h (a, 1) = g) ↔ g.1.1.toCols₂ = fromRows 0 1)) ∧ (IsUnit J →
  ((∃ a, sum h (1, a) = g) ↔ g.1.1.toCols₁ = fromRows 1 0)) := by
  obtain ⟨e, k, u, ⟨⟩⟩ := g.1.1.fromBlocks_toBlocks, mem_U.1 g.2, g.1.isUnit, h
  rw [← e] at k u ⊢
  simp [← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff]
  constructor <;> rintro ⟨_, ⟨⟩⟩ <;> use (by aesop) <;> intro <;> simp_all [-e,
    Matrix.mul_left_eq_iff_eq_invOf_mul] <;> use u.unit <;> aesop

/-- The block diagonal map from the product of the adelic unitary groups of signs s and t to
that of the concatenated signs is a closed embedding. -/
@[fun_prop] lemma G.isClosedEmbedding_sum : IsClosedEmbedding (sum : _ → G E (s ⊕ᵥ t)) := by
  simp [← isClosedEmbedding_mat.of_comp_iff]
  apply ((by tauto : (fromBlocks · 0 0 ·).uncurry.RightInverse fun M ↦ (M.onFun .inl, M.onFun .inr)
    ).isClosedEmbedding ..).comp (isClosedEmbedding_mat.prodMap isClosedEmbedding_mat) <;> fun_prop

@[fun_prop] lemma G.continuous_reindex e h : Continuous (reindex e h : G E s → G E t) := by
  simp [continuous_iff]; fun_prop

@[fun_prop] lemma G.continuous_neg : Continuous (neg : G E s → _) := continuous_iff.2 continuous_mat

namespace Space

variable {E : Type*} [Field E] [CMType E] (V : Space E n s) (W : Space E m t)
attribute [local simp] fromBlocks_mulVec sum vecAtPoint mat_ratEmbed mul_assoc RingHom.map_mulVec
  map_J

@[ext] lemma ext {V V' : Space E n s} (h : V.x = V'.x) : V = V' := by
  simp_all [mk.injEq _, ← (map_injective (@toAdele E ..).injective).eq_iff]

@[local simp] lemma mem_Γ_iff_range {g} : g ∈ V.Γ ↔ ∀ i j, (V.x * g.mat * V.x⁻¹) i j ∈
  toAdele.range := ⟨.rec (by aesop), fun h ↦
  .imp (fun _ ↦ V.toRatCoords.symm_apply_eq.2 ∘ And.right)
  (U.mem_range_map _ (RingHom.injective _) (by simp) rfl (mem_ratMatrices.2 h).choose_spec)⟩

/-- Witt's theorem for a hermitian space V: if X, Y are left invertible n × m matrices over E
with XᴴJX = YᴴJY, J the matrix of V, then gX = Y for some g in U(J)(E). -/
protected lemma witt {X Y : Matrix n m E} : HasLeftInv X → HasLeftInv Y → Xᴴ * V.J * X = Yᴴ * V.J *
  Y → ∃ g : U V.J, g.1.1 * X = Y := witt exists_isUnit_sub_star V.conjTranspose_J (by simp)

lemma ratEmbed_mulVec_vecAtPoint γ y : (V.ratEmbed γ).mat *ᵥ V.vecAtPoint y =
  V.vecAtPoint (γ *ᵥ y) := by simp

lemma stdForm_vecAtPoint y z : star (V.vecAtPoint y) ⬝ᵥ stdForm E s *ᵥ V.vecAtPoint z =
  star y ⬝ᵥ V.J *ᵥ z := by simp [star_mulVec_dotProduct]; simp [dotProduct]

lemma vecAtPoint_injective : (⇑V.vecAtPoint).Injective :=
  (MulAction.injective V.x⁻¹).comp (@toAdele E ..).injective.comp_left

lemma sum_ratEmbed γ : (V.sum W).ratEmbed (U.sum rfl γ) = G.sum (V.ratEmbed γ.1, W.ratEmbed γ.2) :=
  G.ext_mat (by erw [mat_ratEmbed]; simp)

lemma sum_vecAtPoint y z : (V.sum W).vecAtPoint (y ⊕ᵥ z) =
  V.vecAtPoint y ⊕ᵥ W.vecAtPoint z := by simp

lemma sum_mem_Γ {g} : G.sum g ∈ (V.sum W).Γ ↔ g.1 ∈ V.Γ ∧ g.2 ∈ W.Γ := by simp

lemma signedSpace_eq_reindex [StablyUnram E] {e h} (hV : V.x = (signedSpace E s).x) :
  signedSpace _ t = V.reindex e h := h ▸ by ext : 2; simp_all [signedSpace, reindex]

lemma mem_move_Γ a {g} : g ∈ (V.move a).Γ ↔ a * g * a⁻¹ ∈ V.Γ := by simp [move, G.mat]
