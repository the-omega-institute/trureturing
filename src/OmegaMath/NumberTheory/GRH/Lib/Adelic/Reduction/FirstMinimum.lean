import OmegaMath.NumberTheory.GRH.Lib.Adelic.Unitary.SpaceBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski
theorems (known result; see Lib.Adelic.Reduction.Defs).

This file: First minimum of hermitian lattices: positivity, comparison, short vectors are
orthogonal. -/
seal Finset.univ Finset.sum Finset.prod

open EuclideanSpace Matrix Finset ComplexOrder Norms.L2Operator Classical Prod

namespace Space

variable {E : Type*} [Field E] [CMType E] {n} [Fintype n] {s} {V : Space E n s} {m} [Fintype m]
attribute [local simp] signMatrix dotProduct fst_sum snd_sum funext_iff sum_mem archCoords stdForm
  baseLattice

lemma stdForm_dotProduct_fst a b w : (star a ⬝ᵥ stdForm E s *ᵥ b).1 w =
    star (a · |>.1 w) ⬝ᵥ signMatrix s *ᵥ (b · |>.1 w) := by simp

lemma eq_zero_of_vecAtPoint_fst {a w} (h : (V.vecAtPoint a · |>.1 w) = 0) : a = 0 := by
  simpa [vecAtPoint] using (by simp_all [mulVec] : ((V.x.1 *ᵥ V.vecAtPoint a) · |>.1 w) = 0)

lemma move_vecAtPoint g ξ : (V.move g).vecAtPoint ξ = g⁻¹.mat *ᵥ V.vecAtPoint ξ :=
  (mulVec_mulVec ..).symm

lemma exists_smul_mem_baseLattice ξ : ∃ N ≠ 0, N • ξ ∈ V.baseLattice := by
  simpa [← nsmul_eq_mul] using exists_forall_mul_mem_Ô _

lemma le_firstMinimum_iff {l} : l ≤ V.firstMinimum ↔ l ≤ 1 ∧ ∀ y ∈ V.baseLattice, y ≠ 0 →
  l ≤ ‖V.archCoords y‖ := (le_csInf_iff ⟨0, by aesop_cat⟩ (by simp)).trans (by grind)

lemma firstMinimum_le {y} : y ∈ V.baseLattice → y ≠ 0 → V.firstMinimum ≤ ‖V.archCoords y‖ :=
  (le_firstMinimum_iff.1 le_rfl).2 y

/-- The first minimum λ of the lattice of V, cut off at 1, is at most 1. -/
@[simp] lemma firstMinimum_le_one : V.firstMinimum ≤ 1 := (le_firstMinimum_iff.1 le_rfl).1

/-- Suppose the adelic coordinates of ξ for V are N·k times those of η for W, with k of operator
norm ≤ c at each infinite place. Then ‖ξ‖ ≤ Nc‖η‖; ξ is in V's lattice if η is in W's and N·k_f is
integral. -/
lemma mem_and_norm_le_of_vecAtPoint ξ {t} (W : Space E m t) η k (N : ℕ) {c} (h' :
  ∀ w, ‖k.map (·.1 w)‖ ≤ c) (e : V.vecAtPoint ξ = N • k *ᵥ W.vecAtPoint η) :
  ((∀ i j, N * (k i j).2 ∈ Ô E) → η ∈ W.baseLattice → ξ ∈ V.baseLattice) ∧ ‖V.archCoords ξ‖ ≤
  N * c * ‖W.archCoords η‖ := ⟨by simp_all [mulVec, mul_sum, ← mul_assoc, mul_mem], le_of_sq_le_sq
  (by simp [e, mul_pow, norm_sq_eq, Fintype.sum_prod_type]; rw [mul_sum]; gcongr
      grw [← norm_sq_eq (.toLp 2 _), mul_assoc, ← mul_pow, ← h' ‹_›, ← l2_opNorm_mulVec]
      simp [mulVec, norm_sq_eq, mul_sum]) (by grw [← h' ofNonempty]; bound)⟩

/-- For compact Ω ⊆ G_f there is an integer c ≥ 1 such that, with L_g and ‖·‖_g the lattice and
norm of V moved by g, if g⁻¹γg' (γ rational) has finite
part in Ω and operator norm ≤ R at infinity, then y ∈ L_{g'} implies cγy ∈ L_g and ‖cγy‖_g ≤
cR‖y‖_{g'}. -/
lemma exists_smul_mulVec_mem_latticeBall {Ω} (hΩ : IsCompact Ω) : ∃ c ≠ (0 : ℕ), ∀ {γ g g' R},
  let x := g⁻¹ * V.ratEmbed γ * g'; x.2 ∈ Ω → (∀ w, ‖(x.1 w).1.1‖ ≤ R) →
    ∀ y ∈ (V.move g').baseLattice,
  (c : E) • γ *ᵥ y ∈ (V.move g).latticeBall (c * R * ‖(V.move g').archCoords y‖) := by
  peel exists_natCast_smul_mem_of_isCompact E (hΩ.image_auto (·.1.1))
    (isOpen_Ô.matrix.mem_nhds (Ô E).matrix.zero_mem)
  use fun h r _ k ↦ (mem_and_norm_le_of_vecAtPoint _ _ _ (G.mat (_ * _)) _ r
    (by simp [move_vecAtPoint, ← ratEmbed_mulVec_vecAtPoint, ← G.mat_mul])).imp_left
    (· (this _ ⟨_, h, rfl⟩) k)

/-- If a, b lie in the lattice of V and ‖a‖‖b‖ < 1, then h(a,b) = aᴴJb = 0. -/
lemma form_eq_zero_of_norm_mul_lt_one {a b} (ha : a ∈ V.baseLattice) (hb :
  b ∈ V.baseLattice) (h : ‖V.archCoords a‖ * ‖V.archCoords b‖ < 1) : star a ⬝ᵥ V.J *ᵥ b = 0 :=
  eq_zero_of_norm_Φ (by simp_all [↓← stdForm_vecAtPoint, ↓← algebraMap_mem_Ô,
  ↓← toAdele_apply_snd, mul_mem (star_mem_Ô _)]) fun w ↦ by
  grw [← h, norm_eq, norm_eq, ← Real.sum_mul_le_sqrt_mul_sqrt, ← subset_univ ({w} ×ˢ ⊤)]
  simp [↓← toAdele_apply_fst, ↓← stdForm_vecAtPoint, norm_sum_le_of_le, abs_unit_intCast]

lemma eq_zero_of_isotropic_of_definite (hs : ∀ i j, s i = s j) ξ (e : star ξ ⬝ᵥ V.J *ᵥ ξ = 0) :
  ξ = 0 := by ext i; simp [eq_zero_of_vecAtPoint_fst (by
  simpa [e, ↓stdForm_dotProduct_fst,
    hs _ i, -dotProduct] using congr($(V.stdForm_vecAtPoint ξ ξ).1 ofNonempty))]

/-- If all signs of V agree, then `Space.firstMinimum` V ≥ 1: every nonzero vector of the lattice of
V has length at least 1. -/
lemma one_le_firstMinimum (h : ∀ i j, s i = s j := by simp) : 1 ≤ V.firstMinimum := by
  simpa [le_firstMinimum_iff, ← sq] using fun _ a ↦
    (V.eq_zero_of_isotropic_of_definite h _ ∘ form_eq_zero_of_norm_mul_lt_one a a).mt

/-- For every space V, λ > 0, where λ is the first minimum of the lattice of V cut off at 1
(`Space.firstMinimum`). -/
lemma firstMinimum_pos : 0 <
  V.firstMinimum := let ⟨N, _⟩ := exists_forall_mul_mem_Ô V.xFin.1.uncurry
  .trans_le (by simp) (le_firstMinimum_iff.2 ⟨div_le_self zero_le_one le_sup_left, fun y _ _ ↦
    let ⟨_, q⟩ := (stdSpace ..).mem_and_norm_le_of_vecAtPoint (N • y) V y V.x N (norm_le_pi_norm _)
      (by simp [vecAtPoint])
    by grw [div_le_iff₀', ← le_max_right, ← q, ← firstMinimum_le, ← one_le_firstMinimum] <;> aesop⟩)
