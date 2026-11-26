import OmegaMath.NumberTheory.GRH.Lib.Weil.GaussSum.LocalHomUnit
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Injectivity and norm of a chain of theta lifts (see New.Exchange.TriangleArrows).

This file: Abstract triangle of maps: chains are injective, Gram determinant factors over first
arrows. -/

open ComplexInnerProductSpace Finset Module ComplexConjugate


variable {I V : Type} {F : ℕ → ℕ → Type} [∀ i n, NormedAddCommGroup (F i n)] [∀ i n,
  InnerProductSpace ℂ (F i n)] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (m) (w : I → ℕ → ℕ)
  (M : ℕ → (I → ℂ) → Prop) (a : I → ∀ i n, F i n →ₗ[ℂ] F i (n + 1))
  (d : I → ∀ i n, F i (n + 1) →ₗ[ℂ] F (i + 1) n) (j : ∀ i, V →ₗᵢ[ℂ] F i 0) (G : Prop)
attribute [local simp] compUpTo inner_smul_right NeZero.ne

/-- A triangle of inner product spaces with arrows a, d: weighted squares commute up to scalars
(under G graded by M, with an adjoint law); between the copies of V, a is adjoint to d and
da is injective. -/
structure IsTriangle where
  cost_one : M 0 1
  cost_mul {n n' N c c'} : M n c → M n' c' → n + n' ≤ N → M N (c * c')
  square_law i n (h : i + (n + 1) < m) : ∃ β, (∀ t y z, w t n * ⟪z, a t _ n (d t i n y)⟫ =
    conj (β t)⁻¹ * w t (n + 2) * ⟪z, d t i _ (a t i _ y)⟫) ∧ (G → M 1 β ∧ ∃ κ, M 0 κ ∧ ∀ t z, ∃ x,
    (∀ y, ⟪a t i _ y, z⟫ = ⟪y, x⟫) ∧ ∀ y, ⟪d t i n x, y⟫ = κ t * ⟪d t i _ z, a t _ n y⟫)
  length_one i (h : i < m) t y : (∀ z, ⟪z, a t i 0 (j i y)⟫ = ⟪d t i 0 z, j _ y⟫) ∧
    ∃ v, j _ v = d t i 0 (a t i 0 (j i y)) ∧ (v = 0 → y = 0)

/-- The composite F(i,0) → F(i,n) of the first n arrows a in row i, the k-th multiplied by its
weight w(t,k). -/
noncomputable abbrev weightedChain t i := compUpTo fun n ↦ (w t n : ℂ) • a t i n

variable {m w M a d j G} (h : IsTriangle m w M a d j G) [∀ t n, NeZero (w t n)]
include h

lemma IsTriangle.weightedChain_descent i n (hi : i + n < m) : ∃ β κ, (∀ t y,
  weightedChain w a t _ n (d t i 0 (a t i 0 y)) = (w t n.succ / w t 1 / w t 0 / conj (β t) : ℂ) • d
  t i n (weightedChain w a t i _ y)) ∧ (G → M n (κ * β) ∧ ∀ t y z, ⟪z, a t i n
  (weightedChain w a t i n (j i y))⟫ = κ t * ⟪d t i n z, weightedChain w a t _ n (j _ y)⟫) := by
  induction' n with n H; use 1, 1; simp [h.1, h.4 i hi]
  choose _ _ e r u using H hi.le; choose! _ f s _ c _ p q using h.3 i n hi
  refine ⟨_, _, fun t y ↦ ext_inner_left ℂ ?_, fun g ↦ ⟨(mul_mul_mul_comm ..).subst (h.2 (r g)
    (h.2 (c g) (s g) .refl) .refl), ?_⟩⟩ <;> simp [← inner_conj_symm _ (a _ i n.succ _), *, field]

/-- In a triangle of size m, for i + n ≤ m the weighted composite of the first n arrows in row i
is injective on the image of V under j i. -/
lemma IsTriangle.eq_zero_of_weightedChain {t} : ∀ n i, i + n ≤ m → ∀ y,
  weightedChain w a t i n (j i y) = 0 → y = 0 := Nat.rec (by simp [norm_map, ← norm_eq_zero]) fun _
  _ i hi y ↦ by grind [h.weightedChain_descent _ _ hi, h.4 i (by lia) t y, smul_zero]

/-- In a triangle with G, let w₀⟪a x, a s y⟫ = ⟪x, s S_i y⟫ for the first arrow a of each row i < m.
For i + n = m the weighted n-chain of row i has Gram form κ(w₀w₁ⁿ/w_n)⟪x, s T y⟫, det T = ∏_{i≤k<m}
det S_k, with M(n², κ). -/
lemma IsTriangle.inner_weightedChain_eq (hG : G) {U} [AddCommGroup U] [Module ℂ U] {s : U → V} (S :
  I → ℕ → End ℂ U) (hS :
  ∀ i < m, ∀ t x y, w t 0 * ⟪a t i 0 (j i x), a t i 0 (j i (s y))⟫ = ⟪x, s (S t i y)⟫) : ∀ n i,
  i + n = m → ∃ κ, M (n * n) κ ∧ ∀ t, ∃ T : End ℂ U, T.det = ∏ k ∈ Ico i m, (S t k).det ∧ ∀ x y,
  ⟪weightedChain w a t i n (j i x), weightedChain w a t i n (j i (s y))⟫ = κ t * (w t 0 * w t 1 ^
  n / w t n) * ⟪x, s (T y)⟫ := Nat.rec (fun _ _ ↦ ⟨_, h.1, fun _ ↦ ⟨1, by aesop⟩⟩) fun n H i hi ↦ by
  choose _ k T _ E using H i.succ (by lia); choose β _ e l _ using h.weightedChain_descent i n hi.le
  choose g z q p using h.4 i (by omega)
  refine ⟨_, h.2 (l hG) k (by lia), fun t ↦ ⟨S t i * T t,
    by grind [prod_eq_prod_Ico_succ_bot], fun x y ↦ ?_⟩⟩
  specialize E t (z t x) y; simp [*, field] at E ⊢
  grind [(j _).inner_map_map, h.eq_zero_of_weightedChain (t := t) n i.succ, zero_smul,
    inner_zero_left]
