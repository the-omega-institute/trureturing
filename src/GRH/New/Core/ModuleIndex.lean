import GRH.Lib.Adelic.Witt.FrameAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas on `IndexDvd` and `HasType`: bookkeeping for the index of a submodule.

Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Index of a submodule bounded via determinants; multiplicativity; operators onto up to
small index. -/


open Matrix Submodule Finset Pointwise Module
variable {O U V ι} [CommRing O] [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]
  {M N P : Submodule O V} {M' N' : Submodule O U} {z z' a : O} {f : V →ₗ[O] V}
attribute [local simp] sum_smul_mem

variable (M N z) in
/-- The property that every finite family (Φ_k) in M admits a square matrix m over O with det m
dividing z and all combinations ∑_k m_{ik} Φ_k in N. -/
def IndexDvd := ∀ n (Φ : Fin n → V), (∀ k, Φ k ∈ M) → ∃ m, det m ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N

/-- `IndexDvd` pulls back along a linear map f: U → V: if it holds for (M, N, z), f(M') ⊆ M and
every x in M' with f(x) in N lies in N', then it holds for (M', N', z). -/
lemma IndexDvd.comap (h : IndexDvd M N z) (f : U →ₗ[O] V) : M' ≤ M.comap f → (∀ x ∈ M', f x ∈ N →
  x ∈ N') → IndexDvd M' N' z := fun a _ _ _ c ↦ (h _ _ (a <| c ·)).imp (by aesop)

/-- If M ⊆ N, then `IndexDvd` holds for M, N and every scalar z. -/
@[simp] lemma IndexDvd.of_le : M ≤ N → IndexDvd M N z := fun _ _ _ _ ↦ ⟨1, by aesop⟩

/-- If `IndexDvd` holds for (M, N, z) and for (N, P, a), then it holds for (M, P, za). -/
lemma IndexDvd.trans (h : IndexDvd M N z) (g : IndexDvd N P a) : IndexDvd M P (z * a) :=
  (h · · · |>.rec fun m b ↦
  (g _ _ b.2).imp' (· * m) (by simp_all [mul_comm, mul_dvd_mul, mul_smul, ← Module.smul_apply]))

/-- `IndexDvd` pushes forward along a linear map f: if it holds for (M, N, z), M' ⊆ f(M) + N'
and f(N) ⊆ N', then it holds for (M', N', z). -/
lemma IndexDvd.map (h : IndexDvd M N z) (f : V →ₗ[O] U) : M' ≤ M.map f ⊔ N' → N.map f ≤ N' →
  IndexDvd M' N' z := by
  intro a b _ _ H; choose x hx y hy e using by simpa using (mem_sup.1 <| a <| H ·)
  peel h _ x hx
  simpa [← e, add_mem_cancel_right, hy] using b ⟨_, this, rfl⟩

/-- Let f_i : V → U be O-linear, M ⊂ V, N' ⊂ U submodules, with `IndexDvd` holding for (M,
f_i⁻¹(N'), z) for each i. For finite s it then holds for (Q, N', z^|s|), Q the span of N' and the
f_i(M), i ∈ s. -/
lemma IndexDvd.sup {f : ι → V →ₗ[O] U} (h : ∀ i, IndexDvd M (.comap (f i) N') z) (s : Finset ι) :
    IndexDvd (span O (.image2 (f ·) s M ∪ N')) N' (z ^ #s) := s.cons_induction (by simp) fun i _
  _ ↦ by simp [pow_succ', *]; use ((h i).map _ (by order) (by simp [map_comap_eq])).trans

lemma IndexDvd.comp (e : M.map f ≤ M) : IndexDvd M (M.map f ⊔ a • M) z → IndexDvd M (N ⊔ a • M) z' →
  IndexDvd M (N.map f ⊔ a • M) (z * z') := (·.trans <| ·.map f (by order) (by grw [← e]; simp))

/-- The endomorphism y preserves the submodule M, and the index of yM + p^nM in M divides p^l,
in the sense of `IndexDvd`, for some natural l ≤ c. -/
def HasType p M n (y : End O V) (c : ℝ) :=
  M.map y ≤ M ∧ ∃ l : ℕ, l ≤ c ∧ IndexDvd M (M.map y ⊔ p ^ n • M) (p ^ l)

/-- Exponents add under products: if each operator T(l), l in a list L, has type (`HasType`) with
exponent t(l) for fixed z, M, s, then the product of the T(l) has type with exponent ∑ t(l). -/
lemma HasType.prod {s T t} (L : List ι) : (∀ l ∈ L, HasType z M s (T l) (t l)) →
    HasType z M s (L.map T).prod (L.map t).sum := by
  induction L <;> simp [HasType, End.one_eq_id, End.mul_eq_comp, map_comp]
  next I => exact fun e i _ _ H ↦
    (I H).imp (by grw [·, e]) (.imp' (i + ·) (by grind [IndexDvd.comp]))

/-- Let O be a valuation domain and A a square matrix over O indexed by ι whose determinant
divides z. If N contains the image of A in O^ι, then `IndexDvd` holds for (O^ι, N, z). -/
lemma IndexDvd.of_det_dvd [IsDomain O] [ValuationRing O] [Fintype ι] {A : Matrix ι ι O} {N}
    (h : A.det ∣ z) (e : .map A.mulVecLin ⊤ ≤ N) : IndexDvd ⊤ N z := fun _ Φ _ ↦
  (isValuationPair_top.hermite (.refl _) (fromBlocks 1 (-of Φ) 0 Aᵀ) (1 ⊕ᵥ 0)).elim fun _ ⟨_, D, t,
  a, b⟩ ↦ ⟨_, .trans ⟨_, by simpa [mul_left_comm, (ext (by tauto) : D.toBlocks₁₂ = 0)] using
  (D.fromBlocks_toBlocks ▸ congr(($a).det) :)⟩ h, fun i ↦ e ⟨_ ∘ _, ⟨⟩, funext (by simpa [← b,
  toBlocks₁₁, mul_apply, mulVec_eq_sum, neg_add_eq_sub] using (@t (.inl i) <| .inr ·))⟩⟩
