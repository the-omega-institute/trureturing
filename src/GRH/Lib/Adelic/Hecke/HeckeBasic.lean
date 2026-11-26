import GRH.Lib.General.LinearAlgebra.PartialDerivComm
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Abstract Hecke operators of (G,K): coset sums, functoriality, composition as
convolution. -/


open Set Classical Function HasFiniteSupport DoubleCoset QuotientGroup Finset
variable {A G W W'} [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W']
  [Module A W'] {π} (K K' : Subgroup G) {χ' : K' →* A} (f : G → A) {v : W} {G'} [Group G']

/-- The function f on G is nonzero at the chosen representatives of only finitely many cosets
gK. -/
abbrev HasFiniteCosets := (@support (G ⧸ K) A _ (f ·.out)).Finite

/-- The function f on G is left and right K-invariant and supported on finitely many cosets gK. -/
abbrev IsBiInvariant := HasFiniteCosets K f ∧ ∀ᵉ (g) (k ∈ K), f (g * k) = f g ∧ f (k * g) = f g

variable {K K' f} {J : Subgroup G'} {F} (a : G' →* G) (L : W →ₗ[A] W') (h :
  HasFiniteCosets K f) {π'} (hf : ∀ g (k : K), f (g * k) = f g) (hf' : ∀ g k, χ' k * f (k * g) =
  f g) (h1 : v ∈ levelSpace (A := A) π K)

lemma heckeFun_sum v : heckeFun π K f v = ∑ q ∈ h.toFinset, f q.out • π q.out v := by
  rw [heckeFun, finsum_eq_sum_of_support_subset] <;> aesop

attribute [local simp] indicator heckeFun_sum mem_doubleCoset

include h in
lemma map_heckeFun : (∀ g, L (π g v) = π' g (L v)) →
    L (heckeFun π K f v) = heckeFun π' K f (L v) := by aesop

lemma levelSpace_anti : K ≤ K' → levelSpace π K' ≤ levelSpace π K := by aesop_cat

attribute [local simp ←] mul_assoc smul_finsum' smul_smul

/-- For a compact open subgroup K of a topological group G and g in G, the indicator function of
KgK is K-invariant on both sides and supported on finitely many cosets hK. -/
lemma isBiInvariant_doubleCoset [TopologicalSpace G] [IsTopologicalGroup G] (hK :
  @IsOpen G _ K) [CompactSpace K] g : IsBiInvariant K (@indicator _ A _ (doubleCoset g K K) 1) :=
  ⟨(finite_quotient_image_of_isCompact hK (by
  apply_rules [IsCompact.mul, isCompact_iff_compactSpace.2])).subset fun q a ↦ ⟨_,
  support_indicator_subset a, q.out_eq⟩, fun _ _ _ ↦ ⟨by simp_all [← inv_mul_eq_iff_eq_mul,
  mul_mem_cancel_right], by simp_all [← mul_inv_eq_iff_eq_mul, mul_assoc, mul_mem_cancel_left]⟩⟩

include hf h1

/-- Let f(gk) = f(g) for k in K, and v be fixed by K. If the cosets r_iK, i in a finite set s, are
distinct and cover the support of f, then f lives on finitely many cosets and acts on v as ∑_{i∈s}
f(r_i)π(r_i)v.

Known result: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums. -/
lemma heckeFun_eq_sum {ι s} {r : ι → G} (hr : InjOn (@mk _ _ K <| r ·) (SetLike.coe s))
    (hs : ∀ g, f g ≠ 0 → ∃ i ∈ s, (r i : G ⧸ K) = g) : HasFiniteCosets K f ∧ heckeFun π K f v =
  ∑ i ∈ s, f (r i) • π (r i) v := have H := (out_eq' · ▸ mem_image.2 ∘ hs _)
  ⟨(toFinite _).subset H, (axiomOfChoice (mk_out_eq_mul K)).rec (by simp_all [heckeFun,
    finsum_eq_sum_of_support_subset _ (H · ∘ left_ne_zero_of_smul)])⟩

/-- Let f(gk) = f(g) for k in K, v fixed by K, and θ : G' → G induce an injection G'/J → G/K
covering the support of f. If f(θq) = 0 off a finite set s of cosets, f lives on finitely many
cosets and sends v to ∑_{q∈s} f(θq)π(θq)v. -/
lemma heckeFun_eq_sum_pullback s (θ : _ → G) (hθ : ∀ g, f g ≠ 0 → ∃ x, (θ x : G ⧸ K) = g)
    (H : ∀ a b, (θ a)⁻¹ * θ b ∈ K ↔ a⁻¹ * b ∈ J) (hs : ∀ q ∉ s, f (θ (q : _ ⧸ J).out) = 0) :
    HasFiniteCosets K f ∧ heckeFun π K f v = ∑ q ∈ s, f (θ q.out) • π (θ q.out) v := by
  apply heckeFun_eq_sum hf <;> simp_all [← QuotientGroup.eq, exists_mk]; peel hθ
  grind [@QuotientGroup.eq _ _ K, mul_inv_cancel_left, Quotient.out_eq]

/-- Let a : G' → G be surjective, a⁻¹(K) = J, f(gk) = f(g) and π(k)v = v for k in K, and F = f∘a
nonzero on finitely many cosets gJ. If ρ(g)v = π(a(g))v, then F via ρ and f via π send v to the same
vector. -/
lemma heckeFun_comp (hF : HasFiniteCosets J F) (ha : Surjective a) (hK : ∀ g, a g ∈ K ↔ g ∈ J) {ρ}
    (hρ : ∀ g, ρ g v = π (a g) v) (e : ∀ g, F g = f (a g)) : heckeFun ρ J F v = heckeFun π K f v :=
  by simp_all [heckeFun_eq_sum_pullback _ _ hF.toFinset a (ha.forall.2 _), ← hK]

include h

lemma apply_heckeFun x : HasFiniteCosets K (f <| x⁻¹ * ·) ∧ heckeFun π K (f <| x⁻¹ * ·) v = π x
  (heckeFun π K f v) := by simp_all [heckeFun_eq_sum_pullback _ h1 h.toFinset (x * ·) (fun _ ↦
  ⟨x⁻¹ * ·, _⟩)]

/-- Let f, f' be nonzero at finitely many representatives of G/K, f right K-invariant, v fixed
by K. Then f'(fv) = (f' ∗ f)v for the action `heckeFun`, where (f' ∗ f)(x) = ∑
f'(g)f(g⁻¹x) over the representatives g.

Known result: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums. -/
lemma heckeFun_heckeFun {f'} (h' : HasFiniteCosets K f') : heckeFun π K f' (heckeFun π K f v) =
  heckeFun π K
  (fun x ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) v := have := apply_heckeFun h hf h1
  by simp_all [↓heckeFun_sum, heckeFun, sum_smul, finsum_sum_comm, fun_smul_left (this _).1,
    fun_smul_right]

include hf'

lemma heckeFun_mem_levelSpace : heckeFun π K f v ∈ levelSpace π _ χ' := (by
  simp [↓← (apply_heckeFun h hf h1 _).2, heckeFun, ← hf' (_ * _) ·, fun_smul_left h])

omit h hf hf'

lemma IsBiInvariant.heckeFun_mem (hb : IsBiInvariant K f) :
  heckeFun π K f v ∈ levelSpace π K := by simp_all [↓heckeFun_mem_levelSpace]
