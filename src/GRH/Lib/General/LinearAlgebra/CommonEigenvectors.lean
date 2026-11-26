import GRH.Lib.General.LinearAlgebra.SubmersionZero
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

General lemmas of commutative and general algebra (textbook or folklore).

This file: Auerbach's lemma: basis dual to chosen forms with all forms bounded by one. Steinitz:
embeddings of a countable ring extend to field isomorphism with C. Embeddings of countable rings
into C extend to fields of continuum size. Semisimplicity by trace form, free integers, minors
criterion for linear dependence. Common eigenvectors and eigencharacters of commuting operators;
sorting by adjacent swaps. -/

open Module Cardinal Finsupp IsAlgClosed LieModule LieSubalgebra LinearMap Matrix Submodule
  Module.Basis

/-- Auerbach's lemma. Let linear forms ℓ_a on a finite-dimensional K-space, a in a compact
space, have only 0 as common zero, with φ∘ℓ_a(v) continuous in a for φ: K → L normed. Then
some ℓ_a are the coordinates of a basis z with all ‖φ(ℓ_a(z_k))‖ ≤ 1. -/
lemma exists_auerbach {K U A L ι} [Field K] [AddCommGroup U] [Module K U] [Module.Finite K U]
    [Fintype ι] {_ : TopologicalSpace A} [CompactSpace A] [NormedField L] (b : Basis ι K U) (ℓ : A →
    Dual K U) (h : ∀ v, (∀ a, ℓ a v = 0) → v = 0) (φ : K →+* L) (hc : ∀ v, Continuous fun a ↦ φ
    (ℓ a v)) : ∃ᵉ (S : ι → A) (z), (∀ k, coord z k = ℓ (S k)) ∧ ∀ a k, ‖φ (ℓ a (z k))‖ ≤ 1 := by
  choose a p using not_forall.1 (AlternatingMap.coe_multilinearMap_injective.ne
    b.dualBasis.det_ne_zero ∘ MultilinearMap.ext_of_span_eq_top fun _ ↦
    span_eq_top_of_ne_zero (by simpa using mt <| h ·))
  choose S hS using (funext (φ.map_det <| b.dualBasis.toMatrix <| ℓ ∘ ·) ▸ (continuous_matrix (by
    simp [Basis.toMatrix, (hc _).comp', continuous_apply])).matrix_det).norm.exists_forall_ge' a
    (by simp)
  have p := (norm_pos_iff.2 (by simpa)).trans_le (hS a)
  have q := b.dualBasis.is_basis_iff_det.2 (by simpa using! p)
  use S, (dualBasis (.mk q.1 q.2.ge)).map (evalEquiv ..).symm, by bound
  simpa [p, Basis.det] using fun a k ↦ congr(‖φ ($(det_smul_mk_coord_eq_det_update ..) _)‖).trans_le
    (Function.comp_update ℓ S .. ▸ hS _ :)

/-- Let f : K → ℂ and g : K → L be injective ring maps from a nonzero countable commutative
ring, L an algebraically closed field of the cardinality of ℂ. Then g = σ ∘ f for some
isomorphism σ : ℂ → L. -/
lemma exists_ringEquiv_extend {L K} [Field L] [IsAlgClosed L] [CommRing K] [Countable K]
    (e : #ℂ = #L) (f : K →+* ℂ) (g : K →+* L) (hf : (⇑f).Injective := by apply RingHom.injective)
    (hg : (⇑g).Injective := by apply RingHom.injective) : ∃ σ : ℂ ≃+* L, ∀ a, σ (f a) = g a := by
  algebraize [f, g]
  erw [← faithfulSMul_iff_algebraMap_injective] at *
  choose _ E using @exists_isTranscendenceBasis K
  have := f.domain_nontrivial
  use equivOfTranscendenceBasis _ _ (lift_mk_eq'.1 (by simp_all [← e, aleph0_lt_continuum,
    ↓← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt (R := K) Subtype.val])).some (E ℂ)
    (E L), fun a ↦ by erw [@IsAlgClosure.equivOfEquiv_algebraMap (s := algebraMap _ _ a)]; aesop

lemma exists_ringHom_complex_extend {D K} [CommRing D] [Countable D] [Field K] {f : D →+* K} {φ : D
    →+* ℂ} (hf : (⇑f).Injective) (hφ : (⇑φ).Injective) (_ : #K ≤ #ℂ) : ∃ ψ, .comp ψ f = φ := by
  let F := FractionRing (MvPolynomial ℂ K)
  let L := AlgebraicClosure F
  rcases mk_le_of_module F L, Algebra.IsAlgebraic.cardinalMk_le_max F L
  choose σ h using exists_ringEquiv_extend (by simp_all [F, le_antisymm_iff, aleph0_le_continuum])
    φ (.comp (algebraMap K L) f) hφ (by simpa [RingHom.injective])
  use .comp σ.symm (algebraMap K L), by ext; simp_all [eq_comm]

variable {k G n : Type} [Field k] [Group G] [Fintype n] (r : G →* GL n k)

/-- Non-degeneracy of the trace form on the span of r(G): any x in that span with tr(x r(g)) = 0
for all g is zero. -/
def IsTraceNondeg := ∀ x ∈ span k (.range (r · |>.1)), (∀ g, (x * r g).trace = 0) → x = 0

/-- The integers e_i are free: vectors α, β of natural numbers with Σα_i = Σβ_i ≤ (n+1)² and
Σα_i e_i = Σβ_i e_i are equal. -/
def FreeInts {n} (e : Fin n → ℤ) := ∀ d ≤ (n + 1) ^ 2, {α | degree α = d}.InjOn (weight e)

/-- For functions v_i: X → k to a field k, indexed by a finite set n, the determinants
det(v_j(x_i)) vanish for all families (x_i) of points of X indexed by n if and only if the
v_i are linearly dependent over k. -/
lemma minors_eq_zero_iff {X} {v : n → X → k} :
    (∀ x, Matrix.det (of (_root_.flip v ∘ x)) = 0) ↔ ¬LinearIndependent k v :=
    ⟨fun h H ↦ det_one.trans_ne one_ne_zero congr($(detRowAlternating.ext_of_span_eq_top
    (fun _ ↦ span_flip_eq_top_iff_linearIndependent.2 H) (φ' := 0) h) _), fun h x ↦
    det_eq_zero_of_not_linearIndependent_cols (h ∘ .of_comp (.funLeft k k x))⟩

/-- Homogenisation by a linear form F: for a polynomial P over R of total degree at most N there
is a homogeneous G of degree N with φ(G) = φ(P) for every R-algebra map φ with φ(F) = 1. -/
lemma exists_homogenization {ι R N} [CommRing R] {F} (c : @MvPolynomial.IsHomogeneous ι R _ F 1) P
    (h : P.totalDegree ≤ N) : ∃ G, MvPolynomial.IsHomogeneous G N ∧ ∀ {A : Type} [CommRing A]
    [Algebra R A] (φ : _ →ₐ[R] A), φ F = 1 → φ G = φ P :=
    ⟨_, .symm ⟨fun v e ↦ by simpa [e] using congr(v $P.sum_homogeneousComponent), .sum _ _ _ fun n
    _ ↦ .subst (by grind) ((c.pow (N - n)).mul (P.homogeneousComponent_mem n))⟩⟩

variable {k : Type*} {W ι} [Field k] [IsAlgClosed k] [AddCommGroup W] [Module k W] (φ : ι → End k W)
  {S : Submodule k W} [Module.Finite k S]

lemma exists_antitone_of_swap {α N} [LinearOrder α] (f : Fin N → α) (P : Equiv.Perm _ → _)
    (h0 : ∃ σ, P σ) (h : ∀ σ i j, i ⋖ j → f (σ i) < f (σ j) → P σ → P (σ * .swap i j)) :
    ∃ σ, P σ ∧ Antitone (f ∘ σ) := (Set.exists_max_image P (toLex <| f ∘ ·) Subtype.finite h0).imp
    fun σ ⟨M, m⟩ ↦ ⟨M, (antitone_iff_forall_covBy _).2 fun i _ c ↦ not_lt.1
    (h σ _ _ c · M |> m _ |>.not_gt ⟨i, by simp_all [Equiv.swap_apply_def]; grind [CovBy]⟩)⟩

/-- For commuting endomorphisms φ_m of a finite-dimensional space over an algebraically closed
field and a proper subspace U, there are scalars χ_m whose joint generalised eigenspace is
not contained in U and which are the eigenvalues of a common nonzero eigenvector. -/
lemma exists_eigenvector_of_commute (hS : ∀ m, ∀ x ∈ S, φ m x ∈ S)
    (c : ∀ m n, ∀ x ∈ S, φ m (φ n x) = φ n (φ m x)) {U} (hU : U ≠ ⊤) : ∃ χ : ι → k, ¬⨅ m,
    End.maxGenEigenspace (restrict _ (hS m)) (χ m) ≤ U ∧ ∃ x ∈ S, x ≠ 0 ∧ ∀ m, φ m x = χ m • x := by
  let := @LieRing.ofAssociativeRing; let L := lieSpan k _ (.range (restrict _ <| hS ·))
  have : IsLieAbelian L := by aesop
  cases' by simpa [*, genWeightSpace] using congr($(iSup_genWeightSpace_eq_top' k L S) ≤ U) with χ H
  exact ⟨_, H ∘ .trans (iInf_mono' (⟨⟨_, subset_lieSpan ⟨·, rfl⟩⟩, le_rfl⟩)),
    (exists_forall_lie_eq_smul _ _ _ χ).imp' (↑) fun _ ⟨h, e⟩ ↦ by simp [← S.coe_smul, ← e, h]⟩

lemma exists_eigenvector_of_functional' (hS : ∀ m, ∀ x ∈ S, φ m x ∈ S)
    (c : ∀ m n, ∀ x ∈ S, φ m (φ n x) = φ n (φ m x)) {η : ι → k} (l : W →ₗ[k] k) (h0 : ¬S ≤ l.ker)
    (h : ∀ m x, l (φ m x) = η m * l x) : ∃ x ∈ S, x ≠ 0 ∧ ∀ m, φ m x = η m • x := by
  have ⟨χ, H, e⟩ := exists_eigenvector_of_commute φ hS c (h0 ∘ comap_subtype_eq_top.1)
  convert e; contrapose H; exact iInf_le_of_le ‹_› (iSup₂_le fun n _ ↦ n.rec bot_le
    fun _ i _ ↦ (by simpa [*] using i ·))

/-- Let Φ map words to endomorphisms of a finite-dimensional space, k algebraically closed, with
Φ[s]Φ(L) = Φ(Ls), the Φ[s] commuting, without joint eigenvector of eigenvalues η_s. Then
some finitely supported (c_L) has ∑ c_L ∏_{s∈L} η_s = 1 and ∑ c_L Φ(L) = 0. -/
lemma exists_words_comb_eq_zero {ι} [Module.Finite k W] (Φ : _ → End k W) (m : ∀ s L, Φ [s] * Φ L =
  Φ (L ++ [s]))
  (c : ∀ s t, Commute (Φ [s]) (Φ [t])) {η : ι → k} (h : ∀ x, (∀ s, Φ [s] x = η s • x) → x = 0) :
  ∃ c : _ →₀ k, c.sum (fun L a ↦ a * (L.map η).prod) = 1 ∧ c.sum (fun L a ↦ a • Φ L) = 0 := by
  obtain ⟨⟨z, x⟩, hx, _, H⟩ := exists_eigenvector_of_functional' (fun s ↦ mulLeft _ (η s, Φ [s]))
    (S := span _ (.range fun L ↦ ((List.map η L).prod, Φ L))) (fun _ ↦ mapsTo_span
    (by simp_all; grind)) (by simp [(c ..).left_comm, field]) (fst ..)
    (one_ne_zero <| · (subset_span ⟨[], rfl⟩)) (by tauto)
  have := smul_mem _ z⁻¹ hx; simp_all [(LinearMap.ext (h _ fun _ ↦ congr($(H _).2 ·)) : x = 0),
    mem_span_range_iff_exists_finsupp, Finsupp.sum, ← prod_mk_sum]

/-- A representation of a commutative monoid on a non-zero finite-dimensional space over an
algebraically closed field has a common eigenvector, and its eigenvalues form a character. -/
lemma exists_eigencharacter {M} [CommMonoid M] (ρ : M →* End k W) (hS : ∀ m, ∀ x ∈ S, ρ m x ∈ S)
    (h : ¬S ≤ ⊥) : ∃ χ : M →* k, ∃ x ∈ S, x ≠ 0 ∧ ∀ m, ρ m x = χ m • x := by
  have ⟨χ, _, x, _, h, e⟩ := exists_eigenvector_of_commute ρ hS
    (by simp [← End.mul_apply, ← map_mul, mul_comm]) (h ∘ comap_subtype_eq_top.1)
  use ⟨⟨χ, ?_⟩, ?_⟩, x <;> simp [← smul_left_inj h, ← e 1, ← e (_ * _), smul_smul, mul_comm, *]
