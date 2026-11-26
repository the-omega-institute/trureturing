import GRH.New.Selmer.RibetCramer
import GRH.New.Selmer.BlocksAndCocycles
import GRH.Lib.General.Algebra.BlockFittingBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Ribet's method with congruent blocks and tied auxiliary primes (see
New.Selmer.RibetElement).

This file: Fitting ideal of one character contains ∏X_j times a polynomial with bounded
constant term. Abstract first-order Ribet lemma with congruent blocks, ties and Fitting ideal
bound. -/
seal Finset.univ Finset.sum Finset.prod

open Submodule Finset IsDiscreteValuationRing fittingIdeal MvPolynomial
variable {O G J n : Type} [CommRing O] [DVR O] [LinearOrder J] [Fintype n] {s :
  Finset G} {Φ : (n → O) →ₗ[O] s → MvPolynomial J O}

/-- For some L ⊆ G: members of Z zero on L have C·c(τ_j) = C·c(τ'_j), j ∈ I, once earlier
τ-pairs, and earlier φ-pairs in I, agree; and the length of Z restricted to L plus that of S
modulo C-torsion is ≤ b, for S ⊆ Z zero on L and all τ, with equal φ-pairs on I. -/
def HasTriangleCost {B} [AddCommGroup B] [Module O B] (Z : Submodule O (G → B)) (τ φ : _ → G)
    (I : Finset J) C b := ∃ L, (∀ j ∈ I, ∀ c ∈ Z ⊓ .pi L ⊥, (∀ i < j, c (τ (i, true)) =
    c (τ (i, false)) ∧ (i ∈ I → c (φ (i, true)) = c (φ (i, false)))) → C • c (τ (j, true)) =
    C • c (τ (j, false))) ∧ ∀ S ≤ Z ⊓ .pi L ⊥, (∀ c ∈ S, (∀ k, c (τ k) = 0) ∧ ∀ j ∈ I,
    c (φ (j, true)) = c (φ (j, false))) → relLength Z (.pi L ⊥) + relLength S (torsionBy O _ C) ≤ b

/-- Let N ⊆ O[X_J]^s contain pΦ(O^n), p ≠ 0, all Φ(z g) − e_g, all Φ(z τ_k) − X_jΦ(z φ_k) (k a
copy of j), and X_iO[X_J]^s for i ∉ I below a member of I. Under `HasTriangleCost` for
`formsMod`, some G∏_{j∈I}X_j lies in `fittingIdeal` N with v(G(0)) ≤ b + (|I| +
|s|)v(C). -/
lemma exists_mem_fittingIdeal_block [Finite J] {z : G → _} {N p τ φ C I b} (hp : p ≠ 0) (h :
  HasTriangleCost (formsMod Φ z N p) τ φ I C b) (hN : ∀ v, Φ (p • v) ∈ N) (hs : ∀ g : s,
  Φ (z g) - (1 : Matrix ..) g ∈ N) (hτ : ∀ k, Φ (z (τ k)) - X (R := O) k.1 • Φ (z (φ k)) ∈ N) (hI :
  ∀ j ∈ I, ∀ i < j, i ∈ I ∨ ∀ v, X (R := O) i • v ∈ N) : ∃ G, addVal O (constantCoeff G) ≤
  b + (#I + #s) * addVal O C ∧ G * ∏ j ∈ I, X j ∈ fittingIdeal N :=
  h.elim fun L ⟨h₂, h₃⟩ ↦ have ⟨e, K, l, v₁, hL, D₁⟩ := exists_cost_le_relLength z hp hN (.pi L ⊥)
  have Z {K'} (k : K ≤ K') : formsMod Φ z K' p ≤ formsMod .. ⊓ .pi L ⊥
    | _, ⟨Ψ, h, rfl⟩ => ⟨⟨Ψ, by tauto⟩, fun _ _ ↦ h (k (by tauto))⟩
  have W i := by simpa [sub_sub_sub_comm, smul_sub] using l (sub_mem (hτ _) (hτ _))
  have ⟨T, t, hv, D₂⟩ := triangle (C • X ·) fun j hj T t m ↦
    (sub_mem_iff_right _ (mem_of_forall_form_eq_zero hp (by tauto)
    fun c hc ↦ (map_smul ..).trans ((C • c).sub_mem_ker_iff.2 (h₂ j hj _ (Z t ⟨c, hc, rfl⟩) fun i h
    ↦ ⟨c.sub_mem_ker_iff.1 (hc ((sub_mem_iff_left _ ((hI j hj i h).elim (smul_mem _ _ <| m ⟨·, h⟩)
    (by tauto))).1 (t (W i)))), (c.sub_mem_ker_iff.1 <| hc <| m ⟨·, h⟩)⟩)))).1
    (by simpa [smul_sub] using T.smul_of_tower_mem C (t (W j)))
  have l' := le_sup_of_le_left (b := RingHom.ker constantCoeff • ⊤) t
  have ⟨f, M, k, v₄, hC, D⟩ := exists_cost_le_relLength z hp (l' <| l <| hN ·) (torsionBy O _ C)
  have ⟨d₄, D₄, _, m, k⟩ := mem_sup.1 (sup_smul_top_le (D _ (subset_span ⟨C • 1, fun g ↦ by
    simpa [smul_sub] using! sub_mem (@hC (C • z g) (by simp +contextual [funext_iff]))
      (M.smul_of_tower_mem C (k (l' (l (hs g))))), rfl⟩)))
  ⟨(e * C ^ #I) • d₄, by
    simp [eq_sub_of_add_eq k, ← m.symm, add_mul]
    grw [v₄, v₁, add_add_add_comm, h₃ _ (Z l') fun | _, ⟨c, hc, rfl⟩ => ⟨fun k ↦ hc
      ((sub_mem_iff_left _ (mem_sup_right (smul_mem_smul (by simp) mem_top))).1 (l' (l (hτ k)))),
      fun j k ↦ by simpa using hc (mem_sup_left (hv k))⟩], by
    simpa [prod_smul, mul_smul] using D₁ _ (D₂ _ D₄)⟩

open Module CompleteLattice Matrix MonoidAlgebra Polynomial Sum Matrix.Module

attribute [-simp] Subtype.forall map_eq_zero map_smul

variable {O L Y G J σ W : Type} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [Group G]
  (u : Y → G →* Matrix σ σ O) {S : Subalgebra O (Y → MvPolynomial J L)}
  (𝒥 : Submodule S (Y → MvPolynomial J L))

/-- S contains the variables X_j and characteristic polynomial coefficients of u; 𝒥 contains the
families p·tr u(g) and tr((u(τ_k) − 1)u(g)) − X_k·tr(((X − 1)ε_k)(u(φ_k))u(g)). -/
def IsTraceIdeal {A K} [CommRing A] [Algebra O A] [Algebra A L] (u : Y → G → Matrix σ σ A) (p :
  O) (τ φ : K → G) (k : K → J) (ε : J → O[X]) := (∀ j, (fun _ ↦ .X j) ∈ S) ∧ (∀ g k,
  (fun x ↦ .C (algebraMap A L ((u x g).charpoly.coeff k))) ∈ S) ∧ ∀ g, (fun x ↦ .C (algebraMap A L
  (p • (u x g).trace))) ∈ 𝒥 ∧ ∀ i, (fun x ↦ .C (algebraMap A L ((u x (τ i) - 1) * u x g).trace) - .X
  (k i) * .C (algebraMap A L (((.X - 1) * ε (k i)).aeval (u x (φ i)) * u x g).trace)) ∈ 𝒥

/-- Ribet's element: β lies in S and some f ∈ S has fβ ∈ 𝒥; on 𝓧, β vanishes and f has no
monomial properly dividing ∏X_j, whose coefficient at π is c. -/
def IsRibetElement [Fintype J] (β : Y → L) {𝓧 : Set Y} (π : 𝓧) c := (.C <| β ·) ∈ S ∧ ∃ f :
    S, f.1 * (.C <| β ·) ∈ 𝒥 ∧ (∀ x : 𝓧, β x = 0 ∧ ∀ d < ∑ j, .single j 1, (f.1 x).coeff d = 0) ∧
    (f.1 π).coeff (∑ j, .single j 1) = c

attribute [local instance] algebraMvPolynomial

attribute [local simp low] obeyingCocycles AlgHom.map_smul_of_tower mul_sum
  Finsupp.apply_linearCombination Finsupp.sum Matrix.sum_apply MvPolynomial.smul_eq_C_mul
  aeval_eq_sum_range eval_eq_sum_range Set.subset_def mem_obeying_cocycleRels sub_eq_iff_eq_add'

/-- Ribet's lemma to first order: on 𝓧, u_x is a block plus characters ξ_e, ξ_0 = 1; β_x is the
determinant of the combination `ribetNormaliser` of the u_x(g) − 1. Some f in S has fβ ∈ 𝒥; on 𝓧,
β = 0 and f has no term properly dividing ∏X_j; that coefficient at π has valuation ≤ b₀ + Σ
b_e + explicit losses.

Ribet's method with congruent blocks and tied auxiliary primes. -/
lemma ribet_first_order [DVR O] [Fintype Y] [Fintype J] [LinearOrder J] {r : Type} [Fintype r] {t}
  [NeZero t] ϵ {𝓧 : Set Y} π (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O} (ξ₀ : ξ 0 = 1)
  (hu : ∀ (x : 𝓧) g, u x g = reindex ϵ ϵ (fromBlocks (ρ x g) 0 0 (diagonal (ξ · g)))) (hρ : span O
  (.range (ρ π)) = ⊤) {γ : 𝓧 → G} {y : 𝓧 → O} (h₀ : ∀ x, ρ x (γ x) = y x • 1) (hy : ∀ x, IsUnit
  (y x - 1)) (hγ : ∀ x e, ξ e (γ x) = 1) {p τ φ ε C p₀ n b₀} (hp : p ≠ 0) (h𝒥 : IsTraceIdeal 𝒥 (u ·)
  p τ φ Prod.fst ε) (hε : ∀ e k, p ∣ (ε k.1).eval (ξ e (φ k)) - 1) a (hC : ∀ e, ∏ k ∈ {e}ᶜ, (ξ e a -
  ξ k a) ∣ C) (ty : J →o _) (hp₀ : p₀ ≠ 0) {β : _ → _} (hβ : ∀ x, β x = algebraMap O L
  (Finsupp.linearCombination O (u x · - 1) (ribetNormaliser (γ π) a (y π) (p₀ * C) n)).det) (hlt :
  b₀ < addVal O p₀) (hb₀ : length O ↥(obeyingCocycles u (ρ π) p₀ ⊓ .pi (.range τ) ⊥ ⊓
  (LinearMap.proj (γ π)).ker) ≤ b₀) [Fintype W] {δ : W → G} {o : W → _} (hδ : ∀ v e,
  ξ e (δ v) = 1) (hH : ∀ v x, Polynomial.aeval (u x (δ v)) (o v * (.X - 1)) = 0) {s} {b : _ →
  _} (hb : ∀ e Z, (∀ c ∈ Z, c ∈ obeyingCocycles u ((scalar Unit).1.comp (ξ e)) p ∧
  (∀ v, c (δ v) = 0) ∧ ∀ m, (∀ g, c g = (ξ e g - 1) • m) → ∀ g, (ξ e a - 1) • c g = 0) →
  HasTriangleCost Z τ φ {j | ty j = e} C (b e) ∧ ∀ c ∈ Z, (∀ g ∈ s, c g = 0) → c = 0) : ∃ c,
  IsRibetElement 𝒥 β π (algebraMap O L c) ∧ addVal O c ≤ b₀ + (∑ e, b e + t * (∑ v, addVal O
  (Polynomial.eval 1 (o v)) + 2 * #s * addVal O C) + (Fintype.card J + 1) * addVal O C) := by
  let Λ := MvPolynomial J O
  let U := of Λ G
  let κ := Algebra.ofId O Λ
  let μ := κ.mapMatrix (m := σ)
  let χ x := (lift Λ ..) (μ.1.1.comp (u x))
  let ψ x := (lift Λ ..) (κ.mapMatrix.1.1.comp (ρ x))
  let η e := (lift Λ ..) (κ.1.1.comp (ξ e))
  have hη e g : η e (U g) = .C _ := lift_of ..
  obtain ⟨k, hk', hk⟩ := univ.induction_on (motive := (∃ k, (∀ e, η e k = 1) ∧ ∀ x ∈ ·, ψ x k = 0))
    ⟨1, by simp⟩ fun x _ _ ⟨k, h', h⟩ ↦ (hy x).exists_left_inv.elim fun z e ↦ ⟨k * z • (κ (y x)
    • 1 - U (γ x)), by simpa [h', hη, hγ, κ, Λ] using congr(κ $e), by
    simp +contextual [h]; simp +zetaDelta [h₀, smul_one_eq_diagonal]⟩
  choose q hq using fun e ↦ show ∃ q, ∀ k, η k q = ite (k = e) (.C C) 0 from (hC e).elim fun w h ↦
    ⟨w • Polynomial.aeval (U a) (Lagrange.nodal {e}ᶜ (κ <| ξ · a)), fun k ↦ by split <;> simp [κ, Λ,
    mul_comm, Lagrange.nodal, -aeval_eq_sum_range, ← aeval_algHom_apply, prod_eq_zero (i := k), *]⟩
  obtain ⟨⟨s₀, h₁⟩, _⟩ := ((fg_iff_compact _).1 .of_finite).exists_finset_of_le_iSup
    (fun g ↦ O ∙ (u · g - 1)) le_rfl, ϵ.symm.nonempty
  let x : W ⊕ s₀ ⊕ s → G := δ ⊕ᵥ ((↑) ⊕ᵥ (↑))
  let T := Fintype.linearCombination O fun i ↦ (u · (x i) - 1)
  choose z hz using by simpa using h₁.trans (c := T.range) (by
    simp [T]; exact (subset_span ⟨inr <| inl ⟨·, ·⟩, rfl⟩))
  let V := Fintype.linearCombination Λ[G] (U ∘ x - 1)
  let v {ι} := (LinearMap.toSpanSingleton O _ (U 1)).compLeft ι
  have hU y g : χ y (U g) = _ := lift_of ..
  have hv y m : χ y (V (v m)) = μ (T m y) := by simp [V, v, T, hU, Fintype.linearCombination]
  let ω := Finsupp.linearCombination O z (ribetNormaliser (γ π) a (y π) (p₀ * C) n)
  let N := Submodule.comap V (span _ {r | ∀ g, (fun x ↦ algebraMap _ _ (χ x r * χ x (U g)).trace) ∈
    𝒥} ⊔ .map (.mulRight _ (V (v ω))) (RingHom.ker (η 0)))
  have le r (h : ∀ x, χ x (V r) = 0) : r ∈ N := mem_sup_left (subset_span (by
    simp [h, ← Pi.zero_def]))
  have hg g h := le (v (z (g * h) - z g) - U g • v (z h)) (by simp [*, mul_sub])
  have hx i := le (v (z (x i)) - Pi.single i 1) (by simp [V, *])
  have hK θ (h : Finsupp.linearCombination O (fun g ↦ (u · g - 1)) θ = 0) :=
    le (v (Finsupp.linearCombination O z θ)) (by simp [↓hv, Function.comp_def, *])
  have tr A : .C (algebraMap O L A.trace) = algebraMap _ (MvPolynomial J L) (μ A).trace := by
    simp +zetaDelta [trace]
  have hτ k : v (z (τ k)) - (.X k.1 : Λ) • Polynomial.aeval (U (φ k)) (ε k.1) • v (z (φ k)) ∈ N :=
    mem_sup_left
    (subset_span fun g ↦ by simpa [*, Λ, mul_comm (Polynomial.X - _), sub_mul] using (h𝒥.2.2 g).2 k)
  have hω g : (U g - 1) • v ω ∈ N := mem_sup_right ⟨U g - 1, by simp [*]⟩
  have hW w : p • w ∈ N := mem_sup_left ((by simp : V w • p • U 1 = V (p • w)) ▸ smul_mem _ _
    (subset_span fun g ↦ by simpa [*, Λ] using (h𝒥.2.2 g).1))
  let ψ₀ := (MvPolynomial.aeval (S₁ := O) 0).mapMatrix.comp ((ψ π).restrictScalars O)
  have ψU g : ψ₀ (U g) = ρ π g := Matrix.ext (by simp +zetaDelta)
  obtain ⟨B₀, hB₀, e₀⟩ := exists_rows_addVal_det_le ψ₀ (ψ₀.toLinearMap.range_eq_top.1
    (eq_top_mono (by simp [span_le, ← ψU]) hρ)) N hp₀ hlt ((length_le_of_le_map
    (.funLeft _ _ x) _ le_rfl).trans hb₀) fun w H ↦ let l := Fintype.linearCombination O w
    ⟨l ∘ z, .imp (.imp_right (hy π).smul_eq_zero.1) _root_.funext (by
    simpa [show ∀ m, ∑ j, ψ₀ (v m j) • w j = l m by simp [v, l, Fintype.linearCombination],
      mul_smul, ← smul_sum, sub_smul, ψU, ω, ribetNormaliser, smul_sub, h₀,
      add_smul, ↓Set.forall_mem_range, show ∀ j a, ψ₀ ((.X j : Λ) • a) = 0 by simp [ψ₀,
      Matrix.map_smul'], show ∀ b : r → QuotSpan p₀, p₀ • b = 0 by simp [↓funext_iff,
      smul_quot_eq_zero_of_dvd], ← Finsupp.apply_linearCombination] using
      (⟨⟨⟨⟨(H _ <| hg · ·), (H _ <| hK · ·)⟩, (H _ <| hτ ·)⟩, H _ (sub_mem (hω (γ π)) (N.smul_mem
      (U (γ π) - 1) (hg (γ π) a)))⟩, (H _ <| hx ·)⟩ : (((_ ∧ _) ∧ _) ∧ _) ∧ _))⟩
  have R x a : χ x.1 a = reindex ϵ ϵ (fromBlocks (ψ x a) 0 0 (diagonal (η · a))) :=
    (Equiv.symm_apply_eq _).1 (by ext1 ⟨⟩ ⟨⟩ <;> simp +zetaDelta [hu, lift_apply,
    diagonal, apply_ite κ])
  have D (x : 𝓧) (M : type_of% B₀) :=
    (((Matrix.comp ..) (M.map (χ x))).det_submatrix_equiv_self
    (.trans (.symm (.prodSumDistrib ..)) (.prodCongr 1 ϵ))).symm.trans (by
    convert ((Matrix.comp ..) (M.map (ψ x))).det_fromBlocks_zero₂₁ 0 (blockDiagonal (M.map <| η ·))
    ext1 ⟨⟩ ⟨⟩ <;> simp [R, blockDiagonal, diagonal])
  let E e := .funLeft _ _ inr ∘ₗ (η e).toLinearMap.compLeft (W ⊕ s₀ ⊕ s)
  have B {e r} {A : _ →ₗ[_] r → _} {K} (l : (N.restrictScalars _).map (A ∘ₗ E e) ≤ K) :=
    hb e (formsMod ((A ∘ₗ E e).restrictScalars O ∘ₗ v) z K p) (fun _ ⟨Ψ, H, Q⟩ ↦ Q ▸
    have h m {w} k (q : ∀ x, η e _ = η e _) := @H m (l ⟨w, k, congr(A $(_root_.funext q))⟩)
    ⟨by simpa using! And.intro (fun g g' ↦ h (z (g * g') - z g - ξ e g • z g') (hg g g') (by
      simp [hη, Λ])) (H <| l ⟨_, hK · ·, rfl⟩), fun v ↦ h _ (hx (inl v)) (by simp [x]),
      fun m L g ↦ L g ▸ by_contra fun b ↦ by
    obtain ⟨w, W⟩ := (dvd_prod_of_mem (a := 0) _ (by simp; rintro rfl; simp [ξ₀] at b)).trans (hC e)
    have K : Ψ ω = _ := congr($(show Ψ ∘ₗ Finsupp.linearCombination O z =
      (Finsupp.linearCombination O (ξ e · - 1)).smulRight m by ext : 2; simpa using L _) _)
    simp [ribetNormaliser, *] at K; set r := Finsupp.linearCombination O (M := O) _ _
    refine IsLocalRing.nonunits_add (b <| ·.smul_eq_zero.1 ?_) (by
      simp [← addVal_eq_zero_iff, hlt.ne_zero]) ((sub_add_cancel _ (p₀ * (w * r))).substr (hy π))
    linear_combination (norm := module) (ξ e g - 1) • K - (Ψ.map_smul ..).symm.trans (h ((ξ e g - 1)
      • ω) (hω g) (by simp [hη, Λ]))⟩)
  choose m hm k₁ using fun e i ↦ (((N.restrictScalars _).map (.funLeft _ _ inl ∘ₗ E
    e)).sub_mem_iff_right (mem_of_forall_form_eq_zero hp (by exact ⟨_, hW <|
    v ·, by simp⟩) fun Ψ h ↦ congr($((B le_rfl).2 _ ⟨Ψ, h, rfl⟩ (h ⟨_, hx <| inr <|
    inr ⟨·, ·⟩, by ext; simp [E, x]⟩)) _))).1 ⟨_, hx (inr (inl i)), map_sub ..⟩
  simp [E, funext_iff] at k₁
  choose ν hn hn' using fun i ↦ univ.induction_on (motive := (∃ w ∈ N, ∀ e ∈ ·, ∀ j, η e (w (inr
    (inl j))) = ite (j = i) 1 0)) ⟨0, by simp⟩ fun e _ _ ⟨w, h, H⟩ ↦ ⟨_, add_mem h (N.sum_smul_mem
    (t := univ) (Pi.single i 1 - w ∘ inr ∘ inl) fun j _ ↦ hm e j), by simp +contextual [H, k₁]⟩
  let A e := vecMulLinear (fromRows (m₂ := s) (-(of (E e <| ν ·)).toCols₂) 1)
  let 𝔮 := restrictSupportIdeal O _ (isLowerSet_Iic (∑ j : J, .single j 1)).compl
  choose Γ hl hΓ using fun e ↦ exists_mem_fittingIdeal_block hp (@B e _ (A e)
    (_ ⊔ 𝔮.colon {∏ j with ty j < e, .X j} • ⊤) le_sup_left).1
    (mem_sup_left ⟨_, hW <| v ·, by simp⟩) (mem_sup_left ⟨_,
    hx <| inr <| inr ·, by ext1; simp [E, A, x, vecMul_eq_sum]⟩) (fun k ↦ (hε e k).elim fun d h ↦
    mem_sup_left ⟨_, add_mem (hτ k) (hW ((.X _ : Λ) • v (d • z (φ k)))), by
    erw [← (A e).map_smul, ← (A e).map_sub]; congrm A e fun _ ↦ ?_
    simp [E, hη, Λ, by simpa [κ, Λ] using congr(κ $h)]; ring⟩) fun j h i hi ↦
    ((mem_filter.1 h).2 ▸ ty.mono hi.le).eq_or_lt.imp (by simp) fun k _ ↦ mem_sup_right
    (smul_mem_smul (by simpa [MvPolynomial.X, ← monomial_sum_one, 𝔮, Finsupp.le_def,
      ← 𝔮.restrictScalars_mem O] using ⟨i, by simp [k, Finsupp.single_apply]⟩) trivial)
  choose d hd ζ hI h₃ using (mem_sup.1 <| fittingIdeal.sup_smul_top_le <| hΓ ·)
  let a := (∏ v, (o v).eval 1) * C ^ #s
  choose _ w z hw using (mem_span_set'.1 <| hd ·)
  choose B h e' using (z · · |>.2)
  choose w' h k' using h
  let M (i : ∀ _, _) := of ((fun v ↦
    Pi.single (inl v) (Polynomial.aeval (U (δ v)) (o v))) ⊕ᵥ (ν ⊕ᵥ (∑ e, q e • w' e (i e) ·)))
  have e j i : (of (η i <| M j · ·)).det = .C a * (B i (j i)).det := by
    rw [← fromBlocks_toBlocks (of _), (_ : toBlocks₁₂ _ = 0), det_fromBlocks_zero₁₂',
      ← IsDiag.diagonal_diag (A := toBlocks₁₁ _), ← fromBlocks_toBlocks (toBlocks₂₂ _), (_ :
      (toBlocks₂₂ _).toBlocks₁₁ = 1), det_fromBlocks_one₁₁', (_ : _ - _ = κ C • B i (j i))] <;> simp
      +contextual [IsDiag, Pairwise, a, κ, Λ, M, ← ext_iff, toBlocks₁₁, toBlocks₁₂,
      toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hn', hη, hδ, hq, ← k', A, E, vecMul_eq_sum, eq_comm,
      mul_assoc, mul_add, sub_eq_neg_add]
  have hd' D := by simpa [𝔮, ← 𝔮.restrictScalars_mem O, mem_restrictSupport_iff, not_imp_not,
    mul_sub, h₃, sum_fiberwise, MvPolynomial.X, ← mul_assoc, ← monomial_sum_one,
    coeff_mul_monomial'] using 𝔮.mul_mem_left D ((sub_eq_of_eq_add' (prod_add_ordered univ d
    ζ)).symm.subst (sum_mem fun e _ ↦ 𝔮.mem_of_dvd (by simp [h₃, mul_dvd_mul_left,
    prod_fiberwise_eq_prod_filter, Dvd.dvd.mul_right]) (hI e ⟨_, rfl, rfl⟩)))
  have ⟨hS, P⟩ := exists_ribet_element_cramer χ (MvPolynomial.aeval (⟨_, h𝒥.1 ·⟩)).1 (by ext <;>
    simp [Λ]) (by simp +zetaDelta [Algebra.ofId, ↓charpoly_map, h𝒥.2.1]) 𝒥 (v ω) V (.C <| β ·)
    (by simp [hβ, hv, ω, μ, hz, Finsupp.linearCombination, det_apply', κ, Λ])
  choose f hf hf' using fun i ↦ P (k * (∏ e, w e (i e)) • q 0) (B₀ + k • (M i - B₀)) fun j ↦
    add_mem (hB₀ j) (N.smul_mem _ (sub_mem (j.rec (fun v ↦ le (Pi.single _ _) fun y ↦ by
    simpa [V, x, hU] using congr(μ $(hH v y))) (Sum.rec hn
      (N.sum_smul_mem _ fun e _ ↦ h e _ ·))) (hB₀ j)))
  have H (y : 𝓧) n hn : ((∑ i, f i).1 y).coeff n = _ := .trans (by
    simp [(hf · y fun m (k : _ = _) ↦ by simp +contextual [*]), ↓D, (det_classical _).symm.trans
      (det_blockDiagonal _), R, trace, e, ← hw, ← e', hq, Fintype.prod_sum, hk, hk', ← ϵ.sum_comp,
      Matrix.map, κ, Λ, ← MvPolynomial.coeff_map]
    ac_rfl) (congrArg (algebraMap O L) (hd' (((Matrix.comp ..)
    (B₀.map (ψ y))).det * κ (C * a ^ t)) n
      hn).symm)
  exact ⟨_, ⟨hS, _, by simp [sum_mul, sum_mem, hf'], fun y ↦ ⟨by simp +contextual [*,
    det_eq_zero_of_column_eq_zero (ϵ (inr 0)), ϵ.surjective.forall, Finsupp.linearCombination,
    diagonal], fun d h ↦ by simp [↓H y d h.le, h.not_ge]⟩, H π _ le_rfl⟩, by
    simp [← constantCoeff_eq]
    grw [addVal_prod, hl, ← e₀]
    simp +zetaDelta [det_apply', addVal_prod, ← sum_mul, ← Nat.cast_sum,
      ← card_eq_sum_card_fiberwise]
    ring_nf; rfl⟩
