/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Iwahori.SortedExponents. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Iwahori/SortedExponents.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori.IwahoriInjective
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Exchanging and sorting the θ_i(ϖ) of exponents (`torusChar` θ, l); eigenvectors
give exponents in unitary
representations. -/

open Module ComplexOrder Equiv Matrix Pi Submodule Units Valued WithZero Filter.Germ
  Submonoid.LocalizationMap

attribute [-simp] Fin.val_rev map_pow

attribute [local simp] LinearMap.domRestrict₁₂_apply Monotone mulSingle_apply mulSingle_comp_equiv
  diagGL_mem_intGL normAbsChar transvectionGL_mem_proIwahori

variable {F : Type*} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N} {ρ : Rep ℂ (GL (Fin N) F)}
  [IsSmoothRep ρ.ρ] {ϖ : Fˣ} {θ l x} {τ : _ → ℂ} (hϖ : v ϖ.1 = exp (-1)) (hx : x ∈ levelSpace ρ.ρ
  proIwahori) (hτ : ∀ t, diagGL t ∈ intGL _ 𝒪[F] → ρ (diagGL t) x = τ t • x) (hP : ∀ σ,
  (∀ i ε, v ε.1 = 1 → τ (mulSingle i ε) = τ (mulSingle (σ i) ε)) → ∃ c : ℂ, ρ (permGL σ) x = c • x)

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

include hϖ hx hτ hP in
/-- Let I₁ fix x, diagonal units act on x by τ, and each permutation preserving the coordinates
τ_i of τ act on x by a scalar. An exponent (θ, l) with l(x) ≠ 0 gives a permutation σ and an
exponent (θ∘σ, l') with l'(σ⁻¹x) ≠ 0 and |θ_{σ(i)}(ϖ)| non-increasing, ϖ a uniformiser. -/
lemma IsExponent.exists_sorted (hl : IsExponent ρ (torusChar θ) l) (h0 : l x ≠ 0) : ∃ σ : Perm _,
  (∃ l, IsExponent ρ (torusChar (θ ∘ σ)) l ∧ l (ρ (permGL σ⁻¹) x) ≠ 0) ∧ Antitone ((‖θ · ϖ |>.1‖) ∘
  σ) := exists_antitone_of_swap _ _ ⟨1, l, hl, by simpa⟩ fun σ i j c hf ⟨l, hl, h0⟩ ↦ by
  have ⟨h, n, k⟩ : i < j ∧ i ≠ j ∧ i.rev.1 = j.rev + 1 := by simp at c; grind
  let π := σ * swap i j; set y := ρ _ x; set ξ := torusChar (θ ∘ σ)
  have χ t : torusChar (θ ∘ π) t = ξ (t ∘ swap i j) * normAbsChar
    (t i / t j) := by
    ext; induction t using mulSingle_induction <;> simp [-normAbsChar, mul_comp, ξ, field, *]
    grind [Perm.mul_apply, val_one]
  let s := l ∘ₗ ρ (permGL (swap i j))
  have h1 : s y ≠ 0 := by simpa [y, s, -swap_inv]
  let S := s ∘ₗ compactMean ρ.ρ proIwahori; let U t := ρ (diagGL t) * compactMean ρ.ρ proIwahori
  have D t (ht : t ∈ dominantTorus) (e : log (v (t j / t i).1) ≤ 1) z : _ = ξ (t ∘ swap i j) * S
    z := .trans (by simp [↓diagGL_mul_permGL, Function.comp_def]; rfl) (hl.apply_monomial_translate
    hϖ (compactMean_mem_levelSpace _) mem_proIwahori_iff_blockParahoric.2 _
    (by simp_all [dominantTorus, log_le_iff_le_exp]; grind))
  let w := (if · < j then ϖ else 1)
  have hw : w ∈ dominantTorus := by simp +decide [dominantTorus, w, apply_ite, ite_apply, *]; omega
  have K : w ∘ swap i j = w * mulSingle j ϖ * mulSingle i ϖ⁻¹ := by ext; simp [w]; grind
  have T {a b t c z} {h : a ≠ b} (H : transvectionGL h ((t b).1 / (t a).1 * c) ∈ proIwahori) :
    ρ (transvectionGL h c) (U t z) =
    U t z := by simpa [U, H] using congr(ρ $((by ext; simp [transvection]; grind [ne_zero] :
    transvectionGL h c * diagGL t = diagGL t * (⟨_, H⟩ : proIwahori))) (U 1 z))
  have W {y} (hy : ∀ a, v a ≤ 1 → ρ (transvectionGL n a) y = y) : S y = s y :=
    map_compactMean_of_factor hl.apply_proIwahori fun k o ↦
    (exists_swap_conj_mem_proIwahori c o).imp' _ fun c ↦ (⟨·, by simp [hy _ c.2]⟩)
  have G z κ : _ → _ • S _ = _ + _ := D w hw (by simp [w, *]) z ▸ quadratic_relation c κ
    hl.apply_proIwahori fun _ a ↦ T (by simp +decide [w, field, a.trans_lt, *])
  have P t (ht : t ∈ dominantTorus) z (h0 : l z = 0) : S (U t z) = torusChar (θ ∘ π) t * S z := by
    induction' e : (v (t j / t i).1).log.toNat with _ ih generalizing t z
    · simp [(ht h.le).ge_iff_eq] at e
      simpa [χ, e, ← D _ ht] using! W fun _ _ ↦ T (by simp [*])
    refine div_mul_cancel t w ▸ congr(s $(iwahori_operator_mul ?e hw
      (compactMean_mem_levelSpace z))).symm.trans ((ih _ ?e _
      (by simp [*]) ?_).trans (by simpa [χ w, w, field, hϖ, h] using! G z 0 (by
      simp +contextual [↓hl.apply_diagGL_unit, U, *])))
    all_goals simp [dominantTorus, w, ← log_le_log, apply_ite, *] at ht e c ⊢; clear * - ht e c
              rcases @ht j, (@ht · i); grind
  use S ∘ₗ (U w - (ξ w).1 • 1), fun d e z ↦ .trans
    (by simp [S, U, iwahori_operator_mul, mul_comm, *]) (P d e _ (by simp [U, *]))
  simp_intro H
  cases hP (swap (σ i) (σ j)) fun a ε _ ↦ by
    by_contra; have Z π := congr(l (ρ $(diagGL_mul_permGL (mulSingle (σ⁻¹ a) ε) π⁻¹) x))
    simp [apply_ite, hl.apply_diagGL_unit, *] at Z
    have z0 := (Z π).resolve_left (by simpa [π, mul_swap_eq_swap_mul, (Z σ).resolve_right h0])
    grind [by simpa [P w hw y z0, ξ, w, *, mul_assoc] using H, (π.injective.ne n).lt_or_gt.elim
      (transvectionGL_apply_permGL_inv hx · |> W |>.trans_ne h1) fun C ↦ right_ne_zero_of_smul
      ((quadratic_relation c 0 hl.apply_proIwahori (transvectionGL_apply_permGL_inv hx C)
      (by simp +contextual [↓hl.apply_diagGL_unit, *])).trans_ne (by simpa))]
  have E {a b} (p : σ a < σ b ∨ π a < π b) h c k : ρ (transvectionGL h c) y = y := p.rec (by simp
                [y, mul_swap_eq_swap_mul σ, -map_inv,
    transvectionGL_apply_permGL_inv hx ·, *]) (transvectionGL_apply_permGL_inv hx · c k)
  simp [NeZero.ne, (by simpa [W (E _ n), π, ξ, *, field, pow_succ, ← sub_eq_iff_eq_add] using
    (G y (ξ w * s y) fun u _ _ ↦ by simpa [hl.apply_diagGL_unit, apply_ite, U, field, π, n.symm,
    hl.apply_proIwahori, *] using! (congr(l (ρ $(swap_mul_transvectionGL n u) y)).symm)))] at hf

variable {B} (hB :
  IsUnitary ρ.ρ B) [Module.Finite ℂ ((cyclicSpan ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori))]

/-- Let ρ be smooth with invariant scalar product B, the span V_x of translates of x having
finite-dimensional I₁-invariants. If V_x contains a ξ-eigenvector of the U_t, then (ξ,
B(w,·)) is an exponent for some w ∈ V_x with B(w,w) ≠ 0. -/
lemma IsIwahoriEigen.exists_isExponent (hB : IsUnitary ρ.ρ B) {ξ y} (H : IsIwahoriEigen ρ ξ y) (hy : y ∈ cyclicSpan ρ.ρ x) :
    ∃ w ∈ cyclicSpan ρ.ρ x, B w w ≠ 0 ∧ IsExponent ρ ξ (B w) := by
  obtain ⟨_, ⟨w, h, rfl⟩, z, e⟩ := exists_eigenvector_of_functional' (iwahoriHeckeHom ρ · |>.dualMap)
    (S := .map (B.domRestrict₁₂ ..) ((cyclicSpan _ x).submoduleOf _)) (fun | t, _, ⟨w, h, rfl⟩ => ⟨⟨_,
          compactMean_mem_levelSpace _⟩, compactMean_mem_cyclicSpan (diagGL t)⁻¹ h, by ext; simp [hB.adjoint_eq_inv, hB.compactMean_adjoint, ← hB.compactMean_adjoint w, iwahoriHeckeHom]⟩) (fun _
    _ l _ ↦ congr(l ∘ₗ $((Commute.all ..).map (iwahoriHeckeHom ρ)))) (.applyₗ ⟨y, H.2.1⟩) ((hB.1 _ H.1).ne' <|
    · ⟨⟨y, H.2.1⟩, hy, rfl⟩) fun t l ↦ (l.congr_arg (Subtype.ext (H.2.2 _ t.2))).trans (l.2 ..)
  use w, h, (hB.1 w fun _ ↦ by simp_all).ne', fun _ a z ↦
    by simpa [← hB.compactMean_adjoint, iwahoriHeckeHom] using congr($(e ⟨_, a⟩) ⟨_,
    compactMean_mem_levelSpace z⟩)

include hϖ hx hτ hP hB in
/-- Let ρ be unitary, x ≠ 0 and τ as in `IsExponent.exists_sorted`, V_x the span of the
translates of x, with finite-dimensional I₁-fixed part. Some exponent (θ, l) has l(x) ≠ 0
and θ_i = τ_i on units, and V_x holds an eigenvector for θ∘σ with |θ_{σ(i)}(ϖ)|
non-increasing. -/
lemma exists_sorted_of_type (h0 : x ≠ 0) : ∃ θ, (∃ l, IsExponent ρ (torusChar θ) l ∧ l x ≠ 0) ∧
  (∀ i ε, v ε.1 = 1 → θ i ε = τ (mulSingle i ε)) ∧ ∃ σ : Perm _, Antitone ((‖θ · ϖ |>.1‖) ∘ σ) ∧
  ∃ y ∈ cyclicSpan ρ.ρ x, IsIwahoriEigen ρ (torusChar (θ ∘ σ)) y := by
  have ⟨s, ht, I⟩ := exists_iwahoriHeckeHom_injective ρ hϖ
  have R t : (cyclicSpan _ x).submoduleOf _ ∈ (iwahoriHeckeHom ρ t).invtSubmodule := fun _ ↦
    compactMean_mem_cyclicSpan _
  have ⟨χ, y, ⟨Y, Q⟩, z, e⟩ := exists_eigencharacter (S := _ ⊓ ⨅ (i) (ε : Fˣ) (h : v ε.1 = 1),
    (iwahoriHeckeHom ρ ⟨mulSingle i ε, by simp [dominantTorus, apply_ite, h]⟩).eigenspace
    (τ (mulSingle i ε))) _ (fun t y h ↦
    ⟨R t h.1, by simp [← End.mul_apply, ← map_mul, mul_comm]; aesop⟩) (h0 congr($(@· ⟨x, hx⟩
    ⟨self_mem_cyclicSpan, by aesop (add simp [iwahoriHeckeHom, apply_ite])⟩)))
  have ⟨θ, c⟩ : ∃ θ, ∀ t, χ t = torusChar θ t :=
    ⟨torusChar.2 (AwayMap.lift ⟨s, _⟩ (dominantTorus.subtype.toLocalizationMap (Group.isUnit ·.1.1)
    (eventually_pow_mul_mem_dominantTorus ht · |>.exists.rec fun k ↦ (⟨⟨⟨_, ·⟩, _, k, rfl⟩,
    by ac_rfl⟩)) (by simp)) (by simpa [*] using I.ne z)).toHomUnits, fun t ↦ by simp; erw [lift_eq]⟩
  simp +contextual [smul_left_inj, *] at Q e
  have ⟨w, Y, z, hl⟩ := IsIwahoriEigen.exists_isExponent hB ⟨by simpa, y.2, (congr($(e · ·)))⟩ Y
  refine ⟨θ, ⟨_, hl, ?o⟩, Q, (hl.exists_sorted hϖ hx hτ hP ?o).imp fun σ ⟨⟨l, L, h⟩, H⟩ ↦ ⟨H,
    (exists_eigenvector_of_functional' _ R (by simp [← End.mul_apply, ← map_mul, mul_comm])
    (l.domRestrict _) (h <| L.apply_compactMean ▸ @· ⟨_, compactMean_mem_levelSpace _⟩
    (compactMean_mem_cyclicSpan _ self_mem_cyclicSpan)) fun m z ↦ L.apply_compactMean ▸
    compactMean_eq_self _ z.2 ▸ L m.2 _).rec fun y ⟨Y, z, G⟩ ↦
    ⟨y, Y, by simpa, y.2, (congr($(G ⟨·, ·⟩)))⟩⟩⟩
  refine fun o ↦ (coe_eq.1 (span_le (p := ((RingHom.ker
    (coeRingHom (R := ℂ) (.atTop : Filter ℕ))).restrictScalars
    _).comap (.pi fun n ↦ B w ∘ₗ ρ (diagGL (s ^ n)))).2 (Set.range_subset_iff.2 fun g ↦ coe_eq.2 ?_)
    (compactMean_mem_cyclicSpan (K :=
    proIwahori) 1 Y))).exists.rec (by simp [hl (pow_mem ht.monotone _), z])
  have ⟨u, _, ⟨t, σ, k⟩, _⟩ := exists_iwasawa_bruhat g
  filter_upwards [eventually_v_mul_pow_le_one ht u,
    eventually_pow_mul_mem_dominantTorus ht t] with n a d
  simpa [by simpa using hx ⟨_, k⟩, (by_contra fun h ↦ (hP σ fun i ε _ ↦ by simpa [*,
    hl.apply_diagGL_unit, apply_ite] using (congr(B w (ρ $(diagGL_mul_permGL (mulSingle (σ i) ε) σ)
    x)).symm)).rec (by aesop) : B w (ρ (permGL σ) x) = 0)] using (hl.apply_proIwahori (MulAut.conj
    (diagGL (s ^ n)) u) (by simp_all [mem_proIwahori_iff_of_unitriangular,
    diagGL, field]) _).trans (hl.apply_monomial_translate hϖ hx mem_proIwahori_iff_blockParahoric.2
    σ fun _ _ h ↦ .inl (d h.le))
