/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.BaseChangeEigenchar. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/BaseChangeEigenchar.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.WeilDataExtension
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.ParahoricColumns
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangeLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). Only existence is proved, for a lift from U(n) over E to U(n) over E' (not GL_n), with
E'/E tame and E containing enough roots of unity. Hecke polynomials match where the place splits
completely and an auxiliary character is trivial, tame types are kept, and class sums are compared
directly, without stabilisation. Source: J.-P. Labesse, Changement de base CM et séries discrètes,
in On the stabilization of the trace formula, 2011, Cor. 5.3, and Cohomologie, stabilisation et
changement de base, Astérisque 257, 1999; J. Arthur and L. Clozel, Simple algebras, base change, and
the advanced theory of the trace formula, Ann. Math. Studies 120, 1989; local matching after P.
Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013, Prop. 2.1 (norms
inverted inside O[γ]) and J.-P. Labesse, Fonctions élémentaires et lemme fondamental pour le
changement de base stable, Duke Math. J. 61, 1990.

This file: Twisted trace over E' is proportional to trace over E for matching functions. Existence
of weak prime-degree base change for definite unitary groups with matched local data. Base change
keeps a pro-p Iwahori eigencharacter, composed with the norm. -/

open Module Filter Matrix Polynomial Space U Matrix.Module

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] {μ : (𝔸f E)ˣ →* ℂˣ}
  [CMOver E E'] {E₁ E'' : Type} {n'} [Field E₁] [CMType E₁] [Field E''] [Algebra E₁ E'']
  [CMOver E₁ E''] [Fintype n']

open Function in
attribute [local implicit_reducible] stdSpace in
attribute [local simp] Function.Injective _root_.Gf.atPlace RingHom.comp mul_assoc in
/-- Twisted trace identity for a step E'/E: if norm-one elements of integral K are σ-coboundaries
and L ≤ K is open, σ-stable, there are c ≠ 0 and a σ-intertwiner t on base-changed forms with
tr(T't) = c tr T for operators of matching pairs (f, φ). -/
lemma twisted_trace_identity [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) [IsStep (E := E) E' μ] κ {K L}
    (hK : K ≤ Kf _ n) (hL : L ≤ K) (oL : L.IsOpen) (σL : L.comap (galoisGf σ) = L) (coh : ∀ s ∈ K,
  twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t) : ∃ c ≠ 0, ∃ t :
  End ℂ _, (∀ g ψ, t (formTranslation _ _ g ψ) = formTranslation _ _ (galoisGf σ g) (t ψ)) ∧ ∃ h,
  ∀ f φ, IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (normKer _ μ) baseChangeGf K f φ →
  ∀ T T', IsOperatorOf ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf) T f → IsOperatorOf
  ((stdSpace ..).formTranslation κ.baseChange) L T' φ → (T' * t.restrict h).trace ℂ _ =
  c * T.trace ℂ _ := by
  have w := exists_twisted_weightRep_trace (n := n) hσ κ
  extract_lets j ω ρ at w
  let e : U 1 →* Gf E' n := U.map (algebraMap E' _)
  have fσ g (h : galoisGf σ g = g) : ∃ k : Gf E n, _ ∧ baseChangeGf k = g :=
    mem_range_map _ (adeleMap_injective
    _) (by simp) _ (ext (adeleMap_galois_descent hσ congr($h.1.1 · ·) |>.choose_spec))
  have fτ g (h : ω g = g) : ∃ k, j k = g := (mem_range_map _ (by simp) (by simp) _
    (ext (galois_descent_prime hσ congr($h.1.1 · ·) |>.choose_spec))).imp (by tauto)
  let τ := by apply ω.toMulEquiv (mapEnd (map_star_CM ↑σ⁻¹)) <;> ext <;> simp [ω, U.map]
  let θ := by apply (galoisGf (n := n) σ).toMulEquiv (galoisGf σ⁻¹) <;> ext <;> simp [U.map] <;>
    erw [adeleMap_id]
  obtain ⟨⟨s, hs, w⟩, ij, X, ie, hτ, hj, fj, ι⟩ := w, (by simp +zetaDelta [baseChangeGf, U.map,
    DFunLike.ext_iff, Gf.val_ext_iff, Units.ext_iff, ← ext_iff] : Injective j ∧
    (stdSpace ..).embFin = e ∧ Injective e ∧ (∀ γ, e (ω γ) = galoisGf σ (e γ)) ∧ (∀ γ, e (j γ) =
    baseChangeGf ((stdSpace ..).embFin γ)) ∧
    (∀ γ, ω (j γ) = j γ) ∧ ∀ g : Gf E n, galoisGf σ (baseChangeGf g) = baseChangeGf g)
  obtain ⟨M, ⟨c, _, _, _, H⟩, d, _, t, R, H'⟩ := map_twistedNorm e hτ, isSampleTotal_twisted_trace _
    κ 1 continuous_id (fun _ ↦ baseChangeGf_mem_Kf.1 ∘ @hK _) (L.comap_mono hL)
    (continuous_baseChangeGf.1 _ oL) rfl 1 (by simp) 1 (by simp), (X ▸ isSampleTotal_twisted_trace
    (stdSpace ..) _ θ (continuous_map : Continuous (galoisGf σ⁻¹)) hK hL oL σL τ) hτ s hs
  refine ⟨d / c, by simp [*], _, by intros; ext; simp; erw [θ.left_inv'], R, fun f φ h _ _ a i ↦ ?_⟩
  field_simp
  have nc x δ := M _ δ ▸ @twistedNorm_conj _ _ _ (finrank E E') x (by exact Subtype.ext (
             adeleMap_pow_finrank_eq_one (σ := σ) ▸ (finrank ..).rec (by tauto) (by tauto) x : _ =
    x.1.map 1)) _
  let q (δ : U 1) := (δ.1 : GL n E').1.charpoly
  have cq δ : (e δ).1.1.charpoly = (q δ).map _ := charpoly_map ..
  let' C (P : E'[X]) := P.map (algebraMap _ (𝔸f E')) ∈ (_ : Set _) ∧ σ • P = P
  choose! z hz m using fun {P} (c : C P) ↦ h.2 _ (by exact c.1) (ext (by simpa using ext_iff.1 c.2))
  have fx {ν} δ (h : SemiconjBy δ (ω ν) ν) x a : C (q ν) := ⟨⟨x⁻¹ * e ν * x, a,
    by simpa [← cq] using! charpoly_units_conj x.1⁻¹ _⟩, by
    simpa [q, smul_eq_map, ← charpoly_map, ← mul_assoc] using! congr(q (δ⁻¹ * $h))⟩
  choose! _ _ W using fun P (⟨_, c, e⟩ : ∃ δ, C (q δ) ∧ δ.1.1.charpoly = P) ↦ e ▸
    exists_global_root (by simp [← IsGalois.card_aut_eq_finrank]) hσ c.2 (hz c) (cq _)
  choose W u _ V using fun {ν} h ↦ W (q ν) ⟨_, h, rfl⟩ _ ((mul_left_comm ..).trans (mul_comm ..))
    (e ν) (by erw [← map_aeval_matrix]; simp [q]) |> fun w ↦ And.intro w (by simpa using w.1)
  choose! A B hA hB uB using fun {ν} h ↦ exists_and_exists_comm.1 ⟨existsUnique_isRootQuotient
    (isUnit_of_mapMatrix _ ((aeval_algHom_apply (Algebra.ofId ..).mapMatrix ..).subst (@u ν h))),
    existsUnique_isRootQuotient (W h).1⟩
  have cj {ν ν'} g h (H : g * ν = ν' * g) := (by simp [q, ← mul_inv_eq_of_eq_mul H, -mul_assoc] :
    q ν = q ν') |> fun c ↦
    And.intro (c ▸ h) (And.intro ((hA (c ▸ h)).2 _ (c ▸ isRootQuotient_conj H.symm
    (hA h).1)).symm (uB (c ▸ h) _ (c ▸ isRootQuotient_conj (SemiconjBy.map H e).symm (hB h))).symm)
  have cm {ν} h := (cj ν h rfl).2.imp (Commute.inv_left ∘ mul_eq_of_eq_mul_inv) mul_eq_of_eq_mul_inv
  have Z {ν δ} h (hν : SemiconjBy δ (ω ν) ν) := have v := hτ ν ▸ (hν.map e).symm
    (existsUnique_isRootQuotient (V h)).elim (fun _ r _ ↦ eq_inv_mul_of_mul_eq (uB h (e _ * _ * _)
    (((isRootQuotient_map _ (hA h).1).mul (isRootQuotient_conj v
      (isRootQuotient_map _ ((W h).2 _ (hB h))))).mul r)) ▸ r) |> fun r ↦ And.intro (fun y ↦
      m h _ _ (by simp [cq, -mul_assoc]) (isRootQuotient_conj (mul_inv_cancel_right _
    y) ((one_smul ..).substr r))) ((M _ δ).trans ((IsRootQuotient.twistedNorm_eq_mul (by simpa using
      ((hz h).2 _ (cq ν)).2) v r (V h)).trans (congrArg _ (by simpa using nc _ (_ * δ)))))
  choose hz' nA using fun {γ} h ↦ (Z h ((fj γ).substr (cm h).1)).imp_right
    (@ie _ (j γ) <| ·.trans (by simp [twistedNorm]))
  refine (H a).mul_eq_of_double_count (B := U 1) (fun _ : _ × U 1 ↦
    φ (_ * galoisGf σ _) * (ρ _ * s).trace ℂ _) (H' i) (fun y ↦ ((@B (j y.2))⁻¹ * baseChangeGf y.1,
    (@A (j y.2))⁻¹)) (C <| q <| j ·.2) (fun x h ↦ fx 1 (by simp [fj]) (baseChangeGf x.1) (.inl ⟨_,
    left_ne_zero_of_mul h, by simp [hj]⟩)) (fun x c y g ⟨hk, b⟩ ↦
    congrArg₂ _ (.trans (by simp [← b, ι, hτ, τ]) ((h.1 _ hk _).trans ((hz' c ((@B (j
    x.2))⁻¹ * baseChangeGf x.1)).1 _ (by simp [← hj, (cm c).2]) (.trans (by simp
    [ι]) (nA c ▸ nc ..))).symm)) (by simp [τ, ← b, ← w _ _ (nA c), ← hs, (ρ g⁻¹).trace_mul_comm,
    s.trace_mul_comm, ← ρ.map_mul g])) fun (x, δ) ↦ (fun o ↦ ?_) ∘ left_ne_zero_of_mul
  let ν := twistedNorm ω (finrank E E') δ
  have v : δ * ω ν = ν * δ := ie (by
    simpa [ν, hτ, M, map_twistedNorm _ (congrFun rfl)] using congr(e δ * $(nc (e δ) δ)))
  have h := fx _ v x (.inr ⟨_, o, nc ..⟩)
  have l := @ie _ 1 (by simpa [inv_mul_eq_one] using left_eq_mul.1 (Z h v).2)
  choose k hk H using coh _ (((Z h v).1 _).2 _ (nc ..) o) (by simpa [l] using nc (_ * x) (@A ν * δ))
  obtain ⟨g, hg : ω _ = _⟩ := hasse_principle_coboundary hσ (@B ν * x * k) (by simp [H, e]) l
  obtain ⟨⟨y, -, ey⟩, γ, eγ⟩ := fσ (e g⁻¹ * @B ν * x * k) (by simp [← hτ, hg, H]),
    fτ (g⁻¹ * ν * g) (by simp [eq_inv_mul_of_mul_eq v, hg, ← (cm h).1.left_comm])
  use (y, γ), (g * j ·)⁻¹, (⟨fun a ⟨b, c⟩ ↦ (cj (g * j a)⁻¹ h (by simp [← c,
    eγ])).symm.imp_left (⟨by simpa [·, ey, hj] using inv_mem (mul_mem hk b), by simp [*, τ]⟩), by
    simp [ij.eq_iff], fun a ⟨⟨b, (c : _ * ω _ = δ)⟩, d⟩ ↦ have N : a⁻¹ * j ·.2 = ν * a⁻¹ := ie (by
    simp [ν, ← c, hτ, nc, M, nA d, -mul_assoc, -map_inv, e.map_inv a])
    (fτ (a * g)⁻¹ (by simp [hg, ← c, cj _ d N])).imp fun _ ha ↦ ⟨⟨by simpa [cj _ d N, ey, ← hj, ha]
      using (inv_mem (mul_mem b hk)), ij (by simp [ha, eγ, ← N])⟩, by simp [ha]⟩⟩)

/-- Weak base change: Z is finite and, for u above w ∉ Z ∪ Z̄, sphericity passes from f to f' at
`IsStepUnramifiedAt` places, and Hecke polynomials at split `IsMatched` places. -/
def IsWeakBaseChange [Fintype n] μ {M M'} Z (f : Gf E n → M → ℂ) (f' : Gf E' n → M' → ℂ) :=
  Set.Finite Z ∧ ∀ w ∉ Z.conjClosure, ∀ u, .below E u = w → (IsStepUnramifiedAt E' μ w →
  f ∈ sphericalAt (rightRegular ℂ ..) w → f' ∈ sphericalAt (rightRegular ℂ ..)
  u) ∧ (IsMatched E' μ w → ∀ hw P, HasHeckePolyAt f w hw P → ∃ hu, HasHeckePolyAt f' u hu P)

/-- Matching local data above a finite set Z: retracts G, G' of the adelic groups, compatible
levels L, L', and bi-invariant functions F_j, F'_j that form pairs for j ∈ P at a level
where σ-cocycles split. -/
def IsLocalMatching μ Z {G G' J} [Group G] [Group G'] a a' L L' P (F : J → G → ℂ) (F' : J → G' →
  ℂ) := ∃ σ ≠ (1 : Gal(E''/E₁)), ∃ r r', ((∀ j, IsBiInvariant L (F j) ∧ IsBiInvariant L' (F' j)) ∧
  IsLocalRetraction a r Z ∧ IsLocalRetraction a' r' (placesAbove _ Z) ∧ Z.Finite ∧ ∀ k, r' (galoisGf
  σ k) ∈ L' ↔ r' k ∈ L') ∧ let M := L'.comap r'; M.comap baseChangeGf = L.comap r ∧ M.IsOpen ∧
    ∃ K ∈ Set.Icc M (localLevel n' (placesAbove _ Z)), CocyclesSplit (finrank E₁ E'') (idem
    (placesAbove _ Z)) K (galoisGf σ) ∧ P ⊆ {j | IsMatchingPairAbove σ μ Z K (F j ∘ r) (F' j ∘ r')}

variable [hμ : IsStep (E := E) E' μ] {u : FinPlace E'} {hw : (u.below E).IsSplit} (hu : u.IsSplit)

/-- For a step (E'/E, μ), the constant functions 1 on trivial local groups are matching local
data (`IsLocalMatching`) above the empty set of places. -/
lemma isLocalMatching_empty : IsLocalMatching (G := Unit) μ ∅ 1 (1 :
  Unit →* Gf E' n') ⊤ ⊤ {()} 1 1 := hμ.exists_gal_ne_one.imp fun _ ↦
  (⟨·, 1, 1, by simp [IsLocalRetraction, Gf.trivialOn, placesAbove, IsBiInvariant, Set.toFinite,
  localLevel, CocyclesSplit, IsMatchingPair, IsNormRoot, IsRootQuotient, twistedNorm_map_eq_prod,
  isOpen_iff_eventually, show idem ∅ = (0 : 𝔸f E') by aesop]; rfl⟩)

/-- Base change along a step: given matching local data with commuting operators A_j, A'_j, P stable
under the A_{o(i)}, and A_{j₀} of nonzero trace on stable spaces through f of generalised
eigenvalues θ, some weak base change eigenform in the image of A'_{j₀} has eigenvalues θ.

Known result: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). -/
lemma exists_isWeakBaseChange_of_matching [Fintype n] {μ} [hμ : IsStep (E := E) E' μ] [StablyUnram
  E'] {κ} f {Z G G'} [Group G] [Group G'] {a : G →* _} {a' : G' →* _} {L L'} {ι J : Type} {P F F'}
  (hM : IsLocalMatching μ Z a a' L L' P F F') (o : ι → J) (θ : ι → ℂ) j₀ (h₀ : j₀ ∈ P)
  : let ρ := ((stdSpace ..).formTranslation κ).comp a; let ρ' :=
      ((stdSpace E' n).formTranslation κ.baseChange).comp a'
    let A j := heckeFun ρ L (F j); let A' j := heckeFun ρ' L' (F' j); let V := levelSpace ρ L
        let V' := levelSpace ρ' L'; (∀ i j, (∀ x ∈ V, A i (A j x) = A j (A i x)) ∧ ∀ x ∈ V',
          A' i (A' j x) = A' j (A' i x)) → (∀ i, ∀ j ∈ P, ∃ k ∈ P, (∀ x ∈ V, A (o i) (A j x) =
          A k x) ∧ ∀ x ∈ V', A' (o i) (A' j x) = A' k x) → (∀ W : Subrepresentation ρ,
          f ∈ W → let U := (V ⊓ ⨅ i, (A (o i)).maxGenEigenspace (θ i)) ⊓ W.1; Module.Finite ℂ U →
            ∀ h, ((A j₀).restrict h).trace ℂ U ≠ 0) → ∃ g H, IsEigenform g.1 H ∧
          IsWeakBaseChange μ Z f.1 g.1 ∧ g ∈ V' ∧ g ∈ V'.map (A' j₀) ∧ ∀ i, A' (o i) g = θ i • g :=
  hM.elim fun σ ⟨hσ, r, r', ⟨hF, ha, ha', hZ, _⟩, hL, O, K, ⟨MK, KZ⟩, coh, Q⟩ c M pos ↦ by
  choose m mK l n₄ un using exists_baseChange_level hσ f.2.1
  let B w := w ∉ Z.conjClosure ∧ ∀ u ∈ placesAbove _ {w}, m u = Kw ..
  let X := {w | B w ∧ w.IsSplit ∧ IsMatched E' μ w}
  let N := localLevel n (placesAbove _ Z)ᶜ m
  let 𝓛 := L'.comap r' ⊓ N
  have kK : K ⊓ N ≤ _ := fun g h ↦ mem_Kf_iff.2 fun u ↦ by_cases (KZ h.1 u) (mK u <| h.2 u ·)
  obtain ⟨LK, oM⟩ := inf_le_inf_right N MK, ha'.2.2 ▸ L'.ker_le_comap r'
  let X' := {u // u.IsSplit ∧ u ∉ placesAbove _ Z ∧ maxCompactAt n u ≤ 𝓛}
  have kv {w S} (h : B w) (s : S ⊆ placesAbove E' {w} := by simp [placesAbove]) :
    Kf .. ⊓ Gf.supportedOn n S ≤ 𝓛 := fun g k ↦ .imp (oM ·) mem_localLevel.2 (by
    clear * - h k s; simp_all; grind [mem_Kf_iff, placesAbove, star_star, one_mem, below_star])
  let j u (e : _ ∈ X) : X' := ⟨u, ne_of_apply_ne _ ((below_star u).trans_ne e.2.1), e.1.1, kv e.1⟩
  choose Y y oX eZ _ eL using exists_remaining_places (S := Z) (T := X) (by grind) (·.2.1.2)
  choose n₀ _ n₂ _ using l _ N (by rw [eZ])
  have oL : 𝓛.IsOpen := O.inter n₀
  obtain ⟨oZ, _, _, T, -, hT⟩ := (Gf.supportedOn_le_trivialOn (S :=
    placesAbove _ Z) (by simp)).trans (eL ▸ trivialOn_le_localLevel), (stdSpace
    ..).finite_formTranslation_levelSpace κ (K := 𝓛.comap _) (continuous_baseChangeGf.1 _ oL),
    (stdSpace ..).finite_formTranslation_levelSpace κ.baseChange oL, exists_inf_trivialOn_le oL
  choose e₁ w st cm R r₀ r₁ r₂ r₃ using exists_commuting_hecke_family a r (𝓛.comap _) (fun _ h ↦
    baseChangeGf_mem_Kf.1 (kK (LK h))) (hF · |>.1) (·.2.2.1) (fun x : X ↦
    ⟨x.2.1.1, fun _ h ↦ kv x.2.1 .rfl (h.imp baseChangeGf_mem_Kf.2 baseChangeGf_mem_supportedOn)⟩)
    ha congr($hL ⊓ $((congrArg _ eL).trans (Subgroup.comap_inf ..))) (oZ <|
    baseChangeGf_mem_supportedOn <| ha.1 ·) (c · · |>.1)
  choose e₂ _ _ cm' R' u₀ u₁ u₂ u₃ using exists_commuting_hecke_family _ _ 𝓛 (LK.trans kK)
    (hF · |>.2) (X := X') (·.2.1) (by simp [X']) ha' (eL ▸ rfl) (oZ <| ha'.1 ·) (c · · |>.2)
  choose z z₀ t₀ htw tw tr using
    twisted_trace_identity hσ κ kK LK oL (by ext; simp [*]) fun s h e ↦ by
    obtain ⟨⟨t, a, c, H⟩, r, b, d, I⟩ := coh s h.1 e, n₂ s h.2 e
    simp [eZ, ↓← idem_compl, ↓idem_smul_eq_iff_mem_trivialOn, mul_assoc, inv_mul_eq_one] at c d H I
    use t * r, mul_mem ⟨a, trivialOn_le_localLevel (by simpa)⟩ ⟨MK (oM (by simpa)), b⟩
    ext1 w
    by_cases w ∈ placesAbove _ Z <;> simp [*, atPlace_galoisGf σ _ rfl, show w.comap σ ∈ placesAbove
      E' Z ↔ w ∈ placesAbove _ Z by simp [placesAbove]]
  choose D s₁ s₂ U hU s₃ using exists_hecke_stable_matching (n := n) (S := X) hσ fun _ ↦ .right
  choose Θ f' v t₁ t₂ t₅ t₃ t₄ using exists_eigenvector_of_trace_identity st rfl (.map o fun y : Σ'
    y : X × _, Σ' c, f ∈ End.eigenspace (heckeSplit _ y.1.2.2.1 y.2) c ↦ y.1) (.map o fun y ↦
    (j _ (hU _ ▸ y.1.1.2), y.1.2)) (.inl j₀) _ (Sum.elim θ _) cm cm'
    (by rw [e₁, iInf_sum, inf_inf_inf_comm]; exact (pos ⟨_ ⊓ _, fun k x h ↦
    ⟨(w k).1 _ h.1, (Submodule.mem_iInf _).2 (End.mapsTo_maxGenEigenspace_of_comm ((w k).2 _) _ <|
    (Submodule.mem_iInf _).1 h.2 ·)⟩⟩ ⟨fun g ↦ by simpa [Subtype.ext_iff] using! _root_.funext (n₄
    fun u _ ↦ by_cases (by simp +contextual [placesAbove, or_imp, atPlace_baseChangeGf,
    Gf.mem_trivialOn.1 g.2.1, Gf.atPlace_star_eq_one_iff.1]) (g.2.2.2 u)), (Submodule.mem_iInf
    _).2 (End.eigenspace_le_maxGenEigenspace ·.2.2)⟩ (Submodule.finiteDimensional_of_le
    (e₁.trans_ge fun _ ↦ .imp (·.1) (·.1))))) z₀ {t | ∃ᵉ (k ∈ P) (x ∈ D), R k t.1 x.1 ∧
    R' k t.2 x.2} ⟨_, h₀, _, s₁, r₀ _, u₀ _⟩ (by rintro _ ⟨k, p, x, i, e, d⟩; exact ⟨tr _ _
    (by convert (Q p).mul ((s₂ x i).mul (l Y _ rfl).2.2.2 ..) .. <;> simp [*, star_idem,
    idem_mul_self, Set.preimage, mul_sub, sub_mul]; rfl) _ _ (r₁ _ e) (u₁ _ d),
    Sum.forall.2 ⟨(M · k p |>.imp fun _ ⟨a, b, c⟩ ↦ ⟨a, x, i, r₂ _ e b, u₂ _ d c⟩), fun y ↦
    ⟨k, p, _, s₃ _ x i .., r₃ _ e _ fun _ h ↦ oX (baseChangeGf_mem_supportedOn (Gf.supportedOn_mono
    (by simp) h)), u₃ _ d _ (oX.trans' (by simp [Gf.supportedOn_mono, placesAbove, j, *]))⟩⟩⟩)
  have eig (x : X') := (hasHeckePolyAt_iff x.2.1).2 ⟨levelSpace_anti x.2.2.2 f'.2, _, rfl,
    (congr($(t₄ <| .inr ⟨x, ·⟩)))⟩
  choose! H hH using (Exists.intro _ <| eig ⟨·, ·⟩)
  use f', H, ⟨by simpa, .mp (tendsto_place_comap_cofinite _ hZ.cj.compl_mem_cofinite)
    ((T.eventually_all.2 (by simp [↓eventually_and])).mono fun u b a p ↦ ⟨_,
    hH u ⟨isSplit_of_q_prime p, a, (inf_le_inf_left _ (Gf.supportedOn_le_trivialOn b)).trans hT⟩⟩)⟩,
    ⟨hZ, ?_⟩, (e₂.le f'.2).1, ⟨_, (e₂.le
    v.2).1, t₅ ▸ rfl⟩, fun i ↦ congr($(t₄ _).1).trans congr($t₂ (.inl i) • _)
  rintro _ a u rfl; use fun b
    c ↦ by simpa [Subtype.ext_iff, -Gf.mem_supportedOn] using! levelSpace_anti (kv ⟨a,
    un _ b (by simpa [LE.le, funext_iff] using c)⟩) f'.2
  simp_rw [hasHeckePolyAt_iff (f := f)]; rintro b hw _ ⟨c, t, rfl, ht⟩
  let x : X := ⟨_, ⟨a, un _ (fun u e ↦ ⟨⟨_, notMem_inertia_of_comap_ne ((b.2 u e).2 σ hσ)⟩,
    fun _ _ ↦ (e ▸ b).1 _⟩) (by simpa [Subtype.ext_iff, funext_iff, LE.le] using! c)⟩, hw, b⟩
  let P u := ∀ e i, Θ (.inr (j u e, i)) = t i
  have h u (a : P u) : P (u.comap σ) := fun e i ↦ .trans (t₁ _ _ (let := σ.toAlgHom.toAlgebra
    by ext ψ : 2; exact (map_heckeSplit _ _ t₀ fun _ _ ↦
      htw ..).trans (heckeSplit_comp_baseChangeGf _ _ (fun y ↦ ⟨adeleMap ↑σ⁻¹ (singleAdele u y)
      _, by erw [← adeleMap_apply, adeleMap_adeleMap, σ.toRingEquiv.comp_symm]; simp⟩)
      (levelSpace_anti (kv e.1) (tw _ ψ.2)) fun k h ↦ by simp [Gf.eq_of_supportedOn h (one_mem _)
      fun v ⟨a, b⟩ ↦ b.elim (v.ext (Ideal.comap_injective_of_surjective _ (MulAction.surjective σ)
      congr($a.1)))]))) (a (below_comap σ u ▸ e) i)
  exact ⟨_, (b.2 u rfl).1 ▸ _root_.funext ((((bijective_pow_gal hσ).2.exists.1
    (FinPlace.exists_gal_comap_eq (hU x))).rec fun i ↦ (· ▸ i.1.rec (fun _ i ↦ congr($t₂
    (.inr ⟨(x, i), _, End.mem_eigenspace_iff.2 (ht _)⟩))) fun _ ↦ h _) : P u) x.2) ▸ eig _⟩

open Finset Valued

/-- For a step (E'/E, μ), u split, the only place above a split w, and μ_w trivial: the
indicators of the pro-p Iwahori double cosets of N(t) at w and t at u are matching local
data (`IsLocalMatching`), paired for t strictly dominant. -/
lemma isLocalMatching_proIwahori (h : ∀ u', .below E u' = u.below E ↔ u' = u) (hD : ∀ x,
  μ (locIdele (u.below E) x) = 1) : IsLocalMatching (n' := n') μ {u.below E} (embedAtSplit hw)
  (embedAtSplit hu) proIwahori proIwahori {t : dominantTorus | StrictMono (v <| t.1
  · |>.1)} (fun t ↦ (iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1) fun t ↦
  (iwahoriDoubleCoset t.1).indicator 1 := by
  let ε := Fintype.equivFin n'
  obtain ⟨Q, τ, hτ⟩ := isLocalRetraction_atSplit n' h hu hw, hμ.exists_gal_ne_one
  obtain ⟨hs, C, -, T⟩ := (h _).1 (below_comap τ u), exists_isTameAtLevel_intAdeleMap hτ
  obtain ⟨⟨c, _, hc⟩, hv, l⟩ := (T 0 (by simp) (by simp)).2.1,
    v_locMap_eq_of_surjective _ hs τ.surjective,
    (@Function.Semiconj.iterate_right (𝔸f E') _ (· u) _ _ (adeleMap_apply _ hs) · |>.eq)
  have hσ x := by simpa using
    (l ..).symm.trans congr($adeleMap_pow_finrank_eq_one (singleAdele u x) u)
  set ρ := (reindexGL ε).toMonoidHom.comp (Gf.atPlace u); have tw δ : ρ _ = (ρ δ).map (locMap _
    hs) := congr(reindexGL ε $(atPlace_galoisGf ..)); have tn := (map_twistedNorm _
    tw · · |>.symm); have cp g : (ρ g).1.charpoly = _ := (charpoly_reindex ..).trans
    (charpoly_map ..); refine have R := (by simp_all [IsLocalRetraction, ρ, ε, IsBiInvariant,
      isBiInvariant_doubleCoset, isOpen_proIwahori, map_mem_proIwahori_iff_of_isometry]); ⟨τ, hτ,
      (reindexGL ε).toMonoidHom.comp (Gf.atPlace _), ρ, R, SetLike.ext fun _ ↦
      .symm (map_mem_proIwahori_iff_of_isEquiv (isEquiv_comap_locMap _ _)).symm,
      isOpen_proIwahori.preimage (.comp (.units_map _ (by simp; fun_prop)) (by fun_prop)), _,
      ⟨le_rfl, fun _ h ↦ by simpa [Q, mem_intGL, reindex_equiv ε.symm, ρ] using h.1⟩, fun δ s e ↦
      (exists_coboundary_proIwahori hv (RingHom.ext hσ) (mem_Ô.1 c.2 _)
      (by simpa [l] using congr(evalAt u ($hc + 1))) s (by simp_all)).imp' (embedAtSplit hu)
      (by clear * - R tw; simp_all [← idem_compl, ↓idem_smul_eq_iff_mem_trivialOn,
      IsLocalRetraction, ← R.2.2.1.2.2, mul_assoc]),
      fun t ht ↦ ⟨by simp_all, fun | _, ⟨g, c, rfl⟩, _ => ((map_surjective (evalAt u) (⟨singleAdele
      u ·, by simp⟩)).exists.1 (proIwahori_doubleCoset_match hv (RingHom.ext hσ) hμ.out.pos
      (by fun_prop) (fun x e ↦ (adeleMap_galois_descent hτ (x := singleAdele u x)
      (by ext1 o; obtain rfl | _ := em (o = u) <;> simp [*, ← (h _).ne, adeleMap_apply])).imp' (· _)
      (by simp_all [← adeleMap_apply])) (isEquiv_comap_locMap _ rfl) (fun x b ↦ let n' : Ô E' :=
        ⟨singleAdele u _, by simpa +contextual [mem_Ô, ← and_forall_ne u] using b.le⟩
      have hm : ∀ o, reduceAt o n' = 0 := by simp +contextual [b, n', ← and_forall_ne u]
      have t := T n' (Subtype.ext (mem_range_finAdeleIncl_iff.1 ⟨singleAdele _ (x - 1), by
        simp +contextual [DFunLike.ext_iff, ← and_forall_ne u, n', h, adeleMap_apply]⟩ τ))
        (by tauto)
      (t.exists_norm (.inr isProfiniteRing_intAdeles) (x := 1 + n') (by simp [v.map_one_add_of_lt,
        ← reduceAt_eq_zero, hm]) (by simp [t.1]) (by simp)).elim fun z ⟨d, _, hb⟩ ↦ ⟨z.map
        ((evalAt u).domRestrict _).1, by simpa [hm, -map_sub] using map_dvd (reduceAt u) d, by
        simpa [l, n'] using congr(evalAt u $hb)⟩) ht
      (by simp_all [StrictMono, ← toNormedField.norm_lt_iff]) ?_ _ ⟨ρ g, c.imp (fun ⟨_, a, b⟩ ↦ ⟨_,
      Set.mem_of_indicator_ne_zero a, b ▸ rfl⟩) (.imp' ρ (by simp_all)), cp g⟩)).elim fun y ⟨Z, B⟩ ↦
      ⟨1 + idem {u} • (y - 1), (hμ.isNormRoot_of_one_side rfl (by simpa) (by simpa) (by simp_all)
      (by simp [h, twistedNorm_map_eq_prod,
      Polynomial.map_prod] at Z ⊢; convert Z; ext; simp [l])).imp_right fun H γ a b c ↦ (B _ (ρ a)
      (b ▸ cp _) (.trans (congrArg (reindexAlgEquiv (LocField u) _ ε) (by simp [H _ a c]))
      (aeval_algHom_apply (reindexAlgEquiv (LocField u) _ ε) ..).symm)).imp
      (fun B g i k ↦ by exact if_congr (B _ (i ▸ rfl) (by simp [*])) rfl rfl) (by simp_all)⟩⟩⟩
  ext1; simp; intro; erw [← adeleMap_apply, finAdeleIncl_adeleNorm, map_prod (evalAt _), prod_range,
    ← (bijective_pow_gal hτ).prod_comp]; simp [← adeleMap_gal_pow, l]

attribute [-simp] MonoidHom.coe_comp exists_const mem_levelSpace

/-- Base change along a step E'/E with compatible CM types, at a split w with μ_w = 1 and one
split place u above: if f has eigencharacter ξ at w, some eigenform f' over E' matches f off
w (`IsWeakBaseChange`) with eigencharacter ξ∘Nm at u.

Known result: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). -/
lemma exists_baseChange_isIwahoriEigen (h : ∀ u', .below E u' = u.below E ↔ u' = u)
    (hD : ∀ x, μ (locIdele (u.below E) x) = 1) {m} [Fintype m] [StablyUnram E'] {κ f θ}
    (H : IsIwahoriEigen (localFormRep (stdSpace E m) κ hw) (torusChar θ) f) : ∃ f' :
  (stdSpace ..).forms κ.baseChange, ∃ P, IsEigenform f'.1 P ∧
  IsWeakBaseChange μ {u.below E} f.1 f'.1 ∧ IsIwahoriEigen (localFormRep _ _ hu) (torusChar fun i ↦
  (θ i).comp (localNorm E u)) f' := have ⟨_, s, _⟩ :=
    exists_iwahoriHeckeHom_injective (localFormRep (stdSpace _ m) κ.baseChange hu) (v_uniformizer u)
  by refine have dN n (t : Fin n → _) : localNorm E u ∘ t ∈ dominantTorus ↔ t ∈ dominantTorus :=
      (by simp [dominantTorus, Monotone, ←
      toNormedField.norm_le_iff]); have M a t := (by constructor <;> intros <;> simp only [*,
        SetLike.coe_mem, hecke_dominant_eq_iwahoriDegree_smul, map_smul, compactMean_mem_levelSpace,
        iwahori_operator_mul (ρ := localFormRep ..), smul_smul] <;> simp
        <;> ring_nf); (exists_isWeakBaseChange_of_matching f (isLocalMatching_proIwahori hu h hD)
        (·) (fun a ↦ iwahoriDegree a.1 * torusChar θ (localNorm E u ∘ a)) ⟨_, s.monotone⟩ s (by
        simp +contextual [M, mul_comm, -hecke_dominant_eq_iwahoriDegree_smul]) (fun a t ht ↦ ⟨a *
        t, by simpa using! a.2.mul_strictMono ht (by simp [zero_lt_iff]) (by simp), M a t⟩) fun _ y
        _ ↦ trace_restrict_ne_zero (by simp [prod_ne_zero_iff]) (H.1 <| ·.le
        ⟨⟨H.2.1, by simpa using fun a h ↦ ⟨1, by simp [*, H.2, mul_smul]⟩⟩, y⟩) fun _ h ↦
        (Submodule.mem_iInf _).1 h.1.2 _).imp fun _ ⟨_, e, o, k, _, L⟩ ↦
        ⟨_, e, o, ne_of_apply_ne _ e.1, k, by simpa [*, mul_smul, prod_eq_zero_iff, torusChar,
        Pi.monoidHomMulEquiv, MonoidHom.comp_apply, coe_normAbsChar_locField] using L⟩
