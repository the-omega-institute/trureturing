/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Eigenspace/EigenQuotient
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Eigenspace/EigenQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Eigenspace.EigenQuotient. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Eigenspace/EigenQuotient.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Comparison.CrystallineLimit
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representation cut out of cohomology by a Hecke eigensystem; Eichler-Shimura
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Largest Hecke eigen-quotient of cohomology: existence, continuity, crystallinity, killed
Frobenius, weights. -/

open Polynomial TensorProduct Submodule Module LinearMap IsScalarTower nonZeroDivisors
  ModuleCat.Algebra DFinsupp
variable {ℓ Γ ι σ} [ThePrime ℓ] [Group Γ] [Fintype ι] {V : ι → ModuleCat ℚ_[ℓ]}
  [∀ i, Module.Finite ℚ_[ℓ] (V i)] (ρ : ∀ i, Representation ℚ_[ℓ] Γ (V i)) (T : ∀ i, σ → End ℚ_[ℓ]
  (V i)) (θ : σ → PadicAlgCl ℓ) {N} (r : Γ →* GL (Fin N) (PadicAlgCl ℓ))
  (F : ∀ i, V i →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ)

/-- The ℚ_ℓ-linear maps F_i : V_i → ℚ̄_ℓ^N span, turn T_s into the scalar θ_s, intertwine ρ_i
with r, and are universal among maps to ℚ̄_ℓ-spaces turning T_s into θ_s. -/
def IsEigenQuotient := (∀ i g x, matrixRep r g (F i x) = F i (ρ i g x)) ∧
  span (PadicAlgCl ℓ) (.range fun x : Σ
  i, V i ↦ F _ x.2) = ⊤ ∧ (∀ i s x, F i (T i s x) = θ s • F i x) ∧ ∀ M [AddCommGroup.{0} M] [Module
  (PadicAlgCl ℓ) M] [Module ℚ_[ℓ] M] [IsScalarTower ℚ_[ℓ] (PadicAlgCl ℓ) M] (f : ∀ _, _ →ₗ[ℚ_[ℓ]]
  M), (∀ i s x, f i (T i s x) = θ s • f i x) → ∃ φ : _ →ₗ[PadicAlgCl ℓ] _, ∀ i x, φ (F i x) = f i x

variable {ρ T}

/-- For finitely many continuous finite-dimensional ℚ_ℓ-representations V i of Γ with operators
T commuting with Γ, there are a continuous r: Γ → GL_N(ℚ̄_ℓ) and maps F from the V i forming
the largest θ-quotient (`IsEigenQuotient`). -/
lemma exists_isEigenQuotient [TopologicalSpace Γ] [IsTopologicalGroup Γ] (h : ∀ i s g, Commute
  (T i s) (ρ i g)) (hc : ∀ i x {N} (f : _ →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ), Continuous fun g ↦
  f (ρ i g x)) : ∃ N r F, IsEigenQuotient (N := N) ρ T θ r F ∧ Continuous r := by
  let G i := mk ℚ_[ℓ] (PadicAlgCl ℓ) (Π₀ i, V i) 1 ∘ₗ lsingle i
  let S := span (PadicAlgCl ℓ) {G i (T i s x) - θ s • G i x | (i) (s) (x)}
  let e := (finBasis (PadicAlgCl ℓ) (_ ⧸ S)).equivFun; have ⟨F, _, H⟩ : ∃ F, IsEigenQuotient (Γ :=
    Γ) 1 T θ 1 F := ⟨(↑(e.1 ∘ₗ S.mkQ) ∘ₗ G ·), by simp, (ker_mkQ _).symm.trans (ker_eq_top.2
    ((cancel_right e.surjective).1 (by ext; exact (ker_mkQ _).ge (subset_span (by tauto))))), by
    simp [← map_smul, ← Quotient.mk_smul, Submodule.Quotient.eq]; aesop, by intros; exact ⟨S.liftQ
    (liftBaseChange _ (lsum ℕ ‹_›)) (span_le.2 (by aesop_cat)) ∘ₗ e.symm, by simp [G]⟩⟩
  choose R hR using fun g ↦ H.2.2 _ (F · ∘ₗ ρ _ g) (by simp [← H.2.1, ← End.mul_apply, (h ..).eq])
  exact ⟨finrank (PadicAlgCl ℓ) (_ ⧸ S), (toMatrixAlgEquiv'.toMonoidHom.comp
    ⟨⟨R, ext_on_range H.1 (by simp_all)⟩, fun _ _ ↦
  ext_on_range H.1 (by simp_all)⟩).toHomUnits, F, ⟨by simp_all [toMatrixAlgEquiv'], H⟩,
  .of_coeHom_comp (continuous_pi fun _ ↦ span_le (p := (continuousSubmodule ..).comap (pi R)).2
  (Set.range_subset_iff.2 (hc _ ·.2 (F _) |>.congr (by simp_all))) (H.1.ge ⟨⟩)).matrix_transpose⟩

variable {θ r F} (h : IsEigenQuotient ρ T θ r F) {s : Finset ℕ} {m : ℕ → ℤ} {d : ℕ → ℕ} (t : ℕ →
  σ) [OverGp Γ ℓ] (hρ : ∀ i, IsCrystalline (ρ i))
include h hρ

omit [Fintype ι] [∀ i, Module.Finite ℚ_[ℓ] (V i)] in
lemma IsEigenQuotient.isCrystalline : IsCrystalline (matrixRep r) :=
  isAdmissible_of_one_tmul_mem_span (eq_top_iff'.1 h.2.1 · |> closure_induction
  (by simp) (by simp +contextual [tmul_add, add_mem]) fun c _ ⟨⟨i, x⟩, e⟩ ↦ e ▸ (hρ
  i).baseChange_mem_span_fixedPeriods (ρ' := matrixRep r) (f := c • F i) (by simp [← h.1]) (1 ⊗ₜ x))

omit [Fintype ι] [∀ i, Module.Finite ℚ_[ℓ] (V i)] in
lemma IsEigenQuotient.isKilledBy {f g} (hg : IsWeilPair (toGp g) f) (hφ : ∀ i y, ∑ k ∈ s,
  m k • baseChange _ ((T i (t k)).restrictScalars _) (linearFrob (ρ i) (g ^ d k) (d k * f) y) = 0) :
  IsKilledBy (matrixRep r) g f (∑ k ∈ s, C (m k * θ (t k)) * X ^ d k) := have P :=
    (h.isCrystalline hρ).isPotCrys; ⟨P, AlgebraTensorModule.ext fun
  a y ↦ eq_top_iff'.1 h.2.1 y |> closure_induction (by simp) (by intros; simp only [tmul_add,
    map_add, *]) fun c _ ⟨⟨i, x⟩, e⟩ ↦ let φ := (c • F i).restrictScalars _; e ▸ .trans (by
  erw [← φ.baseChange_tmul, eval₂_finsetSum]
  simp [C_mul_X_pow_eq_monomial, -map_mul, ← linearFrob_pow P hg, ← baseChange_linearFrob
    (hρ i).isPotCrys (hg.pow _) P φ (by simp [φ, ← h.1]), -baseChange_tmul]
  congr! 1; induction linearFrob (ρ i) _ _ _ <;> [simp [h.2.2, φ, smul_comm c];
    simp only [map_add, mul_add, *]]) congr(φ.baseChange _ $(hφ i _))⟩

/-- Let θ cut r out of crystalline ρ_i (toGp Γ open, the T_s commuting with each other and with Γ),
and η = γθ. If u is no jump of r at γ, some polynomial c with c(η) = 1 has c(T) killing the weight u
vectors (`HasHodgeTateWeight`) of each ℂ_ℓ ⊗ V_i. -/
lemma IsEigenQuotient.exists_word_kill_of_jump_eq_zero {γ : _ →ₐ[_] ℂ_[ℓ]} {u} {a : Gp ℓ} (ha : ∀ x,
  γ x = a x) (hc : ∀ i s g, Commute (T i s) (ρ i g)) (hc' : ∀ i s t, Commute (T i s) (T i t)) (e :
  jump (matrixRep r) γ u = 0) : ∃ c : List σ →₀ _, (c.sum fun L z ↦ z * (L.map (a ∘ θ)).prod) = 1 ∧
  ∀ i y, HasHodgeTateWeight (ρ i) u y
  → (c.sum fun L z ↦ z • ((L.map (T i)).prod.restrictScalars _).baseChange ℂ_[ℓ]) y = 0 := by
  let Φ v L : End _ (∀ i, hodgeTateMaps (ρ i) (toAlgHom ..) v) := piMap fun i ↦ hodgeTateMaps.pull
    (List.map (T i) L).prod (by simp_all [← End.mul_apply, (Commute.list_prod_left ..).eq])
  have := IsLocalization.isAlgebraic ℚ_[ℓ] ℤ_[ℓ]⁰
  refine (exists_words_comb_eq_zero (Φ u) (by aesop)
    (by intros; ext; exact congrArg _ congr($(hc' ..) _)) fun f
    hf ↦ let := γ.toModule; (@h.2.2.2 _ _ _ _ (of_algHom (γ.extendScalarsOfIsLocalization _ _⁰))
    (⟨f · |>.1.1, by simp [Algebra.smul_def]⟩) fun _ s _ ↦ by
    simpa [ha, RingHom.toModule_smul, Algebra.smul_def] using! congr(($(hf s) _).1 _)).elim fun φ
    hφ ↦ by ext; simp_all; exact hφ .. ▸ congr($(jump_eq_zero_iff.1 e ⟨_, φ.2⟩
              (mem_hodgeTateMaps_of_span h.2.1 (by simpa [↓h.1, ← hφ] using! (f _).2 ·.2))) _)).imp
    fun c ↦ .imp_right fun _ i y hy ↦ ?_
  have ⟨_, w, _, _, b, hb, _⟩ :=
    (hρ i).isPotCrys.exists_isHodgeTateFrame (finBasis ..) (toAlgHom ..)
  let Λ := liftBaseChange ℂ_[ℓ] (.restrictScalars ℤ_[ℓ] (S := ℚ_[ℓ])
    ⟨(b.constr ℕ b).flip.1, by simp⟩)
  refine (forall_dual_apply_eq_zero_iff ℂ_[ℓ] _).1 fun φ ↦ (show φ = Λ.flip ⟨(((liftBaseChangeEquiv
    _).symm φ).extendScalarsOfIsLocalization _⁰ ℚ_[ℓ]).1, by simp [Algebra.smul_def]⟩ by
    ext; simp [Λ]) ▸ congr($(b.ext (f₂ := 0) fun l ↦ ?_) _)
  let z := c.sum (fun L ↦ (· • Φ _ L)) (Pi.single i ⟨_, hb l⟩) i
  exact congr($(show Λ.flip _ ∘ₗ _ = Λ.flip z by ext; simp +zetaDelta [hodgeTateMaps.pull,
    Finsupp.sum]) y).trans (if e : w l = u then by aesop (erase simp finsupp_sum_apply) else
    have ⟨_, _, x, _⟩ := y.exists_sum_tmul_eq
    tate_eq_zero_of_chi_twist (e ∘ neg_inj.1) (nhds_one_le_map_nearOne Γ ((Filter.Eventually.all
      (z.2 <|
    x ·)).mono fun g _ ↦ by simpa [Λ, *, Finset.smul_sum, tensorAction] using congr(Λ $(hy g) z))))
