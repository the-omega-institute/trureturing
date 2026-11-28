/- GID: D5/S3/Zeros/GRH/New/Selmer/HeckeStableSubspaces
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/HeckeStableSubspaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.HeckeStableSubspaces. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/HeckeStableSubspaces.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.BaseLevel
import D5.S3.Zeros.GRH.New.Selmer.AptTuples
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! This file: the auxiliary pairs have apt labels; representations attached to eigenforms are
conjugate self-dual, and local conditions pass to the conjugate place; a Hecke-stable space of forms
has a Hecke-stable complement and is spanned by its isotypic vectors.

Also holds known results stated on this proof's data: Potentially crystalline representations,
Hodge–Tate weights, Weil–Deligne Frobenius (known result; see
Lib.PadicHodge.Crystalline.RegularityFrobenius).

Also holds known results stated on this proof's data: Galois representations attached to forms on
definite unitary groups (known result; see Lib.GaloisRep.Main.AvatarCompatibility). -/

open Finset Fint Fintype Matrix NumberField Polynomial Submodule LevelPlaces.LevelForm

variable {P} (D' : Data P) (ϑ' : D'.Twist) {D : Data P} (ϑ : D.Twist) {p : D.Pair} {j} (H :
  p.IsRankOne j) {r n} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {Z : Submodule ℂ O.FormV}

/-- For 1 ≤ j ≤ m every good family of labels is apt (`IsApt`) for the j-th auxiliary pair of a
twist. -/
lemma isApt_auxPair (j : D'.LiftIndex) {c} (h : c ∈ D'.goodTupleFamilies) :
  IsApt (D'.auxPair ϑ' j) c ϑ' := have h i := (mem_filter.1
    (mem_piFinset.1 (Finset.mem_map_equiv.1 h) i)).2; by refine ⟨rfl, by bound, ?_, ?_, ((h _).1 ·.2
    |>.1), (h · |>.2.elim fun w h ↦ ⟨⟨_, w⟩, w.2.2, .inl ⟨D'.card_rowIndex, h⟩⟩), fun i ↦ by
    erw [IsRoot.def, ← Units.mul_inv, scaleRoots_eval_mul]
    simp
    exact ((h _).1 _).2 _ (charName_pow_eq_one (k :=
      ResField _) (D'.omega_zpow_mul_pow_eq_one _ (isChosen_chosenPlace rfl _).2.1))⟩ <;>
    simp [D'.card_rowIndex, D'.r_odd, D'.t_odd, AuxPair.rankDiff]

/-- For a pair p = (ν, z) of rank one and a twist ϑ, the auxiliary pair of the lift of νϑ from
U(1) to U(2z), with every label equal to X − 1, is apt for ϑ (`IsApt`). -/
lemma isApt_rank_one : IsApt (p.lValueData H.1 ϑ).auxPair (fun _ ↦ X - 1) ϑ := by cases id H; refine
  ⟨rfl, ?_, ?_, ?_, by simp [IsLabel, ← C_1, Monic, -map_one, separable_X_sub_C.squarefree],
  (⟨⟨·, _⟩, (D.chosenEquiv _ 1).2.2, by simp⟩), by simp [MulEquiv.map_eq_one_iff, twistedLabel,
  ← C_1, *, -map_one, -map_pow, isChosen_chosenPlace
  rfl, by simpa using D.omega_zpow_ne_one j (by grind)]⟩ <;> grind [card_unique]

/-- For a pair p = (ν, z) satisfying `Data.Pair.IsRankOne` with z ≥ 2 and a twist ϑ, the lift Ξ_p
from U(1) to U(2z) lies in the image of the idempotent with all labels X − 1. -/
lemma trivialLift_mem_range_tupleProj_rank_one :
  (p.lValueData H.1 ϑ).trivialLift ∈ (tupleProj _ fun _ ↦ X - 1).range := by
  set Y := p.lValueData H.1 ϑ
  have K s Ξ := (Y.inner_trivialLift 1 (Y.auxPair.formAction s Ξ)).trans (.trans (by
    simp [← AuxPair.theta_mul_eq_theta_formAction _ _ (reduceFamily_liftResidue s)]; rfl)
    (Y.inner_trivialLift ..).symm)
  have (w : FinPlace D.E)
    (g : GL Unit (ResField w)) := congr($(labelChar_X_sub_C (faithfulChar (ResField w)) 1).evalGL
    g).trans ((ite_eq_left (by simp)).trans ((evalGL_detChar ..).trans
      (MulChar.one_apply_coe g.det)))
  use Y.trivialLift, ext_inner_right ℂ (by simp_all [↓IsApt.isSymmetric_tupleProj _ _,
    asAlgebraHom_eq_sum, tupleIdem, inner_sum, inner_smul_right, labelIdem,
    prod_ne_zero_iff, ↓(isApt_rank_one _ H).isLabel])

/-- If f is an eigenform in rank n for the system Q and r is attached to Q, then r is conjugate
self-dual on traces: tr r(cgc) = cyc(g)^{1−n} tr r(g⁻¹) for all g, with c complex
conjugation and cyc the cyclotomic character. -/
lemma isConjSelfDual_of_attached [ThePrime j] [PadicIso j] {M} {f : Gf D.E n → M → ℂ} {Q} {r :
  GalRep j _ n} (he : IsEigenform f Q) (hr : Attached Q r) : IsConjSelfDual (Fintype.card n) r :=
  ⟨hr.1, hr.2.1, fun g ↦ by
  cases' e : Fintype.card n with k; simp_all [card_eq_zero_iff]
  have := tendsto_nhds_unique ((hr.tendsto_charpoly_coeff g 0).mul (have o :=
      (Homeomorph.mk ⟨_, _, conjGal_conjGal, conjGal_conjGal⟩).isOpenEmbedding; conjGal_conjGal g ▸
      Attached.tendsto_charpoly_coeff (P := (Q <| star ·)) ⟨hr.1, hr.2.1, o.isOpenMap, (hr.2.2.2
      · · |> mostFrobenii_push o star |>.mono fun y B x e ↦ B ⟨_, _, x, by simp [y.prime_q],
      y.isPlaceOver.conjPlace_star, by simpa [← e] using y.isFrob.conjPlace_conjGal⟩ (by simp) e _
      rfl)⟩ _ k)) (((hr.tendsto_charpoly_coeff g 1).mul (tendsto_mostFrobeniiAt
    (cycInv j _ _ · ^ k))).congr' (Filter.mem_inf_of_left (eventually_mostFrobenii (he.2.and
    (.and (eventually_notMem_star_notMem j ∅) (star_injective.tendsto_cofinite he.2))) fun y a ↦ by
    obtain ⟨⟨a, c, s, x⟩, _, d, u, z⟩ := a.1 y.prime_q, a.2.2 (by simp [y.prime_q])
    have := (heckeSplit_dual a · · c (v_uniformizer _))
    simp [smul_left_inj, smul_smul, he.1, heckeGL_zero ((mem_sphericalAt_iff _).1 d) ▸ this 0,
      cycInv_eq_of_isFrob y, Nat.choose, *] at *
    grind)))
  cases k.even_or_odd <;> simp_all [trace_eq_neg_charpoly_nextCoeff, nextCoeff,
    field, coeff_zero_eq_eval_zero, by simpa using (r g⁻¹).1.charpoly_inv]⟩

attribute [local simp] Units.ext_iff Units.smul_def cycInv in
/-- Let R satisfy `IsConjSelfDual` for j and `IsFiniteTypeAt` at the conjugate of A. Then it
satisfies `IsFiniteTypeAt` at A, the jumps of weight κ and rank j pass to A, and a polynomial
killing inertial s at the conjugate kills (s⁻¹)^c at A. -/
lemma local_clauses_of_conjPlace {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {R : GalRep ℓ D.E r} {A :
  ClosurePlace} (hd : IsConjSelfDual j R) (hf : IsFiniteTypeAt R (conjPlace A)) : IsFiniteTypeAt R A
  ∧ (∀ κ, HasJumpsAt R (conjPlace A) (jumps κ j) → HasJumpsAt R A (jumps κ j)) ∧ ∀ s ∈ inertiaGroup
  _ (conjPlace A), ∀ Q, PolyKillsAt R (conjPlace A) s Q → PolyKillsAt R A (conjGal s⁻¹) Q := by
  let r' := twistByChar (cycCharIn _ Ω ℓ ^ j.pred)⁻¹ (.mk' (transposeGL <| R ·⁻¹) (by simp))
  choose P h using (.twist (fun x hx h ↦ transpose_injective (hd.2 _ (span_mono (by simp [-map_inv])
    (apply_mem_span_image_of_mem_span (transposeLinearEquiv ..).1 hx))
    (by simpa [← trace_transpose_mul x] using h ·⁻¹))) _ :
    IsTraceNondeg r').exists_conj_of_trace_eq _ (.id ..)
    (hd.2.comp conjGal ⟨fun _ _ _ ↦ ⟨_, conjGal_conjGal _⟩⟩).hasSemiprimeSpan (by simp [hd.3])
  choose a b d using local_clauses_of_retract cmConj starRingAut.toRingHom (by simp)
    (by simp [conjGal]) (Homeomorph.mk
    ⟨_, _, conjGal_conjGal, conjGal_conjGal⟩).isOpenEmbedding Filter.univ_mem (fun g _ ↦ h g) P.4
  choose z q t using fun [H : PadicPlaceEmbedding D.E (conjPlace A) ℓ] ↦
    (fun e ↦ And.intro (jump_eq_of_pairing (σ := decompRep r' _) hf.2 (dotProductEquiv ..) (-j.pred)
    e (γ := ·) (u := ·)) (hf.2.of_pairing le_rfl _ _ e)) (by simp [r', H.cyclotomicGp_eq_cycChar,
    mulVec_transpose, ← dotProduct_mulVec, @Algebra.smul_def ℤ_[ℓ]])
  refine ⟨a ⟨(hf.1 · |>.mono fun s b h ↦ by simp [b h, cycChar_of_mem_inertiaGroup ℓ h ‹_›]), @q⟩,
    fun κ h ↦ b P.3 fun H γ τ hτ u ↦ ?_, fun s hs Q h ↦ d _ ⟨⟩ ⟨fun l ↦ ?_, @fun H _ n w ↦ ?_⟩⟩
  erw [@z H, ← h hτ]
  simp [jumps, Multiset.count_map, conjPlace]
  erw [← IsCMField.isConj_complexConj]
  clear * -; congr! 2
  grind [Φ_eq_or, InfinitePlace.mk_conjugate_eq, Multiset.mem_range]
  simpa [cycChar_of_mem_inertiaGroup ℓ hs l, aeval_eq_sum_range,
    transpose_sum] using congr($(h.1 l)ᵀ)
  cases (ℓ.pow_right_inj Fact.out).1 (w.eq_pow_of_isFrob (H.isWeilPair_zero_iff.2 (inv_mem hs)))
  apply @t H _ _ w.inv (@h.2 H _ _ w.inv)

lemma orthogonal_mem_invtSubmodule_hecke (hT : ∀ w hw hS X,
  Z ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule) w hw hS X :
  Zᗮ ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule := fun y m _ a ↦ inner_eq_zero_symm.1
  ((innerAt_heckePolyOnForms ..).trans (inner_eq_zero_symm.1 (m _ (hT _ _ (by aesop) _ a))))

/-- A space Z of forms stable under all Hecke polynomials off the level lies in N if its nonzero
isotypic vectors do. -/
lemma le_of_isotypic_mem {N : Submodule ℂ O.FormV} (hT : ∀ w hw hS X,
  Z ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule) (h : ∀ᵉ (x : Isotypic ..) (v ∈ Z),
  v.toSmoothForm ∈ x.1 ∧ v.toSmoothForm ≠ 0 → v ∈ N) : Z ≤ N := (gciMapComap (f := toSmoothForm)
  Subtype.val_injective).l_le_l_iff.1 (.trans (le_span_isSphericalOff _ (S := .image O.placeAt ⊤)
  (by simp [LE.le]; intros; use algFormRep_eq_self_of_mem _ (inf_trivialOn_le_levelOf (by aesop)))
  fun w h _ _ i _ ⟨y, m, e⟩ ↦ e ▸ heckeSplit_mem_of_heckePolyOp ((Submodule.map ..).comap
  (.applyₗ _)) (⟨_, hT w h (by aesop) · m, rfl⟩) i) (span_le.2 fun _ ⟨⟨v, _⟩, _, k⟩ ↦
  ⟨v, (exists_isotypic_of_isSphericalOff k).rec (by aesop)⟩))
