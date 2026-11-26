/- GID: D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Lift/Staircase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Lift.Staircase. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Lift/Staircase.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Edge
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.LevelModulus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors. Only one
direction is proved, namely that harmonic highest vectors, such as products of leading minors, have
matrix coefficients that extend holomorphically with an explicit weight. No decomposition theorem is
proved. Source: M. Kashiwara, M. Vergne, On the Segal–Shale–Weil representations and harmonic
polynomials, Invent. Math. 44 (1978) 1–48, III 6.3, 7.2; Davidson 1987, Prop. 2.2, Thm 2.9.

Part of: Joint harmonics and global theta lifts between discrete series types (known result; see
Lib.Weil.Lift.Edge).

This file: Holomorphic Fock vectors and kernels; automorphic functions of a level, basic API.
Dictionary between residue-matrix functions, moduli and named Weil data; finite Fourier expansion. A
rapidly decreasing function of a level times a theta kernel keeps both properties. Products of
minors are joint harmonic highest vectors for (U(p,q), U(n)), Kashiwara–Vergne. -/

open Ideal Int Finset Function MeasureTheory Modulus NumberField FockDualPair Space

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ}
  [Fintype n'] (s' : n' → _) {o : n → ℤ} {u : NumberField.InfinitePlace E → n → ℤ} {V : Space E n s}
  {γ e : InfinitePlace E → ℤ} {a : 𝓞 E} {F : G E s → ℂ} {ι : Type _} {_ : Fintype ι} {f c : ι → _}
  (o' : n → ℤ) (u' : NumberField.InfinitePlace E → n → ℤ) (F' : G E s → ℂ) (V' : Space E n s)
  (a' : 𝓞 E)

/-- The additive character y ↦ ψ(tr(yu)) of matrices modulo 𝔪 attached to the matrix u, with ψ
the chosen primitive additive character of O_E/𝔪. -/
noncomputable def traceChar [WeilData E] {𝔪 : Modulus E} (u : Matrix n _ 𝔪.ResRing) (y :
  Matrix n' n 𝔪.ResRing) := 𝔪.primAddChar (y * u).trace

section

variable {E n n' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {s : n → ℤˣ}
  [Fintype n'] (s' : n' → _) {o : n → ℤ} {u : NumberField.InfinitePlace E → n → ℤ}
  {γ e : InfinitePlace E → ℤ} (o' : n → ℤ) (u' : NumberField.InfinitePlace E → n → ℤ)
  (F' : G E s → ℂ)

variable (s o u γ e) in
/-- The subspace of Fock vectors v such that x ↦ ℓ(Ω(x,1)v)
(Ω = `realPairWeil` γ e) is holomorphic of weight u for the
order o, for every bounded linear functional ℓ. -/
def holomorphicData : Set (PairFock E s s') := {v | ∀ ℓ : _ →L[ℂ] ℂ,
  IsHolOfWeight s o u (ℓ <| realPairWeil γ e ⟨·, 1⟩ v)}

/-- For every adelic g, the function h ↦ F(g·(h,1)) on the archimedean group is holomorphic of
weight u for the order o (`IsHolOfWeight`). -/
def IsAdelicHol := ∀ g, IsHolOfWeight s o' u' (F' <| g * ⟨·, 1⟩)

end

/-- The space of automorphic functions of rapid decay for V that are right invariant under the
principal level K(a). -/
noncomputable def rapidOfLevel := V'.rapidFunctions.1 ⊓ Representation.invariants
  ((finRightRep ..).comp (principalLevel n a').subtype)

/-- Known result: Harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors. -/
lemma prod_mem_holomorphicData (ho : IsPosFirstOrder s o) {P l' ν : _ → _} {l : _ → HCParam s} (hl :
  ∀ w a b, s a = s b → o a < o b → l w a < l w b) (h : ∀ w, (std (R := n') 1 s (γ w)
  (-e w)).IsJointHighest (l' w) (-l w) (P w) (ν w) (u w)) {Q} (q : Q = ∏ w, (P w).rename (w, ·)) :
  Q ≠ 0 ∧ polyVector _ Q ∈ holomorphicData s 1 o u γ e := ⟨by simp_all [IsJointHighest,
  prod_eq_zero_iff, Prod.mk_right_injective], fun ℓ ↦ by simpa [q, realPairWeil, pairHomInf,
  realWeil_piTensor, ← piTensor.map_smul_univ, ← prod_inv_distrib, ← piTensor_polyVector] using!
  (HCParam.IsKHighest.isHolOfWeight_coeffMap ho.1 (h · |>.2.1.imp_right fun k a b ↦ by
  obtain ⟨⟨⟩, ⟨⟩⟩ := units_eq_one_or (s a), units_eq_one_or (s b) <;> simp_all [↓k, IsPosFirstOrder,
    lt_asymm, swap_oscRows_E, pairSign, raiseOp, lowerOp, IsHarmonic, IsJointHighest]; aesop)
  (fun _ ↦ oscillatorPair_detTwist.column_rep.derives.isCoeffMap 1) (ℓ.compContinuousMultilinearMap
  _) fun _ _ ↦ oscillatorPair_detTwist (γ := 0).column_rep.unitary_rep.1 _)⟩

/-- Let the linear map f to the Fock space intertwine the conjugate of the representation of
weight (κ, e′) of the definite second group with its Weil action. If f of the highest vector
is holomorphic of weight u, so is every f(ξ̄). -/
lemma mem_holomorphicData_of_highestVector {κ e' l ξ} (f : _ →ₗ[ℂ] _) (hl : ∀ w, (l w).Injective)
  (law : ∀ y ξ, realPairWeil γ e (1, y) (f (star ξ)) = f (star (conjWeylRep (n := n') κ e' y ξ)))
  (h : f (highestVector κ l) ∈ holomorphicData s 1 o u γ e) : f ξ ∈ holomorphicData s 1 o u γ e :=
  (Finsupp.mem_span_range_iff_exists_finsupp.1 (Not.imp_symm Submodule.exists_le_ker_of_notMem
  fun ⟨φ, a, k⟩ ↦ a (highestVector_cyclic hl e' φ (star ξ) (.inr (Submodule.span_le.1 k ⟨·,
  rfl⟩))))).elim fun c q ℓ ↦ by simpa [eq_star_of_eq_star q, Finsupp.sum, ← law, rep_apply_apply,
  star_highestVector] using (IsHolOfWeight.sum _ (h <| ℓ ∘L realPairWeil γ e ⟨1, ·⟩))

lemma isAdelicHol_pairTheta {s' : n' → _} [WeilData E] {S T a b φ ψ v f k} [AutChar.HasWeight a γ φ]
    (h : v ∈ holomorphicData s s' o u γ e) [AutChar.HasWeight b e ψ] :
  IsAdelicHol o u (pairTheta S T a b (integrated _ v f) ⟨·, k⟩) := (by
  simpa [← pairWeil_integrated S T a b, rep_apply_apply] using! h <|
    θ _ ∘L pairWeil _ _ a b ⟨·, k⟩ ∘L (integrated _).flip f)

open Matrix.Norms.L2Operator in
/-- For an element u of the archimedean group, the maximum over infinite places of the operator
norm of the matrix of u at that place. -/
noncomputable abbrev maxOpNorm {E n : Type} [Field E] [NumberField E] [Fintype n] {s : n → ℤˣ}
    (u : GInf E s) := ‖(u · |>.1.1)‖

lemma star_mem_rapidOfLevel (h : F ∈ rapidOfLevel V a) :
    star F ∈ rapidOfLevel V a := h.imp (.imp .conj (by simp [IsRapid])) (congr(star $(· ·)))

lemma mul_sum_mem_rapidOfLevel (h : ∀ i, F * f i ∈ rapidOfLevel V a) :
  F * (∑ i, c i * f i ·) ∈ rapidOfLevel V a := by
  simpa [Pi.mul_def, mul_sum, mul_left_comm, sum_fn] using Submodule.sum_smul_mem _ c fun i _ ↦ h i

lemma integral_mul_sum_const_mul (h : ∀ i, F * f i ∈ rapidOfLevel V a) : ∫ x, F x * ∑ i,
  c i * f i x ∂V.quotMeasure = ∑ i, c i * ∫ x, F x * f i x ∂V.quotMeasure := by
  simpa [mul_sum, mul_left_comm, ← integral_const_mul] using
              integral_finsetSum _ fun i _ ↦ ((h i).1.2.integrable (h i).1.1.1).const_mul _

section

variable {n n' E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  {w : ι → FinPlace E} (f : (∀ _, Matrix n' n _) → ℂ) [Fintype n] [Fintype n'] {x : n' × n → 𝔸f E}
  {y : n' × n → 𝔸f E} {𝔪 : Modulus E}

omit [IsCMField E] in
/-- If the entries of y and x differ by elements of absolute value less than 1 at each place w
i, then `residueDatum` w f takes the same value at y and at x. -/
lemma residueDatum_congr (h : ∀ i p, Valued.v ((y - x) p (w i)) < 1) : residueDatum w f y =
  residueDatum w f x := by
  dsimp [residueDatum, Matrix.map, vecToMat, residueOrZero]
  simp [← mem_LocInt, ← fun i p ↦ (add_mem_cancel_left (h i p).le : _ ↔ x p _ ∈ LocInt _)]
  congr! 7; exact residue_eq_iff_valuation_sub_lt_one.2 (h ..)

@[simp] lemma reductionK₀_map_modulusResidue 𝔪 {w} h (k : Kf E n) : (reductionK₀ 𝔪 k).1.map
  (modulusResidue _ h) = (Kf.reduceAt w k).1 := by ext; apply_rules [modulusResidue_reduction]

lemma liftFn_eq_residueDatum (hS : places 𝔪 = Set.range w) f :
  𝔪.liftFn ((f fun i ↦ .map · (modulusResidue _ (hS.ge ⟨i, rfl⟩))) ∘ @vecToMat n n' _) =
  residueDatum w f := by ext; simp_all [residueDatum, Modulus.liftFn, idem_mul_mem_Ô,
  @forall_comm ι, Matrix.map, vecToMat, reduceAt, ← residueOrZero_coe, RingHom.codRestrict]; congr

lemma exists_modulus_places_eq (hw : ∀ i j, star (w i) ≠ w j) : ∃ 𝔪, places 𝔪 = Set.range w ∧
  univ.inf (w · |>.1) ≤ 𝔪.ideal := have h (u : FinPlace E) := u.2.inf_le'.trans
                                     (u.2.prod_le.symm.trans (prod_places_le_iff (u := w)))
  ⟨⟨_, mt (isPrime_bot.inf_le'.1 ·.le) (by simp [(w _).3]), by grind⟩, Set.ext h, le_rfl⟩

end

variable {n n' E : Type} [Field E] [CMType E] {ι : Type*} [Fintype ι] {w : ι → FinPlace E}
  (f : (∀ _, Matrix n' n _) → ℂ) [Fintype n] [Fintype n'] {x y : n' × n → 𝔸f E} {𝔪 : Modulus E}
      [WeilData E] {s : n → ℤˣ}
  {s' : n' → ℤˣ} (V : Space E n s) (V' : Space E n' s')

omit [WeilData E] in
lemma isSchwartzBruhat_residueDatum (hw : ∀ i j, star (w i) ≠ w j) :
  IsSchwartzBruhat (Set.range w) (residueDatum w f) := (exists_modulus_places_eq hw).rec fun _ ⟨h,
  _⟩ ↦ h ▸ liftFn_eq_residueDatum h f ▸ isSchwartzBruhat_liftFn ..

/-- With the Gaussian vacuum as real part, the datum `modDatum` of Ψ on Hom(V, V') is the name
(`Space.name`), at the places dividing 𝔪, of the lift of Ψ from matrices modulo 𝔪,
applied to the vacuum. -/
@[simp↓] lemma modDatum_vacVector Ψ : modDatum V V' 𝔪 Ψ vacVector =
  name _ 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMat)) (vacElem _) := by simp [modDatum, integrated_name]

/-- Let 𝔪 = (ḡ) and let x be a finite adelic vector of Hom(V,V') with gx integral. Then ϱ(αx) of
the vacuum is ∑_y χ(z_y)·`modDatum` of the indicator of y, over matrices y modulo 𝔪, for
some finite adeles z_y; χ = `stdLattice.psi₀`. -/
lemma exists_heis_vacElem_eq_sum_modDatum {g} (h : ideal 𝔪 = span {star g}) (hx : ∀ i,
  algebraMap E _ g * x i ∈ Ô E) : ∃ z : _ → _, (V.hom V').ϱ (finVec x) (vacElem _) = ∑ y,
  stdLattice.psi₀ E (z y) • modDatum V _ 𝔪 (Pi.single y 1) vacVector := by
  have k q y : 𝔪.reduction y = 0 → y * star (x q) ∈ Ô _ := by
    simp +contextual [𝔪.reduction_eq_zero_iff, h, mem_span_singleton, dvd_iff_exists_eq_mul_left,
      mul_assoc, mul_mem, by simpa using star_mem_Ô (hx q)]
  erw [← finHeisOp_vacElem (star_mem_Ô <|
    k · _ ((RingHom.sub_mem_ker_iff _).2 (𝔪.reduction_idem_mul 1))), _root_.smul_apply, map_smul,
    rho_finVec, (_ : x + _ = _), ← projOn_vacElem, ← name_char_eq_translate_projOn _ _ (⟨_, k · ⟨_,
    𝔪.generator_spec.1⟩ (by simp [generator_spec])⟩),
    ← modDatum_vacVector _ _ (𝔪.primAddChar <| matToVec · ⬝ᵥ _), modDatum_eq_sum]
  simp +singlePass [← (𝔪.reduction_surjective _).choose_spec]
  simp [smul_sum, smul_smul, stdLattice.semichar, ← AddChar.map_add_eq_mul]; tauto
  ext; simp [sub_mul]

variable {E n n' : Type}

lemma mul_modKernel_mem_rapidOfLevel [Field E] [CMType E] [Fintype n] [Fintype n'] [WeilData E]
  {s s'} {S : Space E n s} {T : Space E n' s'} {a b 𝔪 N F} (h𝔪 : 𝔪.ideal = .span {N}) {e ψ} [hb :
  AutChar.HasWeight b e ψ] (hF : F ∈ rapidOfLevel S N) Ψ Q h (hψ : ∀ w ∉ 𝔪.places,
  ψ w = 1 := by simp) : F * (modKernel S T a b 𝔪 Ψ Q · h) ∈ rapidOfLevel S N := by
  obtain ⟨⟨⟨⟩, q⟩, l⟩ := hF
  refine ⟨⟨⟨by fun_prop [modKernel], by grind [modKernel, pairTheta,
    (pairThetaKer ..).theta_rat_mul, Pi.mul_apply], ⟨_, isOpen_principalLevel (by simpa [*] using
    𝔪.2)⟩, (congrFun <| ?l ⟨·, ·⟩)⟩, mul_comm F _ ▸ q.mul ((pairThetaKer ..).isModerate ..)⟩, ?l⟩
  intro k; simp_all [funext_iff, modKernel_mul_Kf_left (k :=
    ⟨_, k.2.1⟩), ↓hb.apply_det_eq_charOfTamePart hψ, (𝔪.mem_principalLevel_iff h𝔪 _).1]

/-- The integer γ + n·[s_c = −1] − s_c ∑_{o(c)<j<n} k(s_c, j): the weight at the basis vector c
of a staircase with k(η, j) minors of size j and sign η. -/
def staircaseWeight n [Fintype n] {r} (s o : r → _) (k : _ → ℕ → ℕ) γ c :=
  (std (R := n) 1 s 0 γ).swap.vacuumWeight (s c) - s c * ∑ j ∈ Ioo (o c) (Fintype.card n), k (s c) j

attribute [local simp] Equiv.symm_apply_eq Fin.exists_iff sum_ite Injective ite_and pairSign

/-- Staircases: the product of k(η, p) copies of the p × p minor on the first p columns of sign
η and the first (η = 1) or last p rows is, if the sizes fit, nonzero, harmonic and highest
on both sides, of explicit weights. -/
lemma staircase_harmonic_highest {r n} [Fintype r] [Fintype n] {s γ γ' ν l l'} (hl : @Injective r ℤ
  (-l)) (hl' : @Injective n ℤ l') {o} (ho : ∀ c, o c = #{d | s d = s c ∧ s c * l c < s c * l d})
  (k : ℤˣ → ℕ → ℕ) (hk : ∀ η i, Fintype.card {c // s c = η} < i → i < Fintype.card n → k η i = 0)
  (fit : ∀ i j, Fintype.card n < i + j → k 1 i = 0 ∨ k (-1) j = 0) (hw : ∀ a, ν a =
  (std (R := n) 1 s γ γ').vacuumWeight 1 + ∑ η, η.1 * ∑ j ∈ Ioo (decrPosition (η.1 • l') a)
  (Fintype.card n), k η j) : let P := ∏ η, ∏ p : Fin (Fintype.card n), (Matrix.of fun i j : Fin p ↦
    ∑ a, ∑ c, ite (decrPosition (η.1 • l') a = i ∧ s c = η ∧ o c = ↑j) (.X (a, c)) 0).det ^ k η p
  (std 1 s γ γ').IsJointHighest l' (-l) P ν (staircaseWeight n s o k γ') := by
  choose u hu q using fun η : ℤˣ ↦ exists_equiv_decrPosition (l := η.1 • l') (by simpa)
  simp_rw [← neg_smul, ← Units.val_neg] at q
  simp at hl
  choose f h _ using fun η ↦ @exists_equiv_decrPosition {c // s c = η} _ (η * l ·) (by simp; grind)
  have {η c} : f η c = o c := by rw [← h, ho]; apply card_nbij (↑) <;> simp_intro _ <;> grind
  choose ρ κ hρ hκ using fun (t : Σ η p, Fin (k η (@Fin.val (Fintype.card n) p))) (i : Fin t.2.1) ↦
    (⟨(u t.1).symm ⟨i, by lia⟩, (f t.1).symm ⟨i, by grind [t.2.2.2]⟩, by
    simp [Subtype.coe_eq_iff]; grind⟩ : ∃ a c, (∀ b, a = b ↔ decrPosition (t.1.1 • l') b = i) ∧
    ∀ d, c = d ↔ s d = t.1 ∧ o d = i)
  obtain ⟨h1, h2⟩ := (hρ · · _ |>.1 rfl), (hκ · · _ |>.1 rfl)
  refine (⟨?_, by rintro ⟨η, _, ⟨⟩⟩ ⟨μ, _, ⟨⟩⟩; fin_cases η, μ <;> grind, by
    introv; simp [*, decrPosition] at h1 ⊢; grw [card_le_card, h1 t i] <;> grind, ?_⟩ :
    IsLayering _ _ _ ρ κ).joint_highest_prod_det ⟨?_, ?_, by introv; simp [*]; grw [card_le_card,
    ← ho (κ t i)] <;> grind, ?_⟩ (by
    simp_rw [← Fin.prod_const, ← Fintype.prod_sigma', ← hρ, ← hκ]; simp) <;>
    simp [*, -ho, card_filter, ↓Fintype.sum_sigma, -UnitsInt.univ, mul_sum,
    staircaseWeight, @sum_fin_eq_sum_range ℕ, apply_dite, show ∀ m N, Ioo m N =
    Finset.map (@Fin.valEmbedding N) {j | m < j} by simp [Finset.ext_iff]] <;> grind [vacuumWeight]
