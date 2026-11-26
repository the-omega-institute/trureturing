/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/WeightCongruence/WeightCongruence
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/WeightCongruence/WeightCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.WeightCongruence.WeightCongruence. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/WeightCongruence/WeightCongruence.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.ClassReps
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.SplitPlaceCount
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Density of algebraic vectors, congruences to supercuspidal types, and limits of
eigensystems. For definite unitary groups, a form is an l-adic uniform limit of forms with very
different weight gaps at some embeddings and a prescribed character on the level, such as a wild
type. There is no completed cohomology here, and there are no congruences modulo powers of l.
Source: M. Emerton, V. Paškūnas, On the density of supercuspidal points of fixed regular weight, J.
Éc. polytech. Math. 7 (2020); J. Fintzen, S. W. Shin, Congruences of algebraic automorphic forms and
supercuspidal representations, Camb. J. Math. 9 (2021); Kaplansky, Proc. AMS 1 (1950).

Known result: Non-archimedean Stone–Weierstrass theorem for modules (localisation form). The form
here is for scalar-valued functions on a compact space over an ultrametric normed field. A
continuous function that agrees with some member of a subspace on each level set of the subspace's
multipliers lies in the closure of the subspace. Source: Dieudonné 1944; Kaplansky, The Weierstrass
theorem in fields with valuations (1950); module form as in Prolla, Approximation of Vector Valued
Functions (1977) and Topics in Functional Analysis over Valued Division Rings (1982).

This file: Ultrametric Stone-Weierstrass for modules; density of matrix coefficients of lacunary
weights. The l-adic model of an algebraic modular form: weight moved to l. Chebotarev uniqueness: a
Hecke system determines the trace of attached representations. A form is an l-adic uniform limit of
typed forms with free weights. -/

noncomputable section

attribute [-instance] Finite.of_subsingleton

open Module Finset IsUltrametricDist Matrix MvPolynomial Submodule Fintype ContinuousMap Classical
variable {X k : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [NormedField k]
  [IsUltrametricDist k]

attribute [local simp] hom_bind₁ RingHom.map_det Finsupp.weight_eq_sum Finsupp.degree_eq_sum
  closedBall_openAddSubgroup minor

/-- Ultrametric Stone–Weierstrass for a module (multipliers and patching): X compact; if for every
point a some element of N agrees with φ wherever all multipliers of N take their values at a, then φ
lies in the closure of N.

Known result: Non-archimedean Stone–Weierstrass theorem for modules (localisation form). -/
lemma stoneWeierstrass_ultrametric (N : Submodule k C(X, k)) φ (h : ∀ a, ∃ d ∈ N, ∀ x,
    (∀ u ∈ N / N, u x = u a) → φ x = d x) : ∀ ε > 0, ∃ g ∈ N, ‖φ - g‖ ≤ ε := by
  by_contra! ⟨ε, o, n⟩
  -- `B`: the ring of the multipliers of norm `≤ 1`
  let A := (N / N).toSubalgebra (by simp) fun x y a b z h ↦ mul_assoc x y z ▸ a _ (b _ h)
  let B := A.toSubring ⊓ {closedBall_openAddSubgroup _ one_pos, Submonoid.unitClosedBall _ with}
  have b (c : B) := mem_closedBall_zero_iff.1 c.2.2
  -- `m`: a maximal ideal of `B` that holds all `w` such that `w φ` is near `N`
  have ⟨m, _, I⟩ := Ideal.exists_le_maximal (comap (.toSpanSingleton B _ φ) (⟨N.1, (·.2.1 _)⟩ ⊔
    ⟨(closedBall_openAddSubgroup _ o).1.1, fun c _ ↦ by simpa using! norm_mul_le_of_le (b c)⟩)) (by
    simpa [Ideal.eq_top_iff_one, Submodule.mem_sup, ← eq_sub_iff_add_eq'] using n)
  -- compactness: some `f ∉ m` makes `g` small off the set `Z` where all `f ∉ m` have size one
  let P := m.primeCompl
  have : Nonempty P := ⟨1⟩
  let Z := {x | 1 ≤ fun f : P ↦ ‖f.1.1 x‖}
  have S g {r} (o : 0 < r) (H : ∀ x ∈ Z, ‖g x‖ ≤ r) : ∃ f : P, ‖f.1.1 * g‖ ≤ r := by
    simpa [norm_le, o.le] using isCompact_univ.elim_directed_cover _ (fun f : P ↦ (isOpen_closedBall
      0 o.ne').preimage (f * g).2) (fun x _ ↦ Set.mem_iUnion.2 (by_contra fun c ↦ c ⟨1, by
      simpa using H _ fun f ↦ not_lt.1 fun l ↦ c ((exists_pow_lt_of_lt_one (by positivity : 0 < r /
      (‖g x‖ + 1)) l).imp' (f ^ ·) fun _ h ↦ by simp; grw [h]; simp [field])⟩)) fun e f ↦ ⟨e * f, by
      refine ⟨mul_comm f e ▸ ?_, ?_⟩ <;> simp_intro x h <;> grw [norm_coe_le_norm, b] <;> simpa⟩
  choose d D h using h (epsilon Z)
  refine (S (φ - d) o fun x hx ↦ h x (fun u U ↦ ?_) |> (by simp [·, o.le])).elim fun e c ↦ e.2 (I
    (mem_sup.2 ⟨_, e.1.2.1 _ D, _, by simpa [mul_sub] using! c, add_sub_cancel ..⟩))
  -- on `Z`, `v` has a zero and is largest at `y`: `f v / v y` and `f` minus it lie in `m`
  let v := u - .const _ (u (epsilon Z))
  have ⟨y, Y, M⟩ := (isClosed_le (by fun_prop) (by fun_prop)).isCompact.exists_isMaxOn ⟨_, hx⟩
    (f := (‖v ·‖)) (by fun_prop)
  exact eq_of_norm_sub_le_zero ((M hx).trans (not_lt.1 fun p ↦ (S v p M).elim fun f c ↦
    (@epsilon_spec _ Z ⟨y, Y⟩ ⟨⟨(v y)⁻¹ • (f * v), A.smul_mem (mul_mem f.1.2.1 (sub_mem U
    (algebraMap_mem ..))) _, by simpa [norm_smul, field]⟩, fun c ↦ (Y ⟨_, f.2 ∘ (
    m.sub_mem_iff_left c).1⟩).not_gt (by simp [mul_comm, norm_pos_iff.1 p])⟩).not_gt (by aesop)))

/-- Let k ⊃ ℚ_l be algebraically closed and ultrametric, X compact, z: X → ∏_τ GL_N(k)
continuous with entries in one finite extension L of ℚ_l. Every continuous φ factoring
through z is a uniform limit of combinations of matrix coefficients of `weylRep` at z, for
weights with λ_{τ,j} + N − j free at each τ.

Known result: Density of algebraic vectors, congruences to supercuspidal types; limits of
eigensystems. -/
lemma mem_uniformClosure_weylRep_coeff {l N Φ} [Fact l.Prime] [Algebra ℚ_[l] k] [a : IsAlgClosed k]
    [Fintype Φ] (z : C(X, Φ → GL _ k)) (L : IntermediateField ℚ_[l] k) [Module.Finite ℚ_[l] L] (hL :
  ∀ γ τ i j, z γ τ i j ∈ L) {φ} (hφ : Continuous φ) (hi : φ.FactorsThrough z) :
  φ ∈ uniformClosure {ψ | ∃ κ e, ∃ β ξ : WeylIndex (Fin N) κ → k, (∀ τ, FreeInts fun j : Fin
  N ↦ -∑ h ∈ Ioo ↑j N, (κ τ h + 1)) ∧ ψ = fun γ ↦ β ⬝ᵥ weylRep κ e (z γ) *ᵥ ξ} := by
  have f (y : Fin N → ℕ) (l : ∀ i, ∀ j > i, y j < y i / (N + 1) ^ 2) : FreeInts (-y ·) := fun d o ↦
    StrictAntiOn.injOn (α := Lex _) (by
    rintro (α : _ →₀ ℕ) rfl (β : _ →₀ ℕ) (_ : _ = _) (⟨j, H⟩ : α.Lex _ _ β)
    have := sum_mono fun i ↦ show α i * y i + α i + ite (i = j) (y j + 1) 0 ≤ β i * y i + β i + α i
      * (y j / (N + 1) ^ 2) by
      grind [mt (Nat.mul_le_mul_left (α i) ∘ l j i), mul_le_mul_left H.2 (y j)]
    simp [← sum_mul] at *; grw [o, Nat.mul_div_le] at this; bound)
  have ⟨v, hv⟩ := @exists_linearIndependent_of_le_rank L k _ _ _ N (not_lt.1 fun h ↦ by
    obtain := rank_lt_aleph0_iff.1 (h.trans (by simp)), @Finite.trans ℚ_[l] L k
    grind [finrank_pos, Int.eq_zero_of_abs_lt_dvd ⟨_, by simpa [Algebra.norm_natCast] using
      congr((Algebra.norm ℚ_[l] $((a.exists_pow_nat_eq l
      (finrank ℚ_[l] k).succ_pos).choose_spec.symm)).valuation)⟩])
  let y (x : (Σ _ : Φ, Fin N) × ℕ) := ite (x.2 ≤ x.1.2) (v x.1.2) 0
  let κ (d : Φ → ℕ) τ h := (N + 1) ^ (4 * (N - h)) + ite (h = 1) (d τ) 0
  let E F : C(X, k) := ⟨fun γ ↦
    (rowSubst (z γ ·|>.1) F).eval y, by simp [rowSubst, eval₂_eq]; fun_prop⟩
  let w := ∏ τ, @tableauPoly _ _ k _ (N + 1) (κ 0 τ) (Sigma.mk τ) fun h _ ↦ Fin.castLE h.is_le
  refine mem_uniformClosure.2 fun ε o ↦ (stoneWeierstrass_ultrametric (span k {E F | (d) (F ∈ nabla
    k _ (diagramWeight _ (κ d)))}) ⟨φ, hφ⟩ (fun γ ↦ ⟨_, subset_span ⟨0, _,
    smul_mem _ (φ γ / w.eval y) (rowSubst_mem_nabla (z γ ·)⁻¹ (prod_tableauPoly_mem_nabla : w ∈ _)),
    rfl⟩, fun δ h ↦ fun t ↦ by simp +zetaDelta [t, hi t, rowSubst_rowSubst, tableauPoly,
    prod_eq_zero_iff, BlockTriangular, hv.ne_zero, det_of_isLowerTriangular] (funext fun τ ↦
    Units.ext (ext fun a b ↦ congr($(linearIndependent_iffₛ.1 hv (⟨_, hL δ τ a ·⟩)
    (⟨_, hL γ τ a ·⟩) (h (E (.X (⟨τ, a⟩, 0))) (mapsTo_span (f := .mulLeft ..) ?_) |> (by simpa [E,
    rowSubst] using! ·)) b).1)))⟩) ε o).imp' _ fun _ ↦ .imp (mapsTo_span (f :=
    coeFnLinearMap _) ?_ ·) (norm_le _ o.le).1 <;> rintro _ ⟨d, F, c, rfl⟩
  · use d + Pi.single τ 1, minor _ ![⟨τ, a⟩] * F, ?_, ext (by simp [E])
    convert SetLike.mul_mem_graded (minor_mem_nabla (Fin.forall_fin_one.2 rfl)) c; ext ⟨⟩
    simp [diagramWeight_apply, κ]; grind [a.2]
  exact (nabla_le_span_nablaBasis_mul_detPow _ (by simpa [diagramWeight, sum_range_succ] using
    c)).elim fun β h ↦ ⟨_, (κ d · N), β,
    (eval y <| nablaBasis k _ _ · * detPow k _ (κ d · N)), fun τ ↦ f _ fun i j h ↦ by
    grw [← single_le_sum (a := j.1), add_assoc, ← le_self_add, Nat.pow_div, ← mul_pow_sub_one,
      sum_le_card_nsmul, smul_eq_mul, mul_lt_mul_iff_left₀]
    any_goals grind [Nat.card_Ioo]
    simp +contextual (disch := grind) [κ, ite_eq_right, pow_lt_pow_right₀],
    funext (by simp [E, ← h, weylRep,
    mulVec, dotProduct, mul_sum, Units.smul_def, sum_mul, mul_assoc, linearCombination_apply])⟩

open RingHomClass IntermediateField Polynomial Filter Topology Metric Units
variable {E n : Type} [Field E] [CMType E] [Fintype n] {l} [Fact l.Prime] [PadicIso l] (κ κ' :
  Weight E)

/-- The homomorphism sending g to the family, over infinite places v, of its component at the
place induced by x ↦ ιΦ_v(x̄), read in GL_n(Q̄_l). -/
@[simps! -isSimp toFun] def padicComponents := (⟨.pi fun v ↦ (GeneralLinearGroup.map
  (exists_placeOfEmb_extension (weightEmbedding (toRingHom ιℓ) v)).choose).comp (Gf.atPlace _),
  continuous_pi fun _ ↦
  (continuous_adeleExtension _).generalLinearGroup_map.continuousOn.domRestrict⟩ : Gf E n →ₜ* _)

/-- The ι-semilinear map sending f to the l-adic function g ↦ M ρ_{κ'}(z(g))⁻¹ ι(f(g)), with z =
`padicComponents`, viewed as a function of g and a coordinate. -/
def padicModel M := (⟨⟨fun f x ↦ (M *ᵥ weylRep κ'.1 κ'.2 (padicComponents x.1)⁻¹ *ᵥ ιℓ ∘ f x.1)
  x.2, by aesop⟩, by simp [_root_.funext_iff, entrywise, Finset.mul_sum, mul_left_comm]⟩ :
  (Gf E n → _) →ₛₗ[toRingHom ιℓ] _ × WeylIndex n κ.1 → _)

lemma padicComponents_embFin γ x : ιℓ ∘ (stdSpace E n).weightRep κ.1 κ.2 γ x =
  weylRep _ κ.2 (padicComponents (stdEmbFin γ)) *ᵥ ιℓ ∘ x := by
  convert! map_weightRep ιℓ.toRingHom ..
  ext; simpa [padicComponents_toFun, Gf.atPlace] using! adeleExtension_algebraMap ..

lemma exists_padic_field_of_form_values {κ f} (hf : f ∈ (stdSpace E n).forms κ) : ∃ L :
  IntermediateField ℚ_[l] _, Module.Finite ℚ_[l] L ∧ ∀ g i, ιℓ (f g i) ∈ L := by
  have := IsLevel.mk inf_le_left (isOpen_Kf.inter hf.1)
  use adjoin _ ((⋃ v, .range (weightEmbedding (E := E) ιℓ v)) ∪ ⋃ c : StdClasses (Kf .. ⊓
    rightStab f), .range (ιℓ ∘ f c.out)), ?_, fun g i ↦ ?_
  rw [adjoin_union,
    adjoin_iUnion]; apply +allowSynthFailures IntermediateField.finiteDimensional_sup
  simp [finiteDimensional_adjoin, IsGalois.integral]
  obtain ⟨_, _, k, rfl⟩ := exists_eq_map_mul_rep_mul stdEmbFin (Kf .. ⊓ rightStab f) (·.out_eq) g
  rw [k.2.2, hf.2,
    stdSpace_weightRep_apply]; apply ((adjoin ..).toSubring.comap ιℓ.toRingHom).sum_mem fun _ _ ↦
    mul_mem (weylRep_entry_mem ..) _ <;> simp [mem_intGL, ← map_inv] <;> bound

variable {ℓ} [ThePrime ℓ] {E n : _} {H} [Field E] [EmbeddedNumberField E] [Fintype n] [Group H]
  [TopologicalSpace H] {P : FinPlace E → _} {j} {ρ : H →* GL n (PadicAlgCl ℓ)}

lemma norm_eq_one_of_continuous [CompactSpace H] {ψ : H →* (PadicAlgCl ℓ)ˣ} (h : Continuous ψ)
    g : ‖(ψ g).1‖ = 1 := have ⟨a, b⟩ := (continuous_val.comp h).norm.exists_forall_ge (by simp)
  by simpa [field, antisymm_iff] using max_le (b (a * g)) (b (a / g))

/-- For polynomials D, R over the algebraic closure of ℚ_ℓ with R monic, if all coefficients of
DR have absolute value at most η, then so do all coefficients of D. -/
lemma norm_coeff_le_of_mul_monic {D R : (PadicAlgCl ℓ)[X]} {η} (hR : R.Monic) (h :
  ∀ i, ‖(D * R).coeff i‖ ≤ η)
  i : ‖D.coeff i‖ ≤ η := by simpa [hR] using (mul_le_mul (le_supNorm ..) (R.le_supNorm
  R.natDegree) (by simp) D.supNorm_nonneg).trans (D.gaussNorm_mul (v := NormedField.toAbsoluteValue
  _) isNonarchimedean_norm one_pos R ▸ (supNorm_eq_iSup _).trans_le (ciSup_le h))

/-- If ρ is attached to the family of polynomials P_w, then for every x, ιP_w converges
coefficientwise to det(X − ρ(x)) along most Frobenii (w, A, s) with s tending to j(x). -/
lemma Attached.tendsto_charpoly_coeff [PadicIso ℓ] (h : Attached P ρ j) x i :
  Tendsto (ιℓ <| P ·.w |>.coeff i) (mostFrobeniiAt E (j x)) (𝓝 ((ρ x).1.charpoly.coeff i)) :=
  nhds_basis_closedBall.tendsto_right_iff.2 fun η
  p ↦ mem_inf_of_inter (h.2.2.2 η p) (Filter.map_comap_le
  (h.2.2.1.image_mem_nhds ((((MvPolynomial.continuous_eval _).comp (h.rec (by fun_prop))).congr fun
  x ↦ charpoly.univ_coeff_eval₂Hom n _ (ρ x).1.uncurry i).tendsto x (closedBall_mem_nhds _ p))))
  fun y ⟨b, z, u, v⟩ ↦ closedBall_eq_of_mem u ▸ by simpa [dist_eq_norm'] using! b _ v i

/-- Two representations of the same size attached to the same system P, of groups mapping to the
Galois group by j and j', have equal traces at x and y whenever j(x) = j'(y). -/
lemma Attached.trace_eq [PadicIso ℓ] {G} [Group G] [TopologicalSpace G] {j'} {σ : G →* GL n
    _} (h : Attached P ρ j) (h' : Attached P σ j') x {y} (e : j x = j' y) : (ρ x).1.trace =
  (σ y).1.trace := by simp [Polynomial.ext (tendsto_nhds_unique (h.tendsto_charpoly_coeff ..) <|
  e ▸ h'.tendsto_charpoly_coeff y ·), trace_eq_sum_roots_charpoly]

open NumberField IsCMField Kronecker Set RingHom
variable {E : Type} [Field E] [CMType E] {N} {l : _} [Fact l.Prime] [PadicIso l] (κ : _) (w :
  FinPlace E) (hw : _ ≠ w) (g : GL (Fin N) (LocField w))

/-- Says that the place of E induced by the l-adic embedding x ↦ ιΦ_v(x̄) is w or w̄. -/
def InducesPlacePair v := let u := placeOfEmb (weightEmbedding ιℓ.toRingHom v); u = star w ∨ u = w

lemma inducesPlacePair_mk σ (h : inducedPrime σ = w) : InducesPlacePair w (.mk σ) :=
  h ▸ .imp (by erw [placeOfEmb_comp_star, ·])
  (by erw [weightEmbedding, RingHom.comp_assoc, ← isConj_complexConj]; aesop) (Φ_eq_or σ)

lemma padicComponents_atSplit {τ} (h : ↑l ∈ w.1 → ¬InducesPlacePair w τ) :
  padicComponents (atSplit hw g) τ = 1 := by
  rw [padicComponents_toFun, atPlace_atSplit_of_ne] <;> aesop (add simp InducesPlacePair)

lemma InducesPlacePair.atPlace_eq_one {v g} (h : InducesPlacePair w v) (e :
  padicComponents (n := Fin N) g v = 1) : g.atPlace w = 1 :=
  have := (map_eq_one_iff _ (Units.map_injective (Matrix.map_injective (RingHom.injective _)))).1 e
  h.rec (Gf.atPlace_star_eq_one_iff.1 <| · ▸ this) (· ▸ this)

/-- For w split there are a ≠ 0 (−1 if w ∤ l) and a linear T not increasing sup norms with
TF = a·ι(P.coeff j)·F, F = `padicModel` κ κ' M f, whenever f has Hecke polynomial P at w and M
intertwines the weights on GL_N(E_w). -/
lemma exists_padicModel_hecke_contraction j : ∃ a ≠ 0, (↑l ∉ w.1 → a = -1) ∧ ∃ T :
  _ →ₗ[PadicAlgCl l] _ → _, (∀ φ r, (∀ z, ‖φ z‖ ≤ r) → ∀ z, ‖T φ z‖ ≤ r) ∧
  ∀ {κ' f} M P, let F := padicModel (n := Fin N) κ κ' M f
  HasHeckePolyAt f w hw P → (∀ g : GL (Fin N) _, let z := padicComponents (atSplit hw g)
    weylRep κ.1 κ.2 z * M * weylRep κ'.1 κ'.2 z⁻¹ = M) → T F = (a * ιℓ (P.coeff j)) • F :=
  let s U : Gf E (Fin N) := atSplit hw (transposeGL (basicCosetRep U))
  let Y := Option.elim' 1 fun (U, a, b) ↦ weylRep κ.1 κ.2 (padicComponents (s U)) a b
  have ⟨y, hT⟩ := Finite.exists_max (‖Y ·‖)
  have := (Units.norm_pos 1).trans_le (hT none)
  ⟨-(Y y)⁻¹, by aesop, by cases y <;> aesop (add simp [weylRep, padicComponents_atSplit]),
    (_ : ℤ) • -(Y y)⁻¹ • ∑ U ∈ _, .pi fun (g, i) ↦ ∑ b, Y (U, i, b) • .proj (g * s U, b),
    fun φ r H z ↦ (IsUltrametricDist.norm_zsmul_le ..).trans (by
    simp [field, ← sum_product', (exists_norm_finsetSum_le ..).elim
    fun _ ↦ (·.2.trans (norm_mul_le_of_le (hT _) (H _)))]), fun M P ⟨k, t, p, e⟩ hL ↦ by
    simp [p, _root_.funext_iff, mul_assoc, ← mul_sum, -Int.cast_ite, -mul_eq_mul_left_iff,
   ← by simpa [heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).1 k)] using
      (congr(padicModel _ _ M $(e (N - j)) ·))]
    congr!
    simpa [padicModel, ← mulVec_mulVec] using! congr($(hL _).mulVec ..)⟩

attribute [local fun_prop] Continuous.if_const

attribute [local simp] mulIndicator

/-- Let K ≤ K_0 be open, θ a smooth character of K, and let d ∈ K with z_τ(d) = 1 on T fix f,
θ(d) = 1. Then the l-adic model of f is a uniform limit from any span containing the
equivariant images of models of θ-eigenforms of weight free on T, κ elsewhere.

Known result: Density of algebraic vectors, congruences to supercuspidal types; limits of
eigensystems. -/
lemma padicModel_mem_uniformClosure {K} (hK : IsLevel (n := Fin N) K) {θ : K →* ℂ} (n : θ =ᶠ[nhds
    1] 1) (T : Set _) (f : (stdSpace E _).forms κ) (t : ∀ d, (∀ τ ∈ T, padicComponents d.1 τ = 1) →
  d.1 ∈ rightStab f.1 ∧ θ d = 1) {D} (hD : ∀ ν,
  ∀ φ ∈ levelSpace ((stdSpace ..).formTranslation ν) K θ, (∀ τ ∉ T, ν.1 τ = κ.1 τ ∧ ν.2 τ =
  κ.2 τ) → (∀ τ ∈ T, FreeInts fun j : Fin N ↦ -∑ h ∈ .Ioo ↑j N, (ν.1 τ h + 1)) → ∀ M, (∀ z : _ →
  GL (Fin N) (PadicAlgCl l), (∀ τ ∈ T, z τ = 1) → weylRep κ.1 κ.2 z * M * weylRep ν.1 ν.2 z⁻¹ = M) →
  padicModel κ ν M φ ∈ span (PadicAlgCl l) D) : padicModel κ κ 1 f.1 ∈ uniformClosure D := by
  have A := exists_transporter stdRatPoints Fact.out .rfl K
  let s c g := (A c g).choose
  let u c k := (ιℓ (θ k), ιℓ (θ k⁻¹) • ιℓ ∘ f.1 (c * k))
  have hu c : Continuous (u c) := (isLocallyConstant_of_eventually_mul ((n.and (IsOpen.mem_nhds
    (.preimage_val f.2.1) (by simp))).mono (by simp +contextual [u, ← mul_assoc]))).continuous
  let R c k := (u c k).1 • weylRep κ.1 κ.2 (Tᶜ.mulIndicator (padicComponents (c * k.1)⁻¹))
  let q {c g} (γ : s c g) : K := ⟨_, (((A ..).choose_spec.1 _).1 γ.2).2⟩
  let L c y := LinearMap.pi fun x : _ × _ ↦
    dotProductEquiv _ _ ((R c · x.2 y) ∘ q) ∘ₗ .funLeft _ _ (@q c x.1)
  let Φ c k := weylRep _ κ.2 (T.mulIndicator (padicComponents (c * k.1)⁻¹)) *ᵥ (u c k).2
  have a c g γ : R c (@q c g γ) *ᵥ Φ c (q γ) = (padicModel _ κ 1 f ⟨g, ·⟩) := by
    simp +contextual [Φ, R, u, q, padicModel, mul_assoc, (f.2.2 · g), padicComponents_embFin,
      ← (weylRep ..).map_mul, Pi.mul_def, Pi.inv_def, ((Group.isUnit _).map θ).ne_zero]
  convert sum_mem (t := .univ) fun (c : StdClasses K) _ ↦ (fun c ↦ Submodule.smul_mem _ (s c
    c).card.cast⁻¹ (sum_mem (t := .univ) fun y _ ↦ (?_ : L c y (Φ c · y) ∈ uniformClosure D))) c.out
  simp [L, s, ↓(A ..).choose_spec.2, dotProduct, sum_comm, ← mulVec_apply_eq_sum, *, -mem_classAut,
    -MonoidHom.coe_range, _root_.funext_iff, HasFiniteType.finite_aut, DoubleCoset.out_eq',
    Nat.card_pos.ne']
  have : Continuous fun k ↦ ((R c k · y), Φ c k y) := by dsimp [R, Φ, weylRep]; fun_prop
  have ⟨_, p, H⟩ := (isCompact_range this.fst).isBounded.exists_pos_norm_le
  refine mem_uniformClosure.2 fun ε o ↦ (mem_uniformClosure.1 (mem_uniformClosure_weylRep_coeff
    (.mk fun k (τ : T) ↦ padicComponents (c * k.1)⁻¹ τ) _ (fun _ τ _ _ ↦
    mem_of_le_of_mem (le_iSup _ τ) ((exists_placeOfEmb_extension _).choose_spec.2.2.1 _))
    this.snd (mul_left_surjective · |>.forall.2 fun d h ↦ by
    clear * - h t; simp_all +unfoldPartialApp [_root_.funext_iff, Φ, u, ← mul_assoc, (t ..).1 _]))
    _ (div_pos o p)).imp' _ fun _ ↦ .imp ((map_span_le ..).2 ?_ ⟨_, ·, rfl⟩) fun h x ↦
    congr(‖$(map_sub (L ..) ..) x‖).ge.trans (norm_sum_le_of_forall_le_of_nonneg o.le fun _ _ ↦
    (norm_mul_le_of_le ((norm_le_pi_norm ..).trans (H _ ⟨_, rfl⟩)) (h _)).trans_eq (by field))
  rintro _ ⟨a, b, β, ξ, he, rfl⟩
  let e {α} := Equiv.piEquivPiSubtypeProd (· ∈ T) α
  have H μ {p} (h : e μ = p) : ∃ σ : _ ≃ _, ∀ η (z : type_of% (padicComponents c)), weylRep μ η z =
      (weylRep p.1 (e η).1 (z ·) ⊗ₖ weylRep p.2 (e η).2 (z ·)).submatrix σ σ := h ▸ ⟨e, by
    simp [← Matrix.ext_iff, weylRep, @schur_apply_eq_prod (Subtype.{1} _), schur_apply_eq_prod (κ :=
      μ), ← Fintype.prod_subtype_mul_prod_subtype (· ∈ T), mul_smul_mul_comm]; tauto⟩
  obtain ⟨⟨ρ, G⟩, σ, H⟩ := H _ (e.apply_symm_apply (a, (e κ.1).2)), H κ.1 rfl
  let M := (vecMulVec (col 1 (σ y).1) β ⊗ₖ 1).submatrix σ ρ
  convert ← hD (_, e.symm (b, (e κ.2).2)) _ (deltaForm (o := ⟨n⟩) _ _ _ c (ιℓ.symm ∘ ((replicateCol
    _ ξ ⊗ₖ 1).submatrix ρ σ *ᵥ Pi.single y 1))).2 (by simp +contextual [e]) (by simpa +contextual
    [e] using he) M fun z h ↦ by simp [M, *, ← Pi.one_def, ← map_mul, Pi.mul_def]
  ext; refine (map_sum (.proj _ ∘ₛₗ padicModel _ (_, _) M ∘ₛₗ .const ∘ₛₗ .applyₗ _) ..).trans
    ((sum_coe_sort ..).symm.trans congr(∑ γ, $((dite_eq_left (q γ).2).symm ▸ ?_)))
  simp [padicModel, Function.comp_def _ (_ ∘ _), padicComponents_embFin (_, _),
    ← map_mul, -mulVec_single, ← (weylRep _ _ _).mul_assoc, M.mul_assoc]; simp [M, *, ← Pi.one_def,
    -mulVec_mulVec, mul_assoc, q, R, vecMulVec_mulVec, ← replicateCol_mulVec]; split <;> ring
