import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Bruhat.BigCell
import OmegaMath.NumberTheory.GRH.Lib.SiegelWeil.Mass.TorusMajorant
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.ExtensionByZero
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

Part of: Siegel's formula for representing a number by a hermitian form; local density bounds (known
result; see Lib.SiegelWeil.OneVector.OneVector).

This file: Product of completions at finite set S: projection, section, measure, modulus, product
formula. Finite place as one ring: volumes, content moments, cone mass bound, slab densities. -/

open Function Pi Sum ENNReal Fintype stdLattice Matrix MeasureTheory Place Pointwise Ring
  SemilocalField Set Valued MeasureTheory.Measure NumberField.FinitePlace

attribute [instance 90] Place.toIsTopologicalRing Place.toLocallyCompactSpace instStarMulForall

section

variable {E : Type} [Field E] [NumberField E] (S : Finset (FinPlace E)) (μ : ℕ)

/-- The ring of finite adeles of E that are integral at every place outside S. -/
noncomputable def integralOff := ⨅ w ∉ S, (LocInt w).1.comap (evalAt w)

/-- The diagonal ring homomorphism from E to the product of the completions E_w, w in S. -/
noncomputable abbrev ratToPlaces := (evalPlaces S).comp (algebraMap E _)

/-- The ring of S-integers of E: the elements integral at every finite place outside S. -/
noncomputable abbrev Filling.ratIntegralOff := (integralOff S).comap (algebraMap E _)

lemma mem_integralOff {x} : x ∈ integralOff S ↔ ∀ w ∉ S, v (x w) ≤ 1 := by simp [integralOff]; rfl

lemma isOpen_integralOff : @IsOpen (𝔸f E) _ (integralOff S) := AddSubgroup.isOpen_mono
    (Subring.toAddSubgroup_mono (iInf_le_iInf₂ ..)) isOpen_Ô

lemma evalAt_adeleOfLocal_of_notMem {w} (h : w ∉ S) x : evalAt w (adeleOfLocal S x) = 0 :=
  dite_eq_right h

@[simp] lemma adeleOfLocal_mem_integralOff x :
  adeleOfLocal S x ∈ integralOff S := by simp_all [integralOff, ↓evalAt_adeleOfLocal_of_notMem]

lemma adeleOfLocal_evalPlaces_mul a b : adeleOfLocal S (evalPlaces S b * a) =
  b * adeleOfLocal S a := by grind [adeleOfLocal_evalPlaces, evalPlaces_adeleOfLocal]

lemma mem_Ô_iff {x} : x ∈ Ô E ↔ evalPlaces S x ∈ O ∧
  x ∈ integralOff S := by simp [mem_O_locProd, mem_integralOff, mem_Ô]; grind

lemma locProd_O_eq_map_evalPlaces : O = (Ô E).map (evalPlaces S) := by ext x; simp; grind
  [mem_Ô_iff, adeleOfLocal_mem_integralOff S x, evalPlaces_adeleOfLocal]

lemma sub_adeleOfLocal_mem_iff {x} : x - adeleOfLocal S (evalPlaces S x) ∈ Ô E ↔ x ∈ integralOff
  S := by simp_all [mem_Ô_iff S, integralOff, evalAt_adeleOfLocal_of_notMem, -evalAt_apply]

instance : IsOpenUnits (LocProd S) := ⟨Units.isOpenEmbedding_val⟩

lemma idealZeta_locProd_le : @idealZeta (LocProd S) _ O μ ≤
  idealZeta (Ô E) μ := let f := (evalPlaces S).restrict (Ô E) O (by grind [mem_Ô_iff])
  have s :
    Surjective f.toAddMonoidHom := by aesop (add simp [Surjective, locProd_O_eq_map_evalPlaces])
  have e (I : Ideal _) := I.toAddSubgroup.index_comap_of_surjective s
  .trans_eq' (tsum_comp_le_tsum_of_injective (Subtype.map_injective (e · |>.trans_ne) (f := .comap
    f) (Ideal.comap_injective_of_surjective f s)) _) (tsum_congr (congr($(e ·).cast⁻¹ ^ μ)))

/-- The projection to the places of S carries Haar measure on the finite adeles integral off S
to vol(Ô) times Haar measure on the product of the E_w, w in S. -/
lemma map_evalPlaces_restrict_volume : (volume.restrict (integralOff S)).map (evalPlaces S) =
  volÔ E • volume := by simpa [← mem_Ô_iff, volume_O, inter_def] using
  (map_restrict_addHaar_eq volume volume (evalPlaces S) (by measurability) (isOpen_integralOff
  S).measurableSet (⟨adeleOfLocal S ·, by simp_all [integralOff,
  evalAt_adeleOfLocal_of_notMem, -evalAt_apply]⟩) isCompact_O.measurableSet rfl).1

lemma denomIndex_ne_zero (a : LocProd S) : denomIndex O a ≠ 0 :=
  isCompact_O.relIndex_ne_zero_add (isOpen_O.preimage (continuous_const_mul _))

lemma locallyIntegrable_sqrt_inv_norm (w : FinPlace E) : LocallyIntegrable fun x : LocField w ↦
  1 + √(‖x‖⁻¹ - 1) := (locallyIntegrable_const 1).add (Integrable.locallyIntegrable ⟨by fun_prop, by
  have ⟨a, h⟩ := NormedField.exists_one_lt_norm (LocField w)
  grw [hasFiniteIntegral_iff_norm, lintegral_eq_lintegral_meas_le _ (.of_forall (by simp)) (by
    fun_prop), setLIntegral_mono' (by simp) fun t k ↦ ?_,
    (integrable_inv_one_add_sq.mul_const ‖a‖).restrict.lintegral_lt_top]
  have ⟨d, z, b, _, c⟩ :=
    rescale_to_shell h (by positivity : 0 < 1 + t ^ 2) (one_ne_zero' (LocField w))
  refine (measure_mono fun x i ↦ mem_inv_smul_set_iff.2 (toNormedField.norm_le_one_iff.1
    ((norm_mul_le d x).trans ?_))).trans ((distribHaarChar_mul _ (Units.mk0 d z)⁻¹ (LocInt
    w)).ge.trans (by simpa [coe_nnreal_eq,
    genIndex_eq_inv_distribHaarChar, ↓genIndex_eq_inv_norm] using ofReal_le_ofReal c))
  simp_all [abs_of_nonneg, Real.le_sqrt']
  grw [b, i, add_sub_cancel, inv_mul_le_one]⟩)

/-- The finite set S of finite places of E is stable under complex conjugation. -/
abbrev Finset.StarStable [NumberField.IsCMField E] := Fact (∀ w ∈ S, star w ∈ S)

end

variable {E : Type} [Field E] [CMType E] (S : Finset (FinPlace E)) (μ : ℕ)
  [h : S.StarStable]

variable {E : Type} [Field E] [NumberField E] (S : Finset (FinPlace E)) [NumberField.IsCMField E]
  [h : S.StarStable] in
noncomputable instance : StarRing (LocProd S) := starRingOfInvolution (.pi fun w ↦
  (conjLoc (star_star _)).comp (evalRingHom _ (⟨_, h.1 _ w.2⟩ : S))) (evalPlaces_adeleOfLocal
  S · ▸ by simp [funext_iff, ← finAdele_star_apply, -evalPlaces_adeleOfLocal])

@[simp] lemma star_evalPlaces x : star (evalPlaces S x) = evalPlaces S (star x) := rfl

lemma adeleOfLocal_star x : adeleOfLocal S (star x) = star (adeleOfLocal S x) :=
  evalPlaces_adeleOfLocal S x ▸ by
  simp [↓star_evalPlaces, ↓adeleOfLocal_evalPlaces, star_idem]; congr; grind [Fact, star_star,
    mem_star]

variable {E : Type} [Field E] [NumberField E] (S : Finset (FinPlace E)) [NumberField.IsCMField E]
  [h : S.StarStable] in
instance : ContinuousStar (LocProd S) :=
    ⟨continuous_pi fun _ ↦ (continuous_locMap ..).comp (continuous_apply _)⟩

variable [WeilData E] in
instance : IsAdelic (A := LocProd S)
  O := by refine' { exists_topology := ⟨isOpen_O, isCompact_O⟩, isValuationPair := valPair, .. } <;>
  simp [locProd_O_eq_map_evalPlaces, ← map_mul] <;> grind [isAdelic_Ô, IsAdelic, IsStarStable]

omit [S.StarStable] in
lemma genIndex_eq_inv_prod_norm (x : LocProd S) : genIndex x = (∏ w, ‖x w‖)⁻¹ := by
  obtain h | ⟨u, rfl⟩ := em' (IsUnit x)
  simp_all [genIndex.map_nonunit, Pi.isUnit_iff, Finset.prod_eq_zero_iff.2]
  simpa [← distribHaarChar_mul, volume_pi_pi, genIndex_eq_inv_distribHaarChar,
    ↓genIndex_eq_inv_norm] using congr($((distribHaarChar_mul _ u⁻¹ _).trans congr(volume
    $(piMap_image_univ_pi (MulEquiv.piUnits u⁻¹ · • ·) (SetLike.coe <| LocInt ·.1)))).toReal)

omit h in
/-- Product formula inequality: for a nonzero S-integer y, the square root of the generalised
index [R : yR], R the integers at S, is at most the product of |y|_v over the infinite
places. -/
lemma sqrt_genIndex_le_prod_norm {y} (h : y ≠ 0 ∧
  y ∈ Filling.ratIntegralOff S) : √(genIndex (ratToPlaces S y)) ≤ ∏ v, ‖Φ v y‖ := by
  erw [Real.sqrt_le_left (by positivity), ← Finset.prod_pow, ← abs_norm_eq_prod_norm_sq,
    genIndex_eq_inv_prod_norm, S.prod_coe_sort (‖(y : 𝔸f E) ·‖)]
  refine inv_le_of_inv_le₀ ?_ ((Finset.prod_le_prod_of_subset_of_le_one₀ le_sup_left ?_ ?_).trans'
    (.trans (mod_cast (prod_eq_inv_abs_norm ?_).ge) ((finprod_comp_equiv
    equivHeightOneSpectrum.symm).ge.trans_eq (finprod_eq_prod_of_mulSupport_toFinset_subset _
    ((hasFiniteMulSupport ?_).preimage ?_) le_sup_right)))) <;> simp_all [mem_integralOff]

/-- A finite place: a place A with a compact open subring R of volume 1 that is self-dual for ψ
and compatible with τ, δ, ν, and with c = 1. -/
class IntegralPlace (A) [SemilocalField A] [StarRing A] extends Place A, isAdelic :
  IsAdelic (A := A) O where
  data_mem : τ ∈ O ∧ skewUnit.1 ∈ O ∧ skewUnit⁻¹.1 ∈ O ∧ c = 1 ∧ skewMeasure {b | b.1 ∈ O} = 1
  self_dual a : (∀ r ∈ O, ψ (r * a) = 1) ↔ a ∈ O
  md_eq_inv_genIndex x : md x = (.ofReal (genIndex x))⁻¹

attribute [local simp] isCompact_O SemilocalField.volume_O

/-- The ring of integers of the finite place: the compact open subring O of A. -/
abbrev IntegralPlace.R {A} [SemilocalField A] [StarRing A] [_P : IntegralPlace A] : Subring A := O

variable {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] (u : Aˣ) {ι : Type}
  [Fintype ι] {p : ι → A} {i : ι} {κ : Type} [Fintype κ] {s μ : ℕ} {𝔰 : Shape} {T : 𝔰.Form A}
  {g : Aˣ} {c : T.G}

@[simp] lemma IntegralPlace.volume_setOf_mul_mem : volume {x | u.1 * x ∈ R} = (P.md u)⁻¹ :=
    (Measure.map_apply (by fun_prop) isCompact_O.measurableSet).symm.trans
  (by simp [P.map_mul_volume])

lemma IntegralPlace.exists_ideal_cardQuot_eq (h : ↑u ∈ P.R) : ∃ I : Ideal P.R, I.cardQuot ≠ 0 ∧
  R.subtype '' I =
  {x | u⁻¹.1 * x ∈ R} ∧ I.cardQuot = (P.md u)⁻¹ := have := (genIndex_pos u).ne'; ⟨.span {⟨_, h⟩}, by
  simp_all [md_eq_inv_genIndex, genIndex_eq_card isOpen_O, Submodule.cardQuot_apply, Set.ext_iff,
    ← range_comp, Submodule.span_singleton_eq_range, ← u.eq_mul_inv_iff_mul_eq, mul_comm]⟩

lemma IntegralPlace.skewMeasure_setOf_mul_mem (h : star u.1 = u) : P.skewMeasure {b | u * b.1 ∈ R} =
  (P.md u ^ (2⁻¹ : ℝ))⁻¹ := by simpa [preimage, data_mem, h, ← add_mul] using (Measure.map_apply (by
  fun_prop) isOpen_O.preimage_val.measurableSet).symm.trans congr($(map_skewMeasure_mul_unit u h) _)

lemma IntegralPlace.intVectors_open_compact_vol : let L := SetLike.coe (intVectors P.R ι); IsOpen L
    ∧ IsCompact L ∧ volume L = 1 := ⟨isOpen_intVectors isOpen_O, isCompact_pi_infinite (by simp), by
    simpa [pi] using! volume_pi_pi fun _ ↦ P.R.carrier⟩

lemma IntegralPlace.md_le_volume {u : Aˣ} {S} (h : ∀ r ∈ P.R, u * r ∈ S) : P.md u ≤ volume S :=
  (md_inv u⁻¹).trans_le (volume_setOf_mul_mem u⁻¹ ▸ measure_mono (u.mul_inv_cancel_left · ▸ h _ ·))

lemma IntegralPlace.md_le_one (h : u.1 ∈ R) :
  P.md u ≤ 1 := by simp [md_eq_inv_genIndex, one_le_genIndex h]

lemma IntegralPlace.unitaryLevel_open_compact {J : Matrix ι ι A} :
  (∀ {g}, (unitaryLevel R g J).IsOpen) ∧ IsCompact (unitaryLevel R 1 J : Set (U J)) :=
  ⟨(isOpen_intGL isOpen_O).preimage_val.and isOpen_O.matrix.preimage_of_continuous,
  unitaryLevel_one.substr ((isCompact_intGL isCompact_O).preimage_val (isClosed_U J))⟩

/-- At a finite place with integers R, the determinant of a matrix in GL(R) has modulus 1. -/
lemma IntegralPlace.md_det_eq_one {V} (h : V ∈ intGL ι P.R) : md V.1.det = 1 := by
  simp [md_eq_inv_genIndex, genIndex_det_eq_one isOpen_O, h]

/-- Content: if some entry of p is a unit of A, there are a unit t of A and a row r over R with
r·p = t such that cp is integral exactly when tc ∈ R. -/
lemma IntegralPlace.exists_content (h : IsUnit (p i)) : ∃ t : Aˣ, ∃ r ∈ intVectors R ι, r ⬝ᵥ p = t ∧
  ∀ c, (∀ i, c * p i ∈ R)
  ↔ t * c ∈ R := (valPair.hermite (.punit i) (replicateCol Unit p)).elim fun V ⟨w, D, _, e, f⟩ ↦ by
  simp [entrywise, Unique.forall_iff, -coe_units_inv, Embedding.punit] at *
  exact ⟨(IsUnit.mul_iff.1 (e i ▸ h)).2.unit, _, w.isIntMatrix_inv i, f, fun c ↦
    ⟨(by simpa [← f, mul_comm c] using! w.isIntMatrix_inv.mulVec (v := c • p) · i),
    fun a j ↦ by grind [mul_mem (w.isIntMatrix j i) a, IsUnit.unit_spec]⟩⟩

/-- The volume of the set of c in A with cp integral if the entry p_i is a unit of A, and ∞
otherwise. -/
noncomputable def IntegralPlace.contentIndex i (p : ι → A) := ⨅ _ : IsUnit (p i),
  volume {c | ∀ j, c * p j ∈ R}

@[fun_prop] lemma IntegralPlace.measurable_contentIndex : Measurable (P.contentIndex i) := (funext
  fun _ ↦ iInf_eq_if _).symm.subst (.ite (measurableEmbedding_units_val.measurableSet_range.preimage
  (by fun_prop)) (measurable_measure_prodMk_right
  (measurable_smul intVectors_open_compact_vol.1.measurableSet)) (by simp))

/-- Let ζ_R(μ) ≤ 2, V ∈ GL_ι(R), β a unit, and single out s + k coordinates of Vᴴw, k ≥ μ. The
integral of `IntegralPlace.contentIndex`^s of these coordinates over the w with βw integral is at
most ζ_R(μ)·md(β)^(−(|ι|−s)). -/
lemma IntegralPlace.lintegral_contentIndex_pow_le (hμ : idealZeta P.R μ ≤ 2) {n k d} [Fintype n]
  (σ : n ⊕ κ ≃ ι) i {V} (β : Aˣ) (hV : V ∈ intGL ι R) (hd : card n + k = d ∧ card κ = s + k ∧ μ ≤
  k) : ∫⁻ w in {w | ∀ i, β.1 * w i ∈ R}, contentIndex i (fun j ↦ (V.1ᴴ *ᵥ w) (σ (inr j))) ^ s ≤
  idealZeta P.R μ * (P.md β)⁻¹ ^ d := have M : MeasurePreserving V.1ᴴ.mulVec :=
    ⟨by fun_prop, by simp [P.map_mulVec_volume, md_det_eq_one, *]⟩
  lintegral_le_idealZeta_mul hμ (fun I ↦ Vᴴ.mulVec ⁻¹' univ.pi fun i ↦
    (β * ·) ⁻¹' ite (σ.symm i).isLeft P.R
    (R.subtype '' I)) ((M.quasiMeasurePreserving.ae (tendsto_eval_ae_ae ae_isUnit)).mono fun w c a ↦
    (exists_content (p := (mulVec _ w <| σ <| inr ·)) (i := i) c).elim fun t ⟨_, _, _, e⟩ ↦ by
  have := by simpa [intVectors] using hV.isIntMatrix.isInt_conjTranspose.mulVec (v := β.1 • w) a
  let ⟨I, m, j, l⟩ := exists_ideal_cardQuot_eq (t * β) (by simp [← e, *])
  use I, m, j ▸ by simp [reindex_equiv σ, mul_mul_mul_comm, *]
  grw [hd.2.2, ← hd.1, j, l, ← md_inv, M.measure_preimage_le, volume_pi_pi, ← σ.prod_comp] <;>
    simp [m.pos.nat_succ_le, contentIndex, c.out, e, preimage, mul_mul_mul_comm, hd.2]
  exact (mul_le_of_le_one_right' (pow_le_one' (P.md t).mul_inv_le_one (s + k))).trans_eq' (by ring))

/-- If ζ_R(μ) ≤ 2 and |ι| ≥ μ + 1, then on |ι| + 1 hyperbolic planes the measure δ(h(v,v))dv
(`Place.quadricMeasure`) of the v with βv integral is at most ζ_R(μ)·md(β)^(−(2|ι|+1)). -/
lemma IntegralPlace.quadricMeasure_cone_le (hμ : idealZeta P.R μ ≤ 2) (hd : μ + 1 ≤ card ι) (β :
  Aˣ) : quadricMeasure (hyperbolicGram ι (0 : Matrix _ Empty
  A)) 0 {v | ∀ i, β * v i ∈ R} ≤ idealZeta P.R μ * (P.md β)⁻¹ ^ (2 * card ι + 1) := ((card_pos_iff.1
  (by lia)).map inr).elim fun i ↦ (fun o ↦ .trans (lintegral_indicator_one o).ge (.trans (by
  rw [(isDisintegration_quadricMeasure (T := hyperbolicGram ι 0) (by simp)).lintegral_eq
    (indicator _ _ ·.2)]
  simp (disch := with_unfolding_all fun_prop) [lintegral_map, ↓lintegral_prod,
    ← measurePreserving_sumElim (ι := ι).lintegral_comp, volume_eq_prod, lintegral_prod_symm']
  refine .trans_eq (lintegral_le_of_ae_imp (tendsto_eval_ae_ae ae_isUnit) fun v c ↦
    (exists_content (i := i) c).elim fun t ⟨r, a, b, e⟩ ↦ ?_) (lintegral_lintegral_swap ?_)
  grw [← mul_one (lintegral ..), ← (by simp [↓skewMeasure_setOf_mul_mem, contentIndex, ↓e, ← sq,
    c.out, ← rpow_natCast_mul, ENNReal.inv_mul_cancel, star_mul] :
    contentIndex i v * P.skewMeasure {b | (t * star t)⁻¹ * b.1 ∈ R} = 1),
    ← mul_assoc, ← setLIntegral_const, setLIntegral_mono ?_ fun x k ↦ ?_, setLIntegral_le_lintegral]
  any_goals fun_prop
  nth_rw 2 [← lintegral_add_right_eq_self _ ((P.τ * skewUnit⁻¹.1 * x * star t⁻¹) • star r ∘ inr)]
  repeat grw [lintegral_mul_const_le]; gcongr
  delta indicator; split_ifs with h n <;> simp [-not_and, flatChart, dotProduct, fromBlocks_mulVec,
    add_mul, intVectors, mul_assoc, ← Finset.mul_sum, mul_comm (star (v _)),
    Finset.sum_of_isEmpty] at *
  cases n ⟨by grind [t.inv_mul, by simpa using congr(star (t⁻¹ * $b))], fun j ↦ by grind
    [add_mem (h.2.1 j) (mul_mem (mul_mem ((e β).1 h.2.2) k) (mul_mem (mul_mem data_mem.1
    (isAdelic.1.1 (a j))) data_mem.2.2.1)), t.inv_mul], h.2.2⟩) ((lintegral_indicator o _).trans_le
  (lintegral_contentIndex_pow_le hμ (s := 1) (.sumAssoc ..) i β (k := card ι - 1) (one_mem _)
  (by simp; lia))))) (measurable_const_smul β.1 intVectors_open_compact_vol.1.measurableSet)

/-- Let h(u, ·) be the z-coordinate, vanishing at u; β the z-coordinate of e, v = e − z, ς =
h(v,e) − τ(h(e,e) − h(z,z)). Then g = 1 + β⁻¹(βu h(v, ·) − (v + ςu) h(u, ·)) is unitary (β⁻¹
= 0 for non-units), in U(V_ϱ) if e ∈ V_ϱ, and ge = z if h(e,e) = h(z,z), β a unit. -/
lemma IntegralPlace.exists_eichler_orbitPoint_eq {T :
  𝔰.Form A} {e} [IsHermUnit T.splitGram] {u} : let l := 𝔰.besselFrame 𝔰.top; let z := Pi.single l 1
    let h x y := star x ⬝ᵥ T.splitGram *ᵥ y; star u ᵥ* T.splitGram = z ∧ u l = 0 → ∃ k,
    let g :=
      U.of IsHermUnit.isUnit (1 + (e l)⁻¹ʳ • (vecMulVec (e l • u) (star (e - z) ᵥ* T.splitGram) -
      vecMulVec (e - z + (h (e - z) e - P.τ * (h e e - h z z)) • u) (star u ᵥ* T.splitGram))) k
    ((∀ i, floorOf i < 𝔰.ϱ → e i = 0) → g ∈ T.GT 𝔰.ϱ) ∧ (h e e = h z z → IsUnit (e l) →
    orbitPoint 𝔰.top g = e) := fun ⟨a, b⟩ ↦ by
  refine ⟨?_, fun k ↦ mem_floorGroup.2 ?_, fun k _ ↦ orbitPoint_eq_iff.2 ?_⟩
  any_goals simp [ext_iff_mulVec, ← mulVec_mulVec, IsHermUnit.conjTranspose_eq, vecMulVec_mulVec,
    star_vecMul, star_form, ← dotProduct_mulVec, ↓op_smul_eq_smul, -mulVec_single, -Pi.star_single,
    mulVec_sub, ((dotProduct_mulVec ..).trans congr($a ⬝ᵥ ·)),
    ← star_form IsHermUnit.conjTranspose_eq u]; intros; match_scalars <;> grind [inverse_non_unit,
    besselFrame_last]
  simp [*, vecMulVec_apply]

/-- The group of units of R, as a subset of A. -/
def IntegralPlace.intUnits := {u ∈ P.R | ∃ v : Aˣ, v⁻¹.1 ∈ R ∧ v = u}

lemma IntegralPlace.measurableSet_unitaryLevel : MeasurableSet (unitaryLevel R g T.splitGram :
  Set T.G) := unitaryLevel_open_compact.1.measurableSet

lemma IntegralPlace.measurableSet_exists_mul_mem_level {S : Subgroup _} : MeasurableSet
  {y | ∃ u ∈ S, u * (y * c) ∈ unitaryLevel R g _} := ofPred_exists _ ▸ (isOpen_iUnion fun _ ↦
  .and (by simp) unitaryLevel_open_compact.1.preimage_of_continuous).measurableSet

/-- Unfolding at a finite place: let η = η₀∗⋯∗η_{j−1}, K(g) the congruence subgroup of level g,
θ an s-finite measure and c an element of the unitary group. Then (η∗θ)(K(g)c⁻¹) =
η(K(g))·θ(𝒩K(g)c⁻¹), with 𝒩 = 𝒩_{<j} (`Shape.Form.unipotentBelow`). -/
lemma IntegralPlace.ascConv_mconv_unfolding [IsHermUnit T.splitGram]
    {θ : Measure T.G} [SFinite θ] {j} :
  (ascConv heisenbergMeasure j ∗ₘ θ) {y | y * c ∈ unitaryLevel R g _} = ascConv
  heisenbergMeasure j (SetLike.coe (unitaryLevel R g T.splitGram)) * θ {y | ∃ u ∈ unipotentBelow j,
  u * (y * c) ∈ unitaryLevel R g _} := (mconv_apply_eq_lintegral (measurable_mul_const c
  measurableSet_unitaryLevel)).trans (.trans (lintegral_congr fun y ↦ iteInduction (fun ⟨ξ, a, b⟩ ↦
  congr($((ascConv_heisenbergMeasure_invariant a).1) _).symm.trans (by simp [mconv_dirac, mul_assoc,
  (measurableEmbedding_mulRight _).map_apply, mul_mem_cancel_right b])) (compl_mem_ae_iff.1 <|
  ae_ascConv_mem_unipotentBelow.mono <| by simpa [mul_assoc] using ·))
  (lintegral_indicator_const measurableSet_exists_mul_mem_level _))

attribute [-simp] Units.val_inv_eq_inv_val evalAt_apply

attribute [local simp] integralOff dotProduct evalAt_adeleOfLocal_of_notMem

/-- Fourier inversion: for Mm = 1, β = β̄, a finite measure μ and C = `codifferent` E M of finite
volume, |∫_{z ∈ C}∫ψ_f(z(x^*x − β)/2) dμ(x) dz| equals vol(C)·μ{x : m(x^*x − β) ∈ Ô}. -/
lemma enorm_integral_codifferent {M : ℕ} {E} [Field E] [CMType E] [WeilData E] {m β : 𝔸f E} [n :
  Fact (volume (SetLike.coe (codifferent E M)) < ∞)] (u : M * m = 1) (hβ : star β = β) {μ :
  Measure (κ → _)} (_ : IsFiniteMeasure μ) : ‖∫ z in SetLike.coe (codifferent E M), ∫ x,
  (ψf E ((2⁻¹ : E) * (z * (star x ⬝ᵥ x - β))) : ℂ) ∂μ‖ₑ =
  volume (SetLike.coe (codifferent E M)) * μ {x | m * (star x ⬝ᵥ x - β) ∈ Ô E} := by
  have := by simpa using congr(star $u)
  rw [integral_integral_swap (.of_bound (Continuous.subtype_val
    (by fun_prop)).aestronglyMeasurable 1 (by simp [uncurry, Circle.norm_coe]))]
  simp (disch := simp [isOpen_codifferent, hβ, star_mul, add_mul, mul_add, AddChar.map_add_eq_mul])
    [↓fun y (s : star y = y) ↦ (⟨fun h ↦ (forall_psi₀_mul_eq_one_iff _).1 fun r
    a ↦ by rw [psi₀_apply, mul_right_comm m, ← mul_assoc, ← ψf_half, star_mul', s, ← add_mul,
    h ⟨_, .add_star_self _⟩ (Circle.ext <| .trans (by simp [psi₀_apply]; grind) <|
    (forall_psi₀_mul_eq_one_iff _).2 (sub_mem a (star_mem_Ô a)) · ·)], fun h z k ↦
    congrArg _ (.trans (by simp; grind) ((ψf_half _).trans (k _ (mul_mem traceOneAdele_mem h))))⟩ :
    (∀ z ∈ codifferent E M, (ψf E ((2⁻¹ : E) * (z * y)) : ℂ) = 1) ↔ m * y ∈ Ô E), setIntegral_char]
  erw [integral_indicator_const _ isOpen_Ô.preimage_of_continuous.measurableSet]
  simp [← ofReal_norm, n.1.ne, preimage, real_def, mul_comm]

/-- Let sm = 1, β = β̄, ζ_Ô(μ) ≤ 2, 2μ+2 ≤ |κ|. Integrals of f(x_T) over x integral off T with
m(x*x−β−a) ∈ Ô are v times the same integrals at T, for a finite v with vol(`codifferent` E s)·ν{Γ :
mΓ/δ ∈ R}·v ≤ ζ_Ô(μ)vol(Ô)^|κ|. -/
lemma IntegralPlace.mass_near_quadric_off_places_le {E} [Field E] [CMType E] [WeilData E] {m β :
  𝔸f E} [n : Fact (volume (SetLike.coe (codifferent E s)) < ∞)] (u : s * m = 1) (hβ : star β =
  β) {T} [Finset.StarStable T] [P : IntegralPlace (LocProd T)] (hμ : idealZeta (Ô E) μ ≤ 2)
  (hd : 2 * (μ + 1) ≤ card κ) : ∃ v ≠ ∞, volume (SetLike.coe (codifferent E s)) *
  (P.skewMeasure {Γ | evalPlaces T m * (skewUnit⁻¹.1 * Γ) ∈ R} * v) ≤ idealZeta (Ô E) μ * volÔ E ^
  card κ ∧ ∀ a f, Measurable f → ∫⁻ x in {x | m * (star x ⬝ᵥ x - (β + adeleOfLocal T a)) ∈ Ô E},
  (intVectors (integralOff T) κ).carrier.indicator (f <| evalPlaces T ∘ ·) x =
  v * ∫⁻ y in {y | evalPlaces T m * (star y ⬝ᵥ y - (evalPlaces T β + a)) ∈ R}, f y := by
  let G := {x ∈ (intVectors (integralOff T) κ).1 | m * (star x ⬝ᵥ x - β) ∈ integralOff T}
  let α (Γ : skewAdjoint _) := β - adeleOfLocal T (P.skewUnit⁻¹ * Γ.1 + evalPlaces T β)
  have o := isOpen_integralOff T
  obtain ⟨O : (evalPlaces T ∘ ·) ⁻¹' intVectors P.R κ ∩ G ⊆ stdLattice E κ, mG : MeasurableSet G,
    mZ : MeasurableSet {(x, Γ) : (κ → _) × _ | m * (star x ⬝ᵥ x - α Γ) ∈ Ô E}⟩ := by
    simp +contextual [subset_def, mem_Ô_iff T, stdLattice, intVectors, G], ((isOpen_intVectors).and
    o.preimage_of_continuous).measurableSet, isOpen_Ô.preimage_of_continuous.measurableSet
  have v := by simpa [intVectors_open_compact_vol] using (map_restrict_addHaar_eq volume volume
    (.compLeft (evalPlaces T) κ) (continuous_postcomp (continuous_evalPlaces T)).measurable mG
    (⟨adeleOfLocal T ∘ ·, by simp +contextual [G, intVectors, ← adeleOfLocal_star, funext_iff]⟩)
    intVectors_open_compact_vol.1.measurableSet rfl).1
  refine ⟨volume _, measure_ne_top_of_subset O isCompact_stdLattice.measure_ne_top, ?_,
    fun a f h ↦ by
    erw [setLIntegral_indicator (isOpen_intVectors).measurableSet, (?_ : _ ∩ _ = _),
      ← restrict_restrict' mG, ← setLIntegral_map ?_ h (by fun_prop), v, setLIntegral_smul_measure]
    exacts [rfl, isCompact_O.measurableSet.preimage (by fun_prop),
      Set.ext (by simp +contextual [mem_Ô_iff T, G, iff_def])]⟩
  grw [← setLIntegral_const, setLIntegral_mono (measurable_measure_prodMk_left mZ) fun x h ↦
    (measure_preimage_add _ (P.skewUnitMul _ (star_dotProduct (evalPlaces T ∘ x) _).symm)
    _).ge.trans ((measure_mono fun Γ k ↦ (fun l ↦ ⟨l, ?_⟩) ?_).trans (le_restrict_apply ..)),
    lintegral_mono_set O, ← Measure.prod_apply mZ, prod_apply_symm mZ, lintegral_const_mul_le,
    lintegral_mono fun _ ↦ ?_, setLIntegral_const, data_mem.2.2.2.2, mul_one]
  grw [← lintegral_gauss_sum_le_idealZeta hμ hd, ← setLIntegral_le_lintegral,
    ← enorm_integral_le_lintegral_enorm]
  exacts [(enorm_integral_codifferent u (by simp [α, *, ← adeleOfLocal_star])
    (isFiniteMeasure_restrict.2 isCompact_stdLattice.measure_ne_top)).ge, by simpa [α, ← mul_assoc,
    u] using (mul_mem data_mem.2.1 ((mem_Ô_iff T).1 (sub_mem (nsmul_mem l s) (dot_mem (O h)
    (O h)))).1), by simpa +contextual [mem_Ô_iff T, α, mul_add] using And.intro k h.2.2]
