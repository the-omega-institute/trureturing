import GRH.Lib.Shimura.IntegralModel.NeatLevel
import GRH.New.RealPlace.FrameNorm
import GRH.New.Filling.GramLiouville
import GRH.New.Filling.StableCells
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Lemmas on lattices, strong approximation, freeness and frame data used for near terms.

Known result: Siegel's lemma over number fields (Bombieri–Vaaler). Here it is stated for lattices in
the genus of the standard hermitian lattice over a CM field containing the 5040th roots of unity. A
subspace is cut out by lattice vectors whose norms have product bounded by its discriminant, with a
crude constant in the degree, the codimension and the root discriminant. Source: E. Bombieri, J.
Vaaler, On Siegel's lemma, Invent. Math. 73 (1983).

This file: Siegel's lemma for hermitian lattices; convergence of height zeta function of subspaces.
Unipotent strong approximation, and its use with freeness on the filling data. Norm identity for
frames, integrality and size of minors of near terms, numerics. -/

section

open Module ENNReal Fintype MatMul Matrix NumberField Prod Space

/-- Siegel's lemma: a subspace T of E^κ of codimension s is the orthogonal of s nonzero vectors
X_i of E^κ ∩ uÔ^κ with (∏‖X_i‖)^(2f) ≤ (8fs·rd_E)^(fs)·d, ‖·‖ Euclidean over all f infinite
places, d the discriminant `Filling.sublatticeDisc` of T ∩ uÔ^κ.

Known result: Siegel's lemma over number fields (Bombieri–Vaaler). -/
lemma Filling.siegel_lemma {E} [Field E] [CMType E] [StablyUnram E] {κ} [Fintype κ] u {T : Submodule
  E _} {s} (hs : finrank E T + s = card κ) : ∃ X : Matrix (Fin s) κ E, Xᵀᴴ.mulVecLin.ker = T ∧
  (∀ i, X i ∈ ((stdSpace ..).move (1, u)).baseLattice ∧ X i ≠ 0) ∧
  (∏ i, ‖((stdSpace ..).move (1, u)).archCoords (X i)‖) ^ (2 * numInfPlaces E) ≤
  (8 * (numInfPlaces E * s) * rootDiscr E) ^ (numInfPlaces E * s) * sublatticeDisc u.1.3 T := by
  rw [sublatticeDisc]; obtain ⟨m, ⟨hm, p, o, hp⟩, x, b, ⟨k⟩, hx, e⟩ := sublatticeBasis u.1.3 T
  obtain ⟨_, h₁, y, a, ⟨l, hl⟩, hy, rfl⟩ := sublatticeBasis u.1.3 _ (s := s) (add_left_cancel
    (xᴴ.mulVecLin.finrank_range_add_finrank_ker.trans (by
    rw [LinearMap.range_eq_top.2 (⟨kᴴ *ᵥ ·, _⟩)] <;> simp_all [← conjTranspose_mul])))
  obtain ⟨Z, f, t, w⟩ := congr($(mul_eq_zero_of_range_le_ker hy.le)ᴴ), exists_mul_add_mul_eq hy.ge
  have := (jacobi_perp_discriminant (by simp [_root_.IsUnimodular]) hm h₁
    ((U.gram_invariant u⁻¹ ..).trans
    (by simpa [e, finAdeleMat_conjTranspose] using congr(b.1ᴴ * finAdeleMat $Zᴴ * a.1))) (by aesop)
    (diagonal 0) 1 rfl (by tauto)).2
  choose r _ hr using fun v ↦ exists_orthonormal_mul id ⟨_, by simpa using congr($(hl).map (Φ v))⟩
  choose B z g H using minkowski_second (mkAdelicGL (r, a))
  have j := h₁.1.mul (N := a.2 * finAdeleMat Bᵀ) fun j i ↦ snd_sum.subst ((g.2 i).1 j)
  have c v := congr(‖det $(hr v)‖)
  simp [← map_conjTranspose, field, ← Matrix.map_mul, ← (yᴴ.map _).mul_assoc,
    ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← finAdeleMat_conjTranspose, fromBlocks_add, ← fromRows_zero, by simpa using
    (U.gram_invariant u⁻¹ (b := Fin ·) (diagonal 1))] at c this H hp j Z
  use (y *ᵥ B ·), hx ▸ le_antisymm (a := (y * Bᵀ)ᴴ.mulVecLin.ker) (fun v h ↦ ⟨tᴴ *ᵥ v, by
    simpa [g] using congr($wᴴ *ᵥ v - fᴴ *ᵥ Bᵀᴴ⁻¹ *ᵥ $h)⟩) (by simp [LE.le, Z]), fun i ↦ ⟨(by
    simpa [↓move_vecAtPoint, mulVec, Space.vecAtPoint, dotProduct, snd_sum] using! j · i), fun z ↦
    g.1 (det_eq_zero_of_row_eq_zero i (by simpa [hl] using congr((l *ᵥ $z) ·)))⟩
  grw [← H, mul_right_comm, ← le_mul_of_one_le_left (by positivity), ← zpow_natCast 2, zpow_comm,
    zpow_sum_of_ne_zero (by simp), zpow_natCast, ← (g.2 _).2]
  gcongr; simpa [archCoords, ↓move_vecAtPoint, Space.vecAtPoint, PiLp.norm_eq_of_L2, sum_prod_type,
    mulVec_eq_sum, fst_sum, -coe_units_inv, ↓mulVec_mulVec] using!
    congr(√(∑ v, $(sum_norm_sq_mulVec_of_isometry (hr v) ((r v).2 *ᵥ _)))).le
  erw [← this, ideleAbs_det_mkAdelicGL, genIndex_eq_inv_finIdeleAbs a.det]
  simpa [field, c, ← Finset.prod_mul_distrib, Real.sqrt_prod, abs_norm_eq_prod_norm_sq,
    finIdeleAbs] using (AddSubgroup.relIndex_eq_one.2 fun v ↦ (by simpa [hp] using o.mulVec ·)).ge

/-- For finite adelic unitary u let d(T) be the discriminant `Filling.sublatticeDisc` of T ∩ uÔ^κ.
Over all subspaces T of E^κ of codimension s, ∑d(T)^(−(k+1)) ≤ (200fk·rd_E)^(f(k+1)s), where k =
|κ| and f is the number of infinite places. -/
lemma Filling.tsum_sublatticeDisc_inv_le {E} [Field E] [CMType E] [StablyUnram E] {κ} [Fintype κ]
  (u : Gf E κ) s : ∑' T : Submodule E _, ite (finrank E T + s =
  card κ) (ENNReal.ofReal (sublatticeDisc u.1.3 T ^ (card κ + 1))⁻¹) 0 ≤ .ofReal
  ((200 * (numInfPlaces E * card κ) * rootDiscr E) ^ (numInfPlaces E * (card κ + 1) * s)) := by
  have O (x : {x ∈ ((stdSpace ..).move (1, u)).baseLattice | x ≠ 0}) :=
    (one_le_firstMinimum).trans (x.2.rec firstMinimum_le)
  choose a b using tsum_inv_pow_le_of_separated one_pos (fun x y _ ↦ by
    simpa using O ⟨x - y, by aesop⟩) O
  grw [(by ring : 200 = (5 / 1 : ℝ) ^ 2 * 8), rootDiscr, mul_assoc, mul_assoc, pow_mul, mul_pow,
    ← pow_mul, ofReal_pow, ← b, ← tsum_mul_right, ofReal_tsum_of_nonneg _ ((a _).mul_right _), ←
    Fin.prod_const, ← tsum_prod_le_prod_tsum, ← tsum_fiberwise _ fun X ↦
    (Subtype.val ∘ X)ᵀᴴ.mulVecLin.ker]
  gcongr; split_ifs with hs
  choose X e h H using siegel_lemma u hs; have := Finset.univ.one_le_prod₀ fun i _ ↦ O ⟨_, h i⟩
  grw [← ENNReal.le_tsum ⟨(⟨_, h ·⟩), e⟩, ← ofReal_prod_of_nonneg, ← one_div,
    sublatticeDisc, div_le_of_le_mul₀] <;> try positivity
  simp [field, Finset.prod_pow, sublatticeDisc, rootDiscr] at *
  grw [← mul_assoc, pow_mul, H, s.le_add_left, hs]
  ring_nf; all_goals simp [mul_add, NeZero.one_le] <;> bound

section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {𝔰 : Shape}

noncomputable instance : TraceOne (𝔸f E) := ⟨(2⁻¹ : E), by norm_num [← map_add]⟩

/-- Strong approximation for the unipotent group 𝖴 of the form H^ϱ ⊥ T, with T invertible
hermitian over E: every open set of matrices containing a finite adelic point of 𝖴 contains
a rational point of 𝖴. -/
lemma besselU_dense {T : 𝔰.Form E} [IsHermUnit T] {T' : 𝔰.Form (𝔸f E)} (e : T.splitGram.map (↑) =
  T'.splitGram) : besselU ≤ (T.besselU.map (U.map _ (h :=
  e))).topologicalClosure := have : IsHermUnit T'.splitGram := e ▸ ⟨Matrix.IsHermitian.map
    IsHermUnit.conjTranspose_eq _ fun _ ↦ by simp, IsHermUnit.isUnit.map (RingHom.mapMatrix _)⟩
  (unipotentBelow_eq_besselU .refl).ge.trans (unipotentBelow_induction (C := fun _ x ↦
    x ∈ _) (by simp) (fun l x c _ i ↦ by
    obtain h | h := le_or_gt 𝔰.ϱ l; simpa [eq_one_of_mem_floorGroup_inf c (.inr h)]
    obtain ⟨p, rfl⟩ := exists_eq_heisenbergElem_of_mem (a := ⟨l, h⟩) c
    exact mul_mem (map_mem_closure ((U.isClosedEmbedding_mat IsHermUnit.isUnit).continuous_iff.2 (by
      simp [Function.comp_def, TraceOne.heisenbergElem, eichlerMap]; fun_prop))
      ((DenseRange.piMap fun _ ↦ denseRange_algebraMap_finAdele).prodMap ((show Function.Surjective
      skewPart from (⟨TraceOne.τ * ·.1, by simp [skewPart, ← add_mul]⟩)).denseRange.comp
      denseRange_algebraMap_finAdele (by fun_prop)) _) fun _ ⟨q, k⟩ ↦
      k ▸ ⟨_, unipotentBelow_le_besselU (heisenbergElem_mem_floorUnipotent _ (q.1, skewPart q.2)).2,
      by ext; simp [inclMatrix, U.map, TraceOne.heisenbergElem, eichlerMap, ← e, Matrix.vecMulVec,
      Matrix.vecMul, entrywise, apply_ite (algebraMap ..), apply_ite star,
      TraceOne.τ, -Fintype.sum_sum_type, -splitGram_eq_ite_oppositeIndex]⟩) i) _)

attribute [local simp] Filling.ratToFin_toBesselH Filling.termPosition mul_assoc

end

attribute [local simp] Filling.ratToFin_toBesselH Filling.termPosition mul_assoc

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

@[simp] lemma Filling.unipotentChar_one : S.unipotentChar 1 = 1 := by simp [unipotentChar,
  simpleRootSum_eq_zero_of_mem_besselH]

/-- Strong approximation for 𝖴: for x ∈ 𝖴(𝔸_f) and any y in the finite adelic unitary group,
some rational u ∈ 𝖴 has y⁻¹ x⁻¹ u y ∈ K(g). -/
lemma Filling.exists_besselU_approx {x} (hx : x ∈ besselU) y : ∃ u ∈ besselU,
  y⁻¹ * (x⁻¹ * S.ratToFin u) * y ∈
  S.principalLevel := by simpa using! Set.exists_mem_image.1 ((closure_inter_open_nonempty_iff
  ((S.principalLevel_eq_unitaryLevel ▸ (isOpen_intGL isOpen_Ô).preimage_val.and
  isOpen_Ô.matrix.preimage_of_continuous : S.principalLevel.IsOpen).preimage_of_continuous (f :=
  (y⁻¹ * x⁻¹ * S.toLatBasis · * y)) (.subtype_mk (by fun_prop) _))).1 ⟨_, besselU_dense
  (map_splitGram_ratMiddle ..) (toLatBasis_mem_besselU.1 (S.toLatBasis.1.4 x ▸ hx)), by simp⟩)

/-- If u, v ∈ 𝖴 and h ∈ H are finite adelic points with u⁻¹ h⁻¹ v h ∈ K(g), then the character
`Filling.unipotentChar` takes the same value at u and v. -/
lemma Filling.unipotentChar_eq_of_mem_principalLevel {u v} (hu : u ∈ besselU) (hv : v ∈ besselU) g
    (hk : u⁻¹ * ((S.inclHFin g)⁻¹ * v * S.inclHFin g) ∈ S.principalLevel) : S.unipotentChar v =
  S.unipotentChar u := by erw [← mul_one (S.unipotentChar u), ← S.selfDualChar_eq_one_of_mem _
  (inv_mul_simpleRootSum_mem (S.principalLevel_eq_unitaryLevel.le hk)),
  ← S.selfDualChar.map_add_eq_mul, ← mul_add, ← simpleRootSum_mul] <;> grind [unipotentChar,
  simpleRootSum_mul, mul_mem, inv_mem, mem_unitriGroup_of_mem_besselU,
  mem_unitriGroup_of_mem_floorGroup, mul_inv_cancel_left, inclHFin_mem_besselH]

/-- Under the standing hypotheses, a rational element γ of the Bessel subgroup S that is a term
over (c, 1, c') forces c = c' and lies in 𝖴_c(g). -/
lemma Filling.eq_and_mem_classUnip_of_besselS [ok : S.IsAdmissible] {c d γ} (h : γ ∈ besselS) (o :
  S.termPosition c d γ ∈ S.principalLevel) : c = d ∧ γ ∈ S.classUnip c :=
  have ⟨_, u, η, _⟩ := exists_besselU_mul_toBesselH h; fun _ : c = d ∧ η = 1 ↦ by simp_all
    [classUnip] (eq_and_eq_one_of_doubleCoset_rep (·.out_eq) ((map_eq_one_iff _ Fact.out).1 <|
    (aut_columnLevel ..).le ⟨⟨·, rfl⟩, ·⟩) η (by simp_all [ok.1, principalLevel_eq_unitaryLevel,
    ↓mem_unitaryLevel_of_besselU_mul (u.termPosition_mem_besselU c) (inclHFin_mem_besselH _)]))

lemma Filling.exists_rat_approx_unipotentChar_eq c {u} (hu : u ∈ besselU) :
    ∃ u₀ ∈ besselU, u⁻¹ * S.termPosition c c u₀ ∈ S.principalLevel ∧
  S.unipotentChar (S.ratToFin u₀) = S.unipotentChar u := (exists_besselU_approx
  ((besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup (inclHFin_mem_besselH c.out))
  _).1 hu) (S.h c)).imp (by simp_all [unipotentChar_eq_of_mem_principalLevel hu _ c.out])

lemma Filling.exists_besselS_mem_termsOver [ok : S.IsAdmissible] c {σ} :
    σ ∈ S.reducedImage besselS → ∃ d, ∃ γ ∈ besselS, γ ∈ S.termsOver c σ d := fun ⟨k, hk, _⟩ ↦ by
  obtain ⟨u, hu, _, ⟨g, ⟨⟩⟩, e⟩ := S.range_inclHFin ▸ mem_besselS.1
    (mul_mem (mem_unitriGroup_of_mem_floorGroup (inclHFin_mem_besselH c.out)) hk)
  obtain ⟨⟨x, hx, l⟩, d, η, a, rfl⟩ := exists_besselU_approx hu (S.inclHFin g),
    exists_eq_map_mul_rep_mul stdEmbFin S.columnLevel (·.out_eq) g
  exact ⟨d, x * toBesselH _ _ η, mem_besselS.2 ⟨_, hx, _, toBesselH_mem η, rfl⟩, (div_mem l (ok.1.le
    a.2)).imp' (k * ·) (by simp_all [division_def, ← mul_inv_eq_of_eq_mul e, ratToFin_toBesselH η])⟩

/-- Freeness: for rank n ≤ |κ|, a rational element γ of the
standard unitary group U(n) is 1 if, for some finite adelic g, g⁻¹γg is integral and
congruent to 1 modulo every chosen place above the prime q_i. -/
lemma Filling.eq_one_of_reduceAt_eq_one [StablyUnram E] {n} [Fintype.{0} n] (hn : Fintype.card n ≤
  𝔰.k) i {γ g} hk (h : ∀ w : S.chosenPlaces i,
  Kf.reduceAt w ⟨g⁻¹ * (stdSpace E n).embFin γ * g, hk⟩ = 1) : γ = 1 := by
  apply (map_eq_one_iff _ Fact.out).1 ((classAut_eq_bot _ _ le_rfl g).le ⟨⟨_, rfl⟩, _, funext h,
    rfl⟩) <;> simp [S.chosenPlaces_q i, S.card_chosenPlaces, finrank_eq_two_mul_card_infinitePlace,
    pow_mul]; rify; gcongr
  grw [hn, ← le_levelPrime, ← k_le_b, ← S.ϱ_le_k.dest.choose_spec]; norm_cast; lia

end

namespace Filling

open Subgroup Real NumberField Matrix Finset ComplexOrder Complex Fin Classical Nat
variable {R : Type} [CommRing R] [StarRing R] {𝔰 : Shape} {T : 𝔰.Form R} {s s' : T.G} {E : Type}
  [Field E] [CMType E] {S : Filling E 𝔰} {γ u : S.G E} {c : S.Classes} {c' : S.Classes} {r : S.GRes}
  {x : Fin (𝔰.ϱ + 1) → E} {y} (v)

lemma frameImage_mul : frameImage (s * s') = s.1.1 * frameImage s'.1.1 := rfl

lemma frameImage_mul_of_mem_besselU0 : u ∈ besselU0 → frameImage (γ * u).1.1 =
  frameImage γ := by simp_all [mem_besselU0_iff, submatrix_mul_besselFrame]

lemma frameImage_inv_mul_eq_iff : frameImage (s⁻¹ * s').1.1 = frameImage 1 ↔ frameImage s.1.1 =
  frameImage s' := s.1.4 ▸ comm.trans s⁻¹.1.1.mul_right_inj_of_invertible

attribute [local simp] frameBox frameDisc funext_iff classBasis toBesselH forall_fin_succ'
  besselLatticeBasis Matrix.mul_apply mul_conj'
  Finset.sum_eq_zero_iff_of_nonneg frameImage_one_mulVec mulVec dotProduct Ne.pos splitGram

attribute [local simp ←] pow_add pow_mul mulVec_mulVec

lemma star_mul_last_eq_of_frameImage_eq (e : frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y) :
  star (x 𝔰.top) * x 𝔰.top = star (y 𝔰.top) * y 𝔰.top := by simpa [↓frameImage_one_mulVec,
  middleGram, field] using (e ▸ frameImage_mulVec γ y ▸ U.form_mulVec_mulVec ..:)

lemma frameProducts_mulVec_of_frameImage_eq (e : frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y) :
  S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (-S.N * x 𝔰.top) := by
  simp [frameGram_eq_frameImage, ← e, middleGram]

lemma eq_zero_of_ratMiddle_form_eq_zero (hv : v (.inr ()) = 0) (h : star v ⬝ᵥ S.ratMiddle E *ᵥ
  v = 0) : v = 0 := by simpa [middleGram, *, conj_mul'] using congr(Φ ofNonempty $h)

/-- Let t = γf·y be orthogonal to e₁, …, e_ϱ, with h(z, t) = D. Then t has no e*-part,
z-coordinate −D/N, and X₀-part t₀ with N|t₀|_v² = |D|_v² − N²|y_z|_v² at each infinite v; if
this is ≤ 0 somewhere, t lies in the span of f. -/
lemma norm_sq_middle_part_eq {D t} (h : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top D) (e :
  frameImage γ.1.1 *ᵥ y = t) : ((∀ a, t (eStar a) = 0) ∧ -(S.N * t 𝔰.z) = D) ∧
  ∀ v, let s := S.N * ∑ i, ‖Φ v (t (𝔰.indexX₀ i))‖ ^ 2
  s = ‖Φ v D‖ ^ 2 - (S.N * ‖Φ v (y 𝔰.top)‖) ^ 2 ∧ (s ≤ 0 → ∃ x, frameImage 1 *ᵥ x = t) := by
  have := (congr(Φ · $(frameImage_mulVec γ y ▸ U.form_mulVec_mulVec ..)))
  simp_all [↓e, ↓frameImage_one_mulVec, frameGram_eq_frameImage, middleGram, @eq_comm _ _ D,
    ← ofReal_inj]
  use fun _ ↦ ⟨by grind [conj_mul'], (⟨t ∘ 𝔰.besselFrame, by
    simpa [init, @eq_comm E] using ·.antisymm (by positivity)⟩)⟩

lemma map_termDisc_eq_norm : Φ v (S.termDisc γ) = ‖Φ v (S.termDisc γ)‖ := eq_coe_norm_of_nonneg (by
  choose y e l using exists_mulVec_eq_single_det (S.frameProducts γ)
  simpa [l, mul_pow] using
    zero_le_real.2 (((norm_sq_middle_part_eq e rfl).2 v).1.subst (by positivity)))

lemma hasLevel_last (h : S.termDisc γ ≠ 0) : S.HasLevel (last _) γ := ⟨⟨1, by simp; lia⟩, fun e ↦ by
  have := map_termDisc_eq_norm (γ := γ) ofNonempty; simp_all [leadingMinor, neg_eq_self], by grind⟩

lemma gramDiscReal_realFrameGram_ratToInf : gramDiscReal (realFrameGram (S.ratToInf γ v)) = (∏ a :
  Fin 𝔰.n, S.frameScaleSq v a) ^ 2 * ‖Φ v (S.termDisc γ)‖ := congrArg _ (by simp [↓ofReal_mul,
  ↓← map_termDisc_eq_norm, leadingMinor, ↓det_submatrix_realFrameGram_ratToInf, frameScaleSq,
  prod_univ_add, pow_add, field] : frameDisc 1 ((realFrameGram _).submatrix id id) = ofReal _)

lemma ratToInf_mem_besselU0 (h : u ∈ besselU0) v : S.ratToInf u v ∈ besselU0 :=
  ⟨h.1.ratToInf_mem_unitriangularOn v, h.2.ratToInf_mem_unitriangularOn v⟩

lemma mul_mem_boxedPoints_iff {u} (hu : ∀ v, u v ∈ besselU0) : u * y ∈ S.boxedPoints ↔
  y ∈ S.boxedPoints := by simp_all [boxedPoints,
  besselSize_besselS_mul (mem_unitriGroup_of_mem_besselU (hu _).1), frameVector_mul, mem_sup_left]

lemma _root_.IsNormalForm.ratToInf {j} : IsNormalForm j γ → IsNormalForm j (S.ratToInf γ v)
  | ⟨_, hc, h⟩ => ⟨_, by simpa using congr(Φ v $hc), fun a ↦ (by
  choose x y e h using h a ·; let d := (S.basisScale v (𝔰.besselFrame a) / S.basisScale v ·)
  refine ⟨d ∘ 𝔰.besselFrame * Φ v ∘ x,
    d ∘ 𝔰.besselFrame * Φ v ∘ y, ?_, ?_⟩; convert congr(d * Φ v ∘ $e)
  all_goals simp [mulVec_eq_sum, mul_sum]; grind [basisScale_ne_zero])⟩

lemma termsOver.isIntMatrix_termPosition : γ ∈ S.termsOver c r c' →
  IsIntMatrix (Ô E) (S.termPosition c c' γ).1.1 | ⟨k, _, e⟩ => e ▸ k.2.isIntMatrix

lemma classCoord_conj_splitGram c : (S.classCoord c)ᴴ * (S.latMiddle _).splitGram * S.classCoord c =
  (S.ratMiddle _).splitGram := gram_inv_of_gram_eq
  (gram_mul_of_gram_eq (toBesselH _ _ _).2 (gram_besselLatticeBasis _ _ S.piBar_mul_star))

lemma frameImage_termPosition : frameImage (S.termPosition c c' γ) = S.classCoord c * finAdeleMat
  (frameImage γ.1.1) := coe_termPosition c .. ▸ frameImage_mul_of_mem_agreeWithOneOn (by simp) _

lemma frameGram_termPosition : (S.latMiddle _).frameGram (S.termPosition c c' γ) =
  finAdeleMat (S.frameProducts γ) := by
  simp [frameGram_eq_frameImage, frameImage_termPosition, ← classCoord_conj_splitGram c,
    ← Matrix.mul_assoc, map_splitGram_ratMiddle, -splitGram]
  congr; simp [classCoord, ← ext_iff]

lemma IsNear.mul_of_mem_besselU0 {u'} (h : S.IsNear γ) (hu : u ∈ besselU0) (hu' : u' ∈ besselU0) :
  S.IsNear (u * γ * u') := h.imp' (S.ratToInf u * ·) (by simp_all [mul_assoc,
  mul_mem_boxedPoints_iff, ratToInf_mem_besselU0])

variable (k : γ ∈ S.termsOver c r c') (l : Fin (𝔰.ϱ + 1 + 1))
  (w : NumberField.InfinitePlace E) (a : Fin (𝔰.ϱ + 1)) (b : Fin (𝔰.ϱ + 1))

/-- An isometry s lies in the Bessel subgroup S if and only if, for every vector f_a of the
frame (e₁, …, e_ϱ, z), the difference s f_a − f_a lies in the span of the earlier frame
vectors. -/
lemma mem_besselS_iff_frameImage : s ∈ besselS ↔ ∀ i a, a.1 ≤ FI.level i → frameImage s.1.1 i a =
  frameImage 1 i a := by simp [mem_unitriGroup, FI.level]; grind

lemma pow_le_tailScale {e} (h : e ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E) : S.b ^ e ≤ S.tailScale := by
  rify at h; grw [tailScale, ← rpow_natCast, ← S.pow_le_k,
    rpow_le_rpow_left_iff] <;> grind [thousand_le_b]

lemma tailScale_pow_four : S.tailScale ^ 4 = S.b ^ (𝔰.k * numInfPlaces E) := by
  erw [← rpow_mul_natCast, ← rpow_natCast] <;> grind [thousand_le_b]

lemma of_size_bounds {p : Prop} (h : 2 ≤ S.g → 2 ≤ S.tailScale → 1000 ≤ S.b → 2 ≤ S.b → 0 ≤
  S.besselEnergy → 0 ≤ S.mainEnergy → 0 < S.N →
  0 < S.unipCovolume → 0 < S.b → 1 ≤ S.b → 0 < .card (S.reducedImage besselS) → p) : p := by
  have : 0 ≤ S.mainEnergy := div_nonneg (by simp) (mul_pos S.besselDegree_pos (mass_pos ..)).le
  apply h <;> simp [this, besselEnergy, field, two_le_iff,
    Nat.Prime.ne_one, unipCovolume_pos] <;> grind [S.pow_le_tailScale NeZero.one_le, thousand_le_b]

lemma IsNear.norm_frameProducts_le [S.IsAdmissible] : S.IsNear γ → ‖Φ w (S.frameProducts γ a b)‖ ≤
  S.b ^ (5 * 𝔰.n ^ 2) | ⟨y, h, k⟩ => (by
  obtain ⟨t⟩ := norm_realFrameGram_le_mul (S.ratToInf γ w) (y w) a b, S.thousand_le_b
  simp [boxedPoints, boxSize, forall_and, -forall_fin_succ'] at *
  nth_grw 1 [← one_le_abs_kappa, h.1, k.1, N_le] at t <;> simp [field] at *
  grw [t]; gcongr <;> nlinarith [S.ϱ_le])

lemma IsNear.norm_map_leadingMinor_le [S.IsAdmissible] (h : S.IsNear γ) : ‖Φ w
  (leadingMinor (S.frameProducts γ) l)‖ ^ 2 ≤ S.b ^ (11 * 𝔰.n ^ 3) := have := S.one_le_b; by
  grw [← place_apply, leadingMinor, det_le (by bound [h.norm_frameProducts_le]), factorial_le_pow]
  simp; grw [l.is_le, S.succ_le_b, sq]; simp; gcongr; nlinarith [S.ϱ_le, l.2]

include k

lemma termsOver.eq_and_mem_classUnip₀ [S.IsAdmissible]
    {d} (h : u ∈ S.termsOver c r d) (e : frameImage γ =
  frameImage u.1.1) : c' = d ∧ γ⁻¹ * u ∈ S.classUnip₀ c' := eq_and_mem_classUnip_of_besselS (by
  simp [mem_besselS_iff_frameImage, ↓frameImage_inv_mul_eq_iff.2 e]) (by simpa using! mul (inv k) h)
    |>.imp_right fun b ↦ ⟨b, b.1, fun i _ ⟨a, h⟩ ↦ h ▸ congrFun₂ (frameImage_inv_mul_eq_iff.2 e) ..⟩

lemma isIntegral_frameProducts : IsIntegral ℤ (S.frameProducts γ a b) := by
  simpa using congr($frameGram_termPosition a b).subst
    (S.isUnimodular_latMiddle.splitGram.isIntMatrix.mul (termsOver.isIntMatrix_termPosition k) _ _)
