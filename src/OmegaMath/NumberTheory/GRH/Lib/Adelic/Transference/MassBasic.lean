import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdditiveCharBasic
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Reduction.FirstMinimum
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Reduction.MahlerForms
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Transference theorem: covering radius of a lattice against the first minimum of its
dual (known result; see Lib.Adelic.QuotientMeasure.Unimodular).

Part of: Mass formula for unimodular hermitian lattices: ratio of consecutive masses (known result;
see Lib.SiegelWeil.Mass.MassRatio).

Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski theorems
(known result; see Lib.Adelic.Reduction.Defs).

This file: Trace dual of a unimodular hermitian lattice; short bases by transference. Effective
bounded fundamental domain for a CM field in its adeles. Mahler-Godement compactness criterion for
unitary groups; finite class number for definite spaces. Mass is positive; weighted count of
norm-one vectors equals mass of rank one less. -/

open Fintype Function Matrix NumberField PiLp QuotientGroup RealInnerProductSpace Space Submodule U

section

variable {E n : Type*} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ}
  (V : Space E n s)

namespace Space

attribute [local simp] Prod.fst_sum Prod.snd_sum vecAtPoint dotProduct stdForm

/-- Covering radius bound: for nonzero d in the different of E, every u in ℂ^{fn} is within
(2fn)²/λ of a point of 2d⁻¹L. Here L is the lattice of V, embedded by `Space.archCoords`, λ =
`Space.firstMinimum`, and f counts infinite places. -/
lemma exists_norm_sub_archCoords_le {d} (hd : d ≠ 0) (h : d ∈ differentIdeal ℤ (𝓞 E)) u :
    ∃ a ∈ V.baseLattice, ‖u - V.archCoords ((2 / d.val) • a)‖ ≤
  (2 * (numInfPlaces E * card n)) ^ 2 / V.firstMinimum := by
  simpa [← mem_toAddSubgroup] using
    weak_transference_covering_radius (V.baseLattice.map (.mk' (V.archCoords <| (2 / d.val) • ·)
    (by simp))).toIntSubmodule V.firstMinimum_pos (u := u) fun x hx o ↦ by
   let t := V.x⁻¹.1ᴴ *ᵥ (fun w ↦ x ⟨w, ·⟩ / star (Φ w d), 0)
   have l ξ : ⟪x, V.archCoords ((2 / d.val) • ξ)⟫ = ∑ w, 2 * ((star (toAdele ∘ ξ) ⬝ᵥ t).1
     w).re := by simp [archCoords, -vecAtPoint, -dotProduct]; simp [t, ↓← star_mulVec_dotProduct,
     inner, Finset.mul_sum, sum_prod_type, map_ofNat, division_def, -Finset.sum_add_distrib]; grind
   have ⟨a, c⟩ := (mulVec_surjective_iff_isUnit.2 V.isUnit_J).exists.1 (Classical.skolem.1 fun i ↦
     exists_eq_emb_of_trace_rat (z := (t i).1) fun b ↦
     (V.exists_smul_mem_baseLattice (Pi.single i (star b))).elim fun M
     h ↦ (hx _ ⟨_, h.2, map_nsmul ..⟩).imp' (↑· / M) (by simp +contextual [*, apply_ite]))
   refine have k : ‖x‖ = ‖V.archCoords (d.val • a)‖ := ?_; k ▸ V.firstMinimum_le ?_ (by aesop)
   simp [norm_eq_of_L2, archCoords, -vecAtPoint, -algebraMap_smul]; congr! with ⟨w, i⟩
   simpa [t, map_J, ← mul_assoc, ← conjTranspose_mul, ← (diagonal _).mulVec_mulVec, field, hd,
    abs_unit_intCast] using congrArg norm (by simp [mulVec, c] :
    ((V.x.1ᴴ *ᵥ t) i).1 w = ((V.x.1ᴴ *ᵥ V.J.map toAdele *ᵥ toAdele ∘ a) i).1 w)
   exact fun i ↦ by simpa [↓map_smulₛₗ] using forall_ψf_mul_eq_one.1 (fun u hu ↦ by
    simpa [apply_ite] using isClosed_property (by simpa [-coe_units_inv, mulVec] using!
      ((MulAction.surjective V.xFin⁻¹).denseRange.comp (.piMap fun _ ↦
      denseRange_algebraMap_finAdele) (by fun_prop)))
      (isClosed_imp (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ô) (isClosed_eq (f :=
      (ψf E <| star · ⬝ᵥ _ ∘ _)) (by fun_prop) continuous_one)) (fun ξ h ↦
      .trans (by simp [↓← toAdele_apply_snd, ↓← stdForm_vecAtPoint])
      ((ψf_eq (star ξ ⬝ᵥ V.J *ᵥ a)).trans (fourierChar_eq_one.2 ((hx _ ⟨ξ, (h · ⟨⟩), rfl⟩).imp (by
      simp [*, ↓trace_eq_sum_Φ, eq_comm]))))) (Pi.single i (star u)) (by
      simp [star_mem_Ô, apply_ite, *])) _ h

section

variable {E n : Type*} [Field E] [NumberField E] [Fintype n]

instance : NeZero (differentIdeal ℤ (𝓞 E)).absNorm :=
    ⟨Ideal.absNorm_eq_zero_iff.1.mt differentIdeal_ne_bot⟩

variable (E n) in
/-- The natural number 6N(fn)², f the number of infinite places of E and n the rank: the
constant in the bound for short bases. -/
noncomputable abbrev shortBasisConst N := 6 * N * (numInfPlaces E * card n) ^ 2

end

/-- For a natural number N ≠ 0 in the different of E, the lattice of V contains a basis of E^n of
vectors of length at most 6N(fn)²/λ; f counts the infinite places, λ = min(1, first minimum of the
lattice of V).

Known result: Transference theorem: covering radius of a lattice against the first minimum of its
dual. -/
lemma exists_short_basis {N} [NeZero N] (h : ↑N ∈ differentIdeal ℤ (𝓞 E)) : ∃ Y : GL n E, ∀ j,
    Y.1.col j ∈ V.latticeBall (shortBasisConst E n N / V.firstMinimum) :=
  exists_GL_col_mem_of_span _ fun y _ ↦ (V.exists_smul_mem_baseLattice
  y).rec fun M ⟨o, e⟩ ↦ (smul_mem_iff _ (mod_cast o : (M : E) ≠ 0)).1 (mod_cast by
  generalize M • y = y at e; cases isEmpty_or_nonempty n; simp [Subsingleton.elim y 0]
  have r : 0 < shortBasisConst E n N / V.firstMinimum / 6 := by simp [firstMinimum_pos, NeZero.pos]
  have ⟨k, f⟩ := Archimedean.arch (‖V.archCoords y‖ - shortBasisConst E n N / V.firstMinimum) r
  induction' k with k ih generalizing y
  aesop
  refine (V.exists_norm_sub_archCoords_le NeZero.out h ((N : ℝ)⁻¹ • V.archCoords y)).elim fun a ⟨u,
    g⟩ ↦ have :=
      norm_le_insert (V.archCoords y) ((2 : ℝ) • V.archCoords a); (sub_mem_iff_left _ (nsmul_mem (ih
    a u ?_) 2)).1 (ih _ (by bound) ?_) <;> simp [div_eq_inv_mul, -smul_add, ← smul_sub, ↓norm_smul,
   map_inv_natCast_smul _ E ℝ, two_smul, inv_mul_le_iff₀, NeZero.pos, mul_smul] at * <;> nlinarith)

/-- Let N ≠ 0 be a natural number in the different of E, g in G_f. Some Y in GL_n(E) has columns in
the lattice L_g of I_n (g⁻¹Y is integral) and entries of absolute value ≤ 6N(fn)² at every complex
embedding, f the number of infinite places. -/
lemma exists_short_basis_stdSpace {N : ℕ} [NeZero N] (h : ↑N ∈ differentIdeal ℤ (𝓞 E)) (g :
  Gf E n) : ∃ Y : GL n E, IsIntMatrix (Ô E) (↑↑g⁻¹ * Y.1.map (↑)) ∧
  ∀ (φ : _ →+* ℂ) i j, ‖φ (Y i j)‖ ≤ shortBasisConst E n N := by
  choose Y a H using ((stdSpace ..).move (1, g)).exists_short_basis h
  use Y, ?_, fun φ i ↦ ?_ <;> try grw [← one_le_firstMinimum, ← norm_apply_le _ (.mk φ, i)] at H
  all_goals simp_all [IsIntMatrix, baseLattice, archCoords, ↓move_vecAtPoint, entrywise,
    ← InfinitePlace.apply]

end Space

variable (V : Space E n s) (E₁ : Type _) [Field E₁] [CMType E₁]

/-- Let d ≠ 0 lie in the different of the CM field E with f infinite places. For z ∈ ℂ^f and a
finite adele y there is a ∈ E with y − a integral and |z_w − a_w| ≤ (2f)²|d_w| at every
infinite place w. -/
lemma exists_rat_near_of_mem_differentIdeal {E} [Field.{0} E] [CMType E] {d} (hd : d ≠ 0)
    (hN' : d ∈ differentIdeal ℤ (𝓞 E)) (z : _ → ℂ) y : ∃ a, y - algebraMap E _ a ∈ Ô E ∧ ∀ w, ‖z w
    - Φ w a‖ ≤ (2 * numInfPlaces E) ^ 2 * ‖Φ w d‖ := (exists_sub_mem_Ô y).elim fun r o ↦
    ((stdSpace E Unit).exists_norm_sub_archCoords_le hd hN' (.toLp _ fun (w, _) ↦
  (z w - Φ w r) / Φ w d)).elim fun a ⟨e, h⟩ ↦
  ⟨r + 2 * _, by simpa [Space.vecAtPoint, sub_sub] using sub_mem o (nsmul_mem e 2 ()), fun w ↦ by
  grw [← one_le_firstMinimum, ← norm_apply_le _ (w, ())] at h
  simpa [archCoords, Space.vecAtPoint, div_mul_eq_mul_div, ← sub_div, hd, div_le_iff₀,
    sub_sub] using h⟩

lemma Space.exists_short_basis_matrix : ∃ c : ℕ, ∀ g, ∃ Y : GL n E, ∀ j, Y.1.col j ∈
  (V.move g).latticeBall (c * V.height g) := ⟨_, fun _ ↦ exists_short_basis _ (Ideal.absNorm_mem _)⟩

/-- For a compact set C of adelic matrices and a subgroup H of GL_n(E) there is a compact K ⊂ G
such that every g with x g⁻¹ x⁻¹ r ∈ C for some r in H has x⁻¹γx·g ∈ K for some γ in U(J)(E)
∩ H. -/
lemma Space.exists_isCompact_of_bounded_frame {C} (c : IsCompact C) (H : Subgroup _) :
    ∃ K, IsCompact K ∧ ∀ g (r : H), (V.toRatCoords g⁻¹).1.1 * r.1.1.map toAdele ∈ C → ∃ γ,
  V.ratEmbed γ * g ∈ K ∧ γ.1 ∈ H := let f (r : H) := r.1.1ᴴ * V.J * r.1
  ⟨_, (G.isClosedEmbedding_mat.isCompact_preimage ((c.smul V.x.inv).mul
    ((instLatMatrix𝔸RatM.finite_preimage (c.image_auto fun c ↦ cᴴ * V.J.map toAdele * c)).image
    fun T ↦ ((f.invFun T).1.map toAdele).inv * V.x).isCompact)).inv, fun g r h ↦
    ⟨⟨_, gram_mul_of_gram_eq (f.invFun_eq ⟨r, rfl⟩) (gram_inv_of_gram_eq rfl)⟩, ⟨_, ⟨_, h,
    rfl⟩, _, ⟨f r, ⟨_, h, by simp [↓U.gram_invariant, f]⟩, rfl⟩, by simp [ratEmbed, toRatCoords,
    G.mat, mul_assoc, U.map]⟩, (_ * r⁻¹).2⟩⟩

/-- Mahler's criterion: for every real R there is a compact C ⊂ G such that each g in G of
height ht(g) ≤ R has a translate γg in C with γ ∈ Γ.

Known result: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski
theorems. -/
lemma Space.mahler_criterion R : ∃ C, IsCompact C ∧ ∀ g, V.height g ≤ R → ∃ γ ∈ V.Γ, γ * g ∈
    C := (V.exists_isCompact_of_bounded_frame
  ((isCompact_closedBall_prod_integral _).matrix.smul V.x) ⊤).imp fun _ ↦ .imp_right fun k g a ↦
  (V.exists_short_basis_matrix.choose_spec g).rec fun Y h ↦ (k g ⟨Y, ⟨⟩⟩ ⟨_, fun i j ↦ ⟨by
  simpa [pi_norm_le_iff_of_nonempty] using! fun w ↦ (norm_apply_le _ (w, i)).trans (by grw [(h j).2,
    a]), (h j).1 i⟩, .symm (congr($(mul_assoc ..) * _).trans (mul_assoc ..))⟩).rec (by tauto)

/-- If all signs of V are equal, G is compact modulo Γ: there is a compact C ⊂ G such that every
g has γg in C for some γ in Γ. -/
lemma Space.exists_isCompact_of_definite (h : ∀ i j, s i = s j := by simp) : V.Γ.Cocpt := by
  peel V.mahler_criterion 1; grind [height, inv_le_one₀, one_le_firstMinimum]

lemma Space.exists_isCompact_finitePart (V : Space E n 1) : V.Γf.Cocpt :=
  V.exists_isCompact_of_definite.imp' _ fun _ ↦
  .imp (·.image_auto (·.2)) (· ⟨1, ·⟩ |> fun ⟨_, ⟨_, rfl⟩, a⟩ ↦ ⟨_, ⟨_, rfl⟩, _, a, rfl⟩)

end

variable {E n : Type*} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ} (V : Space E n s) (E₁ : Type _)
  [Field E₁] [CMType E₁] {n : Type*} [Fintype n] (V : Space E n 1) {E' : Type _} [Field E']
  [CMType E']

instance Space.hasFiniteType_of_isLevel {K} [l : IsLevel K] : HasFiniteType V.Γf K :=
  V.exists_isCompact_finitePart.elim fun _ ⟨c, h⟩ ↦ ⟨(finite_quotient_image_of_isCompact l.2
  c).of_surjective (⟦·.1.out⟧) (Quot.ind (h · |> fun ⟨_, o, e⟩ ↦
  ⟨⟨_, _, e, rfl⟩, .symm ((DoubleCoset.eq ..).2 ⟨_, o, (mk_out_eq_mul ..).imp' _ (⟨·.2, ·⟩)⟩)⟩)),
  (ConjAct.toConjAct ·⁻¹ |> l.isCompact.preimage_smul |>.inter_left
    V.Γf.isClosed_of_discreteTopology
  |>.finite (.mono ⟨mod_cast inferInstance⟩ inf_le_left)), l.2, l.isCompact⟩

lemma mem_stdRatPoints_iff {g} : g ∈ (stdSpace E' n).Γf ↔ ∀ i j,
  g.1 i j ∈ (algebraMap E' _).range := ⟨(·.choose_spec
  ▸ by simp), fun h ↦ (mem_range_map (by simp) (algebraMap E' _).injective isUnit_one (by simp)
  (Matrix.ext (h · · |>.choose_spec))).imp fun | γ, ⟨_, rfl⟩ => Subtype.ext (stdSpace_embFin γ)⟩

lemma classSum_stdRatPoints_eq_mass κ [Fintype κ] : classSum stdRatPoints (Kf E₁ κ) 1 =
  mass E₁ (card κ) := by apply classSum_card_orbit (Gf ..) (Gf ..) () (U.reindex
  (equivFin κ).symm).toMonoidHom ⊤ <;> simp [mem_Kf, ↓mem_stdRatPoints_iff, SetLike.ext_iff,
  Injective, reindex_equiv (equivFin κ)] <;> tauto

/-- The mass of the genus of the standard lattice of rank l is positive, for every l. -/
lemma mass_pos E [Field E] [CMType E] l : 0 < mass E l := classSum_one_pos

/-- For stably unramified E, the class sum for I_{j+1} at level K_0 of the number of vectors y
in E^{j+1} with y*y = 1 and g⁻¹y integral equals mass_j. -/
lemma classSum_card_norm_one_eq_mass [StablyUnram E₁] j :
  classSum stdRatPoints (Kf E₁ (Fin j ⊕ Unit)) (fun g ↦
  ↑{y : _ → E₁ | star y ⬝ᵥ y = 1 ∧ ∀ i, (g⁻¹.1.1 *ᵥ (y ·)) i ∈ Ô E₁}.ncard) = mass E₁ j := by
  have C {R} [CommRing R] [StarRing R] (u : U 1) := (congrArg (@toBlocks₂₂ (Fin j) Unit _ _ R)
    (u.2.trans fromBlocks_one'.symm)).trans (toBlocks_fromBlocks₂₂ ..)
  refine classSum_card_orbit (Gf ..) (Gf ..) _ (blockSumOne.comp (.inl ..)) _ (by simp [U.sum,
    Injective, Gf, Units.ext_iff]) (SetLike.ext fun g ↦ .trans (show (g * 1).1.1ᵀ (.inr ()) = _ ↔ _
    by simp [funext_iff, ← ext_iff]; tauto) ((mem_range_sum (by simp)).1 isUnit_one).symm) ?_
    ?_ (mod_cast fun g ↦ (algebraMap E₁ _).injective.comp_left.injOn.ncard_image) fun g y ↦ ⟨?_, ?_⟩
  iterate 2 simp [↓mem_stdRatPoints_iff, mem_Kf, U.sum, SetLike.ext_iff]
  rintro ⟨y, ⟨_, h'⟩, e⟩
  have ⟨γ, hγ⟩ := witt exists_isUnit_sub_star (by simp) isUnit_one ⟨_,
    C 1⟩ (.of_ne_zero (x := y) (by aesop)) ((C 1).trans (by aesop))
  cases congr($((mul_one _).trans (stdSpace_embFin (γ * 1 :))).1ᵀ _).trans (congr(_ ∘ $hγᵀ ()).trans
    e)
  have ⟨k, s, t⟩ := witt_Ohat_of_orthonormal (C 1) (C (_ * (_ * 1))) (by simp [IsIntMatrix])
    (fun _ ↦ (congr(_ *ᵥ $e) ▸ h') ·)
  use ⟨⟨_, _, rfl⟩, rfl⟩, ⟨k, s⟩, congr($tᵀ _)
  rintro ⟨⟨⟨_, γ, ⟨⟩⟩, H⟩, k, hk⟩
  cases H.symm.trans congr($((mul_one _).trans (stdSpace_embFin γ)).1ᵀ _)
  exact ⟨_, ⟨by simpa using! congr($(C γ) 0 0), (congr($hk ·).subst ((k * 1).2.isIntMatrix _ _))⟩,
    rfl⟩
