/- GID: D5/S3/Zeros/GRH/New/SiegelWeil/AuxPairVanishing
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/SiegelWeil/AuxPairVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.SiegelWeil.AuxPairVanishing. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/SiegelWeil/AuxPairVanishing.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.AlgebraicPartDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Non-lifts sharing one Hecke root have zero theta periods (see
New.Rows.MemberOrthogonality).

This file: Vanishing descent for one level datum passes to all data, via reflection sums. -/

open Classical Finset Fint Gf IsLocalRing Kf MatMul Matrix Space Valued

variable {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] {O : AuxPair E r n}

lemma AuxPair.exists_atPlace_eq {m} [Fintype m] g : g ∈ (supportedOn m O.places).map (.pi fun i ↦
  atPlace (O.placeAt i)) := Subgroup.pi_mem_of_mulSingle_mem g fun i ↦
  ⟨atSplit (O.apart.2 i i) (g i), by simp; grind [atPlace_atSplit_of_ne],
  Function.eq_update_iff.2 (by simp_all [atPlace_atSplit_of_ne, O.apart.1.ne, O.apart.2])⟩

attribute [local simp] prod_eq_zero_iff vecMulVec_apply MulChar.star_apply' AuxPair.resDetDatum
  AuxPair.auxLevelChar add_mul residueDatum inclMatrix mul_assoc starRingEnd_apply matToVec v_inv

lemma AuxPair.exists_annihilator_or_congr_inclMatrix {ι : r ↪ n} {w : FinPlace E} (x :
  Matrix n r (LocField w)) (h : HasLeftInv x) : ∃ l :
  Matrix n n _, l.map (LocInt w).subtype * x = 0 ∧ ((∀ c, residue _ ∘ l c ∘ ι = 0) → ∃ a : GL r
  (LocField w), ∀ i j, v ((x * a.1) i j - inclMatrix (LocInt w) ι i j) < 1) := by
  obtain ⟨b, -, h⟩ := (isValuationPair_valuationSubring (LocInt w)).exists_isPrimitiveMatrix_mul h
  obtain ⟨P, ⟨L, e⟩, rfl⟩ := by simpa [← mul_inv_eq_iff_eq_mul_of_invertible] using
    h.exists_map_subtype_eq
  use P * L - 1, (congr($Matrix.map_mul * _).trans (Matrix.mul_assoc ..)).symm.trans (by simp
    [e]), fun H ↦ (isUnit_of_mapMatrix _ (.of_mul_eq_one_right _ (ext
    (by simpa [mul_apply, funext_iff] using H <| ι ·)))).elim fun T e ↦ ⟨b * .map (algebraMap ..) T,
    by simpa [↓Matrix.mul_assoc, e, mul_apply] using!
    (residue_eq_iff_valuation_sub_lt_one.1 <| congrFun₂ (funext H) · ·)⟩

seal CStarMatrix in
/-- Let k ∈ K₀ have reductions τ_j with ι×ι block s_j and ι-columns (at M), ι-rows (at Q) zero
outside that block. On y of the pair's level and character, π(k)y is ∏_j ψ_j⁻¹(det s_j)
times `AuxPair.chosenGLRep` of (s_j)_{j∈M} applied to y. -/
lemma AuxPair.smul_chosenGLRep_eq {V} [AddCommGroup V] [Module ℂ V] {π :
  Representation ℂ _ V} y {k τ} (s : ∀ _, GL r _) (e : reduceFamily O.placeAt k = τ) (H : ∀ j,
  cond j.isLeft (τ j).1 (τ j).1ᵀ * inclMatrix _ O.incl = inclMatrix _ O.incl * cond
  j.isLeft (s j).1 (s j).1ᵀ) : (∏ j, (O.ψ _)⁻¹ (s j).1.det) • (O.chosenGLRep π (s <| .inl ·) y).1 =
  π k y := set_option backward.isDefEq.respectTransparency false in (smul_smul ..).trans (by
  let S := firstBlockHom _ O.incl (s <| .inl ·)
  have := by simpa [entrywise] using (H <| .inr ·)
  have T j : S (.inr j) = 1 := rfl
  simpa [*, MulChar.inv_apply_eq_inv', submatrix, MulChar.apply_eq_zero_iff] using! congr(π
    (liftResidue S) $(levelSpace_levelOf_apply y.2 ((liftResidue S)⁻¹ * k) ⟨S⁻¹ * τ,
    Sum.rec (by simpa [↓mem_stabilizer_col_iff, S, firstBlockHom, -inclMatrix,
    inv_mul_eq_iff_eq_mul_of_invertible] using (H <| .inl ·)) (by simp +contextual
    [mem_rangeParabolic_iff, *, eq_comm])⟩ (by simp [reduceFamily_liftResidue, e]))).symm)

lemma AuxPair.isAutomorphic_star_algFormCoeff u (y : O.FormV) :
  (stdSpace ..).IsAutomorphic (star (algFormCoeff 1 u y.1)) := (isAutomorphic_algFormCoeff y.1).conj

attribute [-simp] Sum.elim_inl Sum.elim_inr map_sub submatrix_id_mul

/-- Suppose ψ ≠ 1 at each place of Q, the reflection sums of all nonzero rows at M kill y, and
the conjugate u-coordinate of y has zero descent to W for all data P ⊗ Υ. Then its descents
vanish for all data vacuum off M, Q and conjugates. -/
lemma AuxPair.descentsVanish_of_reflectionSum [WeilData E]
    {y} u (hQ : ∀ i, O.ψ (O.twistPlace i) ≠ 1)
    (hM : ∀ i (v : ∀ _, _), v i ≠ 0 → O.formAction.asAlgebraHom (piTensorElem fun i ↦
  reflectionSum (O.ψ _) (v i)) y = 0) (h0 : ∀ P, lift (pairThetaKer _ _ O.a 1).swap (integrated _
  (polyVector _ P) O.auxDatum.1) (star (algFormCoeff 1 u y.1)) = 0) : DescentsVanish O.W (stdSpace E
  n) O.a O.places.conjClosureᶜ (star (algFormCoeff 1 u y.1)) := fun f hf ↦ funext fun g ↦ by
  obtain ⟨hy, hS⟩ := isAutomorphic_star_algFormCoeff u y,
    (by clear * -; grind [O.apart.2] : O.places.IsConjDisjoint)
  let K := (pairThetaKer O.W (stdSpace _ n) O.a 1).swap
  refine (K.exists_clm_lift hy.mem_rapidFunctions).elim fun L hL ↦
    hL .. ▸ ext_integrated _ hf fun P q h ↦ ?_
  erw [_root_.smul_apply, map_smul, map_smul, (?_ : finVec q = _), ← projOn_vacElem,
    ← name_schrodingerAct_boxIndicator hS (y := q), ← hL, mul_eq_zero]
  swap; ext : 3 <;> simp +contextual [finVec, idem_apply, h]
  let D := ((K.liftBilin ∘ₗ (integrated _ P ∘L .apply ℂ _ (vacElem _)).1 ∘ₗ name _ O.places).compr₂
    (.proj g)).compl₂ (.codRestrict _ ((starLinearEquiv ℂ).1 ∘ₛₗ (algFormCoeff 1 u).domRestrict _)
    (isAutomorphic_star_algFormCoeff u · |>.mem_rapidFunctions))
  refine .inr (IsSchwartzBruhat.mem_of_cosets (S := O.places) (D.flip y).ker fun _ _ ↦
    ⟨⊤, by simp, fun t z _ _ ↦ ?_⟩)
  let C z := D (cosetIndicator O.places t z)
  have lv (A B : ∀ j, Matrix n r (LocInt (O.placeAt j))) (s : ∀ j, GL r (ResField (O.placeAt j))) z
    q (X : ∀ j, let τ := (1 + A j * (B j)ᵀ).map (residue _); (s j).1 =
      (1 + (B j)ᵀ * A j).map (residue _) ∧ τ.submatrix O.incl O.incl = (s j).1 ∧
      ∀ b ∉ Set.range O.incl, ∀ a, cond j.isLeft τ τᵀ b (O.incl a) = 0) (H : ∀ j a b, t⁻¹.1 _ * (q
    (a, b) _ - ((1 + A j * (B j)ᵀ).map Subtype.val * (vecToMat z).map (evalAt (O.placeAt j))) a b) ∈
    LocInt _) : C q ((∏ j, (O.ψ _)⁻¹ (s j).1.det) • O.formAction (s <| .inl ·) y) = C z y := by
    obtain ⟨k, hk, e⟩ := exists_atPlace_eq fun j ↦
      .map (LocInt _).subtype (.mk'' _ ((det_one_add_mul_comm
      ..).substr ((isUnit_of_mapMatrix (residue _) ⟨_, (X j).1⟩).map detMonoidHom)))
    lift k to Kf E n using (mem_Kf_iff_of_supportedOn hk).2 fun _ ⟨j, h⟩ ↦ h ▸ ⟨_, congr($e.symm j)⟩
    refine .trans ?_ (mul_one g ▸ K.lift_equivariant hy _ k ..).symm
    erw [pairWeil_integrated_fin _ _ _ _ 1 k.1, pairWeil_name_of_mem hS (one_mem _) k.2]
    refine congr(lift _ (integrated _ _ (name _ _ $(funext fun x ↦ if_congr ?_ rfl rfl) $(by
      simp [↓pairWeil_eq_smul_of_projOn_eq ⊤]))) (star $((congrArg _
      (smul_chosenGLRep_eq y _ (funext (reduceAt_eq_of_atPlace congr($e ·))) fun j ↦
      (mul_inclMatrix ..).trans <| ((eq_inclMatrix_mul_iff _).2 (X j).2.2).trans ((X j).2.1 ▸ by
      cases j <;> rfl))).trans (funext (algFormCoeff_algFormRep u k)))) _)
    simpa [↓mulVec_smul, ↓mulVec_sub, ↓mulVec_add, ← smul_add] using ((mulVec_mem_integralBox
      (g := (G.onHom (s' := 1) ((g.1, 1), k)).2⁻¹) (by simp [mem_Kf_iff.1])).trans
      (add_mem_cancel_right (y := t⁻¹.1 • (x - q)) (x := t⁻¹.1 • (q - matToVec (k.1.1.1 * vecToMat
      z))) fun a ↦ idem_mul_mem_Ô.2 (Set.forall_mem_range.2 fun j ↦ congr(_ * (_ -
      $(Matrix.map_mul.trans congr(($e j).1 * _)) _ _) ∈ _).mpr (H ..)))).symm
  let d j a : LocInt (O.placeAt j) :=
    ite (j.isRight ∧ ∀ b, a ≠ O.incl b) ⟨_, (v_uniformizer _).trans_le (by tauto)⟩ 1
  choose! l hl a ha using fun j ↦ exists_annihilator_or_congr_inclMatrix (ι :=
    O.incl.trans .inl) ((diagonal (d j · |>.1) * (vecToMat z).map (evalAt (O.placeAt j))).fromRows
    (scalar r (t.1 _))) ⟨fromCols 0 (scalar r (t⁻¹.1 _)), by simp⟩
  set_option backward.isDefEq.respectTransparency false in
    let m c j := residue _ ∘ l j c ∘ .inl ∘ O.incl
    by_cases! N : ∀ j c, m c j = 0
    · obtain ⟨⟨A, hA', rfl⟩, _⟩ := exists_atPlace_eq a,
        isSchwartzBruhat_residueDatum O.resDetDatum O.apart.2
      let Ψ x := residueDatum _ O.resDetDatum ((G.onHom (s' := 1) ((g.1, A), 1)).2⁻¹.1.1 *ᵥ x)
      have H q (hq : Ψ q ≠ 0) : Ψ q * C q y = C (matToVec (inclMatrix _ O.incl * A⁻¹.1.1)) y := by
        obtain ⟨hx, m, p⟩ := by simpa [Ψ, -Sum.forall] using hq
        let Z i : Matrix n r (LocInt _) := (⟨_, hx i · ·⟩)
        refine .trans (by simp [*, Ψ, ← Pi.one_def]) (lv (Z · - inclMatrix _ O.incl) (fun _ ↦
          inclMatrix _ O.incl)
          (Sum.rec 1 (.mk'' _ <| MulChar.apply_ne_zero_iff.1 <| p ·)) _ q ?_ fun j a b ↦ ?_)
        · rintro (j | j) <;> simp +contextual [entrywise, ↓m, @eq_comm n, show _ = (vecToMat q *
            A.1.1).map (residueOrZero ∘ evalAt _) _ _ from (residueOrZero_coe (Z ..)).symm]
        rw [vecToMat_matToVec, Matrix.map_mul, map_inclMatrix, ← Matrix.mul_assoc, mul_inclMatrix,
          submatrix_map, show submatrix _ _ _ = Z j by simp [entrywise]]
        erw [← Matrix.map_mul (f := evalAt _)]; simp [vecToMat]
      have h i a := by simpa [atPlace, ← Matrix.map_mul] using ha i (N i) (.inl a)
      have I i a b : (vecToMat z * A.1.1) a b _ ∈ LocInt _ := if c : d i a = 1 then by
        simpa [c] using! v.map_add_le (h i a b).le (inclMatrix (LocInt _) O.incl a b).2 else by
        simpa [d, (ite_ne_right_iff.1 c).1] using! v_uniformizer_inv_mul_le_one_iff.2 (h i a b)
      have J i a b (c : d i a = 1) := (residueOrZero_coe ⟨_, I ..⟩).trans
        (residue_eq_iff_valuation_sub_lt_one.2 (by simpa [c] using h i a b))
      have hz : Ψ z ≠ 0 := by simp [Ψ, ← ext_iff, *, d, submatrix, ← diagonal.eq_1]
      obtain ⟨F, hF, h⟩ := IsSchwartzBruhat.eq_sum_cosetIndicator (S := O.places) (Ψ :=
        Ψ) t fun x _ z h ↦ residueDatum_congr _ fun i p ↦ by simpa [↓← mulVec_sub, mul_apply,
        ← evalAt_apply] using (v.map_sum_lt one_ne_zero fun c ↦ by simpa [field] using!
        (mul_lt_of_le_one_of_lt (idem_mul_mem_Ô.1 (h _) _ ⟨i, rfl⟩) (ha i (N i) (.inr c) _)))
      have e := congrFun (h0 P) (g * A)
      erw [lift_mul_right, hL, pairWeil_integrated_fin (k := A), auxDatum, Subtype.coe_mk,
        liftFn_eq_residueDatum places_levelModulus, places_levelModulus, pairWeil_name_on hS hA'
        (by simp), map_smul, map_smul, ← hL, (congr(D.flip y $(.trans (by simp [Ψ]) h)) : lift
        .. = _), map_sum, sum_eq_card_nsmul fun q ↦ (map_smul ..).trans ∘ H q ∘ hF q, ← H z hz] at e
      exact (by simpa [hz] using e :).resolve_left (hz <| h ▸ · ▸ by simp)
    have H c s (h : ∀ j, ∃ x, (s j).1 = 1 + vecMulVec x (m c j)) := (skolem.1
      (residue_surjective.comp_left.exists.1 <| h ·)).elim fun x hx ↦ lv (fun _ ↦ inclMatrix _
      O.incl) (fun j ↦ vecMulVec (l j c ∘ .inl * d j) (x j)) s z z (by simp +contextual [entrywise,
      hx, m, d, ← residueOrZero_coe ⟨(uniformizer _).1, _⟩, @eq_comm n]) fun j a b ↦ by
      simp [mul_vecMulVec, mul_apply, ← mul_sum, vecToMat, apply_ite, by
        simpa [mul_apply, add_eq_zero_iff_eq_neg, diagonal, vecToMat] using congrFun₂ (hl j) c b]
      simpa [mul_comm (t.1 _)⁻¹] using ((_ *ᵥ x j) a * l j c (.inr b)).2
    obtain ⟨i | i, c, hv⟩ := N
    · exact (smul_eq_zero_iff_right (card_ne_zero.2 ⟨1, by simp⟩)).1 ((sum_eq_card_nsmul fun s h ↦
        .trans (by simp; tauto) (H c (Sum.rec s 1) (Sum.rec (mem_filter.1 h).2
        (by simp)))).symm.trans
        (by simpa [reflectionSum, asAlgebraHom_eq_sum, ↓prod_ite_zero, sum_ite] using
        congr(C z $(hM i (m c <| .inl ·) hv)) :))
    obtain ⟨⟨t, ht⟩, b, hb⟩ := (O.ψ (O.placeAt (.inr i))).ne_one_iff.1 (hQ i), Function.ne_iff.1 hv
    have e : (1 + vecMulVec (Pi.single b ((t.1 - 1) / m c _ b)) (m c (.inr i))).det = t := by
      simp [vecMulVec_eq Unit, det_one_add_mul_comm, mul_div_cancel₀ _ hb]
    refine eq_zero_of_mul_eq_self_left ht (.trans ?_ (H c (Pi.mulSingle _ (.mk'' _ (e ▸ t.isUnit)))
      fun j ↦ (eq_or_ne j (.inr i)).elim (· ▸ ⟨_, by simp; rfl⟩) (by simp [·])))
    simp +contextual [prod_eq_single i, e, ← Pi.one_def, C]
