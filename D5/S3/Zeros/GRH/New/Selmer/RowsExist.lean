/- GID: D5/S3/Zeros/GRH/New/Selmer/RowsExist
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/RowsExist
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.RowsExist. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RowsExist.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.RowDimension
import D5.S3.Zeros.GRH.New.Selmer.LabelledColumns
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

Galois representations of theta lifts as an irreducible block plus a string. The Galois
representation of each eigenform in a space of theta lifts has the trace of a twisted block, with
the block in a finite set independent of the twist, plus a string of powers of the inverse
cyclotomic character, and the block-plus-string shape follows from the unramified theta
correspondence. Tame inertia at a level prime makes the block irreducible mod ℓ, as Ribet's method
needs, by the known device of metacyclic tame inertia, used here with two level primes to cover
every ℓ. Related work: Rallis, Langlands' functoriality and the Weil representation, 1982;
Khare–Larsen–Savin, Functoriality and the inverse Galois problem, 2008;
Arias-de-Reyna–Dieulefait–Shin–Wiese, Compatible systems of symplectic Galois representations III,
2015.

This file: A twist-free row gives traces of lifts; every good eigensystem has a row. -/


open Matrix Polynomial Fintype Filter Data AutChar Classical LinearMap Space Subtype Finset
variable {P} {D : Data P} {r n} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {ℓ} [ThePrime ℓ]
  (ι : PadicIso ℓ)

/-- Given an auxiliary pair O, with character μ, labels c apt for the trivial twist, and a
`IsLabelledColumn` R with system b whose shifted jumps obey `IsRowType`, there is one row T serving
every twist ϑ: forms lifting b with character μϑ satisfy `HasRow`.

Galois representations of theta lifts: irreducible block plus string. -/
lemma exists_row_for_all_twists {c} (hO : IsApt O c 1) b J R (h :
  IsLabelledColumn (m := r) O (card r) J c ∅ R) (s : ∀ g, (mostFrobeniiAt _ g).Tendsto (ιℓ <|
  b ·.w 1) (nhds (R g).1.trace)) (hJ : IsRowType D (card r) O.rankDiff fun σ ↦
  (J σ).map (· - ((card r - O.rankDiff) / 2 - cmSign σ * O.weight (.mk σ)))) : ∃ T, HasRow O b T :=
  have ⟨N', a, ha⟩ : 2 ∣ card n ∧ 2 ∣ (card r - O.rankDiff : ℤ) := by grind [IsApt]
  ⟨_, ⟨_, (h.twist_avatar O.hasWeight.inv 0 a (by grind [IsApt]) hO (hO.tame_part_eq.rec
    (by aesop))).isRow hO (by simpa [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, cmSign,
    apply_ite, ha, sub_eq_add_neg] using hJ)⟩, @fun ϑ V _ _ S h₃ hy f U σ ↦ by
  simp [trace_eq_neg_charpoly_nextCoeff (S _).1, nextCoeff, O.rank_lt.ne_zero, TameChar.invAvatar]
  apply tendsto_nhds_unique (.congr' (mem_inf_of_left _)
    (.neg (.mul _ (U.tendsto_charpoly_coeff ..)))) (.add (.mul _ (.mul _ (s σ))) _)
  any_goals apply tendsto_mostFrobeniiAt (g := σ) _
  filter_upwards [eventually_mostFrobenii (f.2.and (eventually_notMem_star_notMem ℓ
    (.image V.placeAt ⊤))), (ϑ.hasWeight.inv.toAlgebraic 0 0).eventually_avatar_frob,
    (O.hasWeight.inv.toAlgebraic 0 a).eventually_avatar_frob] with x ⟨u, o, _, hl⟩ d d'
  choose _ z s E v using u x.prime_q
  have k T :=
    (smul_left_inj f.1).1 ((isSphericalWith_of_heckeSplit z v).2 T ▸ (hy _ ‹_› (by aesop)).2 T)
  obtain ⟨m, i, l⟩ := (u x.prime_q).2.isMonicOfDegree f.1, k 0, congr(-deriv ($(k ·)) 0)
  simp (disch := fun_prop) only [heckePolyEval, trivialHecke, smul_eq_mul, deriv_fun_mul,
    deriv_fun_finsetProd, deriv_fun_sum, deriv_fun_pow] at i l; simp [E, ← sum_mul, zero_pow_eq,
    O.rank_lt.pos, isMonicOfDegree_iff, sum_range_succ', hO.odd.1.pos] at i l m
  simp [↓d, ↓d', E, chiOneInv_spec x.isPlaceOver hl 1, x.isFrob, HasWeight.toAlgebraic,
    cycInv_eq_of_isFrob x hl, field, HeckeChar.atUnif,
    heckeCoeff, h₃, ← ha, ← i, m, AutChar.frobValue, Nat.sub_sub_self O.rank_lt.pos, l, zpow_sub₀,
    _root_.spaceChar_rankTwist N', ← map_natCast ιℓ, FinPlace.q_eq_sqrt_sq, pow_sub₀, O.rank_lt.le]
  ring⟩

/-- If the system p of Hecke eigenvalues occurs in a nonzero good form on W_m, then for 1 ≤ j ≤ m
some T is a row for the untwisted j-th auxiliary pair and p, serving all twists (`HasRow`).

Galois representations of theta lifts: irreducible block plus string. -/
lemma exists_hasRow_auxPair {p} (H : D.goodForms (D.spaceW D.m) ⊓ D.eigenPart _ p ≠ ⊥) (j :
  D.LiftIndex) : ∃ T, HasRow (D.auxPair .one j) (p ⟨·, ·⟩) T := by
  obtain ⟨⟨z, ⟨hz, hp⟩, z0⟩, d, κ, hκ⟩ := (Submodule.ne_bot_iff _).1 H,
    exists_isHCParam_of_hasGap D.hasGap_signsY_paramW
  let L := (AlgForm ..).subtype ∘ₗ ((D.spaceW D.m).toAlgForm hκ).1
  have ρ g y : L _ = rightRegular ℂ _ _ g (L y) := congr($(toAlgForm_formRep hκ ..).1)
  obtain ⟨K : L z ∈ levelSpace (rightRegular ℂ ..) D.chosenLevel, hf : _ ∈ forms _ (d, κ), c : ∀ x,
    (ResField ((auxPair ..).chosenPlace x))[X], hc, hl⟩ := by simp [← ρ, mem_levelSpace.1 z.2],
    (toAlgForm _ hκ z.1).2, D.goodTupleFamilies.exists_ne_zero_of_sum_ne_zero
    (by simpa [e₀] using ((D.isCentralProj_e₀.1.map _).mem_range_iff.1 hz).trans_ne z0)
  have E := D.isEigenform_of_hasHeckePolyAt (by simpa [L]) fun w a ↦ ⟨levelSpace_anti
    (maxCompactAt_le_levelOf a.2) K, (p ⟨w, ·⟩), rfl, fun i ↦ map_heckeSplit _ i L ▸ by
    simp [by simpa [heckeOperator, a, Subtype.ext_iff] using (Submodule.mem_iInf _).1 hp (w, i)]⟩
  obtain ⟨a, R, h⟩ := isApt_auxPair D 1 j hc, (sphericalCompat_std ofNonempty hf E).1
  apply exists_row_for_all_twists ι a
  convert isLabelledColumn_of_hasProductLabel a hf E h (fun _ _ b ↦
    levelSpace_anti (maxCompactAt_le_levelOf b) K) fun i ↦ HasParahoricType.hasProductLabel (e :=
    .refl _) (b := 0) (s := 0) (ψ := 1) (L.domRestrict _) (fun _ ↦ by simp [L])
    (hl <| piTensorElem_apply_eq_zero i ·) ⟨by simp, fun k _ _ e ↦ by
    simpa [-GeneralLinearGroup.val_det_apply] using ρ .. ▸ congr(L $(apply_liftResidue_eq _ _
      ((reduceFamily_atSplit ..).trans (congrArg _ (Units.ext e))))).symm⟩ nofun nofun
  simp
  simpa [Nat.sub_sub_self D.r_odd.pos, trace_eq_neg_charpoly_coeff, ↓card_rowIndex] using
    (h.tendsto_charpoly_coeff · D.r.pred |>.neg)
  simp [↓card_rowIndex, auxPair, AuxPair.rankDiff, jumps]
  convert isRowType_auxPair j.2 using 3 with σ q i
  have := hκ.eq_hcParameter (.mk σ) (D.basisVec q)
  simp [cmSign, apply_ite, hcParameter, diagramWeight_apply, ↓card_rowIndex] at *; clear * - this
    i; grind [Data.basisVec, paramW, decrPosition_paramW]
