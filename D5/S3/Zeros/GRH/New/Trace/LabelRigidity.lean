/- GID: D5/S3/Zeros/GRH/New/Trace/LabelRigidity
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Trace/LabelRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Trace.LabelRigidity. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Trace/LabelRigidity.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.GaloisRep.LabelUniqueness
import D5.S3.Zeros.GRH.New.Exchange.ChainNorms
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Good forms on different unitary groups have equal traces (see New.Trace.GoodFormTransfer).

This file: A Hecke eigensystem meets at most one primitive cuspidal type at a chosen place. -/

set_option backward.isDefEq.respectTransparency false

/-- Let w in M be split, u of level `AuxPair.levelGroup` and character `AuxPair.auxLevelChar`,
π(k)u = kf for k in GL_n(E_w), F(g) = `AuxPair.chosenGLRep`(g at w)u. Then `HasParahoricType` holds:
integral k preserving the ι-span mod w, with ι-block x, give kf = ψ_w(det x)⁻¹F(x). -/
lemma Data.hasParahoricType_chosenGLRep {P} (D : Data P) {n} [Fintype n] {r} [Fintype r] {O :
  AuxPair D.E r n} {S : Submodule ℂ (_ → WeylIndex n O.κ → ℂ)} {π : Representation ℂ _ S} {u i v f}
  (e : ∀ k, (π (atSplit v k) u.1).1 = rightRegular ℂ _ _ (atSplit v k) f) :
  HasParahoricType f v O.incl (if · ∈ Set.range O.incl then 0 else 1) (O.ψ _)⁻¹ (s := 1) 1 fun g ↦
  (O.chosenGLRep π (Pi.mulSingle i g) u).1.1 := by
  use by simp, fun k g a b ↦ e _ ▸ congr($(O.smul_chosenGLRep_eq u (Sum.rec (Pi.mulSingle i g) 1)
    (reduceFamily_atSplit (.inl i) k) (Sum.rec (fun j ↦ ?_) (by simp))).1).symm.trans (by
    simp +contextual [Finset.prod_eq_single i, -Matrix.GeneralLinearGroup.val_det_apply]; rfl)
  obtain rfl | _ := eq_or_ne j i <;> simp [*]
  erw [← b, mul_inclMatrix, eq_inclMatrix_mul_iff]
  aesop

/-- For every eigensystem p and every chosen place x over g, at most one primitive label occurs
at x in the p-part of the forms on V (`Data.occurringLabels`). -/
abbrev Data.HasRigidLabels {P} (D : Data P) {s} (V : Space D.E D.RowIndex s) := ∀ p x,
  (D.occurringLabels V p x).Subsingleton

/-- For 1 ≤ j ≤ m, the space W_j satisfies `Data.HasRigidLabels`: at each chosen place over g, at
most one primitive label of degree r occurs in each p-part of the forms on W_j. -/
lemma Data.hasRigidLabels_spaceW {P} (D : Data P) (j : D.LiftIndex) : D.HasRigidLabels (D.spaceW
  j) := fun p x ↦ D.occurringLabels_subsingleton _ (D.auxLift_injective .one) (fun _ h _ a ↦
  D.lifts_auxLift _ h _ a.1 (by simp_all [auxPair, levelPlaces, IsSplitOffLevel]; tauto)) x 1 _
  (fun _ ↦ by simpa [auxLift_principalRep] using! D.hasParahoricType_chosenGLRep fun _ ↦ rfl)
  (fun _ ↦ by lia) (by simpa using! D.omega_zpow_mul_pow_eq_one _ rfl) (by simp)

/-- Y₀ satisfies `Data.HasRigidLabels`: for each eigensystem p and chosen place above g, the
idempotent e_c kills the p-part for all but at most one primitive label c of degree r. -/
lemma Data.hasRigidLabels_spaceY_zero {P} (D : Data P) : D.HasRigidLabels (D.spaceY 0) :=
  fun p x ↦ by
  refine D.occurringLabels_subsingleton _ (D.iotaAtLevel_injective 1) (D.exists_isSphericalWith_iota
    p).choose_spec x _ 1 (fun y ↦ ⟨blockNumber_eq_zero _, fun k g h e ↦ congr($(D.algFormRep_iota _
    _ y _ _ (reduceFamily_atSplit (.inl x) k) (Sum.rec ?_ (by simp)) ?_).1).trans
    (by rw [Finset.prod_eq_single (.inl x)] <;> simp_all [-Finset.prod_mul_distrib,
    Matrix.toSquareBlock, Matrix.toSquareBlockProp, -Matrix.GeneralLinearGroup.val_det_apply];
        rfl)⟩) (fun a b h ↦ by_contra fun e ↦ ((D.omega_zpow_ne_one (a - b)) _).2 x.2.2.1 ?_)
    (by simp) fun _ ↦ D.omega_zpow_mul_pow_eq_one _ (one_pow _)
  iterate 2 exact (by cases eq_or_ne · x <;> aesop)
  simp_all [TameChar.pow, (1 : D.MFoldTwist).1.ψ_eq_one x.2.1 nofun, chosen, sub_eq_add_neg,
    zpow_add]
