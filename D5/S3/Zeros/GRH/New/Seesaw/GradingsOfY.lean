/- GID: D5/S3/Zeros/GRH/New/Seesaw/GradingsOfY
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/GradingsOfY
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.GradingsOfY. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/GradingsOfY.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.DoubleLiftValue
import D5.S3.Zeros.GRH.Lib.SiegelWeil.RallisInner.SharpData
import D5.S3.Zeros.GRH.New.Exchange.AlgebraicPartDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

This file: Levels, finite data, Weil actions and tame characters of the row lifts. Defines the
indefinite chain of theta lifts, its levels, character and equivariance law. Gradings of the spaces
Y_k and evaluated finite data for each pair. -/

noncomputable section

open Fin Kf MatMul Matrix NeZero

section

variable {P} {D : Data P} (ϑ : D.TameChar) (j) (s : D.G) (N T : Type) [Fintype N] [Fintype T] {E}
  [Field E] [CMType E] (X : LevelPlaces E)

/-- The inclusion of the basis index set of Y_j in that of Y_{j+1} as the first summand. -/
abbrev Data.inclY (j : ℕ) : D.Y j ↪ D.Y (j + 1) := .inl

lemma Data.liftTamePart_eq_of_mem_Q (w : ϑ.Q) : D.liftTamePart ϑ j w =
  ϑ.ψ w := by simp [liftTamePart, IsChosen, D.levelNorm_mem_and_notMem_of_mem_Q ϑ]

/-- The subgroup of the lattice stabiliser K₀ for Y_j of elements reducing to 1 at every chosen
place, those over g and those of the twist ϑ. -/
abbrev Data.levelY := levelOf (n := D.Y j) (D.levelPlaces ϑ).placeAt ⊥

lemma Data.levelY_le_chosenLevel : levelY ϑ j ≤ chosenLevel :=
  Subgroup.map_mono fun _ e ↦ congr(($e <| .inl ·))

/-- The finite datum on Hom(Y_j, Y_{j+1}) named, on the vacuum, by the indicator of the block
inclusion (1;0) modulo the product of the chosen places and those of Q. -/
def Data.upsilonY := delta% vacuumDatum (D.spaceY j) (D.spaceY _) (D.𝔪 ϑ 1)
  (Pi.single (inclMatrix _ (D.inclY j)) 1)

/-- The theta kernel of the pair (Y_j, Y_{j+1}), with the characters νυ^⌊n/2⌋, νυ^⌊n'/2⌋ for the
ranks n, n' of Y_j, Y_{j+1} and ν = μ⁰_{j+1}ϑ^{j+1}. -/
abbrev Data.thetaKernelY := pairThetaKer (D.spaceY j) (D.spaceY (j + 1))
  (rankTwist (D.chainChar ϑ (j + 1)) (D.Y j)) (rankTwist (D.chainChar ϑ (j + 1)) (D.Y (j + 1)))

/-- The tame part of the character μ⁰_{j+1}ϑ^{j+1} of lift j + 1, a family of characters of the
residue fields. -/
abbrev Data.liftTame := D.liftTamePart (.pow ϑ (j + 1)) (j + 1)

/-- Let k, k' in K₀ for Y_j, Y_{j+1} have reductions g, g' with g'(1;0) = (1;0)g at all chosen
places and places of Q. Then (k, k') multiplies `Data.upsilonY` by ∏ ψ(det g')/ψ(det g) over
these places, ψ = `Data.liftTame`. -/
lemma Data.thetaKernelY_omega_upsilonY {k k' g g'} (e : reduceFamily _ k = g) (e' :
  reduceFamily (D.levelPlaces ϑ).placeAt k' = g') (h : ∀ x, (g' x).1.submatrix id (D.inclY j) =
  inclMatrix _ (D.inclY j) * (g x).1) : (thetaKernelY ϑ j).ω ((1, k), 1, k') (upsilonY ϑ j) =
  (∏ x, liftTame ϑ j _ (g' x).1.det / liftTame ϑ j _ (g x).1.det) • upsilonY ϑ j := by
  subst_vars; simp [upsilonY, ← modDatum_vacVector]
  rw [pairWeil_modDatum_single _ _
    ((Modulus.matrix_ext_modulusResidue (D.levelPlaces ϑ).apart.1).2 fun x ↦ ?_)]
  simp [D.hasWeight_liftChar.hasWeight_rankTwist.apply_det_eq_prod (auxPair ..).apart.1
    (AuxPair.tame_eq_one _), -_root_.mul_inv_rev]; rfl
  simp [← map_inv, map_inclMatrix]
  erw [← h, ← mul_inclMatrix]; simp [reduceFamily]

/-- The number, from 0 to j, of the block containing an index: 0 on R and l on the l-th copy of
T. -/
def blockNumber {R T} : ∀ j, BlockIndex R T j →
  Fin (j + 1) | 0 => 0 | j + 1 => castSucc ∘ blockNumber j ⊕ᵥ fun _ ↦ last _

lemma blockNumber_eq_zero {R T} j : ∀ i, @blockNumber R T j i = 0 ↔ i ∈ Set.range
  (BlockIndex.firstBlock j) := j.rec (by tauto) fun _ _ ↦ show ∀ i, _ ↔ ∃ _, Sum.inl _ = i by simpa!

instance Data.instNonemptyY : Nonempty (D.Y j) := .map (BlockIndex.firstBlock j) inferInstance

/-- The forms on U(Y_j) of the type given by the parameter `Data.paramY` and the signs of Y_j,
with the Petersson product. -/
abbrev Data.FormY := (D.spaceY j).Form (typeKernel (D.paramY j) _)

/-- The datum φ ⊗ Υ on Hom(Y_j, Y_{j+1}) of lift j + 1: the joint harmonic at infinity and the
finite datum `Data.upsilonY`. -/
abbrev Data.datumY := ((D.spaceY j).hom (D.spaceY (j + 1))).integrated
  (polyVector _ (D.gridHarmonic 0 false true j false 0 j 0 _)) (upsilonY ϑ j)

/-- For j < m the datum of lift j + 1 satisfies `IsArrow` both ways: the kernel has moderate
growth, forms are rapid, the lift sends forms on Y_j to forms on Y_{j+1}, and the descent
sends conjugate forms on Y_{j+1} to conjugate forms on Y_j. -/
lemma Data.isArrow_datumY {j} (hj : j < D.m) : IsArrow (thetaKernelY ϑ j) (typeKernel (D.paramY j)
  _) (typeKernel (D.paramY _) _) (datumY ϑ j) ∧ IsArrow (thetaKernelY ϑ j).swap
  (star (typeKernel (D.paramY _) _)) (star (typeKernel (D.paramY j) _)) (datumY ϑ j) :=
  (D.paramsCorrespond_grid false _ _ _ _ rfl).isEdge_jointHarmonic.isArrow _ _ (upsilonY ..).2

/-- Lift j + 1, from forms on Y_j to forms on Y_{j+1}: the theta lift with datum `Data.datumY`,
multiplied by the index [K₀ : 𝒥_j], 𝒥_j = `Data.levelY`. -/
def Data.liftY : D.FormY j →ₗ[ℂ] D.FormY (j + 1) :=
  (stdLevelIndex (levelY ϑ j) : ℂ) • formLift (thetaKernelY ϑ j) _ _ (datumY ϑ j)

/-- The subgroup of ∏ GL(Y_m mod w), over the chosen places, of elements that are 1 at the
places above g and block upper triangular at Q. -/
def Data.lastResLevel : Subgroup (∀ x, GL (D.Y D.m) (ResField ((D.levelPlaces ϑ).placeAt x))) :=
  .pi .univ fun x ↦ parabolic (blockNumber _) ⊓ bif x.isLeft then ⊥ else ⊤

/-- The composite of the first j theta lifts along Y₀, …, Y_j for the twist ϑ, from forms of
principal level g on Y₀ to forms on Y_j. -/
def Data.liftChainY : D.principalForms (D.spaceY 0) →ₗ[ℂ] D.FormY j :=
  compUpTo (liftY ϑ) j ∘ₗ (D.principalForms _).subtype

/-- The chain of lifts ι_μ, on all forms of principal level g on Y₀. -/
def Data.ι := (Space.toAlgForm _ D.isHCParam_Y).1 ∘ₗ liftChainY ϑ _

/-- If k ∈ K₀ on Y_m is block upper triangular at all chosen places, with block 0 equal to s ∈ 𝖦
above g, then k·ι_μ y = ∏_w ∏_{l≥1} μ_{l,w}(det k_{ll}) · ι_μ(s·y). -/
lemma Data.algFormRep_iota y k g (e : reduceFamily (D.levelPlaces ϑ).placeAt k = g) (h : ∀ x, (g
  x).1.BlockTriangular (blockNumber _)) (h' : ∀ x, (g (.inl x)).1.submatrix (BlockIndex.firstBlock
  _) (BlockIndex.firstBlock _) = (s x).1) : algFormRep _ _ k.1 (ι ϑ y) = (∏ x, ∏ l : Fin _, liftTame
  ϑ l _ ((g x).1.toSquareBlock (blockNumber _) l.succ).det) • ι ϑ (D.principalRep _ s y) := by
  erw [← Space.toAlgForm_formRep D.isHCParam_Y, ← map_smul]; apply congrArg
  have a := @isArrow_datumY _ D ϑ; generalize D.m = j at *
  induction' j with j ih
  simpa [prod_univ_zero] using! (apply_liftResidue_eq y k (funext (Units.ext <| (e ▸ h') ·))).symm
  have b x l : ((g x).1.toBlocks₁₁.toSquareBlock (blockNumber j) l).det = _ :=
    (det_submatrix_equiv_self · ((g x).1.toSquareBlock (blockNumber _) l.castSucc)) (.trans
    (.ofInjective _ (Sum.inl_injective.comp (by simp))) (.subtypeEquivRight (by simp! [eq_comm])))
  have t x : (g x).1.toBlocks₁₁.BlockTriangular (blockNumber j) := by tauto
  have d x := by simpa [prod_univ_castSucc, ← b, ← by simpa using (t x).det_fintype] using (h
      x).det_fintype
  have u x := left_ne_zero_of_mul (d x ▸ (g _).det_ne_zero)
  have e' := reduceFamily_liftResidue (.mkOfDetNeZero _ <| u ·)
  erw [LinearMap.map_smul, (a .refl).1.formRep_formLift, pairWeil_integrated_fin,
    thetaKernelY_omega_upsilonY _ _ e' e fun x ↦ (eq_inclMatrix_mul_iff .inl).2
    (·.rec (by simp) fun _ _ _ ↦ h _ (castSucc_lt_last _)),
    ih _ _ e' t h' (a <| Nat.lt_succ_of_lt ·)]
  simp [prod_univ_castSucc, *, MulChar.apply_eq_zero_iff, smul_comm (Nat.cast _), mul_smul]; rfl

/-- The homomorphism `Data.lastResLevel` → ℂ sending κ to the product, over w chosen or in Q and
blocks l ≥ 1, of μ_{l,w}(det κ_{ll}), μ_{l,w} the tame part of μ⁰_l ϑ^l. -/
def Data.lastLevelChar : lastResLevel ϑ →* ℂ := ∏ x, ∏ l : Fin _,
  (liftTame ϑ l _).1.comp (detMonoidHom.comp ((Units.coeHom
  _).comp ((blockHom _ l.succ).comp ((Pi.evalMonoidHom _ x).restrict fun _ ↦ (· x ⟨⟩ |>.1)))))

/-- The map ι_μ with its target restricted to the space of algebraic forms on Y_m
of level `Data.lastResLevel` and its character `Data.lastLevelChar`. -/
def Data.iotaAtLevel : D.principalForms (D.spaceY 0) →ₗ[ℂ] LevelPlaces.LevelForm _ _ (lastLevelChar
  ϑ) D.columnsY (D.lastEntry D.m) :=
  (ι ϑ).codRestrict _ fun y ↦ mem_levelSpace.2 fun k ↦ have h := (mem_levelOf.1 k.2).2
  by simpa [lastLevelChar] using! algFormRep_iota ϑ 1 y _ _ rfl (h · ⟨⟩ |>.1) fun x ↦
    (h (.inl x) ⟨⟩).2 ▸ submatrix_one_embedding _

/-- For s in 𝖦, a chosen element of K₀ on Y_m reducing to diag(s, 1) at the places above g and
to 1 at Q. -/
def Data.groupLift :=
  liftResidue (firstBlockHom (D.levelPlaces ϑ) (@BlockIndex.firstBlock _ (Fin D.t) D.m) s)

/-- The chain of lifts ι_μ commutes with the group 𝖦: ι_μ(s·y) is the right translate of ι_μ(y)
by the finite element `Data.groupLift` attached to s. -/
lemma Data.iota_principalRep y : ι ϑ (D.principalRep _ s y) =
  algFormRep _ _ (groupLift ϑ s) (ι ϑ y) := by
  let g := firstBlockHom (D.levelPlaces ϑ) (@BlockIndex.firstBlock _ (Fin D.t) D.m) s
  have e {x a b} (h : blockNumber .. ≠ 0) : g x a b = ite _ 1 0 :=
    x.rec (fun _ ↦ (extendGL_spec ..).2 a (by rwa [← blockNumber_eq_zero]) b) (by tauto)
  simpa [show ∀ x l, (g x).1.toSquareBlock (blockNumber _) (.succ l) = 1 by simp_all [← ext_iff,
            toSquareBlock_def]] using! (algFormRep_iota ϑ s y _ _ (reduceFamily_liftResidue g) (by
    grind only [BlockTriangular]) fun _ ↦ (extendGL_spec ..).1).symm

lemma card_parabolic_blockNumber j : ∃ k, ∀ R [CommRing R], Nat.card (parabolic (R :=
  R) (@blockNumber N T j)) = .card (GL N R) * .card (GL T R) ^ j * .card R ^ k := j.rec ⟨0, by simp!
  [parabolic, BlockTriangular]⟩ fun j ⟨k, H⟩ ↦ ⟨k + Fintype.card (T × BlockIndex N T j), fun R ↦
  have e (u : parabolic (R := R) (@blockNumber N T j.succ)) := (ext fun _ _ ↦ u.2 (by simp!) :
    u.1.1.toBlocks₂₁ = 0) ▸ fromBlocks_toBlocks _
  have d u := isUnit_fromBlocks_zero₂₁'.1 ⟨_, (e u).symm⟩
  by simp [Nat.card_congr (β := parabolic (blockNumber j) × _ × GL T R) (.mk (fun u ↦
       (⟨(d u).1.unit, fun _ _ ↦ (u.2 ·)⟩, _, (d u).2.unit)) (fun (x, y, z) ↦
       ⟨.mk'' (fromBlocks x.1 y 0 z) (by simp!), by simpa! [parabolic, BlockTriangular,
       lt_asymm] using! x.2⟩) (by ext : 2; use e ·)), H, Matrix, Nat.card_pi]
     ring⟩

lemma LevelPlaces.ker_reductionK₀_eq {N : Type} [Fintype N] : (X.levelModulus 1).reductionK₀.ker =
  (reduceFamily (n := N) X.placeAt).ker := by ext; simp [Units.ext_iff.trans
  ((X.levelModulus 1).matrix_ext_modulusResidue X.apart.1), funext_iff]; rfl

lemma LevelPlaces.card_levelModulus_resRing e : Fintype.card (X.levelModulus e).ResRing =
  (∏ i, (X.chosenPlace i).q) ^ e * ∏ i, (X.twistPlace i).q :=
  Fintype.card_eq_nat_card.trans (by simp [levelModulus] : Ideal.absNorm _ = _)

lemma LevelPlaces.card_GL_levelModulus : Fintype.card (GL N (X.levelModulus 1).ResRing) =
  stdLevelIndex (levelOf (n := N) X.placeAt ⊥) := by
  simp [levelOf, ← ker_reductionK₀_eq]; erw [Modulus.stdLevelIndex_levelOfSubgroup (H := ⊥)]; simp

end

variable {P} {D : Data P}

/-- For k < m, a chosen grading of Y_k as X_k plus a string of length m − 1 − k, with the
indexing `Data.indexEquivY` and the constant c = −(ȷgϖ)⁻¹, ϖ a generator of the different. -/
def Data.gradingY k (hk : k ≤ 2 * D.ϱ + 1 := by omega) := (⟨D.indexEquivY k (by grind), by grind
  [spaceY], by simp [ne], -(WeilData.j * (D.gProd * P.ϖ D.s) : D.E)⁻¹, by
    simp [ne, ne_zero_of_differentIdeal_eq_span P.different_eq_span_varpi,
      ← coe_star_ringOfIntegers, P.star_ϖ]⟩ : Grading (D.spaceY k) D.N _ _)

/-- For M = m, the presentation of Y_M as a space of rank n_M − 1 in grade 0 plus a string of
length 0. -/
def Data.lastGrading {M} (e : D.m = M) : Grading (D.spaceY M) D.N (D.InitIndex M) 0 := e ▸ by
  use .trans (.sumEmpty ..) D.lastIndexEquiv.symm,
    D.isStd_spaceY.std_induction (funext₂ ?_), ?_, 1 <;> simp [gradedGram, ne]

/-- The finite evaluation `ArrowPair.finEval` of the pair of arrows Y_{2i} → Y_{2i+1} → Y_{2i+2}:
for the middle pair if i < ϱ, the last pair if i = ϱ, and 0 beyond. -/
def Data.pairEvalY i := by refine if _ : i < D.ϱ then (middlePair (D.gradingY (2 * i))
  (D.gradingY (2 * i + 1)) (D.gradingY (2 * i + 2)) ?_ ?_ ?_).finEval else if _ : D.ϱ =
  i then (lastPair (D.gradingY _) (D.gradingY _) (D.lastGrading ?_) ?_ ?_
  congr($D.π_mul_star) ?_).finEval else 0 <;> (try simp [gradingY]) <;> grind

/-- The natural number g^{f𝗇²}, with g = g₀g₁, f the number of infinite places, 𝗇 = `Data.n` m. -/
abbrev Data.cutBound := D.gProd ^ (D.f * D.n D.m ^ 2)

/-- For a tuple y of finite adelic group elements of the Y_k, the family of finite data Υ on
Hom(Y_k, Y_{k+1}) moved by y under the twisted Weil action. -/
def Data.translatedUpsilon ϑ (y : ∀ _, _) k :=
  liftWeilFin (D.chainChar ϑ (k + 1)) (y k, y _) (upsilonY ϑ k)

/-- The finite evaluation `Data.pairEvalY` of pair i on the data of lifts 2i+1 and 2i+2, moved by
(y_{2i}, y_{2i+1}) and (y_{2i+1}, y_{2i+2}) as in `Data.translatedUpsilon`. -/
def Data.evaluatedDatum ϑ y i :=
  D.pairEvalY i (arrowProduct (translatedUpsilon ϑ y _).1 (translatedUpsilon ϑ y _).1)
