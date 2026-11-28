/- GID: D5/S3/Zeros/GRH/New/Seesaw/PairTensorData
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/PairTensorData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.PairTensorData. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/PairTensorData.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.SquareLawFourier
import D5.S3.Zeros.GRH.Lib.GLn.Dual.DualWeights
import D5.S3.Zeros.GRH.New.Seesaw.GradingsOfY
import D5.S3.Zeros.GRH.New.Columns.ChainValuation
import D5.S3.Zeros.GRH.New.Exchange.GridModuli
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Integral branching pairing for interlacing weights; definite periods as class sums, norm
bound. Names for spaces, characters, levels, lifts and descents on the two grids. -/

noncomputable section

open Matrix Finset Fintype PolyRep Space Real
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {κ κ' e e'}

attribute [local grind] hcParameter diagramWeight_apply Ioo_eq_empty

/-- For weights of parameters l′ (rank n+1) and −l (rank n), l, l′ interlacing, some integer
matrix B pairs them invariantly under diag(g,u) up to ∏det(u_τ)^{N_τ}, with explicit bounds
on N and B, and periods over definite U(n) are constants times means of this pairing. -/
lemma exists_branching_pairing [Nonempty n] {l l' s t r} {σ : _ ⊕ Unit ≃ n'} (hσ :
  (s ⊕ᵥ r) ∘ σ.symm = t) (ht : t = 1) (h : IsHCParam κ e l') (h' : IsHCParam κ' e' (-l)) (hi :
  ∀ w x, (#{j | x < l' w j} - #{i | x < l w i} : ℤ) ∈ Icc 0 1) : ∃ B : Matrix _ _ ℤ, (∃ N : _ → ℤ,
  (∀ (S R : Type) [CommRing S] [StarRing S] [Field R] [CharZero R] (f : _ → S →+* R) g u v' v,
  weylRep κ' e' (g.1.map <| f ·) *ᵥ v' ⬝ᵥ B.map (↑) *ᵥ weylRep κ e ((U.block σ (g, u)).1.map <|
  f ·) *ᵥ v = (∏ τ, (u.1.map (f τ)).det ^ N τ : Rˣ) * v' ⬝ᵥ B.map (↑) *ᵥ v) ∧ (∀ τ, (N τ).natAbs ≤
  boxes κ (card n') + (e τ).natAbs) ∧ ∀ M, boxes κ (card n') ≤ M → ∀ v' v, ‖v' ⬝ᵥ B.map (↑) *ᵥ v‖ ≤
  ((M ^ M) ^ 3 :) * √(weylNormSq v') * √(weylNormSq v)) ∧ ∀ g, ∃ c, ∀ (V : Space E n s) [V.IsStd]
  (η : AlgForm n _ e') (φ : AlgForm _ _ e) u K [IsLevel K], ∫ x, ofAlgForm (-l) s η x *
  ofAlgForm l' t φ (G.reindex σ hσ (.sum (x, 1, u)) * (g, 1)) ∂V.quotMeasure = c / stdLevelIndex K *
  classIntegral stdRatPoints K fun h ↦ η.1 h ⬝ᵥ B.map (↑) *ᵥ φ.1 (U.block σ (h, u)) := by
  obtain ⟨hn, ⟨⟩, κ₀, e₀, k⟩ := by simpa using card_congr σ.symm, (by simp_all [funext_iff,
    reindex_equiv σ] : (s, r, t) = 1),
    exists_isHCParam_of_hasGap (by simpa using h'.hasGap · 0 |>.neg)
  let d τ q := (hcParameter κ₀ e₀ (card n) τ q - hcParameter κ e (card n') τ q.succ) / 2
  have J w q (o : q.succ ≤ card n) : d w q ∈ Icc 0 ↑(κ w q.succ) := by
    obtain ⟨⟨i, a⟩, ⟨j, _⟩, _, c⟩ := k.exists_decrPosition_eq w o,
      h.exists_decrPosition_eq w (.trans o hn.ge), h.exists_decrPosition_eq w (o.trans_lt hn.ge)
    rcases a.2.2 (l' w j), c.2.2 (l w i), hi w (l' w j),
      hi w (l w i); grind -linarith [decrPosition]
  obtain ⟨⟨A, L, hv, -, hA⟩, b, b1, b2, b3⟩ := exists_dual_pairing_of_isHCParam k h',
    exists_branching_matrix (fun _ ↦ σ) κ₀ 0 e e₀ (funext₂ fun w q ↦ (κ w q).sub_add_min_cancel
    (d w (q - 1)).toNat) (by grind -linarith) nofun (by grind -linarith [card_pos_iff])
  use A * b, ⟨_, by introv _; rw [map_intCast_mul_mulVec, mulVec_mulVec v, b1 _ (g.1.map <|
    f ·) (f · |> u.1.map |>.det)] <;> simp [map_intCast_mul_mulVec, ← mulVec_mulVec, Units.smul_def,
    ← ext_iff, PolyRep.blockScalar, reindex_equiv σ]; tauto, fun τ ↦ ?_, fun M m _ _ ↦ ?_⟩, fun g ↦
    (integral_algFormCoeff_blockEmb (stdSpace ..) (by simp) b3 (_ ∘ₗ conjWeylRep κ e g⁻¹) _).imp
    fun _ H V _ η φ _ _ _ ↦ by simpa [algFormCoeff, map_intCast_mul_mulVec,
    IsStd.eq_stdSpace] using! H φ _ _ _ _ (isAutomorphic_algFormCoeff η) (hv _ _)
  grw [Int.natAbs_add_le, ← FitsRanks.refl.sum_diagramWeight_eq_boxes,
    ← single_le_sum _ (mem_univ (τ, ⟨0, by omega⟩))] <;> simp; simp [diagramWeight_apply]; bound
  grw [map_intCast_mul_mulVec, (hA _).choose_spec.2, gramForm_apply,
    le_sqrt_of_sq_le (posDef_cauchy_schwarz weylGram_posDef ..),
    ← weylNormSq, ← weylNormSq, (hA _).choose_spec.1, b2] <;> simp [field, sqrt_sq_eq_abs]
  grw [← boxes, ← m, ← FitsRanks.refl.sum_diagramWeight_eq_boxes,
    ← @FitsRanks.sum_diagramWeight_eq_boxes n, sum_le_sum]
  intro (w, q); grind -linarith [J w _ (Nat.sub_one_lt_of_lt _)]; grind

namespace Data

variable {P} {D : Data P} (ϑ : D.MFoldTwist) {z : Bool} {i j a b} (c :
  Bool) (l : ℕ) (n : Type) [Fintype n]

/-- The hermitian space at node (i, j) of grid z, offset o: for o = 0, Y_j at (0, j) in V and Y₀
⊕ ⟨1⟩ at (0, 0) in Z; for o > 0, at (0, 0) the opposite of that for o − 1; otherwise
`signedSpace`. -/
def gridSpace : ∀ o z i j, Space D.E _ (D.gridSigns z o i j)
  | 0, true, 0, 0 => ((D.spaceY 0).sum (signedSpace ..)).reindex (.refl _) D.gridSigns_zero.symm
  | 0, false, 0, j => D.spaceY j | _ + 1, _, 0, 0 => (gridSpace ..).neg | _, _, _, _ =>
    signedSpace ..

/-- The pair of kernels `kernelPair` for the parameter and signs at the node (i, j) of grid
z. -/
def gridKernel z i j := kernelPair (D.gridParam z 0 i j) (D.gridSigns z 0 i j)

/-- The forms on the unitary group of the node (a, b) of grid z whose type has the doubled
parameter −`Data.gridParam`. -/
abbrev GridForm z a b := (gridSpace ..).Form (D.gridKernel z a b true)

/-- The character μ⁰_{l+1} ϑ^{l+1} υ^⌊|n|/2⌋ if c is true, and the untwisted μ⁰_{l+1} υ^⌈|n|/2⌉
if c is false. -/
def gridChar := D.liftChar (bif c then ϑ.pow (l + 1) else .one) (l + 1) *
  WeilData.upsilonU1 ^ ((Fintype.card n + (!c).toNat) / 2)

/-- The family ω_w^{l+1} ϑ_w^{l+1} of residue field characters if c is true, ω_w^{l+1}
otherwise: the tame part of μ_{l+1}⁰ϑ^{l+1}, respectively μ_{l+1}⁰. -/
abbrev gridTamePart := D.liftTamePart (bif c then ϑ.pow (l + 1) else .one) (l + 1)

/-- The order of the general linear group over the residue ring of `Data.triangleModulus`, of the
rank of the space at node (0, n) of grid z. -/
abbrev triangleOrder z ϑ n := Fintype.card (GL (D.GridIndex z 0 n) (D.triangleModulus z ϑ).ResRing)

/-- Nodes of the two grids: triples (z, a, b), standing for the space V_{a,b} if z is false and
Z_{b,a} if z is true. -/
abbrev Node := Bool × ℕ × ℕ

/-- The basis index set `Data.GridIndex` of the grid node p = (z, i, j). -/
abbrev NodeIndex (p : Node) := D.GridIndex p.1 p.2.1 p.2.2

/-- The level at node p, inside GL over O_E/𝔟Q, 𝔟 the b₁-th power of the product of the chosen
places: trivial at (false, 0, b), else the kernel of reduction modulo 𝔟. -/
def nodeLevel p := if !p.1 ∧
  p.2.1 = 0 then ⊥ else (GeneralLinearGroup.map (n := D.NodeIndex p) (reduceToTriangle ϑ true)).ker

/-- The index of the level `Data.nodeLevel` at node (a, b) of grid z in the general linear group,
as a complex number. -/
abbrev levelIndex z a b := ((nodeLevel ϑ (z, a, b)).index : ℂ)

/-- The forms on Z_{i,0} of the type of `Data.GridForm` fixed by the principal level of
`Data.gridLevelGen`. -/
abbrev gridLevelForms i :=
  levelSpace ((gridSpace ..).formRep (D.gridKernel true 0 i true)) (principalLevel _ D.gridLevelGen)

lemma isConjKernelPair_gridKernel (h : i ≤ D.m ∧ j ≤ D.m) : IsConjKernelPair (D.gridKernel z i j) :=
  isConjKernelPair_kernelPair (d := false) (D.hasGap_gridParam · .. |>.mono
  (by grw [gapThreshold, card_gridIndex_le _ h]; simpa using D.le_of_hasLogBound))

instance gridChar_hasWeight : (gridChar ϑ c l n).HasWeight (D.gridWeight c l n)
  (gridTamePart ϑ c l) := D.hasWeight_liftChar.mul_upsilonU1_pow _

/-- Steps of the grids are edges: for a step from (i, j) to (i', j') = (i+1, j) or (i, j+1) with
i', j' ≤ m, and any family ϑ, the characters `Data.gridChar`, types `Data.gridKernel` and
polynomial `Data.gridHarmonic` satisfy `IsEdgeFamily`. -/
lemma isEdgeFamily_grid {I} (ϑ : I → _) d {c l i' j'} (e : (c, l, i', j') = bif d then (z, i, i + 1,
  j) else (!z, j, i, j + 1)) (hi : i' ≤ D.m := by omega) (hj : j' ≤ D.m := by omega) : IsEdgeFamily
  (fun x ↦ gridChar (ϑ x) c l) (D.gridKernel z i j) (D.gridKernel z i' j') d (D.gridHarmonic 0 d c
  l ..) := isEdgeFamily_of_paramsCorrespond _ _ (D.paramsCorrespond_grid _ _ _ _ _ e)

/-- For j ≤ m, the space Z_{j,j} equals the orthogonal sum of V_{j,j} and the standard line of
sign (−1)^j, with the basis relabelled by the bijection `Data.gridDiagEquiv`. -/
lemma gridSpace_diag h : D.gridSpace 0 _ j j =
  ((gridSpace ..).sum (signedSpace ..)).reindex _ (D.gridDiagEquiv_spec h) := by
  cases j; rfl
  exact signedSpace_eq_reindex _
    (Units.ext ((fromBlocks_diagonal ..).trans (by simp; congr with ⟨⟩ <;> rfl)))

/-- For every j there is a bijection of basis indices, compatible with the signs, under which
the space Z_{j+1,j} equals the space V_{j+1,j}. -/
lemma gridSpace_subdiag j : ∃ τ h, D.gridSpace 0 true j (j + 1) =
  (D.gridSpace 0 false (j + 1) j).reindex (.symm τ) h :=
  (exists_equiv_of_card_neg (by cases D.t_odd; simp_all [card_gridIndex]; lia) (by
  grind [card_neg_gridSigns])).imp fun _ ↦ (⟨·, by cases j <;> exact signedSpace_eq_reindex _ rfl⟩)

/-- The descent from node (0, b+1) to (0, b) whose datum is the indicator of the standard
inclusion modulo `Data.triangleModulus`, times the order of GL modulo `Data.triangleModulus` at (0,
b). -/
def pointDescent z b : D.GridForm z 0 (b + 1) →ₗ[ℂ] D.GridForm z 0 b := (triangleOrder z ϑ b : ℂ) •
  modDescent _ _ (gridChar ϑ (!z) b) (D.gridHarmonic 0 false (!z) b z 0 b 0 (b + 1))
  (inclusionDatum (triangleModulus z ϑ).ResRing) ..

/-- The composite of the descents `Data.pointDescent` from node (0, m) to node (0, b) of grid z; the
identity for b = m, zero for b > m. -/
def iotaPlus z b : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b := if b < D.m then pointDescent ϑ .. ∘ₗ
  iotaPlus .. else Pi.single (M := (D.GridForm .. →ₗ[ℂ] D.GridForm z 0 ·)) _ .id b

variable {ϑ}

/-- The descent of forms from node (a, b + 1) to node (a, b) of grid z, with the indicator of
the matrix y modulo 𝔪 = `Data.gridModulus` as finite datum. -/
def descentMove (y : Matrix (D.GridIndex z a (b + 1)) (D.GridIndex z a b) (gridModulus ϑ).ResRing) :
  D.GridForm z a (b + 1) →ₗ[ℂ] D.GridForm z a b
  := modDescent _ _ (gridChar ϑ (!z) b) (D.gridHarmonic 0 false (!z) b ..) (Pi.single y 1) ..

/-- The lift of forms from node (a, b) to node (a + 1, b) of grid z, with the indicator of the
matrix y modulo 𝔪 as finite datum. -/
def liftMove (y : Matrix (D.GridIndex z (a + 1) b) (D.GridIndex z a b) (gridModulus ϑ).ResRing) :
  D.GridForm z a b →ₗ[ℂ] D.GridForm z (a + 1) b
  := modLift _ _ (gridChar ϑ z a) (D.gridHarmonic 0 true z a ..) (Pi.single y 1) ..

/-- For k in K_0, the character `Data.gridChar` at det k is the character modulo 𝔪 with local
components (ω_wϑ_w)^(l+1) if c, else ω_w^(l+1), at det(k mod 𝔪), whatever the index type n. -/
lemma gridChar_det {n'} [Fintype n'] s (k : Kf D.E n') : (gridChar ϑ c l n).1 (G.det (s := s)
    (1, k.1)) = (gridModulus ϑ).charOfTamePart (gridTamePart ϑ c l) ((gridModulus ϑ).reductionK₀
  k).1.det := (gridChar_hasWeight ..).apply_det_eq_charOfTamePart (by
  cases c <;> simp +contextual [places_modulus_eq_union, liftTamePart, TameChar.pow, ϑ.1.1.5]
  tauto) _

/-- In grid Z, and in grid V for a ≠ 0, the index of the level at node (a, b) is the order of GL
of its rank over O_E/𝔟, so it is free of ϑ. -/
lemma levelIndex_eq_untwisted (h : z ∨ a ≠ 0) : levelIndex ϑ z a b =
  Fintype.card (GL (D.GridIndex z a b) (D.gridModulus 1).ResRing) := by
  rw [levelIndex, nodeLevel, ite_eq_right (by lia), Subgroup.index_ker, MonoidHom.range_eq_top.2
    (reductionK₀_surjective.forall.2 fun _ ↦ ⟨_, Units.ext Modulus.factor_reductionK₀⟩)]; simp; rfl

variable {P : _} (D : Data P) (ϑ : D.TameChar)

lemma absNorm_piGBar : Ideal.absNorm (.span {D.piGBar}) =
  D.gProd ^ D.f := by simp [span_piGBar, prod_q_chosenPlace]

lemma v_chosenIdele w : Valued.v (D.chosenIdele.1 w) = Valued.v ((algebraMap _ (Ô _) D.piGBar).1
  w) := (Modulus.valued_generator ..).trans ((v_algebraMap_eq_intValuation _).trans
  (w.intValuation_eq_exp_neg_multiplicity D.piGBar_ne_zero)).symm

lemma valuation_shift_const_eq_ideleA_norm {k hk} w : Valued.v (((D.gradingY k hk).c : 𝔸f _) w) =
  Valued.v ((D.ideleA * star D.ideleA.1) w) :=
  have := congr($(@id (D.ideleA.1 * _ = _) (divp_mul_cancel ..) ▸ WeilData.self_dual w) *
    $(w.intValuation_eq_exp_neg_multiplicity
    (ne_zero_of_differentIdeal_eq_span Parameters.different_eq_span_varpi)))
  eq_of_inv_mul_eq_one (by simp [gradingY, ← (congr($D.piGBar_mul_star) : _ = (D.gProd : D.E)),
    v_chosenIdele, Parameters.different_eq_span_varpi, ← v_algebraMap_eq_intValuation,
    v_algebraMap_eq_valuation, WithZero.exp_neg, -WithZero.inv_exp] at *; grind)

lemma spansLattice_gradingY k hk : (gradingY k hk).SpansLattice D.ideleA D.piIdele
  (D.latticeScale k) := by grind [Grading.SpansLattice, gradingY, spaceY]

lemma chosenLevel_inf_trivialOn_le {n} [Fintype n] : chosenLevel ⊓ Gf.trivialOn n ϑ.Q ≤
  levelOf (D.levelPlaces ϑ).placeAt ⊥ := fun _ ⟨h, k⟩ ↦ mem_levelOf.2 ⟨_, funext (Sum.rec
  (congrFun (mem_levelOf.1 h).2) (Kf.reduceAt_eq_one_of_atPlace <| Gf.mem_trivialOn.1 k _ ·.2))⟩

end Data

/-- The pure tensor over i ≤ ϱ of τ_N (at the places dividing π) applied to the tensor of the
translated vacua `Data.translateDatum` t of lifts 2i + 1 and 2i + 2. -/
def Data.reducedVacuum {P} (D : Data P) t :=
  TensorChain.pure (D.pairTranslates (D.translateDatum t)) (D.ϱ + 1)
