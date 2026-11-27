/- GID: D5/S3/Zeros/GRH/New/Rows/LineCoordinates
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/LineCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.LineCoordinates. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/LineCoordinates.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula.TraceComparison
import D5.S3.Zeros.GRH.Lib.Adelic.Hecke.ClassSumBounds
import D5.S3.Zeros.GRH.New.Trace.GoodIdempotent
import D5.S3.Zeros.GRH.New.Rows.MemberKernels
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: Names for index sets, characters, moduli and polynomials of the comparison construction.
Column counts of the weight add up to w_j − j − ⌊(t+k−1)/2⌋. Index sets, determinant data and
coefficient vectors for the one-line identity. Degree, denominator and size of coordinates of the
determinant product in Weyl's lattice. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open Finset Complex ComplexOrder Equiv Fintype PolyRep Ideal Matrix MvPolynomial LevelPlaces Sum
  WeilData Matrix.Module

namespace Data

/-- The modulus ϖ^c, the c-th power of the product ϖ = `piGBar` of the chosen places. -/
abbrev untwistedModulus {P : Parameters} (D : Data P) := (D.𝔪 .one · false)

lemma ideal_untwistedModulus_eq_span {P : Parameters} (D : Data P) {c} : (D.untwistedModulus
  c).ideal = span {D.piGBar ^ c} := by simp [levelModulus, ← span_singleton_pow, span_piGBar]; rfl

instance {P : Parameters} (D : Data P) : NeZero D.m := .of_gt D.le_m

/-- The index set with 2m + m elements, in two blocks, of the space of signature (2m, m) on which
`carrierForm` lives. -/
abbrev CarrierIndex {P : Parameters} (D : Data P) := Fin (2 * D.m) ⊕ Fin D.m

/-- The index set, with 6m + 1 elements, of the definite space I♭ = I_{6m+1}. -/
abbrev FlatIndex {P : Parameters} (D : Data P) := Fin (6 * D.m + 1)

/-- The index set of V°: the r indices of W_j and t − 9m − 1 − r further ones. -/
abbrev SmallIndex {P : Parameters} (D : Data P) := D.RowIndex ⊕ Fin (D.t - 9 * D.m - 1 - D.r)

/-- The set of classes of U(V°) at principal level ϖ²: double cosets of U(V°)(𝔸_f) by the
rational points and the congruence subgroup modulo ϖ². -/
abbrev SmallClasses {P : Parameters} (D : Data P) :=
  StdClasses (principalLevel D.SmallIndex (D.piGBar ^ 2))

variable {P : Parameters} (D : Data P) in
/-- For a natural number i, the basis index of Y₀ whose number under `Data.basisNumber` is min(i, r
− 1). -/
def basisVec i := D.basisNumber.symm ⟨i ⊓ (D.r - 1), by grind⟩

variable {P} (D : Data P) (ϑ : D.TameChar) (j : D.LiftIndex) (h : ℕ)

/-- Pairs of a class of U(I_{6m+1}) at principal level (π̄₀π̄₁)² and, for each infinite place,
𝗁′ = h₂ − ⌊(t+1)/2⌋ lists of 2m row indices among 6m + 1. -/
abbrev LineChoice := StdClasses (principalLevel D.FlatIndex (D.piGBar ^ 2)) × (D.Φ →
  Fin D.reducedHalfGap → Fin (2 * D.m) → D.FlatIndex)

/-- A chosen invertible matrix over E whose rows lie in the lattice at the class of i and whose
entries are small at every complex embedding (`Space.exists_short_basis_stdSpace`). -/
def shortRows (i : D.LineChoice) :=
  (Space.exists_short_basis_stdSpace P.cycloConductor_mem_different i.1.out).choose.1ᵀ

variable {D}

/-- The character χ^j·ϑ of [U(1)], for the fixed weight-zero character χ of tame part ω and a
tame character ϑ. -/
def twistedChi := D.χ ^ j.1 * ϑ.toAutChar

lemma twistedChi_hasWeight : (twistedChi ϑ j).HasWeight 0 (D.liftTamePart ϑ j) :=
  (D.chi_hasWeight.zpow j).mul ϑ.hasWeight

/-- The index set of the padding I_j⁻ ⊕ I_{3m−j} of W_j: a block of j elements and a block of 2m
+ (m − j) elements. -/
abbrev PadIndex := Fin j ⊕ Fin (2 * D.m + (D.m - j))

/-- The index set of V″: the r indices of W_j, the padding `Data.PadIndex` and the indices of I♭. -/
abbrev BigIndex := (D.RowIndex ⊕ PadIndex j) ⊕ D.FlatIndex

/-- The signs of the padded space W_j ⊕ I_j⁻ ⊕ I_{3m−j}: those of W_j, then −1 on j indices and
+1 on 2m + (m − j) indices. -/
abbrev padSigns := (D.signsW j ⊕ᵥ (-1 ⊕ᵥ 1) : _ ⊕ PadIndex j → _)

/-- The map from i < m to R ⊕ Pad(j): the i-th index of the block of j elements of the padding
if i < j, else `Data.basisVec`(k + i − 1). -/
def negIndex (i : Fin D.m) := if h :
  _ then @inr _ (PadIndex j) (inl ⟨i, h⟩) else inl (D.basisVec (D.posRank i))

/-- Sends i < 2m to the basis vector number h + i of W_j if h + i < k + j − 1, and otherwise to
index i of the positive padding block. -/
def posRowIndex i :=
  ite (h + i.1 < D.posRank j) (@inl _ (PadIndex j) (D.basisVec (h + ↑i))) (inr (inr (.castAdd _ i)))

/-- The j-th auxiliary pair `Data.auxPair` at the trivial twist. -/
abbrev untwistedAuxPair := D.auxPair .one j

/-- The index set of determinants at τ: one for each column of length h < k+j−1 of the weight k⁺
of `Data.untwistedAuxPair`, and h′ (`Data.reducedHalfGap`) further ones. -/
abbrev DetIndex τ :=
  (Σ h : Fin (D.posRank j), Fin ((untwistedAuxPair j).colsPlus τ h)) ⊕ Fin D.reducedHalfGap

/-- The polynomial ∏_τ det(y⁻_τ)^{#`Data.DetIndex` j τ + #`BigIndex` j + m} ∏_{h<k+j−1}
det(y_{τ,h})^{k⁺(τ,h)}, with y⁻ the minor in rows negIndex, negative columns, y_h that in rows
posRowIndex(h), positive columns. -/
def linePoly := ∏ τ, letterMinor τ (negIndex j) inr ^
  (Fintype.card (DetIndex j τ) + Fintype.card (BigIndex j) + D.m) * ∏ h :
  Fin (D.posRank j), letterMinor τ (posRowIndex j h) inl ^ (untwistedAuxPair j).colsPlus τ h

/-- The natural number j + ⌊(t + k − 1)/2⌋, the exponent of υ = `upsilonU1` in the character on V″
for the
j-th lift. -/
abbrev bigCharExp := j + (D.t + D.k - 1) / 2

/-- The character μ♭·υ^{m + j + ⌊(t+k−1)/2⌋ − j𝗁} of [U(1)], with μ♭ = `Data.muFlat` and 𝗁 the
gap. -/
def carrierChar := D.muFlat * upsilonU1 ^ (↑(D.m + bigCharExp j) - j * D.h : ℤ)

lemma carrierChar_hasWeight : (carrierChar j).HasWeight (↑(D.m + bigCharExp j) - D.w j ·) 1 := by
  convert! D.muFlat_hasWeight.mul (hasWeight_upsilonU1_zpow _) <;> grind [Pi.add_def]

/-- The character μ_j⁰ϑ·υ^{j + ⌊(t+k−1)/2⌋} of [U(1)], with μ_j⁰ϑ = `Data.liftChar` ϑ j. -/
abbrev bigChar := D.liftChar ϑ j * upsilonU1 ^ bigCharExp j

/-- The choices indexing the functions F♮: a matrix modulo M² with 3m rows and columns
`Data.BigIndex`, M the product of the places `Data.chosen`, and an element of `Data.LineChoice`. -/
abbrev MemberIndex :=
  Matrix D.CarrierIndex (BigIndex j) (D.untwistedModulus 2).ResRing × D.LineChoice

/-- F♮(g) on U(W_j): the integral over [U(2m,m)] of the carrier times the theta kernel at (g, 1,
h_i) with datum y ↦ ψ′(tr yu) mod ϖ², polynomial `Data.linePoly`·(minors of i). -/
def fNatural (i : MemberIndex j) g := ∫ x, carrierForm _ _ x * modKernel (signedSpace ..)
    (((D.spaceW j).sum ((stdSpace ..).neg.sum (stdSpace ..))).sum (stdSpace ..)) (upsilonU1 ^ D.m)
  (carrierChar j) _ (traceChar i.1) (renameRowsCols inl id (linePoly j) * renameRowsCols inr id
  (pairedDetProd (.X ⟨·, ·, inl ·⟩) fun w k ↦ ((D.shortRows i.2).map (Φ w)).submatrix (i.2.2 w k)
  id)) x (.sum (.sum (g, 1), i.2.1.out)) ∂(signedSpace ..).quotMeasure

lemma card_detIndex_add_bigCharExp τ : Fintype.card (DetIndex j τ) + bigCharExp j = D.w j τ := by
    open Finset in simp [← sum_range]; zify; rw [Finset.sum_congr rfl, sum_range_sub'
  fun l ↦ D.rowParameter τ (l - 1) + l ⊔ 1] <;> grind [rowParameter, reducedHalfGap, auxPair]

/-- The index set of the definite space L⁺ = I_{3m−j} ⊕ I_{6m+1} ⊕ I_{3m}. -/
abbrev LPlusIndex := Fin (2 * D.m + (D.m - j)) ⊕ D.FlatIndex ⊕ D.CarrierIndex

/-- The bijection of index sets that regroups W_j ⊕ I_j⁻ ⊕ L⁺ as I_{3m} ⊕ (W_j ⊕ I_j⁻ ⊕ I_{3m−j}
⊕ I_{6m+1}). -/
def regroupEquiv : D.RowIndex ⊕ Fin j ⊕ LPlusIndex j ≃ D.CarrierIndex ⊕ BigIndex j := ((sumComm
  ..).trans ((sumAssoc ..).trans ((sumAssoc ..).trans (sumCongr (.refl _) (sumAssoc ..))))).symm

/-- For j ≤ m, a bijection, chosen from equality of cardinalities, from 2m indices together with
those of V″ to k + j − 1 indices together with those of L⁺. -/
def posEquiv : Fin (2 * D.m) ⊕ BigIndex j ≃ Fin (D.posRank j) ⊕ LPlusIndex j :=
  Fintype.equivOfCardEq (by simp [↓card_rowIndex]; grind)

/-- The 2m-row matrices at τ: for length h < k+j−1, row a is vector h+a of W_{j,+}, or a of
I_{3m−j} on overflow; otherwise the chosen rows of τ(Y), on I_{6m+1}. -/
def detRows i (Y : _ := D.shortRows i) τ : DetIndex j τ →
  Matrix (Fin (2 * D.m)) (Fin (D.posRank j) ⊕ LPlusIndex j) ℂ := (fun h ↦
  (inclMatrix ℂ fun a ↦ dite _ (inl ⟨h.1 + a, ·⟩) fun _ ↦ inr (inl (a.castAdd _)))ᵀ) ⊕ᵥ fun k ↦
  fromCols 0 (fromCols 0 (fromCols ((Y.map (Φ τ)).submatrix (i.2 τ k) id) 0))

/-- The coordinates (`firstColsCoord`), in the weight k⁺ of `Data.untwistedAuxPair` on V″, of the
product of the determinants det(η; x), η from `Data.detRows`; each is a polynomial in the L⁺
variables. -/
abbrev linePolyCoords i (Y : _ := D.shortRows i) :=
  firstColsCoord (untwistedAuxPair j).colsPlus (stackedDetProd (posEquiv j) (detRows j i Y))

/-- The reduction homomorphism O_E/ϖ²Q → O_E/ϖ², where ϖ is the product of the chosen places
above g₀, g₁ and Q that of the places of ϑ. -/
abbrev forgetTwist : (D.𝔪 ϑ 2).ResRing →+* (D.untwistedModulus 2).ResRing := reduceToR₀

/-- The function of z modulo ϖ²Q equal to Σ_g ψ′(tr(z′gu)), g in GL_{3m}(O_E/ϖ²), z′ the last 3m
columns, if the other columns are the standard inclusion; else 0. -/
def lPlusDatum u (z : Matrix (BigIndex j) (LPlusIndex j) _) :=
  ite (z.submatrix id (.map id inl) = inclMatrix _
  (.map (inr ∘ inr) id)) (∑ g : GL _ _, traceChar u (z.toCols₂.toCols₂.map (forgetTwist ϑ) * g.1)) 0

/-- Coordinate l at h: the theta constant of (I_j⁻, V″) times the class sum over c in U(I_{3m}) of
Ξ°(c)·θ^{L⁺,V″}[Φ_L, Q_l]((1, h♭, c), h), h♭ the class in i;
Ξ° = `carrierXi`, Φ_L = `lPlusDatum`, Q_l = coordinate l of `linePolyCoords`. -/
def lineMultiplier (i : MemberIndex j) h l :=
  modKernelI (stdSpace ..).neg (upsilonU1 ^ j.1) (bigChar ϑ j) (D.𝔪 ϑ 2)
  (Pi.single (inclMatrix _ (inl ∘ inr ∘ inl)) 1) 1 1 h * stdClassSum (Kf ..) fun c ↦ carrierXi D.m
  (twistedChi ϑ j) c * modKernelI (stdSpace ..) (bigChar ϑ j) (bigChar ϑ j) _ (lPlusDatum ϑ j i.1)
  ((linePolyCoords j i.2) l) (1, U.blockSumOne (1, U.blockSumOne (i.2.1.out, c))) h

attribute [local grind .] reducedHalfGap auxPair rowParameter

attribute [local simp↓] card_rowIndex detRows Matrix.mul_apply inclMatrix ite_apply

lemma card_detIndex τ : card (DetIndex j τ) = (range (card (BigIndex j))).sum
  ((untwistedAuxPair j).colsPlus τ) ∧ card (DetIndex j τ) ≤ D.b₁ + D.b₂ + D.h + D.m * D.h :=
  ⟨by simp [← sum_range]; rw [eq_comm, eventually_constant_sum (N := D.posRank j + 1),
  sum_range_succ] <;> grind, by grind [card_detIndex_add_bigCharExp j τ, mul_le_mul_left j.2.2 D.h]⟩

open Norms.L2Operator

variable (i : D.LineChoice) (Y : Matrix _ _ D.E) (φ : ℂ →+* ℂ)

/-- For 1 ≤ j ≤ m, specialising the coordinates `Data.linePolyCoords` by z and φ: ℂ → ℂ gives a
vector y whose polynomial is the specialised determinant product. If all |φτ(Y_ab)| and |φ(z_x)| are
at most g⁴, then ‖y‖² ≤ (g⁹)^{31m·Σ_τ #`Data.DetIndex` j τ}. -/
lemma weylNormSq_linePolyCoords_le z : let y := φ ∘ eval z ∘ linePolyCoords j i Y; toPoly _ _ y =
    .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (detRows j i Y))) ∧
    (((∀ τ a b, ‖φ (Φ τ (Y a b))‖ ≤ D.gProd ^ 4) ∧ ∀ x, ‖φ (z x)‖ ≤ D.gProd ^ 4) → weylNormSq y ≤
    ↑(D.gProd ^ 9) ^ (31 * D.m * ∑ τ, card (DetIndex j τ))) := by
  clear_aux_decl; refine (?_ : HasWeightNormLe ..).elim fun ξ h ↦ (?_ : _ ∘ _ = ξ) ▸ h
  simp_rw [stackedDetProd, map_prod, Fintype.card_eq_sum_ones, mul_sum, ← prod_pow_eq_pow_sum]
  convert HasWeightNormLe.prod (n := BigIndex j) fun τ _ ↦ .prod (κ := fun l : DetIndex j τ ↦
    Pi.single τ (Pi.single (l.elim (·.1) fun _ ↦ D.posRank j) 1)) fun l _ ↦ ?_
  simp [funext_iff, Fintype.sum_sigma, sum_fin_eq_sum_range, ← mem_range]
  grind; generalize e : l.elim .. = h
  have ⟨H, A, B⟩ : h ≤ D.posRank j ∧ D.posRank j - h ≤ j ∧
    h < card (BigIndex j) := by simp; grind [Fin, Sigma]
  let E := ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le H))).symm.sumCongr
    (.refl (LPlusIndex j))).trans (.sumAssoc ..)
  let Z :=
    of (φ <| (detRows j i Y τ l).fromRows (fromCols 0 (of (z ⟨τ, ·, ·⟩))) · <| E.symm <| .inr ·)
  choose Y γ d b using exists_det_fromCols ((posEquiv j).trans E) Z
  use γ • weylEval _ _ fun (x, i) ↦ (List.ofFn (Yᵀ (.inr x.2)))[i]!, funext fun x ↦
    .symm (.trans (by
    simp [stackedDet, AlgHom.map_det, RingHom.map_det]
    refine det_eq_of_eq_det_one_mul (fromBlocks 1 0 (of fun u a ↦
      ite (h + a < D.posRank j) (x (⟨τ, u⟩, h + a)) 0) 1) (by simp) (Matrix.ext fun a ↦
      (reindex_equiv ((posEquiv j).trans E).symm).1.2 ?_)
    cases l <;> cases a <;> simp [Z] at e ⊢ <;> simp +contextual [E, inFirstCols, e, Fin.cast]
    all_goals first | lia | intro b; rw [univ.sum_eq_single ⟨b, by grind⟩] <;> clear * - <;> grind)
    ((d (fromRows 0 (of (x ⟨⟨τ, ·⟩, ·⟩)))).trans ?_))
  refine fun q ↦ .trans ?_ (b.trans (by
    grw [norm_det_le_norm_pow, l2_opNorm_conjTranspose_mul_self, ← sq,
      l2_opNorm_le_of_apply (M := D.gProd ^ 4)
      (by cases l <;> simp [Z, E, apply_ite, q, NeZero.one_le, one_le_pow₀])]; norm_cast
    simp; exact pow_le_pow (by grw [A, Nat.sub_le, j.2.2]; exact D.nat_le_of_hasLogBound)
      D.nat_le_of_hasLogBound (by grw [A, Nat.sub_le, j.2.2]; grind)))
  grw [weylNormSq_smul, weylNormSq, re_le_norm,
    ← norm_det_le_norm_det_of_posSemidef (posSemidef_self_mul_conjTranspose
    Y.toCols₂) (by convert Y.toCols₁.posSemidef_self_mul_conjTranspose; ext; simp)]
  iterate 2 simp [star_weylEval, weylKernel, highestPoly, tableauPoly, minor, det_apply,
    rowSubst, ↓det_transpose, Fin.val_eq_val _ ⟨h, B⟩, -sum_sum_type, @sum_sum_type (Fin _)]
  simp [_root_.funext_iff, firstColsCoord, map_fockPairing, MvPolynomial.map_map, ← h.1]

lemma toPoly_linePolyCoords : toPoly _ _ (linePolyCoords j i Y) =
  inFirstCols (stackedDetProd (posEquiv j) (detRows j i Y)) := MvPolynomial.ext _ _ fun d ↦ funext
  fun z ↦ by
    simpa [← coeff_map] using! congr(($((weylNormSq_linePolyCoords_le j i Y 1 z).1)).coeff d)

/-- For 1 ≤ j ≤ m there are d ≤ 31m·∑_τ |`Data.DetIndex` j τ| and an integer 0 < H ≤ d^{3d} such
that every H·`Data.linePolyCoords` is homogeneous of degree d, with coefficients in any subring of ℂ
containing all τ(Y_ab). -/
lemma exists_denom_linePolyCoords : ∃ d ≤ 31 * D.m * ∑ τ, card (DetIndex j τ), ∃ H : ℤ, 0 < H ∧ H ≤
  (d ^ d) ^ 3 ∧ ∀ i Y l,
  let Q := H • linePolyCoords j i Y l; (∀ c ≠ (0 : ℂ), aeval (c • .X ·) Q = c ^ d • Q) ∧
  ∀ A : Subring ℂ, (∀ τ a b, Φ τ (Y a b) ∈ A) → Q ∈ (MvPolynomial.map A.subtype).range := by
  obtain ⟨J, K, a, -, c, -⟩ :=
    exists_dual_isometry (κ := (untwistedAuxPair j).colsPlus) (rowPos (BigIndex j)) _ rfl (by tauto)
  have b i Y := congr((Kᵀ * $(c ▸ weylGram_mul_fockPairing) * Jᵀ)ᵀ • linePolyCoords j i
    Y); simp [← Matrix.mul_assoc, a, mul_smul, ↓Kᵀ.mul_smul, weylGram_isSymm.eq,
    Int.cast_smul_eq_zsmul, -zsmul_eq_mul, -card_sum] at b
  refine ⟨∑ τ, ∑ h ∈ range (card (BigIndex j)), (card (BigIndex j) - h) *
    (untwistedAuxPair j).colsPlus τ h, ?_, _, hookNumber_pos, hookNumber_le (sum_mono fun _ ↦ ?_),
    fun i Y l ↦ ⟨fun c h ↦ ?_, fun A hA ↦ (_root_.prod_mem fun τ _ ↦ _root_.prod_mem fun k _ ↦
    IsIntMatrix.det_mem fun a b ↦ ?_ : _ ∈ (MvPolynomial.map (MvPolynomial.map
    A.subtype)).range.comap inFirstCols.1).elim fun F e ↦ congr($(b ..) l ∈ _).mp (_root_.sum_mem
    fun k _ ↦ zsmul_mem (coord_mem_of_coeff_mem (MvPolynomial.map A.subtype).range.toAddSubgroup 0
    (by simpa using e ▸ toPoly_linePolyCoords ..) (by simp [coeff_map]) _) _)⟩⟩
  simp [↓card_detIndex, mul_sum]; gcongr 2; grind [Nat.mul_lt_mul_right]
  grw [range_mono le_self_add, ← sum_flip]; grind only [sum_range_succ]
  simpa [schur_smul, Pi.smul_def, ↓card_detIndex, *, -detRows, sum_range, ← prod_pow_eq_pow_sum,
    pow_mul, pow_sub_of_lt, ← eq_inv_smul_iff₀, smul_smul, ← division_def, div_pow, inv_mul_eq_div,
    prod_ne_zero_iff] using congr(_ * $(twoSidedSubst_firstColsCoord (c • 1) 1
    (twoSidedSubst_stackedDetProd _ (detRows j i Y) ..) _ l))
  cases a <;> simp [inFirstCols] <;> obtain b := posEquiv j b
  refine ⟨C (C ⟨_, ?_⟩), by simp; rfl⟩; revert k b; simp [apply_ite, hA]
  cases b; exacts [⟨_, map_X ..⟩, ⟨C (.X _), by simp; rfl⟩]
