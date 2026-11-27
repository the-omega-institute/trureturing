/- GID: D5/S3/Zeros/GRH/New/Trace/GoodIdempotent
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Trace/GoodIdempotent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Trace.GoodIdempotent. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Trace/GoodIdempotent.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.FramesForY
import D5.S3.Zeros.GRH.New.Exchange.GridParameters
import D5.S3.Zeros.GRH.New.Columns.ColumnDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

This file: Spaces Y_j, W_j, ideles, levels, rows, auxiliary pairs on the proof's data. Signs and
weight gaps of the data; cusp kernel and finite-dimensionality instances. -/

noncomputable section

/-- The bijection from κ ⊔ {0, …, 2ϱ} to the basis indices: κ is kept, and 0, …, 2ϱ go to e_0,
…, e_{ϱ−1}, z, e*_{ϱ−1}, …, e*_0. -/
def Shape.besselIndexEquiv (𝔰 : Shape) :
  𝔰.κ ⊕ Fin (2 * 𝔰.ϱ + 1) ≃ 𝔰.BesselIndex := by refine .symm (.ofBijective
  (.elim (.inr ⟨·, ?_⟩) (.elim (.elim .inl fun _ ↦ .inr ⟨𝔰.ϱ, ?_⟩) (.inr ⟨2 * 𝔰.ϱ - ·, ?_⟩)))
  ?_) <;> simp [↓Fintype.bijective_iff_injective_and_card, Function.Injective] <;> grind

variable {P} (D : Data P) (ϑ : D.TameChar) (j : ℕ) {s} (V : Space D.E D.RowIndex s)

namespace Data

/-- The number of lifts satisfies m = 2ϱ + 2, where ϱ = `Data.ϱ` is ⌊m/2⌋ − 1 truncated at
zero; so m is even and at least 2. -/
@[grind! .] lemma m_eq_two_mul_varrho_add_two : D.m = 2 * D.ϱ + 2 := by grind [ϱ]

instance {u} : D.HasLogBound u D.ϱ (D.logX / 2 + ite u 2 (-4)) := .of_mem_Icc (D.m / 4) D.m
    (by simpa [field] using mod_cast by grind [le_m])

open Ideal

lemma levelNorm_mem_and_notMem_of_mem_Q {w} : w ∈ ϑ.Q ∨ star w ∈ ϑ.Q → ↑ϑ.levelNorm ∈ w.1 ∧ D.piGBar
  ∉ w.1 ∧ ↑D.N ∉ w.1 := by grind [mem_of_dvd, Dvd.dvd.natCast, absNorm_mem, Finset.dvd_prod_of_mem,
  q_star, piGBar_mul_star, w.2.notMem_of_isCoprime_of_mem ϑ.7.cast, mul_mem_left, mul_mem_right]

/-- The system of places (`LevelPlaces`) formed by the chosen places above g₀, g₁ and the places of
the modulus Q of ϑ. -/
def levelPlaces := LevelPlaces.mk _ ϑ.Q D.chosen (↑) (by
  use D.isConjApart_chosen.1.sumElim (by simp) ?_ <;> grind [D.isConjApart_chosen.2, →
    levelNorm_mem_and_notMem_of_mem_Q, chosen, ϑ.6, star_star])

/-- The modulus M^c Q, or M^c if b is false; M is the product of the chosen places, Q the
product of the places of the tame character ϑ. -/
abbrev 𝔪 c (b := true) := (D.levelPlaces ϑ).levelModulus c b

lemma nonempty_modulus_places {D ϑ c b} [NeZero c] : Nonempty (@𝔪 P D ϑ c b).places :=
    ⟨_, mul_le_left.trans
  ((pow_le_self NeZero.out).trans (prod_places_le_iff.2 ⟨⟨0, chosenEquiv _ 1⟩, rfl⟩))⟩

/-- A chosen finite idele generating the ideal of π̄₀π̄₁ = `Data.piGBar` in Ô, with component 1
at every place not dividing π̄₀π̄₁. -/
def chosenIdele :=
  Modulus.generator ⟨span {D.piGBar}, by simp, by simpa [IsChosen] using fun _ ↦ IsChosen.not_star⟩

/-- The finite idele α/π_g, with π_g generating (π₀π₁) at the conjugates of the chosen places and 1
elsewhere; it generates the fractional ideal 𝔞 = 𝔞₀/π₀π₁. -/
def ideleA := WeilData.α / star D.chosenIdele

/-- The principal finite idele of E given by the nonzero element π. -/
def piIdele := principalIdele (.mk0 D.π (by simp) : D.Eˣ)

lemma piIdele_spec : IsSplitSquarefree D.piPlaces D.N D.piIdele := ⟨by simp [piIdele, ← map_mul,
  ← coe_star_ringOfIntegers, π_mul_star], (⟨by split <;> erw [v_algebraMap_eq_intValuation] <;>
  simp_all [piPlaces, intValuation_pi], D.isSplitLevel_piPlaces.star_notMem ·⟩)⟩

/-- For index j, the finite idele (a/ā) raised to ⌈(m−j)/2⌉, exponent zero for j ≥ m, where a is the
idele `Data.ideleA` = α/π_g. -/
def latticeScale := divStar D.ideleA ^ ((D.m - j + 1) / 2)

/-- For j<m, a bijection from the indices of X_j plus 2ϱ+1−j string indices to those of Y_j:
explicit for j=0, arbitrary by cardinality otherwise. -/
def indexEquivY : ∀ j < D.m, D.X j ⊕ Fin (2 * D.ϱ + 1 - j) ≃ D.Y j
  | 0, _ => D.shape.besselIndexEquiv | _ + 1, _ => Fintype.equivOfCardEq (by simp; grind [n])

/-- There is a space with the signs of Y_j that has J = 1 and x = 1 if j ≥ m, and for j < m has
Gram matrix `gradedGram` and finite frame `gradedLatticeBasis`·k, with k integral and ≡ 1 at the
chosen places above g. -/
lemma exists_spaceY : ∃ V : Space D.E _ (D.signsY j), (D.m ≤ j → V.IsStd) ∧ ∀ h, V.J = gradedGram
  (D.indexEquivY j h) ↑D.N ∧ ∃ k, (∀ x, intGL.map (reduceAt (D.chosen x)) k = 1) ∧ V.xFin.1 =
  gradedLatticeBasis (D.indexEquivY j h) D.ideleA D.piIdele (D.latticeScale j) * k.1.1 := if a :
  j < D.m then have (w : D.Φ) := (exists_frame_gradedGram (D.indexEquivY j a) _ D.N_prime.pos
    (D.card_neg_gridSigns .. ▸ by grind)).choose_spec.1
  (exists_orthonormal_Ô (isUnimodular_gradedLatticeBasis_gram _ D.piIdele_spec.1)).elim fun l
    h ↦ have H := (gram_mul ..).trans h.2
    ⟨⟨_, mkAdelicGL ((.mkOfMulEqOne _ _ <| (mul_assoc ..).trans <|
      this · ▸ signMatrix_mul_self _)⁻¹, (Units.mkOfMulEqOne _ _ H)⁻¹ * _),
      gram_mkAdelicGL this (gram_mul_of_gram_eq H (liftResidue ..).1.2)⟩, by lia, fun _ ↦ ⟨rfl,
      ⟨l, h.1⟩ * _, by simpa [mul_eq_one_iff_eq_inv'] using! congrFun (reduceFamily_liftResidue
      _), by apply mul_assoc⟩⟩ else ⟨_, isStd_signedSpace ∘ gridSigns_eq_one _, by lia⟩

/-- The hermitian space Y_j with its adelic frame, hence its lattice 𝖬_j, chosen as in
`Data.exists_spaceY`. -/
def spaceY := (D.exists_spaceY j).choose

instance isStd_spaceY : (D.spaceY D.m).IsStd := by grind [spaceY]

/-- For index j, the rank r diagonal hermitian space W_j over E whose diagonal entries are the
signs `Data.signsW` j. -/
abbrev spaceW := signedSpace D.E (D.signsW j)

/-- The space of forms on V of parameter ς (`Data.paramW` = 2ς) fixed by the principal level at
the chosen places above the primes g₀, g₁ (`Data.g`). -/
abbrev principalForms :=
  levelSpace (V.formRep (typeKernel D.paramW s)) _ (.comp 1 (levelOf.reduction D.chosen ⊥))

/-- The complex representation of G = ∏ GL_r(k_w), over the chosen places w above g (k_w the residue
field), on the forms on V of principal level
K(g), acting through reduction at these places. -/
def principalRep : Representation ℂ D.G (D.principalForms V) := levelRep _ _ (.id _) (by simp)

/-- The good forms on V: the image of the idempotent e₀ of ℂ[𝖦] acting on forms of principal
level at the chosen places above g. -/
def goodForms := ((D.principalRep V).asAlgebraHom D.e₀).range

/-- The rows: the good forms (`Data.goodForms`) on the space Y_0. -/
abbrev rows := D.goodForms (D.spaceY 0)

/-- The complex dimension of the space of rows (`Data.rows`), the good forms on Y₀. -/
abbrev rowDim := Module.finrank ℂ D.rows

/-- The j-th auxiliary pair (`AuxPair`) for ϑ: W = W_j, V = I_{r+t}, character μ_j⁰ϑ, places
`Data.levelPlaces`, and weights read off from ς and w_j. -/
def auxPair := AuxPair.mk (D.levelPlaces ϑ) _ (D.spaceW j) (.inl (β := Fin D.t)) (fun c ↦
  ite (D.signsW j c = 1) (D.basisNumber c) (D.r - 1 - D.basisNumber c)) (fun τ h ↦
  (D.rowParameter τ (h - 1) - D.rowParameter τ h ⊔ (D.t / 2 - D.w j τ) - 1).toNat)
  (fun τ h ↦ (D.rowParameter τ (D.r - h - 1) ⊓ (-D.w j τ - D.t / 2) - D.rowParameter τ
  (D.r - h) - 1).toNat) (D.liftChar ϑ j) _ _ D.hasWeight_liftChar (by simp_all [liftTamePart,
  levelPlaces, ϑ.5, range_chosen]) (by simp [D.t_odd.pos])

variable {P : _} (D : Data P) (j : _) (v) {s : _} [hs : ∀ v, (toHCParam s (D.paramW v)).HasGap D.h]

instance : (D.spaceW D.m).IsStd := isStd_signedSpace (funext (by simp [signsW, ← r_add]))

/-- −w_j(τ) is at distance at least h₂ from the entries of the row parameter: ς(τ,p) + w_j(τ) ≥
h₂ if p + 1 < k + j, and ≤ −h₂ otherwise. -/
lemma varsigma_add_w_gap τ p : ite (p < D.posRank j) (D.h₂ ≤
  D.rowParameter τ p + D.w j τ) (D.rowParameter τ p + D.w j τ ≤ -D.h₂) := by
    obtain _ := D.w_add_gap_le τ j,
      (D.w_add_gap_le τ · j); grind [rowParameter, (D.nat_le_of_hasLogBound : D.h ≤ D.w j τ)]

grind_pattern varsigma_add_w_gap => D.rowParameter τ p, D.w j τ

instance hasGap_signsY_paramW : (@toHCParam D.RowIndex (D.signsY 0) (D.paramW v)).HasGap D.h :=
  D.hasGap_gridParam v false 0 0

instance hasGap_paramW : (toHCParam (D.signsW j) (D.paramW v)).HasGap D.h := {D.hasGap_signsY_paramW
  v with gap := mod_cast by have := D.varsigma_add_w_gap j v; grind [paramW, signsW]}

/-- If the doubled parameter `Data.paramW` v has gap h for the signs s at every infinite place
v, then the product function `typeKernel` on G_∞ for this parameter and s is a cusp kernel
(`IsCuspKernel`) of order h₂. -/
lemma isCuspKernel_paramW : IsCuspKernel D.h₂ (typeKernel D.paramW s) := isCuspKernel_typeKernel
  (hs · |>.mono (by simpa [↓card_rowIndex, h, two_mul] using D.le_of_hasLogBound))

instance {V} : Module.Finite ℂ (@D.principalForms _ s V) :=
  V.finite_levelSpace D.isCuspKernel_paramW ⟨_, isOpen_levelOf⟩

end Data

open Finset Fint

/-- The good idempotent e₀ of the data D is a central self-adjoint idempotent of its group
algebra. -/
lemma Data.isCentralProj_e₀ {P} (D : Data P) : IsCentralProj D.e₀ := isCentralProj_sum_tupleIdem

/-- Let χ^{M_ω} = 1 and l ≠ 0. A pure tensor over the chosen places above g with one factor ∑
χ(det h)⁻¹h, summed over the invertible h = 1 + u l, has product zero with the good
idempotent e₀. -/
lemma Data.reflectionSum_mul_e₀ {P} (D : Data P) {x} i {χ l} (hχ : χ ^ P.Mω D.s = 1) (hl : l ≠ 0)
    (e : x i = reflectionSum χ l) : piTensorElem x * D.e₀ = 0 := by erw [mul_sum, sum_map,
  sum_eq_zero fun _ o ↦ piTensorElem_mul_eq_zero i (e ▸ reflectionSum_mul_labelIdem
  (((mem_filter.1 (Fintype.mem_piFinset.1 o _)).2.1 _).2 _ (charName_pow_eq_one hχ)) hl)]
