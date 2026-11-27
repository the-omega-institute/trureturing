/- GID: D5/S3/Zeros/GRH/New/Seesaw/EdgePair
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/EdgePair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.EdgePair. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/EdgePair.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.TwoEdgesOnePair
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Finite part of the zero term; its frequency lies in the dual period lattice. Two lifts as
one arrow: weight-zero splitting, finite evaluation map and its equivariance. -/

noncomputable section

section

open stdLattice MatMul Matrix Prod Space

attribute [local simp ←] Matrix.map_mul RingHom.coe_snd Splitting.mixedTerm_zero

attribute [local simp] semichar Splitting.frameAt Splitting.finFrameVector omega_integrated
  mulVec_finVec finVec.eq_1 rep_apply_apply

variable {E n n₀ p : Type} [Field E] [CMType E] [Fintype n] [Fintype n₀] [Fintype p] {s s₀}
  {V : Space E n s} {V₀ : Space E n₀ s₀} [WeilData E] (D : V.Splitting V₀ p)

/-- The map f ↦ zero term along D of v ⊗ f, where v is the Fock vacuum moved by a chosen real
element adapted to D: the finite part of the constant term. -/
@[local simp] def zeroTermFin := D.zeroTerm ∘L V.integrated (realWeil
  (blockU (D.exists_isAdapted_and_frame_eq 1).choose.1) vacVector)

unseal finitePart in
lemma zeroTermFin_spec : (∀ f ∈ V.finitePart, zeroTermFin D f ∈ V₀.finitePart) ∧ ∀ y v, ∃ v₀, ∀ f,
  D.zeroTerm (V.ϱ y (V.integrated v f)) = V₀.integrated
  v₀ (zeroTermFin D (V.finHeisOp (finCoord y) f)) := by
  have h := (D.exists_isAdapted_and_frame_eq 1).choose_spec.1; set g := Exists.choose _
  cases h.mixedTerm_omega_vacElem
  use fun f hf ↦ ((D.zeroTerm ∘L V.ω g).1.map_span_le ..).2
    (by aesop (add simp [rho_finVec_mem_finitePart, finHeisOp,
    ω_ϱ])) ⟨_, omega_mem_finitePart g.2⁻¹ (projReal_of_mem_finitePart hf ▸ hf), by simp [g]⟩,
    (V.exists_rho_integrated_eq · · |>.imp' _ fun w e f ↦ by simpa [e, g] using
    (V.omega_integrated g⁻¹ w _ ▸ (h.exists_real_zeroTerm D.isMixedLaw_mixedTerm).choose_spec .. :))

lemma zeroTermFin_finHeisOp_finFrameVector b {z w} (h : z = D.finFrameVector 1 1 0 w b) f :
    zeroTermFin D (V.finHeisOp z f) = V₀.finHeisOp w (zeroTermFin D f) :=
  h ▸ by simp [finHeisOp, ↓Splitting.star_dot_finFrameVector, ← rho_integrated]

/-- Let MM'ᴴ = 1 and let f be fixed by ϱ_f(Mx) for all x ∈ Ô^n. If the constant term
`zeroTermFin` of ϱ_f(y)f is nonzero, then y ∈ M'Ô^n + k^⊥, k the finite part of the
isotropic frame of the splitting. -/
lemma zeroTermFin_support M M' {f y} (h : zeroTermFin D (V.finHeisOp y f) ≠ 0) (m : M * M'ᴴ = 1)
  (hf : ∀ x ∈ stdLattice E n, V.finHeisOp (M *ᵥ x) f = f) : ∃ l ∈ stdLattice E n, (D.kAdelic.map
  snd)ᴴ *ᵥ (y - M' *ᵥ l) = 0 := (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul (X := M'ᴴ *
  D.kAdelic.map snd) ⟨D.kCoord.map snd * M, by simp [← M.mul_assoc, m]⟩).elim fun t ⟨_, hK, L, hL,
  eL⟩ ↦ ⟨_, hL.isInt_conjTranspose.mulVec (mem_stdLattice_iff_psi₀.2 fun x hx ↦ smul_left_injective
  ℂ h (by simpa [by simpa using zeroTermFin_finHeisOp_finFrameVector D (t *ᵥ x) (w := 0) rfl,
  star_mulVec_dotProduct, m, finHeisOp.eq_1 V₀, ← M.mul_assoc] using congrArg (zeroTermFin D) (hf _
  (hK.mulVec hx) ▸ V.finHeisOp_comm y .. :).symm)), mulVec_injective_of_isUnit t.isUnit.star (by
    simpa [mulVec_sub, ← mulVec_mulVec] using! congr($eLᴴ *ᵥ _).symm)⟩

/-- If B = ig + kc is integral (i, k the frames of the splitting), some C makes, for all y, the zero
term of the vacuum translated by y equal to ζC·ω(g)ϱ_f(Bᴴy)vac, with ζ zero or a root of unity. -/
lemma zeroTermFin_finHeisOp_vacElem g (c : Matrix p _ (𝔸f E)) {B} (e : B =
  D.iAdelic.map snd * g.1.1 + D.kAdelic.map snd * c) (hB : IsIntMatrix (Ô E) B) : ∃ C, ∀ y, ∃ ζ,
  (ζ = 0 ∨ IsOfFinOrder ζ) ∧ zeroTermFin D (V.finHeisOp y V.vacElem) = (ζ * C : ℂ) • V₀.ω (1,
  g) (V₀.finHeisOp (Bᴴ *ᵥ y) V₀.vacElem) := .imp (fun C hC y ↦ by_contra fun H ↦ by
  choose l hx o using by simpa using zeroTermFin_support D 1 1 (H ⟨0, by simpa using ·⟩) (by simp)
                           (by simp_all)
  choose a w b e' using D.exists_eq_finFrameVector 1 1 (y - l)
  obtain ⟨⟨-, rfl⟩, a₂⟩ := by simpa [Sum.elim_eq_iff, o] using
    (e' ▸ Splitting.adjoint_mulVec_finFrameVector .. :)
  exact H ⟨_, .inr ((isOfFinOrder_ψf _).mul (isOfFinOrder_ψf _)), by
    nth_rw 1 [← finHeisOp_vacElem (neg_mem hx), finHeisOp_finHeisOp, map_smul, ← sub_eq_add_neg,
      zeroTermFin_finHeisOp_finFrameVector D _ e', hC, map_smul, ← show g *ᵥ Bᴴ *ᵥ (y - l) =
      w by simp [e, ← mulVec_mulVec, o, a₂]; simp [← U.inv_val_eq_conjTranspose], ← omega_finHeisOp
      _ (1, g), ← finHeisOp_vacElem (hB.isInt_conjTranspose.mulVec hx), finHeisOp_finHeisOp]
    simp [mulVec_sub, smul_comm C, mul_smul]; rfl⟩)
  (exists_eq_smul_omega_vacElem ((zeroTermFin_spec D).1 _ vacElem_mem_finitePart) fun x
  hx ↦ by rw [← zeroTermFin_finHeisOp_finFrameVector D (c *ᵥ x),
  finHeisOp_vacElem (hB.mulVec hx)]; simp [e, add_comm])

end

open Finset Fintype Grading Kronecker Matrix Space Splitting

attribute [-simp] Unitary.mul_star_self_of_mem

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι] [Fintype
  ι'] [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype X₀] [Fintype q] {ε ε' ε'' s s'
  s''} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} {N p} (Y : Grading V N X s)
  (Y' : Grading V' N X' s') {Y'' : Grading V'' N X₀ s''} {w : ι → ℤ} (Y'' : Grading V'' N X₀ s'')

/-- For integer weights on the basis of V, with J pairing only opposite weights: a rational isometry
from V'' onto the span of the basis vectors of weight zero. -/
structure GradeZeroPart (V : Space E ι ε) (V'' : Space E _ ε'') (wt : ι → ℤ) where
  index : ι'' ↪ _
  mem_range_index incl : incl ∈ Set.range index ↔ wt incl = 0
  incl : Matrix ι _ E
  incl_eq_zero a b : wt a ≠ 0 → incl a b = 0
  gram_incl : inclᴴ * V.J * incl = V''.J
  grade_add a b : V.J a b ≠ 0 → wt a + wt b = 0

omit [WeilData E] in
lemma ratCoordMatrix_sum g : (V.sum V').ratCoordMatrix (.sum g) = fromBlocks
  (V.ratCoordMatrix g.1) 0 0 (V'.ratCoordMatrix g.2) := by simp [ratCoordMatrix_eq, sum, blockGL]

attribute [local simp] Fintype.card_subtype ratCoordMatrix_inclX diagonal_apply det_inclX entrywise
  inclMatrix ratCoordMatrix_sum

/-- The splitting of V over its weight-zero part V'' whose isotropic frame k consists of the basis
vectors of positive weight. -/
def GradeZeroPart.splitting (Z : GradeZeroPart V V'' w) : V.Splitting V'' {i // 0 < w i} :=
  have := congr((fun M ↦ (trace M, M * V.J⁻¹)) (V.J⁻¹ * $(show diagonal (if 0 < w · then 1 else 0) *
    V.J = V.J * diagonal fun i ↦ 1 - ite (0 < w i) 1 0 - ite (w i = 0) 1 0 by simp; grind
    [GradeZeroPart])))
  by use inclMatrix E (↑), V.J⁻¹ * inclMatrix E (@Subtype.val ι _), Z.incl <;> simp [↓gram_incl,
    Matrix.mul_assoc, Z.mem_range_index, V.isHermitian_J.inv.eq, ← @Nat.cast_inj E,
    ← Fintype.card_range Z.index, trace_mul_comm] at * <;>
    grind [GradeZeroPart, incl_eq_zero, star_zero, Fintype.sum_eq_zero]

/-- If V'' is the weight-zero part of V, all weights even, and Y' has a string of even length,
then Hom(X', V'') is the weight-zero part of Hom(V', V). -/
def GradeZeroPart.hom (Z : GradeZeroPart V V'' w) (hs' : Even s') (hw : ∀ i, Even (w i)) :
    GradeZeroPart (V'.hom V) ((stdSpace E X').hom V'') fun r ↦ w r.1 - Y'.gradeOf r.2 := by
  use Z.index.prodMap (.trans .inl Y'.indexEquiv.toEmbedding), ?_, Z.incl ⊗ₖ inclMatrix E
    (Y'.indexEquiv ∘ .inl) <;> simp [gram_incl, hom_J, Y'.J_inv_eq_gradedGram] <;> simp [gradedGram,
    reindex_equiv Y'.indexEquiv] <;> grind [incl_eq_zero, GradeZeroPart]

/-- The adelic map (T*, T') from V' to V⁻ ⊕ V'', for the frequency maps T : Y → Y' and T' : Y' →
Y'' with constant c. -/
def stackedT := fromRows (V.formAdjoint V' (Y.stringMap Y')) (Y'.stringMap Y'')

/-- The finite part of `stackedT`, in the frame coordinates of Hom(V', V⁻ ⊕ V''),
multiplied by α⁻¹. -/
def stackedTFin := finCoord (V'.homAtPoint (flipSum V V'') (stackedT Y Y' Y''))

omit [WeilData E] in
lemma inclX_mul_stringMap_mul_inclX_inv g g' : V'.ratCoordMatrix (Y'.inclX g') * Y.stringMap Y' *
  V.ratCoordMatrix (Y.inclX g)⁻¹ = Y.stringMap Y' := by
  simp [← map_inv, stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]

variable (X'' q) in
/-- Data for two consecutive lifts Y → Y' → Y'': an identification of the grade-zero part of V⁻
⊕ V'' with X⁻ ⊕ X'' plus q hyperbolic planes, compatible with U(X) × U(X₀) and with (T*,
T'). -/
structure ArrowPair where
  zeroPart : GradeZeroPart (flipSum V V'') (hypSum q (flipSum (stdSpace E X) (stdSpace E X'')))
    (Y.gradeOf ⊕ᵥ Y''.gradeOf)
  string_spec : Odd s ∧ s' = s - 1 ∧ s'' = s' - 1 ∧ Y'.c = Y.c
  even_card_add : Even (Fintype.card ι + Fintype.card ι'')
  embX : G (n := X₀) E 1 →* G (n := X'') E 1
  det_embX k : (embX k).det = k.det
  intertwines g k : fromBlocks (V.ratCoordMatrix (Y.inclX g)) 0 0
    (V''.ratCoordMatrix (Y''.inclX k)) * zeroPart.incl.map toAdele =
    zeroPart.incl.map toAdele * (G.sum (s := hypSigns q) (1, .sum (g.neg, embX k))).mat
  gradeOne : q ↪ {l // Y'.gradeOf l = 1}
  stackedT_apply a l : stackedT Y Y' Y'' (zeroPart.index a) l = ∑ k,
    ite (l = gradeOne k) ↑(zeroPart.incl (zeroPart.index a) (.inl (.inr k)) * Y'.c) 0

variable {Y Y' Y''} (D : ArrowPair X'' q Y Y' Y'')

/-- For a pair D of consecutive lifts, Hom(X', grade-zero part of V⁻ ⊕ V'') as the degree-zero
part of Hom(V', V⁻ ⊕ V''). -/
def ArrowPair.homZeroPart := D.zeroPart.hom Y' (by grind [ArrowPair])
  (by simp [reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]; grind [ArrowPair])

/-- The splitting of Hom(V', V⁻ ⊕ V'') that removes first the maps of nonzero degree, then the
maps into the hyperbolic planes, leaving Hom(X', X⁻ ⊕ X''). -/
def ArrowPair.splitting := D.homZeroPart.splitting.comp ((removePlanes q _).homTarget _)

/-- The finite evaluation on data for Hom(V', V⁻ ⊕ V''): translate by α⁻¹(T*, T'), take the
finite zero term along `ArrowPair.splitting`, and apply a left inverse of `arrowTensor`. -/
def ArrowPair.finEval :=
  arrowTensor.leftInverse ∘ₗ (zeroTermFin D.splitting ∘L finHeisOp _ (stackedTFin Y Y' Y'')).1

lemma ArrowPair.arrowTensor_finEval (Φ Ψ : finitePart _) : arrowTensor (D.finEval (arrowProduct Φ
  Ψ.1)) = zeroTermFin D.splitting (finHeisOp _ (stackedTFin Y Y' Y'') (arrowProduct Φ.1 Ψ)) :=
  Function.LeftInverse.rightInvOn_range leftInverse_arrowTensor (range_arrowTensor.ge
  ((zeroTermFin_spec _).1 _ (finHeisOp_mem_finitePart _ (range_arrowTensor.le ⟨Φ ⊗ₜ Ψ, rfl⟩))))

/-- The constant term along `ArrowPair.splitting` intertwines the action of U(X) × U(X') × U(X₀)
through V, V', V'' with the action of (g, g', D.embX k) for X, X', X'', both normalised by the
splitting characters of a and b. -/
lemma ArrowPair.zeroTerm_splitting_tripleWeil a b g g' k f :
    D.splitting.zeroTerm (tripleWeil a b (Y.inclX g, Y'.inclX g', Y''.inclX k) f) =
  tripleWeil a b (g, g', D.embX k) (D.splitting.zeroTerm f) := by
  obtain ⟨j, rfl⟩ := D.string_spec.2.1 ▸ D.string_spec.1.tsub_odd odd_one; let w :=
    Y.gradeOf ⊕ᵥ Y''.gradeOf
  let x := G.sum ((Y.inclX g).neg, Y''.inclX k); have : ∀ i l, w i ≠ 0 ∨ w l ≠ 0 →
          (flipSum V V'').ratCoordMatrix x i l =
    ite (i = l) 1 0 := by simp [w, x, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]
  have Z := zeroTerm_omega_of_inclMatrix D.homZeroPart.splitting rfl (g := .onHom (Y'.inclX g', x))
    (g₀ := .onHom (g', .sum (1, .sum (g.neg, D.embX k)))) (u := (g.det * k.det) ^ j * g'.det⁻¹ ^ #{i
    | 0 < w i}) (C := blockDiagonal (if Y'.gradeOf · < 0 then (flipSum V V'').ratCoordMatrix x else
    1) * (blockDiagonal (if 0 < w · then (V'.ratCoordMatrix (Y'.inclX g'⁻¹))ᵀ else 1)).submatrix
    .swap .swap) ?_ ?_ (by simp [(det_classical _).symm.trans (det_blockDiagonal _), x,
    w, ↓reindex_equiv Y'.indexEquiv, ↓@prod_sum_type X', ↓Fin.prod_univ_add, prod_ite, ite_eq_right,
    ← two_mul, apply_ite Matrix.det, det_ratCoordMatrix, ← Equiv.coe_prodComm, -inv_pow]) ?_
  rcases D.zeroPart.splitting.card_eq, card_congr Y'.indexEquiv, D.2, D.3
  have R r := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget_zeroTerm_pairWeil
    (stdSpace E X') 1 1 (.sum (1, r)) _ 1 ?_
    (.trans (congrArg _ ?_) ((coord_mul_frame_mul _).2.1 r.mat).2.1)
  simp_all [x, w, pairWeil, inv_smul_eq_iff₀, splitting, zeroTerm_comp, tripleWeil, smul_smul,
    det_embX, rankTwist, Odd, Even]
  congr 1; exact mod_cast congrArg _ (Additive.ofMul.injective (by simp; match_scalars <;> omega))
  iterate 2 simp [kAdelic, iAdelic, Space.ratMap, removePlanes, hypSum, sum,
    blockGL, -coe_units_inv]
  all_goals simp [-Sum.forall, ↓reindex_equiv Y'.indexEquiv, ↓@Sum.forall X', ← map_inv,
    sum_prod_type, HasDegreeGe, blockDiagonal_apply, Matrix.ite_apply, GradeZeroPart.splitting,
    GradeZeroPart.hom, apply_ite toAdele, -sum_sum_type, homZeroPart]
  grind; grind; simp [x, hypSum, ← sum_mul, ← mul_right_comm _ (toAdele _), ← mul_assoc,
    by simpa [-Sum.forall] using D.intertwines g k]

/-- The finite evaluation `ArrowPair.finEval` commutes with the finite points of U(X) × U(X') ×
U(X₀). -/
lemma ArrowPair.finEval_inclXFin a b {g g' k k' x} (hx : Y''.inclXFin k = x) (e : D.embX (1, k) =
  (1, k')) Φ Φ' : D.finEval (arrowProduct (liftWeilFin a (Y.inclXFin g, Y'.inclXFin g') Φ).1
  (liftWeilFin b (Y'.inclXFin g', x) Φ').1) = .map (liftWeilFin a (g, g'))
  (liftWeilFin b (g', k')) (D.finEval (arrowProduct Φ Φ')) := by
  erw [← hx, ← leftInverse_arrowTensor (.map _ _ _), arrowTensor_map_liftWeilFin,
    arrowTensor_finEval, ← e, ← D.zeroTerm_splitting_tripleWeil,
    (?_ : Function.Commute (tripleWeil ..) (integrated _ _))]
  simp [finEval, zeroTermFin, finHeisOp, show finVec (stackedTFin Y Y' Y'') =
    V'.homAtPoint (flipSum V V'') (fromRows (V.formAdjoint V' (((0, 1) :
    𝔸 E) • Y.stringMap Y')) (((0, 1) : 𝔸 E) • Y'.stringMap Y'')) by ext <;> simp [finVec,
    stackedTFin, homAtPoint, matToVec, stackedT, formAdjoint,
    Prod.fst_sum, Prod.snd_sum], homHeisOp_arrowProduct, ← arrowProduct_twistedPairWeil,
    pairWeil_homHeisOp, inclX_mul_stringMap_mul_inclX_inv, -ratCoordMatrix_inclX, ← inclX_inr]
  intro; simp [tripleWeil, omega_integrated, inclX_inr, G.onHom_eq, G.sum, G.neg, ← Pi.one_def,
    MulEquiv.prodCongr]

attribute [local simp ←] Function.Embedding.toFun_eq_coe

attribute [local simp] Function.Injective G.blockEmb stringMap stringReversal Subtype.ext_iff
  stackedT flipSpace gradedGram hypSum

variable (Y Y' Y'') (H : Odd s ∧ s' = s - 1 ∧ s'' = s' - 1 ∧ Y'.c = Y.c)
  (H' : Even (Fintype.card ι + Fintype.card ι''))

/-- The pair data for strings of lengths s, s − 1 (even), s − 2: one hyperbolic plane, spanned
by the middle vectors z of Y and z'' of Y'', is removed. -/
def middlePair (h : s ≠ 1) :
  ArrowPair X₀ Unit Y Y' Y'' := let z _ := Sum.inl (Y.indexEquiv (.inr ⟨s / 2, by grind⟩))
  let z' _ := Sum.inr (Y''.indexEquiv (.inr ⟨s'' / 2, by grind⟩))
  let j := Sum.map (Y.indexEquiv ∘ .inl) (Y''.indexEquiv ∘ .inl)
  by use ⟨⟨z ⊕ᵥ z' ⊕ᵥ j, ?_⟩, ?_, fromCols (fromCols ((2 * N)⁻¹ • (inclMatrix E z - inclMatrix E
    z')) (inclMatrix E z + inclMatrix E z')) (inclMatrix E j), ?_, ?_, ?_⟩, H, H', .id _, ?_, ?_,
    ⟨fun _ ↦ ⟨Y'.indexEquiv (.inr ⟨s'' / 2, by grind⟩), ?_⟩, ?_⟩ <;> simp +zetaDelta
    [↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y'.indexEquiv, Y.2, ↓reindex_equiv Y''.indexEquiv,
    ↓Y.formAdjoint_apply Y', Y''.2, apply_ite star] <;> grind [Y.3]

/-- The pair data for s = 1 and Y'' without string, N = pp̄: no plane is removed, and z/p is
adjoined to X₀ as last basis vector of X''. -/
def lastPair (e : p * star p = N) (h : s = 1) : ArrowPair (X₀ ⊕ Unit) Empty Y Y' Y'' := let j :=
    isEmptyElim ⊕ᵥ (Sum.inl ∘ Y.indexEquiv ∘ .inl ⊕ᵥ (.inr ∘ Y''.indexEquiv ∘ .inl ⊕ᵥ fun _ ↦
    .inl (Y.indexEquiv (.inr ⟨0, h.ge⟩))))
  by use ⟨⟨j, ?_⟩, ?_, of fun a b ↦ ite (a = j b) (ite (b = .inr (.inr (.inr ()))) p⁻¹ 1) 0, ?_, ?_,
    ?_⟩, H, H', .comp (G.blockEmb (e := .refl _) Sum.elim_one_one.symm) (.inl ..), ?_, ?_,
    .ofIsEmpty <;> simp [j, ↓reindex_equiv Y.indexEquiv, ↓reindex_equiv Y'.indexEquiv,
    Y.2, ↓reindex_equiv Y''.indexEquiv, ↓Y.formAdjoint_apply Y', Y''.2, apply_ite star,
    univ_eq_empty] <;> grind [Y.3]
