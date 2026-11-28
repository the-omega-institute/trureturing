/- GID: D5/S3/Zeros/GRH/New/Seesaw/LinesStep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/LinesStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.LinesStep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/LinesStep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.EdgePair
import D5.S3.Zeros.GRH.Lib.Weil.Periods.UnfoldingStep
import D5.S3.Zeros.GRH.New.Seesaw.EqualLinesOrbit
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Support of unfolded periods: lattice lines move at most one step per lift. -/

open Matrix Gf WithZero Space Kronecker Valued Fintype WeilData MatMul Algebra
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X]
  {s s' N ε ε'} {V : Space E ι ε} {V' : Space E ι' ε'} {Y : Grading V N X s}
attribute [local simp] gradedGram ite_apply division_def v_inv smul_smul atPlace

/-- Let E be stably unramified, b an adapted basis at x with string diagonal β, and N = ππ̄
split along P. For odd s assume that for no n in `Grading.besselFin` and w in P is (nx)⁻¹K_w(X)nx ⊂
K_w(V). Then ord_w β_i + ord_{w̄} β_{s−1−i} ≥ 0 for all i, w. -/
lemma Grading.IsAdaptedAt.ideleLogVal_add_rev_nonpos {x b β P π} [StablyUnram E] (h :
  Y.IsAdaptedAt x b β) (q : IsSplitSquarefree P N π) (hg : Odd s → ∀ᵉ (n ∈ Y.besselFin) (w : P),
  ¬∀ a ∈ maxCompactAt X w, (n * x)⁻¹ * (Y.inclXFin a * (n * x)) ∈ maxCompactAt ι w)
  i w : ideleLogVal (β i) w + ideleLogVal (β i.rev) (star w) ≤ 0 := by
  have G {x b β} (h : Y.IsAdaptedAt x b β) i := by simpa [apply_ite, -ite_mul, Y.2, q.1, smul_def,
             ← log_le_log, ← ideleLogVal.eq_1] using mem_Ô.1 (h.gram_string_entry i _ le_rfl ▸
    h.2.isIntMatrix_inv.isInt_conjTranspose.mul h.2.isIntMatrix_inv _ _ :)
  have K w : ideleLogVal π w = ite (w ∈ P) (-1) 0 := by simp [ideleLogVal, q.2, apply_ite]
  wlog p : star w ≠ w ∧ Odd s ∧ i.rev = i ∧ w ∈ P generalizing w; grind [star_star, q.2 w]
  have L a w : ideleLogVal (star β⁻¹ a) w = -ideleLogVal (β a) (star w) := by simp [ideleLogVal]
  let γ a := ite (a ≤ i) (β a) (star β⁻¹ a.rev)
  let d := diagGL ((1 ⊕ᵥ γ) ∘ Y.indexEquiv.symm)
  have D : Y.IsAdaptedBasis d d γ := by constructor <;> simp [d]
  have ⟨y, o, e⟩ : ∃ y ∈ supportedOn ι {w}, d.map (evalAt w) = (V.xFin * ↑(y * x)).map (evalAt w) :=
    ⟨atSplit p.1 (.map (evalAt w) (V.xFin⁻¹ * d / x)), by simp +contextual [atSplit,
    evalAt_star_locGL, p]⟩
  have ⟨_, _, h'⟩ := Y.exists_isAdaptedAt (y * x); contrapose! hg
  obtain := D.ideleLogVal_eq h' e, (h.ideleLogVal_eq
    h' <| by simpa using mem_supportedOn.1 o · · ·), h'.ideleLogVal_le D (w := star w) (by
    simp_rw [GeneralLinearGroup.val_map_apply, Units.val_mul, coe_units_inv, inv_eq_left_inv
      (gram_mul_of_gram_eq gram_xFin (y * x).2), Matrix.map_mul,
      @id (_ᴴ.map _ = _) (evalAt_star_GL rfl _), ← e]
    simp [d, reindex_equiv Y.indexEquiv, Y.2, apply_ite, -evalAt_apply, q.1, IsIntMatrix,
      v.mem_integer_iff]
    simp [← log_le_log, ← ideleLogVal.eq_1]; grind [star_star])
  refine (h.exists_mem_besselFin h' (by grind [star_star, q.2 w])).elim fun _ ⟨k, r⟩ ↦ ⟨p.2.1, _, r,
    ⟨w, p.2.2.2⟩, fun A ⟨⟨B, a⟩, l⟩ ↦ (and_congr_left mem_Kf_iff_of_supportedOn).2 ⟨?_,
    mem_supportedOn.2 fun u b c ↦ by simpa [mul_eq_one_iff_eq_inv] using
    (Units.ext (congr($(Y.ratCoordMatrixFin_inclXFin A).map _).trans (by simp_all [-evalAt_apply,
    Units.ext_iff, ← submatrix_map])) : (V.xFin * _ * _).map _ = 1)⟩⟩
  simpa [e, mul_assoc] using mem_intGL_Ô.1 (mul_mem (inv_mem k) (mul_mem (a := MulAut.conj (d⁻¹ *
    V.xFin) _) ⟨reindexGL Y.indexEquiv (blockGL (B, 1)), by simp [Units.ext_iff, ← ext_iff, d,
    reindex_equiv Y.indexEquiv, diagGL, ← ratCoordMatrixFin.eq_1, -Matrix.mul_assoc, -coe_units_inv,
    ratCoordMatrixFin_inclXFin, ← @id (_ = A.1) a, apply_ite]⟩ k)) w

attribute [-simp] coe_units_inv in
/-- One step of `Grading.HasNearLines`: from Y, x, m, k to Y', x', m', k + 1, where s' + 1 = s and m
= m' (s odd) or m' + 1 (s even). Assume (c) = (aā), b | conj(α/a)∏_Q w, ϱ_f(b·Ô-vectors) fixes
f, `Grading.constTermAtT` of t ⊗ f is non-zero at (x, x'), and adapted bases at x' have ord_w β_i +
ord_{w̄} β_{s'−1−i} ≥ 0. Here c is the constant of the grading Y and α = `WeilData.α`. -/
lemma Grading.HasNearLines.step {Y' : Grading V' N X' s'} [WeilData E] {μ f a m m' Q k x x' t} (hx :
  Y.HasNearLines a Q m k x.2) (hm : m = m' + ite (Odd s) 0 1) (hs : s' + 1 = s) (ha : ∀ w, v ((Y.c :
  𝔸f E) w) = v ((a * star a.1) w)) (n : Y.constTermAtT Y' μ (integrated _ t f) x x' ≠ 0) b (hb :
  ∀ w, ideleLogVal (star (α / a)) w ≤ ideleLogVal b w + ite (w ∈ Q) 1 0) (hf : ∀ y ∈ stdLattice E _,
  finHeisOp _ (b.1 • y) f = f) (hg : ∀ {b β}, Y'.IsAdaptedAt x'.2 b β → ∀ i w, ideleLogVal (β i) w +
  ideleLogVal (β i.rev) (star w) ≤ 0) : Y'.HasNearLines a Q m' (k + 1) x'.2 := by
  obtain ⟨⟨B, γ, p, _⟩, rfl, rfl⟩ := hx, hs, hm
  peel Y'.exists_isAdaptedAt x'.2 with B' γ' q
  have H i : ite (Odd s' ↔ i ≤ Fin.rev i) Y.c.1 1 • (star (b / γ i.rev.succ) / α /
    γ' i).1 ∈ Ô E := ?_
  simp [apply_ite ideleLogVal, ↓ite_smul, ite_mem, mem_Ô, smul_def] at *; unfold ideleLogVal at *
  simp [ha, ← log_le_log, ← ideleLogVal.eq_1, abs_le] at *
  grind [star_star]
  choose _ _ _ D _ P L using Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  let g := (G.onHom (x, x')).2
  obtain ⟨l, hl, e⟩ := zeroTermFin_support D (b.1 • g) (star b⁻¹.1 • g) (n <| by
    simp [L, pairWeil, omega_integrated]; rw [((zeroTermFin_spec D).2 ..).choose_spec, ·]
    simp) (by simp [← U.inv_val_eq_conjTranspose]) (by simpa using congrArg (ω _ g) <| hf · ·)
  rw [show _ᴴ = (D.kᴴ * (V.hom V').J).map (algebraMap _ (𝔸f E)) * (V.hom V').xFin.1 by
    simp [← gram_inv_of_gram_eq gram_xFin, Splitting.kAdelic, ← RingHom.coe_snd]
    congr with; simp, ← mulVec_mulVec, (rfl : (xFin _).1 = V'.xFin ⊗ₖ V.xFin⁻¹.1ᵀ),
    finCoord_homAtPoint, G.onHom_snd, smul_mulVec, mulVec_sub, mulVec_smul] at e
  have h i j (h : Y'.gradeOf i < Y.gradeOf j) := by
    simpa [← Matrix.map_mul, ↓P, matToVec, ↓vecToMat_matToVec, coe_units_inv, ← mul_assoc,
      ← star_mul, mul_sub, h, ↓kronecker_mulVec_eq_matToVec] using congr(star b *
      (((V.hom V').J⁻¹ * D.k).map (↑) *ᵥ $e) (i, j))
  generalize o : V'.xFin.1 * (_ : Matrix ι' ι (𝔸f E)) = W at h
  convert (by simpa [← o, coe_units_inv, ← U.inv_val_eq_conjTranspose, inv_eq_left_inv gram_xFin,
    ← Matrix.map_mul, ← (V.J.map _).mul_assoc] using (q.2.isIntMatrix.mul (N :=
    vecToMat l) (hl ⟨·, ·⟩)).mul p.2.isIntMatrix.isInt_conjTranspose : IsIntMatrix _ (B'⁻¹.1 * W *
    (V.J⁻¹.map (↑) * B⁻¹.1ᴴ))) (Y'.indexEquiv (.inr i)) (Y.indexEquiv (.inr i.rev.succ))
  clear * - h p q; simp [stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv] at h
  simp only [Y.J_inv_eq_gradedGram, ↓map_gradedGram_mul_apply, mul_apply, Finset.sum_mul]
  rw [← sum_prod_type', sum_eq_single (Y.indexEquiv (.inr i.castSucc), Y'.indexEquiv (.inr i)) (by
    simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, stringReversal]
    grind (splits := 20) [p.inv, q.inv, IsAdaptedBasis, BlockTriangular, flagOrder, star_zero])]
  simp [stringReversal, algebraMap_eq_smul_one, ← h.2]
  grind [Y.N_spec, p.inv.3, q.inv.3, Pi.inv_apply]
