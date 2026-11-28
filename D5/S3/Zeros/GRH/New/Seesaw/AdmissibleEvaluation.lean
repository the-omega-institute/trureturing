/- GID: D5/S3/Zeros/GRH/New/Seesaw/AdmissibleEvaluation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/AdmissibleEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.AdmissibleEvaluation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/AdmissibleEvaluation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.MovedVacuumComb
import D5.S3.Zeros.GRH.New.Seesaw.EdgePair
import D5.S3.Zeros.GRH.New.Seesaw.NamesAtSplitLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Denominator control under adjoints and conjugation; membership in the glued lattice.
Evaluated vacua are admissible translates of the neighbour-lattice vacuum, the sum τ_N. -/

open AddSubgroup Finset Grading Kronecker stdLattice Matrix RingHom Space Valued Weil WeilData

variable {E n n₀ : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] {q : ℕ}

section

attribute [local simp] mem_intGL weightedTranslations

/-- For an integral finite adele β, the function on ι ⊕ κ equal to β on ι and to its conjugate
β̄ on κ. -/
noncomputable def selfOrConj {ι κ} (β : Ô E) (j : ι ⊕ κ) := ite j.isLeft β.1 (star β)

lemma mulVec_mem_weightedTranslations {M : Matrix n n₀ _} (h : IsIntMatrix (Ô E) M) {d d' y} (hy :
  y ∈ weightedTranslations q d) (h' : ∀ i j u, v (d i u) ≠ v (d' j u) → M i j (star u) = 0) :
  Mᴴ *ᵥ y ∈ weightedTranslations q d' := mulVec_eq_sum y _ ▸ sum_mem fun i _ j ↦ by
  simp_all [mem_Ô, IsIntMatrix]
  grind +splitImp [mul_left_comm, mul_le_one', mul_eq_zero]

lemma star_mem_weightedTranslations {ι X c} (h : c ∈ Ô E) {d x} (hx : x ∈ weightedTranslations q d)
  (f : X → ι) : (fun i ↦ c * star (x (f i))) ∈ weightedTranslations q (star <| d <|
  f ·) := by simp_all [mul_left_comm, mul_le_one', mem_Ô]

lemma inv_xFin_mulVec_mem_of_spansLattice {E : Type} [Field E] [CMType E]
    [Fintype n₀] {s N a π u c} {V :
  Space E n s} {Y : Grading V N (n₀ ⊕ _) q} (hL : Y.SpansLattice a π u) (x : _ → _) (h₂ :
  c ∈ Ô E) (hs : Odd q) {v} (h : ∀ i, x (.inl i) ∈ Ô E) (h₁ : star ↑π * x (.inr ()) ∈ Ô E) (hv :
  ∀ i, v (Y.indexEquiv i) = i.elim x (if 2 * ·.1 + 1 = q then u *
  (π⁻¹ * x (.inr ()) + c) else 0)) i : (V.xFin⁻¹.1 *ᵥ v) i ∈ Ô E := hL.elim fun k _ ↦ by
  simp [show v = V.xFin.1 *ᵥ k⁻¹ *ᵥ Subtype.val ∘ (((⟨_, h ·⟩) ⊕ᵥ fun _ ↦
    ⟨_, h₁⟩) ⊕ᵥ (if 2 * ·.1 + 1 = q then ⟨_, h₂⟩ else 0)) ∘
    Y.indexEquiv.symm by simp [funext_iff, reindex_equiv Y.indexEquiv, gradedLatticeBasis, *,
    diagonal, -mul_ite, entrywise, apply_ite Subtype.val]; grind [star_mul, star_one, π.inv_mul]]
  exact sum_mem (by aesop)

end


variable {E ι ι' ι'' X X' X'' μ q : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι']
  [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype μ] [Fintype q] {ε : ι → ℤˣ}
  {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  [WeilData E] {N : ℕ} [Fact N.Prime] {m : ℕ} {m' : ℕ} {m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
  {Y' : Grading V' N (X' ⊕ _) m'} {Y'' : Grading V'' N μ m''} {a : (𝔸f E)ˣ} {π : (𝔸f E)ˣ}
  {u : ↥(unitary (𝔸f E))} (κ : (X ⊕ Unit) ⊕ X'' ⊕ Unit → _) (hL' : Y'.SpansLattice a π u)
  {P : Finset (FinPlace E)} {β : Ô E} (δ : 𝔸f E) (hN : ∀ w, ↑N ∈ w.1 → δ w = 1 ∧ v (β.1 w) = 1)
  (hP : IsSplitLevel P N) (hq : IsSplitSquarefree P ↑N π) (h1 : δ * star δ = 1)
  (hG : ∀ b, star β.1 * κ b ∈ Ô E ∧ selfOrConj β b * κ b ∈ Ô E) (hκ : ∀ b, κ b = 1 ∨ κ b = δ)
  (hδ : (star α * α⁻¹).1 * divStar a = δ)

/-- The condition δc = c, π̄x integral, x integral off the two last indices e, e'', and x_e/π ≡
c, x_{e''}/π ≡ ε̄c modulo Ô, with ε = `Weil.normNegOne`. -/
def IsNeighbourVector (π : (𝔸f E)ˣ) (δ : 𝔸f E) c (x : (X ⊕ _) ⊕ q ⊕ _ → _) := δ * c = c ∧
    (∀ i ≠ .inl (.inr ()), i ≠ .inr (.inr ()) → x i ∈ Ô E) ∧ (∀ i, star ↑π * x i ∈ Ô E) ∧ c - π⁻¹ *
    x (.inl (.inr ())) ∈ Ô E ∧ star normNegOne.1.1 * c - π⁻¹.1 * x (.inr (.inr ())) ∈ Ô E

/-- For some C, all n prime to N and all y with d_i y_{ij} integral away from n: L(ϱ_f(y)vac) is an
admissible combination (`IsAdmissibleComb`), of size ≤ 1 and denominator |Ô/β|^{(|X|+|μ|+2)|X'|}, of
the C·`translateSum`(ϱ_f(t)vac ⊗ ϱ_f(t')vac), β̄t and β̄t' integral away from n. -/
def IsAdmissibleEval (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E)) (β : Ô E) (L :
  𝒮 (V'.hom (flipSum V V'')) → _) (d : _ := selfOrConj β) := ∃ C : ℂ, ∀ n q, N.Coprime n →
  ∀ y ∈ weightedTranslations n (d ·.1), IsAdmissibleComb (fun t ↦ C • translateSum X X' P N μ
  (heisFinPart _ t.1 ⟨_, vacElem_mem_finitePart⟩ ⊗ₜ heisFinPart _ t.2 ⟨_, vacElem_mem_finitePart⟩))
  (translations _ n (star β) ×ˢ translations _ n (star β)) n (.card (((X ⊕ Unit) ⊕ μ ⊕ Unit) × X' →
  _ ⧸ Ideal.span {β})) q 1 (L (finHeisOp _ y (vacElem _)))

attribute [local push_cast] Pi.add_apply star_add star_mul' star_natCast star_one star_star
  star_sub in
include hN hP hq h1 hG hκ in
/-- Let N = ππ̄ along P, δδ̄ = 1, δ = 1 and β a unit above N, κ_b ∈ {1, δ} with βκ, β̄κ integral
as in hG. Some unitary k = diag(κ)γ ⊗ 1 has γ = 1, b = 0 off P ∪ P̄, each (b_j, column j of
γ) in `IsNeighbourVector`, and ω(1,k) followed by the left inverse of `arrowTensor`
satisfies `IsAdmissibleEval` for β, κ. -/
lemma exists_isAdmissibleEval_std : ∃ k : Gf E (_ × X'), ∃ γ, ∃ b : _ → _, k.1.1 =
  (diagonal κ * γ) ⊗ₖ 1 ∧ (∀ w, ¬(w ∈ P ∨ star w ∈ P) → ∀ j, evalAt w (b j) = 0 ∧ ∀ i,
  evalAt w (γ i j) = ite (i = j) 1 0) ∧ (∀ j, IsNeighbourVector π δ (b j) (γ · j)) ∧
  IsAdmissibleEval N P β (arrowTensor.leftInverse <| ω _ (1, k) ·) (selfOrConj β * κ) := by
  let k := U.of isUnit_one (diagonal κ) (by simp [funext_iff]; grind [star_one])
  let j : Ô E := ⟨_, idem_mem_Ô P⟩; let S := star ⁻¹' SetLike.coe P; have K :=
    hP.disjoint_star.preimage star
  have b : (j.1 * j, j * δ, π.1 * π⁻¹) = (j.1, j.1, 1) := by
    simp_all [j, DFunLike.ext_iff (F := 𝔸f E), idem_apply, hP.natCast_mem_iff]
  let ϖ := j + ⟨(1 - j) * π⁻¹, by simp +contextual [j, ← idem_compl, idem_mul_mem_Ô, v_inv, hq.2]⟩
  let p : Ô E := ⟨star π, by simp [mem_Ô, hq.2]; intro; split <;> tauto⟩
  let c : Ô E := normNegOne.1; let l := c * j; let d := p * (j * star p - j - star j) + star j
  have a := congr(($b, $(idem_mul_star hP.disjoint_star), $h1, $(hq.1), $(star_normNegOne_mul_self
    (E := E)), star $b))
  push_cast [Prod.star_def] at a
  let T := (X ⊕ Unit) ⊕ X'' ⊕ Unit
  let e : T := .inl (.inr ()); let e' : T := .inr (.inr ())
  let A := star π⁻¹.1 * d
  let θ (i m : T) : Ô E := ⟨ite (i = m) 1 0, by simp [ite_mem]⟩
  let ρ i := θ i e + star l * θ i e'
  let n (y : X' → P → ZMod N) (i : _ × _) := c * ρ i.1 * star (residueOverN (y i.2))
  have O {x} (y : Ô E) (e : x = y.1 := by
    push_cast +zetaDelta [q, of_apply, kv, ↓hv, ← star_idem]
    clear * - a; grind [star_zero, star_one]) : x ∈ Ô E := e ▸ y.2
  obtain ⟨γ, q⟩ : ∃ γ : Gf E T, γ.1.1 = of fun i m ↦ θ i m + A * (θ e m + l * θ e' m) * ρ i :=
    ⟨U.of isUnit_one _ (by
      simp +zetaDelta [entrywise, mul_add, add_mul, apply_ite star]; clear * - a; grind), rfl⟩
  have hv x i : (γ *ᵥ x) i = x i + A * (x e + l * x e') * ρ i := by
    simp [entrywise, q, θ, T, add_mul, mul_add]; ring
  let h : Gf E T →* Gf E (_ × X') := (U.kron (one_mul 1) (by simp)).comp (.inr ..)
  have kv γ x q : ((h γ).1.1 *ᵥ x) q = (γ.1.1 *ᵥ (x ⟨·, q.2⟩)) q.1 := by
    simp [h, entrywise, Fintype.sum_prod_type]
  let Z := (stdSpace E X').hom (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))
  have s {ι : Type} [Fintype ι] (v : ι → _) : semichar (star j.1 * v ·) = 1 := by
    simp [semichar, entrywise, j, mul_mul_mul_comm _ (star _), idem_mul_star hP.disjoint_star]
  refine ⟨h (γ * k), γ, fun m ↦ A * π⁻¹ * (l * θ e' m + star j * θ e m), by
    simp [h]; ext1; simp +zetaDelta [q]; clear * - a hκ; grind, have u w h i := (by
    simp +zetaDelta [*, not_or.1 h, star_idem, apply_ite (· w : 𝔸f E → _)]); ⟨u, fun m ↦ ⟨by
    simp +zetaDelta; grind, by simp +zetaDelta [q, ite_mem], fun i ↦ O (p * θ i m + d * star (ρ m) *
    ρ i), O (-ϖ * θ e m), O (-ϖ * θ e' m)⟩, ?_⟩⟩
  obtain ⟨C, H⟩ : ∃ C : ℂ, ∀ f, Z.ω (h γ) (Z.projOn S f) = C • ∑ y, Z.finHeisOp (star j.1 * n y ·)
      (Z.projOn S f) := ⟨_, fun f ↦ by
    nth_rw 1 [← name_boxIndicator K, ω_name_on K _ (Gf.mem_supportedOn.2 fun w a b ↦ by
      ext; simp [Gf.atPlace, h, u w (not_or.2 ⟨star_star w ▸ b, a⟩), ← ite_and, and_comm,
      Prod.ext_iff, apply_ite (evalAt w)]),
      (?_ : (boxIndicator _ _ <| _ *ᵥ ·) = ∑ y, (boxIndicator _ S <| · + n y))]
    · simp +zetaDelta only [finHeisOp, s, one_smul, map_sum, _root_.sum_apply,
        ← IsSchwartzBruhat.schrodingerAct_idem K,
        name_schrodingerAct_boxIndicator K, smul_smul, show idem S.conjClosure * idem S = idem S by
        ext; simp +contextual [idem_apply]]; rw [← star_idem]; rfl
    ext x; obtain ⟨x, rfl⟩ := mulVec_surjective_iff_isUnit.2 (h γ).1.isUnit x
    choose b B using fun i ↦ hP.exists_sub_residueOverN_mem_iff (l * π⁻¹.1 * star (x (e, i)))
    have z y : h γ *ᵥ x + n y ∈ integralBox _ S ↔ x ∈ integralBox _ S ∧ b = y := by
      simp_rw [mem_integralBox]; exact
        ⟨fun r ↦ have H i := (B i (y i)).1 (O (c * star ⟨_, r (e, i)⟩))
        ⟨fun i ↦ O (⟨_, r i⟩ - ρ i.1 * (⟨_, r (e, i.2)⟩ + c * ϖ * star ⟨_, (H i.2).1⟩)), funext
          (H · |>.2)⟩, fun r i ↦ O (⟨_, r.1 i⟩ - ρ i.1 * (⟨_, r.1 (e, i.2)⟩ + c * star ⟨_, (B i.2
        (y i.2)).2 ⟨O (p * c * star ⟨_, r.1 (e, i.2)⟩), congrFun r.2 _⟩⟩))⟩
    simp [z, ite_and]; rfl⟩
  simp only [← Prod.one_mk_mul_one_mk, map_mul]
  refine ⟨finMultiplier (h k) * C, fun Q _ o x hx ↦ ((isAdmissibleComb_weil_vacElem Z (A :=
    (weightedTranslations Q (selfOrConj β ·.1)).carrier) (one_mul _) (fun y hy i w e ↦ ?_) ?_
    (by simp)).map (arrowTensor.leftInverse ∘ₗ (Z.ω (h γ)).1)).of_eq_isOfFinOrder_smul fun p hp
    ↦ ⟨semichar (fun (a, b) ↦ p (.inl b, a)) ^ 2, (isOfFinOrder_ψf _).pow, ⟨_, _⟩,
    ⟨star_mem_weightedTranslations c.2 hp fun q ↦ (.inl q.2, q.1), fun q ↦ hp (.inr q.1, q.2)⟩, ?_⟩⟩
  · simpa [kv, k, mul_assoc] using
      add_mem hx (fun i w _ ↦ mem_Ô.1 (mul_mem (hG _).2 (hy i)) w) i w e
  · erw [mul_one_div, ← Complex.ofReal_pow, norm_finMultiplier_sq]
    refine div_mem_integralAway (k := 0) (.trans (dvd_index_map _ (f := .mk' ((Ô E ∙ β).mkQ ⟨_,
      star_mem_Ô <| ·.2 ·⟩) (by simp; tauto)) fun x hx i ↦ ?_) ((index_dvd_card _).mul_right _))
    obtain ⟨z, hz⟩ := (Ideal.Quotient.eq_zero_iff_dvd ..).1 congr($hx i)
    simpa [kv, k, mul_left_comm (κ _), mul_assoc, eq_star_of_eq_star
      congr($(hz).1).symm] using! mul_mem (hG _).1 (star_mem_Ô z.2)
  erw [← leftInverse_arrowTensor (_ • _)]
  simp [translateSum, arrowTensor, smul_sum,
    smul_smul, by simpa +contextual [projOn_finHeisOp, mem_integralBox, S, idem_mul_mem_Ô, or_comm,
    ← hP.natCast_mem_iff, (by simpa +contextual [selfOrConj, apply_ite, hN] using
    (fun i w ↦ hp i w ∘ w.2.notMem_of_isCoprime_of_mem o.cast))] using H (Z.finHeisOp p Z.vacElem)]
  simp [← arrowProduct_vacElem, finHeisOp_arrowProduct, s, Z, smul_smul, mul_comm (_ * C)]; congr! 7
  all_goals simp +zetaDelta [apply_ite star]; clear * - a; grind [star_mul', idem_mul_residueOverN]

include hL' hN hP hq h1 hG hκ hδ in
/-- In the setting of `exists_isAdmissibleEval_std`, with Y' of lattice `Grading.SpansLattice` a π u
and δ = (ᾱ/α)(a/ā): if the embedding of X⁻ ⊕ X'' respects the weights (hA) and maps scaled
`IsNeighbourVector` vectors into the lattices of V, V'' (hM), then `ArrowPair.finEval` satisfies
`IsAdmissibleEval` for β and κ = 1. -/
lemma isAdmissibleEval_finEval (D : ArrowPair _ q Y Y' Y'') (hA : ∀ i b, D.zeroPart.incl i
  (.inr b) = 0 ∨ ∀ w, v (selfOrConj β i w) = v ((selfOrConj β b * κ b) w)) (hM : ∀ s t,
  s * (divStar a).1 = star normNegOne.1.1 * δ ∧ t * s = 1 → ∀ x c, IsNeighbourVector π δ c x → ∀ v,
  v = D.zeroPart.incl.map (↑) *ᵥ ((0 ⊕ᵥ fun _ ↦ s * u * c) ⊕ᵥ ((fun _ ↦ s) ⊕ᵥ 1) * κ * x) → ∀ i,
  Sum.elim (V.xFin⁻¹.1 *ᵥ t • v ∘ .inl) (V''.xFin⁻¹.1 *ᵥ v ∘ .inr) i ∈ Ô E) :
  IsAdmissibleEval N P β D.finEval := by
  choose k γ b hk hγ hf C H using
    exists_isAdmissibleEval_std (X' := X' ⊕ Unit) κ δ hN hP hq h1 hG hκ
  let f := algebraMap E (𝔸f E)
  let S := removePlanes q (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))
  let s := (star (flipIdele normNegOne 1)).map (snd _ (𝔸f E)).1; let J :=
    inclMatrix (𝔸f E) (Y'.indexEquiv ∘ .inl)
  have xV : (flipSum V V'').xFin⁻¹.1 = fromBlocks (s⁻¹.1 • V.xFin⁻¹.1) 0 0 V''.xFin⁻¹.1 := by
    simp [s, xFin, sum, flipSpace, ← map_inv, ← smul_eq_mul_diagonal, entrywise]
  let c := of fun (_ : q) l ↦ s.1 * u * b l
  let M := (of fun j ↦ (0 : q → _) ⊕ᵥ (c · j) ⊕ᵥ ((fun _ ↦ s.1) ⊕ᵥ 1) * κ * (γ · j))ᵀ
  have hK : M = S.i.map f * ((flipSum (stdSpace ..) (stdSpace ..)).xFin.1 * (diagonal κ * γ)) +
    S.k.map f * c := by
    simp [entrywise, M, S, removePlanes, s, xFin, sum, flipSpace, ← mul_assoc, diagonal_apply]
  let B := ((flipSum V V'').xFin⁻¹.1 * (D.zeroPart.incl.map f * M)) ⊗ₖ (Jᵀ * V'.xFin.1)ᵀ
  have hB i j : B i j ∈ Ô E := hL'.elim fun k ⟨h, e⟩ ↦ by
    refine mul_mem (?_ : (_ *ᵥ _) _ ∈ _) (by cases j.2 <;> simp [e, gradedLatticeBasis, J,
      entrywise, inclMatrix, reindex_equiv Y'.indexEquiv, show ¬Odd m' by grind [D.string_spec],
      mem_intGL.1 h]); simp [xV, fromBlocks_mulVec, ↓← mulVec_smul, -coe_units_inv]; apply hM _ _
      ⟨by simp [s, val_flipIdele, ← hδ, mul_assoc], s.inv_mul⟩ _ _ (hf _) _ rfl
  choose C₃ ζ hζ R using zeroTermFin_finHeisOp_vacElem D.splitting k (fromRows 0 (c ⊗ₖ 1)) (by
    simp [Splitting.iAdelic, Splitting.kAdelic, Space.ratMap, ArrowPair.splitting, Splitting.comp,
      Splitting.homTarget, hom, GradeZeroPart.splitting, ArrowPair.homZeroPart, GradeZeroPart.hom,
      ← coe_snd, ← coe_comp, *, B, S, J, inclMatrix, xFin, f, toAdele, ← map_inv, add_kronecker,
      ← submatrix_map, Matrix.mul_assoc, Matrix.mul_add, map_kronecker, ↓transpose_mul]) hB
  have τ : Bᴴ *ᵥ stackedTFin Y Y' Y'' = 0 := by
    delta stackedTFin; erw [conjTranspose_kronecker, finCoord_homAtPoint,
      kronecker_mulVec_eq_matToVec _ _ᴴ]
    simp [↓vecToMat_matToVec, Matrix.mul_assoc, show (Jᵀ * V'.xFin.1)ᴴ =
      V'.xFin⁻¹.1 * J by simp [inv_eq_left_inv V'.gram_xFin, J, entrywise, Y'.gram_eq, gradedGram,
      inclMatrix, reindex_equiv Y'.indexEquiv], show (stackedT Y Y' Y'').map (·.2) * J = 0 by
      simp [J, mul_inclMatrix, entrywise, stackedT, Y.formAdjoint_apply Y', stringMap,
        stringReversal, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]]
  refine ⟨C₃ * C, fun n r hS y hy ↦ ?_⟩
  simp [ArrowPair.finEval, finHeisOp_finHeisOp, R, -omega_finHeisOp, τ, mul_smul]
  refine .smul_of_eq_zero_or_isOfFinOrder (.smul_of_eq_zero_or_isOfFinOrder
    ((H n r hS _ (mulVec_mem_weightedTranslations hB hy fun i j u h ↦ ?_)).map (C₃ • .id))
    (hζ _)) (.inr (isOfFinOrder_ψf (E := E) _))
  refine mul_eq_zero_of_left ((map_sum (evalAt _) ..).trans (sum_eq_zero fun l _ ↦ (hA l j.1).elim
    (fun e ↦ mul_eq_zero_of_right _ ((map_sum (evalAt _) ..).trans (sum_eq_zero ?_))) fun e ↦ ?_)) _
  · simp [M, c, e, -evalAt_apply, -mul_eq_zero, hγ (star u) fun a ↦ h (by
      simp [or_comm, ← hP.natCast_mem_iff] at a
      cases hκ j.1 <;> simp [selfOrConj, apply_ite, ite_apply, *])]
  obtain ⟨_ | _, _⟩ := i <;> cases l <;> first | cases h (e u) | simp [xV]
