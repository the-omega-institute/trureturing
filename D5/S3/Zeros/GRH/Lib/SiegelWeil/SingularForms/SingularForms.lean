/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/SingularForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.SingularForms.SingularForms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/SingularForms/SingularForms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSumNegation
import D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms.AdaptedHom
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Singular forms are governed by their coefficients at unimodular indices. The
setting here is adelic, unitary and not holomorphic, and singularity comes from one split place.
Only the vanishing half is proved, by induction on the index of a lattice in its dual. Source: E.
Freitag, Singular Modular Forms and Theta Relations, Lecture Notes in Math. 1487, Springer 1991; see
also J.-S. Li, Automorphic forms with degenerate Fourier coefficients, Amer. J. Math. 119 (1997).

This file: Adapted hyperbolic splittings compose, reindex and factor in stages. Coefficient at a
degenerate index; definition of invariance under the radical at split places. Fourier expansion
along a larger isotropic space; coefficient vanishes with singular-index ones. Singular forms:
coefficients vanish if unimodular ones do, by induction on lattice index. -/

noncomputable section

section

open Matrix Space Splitting Fintype Equiv
variable {E : Type} [Field E] [CMType E] [WeilData E] {n m p q n₁ : Type} [Fintype n] [Fintype m]
  [Fintype p] [Fintype q] [Fintype n₁] {s : n → ℤˣ} {t : m → ℤˣ} {V' : Space E m t}
  {V : Space E n s} (D : V'.Splitting V p) [h : IsBaseAdapted D]

instance : IsBaseAdapted D.symm := ⟨h.1.of_eq_submatrix_mul (.map .swap _) .one (by aesop)⟩

omit [WeilData E] in
lemma isIntMatrix_kAdelic_and_lCoord : let O := (Ô E).comap (.snd ..); IsIntMatrix O D.kAdelic ∧
    IsIntMatrix O D.lCoord := h.rec
  (by simp_all [IsOrthoIntegral, IsIntMatrix, lCoord, stdForm, star_mem_Ô])

attribute [local simp] kAdelic lAdelic iAdelic Splitting.comp hypSum Space.ratMap

lemma exists_isBaseAdapted_reindex (e : Unit ≃ p) : ∃ A' : V'.Splitting V _, IsBaseAdapted A' ∧
  A'.k = D.k.submatrix id e ∧ A'.i = D.i := ⟨splittingOfGram _ (congr(submatrix $D.gram_eq_hypSum
  (.map (.map e e) _) _).trans (by aesop)) (card_congr e ▸ D.card_eq),
  ⟨h.1.of_eq_submatrix_mul (.map (.map e e) _) .one (by aesop)⟩, rfl, rfl⟩

/-- An adapted splitting D of V′ over V factors in two stages: for a bijection e from n₁ ⊕ q to p,
some adapted splitting of V′ over V plus q planes, followed by removing these planes, has the frame
k (reindexed) and embedding i of D. -/
lemma exists_isBaseAdapted_stage (e : _ ≃ p) : ∃ A₁ : V'.Splitting _ n₁, IsBaseAdapted A₁ ∧
    (A₁.comp (removePlanes q V)).k = D.k.submatrix id e ∧ (A₁.comp (removePlanes ..)).i = D.i :=
  let ε := (sumAssoc ..).symm.trans (((sumSumSumComm ..).trans (e.sumCongr e)).sumCongr 1)
  by refine' ⟨splittingOfGram _ (congr(submatrix $D.gram_eq_hypSum ε _).trans _) _,
    ⟨h.1.of_eq_submatrix_mul ε (.block_diag .one (isOrthoIntegral_hypSpace.1.block_diag .one)) _⟩,
    _⟩ <;> simp +arith [D.card_eq, entrywise, ε, ← card_congr e, removePlanes,
    sum, splittingOfGram, toCols₁, toCols₂]

open MatMul

instance {r} {W : Space E n₁ r} {A : V.Splitting W q} [h' : IsBaseAdapted A] :
  IsBaseAdapted (D.comp A) := ⟨(h.1.mul (.block_diag .one h'.1)).of_eq_submatrix_mul
  (sumAssoc .. ∘ .map (sumSumSumComm ..) _) .one (by aesop)⟩

end

namespace Space.Splitting

open Matrix MatMul WeilData

section

variable {E n n₂ p : Type _} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n₂] [Fintype p]
  {s : n → ℤˣ} {s₂ : n₂ → ℤˣ} {W : Space E n s} {W₂ : Space E n₂ s₂}
  {W₀ : Space E _ (hypSigns p ⊕ᵥ s₂)} (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)
  (T : Matrix p p E) (f : G E s → ℂ)

omit [WeilData E] in
@[simp] lemma symm_adelic (A : W.Splitting W₂ p) : A.symm.kAdelic = A.lAdelic ∧ A.symm.iAdelic =
  A.iAdelic ∧ A.symm.lCoord = A.kCoord ∧ A.symm.iCoord = A.iCoord ∧ A.symm.symm = A := by tauto

omit [WeilData E] in
@[simp] lemma comp_lCoord : (A.comp B).lCoord =
  fromRows A.lCoord (B.lCoord * A.iCoord) := by simp [lCoord, iCoord, comp_kAdelic]

/-- The Fourier coefficient of f along the composite of the splittings A (one isotropic line)
and B, at the index with first row σ and remaining rows (0 T). -/
abbrev borderedCentreCoeff σ := (A.comp B).centreCoeff (fromRows σ (fromCols 0 T)) f

/-- For every first row σ, the coefficient `Space.Splitting.borderedCentreCoeff` of f agrees at g
and νg whenever ν = 1 + ē·kc − e·a with ck = 0, k the isotropic vector of A. -/
def RadicalInvariant (e : 𝔸 E) g := ∀ ⦃σ ν⦄ (c : Matrix Unit n (𝔸 E)) a, c * A.kAdelic = 0 →
  ν.mat = 1 + (star e •
  (A.kAdelic * c) - e • a) → A.borderedCentreCoeff B T f σ (ν * g) = A.borderedCentreCoeff B T f σ g

end

variable {E n n₁ n₂ p : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n₁]
  [Fintype n₂] [Fintype p] {s : n → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {W : Space E n s}
  {W₀ : Space E _ (hypSigns p ⊕ᵥ s₂)} {W₁ : Space E n₁ s₁} {W₂ : Space E n₂ s₂}
  {A : W.Splitting W₀ Unit} {B : W₀.Splitting W₂ p} {D : W.Splitting W₁ p}
  (hD : D.kAdelic = A.iAdelic * B.kAdelic) {f : G E s → ℂ} {T : Matrix p p E}
  (hf : IsAutFunction W f)

/-- The shift u ↦ u − k_B xᴴ of the isotropic vector u of A by the frame of B: a central element of
the radical for the opposite of A followed by B. -/
def shearElt (B : W₀.Splitting W₂ p) x := (A.symm.comp B).radicalCentre (fromBlocks 0 x 0 0)

attribute [local simp] AddChar.map_add_eq_mul fromBlocks_add Matrix.map_neg trace
  comp_kAdelic radicalElt_mul_iAdelic
  radicalElt_mul_kAdelic shearElt mem_ratMatrices mul_assoc ratAdeles sub_eq_add_neg

lemma actsOnFrame_shearElt (B : W₀.Splitting W₂ p) x :
  (A.comp B).ActsOnFrame (A.shearElt B x) (fromBlocks 1 0 (-xᴴ) 1) := by aesop

/-- Let f be automorphic, S non-empty, and `Space.Splitting.RadicalInvariant` hold at g for the
idempotent of S. If the coefficient `Space.Splitting.borderedCentreCoeff` at σ, g is non-zero, it
equals the coefficient at index σ = 0 at every n(c, z)g, n = `Space.Splitting.radicalElt`. -/
lemma RadicalInvariant.borderedCentreCoeff_radicalElt_mul (hf : IsAutFunction W f) {S g σ} (h :
  A.RadicalInvariant B T f (idemAdele S) g) (he : S.Nonempty) (k : A.borderedCentreCoeff B T f σ
  g ≠ 0) z : ∀ c, A.borderedCentreCoeff B T f 0 (A.radicalElt c z * g) = A.borderedCentreCoeff B T f
  σ g := (isDualFamily_ratMatrices.6 σ ((denseRange_rat_matrix_add he 1).eq (fun r ↦
  (mul_eq_right₀ k).1 (.trans (by rw [← borderedCentreCoeff, h (-_)
  (-_) _ (by simpa [↓mat_radicalCentre] using add_comm ..)] <;> simp [entrywise, ← map_mul,
  ← map_sum]) (centreCoeff_radicalCentre_mul _ hf (idemAdele S • fromCols r.2 0) _)))
  (isDualFamily_ratMatrices.1 σ).1)).symm ▸ (denseRange_rat_matrix_add he W₀.x).eq fun ⟨Y, y⟩ ↦ by
  rw [borderedCentreCoeff, ← add_sub_cancel _ z, ← A.radicalElt_mul _ 0, mul_assoc,
    centreCoeff_rat_mul _ hf _ (A.radicalElt_mem_Gamma Y (by simp)) (fromBlocks 1 (Yᴴ * W₀.J *
    B.k) 0 1) (by simp [← Matrix.mul_assoc, add_comm, kAdelic.eq_1 B, map_J, -mul_assoc])]
  generalize z - _ = z; simp
  rw [← centreCoeff_radicalCentre_mul _ hf (fromBlocks (toAdele (2 * j : E)⁻¹ • z) 0 0 0),
    ← mul_assoc, ← borderedCentreCoeff, h (yᴴ * stdForm E
    (hypSigns p ⊕ᵥ s₂) * (A.iCoord - toAdele (2⁻¹ : E) • idemAdele S • y * A.lCoord))
    (A.iAdelic * y * A.lCoord)] <;> simp [Splitting.radicalElt]
  match_scalars <;> grind

include hD hf

omit hf in
lemma radicalCentre_eq_comp M : D.radicalCentre M = (A.comp B).radicalCentre (fromBlocks 0 0 0 M) :=
  G.ext_mat (by simp_all [lCoord])

lemma isContPeriodic_centreCoeff X : IsContPeriodic (ratMatrices ..) (D.centreCoeff T f <|
  (A.comp B).radicalCentre · * X) := ⟨by fun_prop, by simp_all [D.centreCoeff_rat_mul hf T _ 1]⟩

/-- Let D split W along the image of the isotropic frame of B, and f be automorphic. The Fourier
coefficient along the composite of A and B, at the block index [[σ, a], [η, T]], is the same
for f and for its coefficient along D at T. -/
lemma centreCoeff_centreCoeff {R X} : let F := (A.comp B).centreCoeff R; F
    (D.centreCoeff R.toBlocks₂₂ f) X = F f X :=
  R.fromBlocks_toBlocks ▸ by
  refine' .trans (by
    simp [centreCoeff, ← quotMean_const_mul, radicalCentre_eq_comp hD, mul_left_comm]
    rfl) (quotMean_quotMean _
  (isDualFamily_ratMatrices.isContPeriodic_mul (isContPeriodic_radicalCentre _ hf _) _) _
  (.comp (.mk' (fromBlocks 0 0 0) _) (.snd ..) +
  .fst ..) (.add _ _) _ (⟨⟨·, 0⟩, _⟩)) <;> simp_all [add_mem] <;> fun_prop

/-- Let f be automorphic, det T ≠ 0, and D have the isotropic frame k of B carried into W. If
the coefficients `Space.Splitting.borderedCentreCoeff` vanish for all σ at all shears s_x X
(`Space.Splitting.shearElt`), the T-th coefficient along D vanishes at X. -/
lemma centreCoeff_eq_zero_of_shearElt (hT : det T ≠ 0) {X} (H : ∀ x σ, A.borderedCentreCoeff B T f σ
  (A.shearElt B x * X) = 0) : D.centreCoeff T f X = 0 := by simpa using
  (IsDualFamily.eq_zero_of_coeff (isContPeriodic_centreCoeff hD hf _) (fun R k ↦ by
  have e := sub_eq_zero.1 (isDualFamily_ratMatrices.6 (R.toBlocks₂₂ - T)
    fun N ↦ by simpa [entrywise, add_mul, field, AddChar.map_neg_eq_inv] using! (k _ _ (by
                 simpa [add_comm ·, radicalCentre_eq_comp hD] using
                   D.centreCoeff_radicalCentre_mul hf N _) :))
  let x := -(T⁻¹ * R.toBlocks₂₁)ᴴ
  rw [← centreCoeff, ← e, centreCoeff_centreCoeff hD hf, ← H (x.map toAdele) ((R.toBlocks₁₁ +
    R.toBlocks₁₂ * xᴴ).fromCols (R.toBlocks₁₂ + x * T)), borderedCentreCoeff, centreCoeff_rat_mul _
    hf _ (by simp) (fromBlocks 1 0 (-xᴴ) 1)] <;> aesop (add simp fromBlocks_toBlocks)) 0)

end Space.Splitting

open AddSubgroup Matrix Circle RingHom NumberField WeilData G Gf Space Splitting Prod MatMul
  stdLattice
variable {E n n₁ n₂ p : Type} [Field E] [CMType E]
  [Fintype n] [Fintype n₁] [Fintype n₂] [Fintype p] {s : n → ℤˣ} {s₁ : n₁ → ℤˣ}
  (S : Set (FinPlace E)) {W : Space E n s} {W₁ : Space E n₁ s₁} {f : G E s → ℂ}
  {D : W.Splitting W₁ p} (hK : HasLevel f (Kf E n ⊓ supportedOn n S)) (hf : IsAutFunction W f)

attribute [-instance] Prod.instNonAssocRing

section

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {s : n → ℤˣ}
  (S : Set (FinPlace E))

/-- The ring of adeles that are integral at the places of S ∪ S̄. -/
def closureIntegers : Subring (𝔸 E) := by
  use! {x | (idemAdele S.conjClosure * x).2 ∈ Ô E} <;> simp [Ô, idem_apply, ite_mem] <;> bound

/-- The endomorphism of the adelic unitary group that keeps the components on S ∪ S̄ and
replaces all others by 1. -/
def closurePart : G E s →* G E s := .prodMap 1 (componentOn n S)

end

variable {S}

@[simp high] lemma idemAdele_cj_mul_self : idemAdele S.conjClosure * idemAdele S.conjClosure =
  idemAdele S.conjClosure := by simp [idem_mul_self]

@[simp] lemma star_idemAdele_cj : star (idemAdele S.conjClosure) =
  idemAdele S.conjClosure := by aesop

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Set (FinPlace E)} in
instance : IsStarStable (closureIntegers S) := ⟨(by simpa [closureIntegers] using star_mem_Ô ·)⟩

@[simp] lemma mat_closurePart g : (closurePart (s := s) S g).mat =
  idemAdele S.conjClosure • g.mat + (1 - idemAdele S.conjClosure) • 1 := by
  ext <;> simp [closurePart, componentOn, U.cutAt, cutGL] <;> bound

variable [WeilData E]

variable (E) in
/-- The idele ȷκκ̄, with κ = `WeilData.scaleIdele`; its finite part is ȷαᾱ. -/
def invDifferentIdele :=
  .map (toAdele (E := E)) (.mk0 (j : E) j_ne_zero) * scaleIdele E * star (scaleIdele E)

/-- Siegel's T[γ] = γᴴTγ for a rational matrix T and an adelic matrix γ, divided by the idele δ
= ȷκκ̄ (`invDifferentIdele`). -/
def siegelBracket (T : Matrix p p E) γ := (invDifferentIdele E)⁻¹.1 • (γᴴ * T.map toAdele * γ)

lemma star_invDifferentIdele_inv : star (invDifferentIdele E)⁻¹.1 = -(invDifferentIdele
  E)⁻¹.1 := by simp [invDifferentIdele, mul_left_comm]

attribute [local simp] actsOnFrame_shearElt smul_smul mul_sub sub_mul stdAddChar star_mem_Ô
  siegelBracket

lemma closurePart_radicalElt c z : closurePart S (D.radicalElt c z) = D.radicalElt (idemAdele
  S.conjClosure • c) (idemAdele S.conjClosure • z) := ext_mat (by simp [radicalElt]; module)

attribute [-simp] map_smul

lemma closurePart_radicalCentre M : closurePart S (D.radicalCentre M) =
  D.radicalCentre (idemAdele S.conjClosure • M) := ext_mat (by simp; module)

include hK hf

omit hK in
lemma centreCoeff_mul_radicalCentre {T X g c} (hX : closurePart S X = closurePart S g) (h :
  D.ActsOnFrame g c) M : psi₀ E (idemAdele S.conjClosure * (M * siegelBracket T c).trace).2 *
  D.centreCoeff T f (X * closurePart S (D.radicalCentre M)) = D.centreCoeff T f X := by
  erw [psi₀_apply, ← snd_mul (invDifferentIdele E).1, mul_left_comm,
    ← D.centreCoeff_radicalCentre_mul hf (idemAdele S.conjClosure • (c * M * cᴴ)) X]
  congr! 2 <;> simp [M.trace_mul_cycle', ← closurePart_radicalCentre]
  exact ext_mat (by simpa [← hX,
    smul_sub] using congr((closurePart S $(D.mul_radicalCentre h M)).mat))

/-- After Freitag: let f be automorphic, fixed by integral points on S, with
`Space.Splitting.RadicalInvariant` along an extra line; det T ≠ 0. If its T-coefficient vanishes at
points acting on the frame by γ on S with δ⁻¹γᴴTγ unimodular, it vanishes at all points
supported on S ∪ S̄.

Known result: Singular forms are governed by their coefficients at unimodular indices. -/
lemma freitag {T U s₂ W₀} {W₂ : Space E n₂ s₂} (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)
    [IsBaseAdapted A] [IsBaseAdapted B] (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hT :
  T.det ≠ 0) (he : U.Nonempty) (hl : ∀ A : W.Splitting .., D.kAdelic = A.iAdelic * B.kAdelic → ∀ g,
  mat g * (1 - idemAdele S.conjClosure) • D.kAdelic = (1 - idemAdele S.conjClosure) • D.kAdelic →
  A.RadicalInvariant B T f (idemAdele U) g) (base : ∀ X γ, D.ActsOnFrame X (idemAdele
  S.conjClosure • γ + (1 - idemAdele S.conjClosure) • 1) → IsPrimitiveMatrix (closureIntegers S)
  (siegelBracket T γ) → D.centreCoeff T f X = 0) (hU : idemAdele S.conjClosure * idemAdele U = 0)
  {g} (hg : g ∈ supportedOn n S) : D.centreCoeff T f g = 0 := by
  let O X g := closurePart (s := s) S X = closurePart S g ∧
    X.mat * (1 - idemAdele S.conjClosure) • D.kAdelic = (1 - idemAdele S.conjClosure) • D.kAdelic
  have oo {g} : O (closurePart S g) g := ⟨ext_mat (by simp), by simp⟩
  have om {X Y g k} : O X g → O Y k → O (X * Y) (g * k) := by simp_all [O, -Matrix.mul_smul]
  choose κ hκ b l w _ using fun (A : W.Splitting _ Unit) g ↦ (A.comp B).iwasawa g (0 ⊕ᵥ 1)
  have w A g := (ext fun _ _ ↦ l A g .refl : toBlocks₂₁ _ = 0) ▸ (b ..).1.fromBlocks_toBlocks ▸ w ..
  have H {n X g γ σ} (o : O X g) (Q : (b A g).1.toBlocks₂₂ = γ) (hn :
    IsIntMatrix (closureIntegers S) (siegelBracket T γ) → denomIndex (Ô E) (idemAdele
    S.conjClosure * (siegelBracket T γ)⁻¹.det).2 < n) : A.borderedCentreCoeff B T f σ X = 0 := ?_
  exact eq_of_supportedOn (componentOn_mem_supportedOn (g := g)) hg (by simp +contextual) ▸
    centreCoeff_eq_zero_of_shearElt (X := closurePart S g)
    hD hf hT fun x _ ↦ H ⟨rfl, by simp [shearElt, hD]⟩ rfl fun _ ↦ .refl
  induction' n using Nat.strongRec with _ ih generalizing A X g γ σ
  have k := by simpa [Q, comp_kAdelic, fromCols_ext_iff, -mat_mul] using w A g
  have ⟨c, z, t, y, hu, _, q⟩ := A.exists_eq_radicalElt_mul_levi k.1
  set u := A.levi _
  have ⟨v, h, e⟩ : D.ActsOnFrame u γ ∧ (A.comp B).ActsOnFrame u (fromBlocks t 0 0 γ) ∧
    ActsOnFrame (A.symm.comp B) u (fromBlocks t⁻¹.1ᴴ 0 0 γ) := by
    simp [comp_kAdelic, hD]; simp [u, Splitting.levi, q, k, -mat_mul]
  have K {X κ} (h : IsIntMatrix ((Ô E).comap (.snd ..)) κ.mat) : A.borderedCentreCoeff B T f 0
    (X * closurePart S κ) = A.borderedCentreCoeff B T f 0 X := by simp [centreCoeff, ← mul_assoc,
    closurePart, Prod.map, hK, componentOn_mem_Kf, mem_Kf.2 h, componentOn_mem_supportedOn]
  have m := (inv_mul_eq_of_eq_mul hu).subst (om oo (om o oo))
  have dens {f} hf (a : ∀ X, O X u → D.centreCoeff T f X = 0) : A.borderedCentreCoeff B T f 0
    _ = 0 := (centreCoeff_centreCoeff hD hf).symm.trans (.trans congr(quotMean _ (_ * $(funext
    ((denseRange_rat_matrix_add he 1).eq (fun r ↦ ((isContPeriodic_centreCoeff hD hf _).2 _
    ⟨r.1, ?_⟩ _).trans (a _ (one_mul u ▸ om ⟨?_, ?_⟩ m))) (isContPeriodic_centreCoeff hD hf _).1
    (g := 0))) ·)) ?_) <;> try simp [closurePart_radicalCentre, *]
  refine by_cases id fun k ↦ ((hl A hD _ o.2).borderedCentreCoeff_radicalElt_mul hf he
    k ..).symm.trans (.trans (by rw [radicalElt_inv, closurePart_radicalElt, ← mul_assoc,
    K (hκ ..).2.isIntMatrix]) (by_cases id fun h0 ↦ dens hf fun Y y ↦ ?_))
  have I : IsIntMatrix (closureIntegers S) (siegelBracket T γ) := fun i j ↦
    (stdLattice.forall_psi₀_mul_eq_one_iff _).1 fun u _ ↦ cast ?_ ((mul_eq_right₀
   h0).1 (.trans congr(_ * $(K ((mat_radicalCentre ..).substr (.add .one
    (((isIntMatrix_kAdelic_and_lCoord _).1.mul (.sub ?_ ?_)).mul (isIntMatrix_kAdelic_and_lCoord
   _).2))))).symm (centreCoeff_mul_radicalCentre hf m.1 h (.single (.inr j) (.inr i) (0, u)))))
    <;> try simp [*, trace_single_mul, mul_comm u, mul_assoc, IsIntMatrix, single_apply, apply_ite]
  have hγ := γ.isUnit_iff_isUnit_det.1 v.isUnit
  have hC : IsUnit (siegelBracket T γ).det := by simp [*, ← mapMatrix_apply, ← map_det, IsUnit.pow]
  have supp A {X g} σ [IsBaseAdapted A] hD τ z o (e : ActsOnFrame (comp A B) g (fromBlocks τ 0 z
    γ)) : _ → IsIntMatrix _ (γ⁻¹ * z) := not_imp_comm.1 fun h ↦ @ih _ (hn I) A _ hD X g _ σ o rfl
    fun q ↦ (w A g).isUnit.dvd (a := fromBlocks τ 0 z γ).elim fun a k ↦ by
    obtain ⟨⟨⟨-, i⟩, -, r : IsIntMatrix (closureIntegers S) a.toBlocks₂₂⟩, -, -, rfl,
      rfl⟩ := by simpa [by simpa [k,
      ← w, ← Matrix.mul_assoc, ← mat_mul] using congr((g * κ A g)⁻¹.mat * $e), forall_and] using
      (mul_mem (idem_mem_Ô S.conjClosure) <| (isIntMatrix_kAdelic_and_lCoord (A.comp B).symm).2.mul
      (.mul (M := mat _) (mem_Kf.1 (inv_mem (hκ A g)).2) (isIntMatrix_kAdelic_and_lCoord
      (A.comp B)).1) · ·), by simpa using (a.fromBlocks_toBlocks ▸ k :)
    simp [by simpa using hγ] at h
    refine @index_strictAnti _ _ _ _ ⟨fun x c ↦ cast ?_ ((Ô E).mul_mem (r.isInt_conjTranspose.mul
      r).det_mem c), fun c ↦ h (.mul (.smul (cast ?_ (@c ⟨_,
      (r.isInt_conjTranspose.mul q).det_mem⟩ (cast ?_ r.isInt_conjTranspose.det_mem)))
      r.adjugate) i)⟩ ⟨isCompact_Ô.relIndex_ne_zero_add (isOpen_Ô.preimage_of_continuous (by
      simp; fun_prop))⟩ <;> clear * - hC <;> simp [-pow_snd, closureIntegers, mem_addSubgroupOf,
      -det_conjTranspose] at hC ⊢ <;> grind [snd_mul, snd_one, idemAdele_cj_mul_self]
  refine base Y _
    (by simpa [v] using congr($(y.1).mat * idemAdele S.conjClosure • D.kAdelic + $(y.2))) ⟨I, _,
    fun i j ↦ let d := replicateRow _ ((siegelBracket T γ)⁻¹ i); cast (by simp)
      ((γ.nonsing_inv_mul_cancel_left (-dᴴ) hγ ▸ supp A 0 hD t _ (om m oo)
      (by simp [← u.mat.mul_assoc, h]) ((centreCoeff_sub hf hf 1 (closurePart
    S (A.shearElt B d))).rec fun a l ↦ (sub_eq_zero.1 ((l ..).symm.trans (dens a fun X o ↦
   A.symm.centreCoeff_eq_zero_of_shearElt hD a hT fun x σ ↦ ?_))).trans_ne
      (by simpa))).isInt_conjTranspose () j), nonsing_inv_mul _ hC⟩
  have o := om (X := A.symm.shearElt B x) ⟨rfl, by simp [shearElt, hD]⟩ o
  have k := (psi₀_eq_one_of_mem <| IsIntMatrix.mul (M := d * siegelBracket T γ) (fun _ ↦
    (nonsing_inv_mul _ hC ▸ IsIntMatrix.one) i) ·
    () ()) ∘ supp A.symm σ hD t⁻¹.1ᴴ (-xᴴ * t⁻¹.1ᴴ) o ?e
  erw [borderedCentreCoeff, l, sub_eq_zero, ← ((psi₀ E).val_isUnit _).mul_right_inj,
    centreCoeff_mul_radicalCentre hf o.1 ?e, eq_comm]
  simpa [trace, *, mul_left_eq_self₀, or_iff_not_imp_right] using k
  simp [← (mat _).mul_assoc, e]
