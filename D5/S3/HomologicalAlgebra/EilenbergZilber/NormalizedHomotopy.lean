/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive norm-error induction and normalized chain homotopy. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.NormalizedOperators

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

private lemma simplex_one_hom_ext {f g : (⦋1⦌ : SimplexCategory) ⟶ ⦋1⦌}
    (h : ∀ j, SimplexCategory.Hom.toOrderHom f j = SimplexCategory.Hom.toOrderHom g j) :
    f = g := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact h j

private lemma hLetter_one_zero :
    hLetter 1 0 (default : Shuffle 0 1) =
      ⟨SimplexCategory.σ 0 ≫ SimplexCategory.δ 1, 𝟙 _⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero,
    eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ιFront, SimplexCategory.mkHom,
    Fin.val_eq_zero, Fin.zero_eta, Category.comp_id, Category.id_comp, shuffleSndHom, ιBack,
    zero_add, Fin.eta, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma hLetter_one_one :
    hLetter 1 1 (default : Shuffle 1 0) =
      ⟨𝟙 _, SimplexCategory.σ 0 ≫ SimplexCategory.δ 0⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.add_zero, eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ιFront,
    SimplexCategory.mkHom, Fin.eta, Category.comp_id, Category.id_comp, shuffleSndHom, ιBack,
    Nat.mod_succ, Fin.val_eq_zero, add_zero, Fin.mk_one, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma phi_op_zero_eq_diagDegen :
    (phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1 =
      (D0op 0).comp (faceOp 0 1) := by
  simp only [Nat.reduceAdd, phiOp, DerivedOp.zero_comp, prime_zero, neg_zero, zero_add, Fin.isValue]
  rw [boundaryOp_eq 1, DerivedOp.sub_comp, lastFace_comp_hPrime_comp_D0 0]
  abel_nf
  simp [truncBoundaryOp, hOp, D0op, faceOp, idOp, hLetter_one_zero, hLetter_one_one,
    DerivedOp.prime, OpLetter.primeLetter, DerivedOp.add_comp, DerivedOp.comp_add_right,
    DerivedOp.neg_comp,
    DerivedOp.single_comp_single, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Shuffle.sign_default_zero_left,
    Shuffle.sign_default_zero_right, OpLetter.compLetter, primeHom_comp, primeHom_δ, primeHom_σ,
    primeHom_id, Category.assoc]
  have hδ₁σ₀ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₀ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁σ₀δ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁σ₀δ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  simp [hδ₁σ₀, hδ₂σ₀, hδ₁σ₁σ₀δ₁, hδ₂σ₁σ₀δ₁, hδ₁σ₁, hδ₂σ₁]
  abel

private lemma sigma_zero_not_mono : ¬ Mono (SimplexCategory.σ (0 : Fin 1)) := by
  rw [SimplexCategory.mono_iff_injective]
  intro h
  have h01 := h (show
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (0 : Fin 2) =
      (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (1 : Fin 2) from rfl)
  norm_num at h01

/-- Base case for the exact induction: the degree-1 error term is a norm. -/
lemma phi_op_isNorm_zero :
    IsNorm ((phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1) := by
  rw [phi_op_zero_eq_diagDegen, D0op]
  exact IsNorm.diagDegen (SimplexCategory.σ (0 : Fin 1)) sigma_zero_not_mono (faceOp 0 1)

/-- The error term `Φ∂ + ∂Φ + i - h` in the next degree is the `prime` of the preceding error term.

After rewriting `∂ = F₀ - ∂'` and `Φ = -Φ' + h' D₀`, the remaining identity is a formal operator
calculation using `lastFace_comp_prime`, `boundaryOp_comp_hOp`, and `boundary_comp_D0`. -/
lemma phi_op_succ_eq (q : ℕ) :
    (phiOp (q + 1)).comp (boundaryOp (q + 1)) + (boundaryOp (q + 1 + 1)).comp (phiOp (q + 1 + 1)) +
        idOp (q + 1 + 1) - hOp (q + 1 + 1) =
      ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
        idOp (q + 1) - hOp (q + 1)).prime := by
  simp only [sub_eq_add_neg, prime_add, prime_neg]
  rw [prime_comp, prime_comp, prime_boundaryOp, prime_boundaryOp, prime_idOp]
  conv_lhs => simp only [phiOp, boundaryOp_eq]
  simp only [DerivedOp.sub_comp, DerivedOp.comp_sub, DerivedOp.neg_comp, DerivedOp.comp_neg,
    DerivedOp.add_comp, DerivedOp.comp_add_right]
  rw [lastFace_comp_prime, lastFace_comp_hPrime_comp_D0]
  conv_rhs => simp only [phiOp]
  -- Rewrite the surviving `∂' h' D₀` term as `h' - h' D₀ ∂'`; all other terms cancel formally.
  have stepA : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime)
      = (hOp (q + 1)).prime.comp (truncBoundaryOp (q + 1 + 1)) := by
    have h2 := congrArg DerivedOp.prime (boundaryOp_comp_hOp (q + 1))
    simp only [prime_comp, prime_boundaryOp] at h2
    exact h2
  have stepC : (truncBoundaryOp (q + 1 + 1)).comp (D0op (q + 1 + 1))
      = idOp (q + 1 + 1) - (D0op (q + 1)).comp (truncBoundaryOp (q + 1)) := by
    have hb := boundary_comp_D0 (q + 1)
    rw [boundaryOp_eq (q + 1 + 1), DerivedOp.sub_comp, lastFace_comp_D0] at hb
    rw [← hb]; abel
  have hkey : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime.comp (D0op (q + 1 + 1)))
      = (hOp (q + 1)).prime
        - ((hOp (q + 1)).prime.comp (D0op (q + 1))).comp (truncBoundaryOp (q + 1)) := by
    rw [← DerivedOp.comp_assoc, stepA, DerivedOp.comp_assoc, stepC, DerivedOp.comp_sub, comp_idOp,
      ← DerivedOp.comp_assoc]
  rw [hkey]
  simp only [DerivedOp.add_comp, DerivedOp.neg_comp]
  abel

/-- The error term `Φ∂ + ∂Φ + i - h` is a norm in every degree. -/
lemma phi_op_isNorm (q : ℕ) :
    IsNorm ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
      idOp (q + 1) - hOp (q + 1)) := by
  induction q with
  | zero => exact phi_op_isNorm_zero
  | succ q ih => rw [phi_op_succ_eq q]; exact ih.prime

/-- Operator-level form of the EM homotopy identity, modulo norms.

This is the realized statement corresponding to `Φ∂ + ∂Φ + i ≡ h`, obtained by killing the
structural norm term from `phi_op_isNorm` with `retractionNTwo`. -/
lemma phi_comm_op (X : BisimplicialObject C) (q : ℕ) :
    (DerivedOp.realize X ((phiOp q).comp (boundaryOp q)) +
        DerivedOp.realize X ((boundaryOp (q + 1)).comp (phiOp (q + 1))) +
        DerivedOp.realize X (idOp (q + 1))) ≫ (retractionNTwo X).f (q + 1) =
      DerivedOp.realize X (hOp (q + 1)) ≫ (retractionNTwo X).f (q + 1) := by
  have h := (phi_op_isNorm q).kill X
  rw [realize_sub, realize_add, realize_add, Preadditive.sub_comp] at h
  exact sub_eq_zero.mp h

/-- EM's homotopy identity `∂Φ + Φ∂ = ∇f - i`, after postcomposing with `retractionNTwo`. -/
lemma phi_comm_retraction (X : BisimplicialObject C) (n : ℕ) :
    (dNext n (phiHomRaw X) + prevD n (phiHomRaw X) +
        (𝟙 (FTwo.obj X) : (FTwo.obj X) ⟶ (FTwo.obj X)).f n) ≫ (retractionNTwo X).f n =
      (alexanderWhitney X ≫ shuffleMap X).f n ≫ (retractionNTwo X).f n := by
  have hid : ∀ m : ℕ, (𝟙 (FTwo.obj X) : (FTwo.obj X) ⟶ (FTwo.obj X)).f m
      = DerivedOp.realize X (idOp m) := by
    intro m; rw [HomologicalComplex.id_f, idOp, realize_single_id]
  cases n with
  | zero =>
      have hp : prevD 0 (phiHomRaw X) = 0 := by
        rw [prevD_phiHomRaw]; simp [phiOp, realize_comp]
      have hd : dNext 0 (phiHomRaw X) = 0 := by rw [dNext]; simp
      rw [hp, hd]
      simp only [zero_add]
      rw [hid, ← realize_hOp]
      exact (hOp_zero_comp_retraction X).symm
  | succ m =>
      rw [dNext_phiHomRaw, prevD_phiHomRaw, hid, ← realize_hOp]
      exact phi_comm_op X m

/-! ### Descent to the normalized diagonal `NTwo` -/

/-- The normalized Moore complex `NTwo` is a retract of `FTwo`: `inclusionNTwo ≫ retractionNTwo = 𝟙`. -/
@[reassoc]
lemma inclusionNTwo_comp_retractionNTwo (X : BisimplicialObject C) :
    inclusionNTwo X ≫ retractionNTwo X = 𝟙 (NTwo.obj X) := by
  rw [inclusionNTwo, retractionNTwo]
  exact (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (diag.obj X)).id

/-- `Φ` conjugated onto the normalized diagonal `NTwo.obj X` (EM's homotopy on `K ×_N L`):
`inclusionNTwo ≫ phiOp.realize ≫ retractionNTwo`. -/
noncomputable def phiHomNorm (X : BisimplicialObject C) (i j : ℕ) :
    (NTwo.obj X).X i ⟶ (NTwo.obj X).X j :=
  if h : j = i + 1 then
    (inclusionNTwo X).f i ≫ (phiOp i).realize X ≫ eqToHom (by rw [h]) ≫ (retractionNTwo X).f j
  else 0

lemma phiHomNorm_zero (X : BisimplicialObject C) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) : phiHomNorm X i j = 0 :=
  dite_eq_right fun h => hij (by rw [ComplexShape.down_Rel]; omega)

/-- `phiHomNorm` is the conjugate of `phiHomRaw` by `inclusionNTwo … retractionNTwo`. -/
lemma phiHomNorm_eq (X : BisimplicialObject C) (i j : ℕ) :
    phiHomNorm X i j = (inclusionNTwo X).f i ≫ phiHomRaw X i j ≫ (retractionNTwo X).f j := by
  by_cases h : j = i + 1
  · simp only [phiHomNorm, phiHomRaw, dite_eq_left h, Category.assoc]
  · simp only [phiHomNorm, phiHomRaw, dite_eq_right h, Limits.comp_zero, Limits.zero_comp]

/-- `phiHomNorm` as an explicit family (for the `dNext`/`prevD` conjugation lemmas). -/
private lemma phiHomNorm_funext (X : BisimplicialObject C) :
    phiHomNorm X = fun a b => (inclusionNTwo X).f a ≫ phiHomRaw X a b ≫ (retractionNTwo X).f b := by
  funext a b; exact phiHomNorm_eq X a b

/-- `dNext` commutes with the `inclusionNTwo … retractionNTwo` conjugation (both are chain maps). -/
lemma dNext_phiHomNorm (X : BisimplicialObject C) (i : ℕ) :
    dNext i (phiHomNorm X) =
      (inclusionNTwo X).f i ≫ dNext i (phiHomRaw X) ≫ (retractionNTwo X).f i := by
  rw [phiHomNorm_funext, dNext_comp_left, dNext_comp_right]

/-- `prevD` commutes with the `inclusionNTwo … retractionNTwo` conjugation (both are chain maps). -/
lemma prevD_phiHomNorm (X : BisimplicialObject C) (j : ℕ) :
    prevD j (phiHomNorm X) =
      (inclusionNTwo X).f j ≫ prevD j (phiHomRaw X) ≫ (retractionNTwo X).f j := by
  rw [phiHomNorm_funext, prevD_comp_left, prevD_comp_right]


/-- **(6b)** The normalized `AW ≫ ∇` is the `NTwo`-conjugate of the unnormalized `AW ≫ ∇`.
Unfolding the definitions, `normalizedAlexanderWhitney ≫ normalizedShuffleMap`
`= ι₂ ≫ AW ≫ (retractionNOne ≫ inclusionNOne) ≫ ∇ ≫ ρ₂`; the inner Dold–Kan round-trip
`retractionNOne ≫ inclusionNOne` (the `PInfty` idempotent on `FOne`) is absorbed, leaving
`ι₂ ≫ (AW ≫ ∇) ≫ ρ₂`. -/
lemma normalizedAW_shuffle_eq (X : BisimplicialObject C) :
    normalizedAlexanderWhitney X ≫ normalizedShuffleMap X
      = inclusionNTwo X ≫ (alexanderWhitney X ≫ shuffleMap X) ≫ retractionNTwo X := by
  rw [normalizedAlexanderWhitney, normalizedShuffleMap]
  simp only [Category.assoc]
  have : Mono (inclusionNTwo X) := by rw [inclusionNTwo]; infer_instance
  rw [← cancel_mono (inclusionNTwo X)]
  simp only [Category.assoc]
  rw [inclusionNTwo, retractionNTwo]
  erw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Functor.comp_obj,
    retractionNOne_inclusionNOne_shuffleMap_PInfty X]

/-- **`AW ≫ ∇ ≃ 𝟙` on the normalized diagonal `NTwo`** via the Eilenberg–Mac Lane homotopy `Φ`
(EM Thm 2.1a, `∂Φ + Φ∂ = ∇f − i`). This is the contraction homotopy used by
`eilenbergZilberNormalized` (`BisimplicialNormalized.lean`). -/
noncomputable def homotopyAWShuffleNormalized (X : BisimplicialObject C) :
    Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (NTwo.obj X)) where
  hom := phiHomNorm X
  zero := phiHomNorm_zero X
  comm := by
    intro i
    -- `𝟙 NTwo` factors through `FTwo`:
    -- `(𝟙 NTwo).f i = ι₂.f i ≫ ρ₂.f i` (`inclusionNTwo_comp_retractionNTwo`).
    have hid : (𝟙 (NTwo.obj X) : (NTwo.obj X) ⟶ (NTwo.obj X)).f i
        = (inclusionNTwo X).f i ≫ (retractionNTwo X).f i := by
      rw [← HomologicalComplex.comp_f, inclusionNTwo_comp_retractionNTwo]
    -- Conjugate everything onto `FTwo` (6a/6b), then replace `(AW≫∇)≫ρ₂` by the EM identity (5c).
    rw [normalizedAW_shuffle_eq, dNext_phiHomNorm, prevD_phiHomNorm, hid,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← phi_comm_retraction X i]
    -- Both sides are now `ι₂ ≫ (…) ≫ ρ₂`; distribute the sum and kill the `𝟙` term.
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.id_f, Category.id_comp]

end BisimplicialObject

end D5.S3.HomologicalAlgebra.EilenbergZilber
