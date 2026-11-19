/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedOperators
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/NormalizedOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural degeneracies and shuffle absorption under normalization. -/

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

public import D5.S3.HomologicalAlgebra.EilenbergZilber.RecursiveOperators

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

/-- Structural norm class for diagonal degeneracies, closed under `+` and `neg`.

The point of this definition is that closure under `prime` is formal, so the induction can be run
before realizing operators on a bisimplicial object. -/
inductive IsNorm : {s q : ℕ} → DerivedOp s q → Prop where
  | zero {s q : ℕ} : IsNorm (0 : DerivedOp s q)
  | add {s q : ℕ} {M N : DerivedOp s q} : IsNorm M → IsNorm N → IsNorm (M + N)
  | neg {s q : ℕ} {M : DerivedOp s q} : IsNorm M → IsNorm (-M)
  | diagDegen {r s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
      IsNorm (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N)

/-- `prime` of a diagonal letter `⟨θ,θ⟩` is the diagonal of `primeHom θ`. -/
lemma prime_single_diag {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.prime (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1)
      = Finsupp.single (⟨primeHom θ, primeHom θ⟩ : OpLetter (s + 1) (q + 1)) 1 := by
  simp [DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.primeLetter]

/-- `primeHom` preserves non-monicity: `primeHom θ` is injective iff `θ` is, and `Mono` in
`SimplexCategory` is injectivity. -/
lemma primeHom_not_mono {s q : ℕ} {θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌} (hθ : ¬ Mono θ) :
    ¬ Mono (primeHom θ) := by
  rw [SimplexCategory.mono_iff_injective] at hθ ⊢
  intro hinj
  apply hθ
  intro a b hab
  have key : ∀ c : Fin (q + 1),
      (SimplexCategory.Hom.toOrderHom (primeHom θ)) c.succ
        = (SimplexCategory.Hom.toOrderHom θ c).succ := by
    intro c
    apply Fin.ext
    have hle : (SimplexCategory.Hom.toOrderHom θ c : ℕ) ≤ s :=
      Nat.lt_succ_iff.mp (SimplexCategory.Hom.toOrderHom θ c).isLt
    simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
      SimplexCategory.len_mk, Fin.val_succ]
    rw [ite_eq_right (by omega : ¬ ((c : ℕ) + 1 = 0))]
    simp only [Nat.add_sub_cancel, Fin.eta]
    omega
  have hsucc : (SimplexCategory.Hom.toOrderHom (primeHom θ)) a.succ
      = (SimplexCategory.Hom.toOrderHom (primeHom θ)) b.succ := by
    rw [key, key, hab]
  exact Fin.succ_injective _ (hinj hsucc)

/-- `prime` fixes the identity map: `primeHom 𝟙 = 𝟙` (`0 ↦ 0`, `j+1 ↦ 𝟙(j)+1 = j+1`). -/
lemma primeHom_id (q : ℕ) : primeHom (𝟙 (⦋q⦌ : SimplexCategory)) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  have hj : (j : ℕ) ≤ q + 1 := Nat.lt_succ_iff.mp j.isLt
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk, SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
  split_ifs with h <;> omega

/-- `i' = i` (md 173–175, implicit in priming the IH's `−c_q`): the derived operator of the
identity is the identity. -/
lemma prime_idOp (q : ℕ) : (idOp q).prime = idOp (q + 1) := by
  rw [idOp, prime_single_diag, primeHom_id, idOp]

/-- **`F₀ D₀ = i`** (`δ_0 ≫ σ_0 = 𝟙`): the last face undoes the 0-th degeneracy. Repackages the
existing `face_zero_comp_D0` (`lastFaceOp = faceOp _ 0`). -/
lemma lastFace_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (D0op (q + 1)) = idOp (q + 1) := by
  rw [lastFaceOp, idOp]
  exact face_zero_comp_D0 q

/-- Right unit for `DerivedOp.comp`: `M ∘ i = M` (`l ≫ 𝟙 = l` in each coordinate). -/
lemma comp_idOp {s q : ℕ} (M : DerivedOp s q) : M.comp (idOp s) = M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l c f _ _ ih =>
      rw [DerivedOp.add_comp, ih]
      congr 1
      rw [idOp, DerivedOp.single_comp_single, one_mul]
      congr 1
      simp only [OpLetter.compLetter, Category.comp_id]

/-- **`F₀ h' D₀ = h` (EM line 192).** `F₀ h' D₀ = (h F₀) D₀ = h (F₀ D₀) = h`, using
`lastFace_comp_hPrime` and `F₀ D₀ = i` (`δ_0 ≫ σ_0 = 𝟙`). -/
lemma lastFace_comp_hPrime_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (((hOp (q + 1)).prime).comp (D0op (q + 1))) = hOp (q + 1) := by
  rw [← DerivedOp.comp_assoc, lastFace_comp_hPrime, DerivedOp.comp_assoc, lastFace_comp_D0,
    comp_idOp]

/-! #### Degeneracies and shuffle normalization

The shuffle map carries the degenerate part of the total complex into the
part killed by the diagonal projection `PInfty`. The proof below factors
collapsed shuffle projections through a codegeneracy and uses Dold–Kan
annihilation of degenerate simplices. -/

/-- If a simplex operator `f : ⦋n+1⦌ ⟶ Δ'` identifies the adjacent pair `a.castSucc, a.succ`
(i.e. it is "constant across the `a`-th step"), then it factors through the codegeneracy `σ a`:
`f = σ a ≫ (δ a.castSucc ≫ f)`. The section `δ a.castSucc` undoes `σ a` away from the collapsed
pair (`Fin.succAbove_predAbove`), and on the pair the hypothesis `hf` patches it. -/
lemma factor_through_σ {n : ℕ} {Δ' : SimplexCategory} (a : Fin (n + 1))
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ Δ')
    (hf : f.toOrderHom a.castSucc = f.toOrderHom a.succ) :
    f = SimplexCategory.σ a ≫ SimplexCategory.δ a.castSucc ≫ f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change _ = (SimplexCategory.Hom.toOrderHom f) (a.castSucc.succAbove (a.predAbove x))
  by_cases hx : x = a.castSucc
  · subst hx
    rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
    exact hf
  · rw [Fin.succAbove_predAbove hx]

/-- A codegeneracy `σ a` is never a monomorphism (it identifies the adjacent pair `a.castSucc`,
`a.succ`). -/
lemma sigma_not_mono {n : ℕ} (a : Fin (n + 1)) : ¬ Mono (SimplexCategory.σ a) := by
  rw [SimplexCategory.mono_iff_injective]
  intro hinj
  have key : a.castSucc = a.succ := by
    apply hinj
    change a.predAbove a.castSucc = a.predAbove a.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  exact absurd key (ne_of_lt Fin.castSucc_lt_succ)

/-- `PInfty` of the diagonal in degree `n`, typed on the `(n, n)` entry of `X`. -/
noncomputable def diagPInfty (X : BisimplicialObject C) (n : ℕ) :
    (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) ⟶
      (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) :=
  (PInfty : FTwo.obj X ⟶ FTwo.obj X).f n

/-- **Shared per-summand kill (degeneracy ⟹ diagonal degeneracy).** A single Eilenberg–Zilber
summand `(X_⦋s⦌).map v.op ≫ (X.map h.op)_⦋n+1⦌`, in which the horizontal leg `h` and the vertical
leg `v` are *both constant across the `a`-th step* (`a.castSucc ↦ a.succ`), factors through the
diagonal codegeneracy `(diag X).map (σ a).op` and is therefore annihilated by `PInfty`. This is the
direction-agnostic core: the inner kill feeds it `v = sndHom ≫ σ_i` (constant by `exists_snd_step`),
the outer kill feeds it `h = fstHom ≫ σ_i`. -/
private lemma summand_kill {N s t : ℕ} (X : BisimplicialObject C)
    (h : (⦋N⦌ : SimplexCategory) ⟶ ⦋s⦌) (v : (⦋N⦌ : SimplexCategory) ⟶ ⦋t⦌)
    (a : Fin N)
    (hh : (SimplexCategory.Hom.toOrderHom h) a.castSucc = (SimplexCategory.Hom.toOrderHom h) a.succ)
    (hv : (SimplexCategory.Hom.toOrderHom v) a.castSucc =
      (SimplexCategory.Hom.toOrderHom v) a.succ) :
    (X.obj (Opposite.op ⦋s⦌)).map v.op ≫ (X.map h.op).app (Opposite.op ⦋N⦌) ≫
      diagPInfty X N = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by
    have : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0); omega⟩
  have hfh := factor_through_σ a h hh
  have hfv := factor_through_σ a v hv
  set h' : (⦋n⦌ : SimplexCategory) ⟶ ⦋s⦌ := SimplexCategory.δ a.castSucc ≫ h with hh'_def
  set v' : (⦋n⦌ : SimplexCategory) ⟶ ⦋t⦌ := SimplexCategory.δ a.castSucc ≫ v with hv'_def
  have hvop : v.op = v'.op ≫ (SimplexCategory.σ a).op := by rw [hfv, op_comp]
  have hhop : h.op = h'.op ≫ (SimplexCategory.σ a).op := by rw [hfh, op_comp]
  -- the diagonal-degeneracy tail is killed by `PInfty`
  have hbr : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌)
      = (diag.obj X).map (SimplexCategory.σ a).op := by
    rw [(X.map (SimplexCategory.σ a).op).naturality, ← diag_obj_map]
  have hkill : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌) ≫
      diagPInfty X (n + 1) = 0 := by
    rw [← Category.assoc, hbr]
    exact degeneracy_comp_PInfty (diag.obj X) (n + 1) (SimplexCategory.σ a) (sigma_not_mono a)
  rw [hvop, hhop, Functor.map_comp, Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [(X.map h'.op).naturality_assoc, hkill]
  simp

/-- **EZ–degeneracy kill, inner (vertical) direction (the per-summand combinatorial core).**
A `(p, m+1)`-shuffle component of a chain that is *degenerate in the inner simplicial direction*
(in the image of the inner degeneracy `s_i = (X_⦋p⦌).map (σ i).op : X_{p,m} → X_{p,m+1}`) is sent by
the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (1 ⊗ s_i) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_inner_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (p m : ℕ) (i : Fin (m + 1)) :
    (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ i).op ≫ ezComponent X p (m + 1) ≫
        diagPInfty X (p + (m + 1)) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨a, ha1, ha2, ha3⟩ := Shuffle.exists_snd_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.succ := by
    simp only [shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.fst_coe]
    exact ha3
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.snd_coe]
    have e1 : (μ.1 a.castSucc).2 = i.castSucc := Fin.ext (by rw [Fin.val_castSucc]; omega)
    have e2 : (μ.1 a.succ).2 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    change (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.castSucc).2
        = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.succ).2
    rw [e1, e2]
    change i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hcomp : X _⦋p⦌.map (SimplexCategory.σ i).op ≫
      (X _⦋p⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + (m + 1)⦌)) ≫
      diagPInfty X (p + (m + 1)) = 0 := by
    simp only [Category.assoc]
    rw [← Category.assoc (X _⦋p⦌.map (SimplexCategory.σ i).op), ← Functor.map_comp, ← op_comp]
    exact summand_kill X (shuffleFstHom μ) (shuffleSndHom μ ≫ SimplexCategory.σ i) a hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **EZ–degeneracy kill, outer (horizontal) direction (the per-summand combinatorial core).**
An `(a+1, q)`-shuffle component of a chain that is *degenerate in the outer simplicial direction*
(in the image of the outer degeneracy `s_i = (X.map (σ i).op).app ⦋q⦌ : X_{a,q} → X_{a+1,q}`)
is sent
by the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (s_i ⊗ 1) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_outer_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (a q : ℕ) (i : Fin (a + 1)) :
    (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫ ezComponent X (a + 1) q ≫
        diagPInfty X (a + 1 + q) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨b, hb1, hb2, hb3⟩ := Shuffle.exists_fst_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.fst_coe]
    have e1 : (μ.1 b.castSucc).1 = i.castSucc := Fin.ext (by rw [Fin.val_castSucc]; omega)
    have e2 : (μ.1 b.succ).1 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    change (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.castSucc).1
        = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.succ).1
    rw [e1, e2]
    change i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.succ := by
    simp only [shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.snd_coe]
    exact hb3
  have hcomp : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫
      (X _⦋a + 1⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)) ≫
      diagPInfty X (a + 1 + q) = 0 := by
    have happ : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)
        = (X.map (shuffleFstHom μ ≫ SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp only [Category.assoc]
    rw [← (X.map (SimplexCategory.σ i).op).naturality_assoc,
      ← Category.assoc ((X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌)), happ]
    exact summand_kill X (shuffleFstHom μ ≫ SimplexCategory.σ i) (shuffleSndHom μ) b hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **Inner `QInfty`-degeneracy kill.** The inner (vertical) `QInfty` projector at degree `q`,
precomposed with the Eilenberg–Zilber component and the diagonal `PInfty`, vanishes. Each summand of
the Mathlib `decomposition_Q` ends in an inner degeneracy `(X_⦋p⦌).σ`, killed by
`ezComponent_inner_degeneracy_comp_PInfty`. -/
private lemma QInfty_inner_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q ≫ ezComponent X p q ≫
        diagPInfty X (p + q) = 0 := by
  cases q with
  | zero => rw [QInfty_f_0, zero_comp]
  | succ m =>
    rw [QInfty_f, decomposition_Q m (m + 1), Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ (Fin.rev i)).op ≫
        ezComponent X p (m + 1) ≫ diagPInfty X (p + (m + 1)) = 0 :=
      ezComponent_inner_degeneracy_comp_PInfty X p m (Fin.rev i)
    simp only [SimplicialObject.σ, Category.assoc, hkill, comp_zero]

/-- **Outer `QInfty`-degeneracy kill.** The outer (horizontal) `QInfty` projector at degree `p`
(evaluated at inner degree `q`), precomposed with the Eilenberg–Zilber component and the diagonal
`PInfty`, vanishes. Each summand of the Mathlib `decomposition_Q` ends in an outer degeneracy
`(X.map (σ _).op).app ⦋q⦌`, killed by `ezComponent_outer_degeneracy_comp_PInfty`. -/
private lemma QInfty_outer_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌) ≫ ezComponent X p q ≫
        diagPInfty X (p + q) = 0 := by
  cases p with
  | zero => rw [QInfty_f_0]; simp
  | succ a =>
    rw [QInfty_f, decomposition_Q a (a + 1), NatTrans.app_sum, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.map (SimplexCategory.σ (Fin.rev i)).op).app (Opposite.op ⦋q⦌) ≫
        ezComponent X (a + 1) q ≫ diagPInfty X (a + 1 + q) = 0 :=
      ezComponent_outer_degeneracy_comp_PInfty X a q (Fin.rev i)
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc]
    rw [SimplicialObject.σ, hkill, comp_zero, comp_zero]

/-- The inner `PInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def innerPInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (PInfty (X := X.obj (Opposite.op ⦋p⦌))).f q

/-- The outer `PInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def outerPInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((PInfty (X := X)).f p).app (Opposite.op ⦋q⦌)

/-- The inner `QInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def innerQInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q

/-- The outer `QInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def outerQInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌)

/-- The inclusion of `X_{p,q}` into `FOne.obj X` in total degree `p + q`. -/
private noncomputable def ιFOne (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶ (FOne.obj X).X (p + q) :=
  HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p q (p + q)
    (by simp [ComplexShape.π_def])

private lemma innerPInfty_eq (X : BisimplicialObject C) (p q : ℕ) :
    innerPInfty X p q = 𝟙 _ - innerQInfty X p q :=
  eq_sub_iff_add_eq.mpr (PInfty_f_add_QInfty_f (X := X.obj (Opposite.op ⦋p⦌)) q)

private lemma outerPInfty_eq (X : BisimplicialObject C) (p q : ℕ) :
    outerPInfty X p q = 𝟙 _ - outerQInfty X p q :=
  eq_sub_iff_add_eq.mpr
    (congrArg (fun f => NatTrans.app f (Opposite.op ⦋q⦌)) (PInfty_f_add_QInfty_f (X := X) p))

private lemma innerQInfty_ezComponent_diagPInfty (X : BisimplicialObject C) (p q : ℕ) :
    innerQInfty X p q ≫ ezComponent X p q ≫ diagPInfty X (p + q) = 0 :=
  QInfty_inner_ezComponent_PInfty X p q

private lemma outerQInfty_ezComponent_diagPInfty (X : BisimplicialObject C) (p q : ℕ) :
    outerQInfty X p q ≫ ezComponent X p q ≫ diagPInfty X (p + q) = 0 :=
  QInfty_outer_ezComponent_PInfty X p q

private lemma sub_one_sub_comp_eq_zero {A Z : C} (a b : A ⟶ A) (f : A ⟶ Z)
    (ha : a ≫ f = 0) (hb : b ≫ f = 0) : f - (𝟙 A - a) ≫ (𝟙 A - b) ≫ f = 0 := by
  simp [Preadditive.sub_comp, ha, hb]

/-- The `(p, q)` component of `retractionNOne ≫ inclusionNOne` is `outerPInfty ≫ innerPInfty`. -/
private lemma retraction_inclusion_component (X : BisimplicialObject C) (p q : ℕ) :
    ((PInftyToNormalizedMooreComplex (X.obj (Opposite.op ⦋p⦌))).f q ≫
      ((normalizedMooreComplex C).map ((PInftyToNormalizedMooreComplex X).f p)).f q) ≫
      (((normalizedMooreComplex C).map ((inclusionOfMooreComplexMap X).f p)).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q) =
    outerPInfty X p q ≫ innerPInfty X p q := by
  have e1 : ((normalizedMooreComplex C).map ((PInftyToNormalizedMooreComplex X).f p)).f q ≫
      ((normalizedMooreComplex C).map ((inclusionOfMooreComplexMap X).f p)).f q =
      ((normalizedMooreComplex C).map ((PInfty (X := X)).f p)).f q :=
    (congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      ((normalizedMooreComplex C).map_comp _ _)).symm.trans
      (congrArg (fun g => ((normalizedMooreComplex C).map g).f q)
        (congrArg (fun φ => HomologicalComplex.Hom.f φ p)
          (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)))
  have e2 : ((normalizedMooreComplex C).map ((PInfty (X := X)).f p)).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q =
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q ≫ outerPInfty X p q :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      ((inclusionOfMooreComplex C).naturality ((PInfty (X := X)).f p))
  have e3 : (PInftyToNormalizedMooreComplex (X.obj (Opposite.op ⦋p⦌))).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q = innerPInfty X p q :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap _)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans e2))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ outerPInfty X p q) e3).trans (PInfty_f_naturality q ((PInfty (X := X)).f p)).symm

private lemma ιFOne_shuffleMap_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    ιFOne X p q ≫ (shuffleMap X ≫ PInfty).f (p + q) = ezComponent X p q ≫ diagPInfty X (p + q) := by
  rw [HomologicalComplex.comp_f]
  dsimp only [shuffleMap, ιFOne]
  erw [HomologicalComplex₂.ι_totalDesc_assoc]
  exact (Category.assoc _ _ _).trans (congrArg (ezComponent X p q ≫ ·) (Category.id_comp _))

/-- The degenerate part of `FOne` is sent by `shuffleMap` to a diagonal degeneracy, hence is killed by
`PInfty`.

Concretely, after decomposing the complementary projector
`𝟙 - retractionNOne ≫ inclusionNOne` bidegreewise, the resulting inner- and outer-degenerate pieces are
annihilated by `ezComponent_inner_degeneracy_comp_PInfty` and
`ezComponent_outer_degeneracy_comp_PInfty`. -/
lemma degenerate_shuffleMap_comp_PInfty (X : BisimplicialObject C) :
    (𝟙 (FOne.obj X) - retractionNOne X ≫ inclusionNOne X) ≫ shuffleMap X ≫
        (PInfty : FTwo.obj X ⟶ FTwo.obj X) = 0 := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  subst hpq
  erw [comp_zero]
  have hr' : ιFOne X p q ≫ (retractionNOne X ≫ inclusionNOne X).f (p + q) =
      (outerPInfty X p q ≫ innerPInfty X p q) ≫ ιFOne X p q := by
    rw [retractionNOne, inclusionNOne, ← Functor.map_comp, HomologicalComplex₂.totalFunctor_map]
    dsimp only [ιFOne]
    erw [HomologicalComplex₂.ιTotal_map]
    exact congrArg (· ≫ _) (retraction_inclusion_component X p q)
  change ιFOne X p q ≫ ((𝟙 (FOne.obj X) - retractionNOne X ≫ inclusionNOne X) ≫ shuffleMap X ≫
    (PInfty : FTwo.obj X ⟶ FTwo.obj X)).f (p + q) = 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, Preadditive.sub_comp,
    Preadditive.comp_sub, HomologicalComplex.id_f, Category.id_comp, reassoc_of% hr',
    ιFOne_shuffleMap_PInfty, outerPInfty_eq, innerPInfty_eq]
  exact sub_one_sub_comp_eq_zero _ _ _ (outerQInfty_ezComponent_diagPInfty X p q)
    (innerQInfty_ezComponent_diagPInfty X p q)

/-- The round trip `retractionNOne ≫ inclusionNOne` is absorbed under `shuffleMap ≫ PInfty`.

The correction term `1 - retractionNOne ≫ inclusionNOne` lands in the degenerate part of the diagonal,
which `PInfty` kills. -/
@[reassoc]
lemma retractionNOne_inclusionNOne_shuffleMap_PInfty (X : BisimplicialObject C) :
    retractionNOne X ≫ inclusionNOne X ≫ shuffleMap X ≫ (PInfty : FTwo.obj X ⟶ FTwo.obj X)
      = shuffleMap X ≫ PInfty := by
  have key := degenerate_shuffleMap_comp_PInfty X
  rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at key
  rw [← Category.assoc]
  exact key.symm


/-- **Every norm dies under `retractionNTwo`** (for every `X`). Structural induction: linear cases are
`realize`-linearity; the structural generator is a diagonal degeneracy composed with an operator. -/
lemma IsNorm.kill {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) (X : BisimplicialObject C) :
    DerivedOp.realize X M ≫ (retractionNTwo X).f q = 0 := by
  induction h with
  | zero => rw [realize_zero, Limits.zero_comp]
  | add _ _ ihM ihN => rw [realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM => rw [realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | diagDegen θ hθ N => exact realize_comp_diagLetter_not_mono_comp_retractionNTwo X θ hθ N

/-- The structural norm class is closed under `prime`. -/
lemma IsNorm.prime {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) : IsNorm M.prime := by
  induction h with
  | zero => rw [prime_zero]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [prime_add]; exact ihM.add ihN
  | neg _ ihM => rw [prime_neg]; exact ihM.neg
  | diagDegen θ hθ N =>
      rw [prime_comp, prime_single_diag]
      exact IsNorm.diagDegen (primeHom θ) (primeHom_not_mono hθ) N.prime


end BisimplicialObject

end D5.S3.HomologicalAlgebra.EilenbergZilber
