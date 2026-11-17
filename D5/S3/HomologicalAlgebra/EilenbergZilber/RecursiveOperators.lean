/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive Eilenberg-Mac Lane operators and their universal detector. -/

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

public import D5.S3.HomologicalAlgebra.EilenbergZilber.DerivedOperators

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

/-! ### The Eilenberg–Mac Lane homotopy `h = ∇f` and the recursion (2.13) -/

/- `hOp` is the formal derived operator representing `h = ∇f`. Later arguments use only its
realization and its formal interaction with `prime` and `comp`, not the explicit
description of its letters. -/
/-- A single summand of `h = ∇f`: split `q = p + (q - p)`, apply the AW front/back
faces, then apply one `(p, q-p)` shuffle. The two `eqToHom`s transport across
`p + (q-p) = q`. -/
noncomputable def hLetter (q : ℕ) (p : Fin (q + 1)) (μ : Shuffle (p : ℕ) (q - p)) :
    OpLetter q q where
  fst :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleFstHom μ ≫ ιFront (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))
  snd :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleSndHom μ ≫ ιBack (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))

/-- `h = ∇f` as a derived operator: sum over the Alexander-Whitney split and then over
shuffles. -/
noncomputable def hOp (q : ℕ) : DerivedOp q q :=
  ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
    Finsupp.single (hLetter q p μ) μ.sign

omit [Abelian C] in
private lemma awShuffleLetter_core (X : BisimplicialObject C) (p r : ℕ) (μ : Shuffle p r) :
    (X.map (ιFront p r).op).app (Opposite.op ⦋p + r⦌) ≫
        (X.obj (Opposite.op ⦋p⦌)).map (ιBack p r).op ≫
          (X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌) =
      (X.obj (Opposite.op ⦋p + r⦌)).map (shuffleSndHom μ ≫ ιBack p r).op ≫
        (X.map (shuffleFstHom μ ≫ ιFront p r).op).app (Opposite.op ⦋p + r⦌) := by
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, ← op_comp]
  slice_lhs 1 2 =>
    rw [← (X.map (ιFront p r).op).naturality (shuffleSndHom μ ≫ ιBack p r).op]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [← NatTrans.comp_app]

private lemma hLetter_realize_of_add_eq (X : BisimplicialObject C) (p r q : ℕ)
    (h : p + r = q) (μ : Shuffle p r) :
    (OpLetter.mk
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleFstHom μ ≫ ιFront p r ≫
        eqToHom (congrArg SimplexCategory.mk h))
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleSndHom μ ≫ ιBack p r ≫
        eqToHom (congrArg SimplexCategory.mk h))).realizeLetter X =
      eqToHom (by
        simp only [FTwo, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
        rw [← h]) ≫
        awComponent X p r ≫
          ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌)) ≫
          eqToHom (by
            simp only [FTwo, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
            rw [← h]) := by
  subst q
  change (X.obj (Opposite.op ⦋p + r⦌)).map
        (eqToHom rfl ≫ shuffleSndHom μ ≫ ιBack p r ≫ eqToHom rfl).op ≫
      (X.map (eqToHom rfl ≫ shuffleFstHom μ ≫ ιFront p r ≫ eqToHom rfl).op).app
        (Opposite.op ⦋p + r⦌) =
    𝟙 ((X.obj (Opposite.op ⦋p + r⦌)).obj (Opposite.op ⦋p + r⦌)) ≫ awComponent X p r ≫
      ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌)) ≫
      𝟙 ((X.obj (Opposite.op ⦋p + r⦌)).obj (Opposite.op ⦋p + r⦌))
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, awComponent, Category.assoc]
  exact (awShuffleLetter_core X p r μ).symm

/-- Realization of one `hLetter` summand is the corresponding `awComponent ≫ ezComponent` shuffle
summand. This is the Pattern-5 merge of the AW front/back faces with the shuffle degeneracies. -/
lemma hLetter_realize (X : BisimplicialObject C) (q : ℕ) (p : Fin (q + 1))
    (μ : Shuffle (p : ℕ) (q - p)) :
    (hLetter q p μ).realizeLetter X =
      eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
        awComponent X p (q - p) ≫
          ((X.obj (Opposite.op ⦋(p : ℕ)⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋(p : ℕ) + (q - p)⦌)) ≫
          eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) := by
  have hpq : (p : ℕ) + (q - p) = q :=
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)
  simpa [hLetter, hpq] using hLetter_realize_of_add_eq X (p : ℕ) (q - p) q hpq μ

/-- `hOp` realizes to the composite `alexanderWhitney ≫ shuffleMap = ∇f` on `FTwo.obj X`. -/
lemma realize_hOp (X : BisimplicialObject C) (q : ℕ) :
    (hOp q).realize X = (alexanderWhitney X ≫ shuffleMap X).f q := by
  have hrealize :
      (hOp q).realize X =
        ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
          μ.sign • (hLetter q p μ).realizeLetter X := by
    change realizeAddMonoidHom X (hOp q) = _
    rw [hOp, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [realizeAddMonoidHom, realize_single]
  rw [hrealize, alexanderWhitney_comp_shuffleMap_f]
  simp only [hLetter_realize, ezComponent, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]


/-- **The Eilenberg–Mac Lane homotopy `Φ`** as a derived operator, defined by EM's recursion (2.13):
`Φ₀ = 0` and `Φ_{q} = − Φ'_{q-1} + h'_{q} D₀` for `q > 0`. Here `Φ_q : (K×L)_q → (K×L)_{q+1}`. -/
noncomputable def phiOp : (q : ℕ) → DerivedOp q (q + 1)
  | 0 => 0
  | (q + 1) => -(phiOp q).prime + (hOp (q + 1)).prime.comp (D0op (q + 1))


/-! ### Packaging the homotopy on `FTwo` (raw, modulo norms) -/

/-- `Φ` packaged as a degree-`+1` `Homotopy.hom` family on `FTwo.obj X` (the unnormalized diagonal):
`phiOp i` realized (transported along `j = i+1`) on the single nonzero entry, `0` elsewhere. -/
noncomputable def phiHomRaw (X : BisimplicialObject C) (i j : ℕ) :
    (FTwo.obj X).X i ⟶ (FTwo.obj X).X j :=
  if h : j = i + 1 then (phiOp i).realize X ≫ eqToHom (by rw [h]) else 0

/-- `prevD` of `phiHomRaw` is the realized operator `∂Φ` (apply `Φ` then `∂`):
`prevD n (phiHomRaw X) = (phiOp n).realize X ≫ (boundaryOp n).realize X`. -/
lemma prevD_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    prevD n (phiHomRaw X) = DerivedOp.realize X ((boundaryOp n).comp (phiOp n)) := by
  rw [prevD_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dite_eq_left rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- `dNext` of `phiHomRaw` (at `n+1`) is the realized operator `Φ∂` (apply `∂` then `Φ`):
`dNext (n+1) (phiHomRaw X) = (boundaryOp n).realize X ≫ (phiOp n).realize X`. -/
lemma dNext_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    dNext (n + 1) (phiHomRaw X) = DerivedOp.realize X ((phiOp n).comp (boundaryOp n)) := by
  rw [dNext_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dite_eq_left rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- The identity operator `i = 𝟙 × 𝟙 : (K×L)_q → (K×L)_q` (EM's `i`). Realizes to `𝟙`
(`realize_single_id`). -/
noncomputable def idOp (q : ℕ) : DerivedOp q q := Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1

/-! #### Abstract properties of `h = ∇f` used by the EM induction

From this point on, the induction uses `hOp` only through formal operator identities, not by
unfolding its explicit summands. -/

/-- The represented simplicial type `Δ[s] : b ↦ (⦋b⦌ ⟶ ⦋s⦌)` (the `SimplexCategory` Yoneda). -/
abbrev ysimp (s : ℕ) : SimplexCategoryᵒᵖ ⥤ Type := yoneda.obj (⦋s⦌ : SimplexCategory)

/-- The bi-represented **bisimplicial type** at `(s, s)`: `(a, b) ↦ (⦋a⦌ ⟶ ⦋s⦌) × (⦋b⦌ ⟶ ⦋s⦌)`,
the horizontal map acting on the first factor and the vertical on the second. -/
def bitype (s : ℕ) : BisimplicialObject (Type) where
  obj a :=
    { obj := fun b => (ysimp s).obj a × (ysimp s).obj b
      map := fun {b b'} g => TypeCat.ofHom fun p => (p.1, (ysimp s).map g p.2)
      map_id := by intro b; ext p <;> simp
      map_comp := by intro b b' b'' g g'; ext p <;> simp }
  map := fun {a a'} f =>
    { app := fun b => TypeCat.ofHom fun p => ((ysimp s).map f p.1, p.2)
      naturality := by intro b b' g; ext p <;> simp }
  map_id := by intro a; ext b p <;> simp
  map_comp := by intro a a' a'' f f'; ext b p <;> simp

/-- Postcompose a (bi)simplicial type with the free `ℤ`-module functor. -/
noncomputable def freeWhisker :
    (SimplexCategoryᵒᵖ ⥤ Type) ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ Type (ModuleCat.{0} ℤ)).obj (ModuleCat.free ℤ)

/-- A **universal bisimplicial object** detecting all derived operators out of degree `s`:
the free `ℤ`-module on the bi-represented bisimplicial set at `(s, s)`. Realizing a derived
operator against it recovers it as a `Finsupp`, so `realize (univOp s)` is injective
(`realize_univOp_injective`). -/
noncomputable def univOp (s : ℕ) : BisimplicialObject (ModuleCat.{0} ℤ) :=
  bitype s ⋙ freeWhisker

/-- The underlying pair of `SimplexCategory` maps of a letter. Injective (a letter *is* its pair),
so it indexes the free `ℤ`-module realizing `univOp`. -/
private def opToPair {s q : ℕ} (l : OpLetter s q) :
    ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) × ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) := (l.fst, l.snd)

private lemma opToPair_injective {s q : ℕ} :
    Function.Injective (opToPair (s := s) (q := q)) := by
  intro l l' h
  cases l; cases l'
  simpa only [opToPair, Prod.mk.injEq, OpLetter.mk.injEq] using h

/-- The universal generator `(𝟙, 𝟙) ∈ X_{s,s}` for `X = univOp s`. -/
private noncomputable def univGen (s : ℕ) : (FTwo.obj (univOp s)).X s :=
  ModuleCat.freeMk (R := ℤ) ((𝟙 (⦋s⦌ : SimplexCategory)), (𝟙 (⦋s⦌ : SimplexCategory)))

private lemma realize_univOp_single_gen_one {s q : ℕ} (l : OpLetter s q) :
    (DerivedOp.realize (univOp s) (Finsupp.single l 1)) (univGen s)
      = ModuleCat.freeMk (R := ℤ) (opToPair l) := by
  rw [realize_single, one_smul]
  simp only [OpLetter.realizeLetter, univOp, freeWhisker, univGen, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app, bitype, ysimp,
    yoneda_obj_map, Quiver.Hom.unop_op, opToPair]
  erw [ModuleCat.comp_apply, ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  exact congrArg ModuleCat.freeMk (by simp)

private lemma realize_univOp_single_gen {s q : ℕ} (l : OpLetter s q) (c : ℤ) :
    (DerivedOp.realize (univOp s) (Finsupp.single l c)) (univGen s)
      = Finsupp.single (opToPair l) c := by
  rw [show (Finsupp.single l c : DerivedOp s q) = c • Finsupp.single l 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one], realize_zsmul]
  rw [show (ConcreteCategory.hom (c • DerivedOp.realize (univOp s) (Finsupp.single l 1)))
        (univGen s)
        = c • (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l 1)))
          (univGen s) from rfl,
    realize_univOp_single_gen_one, ModuleCat.freeMk]
  exact (Finsupp.smul_single c (opToPair l) 1).trans (by rw [smul_eq_mul, mul_one])

/-- Realizing `M` on `univOp` and evaluating at the universal generator recovers `M` (reindexed
along the letter-to-pair bijection): `realize (univOp s) M (gen) = mapDomain opToPair M`. -/
private lemma realize_univOp_gen {s q : ℕ} (M : DerivedOp s q) :
    (DerivedOp.realize (univOp s) M) (univGen s) = Finsupp.mapDomain opToPair M := by
  induction M using Finsupp.induction with
  | zero => rw [realize_zero, Finsupp.mapDomain_zero]; rfl
  | single_add l c f _ _ ih =>
      rw [realize_add,
        show (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)
              + DerivedOp.realize (univOp s) f)) (univGen s)
            = (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)))
                (univGen s)
              + (ConcreteCategory.hom (DerivedOp.realize (univOp s) f)) (univGen s) from rfl,
        realize_univOp_single_gen, ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rfl

/-- `realize` against the universal object is **injective**: a derived operator is determined by
its realization on `univOp`. This is the faithfulness principle that lets us deduce formal
`DerivedOp` identities from their (realized) chain-level counterparts. -/
lemma realize_univOp_injective {s q : ℕ} :
    Function.Injective (fun M : DerivedOp s q => M.realize (univOp s)) := by
  intro M N h
  have hg := congrArg
    (fun φ : (FTwo.obj (univOp s)).X s ⟶ (FTwo.obj (univOp s)).X q =>
      (ConcreteCategory.hom φ) (univGen s)) h
  simp only [realize_univOp_gen] at hg
  exact Finsupp.mapDomain_injective opToPair_injective hg

/-- **`∂ h = h ∂` (EM line 155, `∂*h' = h'∂*`).** `h = ∇f` is a chain map, so `boundaryOp` commutes
with `hOp`. Proof: `realize` against the universal object is injective, and on the realized side
this is just the chain-map condition `comm` of `alexanderWhitney ≫ shuffleMap`. -/
lemma boundaryOp_comp_hOp (q : ℕ) :
    (boundaryOp q).comp (hOp (q + 1)) = (hOp q).comp (boundaryOp q) := by
  apply realize_univOp_injective
  change ((boundaryOp q).comp (hOp (q + 1))).realize (univOp (q + 1))
    = ((hOp q).comp (boundaryOp q)).realize (univOp (q + 1))
  rw [realize_comp, realize_comp, realize_hOp, realize_hOp, realize_boundaryOp]
  exact (alexanderWhitney (univOp (q + 1)) ≫ shuffleMap (univOp (q + 1))).comm (q + 1) q

/-- **`F₀ h' = h F₀` (EM, Lemma I.3.3).** Just `lastFace_comp_prime` specialized to `hOp`. -/
lemma lastFace_comp_hPrime (q : ℕ) :
    (lastFaceOp q).comp ((hOp q).prime) = (hOp q).comp (lastFaceOp q) :=
  lastFace_comp_prime (hOp q)

/-- Base degree: `hOp 0` agrees with the identity after postcomposing with `retractionNTwo`. -/
lemma hOp_zero_comp_retraction (X : BisimplicialObject C) :
    DerivedOp.realize X (hOp 0) ≫ (retractionNTwo X).f 0 =
      DerivedOp.realize X (idOp 0) ≫ (retractionNTwo X).f 0 := by
  rw [realize_hOp, idOp, realize_single_id, awShuffle_f_zero, HomologicalComplex.id_f]

/-! #### Exact-identity backbone for the EM induction

The induction is organized at the formal `DerivedOp` level. We encode the error term
`Φ∂ + ∂Φ + i - h` as a structural norm class `IsNorm`, prove that this class is closed under
`prime`, and only at the end convert structural norms into vanishing statements after
postcomposing with `retractionNTwo`. -/

/-- Right composition `· .comp N` bundled additively (general `compRightD0`). -/
private noncomputable def compRightHom {s q r : ℕ} (MTwo : DerivedOp q r) :
    DerivedOp s q →+ DerivedOp s r where
  toFun N := MTwo.comp N
  map_zero' := by simp [DerivedOp.comp]
  map_add' := DerivedOp.comp_add_right MTwo

/-- Left composition `M ↦ M.comp K` bundled additively. -/
private noncomputable def compLeftHom {s q r : ℕ} (MOne : DerivedOp s q) :
    DerivedOp q r →+ DerivedOp s r where
  toFun MTwo := MTwo.comp MOne
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N MOne

lemma DerivedOp.comp_neg {s q r : ℕ} (MTwo : DerivedOp q r) (N : DerivedOp s q) :
    MTwo.comp (-N) = -(MTwo.comp N) := map_neg (compRightHom MTwo) N

lemma DerivedOp.neg_comp {s q r : ℕ} (M : DerivedOp q r) (K : DerivedOp s q) :
    (-M).comp K = -(M.comp K) := map_neg (compLeftHom K) M

lemma DerivedOp.comp_sub {s q r : ℕ} (MTwo : DerivedOp q r) (M N : DerivedOp s q) :
    MTwo.comp (M - N) = MTwo.comp M - MTwo.comp N := map_sub (compRightHom MTwo) M N

lemma DerivedOp.sub_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M - N).comp K = M.comp K - N.comp K := map_sub (compLeftHom K) M N

lemma prime_neg {s q : ℕ} (M : DerivedOp s q) : (-M).prime = -M.prime :=
  map_neg primeAddHom M

/-- Associativity of letter composition (`≫`-associativity in each coordinate). -/
private lemma OpLetter.compLetter_assoc {s q r p : ℕ} (l₃ : OpLetter r p) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) : (l₃.compLetter l₂).compLetter l₁ = l₃.compLetter (l₂.compLetter l₁) := by
  simp only [OpLetter.compLetter, Category.assoc]

/-- Associativity of `DerivedOp.comp` (reduces to `single_comp_single` + bilinearity). -/
lemma DerivedOp.comp_assoc {s q r p : ℕ} (M₃ : DerivedOp r p) (MTwo : DerivedOp q r)
    (MOne : DerivedOp s q) : (M₃.comp MTwo).comp MOne = M₃.comp (MTwo.comp MOne) := by
  induction MOne using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, ih, DerivedOp.comp_add_right, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction MTwo using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.comp_add_right, DerivedOp.add_comp, ih₂, DerivedOp.add_comp,
        DerivedOp.comp_add_right]
      congr 1
      clear ih₂
      induction M₃ using Finsupp.induction with
      | zero => simp [DerivedOp.comp]
      | single_add l₃ c₃ h _ _ ih₃ =>
        rw [DerivedOp.add_comp, DerivedOp.add_comp, ih₃, DerivedOp.add_comp]
        congr 1
        rw [DerivedOp.single_comp_single, DerivedOp.single_comp_single,
          DerivedOp.single_comp_single, DerivedOp.single_comp_single, OpLetter.compLetter_assoc]
        congr 1
        ring

@[simp] lemma DerivedOp.zero_comp {s q r : ℕ} (N : DerivedOp s q) :
    DerivedOp.comp (0 : DerivedOp q r) N = 0 := by simp [DerivedOp.comp]


end BisimplicialObject

end D5.S3.HomologicalAlgebra.EilenbergZilber
