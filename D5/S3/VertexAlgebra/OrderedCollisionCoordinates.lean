/- GID: D5/S3/VertexAlgebra/OrderedCollisionCoordinates
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/OrderedCollisionCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete adjacent orders and coefficientwise local residue expansion. -/

/-
Complete adjacent orders and coefficientwise local residue expansion.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.CollisionRationalExpansions
import D5.S3.VertexAlgebra.LabelledRationalClearing
import D5.S3.VertexAlgebra.CollisionLaurentKernels
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- Rational coefficient fields are embedded in full Hahn orders by an actual
order-preserving zero-coordinate insertion. All labels survive the embedding.
The residue square below acts only after global rational expansion. -/
namespace OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.FiniteConvolution CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar LabelledRationalClearing.GlobalRationalCurry
set_option backward.isDefEq.respectTransparency false

def polynomialViaEquiv {Λ Γ K : Type*} [AddCommGroup Λ] [AddCommGroup Γ]
    [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] (e : Λ ≃+ Γ) :
    AddMonoidAlgebra K Λ →+* HahnSeries Γ K := by
  letI : Algebra K (HahnSeries Γ K) := HahnSeries.instAlgebra
  exact
  (scalarPolynomial (Γ := Γ) (K := K)).toRingHom.comp
    (AddMonoidAlgebra.domCongr K K e).toRingHom

theorem polynomialViaEquiv_injective {Λ Γ K : Type*} [AddCommGroup Λ] [AddCommGroup Γ]
    [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] (e : Λ ≃+ Γ) :
    Function.Injective (polynomialViaEquiv (K := K) e) := by
  letI : Algebra K (HahnSeries Γ K) := HahnSeries.instAlgebra
  exact (CollisionRationalExpansions.OrderedRationalExpansion.scalarPolynomial_injective (Γ := Γ) K).comp
    (AddMonoidAlgebra.domCongr K K e).injective

def splitIndex (inner : ℕ) : (outer : ℕ) →
    Indices ((inner + 1) + outer) → ℤ × Indices (inner + outer)
  | 0, g => ofLex g
  | outer + 1, g =>
    let p := splitIndex inner outer (ofLex g).2
    (p.1, toLex ((ofLex g).1, p.2))

theorem splitIndex_insert (inner outer : ℕ) (t : ℤ) (g : Indices (inner + outer)) :
    splitIndex inner outer (insertIndex inner outer t g) = (t, g) := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    simp only [insertIndex, splitIndex, ofLex_toLex, ih]
    rfl

theorem insert_splitIndex (inner outer : ℕ) (g : Indices ((inner + 1) + outer)) :
    insertIndex inner outer (splitIndex inner outer g).1 (splitIndex inner outer g).2 = g := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    change toLex ((ofLex g).1,
      insertIndex inner outer (splitIndex inner outer (ofLex g).2).1
        (splitIndex inner outer (ofLex g).2).2) = g
    rw [ih]
    rfl

theorem insertIndex_add_general (inner outer : ℕ) (t u : ℤ)
    (g h : Indices (inner + outer)) :
    insertIndex inner outer (t + u) (g + h) =
      insertIndex inner outer t g + insertIndex inner outer u h := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      insertIndex inner outer (t + u) ((ofLex g).2 + (ofLex h).2)) = _
    rw [ih]
    rfl

def joinIndex (inner outer : ℕ) :
    (ℤ × Indices (inner + outer)) ≃+ Indices ((inner + 1) + outer) where
  toFun p := insertIndex inner outer p.1 p.2
  invFun := splitIndex inner outer
  left_inv p := splitIndex_insert inner outer p.1 p.2
  right_inv g := insert_splitIndex inner outer g
  map_add' p q := insertIndex_add_general inner outer p.1 q.1 p.2 q.2

variable (K : Type*) [Field K] (inner outer : ℕ)
  (z : Fin ((inner + 1) + outer))
  (tau : Fin (inner + outer) ≃ Remaining z)

def remainingExponents : (Remaining z → ℤ) ≃+ Indices (inner + outer) :=
  ({ toFun := fun e i => e (tau i)
     invFun := fun e i => e (tau.symm i)
     left_inv := by intro e; funext i; simp
     right_inv := by intro e; funext i; simp
     map_add' := by intros; rfl } : (Remaining z → ℤ) ≃+ (Fin (inner + outer) → ℤ)).trans
    (exponentAddEquiv (inner + outer))

/-- Actual global labels enter a full order with z in its chosen word slot,
and every remaining label in exactly its `tau` position. -/
def fullExponents : (Fin ((inner + 1) + outer) → ℤ) ≃+ Indices ((inner + 1) + outer) :=
  (splitExponents z).trans
    ((AddEquiv.prodCongr (AddEquiv.refl ℤ) (remainingExponents inner outer z tau)).trans
      (joinIndex inner outer))

def remainingPolynomial : CoefficientPolynomial K z →+*
    HahnSeries (Indices (inner + outer)) K :=
  polynomialViaEquiv (remainingExponents inner outer z tau)

def coefficientHahn : CoefficientField K z →+* HahnSeries (Indices (inner + outer)) K :=
  IsFractionRing.lift (g := remainingPolynomial K inner outer z tau)
    (polynomialViaEquiv_injective (remainingExponents inner outer z tau))

def fullPolynomial : LabelledPolynomial K ((inner + 1) + outer) →+*
    HahnSeries (Indices ((inner + 1) + outer)) K :=
  polynomialViaEquiv (fullExponents inner outer z tau)

def fullRational : CommonRational K ((inner + 1) + outer) →+*
    HahnSeries (Indices ((inner + 1) + outer)) K :=
  IsFractionRing.lift (g := fullPolynomial K inner outer z tau)
    (polynomialViaEquiv_injective (fullExponents inner outer z tau))

def zeroLabelExponents : (Remaining z → ℤ) →+ (Fin ((inner + 1) + outer) → ℤ) where
  toFun e := (splitExponents z).symm (0, e)
  map_zero' := by change (splitExponents z).symm 0 = 0; exact map_zero _
  map_add' e f := by
    change (splitExponents z).symm ((0, e) + (0, f)) = _
    exact map_add _ _ _

theorem zeroLabelExponents_injective : Function.Injective (zeroLabelExponents inner outer z) := by
  intro e f h
  have he := congrArg (fun p => ((splitExponents z) p).2) h
  simpa only [zeroLabelExponents, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply] using he

def coefficientPolynomialGlobal : CoefficientPolynomial K z →+*
    CommonRational K ((inner + 1) + outer) :=
  (algebraMap _ _).comp
    (AddMonoidAlgebra.mapDomainRingHom K (zeroLabelExponents inner outer z))

def coefficientGlobal : CoefficientField K z →+* CommonRational K ((inner + 1) + outer) :=
  IsFractionRing.lift (g := coefficientPolynomialGlobal K inner outer z)
    ((IsFractionRing.injective (LabelledPolynomial K ((inner + 1) + outer)) _).comp
      (AddMonoidAlgebra.mapDomain_injective (zeroLabelExponents_injective inner outer z)))

theorem full_zero_exponents (e : Remaining z → ℤ) :
    fullExponents inner outer z tau (zeroLabelExponents inner outer z e) =
      insertIndex inner outer 0 (remainingExponents inner outer z tau e) := by
  simp [fullExponents, zeroLabelExponents, joinIndex]
  rfl

/-- The field embedding square commutes for all rational coefficient functions,
so pre/post spectator denominators are expanded in the retained full order. -/
theorem coefficient_expansion_square (h : CoefficientField K z) :
    fullRational K inner outer z tau (coefficientGlobal K inner outer z h) =
      embedRemaining inner outer (coefficientHahn K inner outer z tau h) := by
  have hm : (fullRational K inner outer z tau).comp (coefficientGlobal K inner outer z) =
      (embedRemaining inner outer).comp (coefficientHahn K inner outer z tau) := by
    apply IsFractionRing.ringHom_ext (A := CoefficientPolynomial K z)
    intro P
    simp only [RingHom.comp_apply, coefficientGlobal, fullRational, coefficientHahn,
      IsFractionRing.lift_algebraMap]
    induction P using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | single e a =>
      simp only [coefficientPolynomialGlobal, RingHom.comp_apply,
        IsFractionRing.lift_algebraMap,
        fullPolynomial, remainingPolynomial, polynomialViaEquiv, RingHom.comp_apply]
      change scalarPolynomial
        ((AddMonoidAlgebra.domCongr K K (fullExponents inner outer z tau))
          (AddMonoidAlgebra.mapDomain (zeroLabelExponents inner outer z) (AddMonoidAlgebra.single e a))) =
        embedRemaining inner outer (scalarPolynomial
          ((AddMonoidAlgebra.domCongr K K (remainingExponents inner outer z tau))
            (AddMonoidAlgebra.single e a)))
      rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.domCongr_single,
        AddMonoidAlgebra.domCongr_single, scalarPolynomial_single, scalarPolynomial_single]
      rw [full_zero_exponents]
      change HahnSeries.single (insertEmbedding inner outer 0
        (remainingExponents inner outer z tau e)) a =
        HahnSeries.embDomain (insertEmbedding inner outer 0)
          (HahnSeries.single (remainingExponents inner outer z tau e) a)
      exact (HahnSeries.embDomain_single (f := insertEmbedding inner outer 0)).symm
  exact RingHom.congr_fun hm h

/-- A rational function in x and all spectators multiplies the full expansion
before taking its z-residue; the result is multiplication in the fused order. -/
theorem rational_coefficient_residue (h : CoefficientField K z)
    (R : CommonRational K ((inner + 1) + outer)) :
    residue inner outer (fullRational K inner outer z tau (coefficientGlobal K inner outer z h * R)) =
      coefficientHahn K inner outer z tau h *
        residue inner outer (fullRational K inner outer z tau R) := by
  rw [map_mul, coefficient_expansion_square, residue_mul_remaining]

end OrderedCollisionCoordinates.OrderedCoefficientCompatibility

namespace OrderedCollisionCoordinates.AdjacentSpectatorCancellation
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar OrderedCollisionCoordinates.OrderedCoefficientCompatibility
set_option backward.isDefEq.respectTransparency false

/-- Insert the first of two adjacent variables while retaining the second.
The arbitrary suffix remains the outer lex block. -/
def firstInsert (pre : ℕ) : (post : ℕ) → ℤ →
    Indices ((pre + 1) + post) → Indices ((pre + 2) + post)
  | 0, t, g => toLex ((ofLex g).1, toLex (t, (ofLex g).2))
  | post + 1, t, g => toLex ((ofLex g).1, firstInsert pre post t (ofLex g).2)

theorem firstInsert_le_iff (pre post : ℕ) (t : ℤ)
    (g h : Indices ((pre + 1) + post)) :
    firstInsert pre post t g ≤ firstInsert pre post t h ↔ g ≤ h := by
  induction post with
  | zero =>
    change (toLex ((ofLex g).1, toLex (t, (ofLex g).2)) : ℤ ×ₗ (ℤ ×ₗ Indices pre)) ≤
      toLex ((ofLex h).1, toLex (t, (ofLex h).2)) ↔ (show ℤ ×ₗ Indices pre from g) ≤ h
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rw [Prod.Lex.le_iff]
    simp
  | succ post ih =>
    change (toLex ((ofLex g).1, firstInsert pre post t (ofLex g).2) :
      ℤ ×ₗ Indices ((pre + 2) + post)) ≤
      toLex ((ofLex h).1, firstInsert pre post t (ofLex h).2) ↔
      (show ℤ ×ₗ Indices ((pre + 1) + post) from g) ≤ h
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex, ih]
    rfl

def firstEmbedding (pre post : ℕ) (t : ℤ) :
    Indices ((pre + 1) + post) ↪o Indices ((pre + 2) + post) :=
  OrderEmbedding.ofMapLEIff (firstInsert pre post t) (firstInsert_le_iff pre post t)

def firstValue (pre : ℕ) : (post : ℕ) → Indices ((pre + 2) + post) → ℤ
  | 0, g => (ofLex (ofLex g).2).1
  | post + 1, g => firstValue pre post (ofLex g).2

theorem firstValue_insert (pre post : ℕ) (t : ℤ) (g : Indices ((pre + 1) + post)) :
    firstValue pre post (firstInsert pre post t g) = t := by
  induction post with
  | zero => rfl
  | succ post ih => exact ih _

theorem adjacent_insertions (pre post : ℕ) (a b : ℤ) (g : Indices (pre + post)) :
    firstInsert pre post a (insertIndex pre post b g) =
      insertIndex (pre + 1) post b (insertIndex pre post a g) := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change toLex ((ofLex g).1, firstInsert pre post a (insertIndex pre post b (ofLex g).2)) = _
    rw [ih]
    rfl

/-- An arbitrary supported rational spectator-pole expansion independent of x
has the same z-residue in pre,z,x,post and pre,x,z,post. This compares the full
orders, with no projection of spectators before division. -/
theorem nonadjacent_pole_residue_cancel {K : Type*} [Field K] (pre post : ℕ)
    (F : HahnSeries (Indices ((pre + 1) + post)) K) :
    pullFiber (firstEmbedding pre post (-1))
      (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F) =
    residue (pre + 1) post (HahnSeries.embDomain (firstEmbedding pre post 0) F) := by
  classical
  ext g
  let t := (splitIndex pre post g).1
  let h := (splitIndex pre post g).2
  have hg : g = insertIndex pre post t h := (insert_splitIndex pre post g).symm
  rw [hg]
  change (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F).coeff
      (firstInsert pre post (-1) (insertIndex pre post t h)) =
    (HahnSeries.embDomain (firstEmbedding pre post 0) F).coeff
      (insertIndex (pre + 1) post (-1) (insertIndex pre post t h))
  conv_lhs => rw [adjacent_insertions pre post (-1) t]
  conv_rhs => rw [← adjacent_insertions pre post t (-1)]
  by_cases ht : t = 0
  · rw [ht]
    change (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F).coeff
      (insertEmbedding (pre + 1) post 0 (insertIndex pre post (-1) h)) =
      (HahnSeries.embDomain (firstEmbedding pre post 0) F).coeff
        (firstEmbedding pre post 0 (insertIndex pre post (-1) h))
    rw [HahnSeries.embDomain_coeff, HahnSeries.embDomain_coeff]
  · rw [HahnSeries.embDomain_of_notMem_range, HahnSeries.embDomain_of_notMem_range]
    · rintro ⟨a, ha⟩
      have hv := congrArg (firstValue pre post) ha
      exact ht ((firstValue_insert pre post 0 a).symm.trans
        (hv.trans (firstValue_insert pre post t _))).symm
    · rintro ⟨a, ha⟩
      have hv := congrArg (fun b => (splitIndex (pre + 1) post b).1) ha
      exact ht ((congrArg Prod.fst (splitIndex_insert (pre + 1) post 0 a)).symm.trans
        (hv.trans (congrArg Prod.fst (splitIndex_insert (pre + 1) post t _)))).symm

end OrderedCollisionCoordinates.AdjacentSpectatorCancellation
end

section
/- Translation is performed in the global rational field after algebraic
currying. Its u-residue is then expanded in the complete remaining Hahn order.
No collision theorem is postulated for arbitrary denominators. -/
namespace OrderedCollisionCoordinates.LocalResidueCurrying
open LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.PairDifferenceLocalization
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility CollisionLaurentKernels.ResidueBaseChange
open scoped RatFunc
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N) (x : Remaining z)

def translate : RatFunc (CoefficientField K z) ≃+* RatFunc (CoefficientField K z) :=
  IsFractionRing.ringEquivOfRingEquiv
    (Polynomial.algEquivAevalXAddC (remainingVariable K z x)).toRingEquiv

def localRational : CommonRational K N →+* RatFunc (CoefficientField K z) :=
  (translate K z x).toRingHom.comp (curryRational K z)

def localResidue (R : CommonRational K N) : CoefficientField K z :=
  (algebraMap (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z))
    (localRational K z x R)).coeff (-1)

theorem translate_diagonal :
    translate K z x
      (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) = RatFunc.X := by
  rw [translate, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [linearPole, Polynomial.algEquivAevalXAddC_apply,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem local_diagonal :
    localRational K z x (algebraMap _ (CommonRational K N) (pairPolynomial K z x.val)) =
      RatFunc.X := by
  simp only [localRational, RingHom.comp_apply, curryRational, IsFractionRing.lift_algebraMap]
  rw [curry_pair_left]
  exact translate_diagonal K z x

/-- Every integer residue weight becomes exactly u^r at the rational level. -/
theorem weighted_translation (r : ℤ) (R : CommonRational K N) :
    localRational K z x
      ((algebraMap _ (CommonRational K N) (pairPolynomial K z x.val)) ^ r * R) =
      RatFunc.X ^ r * localRational K z x R := by
  rw [map_mul, map_zpow₀, local_diagonal]

variable (pre post : ℕ) (z : Fin ((pre + 1) + post))
  (x : Remaining z) (tau : Fin (pre + post) ≃ Remaining z)

/-- u is the small local coordinate. The coefficient field is expanded in
the actual complete fused order supplied by tau, preserving all spectators. -/
def fusedLocalSeries (R : CommonRational K ((pre + 1) + post)) :
    LaurentSeries (HahnSeries (SupportedFieldWords.OrderedWords.Indices (pre + post)) K) :=
  seriesMap (coefficientHahn K pre post z tau)
    (algebraMap (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z))
      (localRational K z x R))

theorem fused_residue_square (R : CommonRational K ((pre + 1) + post)) :
    (fusedLocalSeries K pre post z x tau R).coeff (-1) =
      coefficientHahn K pre post z tau (localResidue K z x R) := rfl

theorem fused_labelled_coeff (R : CommonRational K ((pre + 1) + post))
    (e : Remaining z → ℤ) :
    ((fusedLocalSeries K pre post z x tau R).coeff (-1)).coeff
      (remainingExponents pre post z tau e) =
      (coefficientHahn K pre post z tau (localResidue K z x R)).coeff
        (remainingExponents pre post z tau e) := by rw [fused_residue_square]

end OrderedCollisionCoordinates.LocalResidueCurrying
end

section
/- Two true full orderings of one fixed-labelled global rational field.
The collision proposition records the full coefficient identity proved in
RationalCollision; the maps retain every original label and its order. -/
namespace OrderedCollisionCoordinates.AdjacentFullOrders
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar
open CollisionRationalExpansions.FullOrderSpectatorPole CollisionRationalExpansions.FullOrderSpectatorScalar LabelledRationalClearing.PairDifferenceLocalization
set_option backward.isDefEq.respectTransparency false

def firstSplit (pre : ℕ) : (post : ℕ) →
    Indices ((pre + 2) + post) → ℤ × Indices ((pre + 1) + post)
  | 0, g => ((ofLex (ofLex g).2).1, toLex ((ofLex g).1, (ofLex (ofLex g).2).2))
  | post + 1, g =>
    let p := firstSplit pre post (ofLex g).2
    (p.1, toLex ((ofLex g).1, p.2))

theorem firstSplit_insert (pre post : ℕ) (t : ℤ) (g : Indices ((pre + 1) + post)) :
    firstSplit pre post (firstInsert pre post t g) = (t, g) := by
  induction post with
  | zero => rfl
  | succ post ih =>
    simp only [firstSplit, firstInsert, ofLex_toLex, ih]
    rfl

theorem firstInsert_split (pre post : ℕ) (g : Indices ((pre + 2) + post)) :
    firstInsert pre post (firstSplit pre post g).1 (firstSplit pre post g).2 = g := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change toLex ((ofLex g).1,
      firstInsert pre post (firstSplit pre post (ofLex g).2).1
        (firstSplit pre post (ofLex g).2).2) = g
    rw [ih]
    rfl

theorem firstInsert_add_general (pre post : ℕ) (t u : ℤ)
    (g h : Indices ((pre + 1) + post)) :
    firstInsert pre post (t + u) (g + h) = firstInsert pre post t g + firstInsert pre post u h := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      firstInsert pre post (t + u) ((ofLex g).2 + (ofLex h).2)) = _
    rw [ih]
    rfl

def firstJoin (pre post : ℕ) :
    (ℤ × Indices ((pre + 1) + post)) ≃+ Indices ((pre + 2) + post) where
  toFun p := firstInsert pre post p.1 p.2
  invFun := firstSplit pre post
  left_inv p := firstSplit_insert pre post p.1 p.2
  right_inv := firstInsert_split pre post
  map_add' p q := firstInsert_add_general pre post p.1 q.1 p.2 q.2

variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z)

/-- The order sigma=pre,z,x,post, with tau the fixed remaining order pre,x,post. -/
def firstExponents : (Fin ((pre + 2) + post) → ℤ) ≃+ Indices ((pre + 2) + post) :=
  (splitExponents z).trans
    ((AddEquiv.prodCongr (AddEquiv.refl ℤ) (remainingExponents (pre + 1) post z tau)).trans
      (firstJoin pre post))

def firstPolynomial : LabelledPolynomial K ((pre + 2) + post) →+*
    HahnSeries (Indices ((pre + 2) + post)) K := polynomialViaEquiv (firstExponents pre post z tau)
def firstRational : CommonRational K ((pre + 2) + post) →+*
    HahnSeries (Indices ((pre + 2) + post)) K :=
  IsFractionRing.lift (g := firstPolynomial K pre post z tau)
    (polynomialViaEquiv_injective (firstExponents pre post z tau))

/-- The order sigma'=pre,x,z,post uses the identical global labels and tau. -/
def secondRational : CommonRational K ((pre + 2) + post) →+*
    HahnSeries (Indices ((pre + 2) + post)) K := fullRational K (pre + 1) post z tau

theorem first_zero_exponents (e : Remaining z → ℤ) :
    firstExponents pre post z tau (zeroLabelExponents (pre + 1) post z e) =
      firstInsert pre post 0 (remainingExponents (pre + 1) post z tau e) := by
  simp [firstExponents, zeroLabelExponents, firstJoin]
  rfl

theorem first_coefficient_square (h : CoefficientField K z) :
    firstRational K pre post z tau (coefficientGlobal K (pre + 1) post z h) =
      firstEmbed pre post (coefficientHahn K (pre + 1) post z tau h) := by
  have hm : (firstRational K pre post z tau).comp (coefficientGlobal K (pre + 1) post z) =
      (firstEmbed pre post).comp (coefficientHahn K (pre + 1) post z tau) := by
    apply IsFractionRing.ringHom_ext (A := CoefficientPolynomial K z)
    intro P
    simp only [RingHom.comp_apply, coefficientGlobal, firstRational, coefficientHahn,
      IsFractionRing.lift_algebraMap]
    induction P using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | single e a =>
      simp only [coefficientPolynomialGlobal, RingHom.comp_apply,
        IsFractionRing.lift_algebraMap, firstPolynomial, remainingPolynomial,
        polynomialViaEquiv, RingHom.comp_apply]
      change SupportedFieldWords.FiniteConvolution.scalarPolynomial
        ((AddMonoidAlgebra.domCongr K K (firstExponents pre post z tau))
          (AddMonoidAlgebra.mapDomain (zeroLabelExponents (pre + 1) post z) (AddMonoidAlgebra.single e a))) =
        firstEmbed pre post (SupportedFieldWords.FiniteConvolution.scalarPolynomial
          ((AddMonoidAlgebra.domCongr K K (remainingExponents (pre + 1) post z tau))
            (AddMonoidAlgebra.single e a)))
      rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.domCongr_single,
        AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single,
        SupportedFieldWords.FiniteConvolution.scalarPolynomial_single, first_zero_exponents]
      change HahnSeries.single (firstEmbedding pre post 0
        (remainingExponents (pre + 1) post z tau e)) a =
        HahnSeries.embDomain (firstEmbedding pre post 0)
          (HahnSeries.single (remainingExponents (pre + 1) post z tau e) a)
      exact HahnSeries.embDomain_single.symm
  exact RingHom.congr_fun hm h

theorem first_rational_coefficient_residue (h : CoefficientField K z)
    (R : CommonRational K ((pre + 2) + post)) :
    pullFiber (firstEmbedding pre post (-1))
      (firstRational K pre post z tau (coefficientGlobal K (pre + 1) post z h * R)) =
      coefficientHahn K (pre + 1) post z tau h *
        pullFiber (firstEmbedding pre post (-1)) (firstRational K pre post z tau R) := by
  rw [map_mul, first_coefficient_square, first_residue_mul_remaining]

def globalCorrelator (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ) :
    CommonRational K ((pre + 2) + post) :=
  algebraMap _ _ P / algebraMap _ _ (clearingPolynomial K ((pre + 2) + post) k)

/-- Exact coefficientwise collision proposition. x must occupy the boundary
slot of tau, so the two full orders differ by that adjacent transposition.
P is a finite numerator polynomial in z and Laurent in the remaining labels; Q
is exactly the fixed-labelled pair product. This is a Prop, not a theorem. -/
def CollisionStatement (x : Remaining z)
    (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ) : Prop :=
  ∀ (r : ℤ) (e : Remaining z → ℤ),
    let R := (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r *
      globalCorrelator K pre post P k
    (coefficientHahn K (pre + 1) post z tau (OrderedCollisionCoordinates.LocalResidueCurrying.localResidue K z x R)).coeff
      (remainingExponents (pre + 1) post z tau e) =
    (pullFiber (firstEmbedding pre post (-1)) (firstRational K pre post z tau R)).coeff
      (remainingExponents (pre + 1) post z tau e) -
    (residue (pre + 1) post (secondRational K pre post z tau R)).coeff
      (remainingExponents (pre + 1) post z tau e)

end OrderedCollisionCoordinates.AdjacentFullOrders
end

section
/- The complete collision proposition, proved in RationalCollision.
The adjacency condition is spelled out by tau(pre)=x. The numerator property
is the nonnegative z-exponent property of the actual finite polynomial P. -/
namespace OrderedCollisionCoordinates.RemainingCollisionGoal
open CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry

/-- The full generic rational collision statement. The supported-word host
derives its actual vacuum-word application. Monster/PCT identification
and an actual fused-state grading law require additional hypotheses and proofs. -/
def required (K : Type*) [Field K] (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z)
    (x : Remaining z) (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ) : Prop :=
  tau ⟨pre, by omega⟩ = x →
  (∀ e ∈ P.coeff.support, 0 ≤ e z) →
  OrderedCollisionCoordinates.AdjacentFullOrders.CollisionStatement K pre post z tau x P k

end OrderedCollisionCoordinates.RemainingCollisionGoal
end

section
/- Multiplicative flattening of nested Hahn series. This connects the compiled
two-variable Laurent kernel to an actual ordered Hahn exponent carrier. -/
namespace OrderedCollisionCoordinates.HahnIterateRing
open HahnSeries
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {Γ Δ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ] [Field K]

theorem flatten_mul (F G : HahnSeries Γ (HahnSeries Δ K)) :
    HahnSeries.ofIterate (F * G) = HahnSeries.ofIterate F * HahnSeries.ofIterate G := by
  classical
  ext g
  change ((F * G).coeff (ofLex g).1).coeff (ofLex g).2 = _
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_sum]
  simp_rw [HahnSeries.coeff_mul]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
    (fun v _ => (toLex (v.1.1, v.2.1), toLex (v.1.2, v.2.2)))
  · intro v hv
    rcases Finset.mem_sigma.mp hv with ⟨ho, hi⟩
    rcases Finset.mem_antidiagonal.mp ho with ⟨hF, hG, hout⟩
    rcases Finset.mem_antidiagonal.mp hi with ⟨hf, hg, hin⟩
    apply Finset.mem_antidiagonal.mpr
    refine ⟨hf, hg, ?_⟩
    change toLex (v.1.1 + v.1.2, v.2.1 + v.2.2) = g
    rw [hout, hin]
    rfl
  · intro v hv w hw he
    apply Sigma.ext
    · apply Prod.ext
      · exact congrArg (fun p => (ofLex p.1).1) he
      · exact congrArg (fun p => (ofLex p.2).1) he
    · apply heq_of_eq
      apply Prod.ext
      · exact congrArg (fun p => (ofLex p.1).2) he
      · exact congrArg (fun p => (ofLex p.2).2) he
  · intro w hw
    rcases Finset.mem_antidiagonal.mp hw with ⟨hF, hG, hsum⟩
    let o : Γ × Γ := ((ofLex w.1).1, (ofLex w.2).1)
    let i : Δ × Δ := ((ofLex w.1).2, (ofLex w.2).2)
    refine ⟨⟨o, i⟩, ?_, rfl⟩
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_antidiagonal.mpr
      refine ⟨HahnSeries.ne_zero_of_coeff_ne_zero hF, HahnSeries.ne_zero_of_coeff_ne_zero hG, ?_⟩
      exact congrArg (fun h => (ofLex h).1) hsum
    · apply Finset.mem_antidiagonal.mpr
      exact ⟨hF, hG, congrArg (fun h => (ofLex h).2) hsum⟩
  · intro v hv
    rfl

def flatten : HahnSeries Γ (HahnSeries Δ K) →+* HahnSeries (Γ ×ₗ Δ) K where
  toFun := HahnSeries.ofIterate
  map_zero' := by ext g; rfl
  map_one' := by
    ext g
    change ((1 : HahnSeries Γ (HahnSeries Δ K)).coeff (ofLex g).1).coeff (ofLex g).2 = _
    have hz : g = 0 ↔ (ofLex g).1 = 0 ∧ (ofLex g).2 = 0 := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · intro h
        change toLex (ofLex g) = toLex (0, 0)
        exact congrArg toLex (Prod.ext h.1 h.2)
    by_cases ho : (ofLex g).1 = 0
    · by_cases hi : (ofLex g).2 = 0 <;> simp [HahnSeries.coeff_one, ho, hi, hz]
    · simp [HahnSeries.coeff_one, ho, hz]
  map_add' F G := by ext g; rfl
  map_mul' := flatten_mul

def flattenEquiv : HahnSeries Γ (HahnSeries Δ K) ≃+* HahnSeries (Γ ×ₗ Δ) K :=
  RingEquiv.ofBijective flatten (HahnSeries.iterateEquiv.bijective)

end OrderedCollisionCoordinates.HahnIterateRing
end

section
/- The terminal scalar Laurent kernel is transported to the actual full Hahn
orders, first with zero spectator exponents and then with an arbitrary rational
coefficient already expanded in the full fused Hahn field. -/
namespace OrderedCollisionCoordinates.ContextualLaurentKernel
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar CollisionRationalExpansions.FullOrderSpectatorPole
open CollisionRationalExpansions.FullOrderSpectatorScalar OrderedCollisionCoordinates.HahnIterateRing CollisionLaurentKernels.LaurentCollision
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def pairIndex (pre : ℕ) : (post : ℕ) → (ℤ ×ₗ ℤ) → Indices ((pre + 2) + post)
  | 0, a => toLex ((ofLex a).1, toLex ((ofLex a).2, 0))
  | post + 1, a => toLex (0, pairIndex pre post a)
def xIndex (pre : ℕ) : (post : ℕ) → ℤ → Indices ((pre + 1) + post)
  | 0, a => toLex (a, 0)
  | post + 1, a => toLex (0, xIndex pre post a)

theorem pairIndex_le (pre post : ℕ) (a b : ℤ ×ₗ ℤ) :
    pairIndex pre post a ≤ pairIndex pre post b ↔ a ≤ b := by
  induction post with
  | zero =>
    change (toLex ((ofLex a).1, toLex ((ofLex a).2, (0 : Indices pre))) :
      ℤ ×ₗ (ℤ ×ₗ Indices pre)) ≤ toLex ((ofLex b).1, toLex ((ofLex b).2, 0)) ↔ a ≤ b
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rw [Prod.Lex.le_iff]
    simp [le_iff_lt_or_eq]
  | succ post ih =>
    change (toLex (0, pairIndex pre post a) : ℤ ×ₗ Indices ((pre + 2) + post)) ≤
      toLex (0, pairIndex pre post b) ↔ a ≤ b
    rw [Prod.Lex.le_iff]
    simpa using ih

theorem xIndex_le (pre post : ℕ) (a b : ℤ) : xIndex pre post a ≤ xIndex pre post b ↔ a ≤ b := by
  induction post with
  | zero =>
    change (toLex (a, (0 : Indices pre)) : ℤ ×ₗ Indices pre) ≤ toLex (b, 0) ↔ a ≤ b
    rw [Prod.Lex.le_iff]
    simp [le_iff_lt_or_eq]
  | succ post ih =>
    change (toLex (0, xIndex pre post a) : ℤ ×ₗ Indices ((pre + 1) + post)) ≤
      toLex (0, xIndex pre post b) ↔ a ≤ b
    rw [Prod.Lex.le_iff]
    simpa using ih

def pairEmbedding (pre post : ℕ) : (ℤ ×ₗ ℤ) ↪o Indices ((pre + 2) + post) :=
  OrderEmbedding.ofMapLEIff (pairIndex pre post) (pairIndex_le pre post)
def xEmbedding (pre post : ℕ) : ℤ ↪o Indices ((pre + 1) + post) :=
  OrderEmbedding.ofMapLEIff (xIndex pre post) (xIndex_le pre post)

theorem pairIndex_add (pre post : ℕ) (a b : ℤ ×ₗ ℤ) :
    pairIndex pre post (a + b) = pairIndex pre post a + pairIndex pre post b := by
  induction post with
  | zero =>
    change toLex ((ofLex a).1 + (ofLex b).1, toLex ((ofLex a).2 + (ofLex b).2, 0)) = _
    simp only [pairIndex]
    change toLex ((ofLex a).1 + (ofLex b).1, toLex ((ofLex a).2 + (ofLex b).2, 0)) =
      toLex ((ofLex a).1 + (ofLex b).1, toLex ((ofLex a).2 + (ofLex b).2, 0 + 0))
    rw [zero_add]
  | succ post ih =>
    change toLex (0, pairIndex pre post (a + b)) =
      toLex (0 + 0, pairIndex pre post a + pairIndex pre post b)
    rw [ih, zero_add]

def pairHom (pre post : ℕ) : (ℤ ×ₗ ℤ) →+ Indices ((pre + 2) + post) where
  toFun := pairIndex pre post
  map_zero' := by induction post with
    | zero => rfl
    | succ post ih => change toLex (0, pairIndex pre post 0) = 0; rw [ih]; rfl
  map_add' := pairIndex_add pre post

def firstPairFiber : ℤ ↪o (ℤ ×ₗ ℤ) :=
  OrderEmbedding.ofMapLEIff (fun a => toLex (a, (-1 : ℤ))) (by
    intro a b; rw [Prod.Lex.le_iff]; simp [le_iff_lt_or_eq])
def secondPairFiber : ℤ ↪o (ℤ ×ₗ ℤ) :=
  OrderEmbedding.ofMapLEIff (fun a => toLex ((-1 : ℤ), a)) (by
    intro a b; rw [Prod.Lex.le_iff]; simp)

theorem first_square (pre post : ℕ) (a : ℤ) :
    firstInsert pre post (-1) (xIndex pre post a) =
      pairIndex pre post (firstPairFiber a) := by
  induction post with
  | zero => rfl
  | succ post ih => change toLex (0, firstInsert pre post (-1) (xIndex pre post a)) = _; rw [ih]; rfl
theorem second_square (pre post : ℕ) (a : ℤ) :
    insertIndex (pre + 1) post (-1) (xIndex pre post a) =
      pairIndex pre post (secondPairFiber a) := by
  induction post with
  | zero => rfl
  | succ post ih => change toLex (0, insertIndex (pre + 1) post (-1) (xIndex pre post a)) = _; rw [ih]; rfl

theorem first_range (pre post : ℕ) (g : Indices ((pre + 1) + post)) (a : ℤ ×ₗ ℤ)
    (h : firstInsert pre post (-1) g = pairIndex pre post a) :
    g = xIndex pre post (ofLex a).1 := by
  induction post with
  | zero =>
    have h1 := congrArg (fun b => (ofLex b).1) h
    have h2 := congrArg (fun b => (ofLex (ofLex b).2).2) h
    change toLex (ofLex g) = toLex ((ofLex a).1, 0)
    exact congrArg toLex (Prod.ext h1 h2)
  | succ post ih =>
    have h1 : (ofLex g).1 = 0 := congrArg (fun b => (ofLex b).1) h
    have h2 := congrArg (fun b => (ofLex b).2) h
    have ht := ih _ h2
    change toLex (ofLex g) = toLex (0, xIndex pre post (ofLex a).1)
    exact congrArg toLex (Prod.ext h1 ht)
theorem second_range (pre post : ℕ) (g : Indices ((pre + 1) + post)) (a : ℤ ×ₗ ℤ)
    (h : insertIndex (pre + 1) post (-1) g = pairIndex pre post a) :
    g = xIndex pre post (ofLex a).2 := by
  induction post with
  | zero => exact congrArg (fun b => (ofLex b).2) h
  | succ post ih =>
    have h1 : (ofLex g).1 = 0 := congrArg (fun b => (ofLex b).1) h
    have h2 := congrArg (fun b => (ofLex b).2) h
    have ht := ih _ h2
    change toLex (ofLex g) = toLex (0, xIndex pre post (ofLex a).2)
    exact congrArg toLex (Prod.ext h1 ht)

theorem pullFiber_embDomain {A B C D R : Type*} [PartialOrder A] [PartialOrder B]
    [PartialOrder C] [PartialOrder D] [Zero R]
    (f : A ↪o B) (g : C ↪o D) (q : D ↪o B) (h : C ↪o A)
    (square : ∀ c, q (g c) = f (h c))
    (cartesian : ∀ d a, q d = f a → d ∈ Set.range g)
    (F : HahnSeries A R) :
    pullFiber q (HahnSeries.embDomain f F) = HahnSeries.embDomain g (pullFiber h F) := by
  classical
  ext d
  by_cases hd : d ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hd
    rw [pullFiber_coeff, square, HahnSeries.embDomain_coeff, HahnSeries.embDomain_coeff]
    rfl
  · rw [HahnSeries.embDomain_of_notMem_range hd]
    change (HahnSeries.embDomain f F).coeff (q d) = 0
    apply HahnSeries.embDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hd (cartesian d a ha.symm)

variable (K : Type*) [Field K]
def contextPair (pre post : ℕ) : LaurentSeries (LaurentSeries K) →+*
    HahnSeries (Indices ((pre + 2) + post)) K :=
  (HahnSeries.embDomainRingHom (pairHom pre post) (pairEmbedding pre post).injective
    (pairIndex_le pre post)).comp OrderedCollisionCoordinates.HahnIterateRing.flatten
def contextX (pre post : ℕ) (F : LaurentSeries K) :
    HahnSeries (Indices ((pre + 1) + post)) K := HahnSeries.embDomain (xEmbedding pre post) F

theorem context_first_residue (pre post : ℕ) (F : ZX K) :
    pullFiber (firstEmbedding pre post (-1)) (contextPair K pre post F) =
      contextX K pre post (resZ_ZX K F) := by
  exact pullFiber_embDomain (pairEmbedding pre post) (xEmbedding pre post)
    (firstEmbedding pre post (-1)) firstPairFiber (first_square pre post)
    (fun g a h => ⟨(ofLex a).1, (first_range pre post g a h).symm⟩) (HahnSeries.ofIterate F)
theorem context_second_residue (pre post : ℕ) (F : XZ K) :
    residue (pre + 1) post (contextPair K pre post F) =
      contextX K pre post (resZ_XZ K F) := by
  exact pullFiber_embDomain (pairEmbedding pre post) (xEmbedding pre post)
    (insertEmbedding (pre + 1) post (-1)) secondPairFiber (second_square pre post)
    (fun g a h => ⟨(ofLex a).2, (second_range pre post g a h).symm⟩) (HahnSeries.ofIterate F)

/-- The genuine scalar jump now lives in arbitrary full pre/post Hahn orders. -/
theorem contextual_monomial_jump (pre post m p : ℕ) (r : ℤ) :
    pullFiber (firstEmbedding pre post (-1))
      (contextPair K pre post (iotaZX K (z K ^ m * diagonal K ^ (r - p)))) -
    residue (pre + 1) post
      (contextPair K pre post (iotaXZ K (z K ^ m * diagonal K ^ (r - p)))) =
    contextX K pre post (resZ_XZ K (iotaFused K (z K ^ m * diagonal K ^ (r - p)))) := by
  rw [context_first_residue, context_second_residue]
  have h := congrArg (contextX K pre post) (rational_monomial_jump K m p r)
  have hs := (HahnSeries.embDomainLinearMap (R := K) (xEmbedding pre post)).map_sub
    (resZ_ZX K (iotaZX K (z K ^ m * diagonal K ^ (r - p))))
    (resZ_XZ K (iotaXZ K (z K ^ m * diagonal K ^ (r - p))))
  change contextX K pre post _ = contextX K pre post _ - contextX K pre post _ at hs
  exact hs.symm.trans h

/-- Arbitrary fully expanded fused coefficients multiply the two true full
orders before residue extraction. This includes rational spectator coefficients
whose pre/post order cannot be replaced by a fixed scalar specialization. -/
theorem contextual_coefficient_jump (pre post m p : ℕ) (r : ℤ)
    (A : HahnSeries (Indices ((pre + 1) + post)) K) :
    pullFiber (firstEmbedding pre post (-1))
      (firstEmbed pre post A * contextPair K pre post (iotaZX K (z K ^ m * diagonal K ^ (r - p)))) -
    residue (pre + 1) post
      (embedRemaining (pre + 1) post A * contextPair K pre post (iotaXZ K (z K ^ m * diagonal K ^ (r - p)))) =
    A * contextX K pre post (resZ_XZ K (iotaFused K (z K ^ m * diagonal K ^ (r - p)))) := by
  rw [first_residue_mul_remaining, residue_mul_remaining, ← mul_sub,
    contextual_monomial_jump]

end OrderedCollisionCoordinates.ContextualLaurentKernel
end

end D5.S3.VertexAlgebra
