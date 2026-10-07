/- GID: D5/S3/VertexAlgebra/OrderedCollisionResidues
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/OrderedCollisionResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal residues, polynomial regularity, and spectator cancellation. -/

/-
Diagonal residues, polynomial regularity, and spectator cancellation.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.OrderedCollisionCoordinates
import D5.S3.VertexAlgebra.LabelledRationalClearing
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section
namespace D5.S3.VertexAlgebra

section
namespace OrderedCollisionResidues.AdjacentLabelledCoordinates
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution CollisionRationalExpansions.OrderedRationalExpansion
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization CollisionRationalExpansions.HahnFiberResidue OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.FullOrderSpectatorPole
set_option backward.isDefEq.respectTransparency false

def boundarySlot (pre post : ℕ) : Fin ((pre + 1) + post) := ⟨pre, by omega⟩

theorem exponents_boundary (pre post : ℕ) (a : ℤ) :
    exponentAddEquiv ((pre + 1) + post) (Pi.single (boundarySlot pre post) a) = xIndex pre post a := by
  induction post with
  | zero =>
    have hb : boundarySlot pre 0 = Fin.last pre := by ext; rfl
    have ht : (fun i : Fin pre => (Pi.single (boundarySlot pre 0) a : Fin (pre + 1) → ℤ) i.castSucc) = 0 := by
      funext i
      rw [hb]
      simp [Pi.single_apply, Fin.castSucc_ne_last]
    change toLex ((Pi.single (boundarySlot pre 0) a : Fin (pre + 1) → ℤ) (Fin.last pre),
      exponents pre (fun i => (Pi.single (boundarySlot pre 0) a : Fin (pre + 1) → ℤ) i.castSucc)) = toLex (a, (0 : Indices pre))
    rw [ht]
    have he : exponents pre 0 = 0 := (exponentAddEquiv pre).map_zero
    rw [he, hb]
    simp
  | succ post ih =>
    have hb : Fin.last ((pre + 1) + post) ≠ boundarySlot pre (post + 1) := by
      intro h; have hv := congrArg Fin.val h; dsimp [boundarySlot] at hv; omega
    have ht : (fun i : Fin ((pre + 1) + post) =>
      (Pi.single (boundarySlot pre (post + 1)) a : Fin ((pre + 1) + (post + 1)) → ℤ) i.castSucc) = (Pi.single (boundarySlot pre post) a : Fin ((pre + 1) + post) → ℤ) := by
      funext i
      simp only [Pi.single_apply]
      congr 1
      exact propext (by simp [Fin.ext_iff, boundarySlot])
    change toLex ((Pi.single (boundarySlot pre (post + 1)) a : Fin ((pre + 1) + (post + 1)) → ℤ) (Fin.last ((pre + 1) + post)),
      exponents ((pre + 1) + post)
        (fun i => (Pi.single (boundarySlot pre (post + 1)) a : Fin ((pre + 1) + (post + 1)) → ℤ) i.castSucc)) = toLex (0, xIndex pre post a)
    rw [ht]
    change toLex ((Pi.single (boundarySlot pre (post + 1)) a : Fin ((pre + 1) + (post + 1)) → ℤ) (Fin.last ((pre + 1) + post)),
      exponentAddEquiv ((pre + 1) + post) (Pi.single (boundarySlot pre post) a)) = _
    rw [ih]
    simp [Pi.single_apply, hb, Ne.symm hb]

theorem first_pair_square (pre post : ℕ) (t a : ℤ) :
    firstInsert pre post t (xIndex pre post a) = pairIndex pre post (toLex (a, t)) := by
  induction post with
  | zero => rfl
  | succ post ih => change toLex (0, firstInsert pre post t (xIndex pre post a)) = _; rw [ih]; rfl
theorem second_pair_square (pre post : ℕ) (t a : ℤ) :
    insertIndex (pre + 1) post t (xIndex pre post a) = pairIndex pre post (toLex (t, a)) := by
  induction post with
  | zero => rfl
  | succ post ih => change toLex (0, insertIndex (pre + 1) post t (xIndex pre post a)) = _; rw [ih]; rfl
theorem xIndex_zero (pre post : ℕ) : xIndex pre post 0 = 0 := by
  induction post with
  | zero => rfl
  | succ post ih => change toLex (0, xIndex pre post 0) = 0; rw [ih]; rfl

variable (K : Type*) [Field K] (pre post : ℕ) (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
  (hx : tau (boundarySlot pre post) = x)

include hx in
theorem remaining_basis (a : ℤ) :
    remainingExponents (pre + 1) post z tau (Pi.single x a) = xIndex pre post a := by
  have he : (fun j => (Pi.single x a : Remaining z → ℤ) (tau j)) = (Pi.single (boundarySlot pre post) a : Fin ((pre + 1) + post) → ℤ) := by
    funext j
    rw [← hx]
    simp only [Pi.single_apply, tau.injective.eq_iff]
  change exponentAddEquiv ((pre + 1) + post) (fun j => (Pi.single x a : Remaining z → ℤ) (tau j)) = _
  rw [he]
  exact exponents_boundary pre post a

theorem full_first_z_basis : firstExponents pre post z tau (Pi.single z 1) =
    pairIndex pre post (toLex (0, 1)) := by
  have he : (fun i : Remaining z => (Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) i.val) = 0 := by
    funext i; simp [i.property]
  change firstInsert pre post ((Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he, map_zero, ← xIndex_zero pre post, first_pair_square]
  simp

theorem full_second_z_basis : fullExponents (pre + 1) post z tau (Pi.single z 1) =
    pairIndex pre post (toLex (1, 0)) := by
  have he : (fun i : Remaining z => (Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) i.val) = 0 := by
    funext i; simp [i.property]
  change insertIndex (pre + 1) post ((Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single z 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he, map_zero, ← xIndex_zero pre post, second_pair_square]
  simp

include hx in
theorem full_first_x_basis : firstExponents pre post z tau (Pi.single x.val 1) =
    pairIndex pre post (toLex (1, 0)) := by
  have he : (fun i : Remaining z => (Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) i.val) = Pi.single x 1 := by
    funext i
    simp only [Pi.single_apply]
    congr 1
    exact propext Subtype.ext_iff.symm
  change firstInsert pre post ((Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he, remaining_basis pre post z tau x hx]
  simp only [Pi.single_apply, Ne.symm x.property, if_false]
  exact first_pair_square pre post 0 1

include hx in
theorem full_second_x_basis : fullExponents (pre + 1) post z tau (Pi.single x.val 1) =
    pairIndex pre post (toLex (0, 1)) := by
  have he : (fun i : Remaining z => (Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) i.val) = Pi.single x 1 := by
    funext i
    simp only [Pi.single_apply]
    congr 1
    exact propext Subtype.ext_iff.symm
  change insertIndex (pre + 1) post ((Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single x.val 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he, remaining_basis pre post z tau x hx]
  simp only [Pi.single_apply, Ne.symm x.property, if_false]
  exact second_pair_square pre post 0 1

end OrderedCollisionResidues.AdjacentLabelledCoordinates
end

section
/- Actual nonadjacent labelled poles, globally embedded before residue.
The spectator remains on its original side of the adjacent pair. -/
namespace OrderedCollisionResidues.ActualSpectatorPoleCancellation
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.AdjacentFullOrders OrderedCollisionResidues.AdjacentLabelledCoordinates OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar CollisionRationalExpansions.FullOrderSpectatorPole CollisionRationalExpansions.FullOrderSpectatorScalar
set_option backward.isDefEq.respectTransparency false

theorem exponents_boundary_value (pre post : ℕ)
    (e : Fin ((pre + 1) + post) → ℤ) :
    (OrderedCollisionCoordinates.OrderedCoefficientCompatibility.splitIndex pre post
      (exponentAddEquiv ((pre + 1) + post) e)).1 = e (boundarySlot pre post) := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change (OrderedCollisionCoordinates.OrderedCoefficientCompatibility.splitIndex pre post
      (exponentAddEquiv ((pre + 1) + post) (fun i => e i.castSucc))).1 = _
    rw [ih]
    rfl

theorem zero_boundary_insert (pre post : ℕ) (g : Indices ((pre + 1) + post))
    (hg : (OrderedCollisionCoordinates.OrderedCoefficientCompatibility.splitIndex pre post g).1 = 0) :
    firstInsert pre post 0 g = insertIndex (pre + 1) post 0 g := by
  have he := OrderedCollisionCoordinates.OrderedCoefficientCompatibility.insert_splitIndex pre post g
  rw [hg] at he
  rw [← he]
  exact adjacent_insertions pre post 0 0 _

variable (K : Type*) [Field K] (pre post : ℕ) (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x s : Remaining z)
  (hx : tau (boundarySlot pre post) = x)

include hx in
lemma spectator_boundary_zero (hs : s ≠ x) :
    (OrderedCollisionCoordinates.OrderedCoefficientCompatibility.splitIndex pre post
      (remainingExponents (pre + 1) post z tau (Pi.single s 1))).1 = 0 := by
  rw [show remainingExponents (pre + 1) post z tau (Pi.single s 1) =
    exponentAddEquiv ((pre + 1) + post) (fun j => (Pi.single s 1 : Remaining z → ℤ) (tau j)) from rfl,
    exponents_boundary_value, hx]
  simp [Pi.single_apply, Ne.symm hs]

include hx in
lemma first_spectator_basis (hs : s ≠ x) :
    firstExponents pre post z tau (Pi.single s.val 1) =
      insertIndex (pre + 1) post 0
        (remainingExponents (pre + 1) post z tau (Pi.single s 1)) := by
  have he : (fun i : Remaining z => (Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) i.val) = Pi.single s 1 := by
    funext i
    simp only [Pi.single_apply]
    congr 1
    exact propext Subtype.ext_iff.symm
  change firstInsert pre post ((Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he]
  simp only [Pi.single_apply, Ne.symm s.property, if_false]
  exact zero_boundary_insert pre post _ (spectator_boundary_zero pre post z tau x s hx hs)

include hx in
lemma second_spectator_basis (hs : s ≠ x) :
    fullExponents (pre + 1) post z tau (Pi.single s.val 1) =
      firstInsert pre post 0
        (remainingExponents (pre + 1) post z tau (Pi.single s 1)) := by
  have he : (fun i : Remaining z => (Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) i.val) = Pi.single s 1 := by
    funext i
    simp only [Pi.single_apply]
    congr 1
    exact propext Subtype.ext_iff.symm
  change insertIndex (pre + 1) post ((Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) z)
    (remainingExponents (pre + 1) post z tau (fun i : Remaining z => (Pi.single s.val 1 : Fin ((pre + 2) + post) → ℤ) i.val)) = _
  rw [he]
  simp only [Pi.single_apply, Ne.symm s.property, if_false]
  exact (zero_boundary_insert pre post _ (spectator_boundary_zero pre post z tau x s hx hs)).symm

lemma polynomial_variable (i : Fin ((pre + 2) + post)) :
    firstPolynomial K pre post z tau (variablePolynomial K i) =
      HahnSeries.single (firstExponents pre post z tau (Pi.single i 1)) 1 := by
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (firstExponents pre post z tau))
      (AddMonoidAlgebra.single (Pi.single i 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]

lemma second_polynomial_variable (i : Fin ((pre + 2) + post)) :
    fullPolynomial K (pre + 1) post z tau (variablePolynomial K i) =
      HahnSeries.single (fullExponents (pre + 1) post z tau (Pi.single i 1)) 1 := by
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (fullExponents (pre + 1) post z tau))
      (AddMonoidAlgebra.single (Pi.single i 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]

lemma remaining_variable (i : Remaining z) :
    coefficientHahn K (pre + 1) post z tau (remainingVariable K z i) =
      HahnSeries.single (remainingExponents (pre + 1) post z tau (Pi.single i 1)) 1 := by
  rw [remainingVariable, coefficientHahn, IsFractionRing.lift_algebraMap]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (remainingExponents (pre + 1) post z tau))
      (AddMonoidAlgebra.single (Pi.single i 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]

include hx in
theorem first_spectator_pole (hs : s ≠ x) :
    firstRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) =
    embedRemaining (pre + 1) post
      (coefficientHahn K (pre + 1) post z tau
        (remainingVariable K z x - remainingVariable K z s)) := by
  simp only [firstRational, IsFractionRing.lift_algebraMap, pairPolynomial,
    map_sub, polynomial_variable, remaining_variable]
  rw [full_first_z_basis, first_spectator_basis pre post z tau x s hx hs,
    remaining_basis pre post z tau x hx, ← second_pair_square pre post 0 1]
  change HahnSeries.single (insertEmbedding (pre + 1) post 0 (xIndex pre post 1)) 1 -
    HahnSeries.single (insertEmbedding (pre + 1) post 0 _) 1 =
    HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) _ -
    HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) _
  rw [HahnSeries.embDomain_single, HahnSeries.embDomain_single]

include hx in
theorem second_spectator_pole (hs : s ≠ x) :
    secondRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) =
    firstEmbed pre post
      (coefficientHahn K (pre + 1) post z tau
        (remainingVariable K z x - remainingVariable K z s)) := by
  simp only [secondRational, fullRational, IsFractionRing.lift_algebraMap, pairPolynomial,
    map_sub, second_polynomial_variable, remaining_variable]
  rw [full_second_z_basis, second_spectator_basis pre post z tau x s hx hs,
    remaining_basis pre post z tau x hx, ← first_pair_square pre post 0 1]
  change HahnSeries.single (firstEmbedding pre post 0 (xIndex pre post 1)) 1 -
    HahnSeries.single (firstEmbedding pre post 0 _) 1 =
    HahnSeries.embDomain (firstEmbedding pre post 0) _ -
    HahnSeries.embDomain (firstEmbedding pre post 0) _
  rw [HahnSeries.embDomain_single, HahnSeries.embDomain_single]

/- Both global full expansions are formed before extraction. Arbitrary rational
coefficients in every retained label expand in the actual fused order. -/
include hx in
theorem actual_spectator_pole_cancel (hs : s ≠ x) (c : CoefficientField K z) (m : ℕ) :
    pullFiber (firstEmbedding pre post (-1))
      (firstRational K pre post z tau (coefficientGlobal K (pre + 1) post z c *
        (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) ^ (-(m : ℤ)))) -
    residue (pre + 1) post
      (secondRational K pre post z tau (coefficientGlobal K (pre + 1) post z c *
        (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) ^ (-(m : ℤ)))) = 0 := by
  simp only [map_mul, map_zpow₀, first_coefficient_square]
  rw [first_spectator_pole K pre post z tau x s hx hs]
  rw [show secondRational K pre post z tau (coefficientGlobal K (pre + 1) post z c) =
    embedRemaining (pre + 1) post (coefficientHahn K (pre + 1) post z tau c) from
    coefficient_expansion_square K (pre + 1) post z tau c]
  rw [second_spectator_pole K pre post z tau x s hx hs]
  simpa only [map_zpow₀] using
    nonadjacent_spectator_factor_cancel pre post
      (coefficientHahn K (pre + 1) post z tau c)
      ((coefficientHahn K (pre + 1) post z tau
        (remainingVariable K z x - remainingVariable K z s)) ^ (-(m : ℤ)))

end OrderedCollisionResidues.ActualSpectatorPoleCancellation
end

section
namespace OrderedCollisionResidues.LabelledDiagonalResidue
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.GlobalRationalUncurry LabelledRationalClearing.PairDifferenceLocalization OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.AdjacentFullOrders OrderedCollisionResidues.AdjacentLabelledCoordinates OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionCoordinates.HahnIterateRing CollisionLaurentKernels.LaurentCollision
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

lemma flatten_single (a b : ℤ) (c : K) :
    OrderedCollisionCoordinates.HahnIterateRing.flatten (HahnSeries.single a (HahnSeries.single b c)) =
      HahnSeries.single (toLex (a,b)) c := by
  classical
  ext g
  change ((HahnSeries.single a (HahnSeries.single b c)).coeff (ofLex g).1).coeff (ofLex g).2 = _
  have hg : g = toLex (a,b) ↔ (ofLex g).1 = a ∧ (ofLex g).2 = b := by
    constructor
    · rintro rfl; exact ⟨rfl,rfl⟩
    · intro h; exact congrArg toLex (Prod.ext h.1 h.2)
  by_cases ha : (ofLex g).1 = a <;> by_cases hb : (ofLex g).2 = b <;>
    simp [HahnSeries.coeff_single, ha, hb, hg]

lemma context_single (pre post : ℕ) (a b : ℤ) (c : K) :
    contextPair K pre post (HahnSeries.single a (HahnSeries.single b c)) =
      HahnSeries.single (pairIndex pre post (toLex (a,b))) c := by
  change HahnSeries.embDomain (pairEmbedding pre post)
    (OrderedCollisionCoordinates.HahnIterateRing.flatten (HahnSeries.single a (HahnSeries.single b c))) = _
  rw [flatten_single, HahnSeries.embDomain_single]
  rfl

variable (pre post : ℕ) (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
  (hx : tau (boundarySlot pre post) = x)

lemma first_globalZ : firstRational K pre post z tau (globalZ K z) =
    contextPair K pre post (iotaZX K (CollisionLaurentKernels.LaurentCollision.z K)) := by
  rw [globalZ, firstRational, IsFractionRing.lift_algebraMap, iotaZX_z]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (firstExponents pre post z tau))
      (AddMonoidAlgebra.single (Pi.single z 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
  rw [full_first_z_basis]
  exact (context_single K pre post 0 1 1).symm

lemma second_globalZ : secondRational K pre post z tau (globalZ K z) =
    contextPair K pre post (iotaXZ K (CollisionLaurentKernels.LaurentCollision.z K)) := by
  rw [globalZ, secondRational, fullRational, IsFractionRing.lift_algebraMap, iotaXZ_z]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (fullExponents (pre + 1) post z tau))
      (AddMonoidAlgebra.single (Pi.single z 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
  rw [full_second_z_basis]
  have hc := context_single K pre post 1 0 1
  simpa only [HahnSeries.single_zero_one] using hc.symm

include hx in
lemma first_globalX :
    firstRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (variablePolynomial K x.val)) =
    contextPair K pre post (HahnSeries.single 1 1) := by
  rw [firstRational, IsFractionRing.lift_algebraMap]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (firstExponents pre post z tau))
      (AddMonoidAlgebra.single (Pi.single x.val 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
  rw [full_first_x_basis pre post z tau x hx]
  have hc := context_single K pre post 1 0 1
  simpa only [HahnSeries.single_zero_one] using hc.symm

include hx in
lemma second_globalX :
    secondRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (variablePolynomial K x.val)) =
    contextPair K pre post (HahnSeries.C (T K)) := by
  rw [secondRational, fullRational, IsFractionRing.lift_algebraMap]
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr K K (fullExponents (pre + 1) post z tau))
      (AddMonoidAlgebra.single (Pi.single x.val 1) 1)) = _
  rw [AddMonoidAlgebra.domCongr_single, SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
  rw [full_second_x_basis pre post z tau x hx]
  exact (context_single K pre post 0 1 1).symm

include hx in
theorem first_diagonal :
    firstRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) =
    contextPair K pre post (iotaZX K (diagonal K)) := by
  rw [pairPolynomial, map_sub, map_sub, ← globalZ, first_globalZ,
    first_globalX K pre post z tau x hx, iotaZX_diagonal]
  rw [← map_sub, iotaZX_z]
  rfl

include hx in
theorem second_diagonal :
    secondRational K pre post z tau
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) =
    contextPair K pre post (iotaXZ K (diagonal K)) := by
  rw [pairPolynomial, map_sub, map_sub, ← globalZ, second_globalZ,
    second_globalX K pre post z tau x hx, iotaXZ_diagonal]
  rw [← map_sub, iotaXZ_z]
  rfl

/- The old scalar kernel is now attached to the actual fixed global labels
and both complete Hahn expansions, for every integer diagonal exponent. -/
include hx in
theorem actual_diagonal_jump (r : ℤ) :
    CollisionRationalExpansions.HahnFiberResidue.pullFiber (CollisionRationalExpansions.FullOrderSpectatorPole.firstEmbedding pre post (-1))
      (firstRational K pre post z tau
        ((algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r)) -
    CollisionRationalExpansions.HahnFiberResidue.residue (pre + 1) post
      (secondRational K pre post z tau
        ((algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r)) =
    contextX K pre post (resZ_XZ K (iotaFused K (diagonal K ^ r))) := by
  simp only [map_zpow₀]
  rw [first_diagonal K pre post z tau x hx, second_diagonal K pre post z tau x hx]
  simpa only [pow_zero, one_mul, Nat.cast_zero, sub_zero, map_zpow₀] using
    contextual_monomial_jump K pre post 0 0 r

end OrderedCollisionResidues.LabelledDiagonalResidue
end

section
namespace OrderedCollisionResidues.LocalSpectatorResidue
open LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization CollisionRationalExpansions.OrderedRationalExpansion
open OrderedCollisionCoordinates.LocalResidueCurrying
open scoped RatFunc
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [Field E]

/-- A translated spectator pole has a nonzero constant term. Its inverse
stays in the supported power-series subring, so every negative coefficient
vanishes. This premise is proved from distinct labelled variables below. -/
theorem regular_pole_residue (a : E) (ha : a ≠ 0) (m : ℕ) :
    (algebraMap (RatFunc E) (LaurentSeries E)
      ((algebraMap (Polynomial E) (RatFunc E) (Polynomial.X + Polynomial.C a))⁻¹ ^ m)).coeff (-1) = 0 := by
  let φ : PowerSeries E := PowerSeries.X + PowerSeries.C a
  let embed := HahnSeries.ofPowerSeries ℤ E
  have hφ : PowerSeries.constantCoeff φ ≠ 0 := by simpa [φ] using ha
  have hp : embed φ * embed φ⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel φ hφ, map_one]
  have hn : embed φ ≠ 0 := by
    intro hz
    have h0 := congrArg (fun F : LaurentSeries E => F.coeff 0) hz
    exact ha (by simpa [embed, φ] using h0)
  have hinv : (embed φ)⁻¹ = embed φ⁻¹ := by
    calc
      (embed φ)⁻¹ = (embed φ)⁻¹ * 1 := (mul_one _).symm
      _ = (embed φ)⁻¹ * (embed φ * embed φ⁻¹) := congrArg ((embed φ)⁻¹ * ·) hp.symm
      _ = embed φ⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have he : algebraMap (RatFunc E) (LaurentSeries E)
      (algebraMap (Polynomial E) (RatFunc E) (Polynomial.X + Polynomial.C a)) = embed φ := by
    rw [← IsScalarTower.algebraMap_apply (Polynomial E) (RatFunc E) (LaurentSeries E)]
    simp [Polynomial.algebraMap_hahnSeries_apply, embed, φ]
  rw [map_pow, map_inv₀, he, hinv]
  change ((HahnSeries.ofPowerSeries ℤ E) (φ⁻¹) ^ m).coeff (-1) = 0
  rw [← map_pow]
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨n, hn⟩
  have hnonneg := Int.natCast_nonneg n
  change (n : ℤ) = -1 at hn
  omega

variable (K : Type*) [Field K] {N : ℕ} (z : Fin N) (x s : Remaining z)

theorem translate_spectator_pole :
    translate K z x (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z s)) =
      algebraMap _ (RatFunc (CoefficientField K z))
        (Polynomial.X + Polynomial.C (remainingVariable K z x - remainingVariable K z s)) := by
  rw [translate, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [linearPole, Polynomial.algEquivAevalXAddC_apply]
  ring

/-- The local u-residue of any nonadjacent labelled spectator pole vanishes.
The diagonal constant is nonzero because x and s are distinct actual labels. -/
theorem local_spectator_pole_residue (hs : s ≠ x) (m : ℕ) :
    localResidue K z x
      ((algebraMap _ (CommonRational K N) (pairPolynomial K z s.val)) ^ (-(m : ℤ))) = 0 := by
  have ha : remainingVariable K z x - remainingVariable K z s ≠ 0 :=
    sub_ne_zero.mpr ((remainingVariable_injective K z).ne (Ne.symm hs))
  unfold localResidue localRational
  simp only [RingHom.comp_apply, map_zpow₀, curryRational,
    IsFractionRing.lift_algebraMap]
  rw [curry_pair_left]
  change ((algebraMap (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z)))
    (translate K z x (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z s))) ^
      (-(m : ℤ))).coeff (-1) = 0
  rw [translate_spectator_pole, zpow_neg, zpow_natCast, ← inv_pow]
  rw [← map_inv₀, ← map_pow]
  exact regular_pole_residue _ ha m

end OrderedCollisionResidues.LocalSpectatorResidue
end

section
namespace OrderedCollisionResidues.LocalResidueLinear
open LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.GlobalRationalUncurry OrderedCollisionCoordinates.LocalResidueCurrying
open LabelledRationalClearing.PairDifferenceLocalization CollisionRationalExpansions.OrderedRationalExpansion
open scoped RatFunc
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N) (x : Remaining z)

theorem translate_constant (h : CoefficientField K z) :
    translate K z x (RatFunc.C h) = RatFunc.C h := by
  rw [← RatFunc.algebraMap_C, translate, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [Polynomial.algEquivAevalXAddC_apply]

theorem local_constant (h : CoefficientField K z) :
    localRational K z x (coefficient K z h) = RatFunc.C h := by
  rw [localRational, RingHom.comp_apply, curry_coefficient]
  exact translate_constant K z x h

theorem residue_coefficient_mul (h : CoefficientField K z) (R : CommonRational K N) :
    localResidue K z x (coefficient K z h * R) = h * localResidue K z x R := by
  unfold localResidue
  rw [map_mul, local_constant, map_mul]
  have hc : algebraMap (RatFunc (CoefficientField K z))
      (LaurentSeries (CoefficientField K z)) (RatFunc.C h) = HahnSeries.single 0 h := by
    rw [← RatFunc.algebraMap_C,
      ← IsScalarTower.algebraMap_apply (Polynomial (CoefficientField K z))
        (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z))]
    simp [Polynomial.algebraMap_hahnSeries_apply, PowerSeries.coe_C, HahnSeries.C_apply]
  rw [hc, HahnSeries.coeff_single_zero_mul]

theorem localResidue_add (R S : CommonRational K N) :
    localResidue K z x (R + S) = localResidue K z x R + localResidue K z x S := by
  simp [localResidue]

theorem weighted_spectator_zero (s : Remaining z) (hs : s ≠ x)
    (h : CoefficientField K z) (m : ℕ) :
    localResidue K z x (coefficient K z h *
      ((algebraMap _ (CommonRational K N) (pairPolynomial K z s.val)) ^ (-(m : ℤ)))) = 0 := by
  rw [residue_coefficient_mul, OrderedCollisionResidues.LocalSpectatorResidue.local_spectator_pole_residue K z x s hs,
    mul_zero]

end OrderedCollisionResidues.LocalResidueLinear
end

section
namespace OrderedCollisionResidues.CollisionResidueMaps
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.GlobalRationalUncurry OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
open CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.FullOrderSpectatorPole CollisionRationalExpansions.FullOrderSpectatorScalar
open OrderedCollisionCoordinates.LocalResidueCurrying OrderedCollisionResidues.LocalResidueLinear
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)

def firstResidue : CommonRational K ((pre + 2) + post) →+
    HahnSeries (Indices ((pre + 1) + post)) K where
  toFun R := pullFiber (firstEmbedding pre post (-1)) (firstRational K pre post z tau R)
  map_zero' := by ext g; simp
  map_add' R S := by ext g; simp

def secondResidue : CommonRational K ((pre + 2) + post) →+
    HahnSeries (Indices ((pre + 1) + post)) K :=
  (fiberAddHom (pre + 1) post (-1)).comp (secondRational K pre post z tau).toAddMonoidHom

def jump : CommonRational K ((pre + 2) + post) →+
    HahnSeries (Indices ((pre + 1) + post)) K :=
  firstResidue K pre post z tau - secondResidue K pre post z tau

def localResidueHom : CommonRational K ((pre + 2) + post) →+ CoefficientField K z where
  toFun := localResidue K z x
  map_zero' := by simp [localResidue]
  map_add' := localResidue_add K z x

def expandedLocal : CommonRational K ((pre + 2) + post) →+
    HahnSeries (Indices ((pre + 1) + post)) K :=
  (coefficientHahn K (pre + 1) post z tau).toAddMonoidHom.comp
    (localResidueHom K pre post z x)

theorem jump_coefficient_mul (h : CoefficientField K z)
    (R : CommonRational K ((pre + 2) + post)) :
    jump K pre post z tau (coefficient K z h * R) =
      coefficientHahn K (pre + 1) post z tau h * jump K pre post z tau R := by
  change pullFiber _ (firstRational K pre post z tau (coefficientGlobal K (pre + 1) post z h * R)) -
    residue (pre + 1) post (secondRational K pre post z tau (coefficientGlobal K (pre + 1) post z h * R)) = _
  simp only [secondRational]
  rw [first_rational_coefficient_residue,
    rational_coefficient_residue K (pre + 1) post z tau, ← mul_sub]
  rfl

theorem expandedLocal_coefficient_mul (h : CoefficientField K z)
    (R : CommonRational K ((pre + 2) + post)) :
    expandedLocal K pre post z tau x (coefficient K z h * R) =
      coefficientHahn K (pre + 1) post z tau h * expandedLocal K pre post z tau x R := by
  change coefficientHahn K (pre + 1) post z tau (localResidue K z x (coefficient K z h * R)) = _
  rw [residue_coefficient_mul, map_mul]
  rfl

end OrderedCollisionResidues.CollisionResidueMaps
end

section
namespace OrderedCollisionResidues.ActualDiagonalLocalResidue
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
open LabelledRationalClearing.GlobalRationalUncurry OrderedCollisionCoordinates.LocalResidueCurrying OrderedCollisionResidues.LocalResidueLinear
open OrderedCollisionResidues.LabelledDiagonalResidue OrderedCollisionCoordinates.ContextualLaurentKernel OrderedCollisionResidues.AdjacentLabelledCoordinates
open OrderedCollisionResidues.CollisionResidueMaps CollisionLaurentKernels.LaurentCollision
open scoped RatFunc
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)

theorem local_diagonal_power (r : ℤ) :
    localResidue K z x
      ((algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r) =
    if r = -1 then 1 else 0 := by
  unfold localResidue
  rw [map_zpow₀, local_diagonal, map_zpow₀]
  rw [show algebraMap (RatFunc (CoefficientField K z))
    (LaurentSeries (CoefficientField K z)) RatFunc.X = HahnSeries.single 1 1 from RatFunc.coe_X,
    ← RatFunc.single_zpow]
  simp [HahnSeries.coeff_single, eq_comm]

theorem contextX_one : contextX K pre post (1 : LaurentSeries K) = 1 := by
  rw [contextX, ← HahnSeries.single_zero_one, HahnSeries.embDomain_single]
  change HahnSeries.single (xIndex pre post 0) 1 = 1
  rw [xIndex_zero, HahnSeries.single_zero_one]

/-- The contextual scalar kernel is the expansion of the actual translated
global diagonal's local residue, with no compatibility premise. -/
theorem diagonal_collision (hx : tau (boundarySlot pre post) = x) (r : ℤ) :
    expandedLocal K pre post z tau x
      ((algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r) =
    jump K pre post z tau
      ((algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r) := by
  change coefficientHahn K (pre + 1) post z tau (localResidue K z x _) =
    CollisionRationalExpansions.HahnFiberResidue.pullFiber (CollisionRationalExpansions.FullOrderSpectatorPole.firstEmbedding pre post (-1))
      (firstRational K pre post z tau _) -
    CollisionRationalExpansions.HahnFiberResidue.residue (pre + 1) post (secondRational K pre post z tau _)
  rw [actual_diagonal_jump K pre post z tau x hx, local_diagonal_power]
  rw [map_zpow₀, iotaFused_diagonal, ← RatFunc.single_zpow]
  unfold resZ_XZ
  by_cases hr : r = -1
  · simp only [hr, ↓reduceIte, map_one, HahnSeries.coeff_single_same]
    exact (contextX_one K pre post).symm
  · simp [hr, HahnSeries.coeff_single, Ne.symm hr, contextX]

theorem coefficient_diagonal_collision (hx : tau (boundarySlot pre post) = x)
    (h : CoefficientField K z) (r : ℤ) :
    expandedLocal K pre post z tau x (coefficient K z h *
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r) =
    jump K pre post z tau (coefficient K z h *
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z x.val)) ^ r) := by
  rw [expandedLocal_coefficient_mul, jump_coefficient_mul, diagonal_collision K pre post z tau x hx]

end OrderedCollisionResidues.ActualDiagonalLocalResidue
end

section
/- The polynomial part is regular in z in both full orders and regular in u
after the actual rational translation. Coefficients may be arbitrary E. -/
namespace OrderedCollisionResidues.PolynomialResidueZero
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.GlobalRationalUncurry OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
open CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.FullOrderSpectatorPole CollisionRationalExpansions.FullOrderSpectatorScalar
open OrderedCollisionCoordinates.LocalResidueCurrying OrderedCollisionResidues.LocalResidueLinear OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionResidues.LabelledDiagonalResidue OrderedCollisionResidues.CollisionResidueMaps CollisionLaurentKernels.LaurentCollision
open scoped RatFunc
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)

theorem first_z_power_zero (n : ℕ) :
    firstResidue K pre post z tau (globalZ K z ^ n) = 0 := by
  change pullFiber _ (firstRational K pre post z tau (globalZ K z ^ n)) = 0
  rw [map_pow, first_globalZ, ← map_pow, context_first_residue]
  rw [iotaZX_z, HahnSeries.C_apply, HahnSeries.single_pow]
  have hz : resZ_ZX K (HahnSeries.single (n • (0 : ℤ)) (T K ^ n)) = 0 := by
    ext g
    by_cases hg : g = 0 <;>
      simp [resZ_ZX, HahnSeries.map_coeff, T, HahnSeries.single_pow, hg,
      HahnSeries.coeff_single, show (-1 : ℤ) ≠ (n : ℤ) by omega]
  rw [hz]
  simp [contextX]

theorem second_z_power_zero (n : ℕ) :
    secondResidue K pre post z tau (globalZ K z ^ n) = 0 := by
  change residue (pre + 1) post (secondRational K pre post z tau (globalZ K z ^ n)) = 0
  rw [map_pow, second_globalZ, ← map_pow, context_second_residue]
  simp [iotaXZ_z, HahnSeries.single_pow, resZ_XZ, HahnSeries.coeff_single,
    show (-1 : ℤ) ≠ (n : ℤ) by omega, contextX]

theorem uncurry_monomial (n : ℕ) (a : CoefficientField K z) :
    uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) (Polynomial.monomial n a)) =
      coefficient K z a * globalZ K z ^ n := by
  rw [uncurryRational, IsFractionRing.lift_algebraMap]
  simp [LabelledRationalClearing.GlobalRationalUncurry.polynomial, Polynomial.eval₂_monomial]

theorem first_polynomial_zero (q : Polynomial (CoefficientField K z)) :
    firstResidue K pre post z tau
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q t hq ht => simp only [map_add, hq, ht, add_zero]
  | monomial n a =>
    rw [uncurry_monomial]
    change pullFiber _ (firstRational K pre post z tau (coefficientGlobal K (pre + 1) post z a * globalZ K z ^ n)) = 0
    rw [first_rational_coefficient_residue]
    change coefficientHahn K (pre + 1) post z tau a * firstResidue K pre post z tau (globalZ K z ^ n) = 0
    rw [first_z_power_zero, mul_zero]

theorem second_polynomial_zero (q : Polynomial (CoefficientField K z)) :
    secondResidue K pre post z tau
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q t hq ht => simp only [map_add, hq, ht, add_zero]
  | monomial n a =>
    rw [uncurry_monomial]
    change residue (pre + 1) post (fullRational K (pre + 1) post z tau
      (coefficientGlobal K (pre + 1) post z a * globalZ K z ^ n)) = 0
    rw [rational_coefficient_residue]
    change coefficientHahn K (pre + 1) post z tau a * secondResidue K pre post z tau (globalZ K z ^ n) = 0
    rw [second_z_power_zero, mul_zero]

theorem local_polynomial_zero (q : Polynomial (CoefficientField K z)) :
    localResidue K z x
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) = 0 := by
  change ((algebraMap (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z)))
    ((translate K z x) (curryRational K z
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q))))).coeff (-1) = 0
  rw [curry_uncurry, translate,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    ← IsScalarTower.algebraMap_apply (Polynomial (CoefficientField K z))
      (RatFunc (CoefficientField K z)) (LaurentSeries (CoefficientField K z))]
  rw [Polynomial.algebraMap_hahnSeries_apply]
  change ((↑((Polynomial.algEquivAevalXAddC (LabelledRationalClearing.PairDifferenceLocalization.remainingVariable K z x)) q) :
    PowerSeries (CoefficientField K z)) : LaurentSeries (CoefficientField K z)).coeff (-1) = 0
  simp [PowerSeries.coeff_coe]

theorem polynomial_collision (q : Polynomial (CoefficientField K z)) :
    expandedLocal K pre post z tau x
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) =
    jump K pre post z tau
      (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) := by
  change coefficientHahn K (pre + 1) post z tau (localResidue K z x _) =
    firstResidue K pre post z tau _ - secondResidue K pre post z tau _
  rw [local_polynomial_zero, map_zero, first_polynomial_zero, second_polynomial_zero, sub_zero]

end OrderedCollisionResidues.PolynomialResidueZero
end

end D5.S3.VertexAlgebra
