/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeWickCurrentCommutator
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propagate current commutators through the native jet Wick recursion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator

/-! The current commutator through the scalar Wick recursion on actual native jet fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open ThirdEigenspacePairing (p48qForm)
open P48qTwistedHeisenberg (mode projectAt)
open P48qJetNormalOrdering (jetWeight normalOrderedCoeff normalOrderedField_coeff
  normalOrderedField_nil)
open P48qAllJetWickField
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil)
open private sumErase sumErase_cons sumErase_add smul_sumErase sumErase_twice_swap
  normalWick_cons_sumErase from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation
open private chargeWeight shift end_lie_smul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator

private theorem sumErase_append_single (kept : List Jet) (p : Jet)
    (f : Jet → List Jet → Module.End ℂ State) :
    sumErase (kept ++ [p]) f =
      sumErase kept (fun q rest => f q (rest ++ [p])) + f p kept := by
  induction kept generalizing f with
  | nil =>
    simp only [List.nil_append, sumErase_cons]
    simp [sumErase]
  | cons q tail ih =>
    simp only [List.cons_append, sumErase_cons, ih]
    abel

private theorem totalLevel_eraseIdx (jets : List Jet) (j : Fin jets.length) :
    totalLevel jets = (jets.get j).2.val + totalLevel (jets.eraseIdx j) := by
  induction jets with
  | nil => exact Fin.elim0 j
  | cons p tail ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · have h := ih i
      change (p.2 : ℕ) + totalLevel tail =
        (tail.get i).2.val + ((p.2 : ℕ) + totalLevel (tail.eraseIdx i))
      omega

private def commLinear (h : Cartan) (m : ℤ) :
    Module.End ℂ (Module.End ℂ State) where
  toFun B := ⁅mode h m, B⁆
  map_add' B C := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  map_smul' c B := end_lie_smul _ _ _

private theorem map_sumErase (L : Module.End ℂ (Module.End ℂ State))
    (word : List Jet) (f : Jet → List Jet → Module.End ℂ State) :
    L (sumErase word f) = sumErase word (fun x rest => L (f x rest)) := by
  simp only [sumErase, map_sum]

local notation "pairMatrix" => (Matrix.of fun p q : Jet => pairWeight p q)

/-- This exponent includes the level of the whole input word, so removing
one retained slot leaves the common exponent shifted by just the mode. -/
private def wickAt (a : Charge lattice) (r : ℤ) (pending kept : List Jet) :
    Module.End ℂ State :=
  normalWick pairMatrix (singletonWeight a)
    (fun xs => normalOrderedCoeff a (r - 3 * (totalLevel xs : ℤ)) xs)
    pending kept

private theorem wickAt_step (a : Charge lattice) (r : ℤ) (p : Jet)
    (tail kept : List Jet) :
    wickAt a r (p :: tail) kept =
      wickAt a r tail (kept ++ [p]) +
        singletonWeight a p • wickAt a r tail kept +
        sumErase tail (fun q rest => pairWeight p q • wickAt a r rest kept) := by
  exact normalWick_cons_sumErase pairMatrix (singletonWeight a) _ kept p tail

private theorem wickAt_nil (a : Charge lattice) (r : ℤ) (kept : List Jet) :
    wickAt a r [] kept = normalOrderedCoeff a (r - 3 * (totalLevel kept : ℤ)) kept := by
  simp only [wickAt, normalWick_nil]

private theorem wickAt_leaf_lie (h : Cartan) (m : ℤ) (a : Charge lattice)
    (r : ℤ) (kept : List Jet) :
    ⁅mode h m, wickAt a r [] kept⁆ =
      chargeWeight h m a • wickAt a (r - m) [] kept +
      sumErase kept (fun q rest => slotWeight h m q • wickAt a (r - m) [] rest) := by
  simp only [wickAt_nil, normalOrderedCoeff_commutator]
  apply congrArg₂ (· + ·)
  · rw [show r - 3 * (totalLevel kept : ℤ) - m =
      r - m - 3 * (totalLevel kept : ℤ) by omega]
  · unfold sumErase
    apply Finset.sum_congr rfl
    intro j _
    have hl := totalLevel_eraseIdx kept j
    dsimp only []
    rw [show r - 3 * (totalLevel kept : ℤ) - m + shift (kept.get j) =
      r - m - 3 * (totalLevel (kept.eraseIdx j) : ℤ) by
      unfold shift
      omega]

private theorem wickAt_lie (h : Cartan) (m : ℤ) (a : Charge lattice) (r : ℤ)
    (pending kept : List Jet) :
    ⁅mode h m, wickAt a r pending kept⁆ =
      chargeWeight h m a • wickAt a (r - m) pending kept +
      sumErase kept (fun q rest => slotWeight h m q • wickAt a (r - m) pending rest) +
      sumErase pending (fun q rest => slotWeight h m q • wickAt a (r - m) rest kept) := by
  cases pending with
  | nil =>
    simpa only [sumErase, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      using wickAt_leaf_lie h m a r kept
  | cons p tail =>
    let W := wickAt a (r - m)
    let δ := slotWeight h m
    let c := chargeWeight h m a
    let μ := singletonWeight a
    let A := pairWeight
    change commLinear h m (wickAt a r (p :: tail) kept) =
      c • W (p :: tail) kept +
        sumErase kept (fun q rest => δ q • W (p :: tail) rest) +
        sumErase (p :: tail) (fun q rest => δ q • W rest kept)
    rw [wickAt_step a r]
    simp only [map_add, map_smul, map_sumErase]
    change ⁅mode h m, wickAt a r tail (kept ++ [p])⁆ +
      μ p • ⁅mode h m, wickAt a r tail kept⁆ +
      sumErase tail (fun q rest => A p q • ⁅mode h m, wickAt a r rest kept⁆) = _
    rw [wickAt_lie h m a r tail (kept ++ [p]), wickAt_lie h m a r tail kept]
    have hpair :
        sumErase tail (fun q rest => A p q • ⁅mode h m, wickAt a r rest kept⁆) =
          sumErase tail (fun q rest => A p q •
            (c • W rest kept +
              sumErase kept (fun b xs => δ b • W rest xs) +
              sumErase rest (fun b xs => δ b • W xs kept))) := by
      unfold sumErase
      apply Finset.sum_congr rfl
      intro j _
      dsimp only []
      rw [wickAt_lie h m a r (tail.eraseIdx j) kept]
      rfl
    rw [hpair]
    change c • W tail (kept ++ [p]) +
        sumErase (kept ++ [p]) (fun q rest => δ q • W tail rest) +
        sumErase tail (fun q rest => δ q • W rest (kept ++ [p])) +
      μ p • (c • W tail kept + sumErase kept (fun q rest => δ q • W tail rest) +
        sumErase tail (fun q rest => δ q • W rest kept)) +
      sumErase tail (fun q rest => A p q •
        (c • W rest kept + sumErase kept (fun b xs => δ b • W rest xs) +
          sumErase rest (fun b xs => δ b • W xs kept))) = _
    have hW (xs ys : List Jet) : W (p :: xs) ys =
        W xs (ys ++ [p]) + μ p • W xs ys +
        sumErase xs (fun q rest => A p q • W rest ys) :=
      wickAt_step a (r - m) p xs ys
    rw [sumErase_append_single, sumErase_cons, hW tail kept]
    simp only [hW, smul_add, smul_sumErase, sumErase_add, smul_smul]
    have hcross :
        sumErase tail (fun q rest => sumErase kept (fun b xs =>
          (A p q * δ b) • W rest xs)) =
        sumErase kept (fun b xs => sumErase tail (fun q rest =>
          (δ b * A p q) • W rest xs)) := by
      unfold sumErase
      rw [Finset.sum_comm]
      simp only [mul_comm]
    have hdouble :
        sumErase tail (fun q rest => sumErase rest (fun b xs =>
          (A p q * δ b) • W xs kept)) =
        sumErase tail (fun b rest => sumErase rest (fun q xs =>
          (δ b * A p q) • W xs kept)) := by
      rw [sumErase_twice_swap tail (fun q b xs => (A p q * δ b) • W xs kept)]
      simp only [mul_comm]
    rw [hcross, hdouble]
    simp only [mul_comm (μ p), mul_comm (A p _) c]
    abel
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

set_option maxHeartbeats 800000 in
/-- The complete all-level Wick coefficients satisfy the actual current commutator. -/
theorem allJetCoeff_commutator (h : Cartan) (m : ℤ) (a : Charge lattice)
    (k : ℤ) (jets : List Jet) :
    ⁅mode h m, allJetCoeff a k jets⁆ =
      chargeWeight h m a • allJetCoeff a (k - m) jets +
      sumErase jets (fun p rest =>
        slotWeight h m p • allJetCoeff a (k - m + shift p) rest) := by
  have hW (l : ℤ) (xs : List Jet) :
      allJetCoeff a l xs = wickAt a (l + 3 * (totalLevel xs : ℤ)) xs [] := by
    unfold allJetCoeff normalWickWord wickAt leafShift
    apply congrArg (fun N => normalWick pairMatrix (singletonWeight a) N xs [])
    funext ys
    rw [show l + 3 * ((totalLevel xs : ℤ) - totalLevel ys) =
      l + 3 * (totalLevel xs : ℤ) - 3 * (totalLevel ys : ℤ) by omega]
  rw [hW k, wickAt_lie, hW (k - m)]
  simp only [sumErase, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [show k + 3 * (totalLevel jets : ℤ) - m =
    k - m + 3 * (totalLevel jets : ℤ) by omega]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [hW]
  have hl := totalLevel_eraseIdx jets j
  rw [show k - m + shift (jets.get j) + 3 * (totalLevel (jets.eraseIdx j) : ℤ) =
    k - m + 3 * (totalLevel jets : ℤ) by unfold shift; omega]

#print axioms allJetCoeff_commutator

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator
