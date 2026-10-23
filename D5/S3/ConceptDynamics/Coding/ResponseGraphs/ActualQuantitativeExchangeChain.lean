/- GID: D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuantitativeExchangeChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuantitativeExchangeChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent actual lift depths give the full original quantitative exchange chain. -/

import D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualResponseCounting
import D5.S3.ConceptDynamics.Coding.OriginalQuantitativeExchangeChain
import D5.S3.ConceptDynamics.Coding.FiniteResponseTable

/-! Actual numbered-edge response construction in the existing Coding domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualQuantitativeExchangeChain

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.Full62
open D5.S3.ConceptDynamics.Coding.OriginalResponseControls
open D5.S3.ConceptDynamics.Coding.OriginalQuantitativeExchangeChain
open D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualResponseCounting
open D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open scoped BigOperators

private theorem actual_control {n q M : ℕ} {A : CountMat n n} {C : CountMat q q}
    (I : ActualIncoming C A) (hA : Essential A) (hC : Essential C)
    (hM : Nat.card (Edge A) ≤ M) : ResponseControl I.stateLift q M := by
  have hout (u : Fin q) : ∃ (a : Edge A) (v : Fin q)
      (hv : I.stateLift.project v = a.target), (I.stateLift.lift a ⟨v,hv⟩).val = u := by
    obtain ⟨v,hv⟩ := hC.1 u
    let c : Edge C := ⟨u,v,⟨0,Nat.pos_of_ne_zero hv⟩⟩
    refine ⟨I.readout c,v,(I.read_target c).symm,?_⟩
    change (I.liftEdge (I.readout c) ⟨v,(I.read_target c).symm⟩).source = u
    rw [I.unique _ _ c rfl rfl]
  simpa using response_control I.stateLift hA.2 hout M hM

private noncomputable def zeroNumbering {n q : ℕ} {A : CountMat n n}
    (L : IncomingLift A (Fin q)) : Quotient (L.response 0) ≃ Fin q where
  toFun := Quotient.lift id (by
    intro u v h
    rw [(response_zero_and_step L).1] at h
    exact h)
  invFun := Quotient.mk (L.response 0)
  left_inv := by intro F; exact Quotient.inductionOn F (fun _ => rfl)
  right_inv := fun _ => rfl

private theorem zero_matrix {n q : ℕ} {A : CountMat n n} {C : CountMat q q}
    (I : ActualIncoming C A) :
    Matrix.reindex (zeroNumbering I.stateLift) (zeroNumbering I.stateLift)
      (incomingResponseMatrix I.stateLift 0) = C := by
  have h := response_matrix_reindexed I 0 q (zeroNumbering I.stateLift) id (fun _ => rfl)
  have hm : columnMembership (fun u => zeroNumbering I.stateLift
      (Quotient.mk (I.stateLift.response 0) u)) = (1 : CountMat q q) := by
    ext i j
    change (if j = i then (1 : ℕ) else 0) = _
    simp [Matrix.one_apply,eq_comm]
  have hs : columnSelector (id : Fin q → Fin q) = (1 : CountMat q q) := by
    ext i j
    simp [columnSelector,Matrix.one_apply,eq_comm]
  simpa only [hm,hs,Matrix.one_mul,Matrix.mul_one] using h

private theorem terminal_numbering {n q : ℕ} {A : CountMat n n}
    (L : IncomingLift A (Fin q)) (d : ℕ) (hd : Forgets L d) :
    ∃ e : Fin (@Fintype.card _ (responseFintype L d)) ≃ Fin n,
      Matrix.reindex e e (finiteResponseMatrix L d) = A := by
  classical
  letI := responseFintype L d
  obtain ⟨f,hf⟩ := response_matrix_forgetting_reindexed L d
    ((D5.S3.ConceptDynamics.Coding.FiniteResponseTable.forgets_iff_response L d).mp hd)
  refine ⟨(responseIndex L d).symm.trans f,?_⟩
  ext i j
  simpa [finiteResponseMatrix,Matrix.reindex_apply] using congrFun (congrFun hf i) j

private theorem zero_endpoint {q M a b l : ℕ}
    {X : CountMat a a} {Y : CountMat b b}
    (chain : ControlledChain q M X Y l) (hl : l = 0) :
    ∃ g : Fin a ≃ Fin b, Matrix.reindex g g X = Y := by
  cases chain with
  | nil X _ => exact ⟨Equiv.refl _, rfl⟩
  | cons U V tag hU hV hX tail => omega

private noncomputable def reindex_nonempty {q M a b l a' b' : ℕ}
    {X : CountMat a a} {Y : CountMat b b}
    (chain : ControlledChain q M X Y l) (hl : 0 < l)
    (e : Fin a ≃ Fin a') (f : Fin b ≃ Fin b') :
    ControlledChain q M (Matrix.reindex e e X) (Matrix.reindex f f Y) l := by
  let rec go {a b l a' b' : ℕ} {X : CountMat a a} {Y : CountMat b b}
      (chain : ControlledChain q M X Y l) :
      (hl : 0 < l) → (e : Fin a ≃ Fin a') → (f : Fin b ≃ Fin b') →
      ControlledChain q M (Matrix.reindex e e X) (Matrix.reindex f f Y) l := by
    match chain with
    | .nil _ _ => intro hl e f; omega
    | @ControlledChain.cons _ _ _ _ _ t U V tag hU hV hX _ tail =>
        intro hl e f
        by_cases ht : t = 0
        · let g := Classical.choose (zero_endpoint tail ht)
          have hg := Classical.choose_spec (zero_endpoint tail ht)
          have step := ControlledChain.single_reindex e (g.trans f) U V tag
            hU hV hX tail.sourceControl rfl rfl
          have hre := congrArg (Matrix.reindex f f) hg
          change Matrix.reindex (g.trans f) (g.trans f) (V * U) = _ at hre
          rw [hre] at step
          simpa only [ht, Nat.zero_add] using step
        · have hp : 0 < t := Nat.pos_of_ne_zero ht
          let first := ControlledChain.single_reindex e (Equiv.refl _) U V tag
            hU hV hX tail.sourceControl rfl rfl
          let rest := go tail hp (Equiv.refl _) f
          simpa only [Nat.add_comm] using first.trans rest
  termination_by structural chain
  exact go chain hl e f

private theorem actual_diamond {n k q r s : ℕ}
    {A : CountMat n n} {B : CountMat k k} {C : CountMat q q}
    (I : ActualIncoming C A) (J : ActualIncoming C.transpose B.transpose)
    (e : Quotient (I.stateLift.response 1) ≃ Fin r)
    (f : Quotient (J.stateLift.response 1) ≃ Fin s) :
    ∃ (U : CountMat r s) (V : CountMat s r),
      Matrix.reindex e e (incomingResponseMatrix I.stateLift 1) = U * V ∧
      (Matrix.reindex f f (incomingResponseMatrix J.stateLift 1)).transpose = V * U ∧
      (∀ i j, U i j ≤ q) := by
  classical
  let lc := fun u => e (Quotient.mk (I.stateLift.response 1) u)
  let rc := fun u => f (Quotient.mk (J.stateLift.response 1) u)
  let lr := fun i => Quotient.out (e.symm i)
  let rr := fun j => Quotient.out (f.symm j)
  have hl (i) : lc (lr i) = i := by simp [lc,lr,Quotient.out_eq]
  have hr (j) : rc (rr j) = j := by simp [rc,rr,Quotient.out_eq]
  have hcols (u v) (h : lc u = lc v) : ∀ x, C x u = C x v :=
    first_response_columns I (Quotient.exact (e.injective h))
  have hrows (u v) (h : rc u = rc v) : ∀ x, C u x = C v x :=
    first_response_columns J (Quotient.exact (f.injective h))
  obtain ⟨V,hL,hR,_⟩ := first_response_diamond C lc rc lr rr hl hr hcols hrows
  let U := columnMembership lc * rowMembership rc
  refine ⟨U,V,?_,?_,?_⟩
  · rw [response_matrix_reindexed I 1 r e lr hl]
    exact hL
  · rw [response_matrix_reindexed J 1 s f rr hr]
    have htS : (columnSelector rr).transpose = rowSelector rr := rfl
    have htI : (columnMembership rc).transpose = rowMembership rc := rfl
    change (columnMembership rc * C.transpose * columnSelector rr).transpose = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, htS, htI]
    simpa only [Matrix.mul_assoc] using hR
  · intro i j
    calc
      U i j ≤ ∑ _u : Fin q, (1 : ℕ) := by
        change (∑ u : Fin q, columnMembership lc i u * rowMembership rc u j) ≤ _
        apply Finset.sum_le_sum
        intro u _
        simp only [columnMembership,rowMembership]
        split_ifs <;> simp
      _ = q := by simp

private theorem canonical_zero {n q : ℕ} {A : CountMat n n} {C : CountMat q q}
    (I : ActualIncoming C A) :
    ∃ e : Fin (@Fintype.card _ (responseFintype I.stateLift 0)) ≃ Fin q,
      Matrix.reindex e e (finiteResponseMatrix I.stateLift 0) = C := by
  classical
  let e := (responseIndex I.stateLift 0).symm.trans (zeroNumbering I.stateLift)
  refine ⟨e,?_⟩
  ext i j
  simpa [e,finiteResponseMatrix,Matrix.reindex_apply] using
    congrFun (congrFun (zero_matrix I) i) j

private theorem reindex_comp {a b c : ℕ} (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c)
    (X : CountMat a a) :
    Matrix.reindex f f (Matrix.reindex e e X) =
      Matrix.reindex (e.trans f) (e.trans f) X := rfl

private theorem between_numberings {a b c : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}
    (e : Fin a ≃ Fin b) (f : Fin a ≃ Fin c)
    (he : Matrix.reindex e e X = Y) (hf : Matrix.reindex f f X = Z) :
    Matrix.reindex (e.symm.trans f) (e.symm.trans f) Y = Z := by
  rw [← he]
  ext i j
  simpa [Matrix.reindex_apply] using congrFun (congrFun hf i) j

/-- The original same-C arbitrary-span theorem, with both least depths allowed
to be zero. ControlledChain retains natural factors, essential nodes and the
order bound at every node; no endpoint permutation adds a step. -/
theorem full_original_52 {n k q : ℕ} (hn : 0 < n) (hk : 0 < k) (hq : 0 < q)
    {A : CountMat n n} {B : CountMat k k} {C : CountMat q q}
    (I : ActualIncoming C A) (J : ActualIncoming C.transpose B.transpose)
    (hA : Essential A) (hB : Essential B) (hC : Essential C)
    (dL dR : ℕ)
    (leastL : IsLeast {d | Forgets I.stateLift d} dL)
    (leastR : IsLeast {d | Forgets J.stateLift d} dR) :
    ∃ M ℓ, Nonempty (ControlledChain q M A B ℓ) ∧
      ℓ ≤ max (max 1 dL) (max dR (dL + dR - 1)) := by
  classical
  have hdL : Forgets I.stateLift dL := leastL.1
  have hdR : Forgets J.stateLift dR := leastR.1
  obtain ⟨U,V,hUV,hVU,hUq⟩ := actual_diamond I J
    (responseIndex I.stateLift 1) (responseIndex J.stateLift 1)
  let M := max (Nat.card (Edge A))
    (max (Nat.card (Edge B.transpose)) (∑ i, ∑ j, V i j))
  have hmA : Nat.card (Edge A) ≤ M := le_max_left _ _
  have hmB : Nat.card (Edge B.transpose) ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmV : (∑ i, ∑ j, V i j) ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have controlL := actual_control I hA hC hmA
  have controlR := actual_control J ⟨hB.2,hB.1⟩ ⟨hC.2,hC.1⟩ hmB
  have hU : ∀ i j, U i j ≤ factorBound q M true :=
    fun i j => (hUq i j).trans (le_max_left _ _)
  have hV : ∀ i j, V i j ≤ factorBound q M true := by
    intro i j
    apply le_trans _ (le_max_right q M)
    apply le_trans _ hmV
    exact (Finset.single_le_sum (f := fun j2 => V i j2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i2 => ∑ j2, V i2 j2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have leftControl := controlL.1 1 _ (responseIndex I.stateLift 1)
  have rightControl := (ControlledChain.nil _
    (controlR.1 1 _ (responseIndex J.stateLift 1))).transpose.sourceControl
  change finiteResponseMatrix I.stateLift 1 = U * V at hUV
  change (finiteResponseMatrix J.stateLift 1).transpose = V * U at hVU
  let diamond := ControlledChain.single U V true hU hV leftControl rightControl hUV hVU
  obtain ⟨eA,hEndA⟩ := terminal_numbering I.stateLift dL hdL
  obtain ⟨eB,hEndBT⟩ := terminal_numbering J.stateLift dR hdR
  have hEndB : Matrix.reindex eB eB (finiteResponseMatrix J.stateLift dR).transpose = B := by
    ext i j
    exact congrFun (congrFun hEndBT j) i
  obtain ⟨zI,hZeroI⟩ := canonical_zero I
  obtain ⟨zJ,hZeroJT⟩ := canonical_zero J
  have hZeroJ : Matrix.reindex zJ zJ (finiteResponseMatrix J.stateLift 0).transpose = C := by
    ext i j
    exact congrFun (congrFun hZeroJT j) i
  by_cases hL : dL = 0
  · subst dL
    let eCA := zI.symm.trans eA
    have hCA : Matrix.reindex eCA eCA C = A :=
      between_numberings zI eA hZeroI hEndA
    by_cases hR : dR = 0
    · subst dR
      let eCB := zJ.symm.trans eB
      have hCB : Matrix.reindex eCB eCB C = B :=
        between_numberings zJ eB hZeroJ hEndB
      have hCC := controlL.1 0 q (zeroNumbering I.stateLift)
      rw [zero_matrix I] at hCC
      have hCU : ∀ i j, C i j ≤ factorBound q M false :=
        fun i j => (hCC.2.2.2 i j).trans (le_max_right _ _)
      have hCV : ∀ i j, (1 : CountMat q q) i j ≤ factorBound q M false := by
        intro i j
        by_cases h : i = j <;> simp [Matrix.one_apply,h,factorBound]
      let same := ControlledChain.single C (1 : CountMat q q) false hCU hCV
        hCC hCC (Matrix.mul_one C).symm (Matrix.one_mul C).symm
      have chain := reindex_nonempty same (by omega) eCA eCB
      rw [hCA,hCB] at chain
      exact ⟨M,1,⟨chain⟩,by omega⟩
    · have hpR : 0 < dR := Nat.pos_of_ne_zero hR
      have full : ControlledChain q M (finiteResponseMatrix J.stateLift 0).transpose
          (finiteResponseMatrix J.stateLift dR).transpose dR := by
        have chain := controlled_response_chain J.stateLift controlR 0 dR
        rw [Nat.zero_add] at chain
        exact chain.transpose
      have hStart : Matrix.reindex (zJ.trans eCA) (zJ.trans eCA)
          (finiteResponseMatrix J.stateLift 0).transpose = A := by
        rw [← reindex_comp,hZeroJ,hCA]
      have chain := reindex_nonempty full hpR (zJ.trans eCA) eB
      change ControlledChain q M
        (Matrix.reindex (zJ.trans eCA) (zJ.trans eCA) (finiteResponseMatrix J.stateLift 0).transpose)
        (Matrix.reindex eB eB (finiteResponseMatrix J.stateLift dR).transpose) dR at chain
      rw [hStart,hEndB] at chain
      exact ⟨M,dR,⟨chain⟩,by omega⟩

  · have hpL : 0 < dL := Nat.pos_of_ne_zero hL
    by_cases hR : dR = 0
    · subst dR
      let eCB := zJ.symm.trans eB
      have hCB : Matrix.reindex eCB eCB C = B :=
        between_numberings zJ eB hZeroJ hEndB
      have full : ControlledChain q M (finiteResponseMatrix I.stateLift dL)
          (finiteResponseMatrix I.stateLift 0) dL := by
        have chain := controlled_response_chain I.stateLift controlL 0 dL
        rw [Nat.zero_add] at chain
        exact chain.reverse
      have hFinish : Matrix.reindex (zI.trans eCB) (zI.trans eCB)
          (finiteResponseMatrix I.stateLift 0) = B := by
        rw [← reindex_comp,hZeroI,hCB]
      have chain := reindex_nonempty full hpL eA (zI.trans eCB)
      change ControlledChain q M
        (Matrix.reindex eA eA (finiteResponseMatrix I.stateLift dL))
        (Matrix.reindex (zI.trans eCB) (zI.trans eCB) (finiteResponseMatrix I.stateLift 0)) dL at chain
      rw [hEndA,hFinish] at chain
      exact ⟨M,dL,⟨chain⟩,by omega⟩
    · have hpR : 0 < dR := Nat.pos_of_ne_zero hR
      have hidxL : 1 + (dL - 1) = dL := by omega
      have hidxR : 1 + (dR - 1) = dR := by omega
      have tailL := controlled_response_chain I.stateLift controlL 1 (dL - 1)
      have tailR := controlled_response_chain J.stateLift controlR 1 (dR - 1)
      rw [hidxL] at tailL
      rw [hidxR] at tailR
      let joined := (tailL.reverse.trans diamond).trans tailR.transpose
      have hp : 0 < (dL - 1 + 1) + (dR - 1) := by omega
      have chain := reindex_nonempty joined hp eA eB
      rw [hEndA,hEndB] at chain
      exact ⟨M,(dL - 1 + 1) + (dR - 1),⟨chain⟩,by omega⟩

#print axioms full_original_52

end D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualQuantitativeExchangeChain
