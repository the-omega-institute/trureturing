/- GID: D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original balanced maps yield controlled Type traces of exact length twice the lag minus one. -/

import D5.S3.ConceptDynamics.Coding.OriginalResponseControls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.OriginalQuantitativeExchangeChain

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
open D5.S3.ConceptDynamics.Coding.OriginalResponseControls
open scoped BigOperators

/-- The tag keeps the two original factor bounds distinct. -/
def factorBound (q M : ℕ) (diamond : Bool) : ℕ :=
  if diamond then max q M else max 1 M

/-- A data trace, retaining every factor, every node and its controls.
    The final node is checked by nil, including when the trace is empty. -/
inductive ControlledChain (q M : ℕ) :
    {n k : ℕ} → CountMat n n → CountMat k k → ℕ → Type where
  | nil {n : ℕ} (X : CountMat n n) (control : NodeControl X q M) :
      ControlledChain q M X X 0
  | cons {n k r length : ℕ} (U : CountMat n k) (V : CountMat k n)
      (diamond : Bool)
      (boundU : ∀ i j, U i j ≤ factorBound q M diamond)
      (boundV : ∀ i j, V i j ≤ factorBound q M diamond)
      (control : NodeControl (U * V) q M) {Z : CountMat r r}
      (tail : ControlledChain q M (V * U) Z length) :
      ControlledChain q M (U * V) Z (length + 1)

namespace ControlledChain

variable {q M a b c length : ℕ}
  {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}

/-- Erasure builds the ordinary chain with the trace's own U and V. -/
theorem erase (chain : ControlledChain q M X Y length) :
    ExchangeChain ℕ X Y length := by
  induction chain with
  | nil X _ => exact ExchangeChain.nil X
  | cons U V _ _ _ _ _ ih => exact ExchangeChain.cons U V ih

theorem sourceControl (chain : ControlledChain q M X Y length) :
    NodeControl X q M := by
  cases chain with
  | nil _ h => exact h
  | cons _ _ _ _ _ h _ => exact h

def single (U : CountMat a b) (V : CountMat b a) (diamond : Bool)
    (hU : ∀ i j, U i j ≤ factorBound q M diamond)
    (hV : ∀ i j, V i j ≤ factorBound q M diamond)
    (hX : NodeControl X q M) (hY : NodeControl Y q M)
    (hprodX : X = U * V) (hprodY : Y = V * U) :
    ControlledChain q M X Y 1 := by
  subst X
  subst Y
  exact .cons U V diamond hU hV hX (.nil _ hY)

def trans {l₁ l₂ : ℕ} (left : ControlledChain q M X Y l₁)
    (right : ControlledChain q M Y Z l₂) :
    ControlledChain q M X Z (l₁ + l₂) := by
  let rec go {a b c l₁ l₂ : ℕ}
      {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}
      (left : ControlledChain q M X Y l₁) (right : ControlledChain q M Y Z l₂) :
      ControlledChain q M X Z (l₁ + l₂) := by
    match left with
    | .nil _ _ => simpa using right
    | .cons U V diamond hU hV hX tail =>
        let rest := go tail right
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ControlledChain.cons U V diamond hU hV hX rest
  termination_by structural left
  exact go left right

def reverse (chain : ControlledChain q M X Y length) :
    ControlledChain q M Y X length := by
  let rec go {a b length : ℕ} {X : CountMat a a} {Y : CountMat b b}
      (chain : ControlledChain q M X Y length) :
      ControlledChain q M Y X length := by
    match chain with
    | .nil X h => exact .nil X h
    | .cons U V diamond hU hV hX tail =>
        let rest := go tail
        let last := ControlledChain.cons V U diamond hV hU
          tail.sourceControl (ControlledChain.nil _ hX)
        simpa [Nat.add_comm] using rest.trans last
  termination_by structural chain
  exact go chain

private theorem transpose_control {r : ℕ} {T : CountMat r r}
    (h : NodeControl T q M) : NodeControl T.transpose q M :=
  ⟨h.1, h.2.2.1, h.2.1, fun i j => h.2.2.2 j i⟩

def transpose (chain : ControlledChain q M X Y length) :
    ControlledChain q M X.transpose Y.transpose length := by
  let rec go {a b length : ℕ} {X : CountMat a a} {Y : CountMat b b}
      (chain : ControlledChain q M X Y length) :
      ControlledChain q M X.transpose Y.transpose length := by
    match chain with
    | .nil X h => exact .nil X.transpose (transpose_control h)
    | .cons U V diamond hU hV hX tail =>
        let rest := go tail
        have hXT := transpose_control hX
        rw [Matrix.transpose_mul] at hXT ⊢
        refine .cons V.transpose U.transpose diamond
          (fun i j => hV j i) (fun i j => hU j i) hXT ?_
        simpa only [Matrix.transpose_mul] using rest
  termination_by structural chain
  exact go chain

private theorem reindex_control {r s : ℕ} {T : CountMat r r}
    (e : Fin r ≃ Fin s) (h : NodeControl T q M) :
    NodeControl (Matrix.reindex e e T) q M := by
  have hcard : r = s := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  refine ⟨hcard ▸ h.1, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := h.2.1 (e.symm i)
    exact ⟨e j, by simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using hj⟩
  · intro j
    obtain ⟨i, hi⟩ := h.2.2.1 (e.symm j)
    exact ⟨e i, by simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using hi⟩
  · exact fun i j => h.2.2.2 (e.symm i) (e.symm j)

/-- Simultaneous endpoint renumbering of the one actual diamond step. -/
noncomputable def single_reindex {a' b' : ℕ}
    (e : Fin a ≃ Fin a') (f : Fin b ≃ Fin b')
    (U : CountMat a b) (V : CountMat b a) (diamond : Bool)
    (hU : ∀ i j, U i j ≤ factorBound q M diamond)
    (hV : ∀ i j, V i j ≤ factorBound q M diamond)
    (hX : NodeControl X q M) (hY : NodeControl Y q M)
    (hprodX : X = U * V) (hprodY : Y = V * U) :
    ControlledChain q M (Matrix.reindex e e X) (Matrix.reindex f f Y) 1 := by
  apply single (Matrix.reindex e f U) (Matrix.reindex f e V) diamond
    (fun i j => hU (e.symm i) (f.symm j))
    (fun i j => hV (f.symm i) (e.symm j))
    (reindex_control e hX) (reindex_control f hY)
  · rw [hprodX]
    exact (Matrix.submatrix_mul_equiv U V e.symm f.symm e.symm).symm
  · rw [hprodY]
    exact (Matrix.submatrix_mul_equiv V U f.symm e.symm f.symm).symm

end ControlledChain

/- This is the data refinement of finite_response_chain, using its same
   responseIndex and actual U/V formulas. The product identities and uniform
   inequalities are supplied together by ResponseControl, not reproved. -/
noncomputable def controlled_response_chain {p : ℕ} {A : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift A Q) {q M : ℕ}
    (controls : ResponseControl L q M) (start length : ℕ) :
    ControlledChain q M (finiteResponseMatrix L start)
      (finiteResponseMatrix L (start + length)) length := by
  classical
  induction length generalizing start with
  | zero =>
      simpa using ControlledChain.nil (finiteResponseMatrix L start)
        (controls.1 start _ (responseIndex L start))
  | succ length ih =>
      let e0 := responseIndex L start
      let e1 := responseIndex L (start + 1)
      let U := Matrix.reindex e0 e1 (incomingResponseU L start)
      let V := Matrix.reindex e1 e0 (incomingResponseV L start)
      obtain ⟨hbase, hstep, hU, hV⟩ := controls.2 start _ _ e0 e1
      have hX := controls.1 start _ e0
      change NodeControl (finiteResponseMatrix L start) q M at hX
      change finiteResponseMatrix L start = U * V at hbase
      change finiteResponseMatrix L (start + 1) = V * U at hstep
      rw [hbase] at hX ⊢
      refine ControlledChain.cons U V false hU hV hX ?_
      rw [← hstep]
      have hindex : start + 1 + length = start + (length + 1) := by omega
      rw [← hindex]
      exact ih (start + 1)

/-- Same last-step numbering and factors as finite_response_chain_to. -/
noncomputable def controlled_response_chain_to {p : ℕ} {A : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift A Q) {q M : ℕ}
    (controls : ResponseControl L q M) (start length : ℕ) {r : ℕ}
    (eEnd : Quotient (L.response (start + length + 1)) ≃ Fin r) :
    ControlledChain q M (finiteResponseMatrix L start)
      (Matrix.reindex eEnd eEnd (incomingResponseMatrix L (start + length + 1)))
      (length + 1) := by
  classical
  let d := start + length
  let eMid := responseIndex L d
  let U := Matrix.reindex eMid eEnd (incomingResponseU L d)
  let V := Matrix.reindex eEnd eMid (incomingResponseV L d)
  obtain ⟨hbase, hstep, hU, hV⟩ := controls.2 d _ _ eMid eEnd
  let last := ControlledChain.single U V false hU hV
    (controls.1 d _ eMid) (controls.1 (d + 1) _ eEnd) hbase hstep
  exact (controlled_response_chain L controls start length).trans last

/- The public diamond supplies D once. Both product equations and the factor
   bounds refer to that same D throughout the middle step. -/
private theorem controlled_square_ge_two {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) (hm : 2 ≤ m) :
    Nonempty (ControlledChain (Fintype.card (Edge R))
      (max (Nat.card (Edge A)) (Nat.card (Edge B))) A B (2 * m - 1)) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let q := Fintype.card (Edge R)
  let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    exact c.square_right_first_matrix g f
  obtain ⟨hL, hK, hKT⟩ := square_response_controls c
  have hCL : NodeControl Cleft q M := by
    rw [← hleftFirst]
    exact hL.1 1 _ (responseIndex L 1)
  have hCR : NodeControl Cright q M := by
    rw [← hrightFirst]
    exact hKT 1 _ (responseIndex K 1)
  let d := 1 + (m - 2) + 1
  have hd : d = m := by dsimp [d]; omega
  have hLF : L.response d = Setoid.ker Edge.source := by
    rw [hd]
    exact c.squareIncomingLift_forgets_at_lag
  have hKF : K.response d = Setoid.ker Edge.target := by
    rw [hd]
    exact c.squareOutgoingLift_forgets_at_lag
  obtain ⟨eA, hA⟩ := response_matrix_forgetting_reindexed L d hLF
  obtain ⟨eB, hB⟩ := response_matrix_forgetting_reindexed K d hKF
  let left : ControlledChain q M A Cleft ((m - 2) + 1) := by
    have chain := controlled_response_chain_to L hL 1 (m - 2) eA
    rw [hleftFirst, hA] at chain
    exact chain.reverse
  let right : ControlledChain q M Cright B ((m - 2) + 1) := by
    have chain := controlled_response_chain_to K hK 1 (m - 2) eB
    rw [hB] at chain
    simpa only [hrightFirst, Matrix.transpose_transpose] using chain.transpose
  let P := FirstResponseDiamond.columnMembership c.firstLeftClass *
    FirstResponseDiamond.rowMembership c.firstRightClass
  obtain ⟨D, hcol, hrow, hP, hD⟩ := square_diamond_controls c
  let middle : ControlledChain q M Cleft Cright 1 :=
    ControlledChain.single P D true hP hD hCL hCR hcol hrow
  have assembled := (left.trans middle).trans right
  refine ⟨?_⟩
  convert assembled using 1 <;> omega

private theorem controlled_square_one {n k : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S 1) :
    Nonempty (ControlledChain (Fintype.card (Edge R))
      (max (Nat.card (Edge A)) (Nat.card (Edge B))) A B 1) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let q := Fintype.card (Edge R)
  let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    exact c.square_right_first_matrix g f
  obtain ⟨hL, _, hKT⟩ := square_response_controls c
  have hCL : NodeControl Cleft q M := by
    rw [← hleftFirst]
    exact hL.1 1 _ (responseIndex L 1)
  have hCR : NodeControl Cright q M := by
    rw [← hrightFirst]
    exact hKT 1 _ (responseIndex K 1)
  obtain ⟨eA, hA⟩ := response_matrix_forgetting_reindexed L 1
    c.squareIncomingLift_forgets_at_lag
  obtain ⟨eB, hB⟩ := response_matrix_forgetting_reindexed K 1
    c.squareOutgoingLift_forgets_at_lag
  let eLeft := (responseIndex L 1).symm.trans eA
  let eRight := (responseIndex K 1).symm.trans eB
  have hleftIndex (i : Fin n) :
      (responseIndex L 1).symm (eLeft.symm i) = eA.symm i := by
    simp [eLeft]
  have hrightIndex (i : Fin k) :
      (responseIndex K 1).symm (eRight.symm i) = eB.symm i := by
    simp [eRight]
  have hleftReindex : Matrix.reindex eLeft eLeft Cleft = A := by
    ext i j
    rw [← hleftFirst]
    change incomingResponseMatrix L 1
      ((responseIndex L 1).symm (eLeft.symm i))
      ((responseIndex L 1).symm (eLeft.symm j)) = A i j
    rw [hleftIndex i, hleftIndex j]
    exact congrArg (fun X : CountMat n n => X i j) hA
  have hrightReindex : Matrix.reindex eRight eRight Cright = B := by
    ext i j
    rw [← hrightFirst]
    change incomingResponseMatrix K 1
      ((responseIndex K 1).symm (eRight.symm j))
      ((responseIndex K 1).symm (eRight.symm i)) = B i j
    rw [hrightIndex j, hrightIndex i]
    exact congrArg (fun X : CountMat k k => X j i) hB
  let P := FirstResponseDiamond.columnMembership c.firstLeftClass *
    FirstResponseDiamond.rowMembership c.firstRightClass
  obtain ⟨D, hcol, hrow, hP, hD⟩ := square_diamond_controls c
  have chain := ControlledChain.single_reindex eLeft eRight P D true
    hP hD hCL hCR hcol hrow
  rw [hleftReindex, hrightReindex] at chain
  exact ⟨chain⟩

/-- The fixed-lag unit constructs the controlled witness before erasing it. -/
theorem compatibleControlledChain {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    Nonempty (ControlledChain (Fintype.card (Edge R))
      (max (Nat.card (Edge A)) (Nat.card (Edge B))) A B (2 * m - 1)) := by
  by_cases h : m = 1
  · subst m
    simpa using controlled_square_one c
  · have hm : 2 ≤ m := by
      have hpos := c.positiveLag
      omega
    exact controlled_square_ge_two c hm

/-- Same original four numbered maps, same lag and same R/S. The existential
    is one controlled data trace; the ExchangeChain is its erasure. -/
theorem originalBalancedQuantitativeExchangeChain {n k m : ℕ}
    (A : CountMat n n) (B : CountMat k k) (R : CountMat n k) (S : CountMat k n)
    (essentialA : (∀ i, ∃ j, A i j ≠ 0) ∧ (∀ j, ∃ i, A i j ≠ 0))
    (essentialB : (∀ i, ∃ j, B i j ≠ 0) ∧ (∀ j, ∃ i, B i j ≠ 0))
    (positiveLag : 0 < m)
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j)
    (psiB : ∀ t z, EdgePair S R t z ≃ FinitePath B m t z)
    (hA : BalancedA phiR phiS psiA) (hB : BalancedB phiR phiS psiB) :
    let q := Fintype.card (Edge R)
    let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
    q = ∑ i, ∑ j, R i j ∧ max n k ≤ q ∧ q ≤ n * k * powerMaximum A m ∧
    ∃ trace : ControlledChain q M A B (2 * m - 1),
      Nonempty { chain : ExchangeChain ℕ A B (2 * m - 1) // chain = trace.erase } := by
  classical
  let c : CompatibleCertificate A B R S m := {
    positiveLag := positiveLag, essentialA := essentialA, essentialB := essentialB
    phi := phiR, psiA := psiA, psiB := psiB
    compatible := balanced_sweep A B R S essentialA essentialB positiveLag
      phiR phiS psiA psiB hA hB }
  obtain ⟨hq, hdim, hupper, _⟩ := originalBalancedResponseControls A B R S
    essentialA essentialB positiveLag phiR phiS psiA psiB hA hB
  obtain ⟨trace⟩ := compatibleControlledChain c
  exact ⟨hq, hdim, hupper, trace, ⟨⟨trace.erase, rfl⟩⟩⟩

end D5.S3.ConceptDynamics.Coding.OriginalQuantitativeExchangeChain
