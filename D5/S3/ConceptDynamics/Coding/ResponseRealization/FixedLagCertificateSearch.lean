/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search_correct; instance=D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound.unitCountMatrix
   digest: Executable full numbered fixed-positive-lag certificate search with unrestricted completeness. -/

import D5.S3.ConceptDynamics.Coding.OriginalResponseControls
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Encodable.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseRealization.FixedLagCertificateSearch

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
open D5.S3.ConceptDynamics.Coding.OriginalResponseControls

private def zeroPathEquiv {n : ℕ} (A : CountMat n n) (i j : Fin n) :
    FinitePath A 0 i j ≃ {u : Unit // i = j} where
  toFun p := by cases p; exact ⟨(), rfl⟩
  invFun p := by rcases p with ⟨u, h⟩; subst j; exact .nil i
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨u, h⟩; subst j; cases u; rfl

private def stepPathEquiv {n : ℕ} (A : CountMat n n) (d : ℕ) (i j : Fin n) :
    FinitePath A (d + 1) i j ≃ Σ t : Fin n, Fin (A i t) × FinitePath A d t j where
  toFun p := match p with | .cons a tail => ⟨_, a, tail⟩
  invFun p := .cons p.2.1 p.2.2
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨t, a, tail⟩; rfl

private def pathEncodable {n : ℕ} (A : CountMat n n) :
    (d : ℕ) → (i j : Fin n) → Encodable (FinitePath A d i j)
  | 0, i, j => Encodable.ofEquiv _ (zeroPathEquiv A i j)
  | d + 1, i, j =>
      letI (t : Fin n) : Encodable (FinitePath A d t j) := pathEncodable A d t j
      Encodable.ofEquiv _ (stepPathEquiv A d i j)

private instance {n d : ℕ} {A : CountMat n n} {i j : Fin n} :
    Encodable (FinitePath A d i j) := pathEncodable A d i j

private instance {n d : ℕ} {A : CountMat n n} {i j : Fin n} :
    DecidableEq (FinitePath A d i j) := Encodable.decidableEqOfEncodable _

private def pathFintype {n : ℕ} (A : CountMat n n) :
    (d : ℕ) → (i j : Fin n) → Fintype (FinitePath A d i j)
  | 0, i, j => Fintype.ofEquiv _ (zeroPathEquiv A i j).symm
  | d + 1, i, j =>
      letI (t : Fin n) : Fintype (FinitePath A d t j) := pathFintype A d t j
      Fintype.ofEquiv _ (stepPathEquiv A d i j).symm

private instance {n d : ℕ} {A : CountMat n n} {i j : Fin n} :
    Fintype (FinitePath A d i j) := pathFintype A d i j

/- Encode actual forward and inverse tables. All inverse-law tests are finite. -/
private def equivTables {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] :
    (α ≃ β) ≃ {fg : (α → β) × (β → α) //
      Function.LeftInverse fg.2 fg.1 ∧ Function.RightInverse fg.2 fg.1} where
  toFun e := ⟨(e.toFun, e.invFun), e.left_inv, e.right_inv⟩
  invFun fg := ⟨fg.1.1, fg.1.2, fg.2.1, fg.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance {α β : Type} [Fintype α] [Fintype β]
    [Encodable α] [Encodable β] [DecidableEq α] [DecidableEq β] :
    Encodable (α ≃ β) := Encodable.ofEquiv _ equivTables

private instance {n k l : ℕ} (U : CountMat n k) (V : CountMat k l)
    (i : Fin n) (j : Fin l) : Fintype (EdgePair U V i j) :=
  Sigma.instFintype

private def finPiTwoFintype {r s : ℕ} (T : Fin r → Fin s → Type)
    (h : ∀ i j, Fintype (T i j)) : Fintype (∀ i j, T i j) :=
  @Pi.instFintype _ _ inferInstance inferInstance
    (fun i => @Pi.instFintype _ _ inferInstance inferInstance (h i))

private instance {n k l : ℕ} (U : CountMat n k) (V : CountMat k l)
    (i : Fin n) (j : Fin l) : Encodable (EdgePair U V i j) :=
  @Sigma.encodable _ _ inferInstance (fun _ => inferInstance)

private def finPiTwoEncodable {r s : ℕ} (T : Fin r → Fin s → Type)
    (h : ∀ i j, Encodable (T i j)) : Encodable (∀ i j, T i j) :=
  @Encodable.finPi r _ (fun i => @Encodable.finPi s _ (h i))

/-- All four original endpoint-indexed numbered equivalences. -/
abbrev Maps {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n) (m : ℕ) :=
  (∀ i z, EdgePair A R i z ≃ EdgePair R B i z) ×
  (∀ t w, EdgePair B S t w ≃ EdgePair S A t w) ×
  (∀ i w, EdgePair R S i w ≃ FinitePath A m i w) ×
  (∀ t v, EdgePair S R t v ≃ FinitePath B m t v)

private instance {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n) (m : ℕ) : Fintype (Maps A B R S m) := by
  letI : Fintype (∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :=
    finPiTwoFintype _ (fun _ _ => Equiv.instFintype)
  letI : Fintype (∀ t w, EdgePair B S t w ≃ EdgePair S A t w) :=
    finPiTwoFintype _ (fun _ _ => Equiv.instFintype)
  letI : Fintype (∀ i w, EdgePair R S i w ≃ FinitePath A m i w) :=
    finPiTwoFintype _ (fun _ _ => Equiv.instFintype)
  letI : Fintype (∀ t v, EdgePair S R t v ≃ FinitePath B m t v) :=
    finPiTwoFintype _ (fun _ _ => Equiv.instFintype)
  unfold Maps
  infer_instance

private instance {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n) (m : ℕ) : Encodable (Maps A B R S m) := by
  letI : Encodable (∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :=
    finPiTwoEncodable _ (fun _ _ => inferInstance)
  letI : Encodable (∀ t w, EdgePair B S t w ≃ EdgePair S A t w) :=
    finPiTwoEncodable _ (fun _ _ => inferInstance)
  letI : Encodable (∀ i w, EdgePair R S i w ≃ FinitePath A m i w) :=
    finPiTwoEncodable _ (fun _ _ => inferInstance)
  letI : Encodable (∀ t v, EdgePair S R t v ≃ FinitePath B m t v) :=
    finPiTwoEncodable _ (fun _ _ => inferInstance)
  unfold Maps
  infer_instance

/-- Both literal same-map sweep laws, including the whole numbered output path. -/
def Compatible {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (d : Maps A B R S m) : Prop :=
  (∀ (i j : Fin n) (z : Fin k) (alpha : FinitePath A m i j) (r : Fin (R j z)),
    sweep d.1 alpha r =
      (let rs := (d.2.2.1 i j).symm alpha
       ⟨rs.1, rs.2.1, d.2.2.2 rs.1 z ⟨j, rs.2.2, r⟩⟩)) ∧
  (∀ (t z : Fin k) (w : Fin n) (beta : FinitePath B m t z) (s : Fin (S z w)),
    sweep d.2.1 beta s =
      (let sr := (d.2.2.2 t z).symm beta
       ⟨sr.1, sr.2.1, d.2.2.1 sr.1 w ⟨z, sr.2.2, s⟩⟩))

/-- The original AlignedA and AlignedB, on these same four maps. -/
def Aligned {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (d : Maps A B R S m) : Prop :=
  AlignedA d.1 d.2.1 d.2.2.1 ∧ AlignedB d.1 d.2.1 d.2.2.2

def Valid {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (aligned : Bool)
    (d : Maps A B R S m) : Prop := if aligned then Aligned d else Compatible d

private instance {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (d : Maps A B R S m) :
    Decidable (Compatible d) := by unfold Compatible; infer_instance

private instance {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (d : Maps A B R S m) :
    Decidable (Aligned d) := by unfold Aligned AlignedA AlignedB; infer_instance

private instance {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (aligned : Bool) (d : Maps A B R S m) :
    Decidable (Valid aligned d) := by unfold Valid; infer_instance

def Essential {r : ℕ} (X : CountMat r r) : Prop :=
  (∀ i : Fin r, ∃ j : Fin r, X i j ≠ 0) ∧
  (∀ j : Fin r, ∃ i : Fin r, X i j ≠ 0)

def Input {n k : ℕ} (A : CountMat n n) (B : CountMat k k) (m : ℕ) : Prop :=
  0 < n ∧ 0 < k ∧ 0 < m ∧ Essential A ∧ Essential B

private instance {r : ℕ} (X : CountMat r r) : Decidable (Essential X) :=
  @instDecidableAnd _ _
    (@Fintype.decidableForallFintype _ _
      (fun i => @Fintype.decidableExistsFintype _ _
        (fun j => inferInstanceAs (Decidable (X i j ≠ 0))) inferInstance) inferInstance)
    (@Fintype.decidableForallFintype _ _
      (fun j => @Fintype.decidableExistsFintype _ _
        (fun i => inferInstanceAs (Decidable (X i j ≠ 0))) inferInstance) inferInstance)

private instance {n k m : ℕ} (A : CountMat n n) (B : CountMat k k) :
    Decidable (Input A B m) := by unfold Input; infer_instance

/-- The original existence predicate. R and S are unrestricted natural matrices. -/
def OriginalExists {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (m : ℕ) (aligned : Bool) : Prop :=
  Input A B m ∧ ∃ (R : CountMat n k) (S : CountMat k n)
    (d : Maps A B R S m), Valid aligned d

def MatrixLaws {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n) (m : ℕ) : Prop :=
  A * R = R * B ∧ B * S = S * A ∧ R * S = A ^ m ∧ S * R = B ^ m

private instance {n k m : ℕ} (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n) : Decidable (MatrixLaws A B R S m) := by
  unfold MatrixLaws; infer_instance

private theorem pair_card {n k l : ℕ} (X : CountMat n k) (Y : CountMat k l)
    (i : Fin n) (j : Fin l) : Nat.card (EdgePair X Y i j) = (X * Y) i j := by
  classical
  simp [EdgePair, Nat.card_sigma, Nat.card_prod, Nat.card_fin, Matrix.mul_apply]

private theorem matrix_laws {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (d : Maps A B R S m) :
    MatrixLaws A B R S m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i z
    simpa only [pair_card] using Nat.card_congr (d.1 i z)
  · ext t w
    simpa only [pair_card] using Nat.card_congr (d.2.1 t w)
  · ext i w
    simpa only [pair_card, (numbered_path_count A m i w).2] using
      Nat.card_congr (d.2.2.1 i w)
  · ext t v
    simpa only [pair_card, (numbered_path_count B m t v).2] using
      Nat.card_congr (d.2.2.2 t v)

abbrev BoundedMatrix (r s M : ℕ) := Fin r → Fin s → Fin (M + 1)

private instance {r s M : ℕ} : Fintype (BoundedMatrix r s M) :=
  finPiTwoFintype _ (fun _ _ => inferInstance)

private instance {r s M : ℕ} : Encodable (BoundedMatrix r s M) :=
  finPiTwoEncodable _ (fun _ _ => inferInstance)

def entries {r s M : ℕ} (X : BoundedMatrix r s M) : CountMat r s :=
  fun i j => (X i j).val

/-- Inclusive zero-to-maximum entries and the four actual equivalence tables. -/
abbrev Candidate {n k : ℕ} (A : CountMat n n) (B : CountMat k k) (m : ℕ) :=
  Σ R : BoundedMatrix n k (powerMaximum A m),
    Σ S : BoundedMatrix k n (powerMaximum B m), Maps A B (entries R) (entries S) m

private instance {n k : ℕ} (A : CountMat n n) (B : CountMat k k) (m : ℕ) :
    Fintype (Candidate A B m) :=
  @Sigma.instFintype _ _ (fun _ =>
    @Sigma.instFintype _ _ (fun _ => inferInstance) inferInstance) inferInstance

private instance {n k : ℕ} (A : CountMat n n) (B : CountMat k k) (m : ℕ) :
    Encodable (Candidate A B m) :=
  @Sigma.encodable _ _ inferInstance (fun _ =>
    @Sigma.encodable _ _ inferInstance (fun _ => inferInstance))

/-- Full candidate checking rejects lag zero and tests both laws of the selected kind. -/
def candidateCheck {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (m : ℕ) (aligned : Bool) (c : Candidate A B m) : Bool :=
  decide (Input A B m ∧ MatrixLaws A B (entries c.1) (entries c.2.1) m ∧
    Valid aligned c.2.2)

/-- A finite search returning the actual matrices and all four numbered maps. -/
def search {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (m : ℕ) (aligned : Bool) : Option (Candidate A B m) :=
  if decide (Input A B m) then
    (Encodable.sortedUniv (Candidate A B m)).find? (candidateCheck A B m aligned)
  else none

def existsBool {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (m : ℕ) (aligned : Bool) : Bool := (search A B m aligned).isSome

/-- A returned witness satisfies the original input boundary and both selected laws. -/
theorem search_sound {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {aligned : Bool} {c : Candidate A B m} (h : search A B m aligned = some c) :
    Input A B m ∧ Valid aligned c.2.2 := by
  unfold search at h
  split at h
  · have hcheck : candidateCheck A B m aligned c = true :=
      List.find?_some (p := candidateCheck A B m aligned) (a := c)
        (l := Encodable.sortedUniv (Candidate A B m)) h
    change decide (Input A B m ∧ MatrixLaws A B (entries c.1) (entries c.2.1) m ∧
      Valid aligned c.2.2) = true at hcheck
    have hc : Input A B m ∧ MatrixLaws A B (entries c.1) (entries c.2.1) m ∧
        Valid aligned c.2.2 := of_decide_eq_true hcheck
    exact ⟨hc.1, hc.2.2⟩
  · cases h

/-- Terminating executable search is sound and complete for unrestricted original existence. -/
theorem search_correct {n k : ℕ} (A : CountMat n n) (B : CountMat k k)
    (m : ℕ) (aligned : Bool) :
    existsBool A B m aligned = true ↔ OriginalExists A B m aligned := by
  constructor
  · intro h
    cases hs : search A B m aligned with
    | none => simp [existsBool, hs] at h
    | some c =>
        have hc := search_sound hs
        exact ⟨hc.1, entries c.1, entries c.2.1, c.2.2, hc.2⟩
  · intro h
    rcases h with ⟨hinput, R, S, d, hd⟩
    have hR := factor_entry_upper hinput.2.2.2.2.1 d.2.2.1 d.2.2.2
    have hS := factor_entry_upper hinput.2.2.2.1.1 d.2.2.2 d.2.2.1
    let r : BoundedMatrix n k (powerMaximum A m) :=
      fun i z => ⟨R i z, Nat.lt_succ_of_le (hR i z)⟩
    let s : BoundedMatrix k n (powerMaximum B m) :=
      fun z i => ⟨S z i, Nat.lt_succ_of_le (hS z i)⟩
    let c : Candidate A B m := ⟨r, s, d⟩
    have hc : candidateCheck A B m aligned c = true := by
      simpa only [candidateCheck, decide_eq_true_eq] using
        (show Input A B m ∧ MatrixLaws A B (entries c.1) (entries c.2.1) m ∧
          Valid aligned c.2.2 from ⟨hinput, matrix_laws c.2.2, hd⟩)
    change (search A B m aligned).isSome = true
    rw [search, if_pos (show decide (Input A B m) = true from decide_eq_true hinput)]
    exact List.find?_isSome.mpr ⟨c, Encodable.mem_sortedUniv c, hc⟩

-- These evaluations execute the enumerator and both laws on actual numbered maps.
#eval (let A : CountMat 1 1 := fun _ _ => 1
  ("essential-loop", existsBool A A 1 false, existsBool A A 1 true))
#eval (let A : CountMat 1 1 := fun _ _ => 1
  ("zero-lag", existsBool A A 0 false, existsBool A A 0 true))
#eval (let A : CountMat 1 1 := fun _ _ => 1
  ("nonessential", existsBool (fun _ _ : Fin 1 => 0) A 1 false,
    existsBool (fun _ _ : Fin 1 => 0) A 1 true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
#eval ([false, true].map fun law =>
  let A : CountMat 1 1 := fun _ _ => 2
  match search A A 1 law with
  | none => (law, false, 0, 0, ([] : List (List ℕ)), [], [], [])
  | some c =>
      let R := entries c.1
      let S := entries c.2.1
      let phiR := (Encodable.sortedUniv (EdgePair A R 0 0)).map fun p =>
        let q := c.2.2.1 0 0 p
        [p.2.1.val, p.2.2.val, q.2.1.val, q.2.2.val]
      let phiS := (Encodable.sortedUniv (EdgePair A S 0 0)).map fun p =>
        let q := c.2.2.2.1 0 0 p
        [p.2.1.val, p.2.2.val, q.2.1.val, q.2.2.val]
      let psiA := (Encodable.sortedUniv (EdgePair R S 0 0)).map fun p =>
        let q := c.2.2.2.2.1 0 0 p
        [p.2.1.val, p.2.2.val, (match q with | .cons a _ => a.val)]
      let psiB := (Encodable.sortedUniv (EdgePair S R 0 0)).map fun p =>
        let q := c.2.2.2.2.2 0 0 p
        [p.2.1.val, p.2.2.val, (match q with | .cons a _ => a.val)]
      (law, candidateCheck A A 1 law c, R 0 0, S 0 0, phiR, phiS, psiA, psiB))

#print axioms search_sound
#print axioms search_correct

end D5.S3.ConceptDynamics.Coding.ResponseRealization.FixedLagCertificateSearch
