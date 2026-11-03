/- GID: D5/S3/ConceptDynamics/Coding/OriginalResponseControls
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalResponseControls
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original balanced maps control response quotient orders, essentiality and actual diamond factors. -/

import D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.NatCard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.OriginalResponseControls

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
open scoped BigOperators

/- This is the existing proof-local hForward construction in
   CompatibleCertificate.square_graph_essential_and_projections, used before
   a CompatibleCertificate exists. No new mathematical credit is assigned. -/
private theorem numbered_path_from {n : ℕ} {A : CountMat n n}
    (hA : ∀ i : Fin n, ∃ j : Fin n, A i j ≠ 0) :
    ∀ (d : ℕ) (i : Fin n), ∃ j, Nonempty (FinitePath A d i j) := by
  intro d
  induction d with
  | zero => intro i; exact ⟨i, ⟨.nil i⟩⟩
  | succ d ih =>
      intro i
      obtain ⟨j, hj⟩ := hA i
      obtain ⟨z, ⟨path⟩⟩ := ih j
      exact ⟨z, ⟨.cons ⟨0, Nat.pos_of_ne_zero hj⟩ path⟩⟩

/- A row witness is recovered from the actual inverse path bijection.
   This helper is consumed for both R and S; no counting surrogate is used. -/
private theorem first_factor_rows {n k m : ℕ}
    {A : CountMat n n} {R : CountMat n k} {S : CountMat k n}
    (hA : ∀ i : Fin n, ∃ j : Fin n, A i j ≠ 0)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j) :
    ∀ i : Fin n, ∃ z : Fin k, Nonempty (Fin (R i z)) := by
  intro i
  obtain ⟨j, ⟨alpha⟩⟩ := numbered_path_from hA m i
  let rs := (psiA i j).symm alpha
  exact ⟨rs.1, ⟨rs.2.1⟩⟩

/- BDR's boundary projection, retaining both the vertex and edge number. -/
private theorem balanced_first_boundary {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j)
    (hA : BalancedA phiR phiS psiA)
    (hS : ∀ z : Fin k, ∃ w : Fin n, Nonempty (Fin (S z w)))
    {i j : Fin n} {z : Fin k}
    (alpha : FinitePath A m i j) (r : Fin (R j z)) :
    (let p := sweep phiR alpha r
     (⟨p.1, p.2.1⟩ : Σ t : Fin k, Fin (R i t))) =
    (let rs := (psiA i j).symm alpha
     (⟨rs.1, rs.2.1⟩ : Σ t : Fin k, Fin (R i t))) := by
  obtain ⟨w, ⟨s⟩⟩ := hS z
  exact congrArg
    (fun x : Σ t : Fin k, Fin (R i t) ×
      (Σ v : Fin n, Fin (S t v) × FinitePath A m v w) =>
        (⟨x.1, x.2.1⟩ : Σ t : Fin k, Fin (R i t)))
    (hA alpha r s)

/-- Both balances imply the full R compatibility equation for the same
    four bijections, on every actual numbered path at the original lag. -/
theorem balanced_sweep {n k m : ℕ}
    (A : CountMat n n) (B : CountMat k k)
    (R : CountMat n k) (S : CountMat k n)
    (essentialA :
      (∀ i : Fin n, ∃ j : Fin n, A i j ≠ 0) ∧
      (∀ j : Fin n, ∃ i : Fin n, A i j ≠ 0))
    (essentialB :
      (∀ t : Fin k, ∃ z : Fin k, B t z ≠ 0) ∧
      (∀ z : Fin k, ∃ t : Fin k, B t z ≠ 0))
    (_positiveLag : 0 < m)
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j)
    (psiB : ∀ t z, EdgePair S R t z ≃ FinitePath B m t z)
    (hA : BalancedA phiR phiS psiA)
    (hB : BalancedB phiR phiS psiB) :
    ∀ {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A m i j) (r : Fin (R j z)),
      sweep phiR alpha r =
        (let rs := (psiA i j).symm alpha
         ⟨rs.1, rs.2.1, (psiB rs.1 z) ⟨j, rs.2.2, r⟩⟩) := by
  have rowsR := first_factor_rows essentialA.1 psiA
  have rowsS := first_factor_rows essentialB.1 psiB
  intro i j z alpha r
  obtain ⟨w, ⟨s⟩⟩ := rowsS z
  rcases hp : (psiA i j).symm alpha with ⟨u, r₀, s₀⟩
  rcases hr : sweep phiR alpha r with ⟨t, r₁, beta⟩
  rcases hs : sweep phiS beta s with ⟨v, s₁, gamma⟩
  have hbal := hA alpha r s
  dsimp only at hbal
  rw [hr, hs, hp] at hbal
  have htu : t = u := congrArg Sigma.fst hbal
  subst u
  have hrest :
      (r₁, (⟨v, s₁, gamma⟩ : Σ x : Fin n, Fin (S t x) × FinitePath A m x w)) =
      (r₀, (⟨j, s₀, psiA j w ⟨z, r, s⟩⟩ :
        Σ x : Fin n, Fin (S t x) × FinitePath A m x w)) :=
    by
      have h := sigma_mk_injective hbal
      exact h
  have hnum : r₁ = r₀ := congrArg Prod.fst hrest
  subst r₀
  have hvj : v = j := congrArg (fun x => x.2.1) hrest
  subst v
  have htail : (s₁, gamma) = (s₀, psiA j w ⟨z, r, s⟩) :=
    by
      have hsecond := congrArg Prod.snd hrest
      have h := sigma_mk_injective hsecond
      exact h
  have hsnum : s₁ = s₀ := congrArg Prod.fst htail
  subst s₀
  have hgamma : gamma = psiA j w ⟨z, r, s⟩ := congrArg Prod.snd htail
  obtain ⟨x, ⟨r₂⟩⟩ := rowsR w
  rcases hrr : sweep phiR gamma r₂ with ⟨y, r₃, delta⟩
  have hfirst := balanced_first_boundary phiR phiS psiA hA rowsS gamma r₂
  dsimp only at hfirst
  rw [hrr, hgamma, (psiA j w).symm_apply_apply] at hfirst
  have hyz : y = z := congrArg Sigma.fst hfirst
  subst y
  have hrnum : r₃ = r := by
    have h := sigma_mk_injective hfirst
    exact h
  subst r₃
  have hbalB := hB beta s r₂
  dsimp only at hbalB
  rw [hs, hrr] at hbalB
  have hsr :
      (⟨j, s₁, r⟩ : EdgePair S R t z) = (psiB t z).symm beta := by
    rcases hb : (psiB t z).symm beta with ⟨a, s₂, r₄⟩
    rw [hb] at hbalB
    have hja : j = a := congrArg Sigma.fst hbalB
    subst a
    have hrestB := sigma_mk_injective hbalB
    have hsB : s₁ = s₂ := congrArg Prod.fst hrestB
    subst s₂
    have hsecondB := congrArg Prod.snd hrestB
    have hrestR := sigma_mk_injective hsecondB
    have hrB : r = r₄ := congrArg Prod.fst hrestR
    subst r₄
    rfl
  have hbeta : beta = psiB t z ⟨j, s₁, r⟩ := by
    calc
      beta = psiB t z ((psiB t z).symm beta) :=
        ((psiB t z).apply_symm_apply beta).symm
      _ = psiB t z ⟨j, s₁, r⟩ := congrArg (psiB t z) hsr.symm
  simpa only [hr, hp] using
    congrArg (fun p : FinitePath B m t z =>
      (⟨t, r₁, p⟩ : Σ a : Fin k, Fin (R i a) × FinitePath B m a z)) hbeta

/-- Presentation of the three node obligations, with the matrix itself retained. -/
def NodeControl {r : ℕ} (X : CountMat r r) (q M : ℕ) : Prop :=
  r ≤ q ∧
  (∀ i, ∃ j, X i j ≠ 0) ∧
  (∀ j, ∃ i, X i j ≠ 0) ∧
  (∀ i j, X i j ≤ M)

/-- Controls on every actual quotient and its actual factors, including arbitrary
    endpoint numberings. This is not an existential statement about other chains. -/
def ResponseControl {p : ℕ} {A : CountMat p p} {Q : Type}
    (L : IncomingLift A Q) (q M : ℕ) : Prop :=
  (∀ (d r : ℕ) (e : Quotient (L.response d) ≃ Fin r),
    NodeControl (Matrix.reindex e e (incomingResponseMatrix L d)) q M) ∧
  (∀ (d r s : ℕ)
    (e : Quotient (L.response d) ≃ Fin r)
    (f : Quotient (L.response (d + 1)) ≃ Fin s),
    let U := Matrix.reindex e f (incomingResponseU L d)
    let V := Matrix.reindex f e (incomingResponseV L d)
    Matrix.reindex e e (incomingResponseMatrix L d) = U * V ∧
    Matrix.reindex f f (incomingResponseMatrix L (d + 1)) = V * U ∧
    (∀ i j, U i j ≤ max 1 M) ∧ (∀ i j, V i j ≤ max 1 M))

/- The substantive preservation step. An outgoing lifted edge is needed: an
   arbitrary IncomingLift need not have nonzero rows. The consumer below derives
   this property from the original square graph; it is never an input assumption
   on the desired quotient matrices. -/
private theorem response_essential {p : ℕ} {A : CountMat p p} {Q : Type}
    (L : IncomingLift A Q)
    (hcol : ∀ j, ∃ i, A i j ≠ 0)
    (hout : ∀ u : Q, ∃ (a : Edge A) (v : Q)
      (hv : L.project v = a.target), (L.lift a ⟨v, hv⟩).val = u)
    (d : ℕ) :
    (∀ F, ∃ H, incomingResponseMatrix L d F H ≠ 0) ∧
    (∀ H, ∃ F, incomingResponseMatrix L d F H ≠ 0) := by
  classical
  letI (F : Quotient (L.response d)) (v : Q) :
      Finite (incomingResponseFiber L d F v) := by
    unfold incomingResponseFiber
    infer_instance
  constructor
  · intro F
    obtain ⟨a, v, hv, ha⟩ := hout (Quotient.out F)
    let H := Quotient.mk (L.response d) v
    refine ⟨H, ?_⟩
    have hrel : L.response d (Quotient.out H) v :=
      Quotient.exact (Quotient.out_eq H)
    have hcard := incoming_response_fiber_card_step L d F
      ((response_zero_and_step L).2 d hrel)
    change Nat.card (incomingResponseFiber L d F (Quotient.out H)) ≠ 0
    rw [hcard]
    apply Nat.ne_of_gt
    apply Finite.card_pos_iff.mpr
    refine ⟨⟨a, hv, ?_⟩⟩
    rw [ha]
    exact Quotient.out_eq F
  · intro H
    let v := Quotient.out H
    obtain ⟨i, hi⟩ := hcol (L.project v)
    let a : Edge A := ⟨i, L.project v, ⟨0, Nat.pos_of_ne_zero hi⟩⟩
    let F := Quotient.mk (L.response d) (L.lift a ⟨v, rfl⟩).val
    refine ⟨F, ?_⟩
    change Nat.card (incomingResponseFiber L d F v) ≠ 0
    apply Nat.ne_of_gt
    apply Finite.card_pos_iff.mpr
    exact ⟨⟨a, rfl, rfl⟩⟩

/- All cardinal bounds below are direct uses of pinned mathlib, not new
   quotient-cardinality or subtype-cardinality theorems. -/
theorem response_control {p : ℕ} {A : CountMat p p} {Q : Type}
    [Fintype Q] (L : IncomingLift A Q)
    (hcol : ∀ j, ∃ i, A i j ≠ 0)
    (hout : ∀ u : Q, ∃ (a : Edge A) (v : Q)
      (hv : L.project v = a.target), (L.lift a ⟨v, hv⟩).val = u)
    (M : ℕ) (hM : Nat.card (Edge A) ≤ M) :
    ResponseControl L (Fintype.card Q) M := by
  classical
  constructor
  · intro d r e
    letI := responseFintype L d
    have hdim : r ≤ Fintype.card Q := by
      have he := Fintype.card_congr e
      have hq := Fintype.card_le_of_surjective
        (Quotient.mk (L.response d)) (by
          intro F
          exact ⟨Quotient.out F, Quotient.out_eq F⟩)
      rw [he] at hq
      simpa only [Fintype.card_fin] using hq
    obtain ⟨hrow, hcolumn⟩ := response_essential L hcol hout d
    refine ⟨hdim, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨H, hH⟩ := hrow (e.symm i)
      exact ⟨e H, by simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using hH⟩
    · intro j
      obtain ⟨F, hF⟩ := hcolumn (e.symm j)
      exact ⟨e F, by simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using hF⟩
    · intro i j
      change Nat.card (incomingResponseFiber L d (e.symm i)
        (Quotient.out (e.symm j))) ≤ M
      exact (Finite.card_subtype_le _).trans hM
  · intro d r s e f
    letI := responseFintype L d
    letI := responseFintype L (d + 1)
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [incoming_response_matrix_factor_base L d]
      exact (Matrix.submatrix_mul_equiv (incomingResponseU L d)
        (incomingResponseV L d) e.symm f.symm e.symm).symm
    · rw [incoming_response_matrix_factor_step L d]
      exact (Matrix.submatrix_mul_equiv (incomingResponseV L d)
        (incomingResponseU L d) f.symm e.symm f.symm).symm
    · intro i j
      change Nat.card (incomingResponseFiber L d (e.symm i)
        (Quotient.out (f.symm j))) ≤ max 1 M
      exact (Finite.card_subtype_le _).trans (hM.trans (le_max_right 1 M))
    · intro i j
      change incomingResponseV L d (f.symm i) (e.symm j) ≤ max 1 M
      unfold incomingResponseV
      split_ifs
      · exact le_max_left 1 M
      · exact Nat.zero_le _

/- The existing count identities recover actual numbered lift witnesses. -/
private theorem square_left_outgoing {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    ∀ u : Edge R, ∃ (a : Edge A) (v : Edge R)
      (hv : c.squareIncomingLift.project v = a.target),
      (c.squareIncomingLift.lift a ⟨v, hv⟩).val = u := by
  classical
  intro u
  let e := Fintype.equivFin (Edge R)
  obtain ⟨j, hj⟩ := (square_graph_essential_and_projections c).2.2.2.2.1 (e u)
  let v := e.symm j
  have hcard : Nat.card {a : Edge A //
      ∃ h : a.target = v.source, (c.incomingLift a v h).val = u} ≠ 0 := by
    rw [← c.square_column_lift_count v u]
    simpa only [v, e, Equiv.apply_symm_apply] using hj
  obtain ⟨⟨a, h, ha⟩⟩ := Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
  exact ⟨a, v, h.symm, ha⟩

private theorem square_right_outgoing {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    ∀ u : Edge R, ∃ (a : Edge B.transpose) (v : Edge R)
      (hv : c.squareOutgoingLift.project v = a.target),
      (c.squareOutgoingLift.lift a ⟨v, hv⟩).val = u := by
  classical
  intro u
  let e := Fintype.equivFin (Edge R)
  obtain ⟨j, hj⟩ := (square_graph_essential_and_projections c).2.2.2.2.2 (e u)
  let v := e.symm j
  have hcard : Nat.card {b : Edge B //
      ∃ h : v.target = b.source, (c.outgoingLift v b h).val = u} ≠ 0 := by
    rw [← c.square_row_lift_count v u]
    simpa only [v, e, Equiv.apply_symm_apply] using hj
  obtain ⟨⟨b, h, hb⟩⟩ := Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
  refine ⟨⟨b.target, b.source, b.number⟩, v, h, ?_⟩
  cases b
  exact hb

/-- The same square certificate controls every node on both response legs,
    every ordinary exchange factor, and arbitrary endpoint reindexings.
    The right leg is represented on the reversed base; transpose merely swaps
    its row and column clauses and its factor order. -/
theorem square_response_controls {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    let q := Fintype.card (Edge R)
    let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
    ResponseControl c.squareIncomingLift q M ∧
    ResponseControl c.squareOutgoingLift q M ∧
    (∀ (d r : ℕ) (e : Quotient (c.squareOutgoingLift.response d) ≃ Fin r),
      NodeControl (Matrix.reindex e e
        (incomingResponseMatrix c.squareOutgoingLift d)).transpose q M) := by
  classical
  let e : Edge B.transpose ≃ Edge B := {
    toFun b := ⟨b.target, b.source, b.number⟩
    invFun b := ⟨b.target, b.source, b.number⟩
    left_inv := by intro b; cases b; rfl
    right_inv := by intro b; cases b; rfl }
  have hL := response_control c.squareIncomingLift c.essentialA.2
    (square_left_outgoing c) _ (le_max_left (Nat.card (Edge A)) (Nat.card (Edge B)))
  have hR : ResponseControl c.squareOutgoingLift (Fintype.card (Edge R))
      (max (Nat.card (Edge A)) (Nat.card (Edge B))) := by
    apply response_control c.squareOutgoingLift c.essentialB.1
      (square_right_outgoing c)
    rw [Nat.card_congr e]
    exact le_max_right _ _
  refine ⟨hL, hR, ?_⟩
  intro d r f
  obtain ⟨hdim, hrow, hcol, hentry⟩ := hR.1 d r f
  exact ⟨hdim, hcol, hrow, fun i j => hentry j i⟩

/-- Both projections and the literal original q are kept; the cardinal identity
    is bookkeeping only and carries no independent mathematical credit. -/
theorem square_order_identity {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    Fintype.card (Edge R) = ∑ i, ∑ j, R i j ∧
    max n k ≤ Fintype.card (Edge R) := by
  classical
  letI : (i : Fin n) → Fintype (Σ j : Fin k, Fin (R i j)) :=
    fun _ => Sigma.instFintype
  letI : Fintype (Σ i : Fin n, Σ j : Fin k, Fin (R i j)) :=
    Sigma.instFintype
  let e : Edge R ≃ Σ i : Fin n, Σ j : Fin k, Fin (R i j) := {
    toFun r := ⟨r.source, r.target, r.number⟩
    invFun r := ⟨r.1, r.2.1, r.2.2⟩
    left_inv := by intro r; cases r; rfl
    right_inv := by intro r; rcases r with ⟨i, j, h⟩; rfl }
  constructor
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr e
  · apply max_le
    · simpa only [Fintype.card_fin] using
        Fintype.card_le_of_surjective (fun r : Edge R => r.source)
          (square_graph_essential_and_projections c).2.2.1
    · simpa only [Fintype.card_fin] using
        Fintype.card_le_of_surjective (fun r : Edge R => r.target)
          (square_graph_essential_and_projections c).2.2.2.1

/-- The original maximum, with value zero on the additionally allowed empty
    dimension. For nonempty original dimensions this is literally max(A^m). -/
def powerMaximum {n : ℕ} (A : CountMat n n) (m : ℕ) : ℕ :=
  Finset.univ.sup (fun ij : Fin n × Fin n => (A ^ m) ij.1 ij.2)

/- Standard counting normalization, used only by the original q upper bound.
   No independent mathematical credit is assigned. -/
theorem numbered_path_count {n : ℕ} (A : CountMat n n) :
    ∀ (d : ℕ) (i j : Fin n),
      Finite (FinitePath A d i j) ∧ Nat.card (FinitePath A d i j) = (A ^ d) i j := by
  classical
  intro d
  induction d with
  | zero =>
      intro i j
      letI : Subsingleton (FinitePath A 0 i j) := ⟨by
        intro x y
        cases x
        cases y
        rfl⟩
      refine ⟨inferInstance, ?_⟩
      by_cases h : i = j
      · subst j
        simpa using Nat.card_of_subsingleton (FinitePath.nil (A := A) i)
      · letI : IsEmpty (FinitePath A 0 i j) := ⟨by
          intro x
          cases x
          exact h rfl⟩
        simp [Matrix.one_apply, h]
  | succ d ih =>
      intro i j
      letI (t : Fin n) : Finite (FinitePath A d t j) := (ih t j).1
      let e : FinitePath A (d + 1) i j ≃
          Σ t : Fin n, Fin (A i t) × FinitePath A d t j := {
        toFun p := match p with | .cons a tail => ⟨_, a, tail⟩
        invFun p := .cons p.2.1 p.2.2
        left_inv := by intro p; cases p; rfl
        right_inv := by intro p; rcases p with ⟨t, a, tail⟩; rfl }
      letI : Finite (FinitePath A (d + 1) i j) := Finite.of_equiv _ e.symm
      refine ⟨inferInstance, ?_⟩
      rw [Nat.card_congr e, Nat.card_sigma, pow_succ', Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.card_prod, Nat.card_fin, (ih t j).2]

/-- Every entry of the first factor is bounded by the original power maximum.
    This extracts the existing proof-local bound consumed by square_order_upper. -/
theorem factor_entry_upper {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (hB : ∀ j : Fin k, ∃ l : Fin k, B j l ≠ 0)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j)
    (psiB : ∀ t z, EdgePair S R t z ≃ FinitePath B m t z) :
    ∀ (i : Fin n) (j : Fin k), R i j ≤ powerMaximum A m := by
  classical
  intro i j
  obtain ⟨l, ⟨snum⟩⟩ := first_factor_rows hB psiB j
  let f : Fin (R i j) → FinitePath A m i l :=
    fun r => psiA i l ⟨j, r, snum⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hh := (psiA i l).injective hxy
    have hp : (x, snum) = (y, snum) := by
      have h := sigma_mk_injective hh
      exact h
    exact congrArg Prod.fst hp
  letI : Finite (FinitePath A m i l) := (numbered_path_count A m i l).1
  have hcount := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, (numbered_path_count A m i l).2] at hcount
  exact hcount.trans (Finset.le_sup (f := fun ij : Fin n × Fin n =>
    (A ^ m) ij.1 ij.2) (Finset.mem_univ (i, l)))

/- The consumed row-witness helper supplies an actual S edge directly from
   psiB and essential B; no swapped compatibility certificate is needed. -/
theorem square_order_upper {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    Fintype.card (Edge R) ≤ n * k * powerMaximum A m := by
  classical
  have hentry := factor_entry_upper c.essentialB.1 c.psiA c.psiB
  rw [(square_order_identity c).1]
  calc
    (∑ i, ∑ j, R i j) ≤ ∑ _i : Fin n, ∑ _j : Fin k, powerMaximum A m := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hentry i j
    _ = n * k * powerMaximum A m := by simp [Nat.mul_assoc]

/-- The public diamond's actual existential factor is bounded using a nonzero
    column of the intersection matrix and the controlled left product. -/
theorem square_diamond_controls {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (c : CompatibleCertificate A B R S m) :
    letI := responseFintype c.squareIncomingLift 1
    letI := responseFintype c.squareOutgoingLift 1
    let q := Fintype.card (Edge R)
    let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
    let IL := FirstResponseDiamond.columnMembership c.firstLeftClass
    let IJ := FirstResponseDiamond.rowMembership c.firstRightClass
    let SL := FirstResponseDiamond.columnSelector c.firstLeftRep
    let SJ := FirstResponseDiamond.rowSelector c.firstRightRep
    ∃ D : CountMat
        (Fintype.card (Quotient (c.squareOutgoingLift.response 1)))
        (Fintype.card (Quotient (c.squareIncomingLift.response 1))),
      IL * c.squareMatrix * SL = (IL * IJ) * D ∧
      SJ * c.squareMatrix * IJ = D * (IL * IJ) ∧
      (∀ f h, (IL * IJ) f h ≤ max q M) ∧
      (∀ h f, D h f ≤ max q M) := by
  classical
  letI := responseFintype c.squareIncomingLift 1
  letI := responseFintype c.squareOutgoingLift 1
  dsimp only
  let e := Fintype.equivFin (Edge R)
  let eL := Fintype.equivFin (Quotient (c.squareIncomingLift.response 1))
  let eR := Fintype.equivFin (Quotient (c.squareOutgoingLift.response 1))
  have hleftRep (f) : c.firstLeftClass (c.firstLeftRep f) = f := by
    simp [firstLeftClass, firstLeftRep]
  have hrightRep (h) : c.firstRightClass (c.firstRightRep h) = h := by
    simp [firstRightClass, firstRightRep]
  have hcolumns (u v) (h : c.firstLeftClass u = c.firstLeftClass v)
      (i) : c.squareMatrix i u = c.squareMatrix i v := by
    have hq : Quotient.mk (c.squareIncomingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareIncomingLift.response 1) (e.symm v) := eL.injective h
    simpa [e] using c.square_first_column_invariance
      (Quotient.exact hq) (e.symm i)
  have hrows (u v) (h : c.firstRightClass u = c.firstRightClass v)
      (i) : c.squareMatrix u i = c.squareMatrix v i := by
    have hq : Quotient.mk (c.squareOutgoingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareOutgoingLift.response 1) (e.symm v) := eR.injective h
    simpa [e] using c.square_first_row_invariance
      (Quotient.exact hq) (e.symm i)
  obtain ⟨D, hcol, hrow, _⟩ := FirstResponseDiamond.first_response_diamond
    c.squareMatrix c.firstLeftClass c.firstRightClass c.firstLeftRep c.firstRightRep
    hleftRep hrightRep hcolumns hrows
  let P := FirstResponseDiamond.columnMembership c.firstLeftClass *
    FirstResponseDiamond.rowMembership c.firstRightClass
  have hnode := (square_response_controls c).1.1 1 _ (responseIndex c.squareIncomingLift 1)
  have hentry (f g) :
      (FirstResponseDiamond.columnMembership c.firstLeftClass * c.squareMatrix *
        FirstResponseDiamond.columnSelector c.firstLeftRep) f g ≤
      max (Nat.card (Edge A)) (Nat.card (Edge B)) := by
    rw [← c.square_left_first_matrix f g]
    exact hnode.2.2.2 f g
  refine ⟨D, hcol, hrow, ?_, ?_⟩
  · intro f h
    apply le_trans _ (le_max_left _ _)
    rw [Matrix.mul_apply]
    calc
      _ ≤ ∑ _u : Fin (Fintype.card (Edge R)), (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro u _
        simp only [FirstResponseDiamond.columnMembership, FirstResponseDiamond.rowMembership]
        split_ifs <;> simp
      _ = Fintype.card (Edge R) := by simp
  · intro h f
    let u := c.firstRightRep h
    let g := c.firstLeftClass u
    have hpositive : 1 ≤ P g h := by
      have hone :
          FirstResponseDiamond.columnMembership c.firstLeftClass g u *
            FirstResponseDiamond.rowMembership c.firstRightClass u h = 1 := by
        simp [FirstResponseDiamond.columnMembership, FirstResponseDiamond.rowMembership,
          g, u, hrightRep]
      change 1 ≤ ∑ v, FirstResponseDiamond.columnMembership c.firstLeftClass g v *
        FirstResponseDiamond.rowMembership c.firstRightClass v h
      exact hone.symm.le.trans
        (Finset.single_le_sum
          (f := fun v : Fin (Fintype.card (Edge R)) =>
            FirstResponseDiamond.columnMembership c.firstLeftClass g v *
              FirstResponseDiamond.rowMembership c.firstRightClass v h)
          (fun v _ => Nat.zero_le _) (Finset.mem_univ u))
    calc
      D h f ≤ P g h * D h f := by
        simpa only [one_mul] using Nat.mul_le_mul_right (D h f) hpositive
      _ ≤ (P * D) g f := by
        change P g h * D h f ≤ ∑ j, P g j * D j f
        exact Finset.single_le_sum (f := fun j => P g j * D j f)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ h)
      _ = (FirstResponseDiamond.columnMembership c.firstLeftClass * c.squareMatrix *
            FirstResponseDiamond.columnSelector c.firstLeftRep) g f := by
        exact (congrArg (fun X => X g f) hcol).symm
      _ ≤ max (Nat.card (Edge A)) (Nat.card (Edge B)) := hentry g f
      _ ≤ max (Fintype.card (Edge R))
          (max (Nat.card (Edge A)) (Nat.card (Edge B))) := le_max_right _ _

/-- Original balanced-input consumer: the original maps construct c internally.
    No chain, quotient essentiality or size bound is an input assumption. -/
theorem originalBalancedResponseControls {n k m : ℕ}
    (A : CountMat n n) (B : CountMat k k) (R : CountMat n k) (S : CountMat k n)
    (essentialA : (∀ i, ∃ j, A i j ≠ 0) ∧ (∀ j, ∃ i, A i j ≠ 0))
    (essentialB : (∀ i, ∃ j, B i j ≠ 0) ∧ (∀ j, ∃ i, B i j ≠ 0))
    (positiveLag : 0 < m)
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j)
    (psiB : ∀ t z, EdgePair S R t z ≃ FinitePath B m t z)
    (hA : BalancedA phiR phiS psiA) (hB : BalancedB phiR phiS psiB) :
    let c : CompatibleCertificate A B R S m := {
      positiveLag := positiveLag, essentialA := essentialA, essentialB := essentialB
      phi := phiR, psiA := psiA, psiB := psiB
      compatible := balanced_sweep A B R S essentialA essentialB positiveLag
        phiR phiS psiA psiB hA hB }
    letI := responseFintype c.squareIncomingLift 1
    letI := responseFintype c.squareOutgoingLift 1
    let q := Fintype.card (Edge R)
    let M := max (Nat.card (Edge A)) (Nat.card (Edge B))
    q = ∑ i, ∑ j, R i j ∧ max n k ≤ q ∧
    q ≤ n * k * powerMaximum A m ∧
    ResponseControl c.squareIncomingLift q M ∧ ResponseControl c.squareOutgoingLift q M ∧
    (∀ (d r : ℕ) (e : Quotient (c.squareOutgoingLift.response d) ≃ Fin r),
      NodeControl (Matrix.reindex e e
        (incomingResponseMatrix c.squareOutgoingLift d)).transpose q M) := by
  classical
  dsimp only
  let c : CompatibleCertificate A B R S m := {
    positiveLag := positiveLag, essentialA := essentialA, essentialB := essentialB
    phi := phiR, psiA := psiA, psiB := psiB
    compatible := balanced_sweep A B R S essentialA essentialB positiveLag
      phiR phiS psiA psiB hA hB }
  have hupper := square_order_upper c
  obtain ⟨hq, hn⟩ := square_order_identity c
  obtain ⟨hL, hR, hRT⟩ := square_response_controls c
  exact ⟨hq, hn, hupper, hL, hR, hRT⟩

end D5.S3.ConceptDynamics.Coding.OriginalResponseControls
