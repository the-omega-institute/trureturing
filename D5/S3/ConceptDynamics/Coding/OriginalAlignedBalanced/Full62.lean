/- GID: D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/Full62
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/Full62
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full original 6.2 on actual numbered square paths, bilateral conjugacy and exact signed windows. -/
import D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
import D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion

/- Export the exact frozen path lemmas as namespace aliases.  Lean's export
   creates no declaration and preserves their private kernel names and proofs. -/
namespace D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
run_cmd do
  let supplier := Lean.Name.num
    `_private.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound 0
  let owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
  for short in [`squareIncomingLift_path, `squareOutgoingLift_path] do
    let kernel := supplier ++ owner ++ short
    unless (← Lean.getEnv).contains kernel do
      throwError "missing original kernel supplier {kernel}"
    modify fun s => { s with env := Lean.addAlias s.env (owner ++ short) kernel }
end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate

namespace D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.Full62

open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport

def Essential {n : ℕ} (A : CountMat n n) : Prop :=
  (∀ i, ∃ j, A i j ≠ 0) ∧ (∀ j, ∃ i, A i j ≠ 0)

abbrev Actual {n : ℕ} {A : CountMat n n} {Q : Type} [Fintype Q]
    (L : IncomingLift A Q) (u v : Fin (Fintype.card Q)) :=
  {a : Edge A // ∃ h : L.project ((Fintype.equivFin Q).symm v) = a.target,
    (L.lift a ⟨(Fintype.equivFin Q).symm v, h⟩).val = (Fintype.equivFin Q).symm u}

def Model {n : ℕ} {A : CountMat n n} {Q : Type} [Fintype Q]
    (L : IncomingLift A Q) : CountMat (Fintype.card Q) (Fintype.card Q) :=
  fun u v => Fintype.card (Actual L u v)

def modelRead {n : ℕ} {A : CountMat n n} {Q : Type} [Fintype Q]
    (L : IncomingLift A Q) (a : Edge (Model L)) : Edge A :=
  ((Fintype.equivFin (Actual L a.source a.target)).symm a.number).val

structure EdgeIso {n k : ℕ} (A : CountMat n n) (B : CountMat k k) where
  vertices : Fin n ≃ Fin k
  edges : Edge A ≃ Edge B
  source : ∀ a, (edges a).source = vertices a.source
  target : ∀ a, (edges a).target = vertices a.target

def EdgeIso.path {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    (e : EdgeIso A B) (x : Path A) : Path B :=
  ⟨fun i => e.edges (x.val i), fun i => by rw [e.target, e.source, x.property]⟩

def EdgeIso.symm {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    (e : EdgeIso A B) : EdgeIso B A where
  vertices := e.vertices.symm
  edges := e.edges.symm
  source := by
    intro a
    apply e.vertices.injective
    simpa only [Equiv.apply_symm_apply] using (e.source (e.edges.symm a)).symm
  target := by
    intro a
    apply e.vertices.injective
    simpa only [Equiv.apply_symm_apply] using (e.target (e.edges.symm a)).symm

def EdgeIso.homeomorph {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    (e : EdgeIso A B) : Path A ≃ₜ Path B where
  toFun := e.path
  invFun := e.symm.path
  left_inv := by intro x; apply Subtype.ext; funext i; exact e.edges.symm_apply_apply _
  right_inv := by intro x; apply Subtype.ext; funext i; exact e.edges.apply_symm_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    exact (continuous_of_discreteTopology (f := e.edges)).comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    exact (continuous_of_discreteTopology (f := e.edges.symm)).comp
      ((continuous_apply i).comp continuous_subtype_val)

theorem EdgeIso.essential {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    (e : EdgeIso A B) (h : Essential A) : Essential B := by
  constructor
  · intro i
    obtain ⟨j, hj⟩ := h.1 (e.vertices.symm i)
    let a : Edge A := ⟨e.vertices.symm i, j, ⟨0, Nat.pos_of_ne_zero hj⟩⟩
    have ha : 0 < B (e.edges a).source (e.edges a).target :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (e.edges a).number.isLt
    refine ⟨(e.edges a).target, ?_⟩
    rw [e.source, Equiv.apply_symm_apply] at ha
    omega
  · intro j
    obtain ⟨i, hi⟩ := h.2 (e.vertices.symm j)
    let a : Edge A := ⟨i, e.vertices.symm j, ⟨0, Nat.pos_of_ne_zero hi⟩⟩
    have ha : 0 < B (e.edges a).source (e.edges a).target :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (e.edges a).number.isLt
    refine ⟨(e.edges a).source, ?_⟩
    rw [e.target, Equiv.apply_symm_apply] at ha
    omega

@[simp] theorem reverse_reverse {p : ℕ} {M : CountMat p p} (a : Edge M) :
    @reverseEdge p M.transpose (@reverseEdge p M a) = a := by cases a; rfl

def reversal {n : ℕ} (A : CountMat n n) : Path A ≃ₜ Path A.transpose where
  toFun := reversePath
  invFun := reversePath
  left_inv := by
    intro x; apply Subtype.ext; funext i
    change reverseEdge (reverseEdge (x.val (-(-i-1)-1))) = x.val i
    simp only [show -(-i-1)-1 = i by omega]; rfl
  right_inv := by
    intro x; apply Subtype.ext; funext i
    change reverseEdge (reverseEdge (x.val (-(-i-1)-1))) = x.val i
    simp only [show -(-i-1)-1 = i by omega]; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    exact (continuous_of_discreteTopology (f := reverseEdge)).comp
      ((continuous_apply (-i-1)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    exact (continuous_of_discreteTopology (f := reverseEdge)).comp
      ((continuous_apply (-i-1)).comp continuous_subtype_val)

def WindowEq {n : ℕ} {A : CountMat n n} (x y : Path A) (l r : ℤ) : Prop :=
  ∀ i : ℤ, l ≤ i → i ≤ r → x.val i = y.val i

def Escapes {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    (f : Path A → Path B) (p q : ℕ) : Set (Path A × Path A) :=
  {xy | WindowEq xy.1 xy.2 (-(p:ℤ)) p ∧
    ¬ WindowEq (f xy.1) (f xy.2) (-(q:ℤ)) q}

def oneSided {n c : ℕ} (hn : 0 < n) {A : CountMat n n}
    {C : CountMat c c} {Q : Type} [Fintype Q] (L : IncomingLift A Q)
    (e : EdgeIso C (Model L)) (hA : Essential A) (hC : Essential C)
    (d : ℕ) (hd : Forgets L d) :
    ∃ P : Path C ≃ₜ Path A,
      (∀ x i, (P x).val i = modelRead L (e.edges (x.val i))) ∧
      (∀ x, P (shift C x) = shift A (P x)) ∧
      (∀ x y i, (∀ j : ℕ, j ≤ d → x.val (i+j) = y.val (i+j)) →
        (P.symm x).val i = (P.symm y).val i) := by
  have hm := e.essential hC
  obtain ⟨_, _, _, _, pi, hread, hpi, hshift, rest⟩ :=
    incoming_lift_ambiguity_criterion hn A L hA hm
  obtain ⟨inv, hi, hl, hr, hs, hw⟩ := rest.2.1 d hd
  let H : Path (Model L) ≃ₜ Path A :=
    { toFun := pi, invFun := inv, left_inv := hl, right_inv := hr,
      continuous_toFun := hpi, continuous_invFun := hi }
  let P := e.homeomorph.trans H
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x i
    exact hread (e.path x) i
  · intro x
    exact hshift (e.path x)
  · intro x y i h
    have hwin := hw x y i h
    exact congrArg e.edges.symm hwin

structure Bilateral {n k c : ℕ} (A : CountMat n n) (B : CountMat k k)
    (C : CountMat c c) (dL dR : ℕ) (a : Edge C → Edge A)
    (b : Edge C → Edge B) where
  PA : Path C ≃ₜ Path A
  PB : Path C ≃ₜ Path B
  left_read : ∀ x i, (PA x).val i = a (x.val i)
  right_read : ∀ x i, (PB x).val i = b (x.val i)
  shiftA : ∀ x, PA (shift C x) = shift A (PA x)
  shiftB : ∀ x, PB (shift C x) = shift B (PB x)
  future : ∀ x y i, WindowEq x y i (i+dL) →
    (PA.symm x).val i = (PA.symm y).val i
  past : ∀ x y i, WindowEq x y (i-dR) i →
    (PB.symm x).val i = (PB.symm y).val i

def Bilateral.h {n k c : ℕ} {A : CountMat n n} {B : CountMat k k}
    {C : CountMat c c} {dL dR : ℕ} {a : Edge C → Edge A} {b : Edge C → Edge B}
    (D : Bilateral A B C dL dR a b) : Path A ≃ₜ Path B := D.PA.symm.trans D.PB

theorem Bilateral.observations {n k c : ℕ} {A : CountMat n n} {B : CountMat k k}
    {C : CountMat c c} {dL dR : ℕ} {a : Edge C → Edge A} {b : Edge C → Edge B}
    (D : Bilateral A B C dL dR a b) :
    (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
    (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
    (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
    (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
      WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
    (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
      WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
    (∀ N, Escapes D.h (N+dL) N = ∅) ∧
    (∀ N, Escapes D.h.symm (N+dR) N = ∅) := by
  have hf : ∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i := by
    intro x y i h
    rw [show (D.h x).val i = b ((D.PA.symm x).val i) from D.right_read _ i,
      show (D.h y).val i = b ((D.PA.symm y).val i) from D.right_read _ i]
    rw [D.future x y i h]
  have hp : ∀ x y i, WindowEq x y (i-dR) i →
      (D.h.symm x).val i = (D.h.symm y).val i := by
    intro x y i h
    rw [show (D.h.symm x).val i = a ((D.PB.symm x).val i) from D.left_read _ i,
      show (D.h.symm y).val i = a ((D.PB.symm y).val i) from D.left_read _ i]
    rw [D.past x y i h]
  have hNf : ∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
      WindowEq (D.h x) (D.h y) (-(N:ℤ)) N := by
    intro N x y h i hi hj
    apply hf x y i
    intro t ht hu
    exact h t (by omega) (by omega)
  have hNp : ∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
      WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N := by
    intro N x y h i hi hj
    apply hp x y i
    intro t ht hu
    exact h t (by omega) (by omega)
  refine ⟨?_, hf, hp, hNf, hNp, ?_, ?_⟩
  · intro x
    have hPA : D.PA.symm (shift A x) = shift C (D.PA.symm x) := by
      apply D.PA.injective
      rw [D.PA.apply_symm_apply, D.shiftA, D.PA.apply_symm_apply]
    change D.PB (D.PA.symm (shift A x)) = shift B (D.PB (D.PA.symm x))
    rw [hPA, D.shiftB]
  · intro N
    apply Set.ext
    rintro ⟨x,y⟩
    change _ ↔ False
    constructor
    · rintro ⟨h, hn⟩
      apply hn
      apply hNf N x y
      intro i hi hj
      exact h i (by push_cast; omega) (by push_cast; omega)
    · exact False.elim
  · intro N
    apply Set.ext
    rintro ⟨x,y⟩
    change _ ↔ False
    constructor
    · rintro ⟨h, hn⟩
      apply hn
      apply hNp N x y
      intro i hi hj
      exact h i (by push_cast; omega) (by push_cast; omega)
    · exact False.elim

theorem general_bilateral {n k c : ℕ} (hn : 0 < n) (hk : 0 < k)
    {A : CountMat n n} {B : CountMat k k} {C : CountMat c c}
    {Q T : Type} [Fintype Q] [Fintype T]
    (L : IncomingLift A Q) (K : IncomingLift B.transpose T)
    (eL : EdgeIso C (Model L)) (eR : EdgeIso C.transpose (Model K))
    (hA : Essential A) (hB : Essential B) (hC : Essential C)
    (dL dR : ℕ) (hdL : Forgets L dL) (hdR : Forgets K dR) :
    Nonempty (Bilateral A B C dL dR
      (fun a => modelRead L (eL.edges a))
      (fun a => reverseEdge (modelRead K (eR.edges (reverseEdge a))))) := by
  obtain ⟨PA, hPA, hsA, hwA⟩ := oneSided hn L eL hA hC dL hdL
  have hBt : Essential B.transpose := ⟨hB.2, hB.1⟩
  have hCt : Essential C.transpose := ⟨hC.2, hC.1⟩
  obtain ⟨PR, hPR, hsR, hwR⟩ := oneSided hk K eR hBt hCt dR hdR
  let PB := (reversal C).trans (PR.trans (reversal B).symm)
  have hb (x : Path C) (i : ℤ) :
      (PB x).val i = reverseEdge (modelRead K (eR.edges (reverseEdge (x.val i)))) := by
    change reverseEdge ((PR (reversePath x)).val (-i-1)) = _
    rw [hPR]
    change reverseEdge (modelRead K (eR.edges (reverseEdge (x.val (-(-i-1)-1))))) = _
    rw [show -(-i-1)-1 = i by omega]
  refine ⟨⟨PA, PB, hPA, hb, hsA, ?_, ?_, ?_⟩⟩
  · intro x
    apply Subtype.ext; funext i
    rw [hb, show (shift B (PB x)).val i = (PB x).val (i+1) from rfl, hb]
    rfl
  · intro x y i h
    apply hwA x y i
    intro j hj
    exact h (i+j) (by omega) (by omega)
  · intro x y i h
    change reverseEdge ((PR.symm (reversePath x)).val (-i-1)) =
      reverseEdge ((PR.symm (reversePath y)).val (-i-1))
    apply congrArg reverseEdge
    apply hwR (reversePath x) (reversePath y) (-i-1)
    intro j hj
    change reverseEdge (x.val (-(-i-1+(j:ℤ))-1)) =
      reverseEdge (y.val (-(-i-1+(j:ℤ))-1))
    apply congrArg reverseEdge
    exact h _ (by omega) (by omega)

def fiberIso {q : ℕ} {C D : CountMat q q}
    (f : ∀ u v, Fin (C u v) ≃ Fin (D u v)) : EdgeIso C D where
  vertices := Equiv.refl _
  edges := {
    toFun := fun a => ⟨a.source, a.target, f a.source a.target a.number⟩
    invFun := fun a => ⟨a.source, a.target, (f a.source a.target).symm a.number⟩
    left_inv := by intro a; cases a; simp only [Equiv.symm_apply_apply]
    right_inv := by intro a; cases a; simp only [Equiv.apply_symm_apply] }
  source := fun _ => rfl
  target := fun _ => rfl

variable {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
  {R : CountMat n k} {S : CountMat k n}

def squareAt (c : CompatibleCertificate A B R S m) (a : Edge c.squareMatrix) : Square c :=
  (c.squareFiberEquiv a.source a.target a.number).val

/-- Eliminate whole-edge and endpoint equalities before reconstruction.
    The equality motive includes the dependent endpoint proof accepted by phi. -/
theorem outgoing_transport (c : CompatibleCertificate A B R S m) (sq : Square c)
    (r : Edge R) (b : Edge B) (hr : r = sq.initialR) (hb : b = sq.rightB)
    (h : r.target = b.source) : c.outgoingSquare r b h = sq := by
  subst r
  subst b
  rcases sq with ⟨i,z,⟨j,a,rn⟩,⟨t,r0,bn⟩,commutes⟩
  apply (c.squareCoordinates).injective
  change (⟨i,z,(c.phi i z).symm ⟨t,r0,bn⟩⟩ :
    Σ i : Fin n, Σ z : Fin k, EdgePair A R i z) = ⟨i,z,⟨j,a,rn⟩⟩
  exact congrArg (fun input : EdgePair A R i z =>
    (⟨i,z,input⟩ : Σ i : Fin n, Σ z : Fin k, EdgePair A R i z))
      ((congrArg (c.phi i z).symm commutes).symm.trans
        ((c.phi i z).symm_apply_apply ⟨j,a,rn⟩))

def leftFiber (c : CompatibleCertificate A B R S m)
    (u v : Fin (Fintype.card (Edge R))) :
    {sq : Square c // (Fintype.equivFin (Edge R)) sq.initialR = u ∧
      (Fintype.equivFin (Edge R)) sq.terminalR = v} ≃ Actual c.squareIncomingLift u v := by
  let e := Fintype.equivFin (Edge R)
  refine {
    toFun := fun s => ⟨s.val.leftA, ?_⟩
    invFun := fun a => ⟨c.incomingSquare a.val (e.symm v) a.property.choose.symm, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have ht : e.symm v = s.val.terminalR := (congrArg e.symm s.property.2).symm.trans (e.symm_apply_apply _)
    have hs : e.symm u = s.val.initialR := (congrArg e.symm s.property.1).symm.trans (e.symm_apply_apply _)
    have hp : (e.symm v).source = s.val.leftA.target := by rw [ht]; rfl
    refine ⟨hp, ?_⟩
    change (c.incomingSquare s.val.leftA (e.symm v) hp.symm).initialR = e.symm u
    have hsq0 : c.incomingSquare s.val.leftA s.val.terminalR rfl = s.val := by
      apply (c.squareCoordinates).injective
      rcases s.val with ⟨i,z,⟨j,a,rn⟩,⟨t,r0,bn⟩,commutes⟩
      rfl
    have hsq : c.incomingSquare s.val.leftA (e.symm v) hp.symm = s.val := by
      have hr : (⟨e.symm v, hp.symm⟩ :
          {r : Edge R // s.val.leftA.target = r.source}) =
          ⟨s.val.terminalR, rfl⟩ := Subtype.ext ht
      exact (congrArg (fun r : {r : Edge R // s.val.leftA.target = r.source} =>
        c.incomingSquare s.val.leftA r.val r.property) hr).trans hsq0
    exact (congrArg Square.initialR hsq).trans hs.symm
  · constructor
    · have h := a.property.choose_spec
      change (c.incomingSquare a.val (e.symm v) _).initialR = e.symm u at h
      rw [h, e.apply_symm_apply]
    · exact (congrArg e ((square_lifts_left_forgetting c).1 a.val (e.symm v)
        a.property.choose.symm)).trans (e.apply_symm_apply v)
  · intro s
    apply Subtype.ext
    have ht : e.symm v = s.val.terminalR := (congrArg e.symm s.property.2).symm.trans (e.symm_apply_apply _)
    dsimp only
    have hsq0 : c.incomingSquare s.val.leftA s.val.terminalR rfl = s.val := by
      apply (c.squareCoordinates).injective
      rcases s.val with ⟨i,z,⟨j,a,rn⟩,⟨t,r0,bn⟩,commutes⟩
      rfl
    have hp : s.val.leftA.target = (e.symm v).source := by rw [ht]; rfl
    have hr : (⟨e.symm v, hp⟩ :
        {r : Edge R // s.val.leftA.target = r.source}) =
        ⟨s.val.terminalR, rfl⟩ := Subtype.ext ht
    exact (congrArg (fun r : {r : Edge R // s.val.leftA.target = r.source} =>
      c.incomingSquare s.val.leftA r.val r.property) hr).trans hsq0
  · intro a
    apply Subtype.ext
    rcases a with ⟨⟨i,j,h⟩,ha⟩
    rfl

def rightFiber (c : CompatibleCertificate A B R S m)
    (u v : Fin (Fintype.card (Edge R))) :
    {sq : Square c // (Fintype.equivFin (Edge R)) sq.initialR = v ∧
      (Fintype.equivFin (Edge R)) sq.terminalR = u} ≃ Actual c.squareOutgoingLift u v := by
  let e := Fintype.equivFin (Edge R)
  refine {
    toFun := fun s => ⟨reverseEdge s.val.rightB, ?_⟩
    invFun := fun a => ⟨c.outgoingSquare (e.symm v) (reverseEdge a.val) a.property.choose, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have ht : e.symm u = s.val.terminalR := (congrArg e.symm s.property.2).symm.trans (e.symm_apply_apply _)
    have hs : e.symm v = s.val.initialR := (congrArg e.symm s.property.1).symm.trans (e.symm_apply_apply _)
    refine ⟨?_, ?_⟩
    · rw [hs]; rfl
    · change (c.outgoingSquare (e.symm v) s.val.rightB _).terminalR = e.symm u
      simpa only [hs,ht] using congrArg Square.terminalR (outgoing_transport c s.val s.val.initialR s.val.rightB rfl rfl _)
  · constructor
    · exact (congrArg e ((square_lifts_left_forgetting c).2.1 (e.symm v)
        (reverseEdge a.val) a.property.choose)).trans (e.apply_symm_apply v)
    · have h := a.property.choose_spec
      change (c.outgoingSquare (e.symm v) (reverseEdge a.val) _).terminalR = e.symm u at h
      rw [h, e.apply_symm_apply]
  · intro s
    apply Subtype.ext
    have hs : e.symm v = s.val.initialR := (congrArg e.symm s.property.1).symm.trans (e.symm_apply_apply _)
    dsimp only
    exact outgoing_transport c s.val (e.symm v)
      (@reverseEdge k B.transpose (@reverseEdge k B s.val.rightB)) hs
      (@reverse_reverse k B s.val.rightB) _
  · intro a
    apply Subtype.ext
    have hright (r : Edge R) (b : Edge B) (h : r.target = b.source) :
        (c.outgoingSquare r b h).rightB = b := by
      rcases r with ⟨i,z,num⟩
      rcases b with ⟨u,t,edge⟩
      cases h
      rfl
    exact congrArg reverseEdge (hright (e.symm v) (reverseEdge a.val) a.property.choose)

def leftIso (c : CompatibleCertificate A B R S m) :
    EdgeIso c.squareMatrix (Model c.squareIncomingLift) :=
  fiberIso fun u v => ((c.squareFiberEquiv u v).trans (leftFiber c u v)).trans
    (Fintype.equivFin (Actual c.squareIncomingLift u v))

def rightIso (c : CompatibleCertificate A B R S m) :
    EdgeIso c.squareMatrix.transpose (Model c.squareOutgoingLift) :=
  fiberIso fun u v => ((c.squareFiberEquiv v u).trans (rightFiber c u v)).trans
    (Fintype.equivFin (Actual c.squareOutgoingLift u v))

theorem left_read (c : CompatibleCertificate A B R S m) (a : Edge c.squareMatrix) :
    modelRead c.squareIncomingLift ((leftIso c).edges a) = (squareAt c a).leftA := by
  exact congrArg Subtype.val
    ((Fintype.equivFin (Actual c.squareIncomingLift a.source a.target)).symm_apply_apply
      ((leftFiber c a.source a.target) (c.squareFiberEquiv a.source a.target a.number)))

theorem right_read (c : CompatibleCertificate A B R S m) (a : Edge c.squareMatrix) :
    reverseEdge (modelRead c.squareOutgoingLift ((rightIso c).edges (reverseEdge a))) =
      (squareAt c a).rightB := by
  exact (congrArg (fun t : Actual c.squareOutgoingLift a.target a.source =>
      @reverseEdge k B.transpose t.val)
    ((Fintype.equivFin (Actual c.squareOutgoingLift a.target a.source)).symm_apply_apply
      ((rightFiber c a.target a.source)
        (c.squareFiberEquiv a.source a.target a.number)))).trans
          (@reverse_reverse k B (squareAt c a).rightB)

theorem response_forgets {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) (h : L.response d = Setoid.ker L.project) :
    Forgets L d := by
  intro i j path u v
  have huv : L.response d u.val v.val := by
    rw [h]; exact u.property.trans v.property.symm
  have hobs : L.responseReadout d u.val = L.responseReadout d v.val := huv
  have hr := congrArg (fun o => o.2 i j path) hobs
  simp only [IncomingLift.responseReadout, dif_pos u.property, dif_pos v.property,
    Option.some.injEq] at hr
  exact Subtype.ext hr

theorem certificate_bilateral (hn : 0 < n) (hk : 0 < k)
    (c : CompatibleCertificate A B R S m) (dL dR : ℕ)
    (hdL : Forgets c.squareIncomingLift dL) (hdR : Forgets c.squareOutgoingLift dR) :
    Nonempty (Bilateral A B c.squareMatrix dL dR
      (fun a => (squareAt c a).leftA) (fun a => (squareAt c a).rightB)) := by
  obtain ⟨D⟩ := general_bilateral hn hk c.squareIncomingLift c.squareOutgoingLift
    (leftIso c) (rightIso c) c.essentialA c.essentialB
    (square_graph_essential_and_projections c).2.2.2.2 dL dR hdL hdR
  refine ⟨⟨D.PA,D.PB,?_,?_,D.shiftA,D.shiftB,D.future,D.past⟩⟩
  · intro x i
    exact (D.left_read x i).trans (left_read c (x.val i))
  · intro x i
    exact (D.right_read x i).trans (right_read c (x.val i))

theorem psiA_lift (c : CompatibleCertificate A B R S m)
    {i j : Fin n} (alpha : FinitePath A m i j)
    (r : {r : Edge R // r.source = j}) :
    (c.squareIncomingLift.liftPath alpha r).val =
      (let rs := (c.psiA i j).symm alpha; (⟨i,rs.1,rs.2.1⟩ : Edge R)) := by
  rcases r with ⟨⟨j',z,num⟩,h⟩
  cases h
  exact (c.squareIncomingLift_path alpha num).trans
    ((square_lifts_left_forgetting c).2.2 alpha num)

theorem psiB_lift (c : CompatibleCertificate A B R S m)
    {z t : Fin k} (beta : FinitePath B.transpose m z t)
    (r : {r : Edge R // r.target = t}) :
    (c.squareOutgoingLift.liftPath beta r).val =
      (let sr := (c.psiB t z).symm (reverseFinitePath beta)
       (⟨sr.1,z,sr.2.2⟩ : Edge R)) := by
  rcases r with ⟨⟨i,t',num⟩,h⟩
  cases h
  exact (c.squareOutgoingLift_path beta num).trans
    (square_lifts_right_forgetting c num (reverseFinitePath beta))

def state (c : CompatibleCertificate A B R S m) (x : Path c.squareMatrix) (i : ℤ) : Edge R :=
  (Fintype.equivFin (Edge R)).symm (x.val i).source

theorem square_states (c : CompatibleCertificate A B R S m)
    (x : Path c.squareMatrix) (i : ℤ) :
    (squareAt c (x.val i)).initialR = state c x i ∧
    (squareAt c (x.val i)).terminalR = state c x (i+1) := by
  let e := Fintype.equivFin (Edge R)
  have h := (c.squareFiberEquiv (x.val i).source (x.val i).target (x.val i).number).property
  constructor
  · apply e.injective
    exact h.1.trans (e.apply_symm_apply _).symm
  · apply e.injective
    exact h.2.trans ((x.property i).trans (e.apply_symm_apply _).symm)

theorem incoming_square_step (c : CompatibleCertificate A B R S m) (sq : Square c)
    (a : Edge A) (r : Edge R) (h : r.source = a.target)
    (ha : a = sq.leftA) (hr : r = sq.terminalR) :
    (c.squareIncomingLift.lift a ⟨r,h⟩).val = sq.initialR := by
  subst a
  subst r
  exact congrArg Square.initialR ((c.squareCoordinates).symm_apply_apply sq)

theorem outgoing_square_step (c : CompatibleCertificate A B R S m) (sq : Square c)
    (r : Edge R) (b : Edge B) (h : r.target = b.source)
    (hr : r = sq.initialR) (hb : b = sq.rightB) :
    (c.outgoingSquare r b h).terminalR = sq.terminalR := by
  subst r
  subst b
  exact congrArg Square.terminalR (outgoing_transport c sq sq.initialR sq.rightB rfl rfl _)

theorem certificate_formulas (c : CompatibleCertificate A B R S m)
    {dL dR : ℕ}
    (D : Bilateral A B c.squareMatrix dL dR
      (fun a => (squareAt c a).leftA) (fun a => (squareAt c a).rightB)) :
    (∀ x i,
      state c (D.PA.symm x) i =
        (let rs := (c.psiA (x.val i).source (window x m i).1).symm (window x m i).2
         (⟨(x.val i).source,rs.1,rs.2.1⟩ : Edge R))) ∧
    (∀ y i,
      state c (D.PB.symm y) i =
        (let yp := reversePath y
         let sr := (c.psiB (window yp m (-i)).1 (yp.val (-i)).source).symm
           (reverseFinitePath (window yp m (-i)).2)
         (⟨sr.1,(yp.val (-i)).source,sr.2.2⟩ : Edge R))) ∧
    (∀ x i, let sq := squareAt c ((D.PA.symm x).val i)
      sq.leftA = x.val i ∧ sq.rightB = (D.h x).val i ∧
      sq.initialR = state c (D.PA.symm x) i ∧
      sq.terminalR = state c (D.PA.symm x) (i+1) ∧
      c.phi sq.i sq.z sq.input = sq.output) ∧
    (∀ y i, let sq := squareAt c ((D.PB.symm y).val i)
      sq.rightB = y.val i ∧ sq.leftA = (D.h.symm y).val i ∧
      sq.initialR = state c (D.PB.symm y) i ∧
      sq.terminalR = state c (D.PB.symm y) (i+1) ∧
      (c.phi sq.i sq.z).symm sq.output = sq.input) := by
  have leftproj (z : Path c.squareMatrix) (i : ℤ) :
      (state c z i).source = ((D.PA z).val i).source := by
    rw [D.left_read, ← (square_states c z i).1]; rfl
  have leftstep (z : Path c.squareMatrix) (i : ℤ)
      (h : (state c z (i+1)).source = ((D.PA z).val i).target) :
      (c.squareIncomingLift.lift ((D.PA z).val i) ⟨state c z (i+1),h⟩).val = state c z i := by
    exact (incoming_square_step c (squareAt c (z.val i)) ((D.PA z).val i)
      (state c z (i+1)) h (D.left_read z i) (square_states c z i).2.symm).trans
        (square_states c z i).1
  have rightproj (z : Path c.squareMatrix) (i : ℤ) :
      (state c z (-i)).target = ((reversePath (D.PB z)).val i).source := by
    change _ = ((D.PB z).val (-i-1)).target
    rw [D.right_read]
    have he : (squareAt c (z.val (-i-1))).terminalR = state c z (-i) := by
      simpa only [show -i-1+1 = -i by omega] using (square_states c z (-i-1)).2
    exact congrArg Edge.target he.symm
  have rightstep (z : Path c.squareMatrix) (i : ℤ)
      (h : (state c z (-(i+1))).target = ((reversePath (D.PB z)).val i).target) :
      (c.squareOutgoingLift.lift ((reversePath (D.PB z)).val i)
        ⟨state c z (-(i+1)),h⟩).val = state c z (-i) := by
    change (c.outgoingSquare (state c z (-(i+1))) ((D.PB z).val (-i-1)) _).terminalR = _
    have hin : state c z (-(i+1)) = (squareAt c (z.val (-i-1))).initialR := by
      simpa only [show -(i+1) = -i-1 by omega] using (square_states c z (-i-1)).1.symm
    have hout : (squareAt c (z.val (-i-1))).terminalR = state c z (-i) := by
      simpa only [show -i-1+1 = -i by omega] using (square_states c z (-i-1)).2
    exact (outgoing_square_step c (squareAt c (z.val (-i-1))) (state c z (-(i+1)))
      ((D.PB z).val (-i-1)) h hin (D.right_read z (-i-1))).trans hout
  refine ⟨?_,?_,?_,?_⟩
  · intro x i
    let z := D.PA.symm x
    have hl : D.PA z = x := D.PA.apply_symm_apply x
    have ht := history_trace c.squareIncomingLift (D.PA z) (state c z)
      (leftproj z) (leftstep z) m i
    rw [hl] at ht
    let q : {r : Edge R // c.squareIncomingLift.project r = (window x m i).1} :=
      ⟨state c z (i+m), (leftproj z (i+m)).trans
        ((congrArg (fun t : Path A => (t.val (i+m)).source) hl).trans (window_endpoint x m i).symm)⟩
    exact (ht q rfl).symm.trans (psiA_lift c (window x m i).2 q)
  · intro y i
    let z := D.PB.symm y
    have hl : D.PB z = y := D.PB.apply_symm_apply y
    have ht := history_trace c.squareOutgoingLift (reversePath (D.PB z))
      (fun j => state c z (-j)) (rightproj z) (rightstep z) m (-i)
    rw [hl] at ht
    let yp := reversePath y
    let q : {r : Edge R // c.squareOutgoingLift.project r = (window yp m (-i)).1} :=
      ⟨state c z (-(-i+m)), (rightproj z (-i+m)).trans
        ((congrArg (fun t : Path B => ((reversePath t).val (-i+m)).source) hl).trans
          (window_endpoint yp m (-i)).symm)⟩
    have hf := (ht q rfl).symm.trans (psiB_lift c (window yp m (-i)).2 q)
    simpa only [neg_neg] using hf
  · intro x i
    let z := D.PA.symm x
    have hl := D.left_read z i
    rw [D.PA.apply_symm_apply] at hl
    exact ⟨hl.symm,(D.right_read z i).symm,(square_states c z i).1,
      (square_states c z i).2,(squareAt c (z.val i)).commutes⟩
  · intro y i
    let z := D.PB.symm y
    have hr := D.right_read z i
    rw [D.PB.apply_symm_apply] at hr
    refine ⟨hr.symm,(D.left_read z i).symm,(square_states c z i).1,
      (square_states c z i).2,?_⟩
    rw [← (squareAt c (z.val i)).commutes]
    exact (c.phi _ _).symm_apply_apply _


theorem whole_certificate (hn : 0 < n) (hk : 0 < k)
    (c : CompatibleCertificate A B R S m) :
    ∃ dL dR, IsLeast {d | Forgets c.squareIncomingLift d} dL ∧
      IsLeast {d | Forgets c.squareOutgoingLift d} dR ∧ dL ≤ m ∧ dR ≤ m ∧
      ∃ D : Bilateral A B c.squareMatrix dL dR
        (fun a => (squareAt c a).leftA) (fun a => (squareAt c a).rightB),
        (∀ r t, c.squareMatrix ((Fintype.equivFin (Edge R)) t)
          ((Fintype.equivFin (Edge R)) r) = Nat.card {a : Edge A //
            ∃ h : a.target = r.source, (c.incomingLift a r h).val = t}) ∧
        (∀ r t, c.squareMatrix ((Fintype.equivFin (Edge R)) r)
          ((Fintype.equivFin (Edge R)) t) = Nat.card {b : Edge B //
            ∃ h : r.target = b.source, (c.outgoingLift r b h).val = t}) ∧
        (∀ a, modelRead c.squareIncomingLift ((leftIso c).edges a) = (squareAt c a).leftA) ∧
        (∀ a, reverseEdge (modelRead c.squareOutgoingLift ((rightIso c).edges (reverseEdge a))) =
          (squareAt c a).rightB) ∧
        (∀ a, ((leftIso c).edges a).source = a.source ∧
          ((leftIso c).edges a).target = a.target) ∧
        (∀ a, ((rightIso c).edges (reverseEdge a)).source = a.target ∧
          ((rightIso c).edges (reverseEdge a)).target = a.source) ∧
        (∀ x, D.h.symm (D.h x) = x) ∧ (∀ y, D.h (D.h.symm y) = y) ∧
        (∀ x, D.h x = D.PB (D.PA.symm x)) ∧
        (∀ y, D.h.symm y = D.PA (D.PB.symm y)) ∧
        (∀ N, Escapes D.h (N+dL) N = ∅) ∧
        (∀ N, Escapes D.h.symm (N+dR) N = ∅) ∧
        (∀ x i, state c (D.PA.symm x) i =
          (let rs := (c.psiA (x.val i).source (window x m i).1).symm (window x m i).2
           (⟨(x.val i).source,rs.1,rs.2.1⟩ : Edge R))) ∧
        (∀ y i, state c (D.PB.symm y) i =
          (let yp := reversePath y
           let sr := (c.psiB (window yp m (-i)).1 (yp.val (-i)).source).symm
             (reverseFinitePath (window yp m (-i)).2)
           (⟨sr.1,(yp.val (-i)).source,sr.2.2⟩ : Edge R))) ∧
        (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
        (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
        (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
        (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
          WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
        (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
          WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
        (∀ x i, let sq := squareAt c ((D.PA.symm x).val i)
          sq.leftA = x.val i ∧ sq.rightB = (D.h x).val i ∧
          sq.initialR = state c (D.PA.symm x) i ∧
          sq.terminalR = state c (D.PA.symm x) (i+1) ∧
          c.phi sq.i sq.z sq.input = sq.output) ∧
        (∀ y i, let sq := squareAt c ((D.PB.symm y).val i)
          sq.rightB = y.val i ∧ sq.leftA = (D.h.symm y).val i ∧
          sq.initialR = state c (D.PB.symm y) i ∧
          sq.terminalR = state c (D.PB.symm y) (i+1) ∧
          (c.phi sq.i sq.z).symm sq.output = sq.input) ∧
        (∀ (x : Path A) (i : ℤ), pathWord (window x m i).2 =
          List.ofFn (fun j : Fin m => x.val (i+j.val))) ∧
        (∀ (y : Path B) (i : ℤ), pathWord (reverseFinitePath (window (reversePath y) m (-i)).2) =
          (List.ofFn (fun j : Fin m => y.val (i-(j.val:ℤ)-1))).reverse) := by
  have hL : ∃ d, Forgets c.squareIncomingLift d :=
    ⟨m,response_forgets _ _ c.squareIncomingLift_forgets_at_lag⟩
  have hR : ∃ d, Forgets c.squareOutgoingLift d :=
    ⟨m,response_forgets _ _ c.squareOutgoingLift_forgets_at_lag⟩
  let dL := Nat.find hL
  let dR := Nat.find hR
  have hdL := Nat.find_spec hL
  have hdR := Nat.find_spec hR
  obtain ⟨D⟩ := certificate_bilateral hn hk c dL dR hdL hdR
  have ho := D.observations
  have hf := certificate_formulas c D
  exact ⟨dL,dR,⟨hdL,fun _ h => Nat.find_min' hL h⟩,
    ⟨hdR,fun _ h => Nat.find_min' hR h⟩,Nat.find_min' hL (response_forgets _ _ c.squareIncomingLift_forgets_at_lag),
    Nat.find_min' hR (response_forgets _ _ c.squareOutgoingLift_forgets_at_lag),D,c.square_column_lift_count,c.square_row_lift_count,
    left_read c,right_read c,(fun _ => ⟨rfl,rfl⟩),(fun _ => ⟨rfl,rfl⟩),D.h.symm_apply_apply,D.h.apply_symm_apply,
    fun _ => rfl,fun _ => rfl,ho.2.2.2.2.2.1,ho.2.2.2.2.2.2,hf.1,hf.2.1,
    ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2.1,hf.2.2.1,hf.2.2.2,
    (fun x i => window_word x m i),(fun y i => past_word y m i)⟩


theorem whole_general {n k q : ℕ} (hn : 0 < n) (hk : 0 < k)
    {A : CountMat n n} {B : CountMat k k} {C : CountMat q q}
    {Q T : Type} [Fintype Q] [Fintype T]
    (L : IncomingLift A Q) (K : IncomingLift B.transpose T)
    (eL : EdgeIso C (Model L)) (eR : EdgeIso C.transpose (Model K))
    (readA : Edge C → Edge A) (readB : Edge C → Edge B)
    (hreadA : ∀ a, modelRead L (eL.edges a) = readA a)
    (hreadB : ∀ a, reverseEdge (modelRead K (eR.edges (reverseEdge a))) = readB a)
    (hA : Essential A) (hB : Essential B) (hC : Essential C)
    (dL dR : ℕ) (hdL : Forgets L dL) (hdR : Forgets K dR) :
    ∃ D : Bilateral A B C dL dR readA readB,
      (∀ x, D.h.symm (D.h x) = x) ∧ (∀ y, D.h (D.h.symm y) = y) ∧
      (∀ x, D.h x = D.PB (D.PA.symm x)) ∧
      (∀ y, D.h.symm y = D.PA (D.PB.symm y)) ∧
      (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
      (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
      (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
        WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
        WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
      (∀ N, Escapes D.h (N+dL) N = ∅) ∧
      (∀ N, Escapes D.h.symm (N+dR) N = ∅) := by
  obtain ⟨E⟩ := general_bilateral hn hk L K eL eR hA hB hC dL dR hdL hdR
  let D : Bilateral A B C dL dR readA readB :=
    { PA := E.PA, PB := E.PB,
      left_read := fun x i => (E.left_read x i).trans (hreadA _),
      right_read := fun x i => (E.right_read x i).trans (hreadB _),
      shiftA := E.shiftA, shiftB := E.shiftB, future := E.future, past := E.past }
  exact ⟨D,D.h.symm_apply_apply,D.h.apply_symm_apply,fun _ => rfl,fun _ => rfl,D.observations⟩

def modelStep {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a : Edge M) (q : Q) : Q :=
  if h : L.project q = a.target then (L.lift a ⟨q,h⟩).val else q

theorem model_target {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a : Edge (Model L)) :
    L.project ((Fintype.equivFin Q).symm a.target) = (modelRead L a).target :=
  ((Fintype.equivFin (Actual L a.source a.target)).symm a.number).property.choose

theorem model_step {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a : Edge (Model L)) :
    modelStep L (modelRead L a) ((Fintype.equivFin Q).symm a.target) =
      (Fintype.equivFin Q).symm a.source := by
  unfold modelStep
  rw [dif_pos (model_target L a)]
  exact ((Fintype.equivFin (Actual L a.source a.target)).symm a.number).property.choose_spec

theorem model_unique {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a b : Edge (Model L)) (ht : a.target = b.target)
    (hr : modelRead L a = modelRead L b) : a = b := by
  have hs : a.source = b.source := by
    apply (Fintype.equivFin Q).symm.injective
    rw [← model_step L a, ← model_step L b, ht, hr]
  rcases a with ⟨u,v,num⟩
  rcases b with ⟨u',v',num'⟩
  cases hs
  cases ht
  congr 1
  apply (Fintype.equivFin (Actual L u v)).symm.injective
  exact Subtype.ext hr

def modelEncode {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a : Edge M) (q : {q : Q // L.project q = a.target}) :
    Edge (Model L) :=
  { source := (Fintype.equivFin Q) (L.lift a q).val
    target := (Fintype.equivFin Q) q.val
    number := Fintype.equivFin (Actual L
      ((Fintype.equivFin Q) (L.lift a q).val) ((Fintype.equivFin Q) q.val)) ⟨a, by
      simpa only [Equiv.symm_apply_apply] using
        (show ∃ h : L.project q.val = a.target,
          (L.lift a ⟨q.val,h⟩).val = (L.lift a q).val from ⟨q.property,rfl⟩)⟩ }

theorem model_encode_read {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (a : Edge M) (q : {q : Q // L.project q = a.target}) :
    modelRead L (modelEncode L a q) = a := by
  let v : Actual L ((Fintype.equivFin Q) (L.lift a q).val)
      ((Fintype.equivFin Q) q.val) := ⟨a, by
    simpa only [Equiv.symm_apply_apply] using
      (show ∃ h : L.project q.val = a.target,
        (L.lift a ⟨q.val,h⟩).val = (L.lift a q).val from ⟨q.property,rfl⟩)⟩
  exact congrArg Subtype.val ((Fintype.equivFin _).symm_apply_apply v)

/-- Original actual incoming-edge unique lifts. The data concerns C edges,
    their endpoint projection, and their specified A labels only. -/
structure ActualIncoming {q p : ℕ} (C : CountMat q q) (M : CountMat p p) where
  project : Fin q → Fin p
  onto : Function.Surjective project
  readout : Edge C → Edge M
  read_source : ∀ a, (readout a).source = project a.source
  read_target : ∀ a, (readout a).target = project a.target
  liftEdge : (a : Edge M) → {v : Fin q // project v = a.target} → Edge C
  lift_target : ∀ a v, (liftEdge a v).target = v.val
  lift_read : ∀ a v, readout (liftEdge a v) = a
  unique : ∀ a v (c : Edge C), c.target = v.val → readout c = a → liftEdge a v = c

def ActualIncoming.stateLift {q p : ℕ} {C : CountMat q q} {M : CountMat p p}
    (I : ActualIncoming C M) : IncomingLift M (Fin q) where
  project := I.project
  onto := I.onto
  lift := fun a v => ⟨(I.liftEdge a v).source,
    (I.read_source (I.liftEdge a v)).symm.trans (congrArg Edge.source (I.lift_read a v))⟩

def ActualIncoming.encode {q p : ℕ} {C : CountMat q q} {M : CountMat p p}
    (I : ActualIncoming C M) (a : Edge C) : Edge (Model I.stateLift) :=
  modelEncode I.stateLift (I.readout a) ⟨a.target,(I.read_target a).symm⟩

theorem ActualIncoming.encode_source {q p : ℕ} {C : CountMat q q} {M : CountMat p p}
    (I : ActualIncoming C M) (a : Edge C) :
    (I.encode a).source = (Fintype.equivFin (Fin q)) a.source := by
  exact congrArg (fun c : Edge C => (Fintype.equivFin (Fin q)) c.source)
    (I.unique (I.readout a) ⟨a.target,(I.read_target a).symm⟩ a rfl rfl)

theorem ActualIncoming.encode_read {q p : ℕ} {C : CountMat q q} {M : CountMat p p}
    (I : ActualIncoming C M) (a : Edge C) : modelRead I.stateLift (I.encode a) = I.readout a :=
  model_encode_read _ _ _

def ActualIncoming.iso {q p : ℕ} {C : CountMat q q} {M : CountMat p p}
    (I : ActualIncoming C M) : EdgeIso C (Model I.stateLift) := by
  let e := Fintype.equivFin (Fin q)
  have hinj : Function.Injective I.encode := by
    intro a b h
    have ht : a.target = b.target := e.injective (congrArg Edge.target h)
    have hr : I.readout a = I.readout b :=
      (I.encode_read a).symm.trans ((congrArg (modelRead I.stateLift) h).trans (I.encode_read b))
    exact (I.unique (I.readout a) ⟨a.target,(I.read_target a).symm⟩ a rfl rfl).symm.trans
      (I.unique (I.readout a) ⟨a.target,(I.read_target a).symm⟩ b ht.symm hr.symm)
  have hsurj : Function.Surjective I.encode := by
    intro b
    let v : {v : Fin q // I.project v = (modelRead I.stateLift b).target} :=
      ⟨e.symm b.target,model_target I.stateLift b⟩
    let a := I.liftEdge (modelRead I.stateLift b) v
    refine ⟨a,model_unique I.stateLift (I.encode a) b ?_ ?_⟩
    · change e a.target = b.target
      exact (congrArg e (I.lift_target _ v)).trans (e.apply_symm_apply b.target)
    · exact (I.encode_read a).trans (I.lift_read _ v)
  exact {
    vertices := e
    edges := Equiv.ofBijective I.encode ⟨hinj,hsurj⟩
    source := I.encode_source
    target := fun _ => rfl }

theorem actual_general {n k q : ℕ} (hn : 0 < n) (hk : 0 < k)
    {A : CountMat n n} {B : CountMat k k} {C : CountMat q q}
    (I : ActualIncoming C A) (J : ActualIncoming C.transpose B.transpose)
    (hA : Essential A) (hB : Essential B) (hC : Essential C)
    (dL dR : ℕ) (hdL : Forgets I.stateLift dL) (hdR : Forgets J.stateLift dR) :
    ∃ D : Bilateral A B C dL dR I.readout
        (fun a => reverseEdge (J.readout (reverseEdge a))),
      (∀ x, D.h.symm (D.h x) = x) ∧ (∀ y, D.h (D.h.symm y) = y) ∧
      (∀ x, D.h x = D.PB (D.PA.symm x)) ∧
      (∀ y, D.h.symm y = D.PA (D.PB.symm y)) ∧
      (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
      (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
      (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
        WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
        WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
      (∀ N, Escapes D.h (N+dL) N = ∅) ∧
      (∀ N, Escapes D.h.symm (N+dR) N = ∅) := by
  exact whole_general hn hk I.stateLift J.stateLift I.iso J.iso I.readout
    (fun a => reverseEdge (J.readout (reverseEdge a))) I.encode_read
    (fun a => congrArg reverseEdge (J.encode_read (reverseEdge a))) hA hB hC dL dR hdL hdR

theorem full_original_6_2 :
    (∀ {n k q : ℕ} (hn : 0 < n) (hk : 0 < k)
    {A : CountMat n n} {B : CountMat k k} {C : CountMat q q}
    (I : ActualIncoming C A) (J : ActualIncoming C.transpose B.transpose)
    (hA : Essential A) (hB : Essential B) (hC : Essential C)
    (dL dR : ℕ) (hdL : Forgets I.stateLift dL) (hdR : Forgets J.stateLift dR),
    ∃ D : Bilateral A B C dL dR I.readout
        (fun a => reverseEdge (J.readout (reverseEdge a))),
      (∀ x, D.h.symm (D.h x) = x) ∧ (∀ y, D.h (D.h.symm y) = y) ∧
      (∀ x, D.h x = D.PB (D.PA.symm x)) ∧
      (∀ y, D.h.symm y = D.PA (D.PB.symm y)) ∧
      (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
      (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
      (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
        WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
      (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
        WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
      (∀ N, Escapes D.h (N+dL) N = ∅) ∧
      (∀ N, Escapes D.h.symm (N+dR) N = ∅)) ∧
    (∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (hn : 0 < n) (hk : 0 < k)
    (c : CompatibleCertificate A B R S m),
    ∃ dL dR, IsLeast {d | Forgets c.squareIncomingLift d} dL ∧
      IsLeast {d | Forgets c.squareOutgoingLift d} dR ∧ dL ≤ m ∧ dR ≤ m ∧
      ∃ D : Bilateral A B c.squareMatrix dL dR
        (fun a => (squareAt c a).leftA) (fun a => (squareAt c a).rightB),
        (∀ r t, c.squareMatrix ((Fintype.equivFin (Edge R)) t)
          ((Fintype.equivFin (Edge R)) r) = Nat.card {a : Edge A //
            ∃ h : a.target = r.source, (c.incomingLift a r h).val = t}) ∧
        (∀ r t, c.squareMatrix ((Fintype.equivFin (Edge R)) r)
          ((Fintype.equivFin (Edge R)) t) = Nat.card {b : Edge B //
            ∃ h : r.target = b.source, (c.outgoingLift r b h).val = t}) ∧
        (∀ a, modelRead c.squareIncomingLift ((leftIso c).edges a) = (squareAt c a).leftA) ∧
        (∀ a, reverseEdge (modelRead c.squareOutgoingLift ((rightIso c).edges (reverseEdge a))) =
          (squareAt c a).rightB) ∧
        (∀ a, ((leftIso c).edges a).source = a.source ∧
          ((leftIso c).edges a).target = a.target) ∧
        (∀ a, ((rightIso c).edges (reverseEdge a)).source = a.target ∧
          ((rightIso c).edges (reverseEdge a)).target = a.source) ∧
        (∀ x, D.h.symm (D.h x) = x) ∧ (∀ y, D.h (D.h.symm y) = y) ∧
        (∀ x, D.h x = D.PB (D.PA.symm x)) ∧
        (∀ y, D.h.symm y = D.PA (D.PB.symm y)) ∧
        (∀ N, Escapes D.h (N+dL) N = ∅) ∧
        (∀ N, Escapes D.h.symm (N+dR) N = ∅) ∧
        (∀ x i, state c (D.PA.symm x) i =
          (let rs := (c.psiA (x.val i).source (window x m i).1).symm (window x m i).2
           (⟨(x.val i).source,rs.1,rs.2.1⟩ : Edge R))) ∧
        (∀ y i, state c (D.PB.symm y) i =
          (let yp := reversePath y
           let sr := (c.psiB (window yp m (-i)).1 (yp.val (-i)).source).symm
             (reverseFinitePath (window yp m (-i)).2)
           (⟨sr.1,(yp.val (-i)).source,sr.2.2⟩ : Edge R))) ∧
        (∀ x, D.h (shift A x) = shift B (D.h x)) ∧
        (∀ x y i, WindowEq x y i (i+dL) → (D.h x).val i = (D.h y).val i) ∧
        (∀ x y i, WindowEq x y (i-dR) i → (D.h.symm x).val i = (D.h.symm y).val i) ∧
        (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)) ((N:ℤ)+dL) →
          WindowEq (D.h x) (D.h y) (-(N:ℤ)) N) ∧
        (∀ (N : ℕ) x y, WindowEq x y (-(N:ℤ)-dR) N →
          WindowEq (D.h.symm x) (D.h.symm y) (-(N:ℤ)) N) ∧
        (∀ x i, let sq := squareAt c ((D.PA.symm x).val i)
          sq.leftA = x.val i ∧ sq.rightB = (D.h x).val i ∧
          sq.initialR = state c (D.PA.symm x) i ∧
          sq.terminalR = state c (D.PA.symm x) (i+1) ∧
          c.phi sq.i sq.z sq.input = sq.output) ∧
        (∀ y i, let sq := squareAt c ((D.PB.symm y).val i)
          sq.rightB = y.val i ∧ sq.leftA = (D.h.symm y).val i ∧
          sq.initialR = state c (D.PB.symm y) i ∧
          sq.terminalR = state c (D.PB.symm y) (i+1) ∧
          (c.phi sq.i sq.z).symm sq.output = sq.input) ∧
        (∀ (x : Path A) (i : ℤ), pathWord (window x m i).2 =
          List.ofFn (fun j : Fin m => x.val (i+j.val))) ∧
        (∀ (y : Path B) (i : ℤ), pathWord (reverseFinitePath (window (reversePath y) m (-i)).2) =
          (List.ofFn (fun j : Fin m => y.val (i-(j.val:ℤ)-1))).reverse)) :=
  ⟨@actual_general, @whole_certificate⟩

end D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.Full62
