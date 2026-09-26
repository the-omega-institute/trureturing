/- GID: D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatible numbered paths construct an essential square graph and forget both boundaries.
-/

import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
import D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.NatCard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

/-- Two numbered edges with a shared, retained middle vertex. -/
abbrev EdgePair {n k l : ℕ} (U : CountMat n k) (V : CountMat k l)
    (i : Fin n) (z : Fin l) :=
  Σ j : Fin k, Fin (U i j) × Fin (V j z)

/-- Sweep an A path across an R edge, retaining every B edge and the R boundary. -/
def sweep {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k}
    (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :
    {d : ℕ} → {i j : Fin n} → {z : Fin k} →
      FinitePath A d i j → Fin (R j z) →
        Σ t : Fin k, Fin (R i t) × FinitePath B d t z
  | _, _, _, z, .nil _, r => ⟨z, r, .nil z⟩
  | _, i, _, _, .cons (j := j) a tail, r =>
      let rest := sweep phi tail r
      let square := phi i rest.1 ⟨j, a, rest.2.1⟩
      ⟨square.1, square.2.1, .cons square.2.2 rest.2.2⟩

/-- Traverse the same numbered squares in the opposite direction. -/
def unsweep {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k}
    (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :
    {d : ℕ} → {i : Fin n} → {t z : Fin k} →
      Fin (R i t) → FinitePath B d t z →
        Σ j : Fin n, FinitePath A d i j × Fin (R j z)
  | _, i, _, _, r, .nil _ => ⟨i, .nil i, r⟩
  | _, i, _, _, r, .cons (j := u) b tail =>
      let square := (phi i u).symm ⟨_, r, b⟩
      let rest := unsweep phi square.2.2 tail
      ⟨rest.1, .cons square.2.1 rest.2.1, rest.2.2⟩

/-- A forward sweep is recovered exactly, including its terminal edge number. -/
theorem unsweep_sweep {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k}
    (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :
    ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)),
      (let swept := sweep phi alpha r
       unsweep phi swept.2.1 swept.2.2) = ⟨j, alpha, r⟩ := by
  intro d i j z alpha
  induction alpha with
  | nil i =>
      intro r
      rfl
  | @cons d i j t a tail ih =>
      intro r
      rcases hs : sweep phi tail r with ⟨u, s, beta⟩
      have htail : unsweep phi s beta = ⟨t, tail, r⟩ := by
        have h := ih r
        dsimp at h
        rw [hs] at h
        exact h
      simp only [sweep]
      rw [hs]
      have hphi :
          (phi i u).symm
            ⟨((phi i u) ⟨j, a, s⟩).1,
             ((phi i u) ⟨j, a, s⟩).2.1,
             ((phi i u) ⟨j, a, s⟩).2.2⟩ = ⟨j, a, s⟩ := by
        simpa only [Sigma.eta, Prod.mk.eta] using
          (phi i u).symm_apply_apply ⟨j, a, s⟩
      simp only [unsweep]
      rw [hphi]
      rw [htail]

def appendPath {k : ℕ} {B : CountMat k k} :
    {d : ℕ} → {i j z : Fin k} →
      FinitePath B d i j → Fin (B j z) → FinitePath B (d + 1) i z
  | _, _, _, z, .nil _, b => .cons b (.nil z)
  | _, _, _, _, .cons a tail, b => .cons a (appendPath tail b)

private def reverseFinitePath {k : ℕ} {B : CountMat k k} :
    {d : ℕ} → {i j : Fin k} → FinitePath B d i j →
      FinitePath B.transpose d j i
  | _, _, _, .nil i => .nil i
  | _, _, _, .cons a tail => appendPath (reverseFinitePath tail) a

/-- The inverse sweep extends by one actual B edge at the terminal end. -/
private theorem unsweep_append {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z) :
    ∀ {d : ℕ} {i : Fin n} {t u z : Fin k} (r : Fin (R i t))
      (beta : FinitePath B d t u) (b : Fin (B u z)),
      unsweep phi r (appendPath beta b) =
        (let prior := unsweep phi r beta
         let sq := (phi prior.1 z).symm ⟨u, prior.2.2, b⟩
         ⟨sq.1, appendPath prior.2.1 sq.2.1, sq.2.2⟩) := by
  intro d i t u z r beta
  induction beta generalizing i with
  | nil t =>
      intro b
      rfl
  | @cons d t w u a tail ih =>
      intro b
      simp only [appendPath, unsweep]
      rw [ih]
      rfl

/-- A response class at the next depth maps into one response class after an
    actual numbered incoming edge. -/
theorem incoming_response_step {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) {u v : Q}
    (h : L.response (d + 1) u v) (a : Edge A)
    (hu : L.project u = a.target) (hv : L.project v = a.target) :
    L.response d (L.lift a ⟨u, hu⟩).val (L.lift a ⟨v, hv⟩).val := by
  have hsnoc : ∀ {d : ℕ} {i j z : Fin n}
      (path : FinitePath A d i j) (edge : Fin (A j z))
      (q : {x : Q // L.project x = z}),
      L.liftPath (appendPath path edge) q =
        L.liftPath path (L.lift ⟨j, z, edge⟩ q) := by
    intro length i j z path
    induction path with
    | nil i =>
        intro edge q
        rfl
    | @cons length i j t edge tail ih =>
        intro last q
        simp only [appendPath, IncomingLift.liftPath]
        exact congrArg (L.lift ⟨i, j, edge⟩) (ih last q)
  rcases a with ⟨source, target, number⟩
  let lu := L.lift (⟨source, target, number⟩ : Edge A) ⟨u, hu⟩
  let lv := L.lift (⟨source, target, number⟩ : Edge A) ⟨v, hv⟩
  have hobs : L.responseReadout (d + 1) u = L.responseReadout (d + 1) v := h
  have hsourceU : L.project lu.val = source := lu.property
  have hsourceV : L.project lv.val = source := lv.property
  change L.responseReadout d lu.val = L.responseReadout d lv.val
  apply Prod.ext (hsourceU.trans hsourceV.symm)
  funext i j path
  by_cases hj : source = j
  · subst j
    have hpath := congrArg
      (fun p => p.2 i target (appendPath path number)) hobs
    simp only [IncomingLift.responseReadout, dif_pos hu, dif_pos hv,
      Option.some.injEq] at hpath
    have hsame : L.liftPath path lu = L.liftPath path lv := by
      have hwhole :
          L.liftPath (appendPath path number) ⟨u, hu⟩ =
            L.liftPath (appendPath path number) ⟨v, hv⟩ :=
        Subtype.ext hpath
      rw [hsnoc path number ⟨u, hu⟩,
        hsnoc path number ⟨v, hv⟩] at hwhole
      exact hwhole
    simp only [IncomingLift.responseReadout, dif_pos hsourceU,
      dif_pos hsourceV, Option.some.injEq]
    exact congrArg Subtype.val hsame
  · have hnotU : L.project lu.val ≠ j := by
      rw [hsourceU]
      exact hj
    have hnotV : L.project lv.val ≠ j := by
      rw [hsourceV]
      exact hj
    simp only [IncomingLift.responseReadout, dif_neg hnotU, dif_neg hnotV]

#print axioms incoming_response_step

/-- The equation is on all typed numbered inputs, including the entire B output path. -/
structure CompatibleCertificate {n k : ℕ} (A : CountMat n n)
    (B : CountMat k k) (R : CountMat n k) (S : CountMat k n)
    (m : ℕ) where
  positiveLag : 0 < m
  essentialA :
    (∀ i : Fin n, ∃ j : Fin n, A i j ≠ 0) ∧
    (∀ j : Fin n, ∃ i : Fin n, A i j ≠ 0)
  essentialB :
    (∀ i : Fin k, ∃ j : Fin k, B i j ≠ 0) ∧
    (∀ j : Fin k, ∃ i : Fin k, B i j ≠ 0)
  phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z
  psiA : ∀ i j, EdgePair R S i j ≃ FinitePath A m i j
  psiB : ∀ t z, EdgePair S R t z ≃ FinitePath B m t z
  compatible : ∀ {i j z} (alpha : FinitePath A m i j) (r : Fin (R j z)),
    sweep phi alpha r =
      (let rs := (psiA i j).symm alpha
       ⟨rs.1, rs.2.1, (psiB rs.1 z) ⟨j, rs.2.2, r⟩⟩)

namespace CompatibleCertificate

variable {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
  {R : CountMat n k} {S : CountMat k n}

/-- An actual phi square: both numbered pairs are stored and checked. -/
structure Square (c : CompatibleCertificate A B R S m) where
  i : Fin n
  z : Fin k
  input : EdgePair A R i z
  output : EdgePair R B i z
  commutes : c.phi i z input = output

def Square.initialR {c : CompatibleCertificate A B R S m} (sq : Square c) : Edge R :=
  ⟨sq.i, sq.output.1, sq.output.2.1⟩

def Square.terminalR {c : CompatibleCertificate A B R S m} (sq : Square c) : Edge R :=
  ⟨sq.input.1, sq.z, sq.input.2.2⟩

def Square.leftA {c : CompatibleCertificate A B R S m} (sq : Square c) : Edge A :=
  ⟨sq.i, sq.input.1, sq.input.2.1⟩

def Square.rightB {c : CompatibleCertificate A B R S m} (sq : Square c) : Edge B :=
  ⟨sq.output.1, sq.z, sq.output.2.2⟩

private def edgeCoordinates {p q : ℕ} (M : CountMat p q) : Edge M ≃
    Σ i : Fin p, Σ z : Fin q, Fin (M i z) where
  toFun r := ⟨r.source, r.target, r.number⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by intro r; cases r; rfl
  right_inv := by intro p; rcases p with ⟨i, z, number⟩; rfl

noncomputable instance {p q : ℕ} (M : CountMat p q) : Fintype (Edge M) := by
  classical
  letI : (i : Fin p) → Fintype (Σ z : Fin q, Fin (M i z)) :=
    fun _ => Sigma.instFintype
  letI : Fintype (Σ i : Fin p, Σ z : Fin q, Fin (M i z)) :=
    Sigma.instFintype
  exact Fintype.ofEquiv (Σ i : Fin p, Σ z : Fin q, Fin (M i z))
    (edgeCoordinates M).symm

private def squareCoordinates (c : CompatibleCertificate A B R S m) :
    Square c ≃ Σ i : Fin n, Σ z : Fin k, EdgePair A R i z where
  toFun sq := ⟨sq.i, sq.z, sq.input⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, c.phi p.1 p.2.1 p.2.2, rfl⟩
  left_inv := by
    intro sq
    rcases sq with ⟨i, z, input, output, h⟩
    cases h
    rfl
  right_inv := by intro p; rcases p with ⟨i, z, input⟩; rfl

noncomputable instance (c : CompatibleCertificate A B R S m) : Fintype (Square c) := by
  classical
  letI : (i : Fin n) → (z : Fin k) → Fintype (EdgePair A R i z) :=
    fun _ _ => Sigma.instFintype
  letI : (i : Fin n) → Fintype (Σ z : Fin k, EdgePair A R i z) :=
    fun _ => Sigma.instFintype
  letI : Fintype (Σ i : Fin n, Σ z : Fin k, EdgePair A R i z) :=
    Sigma.instFintype
  exact Fintype.ofEquiv (Σ i : Fin n, Σ z : Fin k, EdgePair A R i z)
    (squareCoordinates c).symm

private def incomingResponseFiber {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) (F : Quotient (L.response d))
    (v : Q) : Type :=
  {a : Edge M // ∃ hv : L.project v = a.target,
    Quotient.mk (L.response d) (L.lift a ⟨v, hv⟩).val = F}

/-- Representatives equivalent at depth d+1 count the same actual incoming
    lifts into every depth-d response class. -/
theorem incoming_response_fiber_card_step {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) (F : Quotient (L.response d))
    {v w : Q} (h : L.response (d + 1) v w) :
    Nat.card (incomingResponseFiber L d F v) =
      Nat.card (incomingResponseFiber L d F w) := by
  classical
  have htransport (x y : Q) (hxy : L.response (d + 1) x y)
      (a : Edge M) :
      (∃ hx : L.project x = a.target,
        Quotient.mk (L.response d) (L.lift a ⟨x, hx⟩).val = F) →
      (∃ hy : L.project y = a.target,
        Quotient.mk (L.response d) (L.lift a ⟨y, hy⟩).val = F) := by
    rintro ⟨hx, hclass⟩
    have hobs : L.responseReadout (d + 1) x =
        L.responseReadout (d + 1) y := hxy
    have hp : L.project x = L.project y := congrArg Prod.fst hobs
    have hy : L.project y = a.target := hp.symm.trans hx
    have hlift := incoming_response_step L d hxy a hx hy
    exact ⟨hy, (Quotient.sound hlift).symm.trans hclass⟩
  let e : incomingResponseFiber L d F v ≃
      incomingResponseFiber L d F w := {
    toFun x := ⟨x.val, htransport v w h x.val x.property⟩
    invFun x := ⟨x.val,
      htransport w v ((L.response (d + 1)).iseqv.symm h) x.val x.property⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  exact Nat.card_congr e

#print axioms incoming_response_fiber_card_step

/-- The depth-d quotient adjacency counts the actual numbered base edges
    whose lift reaches each source response class. -/
noncomputable def incomingResponseMatrix {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) :
    Matrix (Quotient (L.response d)) (Quotient (L.response d)) ℕ :=
  fun F H => Nat.card (incomingResponseFiber L d F (Quotient.out H))

private def incomingResponseProjection {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) :
    Quotient (L.response d) → Quotient (L.response (d + 1)) :=
  Setoid.map_of_le ((response_zero_and_step L).2 d)

private noncomputable def incomingResponseU {p : ℕ} {M : CountMat p p}
    {Q : Type} (L : IncomingLift M Q) (d : ℕ) :
    Matrix (Quotient (L.response d)) (Quotient (L.response (d + 1))) ℕ :=
  fun F Z => Nat.card (incomingResponseFiber L d F (Quotient.out Z))

private noncomputable def incomingResponseV {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) :
    Matrix (Quotient (L.response (d + 1))) (Quotient (L.response d)) ℕ := by
  classical
  exact fun Z H => if incomingResponseProjection L d H = Z then 1 else 0

private theorem incoming_response_matrix_factor_base {p : ℕ} {M : CountMat p p}
    {Q : Type} (L : IncomingLift M Q) (d : ℕ)
    [Fintype (Quotient (L.response (d + 1)))] :
    incomingResponseMatrix L d =
      incomingResponseU L d * incomingResponseV L d := by
  classical
  ext F H
  have hq : Quotient.mk (L.response (d + 1)) (Quotient.out H) =
      incomingResponseProjection L d H := by
    calc
      Quotient.mk (L.response (d + 1)) (Quotient.out H) =
          incomingResponseProjection L d
            (Quotient.mk (L.response d) (Quotient.out H)) := rfl
      _ = incomingResponseProjection L d H := by rw [Quotient.out_eq]
  have hresponse : L.response (d + 1) (Quotient.out H)
      (Quotient.out (incomingResponseProjection L d H)) := by
    apply Quotient.exact
    calc
      Quotient.mk (L.response (d + 1)) (Quotient.out H) =
          incomingResponseProjection L d H := hq
      _ = Quotient.mk (L.response (d + 1))
            (Quotient.out (incomingResponseProjection L d H)) :=
              (Quotient.out_eq _).symm
  change Nat.card (incomingResponseFiber L d F (Quotient.out H)) =
    ∑ Z, incomingResponseU L d F Z * incomingResponseV L d Z H
  simp only [incomingResponseU, incomingResponseV]
  simpa using incoming_response_fiber_card_step L d F hresponse

private theorem incoming_response_matrix_factor_step {p : ℕ} {M : CountMat p p}
    {Q : Type} (L : IncomingLift M Q) (d : ℕ)
    [Fintype (Quotient (L.response d))]
    [Fintype (Quotient (L.response (d + 1)))] :
    incomingResponseMatrix L (d + 1) =
      incomingResponseV L d * incomingResponseU L d := by
  classical
  ext Z W
  let v := Quotient.out W
  have hprojection (q : Q) :
      incomingResponseProjection L d (Quotient.mk (L.response d) q) =
        Quotient.mk (L.response (d + 1)) q := rfl
  letI : Fintype (incomingResponseFiber L (d + 1) Z v) := by
    unfold incomingResponseFiber
    infer_instance
  letI (H : Quotient (L.response d)) :
      Fintype (incomingResponseFiber L d H v) := by
    unfold incomingResponseFiber
    infer_instance
  let e : incomingResponseFiber L (d + 1) Z v ≃
      Σ H : Quotient (L.response d),
        {a : incomingResponseFiber L d H v //
          incomingResponseProjection L d H = Z} := {
    toFun := fun x => by
      let hv := Classical.choose x.property
      have hZ := Classical.choose_spec x.property
      let H := Quotient.mk (L.response d) (L.lift x.val ⟨v, hv⟩).val
      refine ⟨H, ⟨⟨x.val, ⟨hv, rfl⟩⟩, ?_⟩⟩
      simpa only [H, hprojection] using hZ
    invFun := fun y => by
      let H := y.1
      let a := y.2.val.val
      let hv := Classical.choose y.2.val.property
      have hH := Classical.choose_spec y.2.val.property
      have hZ := y.2.property
      refine ⟨a, ⟨hv, ?_⟩⟩
      calc
        Quotient.mk (L.response (d + 1)) (L.lift a ⟨v, hv⟩).val =
            incomingResponseProjection L d
              (Quotient.mk (L.response d) (L.lift a ⟨v, hv⟩).val) :=
                (hprojection _).symm
        _ = incomingResponseProjection L d H := congrArg _ hH
        _ = Z := hZ
    left_inv := by
      intro x
      apply Subtype.ext
      rfl
    right_inv := by
      rintro ⟨H, ⟨⟨a, ⟨hv, hH⟩⟩, hZ⟩⟩
      let witness : ∃ hv : L.project v = a.target,
          Quotient.mk (L.response (d + 1)) (L.lift a ⟨v, hv⟩).val = Z := by
        refine ⟨hv, ?_⟩
        calc
          Quotient.mk (L.response (d + 1)) (L.lift a ⟨v, hv⟩).val =
              incomingResponseProjection L d
                (Quotient.mk (L.response d) (L.lift a ⟨v, hv⟩).val) :=
                  (hprojection _).symm
          _ = incomingResponseProjection L d H := congrArg _ hH
          _ = Z := hZ
      have hsub :
          (⟨v, Classical.choose witness⟩ :
            {q : Q // L.project q = a.target}) = ⟨v, hv⟩ :=
        Subtype.ext rfl
      have hfirst := (congrArg (fun q =>
        Quotient.mk (L.response d) (L.lift a q).val) hsub).trans hH
      generalize hK : Quotient.mk (L.response d)
          (L.lift a ⟨v, Classical.choose witness⟩).val = K at hfirst ⊢
      subst K
      subst H
      apply Sigma.ext rfl
      exact heq_of_eq (Subtype.ext (Subtype.ext rfl)) }
  change Nat.card (incomingResponseFiber L (d + 1) Z v) =
    ∑ H, incomingResponseV L d Z H * incomingResponseU L d H W
  calc
    Nat.card (incomingResponseFiber L (d + 1) Z v) =
        Fintype.card (incomingResponseFiber L (d + 1) Z v) :=
          Nat.card_eq_fintype_card
    _ = Fintype.card (Σ H : Quotient (L.response d),
        {a : incomingResponseFiber L d H v //
          incomingResponseProjection L d H = Z}) := Fintype.card_congr e
    _ = ∑ H, (if incomingResponseProjection L d H = Z then
          Nat.card (incomingResponseFiber L d H v) else 0) := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro H _
      by_cases h : incomingResponseProjection L d H = Z
      · simp [h, Nat.card_eq_fintype_card]
      · simp [h]
    _ = ∑ H, incomingResponseV L d Z H * incomingResponseU L d H W := by
      simp only [incomingResponseV, incomingResponseU, v]
      apply Finset.sum_congr rfl
      intro H _
      by_cases h : incomingResponseProjection L d H = Z <;> simp [h]

/-- Once the response remembers only the base vertex, quotient adjacency
    counts exactly the numbered base edges. -/
private theorem incoming_response_matrix_at_forgetting {p : ℕ} {M : CountMat p p}
    {Q : Type} (L : IncomingLift M Q) (d : ℕ)
    (hd : L.response d = Setoid.ker L.project)
    (representative : Fin p → Q)
    (hsection : ∀ i, L.project (representative i) = i)
    (i j : Fin p) :
    incomingResponseMatrix L d
      (Quotient.mk (L.response d) (representative i))
      (Quotient.mk (L.response d) (representative j)) = M i j := by
  classical
  let F := Quotient.mk (L.response d) (representative i)
  let H := Quotient.mk (L.response d) (representative j)
  have hrel : L.response d (Quotient.out H) (representative j) :=
    Quotient.exact (Quotient.out_eq H)
  have hcard := incoming_response_fiber_card_step L d F
    ((response_zero_and_step L).2 d hrel)
  let E := {a : Edge M // a.source = i ∧ a.target = j}
  let e : incomingResponseFiber L d F (representative j) ≃ E := {
    toFun := fun x => by
      let a := x.val
      let hv := Classical.choose x.property
      have hclass := Classical.choose_spec x.property
      have hsource : a.source = i := by
        have hq : L.response d (L.lift a ⟨representative j, hv⟩).val
            (representative i) :=
          Quotient.exact hclass
        rw [hd] at hq
        calc
          a.source = L.project (L.lift a ⟨representative j, hv⟩).val :=
            (L.lift a ⟨representative j, hv⟩).property.symm
          _ = L.project (representative i) := hq
          _ = i := hsection i
      exact ⟨a, hsource, hv.symm.trans (hsection j)⟩
    invFun := fun x => by
      obtain ⟨a, hs, ht⟩ := x
      have hv : L.project (representative j) = a.target :=
        (hsection j).trans ht.symm
      refine ⟨a, ⟨hv, Quotient.sound ?_⟩⟩
      rw [hd]
      calc
        L.project (L.lift a ⟨representative j, hv⟩).val = a.source :=
          (L.lift a ⟨representative j, hv⟩).property
        _ = i := hs
        _ = L.project (representative i) := (hsection i).symm
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by
      rintro ⟨a, ⟨hs, ht⟩⟩
      apply Subtype.ext
      rfl }
  let edgeEquiv : E ≃ Fin (M i j) := {
    toFun := fun x => by
      obtain ⟨⟨source, target, number⟩, hs, ht⟩ := x
      change source = i at hs
      change target = j at ht
      cases hs
      cases ht
      exact number
    invFun := fun number => ⟨⟨i, j, number⟩, rfl, rfl⟩
    left_inv := by
      rintro ⟨⟨source, target, number⟩, hs, ht⟩
      change source = i at hs
      change target = j at ht
      cases hs
      cases ht
      rfl
    right_inv := by intro number; rfl }
  calc
    incomingResponseMatrix L d F H =
        Nat.card (incomingResponseFiber L d F (Quotient.out H)) := rfl
    _ = Nat.card (incomingResponseFiber L d F (representative j)) := hcard
    _ = Nat.card E := Nat.card_congr e
    _ = Nat.card (Fin (M i j)) := Nat.card_congr edgeEquiv
    _ = M i j := Nat.card_fin _

private theorem response_matrix_forgetting_reindexed {p : ℕ}
    {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (d : ℕ)
    (hd : L.response d = Setoid.ker L.project) :
    ∃ e : Quotient (L.response d) ≃ Fin p,
      Matrix.reindex e e (incomingResponseMatrix L d) = M := by
  classical
  let rep : Fin p → Q := Function.surjInv L.onto
  have hsection : ∀ i, L.project (rep i) = i :=
    Function.rightInverse_surjInv L.onto
  let e : Quotient (L.response d) ≃ Fin p := {
    toFun := Quotient.lift L.project (by
      intro a b hab
      exact Eq.mp
        (congrArg (fun T : Setoid Q => T.r a b) hd) hab)
    invFun := fun i => Quotient.mk (L.response d) (rep i)
    left_inv := by
      intro F
      refine Quotient.inductionOn F ?_
      intro q
      apply Quotient.sound
      change (L.response d).r (rep (L.project q)) q
      exact Eq.mp
        (congrArg (fun T : Setoid Q => T.r (rep (L.project q)) q) hd.symm)
        (hsection (L.project q))
    right_inv := hsection }
  refine ⟨e, ?_⟩
  ext i j
  have hrepr (v : Fin p) :
      e.symm v = Quotient.mk (L.response d) (rep v) := rfl
  change incomingResponseMatrix L d (e.symm i) (e.symm j) = M i j
  rw [hrepr i, hrepr j]
  exact incoming_response_matrix_at_forgetting L d hd rep hsection i j

private noncomputable def responseFintype {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q) (d : ℕ) :
    Fintype (Quotient (L.response d)) := by
  classical
  exact Fintype.ofFinite _

private noncomputable def responseIndex {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q) (d : ℕ) :
    Quotient (L.response d) ≃
      Fin (@Fintype.card _ (responseFintype L d)) :=
  @Fintype.equivFin _ (responseFintype L d)

private noncomputable def finiteResponseMatrix {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q) (d : ℕ) :
    CountMat (@Fintype.card _ (responseFintype L d))
      (@Fintype.card _ (responseFintype L d)) :=
  Matrix.reindex (responseIndex L d) (responseIndex L d)
    (incomingResponseMatrix L d)

private theorem finite_response_chain {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q)
    (start length : ℕ) :
    ExchangeChain ℕ (finiteResponseMatrix L start)
      (finiteResponseMatrix L (start + length)) length := by
  classical
  induction length generalizing start with
  | zero =>
      simpa using ExchangeChain.nil (finiteResponseMatrix L start)
  | succ length ih =>
      letI := responseFintype L start
      letI := responseFintype L (start + 1)
      let e0 := responseIndex L start
      let e1 := responseIndex L (start + 1)
      let U := Matrix.reindex e0 e1 (incomingResponseU L start)
      let V := Matrix.reindex e1 e0 (incomingResponseV L start)
      have hbase : finiteResponseMatrix L start = U * V := by
        change Matrix.reindex e0 e0 (incomingResponseMatrix L start) = U * V
        rw [incoming_response_matrix_factor_base L start]
        change (incomingResponseU L start * incomingResponseV L start).submatrix
            e0.symm e0.symm =
          (incomingResponseU L start).submatrix e0.symm e1.symm *
            (incomingResponseV L start).submatrix e1.symm e0.symm
        exact (Matrix.submatrix_mul_equiv _ _ e0.symm e1.symm e0.symm).symm
      have hstep : finiteResponseMatrix L (start + 1) = V * U := by
        change Matrix.reindex e1 e1 (incomingResponseMatrix L (start + 1)) =
          V * U
        rw [incoming_response_matrix_factor_step L start]
        change (incomingResponseV L start * incomingResponseU L start).submatrix
            e1.symm e1.symm =
          (incomingResponseV L start).submatrix e1.symm e0.symm *
            (incomingResponseU L start).submatrix e0.symm e1.symm
        exact (Matrix.submatrix_mul_equiv _ _ e1.symm e0.symm e1.symm).symm
      rw [hbase]
      refine ExchangeChain.cons U V ?_
      rw [← hstep]
      have hindex : start + 1 + length = start + (length + 1) := by omega
      rw [← hindex]
      exact ih (start + 1)

private theorem exchange_chain_trans {a b c : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}
    {l₁ l₂ : ℕ} (left : ExchangeChain ℕ X Y l₁)
    (right : ExchangeChain ℕ Y Z l₂) :
    ExchangeChain ℕ X Z (l₁ + l₂) := by
  induction left with
  | nil _ => simpa using right
  | cons U V tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExchangeChain.cons U V (ih right)

private theorem exchange_chain_reverse {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length) :
    ExchangeChain ℕ Y X length := by
  induction chain with
  | nil _ => exact ExchangeChain.nil _
  | cons U V tail ih =>
      have step : ExchangeChain ℕ (V * U) (U * V) 1 :=
        ExchangeChain.cons V U (ExchangeChain.nil _)
      simpa [Nat.add_comm] using exchange_chain_trans ih step

private theorem exchange_chain_transpose {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length) :
    ExchangeChain ℕ X.transpose Y.transpose length := by
  induction chain with
  | nil _ => exact ExchangeChain.nil _
  | cons U V tail ih =>
      rw [Matrix.transpose_mul]
      refine ExchangeChain.cons V.transpose U.transpose ?_
      simpa only [Matrix.transpose_mul] using ih

private theorem finite_response_chain_to {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q)
    (start length : ℕ) {r : ℕ}
    (eEnd : Quotient (L.response (start + length + 1)) ≃ Fin r) :
    ExchangeChain ℕ (finiteResponseMatrix L start)
      (Matrix.reindex eEnd eEnd
        (incomingResponseMatrix L (start + length + 1)))
      (length + 1) := by
  classical
  let d := start + length
  letI := responseFintype L d
  letI := responseFintype L (d + 1)
  let eMid := responseIndex L d
  let U := Matrix.reindex eMid eEnd (incomingResponseU L d)
  let V := Matrix.reindex eEnd eMid (incomingResponseV L d)
  have hbase : finiteResponseMatrix L d = U * V := by
    change Matrix.reindex eMid eMid (incomingResponseMatrix L d) = U * V
    rw [incoming_response_matrix_factor_base L d]
    change (incomingResponseU L d * incomingResponseV L d).submatrix
        eMid.symm eMid.symm =
      (incomingResponseU L d).submatrix eMid.symm eEnd.symm *
        (incomingResponseV L d).submatrix eEnd.symm eMid.symm
    exact (Matrix.submatrix_mul_equiv _ _ eMid.symm eEnd.symm eMid.symm).symm
  have hstep : Matrix.reindex eEnd eEnd (incomingResponseMatrix L (d + 1)) =
      V * U := by
    rw [incoming_response_matrix_factor_step L d]
    change (incomingResponseV L d * incomingResponseU L d).submatrix
        eEnd.symm eEnd.symm =
      (incomingResponseV L d).submatrix eEnd.symm eMid.symm *
        (incomingResponseU L d).submatrix eMid.symm eEnd.symm
    exact (Matrix.submatrix_mul_equiv _ _ eEnd.symm eMid.symm eEnd.symm).symm
  have last : ExchangeChain ℕ (finiteResponseMatrix L d)
      (Matrix.reindex eEnd eEnd (incomingResponseMatrix L (d + 1))) 1 := by
    rw [hbase, hstep]
    exact ExchangeChain.cons U V (ExchangeChain.nil (V * U))
  exact exchange_chain_trans (finite_response_chain L start length) last

/-- Every matrix edge is a particular numbered square with fixed R endpoints. -/
noncomputable def squareMatrix (c : CompatibleCertificate A B R S m) :
    CountMat (Fintype.card (Edge R)) (Fintype.card (Edge R)) := by
  classical
  let e := Fintype.equivFin (Edge R)
  exact fun u v => Fintype.card
    {sq : Square c // e sq.initialR = u ∧ e sq.terminalR = v}

/-- The matrix entry numbers and its actual endpoint-indexed squares coincide. -/
noncomputable def squareFiberEquiv (c : CompatibleCertificate A B R S m)
    (u v : Fin (Fintype.card (Edge R))) :
    Fin (c.squareMatrix u v) ≃
      {sq : Square c //
        (Fintype.equivFin (Edge R)) sq.initialR = u ∧
        (Fintype.equivFin (Edge R)) sq.terminalR = v} := by
  classical
  exact (Fintype.equivFin _).symm

/-- The finite number of a square in its adjacency entry. -/
noncomputable def numberSquare (c : CompatibleCertificate A B R S m)
    (sq : Square c) :
    Fin (c.squareMatrix
      ((Fintype.equivFin (Edge R)) sq.initialR)
      ((Fintype.equivFin (Edge R)) sq.terminalR)) := by
  classical
  let e := Fintype.equivFin (Edge R)
  exact (c.squareFiberEquiv (e sq.initialR) (e sq.terminalR)).symm
    ⟨sq, rfl, rfl⟩

/-- Fixing the terminal R edge and A edge uniquely determines the incoming square. -/
def incomingSquare (c : CompatibleCertificate A B R S m)
    (a : Edge A) (r : Edge R) (h : a.target = r.source) : Square c := by
  let input : EdgePair A R a.source r.target :=
    ⟨a.target, a.number, h.symm ▸ r.number⟩
  exact ⟨a.source, r.target, input, c.phi a.source r.target input, rfl⟩

/-- Fixing the initial R edge and B edge uniquely determines the outgoing square. -/
def outgoingSquare (c : CompatibleCertificate A B R S m)
    (r : Edge R) (b : Edge B) (h : r.target = b.source) : Square c := by
  let output : EdgePair R B r.source b.target :=
    ⟨r.target, r.number, h.symm ▸ b.number⟩
  exact ⟨r.source, b.target, (c.phi r.source b.target).symm output,
    output, (c.phi r.source b.target).apply_symm_apply output⟩

def incomingLift (c : CompatibleCertificate A B R S m)
    (a : Edge A) (r : Edge R) (h : a.target = r.source) :
    {s : Edge R // s.source = a.source} :=
  ⟨(c.incomingSquare a r h).initialR, rfl⟩

def outgoingLift (c : CompatibleCertificate A B R S m)
    (r : Edge R) (b : Edge B) (h : r.target = b.source) :
    {s : Edge R // s.target = b.target} :=
  ⟨(c.outgoingSquare r b h).terminalR, rfl⟩

/-- Repeated incoming squares act on the actual terminal R edge number. -/
def liftIncomingPath (c : CompatibleCertificate A B R S m) :
    {d : ℕ} → {i j : Fin n} → {z : Fin k} →
      FinitePath A d i j → Fin (R j z) → Σ t : Fin k, Fin (R i t)
  | _, _, _, z, .nil _, r => ⟨z, r⟩
  | _, i, _, _, .cons (j := j) a tail, r =>
      let rest := c.liftIncomingPath tail r
      let terminal : Edge R := ⟨j, rest.1, rest.2⟩
      let sq := c.incomingSquare ⟨i, j, a⟩ terminal rfl
      ⟨sq.output.1, sq.output.2.1⟩

/-- Outgoing squares are traversed with their actual numbered B path. -/
def liftOutgoingPath (c : CompatibleCertificate A B R S m) :
    {d : ℕ} → {i : Fin n} → {t z : Fin k} →
      Fin (R i t) → FinitePath B d t z →
        Σ j : Fin n, FinitePath A d i j × Fin (R j z) :=
  unsweep c.phi

/-- The lift uses phi squares at every step; C then fixes its initial R edge
    from psiA alone, independently of the chosen compatible terminal edge. -/
theorem square_lifts_left_forgetting (c : CompatibleCertificate A B R S m) :
    (∀ (a : Edge A) (r : Edge R) (h : a.target = r.source),
      (c.incomingSquare a r h).terminalR = r) ∧
    (∀ (r : Edge R) (b : Edge B) (h : r.target = b.source),
      (c.outgoingSquare r b h).initialR = r) ∧
    (∀ {i j z} (alpha : FinitePath A m i j) (r : Fin (R j z)),
      (let lifted := c.liftIncomingPath alpha r
       (⟨i, lifted.1, lifted.2⟩ : Edge R)) =
      (let rs := (c.psiA i j).symm alpha
       (⟨i, rs.1, rs.2.1⟩ : Edge R))) := by
  constructor
  · intro a r h
    cases a with
    | mk ai aj av =>
      cases r with
      | mk ri rz rv =>
        cases h
        rfl
  constructor
  · intro r b h
    cases r
    rfl
  · have hbridge :
        ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
          (alpha : FinitePath A d i j) (r : Fin (R j z)),
          c.liftIncomingPath alpha r =
            (let swept := sweep c.phi alpha r
             ⟨swept.1, swept.2.1⟩) := by
      intro d i j z alpha
      induction alpha with
      | nil i =>
          intro r
          rfl
      | @cons d i j t a tail ih =>
          intro r
          rcases hs : sweep c.phi tail r with ⟨u, s, beta⟩
          have hlift : c.liftIncomingPath tail r = ⟨u, s⟩ := by
            have h := ih r
            dsimp at h
            rw [hs] at h
            exact h
          simp only [liftIncomingPath, sweep]
          rw [hlift, hs]
          rfl
    intro i j z alpha r
    have h := hbridge alpha r
    rw [c.compatible alpha r] at h
    exact congrArg (fun p : Σ t : Fin k, Fin (R i t) =>
      (⟨i, p.1, p.2⟩ : Edge R)) h

#print axioms square_lifts_left_forgetting

/-- Inverting C fixes the terminal R edge for every initial R edge and B path.
    The proof uses the actual inverse sweep, not a forgetting hypothesis. -/
theorem square_lifts_right_forgetting (c : CompatibleCertificate A B R S m) :
    ∀ {i : Fin n} {t z : Fin k} (r : Fin (R i t))
      (beta : FinitePath B m t z),
      (let lifted := c.liftOutgoingPath r beta
       (⟨lifted.1, z, lifted.2.2⟩ : Edge R)) =
      (let sr := (c.psiB t z).symm beta
       (⟨sr.1, z, sr.2.2⟩ : Edge R)) := by
  intro i t z r beta
  let sr := (c.psiB t z).symm beta
  let alpha := (c.psiA i sr.1) ⟨t, r, sr.2.1⟩
  have hA : (c.psiA i sr.1).symm alpha = ⟨t, r, sr.2.1⟩ :=
    (c.psiA i sr.1).symm_apply_apply _
  have hB : (c.psiB t z) ⟨sr.1, sr.2.1, sr.2.2⟩ = beta := by
    change (c.psiB t z) sr = beta
    exact (c.psiB t z).apply_symm_apply beta
  have hsweep : sweep c.phi alpha sr.2.2 = ⟨t, r, beta⟩ := by
    rw [c.compatible]
    rw [hA]
    exact congrArg (fun path : FinitePath B m t z =>
      (⟨t, r, path⟩ : Σ u : Fin k, Fin (R i u) × FinitePath B m u z)) hB
  have hundo := unsweep_sweep c.phi alpha sr.2.2
  rw [hsweep] at hundo
  exact congrArg (fun p : Σ j : Fin n,
      FinitePath A m i j × Fin (R j z) =>
      (⟨p.1, z, p.2.2⟩ : Edge R)) hundo

#print axioms square_lifts_right_forgetting

/-- Actual squares give an essential finite adjacency matrix.  Both R endpoint
    maps are onto, using the path bijections and essentiality of A and B. -/
theorem square_graph_essential_and_projections
    (c : CompatibleCertificate A B R S m) :
    (∀ r : Edge R, ∃ sq : Square c, sq.initialR = r) ∧
    (∀ r : Edge R, ∃ sq : Square c, sq.terminalR = r) ∧
    Function.Surjective (fun r : Edge R => r.source) ∧
    Function.Surjective (fun r : Edge R => r.target) ∧
    ((∀ u, ∃ v, c.squareMatrix u v ≠ 0) ∧
      (∀ v, ∃ u, c.squareMatrix u v ≠ 0)) := by
  have hForward : ∀ d (i : Fin n), Σ j, FinitePath A d i j := by
    classical
    intro d
    induction d with
    | zero => intro i; exact ⟨i, .nil i⟩
    | succ d ih =>
        intro i
        let j := Classical.choose (c.essentialA.1 i)
        have hj : A i j ≠ 0 := Classical.choose_spec (c.essentialA.1 i)
        obtain ⟨z, path⟩ := ih j
        exact ⟨z, .cons ⟨0, Nat.pos_of_ne_zero hj⟩ path⟩
  have hBackward : ∀ d (z : Fin k), Σ t, FinitePath B d t z := by
    classical
    intro d
    induction d with
    | zero => intro z; exact ⟨z, .nil z⟩
    | succ d ih =>
        intro z
        let j := Classical.choose (c.essentialB.2 z)
        have hj : B j z ≠ 0 := Classical.choose_spec (c.essentialB.2 z)
        obtain ⟨t, path⟩ := ih j
        exact ⟨t, appendPath path ⟨0, Nat.pos_of_ne_zero hj⟩⟩
  have hout : ∀ r : Edge R, ∃ sq : Square c, sq.initialR = r := by
    intro r
    obtain ⟨z, hz⟩ := c.essentialB.1 r.target
    let b : Edge B := ⟨r.target, z, ⟨0, Nat.pos_of_ne_zero hz⟩⟩
    exact ⟨c.outgoingSquare r b rfl,
      (square_lifts_left_forgetting c).2.1 r b rfl⟩
  have hin : ∀ r : Edge R, ∃ sq : Square c, sq.terminalR = r := by
    intro r
    obtain ⟨i, hi⟩ := c.essentialA.2 r.source
    let a : Edge A := ⟨i, r.source, ⟨0, Nat.pos_of_ne_zero hi⟩⟩
    exact ⟨c.incomingSquare a r rfl,
      (square_lifts_left_forgetting c).1 a r rfl⟩
  refine ⟨hout, hin, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, alpha⟩ := hForward m i
    let rs := (c.psiA i j).symm alpha
    exact ⟨⟨i, rs.1, rs.2.1⟩, rfl⟩
  · intro z
    obtain ⟨t, beta⟩ := hBackward m z
    let sr := (c.psiB t z).symm beta
    exact ⟨⟨sr.1, z, sr.2.2⟩, rfl⟩
  · constructor
    · intro u
      let e := Fintype.equivFin (Edge R)
      obtain ⟨sq, hsq⟩ := hout (e.symm u)
      refine ⟨e sq.terminalR, ?_⟩
      have hu : e sq.initialR = u := by
        rw [hsq]
        exact e.apply_symm_apply u
      have hnonempty : Nonempty
          {s : Square c // e s.initialR = u ∧
            e s.terminalR = e sq.terminalR} :=
        ⟨⟨sq, hu, rfl⟩⟩
      exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr hnonempty)
    · intro v
      let e := Fintype.equivFin (Edge R)
      obtain ⟨sq, hsq⟩ := hin (e.symm v)
      refine ⟨e sq.initialR, ?_⟩
      have hv : e sq.terminalR = v := by
        rw [hsq]
        exact e.apply_symm_apply v
      have hnonempty : Nonempty
          {s : Square c // e s.initialR = e sq.initialR ∧
            e s.terminalR = v} :=
        ⟨⟨sq, rfl, hv⟩⟩
      exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr hnonempty)

#print axioms square_graph_essential_and_projections

private def squareIncomingLift (c : CompatibleCertificate A B R S m) :
    IncomingLift A (Edge R) where
  project := Edge.source
  onto := (square_graph_essential_and_projections c).2.2.1
  lift := by
    intro a r
    exact c.incomingLift a r.val r.property.symm

private def squareOutgoingLift (c : CompatibleCertificate A B R S m) :
    IncomingLift B.transpose (Edge R) where
  project := Edge.target
  onto := (square_graph_essential_and_projections c).2.2.2.1
  lift := by
    intro b r
    exact c.outgoingLift r.val ⟨b.target, b.source, b.number⟩ r.property

private theorem squareOutgoingLift_path (c : CompatibleCertificate A B R S m) :
    ∀ {d : ℕ} {z t : Fin k} {i : Fin n}
      (beta : FinitePath B.transpose d z t) (r : Fin (R i t)),
      (c.squareOutgoingLift.liftPath beta
        ⟨(⟨i, t, r⟩ : Edge R), rfl⟩).val =
      (let lifted := c.liftOutgoingPath r
          (reverseFinitePath beta : FinitePath B d t z)
       (⟨lifted.1, z, lifted.2.2⟩ : Edge R)) := by
  intro d z t i beta
  induction beta generalizing i with
  | nil z =>
      intro r
      rfl
  | @cons d z u t b tail ih =>
      intro r
      let p : FinitePath B d t u := reverseFinitePath tail
      let prior := c.liftOutgoingPath r p
      have htail : c.squareOutgoingLift.liftPath tail
          ⟨(⟨i, t, r⟩ : Edge R), rfl⟩ =
          ⟨(⟨prior.1, u, prior.2.2⟩ : Edge R), rfl⟩ := by
        apply Subtype.ext
        exact ih r
      change (c.squareOutgoingLift.lift ⟨z, u, b⟩
          (c.squareOutgoingLift.liftPath tail
            ⟨(⟨i, t, r⟩ : Edge R), rfl⟩)).val =
        (let lifted := unsweep c.phi r (appendPath p b)
         (⟨lifted.1, z, lifted.2.2⟩ : Edge R))
      rw [htail]
      dsimp only
      rw [unsweep_append c.phi r p b]
      rfl

private theorem squareIncomingLift_path (c : CompatibleCertificate A B R S m) :
    ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)),
      (c.squareIncomingLift.liftPath alpha
        ⟨(⟨j, z, r⟩ : Edge R), rfl⟩).val =
      (let lifted := c.liftIncomingPath alpha r
       (⟨i, lifted.1, lifted.2⟩ : Edge R)) := by
  intro d i j z alpha
  induction alpha with
  | nil i =>
      intro r
      rfl
  | @cons d i j t a tail ih =>
      intro r
      have htail : c.squareIncomingLift.liftPath tail
          ⟨(⟨t, z, r⟩ : Edge R), rfl⟩ =
          ⟨(let rest := c.liftIncomingPath tail r
            (⟨j, rest.1, rest.2⟩ : Edge R)), rfl⟩ := by
        apply Subtype.ext
        exact ih r
      simp only [IncomingLift.liftPath, liftIncomingPath]
      rw [htail]
      rfl

private theorem squareIncomingLift_forgets_at_lag
    (c : CompatibleCertificate A B R S m) :
    c.squareIncomingLift.response m = Setoid.ker Edge.source := by
  apply Setoid.ext
  intro u v
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    rcases u with ⟨us, uz, ur⟩
    rcases v with ⟨vs, vz, vr⟩
    change us = vs at h
    subst vs
    change c.squareIncomingLift.responseReadout m
        (⟨us, uz, ur⟩ : Edge R) =
      c.squareIncomingLift.responseReadout m
        (⟨us, vz, vr⟩ : Edge R)
    unfold IncomingLift.responseReadout
    apply Prod.ext
    · rfl
    · funext i j alpha
      by_cases hj : us = j
      · cases hj
        have hsame :
            (c.squareIncomingLift.liftPath alpha
              ⟨(⟨us, uz, ur⟩ : Edge R), rfl⟩).val =
            (c.squareIncomingLift.liftPath alpha
              ⟨(⟨us, vz, vr⟩ : Edge R), rfl⟩).val := by
          calc
            _ = (let lifted := c.liftIncomingPath alpha ur
              (⟨i, lifted.1, lifted.2⟩ : Edge R)) :=
                c.squareIncomingLift_path alpha ur
            _ = (let rs := (c.psiA i us).symm alpha
              (⟨i, rs.1, rs.2.1⟩ : Edge R)) :=
                (square_lifts_left_forgetting c).2.2 alpha ur
            _ = (let lifted := c.liftIncomingPath alpha vr
              (⟨i, lifted.1, lifted.2⟩ : Edge R)) :=
                ((square_lifts_left_forgetting c).2.2 alpha vr).symm
            _ = _ := (c.squareIncomingLift_path alpha vr).symm
        simpa [squareIncomingLift] using congrArg some hsame
      · simp [squareIncomingLift, hj]

private theorem squareOutgoingLift_forgets_at_lag
    (c : CompatibleCertificate A B R S m) :
    c.squareOutgoingLift.response m = Setoid.ker Edge.target := by
  apply Setoid.ext
  intro u v
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    rcases u with ⟨ui, ut, ur⟩
    rcases v with ⟨vi, vt, vr⟩
    change ut = vt at h
    subst vt
    change c.squareOutgoingLift.responseReadout m
        (⟨ui, ut, ur⟩ : Edge R) =
      c.squareOutgoingLift.responseReadout m
        (⟨vi, ut, vr⟩ : Edge R)
    unfold IncomingLift.responseReadout
    apply Prod.ext
    · rfl
    · funext i j alpha
      by_cases hj : ut = j
      · cases hj
        have hsame :
            (c.squareOutgoingLift.liftPath alpha
              ⟨(⟨ui, ut, ur⟩ : Edge R), rfl⟩).val =
            (c.squareOutgoingLift.liftPath alpha
              ⟨(⟨vi, ut, vr⟩ : Edge R), rfl⟩).val := by
          let beta : FinitePath B m ut i := reverseFinitePath alpha
          calc
            _ = (let lifted := c.liftOutgoingPath ur beta
              (⟨lifted.1, i, lifted.2.2⟩ : Edge R)) :=
                c.squareOutgoingLift_path alpha ur
            _ = (let sr := (c.psiB ut i).symm beta
              (⟨sr.1, i, sr.2.2⟩ : Edge R)) :=
                square_lifts_right_forgetting c ur beta
            _ = (let lifted := c.liftOutgoingPath vr beta
              (⟨lifted.1, i, lifted.2.2⟩ : Edge R)) :=
                (square_lifts_right_forgetting c vr beta).symm
            _ = _ := (c.squareOutgoingLift_path alpha vr).symm
        simpa [squareOutgoingLift] using congrArg some hsame
      · simp [squareOutgoingLift, hj]

/-- A column counts the numbered A edges whose incoming square lift reaches
    its row edge. The proof reconstructs each square from that A edge and its
    terminal R edge, so parallel edges are not collapsed. -/
theorem square_column_lift_count (c : CompatibleCertificate A B R S m)
    (r s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) =
      Nat.card {a : Edge A //
        ∃ h : a.target = r.source, (c.incomingLift a r h).val = s} := by
  classical
  let e := Fintype.equivFin (Edge R)
  let fiber := {sq : Square c // e sq.initialR = e s ∧ e sq.terminalR = e r}
  let incidence := {a : Edge A //
    ∃ h : a.target = r.source, (c.incomingLift a r h).val = s}
  have reconstruct (sq : Square c) :
      c.incomingSquare sq.leftA sq.terminalR rfl = sq := by
    apply (squareCoordinates c).injective
    rcases sq with ⟨i, z, ⟨j, a, edge⟩, output, commutes⟩
    rfl
  let toIncidence : fiber → incidence := fun p =>
    ⟨p.val.leftA, by
    rcases p with ⟨sq, ⟨hs, hr⟩⟩
    have hs' : sq.initialR = s := e.injective hs
    have hr' : sq.terminalR = r := e.injective hr
    have h : sq.leftA.target = r.source := by
      simpa [Square.leftA, Square.terminalR] using congrArg Edge.source hr'
    refine ⟨h, ?_⟩
    subst r
    have hLift := congrArg Square.initialR (reconstruct sq)
    change (c.incomingLift sq.leftA sq.terminalR rfl).val =
      sq.initialR at hLift
    exact hLift.trans hs'⟩
  have injective : Function.Injective toIncidence := by
    intro p q hpq
    apply Subtype.ext
    have ha := congrArg Subtype.val hpq
    change p.val.leftA = q.val.leftA at ha
    have hrp : p.val.terminalR = r := e.injective p.property.2
    have hrq : q.val.terminalR = r := e.injective q.property.2
    have hr : p.val.terminalR = q.val.terminalR := hrp.trans hrq.symm
    calc
      p.val = c.incomingSquare p.val.leftA p.val.terminalR rfl :=
        (reconstruct p.val).symm
      _ = c.incomingSquare q.val.leftA q.val.terminalR rfl := by
        simpa only [ha, hr]
      _ = q.val := reconstruct q.val
  have surjective : Function.Surjective toIncidence := by
    rintro ⟨a, ⟨h, hlift⟩⟩
    let sq := c.incomingSquare a r h
    have hstart : sq.initialR = s := by
      change (c.incomingLift a r h).val = s at hlift
      exact hlift
    have hterminal : sq.terminalR = r :=
      (square_lifts_left_forgetting c).1 a r h
    have hleft : sq.leftA = a := by
      rcases a with ⟨i, j, number⟩
      rcases r with ⟨j', z, edge⟩
      cases h
      rfl
    refine ⟨⟨sq, congrArg e hstart, congrArg e hterminal⟩, ?_⟩
    apply Subtype.ext
    exact hleft
  have hcard : Nat.card fiber = Nat.card incidence :=
    Nat.card_congr (Equiv.ofBijective toIncidence ⟨injective, surjective⟩)
  have hnumber := Fintype.card_congr (c.squareFiberEquiv (e s) (e r))
  calc
    c.squareMatrix (e s) (e r) = Fintype.card fiber := by
      simpa only [Fintype.card_fin] using hnumber
    _ = Nat.card fiber := (Nat.card_eq_fintype_card (α := fiber)).symm
    _ = Nat.card incidence := hcard

/-- A row counts the numbered B edges whose outgoing square lift reaches
    its column edge. The inverse phi square is reconstructed from its B edge
    and initial R edge. -/
theorem square_row_lift_count (c : CompatibleCertificate A B R S m)
    (r s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) =
      Nat.card {b : Edge B //
        ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s} := by
  classical
  let e := Fintype.equivFin (Edge R)
  let fiber := {sq : Square c // e sq.initialR = e r ∧ e sq.terminalR = e s}
  let incidence := {b : Edge B //
    ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s}
  have reconstruct (sq : Square c) :
      c.outgoingSquare sq.initialR sq.rightB rfl = sq := by
    apply (squareCoordinates c).injective
    rcases sq with ⟨i, z, input, ⟨t, edge, b⟩, commutes⟩
    have hinput : (c.phi i z).symm ⟨t, edge, b⟩ = input := by
      rw [← commutes]
      exact (c.phi i z).symm_apply_apply input
    dsimp only [squareCoordinates, outgoingSquare, Square.initialR, Square.rightB]
    exact congrArg (fun p : EdgePair A R i z =>
      (⟨i, z, p⟩ : Σ i : Fin n, Σ z : Fin k, EdgePair A R i z)) hinput
  let toIncidence : fiber → incidence := fun p =>
    ⟨p.val.rightB, by
    rcases p with ⟨sq, ⟨hr, hs⟩⟩
    have hr' : sq.initialR = r := e.injective hr
    have hs' : sq.terminalR = s := e.injective hs
    have h : r.target = sq.rightB.source := by
      simpa [Square.initialR, Square.rightB] using (congrArg Edge.target hr').symm
    refine ⟨h, ?_⟩
    subst r
    have hLift := congrArg Square.terminalR (reconstruct sq)
    change (c.outgoingLift sq.initialR sq.rightB rfl).val =
      sq.terminalR at hLift
    exact hLift.trans hs'⟩
  have injective : Function.Injective toIncidence := by
    intro p q hpq
    apply Subtype.ext
    have hb := congrArg Subtype.val hpq
    change p.val.rightB = q.val.rightB at hb
    have hrp : p.val.initialR = r := e.injective p.property.1
    have hrq : q.val.initialR = r := e.injective q.property.1
    have hr : p.val.initialR = q.val.initialR := hrp.trans hrq.symm
    calc
      p.val = c.outgoingSquare p.val.initialR p.val.rightB rfl :=
        (reconstruct p.val).symm
      _ = c.outgoingSquare q.val.initialR q.val.rightB rfl := by
        simpa only [hr, hb]
      _ = q.val := reconstruct q.val
  have surjective : Function.Surjective toIncidence := by
    rintro ⟨b, ⟨h, hlift⟩⟩
    let sq := c.outgoingSquare r b h
    have hstart : sq.initialR = r :=
      (square_lifts_left_forgetting c).2.1 r b h
    have hterminal : sq.terminalR = s := by
      change (c.outgoingLift r b h).val = s at hlift
      exact hlift
    have hright : sq.rightB = b := by
      rcases r with ⟨i, t, edge⟩
      rcases b with ⟨t', z, number⟩
      cases h
      rfl
    refine ⟨⟨sq, congrArg e hstart, congrArg e hterminal⟩, ?_⟩
    apply Subtype.ext
    exact hright
  have hcard : Nat.card fiber = Nat.card incidence :=
    Nat.card_congr (Equiv.ofBijective toIncidence ⟨injective, surjective⟩)
  have hnumber := Fintype.card_congr (c.squareFiberEquiv (e r) (e s))
  calc
    c.squareMatrix (e r) (e s) = Fintype.card fiber := by
      simpa only [Fintype.card_fin] using hnumber
    _ = Nat.card fiber := (Nat.card_eq_fintype_card (α := fiber)).symm
    _ = Nat.card incidence := hcard

#print axioms square_column_lift_count
#print axioms square_row_lift_count

private theorem square_first_column_invariance
    (c : CompatibleCertificate A B R S m) {r v : Edge R}
    (h : c.squareIncomingLift.response 1 r v) (s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) =
      c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) v) := by
  classical
  have hp : r.source = v.source := congrArg Prod.fst h
  have hstep {x y : Edge R} (hxy : c.squareIncomingLift.response 1 x y)
      (a : Edge A) (hx : a.target = x.source) (hy : a.target = y.source) :
      (c.incomingLift a x hx).val = (c.incomingLift a y hy).val := by
    have hzero := incoming_response_step c.squareIncomingLift 0 hxy a
      hx.symm hy.symm
    rw [(response_zero_and_step c.squareIncomingLift).1] at hzero
    exact hzero
  have hpred (a : Edge A) :
      (∃ ha : a.target = r.source, (c.incomingLift a r ha).val = s) ↔
      (∃ hb : a.target = v.source, (c.incomingLift a v hb).val = s) := by
    constructor
    · rintro ⟨ha, hs⟩
      let hb : a.target = v.source := ha.trans hp
      exact ⟨hb, (hstep h a ha hb).symm.trans hs⟩
    · rintro ⟨hb, hs⟩
      let ha : a.target = r.source := hb.trans hp.symm
      exact ⟨ha,
        (hstep ((c.squareIncomingLift.response 1).iseqv.symm h)
          a hb ha).symm.trans hs⟩
  let leftFiber := {a : Edge A //
    ∃ ha : a.target = r.source, (c.incomingLift a r ha).val = s}
  let rightFiber := {a : Edge A //
    ∃ hb : a.target = v.source, (c.incomingLift a v hb).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => ⟨x.val, (hpred x.val).mp x.property⟩
    invFun := fun x => ⟨x.val, (hpred x.val).mpr x.property⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) = Nat.card leftFiber :=
          c.square_column_lift_count r s
    _ = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) s)
          ((Fintype.equivFin (Edge R)) v) :=
            (c.square_column_lift_count v s).symm

private theorem square_first_row_invariance
    (c : CompatibleCertificate A B R S m) {r v : Edge R}
    (h : c.squareOutgoingLift.response 1 r v) (s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) =
      c.squareMatrix ((Fintype.equivFin (Edge R)) v)
        ((Fintype.equivFin (Edge R)) s) := by
  classical
  have hp : r.target = v.target := congrArg Prod.fst h
  have hstep {x y : Edge R} (hxy : c.squareOutgoingLift.response 1 x y)
      (b : Edge B) (hx : x.target = b.source) (hy : y.target = b.source) :
      (c.outgoingLift x b hx).val = (c.outgoingLift y b hy).val := by
    have hzero := incoming_response_step c.squareOutgoingLift 0 hxy
      (⟨b.target, b.source, b.number⟩ : Edge B.transpose) hx hy
    rw [(response_zero_and_step c.squareOutgoingLift).1] at hzero
    exact hzero
  have hpred (b : Edge B) :
      (∃ hr : r.target = b.source, (c.outgoingLift r b hr).val = s) ↔
      (∃ hv : v.target = b.source, (c.outgoingLift v b hv).val = s) := by
    constructor
    · rintro ⟨hr, hs⟩
      let hv : v.target = b.source := hp.symm.trans hr
      exact ⟨hv, (hstep h b hr hv).symm.trans hs⟩
    · rintro ⟨hv, hs⟩
      let hr : r.target = b.source := hp.trans hv
      exact ⟨hr,
        (hstep ((c.squareOutgoingLift.response 1).iseqv.symm h)
          b hv hr).symm.trans hs⟩
  let leftFiber := {b : Edge B //
    ∃ hr : r.target = b.source, (c.outgoingLift r b hr).val = s}
  let rightFiber := {b : Edge B //
    ∃ hv : v.target = b.source, (c.outgoingLift v b hv).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => ⟨x.val, (hpred x.val).mp x.property⟩
    invFun := fun x => ⟨x.val, (hpred x.val).mpr x.property⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) = Nat.card leftFiber :=
          c.square_row_lift_count r s
    _ = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) v)
          ((Fintype.equivFin (Edge R)) s) :=
            (c.square_row_lift_count v s).symm

private theorem square_left_zero_fiber_count
    (c : CompatibleCertificate A B R S m) (r s : Edge R) :
    Nat.card (incomingResponseFiber c.squareIncomingLift 0
      (Quotient.mk (c.squareIncomingLift.response 0) s) r) =
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
      ((Fintype.equivFin (Edge R)) r) := by
  classical
  let L := c.squareIncomingLift
  let leftFiber := incomingResponseFiber L 0
    (Quotient.mk (L.response 0) s) r
  let rightFiber := {a : Edge A //
    ∃ h : a.target = r.source, (c.incomingLift a r h).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => by
      let a := x.val
      let hv := Classical.choose x.property
      have hclass := Classical.choose_spec x.property
      have heq : (c.incomingLift a r hv.symm).val = s := by
        change (L.lift a ⟨r, hv⟩).val = s
        have hrel : (L.response 0).r (L.lift a ⟨r, hv⟩).val s :=
          Quotient.exact hclass
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) =>
            T.r (L.lift a ⟨r, hv⟩).val s) (response_zero_and_step L).1)
          hrel
      exact ⟨a, ⟨hv.symm, heq⟩⟩
    invFun := fun x => by
      let a := x.val
      let h := Classical.choose x.property
      have heq := Classical.choose_spec x.property
      refine ⟨a, ⟨h.symm, Quotient.sound ?_⟩⟩
      rw [(response_zero_and_step L).1]
      exact heq
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    Nat.card leftFiber = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) s)
          ((Fintype.equivFin (Edge R)) r) :=
            (c.square_column_lift_count r s).symm

private theorem square_right_zero_fiber_count
    (c : CompatibleCertificate A B R S m) (r s : Edge R) :
    Nat.card (incomingResponseFiber c.squareOutgoingLift 0
      (Quotient.mk (c.squareOutgoingLift.response 0) s) r) =
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
      ((Fintype.equivFin (Edge R)) s) := by
  classical
  let L := c.squareOutgoingLift
  let flip : Edge B.transpose ≃ Edge B := {
    toFun := fun a => ⟨a.target, a.source, a.number⟩
    invFun := fun b => ⟨b.target, b.source, b.number⟩
    left_inv := by intro a; cases a; rfl
    right_inv := by intro b; cases b; rfl }
  let leftFiber := incomingResponseFiber L 0
    (Quotient.mk (L.response 0) s) r
  let rightFiber := {b : Edge B //
    ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => by
      let b := flip x.val
      let hv := Classical.choose x.property
      have hclass := Classical.choose_spec x.property
      have heq : (c.outgoingLift r b hv).val = s := by
        change (L.lift x.val ⟨r, hv⟩).val = s
        have hrel : (L.response 0).r (L.lift x.val ⟨r, hv⟩).val s :=
          Quotient.exact hclass
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) =>
            T.r (L.lift x.val ⟨r, hv⟩).val s) (response_zero_and_step L).1)
          hrel
      exact ⟨b, ⟨hv, heq⟩⟩
    invFun := fun x => by
      let b := x.val
      let h := Classical.choose x.property
      have heq := Classical.choose_spec x.property
      refine ⟨flip.symm b, ⟨h, Quotient.sound ?_⟩⟩
      rw [(response_zero_and_step L).1]
      exact heq
    left_inv := by
      intro x
      apply Subtype.ext
      exact flip.symm_apply_apply x.val
    right_inv := by
      intro x
      apply Subtype.ext
      exact flip.apply_symm_apply x.val }
  calc
    Nat.card leftFiber = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) r)
          ((Fintype.equivFin (Edge R)) s) :=
            (c.square_row_lift_count r s).symm

private noncomputable def firstLeftClass
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))] :
    Fin (Fintype.card (Edge R)) →
      Fin (Fintype.card (Quotient (c.squareIncomingLift.response 1))) := by
  classical
  exact fun u => (Fintype.equivFin _)
    (Quotient.mk _ ((Fintype.equivFin (Edge R)).symm u))

private noncomputable def firstRightClass
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    Fin (Fintype.card (Edge R)) →
      Fin (Fintype.card (Quotient (c.squareOutgoingLift.response 1))) := by
  classical
  exact fun u => (Fintype.equivFin _)
    (Quotient.mk _ ((Fintype.equivFin (Edge R)).symm u))

private noncomputable def firstLeftRep
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))] :
    Fin (Fintype.card (Quotient (c.squareIncomingLift.response 1))) →
      Fin (Fintype.card (Edge R)) := by
  classical
  exact fun f => (Fintype.equivFin (Edge R))
    (Quotient.out ((Fintype.equivFin _).symm f))

private noncomputable def firstRightRep
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    Fin (Fintype.card (Quotient (c.squareOutgoingLift.response 1))) →
      Fin (Fintype.card (Edge R)) := by
  classical
  exact fun f => (Fintype.equivFin (Edge R))
    (Quotient.out ((Fintype.equivFin _).symm f))

private theorem square_left_first_matrix
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))]
    (f g : Fin (Fintype.card
      (Quotient (c.squareIncomingLift.response 1)))) :
    incomingResponseMatrix c.squareIncomingLift 1
        ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
      (FirstResponseDiamond.columnMembership c.firstLeftClass *
        c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep)
        f g := by
  classical
  let L := c.squareIncomingLift
  let e := Fintype.equivFin (Edge R)
  let eL := Fintype.equivFin (Quotient (L.response 1))
  let e0 : Edge R ≃ Quotient (L.response 0) :=
    Equiv.ofBijective (fun r => Quotient.mk (L.response 0) r) (by
      constructor
      · intro r s hrs
        have hrel := Quotient.exact hrs
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) => T.r r s)
            (response_zero_and_step L).1) hrel
      · intro F
        exact ⟨Quotient.out F, Quotient.out_eq F⟩)
  have hfiber (r : Edge R) :
      incomingResponseU L 0 (e0 r) (eL.symm g) =
        c.squareMatrix (e r) (c.firstLeftRep g) := by
    change Nat.card (incomingResponseFiber L 0
      (Quotient.mk (L.response 0) r) (Quotient.out (eL.symm g))) = _
    simpa [firstLeftRep, e, eL] using
      c.square_left_zero_fiber_count (Quotient.out (eL.symm g)) r
  have hclass (r : Edge R) :
      incomingResponseV L 0 (eL.symm f) (e0 r) =
        FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) := by
    have hprojection : incomingResponseProjection L 0 (e0 r) =
        Quotient.mk (L.response 1) r := rfl
    have hclass_eq : c.firstLeftClass (e r) =
        eL (Quotient.mk (L.response 1) r) := by
      change eL (Quotient.mk (L.response 1) (e.symm (e r))) =
        eL (Quotient.mk (L.response 1) r)
      rw [e.symm_apply_apply]
    change (if incomingResponseProjection L 0 (e0 r) = eL.symm f
      then 1 else 0) = (if c.firstLeftClass (e r) = f then 1 else 0)
    rw [hprojection, hclass_eq]
    by_cases h : f = eL (Quotient.mk (L.response 1) r)
    · subst f
      simp
    · have hne : Quotient.mk (L.response 1) r ≠ eL.symm f := by
        intro hk
        apply h
        calc
          f = eL (eL.symm f) := (eL.apply_symm_apply f).symm
          _ = eL (Quotient.mk (L.response 1) r) := congrArg eL hk.symm
      simp [h, hne, eq_comm]
  calc
    incomingResponseMatrix L 1 (eL.symm f) (eL.symm g) =
        (incomingResponseV L 0 * incomingResponseU L 0)
          (eL.symm f) (eL.symm g) := by
            rw [incoming_response_matrix_factor_step L 0]
    _ = ∑ r : Edge R,
          FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) *
            c.squareMatrix (e r) (c.firstLeftRep g) := by
        rw [Matrix.mul_apply]
        exact (Fintype.sum_equiv e0 _ _ (fun r => by
          rw [hclass r, hfiber r])).symm
    _ = (FirstResponseDiamond.columnMembership c.firstLeftClass *
          c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep)
          f g := by
        have hsum :
            (∑ r : Edge R,
              FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) *
                c.squareMatrix (e r) (c.firstLeftRep g)) =
            ∑ u : Fin (Fintype.card (Edge R)),
              FirstResponseDiamond.columnMembership c.firstLeftClass f u *
                c.squareMatrix u (c.firstLeftRep g) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
        rw [hsum]
        simp only [Matrix.mul_apply, FirstResponseDiamond.columnSelector]
        simp

private theorem square_right_first_matrix
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))]
    (f g : Fin (Fintype.card
      (Quotient (c.squareOutgoingLift.response 1)))) :
    incomingResponseMatrix c.squareOutgoingLift 1
        ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
      (FirstResponseDiamond.rowSelector c.firstRightRep *
        c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass)
        g f := by
  classical
  let L := c.squareOutgoingLift
  let e := Fintype.equivFin (Edge R)
  let eR := Fintype.equivFin (Quotient (L.response 1))
  let e0 : Edge R ≃ Quotient (L.response 0) :=
    Equiv.ofBijective (fun r => Quotient.mk (L.response 0) r) (by
      constructor
      · intro r s hrs
        have hrel := Quotient.exact hrs
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) => T.r r s)
            (response_zero_and_step L).1) hrel
      · intro F
        exact ⟨Quotient.out F, Quotient.out_eq F⟩)
  have hfiber (r : Edge R) :
      incomingResponseU L 0 (e0 r) (eR.symm g) =
        c.squareMatrix (c.firstRightRep g) (e r) := by
    change Nat.card (incomingResponseFiber L 0
      (Quotient.mk (L.response 0) r) (Quotient.out (eR.symm g))) = _
    simpa [firstRightRep, e, eR] using
      c.square_right_zero_fiber_count (Quotient.out (eR.symm g)) r
  have hclass (r : Edge R) :
      incomingResponseV L 0 (eR.symm f) (e0 r) =
        FirstResponseDiamond.rowMembership c.firstRightClass (e r) f := by
    have hprojection : incomingResponseProjection L 0 (e0 r) =
        Quotient.mk (L.response 1) r := rfl
    have hclass_eq : c.firstRightClass (e r) =
        eR (Quotient.mk (L.response 1) r) := by
      change eR (Quotient.mk (L.response 1) (e.symm (e r))) =
        eR (Quotient.mk (L.response 1) r)
      rw [e.symm_apply_apply]
    change (if incomingResponseProjection L 0 (e0 r) = eR.symm f
      then 1 else 0) = (if c.firstRightClass (e r) = f then 1 else 0)
    rw [hprojection, hclass_eq]
    by_cases h : f = eR (Quotient.mk (L.response 1) r)
    · subst f
      simp
    · have hne : Quotient.mk (L.response 1) r ≠ eR.symm f := by
        intro hk
        apply h
        calc
          f = eR (eR.symm f) := (eR.apply_symm_apply f).symm
          _ = eR (Quotient.mk (L.response 1) r) := congrArg eR hk.symm
      simp [h, hne, eq_comm]
  calc
    incomingResponseMatrix L 1 (eR.symm f) (eR.symm g) =
        (incomingResponseV L 0 * incomingResponseU L 0)
          (eR.symm f) (eR.symm g) := by
            rw [incoming_response_matrix_factor_step L 0]
    _ = ∑ r : Edge R,
          FirstResponseDiamond.rowMembership c.firstRightClass (e r) f *
            c.squareMatrix (c.firstRightRep g) (e r) := by
        rw [Matrix.mul_apply]
        exact (Fintype.sum_equiv e0 _ _ (fun r => by
          rw [hclass r, hfiber r])).symm
    _ = (FirstResponseDiamond.rowSelector c.firstRightRep *
          c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass)
          g f := by
        have hsum :
            (∑ r : Edge R,
              FirstResponseDiamond.rowMembership c.firstRightClass (e r) f *
                c.squareMatrix (c.firstRightRep g) (e r)) =
            ∑ u : Fin (Fintype.card (Edge R)),
              c.squareMatrix (c.firstRightRep g) u *
                FirstResponseDiamond.rowMembership c.firstRightClass u f := by
          calc
            _ = ∑ u : Fin (Fintype.card (Edge R)),
                  FirstResponseDiamond.rowMembership c.firstRightClass u f *
                    c.squareMatrix (c.firstRightRep g) u :=
              Fintype.sum_equiv e _ _ (fun _ => rfl)
            _ = _ := by
              apply Finset.sum_congr rfl
              intro u _
              exact Nat.mul_comm _ _
        rw [hsum]
        simp [Matrix.mul_apply, FirstResponseDiamond.rowSelector]

private theorem square_first_diamond
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))]
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    let IL := FirstResponseDiamond.columnMembership c.firstLeftClass
    let IJ := FirstResponseDiamond.rowMembership c.firstRightClass
    let SL := FirstResponseDiamond.columnSelector c.firstLeftRep
    let SJ := FirstResponseDiamond.rowSelector c.firstRightRep
    ∃ D : CountMat
        (Fintype.card (Quotient (c.squareOutgoingLift.response 1)))
        (Fintype.card (Quotient (c.squareIncomingLift.response 1))),
      IL * c.squareMatrix * SL = (IL * IJ) * D ∧
      SJ * c.squareMatrix * IJ = D * (IL * IJ) ∧
      Nonempty (ExchangeChain ℕ
        (IL * c.squareMatrix * SL)
        (SJ * c.squareMatrix * IJ) 1) := by
  classical
  let e := Fintype.equivFin (Edge R)
  let eL := Fintype.equivFin (Quotient (c.squareIncomingLift.response 1))
  let eR := Fintype.equivFin (Quotient (c.squareOutgoingLift.response 1))
  have hleftRep (f) : c.firstLeftClass (c.firstLeftRep f) = f := by
    simp [firstLeftClass, firstLeftRep, e, eL]
  have hrightRep (f) : c.firstRightClass (c.firstRightRep f) = f := by
    simp [firstRightClass, firstRightRep, e, eR]
  have hcolumns (u v) (h : c.firstLeftClass u = c.firstLeftClass v)
      (i) : c.squareMatrix i u = c.squareMatrix i v := by
    have hq : Quotient.mk (c.squareIncomingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareIncomingLift.response 1) (e.symm v) := by
      exact eL.injective h
    have hrel : c.squareIncomingLift.response 1 (e.symm u) (e.symm v) :=
      Quotient.exact hq
    simpa [e] using
      c.square_first_column_invariance hrel (e.symm i)
  have hrows (u v) (h : c.firstRightClass u = c.firstRightClass v)
      (i) : c.squareMatrix u i = c.squareMatrix v i := by
    have hq : Quotient.mk (c.squareOutgoingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareOutgoingLift.response 1) (e.symm v) := by
      exact eR.injective h
    have hrel : c.squareOutgoingLift.response 1 (e.symm u) (e.symm v) :=
      Quotient.exact hq
    simpa [e] using
      c.square_first_row_invariance hrel (e.symm i)
  obtain ⟨D, hleft, hright, chain⟩ :=
    FirstResponseDiamond.first_response_diamond c.squareMatrix
      c.firstLeftClass c.firstRightClass c.firstLeftRep c.firstRightRep
      hleftRep hrightRep hcolumns hrows
  exact ⟨D, hleft, hright, chain⟩

private theorem square_exchange_chain_ge_two
    (c : CompatibleCertificate A B R S m) (hm : 2 ≤ m) :
    Nonempty (ExchangeChain ℕ A B (2 * m - 1)) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    change incomingResponseMatrix L 1
      ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
        Cleft f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    change incomingResponseMatrix K 1
      ((Fintype.equivFin _).symm g) ((Fintype.equivFin _).symm f) =
        Cright f g
    exact c.square_right_first_matrix g f
  let d := 1 + (m - 2) + 1
  have hd : d = m := by dsimp [d]; omega
  have hleftForget : L.response d = Setoid.ker Edge.source := by
    rw [hd]
    exact c.squareIncomingLift_forgets_at_lag
  have hrightForget : K.response d = Setoid.ker Edge.target := by
    rw [hd]
    exact c.squareOutgoingLift_forgets_at_lag
  obtain ⟨eA, hA⟩ := response_matrix_forgetting_reindexed L d hleftForget
  obtain ⟨eB, hB⟩ := response_matrix_forgetting_reindexed K d hrightForget
  have left : ExchangeChain ℕ A Cleft ((m - 2) + 1) := by
    have chain := finite_response_chain_to L 1 (m - 2) eA
    rw [hleftFirst, hA] at chain
    exact exchange_chain_reverse chain
  have right : ExchangeChain ℕ Cright B ((m - 2) + 1) := by
    have chain := finite_response_chain_to K 1 (m - 2) eB
    rw [hB] at chain
    have transposed := exchange_chain_transpose chain
    simpa only [hrightFirst, Matrix.transpose_transpose] using transposed
  obtain ⟨_, _, _, ⟨middle⟩⟩ := c.square_first_diamond
  have assembled := exchange_chain_trans (exchange_chain_trans left middle) right
  refine ⟨?_⟩
  convert assembled using 1 <;> omega

private theorem square_exchange_chain_one
    (c : CompatibleCertificate A B R S 1) :
    Nonempty (ExchangeChain ℕ A B 1) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    change incomingResponseMatrix L 1
      ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
        Cleft f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    change incomingResponseMatrix K 1
      ((Fintype.equivFin _).symm g) ((Fintype.equivFin _).symm f) =
        Cright f g
    exact c.square_right_first_matrix g f
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
  obtain ⟨D, hcol, hrow, _⟩ := c.square_first_diamond
  let P := FirstResponseDiamond.columnMembership c.firstLeftClass *
    FirstResponseDiamond.rowMembership c.firstRightClass
  let P' := Matrix.reindex eLeft eRight P
  let D' := Matrix.reindex eRight eLeft D
  have hprodA : A = P' * D' := by
    calc
      A = Matrix.reindex eLeft eLeft Cleft := hleftReindex.symm
      _ = Matrix.reindex eLeft eLeft (P * D) :=
        congrArg (Matrix.reindex eLeft eLeft) hcol
      _ = P' * D' := by
        change (P * D).submatrix eLeft.symm eLeft.symm =
          P.submatrix eLeft.symm eRight.symm *
            D.submatrix eRight.symm eLeft.symm
        exact (Matrix.submatrix_mul_equiv P D eLeft.symm eRight.symm eLeft.symm).symm
  have hprodB : B = D' * P' := by
    calc
      B = Matrix.reindex eRight eRight Cright := hrightReindex.symm
      _ = Matrix.reindex eRight eRight (D * P) :=
        congrArg (Matrix.reindex eRight eRight) hrow
      _ = D' * P' := by
        change (D * P).submatrix eRight.symm eRight.symm =
          D.submatrix eRight.symm eLeft.symm *
            P.submatrix eLeft.symm eRight.symm
        exact (Matrix.submatrix_mul_equiv D P eRight.symm eLeft.symm eRight.symm).symm
  rw [hprodA, hprodB]
  exact ⟨ExchangeChain.cons P' D' (ExchangeChain.nil _)⟩

/-- A compatible numbered certificate produces a strong-shift-equivalence
    chain with a linear length bound from its positive lag. -/
theorem compatible_exchange_chain_bound
    (c : CompatibleCertificate A B R S m) :
    Nonempty (ExchangeChain ℕ A B (2 * m - 1)) := by
  by_cases h : m = 1
  · subst m
    simpa using c.square_exchange_chain_one
  · have hm : 2 ≤ m := by
      have hpos := c.positiveLag
      omega
    exact c.square_exchange_chain_ge_two hm

#print axioms compatible_exchange_chain_bound

end CompatibleCertificate

end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
