/- GID: D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.
-/

import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

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
      simp [sweep, unsweep, ih r]

def appendPath {k : ℕ} {B : CountMat k k} :
    {d : ℕ} → {i j z : Fin k} →
      FinitePath B d i j → Fin (B j z) → FinitePath B (d + 1) i z
  | _, _, _, z, .nil _, b => .cons b (.nil z)
  | _, _, _, _, .cons a tail, b => .cons a (appendPath tail b)

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

private def edgeCoordinates : Edge R ≃
    Σ i : Fin n, Σ z : Fin k, Fin (R i z) where
  toFun r := ⟨r.source, r.target, r.number⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by intro r; cases r; rfl
  right_inv := by intro p; rcases p with ⟨i, z, number⟩; rfl

noncomputable instance : Fintype (Edge R) := by
  classical
  exact Fintype.ofEquiv _ (edgeCoordinates (R := R)).symm

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
  exact Fintype.ofEquiv _ (squareCoordinates c).symm

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
          simp only [liftIncomingPath, sweep, ih r, incomingSquare] <;> rfl
    intro i j z alpha r
    rw [hbridge alpha r, c.compatible alpha r]
    rfl

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
  have hsweep : sweep c.phi alpha sr.2.2 = ⟨t, r, beta⟩ := by
    rw [c.compatible]
    simp [alpha, sr]
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
  have hForward : ∀ d (i : Fin n), ∃ j, FinitePath A d i j := by
    intro d
    induction d with
    | zero => intro i; exact ⟨i, .nil i⟩
    | succ d ih =>
        intro i
        obtain ⟨j, hj⟩ := c.essentialA.1 i
        obtain ⟨z, path⟩ := ih j
        exact ⟨z, .cons ⟨0, Nat.pos_of_ne_zero hj⟩ path⟩
  have hBackward : ∀ d (z : Fin k), ∃ t, FinitePath B d t z := by
    intro d
    induction d with
    | zero => intro z; exact ⟨z, .nil z⟩
    | succ d ih =>
        intro z
        obtain ⟨j, hj⟩ := c.essentialB.2 z
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

end CompatibleCertificate

end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
