/- GID: D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CompatibleResponseForgetting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compatible numbered path certificate constructs square lifts whose left boundary forgets after its lag.
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

end CompatibleCertificate

end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
