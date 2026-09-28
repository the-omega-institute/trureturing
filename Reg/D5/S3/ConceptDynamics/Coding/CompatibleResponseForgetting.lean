import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

def identityMatrix (q : ℕ) : CountMat q q := fun i j => if i = j then 1 else 0

theorem identity_edge {q : ℕ} {i j : Fin q}
    (a : Fin (identityMatrix q i j)) : i = j := by
  by_contra h
  have := a.isLt
  simp [identityMatrix, h] at this

def identityNumber {q : ℕ} (i : Fin q) : Fin (identityMatrix q i i) :=
  ⟨0, by simp [identityMatrix]⟩

def rightIdentityPath {q : ℕ} (M : CountMat q q) (i j : Fin q) :
    EdgePair M (identityMatrix q) i j ≃ FinitePath M 1 i j where
  toFun := fun ⟨t, a, b⟩ => by
    have h := identity_edge b
    subst t
    exact .cons a (.nil j)
  invFun := fun p => by
    cases p with
    | cons a tail =>
      cases tail
      exact ⟨j, a, identityNumber j⟩
  left_inv := by
    rintro ⟨t, a, b⟩
    have h := identity_edge b
    subst t
    have hb : b = identityNumber j := by
      apply Fin.ext
      have hb := b.isLt
      simp only [identityMatrix, if_pos rfl] at hb
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    subst b
    rfl
  right_inv := by
    intro p
    cases p with
    | cons a tail => cases tail; rfl

def leftIdentityPath {q : ℕ} (M : CountMat q q) (i j : Fin q) :
    EdgePair (identityMatrix q) M i j ≃ FinitePath M 1 i j where
  toFun := fun ⟨t, a, b⟩ => by
    have h := identity_edge a
    subst t
    exact .cons b (.nil j)
  invFun := fun p => by
    cases p with
    | cons a tail =>
      cases tail
      exact ⟨i, identityNumber i, a⟩
  left_inv := by
    rintro ⟨t, a, b⟩
    have h := identity_edge a
    subst t
    have ha : a = identityNumber i := by
      apply Fin.ext
      have ha := a.isLt
      simp only [identityMatrix, if_pos rfl] at ha
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    subst a
    rfl
  right_inv := by
    intro p
    cases p with
    | cons a tail => cases tail; rfl

/-- The numbered lag-one certificate shared by all certificate audit clients. -/
def lagOneCertificate {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0)) :
    CompatibleCertificate M M M (identityMatrix q) 1 where
  positiveLag := Nat.zero_lt_one
  essentialA := essential
  essentialB := essential
  phi := fun _ _ => Equiv.refl _
  psiA := rightIdentityPath M
  psiB := leftIdentityPath M
  compatible := by
    intro i j z alpha r
    cases alpha with
    | cons a tail => cases tail; rfl

abbrev U : CountMat 1 1 := fun _ _ => 1
abbrev P2 : CountMat 1 1 := fun _ _ => 2
abbrev I2 : CountMat 2 2 := identityMatrix 2

def certificateU : CompatibleCertificate U U U (identityMatrix 1) 1 :=
  lagOneCertificate U ⟨fun _ => ⟨0, by simp [U]⟩, fun _ => ⟨0, by simp [U]⟩⟩

def certificateP2 : CompatibleCertificate P2 P2 P2 (identityMatrix 1) 1 :=
  lagOneCertificate P2 ⟨fun _ => ⟨0, by simp [P2]⟩, fun _ => ⟨0, by simp [P2]⟩⟩

def certificateI2 : CompatibleCertificate I2 I2 I2 (identityMatrix 2) 1 :=
  lagOneCertificate I2 ⟨fun i => ⟨i, by simp [I2, identityMatrix]⟩,
    fun i => ⟨i, by simp [I2, identityMatrix]⟩⟩

#print axioms lagOneCertificate

theorem lagOne_incoming {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0))
    (a r : Edge M) (h : a.target = r.source) :
    ((lagOneCertificate M essential).incomingLift a r h).val = a := rfl

theorem lagOne_outgoing {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0))
    (r b : Edge M) (h : r.target = b.source) :
    ((lagOneCertificate M essential).outgoingLift r b h).val = b := by
  cases r
  cases b
  cases h
  rfl

abbrev edgeSignature : Signature where
  Params := Σ n, Σ k, CountMat n k
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def edgeActual : Realization edgeSignature :=
  realize edgeSignature (fun _ _ r => r) (fun e => nomatch e)

namespace LeftForgetting

def bad : Realization edgeSignature :=
  realize edgeSignature (fun _ _ r => { r with number := Fin.rev r.number })
    (fun e => nomatch e)

def arena : Arena where
  signature := edgeSignature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    (∀ (a : Edge A) (r : Edge R) (h : a.target = r.source),
      (c.incomingSquare a r h).terminalR = rho.readout () ⟨n, k, R⟩ r) ∧
    (∀ (r : Edge R) (b : Edge B) (h : r.target = b.source),
      (c.outgoingSquare r b h).initialR = r) ∧
    (∀ {i j z} (alpha : FinitePath A m i j) (r : Fin (R j z)),
      (let lifted := c.liftIncomingPath alpha r
       (⟨i, lifted.1, lifted.2⟩ : Edge R)) =
      (let rs := (c.psiA i j).symm alpha
       (⟨i, rs.1, rs.2.1⟩ : Edge R)))

theorem actual_law : arena.Law edgeActual := by
  intro n k m A B R S c
  exact square_lifts_left_forgetting c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := (h certificateP2).1 ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
  have hn := congrArg (fun r : Edge P2 => r.number.val) he
  exact Nat.zero_ne_one hn

def registration : Registration arena (arena.Law edgeActual) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2⟩, ⟨0, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
    intro h
    have := congrArg (fun r : Edge P2 => r.number.val) h
    exact Nat.zero_ne_one this

register_information_theorem square_lifts_left_forgetting in arena
  readout via (realize edgeSignature (fun _ _ r => r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "body", "arg"]
      stateBinder := 9 }] })
  escape continues (open)

#print axioms registration

end LeftForgetting

def reverseNumbers {k : ℕ} {B : CountMat k k} :
    {d : ℕ} → {i j : Fin k} → FinitePath B d i j → FinitePath B d i j
  | _, _, _, .nil i => .nil i
  | _, _, _, .cons a tail => .cons (Fin.rev a) (reverseNumbers tail)

def onePathNumber {k : ℕ} {B : CountMat k k} {i j : Fin k}
    (p : FinitePath B 1 i j) : Fin (B i j) := by
  cases p with
  | cons a tail => cases tail; exact a

namespace RightForgetting

abbrev signature : Signature where
  Params := Σ k, Σ m, Σ B : CountMat k k, Σ _ : Fin k, Fin k
  State p := FinitePath p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := FinitePath p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ beta => beta) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ beta => reverseNumbers beta) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    ∀ {i : Fin n} {t z : Fin k} (r : Fin (R i t)) (beta : FinitePath B m t z),
      (let lifted := c.liftOutgoingPath r beta
       (⟨lifted.1, z, lifted.2.2⟩ : Edge R)) =
      (let sr := (c.psiB t z).symm (rho.readout () ⟨k, m, B, t, z⟩ beta)
       (⟨sr.1, z, sr.2.2⟩ : Edge R))

theorem actual_law : arena.Law actual := by
  intro n k m A B R S c
  exact square_lifts_right_forgetting c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := h certificateP2 (i := 0) (t := 0) (z := 0) 0 (.cons 0 (.nil 0))
  have hn := congrArg (fun r : Edge P2 => r.number.val) he
  exact Nat.zero_ne_one hn

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, .cons 0 (.nil 0), .cons 1 (.nil 0), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg (fun p : FinitePath P2 1 0 0 =>
      (onePathNumber p).val) h)

register_information_theorem square_lifts_right_forgetting in arena
  readout via (realize signature (fun _ _ beta => beta) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[1, 2, 4, 9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "value", "arg"]
      stateBinder := 12 }] })
  escape continues (open)

#print axioms registration

end RightForgetting

def loop (i : Fin 2) : Edge I2 := ⟨i, i, identityNumber i⟩

namespace SourceProjection

abbrev signature : Signature where
  Params := Σ n, Σ k, CountMat n k
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r.source) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ r =>
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le r.source.val) r.source.isLt⟩)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    (∀ r : Edge R, ∃ sq : Square c, sq.initialR = r) ∧
    (∀ r : Edge R, ∃ sq : Square c, sq.terminalR = r) ∧
    Function.Surjective (fun r : Edge R => rho.readout () ⟨n, k, R⟩ r) ∧
    Function.Surjective (fun r : Edge R => r.target) ∧
    ((∀ u, ∃ v, c.squareMatrix u v ≠ 0) ∧
      (∀ v, ∃ u, c.squareMatrix u v ≠ 0))

theorem actual_law : arena.Law actual := by
  intro n k m A B R S c
  exact square_graph_essential_and_projections c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨r, hr⟩ := (h certificateI2).2.2.1 1
  exact Nat.zero_ne_one (congrArg Fin.val hr)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 2, I2⟩, loop 0, loop 1, ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

register_information_theorem square_graph_essential_and_projections in arena
  readout via (realize signature (fun _ _ r => r.source) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration

end SourceProjection

open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

/-- Zero exchanges preserve the dimension, including empty matrix fibers. -/
theorem zeroChain_dimension {a b : ℕ} {X : CountMat a a} {Y : CountMat b b}
    (chain : ExchangeChain ℕ X Y 0) : a = b := by
  cases chain
  rfl

def emptyExchangeU : CountMat 0 1 := 0
def emptyExchangeV : CountMat 1 0 := 0

theorem emptyExchange : ExchangeChain ℕ
    (emptyExchangeU * emptyExchangeV) (emptyExchangeV * emptyExchangeU) 1 :=
  .cons emptyExchangeU emptyExchangeV (.nil _)

namespace ChainTrans

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ l₁ l₂ => l₁ + l₂) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {a b c : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}
    {l₁ l₂ : ℕ} (left : ExchangeChain ℕ X Y l₁)
    (right : ExchangeChain ℕ Y Z l₂),
    ExchangeChain ℕ X Z (rho.readout () l₁ l₂)

theorem actual_law : arena.Law actual := by
  intro a b c X Y Z l₁ l₂ left right
  exact exchange_chain_trans left right

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange (.nil _)))

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

register_information_theorem exchange_chain_trans in arena
  readout via (realize signature (fun _ l₁ l₂ => l₁ + l₂) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms registration

end ChainTrans

abbrev numberSignature : Signature where
  Params := Σ n, Σ k, Σ R : CountMat n k, Σ _ : Fin n, Fin k
  State p := Fin (p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def numberActual : Realization numberSignature :=
  realize numberSignature (fun _ _ r => r) (fun e => nomatch e)
def numberBad : Realization numberSignature :=
  realize numberSignature (fun _ _ r => Fin.rev r) (fun e => nomatch e)

def swapNumbers (i z : Fin 1) : EdgePair U P2 i z ≃ EdgePair P2 U i z :=
  Equiv.sigmaCongrRight (fun _ => Equiv.prodComm _ _)

namespace UnsweepSweep

def arena : Arena where
  signature := numberSignature
  Law rho := ∀ {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k}
    (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z),
    ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)),
      (let swept := sweep phi alpha r
       unsweep phi swept.2.1 swept.2.2) =
        ⟨j, alpha, rho.readout () ⟨n, k, R, j, z⟩ r⟩

theorem actual_law : arena.Law numberActual := by
  intro n k A B R phi
  exact unsweep_sweep phi

theorem rejected_law : ¬ arena.Law numberBad := by
  intro h
  have he := h swapNumbers (i := 0) (j := 0) (z := 0) (.nil 0) 0
  exact Nat.zero_ne_one (congrArg (fun p :
    Σ j : Fin 1, FinitePath U 0 0 j × Fin (P2 j 0) => p.2.2.val) he)

def registration : Registration arena (arena.Law numberActual) where
  actual := numberActual
  bridge := Iff.rfl
  variation := ⟨actual_law, numberBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨numberBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

register_information_theorem unsweep_sweep in arena
  readout via (realize numberSignature (fun _ _ r => r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 4, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration

end UnsweepSweep

namespace UnsweepAppend

def arena : Arena where
  signature := numberSignature
  Law rho := ∀ {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z),
    ∀ {d : ℕ} {i : Fin n} {t u z : Fin k} (r : Fin (R i t))
      (beta : FinitePath B d t u) (b : Fin (B u z)),
      unsweep phi (rho.readout () ⟨n, k, R, i, t⟩ r) (appendPath beta b) =
        (let prior := unsweep phi r beta
         let sq := (phi prior.1 z).symm ⟨u, prior.2.2, b⟩
         ⟨sq.1, appendPath prior.2.1 sq.2.1, sq.2.2⟩)

theorem actual_law : arena.Law numberActual := by
  intro n k A B R phi
  exact unsweep_append phi

theorem rejected_law : ¬ arena.Law numberBad := by
  intro h
  have he := h swapNumbers (i := 0) (t := 0) (u := 0) (z := 0) 0 (.nil 0) 0
  exact Nat.zero_ne_one (congrArg (fun p :
    Σ j : Fin 1, FinitePath U 1 0 j × Fin (P2 j 0) => p.2.2.val) he).symm

def registration : Registration arena (arena.Law numberActual) where
  actual := numberActual
  bridge := Iff.rfl
  variation := ⟨actual_law, numberBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨numberBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

register_information_theorem unsweep_append in arena
  readout via (realize numberSignature (fun _ _ r => r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 4, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration

end UnsweepAppend

abbrev depthSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def depthActual : Realization depthSignature :=
  realize depthSignature (fun _ _ d => d) (fun e => nomatch e)
def depthBad : Realization depthSignature :=
  realize depthSignature (fun _ _ _ => 0) (fun e => nomatch e)

namespace ChainReverse

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length),
    ExchangeChain ℕ Y X (rho.readout () () length)

theorem actual_law : arena.Law depthActual := by
  intro a b X Y length chain
  exact exchange_chain_reverse chain

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange)).symm

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

register_information_theorem exchange_chain_reverse in arena
  readout via (realize depthSignature (fun _ _ d => d) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end ChainReverse

namespace ChainTranspose

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length),
    ExchangeChain ℕ X.transpose Y.transpose (rho.readout () () length)

theorem actual_law : arena.Law depthActual := by
  intro a b X Y length chain
  exact exchange_chain_transpose chain

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange))

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

register_information_theorem exchange_chain_transpose in arena
  readout via (realize depthSignature (fun _ _ d => d) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end ChainTranspose

/-- One numbered loop with an arbitrary state transition. -/
def loopLift {Q : Type} (q₀ : Q) (f : Q → Q) : IncomingLift U Q where
  project := fun _ => 0
  onto := fun i => ⟨q₀, Subsingleton.elim _ _⟩
  lift := fun a q => ⟨f q.val, Subsingleton.elim _ _⟩

def uniqueLoopPath : (d : ℕ) → FinitePath U d 0 0
  | 0 => .nil 0
  | d + 1 => .cons 0 (uniqueLoopPath d)

theorem loopLift_path {Q : Type} (q₀ : Q) (f : Q → Q)
    {d : ℕ} {i j : Fin 1} (path : FinitePath U d i j)
    (q : {x : Q // (loopLift q₀ f).project x = j}) :
    ((loopLift q₀ f).liftPath path q).val = f^[d] q.val := by
  induction path with
  | nil i => rfl
  | cons a tail ih =>
    simpa only [IncomingLift.liftPath, loopLift, Function.iterate_succ_apply'] using
      congrArg f (ih q)

theorem loopLift_response {Q : Type} (q₀ : Q) (f : Q → Q)
    (d : ℕ) (x y : Q) :
    (loopLift q₀ f).response d x y ↔ f^[d] x = f^[d] y := by
  constructor
  · intro h
    have he := congrArg (fun o => o.2 0 0 (uniqueLoopPath d))
      (show (loopLift q₀ f).responseReadout d x =
        (loopLift q₀ f).responseReadout d y from h)
    have hx : (loopLift q₀ f).project x = 0 := rfl
    have hy : (loopLift q₀ f).project y = 0 := rfl
    simpa only [IncomingLift.responseReadout, dif_pos hx, dif_pos hy,
      loopLift_path, Option.some.injEq] using he
  · intro h
    change (loopLift q₀ f).responseReadout d x = (loopLift q₀ f).responseReadout d y
    apply Prod.ext
    · rfl
    funext i j path
    have hx : (loopLift q₀ f).project x = j := Subsingleton.elim _ _
    have hy : (loopLift q₀ f).project y = j := Subsingleton.elim _ _
    simp only [IncomingLift.responseReadout, dif_pos hx, dif_pos hy, loopLift_path, h]

def liftL0 : IncomingLift U Bool := loopLift false (fun _ => false)
def liftL2 : IncomingLift U (Fin 3) := loopLift 0 (fun x => if x = 2 then 1 else 0)
def liftIdBool : IncomingLift U Bool := loopLift false id
def liftUnit : IncomingLift U Unit := loopLift () id

def l0End : Quotient (liftL0.response 1) ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => Quotient.mk _ false
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact (loopLift_response false (fun _ => false) 1 false x).mpr rfl
  right_inv := fun _ => Subsingleton.elim _ _

instance uniqueUEdge : Subsingleton (Edge U) where
  allEq := by
    rintro ⟨i, j, a⟩ ⟨i', j', a'⟩
    have hi : i = i' := Subsingleton.elim _ _
    have hj : j = j' := Subsingleton.elim _ _
    subst i'; subst j'
    have ha : a = a' := Subsingleton.elim _ _
    subst a'; rfl

/-- The identity lift's incoming fiber is the singleton edge precisely on its class. -/
def identityFiberEquiv {Q : Type} (q₀ : Q) (d : ℕ) (x y : Q)
    (h : ∀ a b, (loopLift q₀ id).response d a b ↔ a = b) :
    incomingResponseFiber (loopLift q₀ id) d (Quotient.mk _ x) y ≃
      {a : Edge U // y = x} where
  toFun := fun a => ⟨a.val, by
    obtain ⟨hv, he⟩ := a.property
    exact (h _ _).mp (Quotient.exact he)⟩
  invFun := fun a => ⟨a.val, ⟨Subsingleton.elim _ _, by
    apply Quotient.sound
    exact (h _ _).mpr a.property⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

theorem identityFiber_card {Q : Type} [DecidableEq Q] (q₀ : Q) (d : ℕ) (x y : Q) :
    Nat.card (incomingResponseFiber (loopLift q₀ id) d (Quotient.mk _ x) y) =
      if y = x then 1 else 0 := by
  classical
  have hh : ∀ a b, (loopLift q₀ id).response d a b ↔ a = b := by
    intro a b
    simpa using loopLift_response q₀ id d a b
  rw [Nat.card_congr (identityFiberEquiv q₀ d x y hh)]
  by_cases h : y = x
  · let e : {a : Edge U // y = x} ≃ Fin 1 := {
      toFun := fun _ => 0
      invFun := fun _ => ⟨⟨0, 0, 0⟩, h⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    rw [Nat.card_congr e, Nat.card_fin, if_pos h]
  · let e : {a : Edge U // y = x} ≃ Empty := {
      toFun := fun a => (h a.property).elim
      invFun := fun e => nomatch e
      left_inv := fun a => (h a.property).elim
      right_inv := fun e => nomatch e }
    rw [Nat.card_congr e, if_neg h]
    simp

namespace IncomingStep

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) {u v : Q}
    (h : L.response (d + 1) u v) (a : Edge A)
    (hu : L.project u = a.target) (hv : L.project v = a.target),
    L.response (rho.readout () () d)
      (L.lift a ⟨u, hu⟩).val (L.lift a ⟨v, hv⟩).val

theorem actual_law : arena.Law depthActual := by
  intro n A Q L d u v h a hu hv
  exact incoming_response_step L d h a hu hv

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  have hr : liftL2.response 2 (0 : Fin 3) 2 := by
    exact (loopLift_response 0 (fun x : Fin 3 => if x = 2 then 1 else 0)
      2 0 2).mpr (by decide)
  have he := h liftL2 1 hr (⟨0, 0, 0⟩ : Edge U) rfl rfl
  change liftL2.response 0 (0 : Fin 3) 1 at he
  have hn := (loopLift_response 0 (fun x : Fin 3 => if x = 2 then 1 else 0)
    0 0 1).mp he
  exact Nat.zero_ne_one (congrArg Fin.val hn)

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

register_information_theorem incoming_response_step in arena
  readout via (realize depthSignature (fun _ _ d => d) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn", "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end IncomingStep

namespace FiniteChainTo

def actual : Realization depthSignature :=
  realize depthSignature (fun _ _ d => d + 1) (fun e => nomatch e)

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q)
    (start length : ℕ) {r : ℕ}
    (eEnd : Quotient (L.response (start + length + 1)) ≃ Fin r),
    ExchangeChain ℕ (finiteResponseMatrix L start)
      (Matrix.reindex eEnd eEnd
        (incomingResponseMatrix L (start + length + 1)))
      (rho.readout () () length)

theorem actual_law : arena.Law actual := by
  intro p M Q inst L start length r eEnd
  exact finite_response_chain_to L start length eEnd

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  let e0 : Quotient (liftL0.response 0) ≃ Bool :=
    (Equiv.cast (congrArg (fun r : Setoid Bool => Quotient r)
      (response_zero_and_step liftL0).1)).trans Setoid.quotientBotEquiv
  have hc : @Fintype.card _ (responseFintype liftL0 0) = 2 := by
    calc
      _ = Fintype.card Bool :=
        @Fintype.card_congr _ _ (responseFintype liftL0 0) inferInstance e0
      _ = 2 := rfl
  have hh := zeroChain_dimension (h liftL0 0 0 l0End)
  change @Fintype.card _ (responseFintype liftL0 0) = 1 at hh
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), (by decide : (1 : ℕ) ≠ 2)⟩

register_information_theorem finite_response_chain_to in arena
  readout via (realize depthSignature (fun _ _ d => d + 1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration

end FiniteChainTo

namespace FiberCard

abbrev signature : Signature where
  Params := Σ p, Σ M : CountMat p p, Σ Q : Type, Σ L : IncomingLift M Q,
    Σ d : ℕ, Quotient (L.response d)
  State p := p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => Nat.card
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w)) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ p w => Nat.card
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) (F : Quotient (L.response d))
    {v w : Q} (h : L.response (d + 1) v w),
    Nat.card (incomingResponseFiber L d F v) = rho.readout () ⟨p, M, Q, L, d, F⟩ w

theorem actual_law : arena.Law actual := by
  intro p M Q L d F v w h
  exact incoming_response_fiber_card_step L d F h

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := h liftIdBool 0 (Quotient.mk _ false) (v := false) (w := false)
    ((liftIdBool.response 1).refl false)
  change Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) =
    Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) + 1 at he
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, U, Bool, liftIdBool, 0, Quotient.mk _ false⟩, false, true, ?_⟩
    intro h
    change Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) =
      Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) true) at h
    have hfalse : Nat.card (incomingResponseFiber liftIdBool 0
        (Quotient.mk _ false) false) = 1 := identityFiber_card false 0 false false
    have htrue : Nat.card (incomingResponseFiber liftIdBool 0
        (Quotient.mk _ false) true) = 0 := identityFiber_card false 0 false true
    exact Nat.zero_ne_one (htrue.symm.trans (h.symm.trans hfalse))

register_information_theorem incoming_response_fiber_card_step in arena
  readout via (realize signature (fun _ p w => Nat.card
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms registration

end FiberCard

namespace ForgettingReindexed

abbrev signature : Signature where
  Params := ℕ
  State p := CountMat p p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := CountMat p p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (d : ℕ)
    (hd : L.response d = Setoid.ker L.project),
    ∃ e : Quotient (L.response d) ≃ Fin p,
      Matrix.reindex e e (incomingResponseMatrix L d) = rho.readout () p M

theorem actual_law : arena.Law actual := by
  intro p M Q inst L d hd
  exact response_matrix_forgetting_reindexed L d hd

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have hd : liftUnit.response 0 = Setoid.ker liftUnit.project := by
    apply Setoid.ext
    intro x y
    constructor
    · intro _; rfl
    · intro _
      exact (loopLift_response () id 0 x y).mpr (Subsingleton.elim _ _)
  obtain ⟨e, he⟩ := h liftUnit 0 hd
  have hv := congrArg (fun M : CountMat 1 1 => M 0 0) he
  change incomingResponseMatrix liftUnit 0 (e.symm 0) (e.symm 0) = 0 at hv
  have hq : e.symm 0 = Quotient.mk (liftUnit.response 0) () := by
    induction e.symm 0 using Quotient.inductionOn with
    | _ q => cases q; rfl
  rw [hq] at hv
  have hout : Quotient.out (Quotient.mk (liftUnit.response 0) ()) = () :=
    (loopLift_response () id 0 _ ()).mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (liftUnit.response 0) ())))
  change Nat.card (incomingResponseFiber liftUnit 0 (Quotient.mk _ ())
    (Quotient.out (Quotient.mk (liftUnit.response 0) ()))) = 0 at hv
  rw [hout] at hv
  have hc : Nat.card (incomingResponseFiber liftUnit 0 (Quotient.mk _ ()) ()) = 1 :=
    identityFiber_card () 0 () ()
  exact Nat.zero_ne_one (hv.symm.trans hc)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), U, P2, ?_⟩
    intro h
    exact (by decide : (1 : ℕ) ≠ 2) (congrArg (fun M : CountMat 1 1 => M 0 0) h)

register_information_theorem response_matrix_forgetting_reindexed in arena
  readout via (realize signature (fun _ _ M => M) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end ForgettingReindexed

namespace MatrixFactorStep

/-- Dependence is evaluation of a whole depth-indexed matrix family. -/
abbrev signature : Signature where
  Params := Σ p, Σ M : CountMat p p, Σ Q : Type, Σ _ : IncomingLift M Q, ℕ
  State theta := (k : ℕ) → Matrix (Quotient (theta.2.2.2.1.response k))
    (Quotient (theta.2.2.2.1.response k)) ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ theta := Matrix (Quotient (theta.2.2.2.1.response (theta.2.2.2.2 + 1)))
    (Quotient (theta.2.2.2.1.response (theta.2.2.2.2 + 1))) ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ theta F => F (theta.2.2.2.2 + 1)) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ theta F i j => F (theta.2.2.2.2 + 1) i j + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ)
    [Fintype (Quotient (L.response d))]
    [Fintype (Quotient (L.response (d + 1)))],
    rho.readout () ⟨p, M, Q, L, d⟩ (incomingResponseMatrix L) =
      incomingResponseV L d * incomingResponseU L d

theorem actual_law : arena.Law actual := by
  intro p M Q L d inst0 inst1
  exact incoming_response_matrix_factor_step L d

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  let f0 := responseFintype liftUnit 0
  let f1 := responseFintype liftUnit 1
  have changed := @h 1 U Unit liftUnit 0 f0 f1
  have original := @incoming_response_matrix_factor_step 1 U Unit liftUnit 0 f0 f1
  let q : Quotient (liftUnit.response 1) := Quotient.mk _ ()
  have entry := congrArg (fun A => A q q) (changed.trans original.symm)
  change incomingResponseMatrix liftUnit 1 q q + 1 =
    incomingResponseMatrix liftUnit 1 q q at entry
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, U, Unit, liftUnit, 0⟩, (fun _ _ _ => 0), (fun _ _ _ => 1), ?_⟩
    intro h
    let q : Quotient (liftUnit.response 1) := Quotient.mk _ ()
    exact Nat.zero_ne_one (congrArg (fun A => A q q) h)

register_information_theorem incoming_response_matrix_factor_step in arena
  readout via (realize signature (fun _ theta F => F (theta.2.2.2.2 + 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateOperand := some #["fn"]
      stateBinder := 0
      functionOperand := false
      booleanPredicate := false }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms registration

end MatrixFactorStep

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
