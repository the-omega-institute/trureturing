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

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
