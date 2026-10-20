import LeanInformationAuditRegTests.SearchReduction.Candidates

namespace LeanInformationAudit.Tests.SearchReduction.VocabularyCandidates
open Candidates

inductive PureMode where
  | ab | bc | ac
  deriving DecidableEq, Repr, Inhabited

-- A handwritten computational instance must not be silently replaced by deriving.
def noncanonicalRepr : Repr PureMode := ⟨fun _ _ => "author"⟩

structure ForwardLaw (p : Nat → Nat) : Prop where
  start : p 0 = 0
  step : ∀ n, p (n+1) = p n + 1

private theorem easyCertificate (n : Nat) : n = n := rfl
private theorem easyCertificateOther (n : Nat) : n = n := by omega

def easyBox (n : Nat) : {x : Nat // x = n} := ⟨n, easyCertificate n⟩
def easyBoxOther (n : Nat) : {x : Nat // x = n} := ⟨n, easyCertificateOther n⟩

def continuousBox : {f : ℝ → ℝ // Continuous f} := ⟨id, continuous_id⟩

def nestedBox (n : Nat) : Nat := (easyBox n).val

def hardBox (n : Nat) : {x : Nat // stair n = 3*n} := ⟨n, answer n⟩

theorem easyProjection (n : Nat) : (easyBox n).1 = n := rfl
theorem hardProjection (n : Nat) :
    stair (hardBox n).1 = 3*(hardBox n).1 := (hardBox n).2

theorem forwardReadout (p : Nat → Nat) (h : ForwardLaw p) : p 0 = 0 := h.start

theorem modeExhaustive (m : PureMode) : m = .ab ∨ m = .bc ∨ m = .ac := by
  cases m <;> simp

theorem modeReflexive (m : PureMode) : m = m := rfl

private theorem privateStructure (n m : Nat) : stair (n+m) = stair n + stair m := addition n m

theorem privateConsumer (n : Nat) : stair (n+n) = stair n + stair n := privateStructure n n
end LeanInformationAudit.Tests.SearchReduction.VocabularyCandidates
