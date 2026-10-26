import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraResolution
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Original source telescopes and actual count readouts for the complete polynomial assertion. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraResolution
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraPolynomialCoreSum MiuraRunCompositions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

namespace FiberCard
structure Parameter where
  a : ℕ
  b : ℕ
  K : Core a b

structure State (p : Parameter) where
  m : ℕ
  n : ℕ
  hm : 2 * (p.a + p.b) - 1 ≤ m
  hn : 2 * (p.a + p.b) - 1 ≤ n

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun _ => ℕ)

def actual : Realization signature := realize signature
  (fun (_ : Unit) p x => Nat.card (MiuraPartitionCount.Fiber p.a p.b x.m x.n p.K))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), R.readout () p x =
    Nat.card (PositiveLengths (x.m - rowOccupied p.K) (rowRuns p.K) ×
      PositiveLengths (x.n - colOccupied p.K) (colRuns p.K))

theorem actual_law : arena.Law actual := by
  intro p x
  exact MiuraResolution.fiber_card_eq_positive_vectors p.a p.b x.m x.n p.K x.hm x.hn

theorem bridge : (type_of% (@MiuraResolution.fiber_card_eq_positive_vectors)) ↔
    arena.Law actual := by
  constructor
  · intro h p x
    exact h p.a p.b x.m x.n p.K x.hm x.hn
  · intro h a b m n K hm hn
    exact h ⟨a, b, K⟩ ⟨m, n, hm, hn⟩
end FiberCard

namespace Evaluation
structure Parameter where
  a : ℕ
  b : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hd : 5 ≤ a + b

structure State (p : Parameter) where
  m : ℕ
  n : ℕ
  hm : 2 * (p.a + p.b) - 1 ≤ m
  hn : 2 * (p.a + p.b) - 1 ≤ n

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun _ => ℚ)

def actual : Realization signature := realize signature
  (fun (_ : Unit) p x => (residualCount p.a p.b x.m x.n
    (by have := p.hd; have := x.hm; omega)
    (by have := p.hd; have := x.hn; omega) : ℚ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p),
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (x.m : ℚ) else (x.n : ℚ))
      (corePolynomial p.a p.b) = R.readout () p x

theorem actual_law : arena.Law actual := by
  intro p x
  exact MiuraResolution.core_polynomial_counts_residual p.a p.b x.m x.n
    p.ha p.hb p.hd x.hm x.hn

def rejected : Realization signature := realize signature
  (fun (_ : Unit) p x => actual.readout () p x + 1) (fun e => nomatch e)

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro law
  let p : Parameter := ⟨1, 4, by decide, by decide, by decide⟩
  let x : State p := ⟨9, 9, by decide, by decide⟩
  have good := actual_law p x
  have bad := law p x
  change MvPolynomial.eval _ _ = actual.readout () p x + 1 at bad
  linarith

theorem variation : Variation arena actual := ⟨actual_law, rejected, rejected_not_law⟩

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law

theorem bridge : (type_of% (@MiuraResolution.core_polynomial_counts_residual)) ↔
    arena.Law actual := by
  constructor
  · intro h p x
    exact h p.a p.b x.m x.n p.ha p.hb p.hd x.hm x.hn
  · intro h a b m n ha hb hd hm hn
    exact h ⟨a, b, ha, hb, hd⟩ ⟨m, n, hm, hn⟩
end Evaluation

namespace Full
structure Parameter where
  d : ℕ
  a : ℕ
  b : ℕ
  hd : 5 ≤ d
  ha : 1 ≤ a
  hb : 1 ≤ b
  hab : a + b = d
  habOrder : a ≤ b

structure State (p : Parameter) where
  m : ℕ
  n : ℕ
  hm : 2 * p.d - 1 ≤ m
  hn : 2 * p.d - 1 ≤ n

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun _ => ℚ)

def actual : Realization signature := realize signature
  (fun (_ : Unit) p x => (residualCount p.a p.b x.m x.n
    (by have := p.hd; have := x.hm; omega)
    (by have := p.hd; have := x.hn; omega) : ℚ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ q : MvPolynomial (Fin 2) ℚ, q.totalDegree ≤ p.d - 3 ∧
    ∀ x : State p,
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (x.m : ℚ) else (x.n : ℚ)) q =
        R.readout () p x

theorem bridge : (type_of% (@MiuraResolution.result)) ↔ arena.Law actual := by
  constructor
  · intro h p
    obtain ⟨q, hdeg, heval⟩ := h p.d p.a p.b p.hd p.ha p.hb p.hab p.habOrder
    exact ⟨q, hdeg, fun x => heval x.m x.n x.hm x.hn⟩
  · intro h d a b hd ha hb hab habOrder
    obtain ⟨q, hdeg, heval⟩ := h ⟨d, a, b, hd, ha, hb, hab, habOrder⟩
    exact ⟨q, hdeg, fun m n hm hn => heval ⟨m, n, hm, hn⟩⟩

theorem actual_law : arena.Law actual := bridge.mp MiuraResolution.result
end Full

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraResolution
