import LeanInformationAuditInterface.Contract.Analysis.Finite
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

namespace LeanInformationAudit.AuricFib.Contract
open D5.S3.Arith.FibonacciAtomic
open LiteralWindowEnd (Window)
open ImmediateWindowStateCapacity (RawState rawTransition rawMachine rawOutput)

/-- The complete native state domain is Window, independent of law support.
The equalities bind an owner's reader and total continuation to the same source. -/
structure NativeBridge where
  reader : Window → RawState 0
  reply : Window → Option Int
  reader_eq : reader = fun a => rawTransition (rawMachine 0).start a
  reply_eq : reply = fun a => rawOutput (rawTransition (reader a) .high)

/-- The reader is exactly the evaluator occurring in the original theorem,
at its explicit initialized single-window substitution. -/
theorem NativeBridge.reader_source (bridge : NativeBridge) (window : Window) :
    bridge.reader window = (rawMachine 0).toDFA.evalFrom
      (some (false, GraftAffineClosure.residue 0 (0, 0))) [window] := by
  rw [bridge.reader_eq]
  rfl

/-- The total task is the same evaluator at the appended high suffix. -/
theorem NativeBridge.reply_source (bridge : NativeBridge) (window : Window) :
    bridge.reply window = rawOutput ((rawMachine 0).toDFA.evalFrom
      (some (false, GraftAffineClosure.residue 0 (0, 0))) [window, .high]) := by
  rw [bridge.reply_eq, bridge.reader_eq]
  rfl

/-- Exact rational declared masses, with normalization checked by Lean.
Declaration does not certify acquisition or a physical probability law. -/
structure Masses where
  nullMass : Nat
  lowMass : Nat
  highMass : Nat
  endsMass : Nat
  middleMass : Nat
  denominator : Nat
  positive : 0 < denominator
  normalized : nullMass + lowMass + highMass + endsMass + middleMass = denominator

inductive Acquisition where
  | absent (source : String)
  | declared (source : String) (masses : Masses)
  | empirical (source : String) (archive : List Window)

inductive Readout where
  | atom | seam | guard | reply
  deriving DecidableEq

/-- Full native theorem correspondence is confined to this adapter. The
single-window substitution preserves the original theorem as its premise. -/
structure NativeSource {Statement : Prop} (occurrence : Statement) where
  reconstruction : Analysis.Reconstruction Statement
    (type_of% NativeContinuation.NullReplyFiber.native_execution)

/-- The original theorem specialized at seam=false, composition=(0,0), and one
window. This proof is obtained from the indexed occurrence, not another theorem. -/
def NativeSource.specialize {Statement : Prop} {occurrence : Statement}
    (source : NativeSource occurrence) (window : Window) :
    type_of% (NativeContinuation.NullReplyFiber.native_execution false (0, 0) [window]) := by
  cases source with
  | mk reconstruction =>
    cases reconstruction
    exact occurrence false (0, 0) [window]

/-- The same initialized state followed by high uses the original full theorem
at the explicit two-letter history; rejection stays in its Option output. -/
def NativeSource.continueHigh {Statement : Prop} {occurrence : Statement}
    (source : NativeSource occurrence) (window : Window) :
    type_of% (NativeContinuation.NullReplyFiber.native_execution false (0, 0) [window, .high]) := by
  cases source with
  | mk reconstruction =>
    cases reconstruction
    exact occurrence false (0, 0) [window, .high]

/- Canonical law vocabulary. These definitions carry no theorem or evaluator. -/
namespace Pyramid
noncomputable def X (p : Window → ℝ) : ℝ := p .low + p .ends
noncomputable def Y (p : Window → ℝ) : ℝ := p .high + p .ends
noncomputable def Z (p : Window → ℝ) : ℝ := p .middle
noncomputable def r (p : Window → ℝ) : ℝ := 1 - Z p
noncomputable def kappa (p : Window → ℝ) : ℝ := p .ends
noncomputable def delta (p : Window → ℝ) : ℝ := r p * kappa p - X p * Y p
noncomputable def width (p : Window → ℝ) : ℝ :=
  min (min (X p) (Y p)) (min (r p - X p) (r p - Y p))
def CoarseEq (p q : Window → ℝ) : Prop := X p = X q ∧ Y p = Y q ∧ Z p = Z q
end Pyramid

noncomputable def Masses.value (m : Masses) (w : Window) : ℝ :=
  (match w with
    | .zero => m.nullMass | .low => m.lowMass | .high => m.highMass
    | .ends => m.endsMass | .middle => m.middleMass : Nat) / (m.denominator : ℝ)

/-- A mass-valued source with a parameter-independent mode type. The literal
pairing is the complete graph of the proved bijection, not a mode convention.
`law_eq` connects each atom to the selected actual source observation. -/
structure LawFamily {Statement : Prop} {occurrence : Statement}
    (client : Analysis.Client.{0,t,s,r,0,a,v} occurrence) where
  Mode : Type s
  state_eq : ∀ θ, client.source.signature.State θ = Mode
  role : client.source.signature.Role
  output_eq : ∀ θ, client.source.signature.Output role θ = ℝ
  atoms : List (Mode × Window)
  identify : Mode → Window
  bijective : Function.Bijective identify
  atoms_correct : ∀ m w, (m, w) ∈ atoms ↔ identify m = w
  law : client.source.signature.Params → Window → ℝ
  law_eq : ∀ θ m, law θ (identify m) = cast (output_eq θ)
    (client.source.actual.readout role θ (cast (state_eq θ).symm m))
  domain : client.source.signature.Params → Prop
  nonnegative : ∀ θ, domain θ → ∀ w, 0 ≤ law θ w
  normalized : ∀ θ, domain θ →
    law θ .zero + law θ .low + law θ .high + law θ .ends + law θ .middle = 1
  infinite : Option (PLift (Infinite {θ // domain θ})) := none
  simplex : Option (PLift (∀ p : Window → ℝ, (∀ w, 0 ≤ p w) →
    p .zero + p .low + p .high + p .ends + p .middle = 1 →
    ∃ θ, domain θ ∧ ∀ w, law θ w = p w)) := none

structure LawPoint {Statement : Prop} {occurrence : Statement}
    {client : Analysis.Client.{0,t,s,r,0,a,v} occurrence} (family : LawFamily client) where
  parameter : client.source.signature.Params
  in_domain : family.domain parameter
  masses : Masses
  law_eq : ∀ w, family.law parameter w = masses.value w

inductive DeltaSign where
  | positive | nonnegative | zero | nonpositive | negative

def DeltaSign.Holds (sign : DeltaSign) (x : ℝ) : Prop := match sign with
  | .positive => 0 < x | .nonnegative => 0 ≤ x | .zero => x = 0
  | .nonpositive => x ≤ 0 | .negative => x < 0

/-- Closed allow-list of qualitative family facts. Target-result dependency is
read from each proof's compiled closure, not an author's evidence label. -/
inductive LawFact {Statement : Prop} {occurrence : Statement}
    {client : Analysis.Client.{0,t,s,r,0,a,v} occurrence} (family : LawFamily client) where
  | deltaSign (sign : DeltaSign)
      (proof : ∀ θ, family.domain θ → sign.Holds (Pyramid.delta (family.law θ)))
  | positiveWidth (proof : ∀ θ, family.domain θ → 0 < Pyramid.width (family.law θ))
  | identifiable (proof : ∀ θ φ, family.domain θ → family.domain φ →
      Pyramid.CoarseEq (family.law θ) (family.law φ) →
      Pyramid.delta (family.law θ) = Pyramid.delta (family.law φ))
  | separated (proof : ∃ θ φ, family.domain θ ∧ family.domain φ ∧
      Pyramid.CoarseEq (family.law θ) (family.law φ) ∧
      Pyramid.delta (family.law θ) ≠ Pyramid.delta (family.law φ))

/-- An explicit rational task on the five atoms, independent of native replies.
Its mixed difference determines whether association changes its expectation. -/
structure LawTask where
  nullValue : Int
  lowValue : Int
  highValue : Int
  endsValue : Int
  middleValue : Int
  denominator : Nat
  positive : 0 < denominator

/-- Evidence is indexed by the full occurrence. Generic clients have no native
proposition restriction and require neither finite acquisition nor a source law.
Unsupported submissions carry no correspondence evidence. -/
inductive Evidence {Statement : Prop} (occurrence : Statement) where
  | typed (client : Analysis.Client.{0,t,s,r,o,a,v} occurrence)
  | law (client : Analysis.Client.{0,t,s,r,0,a,v} occurrence) (family : LawFamily client)
      (point : Option (LawPoint family)) (facts : List (LawFact family)) (task : Option LawTask)
  | native (source : NativeSource occurrence) (bridge : NativeBridge) (acquisition : Acquisition)
      (initial : List Readout) (layers : List Readout)
  | unsupported (reason : String)

/-- Optional source-owned analysis selected by authoring this typed contract
in Reg. The existing compiled audit/report chain acquires its downstream data;
without an Application it performs no FIB acquisition or numerical analysis and
adds no analysis registration obligation. This is neither a proof-escape
registration nor an admission certificate. -/
structure Application {Statement : Prop} (occurrence : Statement) where
  evidence : Evidence.{t,s,r,o,a,v} occurrence

end LeanInformationAudit.AuricFib.Contract
