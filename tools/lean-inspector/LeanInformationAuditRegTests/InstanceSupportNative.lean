-- Native fixture source inputs; materialize under their logical D5/Reg paths
-- only for a scoped fixture compilation. These are not D5 content declarations.
namespace LeanInformationAuditRegTests.InstanceSupportNative

def source : String := r####"import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace D5.InstanceSupportFixture

theorem source (X : Type) [Fintype X] (n : Nat) : n ≤ Fintype.card X + n :=
  Nat.le_add_left n (Fintype.card X)

-- Construct kernel-checked declarations with raw domains that surface syntax
-- normally elaborates away. Both wrappers reduce to the original class domain.
open Lean Meta in
run_meta do
  let info ← getConstInfo ``source
  let .forallE x xt (.forallE d dt body bi) xb := info.type
    | throwError "unexpected raw-domain fixture telescope"
  let one := Level.succ .zero
  let pair := mkAppN (mkConst ``Prod.mk [one, one])
    #[mkSort one, mkSort one, dt, mkConst ``Nat]
  for (name, domain) in #[
      (`D5.InstanceSupportFixture.metadataSource, Expr.mdata {} dt),
      (`D5.InstanceSupportFixture.projectionSource, Expr.proj ``Prod 0 pair)] do
    addDecl <| .thmDecl {
      name, levelParams := [],
      type := .forallE x xt (.forallE d domain body bi) xb,
      value := mkConst ``source }

abbrev signature : Signature where
  Params := Σ X : Type, Fintype X
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (X : Type) [d : Fintype X] (n : Nat), n ≤ r.readout () ⟨X, d⟩ n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (h Unit 1)

def registration : Registration arena (∀ (X : Type) [Fintype X] (n : Nat),
    n ≤ Fintype.card X + n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨Unit, inferInstance⟩, (0 : Nat), (1 : Nat), ?_⟩
    change Fintype.card Unit + 0 ≠ Fintype.card Unit + 1
    omega

def metadataRegistration : Registration arena
    (∀ (X : Type) [Fintype X] (n : Nat), n ≤ Fintype.card X + n) where
  actual := actual
  bridge := Iff.rfl
  variation := registration.variation
  sensitivity := registration.sensitivity
  dependence := registration.dependence

def projectionRegistration : Registration arena
    (∀ (X : Type) [Fintype X] (n : Nat), n ≤ Fintype.card X + n) where
  actual := actual
  bridge := Iff.rfl
  variation := registration.variation
  sensitivity := registration.sensitivity
  dependence := registration.dependence

theorem dependentSource (X : Type) [Fintype X] (x : Fin (Fintype.card X + 1)) (n : Nat) :
    n ≤ x.val + Fintype.card X + n := Nat.le_add_left _ _

abbrev dependentSignature : Signature where
  Params := Σ X : Type, Σ d : Fintype X, Fin (@Fintype.card X d + 1)
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def dependentActual : Realization dependentSignature :=
  realize dependentSignature
    (fun _ p n => p.2.2.val + @Fintype.card p.1 p.2.1 + (n : Nat)) (fun e => nomatch e)

theorem multipleSource (X : Type) [Fintype X] (n : Nat) :
    (n ≤ Fintype.card X + n) ∧ (n ≤ Fintype.card X + n) :=
  ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩

theorem noncanonicalSource [d : Inhabited Nat] (n : Nat) : n ≤ @default Nat d + n :=
  Nat.le_add_left _ _

abbrev noncanonicalSignature : Signature where
  Params := Inhabited Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def noncanonicalActual : Realization noncanonicalSignature :=
  realize noncanonicalSignature (fun _ p n => p.default + n) (fun e => nomatch e)

def canonicalReplacement : Realization noncanonicalSignature :=
  realize noncanonicalSignature (fun _ _ n => @default Nat ⟨0⟩ + n) (fun e => nomatch e)

example : noncanonicalActual.readout () ⟨7⟩ 2 = 9 := rfl
example : noncanonicalActual.readout () ⟨11⟩ 2 = 13 := rfl

theorem dictionaryState (d : Inhabited Nat) : d = d := rfl
theorem proofState (h : True) : h = h := rfl
theorem dictionaryOutput [d : Inhabited Nat] (n : Nat) : d = d ∧ n = n := ⟨rfl, rfl⟩
theorem explicitDictionary (X : Type) (d : Fintype X) (n : Nat) :
    n ≤ @Fintype.card X d + n := Nat.le_add_left _ _
theorem proofOutput (h : True) (n : Nat) : h = h ∧ n = n := ⟨rfl, rfl⟩
theorem siblingSupport : (∀ [d : Inhabited Nat] (n : Nat), n ≤ @default Nat d + n) ∧
    (∀ [d : Inhabited Nat] (n : Nat), n ≤ @default Nat d + n) :=
  by constructor <;> intro d n <;> exact Nat.le_add_left _ _
class DependentSupport (X : Type) [Fintype X] where
  value : Fin (Fintype.card X + 1)
theorem transitiveSource (X : Type) [Fintype X] [DependentSupport X] (n : Nat) :
    n ≤ (DependentSupport.value (X := X)).val + n := Nat.le_add_left _ _
class ProofSupport : Prop where
  witness : True
def proofReadout (_ : ProofSupport) (n : Nat) : Nat := n
theorem proofClassSource [p : ProofSupport] (n : Nat) : n ≤ proofReadout p n := le_refl n

theorem letSource [d : Inhabited Nat] (n : Nat) :
    let k := @default Nat d
    n ≤ k + n := Nat.le_add_left _ _

theorem operandSource [d : Inhabited Nat] : @default Nat d ≤ @default Nat d + 1 :=
  Nat.le_add_right _ _

theorem omittedData (k n : Nat) : n ≤ k + n := Nat.le_add_left _ _

abbrev dependentArena : Arena where
  signature := dependentSignature
  Law r := ∀ (X : Type) [d : Fintype X] (x : Fin (@Fintype.card X d + 1)) (n : Nat),
    n ≤ r.readout () ⟨X, d, x⟩ n

def dependentRejected : Realization dependentSignature :=
  realize dependentSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependentRejectedLaw : ¬ dependentArena.Law dependentRejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (h Unit ⟨0, by decide⟩ 1)

def dependentRegistration : Registration dependentArena
    (∀ (X : Type) [Fintype X] (x : Fin (Fintype.card X + 1)) (n : Nat),
      n ≤ x.val + Fintype.card X + n) where
  actual := dependentActual
  bridge := Iff.rfl
  variation := ⟨dependentSource, dependentRejected, dependentRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨dependentRejected, ?_, rfl, dependentRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨Unit, inferInstance, ⟨0, by decide⟩⟩, (0 : Nat), (1 : Nat), ?_⟩
    change 0 + Fintype.card Unit + 0 ≠ 0 + Fintype.card Unit + 1
    omega

abbrev noncanonicalArena : Arena where
  signature := noncanonicalSignature
  Law r := ∀ [d : Inhabited Nat] (n : Nat), n ≤ r.readout () d n

def noncanonicalRejected : Realization noncanonicalSignature :=
  realize noncanonicalSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem noncanonicalRejectedLaw : ¬ noncanonicalArena.Law noncanonicalRejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (@h ⟨7⟩ 1)

def noncanonicalRegistration : Registration noncanonicalArena
    (∀ [d : Inhabited Nat] (n : Nat), n ≤ @default Nat d + n) where
  actual := noncanonicalActual
  bridge := Iff.rfl
  variation := ⟨noncanonicalSource, noncanonicalRejected, noncanonicalRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨noncanonicalRejected, ?_, rfl, noncanonicalRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨7⟩, 0, 1, ?_⟩
    change (7 : Nat) + 0 ≠ 7 + 1
    omega

-- The unused Sort domain still belongs to the complete original statement.
-- Construct Sort 253 without changing the surface elaborator's offset guard.
open Lean Elab Term in
elab "supportDeepSort" : term =>
  return mkSort ((List.range 253).foldl (fun level _ => Level.succ level) .zero)

theorem deepLevelSource (_a _b _c : Unit) (X : supportDeepSort) [d : Inhabited Nat] (n : Nat) :
    n ≤ @default Nat d + n := Nat.le_add_left _ _

abbrev deepLevelArena : Arena where
  signature := noncanonicalSignature
  Law r := ∀ (_a _b _c : Unit) (X : supportDeepSort) [d : Inhabited Nat] (n : Nat),
    n ≤ r.readout () d n

theorem deepLevelRejectedLaw : ¬ deepLevelArena.Law noncanonicalRejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (@h () () () PUnit ⟨7⟩ 1)

def deepLevelRegistration : Registration deepLevelArena
    (∀ (_a _b _c : Unit) (X : supportDeepSort) [d : Inhabited Nat] (n : Nat),
      n ≤ @default Nat d + n) where
  actual := noncanonicalActual
  bridge := Iff.rfl
  variation := ⟨deepLevelSource, noncanonicalRejected, deepLevelRejectedLaw⟩
  sensitivity := ⟨by
    intro i
    refine ⟨noncanonicalRejected, ?_, rfl, deepLevelRejectedLaw⟩
    intro j h
    exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)),
    by intro i; exact nomatch i⟩
  dependence := noncanonicalRegistration.dependence

abbrev multipleSignature : Signature where
  Params := Σ X : Type, Fintype X
  State _ := Nat
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def multipleActual : Realization multipleSignature :=
  realize multipleSignature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e)

def multipleRejected (i : Bool) : Realization multipleSignature :=
  realize multipleSignature (fun j p n => if j = i then 0 else @Fintype.card p.1 p.2 + n)
    (fun e => nomatch e)

abbrev multipleArena : Arena where
  signature := multipleSignature
  Law r := ∀ (X : Type) [d : Fintype X] (n : Nat),
    n ≤ r.readout false ⟨X,d⟩ n ∧ n ≤ r.readout true ⟨X,d⟩ n

theorem multipleRejectedLaw (i : Bool) : ¬ multipleArena.Law (multipleRejected i) := by
  intro h
  have h := h Unit 1
  cases i
  · exact Nat.not_succ_le_zero 0 h.1
  · exact Nat.not_succ_le_zero 0 h.2

def multipleRegistration : Registration multipleArena
    (∀ (X : Type) [Fintype X] (n : Nat),
      (n ≤ Fintype.card X + n) ∧ (n ≤ Fintype.card X + n)) where
  actual := multipleActual
  bridge := Iff.rfl
  variation := ⟨multipleSource, multipleRejected false, multipleRejectedLaw false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨multipleRejected i, ?_, rfl, multipleRejectedLaw i⟩
      intro j h
      funext p n
      simp [multipleRejected, multipleActual, realize, h]
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨Unit, inferInstance⟩, (0 : Nat), (1 : Nat), ?_⟩
    change Fintype.card Unit + 0 ≠ Fintype.card Unit + 1
    omega

-- Enter only this exact closed Prop body; the original theorem remains a named reference.
def namedClaim : Prop := ∀ (X : Type) [Fintype X] (n : Nat), n ≤ Fintype.card X + n
theorem namedSource : namedClaim := source
def namedRegistration : Registration arena namedClaim where
  actual := actual
  bridge := Iff.rfl
  variation := registration.variation
  sensitivity := registration.sensitivity
  dependence := registration.dependence

abbrev transitiveSignature : Signature where
  Params := Σ X : Type, Σ d : Fintype X, @DependentSupport X d
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def transitiveActual : Realization transitiveSignature :=
  realize transitiveSignature (fun _ p n => p.2.2.value.val + n) (fun e => nomatch e)

def transitiveRejected : Realization transitiveSignature :=
  realize transitiveSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev transitiveArena : Arena where
  signature := transitiveSignature
  Law r := ∀ (X : Type) [d : Fintype X] [s : DependentSupport X] (n : Nat),
    n ≤ r.readout () ⟨X, d, s⟩ n

theorem transitiveRejectedLaw : ¬ transitiveArena.Law transitiveRejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (@h Unit inferInstance ⟨⟨0, by decide⟩⟩ 1)

def transitiveRegistration : Registration transitiveArena
    (∀ (X : Type) [Fintype X] [DependentSupport X] (n : Nat),
      n ≤ (DependentSupport.value (X := X)).val + n) where
  actual := transitiveActual
  bridge := Iff.rfl
  variation := ⟨transitiveSource, transitiveRejected, transitiveRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨transitiveRejected, ?_, rfl, transitiveRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨Unit, inferInstance, ⟨⟨0, by decide⟩⟩⟩, 0, 1, ?_⟩
    change (0 : Nat) + 0 ≠ 0 + 1
    omega

-- A named body avoids the independent 64-binder outer-telescope guard.
-- The limit tested here is coordinates + automatic instance support.
def wideClaim64 : Prop := ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 : Nat) [d : Inhabited Nat] (n : Nat),
    n ≤ (@default Nat d + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51 + x52 + x53 + x54 + x55 + x56 + x57 + x58 + x59 + x60 + x61 + x62) + n
theorem wideSource64 : wideClaim64 := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 d n
  exact Nat.le_add_left _ _

def wideClaim65 : Prop := ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : Nat) [d : Inhabited Nat] (n : Nat),
    n ≤ (@default Nat d + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51 + x52 + x53 + x54 + x55 + x56 + x57 + x58 + x59 + x60 + x61 + x62 + x63) + n
theorem wideSource65 : wideClaim65 := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 d n
  exact Nat.le_add_left _ _

-- Exact dictionary correspondence survives definitional equality.
def eqRead (_d : DecidableEq Bool) (n : Nat) : Nat := n
abbrev eqSig : Signature where
  Params := DecidableEq Bool
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance
def eqFaithful : Realization eqSig :=
  realize eqSig (fun _ d n => eqRead d n) (fun e => nomatch e)
def eqReplacement : Realization eqSig :=
  realize eqSig (fun _ _ n => eqRead instDecidableEqBool n) (fun e => nomatch e)
def eqRejected : Realization eqSig :=
  realize eqSig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev eqArena : Arena where
  signature := eqSig
  Law r := ∀ [d : DecidableEq Bool] (n : Nat), n ≤ r.readout () d n
theorem eqRejectedLaw : ¬ eqArena.Law eqRejected := by
  intro h; exact Nat.not_succ_le_zero 0 (h 1)

def dropDict (_ : Inhabited Nat) (n : Nat) := n
abbrev swapSig : Signature where
  Params := Σ _ : Inhabited Nat, Inhabited Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance
def swapFaithful : Realization swapSig :=
  realize swapSig (fun _ p n => dropDict p.1 n + @default Nat p.2) (fun e => nomatch e)
def swapLambda : Realization swapSig :=
  realize swapSig (fun _ p n =>
    (fun (_ : Inhabited Nat) => dropDict p.2 n + @default Nat p.2) p.1) (fun e => nomatch e)
def swapSigma : Realization swapSig :=
  realize swapSig (fun _ p n =>
    dropDict ((⟨p.1, p.2⟩ : Σ _ : Inhabited Nat, Inhabited Nat).2) n + @default Nat p.2)
    (fun e => nomatch e)
def swapRejected : Realization swapSig :=
  realize swapSig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev swapArena : Arena where
  signature := swapSig
  Law r := ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ r.readout () ⟨d1,d2⟩ n
theorem swapRejectedLaw : ¬ swapArena.Law swapRejected := by
  intro h; exact Nat.not_succ_le_zero 0 (@h ⟨7⟩ ⟨11⟩ 1)

-- The original dictionary occurs solely in the source-derived State/Output
-- type, never in the observation body. Its type-level use must still match.
def stateBox (_ : Inhabited Nat) := Nat
theorem typeOnlySource [d : Inhabited Nat] (n : stateBox d) : n = n := rfl
abbrev typeOnlySig : Signature where
  Params := Inhabited Nat
  State d := stateBox d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := stateBox d
  Anchor := Empty
  finiteAnchor := inferInstance
def typeOnlyActual : Realization typeOnlySig :=
  realize typeOnlySig (fun _ _ n => n) (fun e => nomatch e)

-- Abstract scalar actions retain their arbitrary type and original dictionary.
theorem scalarSource (R X : Type) [d : SMul R X] (r : R) (x : X) :
    ((fun d => @SMul.smul R X d r x) d) = r • x := rfl
abbrev scalarSignature : Signature where
  Params := Σ R : Type, Σ X : Type, Σ _ : SMul R X, R
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance
def scalarActual : Realization scalarSignature :=
  realize scalarSignature
    (fun _ p x => @SMul.smul p.1 p.2.1 p.2.2.1 p.2.2.2 x) (fun e => nomatch e)
def scalarErased : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => x) (fun e => nomatch e)

theorem eqSource : ∀ [d : DecidableEq Bool] (n : Nat), n ≤ eqRead d n := by intro d n; exact Nat.le_refl n
def eqSourceRegistration : Registration eqArena (∀ [d : DecidableEq Bool] (n : Nat), n ≤ eqRead d n) where
  actual := eqReplacement
  bridge := Iff.rfl
  variation := ⟨eqSource, eqRejected, eqRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, eqRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by intro i; cases i; exact ⟨instDecidableEqBool, 0, 1, by decide⟩

theorem eqFaithfulSource : ∀ [d : DecidableEq Bool] (n : Nat), n ≤ eqRead d n := by intro d n; exact Nat.le_refl n
def eqFaithfulSourceRegistration : Registration eqArena (∀ [d : DecidableEq Bool] (n : Nat), n ≤ eqRead d n) where
  actual := eqFaithful
  bridge := Iff.rfl
  variation := ⟨eqFaithfulSource, eqRejected, eqRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, eqRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by intro i; cases i; exact ⟨instDecidableEqBool, 0, 1, by decide⟩

theorem swapSource : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2 := by intro d1 d2 n; exact Nat.le_add_right _ _
def swapSourceRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2) where
  actual := swapFaithful
  bridge := Iff.rfl
  variation := ⟨swapSource, swapRejected, swapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by intro i; cases i; exact ⟨⟨⟨7⟩, ⟨11⟩⟩, 0, 1, by decide⟩

theorem swapLambdaSource : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2 := by intro d1 d2 n; exact Nat.le_add_right _ _
def swapLambdaSourceRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2) where
  actual := swapLambda
  bridge := Iff.rfl
  variation := ⟨swapLambdaSource, swapRejected, swapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by intro i; cases i; exact ⟨⟨⟨7⟩, ⟨11⟩⟩, 0, 1, by decide⟩

theorem swapSigmaSource : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2 := by intro d1 d2 n; exact Nat.le_add_right _ _
def swapSigmaSourceRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ dropDict d1 n + @default Nat d2) where
  actual := swapSigma
  bridge := Iff.rfl
  variation := ⟨swapSigmaSource, swapRejected, swapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by intro i; cases i; exact ⟨⟨⟨7⟩, ⟨11⟩⟩, 0, 1, by decide⟩

-- Source-side administrative wrappers must preserve dictionary use positions.
def keep (n : Nat) (_ _ : Inhabited Nat) := n
def replacement (n : Nat) (_ : Inhabited Nat) := dropDict ⟨0⟩ n
theorem wrapper_beta_faithful : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_beta_faithfulRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_beta_faithful, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_beta_descriptor : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_beta_descriptorRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_beta_descriptor, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_beta_actual : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_beta_actualRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => keep n d d) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_beta_actual, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_let_faithful : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_let_faithfulRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_let_faithful, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_let_descriptor : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_let_descriptorRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_let_descriptor, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_let_actual : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_let_actualRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((let f := fun d => keep n d d; f d1)) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_let_actual, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_projection_faithful : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_projection_faithfulRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_projection_faithful, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_projection_descriptor : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_projection_descriptorRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_projection_descriptor, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_projection_actual : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_projection_actualRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ (((fun d => keep n d d, d2).1) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_projection_actual, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_quality_faithful : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_quality_faithfulRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_quality_faithful, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_quality_descriptor : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_quality_descriptorRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_quality_descriptor, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_quality_actual : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_quality_actualRegistration : Registration swapArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), n ≤ ((fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => replacement n p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_quality_actual, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
abbrev lexicalArena : Arena where
  signature := swapSig
  Law r := ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat),
    let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement
    n ≤ r.readout () ⟨d1,d2⟩ (f d1)

theorem wrapper_lexical_faithful : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_lexical_faithfulRegistration : Registration lexicalArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_lexical_faithful, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_lexical_descriptor : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_lexical_descriptorRegistration : Registration lexicalArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_lexical_descriptor, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩
theorem wrapper_lexical_actual : ∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2 := by
  intro d1 d2 n; exact Nat.le_add_right n _
def wrapper_lexical_actualRegistration : Registration lexicalArena (∀ [d1 : Inhabited Nat] [d2 : Inhabited Nat] (n : Nat), let f := fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement; n ≤ (f d1) + @default Nat d2) where
  actual := realize swapSig (fun _ p n => replacement n p.1 + @default Nat p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨wrapper_lexical_actual, swapRejected, swapRejectedLaw⟩
  sensitivity := ⟨by intro i; refine ⟨swapRejected, ?_, rfl, swapRejectedLaw⟩; intro j h; exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i)), by intro i; exact nomatch i⟩
  dependence := by intro i; cases i; exact ⟨⟨⟨0⟩,⟨0⟩⟩, 0, 1, by decide⟩

-- A legal dependent dictionary family: k occurs in the class index.
-- eqReadFin ignores its dictionary computationally; raw capture must still bind it.
def eqReadFin (_d : DecidableEq (Fin 2)) (n : Nat) : Nat := n
abbrev familySig : Signature where
  Params := (k : Nat) → DecidableEq (Fin k)
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance
def familyFaithful : Realization familySig :=
  realize familySig (fun _ d n => eqReadFin (d 2) n) (fun e => nomatch e)
def familyCanonical (k : Nat) : DecidableEq (Fin k) := inferInstance
def familyReplacement : Realization familySig :=
  realize familySig (fun _ _ n => eqReadFin (familyCanonical 2) n) (fun e => nomatch e)
def familyDrop : Realization familySig :=
  realize familySig (fun _ _ n => n) (fun e => nomatch e)
def familyRejected : Realization familySig :=
  realize familySig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev familyArena : Arena where
  signature := familySig
  Law r := ∀ [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat), n ≤ r.readout () d n
theorem familyRejectedLaw : ¬ familyArena.Law familyRejected := by
  intro h
  exact Nat.not_succ_le_zero 0 (@h (fun _ => inferInstance) 1)

theorem familyFaithfulSource [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat) :
    n ≤ eqReadFin (d 2) n := Nat.le_refl n
def familyFaithfulRegistration : Registration familyArena
    (∀ [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat), n ≤ eqReadFin (d 2) n) where
  actual := familyFaithful
  bridge := Iff.rfl
  variation := ⟨familyFaithfulSource, familyRejected, familyRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨familyRejected, ?_, rfl, familyRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    exact ⟨(fun _ => inferInstance), 0, 1, by decide⟩

theorem familyReplacementSource [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat) :
    n ≤ eqReadFin (d 2) n := Nat.le_refl n
def familyReplacementRegistration : Registration familyArena
    (∀ [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat), n ≤ eqReadFin (d 2) n) where
  actual := familyReplacement
  bridge := Iff.rfl
  variation := ⟨familyReplacementSource, familyRejected, familyRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨familyRejected, ?_, rfl, familyRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    exact ⟨(fun _ => inferInstance), 0, 1, by decide⟩

theorem familyDropSource [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat) :
    n ≤ eqReadFin (d 2) n := Nat.le_refl n
def familyDropRegistration : Registration familyArena
    (∀ [d : (k : Nat) → DecidableEq (Fin k)] (n : Nat), n ≤ eqReadFin (d 2) n) where
  actual := familyDrop
  bridge := Iff.rfl
  variation := ⟨familyDropSource, familyRejected, familyRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨familyRejected, ?_, rfl, familyRejectedLaw⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    exact ⟨(fun _ => inferInstance), 0, 1, by decide⟩

end D5.InstanceSupportFixture
"####

def registration : String := r####"import D5.InstanceSupportFixture
import Reg.Support.DependentFamily

open Lean Meta LeanInformationAudit
open D5.InstanceSupportFixture
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.InstanceSupportFixture

register_information_theorem familyFaithfulSource in familyArena
  readout via (realize familySig (fun _ d n => eqReadFin (d 2) n) (fun e => nomatch e))
  realizes familyFaithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

register_information_theorem familyReplacementSource in familyArena
  readout via (realize familySig (fun _ d n => eqReadFin (familyCanonical 2) n) (fun e => nomatch e))
  realizes familyReplacementRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

register_information_theorem familyDropSource in familyArena
  readout via (realize familySig (fun _ d n => n) (fun e => nomatch e))
  realizes familyDropRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

run_meta do
  let info ← getConstInfo ``familyFaithfulSource
  let (scope, work) ← (SourceScope.resolve info {
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] }).run 524288
  let .forallE _ domain _ .instImplicit := info.type
    | throwError "family source instance binder missing"
  unless scope.source.equal info.type && scope.supportRaw.size == 1 &&
      scope.supportRaw[0]!.domain.equal domain && scope.parameterSlots == #[0] &&
      scope.coordinates.isEmpty do throwError "family raw source identity changed"
  logInfo m!"[PASS] legal_family_raw_source support=0 work={work}"

register_information_theorem metadataSource in arena
  readout via (realize signature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e))
  realizes metadataRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[0],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem projectionSource in arena
  readout via (realize signature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e))
  realizes projectionRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[0],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem deepLevelSource in deepLevelArena
  readout via (realize noncanonicalSignature (fun _ p n => p.default + n) (fun e => nomatch e))
  realizes deepLevelRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5}] })
  escape continues (open)

register_information_theorem source in arena
  readout via (realize signature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    coordinates := #[0],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

run_meta do
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == ``source)
    | throwError "support fixture occurrence absent"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "support fixture claim absent"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated certificate := record.result
    | throwError "support fixture rejected: {(← TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.continuation.any (·.kind == "open") &&
      record.escape.bridgeKind == "source-equivalence" && certificate.sourceBinding.isSome do
    throwError "support fixture four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "support selection absent"
  let (scope, _) ← (SourceScope.resolve (← getConstInfo ``source) selection).run 524288
  unless scope.parameterSlots == #[0, 1] && scope.support.size == 1 &&
      scope.coordinates.size == 1 do throwError "support fixture closure differs"
  logInfo m!"[PASS] original_fintype_support_declared_validated {certificate.sourceBinding.get!}"

register_information_theorem dependentSource in dependentArena
  readout via (realize dependentSignature
    (fun _ p n => p.2.2.val + @Fintype.card p.1 p.2.1 + (n : Nat)) (fun e => nomatch e))
  realizes dependentRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    coordinates := #[0,2]
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 3}] })
  escape continues (open)

register_information_theorem noncanonicalSource in noncanonicalArena
  readout via (realize noncanonicalSignature (fun _ p n => p.default + n) (fun e => nomatch e))
  realizes noncanonicalRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    coordinates := #[]
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

register_information_theorem multipleSource in multipleArena
  readout via (realize multipleSignature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e))
  realizes multipleRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    coordinates := #[0]
    readouts := #[
      {path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2},
      {path := #["body", "body", "body", "arg", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem namedSource in arena
  readout via (realize signature (fun _ p n => @Fintype.card p.1 p.2 + n) (fun e => nomatch e))
  realizes namedRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    «definition» := some { owner := `D5.InstanceSupportFixture, name := ``namedClaim, path := #[] }
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem transitiveSource in transitiveArena
  readout via (realize transitiveSignature (fun _ p n => p.2.2.value.val + n) (fun e => nomatch e))
  realizes transitiveRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 3}] })
  escape continues (open)

run_meta do
  for name in #[``source, ``dependentSource, ``noncanonicalSource, ``multipleSource,
      ``namedSource, ``transitiveSource] do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "native occurrence absent {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "native claim absent {name}"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated _ := record.result
      | throwError "native certificate rejected: {(← TemplateBinding.recordJson record).compress}"

private def rejects (label : String) (action : SourceScope.M Unit) : MetaM Unit := do
  let rejected ← try discard <| action.run 524288; pure false catch _ => pure true
  unless rejected do throwError "accepted negative support control {label}"
  logInfo m!"[PASS] support rejects {label}"

run_meta do
  let owner := `D5.InstanceSupportFixture
  let info ← getConstInfo ``source
  let selected : SourceSelection := {
    owner := owner, coordinates := #[0],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] }
  rejects "explicit dictionary coordinate" <| discard <| SourceScope.resolve info
    {selected with coordinates := #[0,1]}
  rejects "omitted data" <| discard <| SourceScope.resolve (← getConstInfo ``omittedData)
    { owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] }
  rejects "explicit dictionary support" <| discard <| SourceScope.resolve (← getConstInfo ``explicitDictionary) selected
  let (scope, _) ← (SourceScope.resolve info selected).run 524288
  let namedSelection : SourceSelection := {
    owner := owner, «definition» := some {owner := owner, name := ``namedClaim}
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] }
  rejects "named definition owner" <| discard <| SourceScope.resolve (← getConstInfo ``namedSource)
    {namedSelection with «definition» := some {owner := `D5.Other, name := ``namedClaim}}
  rejects "named definition body reference" <| discard <| SourceScope.resolve (← getConstInfo ``namedSource)
    {namedSelection with «definition» := some {owner := owner, name := ``wideClaim64}}
  rejects "named definition path" <| discard <| SourceScope.resolve (← getConstInfo ``namedSource)
    {namedSelection with «definition» := some {owner := owner, name := ``namedClaim, path := #["arg"]}}
  rejects "mismatching actual" <| SourceScope.validateFields scope (mkConst ``signature) (mkConst ``rejected)
  let dependentSelection : SourceSelection := {
    owner := owner, coordinates := #[0,2],
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 3}] }
  let (dependentScope, _) ← (SourceScope.resolve (← getConstInfo ``dependentSource) dependentSelection).run 524288
  unless dependentScope.parameterSlots == #[0,1,2] do throwError "dependent closure differs"
  discard <| (SourceScope.validateFields dependentScope (mkConst ``dependentSignature)
    (mkConst ``dependentActual)).run 524288
  let (multipleScope, _) ← (SourceScope.resolve (← getConstInfo ``multipleSource)
    {selected with readouts := #[
      {path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2},
      {path := #["body", "body", "body", "arg", "arg"], stateBinder := 2}]}).run 524288
  unless multipleScope.support.size == 1 && multipleScope.readouts.size == 2 do
    throwError "multiple readouts did not share exact ancestor"
  let (noncanonicalScope, _) ← (SourceScope.resolve (← getConstInfo ``noncanonicalSource)
    {owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}]}).run 524288
  discard <| (SourceScope.validateFields noncanonicalScope (mkConst ``noncanonicalSignature)
    (mkConst ``noncanonicalActual)).run 524288
  rejects "canonical replacement" <| SourceScope.validateFields noncanonicalScope
    (mkConst ``noncanonicalSignature) (mkConst ``canonicalReplacement)
  for target in #[``dictionaryState, ``proofState] do
    rejects "dictionary or proof state" <| discard <| SourceScope.resolve (← getConstInfo target)
      {owner := owner, coordinates := #[], readouts := #[{path := #["body", "arg"], stateBinder := 0}]}
  rejects "dictionary output" <| discard <| SourceScope.resolve (← getConstInfo ``dictionaryOutput)
    {owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "fn", "arg", "arg"], stateBinder := 1}]}
  rejects "proof coordinate" <| discard <| SourceScope.resolve (← getConstInfo ``proofOutput)
    {owner := owner, coordinates := #[0], readouts := #[{path := #["body", "body", "arg", "arg"], stateBinder := 1}]}
  rejects "proof output" <| discard <| SourceScope.resolve (← getConstInfo ``proofOutput)
    {owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "fn", "arg", "arg"], stateBinder := 1}]}
  rejects "sibling support" <| discard <| SourceScope.resolve (← getConstInfo ``siblingSupport)
    {owner := owner, coordinates := #[], readouts := #[
      {path := #["fn", "arg", "body", "body", "arg"], stateBinder := 1},
      {path := #["arg", "body", "body", "arg"], stateBinder := 1}]}
  rejects "proof-valued class support" <| discard <| SourceScope.resolve (← getConstInfo ``proofClassSource)
    {owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}]}
  let (letScope, _) ← (SourceScope.resolve (← getConstInfo ``letSource)
    {owner := owner, coordinates := #[], readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 1}]}).run 524288
  unless letScope.support.size == 1 && letScope.parameterSlots == #[0] do
    throwError "lexical let did not recover exact original support"
  discard <| (SourceScope.validateFields letScope (mkConst ``noncanonicalSignature)
    (mkConst ``noncanonicalActual)).run 524288
  let (operandScope, _) ← (SourceScope.resolve (← getConstInfo ``operandSource)
    {owner := owner, coordinates := #[], readouts := #[{
      path := #["body", "arg"], stateBinder := 0, stateOperand := some #["fn", "arg"]}]}).run 524288
  unless operandScope.support.isEmpty && operandScope.parameterSlots.isEmpty do
    throwError "abstracted state operand leaked its dictionary into support"
  let (transitive, _) ← (SourceScope.resolve (← getConstInfo ``transitiveSource)
    {owner := owner, coordinates := #[0], readouts := #[
      {path := #["body", "body", "body", "body", "arg"], stateBinder := 3}]}).run 524288
  unless transitive.parameterSlots == #[0,1,2] && transitive.support.size == 2 do
    throwError "transitive support order/closure differs"
  let .forallE x xt (.forallE d dt body .instImplicit) xb := info.type
    | throwError "unexpected original fixture telescope"
  rejects "binder mode mutation" <| SourceScope.reconstruct info.type
    (.forallE x xt (.forallE d dt body .default) xb)
  logInfo "[PASS] dependent coordinate, shared ancestor, noncanonical and transitive support"

run_meta do
  let owner := `D5.InstanceSupportFixture
  let boundary (count : Nat) (name claim : Name) : SourceScope.M SourceScope.Scope := do
    SourceScope.resolve (← getConstInfo name) {
      owner := owner
      «definition» := some {owner := owner, name := claim, path := #[]}
      coordinates := (List.range (count - 1)).toArray
      readouts := #[{path := (Array.replicate (count + 1) "body").push "arg", stateBinder := count}] }
  let (scope, _) ← (boundary 64 ``wideSource64 ``wideClaim64).run 524288
  unless scope.coordinates.size == 63 && scope.support.size == 1 &&
      scope.parameterSlots == (List.range 64).toArray do
    throwError "combined 64-binder boundary was not reached"
  let reason ← try
      discard <| (boundary 65 ``wideSource65 ``wideClaim65).run 524288
      pure "accepted"
    catch e => e.toMessageData.toString
  unless reason.contains "E8.source_binders" do
    throwError "combined 65-binder boundary failed for wrong reason: {reason}"
  logInfo "[PASS] combined_binders_64_accepted_65_rejected"


register_information_theorem eqSource in eqArena
  readout via (realize eqSig (fun _ _ n => eqRead instDecidableEqBool n) (fun e => nomatch e))
  realizes eqSourceRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

register_information_theorem eqFaithfulSource in eqArena
  readout via (realize eqSig (fun _ d n => eqRead d n) (fun e => nomatch e))
  realizes eqFaithfulSourceRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] })
  escape continues (open)

register_information_theorem swapSource in swapArena
  readout via (realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes swapSourceRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem swapLambdaSource in swapArena
  readout via (realize swapSig (fun _ p n => (fun (_ : Inhabited Nat) => dropDict p.2 n + @default Nat p.2) p.1) (fun e => nomatch e))
  realizes swapLambdaSourceRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

register_information_theorem swapSigmaSource in swapArena
  readout via (realize swapSig (fun _ p n => dropDict ((⟨p.1,p.2⟩ : Σ _ : Inhabited Nat, Inhabited Nat).2) n + @default Nat p.2) (fun e => nomatch e))
  realizes swapSigmaSourceRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}] })
  escape continues (open)

run_meta do
  for (name, valid) in #[(``familyFaithfulSource, true), (``familyReplacementSource, false),
      (``familyDropSource, false), (``eqSource, false), (``eqFaithfulSource, true),
      (``swapSource, true), (``swapLambdaSource, false), (``swapSigmaSource, false)] do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "capture regression missing occurrence {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "capture regression missing claim {name}"
    let record ← TemplateBinding.assess event (some claim)
    match record.result with
    | .declaredValidated _ => unless valid do throwError "accepted dictionary replacement {name}"
    | .declaredUnresolved diagnostic =>
      unless !valid && diagnostic.contains "source.actual_support_link" do
        throwError "wrong capture regression outcome {name}: {diagnostic}"
    | _ => throwError "missing capture regression outcome {name}"
    logInfo m!"[PASS] exact_dictionary_capture {name} valid={valid}"
  let (scope, _) ← (SourceScope.resolve (← getConstInfo ``typeOnlySource) {
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "arg"], stateBinder := 1}] }).run 524288
  unless scope.support.size == 1 do throwError "type-only dictionary support missing"
  discard <| (SourceScope.validateFields scope (mkConst ``typeOnlySig)
    (mkConst ``typeOnlyActual)).run 524288
  logInfo "[PASS] support_only_in_state_and_output_type"
  let (scalarScope, _) ← (SourceScope.resolve (← getConstInfo ``scalarSource) {
    owner := `D5.InstanceSupportFixture, coordinates := #[0,1,3],
    readouts := #[{path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 4}] }).run 524288
  unless scalarScope.parameterSlots == #[0,1,2,3] && scalarScope.support.size == 1 do
    throwError "generic scalar support closure differs"
  discard <| (SourceScope.validateFields scalarScope (mkConst ``scalarSignature)
    (mkConst ``scalarActual)).run 524288
  rejects "generic scalar dictionary erasure" <| SourceScope.validateFields scalarScope
    (mkConst ``scalarSignature) (mkConst ``scalarErased)
  logInfo "[PASS] generic_scalar_source_beta_faithful"

-- Pure encoder controls, separate from the admitted report inventory. Native
-- bindingIdentity supplies the oracle for JSON escaping and structural Names.
run_meta do
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == ``source)
    | throwError "encoding control occurrence missing"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "encoding control claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated certificate := record.result | throwError "encoding control not validated"
  let mut rows := #[]
  for name in #[`plain, Name.str (Name.num `Name 17) "λ😀.\"\\\t\n\r"] do
    let source := Json.mkObj [
      ("z", toJson (String.singleton (Char.ofNat 1) ++ String.singleton (Char.ofNat 8) ++ "\t\n\r\"\\λ😀")),
      ("a", toJson #["lp(ns(n0,7:u,type=))", "lp(ns(n0,7:λ,😀))"])]
    let certificate := { certificate with
      key := { certificate.key with root := name }
      sourceBinding := some source }
    let .ok (identity, _) := TemplateAudit.bindingIdentity event.statementIdentity certificate 524288
      | throwError "encoding control exceeded existing budget"
    rows := rows.push (← TemplateBinding.recordJson { record with
      result := .declaredValidated { certificate with evidenceRef := identity } })
  IO.FS.writeFile ((← Repository.root) / "binding-identity-controls.json") (Json.arr rows).compress

-- Exercise descriptor and actual independently through production assessment.
register_information_theorem wrapper_beta_faithful in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_beta_faithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_beta_descriptor in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_beta_descriptorRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_beta_actual in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_beta_actualRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_let_faithful in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_let_faithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_let_descriptor in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_let_descriptorRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_let_actual in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_let_actualRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_projection_faithful in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_projection_faithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_projection_descriptor in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.2 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_projection_descriptorRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_projection_actual in swapArena
  readout via (realize swapSig (fun _ p n => keep n p.1 p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_projection_actualRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_quality_faithful in swapArena
  readout via (realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_quality_faithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_quality_descriptor in swapArena
  readout via (realize swapSig (fun _ p n => replacement n p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_quality_descriptorRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_quality_actual in swapArena
  readout via (realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_quality_actualRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_lexical_faithful in lexicalArena
  readout via (realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_lexical_faithfulRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_lexical_descriptor in lexicalArena
  readout via (realize swapSig (fun _ p n => replacement n p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_lexical_descriptorRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)
register_information_theorem wrapper_lexical_actual in lexicalArena
  readout via (realize swapSig (fun _ p n => (fun d => (fun (_ : Nat → Inhabited Nat → Nat) => dropDict d n) replacement) p.1 + @default Nat p.2) (fun e => nomatch e))
  realizes wrapper_lexical_actualRegistration
  escape from source ({
    owner := `D5.InstanceSupportFixture, coordinates := #[],
    readouts := #[{path := #["body", "body", "body", "body", "arg"], stateBinder := 2}]})
  escape continues (open)

run_meta do
  for name in #[``wrapper_beta_faithful, ``wrapper_beta_descriptor, ``wrapper_beta_actual, ``wrapper_let_faithful, ``wrapper_let_descriptor, ``wrapper_let_actual, ``wrapper_projection_faithful, ``wrapper_projection_descriptor, ``wrapper_projection_actual, ``wrapper_quality_faithful, ``wrapper_quality_descriptor, ``wrapper_quality_actual, ``wrapper_lexical_faithful, ``wrapper_lexical_descriptor, ``wrapper_lexical_actual] do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "wrapper occurrence absent {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "wrapper claim absent {name}"
    let record ← TemplateBinding.assess event (some claim)
    let valid := name.toString.endsWith "_faithful"
    match record.result with
    | .declaredValidated _ => unless valid do throwError "accepted wrong dictionary {name}"
    | .declaredUnresolved diagnostic =>
      unless !valid && diagnostic.contains "source.actual_support_link" do
        throwError "wrong wrapper outcome {name}: {diagnostic}"
    | _ => throwError "missing wrapper outcome {name}"
    logInfo m!"[PASS] source_wrapper {name} valid={valid}"

end Reg.D5.InstanceSupportFixture
"####

end LeanInformationAuditRegTests.InstanceSupportNative
