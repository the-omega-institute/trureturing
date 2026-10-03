import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.RationalPostprocessor
import Reg.Support.BoundedRunSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.RationalPostprocessor

open _root_.PredictiveThermodynamic _root_.Lax51Proofs.RamToTM
open Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (xs : List Bool) (e : Nat)
    (divisible : 3 ∣ msbValue (true :: xs))
    (oddNumerator : 0 < e → Odd (msbValue (true :: xs))),
    Nonempty (TM2OutputsInTime postMachine (responseWord xs e)
      (some (binaryWord ((responseOutput xs e).map (r.readout ()))))
      (4 * (responseWord xs e).length + 4)) ∧
    msbValue (responseOutput xs e) =
      if e = 0 then 2 * (msbValue (true :: xs) / 3)
      else (msbValue (true :: xs) / 3) / 2 ^ (e - 1)

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

theorem trace_reaches {σ : Type} (f : σ → Option σ) :
    ∀ k a b, (flip bind f)^[k] (some a) = some b → Reaches f a b := by
  have noneStable : ∀ k, (flip bind f)^[k] none = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [Function.iterate_succ_apply, flip] using ih
  intro k
  induction k with
  | zero =>
    intro a b trace
    have h : a = b := Option.some.inj trace
    subst b
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro a b trace
    simp only [Function.iterate_succ_apply, flip, Option.bind_some] at trace
    change (flip bind f)^[k] (f a) = some b at trace
    cases h : f a with
    | none => rw [h, noneStable] at trace; cases trace
    | some a' =>
      rw [h] at trace
      exact Relation.ReflTransGen.head h (ih a' b trace)

theorem terminal_unique {σ : Type} (f : σ → Option σ) {a b c : σ} {s t : Nat}
    (left : EvalsToInTime f a (some b) s) (right : EvalsToInTime f a (some c) t)
    (leftTerminal : f b = none) (rightTerminal : f c = none) : b = c := by
  apply Part.mem_unique
  · exact mem_eval.mpr ⟨trace_reaches f left.steps a b left.evals_in_steps, leftTerminal⟩
  · exact mem_eval.mpr ⟨trace_reaches f right.steps a c right.evals_in_steps, rightTerminal⟩

def sourceLaw : arena.Law symbols := by
  intro xs e divisible oddNumerator
  change Nonempty (TM2OutputsInTime postMachine (responseWord xs e)
    (some (binaryWord ((responseOutput xs e).map (fun b => b))))
    (4 * (responseWord xs e).length + 4)) ∧ _
  rw [List.map_id']
  exact dyadic_response_run xs e divisible oddNumerator

def erased_fails : ¬arena.Law erased := by
  intro all
  obtain ⟨bad⟩ := (all [true] 0 (by decide) (by intro h; omega)).1
  obtain ⟨good⟩ := (dyadic_response_run [true] 0 (by decide) (by intro h; omega)).1
  have same := terminal_unique postMachine.step good bad (by rfl) (by rfl)
  have output := congrArg (fun c : postMachine.Cfg => c.stk .output) same
  have impossible : ([ResponseSymbol.one, .zero] : List ResponseSymbol) = [.zero, .zero] := by
    simpa [arena, erased, cutRealization, responseOutput, canonicalBinary, scan,
      advance, quotientBit, nextRemainder, binaryWord, bitSymbol, haltList, postMachine]
      using output
  cases impossible

def variation : FiniteLawVariation arena := ⟨symbols, erased, sourceLaw, erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : Bool, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨false, true, by change false ≠ true; decide⟩

theorem _root_._private.Reg.D5.S0.Computability.RationalPostprocessor.0.PredictiveThermodynamic.dyadic_response_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.RationalPostprocessor.arena (∀ (xs : List.{0} Bool) (e : Nat) (divisible : @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs))) (oddNumerator : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) e → @Odd.{0} Nat Nat.instSemiring (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs))), And (Nonempty.{1} (Turing.TM2OutputsInTime PredictiveThermodynamic.postMachine (PredictiveThermodynamic.responseWord xs e) (@Option.some.{0} (List.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.postMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.postMachine))) (PredictiveThermodynamic.binaryWord (PredictiveThermodynamic.responseOutput xs e))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol (PredictiveThermodynamic.responseWord xs e))) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))) (@Eq.{1} Nat (Lax51Proofs.RamToTM.msbValue (PredictiveThermodynamic.responseOutput xs e)) (@ite.{1} Nat (@Eq.{1} Nat e (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (instDecidableEqNat e (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) e (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) Reg.D5.S0.Computability.RationalPostprocessor.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => dyadic_response_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.dyadic_response_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalPostprocessor") 0) "PredictiveThermodynamic") "dyadic_response_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalPostprocessor") 0) "PredictiveThermodynamic") "dyadic_response_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.dyadic_response_run.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.RationalPostprocessor
