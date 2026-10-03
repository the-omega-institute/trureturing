import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.RationalResponseRefinement
import Reg.D5.S0.Computability.RationalPostprocessor
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.RationalResponseRefinement
open _root_.PredictiveThermodynamic _root_.Lax51Proofs.RamToTM Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype ResponseSymbol
  signature := cutSignature ResponseSymbol ResponseSymbol
  Law r := ∀ w,
    Nonempty (TM2OutputsInTime postMachine w
      (some ((binaryWord (totalPostOutput w)).map (r.readout ()))) (3*w.length+10)) ∧
    (∀ (xs : List Bool) (e : Nat), w = responseWord xs e →
      3 ∣ msbValue (true::xs) → (0 < e → Odd (msbValue (true::xs))) →
      msbValue (totalPostOutput w) =
        if e=0 then 2*(msbValue (true::xs)/3)
        else (msbValue (true::xs)/3)/2^(e-1)) ∧
    (¬ suitableResponse w → totalPostOutput w = [false]) ∧
    (totalPostOutput w = [false] ∨ ∃ xs : List Bool, totalPostOutput w = true::xs)

def symbols : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun _ => ResponseSymbol.one)

def sourceLaw : arena.Law symbols := by
  intro w
  change Nonempty (TM2OutputsInTime postMachine w
    (some ((binaryWord (totalPostOutput w)).map (fun b => b))) (3*w.length+10)) ∧ _
  rw [List.map_id']
  exact post_word_run w

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := (law []).1
  obtain ⟨good⟩ := (post_word_run []).1
  have same := RationalPostprocessor.terminal_unique postMachine.step good bad (by rfl) (by rfl)
  have output := congrArg (fun c : postMachine.Cfg => c.stk .output) same
  have impossible : ([ResponseSymbol.zero] : List ResponseSymbol) = [.one] := output
  cases impossible

def variation : FiniteLawVariation arena := ⟨symbols,erased,sourceLaw,erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r,r',hr,hr'⟩ := variation
    refine ⟨r,r',?_,?_,⟨fun _ => hr',fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : ResponseSymbol, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨.zero,.one,by change ResponseSymbol.zero ≠ .one; decide⟩

private theorem _root_.PredictiveThermodynamic.post_word_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.RationalResponseRefinement.arena (∀ (w : List.{0} PredictiveThermodynamic.ResponseSymbol), And (Nonempty.{1} (Turing.TM2OutputsInTime PredictiveThermodynamic.postMachine w (@Option.some.{0} (List.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.postMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.postMachine))) (PredictiveThermodynamic.binaryWord (PredictiveThermodynamic.totalPostOutput w))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol w)) (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))) (And (∀ (xs : List.{0} Bool) (e : Nat), @Eq.{1} (List.{0} PredictiveThermodynamic.ResponseSymbol) w (PredictiveThermodynamic.responseWord xs e) → @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs)) → (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) e → @Odd.{0} Nat Nat.instSemiring (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs))) → @Eq.{1} Nat (Lax51Proofs.RamToTM.msbValue (PredictiveThermodynamic.totalPostOutput w)) (@ite.{1} Nat (@Eq.{1} Nat e (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (instDecidableEqNat e (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (Lax51Proofs.RamToTM.msbValue (@List.cons.{0} Bool Bool.true xs)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) e (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) (And (Not (PredictiveThermodynamic.suitableResponse w) → @Eq.{1} (List.{0} Bool) (PredictiveThermodynamic.totalPostOutput w) (@List.cons.{0} Bool Bool.false (@List.nil.{0} Bool))) (Or (@Eq.{1} (List.{0} Bool) (PredictiveThermodynamic.totalPostOutput w) (@List.cons.{0} Bool Bool.false (@List.nil.{0} Bool))) (@Exists.{1} (List.{0} Bool) fun (xs : List.{0} Bool) => @Eq.{1} (List.{0} Bool) (PredictiveThermodynamic.totalPostOutput w) (@List.cons.{0} Bool Bool.true xs)))))) Reg.D5.S0.Computability.RationalResponseRefinement.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw,fun _ => post_word_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.post_word_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (ResponseSymbol)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalResponseRefinement") 0) "PredictiveThermodynamic") "post_word_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalResponseRefinement") 0) "PredictiveThermodynamic") "post_word_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.post_word_run.__primitive_realization)⟩,
  readout := some (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (ResponseSymbol),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.RationalResponseRefinement
