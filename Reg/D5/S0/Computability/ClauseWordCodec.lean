import D5.S0.Computability.ClauseWordCodec
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClauseWordCodec

open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.ClauseCodec
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ physical w n (F : UnaryFormula n),
    readWord physical (w.map (r.readout ())) = some ⟨n, F⟩ ↔
      w = encodeWord physical F ∧ ∀ c ∈ F, c.length ≤ 3

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro physical w n F
  change readWord physical (w.map (fun b => b)) = some ⟨n, F⟩ ↔ _
  rw [List.map_id']
  exact codec_exact physical w n F

def erased_fails : ¬ arena.Law erased := by
  intro h
  have bad := (h false (encodeWord false (n := 1) []) 1 []).mpr ⟨rfl, by simp⟩
  change readWord false ((encodeWord false (n := 1) []).map (fun _ => false)) =
    some ⟨1, []⟩ at bad
  have impossible : (0 : Nat) = 1 := by
    have p := congrArg (fun x : Option (Σ n, UnaryFormula n) => x.map Sigma.fst) bad
    simpa [encodeWord, bodyWord, readWord, readFixed, readUnary, readBody, bind, Option.bind] using p
  contradiction

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
  ⟨false, true, Bool.false_ne_true⟩

register_information_theorem _root_.PredictiveThermodynamic.ClauseCodec.codec_exact in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => codec_exact⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.ClauseWordCodec
