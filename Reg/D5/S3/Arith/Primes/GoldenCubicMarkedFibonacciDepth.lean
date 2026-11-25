import D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth

open _root_.D5.S1.Scale (goldenLucas)
open _root_.D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
private abbrev Residue (q : Params) := ZMod (q.1^(q.2.2+1))

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params Residue Residue

def actual : Realization signature :=
  realize signature
    (fun _ q r => evalMod (q.1^(q.2.2+1)) (goldenLucas (3^q.2.1)) r)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ q r => evalMod (q.1^(q.2.2+1)) (goldenLucas (3^q.2.1)) r + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p i j k : ℕ) (b : ℤ)
    (_hp : p.Prime) (_hp3 : 3 < p) (_hi : 1 ≤ i) (_hij : i < j)
    (_hpi : (p:ℤ) ∣ goldenLucas (3^i)^2+3) (_hb : b=0 ∨ b=3 ∨ b= -3),
    ∃ r : ZMod (p^(k+1)),
      R.readout () ⟨p,j,k⟩ r = 0 ∧
      ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p) r = (b : ZMod p) ∧
      (r = (b : ZMod (p^(k+1))) ↔ (p:ℤ)^(k+1) ∣ (Nat.fib (6*3^i) : ℤ)) ∧
      ∀ s : ZMod (p^(k+1)), evalMod (p^(k+1)) (goldenLucas (3^j)) s = 0 →
        ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p) s = (b : ZMod p) →
        s = r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hB : (19:ℤ) ∣ goldenLucas (3^1)^2+3 := by decide +kernel
  obtain ⟨r,hroot,hmark,_,_⟩ := h 19 1 2 0 0 (by decide) (by decide) (by decide)
    (by decide) hB (Or.inl rfl)
  have hz : r = 0 := by
    have hk := hmark
    change ZMod.castHom (dvd_rfl : 19 ∣ 19) (ZMod 19) r = 0 at hk
    simpa only [ZMod.castHom_self, RingHom.id_apply] using hk
  have he := hroot
  rw [hz] at he
  exact (by decide +kernel :
    evalMod (19^(0+1)) (goldenLucas (3^2)) 0 + 1 ≠ 0) he

private theorem actual_dependence :
    actual.readout () ⟨19,2,0⟩ 0 ≠ actual.readout () ⟨19,2,0⟩ 1 := by
  change evalMod (19^(0+1)) (goldenLucas (3^2)) 0 ≠
    evalMod (19^(0+1)) (goldenLucas (3^2)) 1
  decide +kernel

def family : Registration arena (type_of% @fibonacci_marked_residue) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fibonacci_marked_residue,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨⟨19,2,0⟩,0,1,actual_dependence⟩

/-- Select the actual cubic evaluation under the root binder. -/
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@fibonacci_marked_residue) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth.fibonacci_marked_residue.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
    definition := none
    coordinates := #[0,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body",
        "arg","body","fn","arg","fn","arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth
