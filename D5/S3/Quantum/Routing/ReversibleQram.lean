/- GID: D5/S3/Quantum/Routing/ReversibleQram
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/ReversibleQram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reversible Boolean routing and coherent clean-workspace memory queries at every depth. -/

module

public import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Total Boolean routing by the Toffoli/CNOT network of Arunachalam et al., Section IV. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Quantum.Routing.ReversibleQram

/-- Binary addresses, with a unique empty address at depth zero. -/
def Address : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Address n

/-- In-place routing wires: each split replaces one enabled wire and one scratch wire. -/
def Wires : ℕ → Type
  | 0 => Bool
  | n + 1 => Wires n × Wires n

/-- The wire available as the input to the next split. -/
def root : (n : ℕ) → Wires n → Bool
  | 0, w => w
  | n + 1, w => root n w.1

/-- All scratch wires are zero; the distinguished input wire has value `e`. -/
def clean : (n : ℕ) → Bool → Wires n
  | 0, e => e
  | n + 1, e => (clean n e, clean n false)

/-- XOR on the distinguished input wire, also defined on dirty configurations. -/
def xorRoot : (n : ℕ) → Bool → Equiv.Perm (Wires n)
  | 0, b => (show Function.Involutive (fun x => xor x b) from
      by intro x; cases x <;> cases b <;> rfl).toPerm _
  | n + 1, b => Equiv.prodCongr (xorRoot n b) (Equiv.refl _)

private lemma xorRoot_clean (n : ℕ) (b e : Bool) :
    xorRoot n b (clean n e) = clean n (xor e b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun x => (x, clean n false)) ih

private lemma root_clean (n : ℕ) (e : Bool) : root n (clean n e) = e := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Toffoli from the address and the left root into the right scratch root,
then CNOT from the right root into the left root. -/
def split (n : ℕ) (b : Bool) : Equiv.Perm (Wires (n + 1)) :=
  (Equiv.prodCongrRight fun l => xorRoot n (b && root n l)).trans
    (Equiv.prodCongrLeft fun r => xorRoot n (root n r))

/-- Actual recursive local-gate network, without an initialization precondition. -/
def route : (n : ℕ) → Address n → Equiv.Perm (Wires n)
  | 0, _ => Equiv.refl _
  | n + 1, a => (split n a.1).trans
      (Equiv.prodCongr (route n a.2) (route n a.2))

/-- The specification, separate from the gate network. -/
def oneHot : (n : ℕ) → Address n → Bool → Wires n
  | 0, _, e => e
  | n + 1, a, e =>
      (oneHot n a.2 (e && !a.1), oneHot n a.2 (e && a.1))

private lemma split_clean (n : ℕ) (b e : Bool) :
    split n b (clean (n + 1) e) =
      (clean n (e && !b), clean n (e && b)) := by
  change (xorRoot n (root n (xorRoot n (b && root n (clean n e)) (clean n false)))
      (clean n e), xorRoot n (b && root n (clean n e)) (clean n false)) = _
  simp only [root_clean, xorRoot_clean]
  cases b <;> cases e <;> rfl

/-- Operational induction through the Toffoli/CNOT network. -/
private theorem route_clean (n : ℕ) (a : Address n) (e : Bool) :
    route n a (clean n e) = oneHot n a e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
      change (Equiv.prodCongr (route n a.2) (route n a.2))
        (split n a.1 (clean (n + 1) e)) = _
      rw [split_clean]
      exact Prod.ext (ih a.2 (e && !a.1)) (ih a.2 (e && a.1))

end D5.S3.Quantum.Routing.ReversibleQram
