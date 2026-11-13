/- GID: D5/S3/Quantum/Routing/ReversibleQram
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/ReversibleQram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reversible Boolean routing and coherent clean-workspace memory queries at every depth. -/

module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Units.Equiv

/-! Total Boolean routing by the Toffoli/CNOT network of Arunachalam et al., Section IV. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Quantum.Routing.ReversibleQram

open Matrix

/-- Binary addresses, with a unique empty address at depth zero. -/
abbrev Address : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Address n

/-- In-place routing wires: each split replaces one enabled wire and one scratch wire. -/
abbrev Wires : ℕ → Type
  | 0 => Bool
  | n + 1 => Wires n × Wires n

instance addressFintype : (n : ℕ) → Fintype (Address n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := addressFintype n; inferInstanceAs (Fintype (Bool × Address n))

instance wiresFintype : (n : ℕ) → Fintype (Wires n)
  | 0 => inferInstanceAs (Fintype Bool)
  | n + 1 => letI := wiresFintype n; inferInstanceAs (Fintype (Wires n × Wires n))

instance addressDecidableEq : (n : ℕ) → DecidableEq (Address n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => letI := addressDecidableEq n; inferInstanceAs (DecidableEq (Bool × Address n))

instance wiresDecidableEq : (n : ℕ) → DecidableEq (Wires n)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | n + 1 => letI := wiresDecidableEq n; inferInstanceAs (DecidableEq (Wires n × Wires n))


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

/-- Read the wire indexed by a binary address. -/
def leaf : (n : ℕ) → Wires n → Address n → Bool
  | 0, w, _ => w
  | n + 1, w, a => leaf n (if a.1 then w.2 else w.1) a.2

private lemma oneHot_leaf (n : ℕ) (a i : Address n) (e : Bool) :
    leaf n (oneHot n a e) i = if i = a then e else false := by
  induction n generalizing e with
  | zero => have : i = a := @Subsingleton.elim Unit _ i a; simp [leaf, oneHot, this]
  | succ n ih =>
      rcases a with ⟨b, a⟩
      rcases i with ⟨c, i⟩
      cases b <;> cases c <;> cases e <;> simp [leaf, oneHot, ih, Prod.mk.injEq]

variable {G : Type} [AddCommGroup G]

/-- Sum of the enabled leaf data, used to describe the effect of the gate sequence. -/
def readAmount : (n : ℕ) → (Address n → G) → Wires n → G
  | 0, D, w => if w = true then D () else 0
  | n + 1, D, w =>
      readAmount n (fun a => D (false, a)) w.1 +
      readAmount n (fun a => D (true, a)) w.2

/-- Sequential leaf-controlled additions. At a leaf, the wire controls one translation.
At a fork, read the left subtree and then the right subtree into the same bus. -/
def readLeaves : (n : ℕ) → (Address n → G) → Equiv.Perm (Wires n × G)
  | 0, D => Equiv.prodCongrRight fun w =>
      if w = true then Equiv.addRight (D ()) else Equiv.refl _
  | n + 1, D =>
      let shuffle := (Equiv.prodAssoc (Wires n) (Wires n) G).trans
        ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm (Wires n) G)).trans
          (Equiv.prodAssoc (Wires n) G (Wires n)).symm)
      (shuffle.trans ((Equiv.prodCongr (readLeaves n (fun a => D (false, a)))
        (Equiv.refl _)).trans shuffle.symm)).trans
        ((Equiv.prodAssoc (Wires n) (Wires n) G).trans
          ((Equiv.prodCongr (Equiv.refl _)
            (readLeaves n (fun a => D (true, a)))).trans
              (Equiv.prodAssoc (Wires n) (Wires n) G).symm))

private lemma readLeaves_apply (n : ℕ) (D : Address n → G) (w : Wires n) (r : G) :
    readLeaves n D (w, r) = (w, r + readAmount n D w) := by
  induction n generalizing r with
  | zero => cases w <;> simp [readLeaves, readAmount, Equiv.addRight]
  | succ n ih =>
      rcases w with ⟨l, t⟩
      change (((readLeaves n (fun a => D (false, a)) (l, r)).1,
        (readLeaves n (fun a => D (true, a))
          (t, (readLeaves n (fun a => D (false, a)) (l, r)).2)).1),
        (readLeaves n (fun a => D (true, a))
          (t, (readLeaves n (fun a => D (false, a)) (l, r)).2)).2) = _
      simp only [ih, readAmount, add_assoc]

private lemma readAmount_oneHot (n : ℕ) (D : Address n → G) (a : Address n) (e : Bool) :
    readAmount n D (oneHot n a e) = if e then D a else 0 := by
  induction n generalizing e with
  | zero => cases a; rfl
  | succ n ih =>
      rcases a with ⟨b, a⟩
      cases b <;> cases e <;> simp [readAmount, oneHot, ih]

/-- Compute, read all leaves, and reverse every routing gate. The address is a control.
This is a permutation of all basis configurations, including dirty routing wires. -/
def query (n : ℕ) (D : Address n → G) : Equiv.Perm (Address n × (Wires n × G)) :=
  Equiv.prodCongrRight fun a =>
    (Equiv.prodCongr (route n a) (Equiv.refl G)).trans
      ((readLeaves n D).trans
        (Equiv.prodCongr (route n a).symm (Equiv.refl G)))

private lemma query_apply (n : ℕ) (D : Address n → G)
    (a : Address n) (w : Wires n) (r : G) :
    query n D (a, w, r) = (a, w, r + readAmount n D (route n a w)) := by
  change (a, (Equiv.prodCongr (route n a).symm (Equiv.refl G))
    (readLeaves n D (route n a w, r))) = _
  rw [readLeaves_apply]
  simp

private lemma query_clean (n : ℕ) (D : Address n → G) (a : Address n) (r : G) :
    query n D (a, clean n true, r) = (a, clean n true, r + D a) := by
  rw [query_apply, route_clean, readAmount_oneHot]
  rfl

/-- The forward-action convention: amplitudes pull back along the inverse query. -/
noncomputable def queryMatrix (n : ℕ) [Fintype G] [DecidableEq G]
    (D : Address n → G) : Matrix (Address n × (Wires n × G))
      (Address n × (Wires n × G)) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (query n D)

/-- Complex amplitudes supported on the initialized routing workspace. -/
noncomputable def initialized (n : ℕ) (ψ : Address n × G → ℂ) :
    Address n × (Wires n × G) → ℂ :=
  fun s => if s.2.1 = clean n true then ψ (s.1, s.2.2) else 0

/-- Arbitrary-depth routing, reversible readout, and its coherent complex-amplitude action. -/
theorem correctness :
    (∀ (n : ℕ) (a i : Address n) (e : Bool),
      leaf n (route n a (clean n e)) i = if i = a then e else false) ∧
    (∀ (n : ℕ) (G : Type) [AddCommGroup G] (D : Address n → G)
      (a : Address n) (w : Wires n) (r : G),
      query n D (a, w, r) = (a, w, r + readAmount n D (route n a w))) ∧
    (∀ (n : ℕ) (G : Type) [AddCommGroup G] (D : Address n → G)
      (a : Address n) (r : G),
      query n D (a, clean n true, r) = (a, clean n true, r + D a)) ∧
    (∀ (n : ℕ) (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
      (D : Address n → G),
      (queryMatrix n D)ᴴ * queryMatrix n D = 1 ∧
      queryMatrix n D * (queryMatrix n D)ᴴ = 1 ∧
      ∀ ψ : Address n × G → ℂ,
        queryMatrix n D *ᵥ initialized n ψ =
          initialized n (fun s => ψ (s.1, s.2 - D s.1))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n a i e
    rw [route_clean, oneHot_leaf]
  · intro n G _ D a w r
    exact query_apply n D a w r
  · intro n G _ D a r
    exact query_clean n D a r
  · intro n G _ _ _ D
    refine ⟨?_, ?_, ?_⟩
    · simp only [queryMatrix, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_inv, inv_mul_cancel, Matrix.permMatrix_one]
    · simp only [queryMatrix, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_inv, mul_inv_cancel, Matrix.permMatrix_one]
    · intro ψ
      rw [queryMatrix, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
      funext s
      rcases s with ⟨a, w, r⟩
      by_cases hw : w = clean n true
      · subst w
        have hinv : (query n D).symm (a, clean n true, r) =
            (a, clean n true, r - D a) := by
          apply (query n D).injective
          rw [Equiv.apply_symm_apply, query_clean, sub_add_cancel]
        simp [hinv, initialized]
      · have hdirty : ((query n D).symm (a, w, r)).2.1 = w := by
          have h := congrArg (fun s : Address n × (Wires n × G) => s.2.1)
            ((query n D).apply_symm_apply (a, w, r))
          rw [query_apply] at h
          exact h
        simp [initialized, hw, hdirty]

end D5.S3.Quantum.Routing.ReversibleQram
