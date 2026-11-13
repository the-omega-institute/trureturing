/- GID: D5/S3/Quantum/Routing/HannSpatialQram
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannSpatialQram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sequential qutrit address absorption and spatial clean lookup at every depth. -/

module

public import D5.S3.Quantum.Routing.ReversibleQram

/-! Hann et al.'s three-level incident, router and output systems, with sequential loading. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Routing.HannSpatialQram

open ReversibleQram (Address)
open Matrix

/-- The same three basis labels apply to routers and spatial modes. -/
inductive Qutrit
  | wait | zero | one
  deriving DecidableEq

open Qutrit

instance qutritFintype : Fintype Qutrit :=
  ⟨{wait, zero, one}, by intro x; cases x <;> simp⟩

/-- The occupied two-level subspace, distinct from vacuum. -/
def encode (b : Bool) : Qutrit := if b then one else zero

/-- Internal coordinates below one incident rail. Children include their incident rails;
these are exactly the parent's two output rails, not additional copies. -/
abbrev Interior : ℕ → Type
  | 0 => Unit
  | n + 1 => Qutrit × (Qutrit × Interior n) × (Qutrit × Interior n)

abbrev Tree (n : ℕ) := Qutrit × Interior n
abbrev Slots (n : ℕ) := Fin n → Qutrit
/-- Distinct address slots, an external bus, and all actual spatial/router coordinates. -/
abbrev State (n : ℕ) := Slots n × Qutrit × Tree n

instance interiorFintype : (n : ℕ) → Fintype (Interior n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := interiorFintype n; inferInstanceAs (Fintype (Qutrit × Tree n × Tree n))

instance interiorDecidableEq : (n : ℕ) → DecidableEq (Interior n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => letI := interiorDecidableEq n; inferInstanceAs (DecidableEq (Qutrit × Tree n × Tree n))

/-- One leaf incident exists even at depth zero. -/
def vacuum : (n : ℕ) → Tree n
  | 0 => (wait, ())
  | n + 1 => (wait, wait, vacuum n, vacuum n)

def input (n : ℕ) (t : Tree n) (p : Qutrit) : Tree n := (p, t.2)

/-- Physical address ordering: the head bit is absorbed first. -/
def bit : (n : ℕ) → Address n → Fin n → Bool
  | 0, _, i => Fin.elim0 i
  | n + 1, a, i => if h : i.val = 0 then a.1 else bit n a.2 ⟨i.val - 1, by omega⟩

/-- Routers on the first k edges contain the consumed address programmed; every mode is vacuum. -/
def programmed : (n : ℕ) → Address n → ℕ → Tree n
  | 0, _, _ => vacuum 0
  | n + 1, _, 0 => vacuum (n + 1)
  | n + 1, a, k + 1 =>
      (wait, encode a.1,
        if a.1 then vacuum n else programmed n a.2 k,
        if a.1 then programmed n a.2 k else vacuum n)

/-- Literal full SWAP of the incident rail and router, including dirty states. -/
def absorb (n : ℕ) : Equiv.Perm (Tree (n + 1)) :=
  (show Function.Involutive (fun s : Tree (n + 1) => (s.2.1, s.1, s.2.2)) from
    by intro s; rfl).toPerm _

/-- A controlled full SWAP between incident and one output rail. -/
def leftGate (n : ℕ) : Equiv.Perm (Tree (n + 1)) :=
  (show Function.Involutive (fun s : Tree (n + 1) =>
    if s.2.1 = zero then (s.2.2.1.1, s.2.1, (s.1, s.2.2.1.2), s.2.2.2) else s) from by
      intro s; rcases s with ⟨i, r, ⟨l, u⟩, t⟩
      by_cases h : r = zero <;> simp [h]).toPerm _

def rightGate (n : ℕ) : Equiv.Perm (Tree (n + 1)) :=
  (show Function.Involutive (fun s : Tree (n + 1) =>
    if s.2.1 = one then (s.2.2.2.1, s.2.1, s.2.2.1, (s.1, s.2.2.2.2)) else s) from by
      intro s; rcases s with ⟨i, r, l, ⟨t, u⟩⟩
      by_cases h : r = one <;> simp [h]).toPerm _

def route (n : ℕ) : Equiv.Perm (Tree (n + 1)) := (leftGate n).trans (rightGate n)

/-- Identical scheduled operations in both subtrees; no address selects a nonlocal gate. -/
def children (n : ℕ) (e f : Equiv.Perm (Tree n)) : Equiv.Perm (Tree (n + 1)) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr e f))

/-- Route through k already programmed levels and perform full absorption SWAPs there. -/
def descend : (n k : ℕ) → Equiv.Perm (Tree n)
  | 0, _ => Equiv.refl _
  | n + 1, 0 => absorb n
  | n + 1, k + 1 => (route n).trans (children n (descend n k) (descend n k))

private lemma descend_vacuum (n k : ℕ) : descend n k (vacuum n) = vacuum n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      cases k with
      | zero => rfl
      | succ k => simp [descend, route, leftGate, rightGate, children, vacuum, ih]

private lemma prefix_input (n : ℕ) (a : Address n) (k : ℕ) :
    (programmed n a k).1 = wait := by cases n <;> cases k <;> rfl

private lemma programmed_zero (n : ℕ) (a : Address n) : programmed n a 0 = vacuum n := by
  cases n <;> rfl

/-- Operational programmed extension, obtained from the local gates rather than a query axiom. -/
private theorem descend_prefix (n : ℕ) (a : Address n) (k : ℕ) (hk : k < n) :
    descend n k (input n (programmed n a k) (encode (bit n a ⟨k, hk⟩))) =
      programmed n a (k + 1) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      rcases a with ⟨b, a⟩
      cases k with
      | zero =>
          cases b <;>
            simp [descend, absorb, input, programmed, bit, encode, vacuum, programmed_zero]
      | succ k =>
          have h := ih a k (by omega)
          cases b <;>
            simpa [descend, route, leftGate, rightGate, children, programmed, input, encode,
              bit, prefix_input, descend_vacuum] using h

/-- Exchange an external qutrit with the root incident rail. -/
def exchange (n : ℕ) : Equiv.Perm (Qutrit × Tree n) :=
  (show Function.Involutive (fun s : Qutrit × Tree n => (s.2.1, s.1, s.2.2)) from
    by intro s; rfl).toPerm _

/-- Inject one distinct address slot; the other slots and external bus are untouched. -/
def inject (n : ℕ) (j : Fin n) : Equiv.Perm (State n) :=
  (show Function.Involutive (fun s : State n =>
    (Function.update s.1 j s.2.2.1, s.2.1, s.1 j, s.2.2.2)) from by
      intro s
      rcases s with ⟨v, b, p, u⟩
      simp [Function.update_idem]).toPerm _

/-- Slots whose signals have already been absorbed are vacuum. -/
def remaining (n : ℕ) (a : Address n) (k : ℕ) : Slots n :=
  fun j => if j.val < k then wait else encode (bit n a j)

/-- The state between two successive address injections. -/
def loading (n : ℕ) (a : Address n) (b : Qutrit) (k : ℕ) : State n :=
  (remaining n a k, b, programmed n a k)

/-- The first k injections, in ordinary sequential order. The k >= n cases are inert. -/
def load (n : ℕ) : ℕ → Equiv.Perm (State n)
  | 0 => Equiv.refl _
  | k + 1 => if h : k < n then
      (load n k).trans ((inject n ⟨k, h⟩).trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (descend n k))))
    else load n k

private theorem load_prefix (n : ℕ) (a : Address n) (b : Qutrit) (k : ℕ) (hk : k ≤ n) :
    load n k (loading n a b 0) = loading n a b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkn : k < n := by omega
      have hslots : Function.update (remaining n a k) ⟨k, hkn⟩ wait = remaining n a (k+1) := by
        funext j
        by_cases hj : j = ⟨k, hkn⟩
        · subst j; simp [remaining]
        · have hjv : j.val ≠ k := fun h => hj (Fin.ext h)
          simp [Function.update_of_ne hj, remaining]
          split_ifs <;> simp_all <;> omega
      simp only [load, dite_eq_left hkn, Equiv.trans_apply, ih (by omega)]
      change (Function.update (remaining n a k) ⟨k, hkn⟩ (programmed n a k).1, b,
        descend n k (input n (programmed n a k) (remaining n a k ⟨k, hkn⟩))) = _
      rw [prefix_input, hslots]
      simp only [remaining, lt_self_iff_false, ↓reduceIte]
      rw [descend_prefix n a k hkn]
      rfl

/-- A fully loaded tree with one payload at the addressed spatial leaf. -/
def arrived : (n : ℕ) → Address n → Qutrit → Tree n
  | 0, _, p => (p, ())
  | n + 1, a, p =>
      (wait, encode a.1,
        if a.1 then vacuum n else arrived n a.2 p,
        if a.1 then arrived n a.2 p else vacuum n)

/-- Observe the actual spatial rail at a leaf address. -/
def leaf : (n : ℕ) → Tree n → Address n → Qutrit
  | 0, t, _ => t.1
  | n + 1, t, a => leaf n (if a.1 then t.2.2.2 else t.2.2.1) a.2

private lemma leaf_vacuum (n : ℕ) (i : Address n) : leaf n (vacuum n) i = wait := by
  induction n with
  | zero => rfl
  | succ n ih => cases i.1 <;> exact ih i.2

private lemma arrived_leaf (n : ℕ) (a i : Address n) (p : Qutrit) :
    leaf n (arrived n a p) i = if i = a then p else wait := by
  induction n with
  | zero => cases a; cases i; rfl
  | succ n ih =>
      rcases a with ⟨b,a⟩
      rcases i with ⟨c,i⟩
      cases b <;> cases c <;> simp [leaf, arrived, leaf_vacuum, ih, Prod.mk.injEq]

/-- Transport the incident payload through all router levels by local controlled SWAPs. -/
def transport : (n : ℕ) → Equiv.Perm (Tree n)
  | 0 => Equiv.refl _
  | n + 1 => (route n).trans (children n (transport n) (transport n))

private lemma transport_vacuum (n : ℕ) : transport n (vacuum n) = vacuum n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [transport, route, leftGate, rightGate, children, vacuum, ih]

private theorem transport_prefix (n : ℕ) (a : Address n) (p : Qutrit) :
    transport n (input n (programmed n a n) p) = arrived n a p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases a with ⟨b, a⟩
      cases b <;>
        simpa [transport, route, leftGate, rightGate, children, programmed, input, encode,
          arrived, prefix_input, transport_vacuum] using ih a

/-- Appendix B's X-tilde: exchange occupied basis labels and fix vacuum. -/
def dataGate (d : Bool) : Equiv.Perm Qutrit := if d then Equiv.swap zero one else Equiv.refl _

/-- Fixed classical gates on every leaf, including all leaves without the payload. -/
def readLeaves : (n : ℕ) → (Address n → Bool) → Equiv.Perm (Tree n)
  | 0, D => Equiv.prodCongr (dataGate (D ())) (Equiv.refl _)
  | n + 1, D => children n (readLeaves n (fun a => D (false,a)))
      (readLeaves n (fun a => D (true,a)))

private lemma dataGate_wait (d : Bool) : dataGate d wait = wait := by cases d <;> decide
private lemma dataGate_encode (d b : Bool) : dataGate d (encode b) = encode (xor b d) := by
  cases d <;> cases b <;> decide

private lemma read_vacuum (n : ℕ) (D : Address n → Bool) :
    readLeaves n D (vacuum n) = vacuum n := by
  induction n with
  | zero => exact Prod.ext (dataGate_wait _) rfl
  | succ n ih => simp [readLeaves, children, vacuum, ih]

private theorem read_arrived (n : ℕ) (D : Address n → Bool) (a : Address n) (b : Bool) :
    readLeaves n D (arrived n a (encode b)) = arrived n a (encode (xor b (D a))) := by
  induction n with
  | zero => cases a; exact Prod.ext (dataGate_encode _ _) rfl
  | succ n ih =>
      rcases a with ⟨c,a⟩
      cases c <;> simp [readLeaves, children, arrived, read_vacuum, ih]

/-- Load addresses, inject the external bus, then transport it to a leaf. -/
def forward (n : ℕ) : Equiv.Perm (State n) :=
  (load n n).trans ((Equiv.prodCongr (Equiv.refl _) (exchange n)).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (transport n))))

/-- Completely initialized address/bus inputs, routers in wait and all spatial modes vacuum. -/
def clean (n : ℕ) (a : Address n) (b : Bool) : State n := loading n a (encode b) 0

private theorem forward_clean (n : ℕ) (a : Address n) (b : Bool) :
    forward n (clean n a b) = (remaining n a n, wait, arrived n a (encode b)) := by
  simp only [forward, clean, Equiv.trans_apply, load_prefix n a (encode b) n (le_refl n)]
  change (remaining n a n, (programmed n a n).1,
    transport n (input n (programmed n a n) (encode b))) = _
  rw [prefix_input, transport_prefix]

/-- Read locally and reverse the entire forward gate sequence. -/
def query (n : ℕ) (D : Address n → Bool) : Equiv.Perm (State n) :=
  (forward n).trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (readLeaves n D))).trans (forward n).symm)

private theorem query_clean (n : ℕ) (D : Address n → Bool) (a : Address n) (b : Bool) :
    query n D (clean n a b) = clean n a (xor b (D a)) := by
  apply (forward n).injective
  simp only [query, Equiv.trans_apply, Equiv.apply_symm_apply, forward_clean]
  change (remaining n a n, wait, readLeaves n D (arrived n a (encode b))) = _
  rw [read_arrived]

/-- Complex linear action is the existing permutation-matrix construction. -/
noncomputable def queryMatrix (n : ℕ) (D : Address n → Bool) : Matrix (State n) (State n) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (query n D)

/-- Amplitudes on clean encoded input states, with no restriction on address superpositions. -/
noncomputable def initialized (n : ℕ) (ψ : Address n × Bool → ℂ) : State n → ℂ :=
  fun s => ∑ a : Address n, ∑ b : Bool, if s = clean n a b then ψ (a,b) else 0

/-- Sequential programmed loading, unique payload transport, and exact clean lookup at every depth. -/
theorem correctness :
    (∀ (n : ℕ) (a : Address n) (b : Qutrit) (k : ℕ), k ≤ n →
      load n k (loading n a b 0) = loading n a b k) ∧
    (∀ (n : ℕ) (a : Address n) (p : Qutrit),
      transport n (input n (programmed n a n) p) = arrived n a p ∧
      ∀ i : Address n, leaf n (transport n (input n (programmed n a n) p)) i =
        if i = a then p else wait) ∧
    (∀ (n : ℕ) (D : Address n → Bool) (a : Address n) (b : Bool),
      query n D (clean n a b) = clean n a (xor b (D a))) ∧
    (∀ (n : ℕ) (D : Address n → Bool),
      (queryMatrix n D)ᴴ * queryMatrix n D = 1 ∧
      queryMatrix n D * (queryMatrix n D)ᴴ = 1 ∧
      ∀ ψ : Address n × Bool → ℂ,
        queryMatrix n D *ᵥ initialized n ψ =
          initialized n (fun s => ψ (s.1, xor s.2 (D s.1)))) := by
  refine ⟨load_prefix, ?_, query_clean, ?_⟩
  · intro n a p
    refine ⟨transport_prefix n a p, ?_⟩
    intro i
    rw [transport_prefix, arrived_leaf]
  · intro n D
    refine ⟨?_, ?_, ?_⟩
    · simp only [queryMatrix, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_inv, inv_mul_cancel, Matrix.permMatrix_one]
    · simp only [queryMatrix, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_inv, mul_inv_cancel, Matrix.permMatrix_one]
    · intro ψ
      rw [queryMatrix, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
      funext s
      simp only [Equiv.Perm.inv_def, initialized, Function.comp_apply]
      apply Finset.sum_congr rfl
      intro a _
      have heq (b : Bool) : (query n D).symm s = clean n a b ↔
          s = clean n a (xor b (D a)) := by
        rw [Equiv.symm_apply_eq, query_clean]
      cases hD : D a <;> simp [heq, hD, Fintype.sum_bool,
        add_comm]

end D5.S3.Quantum.Routing.HannSpatialQram
