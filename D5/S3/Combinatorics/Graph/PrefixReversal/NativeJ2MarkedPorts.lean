/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Twelve actual J2 ports are distinct, so six marked b cuts have disjoint endpoints. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open Equiv Fin.NatCast

/-- An actual port, indexed by its right-port number, label swap, and left side. -/
def port (m : ℕ) (p : Fin 3 × Bool × Bool) : Configuration m :=
  let z := if p.2.2 then leftPort m p.1 else rightPort m p.1
  if p.2.1 then bar z else z

/-- The six actual undirected marked b edges. -/
def markedEdge (m : ℕ) (p : Fin 3 × Bool) : Sym2 (Configuration m) :=
  s(port m (p.1, p.2, false), port m (p.1, p.2, true))

private theorem swap_val {m : ℕ} (x y i : Fin (m + 1)) :
    ((Equiv.swap x y) i).val =
      if i.val = x.val then y.val else if i.val = y.val then x.val else i.val := by
  classical
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

private theorem rotate_val (m k : ℕ) (i : Fin (m + 1)) :
    ((finRotate (m + 1) ^ k) i).val = (i.val + k) % (m + 1) := by
  simp only [rotate_pow_eq_cycle, finCycle_apply, Fin.val_add, Fin.val_natCast]
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem mod_two_cases {x n : ℕ} (_hn : 0 < n) (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp only [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ x),
      Nat.mod_eq_of_lt (by omega : x - n < n)]

private def signature {m : ℕ} (hm : 5 ≤ m) (z : Configuration m) : ℕ × ℕ × ℕ × ℕ :=
  ((z ⟨0, by omega⟩).val, (z ⟨1, by omega⟩).val,
    (z ⟨2, by omega⟩).val, (z ⟨m - 1, by omega⟩).val)

private def portSignature (m : ℕ) (p : Fin 3 × Bool × Bool) : ℕ × ℕ × ℕ × ℕ :=
  match p.1.val, p.2.1, p.2.2 with
  | 0, false, false => (m, 0, 1, m - 2)
  | 0, false, true => (m - 2, m - 3, m - 4, m)
  | 0, true, false => (0, m, 1, m - 2)
  | 0, true, true => (m - 2, m - 3, m - 4, 0)
  | 1, false, false => (0, 1, 2, m)
  | 1, false, true => (m, m - 2, m - 3, 0)
  | 1, true, false => (m, 1, 2, 0)
  | 1, true, true => (0, m - 2, m - 3, m)
  | _, false, false => (1, 2, 3, 0)
  | _, false, true => (0, m, m - 2, 1)
  | _, true, false => (1, 2, 3, m)
  | _, true, true => (m, 0, m - 2, 1)

set_option maxHeartbeats 600000 in
private theorem signature_port {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool × Bool) :
    signature hm (port m p) = portSignature m p := by
  rcases p with ⟨i, t, u⟩
  fin_cases i <;> cases t <;> cases u
  all_goals
    simp only [signature, portSignature, port, rightPort, leftPort, bar,
      Fin.val_mk, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    constructor <;> try constructor <;> try constructor
    all_goals
      simp (disch := omega) only [Equiv.Perm.mul_apply, swap_val, rotate_val,
        b_apply, c_apply, Fin.val_mk, Fin.val_last, Fin.val_zero,
        mod_two_cases, Nat.mod_eq_of_lt, if_pos, if_neg, ite_true, ite_false,
        Nat.zero_add, Nat.add_zero, Nat.sub_zero, Nat.sub_self]
      <;> omega

/-- All twelve actual port vertices are distinct at every J2 size. -/
theorem native_j2_port_injective {m : ℕ} (hm : 5 ≤ m) :
    Function.Injective (port m) := by
  rintro ⟨i, t, u⟩ ⟨j, s, v⟩ he
  have hs := congrArg (signature hm) he
  rw [signature_port hm, signature_port hm] at hs
  fin_cases i <;> fin_cases j <;> cases t <;> cases u <;> cases s <;> cases v
  all_goals first | rfl | skip
  all_goals
    simp only [portSignature, Fin.val_mk, Prod.mk.injEq] at hs
    omega

#print axioms native_j2_port_injective

/-- Every actual J2 port has terminal label v=m-1. -/
theorem native_j2_port_last {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool × Bool) :
    (port m p (Fin.last m)).val = m - 1 := by
  have hrot : (m + m) % (m + 1) = m - 1 := by
    rw [show m + m = (m - 1) + (m + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : m - 1 < m + 1)]
  rcases p with ⟨i, t, u⟩
  fin_cases i <;> cases t <;> cases u
  all_goals
    simp (disch := omega) [port, rightPort, leftPort, bar, Equiv.Perm.mul_apply,
      swap_val, rotate_val, b_apply, c_apply, if_pos, if_neg,
      Fin.val_mk, Fin.val_last, Fin.val_zero, hrot]

#print axioms native_j2_port_last

/-- Each independently defined marked pair is its actual b-generator edge. -/
theorem native_j2_marked_edge (m : ℕ) (p : Fin 3 × Bool) :
    markedEdge m p =
      s(port m (p.1, p.2, false), port m (p.1, p.2, false) * b m) := by
  rcases p with ⟨i, t⟩
  cases t <;> simp [markedEdge, port, leftPort, bar, mul_assoc]

/-- Distinct actual marked cuts have no endpoint in common. -/
theorem native_j2_marked_disjoint {m : ℕ} (hm : 5 ≤ m)
    (p q : Fin 3 × Bool) (hpq : p ≠ q) :
    Disjoint {x : Configuration m | x ∈ markedEdge m p}
      {x : Configuration m | x ∈ markedEdge m q} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_setOf_eq, markedEdge, Sym2.mem_iff] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals
    apply hpq
    have he := native_j2_port_injective hm (hx.symm.trans hy)
    exact congrArg (fun r : Fin 3 × Bool × Bool => (r.1, r.2.1)) he

#print axioms native_j2_marked_edge
#print axioms native_j2_marked_disjoint

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
