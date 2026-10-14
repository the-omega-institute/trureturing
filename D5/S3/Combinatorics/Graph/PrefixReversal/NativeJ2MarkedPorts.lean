/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The twelve actual J2 ports are distinct, so the six marked b cuts have disjoint endpoints. -/
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

set_option maxHeartbeats 800000 in
/-- All twelve actual port vertices are distinct at every J2 size. -/
theorem native_j2_port_injective {m : ℕ} (hm : 5 ≤ m) :
    Function.Injective (port m) := by
  rintro ⟨i, t, u⟩ ⟨j, s, v⟩ he
  fin_cases i <;> fin_cases j <;> cases t <;> cases u <;> cases s <;> cases v
  all_goals first | rfl | skip
  all_goals
    have h0 := congrArg (fun z : Configuration m => (z (0 : Fin (m + 1))).val) he
    have h1 := congrArg (fun z : Configuration m => (z (1 : Fin (m + 1))).val) he
    have h2 := congrArg (fun z : Configuration m => (z (2 : Fin (m + 1))).val) he
    have hk := congrArg (fun z : Configuration m =>
      (z ⟨m - 1, by omega⟩).val) he
    simp (disch := omega) [port, rightPort, leftPort, bar, Equiv.Perm.mul_apply,
      swap_val, rotate_val, b_apply, c_apply, if_pos, if_neg,
      mod_two_cases, Nat.mod_eq_of_lt, Fin.val_mk, Fin.val_last, Fin.val_zero] at h0 h1 h2 hk
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
