/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All twelve J2 ports lie in F2 and its same Hamilton cycle contains all six marked edges. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open Equiv Fin.NatCast

open private contactAnchor_val from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open private first_a_cut second_a_cut from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels

private def contactIndex {m : ℕ} (hm : 5 ≤ m) : Fin (m - 2) :=
  ⟨m - 3, by omega⟩

/-- The literal native-circle anchor of each of the six right ports. -/
noncomputable def rightOwner {m : ℕ} (hm : 5 ≤ m)
    (p : Fin 3 × Bool) : Configuration m :=
  match p.1.val, p.2 with
  | 0, false => 1
  | 0, true => Equiv.swap (0 : Fin (m + 1)) (Fin.last m)
  | 1, false => contactAnchor (contactIndex hm)
  | 1, true => lowerPort (contactIndex hm)
  | _, false => gapAnchor (contactAnchor (contactIndex hm)) ⟨m - 1, by omega⟩
  | _, true => gapAnchor (contactAnchor (contactIndex hm)) ⟨m - 2, by omega⟩

private def rightRotation (m : ℕ) (p : Fin 3 × Bool) : ℕ :=
  match p.1.val, p.2 with
  | 0, _ => m
  | 1, false => m
  | 1, true => 1
  | _, false => 1
  | _, true => 2

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
/-- The six right ports are literal rotations in their actual native owners.
The left ports are subsequently obtained across their actual b edges. -/
private theorem right_owner_formula {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool) :
    port m (p.1, p.2, false) =
      rightOwner hm p * finRotate (m + 1) ^ rightRotation m p := by
  rcases p with ⟨r, t⟩
  fin_cases r <;> cases t
  all_goals first | rfl | skip
  all_goals
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hi := i.isLt
    have hposition : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = m - 3 ∨ i.val = m - 2 ∨ i.val = m - 1 ∨ i.val = m ∨
        (3 ≤ i.val ∧ i.val < m - 3) := by omega
    rcases hposition with h | h | h | h | h | h | h | h
    all_goals
      simp (disch := omega) only [h, port, rightPort, bar, rightOwner,
        rightRotation, contactIndex, lowerPort, gapAnchor,
        Equiv.Perm.mul_apply, Equiv.Perm.one_apply, a_apply, Fin.val_rev,
        b_apply, c_apply, native_bc_pow_val (by omega : 2 ≤ m),
        contactAnchor_val, rotate_val, swap_val, mod_two_cases,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_mk, Fin.val_last, Fin.val_zero,
        Bool.false_eq_true, ↓reduceIte, if_pos, if_neg, ite_true, ite_false]
      <;> omega

private theorem cut_circle_domain {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m)
    (hv : Circle (cutStart p) v) : CoreDomain m v := by
  have hp := (native_cut_circle_iff hm p v).mp hv
  exact (native_t_circle_partition hm v).mpr
    ⟨p, hp, fun q hq => native_t_circle_owner_unique hm v q p hq hp⟩

private theorem gap_circle_domain {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (i : Fin m) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v) : F2Domain m v := by
  exact Or.inr ⟨j, j.isLt,
    (native_star_circle_partition (by omega : 3 ≤ m) (contactAnchor j) v).mpr ⟨i, hv⟩⟩

private theorem right_owner_domain {m : ℕ} (hm : 5 ≤ m)
    (p : Fin 3 × Bool) (v : Configuration m)
    (hv : Circle (rightOwner hm p) v) : F2Domain m v := by
  rcases p with ⟨r, t⟩
  fin_cases r <;> cases t <;> simp only [rightOwner, Fin.val_mk] at hv
  · apply Or.inl
    apply cut_circle_domain (by omega : 4 ≤ m) (.inl ⟨m - 1, by omega⟩) v
    simpa only [(first_a_cut (by omega : 4 ≤ m)).1] using hv
  · apply Or.inl
    apply cut_circle_domain (by omega : 4 ≤ m) (.inl ⟨m - 2, by omega⟩) v
    simpa only [(second_a_cut (by omega : 4 ≤ m)).1] using hv
  · apply gap_circle_domain hm (contactIndex hm) ⟨0, by omega⟩ v
    simpa only [gapAnchor, Fin.val_mk, pow_zero, mul_one] using hv
  · apply Or.inl
    apply cut_circle_domain (by omega : 4 ≤ m) (.inl ⟨m - 3, by omega⟩) v
    simpa only [NativeCoreSplicing.cutStart, Fin.val_mk, if_neg (by omega : m - 3 ≠ m - 1),
      tCircleAnchor, gapAnchor, lowerPort, contactIndex] using hv
  · exact gap_circle_domain hm (contactIndex hm) ⟨m - 1, by omega⟩ v hv
  · exact gap_circle_domain hm (contactIndex hm) ⟨m - 2, by omega⟩ v hv

private theorem right_in_owner {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool) :
    Circle (rightOwner hm p) (port m (p.1, p.2, false)) := by
  rw [right_owner_formula hm p]
  left
  rw [rotate_pow_eq_cycle]
  exact native_configurationCycle_rotation _ _

private theorem left_port_eq (m : ℕ) (p : Fin 3 × Bool) :
    port m (p.1, p.2, true) = port m (p.1, p.2, false) * b m := by
  rcases p with ⟨r, t⟩
  cases t <;> simp [port, leftPort, bar, mul_assoc]

/-- Both orientations of each marked edge stay in its specified native owner. -/
theorem native_j2_port_circle {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool × Bool) :
    Circle (rightOwner hm (p.1, p.2.1)) (port m p) := by
  rcases p with ⟨r, t, u⟩
  have hr := right_in_owner hm (r, t)
  cases u
  · exact hr
  · rw [left_port_eq m (r, t)]
    exact native_circle_edge_endpoint _ _ _
      ⟨port m (r, t, false), b m, hr, Or.inr rfl, rfl⟩
      (Sym2.mem_mk_right _ _)

/-- All twelve independently defined J2 ports are actual vertices of F2. -/
theorem native_j2_port_domain {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool × Bool) :
    F2Domain m (port m p) := by
  exact right_owner_domain hm (p.1, p.2.1) _ (native_j2_port_circle hm p)

/-- None of the six marked b edges belongs to the complete T/E cut set.
Their terminal m-1 is different from both selected b-cut terminals 0 and m. -/
theorem native_j2_marked_uncut {m : ℕ} (hm : 5 ≤ m) (p : Fin 3 × Bool) :
    ¬ F2DeletedEdge m (markedEdge m p) := by
  have hl := native_j2_port_last hm (p.1, p.2, false)
  rw [native_j2_marked_edge]
  intro hd
  rcases (native_f2_b_cut_classification (by omega : 4 ≤ m)
    (port m (p.1, p.2, false))).mp hd with
      ⟨j, _, hj⟩ | ⟨j, _, hj⟩ | ⟨j, _, hj⟩
  all_goals
    have hv := congrArg Fin.val hj
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega

/-- One and the same actual Hamilton cycle has the exact full F2 inventory,
all twelve actual J2 ports in its domain, and all six disjoint marked b edges. -/
theorem native_j2_hamiltonian_cycle_with_marked_edges {m : ℕ} (hm : 5 ≤ m) :
    ∃ base : {v : Configuration m // F2Domain m v},
      ∃ w : (domainGraph (F2Domain m)).Walk base base,
        w.IsHamiltonianCycle ∧
          (∀ e : Sym2 (Configuration m),
            e ∈ w.edges.map (Sym2.map Subtype.val) ↔
              (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧
          (∀ p : Fin 3 × Bool × Bool, F2Domain m (port m p)) ∧
          ∀ p : Fin 3 × Bool, markedEdge m p ∈ w.edges.map (Sym2.map Subtype.val) := by
  obtain ⟨base, w, hw, hinv, hkeep⟩ :=
    native_f2_hamiltonian_cycle_with_native_edge_inventory (by omega : 4 ≤ m)
  refine ⟨base, w, hw, hinv, native_j2_port_domain hm, ?_⟩
  intro p
  rw [native_j2_marked_edge]
  apply (hkeep (port m (p.1, p.2, false)) (b m)
    (native_j2_port_domain hm (p.1, p.2, false)) (Or.inr rfl)).mpr
  simpa only [native_j2_marked_edge] using native_j2_marked_uncut hm p

#print axioms native_j2_port_circle
#print axioms native_j2_port_domain
#print axioms native_j2_marked_uncut
#print axioms native_j2_hamiltonian_cycle_with_marked_edges

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
