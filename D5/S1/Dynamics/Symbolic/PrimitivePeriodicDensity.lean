/- GID: D5/S1/Dynamics/Symbolic/PrimitivePeriodicDensity
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive adjacency supplies positive bridge paths in a finite graph. -/
import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Algebra.Ring.Periodic

/-! Primitive finite-graph shifts have periodic points in every finite cylinder.

The first compiled bridge records the matrix-to-quiver step needed by the
periodic-density construction. -/

noncomputable section

open Classical
open Set Function
open SymbolicDynamics
open D5.S1.Dynamics.Shadowing
open D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
open Quiver
open Quiver.Path

namespace D5.S1.Dynamics.Symbolic.PrimitivePeriodicDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Integer adjacency matrix, suitable for `Matrix.IsPrimitive`. -/
def adjacencyInt (edge : V → V → Prop) : Matrix V V ℤ :=
  fun i j => if edge i j then 1 else 0

@[simp] theorem adjacencyInt_apply (edge : V → V → Prop) (i j : V) :
    adjacencyInt edge i j = if edge i j then 1 else 0 := rfl

@[simp] theorem adjacencyInt_pos_iff (edge : V → V → Prop) (i j : V) :
    0 < adjacencyInt edge i j ↔ edge i j := by
  classical
  by_cases h : edge i j <;> simp [adjacencyInt, h]

private theorem adjacencyInt_nonneg (edge : V → V → Prop) (i j : V) :
    0 ≤ adjacencyInt edge i j := by
  classical
  by_cases h : edge i j <;> simp [adjacencyInt, h]

/-- A graph-language point is periodic when it has a positive additive period. -/
def periodicPoints (edge : V → V → Prop) : Set (ℕ → V) :=
  {y | y ∈ edgeLanguage edge ∧ ∃ p : ℕ, 0 < p ∧ Function.Periodic y p}

/-- Primitive adjacency gives a positive-length quiver path between any two
vertices.  The path's arrows are positive entries of the integer adjacency
matrix, hence are exactly the declared graph edges. -/
theorem primitive_bridge_path (edge : V → V → Prop)
    (hprim : Matrix.IsPrimitive (adjacencyInt edge)) (u v : V) :
    ∃ m : ℕ, m > 0 ∧
      ∃ p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) u v,
        @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) u v p = m := by
  obtain ⟨m, hm, hpow⟩ := hprim.exists_pos_pow
  refine ⟨m, hm, ?_⟩
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  have hpos : 0 < (adjacencyInt edge ^ m) u v := hpow u v
  obtain ⟨⟨p, hp⟩⟩ :=
    (Matrix.pow_apply_pos_iff_nonempty_path
      (A := adjacencyInt edge) (fun i j => adjacencyInt_nonneg edge i j) m u v).mp hpos
  exact ⟨p, hp⟩

private theorem path_vertices_get_length
    (edge : V → V → Prop) [DecidableRel edge] {a b : V}
    (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a b) :
    (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[
      @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a b p]'(by
        rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
        omega) = @Quiver.Path.end V (Matrix.toQuiver (adjacencyInt edge)) a b p := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  induction p with
  | nil => rfl
  | @cons m c p e ih =>
      simp [vertices_cons, length_cons]

private theorem path_vertices_edge
    (edge : V → V → Prop) [DecidableRel edge] :
    ∀ {a b : V}
      (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a b),
      ∀ i : Fin (@Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a b p),
      edge
        ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[i.val]'(by
          rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
          omega))
        ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[i.val + 1]'(by
          rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
          omega)) := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  intro a b p
  induction p with
  | nil =>
      intro i
      exact Fin.elim0 i
  | @cons m c p e ih =>
      intro i
      cases i using Fin.lastCases with
      | last =>
          have hpos : 0 < adjacencyInt edge m c := e.down
          have hedge' : edge m c := (adjacencyInt_pos_iff edge m c).mp hpos
          simpa [vertices_cons, path_vertices_get_length, Quiver.Path.end] using hedge'
      | cast j =>
          simpa [vertices_cons] using ih j

private theorem path_vertices_get_zero
    (edge : V → V → Prop) [DecidableRel edge] {a b : V}
    (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a b)
    (hp : 0 < (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p).length) :
    (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[0]'hp = a := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  induction p with
  | nil => rfl
  | @cons m c p e ih =>
      have hplen : 0 < p.vertices.length := by
        rw [vertices_length]
        omega
      have hleft :=
        List.getElem_append_left (as := p.vertices) (bs := [c]) (i := 0) hplen
          (h' := by simp [List.length_append])
      simpa only [vertices_cons, List.concat_eq_append] using hleft.trans (ih hplen)

private theorem closed_path_periodic_word
    (edge : V → V → Prop) [DecidableRel edge]
    {a : V}
    (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a a)
    (hp : 0 < @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a a p) :
    ∃ y : ℕ → V, y ∈ edgeLanguage edge ∧
      Function.Periodic y (@Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a a p) ∧
      ∀ n, y n =
        (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[n %
          (@Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a a p)]'
            (by
              rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]
              exact (Nat.mod_lt n hp).trans_le (by omega)) := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  let L := @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a a p
  let y : ℕ → V := fun n =>
    (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[n % L]'
      (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]
          exact (Nat.mod_lt n hp).trans_le (by omega))
  have hper : Function.Periodic y L := by
    intro n
    dsimp [y]
    congr 1
    rw [Nat.add_mod]
    have hLm : L % L = 0 := Nat.mod_self L
    simp [hLm, Nat.mod_eq_of_lt (Nat.mod_lt n hp)]
  have hedge : ∀ n, edge (y n) (y (n + 1)) := by
    intro n
    have hi : n % L < L := Nat.mod_lt n hp
    by_cases hnext : n % L + 1 < L
    · have hmod : (n + 1) % L = n % L + 1 := by
        rw [Nat.add_mod]
        have hL1 : 1 < L := by omega
        rw [Nat.mod_eq_of_lt hL1]
        rw [Nat.mod_eq_of_lt hnext]
      have he := path_vertices_edge edge p ⟨n % L, hi⟩
      simpa [y, hmod] using he
    · have hlast : n % L + 1 = L := by omega
      have hmod : (n + 1) % L = 0 := by
        rw [Nat.add_mod]
        by_cases hL : L = 1
        · simp [hL, Nat.mod_one]
        · have hL1 : 1 < L := by omega
          rw [Nat.mod_eq_of_lt hL1]
          rw [show n % L + 1 = L by exact hlast]
          simp [Nat.mod_self]
      have he := path_vertices_edge edge p ⟨L - 1, by omega⟩
      have hzero :
          (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[0]'
            (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]; omega) = a :=
        path_vertices_get_zero edge p (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]; omega)
      have hend :
          (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[L]'
            (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]; omega) = a :=
        path_vertices_get_length edge p
      have hlast' : n % L = L - 1 := by omega
      have he' : edge
          ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[L - 1]'
            (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]; omega))
          ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a a p)[L]'
            (by rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a a p]; omega)) := by
        simpa only [show L - 1 + 1 = L by omega] using he
      simpa [y, hmod, hlast', hend, hzero] using he'
  refine ⟨y, ?_, hper, ?_⟩
  change y ∈ graphLanguage edge id
  · exact ⟨y, hedge, fun _ => rfl⟩
  · intro n
    rfl

theorem primitive_periodic_prefix_dense
    (edge : V → V → Prop)
    (hprim : Matrix.IsPrimitive (adjacencyInt edge)) :
    ∀ w ∈ edgeLanguage edge, ∀ k : ℕ,
      ∃ y ∈ periodicPoints edge,
        ∀ i : Fin (k + 1), y i.val = w i.val := by
  intro w hw k
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  have hwedge : ∀ n, edge (w n) (w (n + 1)) := by
    rcases hw with ⟨p, hp, hl⟩
    intro n
    rw [← hl n, ← hl (n + 1)]
    exact hp n
  let prefixPath : ∀ n : ℕ,
      @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) (w 0) (w n) :=
    fun n =>
      Nat.rec (motive := fun n =>
        @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) (w 0) (w n))
        Quiver.Path.nil
        (fun n p =>
          p.cons ⟨(adjacencyInt_pos_iff edge (w n) (w (n + 1))).2 (hwedge n)⟩) n
  have hprefix_len : ∀ n, (prefixPath n).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change ((prefixPath n).cons _).length = n + 1
        rw [Quiver.Path.length_cons, ih]
  have hprefix_vertices : ∀ n, ∀ i : Fin (n + 1),
      (prefixPath n).vertices[i.val]'
          (by rw [Quiver.Path.vertices_length, hprefix_len n]; omega) = w i.val := by
    intro n
    induction n with
    | zero =>
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
    | succ n ih =>
        intro i
        cases i using Fin.lastCases with
        | last =>
            have hend := path_vertices_get_length edge (prefixPath (n + 1))
            have hend' : (prefixPath (n + 1)).end = w (n + 1) := rfl
            simpa [hprefix_len, hend'] using hend
        | cast j =>
            change ((prefixPath n).cons _).vertices[j.val]'_ = w j.val
            have hget := List.getElem_append_left
              (as := (prefixPath n).vertices) (bs := [w (n + 1)]) (i := j.val)
              (by rw [Quiver.Path.vertices_length, hprefix_len n]; exact j.isLt)
              (h' := by simp [Quiver.Path.vertices_length, hprefix_len n])
            simpa only [Quiver.Path.vertices_cons, List.concat_eq_append] using
              hget.trans (ih j)
  obtain ⟨m, hm, bridge, hbridge_len⟩ :=
    primitive_bridge_path edge hprim (w k) (w 0)
  let cycle := (prefixPath k).comp bridge
  have hcycle_len : cycle.length = k + m := by
    simp [cycle, hprefix_len k, hbridge_len]
  have hcycle_pos : 0 < cycle.length := by
    rw [hcycle_len]
    omega
  obtain ⟨y, hyLang, hyPer, hyFormula⟩ :=
    closed_path_periodic_word edge cycle hcycle_pos
  have hcycle_vertices : cycle.vertices =
      (prefixPath k).vertices.dropLast ++ bridge.vertices := by
    exact Quiver.Path.vertices_comp _ _
  have hdrop_len : (prefixPath k).vertices.dropLast.length = k := by
    rw [List.length_dropLast, Quiver.Path.vertices_length, hprefix_len k]
    omega
  have hprefix_match : ∀ i : Fin (k + 1), y i.val = w i.val := by
    intro i
    by_cases hik : i.val < k
    · have hmod : i.val % cycle.length = i.val :=
        Nat.mod_eq_of_lt (by rw [hcycle_len]; omega)
      have hleft := List.getElem_append_left (as := (prefixPath k).vertices.dropLast)
        (bs := bridge.vertices) (i := i.val) (by rw [hdrop_len]; exact hik)
        (h' := by rw [List.length_append, hdrop_len, Quiver.Path.vertices_length, hbridge_len]; omega)
      have hdrop := List.getElem_dropLast (xs := (prefixPath k).vertices) (i := i.val)
        (by rw [hdrop_len]; exact hik)
      have hpref := hprefix_vertices k ⟨i.val, by omega⟩
      simpa [hyFormula i.val, hcycle_vertices, hmod] using hleft.trans (hdrop.trans hpref)
    · have hik' : i.val = k := by omega
      have hiEq : i = Fin.last k := Fin.ext hik'
      rw [hiEq]
      have hright := List.getElem_append_right
        (as := (prefixPath k).vertices.dropLast) (bs := bridge.vertices) (i := k)
        (by rw [hdrop_len])
        (h₂ := by rw [List.length_append, hdrop_len, Quiver.Path.vertices_length, hbridge_len]; omega)
      have hzero := path_vertices_get_zero edge bridge (by
        rw [Quiver.Path.vertices_length, hbridge_len]
        omega)
      have hmod : k % cycle.length = k := Nat.mod_eq_of_lt (by rw [hcycle_len]; omega)
      have hstart : bridge.vertices[0]'
          (by rw [Quiver.Path.vertices_length, hbridge_len]; omega) = w k := by
        exact hzero
      have hright' :
          ((prefixPath k).vertices.dropLast ++ bridge.vertices)[k]'
            (by rw [List.length_append, hdrop_len, Quiver.Path.vertices_length, hbridge_len]; omega) =
          bridge.vertices[0]'
            (by rw [Quiver.Path.vertices_length, hbridge_len]; omega) := by
        simpa [hdrop_len, hprefix_len] using hright
      simpa [hyFormula k, hcycle_vertices, hmod, hstart] using hright'
  refine ⟨y, ?_, hprefix_match⟩
  exact ⟨hyLang, cycle.length, hcycle_pos, hyPer⟩

end D5.S1.Dynamics.Symbolic.PrimitivePeriodicDensity
