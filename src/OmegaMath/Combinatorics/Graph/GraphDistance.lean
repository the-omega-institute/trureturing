import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Dist

/-! Omega original. Graph distance certificates and distance in a finite path. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph

namespace OmegaMath.Combinatorics.Graph.GraphDistance

/-- A graph metric is certified by its zero set, edge bound, and a step toward each target. -/
theorem distance_certificate {V : Type*} [Nonempty V] (G : SimpleGraph V)
    (m : V → V → ℕ)
    (hz : ∀ u v, m u v = 0 ↔ u = v)
    (he : ∀ u v w, G.Adj u v → m u w ≤ m v w + 1)
    (hd : ∀ u v, m u v ≠ 0 → ∃ w, G.Adj u w ∧ m w v + 1 = m u v) :
    G.Connected ∧ ∀ u v, G.dist u v = m u v := by
  have walks : ∀ n u v, m u v = n → ∃ p : G.Walk u v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro u v huv
      have huv' := (hz u v).mp huv
      subst v
      exact ⟨.nil, rfl⟩
    | succ n ih =>
      intro u v huv
      obtain ⟨w, huw, hwv⟩ := hd u v (by omega)
      obtain ⟨p, hp⟩ := ih w v (by omega)
      exact ⟨p.cons huw, by simp [hp]⟩
  have conn : G.Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => ⟨(walks (m u v) u v rfl).choose⟩, inferInstance⟩
  refine ⟨conn, fun u v => ?_⟩
  have lower : ∀ {a b} (p : G.Walk a b), m a b ≤ p.length := by
    intro a b p
    induction p with
    | nil => simp [(hz _ _).mpr rfl]
    | @cons a b c hab p ih =>
      have h := he a b c hab
      simp only [Walk.length_cons]
      omega
  obtain ⟨p, hp⟩ := walks (m u v) u v rfl
  apply le_antisymm
  · simpa [hp] using G.dist_le p
  · obtain ⟨q, hq⟩ := conn.exists_walk_length_eq_dist u v
    simpa [hq] using lower q

/-- The distance in a finite path equals the natural-number distance between indices. -/
theorem pathGraph_dist {s : ℕ} (y t : Fin s) :
    (SimpleGraph.pathGraph s).dist y t = Nat.dist y.val t.val := by
  have : NeZero s := Fin.neZero y
  apply (distance_certificate
    (SimpleGraph.pathGraph s) (fun u v => Nat.dist u.val v.val) ?_ ?_ ?_).2
  · intro u v
    constructor
    · intro h; apply Fin.ext; exact Nat.eq_of_dist_eq_zero h
    · intro h; subst v; exact by simp [Nat.dist]
  · intro u v w h
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [Nat.dist]
    omega
  · intro u v h
    have hu := u.isLt
    have hv := v.isLt
    by_cases huv : u.val < v.val
    · refine ⟨⟨u.val + 1, by omega⟩, ?_, ?_⟩
      · simp [SimpleGraph.pathGraph_adj]
      · simp only [Nat.dist]
        omega
    · refine ⟨⟨u.val - 1, by simp only [Nat.dist] at h; omega⟩, ?_, ?_⟩
      · simp only [SimpleGraph.pathGraph_adj]
        simp only [Nat.dist] at h
        omega
      · simp only [Nat.dist] at *
        omega

end OmegaMath.Combinatorics.Graph.GraphDistance
