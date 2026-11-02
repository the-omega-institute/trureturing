/- GID: D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive clocks reconstruct recurrent named paths iff there is no branching. -/

import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Endpoint-duration reconstruction for actual named paths on a recurrent quiver. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction

universe u v
variable {V : Type u} [Quiver.{v} V]

/-- A named edge retains both endpoints and the actual arrow, including parallel arrows. -/
abbrev NamedEdge (V : Type u) [Quiver.{v} V] := Σ a b : V, a ⟶ b

/-- Ordered names along the actual Mathlib path, in execution order. -/
def edgeWord {a b : V} : Quiver.Path a b → List (NamedEdge V)
  | .nil => []
  | @Quiver.Path.cons _ _ _ c d p e => edgeWord p ++ [⟨c, d, e⟩]

/-- Sum of the given one-edge durations; the empty path has duration zero. -/
def duration (d : ∀ {a b : V}, (a ⟶ b) → ℝ) {a b : V} : Quiver.Path a b → ℝ
  | .nil => 0
  | .cons p e => duration d p + d e

/-- Endpoint and elapsed duration of an arbitrary finite path from the fixed root. -/
def readout (d : ∀ {a b : V}, (a ⟶ b) → ℝ) (r : V)
    (p : Σ b : V, Quiver.Path r b) : V × ℝ := (p.1, duration d p.2)

private theorem edgeWord_eq_weight {a b : V} (p : Quiver.Path a b) :
    edgeWord p = FreeMonoid.toList (Quiver.Path.weight
      (fun {a b} e => FreeMonoid.of (⟨a, b, e⟩ : NamedEdge V)) p) := by
  induction p with
  | nil => rw [edgeWord, Quiver.Path.weight_nil, FreeMonoid.toList_one]
  | cons p e ih =>
    rw [edgeWord, Quiver.Path.weight_cons, FreeMonoid.toList_mul, FreeMonoid.toList_of, ih]

private theorem duration_eq_addWeight (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    {a b : V} (p : Quiver.Path a b) : duration d p = Quiver.Path.addWeight d p := by
  induction p with
  | nil => rw [duration, Quiver.Path.addWeight_nil]
  | cons p e ih => rw [duration, Quiver.Path.addWeight_cons, ih]

private theorem edgeWord_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    edgeWord (p.comp q) = edgeWord p ++ edgeWord q := by
  simpa only [edgeWord_eq_weight, FreeMonoid.toList_mul] using
    congrArg FreeMonoid.toList (Quiver.Path.weight_comp
      (fun {a b} e => FreeMonoid.of (⟨a, b, e⟩ : NamedEdge V)) p q)

private theorem duration_comp (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    duration d (p.comp q) = duration d p + duration d q := by
  simpa only [duration_eq_addWeight] using Quiver.Path.addWeight_comp d p q

private theorem duration_eq_sum (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    {a b : V} (p : Quiver.Path a b) :
    duration d p = ((edgeWord p).map fun e => d e.2.2).sum := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [duration, edgeWord, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, ih]

private theorem duration_nonneg (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    (hd : ∀ {a b : V} (e : a ⟶ b), 0 < d e) {a b : V} (p : Quiver.Path a b) :
    0 ≤ duration d p := by
  rw [duration_eq_sum]
  apply List.sum_nonneg
  intro t ht
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
  exact (hd e.2.2).le

private theorem duration_pos (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    (hd : ∀ {a b : V} (e : a ⟶ b), 0 < d e) {a b : V} (p : Quiver.Path a b)
    (hp : p.length ≠ 0) : 0 < duration d p := by
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons p e => exact add_pos_of_nonneg_of_pos (duration_nonneg d hd p) (hd e)

private theorem deterministic_duration_unique
    (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    (hd : ∀ {a b : V} (e : a ⟶ b), 0 < d e)
    (unique : ∀ a : V, Subsingleton (Σ b : V, a ⟶ b)) :
    ∀ (n : ℕ) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path a c),
      p.length = n → duration d p = duration d q →
      (⟨b, p⟩ : Σ z : V, Quiver.Path a z) = ⟨c, q⟩ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b c p q hlen heq
    by_cases hp : p.length = 0
    · have hq : q.length = 0 := by
        by_contra hn
        have hh := duration_pos d hd q hn
        have hab := p.eq_of_length_zero hp
        subst b
        rw [p.eq_nil_of_length_zero hp] at heq
        simp [duration] at heq
        linarith
      obtain rfl := p.eq_of_length_zero hp
      obtain rfl := q.eq_of_length_zero hq
      rw [p.eq_nil_of_length_zero hp, q.eq_nil_of_length_zero hq]
    · have hq : q.length ≠ 0 := by
        intro hq
        have hh := duration_pos d hd p hp
        obtain rfl := q.eq_of_length_zero hq
        rw [q.eq_nil_of_length_zero hq] at heq
        simp [duration] at heq
        linarith
      obtain ⟨a', e, p', rfl, hpl⟩ := p.length_ne_zero_iff_eq_comp.mp hp
      obtain ⟨a'', f, q', rfl, _⟩ := q.length_ne_zero_iff_eq_comp.mp hq
      have hfirst : (⟨a', e⟩ : Σ z : V, a ⟶ z) = ⟨a'', f⟩ :=
        @Subsingleton.elim _ (unique a) _ _
      cases hfirst
      have htail : duration d p' = duration d q' := by
        simpa only [duration_comp, Quiver.Hom.toPath, duration, zero_add,
          add_right_inj] using heq
      have hsmall : p'.length < n := by
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlen
        omega
      have hrec := ih p'.length hsmall p' q' rfl htail
      cases hrec
      rfl

/-- The specified unequal actual outgoing arrows produce the particular rooted
collision obtained by exchanging their nonempty return blocks. Return segments may be empty. -/
theorem branching_collision_inventory
    (d : ∀ {a b : V}, (a ⟶ b) → ℝ) (r : V)
    (recurrent : ∀ a b : V, Nonempty (Quiver.Path a b))
    (z : V) (a b : Σ t : V, z ⟶ t) (hab : a ≠ b) :
    ∃ (p : Quiver.Path r z) (A : Quiver.Path a.1 z) (B : Quiver.Path b.1 z),
      let U := a.2.toPath.comp A
      let W := b.2.toPath.comp B
      0 < U.length ∧ 0 < W.length ∧
      edgeWord U = ⟨z, a.1, a.2⟩ :: edgeWord A ∧
      edgeWord W = ⟨z, b.1, b.2⟩ :: edgeWord B ∧
      (⟨z, a.1, a.2⟩ : NamedEdge V) ≠ ⟨z, b.1, b.2⟩ ∧
      p.comp (U.comp W) ≠ p.comp (W.comp U) ∧
      duration d (p.comp (U.comp W)) = duration d p + duration d U + duration d W ∧
      duration d (p.comp (W.comp U)) = duration d p + duration d W + duration d U ∧
      readout d r ⟨z, p.comp (U.comp W)⟩ = readout d r ⟨z, p.comp (W.comp U)⟩ ∧
      ¬ Function.Injective (readout d r) := by
  obtain ⟨p⟩ := recurrent r z
  obtain ⟨A⟩ := recurrent a.1 z
  obtain ⟨B⟩ := recurrent b.1 z
  let U := a.2.toPath.comp A
  let W := b.2.toPath.comp B
  have hfirst : (⟨z, a.1, a.2⟩ : NamedEdge V) ≠ ⟨z, b.1, b.2⟩ := by
    intro h
    exact hab (eq_of_heq (Sigma.mk.inj h).2)
  have hdistinct : p.comp (U.comp W) ≠ p.comp (W.comp U) := by
    intro hpath
    have hw := congrArg edgeWord (p.comp_injective_right hpath)
    simp only [U, W, edgeWord_comp, Quiver.Hom.toPath, edgeWord,
      List.nil_append, List.cons_append] at hw
    exact hfirst (List.cons.inj hw).1
  have hleft : duration d (p.comp (U.comp W)) =
      duration d p + duration d U + duration d W := by
    simp only [duration_comp, add_assoc]
  have hright : duration d (p.comp (W.comp U)) =
      duration d p + duration d W + duration d U := by
    simp only [duration_comp, add_assoc]
  have hequal : readout d r ⟨z, p.comp (U.comp W)⟩ =
      readout d r ⟨z, p.comp (W.comp U)⟩ := by
    apply Prod.ext rfl
    change duration d (p.comp (U.comp W)) = duration d (p.comp (W.comp U))
    rw [hleft, hright]
    ring
  have hnoninjective : ¬ Function.Injective (readout d r) := by
    intro hinj
    exact hdistinct (eq_of_heq (Sigma.mk.inj (hinj hequal)).2)
  refine ⟨p, A, B, ?_, ?_, ?_, ?_, hfirst, hdistinct, hleft, hright, hequal,
    hnoninjective⟩
  · simp only [U, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  · simp only [W, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  · simp only [U, edgeWord_comp, Quiver.Hom.toPath, edgeWord, List.nil_append,
      List.cons_append]
  · simp only [W, edgeWord_comp, Quiver.Hom.toPath, edgeWord, List.nil_append,
      List.cons_append]

/-- On a recurrent named graph, a positive additive clock and the endpoint recover
all finite executed words exactly when every vertex has at most one named outgoing edge. -/
theorem readout_injective_iff_no_branching
    (d : ∀ {a b : V}, (a ⟶ b) → ℝ)
    (hd : ∀ {a b : V} (e : a ⟶ b), 0 < d e) (r : V)
    (recurrent : ∀ a b : V, Nonempty (Quiver.Path a b)) :
    Function.Injective (readout d r) ↔
      ∀ a : V, Subsingleton (Σ b : V, a ⟶ b) := by
  classical
  constructor
  · intro hinj z
    refine ⟨?_⟩
    rintro ⟨a, e⟩ ⟨b, f⟩
    by_contra hab
    obtain ⟨p, A, B, _, _, _, _, _, _, _, _, _, hnoninjective⟩ :=
      branching_collision_inventory d r recurrent z ⟨a, e⟩ ⟨b, f⟩ hab
    exact hnoninjective hinj
  · intro unique x y hxy
    exact deterministic_duration_unique d hd unique x.2.length x.2 y.2 rfl
      (congrArg Prod.snd hxy)

#print axioms branching_collision_inventory
#print axioms readout_injective_iff_no_branching

end D5.S3.ConceptDynamics.Spacetime.NamedPathDurationReconstruction
