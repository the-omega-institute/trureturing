/- GID: D5/S3/StatisticalMechanics/HoneycombCylinderCoordination
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/HoneycombCylinderCoordination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Graph distances and coordination sequences of diagonal honeycomb cylinders. -/

/-
admission_basis: open-problem-resolution (#27075; Proved)
escape_witness: geodesic constructs a honeycomb walk of the explicit potential length for every
integer-coordinate vertex by strong induction; plane_distance and quotient_minimum use it.
Direct frozen dependencies:
D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.potential_dist
(module statement_id sha256:f8b677ea402e38581fbfa04887d18040684e7baa21f05cad6421d45525c0cd21).
D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual
(module statement_id sha256:39388ebec954891d46f7cc5672ca48cf1a1d6ded633cb8d8c0e28efbc0c5894d);
consumers=potential, potential_step, potential_zero, potential_descent, plane_distance, band_minimum,
AFiber, BFiber, finiteAFiber, finiteBFiber, evenShellEquiv, oddShellEquiv, a_fiber_card, b_fiber_card;
the A and B parameters are (0,0) and (0,1).
Proof shapes inline the new helpers. The distance and counting conclusions retain the
inductive constructions; coordinate normalisations are bind-only with the consumers below.
Vertex: proof_shape=bind-only; consumers=honeycombGraph, translationSetoid
edge: proof_shape=bind-only; consumers=honeycombGraph, potential_step, potential_descent, shift_adj
honeycombGraph: proof_shape=bind-only; consumers=geodesic, cylinderGraph, projectHom
potential: proof_shape=bind-only; consumers=geodesic, plane_distance, rep_distance, shellEquiv
potential_step: proof_shape=bind-only; consumers=plane_distance
potential_zero: proof_shape=bind-only; consumers=geodesic
potential_descent: proof_shape=bind-only; consumers=geodesic
geodesic: proof_shape=content; consumers=plane_distance, quotient_reachable, quotient_upper
plane_distance: proof_shape=content; consumers=quotient_minimum
shift: proof_shape=bind-only; consumers=translationSetoid, shift_adj, normal, band_minimum
shift_zero: proof_shape=bind-only; consumers=translationSetoid, band_unique, band_minimum
shift_add: proof_shape=bind-only; consumers=translationSetoid
translationSetoid: proof_shape=bind-only; consumers=Cylinder, cylinderGraph, repEquiv
Cylinder: proof_shape=bind-only; consumers=cylinderGraph, origin, c
cylinderGraph: proof_shape=bind-only; consumers=c, projectHom, lift_walk, rep_distance
origin: proof_shape=bind-only; consumers=c, quotient_reachable, quotient_minimum, zero_card
c: proof_shape=bind-only; consumers=even_card, odd_card, zero_card, count_formula, result
shift_adj: proof_shape=bind-only; consumers=lift_edge
projectHom: proof_shape=bind-only; consumers=quotient_reachable, quotient_upper
quotient_reachable: proof_shape=content; consumers=quotient_minimum, zero_card
quotient_upper: proof_shape=content; consumers=quotient_minimum, rep_distance
lift_edge: proof_shape=bind-only; consumers=lift_walk
lift_walk: proof_shape=content; consumers=quotient_minimum
quotient_minimum: proof_shape=content; consumers=rep_distance
lower: proof_shape=bind-only; consumers=InBand, normal, evenShellEquiv, oddShellEquiv
InBand: proof_shape=bind-only; consumers=normal_band, band_unique, band_minimum, Rep
normal: proof_shape=bind-only; consumers=normal_class, normal_band, repEquiv
normal_class: proof_shape=bind-only; consumers=repEquiv
normal_band: proof_shape=bind-only; consumers=repEquiv
band_unique: proof_shape=bind-only; consumers=repEquiv
band_minimum: proof_shape=bind-only; consumers=rep_distance
Rep: proof_shape=bind-only; consumers=repEquiv, rep_distance, evenShellEquiv, oddShellEquiv
repEquiv: proof_shape=bind-only; consumers=shellEquiv
rep_distance: proof_shape=content; consumers=shellEquiv
shellEquiv: proof_shape=content; consumers=finite_shell, even_card, odd_card
AFiber: proof_shape=bind-only; consumers=finiteAFiber, evenShellEquiv, a_fiber_card
BFiber: proof_shape=bind-only; consumers=finiteBFiber, oddShellEquiv, b_fiber_card
finiteAFiber: proof_shape=bind-only; consumers=finite_shell
finiteBFiber: proof_shape=bind-only; consumers=finite_shell
evenShellEquiv: proof_shape=bind-only; consumers=finite_shell, even_card
oddShellEquiv: proof_shape=bind-only; consumers=finite_shell, odd_card
finite_shell: proof_shape=content; consumers=zero_card
a_fiber_card: proof_shape=bind-only; consumers=even_card
b_fiber_card: proof_shape=bind-only; consumers=odd_card
interval_sum: proof_shape=bind-only; consumers=even_card, odd_card
even_card: proof_shape=content; consumers=count_formula
odd_card: proof_shape=content; consumers=count_formula
zero_card: proof_shape=content; consumers=count_formula
count_formula: proof_shape=content; consumers=result
Reg below denotes Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.
result: proof_shape=content; consumers=Reg.initial_values, Reg.family
-/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import D5.S3.StatisticalMechanics.TeaCoordinationSequence

/-! Literal honeycomb graph distances and diagonal translation quotients. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.HoneycombCylinderCoordination

/-- False denotes A and true denotes B; the two remaining coordinates are integers. -/
abbrev Vertex := Bool × ℤ × ℤ

private def edge (i j a b : ℤ) : Prop :=
  (i = a ∧ j = b) ∨ (i = a + 1 ∧ j = b) ∨ (i = a ∧ j = b + 1)

/-- The honeycomb graph, with the three specified neighbours of every A vertex. -/
def honeycombGraph : SimpleGraph Vertex where
  Adj u v :=
    (u.1 = false ∧ v.1 = true ∧ edge u.2.1 u.2.2 v.2.1 v.2.2) ∨
    (v.1 = false ∧ u.1 = true ∧ edge v.2.1 v.2.2 u.2.1 u.2.2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by rintro ⟨b, i, j⟩ h; cases b <;> simp_all⟩

def potential (v : Vertex) : ℕ :=
  if v.1 then 2 * (TeaCoordinationSequence.residual v.2.1 v.2.2 0 1).toNat + 1
  else 2 * (TeaCoordinationSequence.residual v.2.1 v.2.2 0 0).toNat

private lemma potential_step (u v : Vertex) (h : honeycombGraph.Adj u v) :
    potential u ≤ potential v + 1 := by
  rcases u with ⟨c, i, j⟩
  rcases v with ⟨d, a, b⟩
  change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) at h
  cases c <;> cases d <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    false_and, and_false, or_false, false_or, true_and] at h
  all_goals rcases h with h | h | h
  all_goals rcases h with ⟨h₁, h₂⟩
  all_goals dsimp [potential, TeaCoordinationSequence.residual]; omega

private lemma potential_zero (v : Vertex) (h : potential v = 0) :
    v = (false, 0, 0) := by
  rcases v with ⟨c, i, j⟩
  cases c
  · have hi : i = 0 ∧ j = 0 := by dsimp [potential, TeaCoordinationSequence.residual] at h; omega
    rcases hi with ⟨rfl, rfl⟩; rfl
  · dsimp [potential] at h; omega

private lemma potential_descent (v : Vertex) (h : 0 < potential v) :
    ∃ w, honeycombGraph.Adj w v ∧ potential w + 1 = potential v := by
  rcases v with ⟨c, i, j⟩
  cases c
  · by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · by_cases hi' : 0 < i
        · refine ⟨(true, i-1, j),
            Or.inr ⟨rfl, rfl, Or.inr (Or.inl ⟨by dsimp; omega, rfl⟩)⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual]; omega
        · refine ⟨(true, i, j-1),
            Or.inr ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, by dsimp; omega⟩)⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual] at h ⊢; omega
      · by_cases hs : 0 ≤ i+j
        · refine ⟨(true, i-1, j),
            Or.inr ⟨rfl, rfl, Or.inr (Or.inl ⟨by dsimp; omega, rfl⟩)⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual]; omega
        · refine ⟨(true, i, j), Or.inr ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual]; omega
    · by_cases hj : 0 ≤ j
      · by_cases hs : 0 ≤ i+j
        · refine ⟨(true, i, j-1),
            Or.inr ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, by dsimp; omega⟩)⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual]; omega
        · refine ⟨(true, i, j), Or.inr ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
          dsimp [potential, TeaCoordinationSequence.residual]; omega
      · refine ⟨(true, i, j), Or.inr ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
        dsimp [potential, TeaCoordinationSequence.residual]; omega
  · by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · refine ⟨(false, i, j), Or.inl ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
        dsimp [potential, TeaCoordinationSequence.residual]; omega
      · refine ⟨(false, i, j+1),
          Or.inl ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, ?_⟩
        dsimp [potential, TeaCoordinationSequence.residual]; omega
    · refine ⟨(false, i+1, j),
        Or.inl ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      dsimp [potential, TeaCoordinationSequence.residual]; omega

lemma geodesic (v : Vertex) :
    ∃ p : honeycombGraph.Walk (false, 0, 0) v, p.length = potential v := by
  generalize ht : potential v = t
  induction t using Nat.strong_induction_on generalizing v with
  | h t ih =>
    by_cases hz : t = 0
    · have hv := potential_zero v (by omega)
      subst v
      exact ⟨.nil, by simp [hz]⟩
    · obtain ⟨w, hw, hd⟩ := potential_descent v (by omega)
      obtain ⟨p, hp⟩ := ih (potential w) (by omega) w rfl
      exact ⟨p.append hw.toWalk, by
        rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk, hp]; omega⟩

lemma plane_distance (v : Vertex) :
    honeycombGraph.dist (false, 0, 0) v = potential v := by
  obtain ⟨p, hp⟩ := geodesic v
  apply le_antisymm
  · simpa only [hp] using SimpleGraph.dist_le p
  · have hl :=
      D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
        honeycombGraph potential potential_step (SimpleGraph.Reachable.symm ⟨p⟩)
    simpa only [potential, TeaCoordinationSequence.residual, Bool.false_eq_true, ↓reduceIte,
      max_self, neg_zero, sub_zero, zero_add, Int.toNat_zero,
      mul_zero, SimpleGraph.dist_comm] using hl

private def shift (n : ℕ) (k : ℤ) (v : Vertex) : Vertex :=
  (v.1, v.2.1 + (n : ℤ)*k, v.2.2 + (n : ℤ)*k)

private lemma shift_zero (n : ℕ) (v : Vertex) : shift n 0 v = v := by
  rcases v with ⟨c, i, j⟩; simp [shift]

private lemma shift_add (n : ℕ) (k l : ℤ) (v : Vertex) :
    shift n l (shift n k v) = shift n (k+l) v := by
  simp [shift, mul_add, add_assoc]

/-- Two vertices are identified precisely by an integral power of the diagonal translation. -/
def translationSetoid (n : ℕ) : Setoid Vertex where
  r u v := ∃ k : ℤ, shift n k u = v
  iseqv := ⟨fun u => ⟨0, shift_zero n u⟩, by
    rintro u v ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    rw [shift_add]; simpa using shift_zero n u, by
    rintro u v w ⟨k, rfl⟩ ⟨l, rfl⟩
    exact ⟨k+l, (shift_add n k l u).symm⟩⟩

/-- The vertex quotient by translation through (n,n). -/
abbrev Cylinder (n : ℕ) := Quotient (translationSetoid n)

/-- The literal simple-graph quotient: an edge exists when adjacent representatives exist. -/
def cylinderGraph (n : ℕ) : SimpleGraph (Cylinder n) :=
  honeycombGraph.map (Quotient.mk (translationSetoid n))

/-- The specified center of the cylinder. -/
def origin (n : ℕ) : Cylinder n := Quotient.mk _ (false, 0, 0)

/-- The cardinality of the set at genuine shortest-path distance m. -/
def c (n m : ℕ) : ℕ := Nat.card {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m}

private lemma shift_adj (n : ℕ) (k : ℤ) {u v : Vertex} (h : honeycombGraph.Adj u v) :
    honeycombGraph.Adj (shift n k u) (shift n k v) := by
  rcases h with ⟨hu, hv, he⟩ | ⟨hv, hu, he⟩
  · left; refine ⟨hu, hv, ?_⟩
    rcases he with he | he | he <;>
      dsimp [edge, shift] at * <;> rcases he with ⟨h₁,h₂⟩ <;> omega
  · right; refine ⟨hv, hu, ?_⟩
    rcases he with he | he | he <;>
      dsimp [edge, shift] at * <;> rcases he with ⟨h₁,h₂⟩ <;> omega

private def projectHom (n : ℕ) : honeycombGraph →g cylinderGraph n :=
  SimpleGraph.Hom.map (Quotient.mk (translationSetoid n)) honeycombGraph (by
    intro u v h he
    obtain ⟨k, hk⟩ := Quotient.exact he
    have hc := congrArg Prod.fst hk
    change u.1 = v.1 at hc
    rcases h with ⟨hu, hv, _⟩ | ⟨hv, hu, _⟩ <;> simp_all)

private lemma quotient_reachable (n : ℕ) (q : Cylinder n) :
    (cylinderGraph n).Reachable (origin n) q := by
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨p, _⟩ := geodesic v
    exact ⟨p.map (projectHom n)⟩

private lemma quotient_upper (n : ℕ) (v : Vertex) :
    (cylinderGraph n).dist (origin n) (Quotient.mk _ v) ≤ potential v := by
  obtain ⟨p, hp⟩ := geodesic v
  have h := SimpleGraph.dist_le (p.map (projectHom n))
  change (cylinderGraph n).dist (origin n) (Quotient.mk _ v) ≤ _ at h
  simpa only [SimpleGraph.Walk.length_map, hp] using h

private lemma lift_edge (n : ℕ) (v : Vertex) (q : Cylinder n)
    (h : (cylinderGraph n).Adj (Quotient.mk _ v) q) :
    ∃ w, honeycombGraph.Adj v w ∧ Quotient.mk (translationSetoid n) w = q := by
  obtain ⟨_, a, b, hab, ha, hb⟩ := h
  obtain ⟨k, hk⟩ := Quotient.exact ha
  refine ⟨shift n k b, ?_, ?_⟩
  · simpa only [hk] using shift_adj n k hab
  · have he : (Quotient.mk (translationSetoid n) b : Cylinder n) =
        Quotient.mk _ (shift n k b) := Quotient.sound ⟨k, rfl⟩
    exact he.symm.trans hb

private lemma lift_walk (n : ℕ) {q r : Cylinder n} (p : (cylinderGraph n).Walk q r)
    (v : Vertex) (hv : Quotient.mk (translationSetoid n) v = q) :
    ∃ w, Quotient.mk (translationSetoid n) w = r ∧
      ∃ p' : honeycombGraph.Walk v w, p'.length = p.length := by
  induction p generalizing v with
  | nil => exact ⟨v, hv, .nil, rfl⟩
  | @cons q s r hadj p ih =>
    obtain ⟨w, hw, hq⟩ := lift_edge n v s (hv ▸ hadj)
    obtain ⟨z, hz, p', hp'⟩ := ih w hq
    exact ⟨z, hz, .cons hw p', by simp only [SimpleGraph.Walk.length_cons, hp']⟩

private lemma quotient_minimum (n : ℕ) (q : Cylinder n) :
    ∃ v, Quotient.mk (translationSetoid n) v = q ∧
      potential v = (cylinderGraph n).dist (origin n) q := by
  obtain ⟨p, hp⟩ := (quotient_reachable n q).exists_walk_length_eq_dist
  obtain ⟨v, hv, p', hp'⟩ := lift_walk n p (false, 0, 0) rfl
  refine ⟨v, hv, le_antisymm ?_ ?_⟩
  · rw [← plane_distance]
    exact (SimpleGraph.dist_le p').trans_eq (hp'.trans hp)
  · simpa only [hv] using quotient_upper n v

private def lower (n : ℕ) (b : Bool) : ℤ := if b then -(n : ℤ) else 1-n

private def InBand (n : ℕ) (v : Vertex) : Prop :=
  lower n v.1 ≤ v.2.1 + v.2.2 ∧ v.2.1 + v.2.2 < lower n v.1 + 2*n

private def normal (n : ℕ) (v : Vertex) : Vertex :=
  shift n (-((v.2.1 + v.2.2 - lower n v.1) / (2*n))) v

private lemma normal_class (n : ℕ) (v : Vertex) :
    (Quotient.mk (translationSetoid n) (normal n v) : Cylinder n) = Quotient.mk _ v := by
  apply Eq.symm
  apply Quotient.sound
  exact ⟨_, rfl⟩

private lemma normal_band {n : ℕ} (hn : 0 < n) (v : Vertex) : InBand n (normal n v) := by
  have hn' : (0 : ℤ) < 2*n := by omega
  have h₀ := Int.emod_nonneg (v.2.1 + v.2.2 - lower n v.1) (by omega : (2*(n : ℤ)) ≠ 0)
  have h₁ := Int.emod_lt_of_pos (v.2.1 + v.2.2 - lower n v.1) hn'
  have hd := Int.emod_add_mul_ediv (v.2.1 + v.2.2 - lower n v.1) (2*n)
  have hs : (normal n v).2.1 + (normal n v).2.2 = lower n v.1 +
      (v.2.1 + v.2.2 - lower n v.1) % (2*n) := by
    dsimp [normal, shift]
    nlinarith [hd]
  change lower n v.1 ≤ _ ∧ _ < lower n v.1 + 2*n
  rw [hs]
  omega

private lemma band_unique {n : ℕ} (hn : 0 < n) {u v : Vertex}
    (hu : InBand n u) (hv : InBand n v)
    (he : (Quotient.mk (translationSetoid n) u : Cylinder n) = Quotient.mk _ v) : u = v := by
  obtain ⟨k, rfl⟩ := Quotient.exact he
  have hn' : (0 : ℤ) < n := by omega
  have hk : k = 0 := by
    dsimp [InBand, shift] at hu hv
    by_cases h₀ : 0 < k
    · have hd : (n : ℤ) ≤ n*k := by nlinarith
      omega
    · by_cases h₁ : k < 0
      · have hd : (n : ℤ)*k ≤ -n := by nlinarith
        omega
      · omega
  simp [hk, shift_zero]

private lemma band_minimum {n : ℕ} (hn : 0 < n) (v : Vertex) (hv : InBand n v) (k : ℤ) :
    potential v ≤ potential (shift n k v) := by
  have hn' : (0 : ℤ) < n := by omega
  by_cases hk : k = 0
  · simp only [hk, shift_zero, le_refl]
  rcases v with ⟨b, i, j⟩
  by_cases hk' : 0 < k
  · have hd : (n : ℤ) ≤ n*k := by nlinarith
    cases b <;> dsimp [InBand, lower] at hv <;>
      dsimp [potential, shift, TeaCoordinationSequence.residual] <;> omega
  · have hkneg : k ≤ -1 := by omega
    have hd : (n : ℤ)*k ≤ -n := by nlinarith
    cases b <;> dsimp [InBand, lower] at hv <;>
      dsimp [potential, shift, TeaCoordinationSequence.residual] <;> omega

private abbrev Rep (n : ℕ) := {v : Vertex // InBand n v}

private def repEquiv {n : ℕ} (hn : 0 < n) : Cylinder n ≃ Rep n where
  toFun := Quotient.lift (fun v => ⟨normal n v, normal_band hn v⟩) (by
    intro u v h
    apply Subtype.ext
    exact band_unique hn (normal_band hn u) (normal_band hn v)
      ((normal_class n u).trans ((Quotient.sound h).trans (normal_class n v).symm)))
  invFun v := Quotient.mk _ v.1
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h v => exact normal_class n v
  right_inv v := Subtype.ext (band_unique hn (normal_band hn v.1) v.2 (normal_class n v.1))

private lemma rep_distance {n : ℕ} (hn : 0 < n) (v : Rep n) :
    (cylinderGraph n).dist (origin n) (Quotient.mk _ v.1) = potential v.1 := by
  obtain ⟨w, hw, hp⟩ := quotient_minimum n (Quotient.mk _ v.1)
  obtain ⟨k, hk⟩ := Quotient.exact hw.symm
  apply le_antisymm (quotient_upper n v.1)
  rw [← hp, ← hk]
  exact band_minimum hn v.1 v.2 k

private def shellEquiv {n : ℕ} (hn : 0 < n) (m : ℕ) :
    {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m} ≃
      {v : Rep n // potential v.1 = m} :=
  ((repEquiv hn).symm.subtypeEquiv (fun v => by
    change potential v.1 = m ↔ (cylinderGraph n).dist (origin n) (Quotient.mk _ v.1) = m
    rw [rep_distance hn])).symm

abbrev AFiber (s : ℤ) (k : ℕ) :=
  {i : ℤ // (TeaCoordinationSequence.residual i (s-i) 0 0) = k}
abbrev BFiber (s : ℤ) (k : ℕ) :=
  {i : ℤ // (TeaCoordinationSequence.residual i (s-i) 0 1) = k}

instance finiteAFiber (s : ℤ) (k : ℕ) : Finite (AFiber s k) := by
  let f (i : AFiber s k) : Set.Icc (-(k : ℤ)) k :=
    ⟨i.1, by have h := i.2; dsimp [TeaCoordinationSequence.residual] at h; constructor <;> omega⟩
  exact Finite.of_injective f (fun i j h => Subtype.ext
    (congrArg (fun z : Set.Icc (-(k : ℤ)) k => z.1) h))

instance finiteBFiber (s : ℤ) (k : ℕ) : Finite (BFiber s k) := by
  let f (i : BFiber s k) : Set.Icc (-(k : ℤ)-1) k :=
    ⟨i.1, by have h := i.2; dsimp [TeaCoordinationSequence.residual] at h; constructor <;> omega⟩
  exact Finite.of_injective f (fun i j h => Subtype.ext
    (congrArg (fun z : Set.Icc (-(k : ℤ)-1) k => z.1) h))

private def evenShellEquiv (n k : ℕ) :
    {v : Rep n // potential v.1 = 2*k} ≃
      Σ s : Set.Icc (1-(n : ℤ)) n, AFiber s.1 k where
  toFun v := by
    have hc : v.1.1.1 = false := by
      have h := v.2
      cases hb : v.1.1.1 <;> simp [potential, hb] at h ⊢; omega
    refine ⟨⟨v.1.1.2.1 + v.1.1.2.2, ?_⟩, ⟨v.1.1.2.1, ?_⟩⟩
    · have h := v.1.2
      dsimp [InBand, lower] at h
      rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      constructor <;> omega
    · have h := v.2
      have hr : 0 ≤ (TeaCoordinationSequence.residual v.1.1.2.1 v.1.1.2.2 0 0) := le_max_left _ _
      dsimp only [potential] at h
      rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have he : v.1.1.2.1 + v.1.1.2.2 - v.1.1.2.1 = v.1.1.2.2 := by omega
      dsimp only; rw [he]; omega
  invFun s :=
    ⟨⟨(false, s.2.1, s.1.1-s.2.1), by
      have hl := s.1.2.1
      have hu := s.1.2.2
      dsimp [InBand, lower]; constructor <;> omega⟩, by
        have h := s.2.2
        dsimp [potential]
        omega⟩
  left_inv v := by
    rcases v with ⟨⟨⟨b,i,j⟩,hv⟩,hp⟩
    cases b
    · apply Subtype.ext
      apply Subtype.ext
      change (false, i, i+j-i) = (false, i, j)
      congr 2; omega
    · dsimp [potential] at hp; omega
  right_inv s := by
    rcases s with ⟨⟨s,hs⟩,⟨i,hi⟩⟩
    apply Sigma.ext
    · apply Subtype.ext; dsimp; omega
    · refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr rfl
      dsimp only
      rw [show i+(s-i) = s by omega]

private def oddShellEquiv (n k : ℕ) :
    {v : Rep n // potential v.1 = 2*k+1} ≃
      Σ s : Set.Icc (-(n : ℤ)) (n-1), BFiber s.1 k where
  toFun v := by
    have hc : v.1.1.1 = true := by
      have h := v.2
      cases hb : v.1.1.1 <;> simp [potential, hb] at h ⊢; omega
    refine ⟨⟨v.1.1.2.1 + v.1.1.2.2, ?_⟩, ⟨v.1.1.2.1, ?_⟩⟩
    · have h := v.1.2
      dsimp [InBand, lower] at h
      rw [hc] at h
      simp only [↓reduceIte] at h
      constructor <;> omega
    · have h := v.2
      have hr : 0 ≤ (TeaCoordinationSequence.residual v.1.1.2.1 v.1.1.2.2 0 1) := le_max_left _ _
      dsimp only [potential] at h
      rw [hc] at h
      simp only [↓reduceIte] at h
      have he : v.1.1.2.1 + v.1.1.2.2 - v.1.1.2.1 = v.1.1.2.2 := by omega
      dsimp only; rw [he]; omega
  invFun s :=
    ⟨⟨(true, s.2.1, s.1.1-s.2.1), by
      have hl := s.1.2.1
      have hu := s.1.2.2
      dsimp [InBand, lower]; constructor <;> omega⟩, by
        have h := s.2.2
        dsimp [potential]
        omega⟩
  left_inv v := by
    rcases v with ⟨⟨⟨b,i,j⟩,hv⟩,hp⟩
    cases b
    · dsimp [potential] at hp; omega
    · apply Subtype.ext
      apply Subtype.ext
      change (true, i, i+j-i) = (true, i, j)
      congr 2; omega
  right_inv s := by
    rcases s with ⟨⟨s,hs⟩,⟨i,hi⟩⟩
    apply Sigma.ext
    · apply Subtype.ext; dsimp; omega
    · refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr rfl
      dsimp only
      rw [show i+(s-i) = s by omega]

private lemma finite_shell {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Finite {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m} := by
  by_cases hm : m % 2 = 0
  · have he : m = 2*(m/2) := by omega
    rw [he]
    exact Finite.of_equiv _ ((shellEquiv hn _).trans (evenShellEquiv n _)).symm
  · have he : m = 2*(m/2)+1 := by omega
    rw [he]
    exact Finite.of_equiv _ ((shellEquiv hn _).trans (oddShellEquiv n _)).symm

lemma a_fiber_card (s : ℤ) (k : ℕ) (hk : 0 < k) :
    Nat.card (AFiber s k) =
      (if -(k : ℤ) < s ∧ s < k then 2 else 0) +
      (if s = k then k+1 else 0) + (if s = -(k : ℤ) then k+1 else 0) := by
  classical
  by_cases hs : -(k : ℤ) < s ∧ s < k
  · have hp : s ≠ k := by omega
    have hm : s ≠ -(k : ℤ) := by omega
    simp only [ite_eq_left hs, ite_eq_right hp, ite_eq_right hm, add_zero]
    change Set.ncard {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 0) = k} = 2
    by_cases hz : 0 ≤ s
    · have he : {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 0) = k} = {s-k, (k : ℤ)} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        dsimp [TeaCoordinationSequence.residual]; omega
      rw [he]; exact Set.ncard_pair (by omega)
    · have he : {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 0) = k} = {-(k : ℤ), s+k} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        dsimp [TeaCoordinationSequence.residual]; omega
      rw [he]; exact Set.ncard_pair (by omega)
  · by_cases hp : s = k
    · subst s
      have hm : (k : ℤ) ≠ -k := by omega
      simp only [ite_eq_right hs, ite_eq_right hm, zero_add, add_zero]
      have he : {i : ℤ | (TeaCoordinationSequence.residual i (k-i) 0 0) = k}
          = Set.Icc 0 (k : ℤ) := by
        ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        dsimp [TeaCoordinationSequence.residual]; omega
      change Nat.card ↑{i : ℤ | (TeaCoordinationSequence.residual i (k-i) 0 0) = k} = _
      rw [he]; simp [Nat.card_eq_fintype_card]
    · by_cases hm : s = -(k : ℤ)
      · subst s
        simp only [ite_eq_right hs, ite_eq_right hp, zero_add]
        have he : {i : ℤ | (TeaCoordinationSequence.residual i (-k-i) 0 0) = k}
            = Set.Icc (-(k : ℤ)) 0 := by
          ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
          dsimp [TeaCoordinationSequence.residual]; omega
        change Nat.card ↑{i : ℤ | (TeaCoordinationSequence.residual i (-k-i) 0 0) = k} = _
        rw [he]; simp [Nat.card_eq_fintype_card, add_comm]
      · let : IsEmpty (AFiber s k) := ⟨by
          rintro ⟨i, hi⟩; dsimp [TeaCoordinationSequence.residual] at hi; omega⟩
        simp [hs, hp, hm]

lemma b_fiber_card (s : ℤ) (k : ℕ) :
    Nat.card (BFiber s k) =
      (if -(k : ℤ) ≤ s ∧ s < k then 2 else 0) +
      (if s = k then k+1 else 0) + (if s = -(k : ℤ)-1 then k+2 else 0) := by
  classical
  by_cases hs : -(k : ℤ) ≤ s ∧ s < k
  · have hp : s ≠ k := by omega
    have hm : s ≠ -(k : ℤ)-1 := by omega
    simp only [ite_eq_left hs, ite_eq_right hp, ite_eq_right hm, add_zero]
    change Set.ncard {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 1) = k} = 2
    by_cases hz : 0 ≤ s
    · have he : {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 1) = k} = {s-k, (k : ℤ)} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        dsimp [TeaCoordinationSequence.residual]; omega
      rw [he]; exact Set.ncard_pair (by omega)
    · have he : {i : ℤ | (TeaCoordinationSequence.residual i (s-i) 0 1) = k}
        = {-(k : ℤ)-1, s+k+1} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        dsimp [TeaCoordinationSequence.residual]; omega
      rw [he]; exact Set.ncard_pair (by omega)
  · by_cases hp : s = k
    · subst s
      have hm : (k : ℤ) ≠ -k-1 := by omega
      simp only [ite_eq_right hs, ite_eq_right hm, zero_add, add_zero]
      have he : {i : ℤ | (TeaCoordinationSequence.residual i (k-i) 0 1) = k}
          = Set.Icc 0 (k : ℤ) := by
        ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        dsimp [TeaCoordinationSequence.residual]; omega
      change Nat.card ↑{i : ℤ | (TeaCoordinationSequence.residual i (k-i) 0 1) = k} = _
      rw [he]; simp [Nat.card_eq_fintype_card]
    · by_cases hm : s = -(k : ℤ)-1
      · subst s
        simp only [ite_eq_right hs, ite_eq_right hp, zero_add]
        have he : {i : ℤ | (TeaCoordinationSequence.residual i (-k-1-i) 0 1) = k}
            = Set.Icc (-(k : ℤ)-1) 0 := by
          ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
          dsimp [TeaCoordinationSequence.residual]; omega
        change Nat.card ↑{i : ℤ | (TeaCoordinationSequence.residual i (-k-1-i) 0 1) = k} = _
        rw [he]; simp [Nat.card_eq_fintype_card]; omega
      · let : IsEmpty (BFiber s k) := ⟨by
          rintro ⟨i, hi⟩; dsimp [TeaCoordinationSequence.residual] at hi; omega⟩
        simp [hs, hp, hm]

lemma interval_sum (L U a b : ℤ) :
    (∑ s ∈ Finset.Icc L U, if a ≤ s ∧ s ≤ b then (2 : ℕ) else 0) =
      2 * (min U b + 1 - max L a).toNat := by
  classical
  rw [← Finset.sum_filter]
  have he : (Finset.Icc L U).filter (fun s => a ≤ s ∧ s ≤ b) =
      Finset.Icc (max L a) (min U b) := by
    ext s; simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]; omega
  rw [he]
  simp [Int.card_Icc, mul_comm]

private lemma even_card {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    c n (2*k) = if k < n then 6*k else if k = n then 5*n-1 else 4*n := by
  classical
  rw [c, Nat.card_congr ((shellEquiv hn _).trans (evenShellEquiv n k)), Nat.card_sigma]
  rw [← Finset.sum_subtype (Finset.Icc (1-(n : ℤ)) n) (by simp)
    (fun s => Nat.card (AFiber s k))]
  simp_rw [a_fiber_card _ k hk, Finset.sum_add_distrib]
  have hpred (s : ℤ) : (-(k : ℤ) < s ∧ s < k) ↔ (1-(k : ℤ) ≤ s ∧ s ≤ k-1) := by omega
  simp_rw [hpred]
  rw [interval_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  split_ifs <;> omega

private lemma odd_card {n : ℕ} (hn : 0 < n) (k : ℕ) :
    c n (2*k+1) = if k < n then 6*k+3 else 4*n := by
  classical
  rw [c, Nat.card_congr ((shellEquiv hn _).trans (oddShellEquiv n k)), Nat.card_sigma]
  rw [← Finset.sum_subtype (Finset.Icc (-(n : ℤ)) (n-1)) (by simp)
    (fun s => Nat.card (BFiber s k))]
  simp_rw [b_fiber_card, Finset.sum_add_distrib]
  have hpred (s : ℤ) : (-(k : ℤ) ≤ s ∧ s < k) ↔ (-(k : ℤ) ≤ s ∧ s ≤ k-1) := by omega
  simp_rw [hpred]
  rw [interval_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  split_ifs <;> omega

private lemma zero_card {n : ℕ} (hn : 0 < n) : c n 0 = 1 := by
  let S := {v : Cylinder n // (cylinderGraph n).dist (origin n) v = 0}
  let : Finite S := finite_shell hn 0
  let : Unique S := {
    default := ⟨origin n, SimpleGraph.dist_self⟩
    uniq := by
      rintro ⟨v,hv⟩
      apply Subtype.ext
      exact ((quotient_reachable n v).dist_eq_zero_iff.mp hv).symm }
  let : Fintype S := Fintype.ofFinite S
  change Nat.card S = 1
  rw [Nat.card_eq_fintype_card, Fintype.card_unique]

private lemma count_formula {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (c n m : ℤ) = if m = 0 then 1 else if m < 2*n then 3*(m : ℤ)
      else if m = 2*n then 5*(n : ℤ)-1 else 4*(n : ℤ) := by
  by_cases hz : m = 0
  · subst m; simp [zero_card hn]
  by_cases hm : m % 2 = 0
  · have he : m = 2*(m/2) := by omega
    rw [he, even_card hn (m/2) (by omega)]
    split_ifs <;>
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub (show 1 ≤ 5*n by omega)] <;> omega
  · have he : m = 2*(m/2)+1 := by omega
    rw [he, odd_card hn (m/2)]
    split_ifs
    all_goals simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    all_goals first | contradiction | omega

open PowerSeries

set_option maxHeartbeats 2000000 in
-- The symbolic second differences require simultaneous width and radius case analysis.
/-- The registered identity for every positive cylinder width, with denominators cleared. -/
theorem result : ∀ n : ℕ, 1 ≤ n →
    (1 - X)^2 * (PowerSeries.mk fun m => (c n m : ℤ)) =
      (1 - X) * (1 + 2*X - C ((n : ℤ)-2)*X^(2*n) - C ((n : ℤ)-1)*X^(2*n+1)) +
        3*X^2*(1 - X^(2*n-2)) := by
  intro n hn
  have hn' : 0 < n := by omega
  let S : PowerSeries ℤ := PowerSeries.mk fun m => (c n m : ℤ)
  have hs : S - 2*(X^1*S) + X^2*S =
      1 + X + X^2 - C ((n : ℤ)+1)*X^(2*n) - X^(2*n+1) +
        C ((n : ℤ)-1)*X^(2*n+2) := by
    ext m
    simp only [map_add (coeff m), map_sub (coeff m), coeff_ofNat_mul, coeff_X_pow_mul', S, coeff_mk,
      coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
    simp_rw [count_formula hn']
    by_cases hn1 : n = 1
    · subst n
      have hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m := by omega
      rcases hm with rfl | rfl | rfl | rfl | rfl | hm <;>
        simp (disch := omega) <;> omega
    by_cases hm : m < 3
    · have hc : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hc with rfl | rfl | rfl <;>
        simp (disch := omega) <;> omega
    · by_cases h₀ : m < 2*n
      · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
      · by_cases h₁ : m = 2*n
        · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
        · by_cases h₂ : m = 2*n+1
          · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
          · by_cases h₃ : m = 2*n+2
            · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
            · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
  have hp : (X : PowerSeries ℤ)^2 * X^(2*n-2) = X^(2*n) := by
    rw [← pow_add]
    congr 1
    omega
  have h₁ : (X : PowerSeries ℤ)^(2*n+1) = X^(2*n)*X := by rw [pow_succ]
  have h₂ : (X : PowerSeries ℤ)^(2*n+2) = X^(2*n)*X^2 := by rw [pow_add]
  change (1-X)^2*S = _
  calc
    _ = S - 2*(X^1*S) + X^2*S := by ring
    _ = 1 + X + X^2 - C ((n : ℤ)+1)*X^(2*n) - X^(2*n+1) +
        C ((n : ℤ)-1)*X^(2*n+2) := hs
    _ = (1-X)*(1+2*X-C ((n : ℤ)-2)*X^(2*n)-C ((n : ℤ)-1)*X^(2*n+1)) +
        3*X^2*(1-X^(2*n-2)) := by
      simp only [map_add, map_sub, map_natCast, map_one, map_ofNat, h₁, h₂]
      calc
        _ = (1-X)*(1+2*X-((n : PowerSeries ℤ)-2)*X^(2*n)-
              ((n : PowerSeries ℤ)-1)*(X^(2*n)*X)) + 3*X^2*(1-X^(2*n-2)) -
            3*(X^(2*n)-X^2*X^(2*n-2)) := by ring
        _ = _ := by rw [hp]; ring

end D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
