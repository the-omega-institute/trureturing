/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedCollisionEnergyBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedCollisionEnergyBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The two-axis phase bounds control the global mixed collision count. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OverlapPhaseEnergy
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
import Batteries.Tactic.OpenPrivate

/-! Summing the translated overlap bounds counts each ordered distance-two pair once. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedCollisionEnergyBound

open scoped Classical BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsSwitching)
open BalancedCubeComponentBoundary (directions)
open Q9MixedBoundaryCollisions (Separated mixedTriples)
open Q9OverlapPhaseEnergy
  (phase degreeSum degreeCount twoAxisTranslate translated_phase_energy_bound)
open private switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private translate_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OverlapPhaseEnergy
open private ordered_two_flips ordered_axes_unique two_flip_disagreements mem_mixedTriples from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions

/-- Ordered pairs from the two supports at Hamming distance two. -/
def distanceTwoPairs (C D : Finset (Q 9)) : Finset (Q 9 × Q 9) :=
  (C.product D).filter fun p => hammingDist p.1 p.2 = 2

private theorem mem_distanceTwoPairs {C D : Finset (Q 9)} {p : Q 9 × Q 9} :
    p ∈ distanceTwoPairs C D ↔ p.1 ∈ C ∧ p.2 ∈ D ∧ hammingDist p.1 p.2 = 2 := by
  simp [distanceTwoPairs, and_assoc]

private def commonDirections (C D : Finset (Q 9)) (p : Q 9 × Q 9) : Finset (Fin 9) :=
  directions C p.1 ∩ directions D p.2

/-- The number of ordered distance-two pairs with exactly `r` common internal directions. -/
def commonDegreeCount (C D : Finset (Q 9)) (r : ℕ) : ℕ :=
  ((distanceTwoPairs C D).filter fun p => (commonDirections C D p).card = r).card

private def degreeCharge (d : ℕ) : ℕ :=
  3 * d + 6 * (if d = 0 then 1 else 0) + 2 * (if d = 1 then 1 else 0)

private theorem sum_degreeCharge {α : Type*} (s : Finset α) (d : α → ℕ) :
    (∑ x ∈ s, degreeCharge (d x)) =
      3 * (∑ x ∈ s, d x) + 6 * (s.filter fun x => d x = 0).card +
        2 * (s.filter fun x => d x = 1).card := by
  simp only [degreeCharge, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp

private theorem phase_directions {A B : Finset (Q 9)} {σ τ : Q 9 → ℝ} {ε : ℝ}
    (hσ : IsSwitching A σ) (hτ : IsSwitching B τ) (hε : ε ^ 2 = 1)
    {x : Q 9} (hx : x ∈ phase A B σ τ ε) :
    directions (phase A B σ τ ε) x = directions (A ∩ B) x := by
  have ⟨hxK, hxSign⟩ := Finset.mem_filter.mp hx
  have ⟨hxA, hxB⟩ := Finset.mem_inter.mp hxK
  ext i
  rw [mem_directions, mem_directions]
  refine ⟨fun hy => (Finset.mem_filter.mp hy).1, fun hy => Finset.mem_filter.mpr ⟨hy, ?_⟩⟩
  obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
  have hEdge := (hσ.2 x hxA _ hyA (flip_adj x i)).symm.trans
    (hτ.2 x hxB _ hyB (flip_adj x i))
  have hUnit := switching_sq hτ hxB
  have hNonzero : τ x ≠ 0 := by
    intro h
    simp [h] at hUnit
  apply mul_left_cancel₀ hNonzero
  calc
    τ x * σ (flip x i) = ε * (σ x * σ (flip x i)) := by
      rw [hxSign]
      calc
        τ x * σ (flip x i) = ε ^ 2 * (τ x * σ (flip x i)) := by rw [hε, one_mul]
        _ = _ := by ring
    _ = ε * (τ x * τ (flip x i)) := by rw [hEdge]
    _ = τ x * (ε * τ (flip x i)) := by ring

private def overlap (C D : Finset (Q 9)) (ab : Fin 9 × Fin 9) : Finset (Q 9) :=
  C ∩ D.map (twoAxisTranslate ab.1 ab.2).toEmbedding

private theorem mem_translate {D : Finset (Q 9)} {a b : Fin 9} {x : Q 9} :
    x ∈ D.map (twoAxisTranslate a b).toEmbedding ↔ twoAxisTranslate a b x ∈ D :=
  Finset.mem_map_equiv

private theorem overlap_energy (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ) (hsep : Separated C D)
    (ab : Fin 9 × Fin 9) (hab : ab.1 < ab.2) :
    (∑ x ∈ overlap C D ab, degreeCharge (directions (overlap C D ab) x).card) ≤
      7 * (overlap C D ab).card := by
  let D' := D.map (twoAxisTranslate ab.1 ab.2).toEmbedding
  obtain ⟨τ', hτ', hEnergy⟩ :=
    translated_phase_energy_bound C D σ τ ab.1 ab.2 hab.ne hC hD hσ hτ hsep.2
  let K := overlap C D ab
  let pos := phase C D' σ τ' 1
  let neg := phase C D' σ τ' (-1)
  have hUnion : pos ∪ neg = K := by
    ext x
    rw [Finset.mem_union]
    constructor
    · intro hx
      exact hx.elim (fun h => (Finset.mem_filter.mp h).1) (fun h => (Finset.mem_filter.mp h).1)
    · intro hx
      change x ∈ C ∩ D' at hx
      have ⟨hxC, hxD'⟩ := Finset.mem_inter.mp hx
      rcases hσ.1 x hxC with hs | hs <;> rcases hτ'.1 x hxD' with ht | ht <;>
        simp [pos, neg, phase, hxC, hxD', hs, ht]
  have hDisjoint : Disjoint pos neg := by
    apply Finset.disjoint_left.mpr
    intro x hxPos hxNeg
    have hPos : σ x = 1 * τ' x := (Finset.mem_filter.mp hxPos).2
    have hNeg : σ x = -1 * τ' x := (Finset.mem_filter.mp hxNeg).2
    have hZero : τ' x = 0 := by linarith
    have hUnit := switching_sq hτ' (Finset.mem_inter.mp (Finset.mem_filter.mp hxPos).1).2
    simp [hZero] at hUnit
  have hPhase (ε : ℝ) (hε : ε ^ 2 = 1) :
      (∑ x ∈ phase C D' σ τ' ε, degreeCharge (directions K x).card) ≤
        7 * (phase C D' σ τ' ε).card := by
    calc
      _ = ∑ x ∈ phase C D' σ τ' ε,
          degreeCharge (directions (phase C D' σ τ' ε) x).card := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [phase_directions hσ hτ' hε hx]
        rfl
      _ ≤ _ := by
        rw [sum_degreeCharge]
        exact hEnergy ε hε
  have hPos := hPhase 1 (by norm_num)
  have hNeg := hPhase (-1) (by norm_num)
  let charge (x : Q 9) := degreeCharge (directions K x).card
  change (∑ x ∈ K, charge x) ≤ 7 * K.card
  conv_lhs => rw [← hUnion, Finset.sum_union hDisjoint]
  conv_rhs => rw [← hUnion, Finset.card_union_of_disjoint hDisjoint, Nat.mul_add]
  exact Nat.add_le_add hPos hNeg

private theorem directions_overlap (C D : Finset (Q 9)) (ab : Fin 9 × Fin 9) (x : Q 9) :
    directions (overlap C D ab) x = commonDirections C D (x, twoAxisTranslate ab.1 ab.2 x) := by
  ext i
  simp only [commonDirections, Finset.mem_inter, mem_directions, overlap, mem_translate,
    translate_flip]

private theorem sum_overlaps (C D : Finset (Q 9)) (w : Q 9 × Q 9 → ℕ) :
    (∑ ab ∈ (Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun ab => ab.1 < ab.2),
      ∑ x ∈ overlap C D ab, w (x, twoAxisTranslate ab.1 ab.2 x)) =
        ∑ p ∈ distanceTwoPairs C D, w p := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij (fun p : Sigma (fun _ : Fin 9 × Fin 9 => Q 9) =>
    (p.2, twoAxisTranslate p.1.1 p.1.2 p.2))
  · rintro ⟨⟨a, b⟩, x⟩ hx
    obtain ⟨hab, hxK⟩ := Finset.mem_sigma.mp hx
    have hlt : a < b := (Finset.mem_filter.mp hab).2
    obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hxK
    refine mem_distanceTwoPairs.mpr ⟨hxC, mem_translate.mp hxD, ?_⟩
    change (Finset.univ.filter fun k => x k ≠ flip (flip x a) b k).card = 2
    rw [two_flip_disagreements x hlt.ne, Finset.card_pair hlt.ne]
  · rintro ⟨⟨a, b⟩, x⟩ hx ⟨⟨i, j⟩, y⟩ hy he
    have hlt : a < b := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
    have hij : i < j := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).2
    have hxy : x = y := congrArg Prod.fst he
    subst y
    have hTrans : flip (flip x a) b = flip (flip x i) j := congrArg Prod.snd he
    have hAxes : ({a, b} : Finset (Fin 9)) = {i, j} := by
      rw [← two_flip_disagreements x hlt.ne, ← two_flip_disagreements x hij.ne, hTrans]
    obtain ⟨rfl, rfl⟩ := ordered_axes_unique hlt hij hAxes
    rfl
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hd⟩ := mem_distanceTwoPairs.mp hxy
    change x ∈ C at hx
    change y ∈ D at hy
    change hammingDist x y = 2 at hd
    obtain ⟨a, b, hab, rfl⟩ := ordered_two_flips hd
    exact ⟨⟨(a, b), x⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩,
        Finset.mem_inter.mpr ⟨hx, mem_translate.mpr hy⟩⟩, rfl⟩
  · intro p _
    rfl

private theorem card_mixedTriples (C D : Finset (Q 9)) :
    (mixedTriples C D).card = ∑ p ∈ distanceTwoPairs C D, (commonDirections C D p).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_nbij (fun p : Sigma (fun _ : Q 9 × Q 9 => Fin 9) => (p.1.1, p.1.2, p.2))
  · rintro ⟨⟨x, y⟩, i⟩ h
    obtain ⟨hp, hi⟩ := Finset.mem_sigma.mp h
    obtain ⟨hx, hy, hd⟩ := mem_distanceTwoPairs.mp hp
    obtain ⟨hxi, hyi⟩ := Finset.mem_inter.mp hi
    exact mem_mixedTriples.mpr ⟨hx, hy, hd, (mem_directions C x i).mp hxi,
      (mem_directions D y i).mp hyi⟩
  · rintro ⟨⟨x, y⟩, i⟩ _ ⟨⟨u, v⟩, j⟩ _ h
    change (x, y, i) = (u, v, j) at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rintro ⟨x, y, i⟩ h
    obtain ⟨hx, hy, hd, hxi, hyi⟩ := mem_mixedTriples.mp h
    exact ⟨⟨(x, y), i⟩, Finset.mem_sigma.mpr
      ⟨mem_distanceTwoPairs.mpr ⟨hx, hy, hd⟩,
        Finset.mem_inter.mpr ⟨(mem_directions C x i).mpr hxi, (mem_directions D y i).mpr hyi⟩⟩, rfl⟩

/-- The global phase energy bound for an arbitrary pair of separated balanced cubic supports. -/
theorem mixed_collision_energy_bound (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (hsep : Separated C D)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ) :
    3 * (mixedTriples C D).card + 6 * commonDegreeCount C D 0 + 2 * commonDegreeCount C D 1 ≤
      7 * (distanceTwoPairs C D).card := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 9 × Fin 9)).filter
    (fun ab => ab.1 < ab.2)) fun ab hab =>
      overlap_energy C D σ τ hC hD hσ hτ hsep ab (Finset.mem_filter.mp hab).2
  simp only [directions_overlap] at h
  rw [sum_overlaps C D (fun p => degreeCharge (commonDirections C D p).card)] at h
  have hCard :
      (∑ ab ∈ (Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun ab => ab.1 < ab.2),
        (overlap C D ab).card) = (distanceTwoPairs C D).card := by
    simpa using sum_overlaps C D (fun _ => 1)
  rw [← Finset.mul_sum, hCard, sum_degreeCharge, ← card_mixedTriples] at h
  exact h

#print axioms mixed_collision_energy_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedCollisionEnergyBound
