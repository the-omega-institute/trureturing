/- GID: D5/S3/Combinatorics/Sequenceability/BooleanRowChargeConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/BooleanRowChargeConnectivity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Separated original minimal supports have nonzero designated-coordinate charge sums. -/

import D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
The support argument adapts Section 2 of the native original single-ternary
proof (SHA256 485b60f2f519cb1000e89ed96c65fe88c5667e689cb804c9d9ccf3838bf18740),
as preserved in OriginalTwoChargeExclusion.lean (SHA256
228676b458e43ce51613181e7f39084f1f12e603f0408ee1b2a050c8dd8a4a16).
Only the union cover from the original zero_decomposition is needed.
The arbitrary-group formulation removes the draft's unnecessary incidence and
disjoint-decomposition hypotheses. No literature novelty is asserted.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.BooleanRowChargeConnectivity
open scoped BigOperators
open DisjointMinimalZeroOrdering (MinimalZeroSupport zero_decomposition)
universe u v
variable {α : Type u} {G : Type v} [AddCommGroup G]

/-- All original support vertices are retained, including those omitting q.
Distinct vertices are adjacent when they share an original index other than q. -/
def supportIntersectionGraph (E : Finset (Finset α)) (q : α) : SimpleGraph E where
  Adj B D := B ≠ D ∧ ∃ i : α, i ≠ q ∧ i ∈ B.val ∧ i ∈ D.val
  symm := by
    constructor
    intro B D h
    obtain ⟨hne, i, hiq, hiB, hiD⟩ := h
    exact ⟨hne.symm, i, hiq, hiD, hiB⟩
  loopless := by
    constructor
    intro B h
    exact h.1 rfl

/-- Graph on ALL original support vertices, including Q-free and exception-only
vertices. Distinct supports are adjacent exactly when they share an original
coordinate outside the finite designated set Q. -/
def supportIntersectionGraphOutside (E : Finset (Finset α)) (Q : Finset α) :
    SimpleGraph E where
  Adj B D := B ≠ D ∧ ∃ i : α, i ∉ Q ∧ i ∈ B.val ∧ i ∈ D.val
  symm := by
    constructor
    rintro B D ⟨hne, i, hiQ, hiB, hiD⟩
    exact ⟨hne.symm, i, hiQ, hiD, hiB⟩
  loopless := by
    constructor
    intro B h
    exact h.1 rfl

/-- Consumed by the finite-order component bound: the general graph has exactly
the established singleton graph, with its original vertex IDs and paths. -/
theorem supportIntersectionGraphOutside_singleton
    (E : Finset (Finset α)) (q : α) :
    supportIntersectionGraphOutside E {q} = supportIntersectionGraph E q := by
  classical
  ext B D
  simp only [supportIntersectionGraphOutside, supportIntersectionGraph,
    Finset.mem_singleton]

open scoped Classical in
/-- Let E be exactly ALL proper nonempty original minimal zero supports.
For a nonempty finite family U in pairwise distinct components of the ALL-E
graph, if every selected support meets Q and has a nonempty puncture outside Q,
the sum of its designated-coordinate charges is nonzero.

There is no incidence, finite-group, injectivity, or nonzero-label hypothesis.
Exception-only supports remain graph vertices, but cannot satisfy hport.
Applying this theorem to any nonempty subfamily of U gives the corresponding
nonzero subsum, without assuming any zero-sum-free premise. -/
theorem separated_component_charge_sum_ne_zero
    (f : α → G) (Y : Finset α) (E : Finset (Finset α))
    (hE : ∀ B : Finset α,
      B ∈ E ↔ B ⊆ Y ∧ B ≠ Y ∧ MinimalZeroSupport f B)
    (Q : Finset α) (U : Finset E) (hU : U.Nonempty)
    (hmeet : ∀ B ∈ U, (B.val ∩ Q).Nonempty)
    (hport : ∀ B ∈ U, (B.val \ Q).Nonempty)
    (hsep : ∀ B ∈ U, ∀ D ∈ U, B ≠ D →
      (supportIntersectionGraphOutside E Q).connectedComponentMk B ≠
        (supportIntersectionGraphOutside E Q).connectedComponentMk D) :
    (∑ B ∈ U, ∑ i ∈ B.val ∩ Q, f i) ≠ 0 := by
  classical
  let Γ := supportIntersectionGraphOutside E Q
  have data (B : E) : B.val ⊆ Y ∧ B.val ≠ Y ∧ MinimalZeroSupport f B.val :=
    (hE _).mp B.property
  have shared_component {B D : E} {i : α} (hiQ : i ∉ Q)
      (hiB : i ∈ B.val) (hiD : i ∈ D.val) :
      Γ.connectedComponentMk B = Γ.connectedComponentMk D := by
    by_cases hBD : B = D
    · exact congrArg Γ.connectedComponentMk hBD
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show Γ.Adj B D from ⟨hBD, i, hiQ, hiB, hiD⟩)
  have hdis : Set.PairwiseDisjoint (↑U : Set E) (fun B : E => B.val \ Q) := by
    intro B hB D hD hBD
    apply Finset.disjoint_left.mpr
    intro i hiB hiD
    exact hsep B hB D hD hBD
      (shared_component (Finset.mem_sdiff.mp hiB).2
        (Finset.mem_sdiff.mp hiB).1 (Finset.mem_sdiff.mp hiD).1)
  obtain ⟨a, ha⟩ := hU
  obtain ⟨i, hi⟩ := hport a ha
  obtain ⟨q, hq⟩ := hmeet a ha
  have hqa : q ∈ a.val := (Finset.mem_inter.mp hq).1
  have hqQ : q ∈ Q := (Finset.mem_inter.mp hq).2
  let A : Finset α := U.biUnion (fun B : E => B.val \ Q)
  have hiA : i ∈ A := Finset.mem_biUnion.mpr ⟨a, ha, hi⟩
  have outside {j : α} (hj : j ∈ A) : j ∉ Q := by
    obtain ⟨B, _, hjB⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_sdiff.mp hjB).2
  have hqA : q ∉ A := fun h => outside h hqQ
  have hAY : A ⊆ Y := by
    intro j hj
    obtain ⟨B, _, hjB⟩ := Finset.mem_biUnion.mp hj
    exact (data B).1 (Finset.mem_sdiff.mp hjB).1
  have hsum : (∑ j ∈ A, f j) = -(∑ B ∈ U, ∑ j ∈ B.val ∩ Q, f j) := by
    calc
      (∑ j ∈ A, f j) = ∑ B ∈ U, ∑ j ∈ B.val \ Q, f j :=
        Finset.sum_biUnion hdis
      _ = ∑ B ∈ U, -(∑ j ∈ B.val ∩ Q, f j) := by
        apply Finset.sum_congr rfl
        intro B hB
        apply eq_neg_iff_add_eq_zero.mpr
        calc
          (∑ j ∈ B.val \ Q, f j) + (∑ j ∈ B.val ∩ Q, f j) =
              ∑ j ∈ (B.val \ Q) ∪ (B.val ∩ Q), f j :=
            (Finset.sum_union (Finset.disjoint_sdiff_inter B.val Q)).symm
          _ = ∑ j ∈ B.val, f j := by rw [Finset.sdiff_union_inter]
          _ = 0 := (data B).2.2.2.1
      _ = -(∑ B ∈ U, ∑ j ∈ B.val ∩ Q, f j) :=
        Finset.sum_neg_distrib _
  intro hzero
  have hAz : (∑ j ∈ A, f j) = 0 := by rw [hsum, hzero, neg_zero]
  -- The union projection supplies an original minimal block through the port.
  obtain ⟨P, hP, hcover⟩ :=
    zero_decomposition f A A Finset.Subset.rfl hAz
  obtain ⟨D, hDP, hiD⟩ := Finset.mem_biUnion.mp (hcover ▸ hiA)
  have hDA : D ⊆ A := (hP D hDP).1
  have hDE : D ∈ E := (hE D).mpr ⟨hDA.trans hAY, by
    intro he
    exact hqA (hDA (he.symm ▸ (data a).1 hqa)), (hP D hDP).2⟩
  let d : E := ⟨D, hDE⟩
  have hda : Γ.connectedComponentMk d = Γ.connectedComponentMk a :=
    shared_component (Finset.mem_sdiff.mp hi).2 hiD (Finset.mem_sdiff.mp hi).1
  -- Component separation forces the entire block into its representative.
  have hDa : D ⊆ a.val := by
    intro j hjD
    obtain ⟨B, hB, hjB⟩ := Finset.mem_biUnion.mp (hDA hjD)
    have hdB : Γ.connectedComponentMk d = Γ.connectedComponentMk B :=
      shared_component (Finset.mem_sdiff.mp hjB).2 hjD (Finset.mem_sdiff.mp hjB).1
    have hBa : B = a := by
      by_contra hne
      exact hsep B hB a ha hne (hdB.symm.trans hda)
    exact hBa ▸ (Finset.mem_sdiff.mp hjB).1
  have hDeq : D = a.val :=
    (data a).2.2.2.2 D hDa (hP D hDP).2.1 (hP D hDP).2.2.1
  exact hqA (hDA (hDeq.symm ▸ hqa))

/-- A two-torsion label puts all original proper minimal zero supports containing
q in one component of the graph on ALL original proper minimal zero supports.
Paths may pass through supports omitting q. No incidence bound is required. -/
theorem two_charge_supports_connected
    (f : α → G) (Y : Finset α) (E : Finset (Finset α))
    (hE : ∀ B : Finset α,
      B ∈ E ↔ B ⊆ Y ∧ B ≠ Y ∧ MinimalZeroSupport f B)
    (q : α) (htwo : f q + f q = 0)
    (u t : E) (hqu : q ∈ u.val) (hqt : q ∈ t.val) :
    (supportIntersectionGraph E q).connectedComponentMk u =
      (supportIntersectionGraph E q).connectedComponentMk t := by
  classical
  let Γ := supportIntersectionGraph E q
  by_contra hsep
  obtain ⟨huY, _, hu⟩ := (hE _).mp u.property
  obtain ⟨htY, _, ht⟩ := (hE _).mp t.property
  have hneq : u ≠ t := fun h => hsep (congrArg Γ.connectedComponentMk h)
  have shared_component {B D : E} {i : α} (hiq : i ≠ q)
      (hiB : i ∈ B.val) (hiD : i ∈ D.val) :
      Γ.connectedComponentMk B = Γ.connectedComponentMk D := by
    by_cases hBD : B = D
    · exact congrArg Γ.connectedComponentMk hBD
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show Γ.Adj B D from ⟨hBD, i, hiq, hiB, hiD⟩)
  have apart {i : α} (hiq : i ≠ q) : ¬ (i ∈ u.val ∧ i ∈ t.val) := by
    rintro ⟨hiu, hit⟩
    exact hsep (shared_component hiq hiu hit)
  have port : ∃ i ∈ t.val, i ≠ q := by
    by_contra hn
    have htu : t.val ⊆ u.val := by
      intro i hi
      have he : i = q := by
        by_contra hiq
        exact hn ⟨i, hi, hiq⟩
      simpa [he] using hqu
    have he : t.val = u.val := hu.2.2 _ htu ht.1 ht.2.1
    exact hneq (Subtype.ext he.symm)
  obtain ⟨i, hit, hiq⟩ := port
  let A := (u.val ∪ t.val).erase q
  have hqA : q ∉ A := by simp [A]
  have hiA : i ∈ A := by simp [A, hiq, hit]
  have hAY : A ⊆ Y := by
    intro j hj
    rcases Finset.mem_union.mp (Finset.mem_erase.mp hj).2 with hj | hj
    · exact huY hj
    · exact htY hj
  have hdis : Disjoint (u.val.erase q) (t.val.erase q) := by
    apply Finset.disjoint_left.mpr
    intro j hju hjt
    exact apart (Finset.mem_erase.mp hju).1
      ⟨(Finset.mem_erase.mp hju).2, (Finset.mem_erase.mp hjt).2⟩
  have hsumu : (∑ j ∈ u.val.erase q, f j) = - f q := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [Finset.sum_erase_add _ _ hqu]
    exact hu.2.1
  have hsumt : (∑ j ∈ t.val.erase q, f j) = - f q := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [Finset.sum_erase_add _ _ hqt]
    exact ht.2.1
  have hAz : (∑ j ∈ A, f j) = 0 := by
    calc
      (∑ j ∈ A, f j) =
          (∑ j ∈ u.val.erase q, f j) + ∑ j ∈ t.val.erase q, f j := by
        rw [show A = u.val.erase q ∪ t.val.erase q from
          Finset.erase_union_distrib _ _ _, Finset.sum_union hdis]
      _ = - f q + - f q := by rw [hsumu, hsumt]
      _ = 0 := by rw [← neg_add, htwo, neg_zero]
  -- The union projection of the disjoint finite-deletion decomposition
  -- selects a block at the original port i.
  obtain ⟨Q, hQ, hcover⟩ := zero_decomposition f A A Finset.Subset.rfl hAz
  obtain ⟨B, hBQ, hiB⟩ := Finset.mem_biUnion.mp (hcover ▸ hiA)
  have hBA : B ⊆ A := (hQ B hBQ).1
  have hBE : B ∈ E := (hE B).mpr ⟨hBA.trans hAY, by
    intro he
    exact hqA (hBA (he.symm ▸ huY hqu)), (hQ B hBQ).2⟩
  let w : E := ⟨B, hBE⟩
  have hwt : Γ.connectedComponentMk w = Γ.connectedComponentMk t :=
    shared_component hiq hiB hit
  have hBt : B ⊆ t.val := by
    intro j hjB
    have hjA := hBA hjB
    have hjq : j ≠ q := (Finset.mem_erase.mp hjA).1
    rcases Finset.mem_union.mp (Finset.mem_erase.mp hjA).2 with hju | hjt
    · have hwu : Γ.connectedComponentMk w = Γ.connectedComponentMk u :=
        shared_component hjq hjB hju
      exact (hsep (hwu.symm.trans hwt)).elim
    · exact hjt
  have hBeq : B = t.val := ht.2.2 B hBt (hQ B hBQ).2.1 (hQ B hBQ).2.2.1
  exact hqA (hBA (hBeq.symm ▸ hqt))

end D5.S3.Combinatorics.Sequenceability.BooleanRowChargeConnectivity
