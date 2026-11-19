/- GID: D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.claim; result=D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.result; claim=D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.claim
   digest: The six-vertex double star has beta two and SF two equal to four but sub-quorum maximum five. -/

import D5.S3.Combinatorics.Graph.SubQuorum.ColoringBounds
import D5.S3.Combinatorics.Graph.StarForming.Semantics
import D5.S3.Combinatorics.Graph.StarForming.CertificateBound

/-!
Exact parameters of the six-vertex double star from the complete saved note,
subquorum-colorings revision 2e430b6481d4959f05f6d805871117261257e39d.
The finite source witnesses are retained. The upper coloring argument is now
consumed through the general graph/support theorem in ColoringBounds, in the
same canonical semantic integration as arbitrary-interface star formation.
-/

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.StarForming.DoubleStarSeparation

open D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
open D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting

private def edges : Finset (Fin 6 × Fin 6) :=
  {(0,1),(0,2),(0,3),(1,4),(1,5)}

/-- Centers 0,1 are adjacent; 2,3 attach to 0 and 4,5 attach to 1. -/
def doubleStar : SimpleGraph (Fin 6) where
  Adj i j := (i,j) ∈ edges ∨ (j,i) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i h; fin_cases i <;> simp [edges] at h⟩

instance : DecidableRel doubleStar.Adj :=
  inferInstanceAs (DecidableRel (fun i j => (i,j) ∈ edges ∨ (j,i) ∈ edges))

private theorem univ_six : (Finset.univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by
  decide +kernel

/-- The four leaves attain the largest dissociation set. -/
theorem beta_doubleStar : beta doubleStar 2 = 4 := by
  unfold beta
  rw [univ_six]
  decide +kernel

private def leaves : Finset (Fin 6) := {2,3,4,5}

private theorem leaves_minimal : IsMinimalStarForming doubleStar 2 leaves := by
  have hlocal : LocalTwo doubleStar leaves := by
    intro v
    fin_cases v <;> decide +kernel
  have hproper : ∀ T ∈ leaves.powerset, T ≠ leaves → ¬ LocalTwo doubleStar T := by
    simp only [leaves, ← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  refine ⟨(starForming_two_iff doubleStar leaves).mpr hlocal,?_⟩
  intro T hT hstar
  exact hproper T (Finset.mem_powerset.mpr hT.subset) hT.ne
    ((starForming_two_iff doubleStar T).mp hstar)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every inclusion-minimal two-star-forming set has at most four vertices. -/
theorem sf_doubleStar : SF doubleStar 2 = 4 := by
  have hfinite : ∀ S ∈ ({0,1,2,3,4,5} : Finset (Fin 6)).powerset,
      (LocalTwo doubleStar S ∧ ∀ T ∈ S.powerset,
        T ≠ S → ¬ LocalTwo doubleStar T) → S.card ≤ 4 := by
    decide +kernel
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    have hm := (Finset.mem_filter.mp hS).2
    apply hfinite S (by rw [← univ_six]; exact Finset.mem_powerset.mpr (Finset.subset_univ S))
    refine ⟨(starForming_two_iff doubleStar S).mp hm.1,?_⟩
    intro T hT hne hlocal
    apply hm.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hT,hne⟩)
    exact (starForming_two_iff doubleStar T).mpr hlocal
  · have hmem : leaves ∈ Finset.univ.powerset.filter
        (IsMinimalStarForming doubleStar 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),leaves_minimal⟩
    have hcard : leaves.card = 4 := by decide +kernel
    exact hcard ▸ Finset.le_sup (f := Finset.card) hmem

private def fiveColoring (v : Fin 6) : Option ℕ :=
  if v.val < 2 then some 0 else some (v.val - 1)

private theorem fiveColoring_good : IsSubQuorum doubleStar fiveColoring := by
  intro v
  fin_cases v <;>
    norm_num [goodAt,univ_six,doubleStar,edges,fiveColoring,
      Finset.filter_insert,Finset.filter_empty,Finset.filter_singleton]

private theorem fiveColoring_card : (palette fiveColoring Finset.univ).card = 5 := by
  norm_num [palette,coloredSupport,univ_six,fiveColoring,
    Finset.filter_insert,Finset.filter_empty,Finset.filter_singleton]

private theorem coloring_upper (c : Fin 6 → Option ℕ)
    (hc : IsSubQuorum doubleStar c) : (palette c Finset.univ).card ≤ 5 := by
  have hh := SubQuorum.ColoringBounds.palette_lt_card_of_degree doubleStar 0
    (by decide +kernel) c hc
  simpa only [Fintype.card_fin, Nat.lt_succ_iff] using hh

/-- One center color and four separate leaf colors give the exact maximum. -/
theorem psiSq_doubleStar : psiSq doubleStar = 5 := by
  classical
  let P : ℕ → Prop := fun n => ∃ c : Fin 6 → Option ℕ,
    IsSubQuorum doubleStar c ∧ (palette c Finset.univ).card = n
  have h0 : P 0 := ⟨fun _ => none,by simp [IsSubQuorum,goodAt],
    by simp [palette,coloredSupport]⟩
  have hmax : P (psiSq doubleStar) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨c,hc,hcard⟩ := hmax
  apply le_antisymm
  · rw [← hcard]
    exact coloring_upper c hc
  · apply Nat.le_findGreatest (by decide : 5 ≤ Fintype.card (Fin 6))
    exact ⟨fiveColoring,fiveColoring_good,fiveColoring_card⟩

/-- Bipartition: 0,4,5 on one side, 1,2,3 on the other. -/
theorem doubleStar_bipartite : doubleStar.Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if v = 0 ∨ v = 4 ∨ v = 5 then 0 else 1) ?_⟩
  change ∀ i j : Fin 6, doubleStar.Adj i j →
    (if i = 0 ∨ i = 4 ∨ i = 5 then (0 : Fin 2) else 1) ≠
    (if j = 0 ∨ j = 4 ∨ j = 5 then 0 else 1)
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The witness also lies in the triangle-free class. -/
theorem doubleStar_triangleFree : doubleStar.CliqueFree 3 :=
  doubleStar_bipartite.cliqueFree (Nat.lt_succ_self 2)

/-- The complete exact numerical separation from the source note. -/
theorem exact_parameters : beta doubleStar 2 = 4 ∧ SF doubleStar 2 = 4 ∧
    psiSq doubleStar = 5 ∧ SF doubleStar 2 < psiSq doubleStar := by
  rw [beta_doubleStar,sf_doubleStar,psiSq_doubleStar]
  decide

/-- The proposed comparison on both larger graph classes. -/
def claim : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Colorable 2 → psiSq G ≤ SF G 2) ∨
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.CliqueFree 3 → psiSq G ≤ SF G 2)

/-- Neither all bipartite graphs nor all triangle-free graphs satisfy the comparison. -/
theorem result : ¬ claim := by
  rintro (h | h)
  · have hh := h 6 doubleStar doubleStar_bipartite
    exact (Nat.not_le_of_lt exact_parameters.2.2.2) hh
  · have hh := h 6 doubleStar doubleStar_triangleFree
    exact (Nat.not_le_of_lt exact_parameters.2.2.2) hh

end D5.S3.Combinatorics.Graph.StarForming.DoubleStarSeparation
