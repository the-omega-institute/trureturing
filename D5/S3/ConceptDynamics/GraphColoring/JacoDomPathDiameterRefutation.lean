/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Diam, mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.claim
   digest: Kok Conjecture 2.9 is false at n = 33: every dom-path is longer than diam + 1. -/

import D5.S0.Certificates.JacoExponentialDominationRefutation
import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation

open D5.S0.Certificates.JacoExponentialDominationRefutation

/-
proof_shape:
  result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #8569)
Direct frozen dependencies: D5/S0/Certificates/JacoExponentialDominationRefutation
(jacoRight, Adj); D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination
(IsDominating, IsNDominatingSet, dominationNumber,
dominationNumber_le_of_isDominating, exists_isNDominatingSet_dominationNumber).
-/

/-- The vertices `v_1, ..., v_n` of `J_n(x)`, indexed as in the paper. -/
abbrev Vertex (n : ℕ) := ↑(Finset.Icc 1 n)

/--
`J_n(x)`: the induced subgraph of Kok's `J_∞(x)` on `v_1, ..., v_n`, using the
frozen adjacency relation.
-/
def jaco (n : ℕ) : SimpleGraph (Vertex n) where
  Adj a b := Adj a.1 b.1
  symm := ⟨by
    intro a b hab
    rcases hab with hab | hab
    · exact Or.inr hab
    · exact Or.inl hab⟩
  loopless := ⟨by
    intro a haa
    rcases haa with haa | haa <;> omega⟩

private instance (n : ℕ) : DecidableRel (jaco n).Adj := by
  intro a b
  simp only [jaco, Adj]
  infer_instance

/-- The positions on a walk occupied by a vertex set `D`. -/
def positions {n : ℕ} {u v : Vertex n} (w : (jaco n).Walk u v)
    (D : Finset (Vertex n)) : Finset (Fin (w.length + 1)) :=
  Finset.univ.filter fun i => w.getVert i ∈ D

/--
A dom-path of `J_n(x)`: a `(v_1, v_n)` path and one shared vertex set that is
a minimum dominating set of both the path graph and `J_n(x)`.
-/
def IsDomPath (n : ℕ) (h : 1 ≤ n)
    (w : (jaco n).Walk ⟨1, by simp [h]⟩ ⟨n, by simp [h]⟩) : Prop :=
  w.IsPath ∧ ∃ D : Finset (Vertex n), D ⊆ w.support.toFinset ∧
    (SimpleGraph.pathGraph (w.length + 1)).IsNDominatingSet
      (SimpleGraph.pathGraph (w.length + 1)).dominationNumber (positions w D) ∧
    (jaco n).IsNDominatingSet (jaco n).dominationNumber D

/--
Conjecture 2.9 of arXiv:2507.16500v1 in its weakest reading: for every
`n >= 1`, some dom-path of `J_n(x)` has length at most `diam(J_n(x)) + 1`.
-/
def claim : Prop :=
  ∀ n : ℕ, ∀ h : 1 ≤ n,
    ∃ w : (jaco n).Walk ⟨1, by simp [h]⟩ ⟨n, by simp [h]⟩,
      IsDomPath n h w ∧ w.length ≤ (jaco n).diam + 1

private abbrev V33 := Vertex 33

private abbrev v33 (i : ℕ) (h : i ∈ Finset.Icc 1 33) : V33 := ⟨i, h⟩

private def valueRegion (lo hi : ℕ) : Finset V33 :=
  Finset.univ.filter fun v => lo ≤ v.1 ∧ v.1 ≤ hi

private abbrev q1 : V33 := ⟨1, by decide⟩
private abbrev q2 : V33 := ⟨2, by decide⟩
private abbrev q3 : V33 := ⟨3, by decide⟩
private abbrev q4 : V33 := ⟨4, by decide⟩
private abbrev q7 : V33 := ⟨7, by decide⟩
private abbrev q11 : V33 := ⟨11, by decide⟩
private abbrev q12 : V33 := ⟨12, by decide⟩
private abbrev q20 : V33 := ⟨20, by decide⟩
private abbrev q32 : V33 := ⟨32, by decide⟩
private abbrev q33 : V33 := ⟨33, by decide⟩

private def witnessWalk : (jaco 33).Walk q1 q33 :=
  .cons' q1 q2 q33 (by decide +kernel) <|
  .cons' q2 q3 q33 (by decide +kernel) <|
  .cons' q3 q4 q33 (by decide +kernel) <|
  .cons' q4 q7 q33 (by decide +kernel) <|
  .cons' q7 q11 q33 (by decide +kernel) <|
  .cons' q11 q12 q33 (by decide +kernel) <|
  .cons' q12 q20 q33 (by decide +kernel) <|
  .cons' q20 q32 q33 (by decide +kernel) <|
  .cons' q32 q33 q33 (by decide +kernel) .nil

private def witnessD : Finset V33 := {q2, q7, q20, q33}

private abbrev p1 : Fin (witnessWalk.length + 1) := ⟨1, by decide +kernel⟩
private abbrev p4 : Fin (witnessWalk.length + 1) := ⟨4, by decide +kernel⟩
private abbrev p7 : Fin (witnessWalk.length + 1) := ⟨7, by decide +kernel⟩
private abbrev p9 : Fin (witnessWalk.length + 1) := ⟨9, by decide +kernel⟩

private def witnessPositions : Finset (Fin (witnessWalk.length + 1)) :=
  {p1, p4, p7, p9}

/-- Conjecture 2.9 is false at `n = 33`. -/
theorem result : ¬ claim := by
  have four_le_card_of_jaco33_dominating {D : Finset V33}
      (hD : (jaco 33).IsDominating D) :
      4 ≤ D.card := by
    have four_le_card_of_hits
        (D A B C E : Finset V33)
        (hAB : Disjoint A B) (hAC : Disjoint A C) (hAE : Disjoint A E)
        (hBC : Disjoint B C) (hBE : Disjoint B E) (hCE : Disjoint C E)
        (hA : (D ∩ A).Nonempty) (hB : (D ∩ B).Nonempty)
        (hC : (D ∩ C).Nonempty) (hE : (D ∩ E).Nonempty) :
        4 ≤ D.card := by
      rcases hA with ⟨a, ha⟩
      rcases hB with ⟨b, hb⟩
      rcases hC with ⟨c, hc⟩
      rcases hE with ⟨e, he⟩
      simp only [Finset.mem_inter] at ha hb hc he
      obtain ⟨haD, haA⟩ := ha
      obtain ⟨hbD, hbB⟩ := hb
      obtain ⟨hcD, hcC⟩ := hc
      obtain ⟨heD, heE⟩ := he
      have hab : a ≠ b := fun h => Finset.disjoint_left.1 hAB haA (h ▸ hbB)
      have hac : a ≠ c := fun h => Finset.disjoint_left.1 hAC haA (h ▸ hcC)
      have hae : a ≠ e := fun h => Finset.disjoint_left.1 hAE haA (h ▸ heE)
      have hbc : b ≠ c := fun h => Finset.disjoint_left.1 hBC hbB (h ▸ hcC)
      have hbe : b ≠ e := fun h => Finset.disjoint_left.1 hBE hbB (h ▸ heE)
      have hce : c ≠ e := fun h => Finset.disjoint_left.1 hCE hcC (h ▸ heE)
      have hsub : {a, b, c, e} ⊆ D := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨haD, hbD, hcD, heD⟩
      have hcard : ({a, b, c, e} : Finset V33).card = 4 := by
        simp [hab, hac, hae, hbc, hbe, hce]
      rw [← hcard]
      exact Finset.card_le_card hsub
    let A := valueRegion 1 2
    let B := valueRegion 3 7
    let C := valueRegion 8 20
    let E := valueRegion 21 33
    have hit (center : V33) (R : Finset V33)
        (hr : ∀ d : V33, d = center ∨ (jaco 33).Adj center d → d ∈ R) :
        (D ∩ R).Nonempty := by
      rcases hD center with hc | ⟨d, hdD, hadj⟩
      · exact ⟨center, Finset.mem_inter.mpr ⟨hc, hr center (Or.inl rfl)⟩⟩
      · exact ⟨d, Finset.mem_inter.mpr ⟨hdD, hr d (Or.inr hadj)⟩⟩
    have hA : (D ∩ A).Nonempty := hit (v33 1 (by decide)) A (by decide +kernel)
    have hB : (D ∩ B).Nonempty := hit (v33 4 (by decide)) B (by decide +kernel)
    have hC : (D ∩ C).Nonempty := hit (v33 12 (by decide)) C (by decide +kernel)
    have hE : (D ∩ E).Nonempty := hit (v33 33 (by decide)) E (by decide +kernel)
    exact four_le_card_of_hits D A B C E
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA hB hC hE
  have jaco33_diam_le_seven : (jaco 33).diam ≤ 7 := by
    have hpow : ∀ u v : V33, ∃ k : Fin 8,
        0 < (((jaco 33).adjMatrix ℕ) ^ (k : ℕ)) u v := by
      decide +kernel
    have jaco33_ediam_le_seven : (jaco 33).ediam ≤ (7 : ℕ∞) := by
      exact SimpleGraph.ediam_le_of_edist_le fun u v => by
        obtain ⟨k, hk⟩ := hpow u v
        rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk] at hk
        have hnon : Nonempty {p : (jaco 33).Walk u v // p.length = (k : ℕ)} :=
          Fintype.card_pos_iff.mp hk
        obtain ⟨⟨p, hp⟩⟩ := hnon
        have hp7 : p.length ≤ 7 := by omega
        calc
          (jaco 33).edist u v ≤ p.length := p.edist_le
          _ ≤ (7 : ℕ∞) := by exact_mod_cast hp7
    rw [SimpleGraph.diam]
    exact ENat.toNat_le_toNat jaco33_ediam_le_seven (by norm_num)
  have path_dominationNumber_le_three {k : ℕ} (hk : k ≤ 9) :
      (SimpleGraph.pathGraph k).dominationNumber ≤ 3 := by
    have hexists : ∃ D : Finset (Fin k),
        (SimpleGraph.pathGraph k).IsDominating D ∧ D.card ≤ 3 := by
      interval_cases k
      · exact ⟨∅, fun v => Fin.elim0 v, by decide⟩
      · exact ⟨Finset.univ, fun v => Or.inl (Finset.mem_univ v), by decide⟩
      · exact ⟨Finset.univ, fun v => Or.inl (Finset.mem_univ v), by decide⟩
      · exact ⟨Finset.univ, fun v => Or.inl (Finset.mem_univ v), by decide⟩
      · refine ⟨{1, 3}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
      · refine ⟨{1, 4}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
      · refine ⟨{1, 4}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
      · refine ⟨{0, 3, 6}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
      · refine ⟨{1, 4, 7}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
      · refine ⟨{1, 4, 7}, ?_, by decide⟩
        intro v
        fin_cases v <;> simp [SimpleGraph.pathGraph_adj]
    obtain ⟨D, hD, hcard⟩ := hexists
    exact (SimpleGraph.dominationNumber_le_of_isDominating _ D hD).trans hcard
  have positions_card_eq {n : ℕ} {u v : Vertex n}
      {w : (jaco n).Walk u v} (hw : w.IsPath) {D : Finset (Vertex n)}
      (hD : D ⊆ w.support.toFinset) :
      (positions w D).card = D.card := by
    let f : Fin (w.length + 1) → Vertex n := fun i => w.getVert i
    have hf : Function.Injective f := by
      intro i j hij
      apply (hw.pathGraphIsoToSubgraph).injective
      apply Subtype.ext
      change w.support[i] = w.support[j]
      change w.getVert i = w.getVert j at hij
      exact (w.getVert_eq_support_getElem (Nat.le_of_lt_succ i.isLt)).symm.trans
        (hij.trans (w.getVert_eq_support_getElem (Nat.le_of_lt_succ j.isLt)))
    have himage : (positions w D).image f = D := by
      ext x
      constructor
      · simp only [Finset.mem_image, positions, Finset.mem_filter, Finset.mem_univ,
          true_and, f]
        rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hx
        have hs : x ∈ w.support := List.mem_toFinset.mp (hD hx)
        obtain ⟨i, hi, hilength⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hs
        let fi : Fin (w.length + 1) := ⟨i, by omega⟩
        apply Finset.mem_image.mpr
        refine ⟨fi, ?_, ?_⟩
        · simp [positions, fi, hi, hx]
        · simpa [f, fi] using hi
    have hcard := Finset.card_image_of_injective (positions w D) hf
    rw [himage] at hcard
    exact hcard.symm
  intro hclaim
  obtain ⟨w, hwDom, hwLength⟩ := hclaim 33 (by decide)
  rcases hwDom with ⟨hwPath, D, hDsupport, hDPath, hDGraph⟩
  have hDLower : 4 ≤ D.card := four_le_card_of_jaco33_dominating hDGraph.isDominating
  have hwLength' : w.length + 1 ≤ 9 := by
    have := jaco33_diam_le_seven
    omega
  have hPathUpper := path_dominationNumber_le_three hwLength'
  have hDomLower : 4 ≤
      (SimpleGraph.pathGraph (w.length + 1)).dominationNumber := by
    rw [← hDPath.card_eq, positions_card_eq hwPath hDsupport]
    exact hDLower
  omega

/-- Fidelity check: the proposed ten-vertex dom-path exists at `n = 33`. -/
example : IsDomPath 33 (by decide) witnessWalk := by
  have four_le_card_of_hits
      (D A B C E : Finset V33)
      (hAB : Disjoint A B) (hAC : Disjoint A C) (hAE : Disjoint A E)
      (hBC : Disjoint B C) (hBE : Disjoint B E) (hCE : Disjoint C E)
      (hA : (D ∩ A).Nonempty) (hB : (D ∩ B).Nonempty)
      (hC : (D ∩ C).Nonempty) (hE : (D ∩ E).Nonempty) :
      4 ≤ D.card := by
    rcases hA with ⟨a, ha⟩
    rcases hB with ⟨b, hb⟩
    rcases hC with ⟨c, hc⟩
    rcases hE with ⟨e, he⟩
    simp only [Finset.mem_inter] at ha hb hc he
    obtain ⟨haD, haA⟩ := ha
    obtain ⟨hbD, hbB⟩ := hb
    obtain ⟨hcD, hcC⟩ := hc
    obtain ⟨heD, heE⟩ := he
    have hab : a ≠ b := fun h => Finset.disjoint_left.1 hAB haA (h ▸ hbB)
    have hac : a ≠ c := fun h => Finset.disjoint_left.1 hAC haA (h ▸ hcC)
    have hae : a ≠ e := fun h => Finset.disjoint_left.1 hAE haA (h ▸ heE)
    have hbc : b ≠ c := fun h => Finset.disjoint_left.1 hBC hbB (h ▸ hcC)
    have hbe : b ≠ e := fun h => Finset.disjoint_left.1 hBE hbB (h ▸ heE)
    have hce : c ≠ e := fun h => Finset.disjoint_left.1 hCE hcC (h ▸ heE)
    have hsub : {a, b, c, e} ⊆ D := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨haD, hbD, hcD, heD⟩
    have hcard : ({a, b, c, e} : Finset V33).card = 4 := by
      simp [hab, hac, hae, hbc, hbe, hce]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have four_le_card_of_jaco33_dominating {D : Finset V33}
      (hD : (jaco 33).IsDominating D) :
      4 ≤ D.card := by
    let A := valueRegion 1 2
    let B := valueRegion 3 7
    let C := valueRegion 8 20
    let E := valueRegion 21 33
    have hit (center : V33) (R : Finset V33)
        (hr : ∀ d : V33, d = center ∨ (jaco 33).Adj center d → d ∈ R) :
        (D ∩ R).Nonempty := by
      rcases hD center with hc | ⟨d, hdD, hadj⟩
      · exact ⟨center, Finset.mem_inter.mpr ⟨hc, hr center (Or.inl rfl)⟩⟩
      · exact ⟨d, Finset.mem_inter.mpr ⟨hdD, hr d (Or.inr hadj)⟩⟩
    have hA : (D ∩ A).Nonempty := hit (v33 1 (by decide)) A (by decide +kernel)
    have hB : (D ∩ B).Nonempty := hit (v33 4 (by decide)) B (by decide +kernel)
    have hC : (D ∩ C).Nonempty := hit (v33 12 (by decide)) C (by decide +kernel)
    have hE : (D ∩ E).Nonempty := hit (v33 33 (by decide)) E (by decide +kernel)
    exact four_le_card_of_hits D A B C E
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA hB hC hE
  have four_le_card_of_path10_dominating {D : Finset (Fin 10)}
      (hD : (SimpleGraph.pathGraph 10).IsDominating D) :
      4 ≤ D.card := by
    have four_le_card_of_hits_fin10
        (D A B C E : Finset (Fin 10))
        (hAB : Disjoint A B) (hAC : Disjoint A C) (hAE : Disjoint A E)
        (hBC : Disjoint B C) (hBE : Disjoint B E) (hCE : Disjoint C E)
        (hA : (D ∩ A).Nonempty) (hB : (D ∩ B).Nonempty)
        (hC : (D ∩ C).Nonempty) (hE : (D ∩ E).Nonempty) :
        4 ≤ D.card := by
      rcases hA with ⟨a, ha⟩
      rcases hB with ⟨b, hb⟩
      rcases hC with ⟨c, hc⟩
      rcases hE with ⟨e, he⟩
      simp only [Finset.mem_inter] at ha hb hc he
      obtain ⟨haD, haA⟩ := ha
      obtain ⟨hbD, hbB⟩ := hb
      obtain ⟨hcD, hcC⟩ := hc
      obtain ⟨heD, heE⟩ := he
      have hab : a ≠ b := fun h => Finset.disjoint_left.1 hAB haA (h ▸ hbB)
      have hac : a ≠ c := fun h => Finset.disjoint_left.1 hAC haA (h ▸ hcC)
      have hae : a ≠ e := fun h => Finset.disjoint_left.1 hAE haA (h ▸ heE)
      have hbc : b ≠ c := fun h => Finset.disjoint_left.1 hBC hbB (h ▸ hcC)
      have hbe : b ≠ e := fun h => Finset.disjoint_left.1 hBE hbB (h ▸ heE)
      have hce : c ≠ e := fun h => Finset.disjoint_left.1 hCE hcC (h ▸ heE)
      have hsub : {a, b, c, e} ⊆ D := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨haD, hbD, hcD, heD⟩
      have hcard : ({a, b, c, e} : Finset (Fin 10)).card = 4 := by
        simp [hab, hac, hae, hbc, hbe, hce]
      rw [← hcard]
      exact Finset.card_le_card hsub
    let A : Finset (Fin 10) := {0, 1}
    let B : Finset (Fin 10) := {2, 3, 4}
    let C : Finset (Fin 10) := {5, 6, 7}
    let E : Finset (Fin 10) := {8, 9}
    have hit (center : Fin 10) (R : Finset (Fin 10))
        (hr : ∀ d : Fin 10, d = center ∨ (SimpleGraph.pathGraph 10).Adj center d → d ∈ R) :
        (D ∩ R).Nonempty := by
      rcases hD center with hc | ⟨d, hdD, hadj⟩
      · exact ⟨center, Finset.mem_inter.mpr ⟨hc, hr center (Or.inl rfl)⟩⟩
      · exact ⟨d, Finset.mem_inter.mpr ⟨hdD, hr d (Or.inr hadj)⟩⟩
    have hA : (D ∩ A).Nonempty := hit 0 A (by
      intro d hd
      fin_cases d <;> simp [A, SimpleGraph.pathGraph_adj] at hd ⊢)
    have hB : (D ∩ B).Nonempty := hit 3 B (by
      intro d hd
      fin_cases d <;> simp [B, SimpleGraph.pathGraph_adj] at hd ⊢)
    have hC : (D ∩ C).Nonempty := hit 6 C (by
      intro d hd
      fin_cases d <;> simp [C, SimpleGraph.pathGraph_adj] at hd ⊢)
    have hE : (D ∩ E).Nonempty := hit 9 E (by
      intro d hd
      fin_cases d <;> simp [E, SimpleGraph.pathGraph_adj] at hd ⊢)
    exact four_le_card_of_hits_fin10 D A B C E
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA hB hC hE
  have hwPath : witnessWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    change ([q1, q2, q3, q4, q7, q11, q12, q20, q32, q33] : List V33).Nodup
    decide +kernel
  have hLength : witnessWalk.length + 1 = 10 := by decide +kernel
  have hPositions : positions witnessWalk witnessD = witnessPositions := by
    ext i
    fin_cases i <;> decide +kernel
  have hPathDominating :
      (SimpleGraph.pathGraph (witnessWalk.length + 1)).IsDominating witnessPositions := by
    have hp1 : p1 ∈ witnessPositions := by
      unfold witnessPositions
      exact Finset.mem_insert_self _ _
    have hp4 : p4 ∈ witnessPositions := by
      unfold witnessPositions
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hp7 : p7 ∈ witnessPositions := by
      unfold witnessPositions
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hp9 : p9 ∈ witnessPositions := by
      unfold witnessPositions
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    intro v
    fin_cases v
    · exact Or.inr ⟨p1, hp1, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inl rfl⟩
    · exact Or.inl hp1
    · exact Or.inr ⟨p1, hp1, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inr rfl⟩
    · exact Or.inr ⟨p4, hp4, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inl rfl⟩
    · exact Or.inl hp4
    · exact Or.inr ⟨p4, hp4, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inr rfl⟩
    · exact Or.inr ⟨p7, hp7, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inl rfl⟩
    · exact Or.inl hp7
    · exact Or.inr ⟨p7, hp7, by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inr rfl⟩
    · exact Or.inl hp9
  refine ⟨hwPath, witnessD, ?_, ?_, ?_⟩
  · change witnessD ⊆
      ([q1, q2, q3, q4, q7, q11, q12, q20, q32, q33] : List V33).toFinset
    decide +kernel
  · constructor
    · rwa [hPositions]
    · have hDominating :
          (SimpleGraph.pathGraph (witnessWalk.length + 1)).IsDominating
            (positions witnessWalk witnessD) := by
          rwa [hPositions]
      have hUpper := SimpleGraph.dominationNumber_le_of_isDominating
        (SimpleGraph.pathGraph (witnessWalk.length + 1))
        (positions witnessWalk witnessD) hDominating
      obtain ⟨E, hE⟩ :=
        SimpleGraph.exists_isNDominatingSet_dominationNumber (SimpleGraph.pathGraph 10)
      have hLower10 : 4 ≤ (SimpleGraph.pathGraph 10).dominationNumber := by
        rw [← hE.card_eq]
        exact four_le_card_of_path10_dominating hE.isDominating
      have hLower : 4 ≤
          (SimpleGraph.pathGraph (witnessWalk.length + 1)).dominationNumber := by
        rw [hLength]
        exact hLower10
      have hCard : (positions witnessWalk witnessD).card = 4 := by
        rw [hPositions]
        decide +kernel
      omega
  · constructor
    · intro v
      have hall : ∀ x ∈ (Finset.univ : Finset V33),
          x ∈ witnessD ∨ ∃ d ∈ witnessD, (jaco 33).Adj x d := by
        decide +kernel
      exact hall v (Finset.mem_univ v)
    · have hUpper := SimpleGraph.dominationNumber_le_of_isDominating
          (jaco 33) witnessD (by
            intro v
            have hall : ∀ x ∈ (Finset.univ : Finset V33),
                x ∈ witnessD ∨ ∃ d ∈ witnessD, (jaco 33).Adj x d := by
              decide +kernel
            exact hall v (Finset.mem_univ v))
      obtain ⟨E, hE⟩ := SimpleGraph.exists_isNDominatingSet_dominationNumber (jaco 33)
      have hLower : 4 ≤ (jaco 33).dominationNumber := by
        rw [← hE.card_eq]
        exact four_le_card_of_jaco33_dominating hE.isDominating
      have hCard : witnessD.card = 4 := by decide
      omega

/-- Fidelity check: the refuting graph is connected. -/
example : (jaco 33).Connected := by
  have hpow : ∀ u v : V33, ∃ k : Fin 8,
      0 < (((jaco 33).adjMatrix ℕ) ^ (k : ℕ)) u v := by
    decide +kernel
  have jaco33_ediam_le_seven : (jaco 33).ediam ≤ (7 : ℕ∞) := by
    exact SimpleGraph.ediam_le_of_edist_le fun u v => by
      obtain ⟨k, hk⟩ := hpow u v
      rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk] at hk
      have hnon : Nonempty {p : (jaco 33).Walk u v // p.length = (k : ℕ)} :=
        Fintype.card_pos_iff.mp hk
      obtain ⟨⟨p, hp⟩⟩ := hnon
      have hp7 : p.length ≤ 7 := by omega
      calc
        (jaco 33).edist u v ≤ p.length := p.edist_le
        _ ≤ (7 : ℕ∞) := by exact_mod_cast hp7
  let hne : Nonempty V33 := ⟨⟨1, by decide⟩⟩
  apply @SimpleGraph.connected_of_ediam_ne_top V33 (jaco 33) hne
  intro htop
  have hle := jaco33_ediam_le_seven
  rw [htop] at hle
  norm_num at hle

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
