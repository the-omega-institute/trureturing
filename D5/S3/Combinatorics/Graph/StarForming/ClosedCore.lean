/- GID: D5/S3/Combinatorics/Graph/StarForming/ClosedCore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClosedCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual twenty-vertex closed-high core and its independent omission budget. -/

import D5.S3.Combinatorics.Graph.StarForming.ClosedHighCycle
import D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts
import Mathlib.Algebra.BigOperators.Fin

/-! The graph R and normalization/cell proof of
CLOSED_HIGH_CYCLE_COMPENSATION at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
Full-pair indicators implement the written singleton normalization without
changing the score. Every cell inequality is extracted from an actual
three-vertex path; no bound on an arbitrary input count is assumed. -/

namespace D5.S3.Combinatorics.Graph.StarForming.ClosedCore
open StarFormingDissociationRefutation LongCoreUpper
open scoped BigOperators

private def edges : Finset (Fin 20 × Fin 20) :=
  {(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),
   (0,6),(1,7),(2,8),(3,9),(4,10),(5,11),
   (6,12),(7,13),(8,14),(9,15),(10,16),(11,17),
   (6,18),(7,19),(8,18),(9,19),(10,18),(11,19),(13,14),(15,16)}

def graph : SimpleGraph (Fin 20) where
  Adj a b := (a,b)∈edges ∨ (b,a)∈edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private def reflection : Fin 20 → Fin 20 :=
  ![5,4,3,2,1,0,11,10,9,8,7,6,17,16,15,14,13,12,19,18]
private def iota (f : Bool) (v : Fin 20) : Fin 20 := if f then reflection v else v

private theorem reflected : ∀ f : Bool, ∀ a b : Fin 20,
    graph.Adj (iota f a) (iota f b) ↔ graph.Adj a b := by decide +kernel
private theorem injective : ∀ f : Bool, Function.Injective (iota f) := by decide +kernel

def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ :=
  if iota f v∈S then 1 else 0

private theorem bit_bound (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) :
    bit S f v≤1 := by unfold bit; split_ifs <;> omega

def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ :=
  if iota f a∈S ∧ iota f b∈S then 1 else 0

private theorem full_bounds (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) :
    full S f a b≤1 ∧ full S f a b≤bit S f a ∧ full S f a b≤bit S f b := by
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;> simp [full,bit,ha,hb]

private theorem triple (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S)
    (f : Bool) (a b c : Fin 20) (hab : graph.Adj a b) (hbc : graph.Adj b c) (hne : a≠c) :
    bit S f a+bit S f b+bit S f c≤2 := by
  have hnot : ¬ (iota f a∈S ∧ iota f b∈S ∧ iota f c∈S) := by
    rintro ⟨ha,hb,hc⟩
    have he := (SubQuorum.DoubleStarGrafting.independent_iff graph S).mp hS
      (iota f b) hb (iota f a) ha (iota f c) hc
      (graph.adj_symm ((reflected f a b).mpr hab)) ((reflected f b c).mpr hbc)
    exact hne (injective f he)
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;>
    by_cases hc : iota f c∈S <;> simp_all [bit]

def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell :=
  ![{highLeft := bit S f 0, highRight := bit S f 1, leafLeft := bit S f 6, leafRight := bit S f 7, cut := full S f 12 13},
    {highLeft := bit S f 2, highRight := bit S f 3, leafLeft := bit S f 8, leafRight := bit S f 9, cut := full S f 14 15},
    {highLeft := bit S f 4, highRight := bit S f 5, leafLeft := bit S f 10, leafRight := bit S f 11, cut := full S f 16 17}]

def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ :=
  (if iota f 12∉S ∧ iota f 13∉S then 1 else 0)+
  (if iota f 14∉S ∧ iota f 15∉S then 1 else 0)+
  (if iota f 16∉S ∧ iota f 17∉S then 1 else 0)

private theorem pair_score (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) :
    bit S f a+bit S f b+(if iota f a∉S ∧ iota f b∉S then 1 else 0)=1+full S f a b := by
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;> simp [bit,full,ha,hb]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem score (S : Finset (Fin 20)) (f : Bool) :
    S.card+omitted S f=3+(cell S f 0).weight+(cell S f 1).weight+
      (cell S f 2).weight+bit S f 18+bit S f 19 := by
  have hcard : S.card=∑ v : Fin 20, bit S false v := by simp [bit,iota]
  norm_num only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero] at hcard
  change S.card=bit S false 0+(bit S false 1+(bit S false 2+(bit S false 3+(bit S false 4+(bit S false 5+(bit S false 6+(bit S false 7+(bit S false 8+(bit S false 9+(bit S false 10+(bit S false 11+(bit S false 12+(bit S false 13+(bit S false 14+(bit S false 15+(bit S false 16+(bit S false 17+(bit S false 18+(bit S false 19))))))))))))))))))) at hcard
  have h0 := pair_score S f 12 13
  have h1 := pair_score S f 14 15
  have h2 := pair_score S f 16 17
  have href (v : Fin 20) : bit S true v=bit S false (reflection v) := rfl
  cases f <;>
    simp [cell,Cell.weight,omitted,iota,reflection,href] at h0 h1 h2 ⊢ <;>
    omega

private theorem omitted_reflection (S : Finset (Fin 20)) : omitted S true=omitted S false := by
  simp [omitted,iota,reflection,and_comm] <;> omega

private theorem valid (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) (f : Bool)
    (j : Fin 3) : Valid (cell S f j) (bit S f 18) (bit S f 19) := by
  fin_cases j
  · have hf := full_bounds S f 12 13
    have h0 := triple S hS f 1 0 6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 0 1 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 0 6 12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 1 7 13 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 0 6 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 1 7 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 12 6 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 13 7 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 0,bit_bound S f 1,bit_bound S f 6,bit_bound S f 7,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega
  · have hf := full_bounds S f 14 15
    have h0 := triple S hS f 3 2 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 2 3 9 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 2 8 14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 3 9 15 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 2 8 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 3 9 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 14 8 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 15 9 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 2,bit_bound S f 3,bit_bound S f 8,bit_bound S f 9,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega
  · have hf := full_bounds S f 16 17
    have h0 := triple S hS f 5 4 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 4 5 11 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 4 10 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 5 11 17 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 4 10 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 5 11 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 16 10 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 17 11 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 4,bit_bound S f 5,bit_bound S f 10,bit_bound S f 11,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega

private theorem across (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) (f : Bool)
    (j : Fin 2) : Across (cell S f ⟨j.val,by omega⟩) (cell S f ⟨j.val+1,by omega⟩) := by
  fin_cases j
  · have hf := full_bounds S f 12 13
    have hg := full_bounds S f 14 15
    have h0 := triple S hS f 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 7 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 1 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 7 13 14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Across]
    omega
  · have hf := full_bounds S f 14 15
    have hg := full_bounds S f 16 17
    have h0 := triple S hS f 2 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 9 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 3 4 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 9 15 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Across]
    omega

private theorem oriented_cap (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S)
    (f : Bool) (horder : bit S f 19≤bit S f 18) : S.card+omitted S f≤12 := by
  have h0 := valid S hS f 0
  have h1 := valid S hS f 1
  have h2 := valid S hS f 2
  have ha := across S hS f 0
  have hb := across S hS f 1
  have hu0 := bit_bound S f 18
  have hu1 := bit_bound S f 19
  have hcases : (bit S f 18=0 ∧ bit S f 19=0) ∨
      (bit S f 18=1 ∧ bit S f 19=0) ∨ (bit S f 18=1 ∧ bit S f 19=1) := by omega
  rw [score]
  rcases hcases with ⟨he,ho⟩ | ⟨he,ho⟩ | ⟨he,ho⟩
  · rw [he,ho] at h0 h1 h2 ⊢
    have h := ClosedHighCycle.zero_hub_score _ _ _ h0 h1 h2
    omega
  · rw [he,ho] at h0 h1 h2 ⊢
    have hh := triple S hS f 8 18 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have hhub : (cell S f 1).leafLeft+(cell S f 2).leafLeft+1≤2 := by
      dsimp [cell]
      omega
    exact one_hub_block _ _ _ h0 h1 h2 ha hb hhub
  · rw [he,ho] at h0 h1 h2 ⊢
    have hh := triple S hS f 5 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have hclosed : (cell S f 2).highRight+(cell S f 0).highLeft+(cell S f 0).highRight≤2 := by
      exact hh
    have h := ClosedHighCycle.closed_two_hub_score _ _ _ h0 h1 h2 ha hb hclosed
    omega

/-- Every actual core selection pays for all omitted designated pairs locally.
Both interface vertices are unrestricted, and no neighboring core credit is used. -/
theorem omission_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) :
    S.card+omitted S false≤12 := by
  by_cases h : bit S false 19≤bit S false 18
  · exact oriented_cap S hS false h
  · have he : bit S true 19≤bit S true 18 := by
      simpa [bit,iota,reflection] using (Nat.le_of_lt (Nat.lt_of_not_ge h))
    simpa only [omitted_reflection] using oriented_cap S hS true he

end D5.S3.Combinatorics.Graph.StarForming.ClosedCore
