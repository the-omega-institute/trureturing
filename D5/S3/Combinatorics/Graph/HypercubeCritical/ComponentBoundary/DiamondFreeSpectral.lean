/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: A two-step incidence bound gives eight-vertex spectral rigidity under the edge triangle cap. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic

/-!
# Two-step spectral bound for graphs with edge-disjoint triangles

The local triangle count is expressed as an ordered incidence count.
If an external vertex meets a subset of the neighborhood, every edge
of the induced matching has at least one endpoint outside that subset.
Double counting avoids introducing a finite set of unordered pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.DiamondFreeSpectral

open scoped BigOperators
open Finset Matrix
open PrimeContactCardinalityGap (neighborsIn commonIn mem_neighborsIn mem_commonIn)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every adjacent pair has at most one common neighbor. -/
def EdgeCommonCap : Prop :=
  ∀ a b, G.Adj a b → (commonIn G univ a b).card ≤ 1

private theorem common_eq_neighborsIn (x y : V) :
    commonIn G univ x y = neighborsIn G (G.neighborFinset x) y := by
  ext z
  simp only [mem_commonIn, mem_neighborsIn, mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]

private theorem neighborsIn_subset (S : Finset V) (y : V) :
    neighborsIn G S y ⊆ S :=
  fun _ hz => ((mem_neighborsIn G).mp hz).1

private theorem neighborsIn_mono {S T : Finset V} (h : S ⊆ T) (y : V) :
    neighborsIn G S y ⊆ neighborsIn G T y := by
  intro z hz
  obtain ⟨hzS, hyz⟩ := (mem_neighborsIn G).mp hz
  exact (mem_neighborsIn G).mpr ⟨h hzS, hyz⟩

/-- Symmetric incidence counting between two finite sets. -/
private theorem sum_neighborsIn_swap (S T : Finset V) :
    (∑ y ∈ S, (neighborsIn G T y).card) =
      ∑ z ∈ T, (neighborsIn G S z).card := by
  calc
    _ = ∑ z ∈ T, (S.filter (fun y => G.Adj y z)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := G.Adj) (s := S) (t := T)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      ext y
      simp only [mem_filter, mem_neighborsIn]
      constructor
      · rintro ⟨hy, hyz⟩
        exact ⟨hy, G.adj_symm hyz⟩
      · rintro ⟨hy, hzy⟩
        exact ⟨hy, G.adj_symm hzy⟩

private theorem local_degree_le_one (hcap : EdgeCommonCap G)
    (x : V) {a : V} (ha : a ∈ G.neighborFinset x) :
    (neighborsIn G (G.neighborFinset x) a).card ≤ 1 := by
  rw [← common_eq_neighborsIn G x a]
  exact hcap x a ((G.mem_neighborFinset x a).mp ha)

/-- Common neighbors of an external vertex and a center form an independent
subset of the center's neighborhood. -/
private theorem external_independent (hcap : EdgeCommonCap G)
    {x y a b : V} (hxy : x ≠ y)
    (ha : a ∈ neighborsIn G (G.neighborFinset x) y)
    (hb : b ∈ neighborsIn G (G.neighborFinset x) y) :
    ¬ G.Adj a b := by
  intro hab
  obtain ⟨haN, hya⟩ := (mem_neighborsIn G).mp ha
  obtain ⟨hbN, hyb⟩ := (mem_neighborsIn G).mp hb
  have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp haN
  have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hbN
  have hx : x ∈ commonIn G univ a b :=
    (mem_commonIn G).mpr ⟨mem_univ _, G.adj_symm hxa, G.adj_symm hxb⟩
  have hy : y ∈ commonIn G univ a b :=
    (mem_commonIn G).mpr ⟨mem_univ _, G.adj_symm hya, G.adj_symm hyb⟩
  exact hxy (Finset.card_le_one.mp (hcap a b hab) x hx y hy)

/-- Write `m` for twice the number of triangles at a center and `c`
for the number of common neighbors with another vertex. Then
`m + 2*c ≤ 2*d`, where `d` is the center's degree. -/
theorem local_incidence_add_twice_common_le (hcap : EdgeCommonCap G)
    {x y : V} (hxy : x ≠ y) :
    (∑ a ∈ G.neighborFinset x,
      (neighborsIn G (G.neighborFinset x) a).card) +
        2 * (neighborsIn G (G.neighborFinset x) y).card ≤
      2 * G.degree x := by
  let A := G.neighborFinset x
  let C := neighborsIn G A y
  let D := A \ C
  have hCA : C ⊆ A := neighborsIn_subset G A y
  have hDA : D ⊆ A := Finset.sdiff_subset
  have hcard : D.card + C.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hCA
  have hlocal : ∀ a ∈ A, (neighborsIn G A a).card ≤ 1 :=
    fun _ ha => local_degree_le_one G hcap x ha
  have hsplit := Finset.sum_sdiff
    (f := fun a => (neighborsIn G A a).card) hCA
  have hD : (∑ a ∈ D, (neighborsIn G A a).card) ≤ D.card := by
    calc
      _ ≤ ∑ _a ∈ D, (1 : ℕ) :=
        Finset.sum_le_sum (fun a ha => hlocal a (hDA ha))
      _ = _ := by simp
  have hrestrict : ∀ a ∈ C, neighborsIn G A a = neighborsIn G D a := by
    intro a ha
    apply Finset.Subset.antisymm
    · intro b hb
      obtain ⟨hbA, hab⟩ := (mem_neighborsIn G).mp hb
      exact (mem_neighborsIn G).mpr ⟨Finset.mem_sdiff.mpr
        ⟨hbA, fun hbC => external_independent G hcap hxy ha hbC hab⟩, hab⟩
    · exact neighborsIn_mono G hDA a
  have hC : (∑ a ∈ C, (neighborsIn G A a).card) ≤ D.card := by
    calc
      _ = ∑ a ∈ C, (neighborsIn G D a).card :=
        Finset.sum_congr rfl (fun a ha => congrArg Finset.card (hrestrict a ha))
      _ = ∑ b ∈ D, (neighborsIn G C b).card := sum_neighborsIn_swap G C D
      _ ≤ ∑ b ∈ D, (neighborsIn G A b).card :=
        Finset.sum_le_sum (fun b _ => Finset.card_le_card (neighborsIn_mono G hCA b))
      _ ≤ D.card := hD
  change (∑ a ∈ D, (neighborsIn G A a).card) +
    (∑ a ∈ C, (neighborsIn G A a).card) =
      ∑ a ∈ A, (neighborsIn G A a).card at hsplit
  change (∑ a ∈ A, (neighborsIn G A a).card) + 2 * C.card ≤ 2 * A.card
  omega

/-- Two-step walk count decomposed into the return walks, local triangle
incidences, and incidences with vertices outside the closed neighborhood. -/
private theorem two_step_degree_sum (x : V) :
    let A := G.neighborFinset x
    let B := (univ.erase x) \ A
    (∑ a ∈ A, G.degree a) =
      A.card + (∑ a ∈ A, (neighborsIn G A a).card) +
        ∑ b ∈ B, (neighborsIn G A b).card := by
  dsimp only
  let A := G.neighborFinset x
  let B := (univ.erase x) \ A
  have hA : A ⊆ univ.erase x := by
    intro a ha
    exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset x a).mp ha)).symm,
      mem_univ _⟩
  have hback : neighborsIn G A x = A := by
    apply Finset.Subset.antisymm (neighborsIn_subset G A x)
    intro a ha
    exact (mem_neighborsIn G).mpr ⟨ha, (G.mem_neighborFinset x a).mp ha⟩
  have hdegree (a : V) : G.degree a = (neighborsIn G univ a).card := by
    unfold SimpleGraph.degree
    exact congrArg Finset.card (G.neighborFinset_eq_filter (v := a))
  have hswap : (∑ a ∈ A, G.degree a) =
      ∑ b ∈ univ, (neighborsIn G A b).card := by
    simp_rw [hdegree]
    exact sum_neighborsIn_swap G A univ
  have hsplit := Finset.sum_sdiff
    (f := fun b => (neighborsIn G A b).card) hA
  have hreturn := Finset.sum_erase_add univ
    (fun b => (neighborsIn G A b).card) (mem_univ x)
  rw [hback] at hreturn
  change (∑ a ∈ A, G.degree a) = A.card +
    (∑ a ∈ A, (neighborsIn G A a).card) +
    ∑ b ∈ B, (neighborsIn G A b).card
  change (∑ b ∈ B, (neighborsIn G A b).card) +
    (∑ a ∈ A, (neighborsIn G A a).card) =
    ∑ b ∈ univ.erase x, (neighborsIn G A b).card at hsplit
  omega

/-- The general two-step incidence bound. Here `m = 2*t` counts
ordered adjacent pairs among the neighbors and `r` counts incidences
from the external vertices. The final inequality is equivalent to
`2*r ≤ b*(2*d-m)`, avoiding truncated subtraction. -/
theorem two_step_incidence_bound (hcap : EdgeCommonCap G) (x : V) :
    let A := G.neighborFinset x
    let B := (univ.erase x) \ A
    let d := A.card
    let b := B.card
    let m := ∑ a ∈ A, (neighborsIn G A a).card
    let r := ∑ y ∈ B, (neighborsIn G A y).card
    d + b + 1 = Fintype.card V ∧
      m ≤ d ∧
      (∑ a ∈ A, G.degree a) = d + m + r ∧
      2 * r + b * m ≤ b * (2 * d) := by
  dsimp only
  let A := G.neighborFinset x
  let B := (univ.erase x) \ A
  let m := ∑ a ∈ A, (neighborsIn G A a).card
  have hA : A ⊆ univ.erase x := by
    intro a ha
    exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset x a).mp ha)).symm,
      mem_univ _⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hA
  rw [Finset.card_erase_of_mem (mem_univ x), Finset.card_univ] at hcard
  change B.card + A.card = Fintype.card V - 1 at hcard
  have hpos : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr ⟨x⟩
  have hm : m ≤ A.card := by
    calc
      _ ≤ ∑ _a ∈ A, (1 : ℕ) :=
        Finset.sum_le_sum (fun a ha => local_degree_le_one G hcap x ha)
      _ = _ := by simp
  have hbound : ∀ y ∈ B, 2 * (neighborsIn G A y).card + m ≤ 2 * A.card := by
    intro y hy
    have hyx := (mem_erase.mp (mem_sdiff.mp hy).1).1
    have h := local_incidence_add_twice_common_le G hcap hyx.symm
    change m + 2 * (neighborsIn G A y).card ≤ 2 * A.card at h
    omega
  change A.card + B.card + 1 = Fintype.card V ∧
    m ≤ A.card ∧
    (∑ a ∈ A, G.degree a) = A.card + m +
      (∑ y ∈ B, (neighborsIn G A y).card) ∧
    2 * (∑ y ∈ B, (neighborsIn G A y).card) + B.card * m ≤
      B.card * (2 * A.card)
  refine ⟨by omega, hm, two_step_degree_sum G x, ?_⟩
  calc
    _ = ∑ y ∈ B, (2 * (neighborsIn G A y).card + m) := by
      have hconst : (∑ _y ∈ B, m) = B.card * m :=
        Finset.sum_const_nat (fun _ _ => rfl)
      rw [Finset.sum_add_distrib, Finset.mul_sum, hconst]
    _ ≤ ∑ _y ∈ B, 2 * A.card := Finset.sum_le_sum hbound
    _ = _ := Finset.sum_const_nat (fun _ _ => rfl)

/-- The squared eigenvalue is bounded above by the two-step row sum
at a maximum coordinate of a positive eigenvector. -/
theorem eigenvalue_sq_le_two_step_degree_at_max (u : V → ℝ) (lam : ℝ)
    (heigen : ∀ y, (∑ z ∈ G.neighborFinset y, u z) = lam * u y)
    (x : V) (hxpos : 0 < u x) (hmax : ∀ y, u y ≤ u x) :
    lam ^ 2 ≤ ∑ a ∈ G.neighborFinset x, (G.degree a : ℝ) := by
  have hrow (a : V) :
      (∑ z ∈ G.neighborFinset a, u z) ≤ (G.degree a : ℝ) * u x := by
    calc
      _ ≤ ∑ _z ∈ G.neighborFinset a, u x :=
        Finset.sum_le_sum (fun z _ => hmax z)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  have hmul : lam ^ 2 * u x ≤
      (∑ a ∈ G.neighborFinset x, (G.degree a : ℝ)) * u x := by
    calc
      _ = lam * (lam * u x) := by ring
      _ = lam * ∑ a ∈ G.neighborFinset x, u a := by rw [heigen x]
      _ = ∑ a ∈ G.neighborFinset x, lam * u a := by rw [Finset.mul_sum]
      _ = ∑ a ∈ G.neighborFinset x, ∑ z ∈ G.neighborFinset a, u z := by
        exact Finset.sum_congr rfl (fun a _ => (heigen a).symm)
      _ ≤ ∑ a ∈ G.neighborFinset x, (G.degree a : ℝ) * u x :=
        Finset.sum_le_sum (fun a _ => hrow a)
      _ = _ := by rw [Finset.sum_mul]
  exact le_of_mul_le_mul_right hmul hxpos

private theorem small_incidence_rigidity (d b m r : ℕ)
    (hsize : d + b ≤ 7) (hm : m ≤ d) (hlower : 16 ≤ d + m + r)
    (hupper : 2 * r + b * m ≤ b * (2 * d)) :
    d = 4 ∧ b = 3 ∧ m = 0 ∧ r = 12 := by
  have hd : d ≤ 7 := by omega
  have hb : b ≤ 7 := by omega
  interval_cases d <;> interval_cases b <;> norm_num at * <;> omega

/-- A graph of at most eight vertices satisfying the edge cap and having
at least sixteen two-step walks from some vertex is exactly complete
bipartite with two parts of size four. -/
theorem card_eight_and_complete_bipartite_of_two_step
    (hcap : EdgeCommonCap G) (x : V) (hn : Fintype.card V ≤ 8)
    (hrow : 16 ≤ ∑ a ∈ G.neighborFinset x, G.degree a) :
    Fintype.card V = 8 ∧
      ∃ A : Finset V, A.card = 4 ∧ (Aᶜ).card = 4 ∧
        ∀ a b, G.Adj a b ↔ (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A) := by
  let A := G.neighborFinset x
  let B := (univ.erase x) \ A
  let m := ∑ a ∈ A, (neighborsIn G A a).card
  let r := ∑ b ∈ B, (neighborsIn G A b).card
  have hbounds := two_step_incidence_bound G hcap x
  change A.card + B.card + 1 = Fintype.card V ∧
    m ≤ A.card ∧ (∑ a ∈ A, G.degree a) = A.card + m + r ∧
    2 * r + B.card * m ≤ B.card * (2 * A.card) at hbounds
  obtain ⟨hsize, hm, hsum, hupper⟩ := hbounds
  change 16 ≤ ∑ a ∈ A, G.degree a at hrow
  obtain ⟨hd, hb, hmzero, hr⟩ :=
    small_incidence_rigidity A.card B.card m r (by omega) hm
      (by omega) hupper
  have hn8 : Fintype.card V = 8 := by omega
  have hAind : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b := by
    intro a ha b hb hab
    have hle : (neighborsIn G A a).card ≤ m := by
      change (neighborsIn G A a).card ≤ ∑ z ∈ A, (neighborsIn G A z).card
      exact Finset.single_le_sum (f := fun z => (neighborsIn G A z).card)
        (fun _ _ => Nat.zero_le _) ha
    have hpos : 0 < (neighborsIn G A a).card :=
      Finset.card_pos.mpr ⟨b, (mem_neighborsIn G).mpr ⟨hb, hab⟩⟩
    omega
  have htermle (b : V) : (neighborsIn G A b).card ≤ A.card :=
    Finset.card_le_card (neighborsIn_subset G A b)
  have hequal : (∑ b ∈ B, (neighborsIn G A b).card) =
      ∑ _b ∈ B, A.card := by
    calc
      _ = 12 := hr
      _ = B.card * A.card := by rw [hb, hd]
      _ = _ := (Finset.sum_const_nat (fun _ _ => rfl)).symm
  have hBfull : ∀ b ∈ B, neighborsIn G A b = A := by
    intro b hB
    have hcard := (Finset.sum_eq_sum_iff_of_le (fun y _ => htermle y)).mp hequal b hB
    exact Finset.eq_of_subset_of_card_le (neighborsIn_subset G A b) hcard.ge
  have hcross : ∀ a ∈ A, ∀ b, b ∉ A → G.Adj a b := by
    intro a ha b hnot
    by_cases hbx : b = x
    · subst b
      exact G.adj_symm ((G.mem_neighborFinset x a).mp ha)
    · have hbB : b ∈ B := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hbx, mem_univ _⟩, hnot⟩
      have hmem : a ∈ neighborsIn G A b := (hBfull b hbB).symm ▸ ha
      exact G.adj_symm ((mem_neighborsIn G).mp hmem).2
  have hCind : ∀ a b, a ∉ A → b ∉ A → ¬ G.Adj a b := by
    intro a b ha hb hab
    have hsub : A ⊆ commonIn G univ a b := by
      intro z hz
      exact (mem_commonIn G).mpr ⟨mem_univ _, G.adj_symm (hcross z hz a ha),
        G.adj_symm (hcross z hz b hb)⟩
    have hle := (Finset.card_le_card hsub).trans (hcap a b hab)
    omega
  have hc : (Aᶜ).card = 4 := by
    have hc' := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    rw [Finset.card_univ, hn8, hd] at hc'
    rw [Finset.compl_eq_univ_sdiff]
    omega
  refine ⟨hn8, A, hd, hc, ?_⟩
  intro a b
  constructor
  · intro hab
    by_cases ha : a ∈ A
    · exact Or.inl ⟨ha, fun hb => hAind a ha b hb hab⟩
    · exact Or.inr ⟨ha, by
        by_contra hb
        exact hCind a b ha hb hab⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact hcross a ha b hb
    · exact G.adj_symm (hcross b hb a ha)

/-- A finite graph with edge-disjoint triangles and a positive adjacency
eigenvector of eigenvalue four has at least eight vertices. Equality
gives an exact complete bipartite partition of type K4,4. -/
theorem card_ge_eight_and_rigidity [Nonempty V] (hcap : EdgeCommonCap G)
    (u : V → ℝ) (hpos : ∀ x, 0 < u x)
    (heigen : ∀ x, (G.adjMatrix ℝ *ᵥ u) x = 4 * u x) :
    8 ≤ Fintype.card V ∧
      (Fintype.card V = 8 →
        ∃ A : Finset V, A.card = 4 ∧ (Aᶜ).card = 4 ∧
          ∀ a b, G.Adj a b ↔ (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) := by
  obtain ⟨x, _, hmax⟩ := Finset.exists_max_image (univ : Finset V) u
    Finset.univ_nonempty
  have hsum (y : V) : (∑ z ∈ G.neighborFinset y, u z) = 4 * u y := by
    rw [← G.adjMatrix_mulVec_apply y u]
    exact heigen y
  have hreal := eigenvalue_sq_le_two_step_degree_at_max G u 4 hsum x
    (hpos x) (fun y => hmax y (mem_univ y))
  have hcast : (16 : ℝ) ≤ ((∑ a ∈ G.neighborFinset x, G.degree a : ℕ) : ℝ) := by
    push_cast
    norm_num at hreal
    exact hreal
  have hrow : 16 ≤ ∑ a ∈ G.neighborFinset x, G.degree a := by
    exact_mod_cast hcast
  refine ⟨?_, ?_⟩
  · by_contra h
    have hn : Fintype.card V ≤ 8 := by omega
    have h8 := (card_eight_and_complete_bipartite_of_two_step G hcap x hn hrow).1
    omega
  · intro hn
    exact (card_eight_and_complete_bipartite_of_two_step G hcap x hn.le hrow).2

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.DiamondFreeSpectral
