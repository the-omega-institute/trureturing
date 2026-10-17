/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Every full landmark subset of a once-subdivided complete graph has an edge collision. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionDegreeCollision
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionComplement
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMatrix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution

open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionDegreeCollision
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionComplement
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMatrix

variable {n : ℕ}

private theorem pattern_collision (S : Finset (Vertex n)) (u v x y : Fin n)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x)
    (au : originalBit S u = 0) (av : originalBit S v = 1)
    (ax : originalBit S x = 1) (ay : originalBit S y = 0)
    (bu : midpointBit S (subdivisionVertex u v huv) = 1)
    (bx : midpointBit S (subdivisionVertex x y hxy) = 0)
    (du : selectedDegree S u = selectedDegree S x)
    (dv : selectedDegree S v = selectedDegree S y + 1) : ¬ Resolves S := by
  have H := histogram S u v huv
  have K := histogram S x y hxy
  dsimp only at H K
  have hp : profile S (incidence u v huv) = profile S (incidence x y hxy) := by
    apply profile_eq_of_histogram
    intro k
    fin_cases k <;> dsimp <;> omega
  intro hres
  have he := hres (incidence_mem u v huv) (incidence_mem x y hxy) hp
  exact hux ((incidence_eq_iff u v x y huv hxy).mp he).1

private theorem normalized_not_resolving (S : Finset (Vertex n)) (hn : 3 ≤ n)
    (e : Fin n ≃ Fin n) (ranks : ∀ i, ∑ j, selection S (e i) j = i.val)
    (stairs : ∀ i j, selection S (e i) (e j) =
      if n ≤ i.val + j.val then 1 else 0) : ¬ Resolves S := by
  classical
  have abit (i : Fin n) : originalBit S (e i) =
      if n ≤ i.val + i.val then 1 else 0 := by
    rw [← selection_diagonal, stairs]
    split_ifs <;> norm_num
  have bbit (i j : Fin n) (hij : i ≠ j) :
      midpointBit S (subdivisionVertex (e i) (e j) (e.injective.ne hij)) =
        if n ≤ i.val + j.val then 1 else 0 := by
    rw [← selection_offDiagonal, stairs]
    split_ifs <;> norm_num
  have arank (i : Fin n) : selectedDegree S (e i) + originalBit S (e i) = (i.val : ℤ) := by
    rw [← selection_row]
    exact_mod_cast ranks i
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm2 : 2 ≤ m := by omega
    let u : Fin n := ⟨m - 1, by omega⟩
    let v : Fin n := ⟨m + 1, by omega⟩
    let x : Fin n := ⟨m, by omega⟩
    have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega
    have hxu : x ≠ u := by intro h; have := congrArg Fin.val h; dsimp [x, u] at this; omega
    have au : originalBit S (e u) = 0 := by rw [abit, if_neg]; dsimp [u]; omega
    have av : originalBit S (e v) = 1 := by rw [abit, if_pos]; dsimp [v]; omega
    have ax : originalBit S (e x) = 1 := by rw [abit, if_pos]; dsimp [x]; omega
    have bu : midpointBit S (subdivisionVertex (e u) (e v) (e.injective.ne huv)) = 1 := by
      rw [bbit u v huv, if_pos]; dsimp [u, v]; omega
    have bx : midpointBit S (subdivisionVertex (e x) (e u) (e.injective.ne hxu)) = 0 := by
      rw [bbit x u hxu, if_neg]; dsimp [x, u]; omega
    apply pattern_collision S (e u) (e v) (e x) (e u)
      (e.injective.ne huv) (e.injective.ne hxu) (e.injective.ne (Ne.symm hxu))
      au av ax au bu bx
    · have h₁ : selectedDegree S (e u) = ((m - 1 : ℕ) : ℤ) := by
        simpa only [au, add_zero] using arank u
      have h₂ : selectedDegree S (e x) + 1 = (m : ℤ) := by
        simpa only [ax] using arank x
      omega
    · have h₁ : selectedDegree S (e v) + 1 = ((m + 1 : ℕ) : ℤ) := by
        simpa only [av] using arank v
      have h₂ : selectedDegree S (e u) = ((m - 1 : ℕ) : ℤ) := by
        simpa only [au, add_zero] using arank u
      omega
  · have hm1 : 1 ≤ m := by omega
    let u : Fin n := ⟨m, by omega⟩
    let v : Fin n := ⟨m + 1, by omega⟩
    let y : Fin n := ⟨m - 1, by omega⟩
    have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega
    have hvy : v ≠ y := by intro h; have := congrArg Fin.val h; dsimp [v, y] at this; omega
    have au : originalBit S (e u) = 0 := by rw [abit, if_neg]; dsimp [u]; omega
    have av : originalBit S (e v) = 1 := by rw [abit, if_pos]; dsimp [v]; omega
    have ay : originalBit S (e y) = 0 := by rw [abit, if_neg]; dsimp [y]; omega
    have bu : midpointBit S (subdivisionVertex (e u) (e v) (e.injective.ne huv)) = 1 := by
      rw [bbit u v huv, if_pos]; dsimp [u, v]; omega
    have bx : midpointBit S (subdivisionVertex (e v) (e y) (e.injective.ne hvy)) = 0 := by
      rw [bbit v y hvy, if_neg]; dsimp [v, y]; omega
    apply pattern_collision S (e u) (e v) (e v) (e y)
      (e.injective.ne huv) (e.injective.ne hvy) (e.injective.ne huv)
      au av av ay bu bx
    · have h₁ : selectedDegree S (e u) = (m : ℤ) := by
        simpa only [au, add_zero] using arank u
      have h₂ : selectedDegree S (e v) + 1 = ((m + 1 : ℕ) : ℤ) := by
        simpa only [av] using arank v
      omega
    · have h₁ : selectedDegree S (e v) + 1 = ((m + 1 : ℕ) : ℤ) := by
        simpa only [av] using arank v
      have h₂ : selectedDegree S (e y) = ((m - 1 : ℕ) : ℤ) := by
        simpa only [ay, add_zero] using arank y
      omega

/-- No landmark subset, including subsets containing either vertex class, resolves all edges. -/
theorem no_resolving_set (hn : 3 ≤ n) (S : Finset (Vertex n)) : ¬ Resolves S := by
  classical
  intro hres
  have hi := resolving_rows_injective S hres
  rcases distinct_rows_extreme n (by omega) (selection S) (selection_binary S) hi with hz | hf
  · obtain ⟨e, ranks, stairs⟩ := zero_row_normal_form n (selection S)
      (selection_symm S) (selection_binary S) hi hz
    exact normalized_not_resolving S hn e ranks stairs hres
  · have hresc : Resolves Sᶜ := (resolves_compl_iff S).mpr hres
    have hic := resolving_rows_injective Sᶜ hresc
    have hzc : ∃ u, ∑ j, selection Sᶜ u j = 0 := by
      obtain ⟨u, hu⟩ := hf
      refine ⟨u, ?_⟩
      have hc := selection_row_compl S u
      omega
    obtain ⟨e, ranks, stairs⟩ := zero_row_normal_form n (selection Sᶜ)
      (selection_symm Sᶜ) (selection_binary Sᶜ) hic hzc
    exact normalized_not_resolving Sᶜ hn e ranks stairs hresc

/-- Two distinct actual graph edges have equal multisets of minimum shortest endpoint distances. -/
theorem actual_edge_collision (hn : 3 ≤ n) (S : Finset (Vertex n)) :
    ∃ e ∈ (graph n).edgeSet, ∃ f ∈ (graph n).edgeSet,
      e ≠ f ∧ profile S e = profile S f := by
  have h := no_resolving_set hn S
  unfold Resolves Set.InjOn at h
  push Not at h
  obtain ⟨e, he, f, hf, hp, hne⟩ := h
  exact ⟨e, he, f, hf, hne, hp⟩

/-- Infinity is the absence of every finite resolving cardinality, rather than an empty Nat infimum. -/
noncomputable def edgeMultisetDimension (n : ℕ) : ℕ∞ :=
  ⨅ S : {S : Finset (Vertex n) // Resolves S}, (S.val.card : ℕ∞)

theorem edgeMultisetDimension_eq_top (hn : 3 ≤ n) : edgeMultisetDimension n = ⊤ := by
  classical
  unfold edgeMultisetDimension
  apply iInf_eq_top.mpr
  intro S
  exact (no_resolving_set hn S.val S.property).elim

/-- Source Problem 24, with arbitrary sets and the actual endpoint-distance multisets expanded. -/
theorem result (hn : 3 ≤ n) (S : Set (Vertex n)) :
    (∃ a b c d : Vertex n,
      (graph n).Adj a b ∧ (graph n).Adj c d ∧ s(a,b) ≠ s(c,d) ∧
      S.toFinite.toFinset.val.map (fun z => min ((graph n).dist z a) ((graph n).dist z b)) =
        S.toFinite.toFinset.val.map (fun z => min ((graph n).dist z c) ((graph n).dist z d))) ∧
      edgeMultisetDimension n = ⊤ := by
  classical
  refine ⟨?_, edgeMultisetDimension_eq_top hn⟩
  obtain ⟨e, he, f, hf, hne, hp⟩ := actual_edge_collision hn S.toFinite.toFinset
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      exact ⟨a, b, c, d, (graph n).mem_edgeSet.mp he, (graph n).mem_edgeSet.mp hf, hne, hp⟩

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution
