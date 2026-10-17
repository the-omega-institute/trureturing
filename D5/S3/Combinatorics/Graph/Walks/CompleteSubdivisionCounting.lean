/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Multiset.Filter]
   utility: none
   digest: Integer histogram identities for every landmark subset of a subdivided complete graph. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting

open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles

variable {n : ℕ}

noncomputable def originalBit (S : Finset (Vertex n)) (u : Fin n) : ℤ :=
  if Sum.inl u ∈ S then 1 else 0

noncomputable def midpointBit (S : Finset (Vertex n)) (e : Midpoint n) : ℤ :=
  if Sum.inr e ∈ S then 1 else 0

noncomputable def originalTotal (S : Finset (Vertex n)) : ℤ :=
  ∑ s ∈ S, match s with | .inl _ => 1 | .inr _ => 0

noncomputable def midpointTotal (S : Finset (Vertex n)) : ℤ :=
  ∑ s ∈ S, match s with | .inl _ => 0 | .inr _ => 1

noncomputable def selectedDegree (S : Finset (Vertex n)) (u : Fin n) : ℤ :=
  ∑ s ∈ S, match s with | .inl _ => 0 | .inr e => if u ∈ e.val then 1 else 0

noncomputable def bin (S : Finset (Vertex n)) (e : Sym2 (Vertex n)) (k : ℕ) : ℤ :=
  ∑ s ∈ S, if edgeDistance s e = k then 1 else 0

theorem bin_eq_count (S : Finset (Vertex n)) (e : Sym2 (Vertex n)) (k : ℕ) :
    bin S e k = ((profile S e).count k : ℤ) := by
  classical
  rw [profile_count]
  simp [bin, Finset.sum_boole]

private theorem sum_original (S : Finset (Vertex n)) (u : Fin n) :
    (∑ s ∈ S, if s = Sum.inl u then (1 : ℤ) else 0) = originalBit S u := by
  classical
  simp [originalBit]

private theorem sum_midpoint (S : Finset (Vertex n)) (e : Midpoint n) :
    (∑ s ∈ S, if s = Sum.inr e then (1 : ℤ) else 0) = midpointBit S e := by
  classical
  simp [midpointBit]

theorem midpointBit_swap (S : Finset (Vertex n)) (u v : Fin n) (h : u ≠ v) :
    midpointBit S (subdivisionVertex u v h) = midpointBit S (subdivisionVertex v u h.symm) := by
  rw [midpoint_swap]

/-- The four equations use integer arithmetic; no nested truncated subtraction occurs. -/
theorem histogram (S : Finset (Vertex n)) (u v : Fin n) (h : u ≠ v) :
    let e := incidence u v h
    let a := originalBit S
    let b := midpointBit S (subdivisionVertex u v h)
    let d := selectedDegree S
    bin S e 0 = a u + b ∧
    bin S e 1 + b = a v + d u ∧
    bin S e 2 + a u + a v + b = originalTotal S + d v ∧
    bin S e 3 + d u + d v = midpointTotal S + b := by
  classical
  dsimp only
  have pointwise (s : Vertex n) :
      let z := subdivisionVertex u v h
      let e := incidence u v h
      let a : Fin n → ℤ := fun w => if s = .inl w then 1 else 0
      let b : ℤ := if s = .inr z then 1 else 0
      let d : Fin n → ℤ := fun w => match s with
        | .inl _ => 0 | .inr f => if w ∈ f.val then 1 else 0
      let A : ℤ := match s with | .inl _ => 1 | .inr _ => 0
      let M : ℤ := match s with | .inl _ => 0 | .inr _ => 1
      (if edgeDistance s e = 0 then (1 : ℤ) else 0) = a u + b ∧
      (if edgeDistance s e = 1 then (1 : ℤ) else 0) + b = a v + d u ∧
      (if edgeDistance s e = 2 then (1 : ℤ) else 0) + a u + a v + b = A + d v ∧
      (if edgeDistance s e = 3 then (1 : ℤ) else 0) + d u + d v = M + b := by
    dsimp only
    cases s with
    | inl w =>
      rw [edgeDistance_original]
      by_cases hu : w = u
      · subst w; simp [h, h.symm]
      · by_cases hv : w = v
        · subst w; simp [h, h.symm]
        · simp [hu, hv]
    | inr f =>
      rw [edgeDistance_midpoint]
      have both : u ∈ f.val → v ∈ f.val → f = subdivisionVertex u v h := by
        intro hu hv
        apply Subtype.ext
        exact (Sym2.mem_and_mem_iff h).mp ⟨hu, hv⟩
      by_cases he : f = subdivisionVertex u v h
      · subst f
        simp [subdivisionVertex, h]
      · by_cases hu : u ∈ f.val <;> by_cases hv : v ∈ f.val <;> simp_all
  have h0 := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun s _ => (pointwise s).1)
  have h1 := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun s _ => (pointwise s).2.1)
  have h2 := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun s _ => (pointwise s).2.2.1)
  have h3 := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun s _ => (pointwise s).2.2.2)
  simp only [Finset.sum_add_distrib, sum_original, sum_midpoint] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem profile_eq_of_histogram (S : Finset (Vertex n))
    (u v x y : Fin n) (h : u ≠ v) (k : x ≠ y)
    (hbin : ∀ i : Fin 4, bin S (incidence u v h) i.val = bin S (incidence x y k) i.val) :
    profile S (incidence u v h) = profile S (incidence x y k) := by
  apply (profile_eq_iff_four_counts S S _ _ (incidence_mem u v h) (incidence_mem x y k)).mpr
  intro i
  have hi := hbin i
  simp only [bin_eq_count] at hi
  exact_mod_cast hi

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting
