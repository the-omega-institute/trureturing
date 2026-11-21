/- GID: D5/S3/Geometry/KozakiKakeiFour
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed quadratic evaluation distinguishes the four cycle edges from the two diagonals. -/
import D5.S3.Geometry.KozakiKakeiSupport

namespace D5.S3.Geometry.KozakiKakei
open MvPolynomial
noncomputable section

local instance {m : ℕ} (hm : 2 ≤ m) (i j : Col m) : Decidable (Adjacent hm i j) :=
  inferInstanceAs (Decidable (j = step hm i ∨ i = step hm j))

private theorem eval_four (t : Col 2 → ℂ) :
    eval t (F 2) = (t 3 - t 0)*(t 2 - t 1) - (t 1 - t 0)*(t 3 - t 2) := by
  rw [F, map_sub, eval_matchingPolynomial, eval_matchingPolynomial,
    Fin.prod_univ_two, Fin.prod_univ_two]
  rfl

private def pairNumber (i j : Col 2) (v : Col 2) : ℂ :=
  if v = i ∨ v = j then 1 else 0

theorem signed_four_evaluation (i j : Col 2) (h : i ≠ j) :
    eval (pairNumber i j) (F 2) =
      if Adjacent (by decide : 2 ≤ 2) i j then 1 else -2 := by
  classical
  rw [eval_four]
  fin_cases i <;> fin_cases j <;>
    simp_all [pairNumber, Adjacent, step, second, Fin.ext_iff, Fin.add_def] <;> norm_num

private theorem one_of_neighbors :
    ∀ a b c : Col 2, a ≠ b → a ≠ c → b ≠ c →
      Adjacent (by decide : 2 ≤ 2) a b ∨ Adjacent (by decide : 2 ≤ 2) a c := by
  decide

theorem dihedral_of_scalar_four (σ : Equiv.Perm (Col 2))
    {c : ℂ} (hs : rename σ (F 2) = MvPolynomial.C c * F 2) : Dihedral σ := by
  have hm : 2 ≤ 2 := le_rfl
  have hpair (i j : Col 2) :
      eval (pairNumber i j) (F 2) = c * eval (pairNumber (σ i) (σ j)) (F 2) := by
    have he := congrArg (eval (pairNumber (σ i) (σ j))) hs
    rw [eval_rename, map_mul, eval_C] at he
    have hfun : pairNumber (σ i) (σ j) ∘ σ = pairNumber i j := by
      funext v
      simp [pairNumber, σ.injective.eq_iff]
    rwa [hfun] at he
  have hcoeff (i j : Col 2) (hn : i ≠ j) :
      (if Adjacent hm i j then (1 : ℂ) else -2) =
        c * (if Adjacent hm (σ i) (σ j) then 1 else -2) := by
    simpa only [signed_four_evaluation i j hn, signed_four_evaluation (σ i) (σ j) (σ.injective.ne hn)]
      using hpair i j
  have h₁ : Adjacent hm 0 1 := Or.inl rfl
  have h₃ : Adjacent hm 0 3 := Or.inr rfl
  have h1ne : (0 : Col 2) ≠ 1 := by decide
  have h3ne : (0 : Col 2) ≠ 3 := by decide
  have hc : c = 1 := by
    rcases one_of_neighbors (σ 0) (σ 1) (σ 3) (σ.injective.ne h1ne) (σ.injective.ne h3ne)
        (σ.injective.ne (by decide : (1 : Col 2) ≠ 3)) with h | h
    · simpa [h₁, h, eq_comm] using hcoeff 0 1 h1ne
    · simpa [h₃, h, eq_comm] using hcoeff 0 3 h3ne
  apply dihedral_of_preserves_adjacency hm σ
  intro i j ha
  by_contra hn
  have h := hcoeff i j (adjacent_ne hm ha)
  norm_num [hc, ha, hn] at h

theorem dihedral_of_preservesLevel {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (σ : Equiv.Perm (Col m)) (hp : PreservesLevel σ) : Dihedral σ := by
  obtain ⟨c, hc, hs⟩ := admissible_constant_matrix_scalar hm hm3 σ hp
  by_cases h2 : m = 2
  · subst m
    exact dihedral_of_scalar_four σ hs
  · exact dihedral_of_scalar_large (by omega) σ hc hs

#print axioms dihedral_of_scalar_four
#print axioms dihedral_of_preservesLevel

end
end D5.S3.Geometry.KozakiKakei
