/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentWidth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentReduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NikolovSegal.SLnUnipotentWidth
open Matrix
universe u
variable {F : Type u} [Field F]

theorem upper_one (n : ℕ) : Upper (1 : SpecialLinearGroup (Fin n) F) := by
  constructor
  · intro i j hij
    simp [ne_of_gt hij]
  · intro i
    simp

theorem lower_one (n : ℕ) : Lower (1 : SpecialLinearGroup (Fin n) F) := by
  constructor
  · intro i j hij
    simp [ne_of_lt hij]
  · intro i
    simp

private theorem trivial_four {n : ℕ} [Subsingleton (Fin n)]
    (g : SpecialLinearGroup (Fin n) F) :
    ∃ a b c d : SpecialLinearGroup (Fin n) F,
      Upper a ∧ Lower b ∧ Upper c ∧ Lower d ∧ a*b*c*d = g := by
  refine ⟨1,1,1,1,upper_one n,lower_one n,upper_one n,lower_one n,?_⟩
  exact Subsingleton.elim _ _

/-- Rank-independent unitriangular factorization over every field, including
the trivial ranks. Last-row radicals are interleaved through the genuine
Levi factors; no new factors accumulate when the rank increases. -/
theorem four_factor (n : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    ∃ a b c d : SpecialLinearGroup (Fin n) F,
      Upper a ∧ Lower b ∧ Upper c ∧ Lower d ∧ a*b*c*d = g := by
  induction n with
  | zero => exact trivial_four g
  | succ r ih =>
    by_cases hr : r = 0
    · subst r
      simpa only [Nat.zero_add] using (trivial_four (n := 1) g)
    · let e : Fin r ⊕ Fin 1 ≃ Fin (r+1) := finSumFinEquiv
      let h := reindexSL e.symm g
      obtain ⟨B,v₀,v₁,v₂,v₃,hred⟩ := rank_reduction (Nat.pos_of_ne_zero hr) h
      obtain ⟨b₀,b₁,b₂,b₃,h₀,h₁,h₂,h₃,hB⟩ := ih B
      let A₀ := upperRad v₀ * embed b₀
      let A₁ := embed b₁ * (embed (b₂*b₃) * lowerRad v₁ * (embed (b₂*b₃))⁻¹)
      let A₂ := embed b₂ * (embed b₃ * upperRad v₂ * (embed b₃)⁻¹)
      let A₃ := embed b₃ * lowerRad v₃
      have hA₀ : Upper (reindexSL e A₀) := by
        dsimp [A₀]
        rw [upperRad_mul_embed]
        exact embed_mul_upper b₀ h₀ _
      have hA₁ : Lower (reindexSL e A₁) := by
        dsimp [A₁]
        rw [embed_conjugate_lowerRad]
        exact embed_mul_lower b₁ h₁ _
      have hA₂ : Upper (reindexSL e A₂) := by
        dsimp [A₂]
        rw [embed_conjugate_upperRad]
        exact embed_mul_upper b₂ h₂ _
      have hA₃ : Lower (reindexSL e A₃) := embed_mul_lower b₃ h₃ _
      have hEB : embed B = embed b₀ * embed b₁ * embed b₂ * embed b₃ := by
        rw [← hB]
        simp only [map_mul]
      have hprod : A₀*A₁*A₂*A₃ = h := by
        rw [hred,hEB]
        dsimp [A₀,A₁,A₂,A₃]
        rw [map_mul]
        group
      refine ⟨reindexSL e A₀,reindexSL e A₁,reindexSL e A₂,reindexSL e A₃,
        hA₀,hA₁,hA₂,hA₃,?_⟩
      calc
        reindexSL e A₀ * reindexSL e A₁ * reindexSL e A₂ * reindexSL e A₃ =
            reindexSL e (A₀*A₁*A₂*A₃) := by simp only [map_mul]
        _ = reindexSL e h := by rw [hprod]
        _ = g := (reindexSL e).apply_symm_apply g

/-- Exact adapter to the prescribed literal upper-unitriangular carrier. -/
theorem upper_iff_literal {n : ℕ} (A : SpecialLinearGroup (Fin n) F) :
    Upper A ↔ ∀ i j : Fin n, j.val < i.val+1 → A.val i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · intro h i j hij
    by_cases heq : i = j
    · subst j
      simpa using h.2 i
    · have hneq : i.val ≠ j.val := fun hh => heq (Fin.ext hh)
      have hlt : j < i := by change j.val < i.val; omega
      simp [h.1 i j hlt,heq]
  · intro h
    constructor
    · intro i j hij
      have hij' : j.val < i.val+1 := by change j.val < i.val at hij; omega
      simpa [Matrix.one_apply,ne_of_gt hij] using h i j hij'
    · intro i
      simpa using h i i (Nat.lt_succ_self i.val)

theorem lower_iff_literal {n : ℕ} (A : SpecialLinearGroup (Fin n) F) :
    Lower A ↔ ∀ i j : Fin n, i.val < j.val+1 → A.val i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · intro h i j hij
    by_cases heq : i = j
    · subst j
      simpa using h.2 i
    · have hneq : i.val ≠ j.val := fun hh => heq (Fin.ext hh)
      have hlt : i < j := by change i.val < j.val; omega
      simp [h.1 i j hlt,heq]
  · intro h
    constructor
    · intro i j hij
      have hij' : i.val < j.val+1 := by change i.val < j.val at hij; omega
      simpa [Matrix.one_apply,ne_of_lt hij] using h i j hij'
    · intro i
      simpa using h i i (Nat.lt_succ_self i.val)

/-- Literal arbitrary-rank, every-field full SLn width at the exact prescribed
alternating length25. Identity padding retains the factor order and parity. -/
theorem alternating_unipotent_25 (n : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    ∃ a : Fin 25 → SpecialLinearGroup (Fin n) F,
      (∀ i, if i.val % 2 = 0 then
        (∀ r c : Fin n, c.val < r.val+1 → (a i).val r c = (1 : Matrix (Fin n) (Fin n) F) r c)
      else
        (∀ r c : Fin n, r.val < c.val+1 → (a i).val r c = (1 : Matrix (Fin n) (Fin n) F) r c)) ∧
      (List.ofFn a).prod = g := by
  obtain ⟨b₀,b₁,b₂,b₃,h₀,h₁,h₂,h₃,hprod⟩ := four_factor n g
  let a : Fin 25 → SpecialLinearGroup (Fin n) F :=
    ![b₀,b₁,b₂,b₃,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  have htri : ∀ i, if i.val % 2 = 0 then Upper (a i) else Lower (a i) := by
    intro i
    fin_cases i
    all_goals norm_num [a]
    all_goals first
      | exact h₀
      | exact h₁
      | exact h₂
      | exact h₃
      | exact upper_one n
      | exact lower_one n
  refine ⟨a,?_,?_⟩
  · intro i
    have hi := htri i
    by_cases he : i.val % 2 = 0
    · simp only [if_pos he] at hi ⊢
      exact (upper_iff_literal (a i)).mp hi
    · simp only [if_neg he] at hi ⊢
      exact (lower_iff_literal (a i)).mp hi
  · simpa [a,List.ofFn_succ,mul_assoc] using hprod

end NikolovSegal.SLnUnipotentWidth
