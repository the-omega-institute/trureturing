/- GID: D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim; result=D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result; claim=D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim
   digest: A real dual frame violates the cross-Gramian Welch bound of Conjecture 41. -/

/-
proof_shape: result: bind-only (finite exact rational computation)
escape_witness: none
admission_basis: open-problem-resolution (#12318; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace D5.S3.QuantumBounds.Designs.CrossFrameWelchBoundRefutation

/-- A finite family is a frame exactly when it spans the finite-dimensional
Hilbert space, as stated immediately after Definition 1 of Cross-Frame Potential. -/
def IsFrame {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n)) : Prop :=
  Submodule.span ℝ (Set.range F) = ⊤

/-- Definition 3: the second family is a frame and both reconstruction
equations hold. The first family's frame hypothesis is supplied separately. -/
def IsDualFrame {n k : ℕ} (F G : Fin k → EuclideanSpace ℝ (Fin n)) : Prop :=
  IsFrame G ∧
    (∀ x, ∑ i, ⟪x, G i⟫_ℝ • F i = x) ∧
    (∀ x, ∑ i, ⟪x, F i⟫_ℝ • G i = x)

/-- The maximal off-diagonal magnitude of the cross-Gramian. For `2 ≤ k`
the finite index type is nonempty, so this supremum is a maximum. -/
noncomputable def coherence {n k : ℕ}
    (F G : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ p : {p : Fin k × Fin k // p.1 ≠ p.2}, |⟪F p.val.1, G p.val.2⟫_ℝ|

/-- Conjecture 41, Eq. (21), of Aceska and Kaczanowski's Cross-Frame
Potential, over the real Hilbert space. All arithmetic under the square root
is real arithmetic, including subtraction. -/
def claim : Prop :=
  ∀ (n k : ℕ) (F G : Fin k → EuclideanSpace ℝ (Fin n)),
    n ≤ k → 2 ≤ k → IsFrame F → IsDualFrame F G →
      Real.sqrt (((n : ℝ) * k - (n : ℝ) ^ 2) /
        ((k : ℝ) ^ 2 * ((k : ℝ) - 1))) ≤ coherence F G

/-- The nonzero real frame `((-3,-3),(-3,3),(-1,0))` and its canonical
dual have cross-Gramian coherence `3/19`, below the conjectured `1/3`. -/
theorem result : ¬ claim := by
  classical
  let F : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
    ![WithLp.toLp 2 ![-3, -3], WithLp.toLp 2 ![-3, 3], WithLp.toLp 2 ![-1, 0]]
  let G : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
    ![WithLp.toLp 2 ![-3/19, -1/6], WithLp.toLp 2 ![-3/19, 1/6],
      WithLp.toLp 2 ![-1/19, 0]]
  have hFG : ∀ x, ∑ i, ⟪x, G i⟫_ℝ • F i = x := by
    intro x
    ext j
    fin_cases j <;>
      simp [F, G, Fin.sum_univ_succ, PiLp.inner_apply, PiLp.add_apply,
        PiLp.smul_apply] <;> ring
  have hGF : ∀ x, ∑ i, ⟪x, F i⟫_ℝ • G i = x := by
    intro x
    ext j
    fin_cases j <;>
      simp [F, G, Fin.sum_univ_succ, PiLp.inner_apply, PiLp.add_apply,
        PiLp.smul_apply] <;> ring
  have frameOfReconstruction (A B : Fin 3 → EuclideanSpace ℝ (Fin 2))
      (h : ∀ x, ∑ i, ⟪x, B i⟫_ℝ • A i = x) : IsFrame A := by
    apply top_unique
    intro x _
    rw [← h x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hF : IsFrame F := frameOfReconstruction F G hFG
  have hG : IsFrame G := frameOfReconstruction G F hGF
  have hgram (i j : Fin 3) : ⟪F i, G j⟫_ℝ =
      (![![37/38, -1/38, 3/19], ![-1/38, 37/38, 3/19],
        ![3/19, 3/19, 1/19]] : Fin 3 → Fin 3 → ℝ) i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [F, G, PiLp.inner_apply, Fin.sum_univ_succ]
  let : Nonempty {p : Fin 3 × Fin 3 // p.1 ≠ p.2} := ⟨⟨(0, 1), by decide⟩⟩
  have hentries : ∀ p : {p : Fin 3 × Fin 3 // p.1 ≠ p.2},
      |⟪F p.val.1, G p.val.2⟫_ℝ| ≤ 3/19 := by
    intro ⟨⟨i, j⟩, hij⟩
    rw [hgram]
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | norm_num
  have hcoherence : coherence F G = 3/19 := by
    apply le_antisymm
    · exact ciSup_le hentries
    · have h := le_ciSup (show BddAbove
          (Set.range (fun p : {p : Fin 3 × Fin 3 // p.1 ≠ p.2} =>
            |⟪F p.val.1, G p.val.2⟫_ℝ|)) from
          ⟨3/19, by rintro _ ⟨p, rfl⟩; exact hentries p⟩)
          (⟨(0, 2), by decide⟩ : {p : Fin 3 × Fin 3 // p.1 ≠ p.2})
      have he : |⟪F 0, G 2⟫_ℝ| = 3/19 := by
        rw [hgram]
        norm_num [Matrix.cons_val_two]
      change |⟪F 0, G 2⟫_ℝ| ≤ coherence F G at h
      rwa [he] at h
  have hsqrt : Real.sqrt ((1 : ℝ) / 9) = 1/3 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/9)
    nlinarith [Real.sqrt_nonneg ((1 : ℝ)/9)]
  intro h
  have hbound := h 2 3 F G (by decide) (by decide) hF ⟨hG, hFG, hGF⟩
  have hr : (((2 : ℝ) * 3 - (2 : ℝ)^2) / ((3 : ℝ)^2 * ((3 : ℝ) - 1))) = 1/9 := by
    norm_num
  change Real.sqrt (((2 : ℝ) * 3 - (2 : ℝ)^2) /
    ((3 : ℝ)^2 * ((3 : ℝ) - 1))) ≤ coherence F G at hbound
  rw [hr, hsqrt, hcoherence] at hbound
  norm_num at hbound

#print axioms result

end D5.S3.QuantumBounds.Designs.CrossFrameWelchBoundRefutation
