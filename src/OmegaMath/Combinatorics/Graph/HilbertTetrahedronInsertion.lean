import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.ChordalResidualExtension
import OmegaMath.Combinatorics.Graph.HilbertChildFace
import OmegaMath.Combinatorics.Graph.HilbertResidualEnergy
import OmegaMath.Combinatorics.Graph.HilbertTetrahedronBounds
import OmegaMath.Combinatorics.Graph.HilbertTetrahedronGeometryFaces

compile_only_with_mathlib

/-! Omega original.

# Four-neighbor Hilbert insertion

The tetrahedron invariant controls the new radius through the cycle projection.
The triangle invariant and the energies of each candidate face then close
the two invariants for the next elimination step.
-/

namespace HilbertTetrahedronInsertion

open scoped BigOperators

open SimpleGraph.ChordalResidualExtension HilbertTetrahedronGeometry HilbertTetrahedronBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma face_terms {D : Fin 4 → Fin 4 → ℝ} (hD : ∀ i, D i i = 0)
    (hs : ∀ i j, D i j = D j i) (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    ∃ k : Fin 4, Finset.univ.erase k = {i,j,l} ∧
      faceEnergy D k = D i j + D j l + D i l := by
  classical
  have hc : ({i,j,l} : Finset (Fin 4)).card = 3 := by simp [hij, hil, hjl]
  have hex : (Finset.univ \ {i,j,l} : Finset (Fin 4)).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hc]; decide)
  obtain ⟨k, hk⟩ := hex
  have hk' : k ∉ ({i,j,l} : Finset (Fin 4)) := (Finset.mem_sdiff.mp hk).2
  have hset : Finset.univ.erase k = {i,j,l} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact fun x hx => Finset.mem_erase.mpr ⟨fun h => hk' (h ▸ hx), Finset.mem_univ x⟩
    · simp [hc]
  refine ⟨k, hset, ?_⟩
  unfold faceEnergy
  rw [hset]
  simp only [Finset.sum_insert (by simp [hij, hil] : i ∉ ({j,l} : Finset (Fin 4))),
    Finset.sum_insert (by simp [hjl] : j ∉ ({l} : Finset (Fin 4))), Finset.sum_singleton, hD]
  linarith only [hs j i, hs l i, hs l j]

omit [InnerProductSpace ℝ E] in
private lemma edge_terms (y : Fin 4 → E) :
    edgeEnergy (fun i j => ‖y i - y j‖ ^ 2) =
      HilbertResidualEnergy.energy (HilbertResidualEnergy.gradient y) := by
  simp only [edgeEnergy, HilbertResidualEnergy.energy, Fin.sum_univ_four, Fin.sum_univ_six]
  have h0 : HilbertResidualEnergy.gradient y 0 = y 0 - y 1 := rfl
  have h1 : HilbertResidualEnergy.gradient y 1 = y 0 - y 2 := rfl
  have h2 : HilbertResidualEnergy.gradient y 2 = y 0 - y 3 := rfl
  have h3 : HilbertResidualEnergy.gradient y 3 = y 1 - y 2 := rfl
  have h4 : HilbertResidualEnergy.gradient y 4 = y 1 - y 3 := rfl
  have h5 : HilbertResidualEnergy.gradient y 5 = y 2 - y 3 := rfl
  simp only [h0, h1, h2, h3, h4, h5, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, zero_add]
  rw [norm_sub_rev (y 1) (y 0), norm_sub_rev (y 2) (y 0), norm_sub_rev (y 3) (y 0),
    norm_sub_rev (y 2) (y 1), norm_sub_rev (y 3) (y 1), norm_sub_rev (y 3) (y 2)]
  ring

open HilbertResidualEnergy in
private lemma energy_bound (r : Fin 4 → Fin 4 → E) (y : Fin 4 → E)
    (h : Neighborhood (Fin 4) r y (3/2) (329/50) (621/50)) :
    edgeEnergy (fun i j => ‖y i - y j‖ ^ 2) < 357 / 10 := by
  let v : Fin 6 → E := ![r 0 1, r 0 2, r 0 3, r 1 2, r 1 3, r 2 3]
  let d := gradient y - v
  let c := energy (faces v) / 4
  have hv : energy v - 2 * c ≤ 621 / 50 := by
    have ht := h.tet 0 1 2 3
    have v0 : v 0 = r 0 1 := rfl
    have v1 : v 1 = r 0 2 := rfl
    have v2 : v 2 = r 0 3 := rfl
    have v3 : v 3 = r 1 2 := rfl
    have v4 : v 4 = r 1 3 := rfl
    have v5 : v 5 = r 2 3 := rfl
    have f0 : faces v 0 = holonomy r 0 1 2 := rfl
    have f1 : faces v 1 = holonomy r 0 1 3 := rfl
    have f2 : faces v 2 = holonomy r 0 2 3 := rfl
    have f3 : faces v 3 = holonomy r 1 2 3 := rfl
    simp only [energy, c, Fin.sum_univ_six, Fin.sum_univ_four, v0, v1, v2, v3, v4, v5, f0, f1, f2, f3]
    unfold tetrahedron at ht
    linarith only [ht]
  have hd : energy d ≤ 6 := by
    have hd' (i : Fin 6) : ‖d i‖ ≤ 1 := by
      fin_cases i <;> first
        | exact (norm_sub_rev _ _).trans_le (h.defect 0 1)
        | exact (norm_sub_rev _ _).trans_le (h.defect 0 2)
        | exact (norm_sub_rev _ _).trans_le (h.defect 0 3)
        | exact (norm_sub_rev _ _).trans_le (h.defect 1 2)
        | exact (norm_sub_rev _ _).trans_le (h.defect 1 3)
        | exact (norm_sub_rev _ _).trans_le (h.defect 2 3)
    calc
      _ ≤ ∑ _i : Fin 6, (1 : ℝ)^2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hd' i) 2
      _ = _ := by norm_num
  have hvH : energy (gradientPart v) + c = energy v := hodge_energy v
  have hdH : energy (gradientPart d) + c = energy d := by
    have hh := hodge_energy d
    rwa [show faces d = -faces v from faces_sub_gradient v y, energy_neg] at hh
  have hb := corrected_energy (energy_nonneg (gradientPart v))
    (div_nonneg (energy_nonneg _) (by norm_num) : 0 ≤ c) (energy_nonneg (gradientPart d))
    (show energy (gradientPart v) ≤ 621 / 50 + c by linarith only [hvH, hv])
    (show energy (gradientPart d) ≤ 6 - c by linarith only [hdH, hd])
  rw [edge_terms]
  exact (corrected_gradient_energy v y).trans_lt hb

/-- One insertion improves every new residual below the stated global bound,
and preserves the triangle and tetrahedron invariants. -/
theorem place (r : Fin 4 → Fin 4 → E) (y : Fin 4 → E)
    (h : Neighborhood (Fin 4) r y (3/2) (329/50) (621/50)) :
    ∃ z, Placement r y (Real.sqrt (10275/4576)) (329/50) (621/50) z := by
  classical
  obtain ⟨c⟩ := exists_candidate_data y
  let B : ℝ := 25 / 4
  have hB : 0 < B := by norm_num [B]
  have hdiam (i j : Fin 4) (t : ℝ) (ht : ‖r i j - (y i - y j)‖ ≤ t) :
      ‖y i - y j‖ ≤ 3 / 2 + t := by
    calc
      _ = ‖r i j - (r i j - (y i - y j))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖r i j‖ + ‖r i j - (y i - y j)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (h.edge i j) ht
  have hdiam₂ (i j : Fin 4) : ‖y i - y j‖ ^ 2 ≤ B := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hdiam i j 1 (h.defect i j)) 2
    norm_num [B] at hh ⊢
    exact hh
  have hc (i : Fin 4) : ‖y i - c.c‖ ^ 2 ≤ c.q := by linarith [c.slack_eq i, c.slack_nonneg i]
  have hq : c.q < 10275 / 4576 := by
    apply radius_of_energy (S := edgeEnergy fun i j => ‖y i - y j‖ ^ 2) _ (energy_bound r y h)
    by_cases hl : c.q ≤ 25 / 12
    · exact Or.inl hl
    · have hq₀ : B / 3 < c.q := by dsimp [B]; linarith
      have hh := (c.contact_rows hB.le hdiam₂ hq₀).total_energy
      dsimp [B] at hh
      exact Or.inr (by linarith only [hh])
  have hq' : c.q ≤ 9 / 4 := by linarith
  have hnorm (i : Fin 4) : ‖y i - c.c‖ ≤ Real.sqrt (10275 / 4576) :=
    (Real.le_sqrt (norm_nonneg _) (by norm_num)).2 ((hc i).trans hq.le)
  refine ⟨c.c, ⟨hnorm, ?_, ?_⟩⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [h.skew.diagonal]
      linarith only [hc i, hq']
    let t := ‖r i j - (y i - y j)‖
    have hr := pow_le_pow_left₀ (norm_nonneg _) (h.edge i j) 2
    have bound : 9 / 4 + 2 * c.q - (2 / 3) * t ^ 2 ≤ 329 / 50 := by
      by_cases hq₀ : c.q ≤ 25 / 12
      · nlinarith only [hq₀, sq_nonneg t]
      have hq₀' : B / 3 < c.q := by dsimp [B]; linarith
      let a := Real.sqrt (25 * (3 * c.q - 25 / 4) / (4 * c.q - 25 / 4))
      have hd : 0 < 4 * c.q - 25 / 4 := by linarith
      have hn : 0 ≤ 25 * (3 * c.q - 25 / 4) := by linarith
      have ha₂ : a ^ 2 = 25 * (3 * c.q - 25 / 4) / (4 * c.q - 25 / 4) :=
        Real.sq_sqrt (div_nonneg hn hd.le)
      have ha : 0 ≤ a := Real.sqrt_nonneg _
      have ha' : a ≤ ‖y i - y j‖ := by
        apply (sq_le_sq₀ ha (norm_nonneg _)).mp
        rw [ha₂]
        apply (div_le_iff₀ hd).2
        have hh := (c.contact_rows hB.le hdiam₂ hq₀').individual_edge hq₀' hB i j hij
        dsimp [B] at hh
        linarith only [hh]
      refine child_triangle ha (ha'.trans (hdiam i j t le_rfl)) (Or.inr ?_) ?_
      · rw [ha₂, div_mul_cancel₀ _ hd.ne']
      · rw [ha₂]
        apply (div_le_iff₀ hd).2
        linarith only [hq']
    linarith only [bound, hr, hc i, hc j]
  · intro i j l
    let T := ‖y i - c.c‖ ^ 2 + ‖y j - c.c‖ ^ 2 + ‖y l - c.c‖ ^ 2
    let S := ‖y i - y j‖ ^ 2 + ‖y j - y l‖ ^ 2 + ‖y i - y l‖ ^ 2
    let u := ‖holonomy r i j l‖ ^ 2
    let I := ‖r i j‖ ^ 2 + ‖r i l‖ ^ 2 + ‖y i - c.c‖ ^ 2 +
        ‖r j l‖ ^ 2 + ‖y j - c.c‖ ^ 2 + ‖y l - c.c‖ ^ 2 -
        (u + ‖r i j - (y i - y j)‖ ^ 2 + ‖r i l - (y i - y l)‖ ^ 2 +
          ‖r j l - (y j - y l)‖ ^ 2) / 2
    change I ≤ 621 / 50
    have hquad (a b : Fin 4) := pow_le_pow_left₀ (norm_nonneg _) (h.edge a b) 2
    by_cases hrepeated : i = j ∨ i = l ∨ j = l
    · have hnorm' (a : Fin 4) : ‖y a - c.c‖ ^ 2 ≤ 9 / 4 := (hc a).trans hq'
      have hr (a b : Fin 4) : ‖r a b‖ ^ 2 ≤ 9 / 4 := by norm_num at hquad; exact hquad a b
      have hsum : ‖r i j‖ ^ 2 + ‖r i l‖ ^ 2 + ‖r j l‖ ^ 2 ≤ 9 / 2 := by
        rcases hrepeated with he | he | he
        · rw [he, h.skew.diagonal, norm_zero]; nlinarith only [hr j l]
        · rw [he, h.skew.diagonal, norm_zero]; nlinarith only [hr l j, hr j l]
        · rw [he, h.skew.diagonal, norm_zero]; nlinarith only [hr i l]
      dsimp [I, u]
      linarith only [hsum, hnorm' i, hnorm' j, hnorm' l, sq_nonneg ‖holonomy r i j l‖,
        sq_nonneg ‖r i j - (y i - y j)‖, sq_nonneg ‖r i l - (y i - y l)‖,
        sq_nonneg ‖r j l - (y j - y l)‖]
    have hnormrev : ‖y l - y i‖ = ‖y i - y l‖ := norm_sub_rev _ _
    have hdrev : ‖(-r i l) - (y l - y i)‖ = ‖r i l - (y i - y l)‖ := by
      rw [show (-r i l) - (y l - y i) = -(r i l - (y i - y l)) by abel, norm_neg]
    have he := HilbertChildFace.estimates (r i j) (r j l) (-r i l)
      (y i - y j) (y j - y l) (y l - y i) (by abel) (T := T)
      (M := 329 / 50) (by simpa [triangle, holonomy, sub_eq_add_neg] using h.tri i j l)
    dsimp only at he
    rw [norm_neg, hnormrev, hdrev, ← sub_eq_add_neg] at he
    have heasy : I ≤ 329 / 50 + T := by dsimp [I, T, u, holonomy] at *; linarith only [he.1]
    by_cases hsmall : c.q ≤ B / 4
    · dsimp [T] at heasy
      dsimp [B] at hsmall
      linarith only [heasy, hsmall, hc i, hc j, hc l]
    have hsharp : I ≤ 329 / 100 - u / 6 + Real.sqrt (S * (329 / 50 + u / 3)) + T - S / 2 := by
      dsimp [I, S, T, u, holonomy] at *
      linarith only [he.2]
    have hu : u ≤ 1 := by
      simpa [u] using pow_le_pow_left₀ (norm_nonneg _) (h.hol i j l) 2
    apply upper_face_cutoff (face_energy_allowance (sq_nonneg _) hu heasy hsharp)
    push Not at hrepeated
    obtain ⟨k, hk, hSk⟩ := face_terms (D := fun i j => ‖y i - y j‖ ^ 2)
      (by simp) (fun _ _ => by rw [norm_sub_rev]) i j l hrepeated.1 hrepeated.2.1 hrepeated.2.2
    have htSum (f : Fin 4 → ℝ) : (∑ e ∈ Finset.univ.erase k, f e) = f i + f j + f l := by
      rw [hk]
      simp [hrepeated.1, hrepeated.2.1, hrepeated.2.2, add_assoc]
    by_cases hlow : c.q ≤ B / 3
    · have hT := (c.low_radius_face_geometry hB hdiam₂ (lt_of_not_ge hsmall) hlow k)
      have hL := c.low_radius_face_geometry_div hB hdiam₂ (lt_of_not_ge hsmall) hlow k
      dsimp only at hT hL
      rw [htSum] at hT hL
      change 0 < T ∧ T ≤ B ∧ _ at hT
      rw [hSk] at hL
      change 8 * B - 6 * B ^ 2 / T ≤ S at hL
      have hL' : 50 - (1875 / 8) / T ≤ S := by norm_num [B] at hL ⊢; exact hL
      exact (add_le_add_right (faceAllowance_antitone hL') _).trans
        (low_radius_face_allowance hT.1 hT.2.1)
    · have hhigh := lt_of_not_ge hlow
      have hface := (c.contact_rows hB.le hdiam₂ hhigh).high_face hhigh hB k
      rw [hSk] at hface
      have hq₀ : 25 / 12 ≤ c.q := by dsimp [B] at hhigh; linarith
      have hT : T = 3 * c.q := by
        dsimp [T]
        rw [c.four_contacts hB.le hdiam₂ hhigh i, c.four_contacts hB.le hdiam₂ hhigh j,
          c.four_contacts hB.le hdiam₂ hhigh l]
        ring
      have hbound := c.four_radius_bound hB.le hdiam₂
      rw [hT]
      apply high_radius_face_allowance hq₀ (by dsimp [B] at hbound; linarith)
      dsimp [B] at hface
      dsimp [S]
      linarith only [hface]

end HilbertTetrahedronInsertion
