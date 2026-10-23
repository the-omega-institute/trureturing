/- GID: D5/S3/Quantum/LatinSquares/SudoQClueGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/LatinSquares/SudoQClueGeometry
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Clue-fixing isometries force a repeated ray in every SudoQ unit. -/

/-
admission_basis: escape-witness (unique_implies_repeated_ray)
Direct frozen dependencies: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15607
Template gap: enrolled pointwise/guarded/iff/existential templates do not reconstruct
  the dependent completion family and its ray witnesses. DependentFamily still needs
  a source-bound arena, reconstruction, occurrence selection, an equivalence bridge,
  whole-family variation/sensitivity and actual observational dependence.
DTR reading: DTR-Unregistered for nine public theorem targets (Observe); no Reg file is delivered.
proof_shape: blockCell: bind-only; escape_witness: none; consumers: SudoQClueGeometry.IsSudoQ,
  SudoQClueGeometry.isSudoQ_isometry, SudoQClueGeometry.unique_split,
  SudoQClueGeometry.unique_K_no_pair, SudoQClueGeometry.K_eq_line_of_unique,
  SudoQClueGeometry.HasRepeatedRay, SudoQClueGeometry.unique_implies_repeated_ray,
  SudoQMinimumClues.isSudoQ_of_sameRays, SudoQMinimumClues.blockCell_reconstruct,
  SudoQMinimumClues.cellBlock_blockCell, SudoQMinimumClues.blockCell_injective,
  SudoQMinimumClues.sudoq_inner, SudoQMinimumClues.sudoq_of_cells,
  SudoQMinimumClues.sudoq_pullback, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_dichotomy,
  SudoQMinimumClues.canonical_conditions, SudoQMinimumClues.q0_of_d
proof_shape: IsSudoQ: bind-only; escape_witness: none; consumers: SudoQClueGeometry.IsSolution,
  SudoQClueGeometry.isSudoQ_isometry, SudoQClueGeometry.reflection_solution,
  SudoQClueGeometry.isSolution_isometry_of_fixes, SudoQClueGeometry.unique_split,
  SudoQClueGeometry.unique_K_no_pair, SudoQClueGeometry.K_eq_line_of_unique,
  SudoQClueGeometry.unique_implies_repeated_ray, SudoQMinimumClues.isSudoQ_of_sameRays,
  SudoQMinimumClues.sudoq_inner, SudoQMinimumClues.sudoq_pullback,
  SudoQMinimumClues.transpose_sudoq, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.normalize_pattern, SudoQMinimumClues.canonical_equalities,
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.HasSecond,
  SudoQMinimumClues.q0_second, SudoQMinimumClues.pullGrid_sudoq, SudoQMinimumClues.pull_solution,
  SudoQMinimumClues.unpull_solution, SudoQMinimumClues.result
proof_shape: IsSolution: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.UniquelySolvable, SudoQClueGeometry.reflection_solution,
  SudoQClueGeometry.isSolution_isometry_of_fixes, SudoQClueGeometry.unique_split,
  SudoQClueGeometry.unique_K_no_pair, SudoQClueGeometry.K_eq_line_of_unique,
  SudoQClueGeometry.unique_implies_repeated_ray, SudoQMinimumClues.pull_solution,
  SudoQMinimumClues.unpull_solution, SudoQMinimumClues.result
proof_shape: SameRays: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.UniquelySolvable, SudoQClueGeometry.unique_split,
  SudoQClueGeometry.unique_K_no_pair, SudoQClueGeometry.K_eq_line_of_unique,
  SudoQClueGeometry.unique_implies_repeated_ray, SudoQMinimumClues.isSudoQ_of_sameRays,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.HasSecond,
  SudoQMinimumClues.q0_second, SudoQMinimumClues.pull_sameRays, SudoQMinimumClues.result
proof_shape: UniquelySolvable: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.claim, SudoQMinimumClues.result
proof_shape: RayEq: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.reflection_ray_split, SudoQClueGeometry.RayEq.symm,
  SudoQClueGeometry.RayEq.trans, SudoQClueGeometry.rayEq_of_smul,
  SudoQClueGeometry.not_rayEq_of_orthogonal, SudoQClueGeometry.swap_changes_ray,
  SudoQClueGeometry.unique_K_no_pair, SudoQClueGeometry.one_line_exactly_once,
  SudoQClueGeometry.HasRepeatedRay, SudoQClueGeometry.unique_implies_repeated_ray,
  SudoQClueGeometry.RayEq.norm, SudoQClueGeometry.RayEq.inner_left_iff,
  SudoQClueGeometry.RayEq.inner_right_iff, SudoQMinimumClues.orthonormal_of_rayEq,
  SudoQMinimumClues.repeated_pattern, SudoQMinimumClues.IsCanonical,
  SudoQMinimumClues.normalize_pattern, SudoQMinimumClues.canonical_equalities,
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.transpose_canonical,
  SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.q0_second, SudoQMinimumClues.result
proof_shape: isSudoQ_isometry: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.reflection_solution, SudoQClueGeometry.isSolution_isometry_of_fixes
proof_shape: reflection_ray_split: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_split
proof_shape: clueSpan: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.clueSpan_finrank, SudoQClueGeometry.span_proper,
  SudoQClueGeometry.reflection_solution, SudoQClueGeometry.isSolution_isometry_of_fixes,
  SudoQClueGeometry.unique_split, SudoQClueGeometry.unique_K_no_pair,
  SudoQClueGeometry.K_eq_line_of_unique, SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: RayEq.symm: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.one_line_exactly_once, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.canonical_normal_form
proof_shape: RayEq.trans: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.one_line_exactly_once, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.q0_second
proof_shape: rayEq_of_smul: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.orthogonal_line_ray, SudoQMinimumClues.last_ray
proof_shape: not_rayEq_of_orthogonal: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.swap_changes_ray, SudoQClueGeometry.one_line_exactly_once,
  SudoQMinimumClues.repeated_pattern, SudoQMinimumClues.q0_trade_changed
proof_shape: clueSpan_finrank: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.span_proper
proof_shape: clue_mem_span: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.reflection_solution, SudoQClueGeometry.isSolution_isometry_of_fixes
proof_shape: span_proper: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: reflection_solution: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_split
proof_shape: swap_fixes_span: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_K_no_pair
proof_shape: split_unit_has_K: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.one_line_exactly_once, SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: orthogonal_line_ray: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.one_line_exactly_once
proof_shape: isSolution_isometry_of_fixes: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_K_no_pair
proof_shape: swap_changes_ray: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_K_no_pair
proof_shape: unique_split: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.K_eq_line_of_unique, SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: unique_K_no_pair: content; escape_witness: unique_K_no_pair; consumers:
  SudoQClueGeometry.K_eq_line_of_unique
proof_shape: K_eq_line_of_unique: content; escape_witness: unique_K_no_pair; consumers:
  SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: one_line_exactly_once: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_implies_repeated_ray
proof_shape: HasRepeatedRay: bind-only; escape_witness: none; consumers:
  SudoQClueGeometry.unique_implies_repeated_ray, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.normalize_pattern, SudoQMinimumClues.result
proof_shape: unique_implies_repeated_ray: content; escape_witness: unique_K_no_pair; consumers:
  SudoQMinimumClues.result
proof_shape: RayEq.refl: bind-only; escape_witness: none; consumers: SudoQMinimumClues.q0_of_d,
  SudoQMinimumClues.q0_second
proof_shape: RayEq.norm: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.orthonormal_of_rayEq
proof_shape: RayEq.inner_left_iff: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.orthonormal_of_rayEq, SudoQMinimumClues.canonical_equalities,
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d
proof_shape: RayEq.inner_right_iff: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.orthonormal_of_rayEq
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexConjugate InnerProductSpace

namespace D5.S3.Quantum.LatinSquares.SudoQClueGeometry


def blockCell (b : Fin 2 × Fin 2) (k : Fin 2 × Fin 2) : Fin 4 × Fin 4 :=
  (finProdFinEquiv (b.1, k.1), finProdFinEquiv (b.2, k.2))

def IsSudoQ (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) : Prop :=
  (∀ i, Orthonormal ℂ (fun j => G i j)) ∧
  (∀ j, Orthonormal ℂ (fun i => G i j)) ∧
  (∀ b, Orthonormal ℂ (fun k => G (blockCell b k).1 (blockCell b k).2))

def IsSolution (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4) → (EuclideanSpace ℂ (Fin 4)))
    (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) : Prop :=
  IsSudoQ G ∧ ∀ c ∈ C, G c.1 c.2 = v c

def SameRays (G H : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) : Prop :=
  ∀ i j, ∃ z : ℂ, ‖z‖ = 1 ∧ H i j = z • G i j

def UniquelySolvable (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4) → (EuclideanSpace ℂ
    (Fin 4))) : Prop :=
  ∃ G, IsSolution C v G ∧ ∀ H, IsSolution C v H → SameRays G H

def RayEq (x y : (EuclideanSpace ℂ (Fin 4))) : Prop := ∃ z : ℂ, ‖z‖ = 1 ∧ y = z • x

private theorem isSudoQ_isometry (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (T : (EuclideanSpace ℂ (Fin 4)) →ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin 4))) :
    IsSudoQ (fun i j => T (G i j)) := by
  exact ⟨fun i => (hG.1 i).comp_linearIsometry T,
    fun j => (hG.2.1 j).comp_linearIsometry T,
    fun b => (hG.2.2 b).comp_linearIsometry T⟩

private theorem reflection_ray_split (S : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) (x :
    (EuclideanSpace ℂ (Fin 4))) (hx : x ≠ 0)
    (h : RayEq x (S.reflection x)) : x ∈ S ∨ x ∈ Sᗮ := by
  rcases h with ⟨z, hz, he⟩
  have hzz : (z * z) • x = (1 : ℂ) • x := by
    calc
      (z * z) • x = S.reflection (S.reflection x) := by rw [he, map_smul, he, smul_smul]
      _ = (1 : ℂ) • x := by simp
  have hsq : z * z = 1 := (smul_left_injective ℂ hx) hzz
  have hroots : z = 1 ∨ z = -1 := by
    have hprod : (z - 1) * (z + 1) = 0 := by calc
      _ = z * z - 1 := by ring
      _ = 0 := by rw [hsq]; ring
    rcases mul_eq_zero.mp hprod with h1 | h1
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h1
  rcases hroots with rfl | rfl
  · left; apply (Submodule.reflection_eq_self_iff x).mp; simpa using he
  · right
    apply (Submodule.reflection_eq_self_iff (K := Sᗮ) x).mp
    rw [Submodule.reflection_orthogonal_apply, he]
    simp

private def clueSpan (C : Finset (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ
    (Fin 4))) : Submodule ℂ (EuclideanSpace ℂ (Fin 4)) :=
  Submodule.span ℂ ((fun c : (Fin 4 × Fin 4) => G c.1 c.2) '' (C : Set (Fin 4 × Fin 4)))


theorem RayEq.symm {x y : (EuclideanSpace ℂ (Fin 4))} (h : RayEq x y) : RayEq y x := by
  rcases h with ⟨z, hz, rfl⟩
  refine ⟨z⁻¹, by simp [hz], ?_⟩
  have hz0 : z ≠ 0 := by intro e; simp [e] at hz
  simp [smul_smul, hz0]

theorem RayEq.trans {x y z : (EuclideanSpace ℂ (Fin 4))} (h : RayEq x y)
    (k : RayEq y z) : RayEq x z := by
  rcases h with ⟨a, ha, rfl⟩
  rcases k with ⟨b, hb, rfl⟩
  exact ⟨b*a, by simp [ha, hb], by simp [smul_smul]⟩

theorem rayEq_of_smul {x y : (EuclideanSpace ℂ (Fin 4))} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ∃ z : ℂ, y = z • x) : RayEq x y := by
  rcases h with ⟨z, rfl⟩
  refine ⟨z, ?_, rfl⟩
  simpa [norm_smul, hx] using hy

theorem not_rayEq_of_orthogonal {x y : (EuclideanSpace ℂ (Fin 4))} (hx : ‖x‖ = 1)
    (hxy : inner ℂ x y = 0) : ¬ RayEq x y := by
  rintro ⟨z, hz, he⟩
  have hxx : inner ℂ x x = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
  rw [he, inner_smul_right, hxx, mul_one] at hxy
  simp [hxy] at hz

private theorem clueSpan_finrank (C : Finset (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4))) :
    Module.finrank ℂ (clueSpan C G) ≤ C.card := by
  classical
  unfold clueSpan
  rw [← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans (Finset.card_image_le)

private theorem clue_mem_span (C : Finset (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4))) (c : (Fin 4 × Fin 4)) (hc : c ∈ C) :
    G c.1 c.2 ∈ clueSpan C G :=
  Submodule.subset_span ⟨c, hc, rfl⟩

private theorem span_proper (C : Finset (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ
    (Fin 4))) (hC : C.card ≤ 3) :
    clueSpan C G ≠ ⊤ := by
  intro e
  have h := clueSpan_finrank C G
  rw [e] at h
  have : Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) = 4 := by simp
  omega

private theorem reflection_solution (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G) :
    IsSolution C v (fun i j => (clueSpan C G).reflection (G i j)) := by
  refine ⟨isSudoQ_isometry G hG.1 (clueSpan C G).reflection.toLinearIsometry, ?_⟩
  intro c hc
  change (clueSpan C G).reflection (G c.1 c.2) = v c
  rw [Submodule.reflection_mem_subspace_eq_self (clue_mem_span C G c hc)]
  exact hG.2 c hc

private theorem swap_fixes_span (S : Submodule ℂ (EuclideanSpace ℂ (Fin 4)))
    (b : OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)))
    (p q : Fin 4) (hp : b p ∈ Sᗮ) (hq : b q ∈ Sᗮ) (x : (EuclideanSpace ℂ (Fin 4))) (hx : x ∈ S) :
    b.equiv b (Equiv.swap p q) x = x := by
  classical
  rw [b.equiv_apply]
  conv_rhs => rw [← b.sum_repr x]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hip : i = p
  · subst i
    have hz : b.repr x p = 0 := by
      rw [b.repr_apply_apply]
      exact Submodule.inner_left_of_mem_orthogonal hx hp
    simp [hz]
  · by_cases hiq : i = q
    · subst i
      have hz : b.repr x q = 0 := by
        rw [b.repr_apply_apply]
        exact Submodule.inner_left_of_mem_orthogonal hx hq
      simp [hz]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]

private theorem split_unit_has_K (S : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) (hS : S ≠ ⊤)
    (u : Fin 4 → (EuclideanSpace ℂ (Fin 4))) (hu : Orthonormal ℂ u) (hsplit : ∀ i, u i ∈ S
        ∨ u i ∈ Sᗮ) :
    ∃ p, u p ∈ Sᗮ := by
  by_contra h
  have hall : ∀ i, u i ∈ S := by
    intro i
    exact (hsplit i).resolve_right (by aesop)
  apply hS
  apply top_unique
  rw [← hu.linearIndependent.span_eq_top_of_card_eq_finrank (by simp : Fintype.card
      (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)))]
  exact Submodule.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hall i)

private theorem orthogonal_line_ray (K : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) (w :
    (EuclideanSpace ℂ (Fin 4)))
    (hw : ‖w‖ = 1) (he : K = ℂ ∙ w) (x : (EuclideanSpace ℂ (Fin 4))) (hx : x ∈ K) (hn : ‖x‖ = 1) :
    RayEq w x := by
  apply rayEq_of_smul hw hn
  rw [he, Submodule.mem_span_singleton] at hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, hz.symm⟩


private theorem isSolution_isometry_of_fixes (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G) (T : (EuclideanSpace ℂ (Fin 4)) ≃ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin 4)))
    (hfix : ∀ x ∈ clueSpan C G, T x = x) :
    IsSolution C v (fun i j => T (G i j)) := by
  refine ⟨isSudoQ_isometry G hG.1 T.toLinearIsometry, ?_⟩
  intro c hc
  change T (G c.1 c.2) = v c
  rw [hfix _ (clue_mem_span C G c hc)]
  exact hG.2 c hc

private theorem swap_changes_ray (b : OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)))
    (p q : Fin 4)
    (hpq : p ≠ q) : ¬ RayEq (b p) (b.equiv b (Equiv.swap p q) (b p)) := by
  rw [b.equiv_apply_basis, Equiv.swap_apply_left]
  exact not_rayEq_of_orthogonal (b.orthonormal.1 p) (b.orthonormal.2 hpq)

private theorem unique_split (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G)
    (huniq : ∀ H, IsSolution C v H → SameRays G H) :
    ∀ i j, G i j ∈ clueSpan C G ∨ G i j ∈ (clueSpan C G)ᗮ := by
  intro i j
  exact reflection_ray_split _ _ ((hG.1.1 i).ne_zero j)
    (huniq _ (reflection_solution C v G hG) i j)

private theorem unique_K_no_pair (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G)
    (huniq : ∀ H, IsSolution C v H → SameRays G H)
    (p q : Fin 4) (hp : G 0 p ∈ (clueSpan C G)ᗮ)
    (hq : G 0 q ∈ (clueSpan C G)ᗮ) : p = q := by
  by_contra hpq
  let b := OrthonormalBasis.mk (hG.1.1 0) (by
    rw [(hG.1.1 0).linearIndependent.span_eq_top_of_card_eq_finrank (by simp)])
  let T := b.equiv b (Equiv.swap p q)
  have hfix : ∀ x ∈ clueSpan C G, T x = x := by
    intro x hx
    apply swap_fixes_span _ b p q
    · simpa [b] using hp
    · simpa [b] using hq
    · exact hx
  have he := huniq _ (isSolution_isometry_of_fixes C v G hG T hfix) 0 p
  apply swap_changes_ray b p q hpq
  simpa [RayEq, b, T] using he

private theorem K_eq_line_of_unique (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G)
    (huniq : ∀ H, IsSolution C v H → SameRays G H)
    (p : Fin 4) (hp : G 0 p ∈ (clueSpan C G)ᗮ) :
    (clueSpan C G)ᗮ = ℂ ∙ G 0 p := by
  classical
  let b := OrthonormalBasis.mk (hG.1.1 0) (by
    rw [(hG.1.1 0).linearIndependent.span_eq_top_of_card_eq_finrank (by simp)])
  apply le_antisymm
  · intro x hx
    have hs : ∀ i, i ≠ p → G 0 i ∈ clueSpan C G := by
      intro i hip
      exact (unique_split C v G hG huniq 0 i).resolve_right
        (fun hi => hip (unique_K_no_pair C v G hG huniq i p hi hp))
    have hcoords : ∀ i, i ≠ p → b.repr x i = 0 := by
      intro i hip
      rw [b.repr_apply_apply]
      apply Submodule.inner_right_of_mem_orthogonal _ hx
      simpa [b] using hs i hip
    have he : x = b.repr x p • G 0 p := by
      calc
        x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
        _ = b.repr x p • b p := by
          apply Finset.sum_eq_single p
          · intro i _ hip; rw [hcoords i hip, zero_smul]
          · simp
        _ = _ := by simp [b]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hp)

private theorem one_line_exactly_once (S : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) (hS : S ≠ ⊤)
    (w : (EuclideanSpace ℂ (Fin 4)))
    (hw : ‖w‖ = 1) (hK : Sᗮ = ℂ ∙ w) (u : Fin 4 → (EuclideanSpace ℂ (Fin 4)))
    (hu : Orthonormal ℂ u) (hsplit : ∀ i, u i ∈ S ∨ u i ∈ Sᗮ) :
    ∃! p, RayEq w (u p) := by
  obtain ⟨p, hp⟩ := split_unit_has_K S hS u hu hsplit
  have hr : RayEq w (u p) := orthogonal_line_ray Sᗮ w hw hK _ hp (hu.1 p)
  refine ⟨p, hr, ?_⟩
  intro q hq
  by_contra hqp
  exact not_rayEq_of_orthogonal (hu.1 p) (hu.2 (Ne.symm hqp)) (hr.symm.trans hq)

def HasRepeatedRay (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (w : (EuclideanSpace ℂ
    (Fin 4))) : Prop :=
  (∀ i, ∃! j, RayEq w (G i j)) ∧
  (∀ j, ∃! i, RayEq w (G i j)) ∧
  (∀ b, ∃! k, RayEq w (G (blockCell b k).1 (blockCell b k).2))

theorem unique_implies_repeated_ray (C : Finset (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4)
    → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hC : C.card ≤ 3) (hG : IsSolution C v G)
    (huniq : ∀ H, IsSolution C v H → SameRays G H) :
    ∃ w, ‖w‖ = 1 ∧ HasRepeatedRay G w := by
  let S := clueSpan C G
  have hsplit := unique_split C v G hG huniq
  obtain ⟨p, hp⟩ := split_unit_has_K S (span_proper C G hC) (G 0) (hG.1.1 0) (hsplit 0)
  have hK := K_eq_line_of_unique C v G hG huniq p hp
  refine ⟨G 0 p, (hG.1.1 0).1 p, ?_, ?_, ?_⟩
  · intro i; exact one_line_exactly_once S (span_proper C G hC) _ ((hG.1.1 0).1 p)
      hK _ (hG.1.1 i) (hsplit i)
  · intro j; exact one_line_exactly_once S (span_proper C G hC) _ ((hG.1.1 0).1 p)
      hK _ (hG.1.2.1 j) (fun i => hsplit i j)
  · intro b
    let e : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv
    let u : Fin 4 → (EuclideanSpace ℂ (Fin 4)) := fun i => G (blockCell b (e.symm i)).1
        (blockCell b (e.symm i)).2
    have hu : Orthonormal ℂ u := (hG.1.2.2 b).comp e.symm e.symm.injective
    obtain ⟨k, hk, hkuniq⟩ := one_line_exactly_once S (span_proper C G hC) _
      ((hG.1.1 0).1 p) hK u hu (fun i => hsplit _ _)
    refine ⟨e.symm k, hk, ?_⟩
    intro l hl
    have eq : e l = k := hkuniq (e l) (by simpa [u] using hl)
    exact e.injective (by simpa using eq)


theorem RayEq.refl (x : (EuclideanSpace ℂ (Fin 4))) : RayEq x x := ⟨1, norm_one, by simp⟩



theorem RayEq.norm {x y : (EuclideanSpace ℂ (Fin 4))} (h : RayEq x y) : ‖y‖ = ‖x‖ := by
  rcases h with ⟨z, hz, rfl⟩; simp [norm_smul, hz]



theorem RayEq.inner_left_iff {x u y : (EuclideanSpace ℂ (Fin 4))} (h : RayEq x u) :
    inner ℂ u y = 0 ↔ inner ℂ x y = 0 := by
  rcases h with ⟨z, hz, rfl⟩
  have hz0 : z ≠ 0 := by intro e; simp [e] at hz
  simp [inner_smul_left, hz0]



theorem RayEq.inner_right_iff {x y u : (EuclideanSpace ℂ (Fin 4))} (h : RayEq y u) :
    inner ℂ x u = 0 ↔ inner ℂ x y = 0 := by
  rcases h with ⟨z, hz, rfl⟩
  have hz0 : z ≠ 0 := by intro e; simp [e] at hz
  simp [inner_smul_right, hz0]



end D5.S3.Quantum.LatinSquares.SudoQClueGeometry
