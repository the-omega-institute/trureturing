/- GID: D5/S3/Quantum/LatinSquares/SudoQMinimumClues
   generality: I
   mirror-B: D5/B/S3/Quantum/LatinSquares/SudoQMinimumClues
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No uniquely solvable four by four SudoQ has at most three clues. -/

/-
admission_basis: open-problem-resolution (#15470; Proved)
Direct frozen dependencies: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15607
Template gap: enrolled pointwise/guarded/iff/existential templates do not reconstruct
  the dependent completion family and its ray witnesses. DependentFamily still needs
  a source-bound arena, reconstruction, occurrence selection, an equivalence bridge,
  whole-family variation/sensitivity and actual observational dependence.
DTR reading: DTR-Unregistered for the public result (Observe); no Reg file is delivered.
proof_shape: last_ray: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_dichotomy,
  SudoQMinimumClues.q0_of_d
proof_shape: orthonormal_of_rayEq: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.isSudoQ_of_sameRays
proof_shape: isSudoQ_of_sameRays: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_second
proof_shape: claim: bind-only; escape_witness: none; consumers: SudoQMinimumClues.result
proof_shape: blockCell_reconstruct: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.sudoq_inner
proof_shape: cellBlock_blockCell: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.sudoq_of_cells
proof_shape: blockCell_injective: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.sudoq_of_cells
proof_shape: Neighbor: bind-only; escape_witness: none; consumers: SudoQMinimumClues.sudoq_inner,
  SudoQMinimumClues.sudoq_of_cells, SudoQMinimumClues.sudoq_pullback,
  SudoQMinimumClues.transpose_sudoq, SudoQMinimumClues.symmetry_neighbor,
  SudoQMinimumClues.ValidPattern, SudoQMinimumClues.instDecidableValidPattern,
  SudoQMinimumClues.repeated_pattern, SudoQMinimumClues.symmetry_neighbor_inverse,
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_dichotomy,
  SudoQMinimumClues.canonical_conditions, SudoQMinimumClues.q0_of_d, SudoQMinimumClues.trade_orth,
  SudoQMinimumClues.q0_trade_sudoq, SudoQMinimumClues.pullGrid_sudoq,
  SudoQMinimumClues.pull_solution, SudoQMinimumClues.unpull_solution, SudoQMinimumClues.result
proof_shape: instDecidableNeighbor: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.transpose_sudoq, SudoQMinimumClues.symmetry_neighbor,
  SudoQMinimumClues.instDecidableValidPattern, SudoQMinimumClues.canonical_equalities,
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.trade_orth
proof_shape: sudoq_inner: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.sudoq_pullback, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.canonical_equalities, SudoQMinimumClues.canonical_dichotomy,
  SudoQMinimumClues.canonical_conditions, SudoQMinimumClues.q0_of_d
proof_shape: sudoq_of_cells: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.sudoq_pullback, SudoQMinimumClues.q0_trade_sudoq
proof_shape: sudoq_pullback: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.transpose_sudoq, SudoQMinimumClues.pullGrid_sudoq
proof_shape: transpose_sudoq: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.result
proof_shape: symFun: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.symFun_bijective, SudoQMinimumClues.symPerm, SudoQMinimumClues.symPerm_inv
proof_shape: symFun_bijective: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.symPerm
proof_shape: symPerm: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.symmetry_neighbor, SudoQMinimumClues.pattern_orbit,
  SudoQMinimumClues.normalize_pattern, SudoQMinimumClues.symPerm_inv,
  SudoQMinimumClues.symmetry_neighbor_inverse, SudoQMinimumClues.result
proof_shape: symmetry_neighbor: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.symmetry_neighbor_inverse, SudoQMinimumClues.result
proof_shape: ValidPattern: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.pattern_orbit, SudoQMinimumClues.repeated_pattern,
  SudoQMinimumClues.normalize_pattern
proof_shape: instDecidableValidPattern: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.pattern_orbit
proof_shape: pattern_orbit: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.normalize_pattern
proof_shape: repeated_pattern: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.normalize_pattern
proof_shape: IsCanonical: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.normalize_pattern, SudoQMinimumClues.canonical_equalities,
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d, SudoQMinimumClues.transpose_canonical,
  SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.result
proof_shape: normalize_pattern: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.result
proof_shape: invIndex: bind-only; escape_witness: none; consumers: SudoQMinimumClues.symPerm_inv,
  SudoQMinimumClues.symmetry_neighbor_inverse
proof_shape: symPerm_inv: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.symmetry_neighbor_inverse
proof_shape: symmetry_neighbor_inverse: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.result
proof_shape: canonical_equalities: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_dichotomy, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.q0_of_d
proof_shape: canonical_dichotomy: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form
proof_shape: q0Label: bind-only; escape_witness: none; consumers: SudoQMinimumClues.q0,
  SudoQMinimumClues.trade_orth, SudoQMinimumClues.changed_orth, SudoQMinimumClues.q0Trade,
  SudoQMinimumClues.q0_trade_sudoq, SudoQMinimumClues.q0_trade_changed,
  SudoQMinimumClues.q0_second
proof_shape: q0: bind-only; escape_witness: none; consumers: SudoQMinimumClues.q0_of_d,
  SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.q0_trade_changed,
  SudoQMinimumClues.q0_second, SudoQMinimumClues.result
proof_shape: OrthLabel: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.Q0Conditions, SudoQMinimumClues.canonical_conditions,
  SudoQMinimumClues.trade_orth, SudoQMinimumClues.changed_orth, SudoQMinimumClues.q0_trade_sudoq,
  SudoQMinimumClues.q0_trade_changed
proof_shape: instDecidableOrthLabel: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.trade_orth, SudoQMinimumClues.changed_orth
proof_shape: Q0Conditions: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form, SudoQMinimumClues.q0_trade_sudoq,
  SudoQMinimumClues.q0_trade_changed, SudoQMinimumClues.q0_second, SudoQMinimumClues.result
proof_shape: canonical_conditions: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form
proof_shape: q0_of_d: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form
proof_shape: canon_involutive: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.transpose_canonical
proof_shape: transpose_canonical: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.canonical_normal_form
proof_shape: canonical_normal_form: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.result
proof_shape: rectOf: bind-only; escape_witness: none; consumers: SudoQMinimumClues.tradeCell,
  SudoQMinimumClues.rectOf_rep, SudoQMinimumClues.changed_orth,
  SudoQMinimumClues.q0_trade_changed, SudoQMinimumClues.clue_free_rect,
  SudoQMinimumClues.q0_second
proof_shape: tradeCell: bind-only; escape_witness: none; consumers: SudoQMinimumClues.trade_orth,
  SudoQMinimumClues.changed_orth, SudoQMinimumClues.q0Trade, SudoQMinimumClues.q0_trade_sudoq,
  SudoQMinimumClues.q0_trade_changed, SudoQMinimumClues.q0_second
proof_shape: rectRep: bind-only; escape_witness: none; consumers: SudoQMinimumClues.rectOf_rep,
  SudoQMinimumClues.q0_second
proof_shape: rectOf_rep: bind-only; escape_witness: none; consumers: SudoQMinimumClues.q0_second
proof_shape: trade_orth: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_trade_sudoq
proof_shape: changed_orth: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_trade_changed
proof_shape: q0Trade: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_trade_sudoq, SudoQMinimumClues.q0_trade_changed,
  SudoQMinimumClues.q0_second
proof_shape: q0_trade_sudoq: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_second
proof_shape: q0_trade_changed: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_second
proof_shape: clue_free_rect: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.q0_second
proof_shape: HasSecond: bind-only; escape_witness: none; consumers: SudoQMinimumClues.q0_second,
  SudoQMinimumClues.result
proof_shape: q0_second: content; escape_witness: q0_second; consumers: SudoQMinimumClues.result
proof_shape: pullGrid_sudoq: bind-only; escape_witness: none; consumers:
  SudoQMinimumClues.pull_solution, SudoQMinimumClues.unpull_solution
proof_shape: pull_solution: bind-only; escape_witness: none; consumers: SudoQMinimumClues.result
proof_shape: unpull_solution: bind-only; escape_witness: none; consumers: SudoQMinimumClues.result
proof_shape: pull_sameRays: bind-only; escape_witness: none; consumers: SudoQMinimumClues.result
proof_shape: result: content; escape_witness: unique_K_no_pair, q0_second; consumers: settling result
-/

import D5.S3.Quantum.LatinSquares.SudoQClueGeometry

open scoped ComplexConjugate InnerProductSpace
open D5.S3.Quantum.LatinSquares.SudoQClueGeometry

namespace D5.S3.Quantum.LatinSquares.SudoQMinimumClues
private theorem last_ray (u : Fin 4 → (EuclideanSpace ℂ (Fin 4))) (hu : Orthonormal ℂ u)
    (p : Fin 4)
    (x : (EuclideanSpace ℂ (Fin 4))) (hx : ‖x‖ = 1) (ho : ∀ i, i ≠ p → inner ℂ (u i) x = 0) :
    RayEq (u p) x := by
  classical
  let b := OrthonormalBasis.mk hu (by
    rw [hu.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)])
  apply rayEq_of_smul (hu.1 p) hx
  refine ⟨b.repr x p, ?_⟩
  calc
    x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    _ = b.repr x p • b p := by
      apply Finset.sum_eq_single p
      · intro i _ hip
        have : b.repr x i = 0 := by simpa [b, b.repr_apply_apply] using ho i hip
        rw [this, zero_smul]
      · simp
    _ = _ := by simp [b]


private theorem orthonormal_of_rayEq {ι : Type*} (u v : ι → (EuclideanSpace ℂ (Fin 4)))
    (hu : Orthonormal ℂ u)
    (h : ∀ i, RayEq (u i) (v i)) : Orthonormal ℂ v := by
  refine ⟨fun i => (h i).norm.trans (hu.1 i), ?_⟩
  intro i j hij
  apply (h i).inner_left_iff.mpr
  apply (h j).inner_right_iff.mpr
  exact hu.2 hij


private theorem isSudoQ_of_sameRays (G H : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (h : SameRays G H) :
    IsSudoQ H := by
  exact ⟨fun i => orthonormal_of_rayEq _ _ (hG.1 i) (h i),
    fun j => orthonormal_of_rayEq _ _ (hG.2.1 j) (fun i => h i j),
    fun b => orthonormal_of_rayEq _ _ (hG.2.2 b) (fun k => h _ _)⟩



def claim : Prop :=
  ∀ (C : Finset (Fin 4 × Fin 4))
    (v : Fin 4 × Fin 4 → EuclideanSpace ℂ (Fin 4)), C.card ≤ 3 → ¬ UniquelySolvable C v


@[simp] private theorem blockCell_reconstruct (c : (Fin 4 × Fin 4)) :
    blockCell ((Fin.divNat (m := 2) (n := 2) c.1,
      Fin.divNat (m := 2) (n := 2) c.2))
    ((Fin.modNat (m := 2) (n := 2) c.1, Fin.modNat (m := 2) (n := 2) c.2)) = c := by
  exact Prod.ext ((finProdFinEquiv (m := 2) (n := 2)).apply_symm_apply c.1)
    ((finProdFinEquiv (m := 2) (n := 2)).apply_symm_apply c.2)

@[simp] private theorem cellBlock_blockCell (b k : Fin 2 × Fin 2) :
    (Fin.divNat (m := 2) (n := 2) (blockCell b k).1,
    Fin.divNat (m := 2) (n := 2) (blockCell b k).2) = b := by
  apply Prod.ext
  · change (finProdFinEquiv (m := 2) (n := 2) (b.1, k.1)).divNat = b.1
    exact congrArg Prod.fst ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (b.1, k.1))
  · change (finProdFinEquiv (m := 2) (n := 2) (b.2, k.2)).divNat = b.2
    exact congrArg Prod.fst ((finProdFinEquiv (m := 2) (n := 2)).symm_apply_apply (b.2, k.2))

private theorem blockCell_injective (b : Fin 2 × Fin 2) : Function.Injective (blockCell b) := by
  intro k l h
  have h1 : (b.1, k.1) = (b.1, l.1) :=
    (finProdFinEquiv (m := 2) (n := 2)).injective (congrArg Prod.fst h)
  have h2 : (b.2, k.2) = (b.2, l.2) :=
    (finProdFinEquiv (m := 2) (n := 2)).injective (congrArg Prod.snd h)
  have hk1 := congrArg (fun t : Fin 2 × Fin 2 => t.2) h1
  have hk2 := congrArg (fun t : Fin 2 × Fin 2 => t.2) h2
  exact congrArg₂ Prod.mk hk1 hk2

private def Neighbor (c d : (Fin 4 × Fin 4)) : Prop :=
  c ≠ d ∧ (c.1 = d.1 ∨ c.2 = d.2 ∨
    (Fin.divNat (m := 2) (n := 2) c.1, Fin.divNat (m := 2) (n := 2) c.2) =
      (Fin.divNat (m := 2) (n := 2) d.1, Fin.divNat (m := 2) (n := 2) d.2))
private instance (c d : (Fin 4 × Fin 4)) : Decidable (Neighbor c d) := inferInstanceAs
    (Decidable (_ ∧ _))

private theorem sudoq_inner (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (hG : IsSudoQ G)
    (c d : (Fin 4 × Fin 4)) (h : Neighbor c d) :
    inner ℂ (G c.1 c.2) (G d.1 d.2) = 0 := by
  rcases h with ⟨hcd, h | h | h⟩
  · have hne : c.2 ≠ d.2 := by intro e; exact hcd (Prod.ext h e)
    rw [h]; exact (hG.1 d.1).2 hne
  · have hne : c.1 ≠ d.1 := by intro e; exact hcd (Prod.ext e h)
    rw [h]; exact (hG.2.1 d.2).2 hne
  · have hne : (Fin.modNat (m := 2) (n := 2) c.1, Fin.modNat (m := 2) (n := 2) c.2) ≠
        (Fin.modNat (m := 2) (n := 2) d.1, Fin.modNat (m := 2) (n := 2) d.2) := by
      intro e
      apply hcd
      rw [← blockCell_reconstruct c, ← blockCell_reconstruct d, h, e]
    have ho := (hG.2.2 ((Fin.divNat (m := 2) (n := 2) c.1, Fin.divNat (m := 2) (n := 2) c.2))).2 hne
    dsimp only at ho
    rw [blockCell_reconstruct c, h, blockCell_reconstruct d] at ho
    exact ho

private theorem sudoq_of_cells (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (hn : ∀ c :
    (Fin 4 × Fin 4), ‖G c.1 c.2‖ = 1)
    (ho : ∀ c d, Neighbor c d → inner ℂ (G c.1 c.2) (G d.1 d.2) = 0) : IsSudoQ G := by
  refine ⟨fun i => ⟨fun j => hn (i,j), ?_⟩,
    fun j => ⟨fun i => hn (i,j), ?_⟩,
    fun b => ⟨fun k => hn (blockCell b k), ?_⟩⟩
  · intro j k hjk; exact ho (i,j) (i,k) ⟨by simp [hjk], Or.inl rfl⟩
  · intro i k hik; exact ho (i,j) (k,j) ⟨by simp [hik], Or.inr (Or.inl rfl)⟩
  · intro k l hkl
    exact ho _ _ ⟨fun h => hkl (blockCell_injective b h), Or.inr (Or.inr (by simp))⟩

private theorem sudoq_pullback (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (f : (Fin 4 × Fin 4) → (Fin 4 × Fin 4))
    (hf : ∀ c d, Neighbor c d → Neighbor (f c) (f d)) :
    IsSudoQ (fun i j => G (f (i,j)).1 (f (i,j)).2) := by
  apply sudoq_of_cells
  · intro c; exact (hG.1 _).1 _
  · intro c d h; exact sudoq_inner G hG _ _ (hf c d h)


private theorem transpose_sudoq (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) : IsSudoQ (Function.swap G) := by
  apply sudoq_pullback G hG (fun c => (c.2,c.1))
  decide +kernel


private def symFun (r : Fin 8) : Fin 4 → Fin 4 :=
  (![![0,1,2,3], ![1,0,2,3], ![0,1,3,2], ![1,0,3,2],
      ![2,3,0,1], ![3,2,0,1], ![2,3,1,0], ![3,2,1,0]]) r

private theorem symFun_bijective (r : Fin 8) : Function.Bijective (symFun r) := by
  fin_cases r <;> decide

private noncomputable def symPerm (r : Fin 8) : Fin 4 ≃ Fin 4 := Equiv.ofBijective (symFun r)
    (symFun_bijective r)
private theorem symmetry_neighbor : ∀ r s : Fin 8, ∀ c d : (Fin 4 × Fin 4),
    Neighbor c d → Neighbor ((Equiv.prodCongr (symPerm r) (symPerm s)) c)
      ((Equiv.prodCongr (symPerm r) (symPerm s)) d) := by
  decide +kernel

private def ValidPattern (p : Fin 4 → Fin 4) : Prop :=
  ∀ i j, i ≠ j → ¬ Neighbor (i,p i) (j,p j)
private instance (p : Fin 4 → Fin 4) : Decidable (ValidPattern p) := inferInstanceAs (Decidable
    (∀ _ _, _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- The finite orbit check enumerates all row and column permutations.
private theorem pattern_orbit : ∀ p : Fin 4 → Fin 4, ValidPattern p →
    ∃ r s : Fin 8, ∀ i, symPerm s ((Equiv.swap (1 : Fin 4) 2) i) = p (symPerm r i) := by
  decide +kernel

private theorem repeated_pattern (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : HasRepeatedRay G w) :
    ∃ p : Fin 4 → Fin 4, ValidPattern p ∧ ∀ i, RayEq w (G i (p i)) := by
  classical
  choose p hp using fun i => (hw.1 i).exists
  refine ⟨p, ?_, hp⟩
  intro i j hij hnei
  exact not_rayEq_of_orthogonal ((hG.1 i).1 (p i)) (sudoq_inner G hG _ _ hnei)
    ((hp i).symm.trans (hp j))

private def IsCanonical (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (w : (EuclideanSpace ℂ
    (Fin 4))) : Prop := ∀ i, RayEq w (G i ((Equiv.swap (1 : Fin 4) 2) i))

private theorem normalize_pattern (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : HasRepeatedRay G w) :
    ∃ r s : Fin 8, IsCanonical (fun i j => G (symPerm r i) (symPerm s j)) w := by
  obtain ⟨p,hp,hr⟩ := repeated_pattern G hG w hw
  obtain ⟨r,s,hs⟩ := pattern_orbit p hp
  refine ⟨r,s,?_⟩
  intro i
  change RayEq w (G (symPerm r i) (symPerm s ((Equiv.swap (1 : Fin 4) 2) i)))
  rw [hs i]
  exact hr _



private noncomputable def invIndex : Fin 8 → Fin 8 := ![0,1,2,3,4,6,5,7]
private theorem symPerm_inv (r : Fin 8) : (symPerm r).symm = symPerm (invIndex r) := by
  apply Equiv.ext
  intro i
  apply (symPerm r).injective
  rw [(symPerm r).apply_symm_apply]
  change i = symFun r (symFun (invIndex r) i)
  revert i r
  decide +kernel

private theorem symmetry_neighbor_inverse : ∀ r s : Fin 8, ∀ c d : (Fin 4 × Fin 4),
    Neighbor c d → Neighbor ((Equiv.prodCongr (symPerm r) (symPerm s)).symm c)
      ((Equiv.prodCongr (symPerm r) (symPerm s)).symm d) := by
  intro r s c d h
  simpa [symPerm_inv] using symmetry_neighbor (invIndex r) (invIndex s) c d h


private theorem canonical_equalities (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w) :
    RayEq (G 0 1) (G 1 3) ∧ RayEq (G 0 2) (G 2 3) ∧
    RayEq (G 1 0) (G 3 1) ∧ RayEq (G 2 0) (G 3 2) := by
  have hr : ∀ i, RayEq (G 0 0) (G i ((Equiv.swap (1 : Fin 4) 2) i)) :=
    fun i => (hw 0).symm.trans (hw i)
  have h13 : RayEq (G 0 1) (G 1 3) := by
    apply last_ray (G 0) (hG.1 0) 1 _ ((hG.1 1).1 3)
    intro i hi
    fin_cases i
    · exact (hr 1).inner_left_iff.mp (sudoq_inner G hG (1,2) (1,3) (by decide))
    · exact (hi rfl).elim
    · exact sudoq_inner G hG (0,2) (1,3) (by decide)
    · exact sudoq_inner G hG (0,3) (1,3) (by decide)
  have h23 : RayEq (G 0 2) (G 2 3) := by
    apply last_ray (G 0) (hG.1 0) 2 _ ((hG.1 2).1 3)
    intro i hi
    fin_cases i
    · exact (hr 3).inner_left_iff.mp (sudoq_inner G hG (3,3) (2,3) (by decide))
    · exact h13.inner_left_iff.mp (sudoq_inner G hG (1,3) (2,3) (by decide))
    · exact (hi rfl).elim
    · exact sudoq_inner G hG (0,3) (2,3) (by decide)
  have h31 : RayEq (G 1 0) (G 3 1) := by
    apply last_ray (G 1) (hG.1 1) 0 _ ((hG.1 3).1 1)
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact sudoq_inner G hG (1,1) (3,1) (by decide)
    · exact ((hr 1).symm.trans (hr 2)).inner_left_iff.mp
        (sudoq_inner G hG (2,1) (3,1) (by decide))
    · exact h13.symm.inner_left_iff.mp (sudoq_inner G hG (0,1) (3,1) (by decide))
  have h32 : RayEq (G 2 0) (G 3 2) := by
    apply last_ray (G 2) (hG.1 2) 0 _ ((hG.1 3).1 2)
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact ((hr 2).symm.trans (hr 3)).inner_left_iff.mp
        (sudoq_inner G hG (3,3) (3,2) (by decide))
    · exact sudoq_inner G hG (2,2) (3,2) (by decide)
    · exact h23.symm.inner_left_iff.mp (sudoq_inner G hG (0,2) (3,2) (by decide))
  exact ⟨h13,h23,h31,h32⟩

private theorem canonical_dichotomy (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w) :
    RayEq (G 0 2) (G 1 0) ∨ RayEq (G 0 1) (G 2 0) := by
  have h13 := (canonical_equalities G hG w hw).1
  have h23 := (canonical_equalities G hG w hw).2.1
  have hwd : inner ℂ (G 0 0) (G 1 0) = 0 := sudoq_inner G hG (0,0) (1,0) (by decide)
  have had : inner ℂ (G 0 1) (G 1 0) = 0 := sudoq_inner G hG (0,1) (1,0) (by decide)
  have hwg : inner ℂ (G 0 0) (G 2 0) = 0 := sudoq_inner G hG (0,0) (2,0) (by decide)
  have hbg : inner ℂ (G 0 2) (G 2 0) = 0 :=
    h23.inner_left_iff.mp (sudoq_inner G hG (2,3) (2,0) (by decide))
  have hdg : inner ℂ (G 1 0) (G 2 0) = 0 := sudoq_inner G hG (1,0) (2,0) (by decide)
  have hdw : inner ℂ (G 1 0) (G 0 0) = 0 := inner_eq_zero_symm.mpr hwd
  have hda : inner ℂ (G 1 0) (G 0 1) = 0 := inner_eq_zero_symm.mpr had
  let b := OrthonormalBasis.mk (hG.1 0) (by
    rw [(hG.1 0).linearIndependent.span_eq_top_of_card_eq_finrank (by simp)])
  have hprod : inner ℂ (G 1 0) (G 0 3) * inner ℂ (G 0 3) (G 2 0) = 0 := by
    rw [← b.sum_inner_mul_inner] at hdg
    simpa only [Fin.sum_univ_four, OrthonormalBasis.coe_mk, b, hdw, hda, hwg, hbg,
      zero_mul, mul_zero, zero_add, add_zero] using hdg
  rcases mul_eq_zero.mp hprod with hdc | hcg
  · left
    apply last_ray (G 0) (hG.1 0) 2 _ ((hG.1 1).1 0)
    intro i hi
    fin_cases i
    · exact hwd
    · exact had
    · exact (hi rfl).elim
    · exact inner_eq_zero_symm.mp hdc
  · right
    apply last_ray (G 0) (hG.1 0) 1 _ ((hG.1 2).1 0)
    intro i hi
    fin_cases i
    · exact hwg
    · exact (hi rfl).elim
    · exact hbg
    · exact hcg


private def q0Label : (Fin 4 × Fin 4) → Fin 6 := fun c =>
  (![![0,1,2,3], ![2,3,0,1], ![4,0,5,2], ![5,2,4,0]]) c.1 c.2

private def q0 (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) : (Fin 4 → Fin 4 → EuclideanSpace ℂ
    (Fin 4)) := fun i j => B (q0Label (i,j))

private def OrthLabel (x y : Fin 6) : Prop := x ≠ y ∧
  (x = 0 ∨ y = 0 ∨ x = 2 ∨ y = 2 ∨
   (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨ (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4))
private instance (x y : Fin 6) : Decidable (OrthLabel x y) := inferInstanceAs (Decidable (_ ∧ _))

private def Q0Conditions (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) : Prop :=
  (∀ x, ‖B x‖ = 1) ∧ ∀ x y, OrthLabel x y → inner ℂ (B x) (B y) = 0

set_option maxHeartbeats 2000000 in
-- The six-label orthogonality verification splits all pairs of labels.
private theorem canonical_conditions (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w) :
    Q0Conditions ![G 0 0, G 0 1, G 0 2, G 0 3, G 2 0, G 2 2] := by
  have hr : ∀ i, RayEq (G 0 0) (G i ((Equiv.swap (1 : Fin 4) 2) i)) :=
    fun i => (hw 0).symm.trans (hw i)
  have h23 := (canonical_equalities G hG w hw).2.1
  have h_wg : inner ℂ (G 0 0) (G 2 0) = 0 := sudoq_inner G hG (0,0) (2,0) (by decide)
  have h_wh : inner ℂ (G 0 0) (G 2 2) = 0 :=
    (hr 2).inner_left_iff.mp (sudoq_inner G hG (2,1) (2,2) (by decide))
  have h_bg : inner ℂ (G 0 2) (G 2 0) = 0 :=
    h23.inner_left_iff.mp (sudoq_inner G hG (2,3) (2,0) (by decide))
  have h_bh : inner ℂ (G 0 2) (G 2 2) = 0 :=
    h23.inner_left_iff.mp (sudoq_inner G hG (2,3) (2,2) (by decide))
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> exact (hG.1 _).1 _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [OrthLabel] at hij
    all_goals dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons]
    all_goals first
      | exact h_wg
      | exact h_wh
      | exact h_bg
      | exact h_bh
      | exact inner_eq_zero_symm.mpr h_wg
      | exact inner_eq_zero_symm.mpr h_wh
      | exact inner_eq_zero_symm.mpr h_bg
      | exact inner_eq_zero_symm.mpr h_bh
      | exact sudoq_inner G hG (0,0) (0,1) (by decide)
      | exact sudoq_inner G hG (0,0) (0,2) (by decide)
      | exact sudoq_inner G hG (0,0) (0,3) (by decide)
      | exact sudoq_inner G hG (0,1) (0,0) (by decide)
      | exact sudoq_inner G hG (0,1) (0,2) (by decide)
      | exact sudoq_inner G hG (0,1) (0,3) (by decide)
      | exact sudoq_inner G hG (0,2) (0,0) (by decide)
      | exact sudoq_inner G hG (0,2) (0,1) (by decide)
      | exact sudoq_inner G hG (0,2) (0,3) (by decide)
      | exact sudoq_inner G hG (0,3) (0,0) (by decide)
      | exact sudoq_inner G hG (0,3) (0,1) (by decide)
      | exact sudoq_inner G hG (0,3) (0,2) (by decide)
      | exact sudoq_inner G hG (2,0) (2,2) (by decide)
      | exact sudoq_inner G hG (2,2) (2,0) (by decide)

private theorem q0_of_d (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (hG : IsSudoQ G) (w :
    (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w)
    (hd : RayEq (G 0 2) (G 1 0)) :
    SameRays (q0 ![G 0 0, G 0 1, G 0 2, G 0 3, G 2 0, G 2 2]) G := by
  obtain ⟨h13,h23,h31,h32⟩ := canonical_equalities G hG w hw
  have hr : ∀ i, RayEq (G 0 0) (G i ((Equiv.swap (1 : Fin 4) 2) i)) :=
    fun i => (hw 0).symm.trans (hw i)
  have h11 : RayEq (G 0 3) (G 1 1) := by
    apply last_ray (G 0) (hG.1 0) 3 _ ((hG.1 1).1 1)
    intro i hi
    fin_cases i
    · exact sudoq_inner G hG (0,0) (1,1) (by decide)
    · exact sudoq_inner G hG (0,1) (1,1) (by decide)
    · exact hd.inner_left_iff.mp (sudoq_inner G hG (1,0) (1,1) (by decide))
    · exact (hi rfl).elim
  have h30 : RayEq (G 2 2) (G 3 0) := by
    apply last_ray (G 2) (hG.1 2) 2 _ ((hG.1 3).1 0)
    intro i hi
    fin_cases i
    · exact sudoq_inner G hG (2,0) (3,0) (by decide)
    · exact ((hr 2).symm.trans (hr 3)).inner_left_iff.mp
        (sudoq_inner G hG (3,3) (3,0) (by decide))
    · exact (hi rfl).elim
    · exact (h23.symm.trans (hd.trans h31)).inner_left_iff.mp
        (sudoq_inner G hG (3,1) (3,0) (by decide))
  intro i j
  fin_cases i <;> fin_cases j
  all_goals change RayEq _ _
  all_goals dsimp only [q0, q0Label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  all_goals first
    | exact RayEq.refl _
    | exact hd
    | exact h11
    | exact h13
    | exact h23
    | exact h30
    | exact hd.trans h31
    | exact h32
    | exact hr 1
    | exact hr 2
    | exact hr 3

private theorem canon_involutive :
    ∀ i, (Equiv.swap (1 : Fin 4) 2) ((Equiv.swap (1 : Fin 4) 2) i) = i :=
  Equiv.swap_apply_self 1 2

private theorem transpose_canonical (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4))) (w :
    (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w) :
    IsCanonical (Function.swap G) w := by
  intro i
  simpa only [canon_involutive] using hw ((Equiv.swap (1 : Fin 4) 2) i)

private theorem canonical_normal_form (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSudoQ G) (w : (EuclideanSpace ℂ (Fin 4))) (hw : IsCanonical G w) :
    (∃ B, Q0Conditions B ∧ SameRays (q0 B) G) ∨
    (∃ B, Q0Conditions B ∧ SameRays (q0 B) (Function.swap G)) := by
  rcases canonical_dichotomy G hG w hw with hd | hg
  · exact Or.inl ⟨_, canonical_conditions G hG w hw, q0_of_d G hG w hw hd⟩
  · have ht := transpose_sudoq G hG
    have hc := transpose_canonical G w hw
    exact Or.inr ⟨_, canonical_conditions (Function.swap G) ht w hc,
      q0_of_d (Function.swap G) ht w hc hg.symm⟩



private def rectOf (c : (Fin 4 × Fin 4)) : Fin 4 := ⟨2 * (c.1.val / 2) + c.2.val % 2, by omega⟩
private def tradeCell (k : Fin 4) (c : (Fin 4 × Fin 4)) : (Fin 4 × Fin 4)
    := if rectOf c = k then (c.1,(c.2 + 2)) else c

private def rectRep : Fin 4 → (Fin 4 × Fin 4) := ![(0,0),(0,1),(2,0),(2,1)]
private theorem rectOf_rep : ∀ k, rectOf (rectRep k) = k := by decide

private theorem trade_orth : ∀ k : Fin 4, ∀ c d : (Fin 4 × Fin 4), Neighbor c d →
    OrthLabel (q0Label (tradeCell k c)) (q0Label (tradeCell k d)) := by
  decide +kernel

private theorem changed_orth : ∀ k : Fin 4, ∀ c : (Fin 4 × Fin 4), rectOf c = k →
    OrthLabel (q0Label c) (q0Label (tradeCell k c)) := by
  decide +kernel

private def q0Trade (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) (k : Fin 4) : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4)) :=
  fun i j => B (q0Label (tradeCell k (i,j)))

private theorem q0_trade_sudoq (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) (hB : Q0Conditions B)
    (k : Fin 4) :
    IsSudoQ (q0Trade B k) := by
  apply sudoq_of_cells
  · intro c; exact hB.1 _
  · intro c d h; exact hB.2 _ _ (trade_orth k c d h)

private theorem q0_trade_changed (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) (hB : Q0Conditions B)
    (k : Fin 4) (c : (Fin 4 × Fin 4)) (hc : rectOf c = k) :
    ¬ RayEq (q0 B c.1 c.2) (q0Trade B k c.1 c.2) :=
  not_rayEq_of_orthogonal (hB.1 _) (hB.2 _ _ (changed_orth k c hc))

private theorem clue_free_rect (C : Finset (Fin 4 × Fin 4)) (hC : C.card ≤ 3) :
    ∃ k : Fin 4, ∀ c ∈ C, rectOf c ≠ k := by
  classical
  have hc : (C.image rectOf).card < (Finset.univ : Finset (Fin 4)).card := by
    have h := Finset.card_image_le (s := C) (f := rectOf)
    have hn : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨k,?_⟩
  intro c hc he
  apply hk
  rw [← he]
  exact Finset.mem_image_of_mem rectOf hc

private def HasSecond (C : Finset (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4 → EuclideanSpace ℂ
    (Fin 4))) : Prop :=
  ∃ H, IsSudoQ H ∧ (∀ c ∈ C, H c.1 c.2 = G c.1 c.2) ∧ ¬ SameRays G H

private theorem q0_second (B : Fin 6 → (EuclideanSpace ℂ (Fin 4))) (hB : Q0Conditions B) (G :
    (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)))
    (hr : SameRays (q0 B) G) (C : Finset (Fin 4 × Fin 4)) (hC : C.card ≤ 3) : HasSecond C G := by
  classical
  obtain ⟨k,hk⟩ := clue_free_rect C hC
  let H : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)) := fun i j => if rectOf
      (i,j) = k then q0Trade B k i j else G i j
  have hsame : SameRays (q0Trade B k) H := by
    intro i j
    change RayEq (q0Trade B k i j) (H i j)
    have hrij := hr i j
    change RayEq (q0 B i j) (G i j) at hrij
    by_cases he : rectOf (i,j) = k
    · simpa [H,he] using RayEq.refl (q0Trade B k i j)
    · simpa [H,he,q0Trade,tradeCell,q0] using hrij
  refine ⟨H,isSudoQ_of_sameRays _ _ (q0_trade_sudoq B hB k) hsame,?_,?_⟩
  · intro c hc
    simp only [H,if_neg (hk c hc)]
  · intro hn
    let c := rectRep k
    have hc : rectOf c = k := rectOf_rep k
    apply q0_trade_changed B hB k c hc
    have hrc := hr c.1 c.2
    change RayEq (q0 B c.1 c.2) (G c.1 c.2) at hrc
    have hnc := hn c.1 c.2
    change RayEq (G c.1 c.2) (H c.1 c.2) at hnc
    simpa only [H, hc, if_pos] using hrc.trans hnc



private theorem pullGrid_sudoq (f : (Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4)) (G : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4))) (hG : IsSudoQ G)
    (hf : ∀ c d, Neighbor c d → Neighbor (f c) (f d)) :
    IsSudoQ ((Function.curry (Function.uncurry G ∘ f))) := by
  apply sudoq_pullback G hG
  exact hf

private theorem pull_solution (f : (Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4)) (C : Finset
    (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4) → (EuclideanSpace ℂ (Fin 4))) (G : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4)))
    (hG : IsSolution C v G)
    (hf : ∀ c d, Neighbor c d → Neighbor (f c) (f d)) :
    IsSolution ((C.image f.symm)) ((v ∘ f)) ((Function.curry (Function.uncurry G ∘ f))) := by
  refine ⟨pullGrid_sudoq f G hG.1 hf, ?_⟩
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
  change G (f (f.symm d)).1 (f (f.symm d)).2 = v (f (f.symm d))
  rw [Equiv.apply_symm_apply]
  exact hG.2 d hd

private theorem unpull_solution (f : (Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4)) (C : Finset
    (Fin 4 × Fin 4)) (v : (Fin 4 × Fin 4) → (EuclideanSpace ℂ (Fin 4))) (H : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4)))
    (hH : IsSolution ((C.image f.symm)) ((v ∘ f)) H)
    (hfi : ∀ c d, Neighbor c d → Neighbor (f.symm c) (f.symm d)) :
    IsSolution C v ((Function.curry (Function.uncurry H ∘ f.symm))) := by
  refine ⟨pullGrid_sudoq f.symm H hH.1 hfi, ?_⟩
  intro c hc
  have hc' : f.symm c ∈ (C.image f.symm) := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have he := hH.2 (f.symm c) hc'
  simpa [Function.curry, Function.uncurry, Function.comp_def] using he

private theorem pull_sameRays (f : (Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4)) (G H : (Fin 4 → Fin 4
    → EuclideanSpace ℂ (Fin 4))) (h : SameRays G H) :
    SameRays (Function.curry (Function.uncurry G ∘ f))
      (Function.curry (Function.uncurry H ∘ f)) := by
  intro i j; exact h (f (i,j)).1 (f (i,j)).2

theorem result : claim := by
  intro C v hC hU
  rcases hU with ⟨G,hG,hu⟩
  obtain ⟨w,hw,hr⟩ := unique_implies_repeated_ray C v G hC hG hu
  obtain ⟨r,s,hcanon⟩ := normalize_pattern G hG.1 w hr
  let f : (Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4) := Equiv.prodCongr (symPerm r) (symPerm s)
  let G' := (Function.curry (Function.uncurry G ∘ f))
  let C' := (C.image f.symm)
  let v' := (v ∘ f)
  have hf : ∀ c d, Neighbor c d → Neighbor (f c) (f d) := by simpa [f] using symmetry_neighbor r s
  have hf_inv : ∀ c d, Neighbor c d → Neighbor (f.symm c) (f.symm d) := by
    simpa [f] using symmetry_neighbor_inverse r s
  have hG' : IsSolution C' v' G' := pull_solution f C v G hG hf
  have hcanonical : IsCanonical G' w := by
    intro i
    change RayEq w (G (symPerm r i) (symPerm s ((Equiv.swap (1 : Fin 4) 2) i)))
    exact hcanon i
  rcases canonical_normal_form G' hG'.1 w hcanonical with ⟨B,hB,hrB⟩ | ⟨B,hB,hrB⟩
  · have hs := q0_second B hB G' hrB C' (by
      change (C.image f.symm).card ≤ 3
      rw [Finset.card_image_of_injective C f.symm.injective]
      exact hC)
    rcases hs with ⟨H',hH',hclues',hdiff'⟩
    let H : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)) :=
      Function.curry (Function.uncurry H' ∘ f.symm)
    have hcluesv : ∀ c ∈ C', H' c.1 c.2 = v' c := fun c hc => (hclues' c hc).trans (hG'.2 c hc)
    have hH'sol : IsSolution C' v' H' := ⟨hH', hcluesv⟩
    have hH : IsSolution C v H := by simpa [H] using unpull_solution f C v H' hH'sol hf_inv
    have hdiff : ¬ SameRays G H := by
      intro e
      apply hdiff'
      have pe : (Function.curry (Function.uncurry H ∘ f)) = H' := by
        funext i j
        simp [H, Function.curry, Function.uncurry, Function.comp_def]
      have he := pull_sameRays f G H e
      rw [pe] at he
      exact he
    exact hdiff (hu H hH)
  · let Ct : Finset (Fin 4 × Fin 4) := C'.image (fun c : (Fin 4 × Fin 4) => (c.2,c.1))
    have hCt : Ct.card ≤ 3 := by
      apply (Finset.card_image_le).trans
      change (C.image f.symm).card ≤ 3
      rw [Finset.card_image_of_injective C f.symm.injective]
      exact hC
    have hs := q0_second B hB (Function.swap G') hrB Ct hCt
    rcases hs with ⟨H',hH',hclues',hdiff'⟩
    let Ht := Function.swap H'
    have hcluesv : ∀ c ∈ C', Ht c.1 c.2 = v' c := by
      intro c hc
      have hc0 := hclues' (c.2,c.1) (Finset.mem_image_of_mem (fun c : (Fin 4 × Fin 4) =>
          (c.2,c.1)) hc)
      have hg0 := hG'.2 c hc
      simpa [Ht,Function.swap] using (hc0.trans hg0)
    have hHt : IsSolution C' v' Ht := ⟨transpose_sudoq H' hH', hcluesv⟩
    have hdifft : ¬ SameRays G' Ht := by
      intro e
      apply hdiff'
      intro i j
      exact e j i
    let H : (Fin 4 → Fin 4 → EuclideanSpace ℂ (Fin 4)) :=
      Function.curry (Function.uncurry Ht ∘ f.symm)
    have hH : IsSolution C v H := unpull_solution f C v Ht hHt hf_inv
    have hdiff : ¬ SameRays G H := by
      intro e
      apply hdifft
      have pe : (Function.curry (Function.uncurry H ∘ f)) = Ht := by
        funext i j
        simp [H, Function.curry, Function.uncurry, Function.comp_def]
      have he := pull_sameRays f G H e
      rw [pe] at he
      exact he
    exact hdiff (hu H hH)


end D5.S3.Quantum.LatinSquares.SudoQMinimumClues
