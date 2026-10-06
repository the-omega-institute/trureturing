/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47Classification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47Classification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47Mixed

set_option autoImplicit false

/-! Actual type-I/type-II classification and representative choice from
Part I p228. The component movement budget is computed on the powered graph,
never inferred from transitivity of the original unpowered tuple. -/
namespace NikolovSegal.Equation47
universe u
section ComponentRoots
variable {I : Type u} [DecidableEq I] {m : ℕ}

/-- A genuine choice of one representative per powered connected component.
The more general reconstruction theorem also accepts prescribed Hall roots.
-/
noncomputable def poweredComponentRoot {q : ℕ}
    (σ : Fin m → Equiv.Perm I) (v : I) : I :=
  ((qPowerGraph σ q).connectedComponentMk v).out

theorem poweredComponentRoot_spec {q : ℕ} (σ : Fin m → Equiv.Perm I) :
    (∀ v, (qPowerGraph σ q).Reachable (poweredComponentRoot (q := q) σ v) v) ∧
    (∀ v w, (qPowerGraph σ q).Reachable v w →
      poweredComponentRoot (q := q) σ v = poweredComponentRoot (q := q) σ w) := by
  constructor
  · intro v
    exact SimpleGraph.ConnectedComponent.exact
      ((qPowerGraph σ q).connectedComponentMk v).out_eq
  · intro v w h
    unfold poweredComponentRoot
    rw [SimpleGraph.ConnectedComponent.sound h]

end ComponentRoots

variable {I : Type u} [Fintype I] [DecidableEq I] {m : ℕ}

noncomputable def componentVertices (r : I → I) (root : I) : Finset I :=
  Finset.univ.filter (fun v => r v = root)

noncomputable def movedIndices (tau : Fin m → Equiv.Perm I) (v : I) : Finset (Fin m) :=
  Finset.univ.filter (fun j => tau j v ≠ v)

noncomputable def componentMovement (tau : Fin m → Equiv.Perm I) (r : I → I) (root : I) : ℕ :=
  ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ tau j v ≠ v)).card

private theorem movement_sum (tau : Fin m → Equiv.Perm I) (r : I → I) (root : I) :
    componentMovement tau r root = ∑ v ∈ componentVertices r root, (movedIndices tau v).card := by
  classical
  simp only [componentMovement,componentVertices,movedIndices,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : r v = root <;> simp only [h,true_and,false_and,ite_true,ite_false,Finset.sum_const_zero]

private theorem light_representative (tau : Fin m → Equiv.Perm I) (r : I → I) (root : I)
    (K : ℕ) (h : componentMovement tau r root < K * (componentVertices r root).card) :
    ∃ v ∈ componentVertices r root, (movedIndices tau v).card < K := by
  classical
  by_contra hn
  have hh : ∀ v ∈ componentVertices r root, K ≤ (movedIndices tau v).card := by
    intro v hv
    by_contra hh
    exact hn ⟨v,hv,by omega⟩
  have hs := Finset.sum_le_sum hh
  rw [movement_sum] at h
  have he : (∑ v ∈ componentVertices r root, K) = K * (componentVertices r root).card := by simp [Nat.mul_comm]
  rw [he] at hs
  omega

private theorem root_move (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (j : Fin m) (v : I) : r (tau j v) = r v := by
  by_cases h : v = tau j v
  · exact congrArg r h.symm
  · exact (hconst v (tau j v) (show (qPowerGraph tau 1).Adj v (tau j v) from
      ⟨h,j,Or.inl (by simp)⟩).reachable).symm

private theorem heavy_card (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root) (K : ℕ) (hK : 0 < K)
    (hheavy : K * (componentVertices r root).card ≤ componentMovement tau r root) :
    2 ≤ (componentVertices r root).card := by
  classical
  have hmem : root ∈ componentVertices r root := by simp [componentVertices,hroot.symm]
  have hpos := Finset.card_pos.mpr ⟨root,hmem⟩
  by_contra hn
  have hc : (componentVertices r root).card = 1 := by omega
  have heq : componentVertices r root = {root} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hmem,fun v hv => (Finset.card_le_one.mp (show (componentVertices r root).card ≤ 1 by omega)) v hv root hmem⟩
  have hfixed : ∀ j, tau j root = root := by
    intro j
    have hm : tau j root ∈ componentVertices r root := by
      simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
      exact (root_move tau r hconst j root).trans hroot.symm
    simpa only [heq,Finset.mem_singleton] using hm
  have hz : componentMovement tau r root = 0 := by
    rw [movement_sum,heq]
    simp [movedIndices,hfixed]
  rw [hc,hz,Nat.mul_one] at hheavy
  omega

/-- Choose genuine component representatives BEFORE scalar corrections and
all targets. Every light component gets a representative with fewer than K
bad indices, exactly the hypothesis consumed by the MD/Hall interval theorem.
Every heavy component has at least two vertices and its actual movement
threshold. No original transitivity or new coverage assumption is used. -/
theorem exists_quantitative_component_roots (tau : Fin m → Equiv.Perm I)
    (K : ℕ) (hK : 0 < K) :
    ∃ r : I → I,
      (∀ v, (qPowerGraph tau 1).Reachable (r v) v) ∧
      (∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w) ∧
      (∀ root, root = r root →
        componentMovement tau r root < K * (componentVertices r root).card →
        (movedIndices tau root).card < K) ∧
      (∀ root, root = r root →
        ¬ componentMovement tau r root < K * (componentVertices r root).card →
        2 ≤ (componentVertices r root).card) := by
  classical
  let r0 := poweredComponentRoot (q := 1) tau
  obtain ⟨hr0,hconst0⟩ := poweredComponentRoot_spec (q := 1) tau
  have hidem0 : ∀ v, r0 (r0 v) = r0 v := fun v => hconst0 _ _ (hr0 v)
  let light := fun root => componentMovement tau r0 root < K * (componentVertices r0 root).card
  have hex : ∀ root, light root → ∃ v ∈ componentVertices r0 root, (movedIndices tau v).card < K :=
    fun root h => light_representative tau r0 root K h
  let chooseRoot := fun root => if h : light root then Classical.choose (hex root h) else root
  let r := fun v => chooseRoot (r0 v)
  have hchosen : ∀ v, r0 (r v) = r0 v := by
    intro v
    dsimp only [r,chooseRoot]
    split_ifs with h
    · exact (Finset.mem_filter.mp (Classical.choose_spec (hex (r0 v) h)).1).2
    · exact hidem0 v
  have hreach : ∀ v, (qPowerGraph tau 1).Reachable (r v) v := by
    intro v
    have hh : (qPowerGraph tau 1).Reachable (r0 (r v)) (r v) := hr0 (r v)
    rw [hchosen] at hh
    exact hh.symm.trans (hr0 v)
  have hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w := by
    intro v w h
    exact congrArg chooseRoot (hconst0 v w h)
  have hfib : ∀ root, root = r root → ∀ v, r v = root ↔ r0 v = r0 root := by
    intro root hroot v
    constructor
    · intro h
      rw [← hchosen v,h]
    · intro h
      exact (congrArg chooseRoot h).trans hroot.symm
  have hV : ∀ root, root = r root → componentVertices r root = componentVertices r0 (r0 root) := by
    intro root hroot
    ext v
    simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and,hfib root hroot]
  have hM : ∀ root, root = r root → componentMovement tau r root = componentMovement tau r0 (r0 root) := by
    intro root hroot
    rw [movement_sum,movement_sum,hV root hroot]
  refine ⟨r,hreach,hconst,?_,?_⟩
  · intro root hroot hlight
    rw [hM root hroot,hV root hroot] at hlight
    have hl : light (r0 root) := hlight
    have hc : root = Classical.choose (hex (r0 root) hlight) := by
      simpa only [r,chooseRoot,dif_pos hl] using hroot
    rw [hc]
    exact (Classical.choose_spec (hex (r0 root) hlight)).2
  · intro root hroot hheavy
    exact heavy_card tau r hconst root hroot K hK (by omega)

end NikolovSegal.Equation47
