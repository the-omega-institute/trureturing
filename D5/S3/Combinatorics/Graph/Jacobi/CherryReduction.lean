/- GID: D5/S3/Combinatorics/Graph/Jacobi/CherryReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/CherryReduction
   mirror-E: none(waiver:actual-finite-flag-graft)
   anchors: []
   utility: none
   digest: Actual terminal cherry reduction by AS, IHX, ordinary CL, and a flag isomorphism. -/

import D5.S3.Combinatorics.Graph.Jacobi.CyclicFlagDiagram

/-! Actual terminal-cherry reduction using AS, IHX, and ordinary colored-leg relations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi


namespace FlagGraph

/-- An actual terminal ordinary cherry in the X resolution. The remaining
two ports and their entire exterior pairing are unrestricted. -/
structure Cherry {F : Type} (G : FlagGraph F) where
  socket : G.Socket
  leftLeaf : F
  rightLeaf : F
  leaf_ne : leftLeaf ≠ rightLeaf
  left_pair : G.edge (socket.flag 2) = leftLeaf
  right_pair : G.edge (socket.flag 5) = rightLeaf
  left_fixed : G.next leftLeaf = leftLeaf
  right_fixed : G.next rightLeaf = rightLeaf
  left_ordinary : ∃ c, G.color leftLeaf = some (.ordinary c)
  right_ordinary : ∃ c, G.color rightLeaf = some (.ordinary c)

namespace Cherry

private theorem fixed_ne_socket {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : G.next f = f) (i : Fin 6) :
    C.socket.flag i ≠ f := by
  intro h
  have he : socketX i = i := C.socket.flag.injective
    ((C.socket.next_flag i).symm.trans
      ((congrArg G.next h).trans (hf.trans h.symm)))
  have hn : socketX i ≠ i := by fin_cases i <;> decide
  exact hn he

private theorem flag_ne_left {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) : C.socket.flag i ≠ C.leftLeaf :=
  fixed_ne_socket C C.left_fixed i

private theorem flag_ne_right {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) : C.socket.flag i ≠ C.rightLeaf :=
  fixed_ne_socket C C.right_fixed i

private theorem left_outside {F : Type} {G : FlagGraph F} (C : G.Cherry) :
    ¬ ∃ i, C.socket.flag i = C.leftLeaf := by
  rintro ⟨i, h⟩
  exact C.flag_ne_left i h

private theorem right_outside {F : Type} {G : FlagGraph F} (C : G.Cherry) :
    ¬ ∃ i, C.socket.flag i = C.rightLeaf := by
  rintro ⟨i, h⟩
  exact C.flag_ne_right i h

private def socketPatch {F : Type} {G : FlagGraph F} (C : G.Cherry) : G.Patch 6 :=
  ⟨C.socket.flag, socketX, by decide, by decide, C.socket.next_flag⟩

private theorem i_next_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) :
    C.socket.branchI.next (C.socket.flag i) = C.socket.flag (socketI i) := by
  exact patchNext_flag C.socketPatch socketI i

private theorem h_next_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) :
    C.socket.branchH.next (C.socket.flag i) = C.socket.flag (socketH i) := by
  exact patchNext_flag C.socketPatch socketH i

private theorem i_next_outside {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : ¬ ∃ i, C.socket.flag i = f) :
    C.socket.branchI.next f = G.next f := by
  exact patchNext_outside C.socketPatch socketI hf

private theorem h_next_outside {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : ¬ ∃ i, C.socket.flag i = f) :
    C.socket.branchH.next f = G.next f := by
  exact patchNext_outside C.socketPatch socketH hf

private def insertionOrder : Fin 6 ↪ Fin 6 where
  toFun := ![2, 3, 0, 5, 1, 4]
  inj' := by decide

/-- Literal positive I insertions: (h1,h2,k+) and (h4,k-,h3). -/
noncomputable def adjacentI {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : C.socket.branchI.AdjacentLegs where
  flag := insertionOrder.trans C.socket.flag
  leftLeaf := C.leftLeaf
  rightLeaf := C.rightLeaf
  leaf_ne := C.leaf_ne
  next_first i := by
    change C.socket.branchI.next
      (C.socket.flag (insertionOrder (Fin.castAdd 3 i))) =
      C.socket.flag (insertionOrder (Fin.castAdd 3 (finRotate 3 i)))
    rw [C.i_next_flag]
    exact congrArg C.socket.flag (by fin_cases i <;> decide)
  next_second i := by
    change C.socket.branchI.next
      (C.socket.flag (insertionOrder (Fin.natAdd 3 i))) =
      C.socket.flag (insertionOrder (Fin.natAdd 3 (finRotate 3 i)))
    rw [C.i_next_flag]
    exact congrArg C.socket.flag (by fin_cases i <;> decide)
  first_pair := C.left_pair
  second_pair := C.right_pair
  connector := C.socket.central
  left_fixed := (C.i_next_outside C.left_outside).trans C.left_fixed
  right_fixed := (C.i_next_outside C.right_outside).trans C.right_fixed
  left_ordinary := C.left_ordinary
  right_ordinary := C.right_ordinary

private def hLeftOrder : Fin 3 ↪ Fin 6 where
  toFun := ![0, 2, 4]
  inj' := by decide

private def hRightOrder : Fin 3 ↪ Fin 6 where
  toFun := ![1, 3, 5]
  inj' := by decide

private noncomputable def hLeftVertex {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : C.socket.branchH.Vertex where
  flag := hLeftOrder.trans C.socket.flag
  next_flag i := by
    change C.socket.branchH.next (C.socket.flag (hLeftOrder i)) =
      C.socket.flag (hLeftOrder (finRotate 3 i))
    rw [C.h_next_flag]
    exact congrArg C.socket.flag (by fin_cases i <;> decide)

private def leftReversed : Fin 6 → Fin 6 := ![4, 3, 0, 5, 2, 1]
private def bothReversed : Fin 6 → Fin 6 := ![4, 5, 0, 1, 2, 3]

private theorem reverseLeft_next_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) :
    (reverseVertex C.hLeftVertex).next (C.socket.flag i) =
      C.socket.flag (leftReversed i) := by
  classical
  change patchNext _ _ (C.socket.flag i) = _
  by_cases hi : ∃ j, hLeftOrder j = i
  · obtain ⟨j, rfl⟩ := hi
    change patchNext _ _ (C.hLeftVertex.flag j) = _
    rw [patchNext_flag]
    change C.socket.flag (hLeftOrder ((finRotate 3).symm j)) =
      C.socket.flag (leftReversed (hLeftOrder j))
    exact congrArg C.socket.flag (by fin_cases j <;> decide)
  · have hf : ¬ ∃ j, C.hLeftVertex.flag j = C.socket.flag i := by
      rintro ⟨j, hj⟩
      change C.socket.flag (hLeftOrder j) = C.socket.flag i at hj
      exact hi ⟨j, C.socket.flag.injective hj⟩
    rw [patchNext_outside _ _ hf, C.h_next_flag]
    apply congrArg C.socket.flag
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨1, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl

private theorem reverseLeft_next_outside {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : ¬ ∃ i, C.socket.flag i = f) :
    (reverseVertex C.hLeftVertex).next f = G.next f := by
  have hl : ¬ ∃ j, C.hLeftVertex.flag j = f := by
    rintro ⟨j, hj⟩
    change C.socket.flag (hLeftOrder j) = f at hj
    exact hf ⟨hLeftOrder j, hj⟩
  change patchNext _ _ f = _
  rw [patchNext_outside _ _ hl, C.h_next_outside hf]

private noncomputable def hRightVertex {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : (reverseVertex C.hLeftVertex).Vertex where
  flag := hRightOrder.trans C.socket.flag
  next_flag i := by
    change (reverseVertex C.hLeftVertex).next (C.socket.flag (hRightOrder i)) =
      C.socket.flag (hRightOrder (finRotate 3 i))
    rw [C.reverseLeft_next_flag]
    exact congrArg C.socket.flag (by fin_cases i <;> decide)

private noncomputable def reverseH {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : FlagGraph F := reverseVertex C.hRightVertex

private theorem reverseH_next_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) :
    C.reverseH.next (C.socket.flag i) = C.socket.flag (bothReversed i) := by
  classical
  change patchNext _ _ (C.socket.flag i) = _
  by_cases hi : ∃ j, hRightOrder j = i
  · obtain ⟨j, rfl⟩ := hi
    change patchNext _ _ (C.hRightVertex.flag j) = _
    rw [patchNext_flag]
    change C.socket.flag (hRightOrder ((finRotate 3).symm j)) =
      C.socket.flag (bothReversed (hRightOrder j))
    exact congrArg C.socket.flag (by fin_cases j <;> decide)
  · have hf : ¬ ∃ j, C.hRightVertex.flag j = C.socket.flag i := by
      rintro ⟨j, hj⟩
      change C.socket.flag (hRightOrder j) = C.socket.flag i at hj
      exact hi ⟨j, C.socket.flag.injective hj⟩
    rw [patchNext_outside _ _ hf, C.reverseLeft_next_flag]
    apply congrArg C.socket.flag
    fin_cases i
    · rfl
    · exact False.elim (hi ⟨0, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨1, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨2, rfl⟩)

private theorem reverseH_next_outside {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : ¬ ∃ i, C.socket.flag i = f) :
    C.reverseH.next f = G.next f := by
  have hr : ¬ ∃ j, C.hRightVertex.flag j = f := by
    rintro ⟨j, hj⟩
    change C.socket.flag (hRightOrder j) = f at hj
    exact hf ⟨hRightOrder j, hj⟩
  change patchNext _ _ f = _
  rw [patchNext_outside _ _ hr, C.reverseLeft_next_outside hf]

open Classical in
private noncomputable def permutation {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : F ≃ F :=
  ((Equiv.swap (C.socket.flag 0) (C.socket.flag 1)).trans
    (Equiv.swap (C.socket.flag 2) (C.socket.flag 5))).trans
    (Equiv.swap C.leftLeaf C.rightLeaf)

private def socketPermutation : Fin 6 → Fin 6 := ![1, 0, 5, 3, 4, 2]

private theorem permutation_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) :
    C.permutation (C.socket.flag i) = C.socket.flag (socketPermutation i) := by
  classical
  fin_cases i <;>
    simp [permutation, Equiv.trans_apply, Equiv.swap_apply_def,
      C.socket.flag.injective.eq_iff, C.flag_ne_left, C.flag_ne_right,
      socketPermutation]

private theorem permutation_left {F : Type} {G : FlagGraph F} (C : G.Cherry) :
    C.permutation C.leftLeaf = C.rightLeaf := by
  classical
  have hn : ∀ i, C.leftLeaf ≠ C.socket.flag i := fun i => (C.flag_ne_left i).symm
  simp [permutation, Equiv.trans_apply, Equiv.swap_apply_def, hn]

private theorem permutation_right {F : Type} {G : FlagGraph F} (C : G.Cherry) :
    C.permutation C.rightLeaf = C.leftLeaf := by
  classical
  have hn : ∀ i, C.rightLeaf ≠ C.socket.flag i := fun i => (C.flag_ne_right i).symm
  simp [permutation, Equiv.trans_apply, Equiv.swap_apply_def, hn]

private theorem permutation_outside {F : Type} {G : FlagGraph F}
    (C : G.Cherry) {f : F} (hf : ¬ ∃ i, C.socket.flag i = f)
    (hl : f ≠ C.leftLeaf) (hr : f ≠ C.rightLeaf) : C.permutation f = f := by
  classical
  have hn : ∀ i, f ≠ C.socket.flag i := fun i h => hf ⟨i, h.symm⟩
  simp [permutation, Equiv.trans_apply, Equiv.swap_apply_def, hn, hl, hr]

private theorem disjoint_swaps {F : Type} [DecidableEq F] (a b c d f : F)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b (Equiv.swap c d f) =
      Equiv.swap c d (Equiv.swap a b f) := by
  classical
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  by_cases ha : f = a
  · subst f; simp_all [Equiv.swap_apply_def]
  · by_cases hb : f = b
    · subst f; simp_all [Equiv.swap_apply_def]
    · by_cases hc : f = c
      · subst f; simp_all [Equiv.swap_apply_def]
      · by_cases hd : f = d
        · subst f; simp_all [Equiv.swap_apply_def]
        · simp [Equiv.swap_apply_def, ha, hb, hc, hd]

private theorem permutation_edge {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (f : F) :
    G.edge (C.permutation f) = C.permutation (G.edge f) := by
  classical
  have h1 : G.edge (C.socket.flag 1) = C.socket.flag 0 := by
    simpa only [C.socket.central] using G.edge_involutive (C.socket.flag 0)
  have hl : G.edge C.leftLeaf = C.socket.flag 2 := by
    simpa only [C.left_pair] using G.edge_involutive (C.socket.flag 2)
  have hr : G.edge C.rightLeaf = C.socket.flag 5 := by
    simpa only [C.right_pair] using G.edge_involutive (C.socket.flag 5)
  simp only [permutation, Equiv.trans_apply,
    ← G.edge_involutive.injective.swap_apply, C.socket.central, h1,
    C.left_pair, C.right_pair, hl, hr, Equiv.swap_comm (C.socket.flag 1) (C.socket.flag 0)]
  exact disjoint_swaps (C.socket.flag 2) (C.socket.flag 5)
    C.leftLeaf C.rightLeaf _ (C.flag_ne_left 2) (C.flag_ne_right 2)
    (C.flag_ne_left 5) (C.flag_ne_right 5)

private theorem color_flag {F : Type} {G : FlagGraph F}
    (C : G.Cherry) (i : Fin 6) : G.color (C.socket.flag i) = none := by
  apply (G.color_none_iff _).mpr
  rw [C.socket.next_flag]
  intro h
  have hi := C.socket.flag.injective h
  fin_cases i <;> simp [socketX] at hi

/-- The CL exchange in I is isomorphic to H with both actual vertex
cycles reversed. The equivalence swaps k+/k-, h1/h4, and the two leaves. -/
private noncomputable def exchangedIsoReverseH {F : Type} {G : FlagGraph F}
    (C : G.Cherry) : FlagIso (exchangeColors C.adjacentI) C.reverseH where
  flagEquiv := C.permutation
  edge_eq f := by
    change G.edge (C.permutation f) = C.permutation (G.edge f)
    exact C.permutation_edge f
  next_eq f := by
    classical
    change C.reverseH.next (C.permutation f) = C.permutation (C.socket.branchI.next f)
    by_cases hf : ∃ i, C.socket.flag i = f
    · obtain ⟨i, rfl⟩ := hf
      rw [C.permutation_flag, C.reverseH_next_flag, C.i_next_flag, C.permutation_flag]
      congr 1
      fin_cases i <;> decide
    · by_cases hl : f = C.leftLeaf
      · subst f
        rw [C.permutation_left, C.reverseH_next_outside C.right_outside,
          C.right_fixed, C.i_next_outside C.left_outside, C.left_fixed,
          C.permutation_left]
      · by_cases hr : f = C.rightLeaf
        · subst f
          rw [C.permutation_right, C.reverseH_next_outside C.left_outside,
            C.left_fixed, C.i_next_outside C.right_outside, C.right_fixed,
            C.permutation_right]
        · have hn : ¬ ∃ i, C.socket.flag i = G.next f := next_outside C.socketPatch hf
          have hnl : G.next f ≠ C.leftLeaf := by
            intro h
            exact hl (G.next_injective (h.trans C.left_fixed.symm))
          have hnr : G.next f ≠ C.rightLeaf := by
            intro h
            exact hr (G.next_injective (h.trans C.right_fixed.symm))
          rw [C.permutation_outside hf hl hr, C.reverseH_next_outside hf,
            C.i_next_outside hf, C.permutation_outside hn hnl hnr]
  color_eq f := by
    classical
    change G.color (C.permutation f) =
      if f = C.leftLeaf then G.color C.rightLeaf else
        if f = C.rightLeaf then G.color C.leftLeaf else G.color f
    by_cases hf : ∃ i, C.socket.flag i = f
    · obtain ⟨i, rfl⟩ := hf
      rw [C.permutation_flag]
      simp [C.color_flag, C.flag_ne_left, C.flag_ne_right]
    · by_cases hl : f = C.leftLeaf
      · subst f
        simp [C.permutation_left]
      · by_cases hr : f = C.rightLeaf
        · subst f
          simp [C.permutation_right, C.leaf_ne.symm]
        · rw [C.permutation_outside hf hl hr, ite_eq_right hl, ite_eq_right hr]

end Cherry
end FlagGraph

/-- An actual ordinary terminal cherry is zero by geometric IHX, ordinary
CL, the explicit flag isomorphism, and two genuine vertex AS relations. -/
theorem cherry_zero {F : Type} [Finite F] (G : FlagGraph F) (C : G.Cherry) :
    classOf G = 0 := by
  have hcl : classOf C.socket.branchI = classOf (FlagGraph.exchangeColors C.adjacentI) := by
    apply sub_eq_zero.mp
    simpa only [classOf, map_sub] using
      actual_relator_zero _ (ActualRelator.cl C.adjacentI)
  have hiso : classOf (FlagGraph.exchangeColors C.adjacentI) =
      classOf C.reverseH := by
    apply sub_eq_zero.mp
    simpa only [classOf, map_sub] using
      actual_relator_zero _ (ActualRelator.iso C.exchangedIsoReverseH)
  have ha : classOf C.socket.branchH + classOf (FlagGraph.reverseVertex C.hLeftVertex) = 0 := by
    simpa only [classOf, map_add] using
      actual_relator_zero _ (ActualRelator.as C.hLeftVertex)
  have hb : classOf (FlagGraph.reverseVertex C.hLeftVertex) + classOf C.reverseH = 0 := by
    simpa only [classOf, map_add, FlagGraph.Cherry.reverseH] using
      actual_relator_zero _ (ActualRelator.as C.hRightVertex)
  have hh : classOf C.reverseH = classOf C.socket.branchH := by
    apply add_left_cancel (a := classOf (FlagGraph.reverseVertex C.hLeftVertex))
    exact hb.trans (by simpa only [add_comm] using ha.symm)
  have hihx : classOf C.socket.branchI - classOf C.socket.branchH + classOf G = 0 := by
    simpa only [classOf, map_add, map_sub] using
      actual_relator_zero _ (ActualRelator.ihx C.socket)
  rw [hcl.trans (hiso.trans hh), sub_self, zero_add] at hihx
  exact hihx

end D5.S3.Combinatorics.Graph.Jacobi
