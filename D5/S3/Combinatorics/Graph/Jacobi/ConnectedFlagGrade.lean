/- GID: D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade
   mirror-E: none(waiver:actual-connected-flag-grade)
   anchors: []
   utility: none
   digest: Actual AS/IHX/CL relations preserve connected finite flag grades. -/

import D5.S3.Combinatorics.Graph.Jacobi.FlagEulerBridge
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Literal connectivity and population invariants for the source quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace D5.S3.Combinatorics.Graph.Jacobi

namespace FlagGraph

private def FlagReachable {F : Type} (G : FlagGraph F) (f g : F) : Prop :=
  G.incidence.Reachable (.inr f) (.inr g)

private theorem flagReach_refl {F : Type} (G : FlagGraph F) (f : F) :
    G.FlagReachable f f := SimpleGraph.Reachable.refl _

private theorem flagReach_next {F : Type} (G : FlagGraph F) (f : F) :
    G.FlagReachable f (G.next f) := by
  exact (show G.incidence.Adj (.inr f) (.inl (G.vertexOf f)) from rfl).reachable.trans
    (show G.incidence.Adj (.inl (G.vertexOf f)) (.inr (G.next f)) from
      G.vertexOf_next f).reachable

private theorem flagReach_edge {F : Type} (G : FlagGraph F) (f : F) :
    G.FlagReachable f (G.edge f) :=
  (show G.incidence.Adj (.inr f) (.inr (G.edge f)) from rfl).reachable

private theorem transfer_flagReach {F K : Type} (G : FlagGraph F) (H : FlagGraph K)
    (φ : F → K) (he : ∀ f, H.FlagReachable (φ f) (φ (G.edge f)))
    (hn : ∀ f, H.FlagReachable (φ f) (φ (G.next f)))
    {f g : F} (hfg : G.FlagReachable f g) : H.FlagReachable (φ f) (φ g) := by
  let Q : G.IncidenceVertex → Prop
    | .inl v => ∀ x, G.vertexOf x = v → H.FlagReachable (φ f) (φ x)
    | .inr x => H.FlagReachable (φ f) (φ x)
  have hstep : ∀ x y, G.incidence.Adj x y → Q x → Q y := by
    rintro (v | x) (w | y) hadj hx
    · exact False.elim hadj
    · exact hx y hadj
    · intro y hy
      have hv : G.vertexOf x = G.vertexOf y := hadj.trans hy.symm
      rcases (G.vertexOf_eq_iff x y).mp hv with rfl | rfl | rfl
      · exact hx
      · exact hx.trans (hn x)
      · exact (hx.trans (hn x)).trans (hn (G.next x))
    · exact hadj ▸ hx.trans (he x)
  have hall : ∀ {x y}, G.incidence.Walk x y → Q x → Q y := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (hstep x y h hx)
  exact hall hfg.some (H.flagReach_refl (φ f))

private theorem connected_of_flagReach {F : Type} (G : FlagGraph F) (f : F)
    (h : ∀ g, G.FlagReachable f g) : G.incidence.Connected := by
  letI : Nonempty G.IncidenceVertex := ⟨.inr f⟩
  have hall : ∀ x, G.incidence.Reachable (.inr f) x := by
    rintro (⟨s, g, rfl⟩ | g)
    · exact (h g).trans (show G.incidence.Adj (.inr g) (.inl (G.vertexOf g)) from rfl).reachable
    · exact h g
  exact SimpleGraph.Connected.mk (fun x y => (hall x).symm.trans (hall y))

private theorem connected_transfer {F K : Type} (G : FlagGraph F) (H : FlagGraph K)
    (φ : F → K) (hφ : Function.Surjective φ)
    (he : ∀ f, H.FlagReachable (φ f) (φ (G.edge f)))
    (hn : ∀ f, H.FlagReachable (φ f) (φ (G.next f)))
    (hc : G.incidence.Connected) : H.incidence.Connected := by
  obtain ⟨x⟩ := hc.nonempty
  have hne : Nonempty F := by
    rcases x with ⟨s, f, hf⟩ | f
    · exact ⟨f⟩
    · exact ⟨f⟩
  obtain ⟨f⟩ := hne
  apply H.connected_of_flagReach (φ f)
  intro g
  obtain ⟨g, rfl⟩ := hφ g
  exact G.transfer_flagReach H φ he hn (hc _ _)

private theorem flags_reachable_of_table {F : Type} (G : FlagGraph F)
    {n : ℕ} (φ : Fin n → F) (r : Fin n → Fin n) (a b : Fin n)
    (hn : ∀ i, G.next (φ i) = φ (r i))
    (hab : G.FlagReachable (φ a) (φ b))
    (hcover : ∀ i, i = a ∨ i = r a ∨ i = r (r a) ∨
      i = b ∨ i = r b ∨ i = r (r b)) :
    ∀ i j, G.FlagReachable (φ i) (φ j) := by
  have hstep : ∀ i, G.FlagReachable (φ i) (φ (r i)) := by
    intro i
    simpa only [hn i] using G.flagReach_next (φ i)
  have hall : ∀ i, G.FlagReachable (φ a) (φ i) := by
    intro i
    rcases hcover i with rfl | rfl | rfl | rfl | rfl | rfl
    · exact G.flagReach_refl _
    · exact hstep a
    · exact (hstep a).trans (hstep (r a))
    · exact hab
    · exact hab.trans (hstep b)
    · exact (hab.trans (hstep b)).trans (hstep (r b))
  exact fun i j => (hall i).symm.trans (hall j)

private theorem patch_connected_iff {F : Type} {G : FlagGraph F} {n : ℕ}
    (P : G.Patch n) (r : Fin n → Fin n)
    (hc : ∀ i, r (r (r i)) = i) (hne : ∀ i, r i ≠ i)
    (hold : ∀ i j, G.FlagReachable (P.flag i) (P.flag j))
    (hnew : ∀ i j, (FlagGraph.patch P r hc hne).FlagReachable (P.flag i) (P.flag j)) :
    (FlagGraph.patch P r hc hne).incidence.Connected ↔ G.incidence.Connected := by
  classical
  let H := FlagGraph.patch P r hc hne
  constructor
  · apply H.connected_transfer G id Function.surjective_id
    · exact G.flagReach_edge
    · intro f
      by_cases hf : ∃ i, P.flag i = f
      · obtain ⟨i, rfl⟩ := hf
        change G.FlagReachable (P.flag i) (FlagGraph.patchNext P r (P.flag i))
        rw [FlagGraph.patchNext_flag]
        exact hold i (r i)
      · change G.FlagReachable f (FlagGraph.patchNext P r f)
        rw [FlagGraph.patchNext_outside P r hf]
        exact G.flagReach_next f
  · apply G.connected_transfer H id Function.surjective_id
    · exact H.flagReach_edge
    · intro f
      by_cases hf : ∃ i, P.flag i = f
      · obtain ⟨i, rfl⟩ := hf
        rw [P.next_flag]
        exact hnew i (P.rotor i)
      · have hh : H.next f = G.next f := FlagGraph.patchNext_outside P r hf
        simpa only [hh, id_eq] using H.flagReach_next f

private theorem reverseVertex_connected {F : Type} {G : FlagGraph F} (v : G.Vertex) :
    (FlagGraph.reverseVertex v).incidence.Connected ↔ G.incidence.Connected := by
  apply patch_connected_iff
  · exact G.flags_reachable_of_table v.flag (finRotate 3) 0 0 v.next_flag
      (G.flagReach_refl _) (by decide)
  · apply (FlagGraph.reverseVertex v).flags_reachable_of_table v.flag (finRotate 3).symm 0 0
    · intro i
      exact FlagGraph.patchNext_flag _ _ i
    · exact (FlagGraph.reverseVertex v).flagReach_refl _
    · decide

private theorem socket_connected_I {F : Type} {G : FlagGraph F} (S : G.Socket) :
    S.branchI.incidence.Connected ↔ G.incidence.Connected := by
  apply patch_connected_iff
  · apply G.flags_reachable_of_table S.flag FlagGraph.socketX 0 1 S.next_flag
    · simpa only [S.central] using G.flagReach_edge (S.flag 0)
    · decide
  · apply S.branchI.flags_reachable_of_table S.flag FlagGraph.socketI 0 1
    · intro i
      exact FlagGraph.patchNext_flag _ _ i
    · exact (show S.branchI.incidence.Adj (.inr (S.flag 0)) (.inr (S.flag 1)) from
        S.central).reachable
    · decide

private theorem socket_connected_H {F : Type} {G : FlagGraph F} (S : G.Socket) :
    S.branchH.incidence.Connected ↔ G.incidence.Connected := by
  apply patch_connected_iff
  · apply G.flags_reachable_of_table S.flag FlagGraph.socketX 0 1 S.next_flag
    · simpa only [S.central] using G.flagReach_edge (S.flag 0)
    · decide
  · apply S.branchH.flags_reachable_of_table S.flag FlagGraph.socketH 0 1
    · intro i
      exact FlagGraph.patchNext_flag _ _ i
    · exact (show S.branchH.incidence.Adj (.inr (S.flag 0)) (.inr (S.flag 1)) from
        S.central).reachable
    · decide


private theorem iso_connected {F K : Type} {G : FlagGraph F} {H : FlagGraph K}
    (I : FlagIso G H) : H.incidence.Connected ↔ G.incidence.Connected := by
  let J : FlagIso H G :=
    { flagEquiv := I.flagEquiv.symm
      edge_eq f := by
        apply I.flagEquiv.injective
        simp only [Equiv.apply_symm_apply, ← I.edge_eq]
      next_eq f := by
        apply I.flagEquiv.injective
        simp only [Equiv.apply_symm_apply, ← I.next_eq]
      color_eq f := by simpa only [Equiv.apply_symm_apply] using
        (I.color_eq (I.flagEquiv.symm f)).symm }
  constructor
  · apply H.connected_transfer G J.flagEquiv J.flagEquiv.surjective
    · intro f
      simpa only [J.edge_eq] using G.flagReach_edge (J.flagEquiv f)
    · intro f
      simpa only [J.next_eq] using G.flagReach_next (J.flagEquiv f)
  · apply G.connected_transfer H I.flagEquiv I.flagEquiv.surjective
    · intro f
      simpa only [I.edge_eq] using H.flagReach_edge (I.flagEquiv f)
    · intro f
      simpa only [I.next_eq] using H.flagReach_next (I.flagEquiv f)

private theorem cl_connected {F : Type} {G : FlagGraph F} (L : G.AdjacentLegs) :
    (FlagGraph.exchangeColors L).incidence.Connected ↔ G.incidence.Connected := by
  constructor
  · apply (FlagGraph.exchangeColors L).connected_transfer G id Function.surjective_id
    · exact G.flagReach_edge
    · exact G.flagReach_next
  · apply G.connected_transfer (FlagGraph.exchangeColors L) id Function.surjective_id
    · exact (FlagGraph.exchangeColors L).flagReach_edge
    · exact (FlagGraph.exchangeColors L).flagReach_next


private theorem orbit_image {F K : Type} (G : FlagGraph F) (H : FlagGraph K)
    (e : F ≃ K) (hn : ∀ f, H.next (e f) = e (G.next f)) (f : F) :
    e '' G.orbitSet f = H.orbitSet (e f) := by
  ext x
  simp only [Set.mem_image, orbitSet, Set.mem_setOf_eq, hn]
  aesop

private noncomputable def orbitEquiv {F K : Type} (G : FlagGraph F) (H : FlagGraph K)
    (e : F ≃ K) (hn : ∀ f, H.next (e f) = e (G.next f)) :
    G.VertexOrbit ≃ H.VertexOrbit :=
  Equiv.subtypeEquiv e.setCongr (fun s => by
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨e f, (orbit_image G H e hn f).symm⟩
    · rintro ⟨f, hf⟩
      refine ⟨e.symm f, ?_⟩
      apply e.setCongr.injective
      change e '' G.orbitSet (e.symm f) = e '' s
      rw [orbit_image G H e hn, e.apply_symm_apply]
      exact hf)

private theorem patch_orbit_card {F : Type} [Finite F] {G : FlagGraph F} {n : ℕ}
    (P : G.Patch n) (r : Fin n → Fin n)
    (hc : ∀ i, r (r (r i)) = i) (hne : ∀ i, r i ≠ i)
    (q : Equiv.Perm (Fin n)) (hq : ∀ i, r (q i) = q (P.rotor i)) :
    Nat.card (FlagGraph.patch P r hc hne).VertexOrbit = Nat.card G.VertexOrbit := by
  classical
  let H := FlagGraph.patch P r hc hne
  let e := q.viaEmbedding P.flag
  have hn (f : F) : H.next (e f) = e (G.next f) := by
    by_cases hf : ∃ i, P.flag i = f
    · obtain ⟨i, rfl⟩ := hf
      rw [show e (P.flag i) = P.flag (q i) from q.viaEmbedding_apply P.flag i]
      change FlagGraph.patchNext P r (P.flag (q i)) = e (G.next (P.flag i))
      rw [FlagGraph.patchNext_flag, P.next_flag, hq]
      exact (q.viaEmbedding_apply P.flag (P.rotor i)).symm
    · have hf' : f ∉ Set.range P.flag := hf
      have hn' : G.next f ∉ Set.range P.flag := FlagGraph.next_outside P hf
      rw [show e f = f from q.viaEmbedding_apply_of_notMem P.flag f hf']
      change FlagGraph.patchNext P r f = e (G.next f)
      rw [FlagGraph.patchNext_outside P r hf]
      exact (q.viaEmbedding_apply_of_notMem P.flag (G.next f) hn').symm
  exact (Nat.card_congr (orbitEquiv G H e hn)).symm

private theorem patch_euler_genus {F : Type} [Finite F] {G : FlagGraph F} {n : ℕ}
    (P : G.Patch n) (r : Fin n → Fin n)
    (hc : ∀ i, r (r (r i)) = i) (hne : ∀ i, r i ≠ i)
    (q : Equiv.Perm (Fin n)) (hq : ∀ i, r (q i) = q (P.rotor i)) :
    (FlagGraph.patch P r hc hne).eulerGenus = G.eulerGenus := by
  unfold eulerGenus
  rw [patch_orbit_card P r hc hne q hq]
  rfl

private def reversePerm : Equiv.Perm (Fin 3) := Equiv.swap 1 2
private def socketPermI : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide
  right_inv := by decide
private def socketPermH : Equiv.Perm (Fin 6) := Equiv.swap 4 5

private theorem reverseVertex_euler_genus {F : Type} [Finite F] {G : FlagGraph F}
    (v : G.Vertex) : (FlagGraph.reverseVertex v).eulerGenus = G.eulerGenus := by
  apply patch_euler_genus _ _ _ _ reversePerm
  change ∀ i : Fin 3, (finRotate 3).symm (reversePerm i) = reversePerm (finRotate 3 i)
  decide

private theorem socketI_euler_genus {F : Type} [Finite F] {G : FlagGraph F}
    (S : G.Socket) : S.branchI.eulerGenus = G.eulerGenus := by
  apply patch_euler_genus _ _ _ _ socketPermI
  change ∀ i : Fin 6, socketI (socketPermI i) = socketPermI (socketX i)
  decide

private theorem socketH_euler_genus {F : Type} [Finite F] {G : FlagGraph F}
    (S : G.Socket) : S.branchH.eulerGenus = G.eulerGenus := by
  apply patch_euler_genus _ _ _ _ socketPermH
  change ∀ i : Fin 6, socketH (socketPermH i) = socketPermH (socketX i)
  decide

private theorem iso_euler_genus {F K : Type} [Finite F] [Finite K]
    {G : FlagGraph F} {H : FlagGraph K} (I : FlagIso G H) :
    G.eulerGenus = H.eulerGenus := by
  let e : G.edgePairGraph ≃g H.edgePairGraph :=
    { toEquiv := I.flagEquiv
      map_rel_iff' := by
        intro f g
        change H.edge (I.flagEquiv f) = I.flagEquiv g ↔ G.edge f = g
        rw [I.edge_eq]
        exact I.flagEquiv.injective.eq_iff }
  unfold eulerGenus
  rw [Nat.card_congr e.mapEdgeSet, Nat.card_congr (orbitEquiv G H I.flagEquiv I.next_eq)]

end FlagGraph


/-- Connectivity, original Euler genus, and every ordinary or anchor label
population. This is the exact connected source grade on the finite-flag carrier. -/
abbrev FlagGrade := Bool × ℕ × (LeafLabel → ℕ)

noncomputable def flagGrade (D : Diagram) : FlagGrade := by
  classical
  exact (decide D.graph.incidence.Connected, D.graph.eulerGenus,
    fun label => Nat.card {f : D.Flag // D.graph.color f = some label})

private theorem flagGrade_iso {F K : Type} [Finite F] [Finite K]
    {G : FlagGraph F} {H : FlagGraph K} (I : FlagIso G H) :
    flagGrade (pack G) = flagGrade (pack H) := by
  classical
  apply Prod.ext
  · exact Bool.decide_congr (FlagGraph.iso_connected I).symm
  · apply Prod.ext
    · exact FlagGraph.iso_euler_genus I
    · funext label
      apply Nat.card_congr
      exact Equiv.subtypeEquiv I.flagEquiv (fun f => by rw [I.color_eq])

private theorem flagGrade_as {F : Type} [Finite F] {G : FlagGraph F} (v : G.Vertex) :
    flagGrade (pack (FlagGraph.reverseVertex v)) = flagGrade (pack G) := by
  classical
  exact Prod.ext (Bool.decide_congr (FlagGraph.reverseVertex_connected v))
    (Prod.ext (FlagGraph.reverseVertex_euler_genus v) rfl)

private theorem flagGrade_I {F : Type} [Finite F] {G : FlagGraph F} (S : G.Socket) :
    flagGrade (pack S.branchI) = flagGrade (pack G) := by
  classical
  exact Prod.ext (Bool.decide_congr (FlagGraph.socket_connected_I S))
    (Prod.ext (FlagGraph.socketI_euler_genus S) rfl)

private theorem flagGrade_H {F : Type} [Finite F] {G : FlagGraph F} (S : G.Socket) :
    flagGrade (pack S.branchH) = flagGrade (pack G) := by
  classical
  exact Prod.ext (Bool.decide_congr (FlagGraph.socket_connected_H S))
    (Prod.ext (FlagGraph.socketH_euler_genus S) rfl)

private theorem exchange_swap {F : Type} {G : FlagGraph F} (L : G.AdjacentLegs)
    (f : F) :
    (FlagGraph.exchangeColors L).color ((Equiv.swap L.leftLeaf L.rightLeaf) f) = G.color f := by
  classical
  by_cases hl : f = L.leftLeaf
  · subst f
    simp [FlagGraph.exchangeColors, L.leaf_ne, Ne.symm L.leaf_ne]
  · by_cases hr : f = L.rightLeaf
    · subst f
      simp [FlagGraph.exchangeColors, L.leaf_ne, Ne.symm L.leaf_ne]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      simp only [FlagGraph.exchangeColors, ite_eq_right hl, ite_eq_right hr]

private theorem flagGrade_cl {F : Type} [Finite F] {G : FlagGraph F}
    (L : G.AdjacentLegs) : flagGrade (pack (FlagGraph.exchangeColors L)) = flagGrade (pack G) := by
  classical
  apply Prod.ext (Bool.decide_congr (FlagGraph.cl_connected L))
  apply Prod.ext
  · change (FlagGraph.exchangeColors L).eulerGenus = G.eulerGenus
    dsimp only [FlagGraph.eulerGenus, FlagGraph.edgePairGraph, FlagGraph.VertexOrbit,
      FlagGraph.orbitSet, FlagGraph.exchangeColors]
    rfl
  · funext label
    symm
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.swap L.leftLeaf L.rightLeaf) (fun f => by rw [exchange_swap L f])


abbrev GradeFiber (k : FlagGrade) := {D : Diagram // flagGrade D = k}
abbrev FreeGrade (k : FlagGrade) := GradeFiber k →₀ ℚ

noncomputable def gradeInclude (k : FlagGrade) : FreeGrade k →ₗ[ℚ] FreeDiagram :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

noncomputable def gradeProject (k : FlagGrade) : FreeDiagram →ₗ[ℚ] FreeGrade k :=
  Finsupp.lcomapDomain Subtype.val Subtype.val_injective

private noncomputable def gradeCut (k : FlagGrade) : FreeDiagram →ₗ[ℚ] FreeDiagram :=
  (gradeInclude k).comp (gradeProject k)

/-- The source relation generators are precisely literal actual relators
whose entire finite linear combination belongs to this grade fiber. -/
def GradeRelator (k : FlagGrade) (r : FreeGrade k) : Prop :=
  ActualRelator (gradeInclude k r)

noncomputable def gradeRelationSpace (k : FlagGrade) : Submodule ℚ (FreeGrade k) :=
  Submodule.span ℚ {r | GradeRelator k r}

abbrev GradedJacobiSpace (k : FlagGrade) := FreeGrade k ⧸ gradeRelationSpace k

private theorem gradeInclude_injective (k : FlagGrade) : Function.Injective (gradeInclude k) :=
  Finsupp.mapDomain_injective Subtype.val_injective

private theorem gradeProject_include (k : FlagGrade) (v : FreeGrade k) :
    gradeProject k (gradeInclude k v) = v :=
  Finsupp.leftInverse_lcomapDomain_mapDomain Subtype.val Subtype.val_injective v

private theorem gradeProject_basis (k : FlagGrade) (D : Diagram) :
    gradeProject k (basis D) =
      if h : flagGrade D = k then Finsupp.single ⟨D, h⟩ 1 else 0 := by
  classical
  by_cases h : flagGrade D = k
  · rw [dite_eq_left h]
    exact Finsupp.comapDomain_single Subtype.val (⟨D, h⟩ : GradeFiber k) 1
      Subtype.val_injective.injOn
  · rw [dite_eq_right h]
    apply Finsupp.comapDomain_single_of_notMem_range
    rintro ⟨d, hd⟩
    exact h (hd ▸ d.property)

private theorem gradeCut_basis (k : FlagGrade) (D : Diagram) :
    gradeCut k (basis D) = if flagGrade D = k then basis D else 0 := by
  classical
  rw [gradeCut, LinearMap.comp_apply, gradeProject_basis]
  split_ifs
  · exact Finsupp.mapDomain_single
  · exact map_zero _

private theorem gradeCut_actual (k : FlagGrade) {r : FreeDiagram} (hr : ActualRelator r) :
    gradeCut k r = 0 ∨ ActualRelator (gradeCut k r) := by
  classical
  cases hr with
  | @iso F K hF hK G H I =>
    have hg := (flagGrade_iso I).symm
    by_cases hk : flagGrade (pack G) = k
    · right
      simpa only [map_sub, gradeCut_basis, hg, ite_eq_left hk] using ActualRelator.iso I
    · left
      simp only [map_sub, gradeCut_basis, hg, ite_eq_right hk, sub_self]
  | @as F hF G v =>
    have hg := flagGrade_as v
    by_cases hk : flagGrade (pack G) = k
    · right
      simpa only [map_add, gradeCut_basis, hg, ite_eq_left hk] using ActualRelator.as v
    · left
      simp only [map_add, gradeCut_basis, hg, ite_eq_right hk, add_zero]
  | @ihx F hF G S =>
    have hi := flagGrade_I S
    have hh := flagGrade_H S
    by_cases hk : flagGrade (pack G) = k
    · right
      simpa only [map_add, map_sub, gradeCut_basis, hi, hh, ite_eq_left hk] using ActualRelator.ihx S
    · left
      simp only [map_add, map_sub, gradeCut_basis, hi, hh, ite_eq_right hk, sub_self, add_zero]
  | @cl F hF G L =>
    have hg := flagGrade_cl L
    by_cases hk : flagGrade (pack G) = k
    · right
      simpa only [map_sub, gradeCut_basis, hg, ite_eq_left hk] using ActualRelator.cl L
    · left
      simp only [map_sub, gradeCut_basis, hg, ite_eq_right hk, sub_self]

private theorem gradeInclude_relations (k : FlagGrade) :
    gradeRelationSpace k ≤ relationSpace.comap (gradeInclude k) := by
  apply Submodule.span_le.mpr
  intro r hr
  exact Submodule.subset_span hr

private theorem gradeProject_relations (k : FlagGrade) :
    relationSpace ≤ (gradeRelationSpace k).comap (gradeProject k) := by
  apply Submodule.span_le.mpr
  intro r hr
  change gradeProject k r ∈ gradeRelationSpace k
  rcases gradeCut_actual k hr with hz | ha
  · have hzero : gradeProject k r = 0 := (gradeInclude_injective k) (by
      simpa only [gradeCut, LinearMap.comp_apply, map_zero] using hz)
    rw [hzero]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ha

/-- Natural inclusion of the quotient by actual relators in one exact grade. -/
noncomputable def gradeInclusion (k : FlagGrade) : GradedJacobiSpace k →ₗ[ℚ] JacobiSpace :=
  (gradeRelationSpace k).mapQ relationSpace (gradeInclude k) (gradeInclude_relations k)

private noncomputable def gradeProjection (k : FlagGrade) : JacobiSpace →ₗ[ℚ] GradedJacobiSpace k :=
  relationSpace.mapQ (gradeRelationSpace k) (gradeProject k) (gradeProject_relations k)

private theorem gradeProjection_inclusion (k : FlagGrade) :
    Function.LeftInverse (gradeProjection k) (gradeInclusion k) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
    change (gradeRelationSpace k).mkQ (gradeProject k (gradeInclude k v)) =
      (gradeRelationSpace k).mkQ v
    rw [gradeProject_include]

/-- The connected fixed-genus/label-population source quotient embeds into the
actual all-diagram quotient. Taking a true connectivity coordinate gives
the connected source; the source genus is its actual Euler genus. -/
theorem gradeInclusion_injective (k : FlagGrade) : Function.Injective (gradeInclusion k) :=
  (gradeProjection_inclusion k).injective

end D5.S3.Combinatorics.Graph.Jacobi
