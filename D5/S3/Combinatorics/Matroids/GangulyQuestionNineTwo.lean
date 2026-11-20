/- GID: D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/GangulyQuestionNineTwo
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.claim; result=D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.result; claim=D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.claim
   digest: Representability fails under both 1-sums and bridge joins in characteristic two. -/

/- admission_basis: open-problem-resolution (#32367; Refuted)
   question_nine_two: proof_shape: content. The two field-independent determinant
   samples certify the factor basis tests by interpolation. The endpoint gains
   contradict triangle parity, and the unstarred bridge transfers the obstruction.
   result: proof_shape: content after inlining the same-module proof. Each branch
   uses the corresponding obstruction and both factor representations.
   Direct frozen dependencies of these two proof terms are empty. The graph
   definitions use the repository's DirectedMultigraph from EssentialWordRealization.
   The finite Chow and determinant checks support this refutation. -/

import D5.S3.ConceptDynamics.Coding.EssentialWordRealization
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The source definitions are Ganguly, *Representability of Graphical Symplectic
Matroids*, arXiv:2611.01241v2, Definitions 2.9–2.10 and Question 9.2.
A signed selection is a partial marking of the edge IDs. Components use both
orientations of each selected edge and include isolated vertices. Cycles are
nonempty connected 2-regular edge sets, with both incidences counted at a loop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.GangulyQuestionNineTwo

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open scoped BigOperators

private abbrev Marking (E : Type*) := E → Option Bool

section Graph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The spanning subgraph forgets the signs and retains each selected edge ID. -/
private def selected (s : Marking E) : Finset E :=
  Finset.univ.filter fun e => (s e).isSome

/-- Two vertices are in the same component exactly if no cut separates them. -/
private def Joined (G : DirectedMultigraph V E) (S : Finset E) (v w : V) : Prop :=
  ∀ side : V → Bool,
    (∀ e ∈ S, side (G.source e) = side (G.target e)) → side v = side w

private instance joinedDecidable (G : DirectedMultigraph V E) (S : Finset E) (v w : V) :
    Decidable (Joined G S v w) := by
  unfold Joined
  infer_instance

private def componentVertices (G : DirectedMultigraph V E) (S : Finset E) (v : V) : Finset V :=
  Finset.univ.filter (Joined G S v)

private def componentEdges (G : DirectedMultigraph V E) (S : Finset E) (v : V) : Finset E :=
  S.filter fun e => Joined G S v (G.source e)

private def incidentVertices (G : DirectedMultigraph V E) (S : Finset E) : Finset V :=
  Finset.univ.filter fun v => ∃ e ∈ S, G.source e = v ∨ G.target e = v

private def degree (G : DirectedMultigraph V E) (S : Finset E) (v : V) : ℕ :=
  (S.filter fun e => G.source e = v).card + (S.filter fun e => G.target e = v).card

private def IsCycle (G : DirectedMultigraph V E) (S : Finset E) : Prop :=
  S.Nonempty ∧
    (∀ v ∈ incidentVertices G S, degree G S v = 2) ∧
    (∀ v ∈ incidentVertices G S, ∀ w ∈ incidentVertices G S, Joined G S v w)

private instance cycleDecidable (G : DirectedMultigraph V E) (S : Finset E) : Decidable (IsCycle G S) := by
  unfold IsCycle
  infer_instance

private def componentCycles (G : DirectedMultigraph V E) (S : Finset E) (v : V) :
    Finset (Finset E) :=
  (componentEdges G S v).powerset.filter (IsCycle G)

private def Good (G : DirectedMultigraph V E) (s : Marking E) (v : V) : Prop :=
  let S := selected s
  let C := componentCycles G S v
  let nv := (componentVertices G S v).card
  let ne := (componentEdges G S v).card
  (ne + 1 = nv ∧ C = ∅) ∨
    (ne = nv ∧ C.card = 1 ∧ ∀ cycle ∈ C, (cycle.filter fun e => s e = some true).card % 2 = 1)

private instance goodDecidable (G : DirectedMultigraph V E) (s : Marking E) (v : V) :
    Decidable (Good G s v) := by
  unfold Good
  infer_instance

private def Chow (G : DirectedMultigraph V E) (s : Marking E) : Prop :=
  ∀ v, Good G s v

private instance chowDecidable (G : DirectedMultigraph V E) (s : Marking E) : Decidable (Chow G s) := by
  unfold Chow
  infer_instance

/-- The rank of the graphical symplectic matroid is the largest good size. -/
private def ChowRank (G : DirectedMultigraph V E) (k : ℕ) : Prop :=
  (∃ s : Marking E, Chow G s ∧ (selected s).card = k) ∧
    ∀ s : Marking E, Chow G s → (selected s).card ≤ k

/-- Assemble the signed subset from distinct edge IDs and their chosen marks. -/
private def fromColumns {k : ℕ} (e : Fin k → E) (m : Fin k → Bool) : Marking E :=
  fun a =>
    if ∃ i, e i = a ∧ m i = true then some true
    else if ∃ i, e i = a then some false
    else none

end Graph


private theorem chow_card_bound {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    {G : DirectedMultigraph (Fin n) E} {s : Marking E} (hs : Chow G s) :
    (selected s).card ≤ n := by
  let S := selected s
  let root (v : Fin n) := (componentVertices G S v).min'
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩⟩
  have root_joined (v : Fin n) : Joined G S v (root v) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
  have root_eq (v w : Fin n) : root v = root w ↔ Joined G S v w := by
    constructor
    · intro h c hc
      exact (root_joined v c hc).trans (h ▸ root_joined w c hc).symm
    · intro h
      have hcomp : componentVertices G S v = componentVertices G S w := by
        ext u
        simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hv c hc => (h c hc).symm.trans (hv c hc),
          fun hw c hc => (h c hc).trans (hw c hc)⟩
      unfold root
      congr 1
  have edge_count (v : Fin n) : (componentEdges G S v).card ≤ (componentVertices G S v).card := by
    have h := hs v
    change ((_ + 1 = _ ∧ _) ∨ (_ = _ ∧ _)) at h
    rcases h with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact Nat.le_of_succ_le (le_of_eq ht)
    · exact le_of_eq ht
  calc
    S.card = ∑ r : Fin n, (S.filter fun e => root (G.source e) = r).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ r : Fin n, ((Finset.univ : Finset (Fin n)).filter fun v => root v = r).card := by
      apply Finset.sum_le_sum
      intro r _
      by_cases h : ∃ e ∈ S, root (G.source e) = r
      · obtain ⟨e, _, rfl⟩ := h
        have symm (u v : Fin n) : Joined G S u v ↔ Joined G S v u :=
          ⟨fun h c hc => (h c hc).symm, fun h c hc => (h c hc).symm⟩
        simp only [root_eq]
        have heq : (S.filter fun e' => Joined G S (G.source e') (G.source e)) =
            componentEdges G S (G.source e) := by
          ext e'
          simp only [componentEdges, Finset.mem_filter, symm (G.source e') (G.source e)]
        have hveq : (Finset.univ.filter fun v => Joined G S v (G.source e)) =
            componentVertices G S (G.source e) := by
          ext v
          simp only [componentVertices, Finset.mem_filter, symm v (G.source e)]
        rw [heq, hveq]
        exact edge_count (G.source e)
      · have hEmpty : (S.filter fun e => root (G.source e) = r) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he
          exact h ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
        simp [hEmpty]
    _ = n := by
      rw [← Finset.card_eq_sum_card_fiberwise (fun (_ : Fin n) _ => Finset.mem_univ _)]
      simp

private theorem chow_rank_of_basis {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    {G : DirectedMultigraph (Fin n) E} (h : ∃ s : Marking E, Chow G s ∧ (selected s).card = n) :
    ChowRank G n :=
  ⟨h, fun _ hs => chow_card_bound hs⟩

section Representation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (F : Type*) [Field F]

private abbrev PairedMatrix (k : ℕ) := Matrix (Fin k) (E × Bool) F

private def selectedMatrix {k : ℕ} (H : PairedMatrix (E := E) F k)
    (e : Fin k → E) (m : Fin k → Bool) : Matrix (Fin k) (Fin k) F :=
  fun r i => H r (e i, m i)

/-- The entries of `XZᵀ - ZXᵀ` vanish. -/
private def Isotropic {k : ℕ} (H : PairedMatrix (E := E) F k) : Prop :=
  ∀ i j, ∑ e : E, (H i (e, false) * H j (e, true) - H i (e, true) * H j (e, false)) = 0

/-- Definition 2.9, with admissible column sets listed in an arbitrary order. -/
private structure Represents (G : DirectedMultigraph V E) (k : ℕ)
    (H : PairedMatrix (E := E) F k) : Prop where
  rowRank : LinearIndependent F H
  isotropic : Isotropic F H
  bases : ∀ (e : Fin k → E) (m : Fin k → Bool), Function.Injective e →
    ((selectedMatrix F H e m).det ≠ 0 ↔ Chow G (fromColumns e m))

def Representable (G : DirectedMultigraph V E) : Prop :=
  ∃ k, ChowRank G k ∧ ∃ H : PairedMatrix (E := E) F k, Represents F G k H

end Representation

/-- The triangle edge IDs are 0, 1, 2, followed by the loops at vertices 0 and 1. -/
def factorOne : DirectedMultigraph (Fin 3) (Fin 5) :=
  ⟨![0, 1, 2, 0, 1], ![1, 2, 0, 0, 1]⟩

def factorTwo : DirectedMultigraph (Fin 1) (Fin 1) :=
  ⟨![0], ![0]⟩

/-- Identify the two chosen vertices, preserving all edge IDs.
The right vertex `w` is exchanged with the last label before gluing. -/
def oneSumAt {n m l r : ℕ} (G : DirectedMultigraph (Fin n) (Fin l))
    (K : DirectedMultigraph (Fin (m + 1)) (Fin r)) (v : Fin n) (w : Fin (m + 1)) :
    DirectedMultigraph (Fin (n + m)) (Fin (l + r)) :=
  let rightVertex (j : Fin (m + 1)) : Fin (n + m) :=
    Fin.lastCases (Fin.castAdd m v) (Fin.natAdd n) (Equiv.swap w (Fin.last m) j)
  ⟨Fin.append (Fin.castAdd m ∘ G.source) (rightVertex ∘ K.source),
   Fin.append (Fin.castAdd m ∘ G.target) (rightVertex ∘ K.target)⟩

/-- Retain the disjoint rooted factors and append a fresh edge between their roots. -/
def bridgeAt {n m l r : ℕ} (G : DirectedMultigraph (Fin n) (Fin l))
    (K : DirectedMultigraph (Fin (m + 1)) (Fin r)) (v : Fin n) (w : Fin (m + 1)) :
    DirectedMultigraph (Fin (n + (m + 1))) (Fin (l + r + 1)) :=
  ⟨Fin.append
      (Fin.append (Fin.castAdd (m + 1) ∘ G.source) (Fin.natAdd n ∘ K.source))
      ![Fin.castAdd (m + 1) v],
   Fin.append
      (Fin.append (Fin.castAdd (m + 1) ∘ G.target) (Fin.natAdd n ∘ K.target))
      ![Fin.natAdd n w]⟩

def oneSum : DirectedMultigraph (Fin 3) (Fin 6) :=
  oneSumAt factorOne factorTwo 2 0

def bridgeJoin : DirectedMultigraph (Fin 4) (Fin 7) :=
  bridgeAt factorOne factorTwo 2 0

/-- Preservation by an operation on all pairs of finite rooted multigraphs. -/
private def Preserves (F : Type*) [Field F] (extra : ℕ)
    (join : ∀ {n m l r : ℕ}, DirectedMultigraph (Fin n) (Fin l) →
      DirectedMultigraph (Fin (m + 1)) (Fin r) → Fin n → Fin (m + 1) →
      DirectedMultigraph (Fin (n + m + extra)) (Fin (l + r + extra))) : Prop :=
  ∀ {n m l r : ℕ} (G : DirectedMultigraph (Fin n) (Fin l))
    (K : DirectedMultigraph (Fin (m + 1)) (Fin r)) (v : Fin n) (w : Fin (m + 1)),
    Representable F G → Representable F K → Representable F (join G K v w)

/-- An affirmative answer to either closure question over some qualifying field. -/
def claim : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : CharP F 2),
    Nonempty (Fin 4 ↪ F) ∧ (Preserves F 0 @oneSumAt ∨ Preserves F 1 @bridgeAt)


section Factors

variable {R : Type*} [Zero R] [One R]

/-- The supplied rank-three matrix, with paired column indices. -/
private def factorMatrix₁ (a : R) : Matrix (Fin 3) (Fin 5 × Bool) R :=
  fun i p =>
    if p.2 then
      if p.1 = 4 ∧ i = 0 then a
      else (![![1, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 1, 1]]) i p.1
    else (![![1, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 0, 0, 0]]) i p.1

/-- The supplied rank-one matrix `[0 | 1]`. -/
private def factorMatrix₂ : Matrix (Fin 1) (Fin 1 × Bool) R :=
  fun _ p => if p.2 then 1 else 0

variable (F : Type*) [Field F] [CharP F 2]

private theorem factorOne_isotropic (a : F) : Isotropic F (factorMatrix₁ a) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [factorMatrix₁, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
private theorem factorTwo_isotropic : Isotropic F (factorMatrix₂ (R := F)) := by
  intro i j
  simp [factorMatrix₂]

omit [CharP F 2] in
private theorem rowRank_of_det {E : Type*} {k : ℕ} {H : PairedMatrix (E := E) F k}
    {e : Fin k → E} {m : Fin k → Bool} (h : (selectedMatrix F H e m).det ≠ 0) :
    LinearIndependent F H := by
  have hr : LinearIndependent F (selectedMatrix F H e m).row :=
    Matrix.linearIndependent_row_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h.isUnit)
  let project : ((E × Bool) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun v i => v (e i, m i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp project hr

omit [CharP F 2] in
private theorem factorOne_nonzero_minor (a : F) :
    (selectedMatrix F (factorMatrix₁ a) ![0, 1, 3] ![false, false, true]).det = 1 := by
  simp [Matrix.det_fin_three, selectedMatrix, factorMatrix₁]

omit [CharP F 2] in
private theorem factorTwo_nonzero_minor :
    (selectedMatrix F factorMatrix₂ ![0] ![true]).det = 1 := by
  simp [selectedMatrix, factorMatrix₂]

private theorem factorOne_rank : ChowRank factorOne 3 := by
  apply chow_rank_of_basis
  refine ⟨fromColumns ![0, 1, 3] ![false, false, true], ?_⟩
  decide +kernel
private theorem factorTwo_rank : ChowRank factorTwo 1 := by
  apply chow_rank_of_basis
  refine ⟨fromColumns ![0] ![true], ?_⟩
  decide +kernel

omit [CharP F 2] in
private theorem factorTwo_bases (e : Fin 1 → Fin 1) (m : Fin 1 → Bool) :
    (selectedMatrix F factorMatrix₂ e m).det ≠ 0 ↔ Chow factorTwo (fromColumns e m) := by
  have he : e = ![0] := Subsingleton.elim _ _
  subst e
  have hm : m = ![m 0] := by
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hm]
  cases m 0
  · have hg : ¬ Chow factorTwo (fromColumns ![0] ![false]) := by decide +kernel
    simp [selectedMatrix, factorMatrix₂, hg]
  · have hg : Chow factorTwo (fromColumns ![0] ![true]) := by decide +kernel
    simp [selectedMatrix, factorMatrix₂, hg]

omit [CharP F 2] in
private theorem factorOne_det_affine (a : F) (e : Fin 3 → Fin 5) (m : Fin 3 → Bool)
    (he : Function.Injective e) :
    (selectedMatrix F (factorMatrix₁ a) e m).det =
      (selectedMatrix F (factorMatrix₁ 0) e m).det +
      a * ((selectedMatrix F (factorMatrix₁ 1) e m).det -
           (selectedMatrix F (factorMatrix₁ 0) e m).det) := by
  by_cases h : ∃ i, e i = 4 ∧ m i = true
  · obtain ⟨j, hj, hm⟩ := h
    let A := selectedMatrix F (factorMatrix₁ 0) e m
    let u : Fin 3 → F := fun i => if i = 0 then 1 else 0
    have update (z : F) :
        selectedMatrix F (factorMatrix₁ z) e m =
          A.updateCol j ((fun r => A r j) + z • u) := by
      ext i k
      by_cases hk : k = j
      · subst k
        by_cases hi : i = 0 <;>
          simp [A, u, selectedMatrix, factorMatrix₁, hi, hj, hm]
      · have hne : e k ≠ 4 := fun hh => hk (he (hh.trans hj.symm))
        simp [A, selectedMatrix, factorMatrix₁, hk, hne]
    have df (z : F) :
        (selectedMatrix F (factorMatrix₁ z) e m).det = A.det + z * (A.updateCol j u).det := by
      rw [update, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
    rw [df a, df 1]
    change _ = A.det + a * (_ - A.det)
    ring
  · have const (z : F) :
        selectedMatrix F (factorMatrix₁ z) e m = selectedMatrix F (factorMatrix₁ 0) e m := by
      ext i j
      cases hm : m j
      · simp [selectedMatrix, factorMatrix₁, hm]
      · have hne : e j ≠ 4 := fun hh => h ⟨j, hh, hm⟩
        simp [selectedMatrix, factorMatrix₁, hm, hne]
    rw [const a, const 1]
    ring

private def detThree {K : Type*} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) : K :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
  - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
  + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

private theorem factorOne_det_samples :
    ∀ (e : Fin 3 → Fin 5) (m : Fin 3 → Bool), Function.Injective e →
      ((detThree (selectedMatrix (ZMod 2) (factorMatrix₁ 0) e m) ≠ 0 ∨
        detThree (selectedMatrix (ZMod 2) (factorMatrix₁ 1) e m) ≠ 0) ↔
        Chow factorOne (fromColumns e m)) := by decide +kernel

private theorem factorOne_det_cast (b : ZMod 2) (e : Fin 3 → Fin 5) (m : Fin 3 → Bool) :
    let cast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
    (selectedMatrix F (factorMatrix₁ (cast b)) e m).det =
      cast (selectedMatrix (ZMod 2) (factorMatrix₁ b) e m).det := by
  let cast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  change _ = cast _
  rw [RingHom.map_det]
  congr 1
  ext i j
  generalize he : e j = a
  fin_cases i <;> fin_cases a <;> cases hm : m j <;>
    simp [selectedMatrix, factorMatrix₁, he, hm, cast]

private theorem factorOne_bases (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (e : Fin 3 → Fin 5) (m : Fin 3 → Bool) (he : Function.Injective e) :
    (selectedMatrix F (factorMatrix₁ a) e m).det ≠ 0 ↔ Chow factorOne (fromColumns e m) := by
  let cast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let d₀ := (selectedMatrix (ZMod 2) (factorMatrix₁ 0) e m).det
  let d₁ := (selectedMatrix (ZMod 2) (factorMatrix₁ 1) e m).det
  have h₀ : (selectedMatrix F (factorMatrix₁ 0) e m).det = cast d₀ := by
    simpa [cast, d₀] using factorOne_det_cast F 0 e m
  have h₁ : (selectedMatrix F (factorMatrix₁ 1) e m).det = cast d₁ := by
    simpa [cast, d₁] using factorOne_det_cast F 1 e m
  have hsample : (d₀ ≠ 0 ∨ d₁ ≠ 0) ↔ Chow factorOne (fromColumns e m) := by
    simpa only [d₀, d₁, Matrix.det_fin_three, detThree] using factorOne_det_samples e m he
  rw [factorOne_det_affine F a e m he, h₀, h₁, ← hsample]
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz d₀ with h | h <;> rcases hz d₁ with h' | h' <;> rw [h, h']
  · simp
  · simp [ha0]
  · have hn : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    simpa [sub_eq_add_neg] using hn
  · simp

private theorem factorOne_represents (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Represents F factorOne 3 (factorMatrix₁ a) :=
  ⟨rowRank_of_det F (e := ![0, 1, 3]) (m := ![false, false, true])
      (by rw [factorOne_nonzero_minor F a]; exact one_ne_zero),
    factorOne_isotropic F a, factorOne_bases F a ha0 ha1⟩

omit [CharP F 2] in
private theorem factorTwo_represents : Represents F factorTwo 1 factorMatrix₂ :=
  ⟨rowRank_of_det F (e := ![0]) (m := ![true])
      (by rw [factorTwo_nonzero_minor F]; exact one_ne_zero),
    factorTwo_isotropic F, fun e m _ => factorTwo_bases F e m⟩

omit [CharP F 2] in
/-- Four distinct field elements guarantee a choice outside `{0, 1}`. -/
private theorem exists_alpha (size : Nonempty (Fin 4 ↪ F)) : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  obtain ⟨f⟩ := size
  by_contra! h
  have hone (i : Fin 4) : f i = 0 ∨ f i = 1 := by
    by_cases hi : f i = 0
    · exact Or.inl hi
    · exact Or.inr (h (f i) hi)
  rcases hone 0 with h0 | h0 <;>
    rcases hone 1 with h1 | h1 <;>
    rcases hone 2 with h2 | h2
  all_goals
    first
    | exact (by decide : (0 : Fin 4) ≠ 1) (f.injective (h0.trans h1.symm))
    | exact (by decide : (0 : Fin 4) ≠ 2) (f.injective (h0.trans h2.symm))
    | exact (by decide : (1 : Fin 4) ≠ 2) (f.injective (h1.trans h2.symm))

private theorem factors_representable (size : Nonempty (Fin 4 ↪ F)) :
    Representable F factorOne ∧ Representable F factorTwo := by
  obtain ⟨a, ha0, ha1⟩ := exists_alpha F size
  exact ⟨⟨3, factorOne_rank, factorMatrix₁ a, factorOne_represents F a ha0 ha1⟩,
    ⟨1, factorTwo_rank, factorMatrix₂, factorTwo_represents F⟩⟩

end Factors


section Obstruction

private def triangleEdge (i : Fin 3) : Fin 6 := Fin.castAdd 3 i
private def loopEdge (i : Fin 3) : Fin 6 := Fin.natAdd 3 i

private def endLoops (i : Fin 3) : Fin 3 → Fin 6 :=
  ![triangleEdge i, loopEdge i, loopEdge (i + 1)]

private def firstExtension (i : Fin 3) : Fin 3 → Fin 6 :=
  ![triangleEdge i, loopEdge i, loopEdge (i + 2)]

private def secondExtension (i : Fin 3) : Fin 3 → Fin 6 :=
  ![triangleEdge i, loopEdge (i + 1), loopEdge (i + 2)]

private theorem loop_basis :
    Function.Injective (![3, 4, 5] : Fin 3 → Fin 6) ∧
      Chow oneSum (fromColumns ![3, 4, 5] ![true, true, true]) := by decide +kernel

private theorem endpoint_bases :
    ∀ (i : Fin 3) (s : Bool),
      (Function.Injective (endLoops i) ∧
        ¬ Chow oneSum (fromColumns (endLoops i) ![s, true, true])) ∧
      (Function.Injective (firstExtension i) ∧
        Chow oneSum (fromColumns (firstExtension i) ![s, true, true])) ∧
      (Function.Injective (secondExtension i) ∧
        Chow oneSum (fromColumns (secondExtension i) ![s, true, true])) := by decide +kernel

private def OddMarks (m : Fin 3 → Bool) : Prop :=
  ((Finset.univ : Finset (Fin 3)).filter fun i => m i = true).card % 2 = 1

private instance oddMarksDecidable (m : Fin 3 → Bool) : Decidable (OddMarks m) := by
  unfold OddMarks
  infer_instance

private theorem triangle_basis :
    Function.Injective (![0, 1, 2] : Fin 3 → Fin 6) ∧
      ∀ m : Fin 3 → Bool, Chow oneSum (fromColumns ![0, 1, 2] m) ↔ OddMarks m := by
  decide +kernel

variable {F M : Type*} [Field F] [CharP F 2] [AddCommGroup M] [Module F M]

private def SignedColumns (col : Fin 6 → Bool → M) (e : Fin 3 → Fin 6)
    (m : Fin 3 → Bool) : Fin 3 → M :=
  fun i => col (e i) (m i)

omit [AddCommGroup M] in
private theorem signedColumns_vec (col : Fin 6 → Bool → M) (x y z : Fin 6) (s t u : Bool) :
    SignedColumns col ![x, y, z] ![s, t, u] = ![col x s, col y t, col z u] := by
  funext i
  fin_cases i <;> rfl

omit [CharP F 2] in
private theorem endpoint_coefficients
    {b c d x : M} (hbc : LinearIndependent F ![b, c]) (hbad : ¬ LinearIndependent F ![x, b, c])
    (h₁ : LinearIndependent F ![x, b, d]) (h₂ : LinearIndependent F ![x, c, d]) :
    ∃ a g : F, a ≠ 0 ∧ g ≠ 0 ∧ x = a • (b + g • c) := by
  classical
  have hs : x ∈ Submodule.span F (Set.range ![b, c]) := by
    by_contra hn
    exact hbad (linearIndependent_finCons.mpr ⟨hbc, hn⟩)
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hs
  obtain ⟨a, z, hz⟩ := hs
  have avoid {u v : M} (h : LinearIndependent F ![x, u, v]) (t : F) : t • u ≠ x := by
    intro ht
    have hn := (linearIndependent_finCons.mp h).2
    apply hn
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  have ha : a ≠ 0 := by
    intro he
    apply avoid h₂ z
    simpa [he] using hz
  have hz0 : z ≠ 0 := by
    intro he
    apply avoid h₁ a
    simpa [he] using hz
  refine ⟨a, z / a, ha, div_ne_zero hz0 ha, ?_⟩
  rw [smul_add, smul_smul, show a * (z / a) = z by field_simp]
  exact hz.symm

private theorem gain_det {b : Fin 3 → M} (hb : LinearIndependent F b)
    (a g : Fin 3 → F) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent F (fun i => a i • (b i + g i • b (i + 1))) ↔
      g 0 * g 1 * g 2 ≠ 1 := by
  let A : Matrix (Fin 3) (Fin 3) F :=
    ![![1, 0, g 2], ![g 0, 1, 0], ![0, g 1, 1]]
  let L := Fintype.linearCombination F b
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr
    (linearIndependent_iff_injective_fintypeLinearCombination.mp hb)
  have hc : L ∘ A.col = fun i => b i + g i • b (i + 1) := by
    funext i
    change Fintype.linearCombination F b (fun r => A r i) = _
    rw [Fintype.linearCombination_apply]
    fin_cases i <;>
      simp [A, Fin.sum_univ_succ, add_comm]
  let u (i : Fin 3) : Fˣ := Units.mk0 (a i) (ha i)
  change LinearIndependent F (u • (fun i => b i + g i • b (i + 1))) ↔ _
  rw [LinearIndependent.units_smul_iff, ← hc]
  have lift : LinearIndependent F (L ∘ A.col) ↔ LinearIndependent F A.col :=
    ⟨LinearIndependent.of_comp L, fun h => h.map' L hL⟩
  rw [lift, Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  have hd : A.det = 1 + g 0 * g 1 * g 2 := by
    rw [Matrix.det_fin_three]
    simp [A]
    ring
  rw [hd, add_comm, ← CharTwo.sub_eq_add, sub_ne_zero]

private theorem gain_parity (g : Fin 3 → Bool → F) (hg : ∀ i s, g i s ≠ 0)
    (h : ∀ m : Fin 3 → Bool,
      g 0 (m 0) * g 1 (m 1) * g 2 (m 2) ≠ 1 ↔ OddMarks m) : False := by
  have even (m : Fin 3 → Bool) (hm : ¬ OddMarks m) :
      g 0 (m 0) * g 1 (m 1) * g 2 (m 2) = 1 := by
    by_contra he
    exact hm ((h m).mp he)
  have h000 : g 0 false * g 1 false * g 2 false = 1 :=
    even ![false, false, false] (by decide +kernel)
  have h110 : g 0 true * g 1 true * g 2 false = 1 :=
    even ![true, true, false] (by decide +kernel)
  have h101 : g 0 true * g 1 false * g 2 true = 1 :=
    even ![true, false, true] (by decide +kernel)
  have h011 : g 0 false * g 1 true * g 2 true = 1 :=
    even ![false, true, true] (by decide +kernel)
  have h100 : g 0 true * g 1 false * g 2 false ≠ 1 :=
    (h ![true, false, false]).mpr (by decide +kernel)
  let q (i : Fin 3) := g i true / g i false
  have hq (i : Fin 3) : q i ≠ 0 := div_ne_zero (hg i true) (hg i false)
  have ratio (i : Fin 3) : g i true = q i * g i false := by
    dsimp [q]
    exact (div_mul_cancel₀ _ (hg i false)).symm
  have q01 : q 0 * q 1 = 1 := by
    calc
      q 0 * q 1 = (q 0 * q 1) * (g 0 false * g 1 false * g 2 false) := by rw [h000, mul_one]
      _ = (q 0 * g 0 false) * (q 1 * g 1 false) * g 2 false := by ring
      _ = 1 := by rw [← ratio, ← ratio, h110]
  have q02 : q 0 * q 2 = 1 := by
    calc
      q 0 * q 2 = (q 0 * q 2) * (g 0 false * g 1 false * g 2 false) := by rw [h000, mul_one]
      _ = (q 0 * g 0 false) * g 1 false * (q 2 * g 2 false) := by ring
      _ = 1 := by rw [← ratio, ← ratio, h101]
  have q12 : q 1 * q 2 = 1 := by
    calc
      q 1 * q 2 = (q 1 * q 2) * (g 0 false * g 1 false * g 2 false) := by rw [h000, mul_one]
      _ = g 0 false * (q 1 * g 1 false) * (q 2 * g 2 false) := by ring
      _ = 1 := by rw [← ratio, ← ratio, h011]
  have same₁₂ : q 1 = q 2 := mul_left_cancel₀ (hq 0) (q01.trans q02.symm)
  have same₀₁ : q 0 = q 1 := mul_right_cancel₀ (hq 2) (q02.trans q12.symm)
  have sq : q 0 * q 0 = (1 : F) * 1 := by simpa [← same₀₁] using q01
  have one : q 0 = 1 := by
    rcases mul_self_eq_mul_self_iff.mp sq with hq0 | hq0
    · exact hq0
    · simpa only [CharTwo.neg_eq] using hq0
  apply h100
  rw [ratio 0, one, one_mul, h000]

private theorem looped_triangle_obstruction (col : Fin 6 → Bool → M)
    (tests : ∀ (e : Fin 3 → Fin 6) (m : Fin 3 → Bool), Function.Injective e →
      (LinearIndependent F (SignedColumns col e m) ↔ Chow oneSum (fromColumns e m))) : False := by
  let b (i : Fin 3) := col (loopEdge i) true
  have hb : LinearIndependent F b := by
    convert (tests ![3, 4, 5] ![true, true, true] loop_basis.1).2 loop_basis.2 using 1
    funext i
    fin_cases i <;> rfl
  have hpair (i : Fin 3) : LinearIndependent F ![b i, b (i + 1)] := by
    let ends : Fin 2 → Fin 3 := ![i, i + 1]
    have he : Function.Injective ends := by
      have h : ∀ j : Fin 3, Function.Injective (![j, j + 1] : Fin 2 → Fin 3) := by decide
      exact h i
    convert hb.comp ends he using 1
    funext j
    fin_cases j <;> rfl
  have endpoint (i : Fin 3) (s : Bool) : ∃ a g : F, a ≠ 0 ∧ g ≠ 0 ∧
      col (triangleEdge i) s = a • (b i + g • b (i + 1)) := by
    obtain ⟨⟨he, heBad⟩, ⟨h₁, h₁good⟩, ⟨h₂, h₂good⟩⟩ := endpoint_bases i s
    have hb0 := mt (tests (endLoops i) ![s, true, true] he).mp heBad
    have hb1 := (tests (firstExtension i) ![s, true, true] h₁).mpr h₁good
    have hb2 := (tests (secondExtension i) ![s, true, true] h₂).mpr h₂good
    simp only [endLoops, firstExtension, secondExtension, signedColumns_vec] at hb0 hb1 hb2
    exact endpoint_coefficients (hpair i) hb0 hb1 hb2
  choose a g ha hg hcol using endpoint
  apply gain_parity g hg
  intro m
  have hdet := gain_det hb (fun i => a i (m i)) (fun i => g i (m i)) (fun i => ha i (m i))
  have hfamily : SignedColumns col ![0, 1, 2] m =
      fun i => a i (m i) • (b i + g i (m i) • b (i + 1)) := by
    funext i
    have he : (![0, 1, 2] : Fin 3 → Fin 6) i = triangleEdge i := by fin_cases i <;> rfl
    unfold SignedColumns
    rw [he]
    exact hcol i (m i)
  have ht := tests ![0, 1, 2] m triangle_basis.1
  rw [hfamily] at ht
  exact hdet.symm.trans (ht.trans (triangle_basis.2 m))

omit [CharP F 2] in
private theorem det_iff_independent {E : Type*} {k : ℕ} (H : PairedMatrix (E := E) F k)
    (e : Fin k → E) (m : Fin k → Bool) :
    LinearIndependent F (fun i => H.col (e i, m i)) ↔ (selectedMatrix F H e m).det ≠ 0 := by
  change LinearIndependent F (selectedMatrix F H e m).col ↔ _
  rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

private theorem chowRank_unique {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {G : DirectedMultigraph V E} {k l : ℕ}
    (hk : ChowRank G k) (hl : ChowRank G l) : k = l := by
  obtain ⟨s, hs, hsk⟩ := hk.1
  obtain ⟨t, ht, htl⟩ := hl.1
  exact le_antisymm (hsk ▸ hl.2 s hs) (htl ▸ hk.2 t ht)

private theorem oneSum_rank : ChowRank oneSum 3 := by
  apply chow_rank_of_basis
  refine ⟨fromColumns ![3, 4, 5] ![true, true, true], loop_basis.2, ?_⟩
  decide

private theorem one_sum_nonrepresentable : ¬ Representable F oneSum := by
  rintro ⟨k, hk, H, hrep⟩
  have h := chowRank_unique hk oneSum_rank
  subst k
  apply looped_triangle_obstruction (F := F) (fun e m => H.col (e, m))
  intro e m he
  exact (det_iff_independent H e m).trans (hrep.bases e m he)

end Obstruction


section Bridge

/-- Add the unstarred bridge and retain the marks and IDs of surviving edges. -/
private def bridgeMarking (s : Marking (Fin 6)) : Marking (Fin 7) :=
  Fin.snoc s (some false)

private theorem chow_bridge :
    ∀ s : Marking (Fin 6), Chow bridgeJoin (bridgeMarking s) ↔ Chow oneSum s := by
  decide +kernel

private theorem bridge_rank : ChowRank bridgeJoin 4 := by
  apply chow_rank_of_basis
  refine ⟨bridgeMarking (fromColumns ![3, 4, 5] ![true, true, true]), ?_⟩
  exact ⟨(chow_bridge _).mpr loop_basis.2, by decide⟩

private def liftEdges (e : Fin 3 → Fin 6) : Fin 4 → Fin 7 :=
  Fin.snoc (Fin.castSucc ∘ e) (Fin.last 6)

private def liftMarks (m : Fin 3 → Bool) : Fin 4 → Bool :=
  Fin.snoc m false

private theorem liftEdges_injective {e : Fin 3 → Fin 6} (h : Function.Injective e) :
    Function.Injective (liftEdges e) :=
  Fin.snoc_injective_of_injective ((Fin.castSucc_injective 6).comp h)
    (fun ⟨i, hi⟩ => Fin.ne_of_lt (Fin.castSucc_lt_last (e i)) hi)

private theorem lift_marking (e : Fin 3 → Fin 6) (m : Fin 3 → Bool) :
    fromColumns (liftEdges e) (liftMarks m) = bridgeMarking (fromColumns e m) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hne (a : Fin 6) : a.castSucc ≠ Fin.last 6 :=
      Fin.ne_of_lt (Fin.castSucc_lt_last a)
    simp only [fromColumns, liftEdges, liftMarks, bridgeMarking, Fin.exists_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply, hne, false_and,
      exists_false, false_or, or_true, ite_true, eq_self]
    rfl
  · have hne : Fin.last 6 ≠ i.castSucc := Fin.ne_of_gt (Fin.castSucc_lt_last i)
    simp only [fromColumns, liftEdges, liftMarks, bridgeMarking, Fin.exists_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply, Fin.castSucc_inj,
      hne, false_and, or_false]

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

private theorem quotient_snoc {I : Type*} (f : I → M) (x : I) (g : Fin 3 → I)
    (hg : Function.Injective g) (hd : ∀ i, g i ≠ x) (hx : f x ≠ 0) :
    LinearIndependent F (fun i => (Submodule.span F {f x}).mkQ (f (g i))) ↔
      LinearIndependent F (fun i => f ((Fin.snoc g x : Fin 4 → I) i)) := by
  have hs : LinearIndepOn F f {x} := .singleton hx
  have disj : Disjoint ({x} : Set I) (Set.range g) :=
    Set.disjoint_singleton_left.mpr (fun ⟨i, hi⟩ => hd i hi)
  have he := Fin.snoc_injective_of_injective hg (fun ⟨i, hi⟩ => hd i hi)
  change LinearIndependent F ((Submodule.mkQ (Submodule.span F {f x}) ∘ f) ∘ g) ↔
    LinearIndependent F (f ∘ Fin.snoc g x)
  rw [← linearIndepOn_range_iff hg, ← linearIndepOn_range_iff he, Fin.range_snoc,
    ← Set.singleton_union]
  have h := hs.quotient_iff_union disj
  rw [Set.image_singleton (f := f) (a := x)] at h
  exact h

omit [Field F] in
private theorem lift_column_family
    (H : PairedMatrix (E := Fin 7) F 4) (e : Fin 3 → Fin 6) (m : Fin 3 → Bool) :
    (fun i => H.col (liftEdges e i, liftMarks m i)) =
      fun i => H.col ((Fin.snoc (fun j => ((e j).castSucc, m j)) (Fin.last 6, false) :
        Fin 4 → Fin 7 × Bool) i) := by
  funext i
  refine Fin.lastCases ?_ (fun _ => ?_) i <;>
    simp only [liftEdges, liftMarks, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply]

variable [CharP F 2]

private theorem bridge_nonrepresentable : ¬ Representable F bridgeJoin := by
  rintro ⟨k, hk, H, hrep⟩
  have hr := chowRank_unique hk bridge_rank
  subst k
  have lift_test (e : Fin 3 → Fin 6) (m : Fin 3 → Bool) (he : Function.Injective e) :
      LinearIndependent F (fun i => H.col (liftEdges e i, liftMarks m i)) ↔
        Chow oneSum (fromColumns e m) := by
    rw [det_iff_independent, hrep.bases _ _ (liftEdges_injective he), lift_marking, chow_bridge]
  have hb : H.col (Fin.last 6, false) ≠ 0 := by
    have hi := (lift_test ![3, 4, 5] ![true, true, true] loop_basis.1).mpr loop_basis.2
    simpa only [liftEdges, liftMarks, Fin.snoc_last] using hi.ne_zero (Fin.last 3)
  let Q := (Submodule.span F {H.col (Fin.last 6, false)}).mkQ
  apply looped_triangle_obstruction (F := F) (fun e m => Q (H.col (e.castSucc, m)))
  intro e m he
  let g (i : Fin 3) : Fin 7 × Bool := ((e i).castSucc, m i)
  have hg : Function.Injective g := fun _ _ h => he (Fin.castSucc_inj.mp (congrArg Prod.fst h))
  have hd (i : Fin 3) : g i ≠ (Fin.last 6, false) :=
    fun h => Fin.ne_of_lt (Fin.castSucc_lt_last (e i)) (congrArg Prod.fst h)
  have ht := lift_test e m he
  rw [lift_column_family] at ht
  exact (quotient_snoc H.col (Fin.last 6, false) g hg hd hb).trans ht

end Bridge

/-- Counterexamples to both preservation claims of Question 9.2 over each specified field. -/
theorem question_nine_two (F : Type*) [Field F] [CharP F 2] (size : Nonempty (Fin 4 ↪ F)) :
    (Representable F factorOne ∧ Representable F factorTwo) ∧
      (¬ Representable F oneSum ∧ ¬ Representable F bridgeJoin) :=
  ⟨factors_representable F size, one_sum_nonrepresentable, bridge_nonrepresentable⟩

/-- Neither operation preserves representability over any field in the question. -/
theorem result : ¬ claim := by
  rintro ⟨F, field, charTwo, size, closure⟩
  obtain ⟨⟨h₁, h₂⟩, hSum, hBridge⟩ := question_nine_two F size
  rcases closure with sumClosed | bridgeClosed
  · exact hSum (sumClosed factorOne factorTwo 2 0 h₁ h₂)
  · exact hBridge (bridgeClosed factorOne factorTwo 2 0 h₁ h₂)

end D5.S3.Combinatorics.Matroids.GangulyQuestionNineTwo
