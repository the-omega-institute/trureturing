/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Signed source occurrence cycles and minimum natural block bases. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveBranchReduction
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual

/-! Integer consistency and minimum natural ranks on the actual source graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover

open NativePositiveBranchReduction NativePositiveImageCover NativeTermUnification
open NativeGroundSolutionSpace Maths Maths.MaxPlusPotential
open Lambda Strata.Util

variable {X : Type} [DecidableEq X]

/-- Select one residual sort without identifying repeated or parallel edges. -/
def sortEdges (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  (sourceOffsetEdges B s).filter (fun e => e.1.1.2.2 == j)

abbrev Edge (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  Fin (sortEdges B s j).length × Bool

def signedGraph (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    EdgeGraph (Occurrence X) (Edge B s j) where
  source e := if e.2 then ((sortEdges B s j).get e.1).1.1
    else ((sortEdges B s j).get e.1).1.2
  target e := if e.2 then ((sortEdges B s j).get e.1).1.2
    else ((sortEdges B s j).get e.1).1.1

def signedWeight (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (e : Edge B s j) : Int :=
  if e.2 then -((sortEdges B s j).get e.1).2 else ((sortEdges B s j).get e.1).2

def ZeroCycles (B : List (BranchEquation X)) (s : X → Term X) (j : X) : Prop :=
  ∀ (v : Occurrence X) (c : (signedGraph B s j).Walk v v),
    walkWeight (signedWeight B s j) c = 0

def Potential (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) : Prop :=
  ∀ e ∈ sortEdges B s j, δ e.1.1 = δ e.1.2 + e.2

/-- The leaf carrier is arbitrary; nonemptiness is needed only to detect
inconsistent cycles. No shape or rank bound is imposed. -/
def BlockSolution (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    {L : Type} (u : Occurrence X → L → Nat) : Prop :=
  ∀ e ∈ sortEdges B s j, ∀ l, (u e.1.1 l : Int) = (u e.1.2 l : Int) + e.2

private theorem potential_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) :
    Potential B s j δ ↔ IsPotential (signedGraph B s j) (signedWeight B s j) δ := by
  constructor
  · intro h e
    have eq := h _ (List.get_mem (sortEdges B s j) e.1)
    cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
    have hf := h (i, false)
    have hb := h (i, true)
    simp only [signedGraph, signedWeight, Bool.false_eq_true, ↓reduceIte] at hf hb
    omega

private theorem walk_exact {B : List (BranchEquation X)} {s : X → Term X} {j : X}
    {δ : Occurrence X → Int} (h : Potential B s j δ)
    {v w : Occurrence X} (c : (signedGraph B s j).Walk v w) :
    walkWeight (signedWeight B s j) c = δ w - δ v := by
  induction c with
  | nil => simp [walkWeight]
  | concat c e legal ih =>
      have eq := h _ (List.get_mem (sortEdges B s j) e.1)
      rw [walkWeight_concat, ih]
      subst legal
      cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega

private theorem zeroCycles_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    ZeroCycles B s j ↔ ∃ δ, Potential B s j δ := by
  constructor
  · intro h
    obtain ⟨δ, hδ⟩ :=
      (exists_isPotential_iff_forall_closedWalk_nonpos
        (G := signedGraph B s j) (signedWeight B s j)).mpr (fun v c => (h v c).le)
    exact ⟨δ, (potential_iff B s j δ).mpr hδ⟩
  · rintro ⟨δ, hδ⟩ v c
    simpa using walk_exact hδ c

private theorem edge_spec (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {e : (Occurrence X × Occurrence X) × Int}
    (he : e ∈ sourceOffsetEdges B (action p S)) :
    e.1.1 ∈ occurrenceVertices p (action p S) ∧
    e.1.2 ∈ occurrenceVertices p (action p S) ∧ e.1.1.2.2 = e.1.2.2.2 := by
  apply (mgu_occurrence_graph_exact p (shapeEquations B) S hok).2.1
  rw [← source_comparison_graph_identification]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

private theorem connected_sort (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = w.2.2 := by
  induction h with
  | rel a b he =>
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have hs := (edge_spec p B S hok he).2.2
      simpa only [eq] using hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem common_difference (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) {f g : Occurrence X → Int}
    (hf : Potential B (action p S) j f) (hg : Potential B (action p S) j g)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = j → f v - g v = f w - g w := by
  induction h with
  | rel v w he =>
      intro hv
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have pair : e.1 = (v,w) := eq
      have mem : e ∈ sortEdges B (action p S) j := by
        simp only [sortEdges, List.mem_filter, beq_iff_eq]
        exact ⟨he, by simpa only [pair] using hv⟩
      have h1 := hf e mem
      have h2 := hg e mem
      simp only [pair] at h1 h2
      omega
  | refl v => intro _; rfl
  | symm v w h ih =>
      intro hw
      have hv : v.2.2 = j := (connected_sort p B S hok h).trans hw
      exact (ih hv).symm
  | trans v w z h1 h2 ih1 ih2 =>
      intro hv
      have hw : w.2.2 = j := (connected_sort p B S hok h1).symm.trans hv
      exact (ih1 hv).trans (ih2 hw)

/-- The actual source comparison graph admits one minimum natural base per
occurring sort. Nonzero cycles exclude solutions on every inhabited leaf
carrier; zero cycles classify all natural solutions, including a singleton
isolated occurrence. The theorem does not assert native code reconstruction. -/
theorem source_sort_minimum_base (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j) :
    (¬ ZeroCycles B (action p S) j →
      ∀ (L : Type) [Nonempty L] (u : Occurrence X → L → Nat),
        ¬ BlockSolution B (action p S) j u) ∧
    (ZeroCycles B (action p S) j →
      ∃ (δ : Occurrence X → Int) (b : Occurrence X) (a : Occurrence X → Nat),
        Potential B (action p S) j δ ∧
        b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          δ b ≤ δ v ∧ (a v : Int) = δ v - δ b) ∧
        (∀ (L : Type) (u : Occurrence X → L → Nat),
          BlockSolution B (action p S) j u ↔
          ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
            ∀ l, u v l = u b l + a v)) := by
  classical
  constructor
  · intro bad L _ u hu
    let l : L := Classical.choice (inferInstance : Nonempty L)
    apply bad
    exact (zeroCycles_iff B (action p S) j).mpr ⟨fun v => (u v l : Int), fun e he => hu e he l⟩
  · intro good
    obtain ⟨δ, hδ⟩ := (zeroCycles_iff B (action p S) j).mp good
    let V := (occurrenceVertices p (action p S)).toFinset.filter (fun v => v.2.2 = j)
    have hV : V.Nonempty := by
      obtain ⟨v, hv, hj⟩ := occurs
      exact ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩⟩
    obtain ⟨b, hb, hmin⟩ := V.exists_min_image δ hV
    have hb' := Finset.mem_filter.mp hb
    let a : Occurrence X → Nat := fun v => (δ v - δ b).toNat
    have ha : ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
        δ b ≤ δ v ∧ (a v : Int) = δ v - δ b := by
      intro v hv hj
      have hm := hmin v (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩)
      exact ⟨hm, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨δ, b, a, hδ, List.mem_toFinset.mp hb'.1, hb'.2, ?_, ha, ?_⟩
    · simp [a]
    · intro L u
      constructor
      · intro hu v hv hj l
        have conn := (source_connected_iff_sort p B S hok b v
          (List.mem_toFinset.mp hb'.1) hv).mpr (hb'.2.trans hj.symm)
        have hd := common_difference p B S hok j
          (f := fun w => (u w l : Int)) (g := δ)
          (fun e he => hu e he l) hδ conn hb'.2
        have hav := (ha v hv hj).2
        omega
      · intro hu e he l
        have he' := (List.mem_filter.mp he).1
        have hj : e.1.1.2.2 = j := by
          simpa only [beq_iff_eq] using (List.mem_filter.mp he).2
        have spec := edge_spec p B S hok he'
        have hu1 := hu e.1.1 spec.1 hj l
        have hu2 := hu e.1.2 spec.2.1 (spec.2.2.symm.trans hj) l
        have ha1 := (ha e.1.1 spec.1 hj).2
        have ha2 := (ha e.1.2 spec.2.1 (spec.2.2.symm.trans hj)).2
        have hed := hδ e he
        omega

/-- Leaves retain their ordered positions even when all ranks coincide. -/
def Leaves : FreeMagma Unit → Type
  | .of _ => Unit
  | .mul A B => Leaves A ⊕ Leaves B

instance leavesFinite : (T : FreeMagma Unit) → Finite (Leaves T)
  | .of _ => inferInstanceAs (Finite Unit)
  | .mul A B =>
      letI := leavesFinite A
      letI := leavesFinite B
      inferInstanceAs (Finite (Leaves A ⊕ Leaves B))

instance leavesNonempty : (T : FreeMagma Unit) → Nonempty (Leaves T)
  | .of _ => inferInstanceAs (Nonempty Unit)
  | .mul A B =>
      letI := leavesNonempty A
      inferInstanceAs (Nonempty (Leaves A ⊕ Leaves B))

def fill : (T : FreeMagma Unit) → (Leaves T → Nat) → NativeFiniteNormalInversion.Code
  | .of _, r => .of (r ())
  | .mul A B, r => .mul (fill A (fun l => r (.inl l))) (fill B (fun l => r (.inr l)))

private theorem fill_shift (T : FreeMagma Unit) (r : Leaves T → Nat) (a : Nat) :
    fill T (fun l => r l + a) = NativeFiniteNormalInversion.shiftCode a (fill T r) := by
  induction T with
  | of => rfl
  | mul A B ihA ihB =>
      exact congrArg₂ FreeMagma.mul (ihA _) (ihB _)

private theorem normal_subtree (C : NativeFiniteNormalInversion.Code) (q : List Bool)
    (D : NativeFiniteNormalInversion.Code) (hC : NativeFiniteNormalInversion.Normal C)
    (h : subtree C q = some D) : NativeFiniteNormalInversion.Normal D := by
  induction q generalizing C with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      exact h ▸ hC
  | cons b q ih =>
      cases C with
      | of n => cases h
      | mul A B =>
          cases b
          · exact ih A hC.1 h
          · exact ih B hC.2.1 h

/-- Actual occurrence subtrees turn the minimum rank base into a normal
native block. Rank inverses and expansion recover the identical blocks. -/
theorem source_canonical_block_recovery (p : Presentation X)
    (B : List (BranchEquation X)) (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j)
    (good : ZeroCycles B (action p S) j) :
    ∃ (b : Occurrence X) (a : Occurrence X → Nat),
      b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
      ∀ (T : FreeMagma Unit) (u : Occurrence X → Leaves T → Nat)
        (C : X → NativeFiniteNormalInversion.Code),
        BlockSolution B (action p S) j u →
        (∀ x, NativeFiniteNormalInversion.Normal (C x)) →
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          subtree (C v.1) v.2.1 = some (fill T (u v))) →
        NativeFiniteNormalInversion.Normal (fill T (u b)) ∧
        ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) ∧
          NativeFiniteNormalInversion.expand (fill T (u v)) =
            GenealogicalFiberTransport.substitution^[a v]
              (NativeFiniteNormalInversion.expand (fill T (u b))) ∧
          (∀ l, NativeFiniteNormalInversion.rankInverse (a v) (u v l) = some (u b l)) := by
  obtain ⟨δ, b, a, hδ, hb, hj, hab, hmin, law⟩ :=
    (source_sort_minimum_base p B S hok j occurs).2 good
  refine ⟨b, a, hb, hj, hab, ?_⟩
  intro T u C hu hC actual
  have ranks := (law (Leaves T) u).mp hu
  refine ⟨normal_subtree (C b.1) b.2.1 _ (hC b.1) (actual b hb hj), ?_⟩
  intro v hv hvj
  have heq : u v = fun l => u b l + a v := funext (ranks v hv hvj)
  have code : fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) := by
    rw [heq]
    exact fill_shift T (u b) (a v)
  refine ⟨code, ?_, ?_⟩
  · rw [code]
    exact NativeFiniteNormalInversion.shift_expand (a v) (fill T (u b))
  · intro l
    exact ((NativeFiniteNormalInversion.exact_natural_rank_inverse (a v) (u v l)).1
      (u b l)).mpr (ranks v hv hvj l).symm

#print axioms source_sort_minimum_base
#print axioms source_canonical_block_recovery

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover
