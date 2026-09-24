/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupOverlap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Group-ring coefficients construct labelled edge splittings and equivariant one-step overlap conjugacies. -/

import D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

open D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
open D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding

universe u
variable {H : Type u} [Group H] [Fintype H]

abbrev GroupMat (H : Type u) [Group H] (n m : ℕ) :=
  Matrix (Fin n) (Fin m) (MonoidAlgebra ℕ H)

/-- Parallel edges retain both their group label and their number within that label. -/
structure Edge {n m : ℕ} (M : GroupMat H n m) where
  source : Fin n
  target : Fin m
  label : H
  number : Fin ((M source target).coeff label)

instance {n m : ℕ} (M : GroupMat H n m) : TopologicalSpace (Edge M) := ⊥
instance {n m : ℕ} (M : GroupMat H n m) : DiscreteTopology (Edge M) := ⟨rfl⟩

abbrev Path {n : ℕ} (M : GroupMat H n n) :=
  {x : ℤ → Edge M // ∀ i : ℤ, (x i).target = (x (i + 1)).source}

def shift {n : ℕ} (M : GroupMat H n n) (x : Path M) : Path M :=
  ⟨fun i => x.val (i + 1), fun i => x.property (i + 1)⟩

/-- The time step includes the ordered multiplication of the current edge label. -/
def step {n : ℕ} (M : GroupMat H n n) (p : Path M × H) : Path M × H :=
  (shift M p.1, p.2 * (p.1.val 0).label)

variable {n m : ℕ} (U : GroupMat H n m) (V : GroupMat H m n)

abbrev Fiber (i k : Fin n) (g : H) :=
  Σ j : Fin m, Σ h : H,
    Fin ((U i j).coeff h) × Fin ((V j k).coeff (h⁻¹ * g))

private theorem coeff_product_finite (a b : MonoidAlgebra ℕ H) (g : H) :
    (a * b).coeff g = ∑ h : H, a.coeff h * b.coeff (h⁻¹ * g) := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

/-- Counting is performed separately in each endpoint and total-label fiber. -/
theorem fiber_card (i k : Fin n) (g : H) :
    Fintype.card (Fiber U V i k g) = ((U * V) i k).coeff g := by
  classical
  simp [Fiber, Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod,
    coeff_product_finite]

noncomputable def fiberEquiv (i k : Fin n) (g : H) :
    Fin (((U * V) i k).coeff g) ≃ Fiber U V i k g :=
  (Fintype.equivFinOfCardEq (fiber_card U V i k g)).symm

noncomputable def split (a : Edge (U * V)) : Edge U × Edge V :=
  let p := fiberEquiv U V a.source a.target a.label a.number
  (⟨a.source, p.1, p.2.1, p.2.2.1⟩,
   ⟨p.1, a.target, p.2.1⁻¹ * a.label, p.2.2.2⟩)

@[simp] theorem split_source (a : Edge (U * V)) :
    (split U V a).1.source = a.source := rfl

@[simp] theorem split_target (a : Edge (U * V)) :
    (split U V a).2.target = a.target := rfl

@[simp] theorem split_boundary (a : Edge (U * V)) :
    (split U V a).1.target = (split U V a).2.source := rfl

@[simp] theorem split_label (a : Edge (U * V)) :
    (split U V a).1.label * (split U V a).2.label = a.label := by
  simp [split]

noncomputable def join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    Edge (U * V) :=
  ⟨a.source, b.target, a.label * b.label,
    (fiberEquiv U V a.source b.target (a.label * b.label)).symm
      ⟨a.target, a.label, a.number, by simpa using h.symm ▸ b.number⟩⟩

@[simp] theorem split_join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    split U V (join U V a b h) = (a, b) := by
  rcases a with ⟨i, j, g, a⟩
  rcases b with ⟨j', k, h', b⟩
  cases h
  let p : Fiber U V i k (g * h') :=
    ⟨j, g, a, by simpa using b⟩
  let rebuild : Fiber U V i k (g * h') → Edge U × Edge V := fun q =>
    (⟨i, q.1, q.2.1, q.2.2.1⟩,
     ⟨q.1, k, q.2.1⁻¹ * (g * h'), q.2.2.2⟩)
  have hinv := congrArg rebuild
    ((fiberEquiv U V i k (g * h')).apply_symm_apply p)
  change rebuild
      (fiberEquiv U V i k (g * h')
        ((fiberEquiv U V i k (g * h')).symm p)) =
    (⟨i, j, g, a⟩, ⟨j, k, h', b⟩)
  rw [Equiv.apply_symm_apply]
  simpa [rebuild, p] using hinv

@[simp] theorem join_split (a : Edge (U * V)) :
    join U V (split U V a).1 (split U V a).2 (split_boundary U V a) = a := by
  rcases a with ⟨i, k, g, a⟩
  let totalFiberEquiv :
      (Σ h : H, Fin (((U * V) i k).coeff h)) ≃ (Σ h : H, Fiber U V i k h) :=
    Equiv.sigmaCongrRight fun h => fiberEquiv U V i k h
  let rebuild : (Σ h : H, Fin (((U * V) i k).coeff h)) → Edge (U * V) :=
    fun q => ⟨i, k, q.1, q.2⟩
  have hinv := congrArg rebuild
    (totalFiberEquiv.symm_apply_apply
      (⟨g, a⟩ : Σ h : H, Fin (((U * V) i k).coeff h)))
  simp [rebuild, totalFiberEquiv] at hinv
  simpa [join, split] using hinv.2

def boundary : Boundary (Edge U) (Edge V) (Fin n) (Fin m) :=
  ⟨Edge.source, Edge.target, Edge.source, Edge.target⟩

noncomputable def toAlternating (x : Path (U * V)) : LeftPath (boundary U V) :=
  ⟨fun i => split U V (x.val i), fun i => ⟨rfl, x.property i⟩⟩

noncomputable def fromAlternating (x : LeftPath (boundary U V)) : Path (U * V) :=
  ⟨fun i => join U V (x.val i).1 (x.val i).2 (x.property i).1,
    fun i => (x.property i).2⟩

@[simp] theorem from_to (x : Path (U * V)) :
    fromAlternating U V (toAlternating U V x) = x := by
  apply Subtype.ext
  funext i
  exact join_split U V (x.val i)

@[simp] theorem to_from (x : LeftPath (boundary U V)) :
    toAlternating U V (fromAlternating U V x) = x := by
  apply Subtype.ext
  funext i
  exact split_join U V (x.val i).1 (x.val i).2 (x.property i).1

noncomputable def alternatingEquiv : Path (U * V) ≃ LeftPath (boundary U V) where
  toFun := toAlternating U V
  invFun := fromAlternating U V
  left_inv := from_to U V
  right_inv := to_from U V

theorem continuous_toAlternating : Continuous (toAlternating U V) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous (split U V)).comp
    ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_fromAlternating : Continuous (fromAlternating U V) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  let P := {p : Edge U × Edge V // p.1.target = p.2.source}
  let f : P → Edge (U * V) := fun p => join U V p.val.1 p.val.2 p.property
  have hf : Continuous f := continuous_of_discreteTopology
  have hi : Continuous (fun x : LeftPath (boundary U V) =>
      (⟨x.val i, (x.property i).1⟩ : P)) := by
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  exact hf.comp hi

noncomputable def alternatingHomeomorph : Path (U * V) ≃ₜ LeftPath (boundary U V) where
  toEquiv := alternatingEquiv U V
  continuous_toFun := continuous_toAlternating U V
  continuous_invFun := continuous_fromAlternating U V

noncomputable def unpack (p : Path (U * V) × H) : LeftPath (boundary U V) × H :=
  (toAlternating U V p.1, p.2)

noncomputable def repack (p : LeftPath (boundary U V) × H) : Path (U * V) × H :=
  (fromAlternating U V p.1, p.2)

@[simp] theorem repack_unpack (p : Path (U * V) × H) :
    repack U V (unpack U V p) = p := by
  apply Prod.ext
  · exact from_to U V p.1
  · rfl

@[simp] theorem unpack_repack (p : LeftPath (boundary U V) × H) :
    unpack U V (repack U V p) = p := by
  apply Prod.ext
  · exact to_from U V p.1
  · rfl

theorem unpack_step (p : Path (U * V) × H) :
    unpack U V (step (U * V) p) =
      leftStep (boundary U V) Edge.label Edge.label (unpack U V p) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun g : H => p.2 * g) (split_label U V (p.1.val 0)).symm

theorem repack_step (p : LeftPath (boundary U V) × H) :
    repack U V (leftStep (boundary U V) Edge.label Edge.label p) =
      step (U * V) (repack U V p) := by
  apply Prod.ext <;> rfl

section Topology
variable [TopologicalSpace H] [IsTopologicalGroup H]

/-- The group action is preserved by constructing the label transfer, without a cocycle premise. -/
noncomputable def elementaryHomeomorph : Path (U * V) × H ≃ₜ Path (V * U) × H :=
  ((alternatingHomeomorph U V).prodCongr (Homeomorph.refl H)).trans
    ((skewHomeomorph (boundary U V) (Edge.label : Edge U → H)
      continuous_of_discreteTopology).trans
      ((alternatingHomeomorph V U).prodCongr (Homeomorph.refl H)).symm)

theorem elementary_apply (p : Path (U * V) × H) :
    elementaryHomeomorph U V p = repack V U
      (encode (boundary U V) Edge.label (unpack U V p)) := rfl

theorem elementary_symm_apply (p : Path (V * U) × H) :
    (elementaryHomeomorph U V).symm p = repack U V
      (decode (boundary U V) Edge.label (unpack V U p)) := rfl

/-- Both time maps act on the original one-step group extensions. -/
theorem elementary_step (p : Path (U * V) × H) :
    elementaryHomeomorph U V (step (U * V) p) =
      step (V * U) (elementaryHomeomorph U V p) := by
  change repack V U (encode (boundary U V) Edge.label
      (unpack U V (step (U * V) p))) =
    step (V * U) (repack V U (encode (boundary U V) Edge.label (unpack U V p)))
  rw [unpack_step]
  exact (congrArg (repack V U)
    (encode_step (boundary U V) Edge.label Edge.label (unpack U V p))).trans
      (repack_step V U (encode (boundary U V) Edge.label (unpack U V p)))

theorem elementary_equivariant (g : H) (p : Path (U * V) × H) :
    elementaryHomeomorph U V (translate g p) =
      translate g (elementaryHomeomorph U V p) := by
  change repack V U (encode (boundary U V) Edge.label
      (translate g (unpack U V p))) =
    repack V U (translate g (encode (boundary U V) Edge.label (unpack U V p)))
  exact congrArg (repack V U)
    (encode_equivariant (boundary U V) Edge.label g (unpack U V p))

theorem elementary_inverse_step (p : Path (V * U) × H) :
    (elementaryHomeomorph U V).symm (step (V * U) p) =
      step (U * V) ((elementaryHomeomorph U V).symm p) := by
  apply (elementaryHomeomorph U V).injective
  rw [(elementaryHomeomorph U V).apply_symm_apply, elementary_step,
    (elementaryHomeomorph U V).apply_symm_apply]

theorem elementary_recovery (p : Path (U * V) × H) :
    (elementaryHomeomorph U V).symm (elementaryHomeomorph U V p) = p :=
  (elementaryHomeomorph U V).symm_apply_apply p

/-- A homeomorphism together with the specified time and group laws. -/
structure GroupConjugacy {a b : ℕ} (A : GroupMat H a a) (B : GroupMat H b b) where
  homeomorph : Path A × H ≃ₜ Path B × H
  time_law : ∀ p, homeomorph (step A p) = step B (homeomorph p)
  group_law : ∀ g p, homeomorph (translate g p) = translate g (homeomorph p)

def GroupConjugacy.trans {a b c : ℕ}
    {A : GroupMat H a a} {B : GroupMat H b b} {C : GroupMat H c c}
    (f : GroupConjugacy A B) (g : GroupConjugacy B C) : GroupConjugacy A C where
  homeomorph := f.homeomorph.trans g.homeomorph
  time_law := fun p =>
    (congrArg g.homeomorph (f.time_law p)).trans (g.time_law (f.homeomorph p))
  group_law := fun h p =>
    (congrArg g.homeomorph (f.group_law h p)).trans (g.group_law h (f.homeomorph p))

/-- The entire chain is interpreted on numbered, group-labelled histories. -/
theorem chain_has_group_conjugacy {a b L : ℕ}
    {A : GroupMat H a a} {B : GroupMat H b b}
    (c : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain
      (MonoidAlgebra ℕ H) A B L) : Nonempty (GroupConjugacy A B) := by
  induction c with
  | nil A => exact ⟨⟨Homeomorph.refl _, fun _ => rfl, fun _ _ => rfl⟩⟩
  | cons R S tail ih =>
      obtain ⟨g⟩ := ih
      let f : GroupConjugacy (R * S) (S * R) :=
        ⟨elementaryHomeomorph R S, elementary_step R S, elementary_equivariant R S⟩
      exact ⟨f.trans g⟩

end Topology

#print axioms fiber_card
#print axioms split_join
#print axioms join_split
#print axioms elementaryHomeomorph
#print axioms elementary_step
#print axioms elementary_equivariant
#print axioms elementary_recovery
#print axioms chain_has_group_conjugacy

end D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
