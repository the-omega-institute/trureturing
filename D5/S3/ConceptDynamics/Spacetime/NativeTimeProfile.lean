/- GID: D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/NativeTimeProfile
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Finite signed time profiles retain selection and all current successor attributes under native operations. -/

import D5.S3.ConceptDynamics.Spacetime.CoarseObservation
import D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.LinearAlgebra.BilinearMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile

open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge TotalCopyNormalization ProductNodes
open scoped BigOperators
noncomputable section
open Classical

abbrev Cell := Attributes 3 × Bool × Finset (Attributes 3)
abbrev Profile := Cell →₀ Int

/-- Reflexive current successors; unselected targets are retained. -/
def successors (c : Context 3) (e : c.Event) : Finset (Attributes 3) :=
  (c.current.filter (fun d => e = d ∨ c.archive.causal e d)).image c.archive.attributes

private theorem mem_successors (c : Context 3) (e : c.Event) (a : Attributes 3) :
    a ∈ successors c e ↔ ∃ d : ↥c.current,
      (e = d.val ∨ c.archive.causal e d.val) ∧ c.archive.attributes d.val = a := by
  simp only [successors, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨d, ⟨hd, h⟩, ha⟩; exact ⟨⟨d, hd⟩, h, ha⟩
  · rintro ⟨d, h, ha⟩; exact ⟨d.val, ⟨d.property, h⟩, ha⟩

def cell (X : Rich 3) (e : ↥X.1.current) : Cell :=
  (X.1.archive.attributes e.val, decide (e.val ∈ X.2.val), successors X.1 e.val)

/-- The signed finite measure on attribute, selection-bit and successor-set cells. -/
def gamma (X : Rich 3) : Profile :=
  ∑ e : ↥X.1.current, Finsupp.single (cell X e) (contribution X.1 e.val)

/-- Push a profile along a cell map, merging colliding cells by integer addition. -/
def push (f : Cell → Cell) : Profile →ₗ[Int] Profile := Finsupp.lmapDomain Int Int f

/-- Terminal selected-charge functional. -/
def readout : Profile →ₗ[Int] Int :=
  Finsupp.linearCombination Int (fun z : Cell => if z.2.1 then (1 : Int) else 0)

theorem readout_gamma (X : Rich 3) : readout (gamma X) = q X := by
  simp only [gamma, map_sum, readout, Finsupp.linearCombination_single, smul_eq_mul]
  simp only [cell, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
  change (∑ e : ↥X.1.current, if e.val ∈ X.2.val then contribution X.1 e.val else 0) =
    ∑ e ∈ X.2.val, contribution X.1 e
  rw [← sum_selectedParents X.2 (contribution X.1)]
  have hs : selectedParents X.2 = Finset.univ.filter
      (fun e : ↥X.1.current => e.val ∈ X.2.val) := by ext e; simp
  rw [hs, Finset.sum_filter]

def shiftAttribute (k : Int) (a : Attributes 3) : Attributes 3 :=
  {a with time := a.time + k}

def unaryCell : Unary → Cell → Cell
  | .complement, (a, b, U) => (a, !b, U)
  | .spatial S, (a, b, U) => (a, b && decide (a.position ∈ S), U)
  | .source L, (a, b, U) => (a, b && decide (a.source ∈ L), U)
  | .causal Q, (a, b, U) =>
      (a, b && decide (∃ v ∈ U, sourceAttributeEquiv v ∈ Q), U)
  | .shift k, (a, b, U) => (shiftAttribute k a, b, U.image (shiftAttribute k))

private theorem causal_hit (X : B) (e : ↥X.val.1.current) (Q : Set SourceTimedAttribute) :
    (∃ v ∈ successors X.val.1 e.val, sourceAttributeEquiv v ∈ Q) ↔
    ∃ d ∈ X.val.1.current, sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
      (e.val = d ∨ X.val.1.archive.causal e.val d) := by
  simp only [successors, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨d, ⟨hd, he⟩, rfl⟩, hQ⟩; exact ⟨d, hd, hQ, he⟩
  · rintro ⟨d, hd, hQ, he⟩; exact ⟨_, ⟨d, ⟨hd, he⟩, rfl⟩, hQ⟩

private theorem successors_shift (X : B) (k : Int) (e : X.val.1.Event) :
    successors (unary (.shift k) X).val.1 e =
      (successors X.val.1 e).image (shiftAttribute k) := by
  simp only [successors, Finset.image_image]
  rfl

private def unaryCurrent (f : Unary) (X : B) :
    ↥X.val.1.current ≃ ↥(unary f X).val.1.current := by
  cases f <;> exact Equiv.refl _

private theorem cell_unary (f : Unary) (X : B) (e : ↥X.val.1.current) :
    cell (unary f X).val (unaryCurrent f X e) = unaryCell f (cell X.val e) := by
  cases f with
  | complement =>
    simp [cell, unaryCurrent, unary, unaryCell, complementBalanced, complementRich,
      complement, e.property]
  | spatial S => simp [cell, unaryCurrent, unary, unaryCell, filterBalanced]
  | source L => simp [cell, unaryCurrent, unary, unaryCell,
      LeafSquareReadout.sourceFilterBalanced, LeafSquareReadout.sourceFilter]
  | causal Q =>
    simp [cell, unaryCurrent, unaryCell, unary, filterBalanced, causal_hit]
  | shift k => exact congrArg (fun U => (_, _, U)) (successors_shift X k e.val)

/-- Every native unary primitive acts by a fixed linear push on complete time profiles. -/
theorem gamma_unary (f : Unary) (X : B) :
    gamma (unary f X).val = push (unaryCell f) (gamma X.val) := by
  simp only [gamma, map_sum, push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [← (unaryCurrent f X).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  rw [cell_unary]
  cases f <;> rfl

private theorem successors_parallel (X Y : B)
    (e : ↥X.val.1.current ⊕ ↥Y.val.1.current) :
    successors (ParallelComposition.parallelBalanced X Y).val.1
        (CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1 e).val =
      e.elim (fun a => successors X.val.1 a.val) (fun b => successors Y.val.1 b.val) := by
  dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel]
  ext a
  rw [mem_successors]
  rw [← Equiv.exists_congr_right
    (CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1)]
  cases e with
  | inl e =>
    dsimp only [Sum.elim_inl]
    rw [mem_successors]
    simp [CoarseObservation.parallelCurrentEquiv, ParallelComposition.context,
      TaggedPresentation.contextOf, TaggedPresentation.archiveOf,
      ParallelComposition.archive, ParallelComposition.equiv,
      ParallelComposition.internal, ParallelComposition.attributes]
  | inr e =>
    dsimp only [Sum.elim_inr]
    rw [mem_successors]
    simp [CoarseObservation.parallelCurrentEquiv, ParallelComposition.context,
      TaggedPresentation.contextOf, TaggedPresentation.archiveOf,
      ParallelComposition.archive, ParallelComposition.equiv,
      ParallelComposition.internal, ParallelComposition.attributes]

private theorem cell_parallel (X Y : B)
    (e : ↥X.val.1.current ⊕ ↥Y.val.1.current) :
    cell (ParallelComposition.parallelBalanced X Y).val
        (CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1 e) =
      e.elim (cell X.val) (cell Y.val) := by
  have hs := successors_parallel X Y e
  cases e with
  | inl e =>
    apply Prod.ext (ParallelComposition.attributes_left _ _ _)
    apply Prod.ext _ hs
    change decide (ParallelComposition.equiv _ _ (.inl e.val) ∈
      (X.val.2.val.disjSum Y.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding) = _
    simp [cell]
  | inr e =>
    apply Prod.ext (ParallelComposition.attributes_right _ _ _)
    apply Prod.ext _ hs
    change decide (ParallelComposition.equiv _ _ (.inr e.val) ∈
      (X.val.2.val.disjSum Y.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding) = _
    simp [cell]

/-- Parallel archives contribute their complete profiles independently. -/
theorem gamma_parallel (X Y : B) :
    gamma (ParallelComposition.parallelBalanced X Y).val = gamma X.val + gamma Y.val := by
  dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel]
  unfold gamma
  rw [← (CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1).sum_comp,
    Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
  · exact congrArg₂ Finsupp.single (cell_parallel X Y (.inl e))
      (congrArg (fun a : Attributes 3 => if a.positive then (1 : Int) else -1)
        (ParallelComposition.attributes_left _ _ _))
  · exact congrArg₂ Finsupp.single (cell_parallel X Y (.inr e))
      (congrArg (fun a : Attributes 3 => if a.positive then (1 : Int) else -1)
        (ParallelComposition.attributes_right _ _ _))

def productAttribute (a b : Attributes 3) : Attributes 3 where
  time := max a.time b.time + 1
  position i := a.position i + b.position i
  positive := a.positive == b.positive
  source := FreeMagma.mul a.source b.source

def productCell (x y : Cell) : Cell :=
  (productAttribute x.1 y.1, x.2.1 && y.2.1, {productAttribute x.1 y.1})

/-- Bilinear push from parent cells; the generated successor set is a singleton. -/
def productPush : Profile →ₗ[Int] Profile →ₗ[Int] Profile :=
  Finsupp.linearCombination Int (fun x : Cell =>
    Finsupp.linearCombination Int (fun y : Cell => Finsupp.single (productCell x y) 1))

private theorem productPush_single (a b : Cell) (m n : Int) :
    productPush (Finsupp.single a m) (Finsupp.single b n) =
      Finsupp.single (productCell a b) (m * n) := by
  simp [productPush, Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.smul_single, smul_eq_mul]

private theorem successors_product (X Y : B) (p : Parents X.val.1 Y.val.1) :
    successors (GeneratedProduct.productBalanced X Y).val.1
        (GeneratedProduct.generatedMap _ _ p) =
      {productAttribute (X.val.1.archive.attributes p.1.val)
        (Y.val.1.archive.attributes p.2.val)} := by
  ext a
  rw [mem_successors, Finset.mem_singleton]
  constructor
  · rintro ⟨d, h | h, ha⟩
    · rw [← h] at ha
      exact ha.symm.trans (GeneratedProduct.attributes_generated _ _ p)
    · obtain ⟨s, rfl⟩ := (CoarseObservation.generatedCurrentEquiv _ _).surjective d
      exact False.elim ((ProductPaths.generated_no_path _ _ p (.inr s))
        ((GeneratedProduct.causal_equiv _ _ (.inr p) (.inr s)).mp h))
  · intro ha
    refine ⟨CoarseObservation.generatedCurrentEquiv _ _ p, Or.inl rfl, ?_⟩
    exact (GeneratedProduct.attributes_generated _ _ p).trans ha.symm

private theorem cell_product (X Y : B) (p : Parents X.val.1 Y.val.1) :
    cell (GeneratedProduct.productBalanced X Y).val
        (CoarseObservation.generatedCurrentEquiv _ _ p) =
      productCell (cell X.val p.1) (cell Y.val p.2) := by
  apply Prod.ext (GeneratedProduct.attributes_generated _ _ p)
  apply Prod.ext _ (successors_product X Y p)
  change decide (GeneratedProduct.generatedMap _ _ p ∈
    (GeneratedProduct.selection X.val.2 Y.val.2).val) = _
  simp [productCell, cell, GeneratedProduct.generated_mem_selection]

/-- Native multiplication agrees with the bilinear profile interpretation. -/
theorem gamma_product (X Y : B) :
    gamma (GeneratedProduct.productBalanced X Y).val =
      productPush (gamma X.val) (gamma Y.val) := by
  dsimp only [GeneratedProduct.productBalanced, GeneratedProduct.product]
  simp only [gamma, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  rw [← (CoarseObservation.generatedCurrentEquiv X.val.1 Y.val.1).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  rw [productPush_single]
  apply congrArg₂ Finsupp.single (cell_product X Y (e, f))
  change (if ((GeneratedProduct.archive _ _).attributes
    (GeneratedProduct.generatedMap _ _ (e, f))).positive then (1 : Int) else -1) = _
  rw [GeneratedProduct.attributes_generated]
  exact generated_contribution _ _ (e, f)

/-- The extra coordinate homogenizes constants and parallel addition. -/
abbrev Augmented := Int × Profile

def pack (X : B) : Augmented := (1, gamma X.val)

private def unaryAugmented (f : Unary) : Augmented →ₗ[Int] Augmented :=
  (LinearMap.fst Int Int Profile).prod
    ((push (unaryCell f)).comp (LinearMap.snd Int Int Profile))

private def parallelAugmented : Augmented →ₗ[Int] Augmented →ₗ[Int] Augmented :=
  LinearMap.mk₂ Int (fun x y => (x.1 * y.1, y.1 • x.2 + x.1 • y.2))
    (by intros; apply Prod.ext (by dsimp; ring); simp [add_smul, smul_add]; abel)
    (by intros; apply Prod.ext (by simp [smul_eq_mul, mul_assoc]);
        simp [smul_add, smul_smul, mul_comm, mul_left_comm])
    (by intros; apply Prod.ext (by dsimp; ring); simp [add_smul, smul_add]; abel)
    (by intros; apply Prod.ext (by simp [smul_eq_mul, mul_left_comm, mul_assoc]);
        simp [smul_add, smul_smul, mul_comm, mul_left_comm])

private def productAugmented : Augmented →ₗ[Int] Augmented →ₗ[Int] Augmented :=
  LinearMap.mk₂ Int (fun x y => (x.1 * y.1, productPush x.2 y.2))
    (by intros; apply Prod.ext (by dsimp; ring); simp [map_add, LinearMap.add_apply])
    (by intros; apply Prod.ext (by simp [smul_eq_mul, mul_assoc]); simp)
    (by intros; apply Prod.ext (by dsimp; ring); simp)
    (by intros; apply Prod.ext (by simp [smul_eq_mul, mul_left_comm, mul_assoc]); simp)

private def join {n m : Nat} (b : Augmented →ₗ[Int] Augmented →ₗ[Int] Augmented)
    (f : MultilinearMap Int (fun _ : Fin n => Augmented) Augmented)
    (g : MultilinearMap Int (fun _ : Fin m => Augmented) Augmented) :
    MultilinearMap Int (fun _ : Fin (n + m) => Augmented) Augmented :=
  ((TensorProduct.lift b).compMultilinearMap (f.domCoprod g)).domDomCongr finSumFinEquiv

private theorem join_apply {n m : Nat}
    (b : Augmented →ₗ[Int] Augmented →ₗ[Int] Augmented)
    (f : MultilinearMap Int (fun _ : Fin n => Augmented) Augmented)
    (g : MultilinearMap Int (fun _ : Fin m => Augmented) Augmented)
    (v : Fin (n + m) → Augmented) :
    join b f g v = b (f (fun i => v (i.castAdd m))) (g (fun i => v (i.natAdd n))) := by
  simp [join, MultilinearMap.domDomCongr, MultilinearMap.domCoprod_apply]

/-- A syntax interpretation on homogenized profiles, with one distinct coordinate per leaf. -/
def model : {n : Nat} → CopyTerm n →
    MultilinearMap Int (fun _ : Fin n => Augmented) Augmented
  | _, .input => MultilinearMap.ofSubsingleton Int Augmented Augmented (0 : Fin 1) LinearMap.id
  | _, .param X => MultilinearMap.constOfIsEmpty Int _ (pack X)
  | _, .unary f a => (unaryAugmented f).compMultilinearMap (model a)
  | _, .binary .product a b => join productAugmented (model a) (model b)
  | _, .binary _ a b => join parallelAugmented (model a) (model b)

/-- The abstract multilinear interpretation computes the actual native finite time profile. -/
theorem model_eval {n : Nat} (N : CopyTerm n) (h : TemporalFree N)
    (v : Fin n → B) (Y : B) (he : eval N v = some Y) :
    model N (fun i => pack (v i)) = pack Y := by
  induction N generalizing Y with
  | input => cases Option.some.inj he; rfl
  | param X => cases Option.some.inj he; rfl
  | unary f a ih =>
    change (eval a v).map (unary f) = some Y at he
    obtain ⟨X, hx, rfl⟩ := Option.map_eq_some_iff.mp he
    change unaryAugmented f (model a (fun i => pack (v i))) = _
    rw [ih h v X hx]
    change (1, push (unaryCell f) (gamma X.val)) = (1, gamma (unary f X).val)
    exact congrArg (fun z : Profile => ((1 : Int), z)) (gamma_unary f X).symm
  | @binary n m f a b iha ihb =>
    change (eval a (fun i => v (i.castAdd m))).bind
      (fun x => (eval b (fun i => v (i.natAdd n))).bind (binary f x)) = some Y at he
    obtain ⟨X, hx, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨Z, hz, he⟩ := Option.bind_eq_some_iff.mp he
    have ha := iha h.2.1 (fun i => v (i.castAdd m)) X hx
    have hb := ihb h.2.2 (fun i => v (i.natAdd n)) Z hz
    cases f with
    | parallel =>
      cases Option.some.inj he
      change join parallelAugmented (model a) (model b) _ = _
      rw [join_apply, ha, hb]
      apply Prod.ext (by simp [pack, parallelAugmented])
      simpa [parallelAugmented, pack] using (gamma_parallel X Z).symm
    | product =>
      cases Option.some.inj he
      change join productAugmented (model a) (model b) _ = _
      rw [join_apply, ha, hb]
      apply Prod.ext (by simp [pack, productAugmented])
      exact (gamma_product X Z).symm
    | temporal => exact (h.1 rfl).elim


end
end D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
