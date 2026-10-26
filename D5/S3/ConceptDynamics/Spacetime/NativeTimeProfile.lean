/- GID: D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/NativeTimeProfile
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Finite signed time profiles retain selection and all current successor attributes under native operations. -/

import D5.S3.ConceptDynamics.Spacetime.CoarseObservation
import D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
import D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
import Mathlib.Algebra.Polynomial.Roots
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



open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge TotalCopyNormalization RegionFilterQExpressibility
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Bal := TotalCopyNormalization.B

/-- The diagonal operation that supplies `m` tagged parallel copies of one input. -/
def copies : Nat → Bal → Bal
  | 0, _ => zero
  | n + 1, X => ParallelComposition.parallelBalanced (copies n X) X

/-- The total value of a copy term under an arbitrary independent assignment. -/
def value {r : Nat} (N : CopyTerm r) (v : Fin r → Bal) : Bal :=
  (eval N v).getD zero

/--
The 5B/5C bridge used by the copy argument. It says that a temporal-free
term, evaluated on independently replicated leaves, has an integer polynomial
profile.  The displayed coefficient is the full 5C coefficient and retains the
constant correction `- r * q(N(0))`.
-/
def CopyPolynomialLaw : Prop := ∀ (r : Nat) (N : CopyTerm r), 0 < r → TemporalFree N →
  ∀ X : Bal, ∃ P : Polynomial Int,
    P.natDegree ≤ r ∧
    (∀ n : Nat, P.eval (n : Int) = q (value N (fun _ => copies n X)).val) ∧
    P.coeff 0 = q (zeroValue N).val ∧
    P.coeff 1 = (∑ i : Fin r, q (value N (sliceAssignment i X)).val) -
      (r : Int) * q (zeroValue N).val

private def diagonalPolynomial {r : Nat} {M : Type*} [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) : Polynomial Int :=
  ∑ J : Finset (Fin r), Polynomial.C (f (J.piecewise b a)) * Polynomial.X ^ J.card

private theorem diagonalPolynomial_degree {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).natDegree ≤ r := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro J _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by simpa using J.card_le_univ)

private theorem diagonalPolynomial_eval {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) (m : Int) :
    (diagonalPolynomial f a b).eval m = f (fun i => a i + m • b i) := by
  simp only [diagonalPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (fun i => a i + m • b i) = (fun i => m • b i) + a from
    funext (fun i => add_comm _ _), f.map_add_univ]
  apply Finset.sum_congr rfl
  intro J _
  have h := f.map_piecewise_smul (fun _ => m) (J.piecewise b a) J
  have hv : J.piecewise (fun i => m • J.piecewise b a i) (J.piecewise b a) =
      J.piecewise (fun i => m • b i) a := by
    funext i
    by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi]
  have hh := (congrArg f hv).symm.trans h
  simpa [smul_eq_mul, mul_comm] using hh.symm

private theorem diagonalPolynomial_zero {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).coeff 0 = f a := by
  rw [Polynomial.coeff_zero_eq_eval_zero, diagonalPolynomial_eval]
  simp

private theorem diagonalPolynomial_one {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).coeff 1 =
      (∑ i, f (Function.update a i (a i + b i))) - (r : Int) * f a := by
  have hs : (Finset.univ.filter (fun J : Finset (Fin r) => 1 = J.card)) =
      Finset.univ.image (fun i : Fin r => ({i} : Finset (Fin r))) := by
    ext J
    simp [eq_comm, Finset.card_eq_one]
  have hcoeff : (diagonalPolynomial f a b).coeff 1 =
      ∑ i : Fin r, f (Function.update a i (b i)) := by
    simp only [diagonalPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter, hs, Finset.sum_image]
    · simp only [Finset.piecewise_singleton]
    · intro i _ j _ h
      exact Finset.singleton_injective h
  rw [hcoeff]
  simp only [f.map_update_add, Function.update_eq_self, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem gamma_zero : gamma zero.val = 0 := by
  haveI : IsEmpty ↥zero.val.1.current := Finset.isEmpty_coe_sort.mpr zero_empty.2.1
  exact Finset.sum_eq_zero (fun e _ => isEmptyElim e)

private theorem gamma_copies (n : Nat) (X : Bal) :
    gamma (copies n X).val = (n : Int) • gamma X.val := by
  induction n with
  | zero => simp [copies, gamma_zero]
  | succ n ih =>
    rw [copies, gamma_parallel, ih]
    simp [Nat.cast_add, add_smul]

private def basePoint : Augmented := (1, 0)
private def inputPoint (X : Bal) : Augmented := (0, gamma X.val)

private def profileModel {r : Nat} (N : CopyTerm r) :
    MultilinearMap Int (fun _ : Fin r => Augmented) Profile :=
  (LinearMap.snd Int Int Profile).compMultilinearMap (model N)

/-- The coefficient at a set of distinct input occurrences in the complete profile expansion. -/
def profileCoefficients {r : Nat} (N : CopyTerm r) (X : Bal) (J : Finset (Fin r)) : Profile :=
  profileModel N (J.piecewise (fun _ => inputPoint X) (fun _ => basePoint))

/-- Native evaluation on independently many tagged copies has a squarefree profile expansion. -/
theorem profile_multiaffine {r : Nat} (N : CopyTerm r) (hN : TemporalFree N) (X : Bal)
    (v : Fin r → Nat) :
    gamma (value N (fun i => copies (v i) X)).val =
      ∑ J : Finset (Fin r), (∏ i ∈ J, (v i : Int)) • profileCoefficients N X J := by
  let a : Fin r → Augmented := fun _ => basePoint
  let b : Fin r → Augmented := fun _ => inputPoint X
  let f := profileModel N
  have native : gamma (value N (fun i => copies (v i) X)).val =
      f (fun i => a i + (v i : Int) • b i) := by
    obtain ⟨Y, hY⟩ := temporal_free_total N hN (fun i => copies (v i) X)
    have hm := model_eval N hN (fun i => copies (v i) X) Y hY
    have hp : (fun i => pack (copies (v i) X)) =
        (fun i => a i + (v i : Int) • b i) := by
      funext i
      simp [pack, a, b, basePoint, inputPoint, gamma_copies]
    rw [hp] at hm
    simpa only [value, hY, Option.getD_some, pack, f, profileModel,
      LinearMap.compMultilinearMap_apply, LinearMap.snd_apply] using
        (congrArg Prod.snd hm).symm
  rw [native]
  have hab : (fun i => a i + (v i : Int) • b i) =
      (fun i => (v i : Int) • b i) + a := funext (fun i => add_comm _ _)
  rw [hab, f.map_add_univ]
  apply Finset.sum_congr rfl
  intro J _
  have hs := f.map_piecewise_smul (fun i => (v i : Int)) (J.piecewise b a) J
  have hv : J.piecewise (fun i => (v i : Int) • J.piecewise b a i) (J.piecewise b a) =
      J.piecewise (fun i => (v i : Int) • b i) a := by
    funext i
    by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi]
  exact (congrArg f hv).symm.trans hs

/-- Lemma 5B/5C, including the constant correction in the linear coefficient. -/
theorem copy_polynomial_law : CopyPolynomialLaw := by
  intro r N _ hN X
  let a : Fin r → Augmented := fun _ => basePoint
  let b : Fin r → Augmented := fun _ => inputPoint X
  let f := NativeTimeProfile.readout.compMultilinearMap (profileModel N)
  have native (v : Fin r → Bal) :
      f (fun i => pack (v i)) = q (value N v).val := by
    obtain ⟨Y, hY⟩ := temporal_free_total N hN v
    change NativeTimeProfile.readout ((model N (fun i => pack (v i))).2) = _
    rw [model_eval N hN v Y hY]
    simpa [value, hY, pack] using readout_gamma Y.val
  have fzero : f a = q (zeroValue N).val := by
    have hv := native (fun _ => zero)
    simpa [a, pack, basePoint, gamma_zero, value, zeroValue, evalDiagonal] using hv
  have fslice (i : Fin r) : f (Function.update a i (a i + b i)) =
      q (value N (sliceAssignment i X)).val := by
    apply Eq.trans _ (native (sliceAssignment i X))
    apply congrArg f
    funext j
    by_cases hji : j = i <;>
      simp [Function.update_apply, a, b, basePoint, inputPoint, pack,
        sliceAssignment, hji, gamma_zero]
  refine ⟨diagonalPolynomial f a b, diagonalPolynomial_degree f a b, ?_, ?_, ?_⟩
  · intro m
    have hp := congrArg NativeTimeProfile.readout (profile_multiaffine N hN X (fun _ => m))
    rw [readout_gamma] at hp
    rw [hp]
    simp only [diagonalPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro J _
    simp [f, a, b, profileCoefficients, smul_eq_mul, mul_comm]
  · exact (diagonalPolynomial_zero f a b).trans fzero
  · rw [diagonalPolynomial_one, fzero]
    simp only [fslice]

/-- Parallel replication is linear for every fixed region readout. -/
def CopiesRegionLinear : Prop := ∀ (R : Region) (n : Nat) (X : Bal),
  regionReadout R (copies n X) = (n : Int) * regionReadout R X

/-- A readout of a total one-hole word, with failure assigned the neutral integer. -/
def wordReadout (w : Word) (X : Bal) : Int :=
  ((contextDenote nativeSignature w X).map (fun Y => q Y.val)).getD 0

/--
The post-polynomial normalization statement needed by the tail argument.  It
keeps the exact finite family of temporal-free one-hole words and the exact
sum of their readouts.
-/
def CopySliceReadoutLaw : Prop := ∀ (R : Region) (n : Nat) (C : CopyTerm n), 0 < n →
  DiagonalTotal C →
  (∀ X : Bal, ∃ Y : Bal, evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X) →
  ∃ w : Fin n → Word,
    (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) ∧
    ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X

/-- The finite joint saturation principle used after slice normalization. -/
def CopySaturationLaw : Prop := ∀ {ι : Type} [Fintype ι] (w : ι → Word),
  (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) →
  ∃ c : Int, c ≤ 0 ∧ ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
    ∃ X Y : Bal, SelectedVariant X Y p t t' ∧
      ∀ i, wordReadout (w i) X = wordReadout (w i) Y

/-- The copy form of Proposition 64. -/
def CopyQExpressible (R : Region) : Prop := ∃ n : Nat, 0 < n ∧ ∃ C : CopyTerm n,
  DiagonalTotal C ∧ ∀ X : Bal, ∃ Y : Bal,
    evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X

/-- Polynomial identification from all natural evaluations. -/
theorem polynomial_identification (P : Polynomial Int) (a : Int)
    (h : ∀ n : Nat, P.eval (n : Int) = (n : Int) * a) :
    P = Polynomial.X * Polynomial.C a := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Int.ofNat_injective).mono
  rintro _ ⟨n, rfl⟩
  simpa using h n

private theorem region_parallel (R : Region) (X Y : Bal) :
    regionReadout R (ParallelComposition.parallelBalanced X Y) =
      regionReadout R X + regionReadout R Y := by
  unfold regionReadout
  simp only [Finset.sum_filter]
  change (∑ e ∈ (X.val.2.val.disjSum Y.val.2.val).map
      (ParallelComposition.equiv X.val.1.archive Y.val.1.archive).toEmbedding,
      if (((ParallelComposition.archive X.val.1.archive Y.val.1.archive).attributes e).time,
          ((ParallelComposition.archive X.val.1.archive Y.val.1.archive).attributes e).position) ∈ R
      then contribution (ParallelComposition.context X.val.1 Y.val.1) e else 0) = _
  rw [Finset.sum_map, Finset.sum_disjSum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
  · exact congrArg (fun a : Attributes 3 => if (a.time, a.position) ∈ R
        then (if a.positive then (1 : Int) else -1) else 0)
      (ParallelComposition.attributes_left _ _ e)
  · exact congrArg (fun a : Attributes 3 => if (a.time, a.position) ∈ R
        then (if a.positive then (1 : Int) else -1) else 0)
      (ParallelComposition.attributes_right _ _ e)

/-- Every fixed region readout is integer-linear in the number of tagged copies. -/
theorem copies_region_linear : CopiesRegionLinear := by
  intro R n X
  induction n with
  | zero => simp [copies, regionReadout, zero_empty.2.2]
  | succ n ih => rw [copies, region_parallel, ih]; push_cast; ring

/-- Lemma 6: the existing finite predicate construction saturates a whole finite word family. -/
theorem copy_saturation_law : CopySaturationLaw := by
  intro ι _ w hw
  have hn := fun i => normalize_word (w i) (hw i)
  choose w' hf he using hn
  have hr := fun i => reify_temporal_free (w' i) (hf i)
  choose v hv using hr
  obtain ⟨K, hK⟩ := Finite.exists_ge (fun i => timeThreshold (v i))
  let Qs := Finset.univ.toList.flatMap (fun i => requiredPredicates (v i))
  obtain ⟨c, hc, hs⟩ := finite_joint_input Qs (min K 0)
  refine ⟨c, hc.trans (min_le_right K 0), fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, h, hx, hy, sat⟩ := hs p t t' ht ht'
  refine ⟨X, Y, pair, fun i => ?_⟩
  unfold wordReadout
  rw [he i X, he i Y, hv i X, hv i Y]
  change q (runSteps (v i) X).val = q (runSteps (v i) Y).val
  apply saturated_runSteps (v i) h
  · rw [hx]
    exact ht.trans_le (hc.trans ((min_le_left K 0).trans (hK i)))
  · rw [hy]
    exact ht'.trans_le (hc.trans ((min_le_left K 0).trans (hK i)))
  · intro Q hQ hnQ
    apply sat Q _ hnQ
    exact List.mem_flatMap.mpr ⟨i, by simp, hQ⟩

/-- The polynomial linear coefficient recovers the fixed finite family of one-hole slices. -/
theorem copy_slice_readout_law : CopySliceReadoutLaw := by
  intro R n C hn ht hC
  obtain ⟨_, _, _, N, _, hN, he, hAll, w, _, hw, hwTotal, _⟩ :=
    total_copy_normalization C hn ht
  refine ⟨w, hwTotal, fun X => ?_⟩
  obtain ⟨P, _, hP, hP0, hP1⟩ := copy_polynomial_law n N hn hN X
  have evals : ∀ m : Nat, P.eval (m : Int) = (m : Int) * regionReadout R X := by
    intro m
    obtain ⟨Y, hY, hq⟩ := hC (copies m X)
    rw [hP m]
    have hNY : eval N (fun _ => copies m X) = some Y := (he _).symm.trans hY
    simp only [value, hNY, Option.getD_some]
    rw [hq, copies_region_linear]
  have pEq := polynomial_identification P (regionReadout R X) evals
  have zeroQ : q (zeroValue N).val = 0 := by
    rw [← hP0, pEq]
    simp
  have coeff1 : P.coeff 1 = regionReadout R X := by rw [pEq]; simp
  rw [coeff1, zeroQ, mul_zero, sub_zero] at hP1
  rw [hP1]
  apply Finset.sum_congr rfl
  intro i _
  unfold wordReadout value
  rw [hw i X]
  obtain ⟨Y, hY⟩ := hAll (sliceAssignment i X)
  rw [hY]
  rfl

/-- A finite sum of total word readouts is a tail readout. -/
theorem sum_word_readouts_implies_tail
    (R : Region) {ι : Type} [Fintype ι]
    (w : ι → Word)
    (hw : ∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y)
    (hsum : ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X) : Tail R := by
  obtain ⟨c, _, hc⟩ := copy_saturation_law (ι := ι) w hw
  refine ⟨c, fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, same⟩ := hc p t t' ht ht'
  have values : regionReadout R X = regionReadout R Y := by
    rw [hsum X, hsum Y]
    exact Finset.sum_congr rfl (fun i _ => same i)
  obtain ⟨hX, hY⟩ := selected_region_values R X Y p t t' pair
  rw [hX, hY] at values
  split_ifs at values <;> simp_all

/-- Necessity of the copy criterion. -/
theorem copy_q_expressible_implies_tail
    (R : Region) (hR : CopyQExpressible R) : Tail R := by
  obtain ⟨n, hn, C, ht, hC⟩ := hR
  obtain ⟨w, hw, hsum⟩ := copy_slice_readout_law R n C hn ht hC
  exact sum_word_readouts_implies_tail R w hw hsum

/-- Tail regions are copy-expressible by the existing one-hole construction. -/
theorem tail_implies_copy_q_expressible (R : Region) (hR : Tail R) :
    CopyQExpressible R := by
  obtain ⟨w, hw⟩ := (q_expressible_iff_tail R).mpr hR
  refine ⟨1, by decide, wordToCopy w, ?_, ?_⟩
  · intro X
    obtain ⟨Y, hY, _⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY⟩
  · intro X
    obtain ⟨Y, hY, hq⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY, hq⟩




/-- Proposition 64 with no profile or saturation assumptions. -/
theorem proposition64 (R : Region) :
    CopyQExpressible R ↔ Tail R := by
  constructor
  · exact copy_q_expressible_implies_tail R
  · exact tail_implies_copy_q_expressible R

/-- The copy criterion agrees with the existing one-hole criterion and the tail condition. -/
theorem proposition64_three_way (R : Region) :
    CopyQExpressible R ↔ QExpressible R ∧ Tail R := by
  constructor
  · intro h
    have ht : Tail R := copy_q_expressible_implies_tail R h
    exact ⟨(q_expressible_iff_tail R).mpr ht, ht⟩
  · rintro ⟨_, ht⟩
    exact tail_implies_copy_q_expressible R ht


end
end D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
