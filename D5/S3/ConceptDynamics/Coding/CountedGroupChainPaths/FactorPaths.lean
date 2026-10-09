/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ordered factor paths and reversible peeling of finite group-ring chains. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths

open CountedGroupOverlap
open RectangularNilpotenceBarrier

universe u
variable {H : Type u} [Group H] [Fintype H]

inductive Factors (H : Type u) [Group H] : ℕ → ℕ → ℕ → Type u where
  | nil (n : ℕ) : Factors H n n 0
  | cons {n k m L : ℕ} (M : GroupMat H n k) (tail : Factors H k m L) :
      Factors H n m (L + 1)

/-- Multiplication follows the order of the factor sequence. -/
noncomputable def factorProduct {n m L : ℕ} : Factors H n m L → GroupMat H n m
  | .nil _ => 1
  | .cons M tail => M * (factorProduct tail)

/-- Append one actual matrix at the right-hand end. -/
def factorSnoc {n k m L : ℕ} (a : Factors H n k L) (M : GroupMat H k m) :
    Factors H n m (L + 1) :=
  match a with
  | .nil _ => .cons M (.nil _)
  | .cons N tail => .cons N ((factorSnoc tail) M)

omit [Fintype H] in
private theorem product_snoc {n k m L : ℕ}
    (a : Factors H n k L) (M : GroupMat H k m) :
    (factorProduct ((factorSnoc a) M)) = (factorProduct a) * M := by
  induction a with
  | nil _ => simp [factorSnoc, factorProduct]
  | cons N tail ih => simp only [factorSnoc, factorProduct, ih, Matrix.mul_assoc]

/-- Each path is typed by its endpoints. The empty path contains its named vertex.
For a nonempty path the coordinates are middle vertex, first label, first copy,
then the complete remaining path. -/
def FactorPath {n m L : ℕ} (f : Factors H n m L) (i : Fin n) (j : Fin m) : Type u :=
  match f with
  | .nil _ => ULift.{u} {v : Fin n // v = i ∧ v = j}
  | @Factors.cons _ _ _ k _ _ M tail =>
      Lex (Σ v : Fin k, Lex (Σ h : H,
        Lex (Fin ((M i v).coeff h) × (FactorPath tail) v j)))

/-- Group labels multiply from left to right, including in a nonabelian group. -/
def factorLabel : {n m L : ℕ} → (f : Factors H n m L) →
    {i : Fin n} → {j : Fin m} → (FactorPath f) i j → H
  | _, _, _, .nil _, _, _, _ => 1
  | _, _, _, .cons _ tail, _, _, p => p.2.1 * (factorLabel tail) p.2.2.2

/-- The named zero-edge path at vertex i. -/
def nilPath {n : ℕ} (i : Fin n) : (FactorPath (Factors.nil (H := H) n)) i i :=
  ⟨⟨i, rfl, rfl⟩⟩

/-- An actual first edge and its typed tail; no edge-copy number is forgotten. -/
def consPath {n k m L : ℕ} (M : GroupMat H n k) (tail : Factors H k m L)
    (e : Edge M) {j : Fin m} (p : (FactorPath tail) e.target j) :
    (FactorPath (Factors.cons M tail)) e.source j :=
  ⟨e.target, e.label, e.number, p⟩

noncomputable instance pathFintype {n m L : ℕ} (f : Factors H n m L)
    (i : Fin n) (j : Fin m) : Fintype ((FactorPath f) i j) := by
  classical
  induction f with
  | nil n => exact inferInstanceAs (Fintype (ULift {v : Fin n // v = i ∧ v = j}))
  | @cons n k m L M tail ih =>
      letI : ∀ v : Fin k, Fintype ((FactorPath tail) v j) := fun v => ih v j
      exact inferInstanceAs (Fintype
        (Lex (Σ v : Fin k, Lex (Σ h : H,
          Lex (Fin ((M i v).coeff h) × (FactorPath tail) v j)))))

noncomputable instance pathLinearOrder [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) :
    LinearOrder (FactorPath f i j) :=
  @Factors.rec H _
    (fun n m _ f => ∀ i : Fin n, ∀ j : Fin m, LinearOrder (FactorPath f i j))
    (fun n i j =>
      (inferInstance : LinearOrder (ULift {v : Fin n // v = i ∧ v = j})))
    (fun {_ k _ _} M tail ih i j =>
      letI : ∀ v : Fin k, LinearOrder (FactorPath tail v j) := fun v => ih v j
      (inferInstance : LinearOrder
        (Lex (Σ v : Fin k, Lex (Σ h : H,
          Lex (Fin ((M i v).coeff h) × FactorPath tail v j))))))
    n m L f i j

/-- The complete endpoint and total-label fiber, before any ranking. -/
def FactorFiber {n m L : ℕ} (f : Factors H n m L) (i : Fin n) (j : Fin m) (g : H) :=
  {p : (FactorPath f) i j // (factorLabel f) p = g}

noncomputable instance fiberFintype {n m L : ℕ} (f : Factors H n m L)
    (i : Fin n) (j : Fin m) (g : H) : Fintype ((FactorFiber f) i j g) := by
  classical
  unfold FactorFiber
  infer_instance

noncomputable instance fiberLinearOrder [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) (g : H) :
    LinearOrder (FactorFiber f i j g) :=
  inferInstanceAs (LinearOrder {p : FactorPath f i j // factorLabel f p = g})

def fiberConsEquiv {n k m L : ℕ} (M : GroupMat H n k)
    (tail : Factors H k m L) (i : Fin n) (j : Fin m) (g : H) :
    (FactorFiber (Factors.cons M tail)) i j g ≃
      Σ v : Fin k, Σ h : H, Fin ((M i v).coeff h) × (FactorFiber tail) v j (h⁻¹ * g) where
  toFun p := ⟨p.val.1, p.val.2.1, p.val.2.2.1,
    ⟨p.val.2.2.2, by
      have hp := p.property
      change p.val.2.1 * (factorLabel tail) p.val.2.2.2 = g at hp
      simpa [mul_assoc] using congrArg (fun x => p.val.2.1⁻¹ * x) hp⟩⟩
  invFun p := ⟨consPath M tail ⟨i, p.1, p.2.1, p.2.2.1⟩ p.2.2.2.val, by
    change p.2.1 * (factorLabel tail) p.2.2.2.val = g
    rw [p.2.2.2.property]
    simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coefficients count every actual heterogeneous path, including empty fibers. -/
theorem fiber_card {n m L : ℕ} (f : Factors H n m L)
    (i : Fin n) (j : Fin m) (g : H) :
    Fintype.card ((FactorFiber f) i j g) = ((factorProduct f) i j).coeff g := by
  classical
  induction f generalizing g with
  | nil n =>
      by_cases hij : i = j
      · subst j
        by_cases hg : g = 1
        · subst g
          let : Unique ((FactorFiber (Factors.nil (H := H) n)) i i 1) :=
            { default := ⟨nilPath i, rfl⟩
              uniq := by
                intro p
                apply Subtype.ext
                apply ULift.ext
                apply Subtype.ext
                exact p.val.down.property.1 }
          simp [factorProduct]
        · let : IsEmpty ((FactorFiber (Factors.nil (H := H) n)) i i g) :=
            ⟨fun p => hg p.property.symm⟩
          simp [factorProduct, MonoidAlgebra.one_def, hg]
      · let : IsEmpty ((FactorFiber (Factors.nil (H := H) n)) i j g) :=
          ⟨fun p => hij (p.val.down.property.1.symm.trans p.val.down.property.2)⟩
        simp [factorProduct, hij]
  | @cons n k m L M tail ih =>
      rw [Fintype.card_congr (fiberConsEquiv M tail i j g)]
      simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, ih]
      have coeff_product (a b : MonoidAlgebra ℕ H) :
          (a * b).coeff g = ∑ h : H, a.coeff h * b.coeff (h⁻¹ * g) := by
        rw [MonoidAlgebra.coeff_mul_apply_left]
        exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
      simp [factorProduct, Matrix.mul_apply, coeff_product]

/-- The increasing rank on the complete path fiber. -/
noncomputable def rankedFiberOrderIso [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) (g : H) :
    Fin (((factorProduct f) i j).coeff g) ≃o (FactorFiber f) i j g :=
  Fintype.orderIsoFinOfCardEq _ (fiber_card f i j g)

/-- One increasing enumeration of the WHOLE actual path fiber. Its order is the
lexicographic order on all original edge coordinates, not iterated binary ranks. -/
noncomputable def rankedFiberEquiv [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) (g : H) :
    Fin (((factorProduct f) i j).coeff g) ≃ (FactorFiber f) i j g :=
  (rankedFiberOrderIso f i j g).toEquiv

/-- Standard numbered matrix edges and complete factor paths have the same endpoints
and total group label. The inverse recovers every original factor copy number. -/
noncomputable def edgePathEquiv [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) :
    Edge (factorProduct f) ≃ Σ i : Fin n, Σ j : Fin m, Σ g : H, (FactorFiber f) i j g :=
  (edgeCoordinates (factorProduct f)).trans (Equiv.sigmaCongrRight fun i =>
    Equiv.sigmaCongrRight fun j => Equiv.sigmaCongrRight fun g =>
      rankedFiberEquiv f i j g)

/-- Actual prescribed SSE data live in Type. Each step retains its two factors,
its source and intermediate matrices, and BOTH original factor equalities. -/
inductive Chain (H : Type u) [Group H] [Fintype H] :
    {n m : ℕ} → GroupMat H n n → GroupMat H m m → ℕ → Type u where
  | nil {n : ℕ} (A : GroupMat H n n) : Chain H A A 0
  | cons {n k m L : ℕ} {A : GroupMat H n n} {B : GroupMat H k k}
      {C : GroupMat H m m} (U : GroupMat H n k) (V : GroupMat H k n)
      (leftFactor : A = U * V) (rightFactor : B = V * U)
      (tail : Chain H B C L) : Chain H A C (L + 1)

/-- U factors retain their original increasing layer order. -/
def forwardFactors {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m} :
    Chain H A B L → Factors H n m L
  | .nil _ => .nil _
  | .cons U _ _ _ tail => .cons U (forwardFactors tail)

/-- V factors retain their original decreasing layer order. -/
def backwardFactors {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m} :
    Chain H A B L → Factors H m n L
  | .nil _ => .nil _
  | .cons _ V _ _ tail => (factorSnoc (backwardFactors tail)) V

noncomputable def R {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) : GroupMat H n m := (factorProduct (forwardFactors c))

noncomputable def S {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) : GroupMat H m n := (factorProduct (backwardFactors c))

/-- The four rectangular cumulative identities hold for the same retained chain. -/
theorem cumulative_equations {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) :
    A * (R c) = (R c) * B ∧ B * (S c) = (S c) * A ∧
      (R c) * (S c) = A ^ L ∧ (S c) * (R c) = B ^ L := by
  induction c with
  | nil A => simp [R, S, forwardFactors, backwardFactors, factorProduct]
  | @cons n k m L A B C U V hA hB tail ih =>
      have hR : (R (Chain.cons U V hA hB tail)) = U * (R tail) := rfl
      have hS : (S (Chain.cons U V hA hB tail)) = (S tail) * V := by
        simp [S, backwardFactors, product_snoc]
      rw [hR, hS]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc U V U, ← hB,
          Matrix.mul_assoc, ih.1]
        simp only [Matrix.mul_assoc]
      · rw [← Matrix.mul_assoc, ih.2.1]
        simp only [Matrix.mul_assoc, hA, hB]
      · calc
          (U * (R tail)) * ((S tail) * V) = U * ((R tail) * (S tail)) * V := by
            simp only [Matrix.mul_assoc]
          _ = U * B ^ L * V := by rw [ih.2.2.1]
          _ = A ^ (L + 1) := by
            rw [hA, hB, rectangular_exchange_power]
      · calc
          ((S tail) * V) * (U * (R tail)) = (S tail) * B * (R tail) := by
            simp only [hB, Matrix.mul_assoc]
          _ = (S tail) * ((R tail) * C) := by rw [Matrix.mul_assoc, ih.1]
          _ = ((S tail) * (R tail)) * C := by rw [Matrix.mul_assoc]
          _ = C ^ (L + 1) := by rw [ih.2.2.2, pow_succ]

/-- The original indexed telescope d_j,A_j,U_j,V_j, with no positivity assumption. -/
structure IndexedChain (H : Type u) [Group H] [Fintype H] (L : ℕ) where
  d : Fin (L + 1) → ℕ
  A : (j : Fin (L + 1)) → GroupMat H (d j) (d j)
  U : (j : Fin L) → GroupMat H (d j.castSucc) (d j.succ)
  V : (j : Fin L) → GroupMat H (d j.succ) (d j.castSucc)
  leftFactor : ∀ j, A j.castSucc = U j * V j
  rightFactor : ∀ j, A j.succ = V j * U j

/-- Removing the first layer preserves the actual indexed factors and equalities. -/
def tail {L : ℕ} (c : IndexedChain H (L + 1)) : IndexedChain H L where
  d j := c.d j.succ
  A j := c.A j.succ
  U j := c.U j.succ
  V j := c.V j.succ
  leftFactor j := c.leftFactor j.succ
  rightFactor j := c.rightFactor j.succ

/-- Inspectable recursion on the supplied chain, retaining every prescribed step. -/
def toChain : {L : ℕ} → (c : IndexedChain H L) →
    Chain H (c.A 0) (c.A (Fin.last L)) L
  | 0, c => .nil (c.A 0)
  | _L + 1, c => .cons (c.U 0) (c.V 0) (c.leftFactor 0) (c.rightFactor 0)
      (toChain (tail c))

/-- A numbered edge with its two endpoints fixed. -/
abbrev At {n m : ℕ} (M : GroupMat H n m) (i : Fin n) (j : Fin m) :=
  Σ g : H, Fin ((M i j).coeff g)

/-- The prescribed local increasing rank, with both labels retained separately. -/
noncomputable def orderedAtEquiv [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (i j : Fin n) :
    At (U * V) i j ≃ Σ v : Fin k, At U i v × At V v j := by
  let rearrange : (Σ g : H, Fiber U V i j g) ≃
      Σ v : Fin k, Σ h : H, Fin ((U i v).coeff h) ×
        (Σ g : H, Fin ((V v j).coeff (h⁻¹ * g))) := {
    toFun := fun p => ⟨p.2.1, p.2.2.1, p.2.2.2.1, p.1, p.2.2.2.2⟩
    invFun := fun p => ⟨p.2.2.2.1, p.1, p.2.1, p.2.2.1, p.2.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let labels : (Σ v : Fin k, Σ h : H, Fin ((U i v).coeff h) ×
      (Σ g : H, Fin ((V v j).coeff (h⁻¹ * g)))) ≃
      Σ v : Fin k, Σ h : H, Fin ((U i v).coeff h) × At V v j :=
    Equiv.sigmaCongrRight fun v => Equiv.sigmaCongrRight fun h =>
      Equiv.prodCongr (Equiv.refl _) (Equiv.sigmaCongr (Equiv.mulLeft h⁻¹)
        (fun _ => Equiv.refl _))
  let pairs : (Σ v : Fin k, Σ h : H, Fin ((U i v).coeff h) × At V v j) ≃
      Σ v : Fin k, At U i v × At V v j := {
    toFun := fun p => ⟨p.1, ⟨p.2.1, p.2.2.1⟩, p.2.2.2⟩
    invFun := fun p => ⟨p.1, p.2.1.1, p.2.1.2, p.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sigmaCongrRight (fun g => orderedFiberEquiv U V i j g)).trans
    (rearrange.trans (labels.trans pairs))

/-- Unpack the first actual factor edge, retaining the complete tail. -/
def pathHeadEquiv {n k m L : ℕ} (M : GroupMat H n k) (f : Factors H k m L)
    (i : Fin n) (j : Fin m) :
    FactorPath (Factors.cons M f) i j ≃ Σ v : Fin k, At M i v × FactorPath f v j where
  toFun p := ⟨p.1, ⟨p.2.1, p.2.2.1⟩, p.2.2.2⟩
  invFun p := ⟨p.1, p.2.1.1, p.2.1.2, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A square-matrix word, including its named zero-edge vertex. -/
def wordFactors {n : ℕ} (A : GroupMat H n n) : (l : ℕ) → Factors H n n l
  | 0 => .nil n
  | l + 1 => .cons A (wordFactors A l)

abbrev Word {n : ℕ} (A : GroupMat H n n) (l : ℕ) (i j : Fin n) :=
  FactorPath (wordFactors A l) i j

/-- Remove a named nil segment at the right endpoint. -/
def rightNilEquiv {n m : ℕ} (M : GroupMat H n m) (i : Fin n) (j : Fin m) :
    (Σ v : Fin m, At M i v × Word (0 : GroupMat H m m) 0 v j) ≃ At M i j where
  toFun p := (p.2.2.down.property.1.symm.trans p.2.2.down.property.2) ▸ p.2.1
  invFun e := ⟨j, e, nilPath j⟩
  left_inv p := by
    rcases p with ⟨v, e, ⟨⟨w, hwv, hwj⟩⟩⟩
    subst w
    subst v
    rfl
  right_inv _ := rfl

/-- Append a last actual edge to a factor path, and split it back off. -/
noncomputable def pathSnocEquiv {n k m L : ℕ} (f : Factors H n k L) (M : GroupMat H k m)
    (i : Fin n) (j : Fin m) :
    FactorPath (factorSnoc f M) i j ≃ Σ v : Fin k, FactorPath f i v × At M v j := by
  induction f generalizing m with
  | nil n =>
    let remove : (Σ v : Fin n, FactorPath (Factors.nil (H := H) n) i v × At M v j) ≃
        At M i j := {
      toFun := fun p => (p.2.1.down.property.1.symm.trans
        p.2.1.down.property.2).symm ▸ p.2.2
      invFun := fun e => ⟨i, nilPath i, e⟩
      left_inv := by
        rintro ⟨v, ⟨⟨w, hwi, hwv⟩⟩, e⟩
        subst w
        subst v
        rfl
      right_inv := fun _ => rfl }
    exact (pathHeadEquiv M (.nil _) i j).trans
      ((rightNilEquiv M i j).trans remove.symm)
  | @cons n t k L N f ih =>
    let reassociate : (Σ v : Fin t, At N i v ×
        (Σ w : Fin k, FactorPath f v w × At M w j)) ≃
        Σ w : Fin k, (Σ v : Fin t, At N i v × FactorPath f v w) × At M w j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (pathHeadEquiv N (factorSnoc f M) i j).trans
      ((Equiv.sigmaCongrRight fun v => Equiv.prodCongr (Equiv.refl _) (ih M v j)).trans
        (reassociate.trans (Equiv.sigmaCongrRight fun w =>
          Equiv.prodCongr (pathHeadEquiv N f i w).symm (Equiv.refl _))))

/-- The two saved outside half-edges and the shorter internal word. -/
abbrev PeelBoundary {n k : ℕ} (U : GroupMat H n k) (V : GroupMat H k n)
    (l : ℕ) (i j : Fin n) :=
  Σ x : Fin k, Σ y : Fin k, At U i x × Word (V * U) l x y × At V y j

private def peelRowRearrangeForward {n k l : ℕ} (U : GroupMat H n k)
    (V : GroupMat H k n) (i j : Fin n) :
    (Σ z : Fin n, (Σ w : Fin k, At U i w × At V w z) ×
      PeelBoundary U V l z j) →
      Σ w : Fin k, Σ y : Fin k, At U i w ×
        (Σ x : Fin k, (Σ z : Fin n, At V w z × At U z x) ×
          Word (V * U) l x y) × At V y j :=
  fun p => ⟨p.2.1.1, p.2.2.2.1, p.2.1.2.1,
    ⟨p.2.2.1, ⟨p.1, p.2.1.2.2, p.2.2.2.2.1⟩,
      p.2.2.2.2.2.1⟩, p.2.2.2.2.2.2⟩

private def peelRowRearrangeInverse {n k l : ℕ} (U : GroupMat H n k)
    (V : GroupMat H k n) (i j : Fin n) :
    (Σ w : Fin k, Σ y : Fin k, At U i w ×
      (Σ x : Fin k, (Σ z : Fin n, At V w z × At U z x) ×
        Word (V * U) l x y) × At V y j) →
      (Σ z : Fin n, (Σ w : Fin k, At U i w × At V w z) ×
        PeelBoundary U V l z j) :=
  fun p => ⟨p.2.2.2.1.2.1.1,
    ⟨p.1, p.2.2.1, p.2.2.2.1.2.1.2.1⟩,
    ⟨p.2.2.2.1.1, p.2.1, p.2.2.2.1.2.1.2.2,
      p.2.2.2.1.2.2, p.2.2.2.2⟩⟩

omit [Fintype H] in
private theorem peelRowRearrange_roundtrip {n k l : ℕ} (U : GroupMat H n k)
    (V : GroupMat H k n) (i j : Fin n) :
    Function.LeftInverse (peelRowRearrangeInverse (l := l) U V i j)
      (peelRowRearrangeForward (l := l) U V i j) ∧
      Function.RightInverse (peelRowRearrangeInverse (l := l) U V i j)
        (peelRowRearrangeForward (l := l) U V i j) := by
  constructor <;> intro p <;> rfl

private def peelRowRearrangeEquiv {n k l : ℕ} (U : GroupMat H n k)
    (V : GroupMat H k n) (i j : Fin n) :
    (Σ z : Fin n, (Σ w : Fin k, At U i w × At V w z) ×
      PeelBoundary U V l z j) ≃
      Σ w : Fin k, Σ y : Fin k, At U i w ×
        (Σ x : Fin k, (Σ z : Fin n, At V w z × At U z x) ×
          Word (V * U) l x y) × At V y j :=
  let h := peelRowRearrange_roundtrip (l := l) U V i j
  { toFun := peelRowRearrangeForward (l := l) U V i j
    invFun := peelRowRearrangeInverse (l := l) U V i j
    left_inv := h.1
    right_inv := h.2 }

/-- One complete peeling layer. Its inverse splits the internal eta edges,
restores both outside half-edges and joins each theta pair. -/
noncomputable def peelRow [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) :
    (l : ℕ) → (i j : Fin n) → Word (U * V) (l + 1) i j ≃ PeelBoundary U V l i j
  | 0, i, j => by
    let remove : PeelBoundary U V 0 i j ≃ Σ x : Fin k, At U i x × At V x j := {
      toFun := fun p => ⟨p.1, p.2.2.1,
        (p.2.2.2.1.down.property.1.symm.trans
          p.2.2.2.1.down.property.2).symm ▸ p.2.2.2.2⟩
      invFun := fun p => ⟨p.1, p.1, p.2.1, nilPath p.1, p.2.2⟩
      left_inv := by
        rintro ⟨x, y, u, ⟨⟨v, hvx, hvy⟩⟩, z⟩
        subst v
        subst y
        rfl
      right_inv := fun _ => rfl }
    exact (pathHeadEquiv (U * V) (.nil _) i j).trans
      ((rightNilEquiv (U * V) i j).trans ((orderedAtEquiv U V i j).trans remove.symm))
  | l + 1, i, j => by
    let assemble (w y : Fin k) :
        (Σ x : Fin k, (Σ z : Fin n, At V w z × At U z x) ×
          Word (V * U) l x y) ≃ Word (V * U) (l + 1) w y :=
      (Equiv.sigmaCongrRight fun x => Equiv.prodCongr
        (orderedAtEquiv V U w x).symm (Equiv.refl _)).trans
          (pathHeadEquiv (V * U) (wordFactors (V * U) l) w y).symm
    exact (pathHeadEquiv (U * V) (wordFactors (U * V) (l + 1)) i j).trans
      ((Equiv.sigmaCongrRight fun z => Equiv.prodCongr
        (orderedAtEquiv U V i z) (peelRow U V l z j)).trans
          ((peelRowRearrangeEquiv U V i j).trans (Equiv.sigmaCongrRight fun w =>
            Equiv.sigmaCongrRight fun y => Equiv.prodCongr (Equiv.refl _)
              (Equiv.prodCongr (assemble w y) (Equiv.refl _)))))

/-- Both complete factor boundaries meet at their retained middle vertex. -/
abbrev ChainBoundary {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (i j : Fin n) :=
  Σ v : Fin m, FactorPath (forwardFactors c) i v × FactorPath (backwardFactors c) v j

/-- The actual source triangle. The forward map fills it from its two factor
boundaries; the inverse peels theta rows and saves the left U and right V edges. -/
noncomputable def psi0 [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin n) : ChainBoundary c i j ≃ Word A L i j := by
  induction c with
  | nil A =>
    exact {
      toFun := fun p => ⟨⟨i, rfl,
        p.2.1.down.property.1.symm.trans p.2.1.down.property.2 |>.trans
          (p.2.2.down.property.1.symm.trans p.2.2.down.property.2)⟩⟩
      invFun := fun p => ⟨i, nilPath i, p⟩
      left_inv := by
        rintro ⟨v, ⟨⟨w, hwi, hwv⟩⟩, ⟨⟨z, hzv, hzj⟩⟩⟩
        subst w
        subst v
        subst z
        subst j
        rfl
      right_inv := by
        rintro ⟨⟨v, hvi, hvj⟩⟩
        subst v
        rfl }
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    let rearrange : (Σ v : Fin m,
        (Σ x : Fin k, At U i x × FactorPath (forwardFactors c) x v) ×
        (Σ y : Fin k, FactorPath (backwardFactors c) v y × At V y j)) ≃
        Σ x : Fin k, Σ y : Fin k, At U i x × ChainBoundary c x y × At V y j := {
      toFun := fun p => ⟨p.2.1.1, p.2.2.1, p.2.1.2.1,
        ⟨p.1, p.2.1.2.2, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.2.2.1.1,
        ⟨p.1, p.2.2.1, p.2.2.2.1.2.1⟩,
        ⟨p.2.1, p.2.2.2.1.2.2, p.2.2.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongrRight fun v => Equiv.prodCongr
      (pathHeadEquiv U (forwardFactors c) i v)
      (pathSnocEquiv (backwardFactors c) V v j)).trans
        (rearrange.trans ((Equiv.sigmaCongrRight fun x =>
          Equiv.sigmaCongrRight fun y => Equiv.prodCongr (Equiv.refl _)
            (Equiv.prodCongr (ih x y) (Equiv.refl _))).trans (peelRow U V L i j).symm))

/-- Append a prescribed SSE step without replacing any chain data. -/
def chainSnoc {n k m L : ℕ} {A : GroupMat H n n} {B : GroupMat H k k}
    {C : GroupMat H m m} (c : Chain H A B L)
    (U : GroupMat H k m) (V : GroupMat H m k)
    (hB : B = U * V) (hC : C = V * U) : Chain H A C (L + 1) :=
  match c with
  | .nil _ => .cons U V hB hC (.nil _)
  | .cons N M hA hD tail => .cons N M hA hD (chainSnoc tail U V hB hC)

/-- The actual reversed chain exchanges U and V and reverses the layer order. -/
def reverseChain {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m} :
    Chain H A B L → Chain H B A L
  | .nil A => .nil A
  | .cons U V hA hB c => chainSnoc (reverseChain c) V U hB hA

theorem forward_snoc {n k m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H k k} {C : GroupMat H m m} (c : Chain H A B L)
    (U : GroupMat H k m) (V : GroupMat H m k) (hB : B = U * V) (hC : C = V * U) :
    forwardFactors (chainSnoc c U V hB hC) = factorSnoc (forwardFactors c) U := by
  induction c with
  | nil A => rfl
  | cons N M hA hD c ih => simp only [chainSnoc, forwardFactors, factorSnoc, ih]

theorem backward_snoc {n k m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H k k} {C : GroupMat H m m} (c : Chain H A B L)
    (U : GroupMat H k m) (V : GroupMat H m k) (hB : B = U * V) (hC : C = V * U) :
    backwardFactors (chainSnoc c U V hB hC) = Factors.cons V (backwardFactors c) := by
  induction c with
  | nil A => rfl
  | cons N M hA hD c ih => simp only [chainSnoc, backwardFactors, ih, factorSnoc]

/-- Reversal keeps precisely the original decreasing V factor sequence. -/
theorem reverse_forward {n m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H m m} (c : Chain H A B L) :
    forwardFactors (reverseChain c) = backwardFactors c := by
  induction c with
  | nil A => rfl
  | cons U V hA hB c ih => simp only [reverseChain, forward_snoc, backwardFactors, ih]

/-- The reverse chain's decreasing factors are the original increasing U sequence. -/
theorem reverse_backward {n m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H m m} (c : Chain H A B L) :
    backwardFactors (reverseChain c) = forwardFactors c := by
  induction c with
  | nil A => rfl
  | cons U V hA hB c ih => simp only [reverseChain, backward_snoc, forwardFactors, ih]

/-- The terminal triangle is the source triangle of this actual reversed chain. -/
noncomputable def psiL [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin m) :
    (Σ v : Fin n, FactorPath (backwardFactors c) i v ×
      FactorPath (forwardFactors c) v j) ≃ Word B L i j :=
  (Equiv.cast (by simp only [ChainBoundary, reverse_forward, reverse_backward] :
    (Σ v : Fin n, FactorPath (backwardFactors c) i v × FactorPath (forwardFactors c) v j) =
      ChainBoundary (reverseChain c) i j)).trans (psi0 (reverseChain c) i j)

/-- One actual cell: split theta, keep u, and join eta(v,u'). -/
noncomputable def localSweep [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (i : Fin n) (j : Fin k) :
    (Σ x : Fin n, At (U * V) i x × At U x j) ≃
      Σ y : Fin k, At U i y × At (V * U) y j := by
  let regroup : (Σ x : Fin n, (Σ y : Fin k, At U i y × At V y x) × At U x j) ≃
      Σ y : Fin k, At U i y × (Σ x : Fin n, At V y x × At U x j) := {
    toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
    invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sigmaCongrRight fun x =>
    Equiv.prodCongr (orderedAtEquiv U V i x) (Equiv.refl _)).trans
      (regroup.trans (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (Equiv.refl _) (orderedAtEquiv V U y j).symm))

/-- Send one A edge through all original U factors. The inverse traverses the
same cells in decreasing layer order, splits eta and rejoins theta. -/
noncomputable def phiR [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin n) (j : Fin m) :
    (Σ x : Fin n, At A i x × FactorPath (forwardFactors c) x j) ≃
      Σ y : Fin m, FactorPath (forwardFactors c) i y × At B y j := by
  induction c with
  | @nil n A =>
    let left := rightNilEquiv A i j
    let right : (Σ y : Fin n, FactorPath (Factors.nil (H := H) n) i y × At A y j) ≃
        At A i j := {
      toFun := fun p => (p.2.1.down.property.1.symm.trans
        p.2.1.down.property.2).symm ▸ p.2.2
      invFun := fun p => ⟨i, nilPath i, p⟩
      left_inv := by
        rintro ⟨y, ⟨⟨v, hvi, hvy⟩⟩, a⟩
        subst v
        subst y
        rfl
      right_inv := fun _ => rfl }
    exact left.trans right.symm
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    let before : (Σ x : Fin n, At (U * V) i x ×
        (Σ z : Fin k, At U x z × FactorPath (forwardFactors c) z j)) ≃
        Σ z : Fin k, (Σ x : Fin n, At (U * V) i x × At U x z) ×
          FactorPath (forwardFactors c) z j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let middle : (Σ z : Fin k, (Σ y : Fin k, At U i y × At (V * U) y z) ×
        FactorPath (forwardFactors c) z j) ≃
        Σ y : Fin k, At U i y ×
          (Σ z : Fin k, At (V * U) y z × FactorPath (forwardFactors c) z j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let after : (Σ y : Fin k, At U i y ×
        (Σ z : Fin m, FactorPath (forwardFactors c) y z × At C z j)) ≃
        Σ z : Fin m, (Σ y : Fin k, At U i y × FactorPath (forwardFactors c) y z) ×
          At C z j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
      (pathHeadEquiv U (forwardFactors c) x j)).trans
        (before.trans ((Equiv.sigmaCongrRight fun z =>
          Equiv.prodCongr (localSweep U V i z) (Equiv.refl _)).trans
            (middle.trans ((Equiv.sigmaCongrRight fun y =>
              Equiv.prodCongr (Equiv.refl _) (ih y j)).trans
                (after.trans (Equiv.sigmaCongrRight fun z =>
                  Equiv.prodCongr (pathHeadEquiv U (forwardFactors c) i z).symm
                    (Equiv.refl _)))))))

/-- Send one B edge through the actual decreasing V sequence. -/
noncomputable def phiS [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin m) (j : Fin n) :
    (Σ x : Fin m, At B i x × FactorPath (backwardFactors c) x j) ≃
      Σ y : Fin n, FactorPath (backwardFactors c) i y × At A y j :=
  (Equiv.cast (by rw [reverse_forward] :
    (Σ x : Fin m, At B i x × FactorPath (backwardFactors c) x j) =
      (Σ x : Fin m, At B i x × FactorPath (forwardFactors (reverseChain c)) x j))).trans
    ((phiR (reverseChain c) i j).trans (Equiv.cast (by rw [reverse_forward])))

/-- The literal right-to-left column sweep on an arbitrary finite word.
At each column it uses phiR and its inverse on the same original chain. -/
noncomputable def phiRPower [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L) :
    (l : ℕ) → (i : Fin n) → (j : Fin m) →
      (Σ x : Fin n, Word A l i x × FactorPath (forwardFactors c) x j) ≃
        Σ y : Fin m, FactorPath (forwardFactors c) i y × Word B l y j
  | 0, i, j => by
    let left : (Σ x : Fin n, Word A 0 i x × FactorPath (forwardFactors c) x j) ≃
        FactorPath (forwardFactors c) i j := {
      toFun := fun p => (p.2.1.down.property.1.symm.trans
        p.2.1.down.property.2).symm ▸ p.2.2
      invFun := fun p => ⟨i, nilPath i, p⟩
      left_inv := by
        rintro ⟨x, ⟨⟨v, hvi, hvx⟩⟩, p⟩
        subst v
        subst x
        rfl
      right_inv := fun _ => rfl }
    let right : (Σ y : Fin m, FactorPath (forwardFactors c) i y × Word B 0 y j) ≃
        FactorPath (forwardFactors c) i j := {
      toFun := fun p => (p.2.2.down.property.1.symm.trans
        p.2.2.down.property.2) ▸ p.2.1
      invFun := fun p => ⟨j, p, nilPath j⟩
      left_inv := by
        rintro ⟨y, p, ⟨⟨v, hvy, hvj⟩⟩⟩
        subst v
        subst y
        rfl
      right_inv := fun _ => rfl }
    exact left.trans right.symm
  | l + 1, i, j => by
    let before : (Σ x : Fin n,
        (Σ v : Fin n, At A i v × Word A l v x) ×
          FactorPath (forwardFactors c) x j) ≃
        Σ v : Fin n, At A i v ×
          (Σ x : Fin n, Word A l v x × FactorPath (forwardFactors c) x j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let middle : (Σ v : Fin n, At A i v ×
        (Σ y : Fin m, FactorPath (forwardFactors c) v y × Word B l y j)) ≃
        Σ y : Fin m, (Σ v : Fin n, At A i v × FactorPath (forwardFactors c) v y) ×
          Word B l y j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let after : (Σ y : Fin m,
        (Σ z : Fin m, FactorPath (forwardFactors c) i z × At B z y) × Word B l y j) ≃
        Σ z : Fin m, FactorPath (forwardFactors c) i z ×
          (Σ y : Fin m, At B z y × Word B l y j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongrRight fun x => Equiv.prodCongr
      (pathHeadEquiv A (wordFactors A l) i x) (Equiv.refl _)).trans
        (before.trans ((Equiv.sigmaCongrRight fun v => Equiv.prodCongr
          (Equiv.refl _) (phiRPower c l v j)).trans
            (middle.trans ((Equiv.sigmaCongrRight fun y => Equiv.prodCongr
              (phiR c i y) (Equiv.refl _)).trans
                (after.trans (Equiv.sigmaCongrRight fun z => Equiv.prodCongr
                  (Equiv.refl _) (pathHeadEquiv B (wordFactors B l) z j).symm))))))

/-- The dual finite-word sweep uses the actual reversed chain. -/
noncomputable def phiSPower [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (l : ℕ) (i : Fin m) (j : Fin n) :
    (Σ x : Fin m, Word B l i x × FactorPath (backwardFactors c) x j) ≃
      Σ y : Fin n, FactorPath (backwardFactors c) i y × Word A l y j :=
  (Equiv.cast (by rw [reverse_forward] :
    (Σ x : Fin m, Word B l i x × FactorPath (backwardFactors c) x j) =
      (Σ x : Fin m, Word B l i x × FactorPath (forwardFactors (reverseChain c)) x j))).trans
    ((phiRPower (reverseChain c) l i j).trans (Equiv.cast (by rw [reverse_forward])))

/-- Read the single global whole-factor rank, with no iterated binary ranking. -/
noncomputable def pathAtEquiv [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) :
    At (factorProduct f) i j ≃ FactorPath f i j :=
  (Equiv.sigmaCongrRight fun g => rankedFiberEquiv f i j g).trans
    (Equiv.sigmaFiberEquiv (factorLabel f))

/-- All R and S occurrences in psi0 use the same whole-fiber ranks. -/
noncomputable def matrixPsi0 [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin n) : (Σ v : Fin m, At (R c) i v × At (S c) v j) ≃ Word A L i j :=
  (Equiv.sigmaCongrRight fun v => Equiv.prodCongr
    (pathAtEquiv (forwardFactors c) i v) (pathAtEquiv (backwardFactors c) v j)).trans
      (psi0 c i j)

/-- The dual triangle uses those same S and R ranks. -/
noncomputable def matrixPsiL [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin m) : (Σ v : Fin n, At (S c) i v × At (R c) v j) ≃ Word B L i j :=
  (Equiv.sigmaCongrRight fun v => Equiv.prodCongr
    (pathAtEquiv (backwardFactors c) i v) (pathAtEquiv (forwardFactors c) v j)).trans
      (psiL c i j)

/-- Transport both appearances of R in the actual one-edge sweep. -/
noncomputable def matrixPhiR [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin n) (j : Fin m) :
    (Σ x : Fin n, At A i x × At (R c) x j) ≃ Σ y : Fin m, At (R c) i y × At B y j :=
  (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
    (pathAtEquiv (forwardFactors c) x j)).trans
      ((phiR c i j).trans (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (pathAtEquiv (forwardFactors c) i y).symm (Equiv.refl _)))

/-- Transport both appearances of S in the actual one-edge dual sweep. -/
noncomputable def matrixPhiS [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin m) (j : Fin n) :
    (Σ x : Fin m, At B i x × At (S c) x j) ≃ Σ y : Fin n, At (S c) i y × At A y j :=
  (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
    (pathAtEquiv (backwardFactors c) x j)).trans
      ((phiS c i j).trans (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (pathAtEquiv (backwardFactors c) i y).symm (Equiv.refl _)))

end D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
