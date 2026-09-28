/- GID: D5/S3/Quantum/Recovery/FiniteLocalRecoveryObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalRecoveryObstruction
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Informationally complete local records obstruct finite local exact recovery. -/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import Mathlib.LinearAlgebra.UnitaryGroup

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators
open Matrix
noncomputable section
variable {A S : Type} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

noncomputable def recordTrace {d : A → ℕ} (X : State S d) : Matrix S S ℂ :=
  fun i j => ∑ r : Coordinates d, X (i,r) (j,r)

/-- Feedback occurs only after termination and acts only on the system. -/
noncomputable def corrected (z : Terminal (Matrix.unitaryGroup S ℂ) S A) :
    Matrix S S ℂ :=
  (z.feedback : Matrix S S ℂ) * recordTrace z.state *
    (z.feedback : Matrix S S ℂ).conjTranspose

noncomputable def correctedTotal {d : A → ℕ}
    (T : Tree (Matrix.unitaryGroup S ℂ) d) (X : State S d) : Matrix S S ℂ :=
  ((terminalOutputs T X).map corrected).sum

/-- Prepare common-label records without restricting the system matrix. -/
noncomputable def commonPreparation {H : A → ℕ}
    (s : (a : A) → S → Fin (H a) → ℂ) (X : Matrix S S ℂ) : State S H :=
  fun p q => X p.1 q.1 * ∏ a, s a p.1 (p.2 a) * star (s a q.1 (q.2 a))

noncomputable def Protocol.correctedRun {H : A → ℕ}
    (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ) (X : Matrix S S ℂ) : Matrix S S ℂ :=
  correctedTotal P.tree (appendAncillas P.ancillas (commonPreparation s X))

/-- Physical deterministic recovery, with no scalarity or Kraus witness fields. -/
def Protocol.ExactRecovery {H : A → ℕ}
    (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ) : Prop :=
  ∀ X : Matrix S S ℂ, P.correctedRun s X = X

/-- Input-independent observed leaf addresses. Hidden Kraus labels are absent. -/
def Tree.Leaves {d : A → ℕ} : Tree (Matrix.unitaryGroup S ℂ) d → Type
  | .leaf _ => Unit
  | .node J child => (y : Fin J.outcomes) × (child y).Leaves

noncomputable instance Tree.fintypeLeaves {d : A → ℕ}
    (T : Tree (Matrix.unitaryGroup S ℂ) d) : Fintype T.Leaves := by
  induction T with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | node J child ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((y : Fin J.outcomes) × (child y).Leaves))

/-- Execute the original coarse maps down one observed leaf address. -/
noncomputable def Tree.branch {d : A → ℕ}
    (T : Tree (Matrix.unitaryGroup S ℂ) d) (X : State S d) :
    T.Leaves → Terminal (Matrix.unitaryGroup S ℂ) S A :=
  match T with
  | .leaf U => fun _ => ⟨[], U, d, X⟩
  | .node J child => fun w =>
      let z := (child w.1).branch (step J w.1 X) w.2
      { z with history := w.1.val :: z.history }

/-- The retained path selected by an actual observed leaf address. -/
def Tree.leafPath {d : A → ℕ} (T : Tree (Matrix.unitaryGroup S ℂ) d) :
    T.Leaves → ObservedPath T := match T with
  | .leaf _ => fun _ => .here
  | .node _ child => fun w => .next w.1 ((child w.1).leafPath w.2)

def Tree.leafUnitary {d : A → ℕ} (T : Tree (Matrix.unitaryGroup S ℂ) d) :
    T.Leaves → Matrix.unitaryGroup S ℂ := match T with
  | .leaf U => fun _ => U
  | .node _ child => fun w => (child w.1).leafUnitary w.2

/-- Input-independent source amplitudes through the actual accumulated local factors. -/
def LocalFactors.sourceAmplitude {H d : A → ℕ} (F : LocalFactors H d)
    (s : (a : A) → S → Fin (H a) → ℂ) (i : S)
    (z : Coordinates d × F.stack) : ℂ :=
  ∏ a, ∑ x, F.matrix a (z.1 a, F.regroup z.2 a) x * s a i x

/-- Actual observed leaf, actual mixed-root purification and inaccessible stack.
The family has no input-matrix argument. -/
def Protocol.leafKraus {H : A → ℕ} (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ) (w : P.tree.Leaves) :=
  let F := (P.tree.leafPath w).factors (P.ancillas.rootFactors H)
  fun z : Coordinates (P.tree.leafPath w).endDimensions × F.stack =>
    (P.tree.leafUnitary w : Matrix S S ℂ) *
      Matrix.diagonal (fun i => F.sourceAmplitude s i z)

def Protocol.leafWeight {H : A → ℕ} (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ) (j₀ : S) (w : P.tree.Leaves) : ℝ :=
  ∑ z, Complex.normSq (P.leafKraus s w z j₀ j₀)

inductive Tree.SelectedPrefix : {d : A → ℕ} → Tree (Matrix.unitaryGroup S ℂ) d → Type
  | here {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d} : SelectedPrefix T
  | next {d : A → ℕ} {J : Instrument d} {child : ∀ y, Tree (Matrix.unitaryGroup S ℂ) (J.output y)}
      (y : Fin J.outcomes) (p : SelectedPrefix (child y)) : SelectedPrefix (.node J child)
def Tree.SelectedPrefix.dimensions {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (p : T.SelectedPrefix) : A → ℕ := match p with
  | .here => d
  | .next _ p => p.dimensions
def Tree.SelectedPrefix.subtree {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (p : T.SelectedPrefix) : Tree (Matrix.unitaryGroup S ℂ) p.dimensions := match p with
  | .here => T
  | .next _ p => p.subtree
def Tree.SelectedPrefix.state {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (p : T.SelectedPrefix) (X : State S d) : State S p.dimensions := match p with
  | .here => X
  | .next y p => p.state (step _ y X)
def Tree.SelectedPrefix.extendLeaf {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (p : T.SelectedPrefix) : p.subtree.Leaves → T.Leaves := match p with
  | .here => id
  | .next y p => fun w => ⟨y,p.extendLeaf w⟩

def ObservedPath.selected {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (path : ObservedPath T) : T.SelectedPrefix := match path with
  | .here => .here
  | .next y tail => .next y tail.selected

def ObservedPath.take {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
    (path : ObservedPath T) : ℕ → ObservedPath T
  | 0 => .here
  | t+1 => match path with
    | .here => .here
    | .next y tail => .next y (tail.take t)

def Protocol.pathWeight {H : A → ℕ} (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ) (j₀ : S)
    (path : ObservedPath P.tree) (t : ℕ) : ℝ :=
  let q := (path.take t).selected
  ∑ w : q.subtree.Leaves, P.leafWeight s j₀ (q.extendLeaf w)

set_option maxHeartbeats 1600000 in
-- The combined proof expands dependent finite sums for all retained-path and leaf identities.
/-- Normalized locally informationally complete source families with an orthogonal pair
cannot be exactly recovered by any finite local protocol with product mixed ancillas.
Prefix weights and scalar endpoint effects are derived from recovery. -/
theorem actual_informationally_complete_obstruction [Nonempty A] {H : A → ℕ}
    (P : Protocol (Matrix.unitaryGroup S ℂ) H)
    (s : (a : A) → S → Fin (H a) → ℂ)
    (normalized : ∀ a i, star (s a i) ⬝ᵥ s a i = 1)
    (complete : ∀ a (Q : Matrix (Fin (H a)) (Fin (H a)) ℂ), Q.IsHermitian →
      Q ∈ Submodule.span ℝ (Set.range (fun i => vecMulVec (s a i) (star (s a i)))))
    (i j : S) (distinct : i ≠ j) (b : A)
    (orthogonal : star (s b j) ⬝ᵥ s b i = 0) : ¬ P.ExactRecovery s := by
  classical
  have observed_leaf_regrouping {d : A → ℕ}
      (T : Tree (Matrix.unitaryGroup S ℂ) d) (X : State S d) :
      (∑ w : T.Leaves, corrected (T.branch X w)) = correctedTotal T X := by
    induction T with
    | @leaf d U =>
      change (∑ _ : Unit, corrected ⟨[], U, d, X⟩) =
        correctedTotal (.leaf U) X
      simp [correctedTotal, terminalOutputs]
    | @node d J child ih =>
      change (∑ w : (y : Fin J.outcomes) × (child y).Leaves,
        corrected { (child w.1).branch (step J w.1 X) w.2 with
          history := w.1.val :: ((child w.1).branch (step J w.1 X) w.2).history }) = _
      rw [Fintype.sum_sigma]
      change (∑ y, ∑ w : (child y).Leaves,
        corrected ((child y).branch (step J y X) w)) = _
      simp_rw [ih]
      simp only [correctedTotal, terminalOutputs, List.map_flatten,
        List.sum_flatten, List.map_ofFn, List.sum_ofFn, List.map_map,
        Function.comp_def]
      rfl
  -- Actual coarse leaves have input-independent Kraus amplitudes.
  have actual_leaf_amplitude {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (w : P.tree.Leaves)
      (M : Matrix S S ℂ) :
      corrected (P.tree.branch (appendAncillas P.ancillas (commonPreparation s M)) w) =
        ∑ z, P.leafKraus s w z * M * (P.leafKraus s w z).conjTranspose := by
    classical
    have edge {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes)
        {G : Type} [Fintype G] (X : RetainedState S G d) :
        traceGarbage (retainedStep J y X) = step J y (traceGarbage X) := by
      have h := (recursive_coarse_retained
        (Tree.node J (fun _ => Tree.leaf ())) X).1
      simp only [retainedOutputs, terminalOutputs, List.map_singleton] at h
      have collapse {α : Type} {n : ℕ} (f : Fin n → α) :
          (List.ofFn (fun y => [f y])).flatten = List.ofFn f := by
        rw [show List.ofFn (fun y => [f y]) = (List.ofFn f).map (fun z => [z])
          from (List.map_ofFn (f := f) (g := fun z => [z])).symm]
        exact List.flatMap_singleton' _
      rw [collapse, collapse] at h
      have hy := congrFun (List.ofFn_injective h) y
      simpa only [Terminal.mk.injEq, heq_eq_eq, true_and] using hy
    have branch_path {d : A → ℕ} (T : Tree (Matrix.unitaryGroup S ℂ) d) :
        ∀ (w : T.Leaves) {G : Type} [Fintype G] (X : RetainedState S G d),
        T.branch (traceGarbage X) w =
          ⟨(T.leafPath w).history, T.leafUnitary w,
            (T.leafPath w).endDimensions,
            traceGarbage ((T.leafPath w).execute X)⟩ := by
      induction T with
      | leaf U => intro w G _ X; rfl
      | node J child ih =>
        intro w G _ X
        rcases w with ⟨y,w⟩
        simp only [Tree.branch, Tree.leafPath, Tree.leafUnitary,
          ObservedPath.history, ObservedPath.endDimensions, ObservedPath.execute]
        rw [← edge, ih]
    let B := P.ancillas.rootFactors H
    let path := P.tree.leafPath w
    let F := path.factors B
    have bridge := purified_local_path_bridge P (commonPreparation s M)
    rw [← bridge.1, branch_path]
    change (P.tree.leafUnitary w : Matrix S S ℂ) *
      recordTrace (traceGarbage (path.execute (B.lift (commonPreparation s M)))) *
      (P.tree.leafUnitary w : Matrix S S ℂ).conjTranspose = _
    rw [(bridge.2.2 path).2.1]
    have amplitude_expand (i : S) (z : Coordinates path.endDimensions × F.stack) :
        F.sourceAmplitude s i z =
          ∑ x : Coordinates H, F.amplitude z x * ∏ a, s a i (x a) := by
      dsimp only [LocalFactors.sourceAmplitude]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      rfl
    have lift_entry (p q : (S × Coordinates path.endDimensions) × F.stack) :
        F.lift (commonPreparation s M) p q =
          F.sourceAmplitude s p.1.1 (p.1.2,p.2) * M p.1.1 q.1.1 *
            star (F.sourceAmplitude s q.1.1 (q.1.2,q.2)) := by
      simp only [LocalFactors.lift, amplitude_expand, commonPreparation,
        star_sum, star_mul, star_prod, Finset.prod_mul_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      ring
    have marginal : recordTrace (traceGarbage
        (((path.factors B).lift (commonPreparation s M)).submatrix
          (fun p => (p.1,(path.stackEquiv B).symm p.2))
          (fun p => (p.1,(path.stackEquiv B).symm p.2)))) =
        ∑ z : Coordinates path.endDimensions × F.stack,
          Matrix.diagonal (fun i => F.sourceAmplitude s i z) * M *
            (Matrix.diagonal (fun i => F.sourceAmplitude s i z)).conjTranspose := by
      ext i j
      simp only [recordTrace, traceGarbage, Matrix.submatrix_apply]
      change (∑ r, ∑ g : path.stack B.stack,
        F.lift (commonPreparation s M)
          ((i,r),(path.stackEquiv B).symm g) ((j,r),(path.stackEquiv B).symm g)) = _
      simp_rw [lift_entry]
      simp only [Matrix.sum_apply, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      rw [← (path.stackEquiv B).sum_comp]
      simp only [Equiv.symm_apply_apply, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Matrix.mul_diagonal]
      rfl
    rw [marginal, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Protocol.leafKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  -- Recovery and the existing scalar-Kraus theorem fix each observed leaf.
  have actual_recovery_leaf_scalarity {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (j₀ : S)
      (recovery : P.ExactRecovery s) :
      (∀ w, 0 ≤ P.leafWeight s j₀ w) ∧
      (∑ w, P.leafWeight s j₀ w) = 1 ∧
      (∀ w (M : Matrix S S ℂ),
        corrected (P.tree.branch (appendAncillas P.ancillas (commonPreparation s M)) w) =
          (P.leafWeight s j₀ w : ℂ) • M) := by
    classical
    let Z := fun w : P.tree.Leaves =>
      Coordinates (P.tree.leafPath w).endDimensions ×
        ((P.tree.leafPath w).factors (P.ancillas.rootFactors H)).stack
    let F : ((w : P.tree.Leaves) × Z w) → Matrix S S ℂ :=
      fun q => P.leafKraus s q.1 q.2
    have total (M : Matrix S S ℂ) : ∑ q, F q * M * (F q).conjTranspose = M := by
      rw [Fintype.sum_sigma]
      change (∑ w, ∑ z, P.leafKraus s w z * M * (P.leafKraus s w z).conjTranspose) = M
      simp_rw [← actual_leaf_amplitude P s]
      rw [observed_leaf_regrouping]
      exact recovery M
    have scalar := D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar F total j₀
    have leaf (w : P.tree.Leaves) (M : Matrix S S ℂ) :
        corrected (P.tree.branch (appendAncillas P.ancillas (commonPreparation s M)) w) =
          (P.leafWeight s j₀ w : ℂ) • M := by
      rw [actual_leaf_amplitude]
      have hs (z : Z w) : P.leafKraus s w z =
          P.leafKraus s w z j₀ j₀ • (1 : Matrix S S ℂ) := scalar ⟨w,z⟩
      rw [show (P.leafWeight s j₀ w : ℂ) =
        ∑ z, (Complex.normSq (P.leafKraus s w z j₀ j₀) : ℂ) by
          simp only [Protocol.leafWeight, Complex.ofReal_sum], Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro z _
      calc
        _ = (P.leafKraus s w z j₀ j₀ • (1 : Matrix S S ℂ)) * M *
            (P.leafKraus s w z j₀ j₀ • (1 : Matrix S S ℂ)).conjTranspose :=
          congrArg (fun K : Matrix S S ℂ => K * M * K.conjTranspose) (hs z)
        _ = _ := by
          simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
            Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
            smul_smul, Complex.normSq_eq_conj_mul_self]
          rfl
    refine ⟨fun w => Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _), ?_, leaf⟩
    have h := observed_leaf_regrouping P.tree
      (appendAncillas P.ancillas (commonPreparation s (1 : Matrix S S ℂ)))
    simp_rw [leaf] at h
    rw [show correctedTotal P.tree (appendAncillas P.ancillas
        (commonPreparation s (1 : Matrix S S ℂ))) = 1 from recovery 1] at h
    have he := congrArg (fun M : Matrix S S ℂ => (M j₀ j₀).re) h
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Complex.re_sum, Complex.ofReal_re, Complex.one_re] using he
  -- Complete descendant traces give the actual prefix weights.
  have actual_recovery_prefix_weights {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (j₀ : S)
      (recovery : P.ExactRecovery s) (p : P.tree.SelectedPrefix) :
      Function.Injective p.extendLeaf ∧
      0 ≤ (∑ w : p.subtree.Leaves, P.leafWeight s j₀ (p.extendLeaf w)) ∧
      ∀ M : Matrix S S ℂ,
        Matrix.trace (p.state (appendAncillas P.ancillas (commonPreparation s M))) =
          ((∑ w : p.subtree.Leaves, P.leafWeight s j₀ (p.extendLeaf w)) : ℂ) *
            Matrix.trace M := by
    classical
    have transport {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d} (q : T.SelectedPrefix) :
        Function.Injective q.extendLeaf ∧ ∀ (X : State S d) (w : q.subtree.Leaves),
          corrected (q.subtree.branch (q.state X) w) =
            corrected (T.branch X (q.extendLeaf w)) := by
      induction q with
      | here => exact ⟨Function.injective_id, fun _ _ => rfl⟩
      | next y q ih =>
        refine ⟨?_, ?_⟩
        · intro u v h
          exact ih.1 (eq_of_heq (Sigma.mk.inj h).2)
        · intro X w
          exact ih.2 (step _ y X) w
    have leafTrace (z : Terminal (Matrix.unitaryGroup S ℂ) S A) :
        Matrix.trace (corrected z) = Matrix.trace z.state := by
      unfold corrected
      rw [Matrix.trace_mul_cycle]
      rw [show (z.feedback : Matrix S S ℂ).conjTranspose *
        (z.feedback : Matrix S S ℂ) = 1 from Matrix.UnitaryGroup.star_mul_self z.feedback]
      rw [Matrix.one_mul]
      simp only [Matrix.trace, Matrix.diag_apply, recordTrace]
      rw [Fintype.sum_prod_type]
    have subtree {d : A → ℕ} (T : Tree (Matrix.unitaryGroup S ℂ) d) (X : State S d) :
        (∑ w : T.Leaves, Matrix.trace (corrected (T.branch X w))) = Matrix.trace X := by
      rw [← Matrix.trace_sum, observed_leaf_regrouping]
      unfold correctedTotal
      rw [Matrix.trace_list_sum]
      simp only [List.map_map, Function.comp_def]
      simp_rw [leafTrace]
      exact complete_subtree_trace T X
    have leaves := actual_recovery_leaf_scalarity P s j₀ recovery
    refine ⟨(transport p).1, Finset.sum_nonneg (fun w _ => leaves.1 _), ?_⟩
    intro M
    rw [← subtree p.subtree]
    simp_rw [(transport p).2, leaves.2.2, Matrix.trace_smul]
    simp only [smul_eq_mul, Finset.sum_mul]
  -- Purified path traces are local norm products, so prefix rigidity applies.
  have actual_recovery_path_rigidity {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (j₀ : S)
      (recovery : P.ExactRecovery s)
      (normalized : ∀ a i, star (s a i) ⬝ᵥ s a i = 1)
      (complete : ∀ a (Q : Matrix (Fin (H a)) (Fin (H a)) ℂ), Q.IsHermitian →
        Q ∈ Submodule.span ℝ (Set.range (fun i => vecMulVec (s a i) (star (s a i)))))
      (path : ObservedPath P.tree) :
      let F := P.ancillas.rootFactors H
      let L := ProductPrefixRigidity.accumulated (fun a => Fin (H a)) (path.localCoordinates F)
        (path.frame F 0).2.matrix (path.edges F)
      (∀ t i, (∏ a, ∑ k, Complex.normSq ((L t a *ᵥ s a i) k)) =
        P.pathWeight s j₀ path t) ∧
      ∀ t, (P.pathWeight s j₀ path t = 0 ∧ (∃ a, L t a = 0) ∧
        ProductPrefixRigidity.productMap (fun a => Fin (H a)) (L t) = 0) ∨
        (0 < P.pathWeight s j₀ path t ∧ ∃ c : A → ℝ,
          (∀ a, 0 < c a ∧ ProductPrefixRigidity.gram (L t a) = (c a : ℂ) • 1) ∧
          (∏ a, c a) = P.pathWeight s j₀ path t ∧
          ∃ V : ∀ a, Matrix (path.localCoordinates F t a) (Fin (H a)) ℂ,
            (∀ a, ProductPrefixRigidity.gram (V a) = 1 ∧
              L t a = (Real.sqrt (c a) : ℂ) • V a ∧
              ∀ x y : Fin (H a) → ℂ,
                star (V a *ᵥ x) ⬝ᵥ (V a *ᵥ y) = star x ⬝ᵥ y) ∧
            ProductPrefixRigidity.productMap (fun a => Fin (H a)) (L t) =
              (Real.sqrt (P.pathWeight s j₀ path t) : ℂ) •
                ProductPrefixRigidity.productMap (fun a => Fin (H a)) V) := by
    classical
    let : Nonempty S := ⟨j₀⟩
    have probability :
        let F := P.ancillas.rootFactors H
        ∀ t i, (∏ a, ∑ k, Complex.normSq
          ((ProductPrefixRigidity.accumulated (fun a => Fin (H a)) (path.localCoordinates F)
            (path.frame F 0).2.matrix (path.edges F) t a *ᵥ s a i) k)) =
              P.pathWeight s j₀ path t := by
      classical
      let F := P.ancillas.rootFactors H
      have edge {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes)
          {G : Type} [Fintype G] (X : RetainedState S G d) :
          traceGarbage (retainedStep J y X) = step J y (traceGarbage X) := by
        have h := (recursive_coarse_retained
          (Tree.node J (fun _ => Tree.leaf ())) X).1
        simp only [retainedOutputs, terminalOutputs, List.map_singleton] at h
        have collapse {α : Type} {n : ℕ} (f : Fin n → α) :
            (List.ofFn (fun y => [f y])).flatten = List.ofFn f := by
          rw [show List.ofFn (fun y => [f y]) = (List.ofFn f).map (fun z => [z])
            from (List.map_ofFn (f := f) (g := fun z => [z])).symm]
          exact List.flatMap_singleton' _
        rw [collapse, collapse] at h
        have hy := congrFun (List.ofFn_injective h) y
        simpa only [Terminal.mk.injEq, heq_eq_eq, true_and] using hy
      have selected_trace {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
          (q : ObservedPath T) {G : Type} [Fintype G] (X : RetainedState S G d) :
          Matrix.trace (q.selected.state (traceGarbage X)) =
            Matrix.trace (traceGarbage (q.execute X)) := by
        induction q generalizing G with
        | here => rfl
        | next y tail ih =>
          change Matrix.trace (tail.selected.state (step _ y (traceGarbage X))) = _
          rw [← edge]
          exact ih _
      have cut_frame {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
          (q : ObservedPath T) (B : LocalFactors H d) (t : ℕ) :
          (⟨(q.take t).endDimensions, (q.take t).factors B⟩ : Σ d, LocalFactors H d) =
            q.frame B t := by
        induction t generalizing d with
        | zero => cases q <;> rfl
        | succ t ih => cases q with
          | here => rfl
          | next y tail => exact ih tail (B.advance _ y)
      have endpoint (q : ObservedPath P.tree) (i : S) :
          (∏ a, ∑ k, Complex.normSq (((q.factors F).matrix a *ᵥ s a i) k)) =
            ∑ w : q.selected.subtree.Leaves, P.leafWeight s j₀ (q.selected.extendLeaf w) := by
        let M : Matrix S S ℂ := Matrix.single i i 1
        have bridge := purified_local_path_bridge P (commonPreparation s M)
        have weight := (actual_recovery_prefix_weights P s j₀ recovery q.selected).2.2 M
        rw [← bridge.1, selected_trace, (bridge.2.2 q).2.1] at weight
        have trace_norm : Matrix.trace (traceGarbage
            (((q.factors F).lift (commonPreparation s M)).submatrix
              (fun p => (p.1,(q.stackEquiv F).symm p.2))
              (fun p => (p.1,(q.stackEquiv F).symm p.2)))) =
            ((∏ a, ∑ k, Complex.normSq (((q.factors F).matrix a *ᵥ s a i) k) : ℝ) : ℂ) := by
          let L := q.factors F
          have amp (j : S) (z : Coordinates q.endDimensions × L.stack) :
              L.sourceAmplitude s j z = ∑ x : Coordinates H,
                L.amplitude z x * ∏ a, s a j (x a) := by
            dsimp only [LocalFactors.sourceAmplitude]
            rw [Fintype.prod_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.prod_mul_distrib]
            rfl
          have entry (p : (S × Coordinates q.endDimensions) × L.stack) :
              L.lift (commonPreparation s M) p p =
                L.sourceAmplitude s p.1.1 (p.1.2,p.2) * M p.1.1 p.1.1 *
                  star (L.sourceAmplitude s p.1.1 (p.1.2,p.2)) := by
            simp only [LocalFactors.lift, amp, commonPreparation, star_sum, star_mul,
              star_prod, Finset.prod_mul_distrib, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro z _
            ring
          simp only [Matrix.trace, Matrix.diag_apply, traceGarbage, Matrix.submatrix_apply]
          rw [Fintype.sum_prod_type]
          change (∑ j : S, ∑ r, ∑ g : q.stack F.stack,
            L.lift (commonPreparation s M)
              ((j,r),(q.stackEquiv F).symm g) ((j,r),(q.stackEquiv F).symm g)) = _
          simp_rw [entry]
          simp only [M, Matrix.single_apply]
          simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
            Finset.sum_ite_irrel, Finset.sum_const_zero]
          simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
          conv_lhs =>
            arg 2
            ext r
            rw [← (q.stackEquiv F).sum_comp]
          simp only [Equiv.symm_apply_apply]
          let e : (Coordinates q.endDimensions × L.stack) ≃
              ((a : A) → Fin (q.endDimensions a) × L.garbage a) :=
            { toFun := fun z a => (z.1 a, L.regroup z.2 a)
              invFun := fun z => (fun a => (z a).1, L.regroup.symm (fun a => (z a).2))
              left_inv := fun z => by simp
              right_inv := fun z => by simp }
          rw [← Fintype.sum_prod_type (fun z : Coordinates q.endDimensions × L.stack =>
            L.sourceAmplitude s i z * star (L.sourceAmplitude s i z))]
          change (∑ z : Coordinates q.endDimensions × L.stack,
            (∏ a, (L.matrix a *ᵥ s a i) (e z a)) *
              star (∏ a, (L.matrix a *ᵥ s a i) (e z a))) = _
          simp only [star_prod, ← Finset.prod_mul_distrib, Complex.star_def, Complex.mul_conj]
          rw [e.sum_comp (fun z => ∏ a, (Complex.normSq ((L.matrix a *ᵥ s a i) (z a)) : ℂ))]
          simp only [Complex.ofReal_prod, Complex.ofReal_sum]
          rw [Fintype.prod_sum]
        rw [trace_norm] at weight
        have wt := congrArg Complex.re weight
        simp only [M, Matrix.trace_single_eq_same, mul_one, Complex.ofReal_re,
          ← Complex.ofReal_sum] at wt
        simpa only [Complex.ofReal_re] using wt
      change ∀ t i, (∏ a, ∑ k, Complex.normSq
        ((ProductPrefixRigidity.accumulated (fun a => Fin (H a)) (path.localCoordinates F)
          (path.frame F 0).2.matrix (path.edges F) t a *ᵥ s a i) k)) = _
      intro t i
      have bridge := purified_local_path_bridge P (commonPreparation s (0 : Matrix S S ℂ))
      have accumulated_eq := (bridge.2.2 path).2.2.2.1
      change (∏ a, ∑ k, Complex.normSq
        ((ProductPrefixRigidity.accumulated (fun a => Fin (H a)) (path.localCoordinates F)
          (path.frame F 0).2.matrix (path.edges F) t a *ᵥ s a i) k)) = _
      conv_lhs =>
        arg 2
        ext a
        rw [accumulated_eq t a]
      have h := endpoint (path.take t) i
      have eq := cut_frame path F t
      have hn := congrArg (fun z : Σ d, LocalFactors H d =>
        ∏ a, ∑ k, Complex.normSq ((z.2.matrix a *ᵥ s a i) k)) eq
      exact hn.symm.trans h
    dsimp only
    refine ⟨probability, ?_⟩
    intro t
    let F := P.ancillas.rootFactors H
    have bridge := purified_local_path_bridge P (commonPreparation s (0 : Matrix S S ℂ))
    have frame_zero {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
        (q : ObservedPath T) (B : LocalFactors H d) : q.frame B 0 = ⟨d,B⟩ := by
      cases q <;> rfl
    have root : ∀ a, ProductPrefixRigidity.gram ((path.frame F 0).2.matrix a) = 1 := by
      rw [frame_zero]
      exact bridge.2.1
    exact ProductPrefixRigidity.prefix_rigidity (fun a => Fin (H a)) (path.localCoordinates F)
      (path.frame F 0).2.matrix (path.edges F) path.actorAt
      (bridge.2.2 path).2.2.2.2 root s normalized complete t
      (P.pathWeight s j₀ path) (fun k _ i => probability k i) t (Nat.le_refl t)
  -- An orthogonal source pair annihilates the actual endpoint matrix unit.
  have actual_scalar_gram_leaf_zero {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (w : P.tree.Leaves)
      (i j : S) (b : A)
      (orthogonal : star (s b j) ⬝ᵥ s b i = 0)
      (c : A → ℂ)
      (grams : ∀ a, ProductPrefixRigidity.gram
        (((P.tree.leafPath w).factors (P.ancillas.rootFactors H)).matrix a) = c a • 1) :
      corrected (P.tree.branch (appendAncillas P.ancillas
        (commonPreparation s (Matrix.single i j 1))) w) = 0 := by
    classical
    let F := (P.tree.leafPath w).factors (P.ancillas.rootFactors H)
    let e : (Coordinates (P.tree.leafPath w).endDimensions × F.stack) ≃
        ((a : A) → Fin ((P.tree.leafPath w).endDimensions a) × F.garbage a) :=
      { toFun := fun z a => (z.1 a, F.regroup z.2 a)
        invFun := fun z => (fun a => (z a).1, F.regroup.symm (fun a => (z a).2))
        left_inv := by intro z; simp
        right_inv := by intro z; funext a; simp }
    have pairing (a : A) :
        (∑ k, (F.matrix a *ᵥ s a i) k * star ((F.matrix a *ᵥ s a j) k)) =
          c a * (star (s a j) ⬝ᵥ s a i) := by
      calc
        _ = star (F.matrix a *ᵥ s a j) ⬝ᵥ (F.matrix a *ᵥ s a i) := by
          simp only [dotProduct, Pi.star_apply]; apply Finset.sum_congr rfl
          intro k _; ring
        _ = star (s a j) ⬝ᵥ (ProductPrefixRigidity.gram (F.matrix a) *ᵥ s a i) := by
          rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]; rfl
        _ = _ := by rw [grams]; simp [smul_mulVec, dotProduct_smul]
    have ampzero : (∑ z, F.sourceAmplitude s i z * star (F.sourceAmplitude s j z)) = 0 := by
      have reindex : (∑ z, F.sourceAmplitude s i z * star (F.sourceAmplitude s j z)) =
          ∑ z : (a : A) → Fin ((P.tree.leafPath w).endDimensions a) × F.garbage a,
            ∏ a, (F.matrix a *ᵥ s a i) (z a) * star ((F.matrix a *ᵥ s a j) (z a)) := by
        rw [← e.sum_comp]
        apply Finset.sum_congr rfl
        intro z _
        simp only [LocalFactors.sourceAmplitude, star_prod, ← Finset.prod_mul_distrib]
        rfl
      rw [reindex]
      rw [← Fintype.prod_sum (fun a (k : Fin ((P.tree.leafPath w).endDimensions a) × F.garbage a) =>
        (F.matrix a *ᵥ s a i) k * star ((F.matrix a *ᵥ s a j) k))]
      simp_rw [pairing]
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      rw [orthogonal, mul_zero]
    rw [actual_leaf_amplitude]
    let U : Matrix S S ℂ := P.tree.leafUnitary w
    have sand (z) : P.leafKraus s w z * Matrix.single i j 1 *
        (P.leafKraus s w z).conjTranspose =
        U * ((F.sourceAmplitude s i z * star (F.sourceAmplitude s j z)) •
          Matrix.single i j 1) * U.conjTranspose := by
      simp only [Protocol.leafKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      change U * (diagonal (fun k => F.sourceAmplitude s k z) *
        (single i j 1 * ((diagonal (fun k => F.sourceAmplitude s k z)).conjTranspose *
        U.conjTranspose))) = _
      rw [← Matrix.mul_assoc (single i j 1), ← Matrix.mul_assoc (diagonal _)]
      congr 2
      ext k l
      simp only [diagonal_conjTranspose, diagonal_mul, mul_diagonal,
        Matrix.smul_apply, smul_eq_mul, single_apply]
      split_ifs <;> simp_all
    simp_rw [sand]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← Finset.sum_smul, ampzero]
    simp
  -- A positive scalar leaf cannot annihilate that matrix unit.
  have actual_endpoint_obstruction {H : A → ℕ}
      (P : Protocol (Matrix.unitaryGroup S ℂ) H)
      (s : (a : A) → S → Fin (H a) → ℂ) (i j : S) (_distinct : i ≠ j)
      (b : A) (orthogonal : star (s b j) ⬝ᵥ s b i = 0)
      (endpoint : ∀ w, 0 < P.leafWeight s i w →
        ∃ c : A → ℝ, ∀ a, 0 < c a ∧ ProductPrefixRigidity.gram
          (((P.tree.leafPath w).factors (P.ancillas.rootFactors H)).matrix a) =
            (c a : ℂ) • 1) :
      ¬ P.ExactRecovery s := by
    intro recovery
    obtain ⟨nonneg, total, scalar⟩ := actual_recovery_leaf_scalarity P s i recovery
    have exists_pos : ∃ w, 0 < P.leafWeight s i w := by
      by_contra h
      push Not at h
      have hz : ∀ w, P.leafWeight s i w = 0 := fun w => le_antisymm (h w) (nonneg w)
      simp_rw [hz] at total
      simp at total
    obtain ⟨w, hw⟩ := exists_pos
    obtain ⟨c, hc⟩ := endpoint w hw
    have zero := actual_scalar_gram_leaf_zero P s w i j b orthogonal
      (fun a => (c a : ℂ)) (fun a => (hc a).2)
    rw [scalar] at zero
    have entry := congrArg (fun M : Matrix S S ℂ => (M i j).re) zero
    have weight_zero : P.leafWeight s i w = 0 := by
      simpa [Matrix.smul_apply, smul_eq_mul] using entry
    linarith
  -- Transport the recovered path invariant to each actual terminal factor.
  intro recovery
  apply actual_endpoint_obstruction P s i j distinct b orthogonal ?_ recovery
  intro w positive
  let F := P.ancillas.rootFactors H
  let path := P.tree.leafPath w
  have take_length {d : A → ℕ} {T : Tree (Matrix.unitaryGroup S ℂ) d}
      (q : ObservedPath T) : q.take q.length = q := by
    induction q with
    | here => rfl
    | next y tail ih =>
      simpa only [ObservedPath.length, ObservedPath.take] using
        (congrArg (ObservedPath.next y) ih)
  have leaf_sum {d : A → ℕ} (T : Tree (Matrix.unitaryGroup S ℂ) d)
      (v : T.Leaves) (f : T.Leaves → ℝ) :
      (∑ u : (T.leafPath v).selected.subtree.Leaves,
        f ((T.leafPath v).selected.extendLeaf u)) = f v := by
    induction T with
    | leaf U =>
      change (∑ u : Unit, f u) = f v
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact congrArg (fun u : Unit => f u) (Subsingleton.elim _ _)
    | node J child ih =>
      exact ih v.1 v.2 (fun u => f ⟨v.1,u⟩)
  have weight : P.pathWeight s i path path.length = P.leafWeight s i w := by
    unfold Protocol.pathWeight
    rw [take_length]
    exact leaf_sum P.tree w _
  have rigidity := (actual_recovery_path_rigidity P s i recovery normalized complete path).2
    path.length
  rcases rigidity with zero | pos
  · exact False.elim ((ne_of_gt positive) (weight.symm.trans zero.1))
  · obtain ⟨c, grams, rest⟩ := pos.2
    have bridge := purified_local_path_bridge P (commonPreparation s (0 : Matrix S S ℂ))
    have acc := (bridge.2.2 path).2.2.2.1
    have frame := (bridge.2.2 path).2.2.1
    have frameGrams : ∀ a, 0 < c a ∧ ProductPrefixRigidity.gram
        ((path.frame F path.length).2.matrix a) = (c a : ℂ) • 1 := by
      intro a
      simpa only [acc] using grams a
    have transported := congrArg (fun z : Σ d, LocalFactors H d =>
      ∀ a, 0 < c a ∧ ProductPrefixRigidity.gram (z.2.matrix a) = (c a : ℂ) • 1) frame
    exact ⟨c, transported.mp frameGrams⟩

end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol
