/- GID: D5/S3/Quantum/Recovery/FiniteLocalSharedLabelRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalSharedLabelRecovery
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual shared-label recovery gives normalized effects and finite-reference execution. -/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker
import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
open FiniteLocalProtocol FiniteLocalLatitudeGeometry
open ProductPrefixRigidity renaming gram → inputGram
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {Y : Type}
abbrev InputDimensions : Fin 2 → ℕ := fun _ => 2
abbrev ActualProtocol (Y : Type) := Protocol Y InputDimensions

def pairCoordinates : (Fin 2 × Fin 2) ≃ Coordinates InputDimensions where
  toFun p := ![p.1,p.2]
  invFun x := (x 0,x 1)
  left_inv p := rfl
  right_inv x := by funext a; fin_cases a <;> rfl

def sourceRecord (r : ℝ) (i : Fin 5) (x : Coordinates InputDimensions) : ℂ :=
  record r i (pairCoordinates.symm x)

def leafFactors (P : ActualProtocol Y) (w : P.tree.Leaves) :=
  (P.tree.leafPath w).factors (P.ancillas.rootFactors InputDimensions)

def leafEffect (P : ActualProtocol Y) (w : P.tree.Leaves) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (leafFactors P w).inputEffect.submatrix pairCoordinates pairCoordinates

def historyMap (P : ActualProtocol Y) (r : ℝ) (w : P.tree.Leaves)
    (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  recordTrace (P.tree.branch (appendAncillas P.ancillas
    (recordPreparation (sourceRecord r) X)) w).state

def correctedHistory (P : ActualProtocol Y) (r : ℝ)
    (U : Y → unitaryGroup (Fin 5) ℂ) (w : P.tree.Leaves)
    (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (U (P.tree.leafFeedback w) : Matrix (Fin 5) (Fin 5) ℂ) * historyMap P r w X *
    (U (P.tree.leafFeedback w) : Matrix (Fin 5) (Fin 5) ℂ)ᴴ

/-- Physical preparation and coarse execution with a finite untouched reference. -/
def referenceHistory (P : ActualProtocol Y) (r : ℝ) (F : Type) [Fintype F]
    (w : P.tree.Leaves) (X : Matrix (F × Fin 5) (F × Fin 5) ℂ) :
    Matrix (F × Fin 5) (F × Fin 5) ℂ :=
  recordTrace (P.tree.branch (appendAncillas P.ancillas
    (recordPreparation (fun z : F × Fin 5 => sourceRecord r z.2) X)) w).state

def referenceCorrectedHistory (P : ActualProtocol Y) (r : ℝ)
    (U : Y → unitaryGroup (Fin 5) ℂ) (F : Type) [Fintype F] [DecidableEq F]
    (w : P.tree.Leaves) (X : Matrix (F × Fin 5) (F × Fin 5) ℂ) :
    Matrix (F × Fin 5) (F × Fin 5) ℂ :=
  let V := kronecker (1 : Matrix F F ℂ)
    (U (P.tree.leafFeedback w) : Matrix (Fin 5) (Fin 5) ℂ)
  V * referenceHistory P r F w X * Vᴴ

def PhysicalReferenceLaws (P : ActualProtocol Y) (r : ℝ)
    (U : Y → unitaryGroup (Fin 5) ℂ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (w : P.tree.Leaves)
    (X : Matrix (F × Fin 5) (F × Fin 5) ℂ) (f g : F),
    (referenceCorrectedHistory P r U F w X).submatrix (fun i => (f,i)) (fun j => (g,j)) =
    correctedHistory P r U w (X.submatrix (fun i => (f,i)) (fun j => (g,j)))

def Accepted (P : ActualProtocol Y) (accept : Y → Prop) :=
  {w : P.tree.Leaves // accept (P.tree.leafFeedback w)}

noncomputable instance acceptedFintype (P : ActualProtocol Y) (accept : Y → Prop) :
    Fintype (Accepted P accept) := by
  classical
  unfold Accepted
  infer_instance

def acceptedMap (P : ActualProtocol Y) (r : ℝ) (accept : Y → Prop)
    (U : Y → unitaryGroup (Fin 5) ℂ)
    (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ := by
  classical
  exact ∑ w : Accepted P accept, correctedHistory P r U w.val X

def referenceAcceptedMap (P : ActualProtocol Y) (r : ℝ) (accept : Y → Prop)
    (U : Y → unitaryGroup (Fin 5) ℂ)
    (F : Type) [Fintype F] [DecidableEq F] (X : Matrix (F × Fin 5) (F × Fin 5) ℂ) :
    Matrix (F × Fin 5) (F × Fin 5) ℂ := by
  classical
  exact ∑ w : Accepted P accept, referenceCorrectedHistory P r U F w.val X

def RowIndices {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) :=
  Fin (d a) × F.garbage a

noncomputable instance rowIndicesFintype {d : Fin 2 → ℕ}
    (F : LocalFactors InputDimensions d) (a : Fin 2) : Fintype (RowIndices F a) :=
  inferInstanceAs (Fintype (Fin (d a) × F.garbage a))

def rowAmplitude {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d)
    (r : ℝ) (z : RowIndices F 0 × RowIndices F 1) (i : Fin 5) : ℂ :=
  (∑ k, F.matrix 0 z.1 k * source r i k) * (∑ k, F.matrix 1 z.2 k * source r i k)

def historyKraus (P : ActualProtocol Y) (r : ℝ)
    (U : Y → unitaryGroup (Fin 5) ℂ) (w : P.tree.Leaves)
    (z : RowIndices (leafFactors P w) 0 × RowIndices (leafFactors P w) 1) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  (U (P.tree.leafFeedback w) : Matrix (Fin 5) (Fin 5) ℂ) *
    diagonal (rowAmplitude (leafFactors P w) r z)

def symProduct (x y : Fin 2 → ℂ) : Fin 3 → ℂ := ![x 0*y 0,x 0*y 1+x 1*y 0,x 1*y 1]

def localTrace {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) : ℝ :=
  (trace (inputGram (F.matrix a))).re

def localBloch {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) : Bloch :=
  (localTrace F a)⁻¹ • bloch (inputGram (F.matrix a))

def effectWeight {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) : ℝ :=
  localTrace F 0 * localTrace F 1

def pairEffect {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  F.inputEffect.submatrix pairCoordinates pairCoordinates

def splitWeight {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d)
    (J : Instrument d) (y : Fin J.outcomes) : ℝ :=
  localTrace (F.advance J y) J.actor / localTrace F J.actor

/-- Trace weights are effect weights, not unknown-input outcome probabilities.
Zero children keep weight zero and need no division by their own trace. -/
def NormalizedInputTreeLaws (P : ActualProtocol Y) : Prop :=
  effectWeight (P.ancillas.rootFactors InputDimensions) = 4 ∧
  (∀ a, localBloch (P.ancillas.rootFactors InputDimensions) a = 0) ∧
  (∀ {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d), (∀ a, 0 ≤ localTrace F a ∧
      (localTrace F a = 0 ↔ inputGram (F.matrix a) = 0) ∧
      ‖localBloch F a‖ ≤ 1 ∧
      inputGram (F.matrix a) = (localTrace F a : ℂ) • rho (localBloch F a)) ∧
    pairEffect F = (effectWeight F : ℂ) • Q (localBloch F 0) (localBloch F 1) ∧
    (trace (pairEffect F)).re = effectWeight F) ∧
  (∀ {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (J : Instrument d), (effectWeight F > 0 →
      (∀ y, 0 ≤ splitWeight F J y) ∧
      (∑ y, splitWeight F J y) = 1 ∧
      (∀ y, effectWeight (F.advance J y) = effectWeight F * splitWeight F J y) ∧
      localBloch F J.actor = ∑ y, splitWeight F J y • localBloch (F.advance J y) J.actor ∧
      (∀ y a, a ≠ J.actor → localBloch (F.advance J y) a = localBloch F a)) ∧
    (F.inputEffect = 0 → ∀ y, (F.advance J y).inputEffect = 0)) ∧
  (∀ {d : Fin 2 → ℕ} (T : Tree Y d) (F : LocalFactors InputDimensions d),
    F.inputEffect = 0 → ∀ w : T.Leaves, ((T.leafPath w).factors F).inputEffect = 0)

set_option maxHeartbeats 2000000 in
-- The proof retains the finite actual history family and all inaccessible rows.
theorem actual_shared_label_support_rigidity (P : ActualProtocol Y) (r : ℝ) (hr : 0 < r)
    (accept : Y → Prop)
    (U : Y → unitaryGroup (Fin 5) ℂ)
    (p : ℝ) (hp : 0 ≤ p)
    (recovery : ∀ X : Matrix (Fin 5) (Fin 5) ℂ, acceptedMap P r accept U X = (p : ℂ) • X) :
    p ≤ 1 ∧ InputEffectTreeLaws P ∧ NormalizedInputTreeLaws P ∧ PhysicalReferenceLaws P r U ∧
    (∀ q : ℝ, (∀ X : Matrix (Fin 5) (Fin 5) ℂ, acceptedMap P r accept U X = (q : ℂ) • X) ↔
      (∀ (F : Type) [Fintype F] [DecidableEq F] (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
        referenceAcceptedMap P r accept U F X = (q : ℂ) • X)) ∧
    (∀ w : P.tree.Leaves, leafEffect P w = 0 → ∀ (F : Type) [Fintype F] [DecidableEq F]
        (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
        referenceCorrectedHistory P r U F w X = 0) ∧
    (1/2 < r^2 → r^2 < 2 → p = h r * ∑ w : Accepted P accept, effectWeight (leafFactors P w.val)) ∧
    ∀ w : Accepted P accept, (∃ c : ℝ, 0 ≤ c ∧ (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        correctedHistory P r U w.val X = (c : ℂ) • X) ∧
      (∀ (F : Type) [Fintype F] [DecidableEq F] (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
        referenceCorrectedHistory P r U F w.val X = (c : ℂ) • X)) ∧
      (p = 0 → leafEffect P w.val = 0) ∧
      (leafEffect P w.val ≠ 0 → (inputGram ((leafFactors P w.val).matrix 0)).rank = 1 ∧
        (inputGram ((leafFactors P w.val).matrix 1)).rank = 1 ∧
        (1/2 < r^2 → r^2 < 2 → 0 < effectWeight (leafFactors P w.val) ∧
          (localBloch (leafFactors P w.val) 0,localBloch (leafFactors P w.val) 1) ∈ K_s r ∧
          ∀ (F : Type) [Fintype F] [DecidableEq F] (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
            referenceCorrectedHistory P r U F w.val X =
              ((effectWeight (leafFactors P w.val) * h r : ℝ) : ℂ) • X)) := by
  let ReferenceMatrix (F : Type) : Type := Matrix (F × Fin 5) (F × Fin 5) ℂ
  have input_effect_tree : InputEffectTreeLaws P := by
    classical
    have gram_amplitude {d : (Fin 2) → ℕ} (F : LocalFactors InputDimensions d) (x z : Coordinates InputDimensions) :
        (∑ u : Coordinates d × F.stack, star (F.amplitude u x) * F.amplitude u z) =
          F.inputEffect x z := by
      let e : (Coordinates d × F.stack) ≃ ((a : (Fin 2)) → Fin (d a) × F.garbage a) :=
        { toFun := fun p a => (p.1 a,F.regroup p.2 a)
          invFun := fun u => (fun a => (u a).1,F.regroup.symm (fun a => (u a).2))
          left_inv := fun p => by simp
          right_inv := fun u => by funext a; simp }
      rw [← e.symm.sum_comp]
      simp only [LocalFactors.amplitude, ProductPrefixRigidity.productMap,
        star_prod, ← Finset.prod_mul_distrib]
      simp only [e,Equiv.coe_fn_mk,Equiv.symm_mk,Equiv.apply_symm_apply]
      change (∑ u : (a : (Fin 2)) → Fin (d a) × F.garbage a,
        ∏ a, star (F.matrix a (u a) (x a)) * F.matrix a (u a) (z a)) = _
      erw [← Fintype.prod_sum (fun a (u : Fin (d a) × F.garbage a) =>
        star (F.matrix a u (x a)) * F.matrix a u (z a))]
      rfl
    have psd {d : (Fin 2) → ℕ} (F : LocalFactors InputDimensions d) : F.inputEffect.PosSemidef := by
      let L : Matrix (Coordinates d × F.stack) (Coordinates InputDimensions) ℂ := F.amplitude
      have he : Lᴴ * L = F.inputEffect := by
        ext x z
        exact gram_amplitude F x z
      rw [← he]
      exact Matrix.posSemidef_conjTranspose_mul_self L
    have instrument_gram {d : (Fin 2) → ℕ} (J : Instrument d) :
        (∑ y, ∑ k : Hidden J y, (chosenKraus J y k)ᴴ * chosenKraus J y k) = 1 := by
      apply Matrix.ext_iff_trace_mul_right.mpr
      intro X
      rw [Matrix.sum_mul, Matrix.trace_sum]
      simp only [Matrix.sum_mul, Matrix.trace_sum]
      have hk (y : Fin J.outcomes) :
          action (J.operation y) X = ∑ k, chosenKraus J y k * X * (chosenKraus J y k)ᴴ :=
        ((recursive_coarse_retained (FiniteLocalProtocol.Tree.node J (fun _ => FiniteLocalProtocol.Tree.leaf ()))
          (0 : RetainedState Unit Unit d)).2.2) y X
      calc
        _ = ∑ y, Matrix.trace (action (J.operation y) X) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hk y, Matrix.trace_sum]
          exact Finset.sum_congr rfl (fun _ _ => by rw [Matrix.mul_assoc, Matrix.trace_mul_comm])
        _ = Matrix.trace (1 * X) := by simpa only [Matrix.one_mul] using J.trace_preserving X
    have inactive {d : (Fin 2) → ℕ} (F : LocalFactors InputDimensions d) (J : Instrument d)
        (y : Fin J.outcomes) (a : (Fin 2)) (ha : a ≠ J.actor) :
        inputGram ((F.advance J y).matrix a) = inputGram (F.matrix a) := by
      let e : (Fin (J.output y a) × (LocalHidden J y a × F.garbage a)) ≃
          (Fin (d a) × F.garbage a) :=
        { toFun := fun p => (Fin.cast (J.unchanged y a ha) p.1,p.2.2)
          invFun := fun p => (Fin.cast (J.unchanged y a ha).symm p.1,
            (fun u => (ha u.2).elim,p.2))
          left_inv := fun p => by
            ext
            · simp
            · funext u; exact (ha u.2).elim
            · rfl
          right_inv := fun p => by ext <;> simp }
      ext x z
      change (∑ u, star ((F.advance J y).matrix a u x) *
        (F.advance J y).matrix a u z) = _
      rw [← e.symm.sum_comp]
      simp [LocalFactors.advance, LocalFactors.advanceMatrix, ha, e,
        inputGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have actor_sum {d : (Fin 2) → ℕ} (F : LocalFactors InputDimensions d) (J : Instrument d) :
        (∑ y, inputGram ((F.advance J y).matrix J.actor)) = inputGram (F.matrix J.actor) := by
      let C (g : F.garbage J.actor) : Matrix (Fin (d J.actor)) (Fin (InputDimensions J.actor)) ℂ :=
        fun i x => F.matrix J.actor (i,g) x
      have he (y : Fin J.outcomes) : inputGram ((F.advance J y).matrix J.actor) =
          ∑ g, (C g)ᴴ * (∑ k : Hidden J y, (chosenKraus J y k)ᴴ * chosenKraus J y k) * C g := by
        let e : (Hidden J y × (Fin (J.output y J.actor) × F.garbage J.actor)) ≃
            (Fin (J.output y J.actor) × (LocalHidden J y J.actor × F.garbage J.actor)) :=
          { toFun := fun p => (p.2.1,(fun _ => p.1,p.2.2))
            invFun := fun p => (p.2.1 ⟨(),rfl⟩,(p.1,p.2.2))
            left_inv := fun p => rfl
            right_inv := fun p => by
              ext
              · rfl
              · funext u
                have hu : u = ⟨(),rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
                rw [hu]
              · rfl }
        calc
          _ = ∑ k : Hidden J y, ∑ g : F.garbage J.actor,
              (chosenKraus J y k * C g)ᴴ * (chosenKraus J y k * C g) := by
            ext x z
            change (∑ v, star ((F.advance J y).matrix J.actor v x) *
              (F.advance J y).matrix J.actor v z) = _
            rw [← e.sum_comp,Fintype.sum_prod_type]
            simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            refine Finset.sum_congr rfl (fun o _ => ?_)
            simp [e, LocalFactors.advanceMatrix, C]
          _ = _ := by
            rw [Finset.sum_comm]
            simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc,
              Matrix.mul_sum,Matrix.sum_mul]
      simp_rw [he]
      rw [Finset.sum_comm]
      simp only [← Matrix.mul_sum, ← Matrix.sum_mul, instrument_gram, Matrix.mul_one]
      ext x z
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        inputGram, Fintype.sum_prod_type, C]
      exact Finset.sum_comm
    have children {d : (Fin 2) → ℕ} (F : LocalFactors InputDimensions d) (J : Instrument d) :
        (∑ y, (F.advance J y).inputEffect) = F.inputEffect := by
      ext x z
      simp only [Matrix.sum_apply, LocalFactors.inputEffect, ProductPrefixRigidity.productMap]
      simp_rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ J.actor)]
      have hr (y : Fin J.outcomes) : (∏ a ∈ Finset.univ.erase J.actor,
            inputGram ((F.advance J y).matrix a) (x a) (z a)) =
          ∏ a ∈ Finset.univ.erase J.actor, inputGram (F.matrix a) (x a) (z a) := by
        refine Finset.prod_congr rfl (fun a ha => ?_)
        rw [inactive F J y a (Finset.mem_erase.mp ha).1]
      simp_rw [hr]
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Matrix.sum_apply] using
        congrArg (fun M => M (x J.actor) (z J.actor)) (actor_sum F J)
    have descendants {d : (Fin 2) → ℕ} (T : Tree Y d) :
        ∀ F : LocalFactors InputDimensions d, T.descendantEffect F = F.inputEffect := by
      induction T with
      | leaf y => intro F; simp [Tree.descendantEffect, Tree.Leaves, Tree.leafPath,
          ObservedPath.factors]
      | node J child ih =>
        intro F
        change (∑ w : (y : Fin J.outcomes) × (child y).Leaves,
          (((child w.1).leafPath w.2).factors (F.advance J w.1)).inputEffect) = _
        rw [Fintype.sum_sigma]
        change (∑ y, (child y).descendantEffect (F.advance J y)) = _
        simp_rw [ih]
        exact children F J
    have edge_trace {I : Type} [Fintype I] {d : (Fin 2) → ℕ} (J : Instrument d)
        (y : Fin J.outcomes) {G : Type} [Fintype G] (X : RetainedState I G d) :
        traceGarbage (retainedStep J y X) = step J y (traceGarbage X) := by
      have h := (recursive_coarse_retained (FiniteLocalProtocol.Tree.node J (fun _ => FiniteLocalProtocol.Tree.leaf ())) X).1
      simp only [retainedOutputs, terminalOutputs, List.map_singleton] at h
      have collapse {α : Type} {n : ℕ} (f : Fin n → α) :
          (List.ofFn (fun y => [f y])).flatten = List.ofFn f := by
        rw [show List.ofFn (fun y => [f y]) = (List.ofFn f).map (fun z => [z])
          from (List.map_ofFn (f := f) (g := fun z => [z])).symm]
        exact List.flatMap_singleton' _
      rw [collapse,collapse] at h
      have hy := congrFun (List.ofFn_injective h) y
      simpa only [Terminal.mk.injEq, heq_eq_eq, true_and] using hy
    have branch_path {I : Type} [Fintype I] {d : (Fin 2) → ℕ} (T : Tree Y d) :
        ∀ (w : T.Leaves) {G : Type} [Fintype G] (X : RetainedState I G d),
        T.branch (traceGarbage X) w =
          ⟨(T.leafPath w).history,T.leafFeedback w,(T.leafPath w).endDimensions,
            traceGarbage ((T.leafPath w).execute X)⟩ := by
      induction T with
      | leaf y => intro w G _ X; rfl
      | node J child ih =>
        intro w G _ X
        rcases w with ⟨y,w⟩
        simp only [Tree.branch,Tree.leafPath,Tree.leafFeedback,ObservedPath.history,
          ObservedPath.endDimensions,ObservedPath.execute]
        rw [← edge_trace,ih]
    have root := (purified_local_path_bridge P (0 : State Unit InputDimensions)).2.1
    refine ⟨root, ?_, (fun F => ⟨psd F,fun a => posSemidef_conjTranspose_mul_self _⟩),
      (fun F J => ⟨children F J,actor_sum F J,inactive F J⟩),descendants,?_⟩
    · ext x z
      simp only [LocalFactors.inputEffect, ProductPrefixRigidity.productMap, root,
        Matrix.one_apply]
      rw [Fintype.prod_ite_zero]
      simp [funext_iff]
    · intro I _ q X w i j
      let B := P.ancillas.rootFactors InputDimensions
      let path := P.tree.leafPath w
      let F := path.factors B
      have bridge := purified_local_path_bridge P (recordPreparation q X)
      rw [← bridge.1, branch_path, (bridge.2.2 path).2.1]
      simp only [recordTrace, traceGarbage, Matrix.submatrix_apply]
      change (∑ r, ∑ g : path.stack B.stack,
        F.lift (recordPreparation q X) ((i,r),(path.stackEquiv B).symm g)
          ((j,r),(path.stackEquiv B).symm g)) = _
      conv_lhs =>
        enter [2,r]
        erw [← (path.stackEquiv B).sum_comp]
      simp only [Equiv.symm_apply_apply]
      change (∑ r, ∑ g : F.stack,
        F.lift (recordPreparation q X) ((i,r),g) ((j,r),g)) = _
      let f : Coordinates path.endDimensions × F.stack → ℂ := fun u =>
        F.lift (recordPreparation q X) ((i,u.1),u.2) ((j,u.1),u.2)
      change (∑ r, ∑ g, f (r,g)) = _
      rw [← Fintype.sum_prod_type f]
      dsimp only [f,LocalFactors.lift,recordPreparation]
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      change (∑ u, F.amplitude u x * (X i j * q i x * star (q j z)) *
        star (F.amplitude u z)) = star (q j z) * (F.inputEffect z x * q i x) * X i j
      have he := gram_amplitude F z x
      rw [← he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      ring
  have raw_pair {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) :
      pairEffect F = kronecker (inputGram (F.matrix 0)) (inputGram (F.matrix 1)) := by
    ext x z
    simp [pairEffect,LocalFactors.inputEffect,ProductPrefixRigidity.productMap,
      pairCoordinates,Fin.prod_univ_two,Matrix.kronecker_apply,Matrix.cons_val]
  have normalized_tree : NormalizedInputTreeLaws P := by
    classical
    have normalize (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
        0 ≤ (trace M).re ∧ ((trace M).re = 0 ↔ M = 0) ∧
        ‖(trace M).re⁻¹ • bloch M‖ ≤ 1 ∧
        M = ((trace M).re : ℂ) • rho ((trace M).re⁻¹ • bloch M) := by
      have ht : 0 ≤ (trace M).re := (Complex.nonneg_iff.mp hM.trace_nonneg).1
      have hi : (trace M).im = 0 := (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm
      have hz : (trace M).re = 0 ↔ M = 0 := by
        rw [← hM.trace_eq_zero_iff]
        simp [Complex.ext_iff, hi]
      have h00 := Complex.conj_eq_iff_im.mp (hM.isHermitian.apply 0 0)
      have h11 := Complex.conj_eq_iff_im.mp (hM.isHermitian.apply 1 1)
      have h10r : (M 1 0).re = (M 0 1).re := by
        simpa using (congrArg Complex.re (hM.isHermitian.apply 1 0)).symm
      have h10i : (M 1 0).im = -(M 0 1).im := by
        simpa using (congrArg Complex.im (hM.isHermitian.apply 1 0)).symm
      have determinant : (det M).re = ((trace M).re^2 - ‖bloch M‖^2)/4 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Matrix.det_fin_two, trace, Fin.sum_univ_two, Fin.sum_univ_three,
          bloch,h00,h11,h10r,h10i]
        ring
      have hb : ‖bloch M‖ ≤ (trace M).re := by
        have hd := (Complex.nonneg_iff.mp hM.det_nonneg).1
        rw [determinant] at hd
        nlinarith only [hd,ht,norm_nonneg (bloch M)]
      refine ⟨ht,hz,?_,?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht)]
        exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht)).trans
          (by by_cases h : (trace M).re = 0 <;> simp [h])
      · by_cases h : (trace M).re = 0
        · simp [hz.mp h,h,rho]
        · simp only [trace, Fin.sum_univ_two, Matrix.diag_apply, Complex.add_re] at h
          ext i j
          fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
            simp [rho, blochMatrix, bloch, trace, Fin.sum_univ_two,
              h00, h11, h10r, h10i, Complex.mul_re, Complex.mul_im,
              Complex.normSq_apply] <;>
            field_simp [h, (add_comm (M 0 0).re (M 1 1).re) ▸ h] <;> ring
    have single {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) :
        0 ≤ localTrace F a ∧
        (localTrace F a = 0 ↔ inputGram (F.matrix a) = 0) ∧
        ‖localBloch F a‖ ≤ 1 ∧
        inputGram (F.matrix a) = (localTrace F a : ℂ) • rho (localBloch F a) :=
      normalize _ ((input_effect_tree.2.2.1 F).2 a)
    have scaled {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) :
        localTrace F a • localBloch F a = bloch (inputGram (F.matrix a)) := by
      by_cases h : localTrace F a = 0
      · ext i
        fin_cases i <;> simp [h,(single F a).2.1.mp h,
          bloch]
      · simp [localBloch,smul_smul,h]
    refine ⟨?_,?_,?_,?_,?_⟩
    · norm_num [effectWeight,localTrace,input_effect_tree.1,trace,Fin.sum_univ_two]
    · intro a
      simp [localBloch,localTrace,input_effect_tree.1,
        bloch]
    · intro d F
      refine ⟨single F,?_,?_⟩
      · rw [raw_pair,(single F 0).2.2.2,(single F 1).2.2.2,
          Matrix.kronecker]
        rw [Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul]
        simp [effectWeight,Q,Complex.ofReal_mul,mul_comm]
      · rw [raw_pair,Matrix.kronecker,Matrix.trace_kronecker]
        have ha := (Complex.nonneg_iff.mp ((input_effect_tree.2.2.1 F).2 0).trace_nonneg).2
        have hb := (Complex.nonneg_iff.mp ((input_effect_tree.2.2.1 F).2 1).trace_nonneg).2
        simp [Complex.mul_re,← ha,← hb,effectWeight,localTrace]
    · intro d F J
      have actor_cases : J.actor = 0 ∨ J.actor = 1 := by omega
      have hs := input_effect_tree.2.2.2.1 F J
      have inactive (y : Fin J.outcomes) (a : Fin 2) (ha : a ≠ J.actor) :
          localTrace (F.advance J y) a = localTrace F a ∧
          localBloch (F.advance J y) a = localBloch F a := by
        simp [localTrace,localBloch,hs.2.2 y a ha]
      constructor
      · intro hp
        have trace_positive (a : Fin 2) : 0 < localTrace F a := by
          have h0 := (single F 0).1
          have h1 := (single F 1).1
          change 0 < localTrace F 0 * localTrace F 1 at hp
          rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> nlinarith
        have active := trace_positive J.actor
        have trsum : (∑ y,localTrace (F.advance J y) J.actor) = localTrace F J.actor := by
          simp only [localTrace]
          rw [← Complex.re_sum,← Matrix.trace_sum,hs.2.1]
        refine ⟨?_,?_,?_,?_,?_⟩
        · intro y
          exact div_nonneg (single (F.advance J y) J.actor).1 active.le
        · simp only [splitWeight,← Finset.sum_div,trsum,div_self active.ne']
        · intro y
          by_cases hactor : J.actor = 0
          · have hi := (inactive y 1 (by omega)).1
            simp only [effectWeight,splitWeight,hactor,hi]
            field_simp [ne_of_gt (trace_positive 0), ne_of_gt (trace_positive 1)] <;> ring
          · have hactor : J.actor = 1 := (actor_cases).resolve_left hactor
            have hi := (inactive y 0 (by omega)).1
            simp only [effectWeight,splitWeight,hactor,hi]
            field_simp [ne_of_gt (trace_positive 0), ne_of_gt (trace_positive 1)] <;> ring
        · change (localTrace F J.actor)⁻¹ •
            blochLinear (inputGram (F.matrix J.actor)) = _
          rw [← hs.2.1, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          change (localTrace F J.actor)⁻¹ • bloch (inputGram ((F.advance J y).matrix J.actor)) = _
          rw [← scaled (F.advance J y) J.actor, smul_smul]
          congr 1
          simp [splitWeight, div_eq_mul_inv, mul_comm]
        · intro y a ha
          exact (inactive y a ha).2
      · intro hz
        have total : (∑ y,(F.advance J y).inputEffect) = 0 := by rw [hs.1,hz]
        have hn : (0 : Fin J.outcomes → Matrix (Coordinates InputDimensions)
            (Coordinates InputDimensions) ℂ) ≤ fun y => (F.advance J y).inputEffect :=
          fun y => (input_effect_tree.2.2.1 (F.advance J y)).1.nonneg
        exact congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp total)

    · intro d T F hz
      have total : (∑ w : T.Leaves,((T.leafPath w).factors F).inputEffect) = 0 := by
        change T.descendantEffect F = 0
        rw [input_effect_tree.2.2.2.2.1,hz]
      have hn : (0 : T.Leaves → Matrix (Coordinates InputDimensions)
          (Coordinates InputDimensions) ℂ) ≤ fun w => ((T.leafPath w).factors F).inputEffect :=
        fun w => (input_effect_tree.2.2.1 ((T.leafPath w).factors F)).1.nonneg
      exact congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp total)
  have source_map (w : P.tree.Leaves) (X : LocalState 5) (i j : Fin 5) : historyMap P r w X i j =
        (star (record r j) ⬝ᵥ (leafEffect P w *ᵥ record r i)) * X i j := by
    simp only [historyMap, input_effect_tree.2.2.2.2.2]
    congr 1
  have reference_blocks : PhysicalReferenceLaws P r U := by
    classical
    intro F _ _ w X f g
    have uncorrected : (referenceHistory P r F w X).submatrix (fun i => (f,i)) (fun j => (g,j)) =
        historyMap P r w (X.submatrix (fun i => (f,i)) (fun j => (g,j))) := by
      ext i j
      have ht := input_effect_tree.2.2.2.2.2
      rw [referenceHistory, Matrix.submatrix_apply, ht, historyMap, ht]
      rfl
    have feedback (V : LocalState 5) (M : ReferenceMatrix F) :
        (kronecker (1 : Matrix F F ℂ) V * M * (kronecker (1 : Matrix F F ℂ) V)ᴴ).submatrix
          (fun i => (f,i)) (fun j => (g,j)) =
        V * M.submatrix (fun i => (f,i)) (fun j => (g,j)) * Vᴴ := by
      ext i j
      simp [ReferenceMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        kronecker, kroneckerMap, Matrix.one_apply, Finset.sum_mul,
        apply_ite, Finset.sum_ite_irrel]
    have hb := feedback (U (P.tree.leafFeedback w) : LocalState 5)
      (referenceHistory P r F w X)
    rw [uncorrected] at hb
    exact hb
  have accepted_blocks (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F) (f g : F) :
      (referenceAcceptedMap P r accept U F X).submatrix (fun i => (f,i)) (fun j => (g,j)) =
      acceptedMap P r accept U (X.submatrix (fun i => (f,i)) (fun j => (g,j))) := by
    classical
    ext i j
    simp only [referenceAcceptedMap,acceptedMap,Matrix.submatrix_apply,Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrFun (congrFun (reference_blocks F w.val X f g) i) j
  have reference_recovery (q : ℝ) : (∀ X : LocalState 5, acceptedMap P r accept U X = (q : ℂ) • X) ↔
      (∀ (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F),
        referenceAcceptedMap P r accept U F X = (q : ℂ) • X) := by
    constructor
    · intro h F _ _ X
      ext ⟨f,i⟩ ⟨g,j⟩
      have hb := congrFun (congrFun (accepted_blocks F X f g) i) j
      rw [h] at hb
      exact hb
    · intro h X
      let M : ReferenceMatrix Unit := fun a b => X a.2 b.2
      have hm := congrArg (fun N : ReferenceMatrix Unit =>
        N.submatrix (fun i => ((),i)) (fun j => ((),j))) (h Unit M)
      rw [accepted_blocks] at hm
      exact hm
  have zero_reference (w : P.tree.Leaves) (hz : leafEffect P w = 0)
      (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F) :
      referenceCorrectedHistory P r U F w X = 0 := by
    have hu (M : LocalState 5) : historyMap P r w M = 0 := by
      ext i j
      rw [source_map, hz]
      simp
    ext ⟨f,i⟩ ⟨g,j⟩
    have hb := congrFun (congrFun (reference_blocks F w X f g) i) j
    simpa [correctedHistory, hu] using hb
  have support_result : ∀ w : Accepted P accept, (∃ c : ℝ, 0 ≤ c ∧ (∀ X : LocalState 5,
          correctedHistory P r U w.val X = (c : ℂ) • X) ∧
        (∀ (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F),
          referenceCorrectedHistory P r U F w.val X = (c : ℂ) • X)) ∧
        (p = 0 → leafEffect P w.val = 0) ∧
        (leafEffect P w.val ≠ 0 → (inputGram ((leafFactors P w.val).matrix 0)).rank = 1 ∧
          (inputGram ((leafFactors P w.val).matrix 1)).rank = 1 ∧
          (1/2 < r^2 → r^2 < 2 → 0 < effectWeight (leafFactors P w.val) ∧
            (localBloch (leafFactors P w.val) 0,localBloch (leafFactors P w.val) 1) ∈ K_s r ∧
            ∀ (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F),
              referenceCorrectedHistory P r U F w.val X =
                ((effectWeight (leafFactors P w.val) * h r : ℝ) : ℂ) • X)) := by
    classical
    let Z := fun w : Accepted P accept =>
      RowIndices (leafFactors P w.val) 0 × RowIndices (leafFactors P w.val) 1
    let K : ((w : Accepted P accept) × Z w) → LocalState 5 :=
      fun z => historyKraus P r U z.1.val z.2
    have representation (w : P.tree.Leaves) (X : LocalState 5) : correctedHistory P r U w X =
          ∑ z, historyKraus P r U w z * X * (historyKraus P r U w z)ᴴ := by
      have marginal : historyMap P r w X =
          ∑ z : RowIndices (leafFactors P w) 0 × RowIndices (leafFactors P w) 1,
            diagonal (rowAmplitude (leafFactors P w) r z) * X *
              (diagonal (rowAmplitude (leafFactors P w) r z))ᴴ := by
        let F := leafFactors P w
        have ef : leafEffect P w = kronecker (inputGram (F.matrix 0)) (inputGram (F.matrix 1)) :=
          raw_pair F
        have local_gram {R : Type} [Fintype R] (L : Matrix R (Fin 2) ℂ) (i j : Fin 5) :
            star (source r j) ⬝ᵥ (inputGram L *ᵥ source r i) =
            ∑ a, (L *ᵥ source r i) a * star ((L *ᵥ source r j) a) := by
          rw [inputGram, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
          exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
        have coeff (i j : Fin 5) : star (record r j) ⬝ᵥ (leafEffect P w *ᵥ record r i) =
            (star (source r j) ⬝ᵥ (inputGram (F.matrix 0) *ᵥ source r i)) *
            (star (source r j) ⬝ᵥ (inputGram (F.matrix 1) *ᵥ source r i)) := by
          rw [ef]
          simp only [kronecker, kroneckerMap, Matrix.of_apply, record, dotProduct, Matrix.mulVec,
            Fintype.sum_prod_type,Fin.sum_univ_two,Pi.star_apply,star_mul]
          ring
        ext i j
        rw [source_map,coeff,local_gram,local_gram]
        simp only [Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
          Matrix.mul_diagonal]
        conv_rhs => rw [Fintype.sum_prod_type]
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        simp only [Pi.star_apply, rowAmplitude, Matrix.mulVec, dotProduct, star_mul, F]
        ring
      unfold correctedHistory
      rw [marginal, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [historyKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have total (X : LocalState 5) : (∑ z, K z * X * (K z)ᴴ) = (p : ℂ) • X := by
      rw [Fintype.sum_sigma]
      change (∑ w : Accepted P accept, ∑ z : Z w,
        historyKraus P r U w.val z * X * (historyKraus P r U w.val z)ᴴ) = _
      calc
        _ = acceptedMap P r accept U X := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          exact (representation w.val X).symm
        _ = _ := recovery X
    have zero_kraus (hp0 : p = 0) (z : (w : Accepted P accept) × Z w) : K z = 0 := by
      have hn : (0 : ((w : Accepted P accept) × Z w) → LocalState 5) ≤
          fun z => K z * (K z)ᴴ := fun z => (posSemidef_self_mul_conjTranspose _).nonneg
      have each := (Fintype.sum_eq_zero_iff_of_nonneg hn).mp
        (by simpa [hp0] using total 1)
      exact Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa using congrFun each z)
    have scalar (z : (w : Accepted P accept) × Z w) : K z = K z 0 0 • (1 : LocalState 5) := by
      by_cases hp0 : p = 0
      · simp [zero_kraus hp0 z]
      · have pp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
        let c : ℂ := (Real.sqrt p : ℂ)⁻¹
        have sq : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by exact_mod_cast Real.sq_sqrt hp
        have s0 : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr pp)
        have normalized (X : LocalState 5) : (∑ z, (c • K z) * X * (c • K z)ᴴ) = X := by
          simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul, ← Finset.smul_sum]
          rw [total, smul_smul]
          have cc : star c * c * (p : ℂ) = 1 := by
            simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
            rw [← sq]
            field_simp [s0]
          rw [cc,one_smul]
        have hs := KrausLeftInverseNecessity.identity_kraus_scalar
          (fun z => c • K z) normalized (0 : Fin 5) z
        apply (smul_right_injective (LocalState 5) (inv_ne_zero s0))
        simpa only [Matrix.smul_apply, smul_eq_mul, smul_smul] using hs
    have uncorrected_scalar (w : Accepted P accept) (z : Z w) :
        diagonal (rowAmplitude (leafFactors P w.val) r z) = (K ⟨w,z⟩ 0 0) •
            (U (P.tree.leafFeedback w.val) : LocalState 5)ᴴ := by
      have hs := congrArg (fun M : LocalState 5 =>
        (U (P.tree.leafFeedback w.val) : LocalState 5)ᴴ * M) (scalar ⟨w,z⟩)
      have uu : (U (P.tree.leafFeedback w.val) : LocalState 5)ᴴ *
          (U (P.tree.leafFeedback w.val) : LocalState 5) = 1 :=
        (U (P.tree.leafFeedback w.val)).property.1
      simpa only [K,historyKraus,← Matrix.mul_assoc,uu,Matrix.one_mul,
        Matrix.mul_smul,Matrix.mul_one] using hs
    have row_injective (x : Fin 2 → ℂ) (hx : x ≠ 0) :
        Function.Injective (fun y : Fin 2 → ℂ => fun i : Fin 5 =>
          (∑ k, x k * source r i k) * (∑ k, y k * source r i k)) := by
      intro y z he
      have h0 := congrFun he 0
      have h1 := congrFun he 1
      have h2 := congrFun he 2
      simp only [source, Fin.sum_univ_two, Matrix.cons_val, Matrix.head_cons,
        Matrix.head_fin_const, mul_one, mul_zero, zero_add, add_zero] at h0 h1 h2
      have sr0 : (Real.sqrt (1+r^2) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 1+r^2))
      have rr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      have hm : x 0 * y 1 + x 1 * y 0 = x 0 * z 1 + x 1 * z 0 := by
        field_simp [sr0] at h2
        apply mul_left_cancel₀ rr0
        linear_combination h2 - h0 - (r : ℂ)^2*h1
      by_cases x0 : x 0 = 0
      · have x1 : x 1 ≠ 0 := by
          simpa [funext_iff, Fin.forall_fin_two, x0] using hx
        have hz1 := mul_left_cancel₀ x1 h1
        have hz0 : y 0 = z 0 := mul_left_cancel₀ x1 (by simpa [x0] using hm)
        funext k; fin_cases k <;> assumption
      · have hz0 := mul_left_cancel₀ x0 h0
        have hz1 : y 1 = z 1 := mul_left_cancel₀ x0 (by simpa [hz0] using hm)
        funext k; fin_cases k <;> assumption
    have record_separates (x y : Fin 2 → ℂ)
        (hz : ∀ i, (∑ k, x k * source r i k) * (∑ k, y k * source r i k) = 0) :
        x = 0 ∨ y = 0 := by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (row_injective x hx (by funext i; simpa using hz i))
    have nonzero_rows {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (hn : pairEffect F ≠ 0) :
        ∃ a : RowIndices F 0, ∃ b : RowIndices F 1, F.matrix 0 a ≠ 0 ∧ F.matrix 1 b ≠ 0 := by
      have local_nonzero (j : Fin 2) : F.matrix j ≠ 0 := by
        intro hz
        apply hn
        ext x z
        change (∏ a : Fin 2, inputGram (F.matrix a)
          (pairCoordinates x a) (pairCoordinates z a)) = 0
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          simp [Fin.prod_univ_two, inputGram, hz]
      obtain ⟨a,ha⟩ := Function.ne_iff.mp (local_nonzero 0)
      obtain ⟨b,hb⟩ := Function.ne_iff.mp (local_nonzero 1)
      exact ⟨a,b,ha,hb⟩
    have history_scalar (w : Accepted P accept) : ∃ c : ℝ, 0 ≤ c ∧
          (∀ X : LocalState 5, correctedHistory P r U w.val X = (c : ℂ) • X) ∧
          (∀ (F : Type) [Fintype F] [DecidableEq F] (X : ReferenceMatrix F),
            referenceCorrectedHistory P r U F w.val X = (c : ℂ) • X) := by
      let c : ℝ := ∑ z : Z w, Complex.normSq (K ⟨w,z⟩ 0 0)
      have system_scalar (X : LocalState 5) : correctedHistory P r U w.val X = (c : ℂ) • X := by
        rw [representation]
        calc
          _ = ∑ z : Z w, (Complex.normSq (K ⟨w,z⟩ 0 0) : ℂ) • X := by
            refine Finset.sum_congr rfl (fun z _ => ?_)
            change K ⟨w,z⟩ * X * (K ⟨w,z⟩)ᴴ = _
            rw [scalar ⟨w,z⟩]
            simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
              Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul]
            rw [Complex.normSq_eq_conj_mul_self]
            simp only [Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,Complex.star_def]
          _ = (c : ℂ) • X := by simp [c,Complex.ofReal_sum,Finset.sum_smul]
      refine ⟨c,Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _),system_scalar,?_⟩
      intro F _ _ X
      ext ⟨f,i⟩ ⟨g,j⟩
      have hb := congrFun (congrFun (reference_blocks F w.val X f g) i) j
      rw [system_scalar] at hb
      exact hb
    intro w
    refine ⟨history_scalar w,?_,?_⟩
    · intro hp0
      have rows (z : Z w) : rowAmplitude (leafFactors P w.val) r z = 0 := by
        have hz := zero_kraus hp0 ⟨w,z⟩
        have hd := uncorrected_scalar w z
        rw [hz] at hd
        have dd : diagonal (rowAmplitude (leafFactors P w.val) r z) = 0 := by simpa using hd
        funext i
        simpa using congrArg (fun M : LocalState 5 => M i i) dd
      by_contra hn
      obtain ⟨a,b,ha,hb⟩ := nonzero_rows (leafFactors P w.val) hn
      exact (not_or.mpr ⟨ha,hb⟩) (record_separates _ _ (fun i => congrFun (rows (a,b)) i))
    · intro nonzero
      let F := leafFactors P w.val
      obtain ⟨a,b,ha,hb⟩ := nonzero_rows F nonzero
      let gamma : Z w → ℂ := fun z => K ⟨w,z⟩ 0 0
      have gz : gamma (a,b) ≠ 0 := by
        intro h
        have hd := uncorrected_scalar w (a,b)
        change diagonal (rowAmplitude F r (a,b)) = gamma (a,b) • _ at hd
        rw [h,zero_smul] at hd
        have hz (i : Fin 5) : rowAmplitude F r (a,b) i = 0 := by
          simpa using congrArg (fun M : LocalState 5 => M i i) hd
        exact (not_or.mpr ⟨ha,hb⟩) (record_separates _ _ hz)
      let ratio : Z w → ℂ := fun z => gamma z / gamma (a,b)
      have proportional (z : Z w) (i : Fin 5) :
          rowAmplitude F r z i = ratio z * rowAmplitude F r (a,b) i := by
        have h1 := congrArg (fun M : LocalState 5 => M i i)
          (uncorrected_scalar w z)
        have h2 := congrArg (fun M : LocalState 5 => M i i)
          (uncorrected_scalar w (a,b))
        simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul] at h1 h2
        change rowAmplitude F r z i = gamma z * _ at h1
        change rowAmplitude F r (a,b) i = gamma (a,b) * _ at h2
        rw [h1,h2]
        dsimp [ratio]
        field_simp [gz]
      have rowB (z : RowIndices F 1) : F.matrix 1 z = ratio (a,z) • F.matrix 1 b := by
        apply row_injective (F.matrix 0 a) ha
        funext i
        have he := proportional (a,z) i
        dsimp only [rowAmplitude] at he ⊢
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
        rw [he]
        ring
      have rowA (z : RowIndices F 0) : F.matrix 0 z = ratio (z,b) • F.matrix 0 a := by
        apply row_injective (F.matrix 1 b) hb
        funext i
        have he := proportional (z,b) i
        dsimp only [rowAmplitude] at he
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
        rw [mul_comm (∑ k, F.matrix 1 b k * source r i k), he]
        ring
      have rank_local {R : Type} [Fintype R] (L : Matrix R (Fin 2) ℂ)
          (u : R) (hu : L u ≠ 0) (c : R → ℂ) (hc : ∀ z, L z = c z • L u) :
          (inputGram L).rank = 1 := by
        rw [inputGram, Matrix.rank_conjTranspose_mul_self, Matrix.rank_eq_finrank_span_row]
        have span : Submodule.span ℂ (Set.range L.row) = ℂ ∙ L u := by
          apply le_antisymm
          · refine Submodule.span_le.mpr ?_
            rintro _ ⟨z, rfl⟩
            rw [show L.row z = c z • L u from hc z]
            exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
          · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self u))
        rw [span]
        exact finrank_span_singleton hu
      have ra := rank_local (F.matrix 0) a ha (fun z => ratio (z,b)) rowA
      have rb := rank_local (F.matrix 1) b hb (fun z => ratio (a,z)) rowB
      have row_ket {R : Type} [Fintype R] (L : Matrix R (Fin 2) ℂ)
          (u : R) (hu : L u ≠ 0) (c : R → ℂ) (hc : ∀ z, L z = c z • L u) :
          ∃ x : Fin 2 → ℂ, UnitSpinor x ∧ inputGram L =
              ((trace (inputGram L)).re : ℂ) • vecMulVec x (star x) := by
        classical
        unfold Matrix at L
        let n : ℝ := ∑ k,Complex.normSq (L u k)
        have hn : 0 < n := by
          obtain ⟨k,hk⟩ := Function.ne_iff.mp hu
          exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k,Finset.mem_univ _,
            (Complex.normSq_pos).mpr hk⟩
        let s := Real.sqrt n
        have sp : 0 < s := Real.sqrt_pos.mpr hn
        have s0 : (s : ℂ) ≠ 0 := by exact_mod_cast sp.ne'
        have ss : s^2 = n := Real.sq_sqrt hn.le
        let x : Fin 2 → ℂ := fun k => star (L u k)/(s : ℂ)
        have hx : UnitSpinor x := by
          simp only [UnitSpinor,x,Complex.normSq_div,Complex.normSq_conj,
            Complex.star_def,Complex.normSq_ofReal]
          rw [← Finset.sum_div,← pow_two,ss]
          exact div_self hn.ne'
        let q : ℝ := ∑ z,Complex.normSq (c z)
        have lf : L = vecMulVec c (L u) := by
          ext z i
          exact congrFun (hc z) i
        have form : inputGram L = (q : ℂ) • vecMulVec (star (L u)) (L u) := by
          conv_lhs => rw [inputGram, lf, Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
          have coeff : star c ⬝ᵥ c = (q : ℂ) := by
            simp [q, dotProduct, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
          rw [coeff, Matrix.vecMulVec_smul]
        have tr : (trace (inputGram L)).re = q*n := by
          rw [form]
          simp [trace,Fin.sum_univ_two,n,Matrix.vecMulVec_apply,Matrix.smul_apply,
            Complex.normSq_apply,Complex.star_def,Complex.normSq_eq_conj_mul_self]
          ring
        refine ⟨x,hx,?_⟩
        rw [tr,form]
        ext i j
        simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,x,
          star_div₀,star_star,Complex.ofReal_mul,smul_eq_mul]
        have st : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal _
        rw [st]
        have ss' : (s : ℂ)^2 = (n : ℂ) := by exact_mod_cast ss
        field_simp [s0]
        rw [← ss']
      refine ⟨ra,rb,?_⟩
      intro hlo hhi
      obtain ⟨x,hx,gx⟩ := row_ket (F.matrix 0) a ha (fun z => ratio (z,b)) rowA
      obtain ⟨y,hy,gy⟩ := row_ket (F.matrix 1) b hb (fun z => ratio (a,z)) rowB
      have local_laws := (normalized_tree.2.2.1 F).1
      have trace_pos (j : Fin 2) (u : RowIndices F j) (hu : F.matrix j u ≠ 0) :
          0 < localTrace F j := by
        apply lt_of_le_of_ne (local_laws j).1
        intro ht
        have gram0 := (local_laws j).2.1.mp ht.symm
        exact hu (congrFun (Matrix.conjTranspose_mul_self_eq_zero.mp gram0) u)
      have ta := trace_pos 0 a ha
      have tb := trace_pos 1 b hb
      have tw : 0 < effectWeight F := mul_pos ta tb
      have px : rho (localBloch F 0) = vecMulVec x (star x) := by
        apply (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) (by exact_mod_cast ta.ne' :
          (localTrace F 0 : ℂ) ≠ 0))
        exact (local_laws 0).2.2.2.symm.trans gx
      have py : rho (localBloch F 1) = vecMulVec y (star y) := by
        apply (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) (by exact_mod_cast tb.ne' :
          (localTrace F 1 : ℂ) ≠ 0))
        exact (local_laws 1).2.2.2.symm.trans gy
      have pure (v : Bloch) (z : Fin 2 → ℂ) (hz : rho v = vecMulVec z (star z)) : ‖v‖ = 1 := by
        have hd : (rho v).det = 0 := by
          rw [hz]
          simp [Matrix.det_fin_two,Matrix.vecMulVec_apply]
          ring
        have he : (rho v).det.re = (1-‖v‖^2)/4 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [rho,blochMatrix,Matrix.det_fin_two,Fin.sum_univ_three]
          ring
        rw [hd] at he
        simp only [Complex.zero_re] at he
        nlinarith [norm_nonneg v]
      have qform : Q (localBloch F 0) (localBloch F 1) =
          vecMulVec (productVector x y) (star (productVector x y)) := by
        ext i j
        simp [Q,Matrix.kronecker,Matrix.kroneckerMap,px,py,productVector,Matrix.vecMulVec_apply]
        ring
      have qresponse (i : Fin 5) :
          matrixResponse r (localBloch F 0) (localBloch F 1) i = productResponse r x y i := by
        let v := productVector x y
        have hc : star (record r i) ⬝ᵥ (Q (localBloch F 0) (localBloch F 1) *ᵥ record r i) =
            (Complex.normSq (star v ⬝ᵥ record r i) : ℂ) := by
          rw [qform,Matrix.vecMulVec_mulVec,dotProduct_smul,star_dotProduct]
          rw [Complex.normSq_eq_conj_mul_self]
          simp only [← Complex.star_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
            star_star]
        exact congrArg Complex.re hc
      obtain ⟨c,hc,cs,cr⟩ := history_scalar w
      have coefficient (i : Fin 5) :
          matrixResponse r (localBloch F 0) (localBloch F 1) i * effectWeight F = c := by
        let V := (U (P.tree.leafFeedback w.val) : LocalState 5)
        have ht := congrArg Matrix.trace (cs (Matrix.single i i 1))
        change trace (V * historyMap P r w.val (Matrix.single i i 1) * Vᴴ) = _ at ht
        have uu : Vᴴ * V = 1 := (U (P.tree.leafFeedback w.val)).property.1
        rw [trace_mul_cycle, uu, one_mul] at ht
        simp [trace,source_map,Matrix.single,Matrix.smul_apply] at ht
        have he := (normalized_tree.2.2.1 F).2.1
        change leafEffect P w.val = (effectWeight F : ℂ) •
          Q (localBloch F 0) (localBloch F 1) at he
        rw [he,Matrix.smul_mulVec,dotProduct_smul] at ht
        have hh := congrArg Complex.re ht
        simpa [matrixResponse,Complex.mul_re,mul_comm] using hh
      have flat : FlatProduct r x y := by
        intro i
        apply mul_right_cancel₀ tw.ne'
        rw [← qresponse i,← qresponse 0]
        exact (coefficient i).trans (coefficient 0).symm
      have geometry := (all_r_flat_geometry r hr hlo hhi).2.2.1 x y hx hy flat
      have membership : (localBloch F 0,localBloch F 1) ∈ K_s r :=
        ⟨pure _ _ px,pure _ _ py,fun i => (qresponse i).trans (geometry.1 i)⟩
      have cw : c = effectWeight F * h r := by
        rw [← coefficient 0,qresponse 0,geometry.1 0,mul_comm]
      refine ⟨tw,membership,?_⟩
      intro R _ _ X
      rw [← cw]
      exact cr R X

  have probability_bound : p ≤ 1 := by
    classical
    let e : Coordinates InputDimensions := pairCoordinates (0,0)
    let t : P.tree.Leaves → ℝ := fun w => ((leafFactors P w).inputEffect e e).re
    have tn (w : P.tree.Leaves) : 0 ≤ t w :=
      (Complex.nonneg_iff.mp ((input_effect_tree.2.2.1 (leafFactors P w)).1.diag_nonneg)).1
    have total : (∑ w : P.tree.Leaves,t w) = 1 := by
      have hh := input_effect_tree.2.2.2.2.1 P.tree (P.ancillas.rootFactors InputDimensions)
      rw [input_effect_tree.2.1] at hh
      have he := congrArg (fun M => (M e e).re) hh
      simpa only [Tree.descendantEffect,Matrix.sum_apply,Complex.re_sum,Matrix.one_apply_eq,
        Complex.one_re,t,leafFactors] using he
    have q0 : record r 0 = Pi.single (0,0) 1 := by
      ext ⟨i,j⟩
      fin_cases i <;> fin_cases j <;> norm_num [record, source, Pi.single_apply]
    have trhistory (w : P.tree.Leaves) :
        trace (correctedHistory P r U w (Matrix.single 0 0 1)) = (t w : ℂ) := by
      rw [correctedHistory, trace_mul_cycle]
      have hu : (U (P.tree.leafFeedback w) : LocalState 5)ᴴ *
          (U (P.tree.leafFeedback w) : LocalState 5) = 1 :=
        (U (P.tree.leafFeedback w)).property.1
      rw [hu, one_mul]
      simp [trace, source_map, Matrix.single, q0, Matrix.mulVec, dotProduct, Pi.single_apply]
      have him := (Complex.nonneg_iff.mp
        ((input_effect_tree.2.2.1 (leafFactors P w)).1.diag_nonneg (i := e))).2
      exact Complex.ext rfl him.symm
    have accepted_total : p = ∑ w : Accepted P accept,t w.val := by
      have he := congrArg (fun M => (trace M).re) (recovery (Matrix.single 0 0 1))
      rw [acceptedMap,Matrix.trace_sum] at he
      simp only [Complex.re_sum,trhistory,Complex.ofReal_re] at he
      simpa using he.symm
    have split := Fintype.sum_subtype_add_sum_subtype (fun w : P.tree.Leaves =>
      accept (P.tree.leafFeedback w)) t
    have failed_nonneg : 0 ≤ ∑ w : {w : P.tree.Leaves // ¬ accept (P.tree.leafFeedback w)},t w.val :=
      Finset.sum_nonneg (fun w _ => tn w.val)
    change (∑ w : Accepted P accept,t w.val) + _ = _ at split
    rw [← accepted_total,total] at split
    linarith
  refine ⟨probability_bound,input_effect_tree,normalized_tree,reference_blocks,reference_recovery,
    zero_reference,?_,support_result⟩
  intro hlo hhi
  classical
  have leaf_action (w : Accepted P accept) (F : Type) [Fintype F] [DecidableEq F]
      (X : ReferenceMatrix F) :
      referenceCorrectedHistory P r U F w.val X =
        ((effectWeight (leafFactors P w.val) * h r : ℝ) : ℂ) • X := by
    by_cases hz : leafEffect P w.val = 0
    · have wt : effectWeight (leafFactors P w.val) = 0 := by
        have ht := (normalized_tree.2.2.1 (leafFactors P w.val)).2.2
        change (trace (leafEffect P w.val)).re = effectWeight (leafFactors P w.val) at ht
        rw [hz] at ht
        simpa using ht.symm
      rw [zero_reference w.val hz]
      simp [wt]
    · exact (((support_result w).2.2 hz).2.2 hlo hhi).2.2 F X
  have total_action : referenceAcceptedMap P r accept U Unit 1 =
      ((h r * ∑ w : Accepted P accept,effectWeight (leafFactors P w.val) : ℝ) : ℂ) •
        (1 : ReferenceMatrix Unit) := by
    simp only [referenceAcceptedMap, leaf_action, ← Finset.sum_smul]
    congr 1
    simp [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, mul_comm]
  have hpRef := (reference_recovery p).mp recovery Unit 1
  have heq := congrArg (fun M : ReferenceMatrix Unit => M ((),0) ((),0))
    (hpRef.symm.trans total_action)
  apply Complex.ofReal_injective
  simpa [ReferenceMatrix] using heq

end D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery

#check D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity
#print axioms D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity
