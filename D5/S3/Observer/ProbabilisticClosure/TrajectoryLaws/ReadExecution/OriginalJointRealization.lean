/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite joint operations admit common fresh tables on the actual source product. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw

/-! Original joint stochastic operations and their common fresh innovation realization. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization
open OriginalObserverNormalization ActualRenewalPrefixLaw

variable {C : Type*}

instance actionFinite [Finite C] (e : C → Option Bool) : Finite (Action e) := by
  let encode : Action e → C × Option Bool := fun a => match a with
    | .read c => (c.val, none)
    | .emit c d _ => (c, some d)
  apply Finite.of_injective encode
  intro a b h
  cases a <;> cases b <;> simp_all [encode]
  exact Subtype.ext h

instance actionMeasurableSpace (e : C → Option Bool) : MeasurableSpace (Action e) := ⊤
instance actionMeasurableSingletonClass (e : C → Option Bool) :
    MeasurableSingletonClass (Action e) := ⟨fun _ => trivial⟩

/-- Original stochastic primitives are specified before any innovation tape.
    The pair retains the correlation of the update and ensuing action choice.
    Both configuration values belong to the complete original carrier. -/
structure Stochastic (C : Type*) where
  emission : C → Option Bool
  label : Bool → C
  label_emission : ∀ d, emission (label d) = some d
  initialLaw : PMF (C × Action emission)
  operation : C → Bool → PMF (C × Action emission)

namespace Stochastic
variable (O : Stochastic C)

abbrev Outcome := C × Action O.emission
abbrev Innovation := C × Bool → O.Outcome

/-- This random table is fresh at each paid read. Only its selected entry is
    evaluated; it is not part of the retained configuration. -/
def machine : Machine C O.Outcome O.Innovation where
  emission := O.emission
  label := O.label
  label_emission := O.label_emission
  prepare := Prod.fst
  initialAction := fun _ seed => seed.2
  update := fun c b r => (r (c,b)).1
  afterRead := fun c b r _ => (r (c,b)).2

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

def seedLaw : Measure O.Outcome := O.initialLaw.toMeasure
def innovationLaw : Measure O.Innovation :=
  Measure.pi fun p : C × Bool => (O.operation p.1 p.2).toMeasure

instance : IsProbabilityMeasure O.seedLaw := by unfold seedLaw; infer_instance
instance : IsProbabilityMeasure O.innovationLaw := by unfold innovationLaw; infer_instance

private theorem table_entry (c : C) (b : Bool) :
    O.innovationLaw.map (fun r => r (c,b)) = (O.operation c b).toMeasure :=
  (measurePreserving_eval (fun p : C × Bool => (O.operation p.1 p.2).toMeasure) (c,b)).map_eq

/-- The original paid-operation semantics, with no reference to a random table.
    An emitted action holds without another read. -/
def nextLaw (e : O.Outcome) (b : Bool) : PMF O.Outcome :=
  match e.2 with
  | .read c => O.operation c.val b
  | .emit _ _ _ => PMF.pure e

/-- The complete finite original joint execution law. Each vector records the
    intermediate configuration and its correlated ensuing action. Emission
    is held analytically; this does not charge any additional read. -/
def executionLaw (source : ℕ → Bool) : (n : ℕ) → PMF (Fin (n + 1) → O.Outcome)
  | 0 => O.initialLaw.map (fun e _ => e)
  | n + 1 => (O.executionLaw source n).bind fun x =>
      (O.nextLaw (x (Fin.last n)) (source n)).map (Fin.snoc x)

def advance (e : O.Outcome) (b : Bool) (r : O.Innovation) : O.Outcome :=
  match e.2 with
  | .read c => r (c.val,b)
  | .emit _ _ _ => e

def develop (source : ℕ → Bool) (seed : O.Outcome) :
    (n : ℕ) → (Fin n → O.Innovation) → (Fin (n + 1) → O.Outcome)
  | 0, _ => fun _ => seed
  | n + 1, r =>
    let x := O.develop source seed n (fun j => r j.castSucc)
    Fin.snoc x (O.advance (x (Fin.last n)) (source n) (r (Fin.last n)))

private theorem advance_law (e : O.Outcome) (b : Bool) :
    O.innovationLaw.map (O.advance e b) = (O.nextLaw e b).toMeasure := by
  cases he : e.2 with
  | read c => simpa [advance, nextLaw, he] using O.table_entry c.val b
  | emit c d hd => simp [advance, nextLaw, he, PMF.toMeasure_pure]

private theorem extend_law {n : ℕ} (ν : PMF (Fin (n + 1) → O.Outcome)) (b : Bool) :
    (ν.toMeasure.prod O.innovationLaw).map
      (fun p => Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) b p.2)) =
      (ν.bind fun x => (O.nextLaw (x (Fin.last n)) b).map (Fin.snoc x)).toMeasure := by
  ext B hB
  have hm : Measurable (fun p : (Fin (n + 1) → O.Outcome) × O.Innovation =>
      Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) b p.2)) := measurable_of_countable _
  rw [Measure.map_apply hm hB, Measure.prod_apply (hm hB), lintegral_countable',
    PMF.toMeasure_bind_apply _ _ hB]
  apply tsum_congr
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) hB]
  congr 1
  have hrow := congrArg (fun μ : Measure O.Outcome => μ ((Fin.snoc x) ⁻¹' B))
    (O.advance_law (x (Fin.last n)) b)
  rw [Measure.map_apply (measurable_of_countable _)
    (hB.preimage (measurable_of_countable _))] at hrow
  exact hrow

/-- Fresh table evaluation preserves the whole finite original joint law,
    including all initial, updated, read-ready and emitted configurations. -/
theorem finite_execution_law (source : ℕ → Bool) (n : ℕ) :
    (O.seedLaw.prod (Measure.pi fun _ : Fin n => O.innovationLaw)).map
      (fun p => O.develop source p.1 n p.2) = (O.executionLaw source n).toMeasure := by
  induction n with
  | zero =>
    have he : (fun p : O.Outcome × (Fin 0 → O.Innovation) =>
        O.develop source p.1 0 p.2) = (fun e _ => e) ∘ Prod.fst := rfl
    rw [he, ← Measure.map_map (measurable_of_countable _) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, executionLaw,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
    rfl
  | succ n ih =>
    let split : O.Outcome × (Fin (n + 1) → O.Innovation) →
        (O.Outcome × (Fin n → O.Innovation)) × O.Innovation := fun p =>
      ((p.1, fun j => p.2 j.castSucc), p.2 (Fin.last n))
    have hsplit : (O.seedLaw.prod (Measure.pi fun _ : Fin (n + 1) => O.innovationLaw)).map
        split = (O.seedLaw.prod (Measure.pi fun _ : Fin n => O.innovationLaw)).prod
          O.innovationLaw := by
      have he : split = MeasurableEquiv.prodAssoc.symm ∘
          Prod.map id (fun r : Fin (n + 1) → O.Innovation =>
            (fun j : Fin n => r j.castSucc, r (Fin.last n))) := rfl
      rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
        ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
        split_last O.innovationLaw n, ← Measure.prodAssoc_prod,
        MeasurableEquiv.map_symm_map]
    let step : (Fin (n + 1) → O.Outcome) × O.Innovation →
        (Fin (n + 2) → O.Outcome) := fun p =>
      Fin.snoc p.1 (O.advance (p.1 (Fin.last n)) (source n) p.2)
    have he : (fun p => O.develop source p.1 (n + 1) p.2) =
        step ∘ Prod.map (fun p => O.develop source p.1 n p.2) id ∘ split := rfl
    rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), hsplit,
      ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      ← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,
      ih, Measure.map_id]
    exact O.extend_law (O.executionLaw source n) (source n)

end Stochastic

section Product
variable {I S R : Type*} [MeasurableSpace I] [MeasurableSpace S] [MeasurableSpace R]
    (κ : Measure I) (ρ : Measure R) [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ]

private theorem finite_coordinates (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => fun j : Fin n => z j.val) = Measure.pi (fun _ : Fin n => ρ) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

private theorem separated_blocks (l r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) =
      (Measure.pi fun _ : Fin l => ρ).prod (Measure.pi fun _ : Fin r => ρ) := by
  apply (Measure.prod_eq fun D B hD hB => ?_).symm
  rw [Measure.map_apply (by fun_prop) (hD.prod hB)]
  have he : (fun z : ℕ → R =>
      (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) ⁻¹' (D ×ˢ B) =
      (fun z => fun j : Fin l => z j.val) ⁻¹' D ∩
        FreshServiceRestart.shift l ⁻¹'
          ((fun z : ℕ → R => fun j : Fin r => z j.val) ⁻¹' B) := by
    ext z
    simp [FreshServiceRestart.shift, Nat.add_comm]
  rw [he, FreshServiceRestart.prefix_suffix_independent ρ l D hD _
    (hB.preimage (by fun_prop)),
    ← Measure.map_apply (by fun_prop) hD, finite_coordinates,
    ← Measure.map_apply (by fun_prop) hB, finite_coordinates]

private theorem seed_blocks (initial : I → S) (h : Measurable initial) (l r : ℕ) :
    (κ.prod (Measure.infinitePi (fun _ : ℕ => ρ))).map
      (fun p => ((initial p.1, fun j : Fin l => p.2 j.val),
        fun j : Fin r => p.2 (l + j.val))) =
      ((κ.map initial).prod (Measure.pi fun _ : Fin l => ρ)).prod
        (Measure.pi fun _ : Fin r => ρ) := by
  have he : (fun p : I × (ℕ → R) =>
      ((initial p.1, fun j : Fin l => p.2 j.val), fun j : Fin r => p.2 (l + j.val))) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map initial
        (fun z : ℕ → R => (fun j : Fin l => z j.val,
          fun j : Fin r => z (l + j.val))) := rfl
  rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
    ← Measure.map_prod_map _ _ h (by fun_prop), separated_blocks,
    ← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]

/-- The source coordinates and all observer randomness inhabit one product.
    The initial map is chosen independently of the source label. -/
def productLaw (w f : PMF ℕ) : Measure ((ℕ × (ℕ → ℕ)) × (I × (ℕ → R))) :=
  (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).prod
    (κ.prod (Measure.infinitePi fun _ : ℕ => ρ))

private theorem product_primitive (initial : I → S) (h : Measurable initial)
    (w f : PMF ℕ) :
    Primitive (productLaw κ ρ w f) (fun ω => initial ω.2.1)
      (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2.2) (κ.map initial) w f ρ := by
  intro n a l r D B hD hB
  let G : Set (ℕ × (ℕ → ℕ)) :=
    {g | g.1 = a.1 ∧ ∀ j : Fin n, g.2 j.val = a.2 j}
  let E : Set (I × (ℕ → R)) :=
    (fun p => ((initial p.1, fun j : Fin l => p.2 j.val),
      fun j : Fin r => p.2 (l + j.val))) ⁻¹' (D ×ˢ B)
  have he : sourceSlice (fun ω : (ℕ × (ℕ → ℕ)) × (I × (ℕ → R)) => ω.1.1)
      (fun ω => ω.1.2) n a ∩
      rawPrefix (fun ω => initial ω.2.1) (fun ω => ω.2.2) l ⁻¹' D ∩
      rawBlock (fun ω => ω.2.2) l r ⁻¹' B = G ×ˢ E := by
    ext ω
    change (((ω.1.1 = a.1 ∧ ∀ j : Fin n, ω.1.2 j.val = a.2 j) ∧
      (initial ω.2.1, fun j : Fin l => ω.2.2 j.val) ∈ D) ∧
      (fun j : Fin r => ω.2.2 (l + j.val)) ∈ B) ↔ _
    simp only [G, E, Set.mem_prod, Set.mem_setOf_eq, Set.mem_preimage]
    tauto
  rw [he, productLaw, Measure.prod_prod]
  have hG : (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)) G =
      w a.1 * ∏ j, f (a.2 j) := by
    have hGset : G = {a.1} ×ˢ
        ((fun z : ℕ → ℕ => fun j : Fin n => z j.val) ⁻¹' {a.2}) := by
      ext g
      simp [G, funext_iff]
    rw [hGset, Measure.prod_prod,
      ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      finite_coordinates f.toMeasure,
      Measure.pi_singleton]
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hE : (κ.prod (Measure.infinitePi fun _ : ℕ => ρ)) E =
      ((κ.map initial).prod (Measure.pi fun _ : Fin l => ρ)) D *
        (Measure.pi fun _ : Fin r => ρ) B := by
    dsimp only [E]
    rw [← Measure.map_apply (by fun_prop) (hD.prod hB), seed_blocks κ ρ initial h,
      Measure.prod_prod]
  simp only [hG, hE, mul_assoc]

end Product
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization
