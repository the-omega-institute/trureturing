/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables
   mirror-E: none(waiver:symbolic-execution-and-measure)
   anchors: []
   utility: none
   digest: Local scheduled replay extracts one whole table from actual executions. -/

import D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
import D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
import Mathlib.Computability.StateTransition
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables

open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

universe u v

/-- The chronological replies, including the first false reply in stopped mode. -/
def view {A : Type*} (stop : Bool) : List A → (A → Bool) → List Bool
  | [], _ => []
  | i :: rest, q => q i :: (if stop && !q i then [] else view stop rest q)

/-- Every read appends one actual request; silent updates append nothing. -/
def step {C : Type u} (prog : C → Instruction C ℕ Bool) (q : ℕ → Bool)
    (z : C × List (ℕ × Bool)) : Option (C × List (ℕ × Bool)) :=
  match prog z.1 with
  | .read i k => some (k (q i), z.2 ++ [(i, q i)])
  | .update c => some (c, z.2)
  | .halt => none

/-- Local schedule discipline at reachable reads. In stopped mode all earlier
replies must be true. This condition contains no terminal-map factorization. -/
def Disciplined {C : Type u} (stop : Bool) (xs : List ℕ)
    (prog : C → Instruction C ℕ Bool) (initial : C) (q : ℕ → Bool) : Prop :=
  ∀ z, StateTransition.Reaches (step prog q) (initial, []) z →
    ∀ i k, prog z.1 = .read i k →
      (∃ tail, xs = z.2.map Prod.fst ++ i :: tail) ∧
      (stop = true → ∀ e ∈ z.2, e.2 = true)

private theorem view_at_next (stop : Bool) (before after : List ℕ) (i : ℕ)
    (q r : ℕ → Bool) (positive : stop = true → ∀ j ∈ before, q j = true)
    (same : view stop (before ++ i :: after) q = view stop (before ++ i :: after) r) :
    q i = r i := by
  induction before with
  | nil => exact (List.cons.inj same).1
  | cons j before ih =>
      have head : q j = r j := (List.cons.inj same).1
      have tails := (List.cons.inj same).2
      have next : view stop (before ++ i :: after) q =
          view stop (before ++ i :: after) r := by
        cases hs : stop with
        | false => simpa [view, hs] using tails
        | true =>
          have hq := positive hs j (by simp)
          have hr : r j = true := head.symm.trans hq
          simpa [view, hs, hq, hr] using tails
      exact ih (fun hs j hj => positive hs j (by simp [hj])) next

private theorem replay {C : Type u} (stop : Bool) (xs : List ℕ)
    (prog : C → Instruction C ℕ Bool) (initial : C) (q r : ℕ → Bool)
    (discipline : Disciplined stop xs prog initial q)
    (same : view stop xs q = view stop xs r)
    {last : C × List (ℕ × Bool)}
    (terminated : last ∈ StateTransition.eval (step prog q) (initial, [])) :
    last ∈ StateTransition.eval (step prog r) (initial, []) := by
  let rel := fun a b : C × List (ℕ × Bool) =>
    a = b ∧ StateTransition.Reaches (step prog q) (initial, []) a ∧
      ∀ e ∈ a.2, e.2 = q e.1
  have respects : StateTransition.Respects (step prog q) (step prog r) rel := by
    intro a b related
    obtain ⟨rfl, reached, consistent⟩ := related
    cases hp : prog a.1 with
    | halt => simp [step, hp]
    | update c =>
        simp only [step, hp]
        refine ⟨(c, a.2), ⟨rfl, reached.tail ?_, consistent⟩, ?_⟩
        · simp [step, hp]
        · exact Relation.TransGen.single (by simp [step, hp])
    | read i k =>
        obtain ⟨⟨tail, schedule⟩, positive⟩ := discipline a reached i k hp
        have agree : q i = r i := by
          apply view_at_next stop (a.2.map Prod.fst) tail i q r
          · intro hs j hj
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
            exact (consistent e he).symm.trans (positive hs e he)
          · simpa only [← schedule] using same
        simp only [step, hp]
        refine ⟨(k (q i), a.2 ++ [(i, q i)]),
          ⟨rfl, reached.tail ?_, ?_⟩, ?_⟩
        · simp [step, hp]
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact consistent e he
          · have eq : e = (i, q i) := by simpa using he
            subst e
            rfl
        · exact Relation.TransGen.single (by simp [step, hp, ← agree])
  obtain ⟨last', related, ended⟩ := StateTransition.tr_eval respects
    (a₁ := (initial, [])) (a₂ := (initial, []))
    ⟨rfl, Relation.ReflTransGen.refl, by simp⟩ terminated
  simpa only [← related.1] using ended

/-- Low indices retain their original numerical addresses, order and repeats. -/
def lowSchedule (L : ℕ) (xs : List ℕ) : List ℕ := xs.filter (fun i => i < L)

def lowReply {L : ℕ} (b : Fin L → Bool) (i : ℕ) : Bool :=
  if h : i < L then b ⟨i, h⟩ else false

theorem view_congr {A : Type*} (stop : Bool) (xs : List A) (q r : A → Bool)
    (same : ∀ i ∈ xs, q i = r i) : view stop xs q = view stop xs r := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp only [view, same i (by simp)]
      rw [ih (fun j hj => same j (by simp [hj]))]

private theorem view_filter (stop : Bool) (L : ℕ) (xs : List ℕ) (q r : ℕ → Bool)
    (high : ∀ i ∈ xs, ¬ i < L → q i = false ∧ r i = false)
    (same : view stop (lowSchedule L xs) q = view stop (lowSchedule L xs) r) :
    view stop xs q = view stop xs r := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases low : i < L
      · have lowcons : lowSchedule L (i :: xs) = i :: lowSchedule L xs := by
          simp [lowSchedule, low]
        rw [lowcons] at same
        have head : q i = r i := (List.cons.inj same).1
        have tails := (List.cons.inj same).2
        by_cases stopped : (stop && !q i) = true
        · simp [view, ← head, stopped]
        · have next : view stop (lowSchedule L xs) q =
              view stop (lowSchedule L xs) r := by
            simpa only [← head, if_neg stopped] using tails
          simp only [view, ← head, if_neg stopped]
          rw [ih (fun j hj => high j (by simp [hj])) next]
      · have hz := high i (by simp) low
        have next := ih (fun j hj => high j (by simp [hj]))
          (by simpa [lowSchedule, low] using same)
        cases stop <;> simp [view, hz.1, hz.2, next]

/-- The complete finite catalog, as output functions with a representing low
schedule. Labels are unrestricted. N permits repeats and reversal; O is increasing. -/
def InCatalog (stop : Bool) (L : ℕ) (f : (Fin L → Bool) → Fin (L + 1)) : Prop :=
  ∃ xs : List ℕ, xs.length ≤ 2 ∧ (∀ i ∈ xs, i < L) ∧
    (stop = true → xs.Pairwise (· < ·)) ∧
    ∀ b c, view stop xs (lowReply b) = view stop xs (lowReply c) → f b = f c

/-- One gate for the entire table; outside it every word has base label zero. -/
def witnessTable {S Θ : Type*} {L : ℕ} (D : Set S)
    (rho : Θ → Fin (L + 1)) (phi : (Fin L → Bool) → S → Θ)
    (s : S) (b : Fin L → Bool) : Fin (L + 1) :=
  by classical exact if s ∈ D then rho (phi b s) else 0

/-- Whole-table class extraction uses only local reachable schedule discipline
and finitely terminating actual witnesses. No global response equality is assumed. -/
private theorem actual_witness_table_class {S Θ : Type*} {C : Type u} (L m : ℕ)
    (stop : Bool) (schedule : S → List ℕ)
    (prog : S → C → Instruction C ℕ Bool) (initial : S → C)
    (q : (Fin L → Bool) → ℕ → Bool) (phi : (Fin L → Bool) → S → Θ)
    (rho : Θ → Fin (L + 1)) (D : Set S)
    (low : ∀ b (i : Fin L), q b i = b i)
    (high : ∀ b i, L ≤ i → i < m → q b i = false)
    (bounded : ∀ s ∈ D, (schedule s).length ≤ 2 ∧
      (∀ i ∈ schedule s, i < m) ∧
      (stop = true → (schedule s).Pairwise (· < ·)))
    (discipline : ∀ b s, Disciplined stop (schedule s) (prog s) (initial s) (q b))
    (terminal : ∀ b s, s ∈ D → ∃ last : C × List (ℕ × Bool),
      last ∈ StateTransition.eval (step (prog s) (q b)) (initial s, []))
    (readout : C → Θ)
    (output : ∀ b s last, s ∈ D →
      last ∈ StateTransition.eval (step (prog s) (q b)) (initial s, []) →
      readout last.1 = phi b s) :
    ∀ s, InCatalog stop L (witnessTable D rho phi s) := by
  intro s
  by_cases good : s ∈ D
  · obtain ⟨length, addresses, increasing⟩ := bounded s good
    refine ⟨lowSchedule L (schedule s), (List.length_filter_le ..).trans length,
      ?_, (fun hs => (increasing hs).filter _), ?_⟩
    · intro i hi
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    · intro b c same
      have loweq (b) : view stop (lowSchedule L (schedule s)) (q b) =
          view stop (lowSchedule L (schedule s)) (lowReply b) := by
        apply view_congr
        intro i hi
        have hi' : i < L := of_decide_eq_true (List.mem_filter.mp hi).2
        simpa [lowReply, hi'] using low b ⟨i, hi'⟩
      have full : view stop (schedule s) (q b) = view stop (schedule s) (q c) := by
        apply view_filter stop L
        · intro i hi hL
          exact ⟨high b i (by omega) (addresses i hi), high c i (by omega) (addresses i hi)⟩
        · exact (loweq b).trans (same.trans (loweq c).symm)
      obtain ⟨last, ended⟩ := terminal b s good
      have ended' := replay stop (schedule s) (prog s) (initial s) (q b) (q c)
        (discipline b s) full ended
      have eqout := (output b s last good ended).symm.trans (output c s last good ended')
      simp only [witnessTable, if_pos good, eqout]
  · refine ⟨[], by simp, by simp, by simp, ?_⟩
    intro b c _
    simp [witnessTable, good]

/-- Functions in the complete catalog; a representative schedule is supplied
by its defining existential and may be chosen once for each of these finitely many functions. -/
abbrev Catalog (stop : Bool) (L : ℕ) :=
  {f : (Fin L → Bool) → Fin (L + 1) // InCatalog stop L f}

private theorem gate_tv {S J : Type*} [MeasurableSpace S] [MeasurableSpace J]
    (mu : Measure S) (D : Set S) (f g : S → J)
    (hf : Measurable f) (hg : Measurable g) (agree : ∀ s ∈ D, f s = g s) :
    measurableTotalVariation (mu.map f) (mu.map g) ≤ mu (Dᶜ) := by
  unfold measurableTotalVariation
  refine iSup_le fun E => ?_
  rw [Measure.map_apply hf E.2, Measure.map_apply hg E.2]
  have compare (a b : S → J) (eqon : ∀ s ∈ D, a s = b s) :
      mu (a ⁻¹' E.1) ≤ mu (b ⁻¹' E.1) + mu (Dᶜ) := by
    apply (measure_mono (show a ⁻¹' E.1 ⊆ b ⁻¹' E.1 ∪ Dᶜ from ?_)).trans
      (measure_union_le _ _)
    intro s hs
    by_cases hd : s ∈ D
    · exact Or.inl (by
        change a s ∈ E.1 at hs
        change b s ∈ E.1
        rwa [← eqon s hd])
    · exact Or.inr hd
  exact max_le (tsub_le_iff_right.mpr (by simpa [add_comm] using compare f g agree))
    (tsub_le_iff_right.mpr (by
      simpa [add_comm] using compare g f (fun s hs => (agree s hs).symm)))

/-- Actual witness executions with one common gate yield one probability vector
on the entire restricted catalog and a simultaneous row error bound.
The bound uses the single schedule event, without a factor for the number of words. -/
private theorem actual_witness_tables {S Θ : Type*} [MeasurableSpace S] [MeasurableSpace Θ]
    {C : Type u} (mu : Measure S) [IsProbabilityMeasure mu] (L m : ℕ)
    (stop : Bool) (schedule : S → List ℕ)
    (prog : S → C → Instruction C ℕ Bool) (initial : S → C)
    (q : (Fin L → Bool) → ℕ → Bool) (phi : (Fin L → Bool) → S → Θ)
    (rho : Θ → Fin (L + 1)) (H : Set S) (T : (Fin L → Bool) → Set S)
    (readout : C → Θ) (target : (Fin L → Bool) → Measure Θ) (eps : ENNReal)
    (hH : MeasurableSet H) (hT : ∀ b, MeasurableSet (T b))
    (conull : ∀ b, ∀ᵐ s ∂mu, s ∈ T b)
    (hphi : ∀ b, Measurable (phi b)) (hrho : Measurable rho)
    (cap : ∀ b, measurableTotalVariation (mu.map (phi b)) (target b) ≤ eps)
    (low : ∀ b (i : Fin L), q b i = b i)
    (high : ∀ b i, L ≤ i → i < m → q b i = false)
    (bounded : ∀ s ∈ H, (schedule s).length ≤ 2 ∧
      (∀ i ∈ schedule s, i < m) ∧
      (stop = true → (schedule s).Pairwise (· < ·)))
    (discipline : ∀ b s, Disciplined stop (schedule s) (prog s) (initial s) (q b))
    (terminal : ∀ b s, s ∈ T b → ∃ last : C × List (ℕ × Bool),
      last ∈ StateTransition.eval (step (prog s) (q b)) (initial s, []))
    (output : ∀ b s last, s ∈ T b →
      last ∈ StateTransition.eval (step (prog s) (q b)) (initial s, []) →
      readout last.1 = phi b s) :
    let D := H ∩ {s | ∀ b, s ∈ T b}
    ∃ (F : S → Catalog stop L) (w : PMF (Catalog stop L)),
      Measurable F ∧ w.toMeasure = mu.map F ∧
      (∀ s, (F s).val = witnessTable D rho phi s) ∧
      mu (Dᶜ) = mu (Hᶜ) ∧
      ∀ b, measurableTotalVariation
        (w.toMeasure.map (fun f => f.val b)) ((target b).map rho) ≤ eps + mu (Hᶜ) := by
  classical
  intro D
  have intereq : {s | ∀ b, s ∈ T b} = ⋂ b, T b := by ext s; simp
  have hD : MeasurableSet D := hH.inter (by
    rw [intereq]
    exact MeasurableSet.iInter hT)
  have hclass : ∀ s, InCatalog stop L (witnessTable D rho phi s) :=
    actual_witness_table_class L m stop schedule prog initial q phi rho D low high
      (fun s hs => bounded s hs.1) discipline
      (fun b s hs => terminal b s (hs.2 b)) readout
      (fun b s last hs => output b s last (hs.2 b))
  let F : S → Catalog stop L := fun s => ⟨witnessTable D rho phi s, hclass s⟩
  have hcoord (b) : Measurable (fun s => witnessTable D rho phi s b) := by
    exact Measurable.ite hD (hrho.comp (hphi b)) measurable_const
  have hF : Measurable F := (Measurable.of_eval hcoord).subtype_mk
  have : IsProbabilityMeasure (mu.map F) := inferInstance
  let w := (mu.map F).toPMF
  have mass : mu (Dᶜ) = mu (Hᶜ) := by
    have same : mu D = mu H := by
      change mu (H ∩ {s | ∀ b, s ∈ T b}) = mu H
      rw [Set.inter_comm]
      exact Measure.measure_inter_eq_of_ae (ae_all_iff.mpr conull)
    rw [measure_compl hD (measure_ne_top _ _),
      measure_compl hH (measure_ne_top _ _), same]
  refine ⟨F, w, hF, Measure.toPMF_toMeasure _, (fun _ => rfl), mass, ?_⟩
  intro b
  have evalmeas : Measurable (fun f : Catalog stop L => f.val b) :=
    (measurable_pi_apply b).comp measurable_subtype_coe
  have law : w.toMeasure.map (fun f => f.val b) =
      mu.map (fun s => witnessTable D rho phi s b) := by
    rw [Measure.toPMF_toMeasure, Measure.map_map evalmeas hF]
    rfl
  rw [law]
  calc
    measurableTotalVariation (mu.map (fun s => witnessTable D rho phi s b))
        ((target b).map rho) ≤
      measurableTotalVariation (mu.map (fun s => witnessTable D rho phi s b))
        (mu.map (rho ∘ phi b)) +
      measurableTotalVariation (mu.map (rho ∘ phi b)) ((target b).map rho) :=
        measurable_total_variation_triangle _ _ _
    _ ≤ mu (Dᶜ) + eps := add_le_add
      (gate_tv mu D _ _ (hcoord b) (hrho.comp (hphi b))
        (by intro s hs; simp [witnessTable, hs]))
      (by rw [← Measure.map_map hrho (hphi b)]
          exact (measurable_total_variation_map_le _ _ rho hrho).trans (cap b))
    _ = eps + mu (Hᶜ) := by rw [mass, add_comm]


/-- The whole preselected schedule lies strictly below the cutoff. -/
def scheduleGate {S : Type*} (schedule : S → List ℕ) (m : ℕ) : Set S :=
  {s | ∀ i ∈ schedule s, i < m}

/-- Both restricted original classes have a common-catalog approximation with
vanishing error slack, using actual witness executions and no transition cutoff. -/
theorem scheduled_witness_approximation {S Θ : Type*}
    [MeasurableSpace S] [MeasurableSpace Θ] {C : Type u}
    (mu : Measure S) [IsProbabilityMeasure mu] (L : ℕ) (stop : Bool)
    (schedule : S → List ℕ)
    (hschedule : ∀ m, MeasurableSet (scheduleGate schedule m))
    (prog : S → C → Instruction C ℕ Bool) (initial : S → C)
    (q : ℕ → (Fin L → Bool) → ℕ → Bool)
    (phi : ℕ → (Fin L → Bool) → S → Θ)
    (rho : Θ → Fin (L + 1)) (T : ℕ → (Fin L → Bool) → Set S)
    (readout : C → Θ) (target : ℕ → (Fin L → Bool) → Measure Θ) (eps : ENNReal)
    (hT : ∀ m b, MeasurableSet (T m b))
    (conull : ∀ m b, ∀ᵐ s ∂mu, s ∈ T m b)
    (hphi : ∀ m b, Measurable (phi m b)) (hrho : Measurable rho)
    (cap : ∀ m b, measurableTotalVariation (mu.map (phi m b)) (target m b) ≤ eps)
    (low : ∀ m b (i : Fin L), q m b i = b i)
    (high : ∀ m b i, L ≤ i → i < L + 1 + m → q m b i = false)
    (bounded : ∀ s, (schedule s).length ≤ 2 ∧
      (stop = true → (schedule s).Pairwise (· < ·)))
    (discipline : ∀ m b s,
      Disciplined stop (schedule s) (prog s) (initial s) (q m b))
    (terminal : ∀ m b s, s ∈ T m b → ∃ last : C × List (ℕ × Bool),
      last ∈ StateTransition.eval (step (prog s) (q m b)) (initial s, []))
    (output : ∀ m b s last, s ∈ T m b →
      last ∈ StateTransition.eval (step (prog s) (q m b)) (initial s, []) →
      readout last.1 = phi m b s) :
    let H := fun m => scheduleGate schedule (L + 1 + m)
    Filter.Tendsto (fun m => mu ((H m)ᶜ)) Filter.atTop (nhds 0) ∧
    ∀ m, let D := H m ∩ {s | ∀ b, s ∈ T m b}
      ∃ (F : S → Catalog stop L) (w : PMF (Catalog stop L)),
        Measurable F ∧ w.toMeasure = mu.map F ∧
        (∀ s, (F s).val = witnessTable D rho (phi m) s) ∧
        mu (Dᶜ) = mu ((H m)ᶜ) ∧
        ∀ b, measurableTotalVariation
          (w.toMeasure.map (fun f => f.val b)) ((target m b).map rho) ≤ eps + mu ((H m)ᶜ) := by
  classical
  intro H
  have hH (m) : MeasurableSet (H m) := hschedule (L + 1 + m)
  constructor
  · have anti : Antitone (fun m => (H m)ᶜ) := by
      intro m n hmn s hs hn
      apply hs
      intro i hi
      have := hn i hi
      omega
    have empty : (⋂ m, (H m)ᶜ) = ∅ := by
      ext s
      simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      push Not
      refine ⟨(schedule s).toFinset.sup id + 1, ?_⟩
      intro i hi
      have le : i ≤ (schedule s).toFinset.sup id :=
        Finset.le_sup (f := id) (List.mem_toFinset.mpr hi)
      omega
    have ht := tendsto_measure_iInter_atTop (μ := mu)
      (fun m => (hH m).compl.nullMeasurableSet) anti (by simp)
    simpa only [Function.comp_def, empty, measure_empty] using ht
  · intro m
    exact actual_witness_tables mu L (L + 1 + m) stop schedule prog initial
      (q m) (phi m) rho (H m) (T m) readout (target m) eps (hH m) (hT m)
      (conull m) (hphi m) hrho (cap m) (low m) (high m)
      (fun s hs => ⟨(bounded s).1, hs, (bounded s).2⟩)
      (discipline m) (terminal m) (output m)

#print axioms scheduled_witness_approximation

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
