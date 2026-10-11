/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite marked runtime generates normalized laws of complete original transcripts. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFullFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorGeneratedLaw
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeFullResidual RarePriorFiniteMonitor RarePriorFairBitService RarePriorFullFields

def emissionParameter (z : Runtime) : unitInterval :=
  ⟨(threshold (selectedThreshold z)).val/100, by
    cases selectedThreshold z <;> norm_num [threshold], by
    cases selectedThreshold z <;> norm_num [threshold]⟩

/-- The actual deterministic update remains defined when an emission vanishes. -/
def readAdvance (z : Runtime) (x : Letter) : Runtime := (runtimeStep z (.read x)).getD z

/-- Marks are raw letters; the original renderer alone inserts the unique Stop. -/
abbrev Marked := Runtime × Letter
instance : MeasurableSpace Marked := ⊤
instance : MeasurableSingletonClass Marked := ⟨fun _ => trivial⟩

def markedInitial (z : Runtime) : Measure Marked :=
  (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)).map fun x => (z,x)

instance (z : Runtime) : IsProbabilityMeasure (markedInitial z) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

def markedKernel : Kernel Marked Marked where
  toFun m :=
    (bernoulliMeasure (0 : Letter) 1 (emissionParameter (readAdvance m.1 m.2))).map
      fun x => (readAdvance m.1 m.2,x)
  measurable' := measurable_of_countable _

instance : IsMarkovKernel markedKernel := ⟨fun _ =>
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

def pathLaw (z : Runtime) : Measure (ℕ → Marked) :=
  Kernel.trajMeasure (X := fun _ => Marked) (markedInitial z)
    (fun n => markedKernel.comap (fun u : Finset.Iic n → Marked =>
      u ⟨n,Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _))

instance (z : Runtime) : IsProbabilityMeasure (pathLaw z) := by
  unfold pathLaw
  infer_instance

def renderPath (z : Runtime) (p : ℕ → Marked) : FullTranscript :=
  fieldsTranscript z.fields (fun n => (p n).2)

theorem fields_measurable (f : FiniteFields) : Measurable (fieldsTranscript f) := by
  let c : AcquiredNativeState := ⟨⟨f,0⟩,⟨0,0⟩⟩
  have he : fieldsTranscript f = fullTranscript c :=
    funext fun ω => (full_fields_factorization c ω).1.symm
  rw [he]
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable (fun r : Option (List Operation × AcquiredNativeState × ℕ) =>
    r.map fun p => (p.1,p.2.1.source.finiteFields,eventBlocks f p.1))).comp
      (NativeConditionalControl.Tail.drive_measurable c n)

private theorem render_measurable (z : Runtime) : Measurable (renderPath z) :=
  (fields_measurable z.fields).comp (by fun_prop)

/-- Decoder arguments contain only the installed finite runtime. -/
def decoder (z : Runtime) : Measure FullTranscript := (pathLaw z).map (renderPath z)

def readFold (z : Runtime) (ω : Stream) : ℕ → Runtime
  | 0 => z
  | n+1 => readAdvance (readFold z ω n) (ω n)

private theorem tracks_fold (z : Runtime) (p : ℕ → Marked)
    (hp : (p 0).1 = z)
    (ht : ∀ n, (p (n+1)).1 = readAdvance (p n).1 (p n).2) :
    ∀ n, (p n).1 = readFold z (fun k => (p k).2) n := by
  intro n
  induction n with
  | zero => exact hp
  | succ n ih => rw [ht,readFold,ih]

private theorem initial_support (z : Runtime) (m : Marked)
    (hm : markedInitial z {m} ≠ 0) : m.1 = z := by
  by_contra h
  have he : (fun x : Letter => (z,x)) ⁻¹' ({m} : Set Marked) = ∅ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    intro hx
    exact h (congrArg Prod.fst hx).symm
  apply hm
  rw [markedInitial,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),he]
  exact measure_empty

private theorem transition_support (m d : Marked)
    (hd : markedKernel m {d} ≠ 0) : d.1 = readAdvance m.1 m.2 := by
  by_contra h
  have he : (fun x : Letter => (readAdvance m.1 m.2,x)) ⁻¹' ({d} : Set Marked) = ∅ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    intro hx
    exact h (congrArg Prod.fst hx).symm
  apply hd
  change ((bernoulliMeasure (0 : Letter) 1 (emissionParameter (readAdvance m.1 m.2))).map
    fun x => (readAdvance m.1 m.2,x)) {d} = 0
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),he]
  exact measure_empty

private theorem path_tracks (z : Runtime) :
    ∀ᵐ p ∂pathLaw z, (p 0).1 = z ∧
      ∀ n, (p (n+1)).1 = readAdvance (p n).1 (p n).2 := by
  have hg (n : ℕ) : ∀ᵐ w ∂((pathLaw z).map fun p (i : Fin (n+1)) => p i.val),
      (w 0).1 = z ∧ ∀ i : Fin n,
        (w i.succ).1 = readAdvance (w i.castSucc).1 (w i.castSucc).2 := by
    apply ae_iff_of_countable.mpr
    intro w hw
    unfold pathLaw at hw
    rw [MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (markedInitial z) markedKernel n w] at hw
    have hm : markedInitial z {w 0} ≠ 0 := (mul_ne_zero_iff.mp hw).1
    have hp : ∏ i : Fin n, markedKernel (w i.castSucc) {w i.succ} ≠ 0 :=
      (mul_ne_zero_iff.mp hw).2
    refine ⟨initial_support z _ hm,?_⟩
    intro i
    apply transition_support
    exact Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _)
  have h0 : ∀ᵐ p ∂pathLaw z, (p 0).1 = z := by
    filter_upwards [ae_of_ae_map (Measurable.aemeasurable (by fun_prop)) (hg 0)] with p hp
    exact hp.1
  have hn (n : ℕ) : ∀ᵐ p ∂pathLaw z,
      (p (n+1)).1 = readAdvance (p n).1 (p n).2 := by
    filter_upwards [ae_of_ae_map (Measurable.aemeasurable (by fun_prop)) (hg (n+1))] with p hp
    exact hp.2 (Fin.last n)
  filter_upwards [h0,ae_all_iff.mpr hn] with p hp hn
  exact ⟨hp,hn⟩

private theorem paths_ext (μ ν : Measure (ℕ → Marked)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (he : ∀ n : ℕ, μ.map (fun p (i : Fin (n+1)) => p i.val) =
      ν.map (fun p (i : Fin (n+1)) => p i.val)) : μ = ν := by
  let P : (I : Finset ℕ) → Measure (Π _ : I, Marked) := fun I => ν.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ : ℕ => Marked) P := by
    intro I J hJI
    dsimp [P]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have hm : IsProjectiveLimit (α := fun _ : ℕ => Marked) μ P := by
    apply (isProjectiveLimit_nat_iff hp μ).mpr
    intro n
    let E : (Fin (n+1) → Marked) → (Finset.Iic n → Marked) :=
      fun w i => w ⟨i.val,Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp i.property)⟩
    have hf (ρ : Measure (ℕ → Marked)) : ρ.map (frestrictLe n) =
        (ρ.map (fun p (i : Fin (n+1)) => p i.val)).map E := by
      rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]
      rfl
    rw [hf,he n,← hf]
    rfl
  have hn : IsProjectiveLimit (α := fun _ : ℕ => Marked) ν P := fun _ => rfl
  exact hm.unique hn

/-- The first marked read conditions to a fresh trajectory from the exact
    retained successor. This is an equality of complete infinite path laws. -/
theorem conditioned_read_path (z : Runtime) (x : Letter) :
    (ProbabilityTheory.cond (pathLaw z) {p | p 0 = (z,x)}).map
      (fun p n => p (n+1)) = pathLaw (readAdvance z x) := by
  have hi : markedInitial z {(z,x)} =
      (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)) {x} := by
    rw [markedInitial,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext y
    simp
  have hib : markedInitial z {(z,x)} ≠ 0 := by
    rw [hi]
    fin_cases x <;> cases ht : selectedThreshold z <;>
      norm_num [bernoulliMeasure_apply,emissionParameter,ht,threshold,
        ENNReal.coe_eq_zero,← NNReal.coe_eq_zero,unitInterval.coe_toNNReal]
  have hmass : pathLaw z {p | p 0 = (z,x)} = markedInitial z {(z,x)} := by
    have h := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (markedInitial z) markedKernel 0 (fun _ => (z,x))
    have hf : (fun p : ℕ → Marked => fun i : Fin 1 => p i.val) =
        (fun p : ℕ → Marked => fun _ : Fin 1 => p 0) := by funext p i; congr 1; omega
    change ((pathLaw z).map fun p (i : Fin 1) => p i.val) {fun _ => (z,x)} = _ at h
    rw [hf] at h
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
    have hset : (fun p : ℕ → Marked => fun _ : Fin 1 => p 0) ⁻¹' {fun _ => (z,x)} =
        {p | p 0 = (z,x)} := by
      ext p
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq,funext_iff]
      exact ⟨fun hp => hp 0,fun hp _ => hp⟩
    simpa [hset] using h
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (pathLaw z) {p | p 0 = (z,x)}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (hmass ▸ hib)
  haveI : IsProbabilityMeasure ((ProbabilityTheory.cond (pathLaw z) {p | p 0 = (z,x)}).map
      (fun p n => p (n+1))) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  apply paths_ext
  intro n
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_apply (by fun_prop)
    (measurableSet_singleton _),ProbabilityTheory.cond,Measure.smul_apply,
    Measure.restrict_apply ((measurableSet_singleton _).preimage (by fun_prop)),hmass]
  simp only [Function.comp_def,smul_eq_mul]
  have he :
      (fun p : ℕ → Marked => fun i : Fin (n+1) => p (i.val+1)) ⁻¹' {w} ∩
        {p | p 0 = (z,x)} =
      (fun p : ℕ → Marked => fun i : Fin (n+2) => p i.val) ⁻¹' {Fin.cons (z,x) w} := by
    ext p
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq,
      funext_iff]
    constructor
    · intro hp i
      refine Fin.cases hp.2 (fun j => hp.1 j) i
    · intro hp
      exact ⟨fun i => hp i.succ,hp 0⟩
  rw [he,← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hprefix := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
    (markedInitial z) markedKernel (n+1) (Fin.cons (z,x) w)
  have htail := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
    (markedInitial (readAdvance z x)) markedKernel n w
  change _ = ((pathLaw (readAdvance z x)).map fun p (i : Fin (n+1)) => p i.val) {w}
  change ((markedInitial z) {(z,x)})⁻¹ *
    ((pathLaw z).map fun p (i : Fin (n+2)) => p i.val) {Fin.cons (z,x) w} =
      ((pathLaw (readAdvance z x)).map fun p (i : Fin (n+1)) => p i.val) {w}
  unfold pathLaw
  rw [hprefix,htail,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.castSucc_zero,Fin.castSucc_succ]
  have hik : markedKernel (z,x) = markedInitial (readAdvance z x) := rfl
  rw [hik,← mul_assoc,ENNReal.inv_mul_cancel hib (measure_ne_top _ _),one_mul]

instance : MeasurableSpace (Option Operation) := ⊤
instance : MeasurableSingletonClass (Option Operation) := ⟨fun _ => trivial⟩

def firstOperation (t : FullTranscript) : Option Operation :=
  (t 1).bind fun r => r.1.head?

theorem first_measurable : Measurable firstOperation := by
  exact (measurable_of_countable (fun r : FullOutput => r.bind fun v => v.1.head?)).comp
    (measurable_pi_apply 1)

private theorem map_cond (z : Runtime) (S : Set FullTranscript) (hS : MeasurableSet S) :
    ProbabilityTheory.cond (decoder z) S =
      (ProbabilityTheory.cond (pathLaw z) ((renderPath z) ⁻¹' S)).map (renderPath z) := by
  apply Measure.ext
  intro A hA
  rw [ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply hA,
    decoder,Measure.map_apply (render_measurable z) hS,
    Measure.map_apply (render_measurable z) (hA.inter hS),
    Measure.map_apply (render_measurable z) hA,
    ProbabilityTheory.cond,Measure.smul_apply,
    Measure.restrict_apply (hA.preimage (render_measurable z))]
  rfl

private theorem read_step_fields (z : Runtime) (x : Letter) (d : Runtime)
    (hd : runtimeStep z (.read x) = some d) :
    finiteStep z.fields (.read x) = some d.fields := by
  have h := runtime_projection z [.read x]
  simpa [runtimeExecute,hd,executeFinite] using h.symm

private theorem read_first (z : Runtime)
    (hr : ∀ x, finiteOperation z.fields x = some (.read x))
    (hs : ∀ x, ∃ d, runtimeStep z (.read x) = some d) (p : ℕ → Marked) :
    firstOperation (renderPath z p) = some (.read (p 0).2) := by
  obtain ⟨d,hd⟩ := hs (p 0).2
  have hf := read_step_fields z (p 0).2 d hd
  simp [firstOperation,renderPath,fieldsTranscript,finiteDrive,finiteNext,hr,hf]

private theorem read_delete (z d : Runtime) (x : Letter)
    (hr : finiteOperation z.fields x = some (.read x))
    (hd : runtimeStep z (.read x) = some d) (p : ℕ → Marked) (hp : (p 0).2 = x) :
    deleteBlock (renderPath z p) = renderPath d (fun n => p (n+1)) := by
  have hf := read_step_fields z x d hd
  funext n
  simp [deleteBlock,renderPath,fieldsTranscript,finiteDrive,finiteNext,hp,hr,hf,
    Option.map_map,Function.comp_def,eventBlocks,rawTail,readCost]
  rfl

private theorem ready_permits (z : Runtime)
    (hr : ∀ b, z.fields.control ≠ .fourth (.pending b))
    (he : z.fields.control ≠ .fourth .delivered) :
    (∀ x, finiteOperation z.fields x = some (.read x)) ∧
    (∀ x, ∃ d, runtimeStep z (.read x) = some d) := by
  constructor
  · intro x
    cases hc : z.fields.control with
    | seed a => simp [finiteOperation,hc]
    | early t s => simp [finiteOperation,hc]
    | fourth c => cases c with
      | active s => simp [finiteOperation,hc]
      | pending b => exact (hr b hc).elim
      | delivered => exact (he hc).elim
  · intro x
    cases hc : z.fields.control with
    | seed a => cases a <;> simp [runtimeStep,finiteStep,finiteRead,hc]
    | early t s => simp [runtimeStep,finiteStep,finiteRead,hc]
    | fourth c => cases c with
      | active s => simp [runtimeStep,finiteStep,finiteRead,hc]
      | pending b => exact (hr b hc).elim
      | delivered => exact (he hc).elim

/-- Every read-ready configuration has the original first-operation law and the
    exact complete-record conditional residual under its actual update. -/
theorem generated_read_compatibility (z : Runtime)
    (hr : ∀ x, finiteOperation z.fields x = some (.read x))
    (hs : ∀ x, ∃ d, runtimeStep z (.read x) = some d) (x : Letter) :
    (decoder z) {t | firstOperation t = some (.read x)} =
      (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)) {x} ∧
    (ProbabilityTheory.cond (decoder z) {t | firstOperation t = some (.read x)}).map
      deleteBlock = decoder (readAdvance z x) := by
  let A : Set (ℕ → Marked) := {p | p 0 = (z,x)}
  let S : Set FullTranscript := {t | firstOperation t = some (.read x)}
  have hS : MeasurableSet S := (measurableSet_singleton _).preimage first_measurable
  have he : (renderPath z) ⁻¹' S =ᵐ[pathLaw z] A := by
    filter_upwards [path_tracks z] with p hp
    change (firstOperation (renderPath z p) = some (.read x)) = (p 0 = (z,x))
    simp [read_first z hr hs,Prod.ext_iff,hp.1]
  have hc : ProbabilityTheory.cond (pathLaw z) ((renderPath z) ⁻¹' S) =
      ProbabilityTheory.cond (pathLaw z) A := by
    unfold ProbabilityTheory.cond
    rw [measure_congr he,Measure.restrict_congr_set he]
  constructor
  · rw [decoder,Measure.map_apply (render_measurable z) hS,measure_congr he]
    have h := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (markedInitial z) markedKernel 0 (fun _ => (z,x))
    change ((pathLaw z).map fun p (i : Fin 1) => p i.val) {fun _ => (z,x)} = _ at h
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
    have hf : (fun p : ℕ → Marked => fun i : Fin 1 => p i.val) ⁻¹' {fun _ => (z,x)} = A := by
      ext p
      simp only [A,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq,funext_iff]
      exact ⟨fun hp => hp 0,fun hp i => by simpa using hp⟩
    rw [hf] at h
    rw [h,markedInitial,Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton _)]
    simp
    congr 1
    ext y
    simp
  · change (ProbabilityTheory.cond (decoder z) S).map deleteBlock = _
    rw [map_cond z S hS,hc,Measure.map_map (by unfold deleteBlock; fun_prop)
      (render_measurable z)]
    obtain ⟨d,hd⟩ := hs x
    have had : readAdvance z x = d := by simp [readAdvance,hd]
    have hm : (ProbabilityTheory.cond (pathLaw z) A).map
        (deleteBlock ∘ renderPath z) =
        (ProbabilityTheory.cond (pathLaw z) A).map
          (renderPath d ∘ (fun p n => p (n+1))) := by
      apply Measure.map_congr
      filter_upwards [ProbabilityTheory.ae_cond_mem
        (show MeasurableSet A from (measurableSet_singleton _).preimage (measurable_pi_apply 0))]
        with p hp
      exact read_delete z d x (hr x) hd p (congrArg Prod.snd hp)
    rw [hm,← Measure.map_map (render_measurable d) (by fun_prop)]
    change ((ProbabilityTheory.cond (pathLaw z) {p | p 0 = (z,x)}).map
      (fun p n => p (n+1))).map (renderPath d) = _
    rw [conditioned_read_path,had]
    rfl

theorem terminal_constant (z : Runtime)
    (ht : (∃ b, z.fields.control = .fourth (.pending b)) ∨
      z.fields.control = .fourth .delivered) (p q : ℕ → Marked) :
    renderPath z p = renderPath z q := by
  funext n
  rcases ht with ⟨b,hb⟩ | hb
  · cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => simp [renderPath,fieldsTranscript,finiteDrive,finiteNext,finiteOperation,
          hb,finiteStep,finiteStop]
      | succ n => simp [renderPath,fieldsTranscript,finiteDrive,finiteNext,finiteOperation,
          hb,finiteStep,finiteStop]
  · cases n <;> simp [renderPath,fieldsTranscript,finiteDrive,finiteNext,finiteOperation,hb]

theorem terminal_dirac (z : Runtime)
    (ht : (∃ b, z.fields.control = .fourth (.pending b)) ∨
      z.fields.control = .fourth .delivered) :
    decoder z = Measure.dirac (renderPath z (fun _ => (z,0))) := by
  unfold decoder
  calc
    (pathLaw z).map (renderPath z) =
        (pathLaw z).map (fun _ => renderPath z (fun _ => (z,0))) :=
      Measure.map_congr (Filter.Eventually.of_forall fun p => terminal_constant z ht p _)
    _ = _ := by simp

private theorem stop_render (z : Runtime) (b : Letter)
    (hb : z.fields.control = .fourth (.pending b)) (p q : ℕ → Marked) :
    deleteBlock (renderPath z p) =
      renderPath ((runtimeStep z (.stop b)).getD z) q := by
  funext n
  cases n with
  | zero => simp [deleteBlock,renderPath,fieldsTranscript,finiteDrive,finiteNext,
      finiteOperation,hb,runtimeStep,finiteStep,finiteStop,eventBlocks]
  | succ n => simp [deleteBlock,renderPath,fieldsTranscript,finiteDrive,finiteNext,
      finiteOperation,hb,runtimeStep,finiteStep,finiteStop,eventBlocks]

/-- The finite decoder has both positive letter branches at each read menu,
    the unique matching Stop at pending, and the delivered empty future.
    Conditioning and deletion always use the actual deterministic successor. -/
theorem configuration_compatibility (z : Runtime) :
    ((∀ b, z.fields.control ≠ .fourth (.pending b)) →
      z.fields.control ≠ .fourth .delivered → ∀ x : Letter,
      (decoder z) {t | firstOperation t = some (.read x)} =
        (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)) {x} ∧
      (ProbabilityTheory.cond (decoder z) {t | firstOperation t = some (.read x)}).map
        deleteBlock = decoder (readAdvance z x)) ∧
    (∀ b : Letter, z.fields.control = .fourth (.pending b) →
      (decoder z) {t | firstOperation t = some (.stop b)} = 1 ∧
      (ProbabilityTheory.cond (decoder z) {t | firstOperation t = some (.stop b)}).map
        deleteBlock = decoder ((runtimeStep z (.stop b)).getD z)) ∧
    (z.fields.control = .fourth .delivered →
      decoder z = Measure.dirac (renderPath z (fun _ => (z,0))) ∧
      (decoder z) {t | firstOperation t = none} = 1 ∧
      ∀ (p : ℕ → Marked) (n : ℕ), renderPath z p (n+1) = none) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro hp he x
    obtain ⟨hr,hs⟩ := ready_permits z hp he
    exact generated_read_compatibility z hr hs x
  · intro b hb
    have ht : (∃ b, z.fields.control = .fourth (.pending b)) ∨
        z.fields.control = .fourth .delivered := Or.inl ⟨b,hb⟩
    have hd : ((runtimeStep z (.stop b)).getD z).fields.control = .fourth .delivered := by
      simp [runtimeStep,finiteStep,finiteStop,hb]
    have hfirst : firstOperation (renderPath z (fun _ => (z,0))) = some (.stop b) := by
      simp [firstOperation,renderPath,fieldsTranscript,finiteDrive,finiteNext,
        finiteOperation,hb,finiteStep,finiteStop]
    rw [terminal_dirac z ht]
    constructor
    · simp [Measure.dirac_apply',hfirst]
    · rw [ProbabilityTheory.cond]
      have hx : Measure.dirac (renderPath z (fun _ => (z,0)))
          {t | firstOperation t = some (.stop b)} = 1 := by simp [hfirst]
      rw [hx]
      simp only [inv_one,one_smul]
      have hmeas : MeasurableSet {t : FullTranscript | firstOperation t = some (.stop b)} :=
        (measurableSet_singleton _).preimage first_measurable
      rw [restrict_dirac' hmeas]
      simp only [Set.mem_setOf_eq,hfirst,if_pos]
      have hm : Measurable deleteBlock := by unfold deleteBlock; fun_prop
      rw [Measure.map_dirac' hm (renderPath z (fun _ => (z,0)))]
      rw [terminal_dirac _ (Or.inr hd),stop_render z b hb]
  · intro hd
    refine ⟨terminal_dirac z (Or.inr hd),?_,?_⟩
    · rw [terminal_dirac z (Or.inr hd)]
      have hf : firstOperation (renderPath z (fun _ => (z,0))) = none := by
        simp [firstOperation,renderPath,fieldsTranscript,finiteDrive,finiteNext,finiteOperation,hd]
      simp [Measure.dirac_apply',hf]
    · intro p n
      simp [renderPath,fieldsTranscript,finiteDrive,finiteNext,finiteOperation,hd]

/-- Normalization and exact finite prefix masses use the same marked kernel.
    Every path satisfying its deterministic support equations tracks the finite
    runtime, and its full output agrees with every native lift of those fields. -/
theorem generated_full_law (z : Runtime) :
    IsProbabilityMeasure (decoder z) ∧
    0 < (emissionParameter z : ℝ) ∧ (emissionParameter z : ℝ) < 1 ∧
    returnedAlphaMass (selectedThreshold z) = (emissionParameter z : ℝ) ∧
    (∀ (n : ℕ) (w : Fin (n+1) → Marked),
      ((pathLaw z).map fun p (i : Fin (n+1)) => p i.val) {w} =
        markedInitial z {w 0} * ∏ i : Fin n, markedKernel (w i.castSucc) {w i.succ}) ∧
    (∀ (p : ℕ → Marked), (p 0).1 = z →
      (∀ n, (p (n+1)).1 = readAdvance (p n).1 (p n).2) →
      (∀ n, (p n).1 = readFold z (fun k => (p k).2) n) ∧
      ∀ c : AcquiredNativeState, c.source.finiteFields = z.fields →
        renderPath z p = fullTranscript c (fun k => (p k).2)) ∧
    (∀ᵐ p ∂pathLaw z, (p 0).1 = z ∧
      ∀ n, (p (n+1)).1 = readAdvance (p n).1 (p n).2) := by
  refine ⟨Measure.isProbabilityMeasure_map (render_measurable z).aemeasurable,
    ?_,?_,?_,?_,?_,path_tracks z⟩
  · cases ht : selectedThreshold z <;> norm_num [emissionParameter,ht,threshold]
  · cases ht : selectedThreshold z <;> norm_num [emissionParameter,ht,threshold]
  · obtain ⟨ho,hh,hl,_⟩ := exact_service_law
    cases ht : selectedThreshold z <;>
      norm_num [emissionParameter,ht,threshold,ho,hh,hl]
  · intro n w
    exact MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (markedInitial z) markedKernel n w
  · intro p hp ht
    refine ⟨tracks_fold z p hp ht,?_⟩
    intro c hc
    simpa [renderPath,hc] using
      (full_fields_factorization c (fun k => (p k).2)).1.symm

def historyGenerated (h : List Operation) : Measure FullTranscript :=
  ∑ z : Runtime, NativeObserverJointLaw.row actualObserver h z • decoder z

private theorem history_pure (h : List Operation) (z : Runtime)
    (hz : NativeObserverJointLaw.row actualObserver h = PMF.pure z) :
    historyGenerated h = decoder z := by
  classical
  simp [historyGenerated,hz,PMF.pure_apply,ite_smul]

private theorem permitted_residual (z : Runtime) (op : Operation) (f : FiniteFields)
    (hf : finiteStep z.fields op = some f) :
    (ProbabilityTheory.cond (decoder z) {t | firstOperation t = some op}).map deleteBlock =
      decoder ((runtimeStep z op).getD z) := by
  cases op with
  | read x =>
    have hp : ∀ b, z.fields.control ≠ .fourth (.pending b) := by
      intro b hb
      simp [finiteStep,finiteRead,hb] at hf
    have he : z.fields.control ≠ .fourth .delivered := by
      intro hb
      simp [finiteStep,finiteRead,hb] at hf
    exact ((configuration_compatibility z).1 hp he x).2
  | stop b =>
    cases hc : z.fields.control with
    | seed a => simp [finiteStep,finiteStop,hc] at hf
    | early t s => simp [finiteStep,finiteStop,hc] at hf
    | fourth c => cases c with
      | active s => simp [finiteStep,finiteStop,hc] at hf
      | delivered => simp [finiteStep,finiteStop,hc] at hf
      | pending a =>
        have he : b = a := by
          by_contra hn
          simp [finiteStep,finiteStop,hc,hn] at hf
        subst b
        exact ((configuration_compatibility z).2.1 a hc).2

/-- Conditioning on each original positive legal history gives its actual
    deterministic row. Marginalizing that row preserves the generated residual,
    including Stop, under the same update for every permitted source operation. -/
theorem history_marginal_compatibility (μ : PMF NativeConditionalControl.DepthLaw.Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) :
    (ProbabilityTheory.cond (NativeObserverJointLaw.actualLaw actualObserver μ h.length)
      (NativeConditionalControl.DepthLaw.nativeEvent h c ×ˢ Set.univ)).map
      (Prod.map (fun t : NativeConditionalControl.DepthLaw.Depth × Stream =>
        (t.1,rawTail t.2 (readLetters h).length)) id) =
      (NativeConditionalControl.DepthLaw.jointLaw
        (NativeConditionalControl.DepthLaw.posterior μ h c hc)).prod
        (NativeObserverJointLaw.row actualObserver h).toMeasure ∧
    ∃ z : Runtime, runtimeRun h = some z ∧ z.fields = c.source.finiteFields ∧
      NativeObserverJointLaw.row actualObserver h = PMF.pure z ∧
      historyGenerated h = decoder z ∧
      ∀ (op : Operation) (d : AcquiredNativeState), nativeStep c op = some d →
        NativeObserverJointLaw.row actualObserver (h ++ [op]) = actualUpdate op z ∧
        (ProbabilityTheory.cond (historyGenerated h) {t | firstOperation t = some op}).map
          deleteBlock = historyGenerated (h ++ [op]) := by
  refine ⟨NativeObserverJointLaw.sameK_private_tail actualObserver μ h c hc,?_⟩
  obtain ⟨z,hz,hfields,hrow,hnext⟩ := deterministic_actual_rows h c hc
  refine ⟨z,hz,hfields,hrow,history_pure h z hrow,?_⟩
  intro op d hd
  have hf : finiteStep z.fields op = some d.source.finiteFields := by
    rw [hfields,← finite_projection_commutes,hd]
    rfl
  refine ⟨hnext op,?_⟩
  rw [history_pure h z hrow]
  have hr : NativeObserverJointLaw.row actualObserver (h ++ [op]) =
      PMF.pure ((runtimeStep z op).getD z) := hnext op
  rw [history_pure (h ++ [op]) _ hr]
  exact permitted_residual z op d.source.finiteFields hf

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorGeneratedLaw
