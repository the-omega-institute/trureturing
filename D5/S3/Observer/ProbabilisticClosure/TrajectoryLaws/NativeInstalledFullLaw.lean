/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Installed emissions and actual updates generate lawful complete native event laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Tail
open NativeConditionalControl.Control NativeConditionalControl.Stopping
open NativeFullResidual NativeObserverJointLaw
universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

local instance : MeasurableSpace (Option (List Operation)) := ⊤
local instance : MeasurableSingletonClass (Option (List Operation)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List Operation) := ⊤
local instance : MeasurableSingletonClass (List Operation) := ⟨fun _ => trivial⟩

instance : MeasurableSpace (Option Operation) := ⊤
instance : MeasurableSingletonClass (Option Operation) := ⟨fun _ => trivial⟩

/-- Semantic emission law of the installed program, on the original COMPLETE carrier. -/
structure InstalledEmitter (M : Observer Z) where
  emit : Z → PMF (Option Operation)
  lawful : ∀ z a, a ∈ (emit z).support →
    match a with
    | none => (M.project z).control = .fourth .delivered
    | some op => (finiteStep (M.project z) op).isSome

abbrev Marked (Z : Type u) := Z × Option Operation

/-- Incoming marks are analysis coordinates. A real operation uses exactly M.update. -/
def markedRow (M : Observer Z) (e : InstalledEmitter M) (w : Marked Z) : PMF (Marked Z) :=
  (e.emit w.1).bind fun a => match a with
    | none => PMF.pure (w.1, none)
    | some op => (M.update op w.1).map fun z' => (z', some op)

def markedKernel (M : Observer Z) (e : InstalledEmitter M) : Kernel (Marked Z) (Marked Z) :=
  Kernel.ofFunOfCountable fun w => (markedRow M e w).toMeasure

instance (M : Observer Z) (e : InstalledEmitter M) : IsMarkovKernel (markedKernel M e) :=
  ⟨fun w => inferInstanceAs (IsProbabilityMeasure (markedRow M e w).toMeasure)⟩

def markedLaw (M : Observer Z) (e : InstalledEmitter M) (w : Marked Z) :
    Measure (ℕ → Marked Z) :=
  Kernel.trajMeasure (X := fun _ => Marked Z) (Measure.dirac w) (fun n => (markedKernel M e).comap
      (fun x : Iic n → Marked Z => x ⟨n, mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

instance (M : Observer Z) (e : InstalledEmitter M) (w : Marked Z) :
    IsProbabilityMeasure (markedLaw M e w) := by unfold markedLaw; infer_instance

private theorem prefix_mass (M : Observer Z) (e : InstalledEmitter M)
    (w : Marked Z) (n : ℕ) (v : Fin (n+1) → Marked Z) :
    ((markedLaw M e w).map (fun x i => x (i : Fin (n+1)))) {v} =
      (if v 0 = w then 1 else 0) *
        ∏ i : Fin n, markedRow M e (v i.castSucc) (v i.succ) := by
  simp only [markedLaw]
  rw [MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton]
  change (Measure.dirac w) {v 0} *
    (∏ i : Fin n, (markedRow M e (v i.castSucc)).toMeasure {v i.succ}) = _
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [Measure.dirac_apply', Pi.single_apply, eq_comm]

private theorem path_ext {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (μ ν : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (h : ∀ n : ℕ, μ.map (fun x i => x (i : Fin (n+1))) =
      ν.map (fun x i => x (i : Fin (n+1)))) : μ = ν := by
  let P := fun I : Finset ℕ => μ.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ => A) P := by
    intro I J hij
    dsimp only [P]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have hn : IsProjectiveLimit (α := fun _ => A) ν P := by
    apply (isProjectiveLimit_nat_iff hp ν).mpr
    intro n
    let f : (Fin (n+1) → A) → (Iic n → A) :=
      fun v i => v ⟨i.val, Nat.lt_succ_of_le (mem_Iic.mp i.property)⟩
    have hf : Measurable f := by fun_prop
    have hm := congrArg (Measure.map f) (h n)
    rw [Measure.map_map hf (by fun_prop : Measurable
      (fun x : ℕ → A => fun i : Fin (n+1) => x i)),
      Measure.map_map hf (by fun_prop : Measurable
      (fun x : ℕ → A => fun i : Fin (n+1) => x i))] at hm
    exact hm.symm
  exact (show IsProjectiveLimit (α := fun _ => A) μ P from fun _ => rfl).unique hn

private def prepend {A : Type*} (a : A) (x : ℕ → A) : ℕ → A
  | 0 => a
  | n+1 => x n

@[fun_prop] private theorem measurable_prepend {A : Type*} [MeasurableSpace A] (a : A) :
    Measurable (prepend a) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

private theorem marked_regenerate (M : Observer Z) (e : InstalledEmitter M)
    (w : Marked Z) :
    markedLaw M e w = ∑ v : Marked Z, markedRow M e w v •
      (markedLaw M e v).map (fun x => prepend w x) := by
  classical
  apply path_ext
  intro n
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_finset_sum' (Measurable.aemeasurable (by fun_prop))]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.map_smul, Measure.smul_apply, smul_eq_mul]
  rw [prefix_mass]
  cases n with
  | zero =>
    have hh (y : Marked Z) :
        ((markedLaw M e y).map (fun x i => prepend w x (i : Fin 1))) {v} =
          if v 0 = w then 1 else 0 := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      have he : (fun x i => prepend w x (i : Fin 1)) ⁻¹' {v} =
          if v 0 = w then Set.univ else ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
        split_ifs with h0
        · simp only [Set.mem_univ, iff_true]
          intro i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa [hi, prepend] using h0.symm
        · simp only [Set.mem_empty_iff_false, iff_false]
          intro h; exact h0 (by simpa [prepend] using (h 0).symm)
      rw [he]; split_ifs <;> simp
    simp_rw [Measure.map_map (by fun_prop : Measurable
      (fun x : ℕ → Marked Z => fun i : Fin 1 => x i)) (measurable_prepend w),
      Function.comp_def, hh]
    have hs : ∑ y : Marked Z, markedRow M e w y = 1 := by
      simpa only [tsum_fintype] using (markedRow M e w).tsum_coe
    rw [← Finset.sum_mul, hs]
    simp
  | succ n =>
    let tail : Fin (n+1) → Marked Z := fun i => v i.succ
    have hh (y : Marked Z) :
        ((markedLaw M e y).map (fun x i => prepend w x (i : Fin (n+2)))) {v} =
          if v 0 = w then ((markedLaw M e y).map
            (fun x i => x (i : Fin (n+1)))) {tail} else 0 := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      split_ifs with h0
      · have he : (fun x i => prepend w x (i : Fin (n+2))) ⁻¹' {v} =
            (fun x i => x (i : Fin (n+1))) ⁻¹' {tail} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
          constructor
          · intro hx i; exact hx i.succ
          · intro hx i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact h0.symm
            · exact hx j
        rw [he, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      · have he : (fun x i => prepend w x (i : Fin (n+2))) ⁻¹' {v} = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false]
          intro hx; exact h0 (by simpa [prepend] using (congrFun hx 0).symm)
        rw [he, measure_empty]
    simp_rw [Measure.map_map (by fun_prop : Measurable
      (fun x : ℕ → Marked Z => fun i : Fin (n+2) => x i)) (measurable_prepend w),
      Function.comp_def, hh]
    by_cases h0 : v 0 = w
    · simp only [h0, ↓reduceIte, one_mul]
      simp_rw [prefix_mass]
      rw [Fin.prod_univ_succ]
      have ht : tail 0 = v (0 : Fin (n+1)).succ := rfl
      rw [Finset.sum_eq_single (tail 0)]
      · simp only [tail, if_pos rfl, one_mul, Fin.succ_castSucc, Fin.castSucc_zero, if_true]
        rw [h0]
      · intro y _ hy; simp [hy, Ne.symm hy]
      · exact fun h => (h (Finset.mem_univ _)).elim
    · simp [h0]

/-- A finite-fields representative; its analysis counters are immaterial to the output. -/
def representative (f : FiniteFields) : AcquiredNativeState := ⟨⟨f, 0⟩, ⟨0, 0⟩⟩

private theorem full_fields_eq (c d : AcquiredNativeState) (ω : Stream)
    (hf : c.source.finiteFields = d.source.finiteFields) :
    fullTranscript c ω = fullTranscript d ω := by
  funext n
  have hv := drive_control c d ω n (congrArg FiniteFields.control hf)
  cases hc : nativeDrive c ω n with
  | none =>
    cases hd : nativeDrive d ω n with
    | none => simp [fullTranscript, hc, hd]
    | some r => simp [visible, hc, hd] at hv
  | some r =>
    rcases r with ⟨ops, c', k⟩
    cases hd : nativeDrive d ω n with
    | none => simp [visible, hc, hd] at hv
    | some r =>
      rcases r with ⟨ops', d', j⟩
      have hop : ops = ops' := by
        simpa only [visible, hc, hd, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] using (show ops = ops' ∧ c'.source.finiteFields.control =
          d'.source.finiteFields.control from by simpa [visible, hc, hd] using hv).1
      subst ops'
      have hec := ((drive_spec n c c' ω ops k).mp hc).2.1
      have hed := ((drive_spec n d d' ω ops j).mp hd).2.1
      have hp := execute_finite_projection c ops
      have hq := execute_finite_projection d ops
      rw [hec, Option.map_some, hf] at hp
      rw [hed, Option.map_some, ← hp] at hq
      have he : c'.source.finiteFields = d'.source.finiteFields :=
        (Option.some.inj hq).symm
      simp [fullTranscript, hc, hd, hf, he]

/-- Read marks at coordinates 1,2,...; Stop and delivered padding are not source Reads. -/
def rawFrom (x : ℕ → Marked Z) : Stream := fun n =>
  match (x (n+1)).2 with
  | some (.read b) => b
  | _ => 0

@[fun_prop] private theorem rawFrom_measurable : Measurable (rawFrom (Z := Z)) := by
  apply measurable_pi_lambda
  intro n
  change Measurable (fun x : ℕ → Marked Z => match (x (n+1)).2 with
    | some (.read b) => b | _ => (0 : Letter))
  exact (measurable_of_countable (fun a : Option Operation => match a with
    | some (.read b) => b | _ => (0 : Letter))).comp
    ((measurable_snd : Measurable (Prod.snd : Marked Z → Option Operation)).comp
      (measurable_pi_apply (n+1) : Measurable (fun x : ℕ → Marked Z => x (n+1))))

def decode (M : Observer Z) (z : Z) (x : ℕ → Marked Z) : FullTranscript :=
  fullTranscript (representative (M.project z)) (rawFrom x)

@[fun_prop] private theorem decode_measurable (M : Observer Z) (z : Z) :
    Measurable (decode M z) := by
  apply measurable_pi_lambda
  intro n
  let f : Option (List Operation × AcquiredNativeState × ℕ) → FullOutput :=
    fun r => r.map fun t => (t.1, t.2.1.source.finiteFields, eventBlocks (M.project z) t.1)
  have hf : Measurable f := measurable_of_countable _
  exact (hf.comp (drive_measurable (representative (M.project z)) n)).comp
    rawFrom_measurable

/-- A configuration-only complete probability law; initialization is the current delta. -/
private def nativeLaw (M : Observer Z) (e : InstalledEmitter M) (z : Z) : Measure FullTranscript :=
  (markedLaw M e (z, none)).map (decode M z)

private theorem marked_head (M : Observer Z) (e : InstalledEmitter M) (w : Marked Z) :
    ∀ᵐ x ∂markedLaw M e w, x 0 = w := by
  have h := prefix_mass M e w 0 (fun _ : Fin 1 => w)
  have he : (fun x : ℕ → Marked Z => fun i : Fin 1 => x i) ⁻¹' {fun _ => w} =
      {x | x 0 = w} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_setOf_eq]
    exact ⟨fun h => h 0, fun h i => by simpa using h⟩
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _), he] at h
  apply (mem_ae_iff_prob_eq_one (measurableSet_eq_fun
    (measurable_pi_apply 0) measurable_const)).mpr
  simpa using h

private theorem decoded_mark_irrelevance (M : Observer Z) (e : InstalledEmitter M)
    (z : Z) (a : Option Operation) :
    (markedLaw M e (z,a)).map (decode M z) = nativeLaw M e z := by
  rw [nativeLaw, marked_regenerate M e (z,a), marked_regenerate M e (z,none)]
  rw [Measure.map_finset_sum' (decode_measurable M z).aemeasurable,
    Measure.map_finset_sum' (decode_measurable M z).aemeasurable]
  simp only [Measure.map_smul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.map_map (decode_measurable M z) (measurable_prepend _),
    Measure.map_map (decode_measurable M z) (measurable_prepend _)]
  rfl

/-- Arbitrary measurable residual events remove the entire first native block. -/
def blockEvent (f f' : FiniteFields) (op : Operation) (E : Set FullTranscript) :
    Set FullTranscript := {t |
      t 0 = some ([], f, []) ∧
      t 1 = some ([op], f', [eventBlock f op]) ∧ deleteBlock t ∈ E}

private theorem deleteBlock_measurable : Measurable deleteBlock := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable (fun a : FullOutput =>
    a.map fun r => (r.1.tail,r.2.1,r.2.2.tail))).comp (measurable_pi_apply (n+1))

private theorem blockEvent_measurable (f f' : FiniteFields) (op : Operation)
    (E : Set FullTranscript) (hE : MeasurableSet E) :
    MeasurableSet (blockEvent f f' op E) := by
  exact (measurableSet_eq_fun (measurable_pi_apply 0)
    (measurable_const (a := (some ([],f,[]) : FullOutput)))).inter
    ((measurableSet_eq_fun (measurable_pi_apply 1)
    (measurable_const (a := (some ([op],f',[eventBlock f op]) : FullOutput)))).inter
    (hE.preimage deleteBlock_measurable))

/-- A lawful incoming mark has the original finite transaction as its projected edge. -/
def Edge (M : Observer Z) (w v : Marked Z) : Prop :=
  match v.2 with
  | none => (M.project w.1).control = .fourth .delivered ∧ v.1 = w.1
  | some op => finiteStep (M.project w.1) op = some (M.project v.1)

private theorem supported_edge (M : Observer Z) (e : InstalledEmitter M)
    (w v : Marked Z) (hv : v ∈ (markedRow M e w).support) : Edge M w v := by
  obtain ⟨a,ha,hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
  have he := e.lawful w.1 a ha
  cases a with
  | none =>
    have hh := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact ⟨he,rfl⟩
  | some op =>
    obtain ⟨z',hz',hh⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    subst v
    obtain ⟨f,hf⟩ := Option.isSome_iff_exists.mp he
    have hp := M.update_refines op w.1 f hf z' hz'
    simpa only [Edge, hp] using hf

/-- Every actual trajectory edge is supported, simultaneously at all finite cuts. -/
private theorem marked_edges (M : Observer Z) (e : InstalledEmitter M) (w : Marked Z) :
    ∀ᵐ x ∂markedLaw M e w, ∀ n, Edge M (x n) (x (n+1)) := by
  apply ae_all_iff.mpr
  intro n
  have hv : ∀ᵐ v ∂(markedLaw M e w).map
      (fun x i => x (i : Fin (n+2))),
      Edge M (v ⟨n,by omega⟩) (v ⟨n+1,by omega⟩) := by
    apply ae_iff_of_countable.mpr
    intro v hmass
    rw [prefix_mass] at hmass
    have hp := (mul_ne_zero_iff.mp hmass).2
    have hedge : markedRow M e (v ⟨n,by omega⟩) (v ⟨n+1,by omega⟩) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hp) (Fin.last n) (Finset.mem_univ _)
    exact supported_edge M e _ _ hedge
  exact ae_of_ae_map (Measurable.aemeasurable (by fun_prop : Measurable
    (fun x : ℕ → Marked Z => fun i : Fin (n+2) => x i))) hv

private def shifted (x : ℕ → Marked Z) : ℕ → Marked Z := fun n => x (n+1)

/-- Only incoming real operations form the prefix. Padding terminates its finite output. -/
def operations (x : ℕ → Marked Z) : ℕ → Option (List Operation)
  | 0 => some []
  | n+1 => (x 1).2.bind fun op => (operations (shifted x) n).map (op :: ·)

@[fun_prop] private theorem operations_measurable (n : ℕ) :
    Measurable (fun x : ℕ → Marked Z => operations x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let f : Option Operation × Option (List Operation) → Option (List Operation) :=
      fun p => p.1.bind fun op => p.2.map (op :: ·)
    have hf : Measurable f := measurable_of_countable _
    exact hf.comp (((measurable_snd : Measurable (Prod.snd : Marked Z → Option Operation)).comp
      (measurable_pi_apply 1)).prodMk (ih.comp (by unfold shifted; fun_prop)))

/-- The decoder reads projected COMPLETE fields at the actual event coordinate. -/
def markedTranscript (M : Observer Z) (x : ℕ → Marked Z) : FullTranscript := fun n =>
  (operations x n).map fun ops =>
    (ops, M.project (x n).1, eventBlocks (M.project (x 0).1) ops)

@[fun_prop] private theorem markedTranscript_measurable (M : Observer Z) :
    Measurable (markedTranscript M) := by
  apply measurable_pi_lambda
  intro n
  let f : Option (List Operation) × Z × Z → FullOutput :=
    fun p => p.1.map fun ops => (ops,M.project p.2.1,eventBlocks (M.project p.2.2) ops)
  exact (measurable_of_countable f).comp ((operations_measurable n).prodMk
    (((measurable_fst : Measurable (Prod.fst : Marked Z → Z)).comp
      (measurable_pi_apply n)).prodMk
    ((measurable_fst : Measurable (Prod.fst : Marked Z → Z)).comp
      (measurable_pi_apply 0))))

private theorem next_of_edge (c : AcquiredNativeState) (ω : Stream) (op : Operation)
    (hf : (finiteStep c.source.finiteFields op).isSome)
    (hr : ∀ b, op = .read b → ω 0 = b) :
    ∃ d, nextNative c ω = some (op,d) ∧ nativeStep c op = some d := by
  have hn : nextOperation c ω = some op := by
    cases op with
    | read b =>
      have hb := hr b rfl
      cases hc : c.source.finiteFields.control with
      | seed a => simp [nextOperation,hc,hb]
      | early t s => simp [nextOperation,hc,hb]
      | fourth q =>
        cases q <;> simp_all [finiteStep,finiteRead,nextOperation]
    | stop b =>
      cases hc : c.source.finiteFields.control <;>
        simp [finiteStep,finiteStop,hc] at hf
      rename_i q
      cases q <;> simp [finiteStop] at hf
      rename_i a
      have ha : b = a := by simpa [finiteStop] using hf
      simp [nextOperation,hc,ha]
  have hs : (nativeStep c op).isSome := by
    have h := finite_projection_commutes c op
    rw [← h,Option.isSome_map] at hf
    exact hf
  obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨d,by simp [nextNative,hn,hd],hd⟩

private theorem stop_delivered (f f' : FiniteFields) (b : Letter)
    (hf : finiteStep f (.stop b) = some f') : f'.control = .fourth .delivered := by
  cases hc : f.control <;> simp [finiteStep,finiteStop,hc] at hf
  rename_i q
  cases q <;> simp [finiteStop] at hf
  obtain ⟨_,hh⟩ := hf
  rw [← hh]

/-- Complete literal realization of every coherent marked trajectory, without a completion premise. -/
theorem marked_native_realization (M : Observer Z) (x : ℕ → Marked Z)
    (hx : ∀ n, Edge M (x n) (x (n+1))) (c : AcquiredNativeState)
    (hc : c.source.finiteFields = M.project (x 0).1) :
    markedTranscript M x = fullTranscript c (rawFrom x) := by
  funext n
  induction n generalizing x c with
  | zero => simp [markedTranscript,operations,fullTranscript,nativeDrive,hc]
  | succ n ih =>
    have he := hx 0
    cases ha : (x 1).2 with
    | none =>
      have hd : c.source.finiteFields.control = .fourth .delivered := by
        exact (show (M.project (x 0).1).control = .fourth .delivered ∧
          (x 1).1 = (x 0).1 from by simpa [Edge,ha] using he).1 |> (fun h => hc ▸ h)
      simp [markedTranscript,operations,ha,fullTranscript,
        delivered_positive_none c hd]
    | some op =>
      have hf : finiteStep c.source.finiteFields op = some (M.project (x 1).1) := by
        simpa only [Edge,ha,← hc] using he
      obtain ⟨d,hn,hs⟩ := next_of_edge c (rawFrom x) op (by simp [hf]) (by
        intro b hb; subst op; simp [rawFrom,ha])
      have hdp : d.source.finiteFields = M.project (x 1).1 := by
        have h := finite_projection_commutes c op
        rw [hs,Option.map_some,hf] at h
        exact Option.some.inj h
      have hshift : ∀ j, Edge M (shifted x j) (shifted x (j+1)) := fun j => hx (j+1)
      cases op with
      | read b =>
        have hr : rawTail (rawFrom x) 1 = rawFrom (shifted x) := rfl
        have hi := ih (shifted x) hshift d hdp
        have hf' : finiteStep (M.project (x 0).1) (.read b) =
            some (M.project (x 1).1) := by simpa only [hc] using hf
        simp only [markedTranscript,operations,ha,Option.bind_some,
          fullTranscript,nativeDrive,hn,Option.bind_some,readCost,hr,
          Option.map_map,Function.comp_def] at hi ⊢
        cases hm : operations (shifted x) n <;>
          cases hn' : nativeDrive d (rawFrom (shifted x)) n <;>
          simp [markedTranscript,fullTranscript,hm,hn',shifted,hdp] at hi ⊢
        all_goals simp_all [eventBlocks,hf',hc,shifted]
      | stop b =>
        have hd : d.source.finiteFields.control = .fourth .delivered := by
          rw [hdp]; exact stop_delivered _ _ _ hf
        have hp : (M.project (x 1).1).control = .fourth .delivered := by rw [← hdp]; exact hd
        have he1 := hx 1
        have hn2 : (x 2).2 = none := by
          cases h2 : (x 2).2 with
          | none => rfl
          | some o =>
            have hbad : finiteStep (M.project (x 1).1) o = some (M.project (x 2).1) :=
              by simpa only [Edge,h2] using he1
            cases o <;> simp [finiteStep,finiteRead,finiteStop,hp] at hbad
        cases n with
        | zero => simp [markedTranscript,operations,ha,fullTranscript,nativeDrive,hn,
            eventBlocks,hf,hc,hdp,shifted]
        | succ n =>
          simp only [markedTranscript,operations,ha,shifted,hn2,Option.bind_none,
            Option.bind_some,Option.map_none,fullTranscript]
          rw [nativeDrive,hn]
          simp only [Option.bind_some,delivered_positive_none d hd,Option.map_none]

/-- Constructed from the actual marked fields and operations, including infinite trajectories. -/
def fullLaw (M : Observer Z) (e : InstalledEmitter M) (z : Z) : Measure FullTranscript :=
  (markedLaw M e (z,none)).map (markedTranscript M)

instance (M : Observer Z) (e : InstalledEmitter M) (z : Z) :
    IsProbabilityMeasure (fullLaw M e z) :=
  Measure.isProbabilityMeasure_map (markedTranscript_measurable M).aemeasurable

private theorem fullLaw_native (M : Observer Z) (e : InstalledEmitter M) (z : Z) :
    fullLaw M e z = nativeLaw M e z := by
  apply Measure.map_congr
  filter_upwards [marked_head M e (z,none),marked_edges M e (z,none)] with x h0 hx
  exact marked_native_realization M x hx _ (by simp [representative,h0])

private def tailValue (s : ActivePhase) (ω : Stream) : ValidTail s :=
  ⟨stoppedReadWord s ω, by
    cases h : stoppedReadWord s ω with
    | none => trivial
    | some w => exact ((stopped_word_fiber s ω w).mp h).2⟩

@[fun_prop] private theorem tailValue_measurable (s : ActivePhase) : Measurable (tailValue s) :=
  (measurable_stopped_read_word s).subtype_mk

/-- The fourth-segment law retains its unique infinite outcome and depends on the full configuration. -/
def tailLaw (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase) (z : Z) :
    Measure (ValidTail s) :=
  (markedLaw M e (z,none)).map (fun x => tailValue s (rawFrom x))

instance (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase) (z : Z) :
    IsProbabilityMeasure (tailLaw M e s z) :=
  Measure.isProbabilityMeasure_map ((tailValue_measurable s).comp rawFrom_measurable).aemeasurable

/-- The installed law is the literal full-record renderer of a configuration-only fourth tail. -/
theorem installed_configuration_identity (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (c : AcquiredNativeState)
    (hc : M.project z = c.source.finiteFields)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    fullLaw M e z = (tailLaw M e s z).map (fullRenderer c s) := by
  rw [fullLaw_native, nativeLaw, tailLaw,
    Measure.map_map (f := fun x : ℕ → Marked Z => tailValue s (rawFrom x))
      (g := fullRenderer c s) (measurable_of_countable _)
      ((tailValue_measurable s).comp rawFrom_measurable)]
  congr 1
  funext x
  have hf := full_fields_eq (representative (M.project z)) c (rawFrom x) hc
  exact hf.trans (full_renderer_all_paths c s hs (rawFrom x))

private theorem delivered_stream_eq (c : AcquiredNativeState)
    (hc : c.source.finiteFields.control = .fourth .delivered) (ω η : Stream) :
    fullTranscript c ω = fullTranscript c η := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [fullTranscript,delivered_positive_none c hc]

private theorem decode_first (M : Observer Z) (z : Z) (y : Marked Z) (q : Operation)
    (hy : y.2 = some q) (hf : finiteStep (M.project z) q = some (M.project y.1))
    (x : ℕ → Marked Z) (hx : x 0 = y) :
    (decode M z (prepend (z,none) x)) 0 = some ([],M.project z,[]) ∧
    (decode M z (prepend (z,none) x)) 1 =
      some ([q],M.project y.1,[eventBlock (M.project z) q]) ∧
    deleteBlock (decode M z (prepend (z,none) x)) = decode M y.1 x := by
  let c := representative (M.project z)
  let ω := rawFrom (prepend (z,none) x)
  obtain ⟨d,hn,hd⟩ := next_of_edge c ω q (by simp [c,representative,hf]) (by
    intro b hb; subst q; simp [ω,rawFrom,prepend,hx,hy])
  have hp : d.source.finiteFields = M.project y.1 := by
    have h := finite_projection_commutes c q
    rw [hd,Option.map_some] at h
    change some d.source.finiteFields = finiteStep (M.project z) q at h
    rw [hf] at h
    exact Option.some.inj h
  refine ⟨rfl,?_,?_⟩
  · change fullTranscript c ω 1 = _
    simp only [fullTranscript,nativeDrive,hn,Option.bind_some,Option.map_some]
    simp [hp,eventBlocks,c,representative,hf]
  · change deleteBlock (fullTranscript c ω) = _
    rw [full_delete_block c d ω q hn]
    rw [full_fields_eq d (representative (M.project y.1)) _ hp]
    cases q with
    | read b => rfl
    | stop b =>
      exact delivered_stream_eq _ (stop_delivered _ _ b hf) _ _

private theorem marked_some_mass (M : Observer Z) (e : InstalledEmitter M)
    (z z' : Z) (op : Operation) :
    markedRow M e (z,none) (z',some op) = e.emit z (some op) * M.update op z z' := by
  classical
  simp [markedRow,PMF.bind_apply,PMF.map_apply,PMF.pure_apply,Prod.mk.injEq,and_comm]
  have hi (q : Operation) :
      (∑ a : Z, if z' = a ∧ op = q then M.update q z a else 0) =
        if op = q then M.update q z z' else 0 := by
    by_cases h : op = q
    · simp only [h,and_true]
      rw [Finset.sum_eq_single z']
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · simp [h]
  simp_rw [hi]
  rw [Finset.sum_eq_single op]
  · simp
  · intro q _ hq; simp [Ne.symm hq]
  · simp

/-- Exact generation for arbitrary measurable full residual events, including zero emissions. -/
theorem installed_first_block_recursion (M : Observer Z) (e : InstalledEmitter M)
    (z : Z) (op : Operation) (f' : FiniteFields)
    (hf : finiteStep (M.project z) op = some f') (E : Set FullTranscript)
    (hE : MeasurableSet E) :
    fullLaw M e z (blockEvent (M.project z) f' op E) =
      e.emit z (some op) * ∑ z' : Z, M.update op z z' * fullLaw M e z' E := by
  classical
  let C := blockEvent (M.project z) f' op E
  have hC : MeasurableSet C := blockEvent_measurable _ _ _ E hE
  have hm (y : Marked Z) :
      markedRow M e (z,none) y *
        ((markedLaw M e y).map (decode M z ∘ prepend (z,none))) C =
      match y.2 with
      | none => 0
      | some q => if q = op then markedRow M e (z,none) y * nativeLaw M e y.1 E else 0 := by
    by_cases hzero : markedRow M e (z,none) y = 0
    · cases y.2 <;> simp [hzero]
    have hedge := supported_edge M e (z,none) y hzero
    rw [Measure.map_apply ((decode_measurable M z).comp (measurable_prepend _)) hC]
    cases hy : y.2 with
    | none =>
      have hd : (M.project z).control = .fourth .delivered :=
        (show (M.project z).control = .fourth .delivered ∧ y.1 = z from
          by simpa [Edge,hy] using hedge).1
      have hnull : (decode M z ∘ prepend (z,none)) ⁻¹' C = ∅ := by
        ext x
        simp [C,blockEvent,decode,fullTranscript,delivered_positive_none,
          representative,hd]
      rw [hnull,measure_empty,mul_zero]
    | some q =>
      have hq : finiteStep (M.project z) q = some (M.project y.1) :=
        by simpa [Edge,hy] using hedge
      have hmass : (markedLaw M e y) ((decode M z ∘ prepend (z,none)) ⁻¹' C) =
          if q = op then nativeLaw M e y.1 E else 0 := by
        by_cases hqo : q = op
        · subst q
          have hfields : M.project y.1 = f' := Option.some.inj (hq.symm.trans hf)
          rw [if_pos rfl,← decoded_mark_irrelevance M e y.1 y.2,
            Measure.map_apply (decode_measurable M y.1) hE]
          apply measure_congr
          filter_upwards [marked_head M e y] with x hx
          obtain ⟨ht0,ht1,htail⟩ := decode_first M z y op hy hq x hx
          apply propext
          change ((decode M z (prepend (z,none) x)) 0 = _ ∧
            (decode M z (prepend (z,none) x)) 1 = _ ∧
            deleteBlock (decode M z (prepend (z,none) x)) ∈ E) ↔
              decode M y.1 x ∈ E
          simp [ht0,ht1,hfields,htail]
        · rw [if_neg hqo]
          apply (ae_eq_empty.mp ?_)
          filter_upwards [marked_head M e y] with x hx
          obtain ⟨_,ht1,_⟩ := decode_first M z y q hy hq x hx
          apply propext
          change ((decode M z (prepend (z,none) x)) 0 = _ ∧
            (decode M z (prepend (z,none) x)) 1 = _ ∧
            deleteBlock (decode M z (prepend (z,none) x)) ∈ E) ↔ False
          simp [ht1,hqo]
      rw [hmass]
      by_cases h : q = op <;> simp [hy,h]
  simp_rw [fullLaw_native]
  rw [nativeLaw,marked_regenerate M e (z,none),
    Measure.map_finset_sum' (decode_measurable M z).aemeasurable]
  simp only [Measure.coe_finsetSum,Finset.sum_apply,Measure.map_smul,Measure.smul_apply,
    smul_eq_mul,Measure.map_map (decode_measurable M z) (measurable_prepend _)]
  change (∑ y : Marked Z, markedRow M e (z,none) y *
    ((markedLaw M e y).map (decode M z ∘ prepend (z,none))) C) = _
  rw [Finset.sum_congr rfl (fun y _ => hm y)]
  simp [Fintype.sum_prod_type,Fintype.sum_option,marked_some_mass,Finset.mul_sum,mul_assoc]

def terminalTranscript (f : FiniteFields) : FullTranscript
  | 0 => some ([],f,[])
  | _+1 => none

private theorem delivered_law (M : Observer Z) (e : InstalledEmitter M) (z : Z)
    (hz : (M.project z).control = .fourth .delivered) :
    fullLaw M e z = Measure.dirac (terminalTranscript (M.project z)) := by
  rw [fullLaw_native,nativeLaw]
  have he : decode M z = fun _ : ℕ → Marked Z => terminalTranscript (M.project z) := by
    funext x n
    cases n with
    | zero => rfl
    | succ n => simp [decode,fullTranscript,terminalTranscript,
        delivered_positive_none,representative,hz]
  rw [he,Measure.map_const]
  simp

private theorem pending_emission (M : Observer Z) (e : InstalledEmitter M) (z : Z)
    (b : Letter) (hz : (M.project z).control = .fourth (.pending b)) :
    e.emit z = PMF.pure (some (.stop b)) := by
  classical
  have only (a : Option Operation) (ha : a ∈ (e.emit z).support) :
      a = some (.stop b) := by
    have h := e.lawful z a ha
    cases a with
    | none => simp [hz] at h
    | some op =>
      cases op with
      | read d => simp [finiteStep,finiteRead,hz] at h
      | stop d =>
        have hd : d = b := by simpa [finiteStep,finiteStop,hz] using h
        simp [hd]
  have ha : some (.stop b) ∈ (e.emit z).support := by
    obtain ⟨a,ha⟩ := (e.emit z).support_nonempty
    simpa only [only a ha] using ha
  have hsupport : (e.emit z).support = {some (.stop b)} :=
    Set.ext fun a => ⟨fun h => only a h,fun h => h ▸ ha⟩
  have hm := (PMF.apply_eq_one_iff _ _).mpr hsupport
  apply PMF.ext
  intro a
  by_cases h : a = some (.stop b)
  · simp [h,hm]
  · have hzero : e.emit z a = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      simpa only [hsupport,Set.mem_singleton_iff] using h
    simp [h,hzero,PMF.pure_apply]

/-- Configuration-before-TV for the constructed installed full law over every original phase history. -/
def installedRisk (M : Observer Z) (e : InstalledEmitter M) (μ : PMF Depth)
    (s : ActivePhase) : ℝ≥0∞ :=
  ⨆ H : PhaseHistory s, ∑ z, row M H.val.1 z *
    D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
      (fullLaw M e z) (fullTarget M μ H.val.1 H.val.2)

private theorem history_risk (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) :
    installedRisk M e μ s = rawRisk M μ s (fun _ z => tailLaw M e s z) := by
  have ht := (native_history_risk_transport M μ s (fun _ z => tailLaw M e s z)).2
  rw [← ht]
  unfold installedRisk fullRisk
  congr 1
  funext H
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : row M H.val.1 z = 0
  · simp [hz]
  · rw [installed_configuration_identity M e s z H.val.2
      ((actual_row_refines M _ _ H.property.1).1 z hz) H.property.2]

/-- The installed law, literal all-path realization, arbitrary-event generation and original
    full-history risk transport belong to the same COMPLETE carrier and actual update rows. -/
theorem installed_full_law (M : Observer Z) (e : InstalledEmitter M) :
    (∀ z : Z, IsProbabilityMeasure (fullLaw M e z)) ∧
    (∀ z : Z, ∀ᵐ x ∂markedLaw M e (z,none),
      markedTranscript M x = fullTranscript (representative (M.project z)) (rawFrom x)) ∧
    (∀ (z : Z) (op : Operation) (f' : FiniteFields),
      finiteStep (M.project z) op = some f' →
      ∀ (E : Set FullTranscript), MeasurableSet E →
      fullLaw M e z (blockEvent (M.project z) f' op E) =
        e.emit z (some op) * ∑ z' : Z, M.update op z z' * fullLaw M e z' E) ∧
    (∀ (z : Z) (b : Letter), (M.project z).control = .fourth (.pending b) →
      e.emit z = PMF.pure (some (.stop b))) ∧
    (∀ z : Z, (M.project z).control = .fourth .delivered →
      fullLaw M e z = Measure.dirac (terminalTranscript (M.project z))) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase),
      installedRisk M e μ s = rawRisk M μ s (fun _ z => tailLaw M e s z)) := by
  refine ⟨fun _ => inferInstance,?_,installed_first_block_recursion M e,
    pending_emission M e,delivered_law M e,history_risk M e⟩
  intro z
  filter_upwards [marked_head M e (z,none),marked_edges M e (z,none)] with x h0 hx
  exact marked_native_realization M x hx _ (by simp [representative,h0])

#print axioms marked_native_realization
#print axioms installed_configuration_identity
#print axioms installed_first_block_recursion
#print axioms installed_full_law

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
