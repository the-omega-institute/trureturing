/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitReturnRestart
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitReturnRestart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Almost-sure finite variable-request service returns retain an independent unused suffix. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
open FiniteFairBitFirstReturn FiniteFairBitExitLaws

variable {S O : Type} [Fintype S] [Fintype O]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O]

local instance : MeasurableSpace (Option O) := ⊤
local instance : MeasurableSingletonClass (Option O) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => trivial⟩

def label : S ⊕ O → Option O
  | .inl _ => none
  | .inr o => some o

/-- A proof-side bounded return readout. No label or suffix is installed in S. -/
def bounded (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (ω : ℕ → Bool)
    (n : ℕ) : Option O × (ℕ → Bool) :=
  (label (path d a ω n), unused (stopped d) a ω n)

private theorem measurable_unused {X : Type} (d : X → Instruction X) (s : X) (n : ℕ) :
    Measurable (fun ω => unused d s ω n) := by
  induction n generalizing s with
  | zero => exact measurable_id
  | succ n ih =>
    cases h : d s with
    | deterministic t => simpa [unused,successor,h] using ih t
    | fair t u =>
      have ht : Measurable tail := by unfold tail; fun_prop
      have he : MeasurableSet {ω : ℕ → Bool | ω 0 = true} := by measurability
      have hh : (fun ω => unused d s ω (n+1)) =
          fun ω => if ω 0 then unused d u (tail ω) n else unused d t (tail ω) n := by
        funext ω
        simp only [unused,successor,h]
        split <;> rfl
      rw [hh]
      exact Measurable.ite he ((ih u).comp ht) ((ih t).comp ht)

private theorem bounded_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (n : ℕ) :
    Measurable (fun ω => bounded d a ω n) :=
  ((measurable_of_countable label).comp (measurable_run (stopped d) a n)).prodMk
    (measurable_unused (stopped d) a n)

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem unused_exit (d : S → Instruction (S ⊕ O)) (o : O)
    (ω : ℕ → Bool) (n : ℕ) : unused (stopped d) (.inr o) ω n = ω := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unused,stopped,successor] using ih

private theorem bounded_exit (d : S → Instruction (S ⊕ O)) (o : O)
    (ω : ℕ → Bool) (n : ℕ) : bounded d (.inr o) ω n = (some o,ω) := by
  simp [bounded,path_exit,unused_exit,label]

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem bounded_step (d : S → Instruction (S ⊕ O)) (s : S)
    (ω : ℕ → Bool) (n : ℕ) :
    bounded d (.inl s) ω (n+1) =
      bounded d (successor (d s) ω).1 (successor (d s) ω).2 n := rfl

private theorem bounded_stable_succ (d : S → Instruction (S ⊕ O))
    (a : S ⊕ O) (ω : ℕ → Bool) (n : ℕ) (h : (bounded d a ω n).1 ≠ none) :
    bounded d a ω (n+1) = bounded d a ω n := by
  induction n generalizing a ω with
  | zero =>
    cases a with
    | inl s => exact (h rfl).elim
    | inr o => rw [bounded_exit,bounded_exit]
  | succ n ih =>
    cases a with
    | inl s => rw [bounded_step] at h ⊢; rw [bounded_step]; exact ih _ _ h
    | inr o => rw [bounded_exit,bounded_exit]

private theorem bounded_stable (d : S → Instruction (S ⊕ O))
    (a : S ⊕ O) (ω : ℕ → Bool) {n m : ℕ} (hnm : n ≤ m)
    (h : (bounded d a ω n).1 ≠ none) : bounded d a ω m = bounded d a ω n := by
  induction m,hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [bounded_stable_succ d a ω m (by simpa [ih] using h),ih]

/-- The physical step bound is an analytical coordinate, not charged elapsed time. -/
def firstIndex (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (ω : ℕ → Bool) : Option ℕ :=
  if h : ∃ n, (bounded d a ω n).1 ≠ none then some (Nat.find h) else none

/-- The complete label and the actual unused suffix at first return.
    Nonreturn is totalized by none and the original tape on its null event. -/
def restart (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (ω : ℕ → Bool) :
    Option O × (ℕ → Bool) :=
  match firstIndex d a ω with
  | none => (none,ω)
  | some n => bounded d a ω n

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem first_index_some (d : S → Instruction (S ⊕ O))
    (a : S ⊕ O) (ω : ℕ → Bool) (n : ℕ) :
    firstIndex d a ω = some n ↔
      (bounded d a ω n).1 ≠ none ∧ ∀ k < n, (bounded d a ω k).1 = none := by
  constructor
  · intro hn
    unfold firstIndex at hn
    split at hn
    next h =>
      have he : Nat.find h = n := Option.some.inj hn
      exact ⟨he ▸ Nat.find_spec h,fun k hk => not_not.mp (Nat.find_min h (he ▸ hk))⟩
    next h => simp at hn
  · rintro ⟨hn,hp⟩
    have h : ∃ k, (bounded d a ω k).1 ≠ none := ⟨n,hn⟩
    have he : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn,by simpa using hp⟩
    simp [firstIndex,h,he]

private theorem first_index_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    Measurable (firstIndex d a) := by
  apply measurable_to_countable'
  intro v
  cases v with
  | some n =>
    have he : firstIndex d a ⁻¹' {some n} =
        {ω | (bounded d a ω n).1 ≠ none} ∩
          ⋂ k : Fin n, {ω | (bounded d a ω k).1 = none} := by
      ext ω
      simp only [mem_preimage,mem_singleton_iff,first_index_some,mem_inter_iff,mem_setOf_eq,mem_iInter]
      exact and_congr_right fun _ => ⟨fun h k => h k k.isLt,fun h k hk => h ⟨k,hk⟩⟩
    rw [he]
    exact ((bounded_measurable d a n).fst.eq_const none).setOf.compl.inter
      (MeasurableSet.iInter fun k => ((bounded_measurable d a k).fst.eq_const none).setOf)
  | none =>
    have he : firstIndex d a ⁻¹' {none} =
        ⋂ n, {ω | (bounded d a ω n).1 = none} := by
      ext ω; simp [firstIndex]
    rw [he]
    exact MeasurableSet.iInter fun n => ((bounded_measurable d a n).fst.eq_const none).setOf

private theorem restart_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    Measurable (restart d a) := by
  let f : Option ℕ × (ℕ → Bool) → Option O × (ℕ → Bool) := fun p =>
    match p.1 with
    | none => (none,p.2)
    | some n => bounded d a p.2 n
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro n
    cases n with
    | none => exact measurable_const.prodMk measurable_id
    | some n => exact bounded_measurable d a n
  exact hf.comp ((first_index_measurable d a).prodMk measurable_id)

private theorem restart_of_bounded (d : S → Instruction (S ⊕ O))
    (a : S ⊕ O) (ω : ℕ → Bool) (n : ℕ) (hn : (bounded d a ω n).1 ≠ none) :
    restart d a ω = bounded d a ω n := by
  have h : ∃ k, (bounded d a ω k).1 ≠ none := ⟨n,hn⟩
  simp only [restart,firstIndex,dif_pos h]
  exact (bounded_stable d a ω (Nat.find_min' h hn) (Nat.find_spec h)).symm

private theorem restart_some_iff (d : S → Instruction (S ⊕ O))
    (a : S ⊕ O) (ω : ℕ → Bool) (o : O) (E : Set (ℕ → Bool)) :
    (restart d a ω).1 = some o ∧ (restart d a ω).2 ∈ E ↔
      ∃ n, (bounded d a ω n).1 = some o ∧ (bounded d a ω n).2 ∈ E := by
  constructor
  · intro h
    unfold restart at h
    cases hi : firstIndex d a ω with
    | none => simp [hi] at h
    | some n => exact ⟨n,by simpa [hi] using h⟩
  · rintro ⟨n,hn,hE⟩
    rw [restart_of_bounded d a ω n (by simp [hn])]
    exact ⟨hn,hE⟩

private theorem bounded_factor (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (n : ℕ) (o : O) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    tapeLaw {ω | (bounded d a ω n).1 = some o ∧ (bounded d a ω n).2 ∈ E} =
      tapeLaw {ω | (bounded d a ω n).1 = some o} * tapeLaw E := by
  induction n generalizing a with
  | zero =>
    cases a with
    | inl s => simp [bounded,path,run,label]
    | inr p => by_cases hp : p=o <;> simp [bounded,path,run,label,unused,hp]
  | succ n ih =>
    cases a with
    | inr p => by_cases hp : p=o <;> simp [bounded_exit,hp]
    | inl s =>
      simp only [bounded_step]
      have hs := step_mass d s (fun z => {ω | (bounded d z ω n).1 = some o ∧
          (bounded d z ω n).2 ∈ E}) (fun z =>
          ((bounded_measurable d z n).fst.eq_const (some o)).setOf.inter
            (hE.preimage (bounded_measurable d z n).snd))
      simp only [Set.mem_ofPred_eq] at hs
      rw [hs]
      simp_rw [ih,← mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Set.mem_ofPred_eq] using
        (step_mass d s (fun z => {ω | (bounded d z ω n).1 = some o})
          (fun z => ((bounded_measurable d z n).fst.eq_const (some o)).setOf)).symm

private theorem bounded_mono (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (o : O) (E : Set (ℕ → Bool)) :
    Monotone (fun n => {ω | (bounded d a ω n).1 = some o ∧ (bounded d a ω n).2 ∈ E}) := by
  intro n m hnm ω hω
  change (bounded d a ω m).1 = some o ∧ (bounded d a ω m).2 ∈ E
  rw [bounded_stable d a ω hnm (by simp [hω.1])]
  exact hω

/-- Freshness at an arbitrary variable-request first return. Deterministic
    primitives consume no bits; both coincident fair alternatives consume one.
    The label can be the entire returned snapshot, without resetting it. -/
private theorem return_suffix_factorization (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (o : O) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    tapeLaw {ω | (restart d a ω).1 = some o ∧ (restart d a ω).2 ∈ E} =
      tapeLaw {ω | (restart d a ω).1 = some o} * tapeLaw E := by
  have hu (E : Set (ℕ → Bool)) :
      {ω | (restart d a ω).1 = some o ∧ (restart d a ω).2 ∈ E} =
        ⋃ n, {ω | (bounded d a ω n).1 = some o ∧ (bounded d a ω n).2 ∈ E} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    exact restart_some_iff d a ω o E
  have hh := hu univ
  simp only [mem_univ,and_true] at hh
  rw [hu E,(bounded_mono d a o E).measure_iUnion]
  simp_rw [bounded_factor d a _ o E hE]
  rw [← ENNReal.iSup_mul]
  congr 1
  have hm := (bounded_mono d a o univ).measure_iUnion (μ := tapeLaw)
  simp only [mem_univ,and_true] at hm
  rw [← hm,← hh]

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem label_some (x : S ⊕ O) (o : O) : label x = some o ↔ x = .inr o := by
  cases x <;> simp [label]

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem label_none (x : S ⊕ O) : label x = none ↔ ∃ s, x = .inl s := by
  cases x <;> simp [label]

private theorem restart_label (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (ω : ℕ → Bool) (o : O) : (restart d a ω).1 = some o ↔ ω ∈ exits d a o := by
  constructor
  · intro h
    have hn := (restart_some_iff d a ω o univ).mp ⟨h,mem_univ _⟩
    obtain ⟨n,hn,_⟩ := hn
    have hex : ∃ k, (bounded d a ω k).1 ≠ none := ⟨n,by simp [hn]⟩
    let m := Nat.find hex
    have hp : (bounded d a ω m).1 = some o := by
      have hmn : m ≤ n := Nat.find_min' hex (by simp [hn])
      have hs := bounded_stable d a ω (n := m) (m := n) hmn (Nat.find_spec hex)
      rw [← hs]
      exact hn
    refine Set.mem_iUnion.mpr ⟨m,⟨(label_some _ o).mp hp,?_⟩⟩
    intro k hk
    exact (label_none _).mp (not_not.mp (Nat.find_min hex hk))
  · intro h
    obtain ⟨n,hn,_⟩ := Set.mem_iUnion.mp h
    have hp : (bounded d a ω n).1 = some o := (label_some _ o).mpr hn
    rw [restart_of_bounded d a ω n (by simp [hp])]
    exact hp

private theorem restart_none (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (ω : ℕ → Bool) : (restart d a ω).1 = none ↔ ω ∈ never d a := by
  have hh : (restart d a ω).1 = none ↔ ¬ ∃ o, (restart d a ω).1 = some o := by
    cases (restart d a ω).1 <;> simp
  rw [hh]
  simp_rw [restart_label]
  rw [← Set.mem_iUnion,exits_partition]
  simp

/-- The genuine first-return label keeps every private field when O is the
    complete ready carrier. Its joint law uses this invocation's consumed
    prefix, without resetting a state or installing a reusable random tape. -/
theorem actual_return_restart (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (ha : tapeLaw (never d a) = 0) :
    Measurable (restart d a) ∧
    tapeLaw.map (restart d a) =
      (tapeLaw.map (fun ω => (restart d a ω).1)).prod tapeLaw ∧
    (∀ o, {ω | (restart d a ω).1 = some o} = exits d a o) ∧
    (∀ (ω : ℕ → Bool) (n : ℕ) (o : O), ω ∈ hit d a n o →
      restart d a ω = (some o,fun k => ω (k + requests (stopped d) a ω n))) := by
  refine ⟨restart_measurable d a,?_,fun o => Set.ext (fun ω => restart_label d a ω o),?_⟩
  · have hm := restart_measurable d a
    have hr (v : Option O) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
        tapeLaw {ω | (restart d a ω).1 = v ∧ (restart d a ω).2 ∈ E} =
          tapeLaw {ω | (restart d a ω).1 = v} * tapeLaw E := by
      cases v with
      | some o => exact return_suffix_factorization d a o E hE
      | none =>
        have hn : {ω | (restart d a ω).1 = none} = never d a :=
          Set.ext (fun ω => restart_none d a ω)
        have hz : tapeLaw {ω | (restart d a ω).1 = none ∧ (restart d a ω).2 ∈ E} = 0 := by
          apply measure_mono_null _ ha
          intro ω hω
          exact (restart_none d a ω).mp hω.1
        rw [hz,hn,ha,zero_mul]
    apply Measure.ext_prod
    intro U E hU hE
    rw [Measure.map_apply hm (hU.prod hE),Measure.prod_prod,
      Measure.map_apply hm.fst hU]
    have hu (E : Set (ℕ → Bool)) :
        (restart d a) ⁻¹' (U ×ˢ E) =
          ⋃ v : U, {ω | (restart d a ω).1 = v.val ∧ (restart d a ω).2 ∈ E} := by
      ext ω
      simp only [mem_preimage,mem_prod,mem_iUnion,mem_setOf_eq]
      constructor
      · intro h; exact ⟨⟨(restart d a ω).1,h.1⟩,rfl,h.2⟩
      · rintro ⟨v,hv,hE⟩; exact ⟨hv ▸ v.property,hE⟩
    have hd (E : Set (ℕ → Bool)) :
        Pairwise (fun v w : U => Disjoint
          {ω | (restart d a ω).1 = v.val ∧ (restart d a ω).2 ∈ E}
          {ω | (restart d a ω).1 = w.val ∧ (restart d a ω).2 ∈ E}) := by
      intro v w hvw
      rw [Set.disjoint_left]
      intro ω hv hw
      exact hvw (Subtype.ext (hv.1.symm.trans hw.1))
    have hmeas (v : U) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
        MeasurableSet {ω | (restart d a ω).1 = v.val ∧ (restart d a ω).2 ∈ E} :=
      (hm.fst.eq_const v.val).setOf.inter (hE.preimage hm.snd)
    have hu' := hu univ
    simp only [prod_univ,mem_univ,and_true] at hu'
    change (fun ω => (restart d a ω).1) ⁻¹' U =
      ⋃ v : U, {ω | (restart d a ω).1 = v.val} at hu'
    rw [hu E,measure_iUnion (hd E) (fun v => hmeas v E hE)]
    simp_rw [hr _ E hE]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [hu']
    simpa only [mem_univ,and_true] using (measure_iUnion (μ := tapeLaw) (hd univ)
      (fun v => hmeas v univ MeasurableSet.univ)).symm
  · intro ω n o hn
    have hp : (bounded d a ω n).1 = some o := (label_some _ o).mpr hn.1
    rw [restart_of_bounded d a ω n (by simp [hp])]
    apply Prod.ext
    · exact hp
    · funext k; exact unused_suffix (stopped d) a ω n k

/-- Repeated boundary-to-boundary invocations of one common graph. The output
    list and tape are analysis coordinates; the returned physical state itself
    is the next entrance. There is no state reset or runtime output archive. -/
def services (d : S → Instruction (S ⊕ O)) (entrance : O → S ⊕ O)
    (s : O) (ω : ℕ → Bool) : ℕ → Option (List O × (ℕ → Bool))
  | 0 => some ([],ω)
  | n+1 =>
    let r := restart d (entrance s) ω
    r.1.bind fun t => (services d entrance t r.2 n).map fun p => (t :: p.1,p.2)

private def serviceEvent (d : S → Instruction (S ⊕ O)) (entrance : O → S ⊕ O)
    (s : O) (w : List O) (E : Set (ℕ → Bool)) : Set (ℕ → Bool) :=
  {ω | ∃ σ ∈ E, services d entrance s ω w.length = some (w,σ)}

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem service_event_nil (d : S → Instruction (S ⊕ O))
    (entrance : O → S ⊕ O) (s : O)
    (E : Set (ℕ → Bool)) : serviceEvent d entrance s [] E = E := by
  ext ω; simp [serviceEvent,services]

omit [Fintype S] [Fintype O] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O] in
private theorem service_event_cons (d : S → Instruction (S ⊕ O))
    (entrance : O → S ⊕ O) (s t : O) (w : List O) (E : Set (ℕ → Bool)) :
    serviceEvent d entrance s (t :: w) E =
      restart d (entrance s) ⁻¹' ({some t} ×ˢ serviceEvent d entrance t w E) := by
  ext ω
  simp only [serviceEvent,List.length_cons,services,mem_preimage,mem_prod,mem_singleton_iff]
  constructor
  · rintro ⟨σ,hE,hs⟩
    obtain ⟨u,hu,hup⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp hup
    obtain ⟨hc,hσ⟩ := Prod.mk.inj he
    obtain ⟨hut,hpw⟩ := List.cons.inj hc
    subst u
    refine ⟨hu,σ,hE,?_⟩
    rw [hp]
    exact congrArg some (Prod.ext hpw hσ)
  · rintro ⟨hu,σ,hE,hs⟩
    exact ⟨σ,hE,Option.bind_eq_some_iff.mpr
      ⟨t,hu,Option.map_eq_some_iff.mpr ⟨(w,σ),hs,rfl⟩⟩⟩

private theorem service_event_measurable (d : S → Instruction (S ⊕ O))
    (entrance : O → S ⊕ O) (s : O) (w : List O)
    (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    MeasurableSet (serviceEvent d entrance s w E) := by
  induction w generalizing s with
  | nil => simpa only [service_event_nil] using hE
  | cons t w ih =>
    rw [service_event_cons]
    exact ((measurableSet_singleton _).prod (ih t)).preimage
      (restart_measurable d (entrance s))

def prefixMass (d : S → Instruction (S ⊕ O))
    (entrance : O → S ⊕ O) (s : O) : List O → ℝ≥0∞
  | [] => 1
  | t :: w => tapeLaw (exits d (entrance s) t) * prefixMass d entrance t w

/-- Finite complete-return prefixes have their actual ordered product law,
    and the suffix after the whole prefix remains fresh. A.s. service return
    is required at the stated entrances, with no worst-case time bound and
    no assertion that an entire infinite native future completes. -/
theorem repeated_service_prefix (d : S → Instruction (S ⊕ O))
    (entrance : O → S ⊕ O) (ha : ∀ s : O, tapeLaw (never d (entrance s)) = 0)
    (s : O) (w : List O)
    (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    tapeLaw {ω | ∃ σ ∈ E, services d entrance s ω w.length = some (w,σ)} =
      prefixMass d entrance s w * tapeLaw E := by
  change tapeLaw (serviceEvent d entrance s w E) = _
  induction w generalizing s with
  | nil => simp [service_event_nil,prefixMass]
  | cons t w ih =>
    obtain ⟨hm,hr,hlabel,_⟩ := actual_return_restart d (entrance s) (ha s)
    rw [service_event_cons,← Measure.map_apply hm
      ((measurableSet_singleton _).prod
        (service_event_measurable d entrance t w E hE)),hr,
      Measure.prod_prod,Measure.map_apply hm.fst (measurableSet_singleton _)]
    change tapeLaw {ω | (restart d (entrance s) ω).1 = some t} *
      tapeLaw (serviceEvent d entrance t w E) = _
    rw [hlabel t,ih]
    exact (mul_assoc _ _ _).symm

#print axioms actual_return_restart
#print axioms repeated_service_prefix

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
