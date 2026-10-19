/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual primitive exit events yield reachable transience and normalized renewal laws. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset Function
open scoped ENNReal BigOperators Matrix
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open FiniteFairBitFirstReturn

variable {S O : Type} [Fintype S] [Fintype O]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O]

instance : MeasurableSingletonClass (S ⊕ O) := by
  constructor
  intro x
  cases x with
  | inl s => simpa only [Set.image_singleton] using (measurableSet_inl_image (α := S) (β := O)).2 (measurableSet_singleton s)
  | inr o => simpa only [Set.image_singleton] using (measurableSet_inr_image (α := S) (β := O)).2 (measurableSet_singleton o)

/-- Labelled primitive results carry an actual next state and an optional edge observation. -/
def mapInstruction {A B : Type} (f : A → B) : Instruction A → Instruction B
  | .deterministic a => .deterministic (f a)
  | .fair a b => .fair (f a) (f b)

def cutTarget (z : S × Option O) : S ⊕ O :=
  match z.2 with
  | none => .inl z.1
  | some o => .inr o

def cut (d : S → Instruction (S × Option O)) (s : S) : Instruction (S ⊕ O) :=
  mapInstruction cutTarget (d s)

/-- First observation within a finite physical prefix; this is a proof-side readout. -/
def observed (d : S → Instruction (S × Option O)) (s : S) (ω : ℕ → Bool) : ℕ → Option O
  | 0 => none
  | n+1 =>
    let z := successor (d s) ω
    match z.1.2 with
    | some o => some o
    | none => observed d z.1.1 z.2 n

/-- Actual edge at time n, continuing the physical execution after observations. -/
def edgeEvent (d : S → Instruction (S × Option O)) (s : S) (ω : ℕ → Bool) : ℕ → Option O
  | 0 => (successor (d s) ω).1.2
  | n+1 =>
    let z := successor (d s) ω
    edgeEvent d z.1.1 z.2 n

private theorem mapped_successor {A B : Type} (f : A → B) (i : Instruction A)
    (ω : ℕ → Bool) :
    successor (mapInstruction f i) ω =
      (f (successor i ω).1,(successor i ω).2) := by
  cases i with
  | deterministic a => rfl
  | fair a b => cases h : ω 0 <;> simp [mapInstruction,successor,h]

/-- Exit labels are primitive edge observations. Terminal copies are analytical coordinates. -/
def stopped (d : S → Instruction (S ⊕ O)) : S ⊕ O → Instruction (S ⊕ O)
  | .inl s => d s
  | .inr o => .deterministic (.inr o)

def path (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (ω : ℕ → Bool) :=
  run (stopped d) a ω

def live (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (n : ℕ) : Set (ℕ → Bool) :=
  {ω | ∃ s, path d a ω n = .inl s}

def hit (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (n : ℕ) (o : O) : Set (ℕ → Bool) :=
  {ω | path d a ω n = .inr o ∧ ∀ k < n, ω ∈ live d a k}

def trajectoryHit (n : ℕ) (o : O) : Set (ℕ → S ⊕ O) :=
  {x | x n = .inr o ∧ ∀ k < n, ∃ s, x k = .inl s}

private theorem trajectory_hit_measurable (n : ℕ) (o : O) :
    MeasurableSet (trajectoryHit (S := S) n o) := by
  have hL (k : ℕ) : MeasurableSet {x : ℕ → S ⊕ O | ∃ s, x k = .inl s} := by
    have he : {x : ℕ → S ⊕ O | ∃ s, x k = .inl s} = ⋃ s : S, {x | x k = .inl s} := by
      ext x; simp
    rw [he]
    exact MeasurableSet.iUnion fun s => ((measurable_pi_apply k : Measurable (fun x : ℕ → S ⊕ O => x k)).eq_const (.inl s)).setOf
  have he : trajectoryHit (S := S) n o = {x | x n = .inr o} ∩
      ⋂ k : Fin n, {x : ℕ → S ⊕ O | ∃ s, x k = .inl s} := by
    ext x
    simp only [trajectoryHit,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · intro h; exact ⟨h.1,fun k => h.2 k k.isLt⟩
    · intro h; exact ⟨h.1,fun k hk => h.2 ⟨k,hk⟩⟩
  rw [he]
  exact ((measurable_pi_apply n).eq_const (.inr o)).setOf.inter
    (MeasurableSet.iInter fun (k : Fin n) => hL k)

def exits (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (o : O) : Set (ℕ → Bool) :=
  ⋃ n, hit d a n o

def never (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) : Set (ℕ → Bool) :=
  ⋂ n, live d a n

def T (d : S → Instruction (S ⊕ O)) : Matrix S S ℝ≥0∞ :=
  fun s t => row (stopped d) (.inl s) (.inl t)
def R (d : S → Instruction (S ⊕ O)) : Matrix S O ℝ≥0∞ :=
  fun s o => row (stopped d) (.inl s) (.inr o)
def Z (d : S → Instruction (S ⊕ O)) : Matrix S O ℝ≥0∞ :=
  fun s o => tapeLaw (exits d (.inl s) o)
def survival (d : S → Instruction (S ⊕ O)) (s : S) (n : ℕ) : ℝ≥0∞ :=
  tapeLaw (live d (.inl s) n)

theorem path_exit (d : S → Instruction (S ⊕ O)) (o : O)
    (ω : ℕ → Bool) (n : ℕ) : path d (.inr o) ω n = .inr o := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [path,run,stopped,successor] using ih

private theorem live_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (n : ℕ) :
    MeasurableSet (live d a n) := by
  have he : live d a n = ⋃ s, {ω | path d a ω n = .inl s} := by
    ext ω; simp [live]
  rw [he]
  exact MeasurableSet.iUnion fun s =>
    (measurable_run (stopped d) a n).eq_const (.inl s) |>.setOf

private theorem hit_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (n : ℕ) (o : O) : MeasurableSet (hit d a n o) := by
  have he : hit d a n o = {ω | path d a ω n = .inr o} ∩
      ⋂ k : Fin n, live d a k := by
    ext ω
    simp only [hit,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · intro h; exact ⟨h.1,fun k => h.2 k k.isLt⟩
    · intro h; exact ⟨h.1,fun k hk => h.2 ⟨k,hk⟩⟩
  rw [he]
  exact ((measurable_run (stopped d) a n).eq_const (.inr o)).setOf.inter
    (MeasurableSet.iInter fun k => live_measurable d a k)

private theorem exits_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (o : O) :
    MeasurableSet (exits d a o) :=
  MeasurableSet.iUnion fun n => hit_measurable d a n o

private theorem never_measurable (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    MeasurableSet (never d a) := MeasurableSet.iInter fun n => live_measurable d a n

/-- A first-step event is evaluated on exactly the unused variable-request suffix. -/
theorem step_mass (d : S → Instruction (S ⊕ O)) (s : S)
    (A : S ⊕ O → Set (ℕ → Bool)) (hA : ∀ z, MeasurableSet (A z)) :
    tapeLaw {ω | (successor (d s) ω).2 ∈ A (successor (d s) ω).1} =
      ∑ z, row (stopped d) (.inl s) z * tapeLaw (A z) := by
  cases hd : d s with
  | deterministic z => simp [hd,successor,row,stopped,PMF.pure_apply]
  | fair t u =>
    let E := ({false} ×ˢ A t) ∪ ({true} ×ˢ A u)
    have he : {ω : ℕ → Bool | (successor (Instruction.fair t u) ω).2 ∈
        A (successor (Instruction.fair t u) ω).1} =
        (fun ω => (ω 0,tail ω)) ⁻¹' E := by
      ext ω; cases h : ω 0 <;> simp [E,successor,h]
    rw [he,← Measure.map_apply (by unfold tail; fun_prop)
      (((measurableSet_singleton _).prod (hA t)).union
        ((measurableSet_singleton _).prod (hA u))),split_tape]
    have hj : Disjoint ({false} ×ˢ A t) ({true} ×ˢ A u) := by
      rw [Set.disjoint_left]
      rintro ⟨b,ω⟩ ⟨hb,_⟩ ⟨hb',_⟩
      simp only [mem_singleton_iff] at hb hb'
      exact Bool.false_ne_true (hb.symm.trans hb')
    rw [measure_union hj ((measurableSet_singleton _).prod (hA u)),
      Measure.prod_prod,Measure.prod_prod]
    have hf (b : Bool) : fairBit b = (1/2 : ℝ≥0∞) := by
      cases b <;> norm_num [fairBit,PMF.bernoulli_apply]
    simp [PMF.toMeasure_apply_singleton,hf,row,stopped,hd,add_mul,Finset.sum_add_distrib,add_comm]

private theorem never_succ (d : S → Instruction (S ⊕ O)) (s : S) :
    never d (.inl s) =
      {ω | (successor (d s) ω).2 ∈ never d (successor (d s) ω).1} := by
  ext ω
  simp only [never,Set.mem_iInter,Set.mem_setOf_eq]
  constructor
  · intro h n; exact h (n+1)
  · intro h n
    cases n with
    | zero => exact ⟨s,rfl⟩
    | succ n => exact h n

private theorem live_exit_empty (d : S → Instruction (S ⊕ O)) (o : O) (n : ℕ) :
    live d (.inr o) n = ∅ := by
  ext ω; simp [live,path_exit]

private theorem never_exit_empty (d : S → Instruction (S ⊕ O)) (o : O) :
    never d (.inr o) = ∅ := by
  ext ω; simp [never,live_exit_empty]

private theorem never_equation (d : S → Instruction (S ⊕ O)) (s : S) :
    tapeLaw (never d (.inl s)) = ∑ t, T d s t * tapeLaw (never d (.inl t)) := by
  rw [never_succ,step_mass d s _ (never_measurable d)]
  rw [Fintype.sum_sum_type]
  simp [T,never_exit_empty]

private theorem run_add {X : Type} (d : X → Instruction X) (a : X)
    (ω : ℕ → Bool) (n m : ℕ) :
    run d a ω (n+m) = run d (run d a ω n) (unused d a ω n) m := by
  induction n generalizing a ω with
  | zero => simp [run,unused]
  | succ n ih => simpa [Nat.succ_add,run,unused] using
      (ih (successor (d a) ω).1 (successor (d a) ω).2)

private theorem path_absorb (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (ω : ℕ → Bool) (n m : ℕ) (o : O) (h : path d a ω n = .inr o) :
    path d a ω (n+m) = .inr o := by
  change run (stopped d) a ω (n+m) = _
  rw [run_add,show run (stopped d) a ω n = .inr o from h]
  exact path_exit d o _ m

private theorem live_antitone (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    Antitone (live d a) := by
  intro n m hnm ω hm
  cases hn : path d a ω n with
  | inl s => exact ⟨s,hn⟩
  | inr o =>
    obtain ⟨t,ht⟩ := hm
    have he := path_absorb d a ω n (m-n) o hn
    rw [Nat.add_sub_of_le hnm,ht] at he
    cases he

private theorem hit_succ (d : S → Instruction (S ⊕ O)) (s : S) (n : ℕ) (o : O) :
    hit d (.inl s) (n+1) o =
      {ω | (successor (d s) ω).2 ∈ hit d (successor (d s) ω).1 n o} := by
  ext ω
  simp only [hit,Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h.1,fun k hk => h.2 (k+1) (Nat.succ_lt_succ hk)⟩
  · intro h
    refine ⟨h.1,?_⟩
    intro k hk
    cases k with
    | zero => exact ⟨s,rfl⟩
    | succ k => exact h.2 k (Nat.lt_of_succ_lt_succ hk)

private theorem hit_zero (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (o : O) :
    hit d a 0 o = if a = .inr o then univ else ∅ := by
  ext ω; simp [hit,path,run]

private theorem hit_exit_succ (d : S → Instruction (S ⊕ O)) (p o : O) (n : ℕ) :
    hit d (.inr p) (n+1) o = ∅ := by
  ext ω
  simp only [hit,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
  intro h
  have hh := h.2 0 (Nat.zero_lt_succ _)
  rw [live_exit_empty] at hh
  exact hh

private theorem hit_disjoint (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (i j : ℕ × O) (hij : i ≠ j) : Disjoint (hit d a i.1 i.2) (hit d a j.1 j.2) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  by_cases ht : i.1 = j.1
  · have hl : i.2 = j.2 := Sum.inr_injective (hi.1.symm.trans (ht ▸ hj.1))
    exact hij (Prod.ext ht hl)
  · rcases lt_or_gt_of_ne ht with hlt | hgt
    · obtain ⟨s,hs⟩ := hj.2 i.1 hlt
      rw [hi.1] at hs
      cases hs
    · obtain ⟨s,hs⟩ := hi.2 j.1 hgt
      rw [hj.1] at hs
      cases hs

private theorem internal_mass (d : S → Instruction (S ⊕ O)) (s t : S) (n : ℕ) :
    tapeLaw {ω | path d (.inl s) ω n = .inl t} = (T d ^ n) s t := by
  induction n generalizing s with
  | zero =>
    by_cases h : s=t
    · subst t; simp [path,run,Matrix.one_apply]
    · have hts : t ≠ s := Ne.symm h
      simp [path,run,Matrix.one_apply,h,hts]
  | succ n ih =>
    have he : {ω | path d (.inl s) ω (n+1) = .inl t} =
        {ω | (successor (d s) ω).2 ∈
          {v | path d (successor (d s) ω).1 v n = .inl t}} := rfl
    rw [he,step_mass d s (fun z => {ω | path d z ω n = .inl t})
      (fun z => ((measurable_run (stopped d) z n).eq_const (.inl t)).setOf),
      Fintype.sum_sum_type,pow_succ',Matrix.mul_apply]
    simp only [T,ih]
    have hz (o : O) : {ω | path d (.inr o) ω n = .inl t} = ∅ := by
      ext ω; simp [path_exit]
    simp [hz]

private theorem survival_matrix (d : S → Instruction (S ⊕ O)) (s : S) (n : ℕ) :
    survival d s n = ∑ t, (T d ^ n) s t := by
  have hj : Pairwise (fun t u : S => Disjoint {ω | path d (.inl s) ω n = .inl t} {ω | path d (.inl s) ω n = .inl u}) := by
    intro t u htu
    rw [Set.disjoint_left]
    intro ω ht hu
    exact htu (Sum.inl_injective (ht.symm.trans hu))
  have he : live d (.inl s) n = ⋃ t : S, {ω | path d (.inl s) ω n = .inl t} := by
    ext ω; simp [live]
  rw [survival,he,measure_iUnion hj (fun t =>
    ((measurable_run (stopped d) (.inl s) n).eq_const _).setOf),tsum_fintype]
  simp_rw [internal_mass]

private theorem first_exit_matrix (d : S → Instruction (S ⊕ O)) (s : S) (o : O) (n : ℕ) :
    tapeLaw (hit d (.inl s) (n+1) o) = ((T d ^ n) * R d) s o := by
  induction n generalizing s with
  | zero =>
    rw [hit_succ,step_mass d s _ (fun z => hit_measurable d z 0 o)]
    simp [hit_zero,R,Matrix.one_mul,apply_ite]
  | succ n ih =>
    rw [hit_succ,step_mass d s _ (fun z => hit_measurable d z (n+1) o),
      Fintype.sum_sum_type]
    simp only [ih,hit_exit_succ,measure_empty,mul_zero,Finset.sum_const_zero,add_zero]
    rw [pow_succ',Matrix.mul_assoc,Matrix.mul_apply]
    rfl

private theorem exits_succ (d : S → Instruction (S ⊕ O)) (s : S) (o : O) :
    exits d (.inl s) o =
      {ω | (successor (d s) ω).2 ∈ exits d (successor (d s) ω).1 o} := by
  ext ω
  simp only [exits,Set.mem_iUnion,Set.mem_setOf_eq]
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => rw [hit_zero] at hn; simpa using hn
    | succ n => exact ⟨n,by rw [hit_succ] at hn; exact hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by rw [hit_succ]; exact hn⟩

theorem exits_exit (d : S → Instruction (S ⊕ O)) (p o : O) :
    exits d (.inr p) o = if p=o then univ else ∅ := by
  ext ω
  simp only [exits,Set.mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => simpa [hit_zero] using hn
    | succ n => rw [hit_exit_succ] at hn; exact hn.elim
  · intro h
    exact ⟨0,by simpa [hit_zero] using h⟩

theorem exits_partition (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    (⋃ o, exits d a o) = (never d a)ᶜ := by
  ext ω
  simp only [exits,Set.mem_iUnion,never,Set.mem_compl_iff,Set.mem_iInter]
  constructor
  · rintro ⟨o,n,hn⟩ h
    obtain ⟨s,hs⟩ := h n
    rw [hn.1] at hs
    cases hs
  · intro h
    have hx : ∃ n, ω ∉ live d a n := not_forall.mp h
    let n := Nat.find hx
    have hn : ω ∉ live d a n := Nat.find_spec hx
    cases hp : path d a ω n with
    | inl s => exact (hn ⟨s,hp⟩).elim
    | inr o =>
      refine ⟨o,n,hp,?_⟩
      intro k hk
      exact not_not.mp (Nat.find_min hx hk)

private theorem exits_disjoint (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    Pairwise (fun o p => Disjoint (exits d a o) (exits d a p)) := by
  intro o p hop
  rw [Set.disjoint_left]
  intro ω ho hp
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ho
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hp
  exact Set.disjoint_left.mp (hit_disjoint d a (n,o) (m,p)
    (fun h => hop (congrArg Prod.snd h))) hn hm

private theorem path_law (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    tapeLaw.map (path d a) = instructionLaw (stopped d) a := by
  letI : IsProbabilityMeasure (instructionLaw (stopped d) a) := by
    dsimp [instructionLaw]; infer_instance
  have hm : Measurable (path d a) :=
    Measurable.of_eval (fun n => measurable_run (stopped d) a n)
  have hp (n : ℕ) :
      (tapeLaw.map (fun ω i => path d a ω (i : Fin (n+1)))) =
        (instructionLaw (stopped d) a).map (fun x i => x (i : Fin (n+1))) :=
    Measure.ext_of_singleton (execution_prefix_law (stopped d) a n)
  let P := fun I : Finset ℕ => (instructionLaw (stopped d) a).map I.restrict
  haveI (I : Finset ℕ) : IsFiniteMeasure (P I) := by
    dsimp [P]
    letI : IsProbabilityMeasure ((instructionLaw (stopped d) a).map I.restrict) :=
      inferInstance
    infer_instance
  apply IsProjectiveLimit.unique (P := P) ?_ (fun _ => rfl)
  intro I
  let n := I.sup id
  let f : (Fin (n+1) → S ⊕ O) → (I → S ⊕ O) :=
    fun w i => w ⟨i.val,Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hproj : f ∘ (fun (x : ℕ → S ⊕ O) (i : Fin (n+1)) => x i) = I.restrict := rfl
  have htape : f ∘ (fun ω (i : Fin (n+1)) => path d a ω i) = I.restrict ∘ path d a := rfl
  change (tapeLaw.map (path d a)).map I.restrict =
    (instructionLaw (stopped d) a).map I.restrict
  rw [Measure.map_map (by fun_prop) hm,← hproj,← Measure.map_map hf (by fun_prop),
    ← hp,Measure.map_map hf (by exact Measurable.of_eval (fun i =>
      measurable_run (stopped d) a i.val)),htape]
  rfl

private theorem cut_observed (d : S → Instruction (S × Option O)) (s : S)
    (ω : ℕ → Bool) (n : ℕ) (o : O) :
    path (cut d) (.inl s) ω n = .inr o ↔ observed d s ω n = some o := by
  induction n generalizing s ω with
  | zero => simp [path,run,observed]
  | succ n ih =>
    rw [observed,path,run,stopped,cut,mapped_successor]
    dsimp only
    cases he : (successor (d s) ω).1.2 with
    | none => simpa [cutTarget,he,path] using
        (ih (successor (d s) ω).1.1 (successor (d s) ω).2)
    | some p =>
      have hh := path_exit (cut d) p (successor (d s) ω).2 n
      change run (stopped (cut d)) (.inr p) (successor (d s) ω).2 n = .inr p at hh
      simp [cutTarget,he,hh]

private theorem observed_iff (d : S → Instruction (S × Option O)) (s : S)
    (ω : ℕ → Bool) (n : ℕ) (o : O) :
    observed d s ω n = some o ↔
      ∃ k < n, edgeEvent d s ω k = some o ∧ ∀ j < k, edgeEvent d s ω j = none := by
  induction n generalizing s ω with
  | zero => simp [observed]
  | succ n ih =>
    cases he : (successor (d s) ω).1.2 with
    | none =>
      simp only [observed,he]
      rw [ih]
      constructor
      · rintro ⟨k,hk,ho,hj⟩
        refine ⟨k+1,Nat.succ_lt_succ hk,ho,?_⟩
        intro j hjk
        cases j with
        | zero => exact he
        | succ j => exact hj j (Nat.lt_of_succ_lt_succ hjk)
      · rintro ⟨k,hk,ho,hj⟩
        cases k with
        | zero => simp [edgeEvent,he] at ho
        | succ k => exact ⟨k,Nat.lt_of_succ_lt_succ hk,ho,
            fun j hjk => hj (j+1) (Nat.succ_lt_succ hjk)⟩
    | some p =>
      simp only [observed,he,Option.some.injEq]
      constructor
      · intro h; subst p; exact ⟨0,Nat.zero_lt_succ _,he,by simp⟩
      · rintro ⟨k,hk,ho,hj⟩
        cases k with
        | zero => exact Option.some.inj (he.symm.trans ho)
        | succ k => have h0 := hj 0 (Nat.zero_lt_succ _); simp [edgeEvent,he] at h0

/-- The analytical cut detects the first actual primitive event; the physical trace continues. -/
theorem primitive_event_cut (d : S → Instruction (S × Option O)) (s : S)
    (ω : ℕ → Bool) (n : ℕ) (o : O) :
    path (cut d) (.inl s) ω n = .inr o ↔
      ∃ k < n, edgeEvent d s ω k = some o ∧ ∀ j < k, edgeEvent d s ω j = none := by
  rw [cut_observed,observed_iff]

/-- Exact exit events, with the entire exit label retained, and finite survival powers. -/
theorem finite_exit_laws (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) :
    tapeLaw.map (path d a) = instructionLaw (stopped d) a ∧
    (∀ n o, MeasurableSet (trajectoryHit (S := S) n o) ∧
      instructionLaw (stopped d) a (trajectoryHit n o) = tapeLaw (hit d a n o)) ∧
    (∀ n o, MeasurableSet (hit d a n o)) ∧
    Pairwise (fun i j : ℕ × O => Disjoint (hit d a i.1 i.2) (hit d a j.1 j.2)) ∧
    (∀ s t n, tapeLaw {ω | path d (.inl s) ω n = .inl t} = (T d ^ n) s t) ∧
    (∀ s n, survival d s n = ∑ t, (T d ^ n) s t) ∧
    (∀ s o n, tapeLaw (hit d (.inl s) (n+1) o) = ((T d ^ n) * R d) s o) ∧
    (∀ o, tapeLaw (hit d a 0 o) = if a = .inr o then 1 else 0) := by
  refine ⟨path_law d a,?_,hit_measurable d a,hit_disjoint d a,internal_mass d,survival_matrix d,
    first_exit_matrix d,fun o => by rw [hit_zero]; split <;> simp⟩
  intro n o
  refine ⟨trajectory_hit_measurable n o,?_⟩
  have hm : Measurable (path d a) :=
    Measurable.of_eval (fun n => measurable_run (stopped d) a n)
  rw [← path_law d a,Measure.map_apply hm (trajectory_hit_measurable n o)]
  rfl

/-- The renewal equation concerns actual event masses and needs no transience premise. -/
theorem actual_renewal (d : S → Instruction (S ⊕ O)) : Z d = R d + T d * Z d := by
  ext s o
  rw [Z,exits_succ,step_mass d s _ (fun z => exits_measurable d z o),Fintype.sum_sum_type]
  simp [exits_exit,Z,R,T,Matrix.add_apply,Matrix.mul_apply,add_comm,apply_ite]

/-- Common reachability uses all permitted entrances and strictly positive primitive edges. -/
inductive Reachable (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : S → Prop
  | entrance (s : S) (hs : Sum.inl s ∈ E) : Reachable d E s
  | step (s t : S) (hs : Reachable d E s) (hst : 0 < T d s t) : Reachable d E t

/-- Literal a.s. entry exit propagates to every positively reachable internal state. -/
theorem reachable_as_exit (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) (s : S) (hs : Reachable d E s) :
    tapeLaw (never d (.inl s)) = 0 := by
  induction hs with
  | entrance s h => exact hE _ h
  | step s t hs hp ih =>
    rw [never_equation] at ih
    have hb : T d s t * tapeLaw (never d (.inl t)) ≤
        ∑ x, T d s x * tapeLaw (never d (.inl x)) :=
      Finset.single_le_sum (f := fun x => T d s x * tapeLaw (never d (.inl x)))
        (fun x _ => bot_le) (Finset.mem_univ t)
    rw [ih] at hb
    have hz : T d s t * tapeLaw (never d (.inl t)) = 0 :=
      le_antisymm hb (bot_le)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)

private theorem survival_add (d : S → Instruction (S ⊕ O)) (s : S) (n m : ℕ) :
    survival d s (n+m) = ∑ t, (T d ^ n) s t * survival d t m := by
  simp_rw [survival_matrix,pow_add,Matrix.mul_apply,Finset.mul_sum]
  exact Finset.sum_comm

private theorem unreachable_zero (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (s t : S) (hs : Reachable d E s) (ht : ¬ Reachable d E t) (n : ℕ) :
    (T d ^ n) s t = 0 := by
  induction n generalizing s with
  | zero =>
    have hst : s ≠ t := fun h => ht (h ▸ hs)
    simp [Matrix.one_apply,hst]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hup : Reachable d E u
    · rw [ih u hup,mul_zero]
    · have hz : T d s u = 0 := by
        by_contra hn
        exact hup (.step s u hs (pos_iff_ne_zero.mpr hn))
      rw [hz,zero_mul]

private theorem survival_limit (d : S → Instruction (S ⊕ O)) (s : S)
    (hs : tapeLaw (never d (.inl s)) = 0) :
    Filter.Tendsto (survival d s) Filter.atTop (nhds 0) := by
  have h := tendsto_measure_iInter_atTop (μ := tapeLaw)
    (fun n => (live_measurable d (.inl s) n).nullMeasurableSet)
    (live_antitone d (.inl s)) ⟨0,measure_ne_top _ _⟩
  change Filter.Tendsto (survival d s) Filter.atTop
    (nhds (tapeLaw (never d (.inl s)))) at h
  rwa [hs] at h

/-- One common escape block is derived across the common graph of all permitted entrances. -/
theorem reachable_escape (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) :
    ∃ L : ℕ, 0 < L ∧
      (∀ s, Reachable d E s → survival d s L ≤ (1/2 : ℝ≥0∞)) ∧
      (∀ s, Reachable d E s → ∀ n, survival d s (n*L) ≤ (1/2 : ℝ≥0∞)^n) ∧
      (∀ s, Reachable d E s → Filter.Tendsto (survival d s) Filter.atTop (nhds 0)) ∧
      (∀ s t, Reachable d E s → ¬ Reachable d E t → ∀ n, (T d ^ n) s t = 0) := by
  have hlim (s : S) (hs : Reachable d E s) :=
    survival_limit d s (reachable_as_exit d E hE s hs)
  have he (s : {s : S | Reachable d E s}) :
      ∃ N : ℕ, ∀ n ≥ N, survival d s.val n < (1/2 : ℝ≥0∞) := by
    have hh : ∀ᶠ n in Filter.atTop, survival d s.val n < (1/2 : ℝ≥0∞) :=
      (Filter.Tendsto.eventually_lt_const (by norm_num) (hlim s.val s.property))
    exact Filter.eventually_atTop.mp hh
  choose N hN using he
  let L := 1 + Finset.univ.sup N
  have hblock (s : S) (hs : Reachable d E s) : survival d s L ≤ (1/2 : ℝ≥0∞) := by
    apply le_of_lt (hN ⟨s,hs⟩ L _)
    exact le_trans (Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ (⟨s,hs⟩ : {s : S | Reachable d E s})))
      (by dsimp [L]; omega)
  refine ⟨L,by dsimp [L]; omega,hblock,?_,hlim,fun s t hs ht n => unreachable_zero d E s t hs ht n⟩
  intro s hs n
  induction n with
  | zero => simp [survival,live,path,run]
  | succ n ih =>
    rw [Nat.succ_mul,survival_add]
    calc
      ∑ t, (T d ^ (n*L)) s t * survival d t L
          ≤ ∑ t, (T d ^ (n*L)) s t * (1/2 : ℝ≥0∞) := by
            apply Finset.sum_le_sum
            intro t ht
            by_cases hr : Reachable d E t
            · exact mul_le_mul le_rfl (hblock t hr) bot_le bot_le
            · rw [unreachable_zero d E s t hs hr]
              simp
      _ = survival d s (n*L) * (1/2 : ℝ≥0∞) := by
            rw [survival_matrix,Finset.sum_mul]
      _ ≤ (1/2 : ℝ≥0∞)^n * (1/2 : ℝ≥0∞) := mul_le_mul ih le_rfl bot_le bot_le
      _ = (1/2 : ℝ≥0∞)^(n+1) := (pow_succ _ _).symm

private theorem total_exit_mass (d : S → Instruction (S ⊕ O)) (a : S ⊕ O)
    (ha : tapeLaw (never d a) = 0) : (∑ o, tapeLaw (exits d a o)) = 1 := by
  have hsum : (∑ o, tapeLaw (exits d a o)) = tapeLaw (⋃ o, exits d a o) := by
    calc
      _ = ∑' o : O, tapeLaw (exits d a o) := (tsum_fintype _).symm
      _ = _ := (measure_iUnion (μ := tapeLaw) (exits_disjoint d a)
        (exits_measurable d a)).symm
  rw [hsum,exits_partition,measure_compl (never_measurable d a)
    (measure_ne_top _ _),ha,measure_univ]
  simp

/-- Normalization holds at every permitted entrance, including immediate exits, and throughout its graph. -/
theorem normalized_reachable_exits (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) :
    (∀ a ∈ E, (∑ o, tapeLaw (exits d a o)) = 1) ∧
    (∀ s, Reachable d E s → (∑ o, Z d s o) = 1) := by
  exact ⟨fun a ha => total_exit_mass d a (hE a ha),
    fun s hs => total_exit_mass d (.inl s) (reachable_as_exit d E hE s hs)⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
