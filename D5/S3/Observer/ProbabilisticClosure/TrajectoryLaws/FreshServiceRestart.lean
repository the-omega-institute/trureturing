/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First acceptance leaves an independent untouched iid suffix. -/

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

variable {A : Type*} [MeasurableSpace A]

local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => trivial⟩

/-- The index is an external execution coordinate, not a retained service register. -/
def firstHit (accept : Set A) (ω : ℕ → A) : Option ℕ :=
  if h : ∃ n, ω n ∈ accept then some (Nat.find h) else none

def shift (n : ℕ) (ω : ℕ → A) : ℕ → A := fun i => ω (i+n)

/-- The fallback only totalizes the null nonreturn event. -/
def restart (accept : Set A) (fallback : A) (ω : ℕ → A) : A × (ℕ → A) :=
  match firstHit accept ω with
  | none => (fallback,ω)
  | some n => (ω n,shift (n+1) ω)

private def hitEvent (accept output : Set A) (n : ℕ) : Set (ℕ → A) :=
  Set.pi (Finset.range (n+1)) (fun i => if i = n then accept ∩ output else acceptᶜ)

theorem first_hit_some (accept : Set A) (ω : ℕ → A) (n : ℕ) :
    firstHit accept ω = some n ↔ ω n ∈ accept ∧ ∀ i < n, ω i ∉ accept := by
  constructor
  · intro hn
    unfold firstHit at hn
    split at hn
    next h =>
      have he : Nat.find h = n := Option.some.inj hn
      exact ⟨he ▸ Nat.find_spec h,fun i hi => Nat.find_min h (he ▸ hi)⟩
    next h => simp at hn
  · rintro ⟨hn,hp⟩
    have h : ∃ i, ω i ∈ accept := ⟨n,hn⟩
    have he : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn,hp⟩
    simp [firstHit,h,he]

private theorem hit_event_iff (accept output : Set A) (n : ℕ) (ω : ℕ → A) :
    ω ∈ hitEvent accept output n ↔ firstHit accept ω = some n ∧ ω n ∈ output := by
  constructor
  · intro h
    have hn : ω n ∈ accept ∩ output := by
      simpa [hitEvent] using h n (Finset.mem_range.mpr (by omega))
    refine ⟨(first_hit_some accept ω n).mpr ⟨hn.1,?_⟩,hn.2⟩
    intro i hi
    have hh := h i (Finset.mem_range.mpr (by omega))
    simpa [hitEvent,show i ≠ n by omega] using hh
  · rintro ⟨hn,ho⟩ i hi
    obtain ⟨ha,hp⟩ := (first_hit_some accept ω n).mp hn
    by_cases he : i = n
    · subst i; simpa [hitEvent] using And.intro ha ho
    · have hil : i < n := by have := Finset.mem_range.mp hi; omega
      simpa [hitEvent,he] using hp i hil

private theorem hit_event_measurable (accept output : Set A) (n : ℕ)
    (ha : MeasurableSet accept) (ho : MeasurableSet output) :
    MeasurableSet (hitEvent accept output n) :=
  MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => by
    split
    · exact ha.inter ho
    · exact ha.compl)

private theorem first_hit_measurable (accept : Set A) (ha : MeasurableSet accept) :
    Measurable (firstHit accept) := by
  apply measurable_to_countable'
  intro v
  cases v with
  | some n =>
    have he : firstHit accept ⁻¹' {some n} = hitEvent accept univ n := by
      ext ω; simp [hit_event_iff]
    rw [he]
    exact hit_event_measurable accept univ n ha MeasurableSet.univ
  | none =>
    have he : firstHit accept ⁻¹' {none} = (⋃ n, hitEvent accept univ n)ᶜ := by
      ext ω
      simp only [mem_preimage,mem_singleton_iff,mem_compl_iff,mem_iUnion,
        hit_event_iff,mem_univ,and_true,not_exists]
      cases firstHit accept ω <;> simp
    rw [he]
    exact (MeasurableSet.iUnion fun n =>
      hit_event_measurable accept univ n ha MeasurableSet.univ).compl

private theorem restart_measurable (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) : Measurable (restart accept fallback) := by
  let f : Option ℕ × (ℕ → A) → A × (ℕ → A) := fun p =>
    match p.1 with
    | none => (fallback,p.2)
    | some n => (p.2 n,shift (n+1) p.2)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro n
    cases n with
    | none => exact measurable_const.prodMk measurable_id
    | some n =>
      exact (measurable_pi_apply n).prodMk
        (show Measurable (shift (n+1)) from by unfold shift; fun_prop)
  exact hf.comp ((first_hit_measurable accept ha).prodMk measurable_id)

private theorem prefix_suffix_independent (μ : Measure A) [IsProbabilityMeasure μ]
    (n : ℕ) (S : Set (Fin n → A)) (hS : MeasurableSet S)
    (T : Set (ℕ → A)) (hT : MeasurableSet T) :
    (Measure.infinitePi (fun _ : ℕ => μ))
      ((fun ω : ℕ → A => fun i : Fin n => ω i.val) ⁻¹' S ∩ (shift n) ⁻¹' T) =
      (Measure.infinitePi (fun _ : ℕ => μ))
        ((fun ω : ℕ → A => fun i : Fin n => ω i.val) ⁻¹' S) *
      (Measure.infinitePi (fun _ : ℕ => μ)) T := by
  let m : ℕ → MeasurableSpace (ℕ → A) := fun i =>
    MeasurableSpace.comap (fun ω : ℕ → A => ω i) inferInstance
  let below : MeasurableSpace (ℕ → A) := ⨆ i ∈ {i : ℕ | i < n}, m i
  let above : MeasurableSpace (ℕ → A) := ⨆ i ∈ {i : ℕ | n ≤ i}, m i
  have hind : iIndep m (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (x : A) => x) (by fun_prop)
  have hd : Disjoint {i : ℕ | i < n} {i : ℕ | n ≤ i} := by
    rw [Set.disjoint_left]
    intro i hi hj
    exact Nat.not_lt_of_ge hj hi
  have hi : Indep below above (Measure.infinitePi (fun _ : ℕ => μ)) :=
    indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind hd
  have hp : @Measurable (ℕ → A) (Fin n → A) below MeasurableSpace.pi
      (fun ω i => ω i.val) := by
    apply (@measurable_pi_lambda (ℕ → A) (Fin n) (fun _ => A) below
      (fun _ => inferInstance))
    intro i
    apply measurable_iff_comap_le.mpr
    change m i.val ≤ below
    exact le_iSup_of_le i.val (le_iSup_of_le i.isLt le_rfl)
  have ht : @Measurable (ℕ → A) (ℕ → A) above MeasurableSpace.pi (shift n) := by
    apply (@measurable_pi_lambda (ℕ → A) ℕ (fun _ => A) above
      (fun _ => inferInstance))
    intro i
    apply measurable_iff_comap_le.mpr
    change m (i+n) ≤ above
    exact le_iSup_of_le (i+n) (le_iSup_of_le (show n ≤ i+n by omega) le_rfl)
  have he : (Measure.infinitePi (fun _ : ℕ => μ))
      ((fun ω : ℕ → A => fun i : Fin n => ω i.val) ⁻¹' S ∩ (shift n) ⁻¹' T) =
      (Measure.infinitePi (fun _ : ℕ => μ))
        ((fun ω : ℕ → A => fun i : Fin n => ω i.val) ⁻¹' S) *
      (Measure.infinitePi (fun _ : ℕ => μ)) ((shift n) ⁻¹' T) :=
    (@Indep.indepSet_of_measurableSet (ℕ → A) below above MeasurableSpace.pi
      (Measure.infinitePi (fun _ : ℕ => μ)) hi _ _
      (show MeasurableSet[below] ((fun ω : ℕ → A => fun i : Fin n => ω i.val) ⁻¹' S)
        from hp hS)
      (show MeasurableSet[above] ((shift n) ⁻¹' T) from ht hT)).measure_inter_eq_mul
  have hs : @Measure.map (ℕ → A) (ℕ → A) MeasurableSpace.pi MeasurableSpace.pi
      (shift n) (Measure.infinitePi (fun _ : ℕ => μ)) =
      Measure.infinitePi (fun _ : ℕ => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (f := fun i => i+n)
      (fun i j h => Nat.add_right_cancel h)
  rw [← Measure.map_apply (by unfold shift; fun_prop) hT,hs] at he
  exact he

private theorem hit_tail_mass (μ : Measure A) [IsProbabilityMeasure μ]
    (accept output : Set A) (ha : MeasurableSet accept) (ho : MeasurableSet output)
    (n : ℕ) (T : Set (ℕ → A)) (hT : MeasurableSet T) :
    (Measure.infinitePi (fun _ : ℕ => μ))
      (hitEvent accept output n ∩ (shift (n+1)) ⁻¹' T) =
      (μ acceptᶜ)^n * μ (accept ∩ output) *
        (Measure.infinitePi (fun _ : ℕ => μ)) T := by
  let S : Set (Fin (n+1) → A) :=
    Set.univ.pi (fun i => if i.val = n then accept ∩ output else acceptᶜ)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun i => by
    split
    · exact ha.inter ho
    · exact ha.compl
  have he : hitEvent accept output n =
      (fun ω : ℕ → A => fun i : Fin (n+1) => ω i.val) ⁻¹' S := by
    ext ω
    simp only [hitEvent,S,Set.mem_pi,Finset.mem_coe,Finset.mem_range,mem_preimage,
      mem_univ,true_implies,Subtype.forall]
    exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩
  rw [he,prefix_suffix_independent μ (n+1) S hS T hT,← he]
  congr 1
  rw [hitEvent,Measure.infinitePi_pi _ (fun i hi => by
    split
    · exact ha.inter ho
    · exact ha.compl),Finset.prod_range_succ]
  have hp : (∏ i ∈ Finset.range n,
      μ (if i = n then accept ∩ output else acceptᶜ)) = (μ acceptᶜ)^n := by
    calc
      _ = ∏ _i ∈ Finset.range n, μ acceptᶜ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
      _ = _ := by simp
  rw [hp]
  simp

private theorem nonreturn_null (μ : Measure A) [IsProbabilityMeasure μ]
    (accept : Set A) (ha : MeasurableSet accept) (hpos : μ accept ≠ 0) :
    (Measure.infinitePi (fun _ : ℕ => μ)) {ω | firstHit accept ω = none} = 0 := by
  let S : ℕ → Set (ℕ → A) := fun n => Set.pi (Finset.range n) (fun _ => acceptᶜ)
  have he : {ω | firstHit accept ω = none} = ⋂ n, S n := by
    ext ω
    simp only [mem_setOf_eq,mem_iInter,S,Set.mem_pi,Finset.mem_coe,Finset.mem_range,
      mem_compl_iff]
    constructor
    · intro hn n i hi
      unfold firstHit at hn
      split at hn
      · simp at hn
      next h => exact fun ha => h ⟨i,ha⟩
    · intro h
      have hn : ¬∃ i, ω i ∈ accept := by
        rintro ⟨i,hi⟩; exact h (i+1) i (by omega) hi
      simp [firstHit,hn]
  have hm : Antitone S := by
    intro i j hij ω hj k hk
    exact hj k (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hij))
  have hs (n : ℕ) : MeasurableSet (S n) :=
    MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => ha.compl)
  have hp (n : ℕ) : (Measure.infinitePi (fun _ : ℕ => μ)) (S n) = (μ acceptᶜ)^n := by
    change (Measure.infinitePi (fun _ : ℕ => μ))
      (Set.pi (Finset.range n) (fun _ => acceptᶜ)) = _
    rw [Measure.infinitePi_pi _ (fun _ _ => ha.compl)]
    simp
  have hlt : μ acceptᶜ < 1 := by
    rw [prob_compl_eq_one_sub ha]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top (by simp) hpos
  have hz : Tendsto (fun n => (Measure.infinitePi (fun _ : ℕ => μ)) (S n))
      atTop (𝓝 0) := by
    simp only [hp]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  rw [he]
  exact tendsto_nhds_unique
    (tendsto_measure_iInter_atTop (fun n => (hs n).nullMeasurableSet) hm
      ⟨0,measure_ne_top _ _⟩) hz

/-- The accepted value and the complete unused suffix are independent. The source
    is one iid stream; no bound on the number of consumed candidates is assumed. -/
theorem first_acceptance_restart (μ : Measure A) [IsProbabilityMeasure μ]
    (accept : Set A) (fallback : A) (ha : MeasurableSet accept) (hpos : μ accept ≠ 0) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (restart accept fallback) =
      (ProbabilityTheory.cond μ accept).prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  have hm := restart_measurable accept fallback ha
  haveI : IsProbabilityMeasure (ν.map (restart accept fallback)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_prod
  intro U T hU hT
  rw [Measure.map_apply hm (hU.prod hT),Measure.prod_prod,
    ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply hU]
  simp only [smul_eq_mul]
  let E (n : ℕ) := hitEvent accept U n ∩ (shift (n+1)) ⁻¹' T
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (hit_event_measurable accept U n ha hU).inter (hT.preimage (by unfold shift; fun_prop))
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    have h1 := ((hit_event_iff accept U i ω).mp hi.1).1
    have h2 := ((hit_event_iff accept U j ω).mp hj.1).1
    exact hij (Option.some.inj (h1.symm.trans h2))
  have he : (restart accept fallback) ⁻¹' (U ×ˢ T) =ᵐ[ν] ⋃ n, E n := by
    have hn : ∀ᵐ ω ∂ν, firstHit accept ω ≠ none := by
      rw [ae_iff]
      simpa only [not_not,ν] using nonreturn_null μ accept ha hpos
    filter_upwards [hn] with ω hω
    cases hh : firstHit accept ω with
    | none => exact (hω hh).elim
    | some n =>
      apply propext
      change ω ∈ (restart accept fallback) ⁻¹' (U ×ˢ T) ↔ ω ∈ ⋃ n, E n
      simp only [mem_preimage,restart,hh,mem_prod,mem_iUnion,E,mem_inter_iff,
        hit_event_iff]
      constructor
      · intro h; exact ⟨n,⟨⟨rfl,h.1⟩,h.2⟩⟩
      · rintro ⟨j,⟨⟨hj,ho⟩,ht⟩⟩
        have hjn : j = n := (Option.some.inj hj).symm
        subst j
        exact ⟨ho,ht⟩
  rw [measure_congr he,measure_iUnion hd hE]
  dsimp only [ν]
  simp_rw [E,hit_tail_mass μ accept U ha hU _ T hT]
  rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right,ENNReal.tsum_geometric,
    prob_compl_eq_one_sub ha,ENNReal.sub_sub_cancel ENNReal.one_ne_top
      (prob_le_one (μ := μ))]
  rw [Set.inter_comm U accept]

/-- Only the semantic analysis retains an unused suffix. The service receives
    its coordinates one at a time and never reads an earlier coordinate. -/
def unused (accept : Set A) (fallback : A) : ℕ → (ℕ → A) → (ℕ → A)
  | 0, ω => ω
  | n+1, ω => unused accept fallback n (restart accept fallback ω).2

def draws (accept : Set A) (fallback : A) (ω : ℕ → A) (n : ℕ) : A :=
  (restart accept fallback (unused accept fallback n ω)).1

private theorem unused_measurable (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) (n : ℕ) : Measurable (unused accept fallback n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp ((restart_measurable accept fallback ha).snd)

private theorem draws_measurable (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) : Measurable (draws accept fallback) := by
  apply measurable_pi_lambda
  intro n
  exact (restart_measurable accept fallback ha).fst.comp
    (unused_measurable accept fallback ha n)

private theorem unused_preserves (μ : Measure A) [IsProbabilityMeasure μ]
    (accept : Set A) (fallback : A) (ha : MeasurableSet accept)
    (hpos : μ accept ≠ 0) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (unused accept fallback n) =
      Measure.infinitePi (fun _ : ℕ => μ) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ accept) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  have hs : (Measure.infinitePi (fun _ : ℕ => μ)).map
      (fun ω => (restart accept fallback ω).2) = Measure.infinitePi (fun _ : ℕ => μ) := by
    change (Measure.infinitePi (fun _ : ℕ => μ)).map
      (Prod.snd ∘ restart accept fallback) = _
    rw [← Measure.map_map measurable_snd (restart_measurable accept fallback ha),
      first_acceptance_restart μ accept fallback ha hpos,Measure.map_snd_prod]
    simp
  induction n with
  | zero => simp [unused]
  | succ n ih =>
    change (Measure.infinitePi (fun _ : ℕ => μ)).map
      ((unused accept fallback n) ∘ (fun ω => (restart accept fallback ω).2)) = _
    rw [← Measure.map_map (unused_measurable accept fallback ha n)
      (restart_measurable accept fallback ha).snd,hs,ih]

private theorem drawn_prefix_mass [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure A) [IsProbabilityMeasure μ] (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) (hpos : μ accept ≠ 0) (n : ℕ) (v : Fin n → A) :
    (Measure.infinitePi (fun _ : ℕ => μ))
      {ω | ∀ i : Fin n, draws accept fallback ω i.val = v i} =
      ∏ i : Fin n, (ProbabilityTheory.cond μ accept) {v i} := by
  induction n with
  | zero => simp
  | succ n ih =>
    let T : Set (ℕ → A) := {ω | ∀ i : Fin n, draws accept fallback ω i.val = v i.succ}
    have hT : MeasurableSet T := by
      have hT' : T = ⋂ i : Fin n,
          {ω | draws accept fallback ω i.val = v i.succ} := by ext ω; simp [T]
      rw [hT']
      exact MeasurableSet.iInter fun i => (measurableSet_singleton _).preimage
        ((measurable_pi_apply i.val).comp (draws_measurable accept fallback ha))
    have he : {ω | ∀ i : Fin (n+1), draws accept fallback ω i.val = v i} =
        (restart accept fallback) ⁻¹' ({v 0} ×ˢ T) := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_preimage,Set.mem_prod,Set.mem_singleton_iff,T]
      constructor
      · intro h
        exact ⟨h 0,fun i => h i.succ⟩
      · rintro ⟨h0,hs⟩ i
        exact Fin.cases h0 hs i
    rw [he,← Measure.map_apply (restart_measurable accept fallback ha)
      ((measurableSet_singleton _).prod hT),
      first_acceptance_restart μ accept fallback ha hpos,Measure.prod_prod]
    rw [ih (fun i => v i.succ),Fin.prod_univ_succ]

/-- All repeated services return outside one null event, and their complete
    infinite output law is iid conditional acceptance. Every suffix restart
    uses the same external stream rather than an independent replacement tape. -/
theorem repeated_acceptance_law [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure A) [IsProbabilityMeasure μ] (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) (hpos : μ accept ≠ 0) :
    Measurable (draws accept fallback) ∧
    (Measure.infinitePi (fun _ : ℕ => μ)).map (draws accept fallback) =
      Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond μ accept) ∧
    (∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ),
      ∀ n, firstHit accept (unused accept fallback n ω) ≠ none) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ accept) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  have hd := draws_measurable accept fallback ha
  refine ⟨hd,?_,?_⟩
  · have hp (n : ℕ) :
        ((Measure.infinitePi (fun _ : ℕ => μ)).map (draws accept fallback)).map
          (fun ω i => ω (i : Fin (n+1))) =
        (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond μ accept)).map
          (fun ω i => ω (i : Fin (n+1))) := by
      apply Measure.ext_of_singleton
      intro v
      rw [Measure.map_map (by fun_prop) hd,
        Measure.map_apply (by fun_prop) (measurableSet_singleton _),
        Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      have h1 : (fun ω i => draws accept fallback ω (i : Fin (n+1))) ⁻¹' {v} =
          {ω | ∀ i : Fin (n+1), draws accept fallback ω i.val = v i} := by
        ext ω; simp [funext_iff]
      have h2 : (fun ω : ℕ → A => fun i : Fin (n+1) => ω i) ⁻¹' {v} =
          Set.pi (Finset.range (n+1)) (fun i =>
            if h : i < n+1 then {v ⟨i,h⟩} else univ) := by
        ext ω
        simp only [mem_preimage,mem_singleton_iff,funext_iff,Set.mem_pi,
          Finset.mem_coe,Finset.mem_range]
        constructor
        · intro h i hi; simpa [hi] using h ⟨i,hi⟩
        · intro h i; simpa [i.isLt] using h i.val i.isLt
      change (Measure.infinitePi (fun _ : ℕ => μ))
        ((fun ω i => draws accept fallback ω (i : Fin (n+1))) ⁻¹' {v}) = _
      rw [h1,drawn_prefix_mass μ accept fallback ha hpos,h2,
        Measure.infinitePi_pi _ (fun i _ => by split <;> measurability)]
      rw [← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      simp [i.isLt]
    let P := fun I : Finset ℕ =>
      (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond μ accept)).map I.restrict
    have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => A) P := by
      intro I J hJI
      dsimp [P]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    have hl : IsProjectiveLimit (α := fun _ : ℕ => A)
        ((Measure.infinitePi (fun _ : ℕ => μ)).map (draws accept fallback)) P := by
      apply (isProjectiveLimit_nat_iff hP _).mpr
      intro n
      let f : (Fin (n+1) → A) → (Finset.Iic n → A) :=
        fun v i => v ⟨i.val,Nat.lt_succ_of_le (Finset.mem_Iic.mp i.property)⟩
      change (((Measure.infinitePi (fun _ : ℕ => μ)).map
        (draws accept fallback)).map (Finset.Iic n).restrict) = P (Finset.Iic n)
      calc
        _ = (((Measure.infinitePi (fun _ : ℕ => μ)).map (draws accept fallback)).map
            (fun ω i => ω (i : Fin (n+1)))).map f := by
          conv_rhs => rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
        _ = ((Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond μ accept)).map
            (fun ω i => ω (i : Fin (n+1)))).map f := congrArg (Measure.map f) (hp n)
        _ = P (Finset.Iic n) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    exact hl.unique (fun _ => rfl)
  · apply ae_all_iff.mpr
    intro n
    have hn : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ), firstHit accept ω ≠ none := by
      rw [ae_iff]
      simpa only [not_not] using nonreturn_null μ accept ha hpos
    have hm := unused_measurable accept fallback ha n
    have he := unused_preserves μ accept fallback ha hpos n
    exact ae_of_ae_map hm.aemeasurable (he.symm ▸ hn)

#print axioms first_acceptance_restart
#print axioms repeated_acceptance_law

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
