/- GID: D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native two-vertex history supplies the uniform lag-two variance bracket. -/

/-
proof_shape: result: content
escape_witness: input_time_vertex; innovation_history_law
admission_basis: escape-witness
literature_status: inherited source consequence; no novelty claim
The native innovation law supplies the full-horizon native_variance and native_binomial clauses.
Scalar helpers are consumed bind-only declarations and receive no escape credit.
Theorem inventory: 12 content; 23 consumed bind-only; 34 private; 1 public.
The causal-support induction proves a time-and-vertex restriction absent from the suppliers.
The horizon induction proves the joint law of the actual synchronous agreement variables.
Initial and positive-time laws are the only coordinate premises on the original P.
Declaration rows: name | proof_shape | escape_witness | direct value consumers.
Compiler-generated proof auxiliaries inherit their enclosing authored proof classification.
Constructions and generated structure projections carry no claim of new mathematical content.
input_time_vertex | content | input_time_vertex | history_input_time_vertex
history_input_time_vertex | content | input_time_vertex | block_not_past
k2Neighbor | bind-only | none | nativeConclusions, result, agreement_extension, block_hasLaw, block_independent_past, initial_block_law, initial_history_law, innovation_history_law, native_binomial, native_conclusions, native_transition_fiber, native_variance, repetitions_law, upper_member
choice_other | bind-only | none | initial_history_law, native_two_step
block_positive | bind-only | none | block_hasLaw, block_independent_past
block_injective | bind-only | none | block_hasLaw
block_not_past | content | input_time_vertex | block_independent_past
native_two_step | bind-only | none | agreement_extension, native_transition_fiber
block_hasLaw | bind-only | none | agreement_extension, native_transition_fiber
block_kernel | bind-only | none | block_agreement_kernel, native_transition_fiber
bits_measurable | bind-only | none | agreement_extension, initial_history_law, innovation_history_law
block_independent_past | content | input_time_vertex | agreement_extension, native_transition_fiber
independent_update_fiber | bind-only | none | agreement_extension, native_transition_fiber
native_transition_fiber | content | input_time_vertex | native_conclusions
block_agreement_kernel | bind-only | none | agreement_extension
agreement_extension | content | input_time_vertex | innovation_history_law
initial_block_law | bind-only | none | initial_history_law
initial_kernel | bind-only | none | initial_history_law
initial_history_law | bind-only | none | innovation_history_law
innovations_snoc | bind-only | none | innovation_history_law._simp_1_4
innovation_history_law | content | innovation_history_law | native_conclusions, repetitions_law
repetitions_law | content | innovation_history_law | native_binomial, native_variance
original_W_sum | bind-only | none | native_binomial, native_variance
bit_variance | bind-only | none | native_variance
native_variance | content | innovation_history_law | native_conclusions, upper_member
bit_count_law | bind-only | none | native_binomial
original_lower | bind-only | none | bracket
upper_member | bind-only | none | bracket
bracket | bind-only | none | asymptotic_bounds, scalar_bounds
scalar_bounds | bind-only | none | result, asymptotic_bounds
native_binomial | content | innovation_history_law | native_conclusions
near_zero | bind-only | none | asymptotic_bounds
asymptotic_bounds | bind-only | none | result
native_conclusions | content | innovation_history_law | result
result | content | innovation_history_law | terminal complete Theorem 3.2
Frozen module pins and directly used original suppliers:
D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths: original_potential_path_bounds
  module statement_id: sha256:2c0a4740fd3192bd7ed2ed950aca034cd004d7ba2bb3fcca0883169f430e432d
D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs: finite_history_factorization, inputs, historyInputs, positive, decode
  module statement_id: sha256:81feffad81eb171cb125c1ea50f72b90ca584552238c96c8498bd11504367f2e
D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear: nvm, W, coordinateLaw, Coord, Value
  module statement_id: sha256:d0ef35748b99db85baa606316acc01db27d583a5a6de1a54c800bdc6a2a06afc
D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources: coordinateTime
  module statement_id: sha256:0a187dc75326fb897504e7e4efe52c7c454137d1c6dcab7904797dabdab00bc2
-/

import D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Topology.Order.LiminfLimsup

/-! # Native lag-two history and its optimal-constant bracket -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket

open RepetitionVarianceLinear AncestralSources FiniteCausalInputs

/-- The original law imposes conditions only on initial and positive-time slots. -/
structure OriginalLaw {V Ω : Type} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace Ω] (P : Measure Ω) (ε : unitInterval)
    (hNbr : ∀ v, ∃ w, G.Adj v w) (x : (c : Coord V) → Ω → Value G c) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ c, positive c → Measurable (x c)
  independent : iIndepFun (fun c : {c : Coord V // positive c} => x c.val) P
  laws : ∀ c : {c : Coord V // positive c},
    HasLaw (x c.val) (coordinateLaw G ε hNbr c.val) P

private def vertex {V : Type} : Coord V → V
  | .initial v | .fresh _ v | .refresh _ v | .choice _ v => v

private theorem input_time_vertex {V : Type} {G : SimpleGraph V} [G.LocallyFinite] :
    ∀ n v c, c ∈ inputs (G := G) n v →
      coordinateTime c ≤ n ∧ (coordinateTime c = n → vertex c = v) := by
  classical
  intro n
  induction n with
  | zero =>
      intro v c hc
      have hc' : c = .initial v := by simpa only [inputs, Finset.mem_singleton] using hc
      subst c
      exact ⟨by simp [coordinateTime], fun _ => rfl⟩
  | succ n ih =>
      intro v c hc
      simp only [inputs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_biUnion] at hc
      rcases hc with (rfl | rfl | rfl) | ⟨w, _, hc⟩
      · exact ⟨le_rfl, fun _ => rfl⟩
      · exact ⟨le_rfl, fun _ => rfl⟩
      · exact ⟨le_rfl, fun _ => rfl⟩
      · obtain ⟨ht, _⟩ := ih w c hc
        exact ⟨by omega, fun he => by omega⟩

private theorem history_input_time_vertex {V : Type} {G : SimpleGraph V} [G.LocallyFinite]
    (u : V) (N : ℕ) (c : Coord V) (hc : c ∈ historyInputs (G := G) u N) :
    coordinateTime c ≤ N ∧ (coordinateTime c = N → vertex c = u) := by
  classical
  simp only [historyInputs, Finset.mem_biUnion, Finset.mem_range] at hc
  obtain ⟨n, hn, hc⟩ := hc
  obtain ⟨ht, hv⟩ := input_time_vertex n u c hc
  refine ⟨by omega, fun he => hv ?_⟩
  omega

abbrev K2 : SimpleGraph Bool := ⊤

private theorem k2Neighbor (u : Bool) : ∃ v, K2.Adj u v := by
  refine ⟨!u, ?_⟩
  cases u <;> decide

private theorem choice_other (u : Bool) (v : K2.neighborSet u) : v.val = !u := by
  have h := v.property
  cases u <;> rcases v with ⟨v, hv⟩ <;> cases v <;> simp_all [K2]

private def blockCoord (u : Bool) (n : ℕ) : Fin 4 → Coord Bool :=
  ![.refresh (n + 2) u, .fresh (n + 2) u, .refresh (n + 1) (!u), .fresh (n + 1) (!u)]

private theorem block_positive (u : Bool) (n : ℕ) (i : Fin 4) :
    positive (blockCoord u n i) := by
  fin_cases i <;> simp [blockCoord, positive]

private theorem block_injective (u : Bool) (n : ℕ) :
    Function.Injective (blockCoord u n) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [blockCoord]

private theorem block_not_past (u : Bool) (n : ℕ) (i : Fin 4) :
    blockCoord u n i ∉ historyInputs (G := K2) u (n + 1) := by
  intro h
  obtain ⟨ht, hv⟩ := history_input_time_vertex u (n + 1) _ h
  fin_cases i <;> cases u <;> simp_all [blockCoord, coordinateTime, vertex]

private def readBlock (u : Bool) (n : ℕ) (i : Fin 4) :
    Value K2 (blockCoord u n i) → Bool :=
  match i with
  | ⟨0, _⟩ => id
  | ⟨1, _⟩ => id
  | ⟨2, _⟩ => id
  | ⟨3, _⟩ => id

private def block {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (n : ℕ) (ω : Ω) : Fin 4 → Bool :=
  fun i => readBlock u n i (x (blockCoord u n i) ω)

private def update (a : Fin 4 → Bool) (old : Bool) : Bool :=
  if a 0 then a 1 else if a 2 then a 3 else old

private theorem native_two_step {Ω : Type}
    (x : (c : Coord Bool) → Ω → Value K2 c) (u : Bool) (n : ℕ) (ω : Ω) :
    nvm x (n + 2) u ω =
      update (block x u n ω) (nvm x n u ω) := by
  have h₀ := choice_other u (x (.choice (n + 1 + 1) u) ω)
  have h₁ := choice_other (!u) (x (.choice (n + 1) (!u)) ω)
  simp only [nvm]
  rw [h₀, h₁]
  simp [update, block, readBlock, blockCoord] <;> rfl

noncomputable def fair : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private noncomputable def blockParameter (ε : unitInterval) : Fin 4 → unitInterval := ![ε, fair, ε, fair]

private noncomputable def blockLaw (ε : unitInterval) : Measure (Fin 4 → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (blockParameter ε i))

private theorem block_hasLaw {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (n : ℕ) : HasLaw (block x u n) (blockLaw ε) P := by
  let f (i : Fin 4) : {c : Coord Bool // positive c} :=
    ⟨blockCoord u n i, block_positive u n i⟩
  have hf : Function.Injective f := fun _ _ he =>
    block_injective u n (congrArg Subtype.val he)
  have hm (i : Fin 4) : Measurable (readBlock u n i) := measurable_of_finite _
  have hi := (h.independent.precomp hf).comp (readBlock u n) hm
  apply hi.hasLaw_pi
  intro i
  fin_cases i
  · exact h.laws ⟨.refresh (n + 2) u, by simp [positive]⟩
  · exact h.laws ⟨.fresh (n + 2) u, by simp [positive]⟩
  · exact h.laws ⟨.refresh (n + 1) (!u), by simp [positive]⟩
  · exact h.laws ⟨.fresh (n + 1) (!u), by simp [positive]⟩

private def tuple4 : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by rcases a with ⟨a,b,c,d⟩; rfl

private theorem block_kernel (ε : unitInterval) (old b : Bool) :
    (blockLaw ε).real {a | update a old = b} =
      if b = old then (1 + (1-(ε : ℝ)) ^ 2) / 2 else (1-(1-(ε : ℝ)) ^ 2) / 2 := by
  classical
  let μ := blockLaw ε
  letI : IsProbabilityMeasure μ := by dsimp [μ, blockLaw]; infer_instance
  have hs : {a | update a old = b} =
      (↑(Finset.univ.filter (fun a => update a old = b)) : Set (Fin 4 → Bool)) := by
    ext a; simp
  rw [hs, ← sum_measureReal_singleton, Finset.sum_filter]
  simp only [μ, blockLaw, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  rw [← tuple4.symm.sum_comp]
  cases old <;> cases b <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, tuple4, update, Fin.prod_univ_four,
      blockParameter, fair, bernoulliMeasure_real_apply, Measure.real,
      bernoulliMeasure_apply, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, ENNReal.coe_toReal] <;> ring

private def base : (c : Coord Bool) → Value K2 c
  | .initial _ | .fresh _ _ | .refresh _ _ => false
  | .choice _ v => ⟨!v, by cases v <;> decide⟩

def bits {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (N : ℕ) (ω : Ω) : Fin (N + 1) → Bool :=
  fun i => nvm x i.val u ω

private theorem bits_measurable {Ω : Type} [MeasurableSpace Ω]
    (x : (c : Coord Bool) → Ω → Value K2 c)
    (hx : ∀ c, positive c → Measurable (x c)) (u : Bool) (N : ℕ) :
    Measurable (bits x u N) := by
  let f (a : InputState (G := K2) u N) : Fin (N + 1) → Bool :=
    fun i => (decode base u N a i).1
  have he : bits x u N = f ∘ restrictInputs x u N := by
    funext ω i
    exact congrArg (fun a => (a i).1) ((finite_history_factorization base u N).2 x ω)
  rw [he]
  exact (measurable_of_finite f).comp (measurable_pi_iff.mpr (fun c =>
    hx c.val ((finite_history_factorization (Ω := Ω) base u N).1 c.val c.property)))

private theorem block_independent_past {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (n : ℕ) : IndepFun (block x u n) (bits x u (n + 1)) P := by
  classical
  let f (i : Fin 4) : {c : Coord Bool // positive c} :=
    ⟨blockCoord u n i, block_positive u n i⟩
  let S : Set {c : Coord Bool // positive c} := Set.range f
  let T : Set {c : Coord Bool // positive c} :=
    {c | c.val ∈ historyInputs (G := K2) u (n + 1)}
  have hd : Disjoint S T := by
    apply Set.disjoint_left.mpr
    rintro c ⟨i, rfl⟩ hc
    exact block_not_past u n i hc
  have hi := h.independent.indepFun_set S T hd (fun c => h.measurable c.val c.property)
  let b (a : (c : S) → Value K2 c.val.val) : Fin 4 → Bool :=
    fun i => readBlock u n i (a ⟨f i, Set.mem_range_self i⟩)
  let r (a : (c : T) → Value K2 c.val.val) : InputState (G := K2) u (n + 1) :=
    fun c => a ⟨⟨c.val,
      (finite_history_factorization (Ω := Ω) base u (n + 1)).1 c.val c.property⟩, c.property⟩
  let d (a : InputState (G := K2) u (n + 1)) : Fin (n + 2) → Bool :=
    fun i => (decode base u (n + 1) a i).1
  have hb : Measurable b := measurable_pi_iff.mpr (fun i =>
    (measurable_of_finite (readBlock u n i)).comp (measurable_pi_apply _))
  have hr : Measurable r := measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  have hd' : Measurable d := measurable_of_finite d
  have he : bits x u (n + 1) = d ∘ r ∘ (fun ω c => x c.val.val ω) := by
    funext ω i
    exact congrArg (fun a => (a i).1)
      ((finite_history_factorization base u (n + 1)).2 x ω)
  rw [he]
  exact hi.comp hb (hd'.comp hr)

private theorem independent_update_fiber {Ω α β : Type} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → α) (B : Ω → β) (μ : Measure β) (h : IndepFun H B P)
    (hl : HasLaw B μ P) (f : α → β → Bool) (a : α) (b : Bool) :
    P.real {ω | H ω = a ∧ f (H ω) (B ω) = b} =
      P.real {ω | H ω = a} * μ.real {z | f a z = b} := by
  have hs : {ω | H ω = a ∧ f (H ω) (B ω) = b} =
      H ⁻¹' {a} ∩ B ⁻¹' {z | f a z = b} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]; constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by simpa [ha] using hb⟩
  have he := congrArg ENNReal.toReal
    (h.measure_inter_preimage_eq_mul {a} {z | f a z = b}
      (measurableSet_singleton a) (Set.to_countable _).measurableSet)
  rw [← hl.measureReal_eq (Set.to_countable {z | f a z = b}).measurableSet]
  simpa [Measure.real, hs, ENNReal.toReal_mul, Set.preimage] using he

private theorem native_transition_fiber {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (n : ℕ) (z : Fin (n + 2) → Bool) (b : Bool) :
    P.real {ω | bits x u (n + 1) ω = z ∧ nvm x (n + 2) u ω = b} =
      P.real {ω | bits x u (n + 1) ω = z} *
        (if b = z ⟨n, by omega⟩ then (1 + (1-(ε : ℝ)) ^ 2) / 2
         else (1-(1-(ε : ℝ)) ^ 2) / 2) := by
  let := h.probability
  have he := independent_update_fiber P (bits x u (n + 1)) (block x u n) (blockLaw ε)
    (block_independent_past P ε x h u n).symm (block_hasLaw P ε x h u n)
    (fun a c => update c (a ⟨n, by omega⟩)) z b
  simp_rw [block_kernel] at he
  simpa only [native_two_step, bits] using he

noncomputable def successProbability (ε : unitInterval) : unitInterval :=
  ⟨(1 + (1-(ε : ℝ)) ^ 2) / 2, by positivity, by
    have h₀ := ε.property.1
    have h₁ := ε.property.2
    nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]⟩

def agreement {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (n : ℕ) (ω : Ω) : Bool :=
  decide (nvm x (n + 2) u ω = nvm x n u ω)

private theorem block_agreement_kernel (ε : unitInterval) (old b : Bool) :
    (blockLaw ε).real {a | decide (update a old = old) = b} =
      (bernoulliMeasure true false (successProbability ε)).real {b} := by
  cases b
  · have he : {a | decide (update a old = old) = false} =
        {a | update a old = !old} := by ext a; cases h : update a old <;> cases old <;> simp_all
    rw [he, block_kernel]
    cases old <;> norm_num [bernoulliMeasure_real_apply, successProbability] <;> ring
  · have he : {a | decide (update a old = old) = true} =
        {a | update a old = old} := by ext a; simp
    rw [he, block_kernel]
    norm_num [bernoulliMeasure_real_apply, successProbability]

private theorem agreement_extension {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (n : ℕ) :
    HasLaw (fun ω => (bits x u (n + 1) ω, agreement x u n ω))
      ((P.map (bits x u (n + 1))).prod
        (bernoulliMeasure true false (successProbability ε))) P := by
  classical
  let := h.probability
  have hm := bits_measurable x h.measurable u (n + 1)
  have ha : Measurable (agreement x u n) := by
    let f (a : Fin (n + 3) → Bool) : Bool := decide (a ⟨n + 2, by omega⟩ = a ⟨n, by omega⟩)
    exact (measurable_of_finite f).comp (bits_measurable x h.measurable u (n + 2))
  refine ⟨(hm.prodMk ha).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨z,b⟩
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change (P.map (fun ω => (bits x u (n + 1) ω, agreement x u n ω))).real {(z,b)} =
    ((P.map (bits x u (n + 1))).prod
      (bernoulliMeasure true false (successProbability ε))).real {(z,b)}
  rw [map_measureReal_apply (hm.prodMk ha) (measurableSet_singleton _)]
  simp only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  have he := independent_update_fiber P (bits x u (n + 1)) (block x u n) (blockLaw ε)
    (block_independent_past P ε x h u n).symm (block_hasLaw P ε x h u n)
    (fun a c => decide (update c (a ⟨n, by omega⟩) = a ⟨n, by omega⟩)) z b
  simp_rw [block_agreement_kernel] at he
  have hr : {(z,b)} = ({z} : Set _) ×ˢ {b} := Set.singleton_prod_singleton.symm
  rw [hr, measureReal_prod_prod,
    map_measureReal_apply hm (measurableSet_singleton z)]
  cases b <;>
    simp only [agreement, decide_eq_true_eq, decide_eq_false_iff_not] at he ⊢ <;>
    simpa only [native_two_step, bits, Set.preimage, Set.mem_singleton_iff] using he

private def initialCoord (u : Bool) : Fin 4 → Coord Bool :=
  ![.initial u, .refresh 1 u, .fresh 1 u, .initial (!u)]

private noncomputable def initialParameter (ε : unitInterval) : Fin 4 → unitInterval :=
  ![fair, ε, fair, fair]

private def initialRead (u : Bool) (i : Fin 4) : Value K2 (initialCoord u i) → Bool :=
  match i with
  | ⟨0, _⟩ => id
  | ⟨1, _⟩ => id
  | ⟨2, _⟩ => id
  | ⟨3, _⟩ => id

private def initialBlock {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (ω : Ω) : Fin 4 → Bool :=
  fun i => initialRead u i (x (initialCoord u i) ω)

private noncomputable def initialLaw (ε : unitInterval) : Measure (Fin 4 → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (initialParameter ε i))

private theorem initial_block_law {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) : HasLaw (initialBlock x u) (initialLaw ε) P := by
  let f (i : Fin 4) : {c : Coord Bool // positive c} :=
    ⟨initialCoord u i, by fin_cases i <;> simp [initialCoord, positive]⟩
  have hf : Function.Injective f := by
    intro i j he
    have hv := congrArg Subtype.val he
    fin_cases i <;> fin_cases j <;> cases u <;> simp_all [f, initialCoord]
  have hm (i : Fin 4) : Measurable (initialRead u i) := measurable_of_finite _
  have hi := (h.independent.precomp hf).comp (initialRead u) hm
  apply hi.hasLaw_pi
  intro i
  fin_cases i
  · exact h.laws ⟨.initial u, trivial⟩
  · exact h.laws ⟨.refresh 1 u, by simp [positive]⟩
  · exact h.laws ⟨.fresh 1 u, by simp [positive]⟩
  · exact h.laws ⟨.initial (!u), trivial⟩

private def initialDecode (a : Fin 4 → Bool) : Fin 2 → Bool :=
  ![a 0, if a 1 then a 2 else a 3]

private theorem initial_kernel (ε : unitInterval) (z : Fin 2 → Bool) :
    (initialLaw ε).real {a | initialDecode a = z} = (1 / 4 : ℝ) := by
  classical
  let μ := initialLaw ε
  letI : IsProbabilityMeasure μ := by dsimp [μ, initialLaw]; infer_instance
  have hs : {a | initialDecode a = z} =
      (↑(Finset.univ.filter (fun a => initialDecode a = z)) : Set (Fin 4 → Bool)) := by
    ext a; simp
  rw [hs, ← sum_measureReal_singleton, Finset.sum_filter]
  simp only [initialLaw, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  rw [← tuple4.symm.sum_comp]
  cases h₀ : z 0 <;> cases h₁ : z 1 <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, tuple4, initialDecode,
      Fin.prod_univ_four, initialParameter, fair, bernoulliMeasure_real_apply,
      Measure.real, bernoulliMeasure_apply, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, ENNReal.coe_toReal, funext_iff, Fin.forall_fin_succ, h₀, h₁] <;> ring

private theorem initial_history_law {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) : HasLaw (bits x u 1)
      (Measure.pi (fun _ : Fin 2 => bernoulliMeasure true false fair)) P := by
  classical
  let := h.probability
  have he : bits x u 1 = initialDecode ∘ initialBlock x u := by
    funext ω i
    fin_cases i
    · rfl
    · simp only [bits, nvm]
      rw [choice_other u (x (.choice 1 u) ω)]
      rfl
  refine ⟨(bits_measurable x h.measurable u 1).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change (P.map (bits x u 1)).real {z} = _
  rw [map_measureReal_apply (bits_measurable x h.measurable u 1)
    (measurableSet_singleton z)]
  have hk := (initial_block_law P ε x h u).measureReal_eq
    (p := fun a => initialDecode a = z) (Set.to_countable _).measurableSet
  rw [initial_kernel] at hk
  have hl : (Measure.pi (fun _ : Fin 2 => bernoulliMeasure true false fair)).real {z} =
      (1 / 4 : ℝ) := by
    simp [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, Fin.prod_univ_two]
    cases z 0 <;> cases z 1 <;> norm_num [bernoulliMeasure_apply, fair]
  rw [← Measure.real, hl]
  simpa only [he, Function.comp_def, Set.preimage, Set.mem_singleton_iff] using hk

def encode {N : ℕ} (z : Fin (N + 2) → Bool) : Fin (N + 2) → Bool :=
  fun i => if hi : i.val < 2 then z i
    else decide (z i = z ⟨i.val-2, by omega⟩)

def innovations {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (N : ℕ) (ω : Ω) : Fin (N + 2) → Bool :=
  encode (bits x u (N + 1) ω)

noncomputable def innovationParameter (ε : unitInterval) {N : ℕ}
    (i : Fin (N + 2)) : unitInterval :=
  if i.val < 2 then fair else successProbability ε

noncomputable def innovationLaw (ε : unitInterval) (N : ℕ) :
    Measure (Fin (N + 2) → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (innovationParameter ε i))

private theorem innovations_snoc {Ω : Type}
    (x : (c : Coord Bool) → Ω → Value K2 c) (u : Bool) (N : ℕ) (ω : Ω) :
    innovations x u (N + 1) ω = Fin.snoc (innovations x u N ω) (agreement x u N ω) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [innovations, encode, bits, agreement, show ¬ N + 2 < 2 by omega]
  · simp [innovations, encode, bits]
    rfl

private theorem innovation_history_law {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) : ∀ N : ℕ, HasLaw (innovations x u N) (innovationLaw ε N) P := by
  classical
  let := h.probability
  intro N
  induction N with
  | zero =>
      have he : innovations x u 0 = bits x u 1 := by
        funext ω i; fin_cases i <;> rfl
      have hp : innovationLaw ε 0 =
          Measure.pi (fun _ : Fin 2 => bernoulliMeasure true false fair) := by
        unfold innovationLaw
        congr 1; funext i; fin_cases i <;> rfl
      rw [he, hp]
      exact initial_history_law P ε x h u
  | succ N ih =>
      have hm := bits_measurable x h.measurable u (N + 1)
      have hext := agreement_extension P ε x h u N
      let ν := bernoulliMeasure true false (successProbability ε)
      have hE : HasLaw (agreement x u N) ν P :=
        (measurePreserving_snd (μ := P.map (bits x u (N + 1))) (ν := ν)).hasLaw.comp hext
      have hi : IndepFun (bits x u (N + 1)) (agreement x u N) P :=
        (indepFun_iff_hasLaw_prodMk_prod (hasLaw_map hm.aemeasurable) hE).mpr hext
      have hY : IndepFun (agreement x u N) (innovations x u N) P :=
        hi.symm.comp measurable_id (measurable_of_finite encode)
      have hpair := hY.hasLaw_prod hE ih
      let μ (i : Fin (N + 3)) := bernoulliMeasure true false (innovationParameter ε i)
      have hp := (measurePreserving_piFinSuccAbove μ (Fin.last (N + 2))).symm.hasLaw
      have hμ : (μ (Fin.last (N + 2))).prod
          (Measure.pi (fun j => μ ((Fin.last (N + 2)).succAbove j))) =
          ν.prod (innovationLaw ε N) := by
        simp [μ, ν, innovationLaw, innovationParameter, show ¬ N + 2 < 2 by omega]
      rw [hμ] at hp
      have hout := hp.comp hpair
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last',
        Function.comp_def, ← innovations_snoc, innovationLaw, μ] using hout

private def repetitions {Ω : Type} (x : (c : Coord Bool) → Ω → Value K2 c)
    (u : Bool) (t : ℕ) (ω : Ω) : Fin t → Bool :=
  fun i => agreement x u (i.val + 1) ω

private theorem repetitions_law {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (t : ℕ) : HasLaw (repetitions x u t)
      (Measure.pi (fun _ : Fin t => bernoulliMeasure true false (successProbability ε))) P := by
  let f (i : Fin t) : Fin (t + 3) := ⟨i.val + 3, by omega⟩
  have hf : Function.Injective f := by intro i j he; apply Fin.ext; have := congrArg Fin.val he; dsimp [f] at this; omega
  have hp := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun i : Fin (t + 3) => bernoulliMeasure true false (innovationParameter ε i)) hf
  simp only [Measure.infinitePi_eq_pi] at hp
  have hr : HasLaw (fun z : Fin (t + 3) → Bool => fun i => z (f i))
      (Measure.pi (fun _ : Fin t => bernoulliMeasure true false (successProbability ε)))
      (innovationLaw ε (t + 1)) := by
    refine ⟨(measurable_of_finite _).aemeasurable, ?_⟩
    simpa [innovationLaw, innovationParameter, f, show ∀ i : Fin t, ¬ i.val + 3 < 2 by omega] using hp
  have hout := hr.comp (innovation_history_law P ε x h u (t + 1))
  convert hout using 1
  funext ω i
  simp [repetitions, innovations, encode, bits, f, agreement,
    show ¬ i.val + 3 < 2 by omega]

private def bitValue (b : Bool) : ℝ := if b then 1 else 0

private def bitSum {t : ℕ} (z : Fin t → Bool) : ℝ := ∑ i, bitValue (z i)

private theorem original_W_sum {Ω : Type}
    (x : (c : Coord Bool) → Ω → Value K2 c) (u : Bool) (t : ℕ) :
    W x u 2 t = bitSum ∘ repetitions x u t := by
  funext ω
  have hb (n : ℕ) : (if nvm x n u ω = nvm x (n + 2) u ω then 1 else 0 : ℝ) =
      bitValue (agreement x u n ω) := by
    simp [bitValue, agreement, eq_comm]
  simp only [W, bitSum, repetitions, Function.comp_def, hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => bitValue (agreement x u (i + 1) ω)) t]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  congr 1
  funext i
  rw [Nat.add_comm i 1]

private theorem bit_variance (p : unitInterval) :
    variance bitValue (bernoulliMeasure true false p) = (p : ℝ) * (1-p) := by
  rw [variance_eq_integral (measurable_of_finite bitValue).aemeasurable]
  simp [integral_bernoulliMeasure, bitValue]
  ring

private theorem native_variance {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (t : ℕ) :
    variance (W x u 2 t) P = (t : ℝ) * (1-(1-(ε : ℝ)) ^ 4) / 4 := by
  let μ := Measure.pi (fun _ : Fin t => bernoulliMeasure true false (successProbability ε))
  have hl := repetitions_law P ε x h u t
  have hv : variance (bitSum (t := t)) μ =
      variance (bitSum ∘ repetitions x u t) P := by
    change variance bitSum (Measure.pi _) = _
    rw [← hl.map_eq]
    exact variance_map (measurable_of_finite bitSum).aemeasurable hl.aemeasurable
  rw [original_W_sum, ← hv]
  have he : bitSum (t := t) = ∑ i : Fin t, fun z => bitValue (z i) := by
    ext z; simp [bitSum]
  rw [he]
  dsimp [μ]
  rw [variance_sum_pi (fun i => MemLp.of_bound (measurable_of_finite bitValue).aestronglyMeasurable
    (C := 1) (by filter_upwards [] with b; cases b <;> norm_num [bitValue]))]
  simp only [bit_variance, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [successProbability]
  ring

private theorem bit_count_law (t : ℕ) (p : unitInterval) :
    HasLaw (fun z : Fin t → Bool => {i | z i = true}.ncard) (binomial t p)
      (Measure.pi (fun _ : Fin t => bernoulliMeasure true false p)) := by
  classical
  let μ := Measure.pi (fun _ : Fin t => bernoulliMeasure true false p)
  let pred (z : Fin t → Bool) : Fin t → Prop := fun i => z i = true
  have hm : Measurable pred := measurable_of_finite pred
  have hp := Measure.infinitePi_map_pi
    (μ := fun _ : Fin t => bernoulliMeasure true false p)
    (f := fun _ b => b = true) (fun _ => measurable_of_finite _)
  simp only [Measure.infinitePi_eq_pi, map_bernoulliMeasure] at hp
  have hs : HasLaw (fun z : Fin t → Bool => {i | z i = true})
      (setBernoulli (Set.univ : Set (Fin t)) p) μ := by
    refine ⟨(measurable_of_finite _).aemeasurable, ?_⟩
    rw [setBernoulli_eq_map]
    change μ.map ((fun a : Fin t → Prop => {i | a i}) ∘ pred) = _
    rw [← Measure.map_map (measurable_of_finite (fun a : Fin t → Prop => {i | a i})) hm]
    rw [show μ.map pred = Measure.pi (fun _ : Fin t => bernoulliMeasure True False p) by simpa [μ, pred] using hp]
    simp only [Set.mem_univ, Measure.infinitePi_eq_pi]
  have hn : HasLaw Set.ncard (binomial t p) (setBernoulli (Set.univ : Set (Fin t)) p) := by
    refine ⟨(measurable_of_finite _).aemeasurable, ?_⟩
    apply Measure.ext_of_singleton
    intro k
    rw [map_ncard_setBernoulli_singleton Set.finite_univ, binomial_singleton]
    simp
  exact hn.comp hs

private def valuesOn (V Ω : Type) (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace Ω] (ε r : ℝ) : Prop :=
  ∃ (P : Measure Ω) (e : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (x : (c : Coord V) → Ω → Value G c) (u : V) (t : ℕ),
    (e : ℝ) = ε ∧ G.Connected ∧ OriginalLaw G P e hNbr x ∧
    1 ≤ t ∧ r = variance (W x u 2 t) P / t

/-- All normalized native lag-two variances on the original graph and probability-space class. -/
noncomputable def varianceValues (ε : ℝ) : Set ℝ :=
  {r | ∃ (V Ω : Type) (G : SimpleGraph V) (lf : G.LocallyFinite)
    (m : MeasurableSpace Ω), @valuesOn V Ω G lf m ε r}

/-- The infimum is taken over the full original variance-value class. -/
noncomputable def cOpt (ε : ℝ) : ℝ := sInf (varianceValues ε)

private theorem original_lower (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    {r : ℝ} (hr : r ∈ varianceValues ε) : (1-(1-ε) ^ 2) / 4 ≤ r := by
  rcases hr with ⟨V, Ω, G, lf, m, P, e, hNbr, x, u, t, he, hG, h, ht, rfl⟩
  let := lf
  let := m
  let := h.probability
  have hb := PotentialPaths.original_potential_path_bounds P hG hNbr e
    (by simpa [he] using hε) (by simpa [he] using hε') x
    h.measurable h.independent h.laws u 2 t
  have hv := hb.2.2.trans hb.2.1
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  apply (le_div_iff₀ ht').mpr
  rw [he] at hv
  nlinarith

private theorem upper_member (e : unitInterval) :
    (1-(1-(e : ℝ)) ^ 4) / 4 ∈ varianceValues e := by
  let Ω := (c : Coord Bool) → Value K2 c
  let P : Measure Ω := Measure.infinitePi (coordinateLaw K2 e k2Neighbor)
  let x (c : Coord Bool) (ω : Ω) := ω c
  have h : OriginalLaw K2 P e k2Neighbor x := {
    probability := inferInstance
    measurable := fun c _ => measurable_pi_apply c
    independent := (iIndepFun_infinitePi (X := fun _ a => a)
      (fun _ => measurable_id)).precomp Subtype.val_injective
    laws := fun c => (measurePreserving_eval_infinitePi
      (coordinateLaw K2 e k2Neighbor) c.val).hasLaw }
  refine ⟨Bool, Ω, K2, inferInstance, inferInstance, P, e, k2Neighbor, x, false, 1,
    rfl, SimpleGraph.connected_top, h, le_rfl, ?_⟩
  rw [native_variance P e x h false 1]
  norm_num

private theorem bracket (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (1-(1-ε) ^ 2) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (1-(1-ε) ^ 4) / 4 := by
  let e : unitInterval := ⟨ε, hε.le, hε'.le⟩
  have hu := upper_member e
  have hne : (varianceValues ε).Nonempty := ⟨_, hu⟩
  have hbd : BddBelow (varianceValues ε) := ⟨_, fun _ hr => original_lower ε hε hε' hr⟩
  exact ⟨le_csInf hne (fun _ hr => original_lower ε hε hε' hr), csInf_le hbd hu⟩

private theorem scalar_bounds (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (1-(1-ε) ^ 2) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (1-(1-ε) ^ 4) / 4 ∧
    (1-(1-ε) ^ 4) / (1-(1-ε) ^ 2) = 1 + (1-ε) ^ 2 ∧ 1 + (1-ε) ^ 2 < 2 ∧
    (2 * ε-ε ^ 2) / 4 ≤ cOpt ε ∧
    cOpt ε ≤ (4 * ε-6 * ε ^ 2 + 4 * ε ^ 3-ε ^ 4) / 4 ∧
    ε / 4 ≤ cOpt ε ∧ cOpt ε ≤ ε := by
  obtain ⟨hl, hu⟩ := bracket ε hε hε'
  have hq : 0 < 1-ε := by linarith
  have hq' : 1-ε < 1 := by linarith
  have hd : 0 < 1-(1-ε) ^ 2 := by nlinarith
  have heq : (1-(1-ε) ^ 4) / (1-(1-ε) ^ 2) = 1 + (1-ε) ^ 2 := by
    apply (div_eq_iff (ne_of_gt hd)).mpr
    ring
  refine ⟨hl, hu, heq, by nlinarith, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg ε,
    mul_nonneg (sq_nonneg (1-ε)) hq.le,
    mul_nonneg (sq_nonneg (1-ε)) (sub_nonneg.mpr hq'.le)]

private theorem native_binomial {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : unitInterval)
    (x : (c : Coord Bool) → Ω → Value K2 c) (h : OriginalLaw K2 P ε k2Neighbor x)
    (u : Bool) (t : ℕ) :
    HasLaw (W x u 2 t) ((binomial t (successProbability ε)).map (Nat.cast : ℕ → ℝ)) P := by
  classical
  have hsum (z : Fin t → Bool) : bitSum z = ({i | z i = true}.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card']
    have he : {i | z i = true}.toFinset = Finset.univ.filter (fun i => z i = true) := by
      ext i; simp
    rw [he, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp [bitSum, bitValue, Finset.sum_filter]
  have hn := (bit_count_law t (successProbability ε)).comp (repetitions_law P ε x h u t)
  have hout := (hasLaw_map (P := binomial t (successProbability ε))
    (X := (Nat.cast : ℕ → ℝ)) (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable).comp hn
  rw [original_W_sum]
  simpa only [Function.comp_def, ← hsum] using hout

open Filter
open scoped Topology

private theorem near_zero : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with ε hε hε'
  exact ⟨hε, hε'⟩

private theorem asymptotic_bounds :
    Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) cOpt (fun ε => ε) ∧
    (1 / 2 : ℝ) ≤ liminf (fun ε : ℝ => cOpt ε / ε) (𝓝[>] 0) ∧
    liminf (fun ε : ℝ => cOpt ε / ε) (𝓝[>] 0) ≤
      limsup (fun ε : ℝ => cOpt ε / ε) (𝓝[>] 0) ∧
    limsup (fun ε : ℝ => cOpt ε / ε) (𝓝[>] 0) ≤ 1 := by
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε / 4 ≤ cOpt ε ∧ cOpt ε ≤ ε := by
    filter_upwards [near_zero] with ε hε
    obtain ⟨_, _, _, _, _, _, hl, hu⟩ := scalar_bounds ε hε.1 hε.2
    exact ⟨hε.1, hl, hu⟩
  have htheta : Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) cOpt (fun ε => ε) := by
    constructor
    · apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, hb.mono (fun ε hε => ?_)⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hε.1.le,
        abs_of_nonneg (by linarith : 0 ≤ cOpt ε), one_mul]
      exact hε.2.2
    · apply Asymptotics.isBigO_iff.mpr
      refine ⟨4, hb.mono (fun ε hε => ?_)⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hε.1.le,
        abs_of_nonneg (by linarith : 0 ≤ cOpt ε)]
      linarith [hε.2.1]
  have hl : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) (fun ε => cOpt ε / ε) := by
    refine ⟨1 / 4, hb.mono (fun ε hε => ?_)⟩
    exact (le_div_iff₀ hε.1).mpr (by linarith [hε.2.1])
  have hu : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (fun ε => cOpt ε / ε) := by
    refine ⟨1, hb.mono (fun ε hε => ?_)⟩
    exact (div_le_iff₀ hε.1).mpr (by simpa using hε.2.2)
  refine ⟨htheta, ?_, liminf_le_limsup hu hl,
    limsup_le_of_le hl.isCoboundedUnder_le (hb.mono (fun ε hε =>
      (div_le_iff₀ hε.1).mpr (by simpa using hε.2.2)))⟩
  apply (le_liminf_iff hu.isCoboundedUnder_ge hl).mpr
  intro a ha
  filter_upwards [near_zero,
    (eventually_lt_nhds (show (0 : ℝ) < 2 - 4 * a by linarith)).filter_mono nhdsWithin_le_nhds]
    with ε hε hδ
  obtain ⟨hlow, _⟩ := bracket ε hε.1 hε.2
  apply (lt_div_iff₀ hε.1).mpr
  have hmul := mul_pos hε.1 (show 0 < 2 - 4 * a-ε by linarith)
  nlinarith

/-- The native K2 conditional history, joint innovations and finite-time repetition law. -/
def nativeConclusions (ε : unitInterval) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
    (x : (c : Coord Bool) → Ω → Value K2 c)
    (_h : @OriginalLaw Bool Ω K2 inferInstance m P ε k2Neighbor x) (u : Bool),
    (∀ (n : ℕ) (z : Fin (n + 2) → Bool) (b : Bool),
      0 < P.real {ω | bits x u (n + 1) ω = z} →
      P.real {ω | bits x u (n + 1) ω = z ∧ nvm x (n + 2) u ω = b} /
          P.real {ω | bits x u (n + 1) ω = z} =
        (1-(1-(ε : ℝ)) ^ 2) / 2 + (1-(ε : ℝ)) ^ 2 *
          (if b = z ⟨n, by omega⟩ then 1 else 0)) ∧
    (∀ N : ℕ, @HasLaw Ω (Fin (N + 2) → Bool) m _
      (innovations x u N) (innovationLaw ε N) P) ∧
    (∀ t : ℕ, @HasLaw Ω ℝ m _ (W x u 2 t)
        ((binomial t (successProbability ε)).map (Nat.cast : ℕ → ℝ)) P ∧
      variance (W x u 2 t) P = (t : ℝ) * (1-(1-(ε : ℝ)) ^ 4) / 4)

private theorem native_conclusions (ε : unitInterval) : nativeConclusions ε := by
  intro Ω m P x h u
  let := m
  refine ⟨?_, innovation_history_law P ε x h u, fun t =>
    ⟨native_binomial P ε x h u t, native_variance P ε x h u t⟩⟩
  intro n z b hz
  rw [native_transition_fiber P ε x h u n z b]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hz)]
  split <;> simp_all <;> ring

/-- The full original-domain bracket, small-noise order and native two-vertex law. -/
theorem result (ε : unitInterval) (hε : 0 < (ε : ℝ)) (hε' : (ε : ℝ) < 1) :
    ((1-(1-(ε : ℝ)) ^ 2) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (1-(1-(ε : ℝ)) ^ 4) / 4 ∧
      (1-(1-(ε : ℝ)) ^ 4) / (1-(1-(ε : ℝ)) ^ 2) = 1 + (1-(ε : ℝ)) ^ 2 ∧
      1 + (1-(ε : ℝ)) ^ 2 < 2 ∧
      (2 * (ε : ℝ)-(ε : ℝ) ^ 2) / 4 ≤ cOpt ε ∧
      cOpt ε ≤ (4 * (ε : ℝ)-6 * (ε : ℝ) ^ 2 + 4 * (ε : ℝ) ^ 3-(ε : ℝ) ^ 4) / 4 ∧
      (ε : ℝ) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (ε : ℝ)) ∧
    (Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) cOpt (fun e => e) ∧
      (1 / 2 : ℝ) ≤ liminf (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ∧
      liminf (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ≤
        limsup (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ∧
      limsup (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ≤ 1) ∧
    (  ∀ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
    (x : (c : Coord Bool) → Ω → Value K2 c)
    (_h : @OriginalLaw Bool Ω K2 inferInstance m P ε k2Neighbor x) (u : Bool),
    (∀ (n : ℕ) (z : Fin (n + 2) → Bool) (b : Bool),
      0 < P.real {ω | bits x u (n + 1) ω = z} →
      P.real {ω | bits x u (n + 1) ω = z ∧ nvm x (n + 2) u ω = b} /
          P.real {ω | bits x u (n + 1) ω = z} =
        (1-(1-(ε : ℝ)) ^ 2) / 2 + (1-(ε : ℝ)) ^ 2 *
          (if b = z ⟨n, by omega⟩ then 1 else 0)) ∧
    (∀ N : ℕ, @HasLaw Ω (Fin (N + 2) → Bool) m _
      (innovations x u N) (innovationLaw ε N) P) ∧
    (∀ t : ℕ, @HasLaw Ω ℝ m _ (W x u 2 t)
        ((binomial t (successProbability ε)).map (Nat.cast : ℕ → ℝ)) P ∧
      variance (W x u 2 t) P = (t : ℝ) * (1-(1-(ε : ℝ)) ^ 4) / 4)
    ) := by
  exact ⟨scalar_bounds ε hε hε', asymptotic_bounds, native_conclusions ε⟩

end D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
