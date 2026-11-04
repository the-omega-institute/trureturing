/- GID: D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite positive-time inputs determine the joint native opinion and source history. -/

import D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

/-! # Finite causal inputs of the synchronous noisy voter process

The input sets contain every branch of the backward recursion. They depend on the
graph, time and vertex, rather than on a realized path. Keeping the opinion and
its source label together preserves the distinction between agreement of colours
and equality of sources.
-/

open MeasureTheory ProbabilityTheory

namespace D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs

open RepetitionVarianceLinear AncestralSources

variable {V Ω Ω' : Type} {G : SimpleGraph V} [G.LocallyFinite]

/-- A deterministic finite set of coordinates sufficient for one space-time observation. -/
noncomputable def inputs : ℕ → V → Finset (Coord V)
  | 0, v => {.initial v}
  | n+1, v => by
      classical
      exact {.fresh (n+1) v, .refresh (n+1) v, .choice (n+1) v} ∪
        (G.neighborFinset v).biUnion (inputs n)

/-- Every input is initial or has a strictly positive time coordinate. -/
def positive : Coord V → Prop
  | .initial _ => True
  | .fresh n _ | .refresh n _ | .choice n _ => 0 < n

private theorem inputs_positive : ∀ n v c, c ∈ inputs (G := G) n v → positive c := by
  classical
  intro n
  induction n with
  | zero =>
      intro v c hc
      have hc' : c = .initial v := by simpa only [inputs, Finset.mem_singleton] using hc
      subst c
      trivial
  | succ n ih =>
      intro v c hc
      simp only [inputs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_biUnion] at hc
      rcases hc with (rfl | rfl | rfl) | ⟨w, _, hc⟩
      · exact Nat.succ_pos n
      · exact Nat.succ_pos n
      · exact Nat.succ_pos n
      · exact ih w c hc

/-- Agreement on the causal inputs preserves the actual opinion and its actual source. -/
private theorem causal_congr
    (x : (c : Coord V) → Ω → Value G c)
    (y : (c : Coord V) → Ω' → Value G c) :
    ∀ n v ω ω', (∀ c ∈ inputs (G := G) n v, x c ω = y c ω') →
      nvm x n v ω = nvm y n v ω' ∧ source x n v ω = source y n v ω' := by
  classical
  intro n
  induction n with
  | zero =>
      intro v ω ω' h
      exact ⟨h (.initial v) (by simp [inputs]), rfl⟩
  | succ n ih =>
      intro v ω ω' h
      have hr := h (.refresh (n+1) v) (by simp [inputs])
      have hf := h (.fresh (n+1) v) (by simp [inputs])
      have hj := h (.choice (n+1) v) (by simp [inputs])
      have hprev : ∀ w ∈ G.neighborFinset v,
          ∀ c ∈ inputs (G := G) n w, x c ω = y c ω' := by
        intro w hw c hc
        exact h c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, hc⟩))
      simp only [nvm, source, hr, hj]
      split_ifs
      · exact ⟨hf, rfl⟩
      · exact ih (y (.choice (n+1) v) ω').val ω ω'
          (hprev _ (by
            rw [SimpleGraph.mem_neighborFinset]
            exact (y (.choice (n+1) v) ω').property))

/-- Inputs for every observation from time zero through the horizon. -/
noncomputable def historyInputs (u : V) (N : ℕ) : Finset (Coord V) := by
  classical
  exact (Finset.range (N+1)).biUnion (fun n => inputs (G := G) n u)

abbrev InputState (u : V) (N : ℕ) :=
  (c : {c // c ∈ historyInputs (G := G) u N}) → Value G c.val

/-- The opinion and disjoint source label are retained jointly at every time. -/
def history (x : (c : Coord V) → Ω → Value G c) (u : V) (N : ℕ) (ω : Ω) :
    Fin (N+1) → Bool × Label V :=
  fun n => (nvm x n.val u ω, source x n.val u ω)

def restrictInputs (x : (c : Coord V) → Ω → Value G c) (u : V) (N : ℕ) (ω : Ω) :
    InputState (G := G) u N := fun c => x c.val ω

private noncomputable def complete (base : (c : Coord V) → Value G c)
    (u : V) (N : ℕ) (z : InputState (G := G) u N) (c : Coord V) : Value G c := by
  classical
  exact if hc : c ∈ historyInputs (G := G) u N then z ⟨c, hc⟩ else base c

/-- The joint history reconstructed from its finite coordinate vector. -/
noncomputable def decode (base : (c : Coord V) → Value G c) (u : V) (N : ℕ)
    (z : InputState (G := G) u N) : Fin (N+1) → Bool × Label V :=
  history (fun c (_ : Unit) => complete base u N z c) u N ()

/-- The entire native history factors through a finite set of strictly positive-time inputs. -/
theorem finite_history_factorization (base : (c : Coord V) → Value G c) (u : V) (N : ℕ) :
    (∀ c ∈ historyInputs (G := G) u N, positive c) ∧
    ∀ (x : (c : Coord V) → Ω → Value G c) (ω : Ω),
      history x u N ω = decode base u N (restrictInputs x u N ω) := by
  classical
  constructor
  · intro c hc
    obtain ⟨n, _, hn⟩ := Finset.mem_biUnion.mp hc
    exact inputs_positive n u c hn
  · intro x ω
    funext n
    apply Prod.ext
    all_goals
      have he := causal_congr x
        (fun c (_ : Unit) => complete base u N (restrictInputs x u N ω) c)
        n.val u ω () (by
          intro c hc
          have hc' : c ∈ historyInputs (G := G) u N :=
            Finset.mem_biUnion.mpr ⟨n.val, Finset.mem_range.mpr n.isLt, hc⟩
          simp [complete, hc', restrictInputs])
    · exact he.1
    · exact he.2

theorem decode_measurable (base : (c : Coord V) → Value G c) (u : V) (N : ℕ) :
    Measurable (decode base u N) := by
  classical
  exact measurable_of_finite _

/-- Equal finite input laws give equal joint laws of all native opinions and sources.
The input-law premise concerns only the displayed finite set, including no fresh,
refresh or neighbour-choice coordinate at time zero. -/
private theorem history_map_eq_of_input_map_eq [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (x : (c : Coord V) → Ω → Value G c)
    (y : (c : Coord V) → Ω' → Value G c)
    (hx : ∀ c, positive c → Measurable (x c))
    (hy : ∀ c, positive c → Measurable (y c))
    (base : (c : Coord V) → Value G c) (u : V) (N : ℕ)
    (h : P.map (restrictInputs x u N) = Q.map (restrictInputs y u N)) :
    P.map (history x u N) = Q.map (history y u N) := by
  have he (ω : Ω) := (finite_history_factorization base u N).2 x ω
  have he' (ω : Ω') := (finite_history_factorization base u N).2 y ω
  have hm : Measurable (restrictInputs x u N) :=
    measurable_pi_iff.mpr (fun c => hx c.val
      ((finite_history_factorization (Ω := Ω) base u N).1 c.val c.property))
  have hm' : Measurable (restrictInputs y u N) :=
    measurable_pi_iff.mpr (fun c => hy c.val
      ((finite_history_factorization (Ω := Ω) base u N).1 c.val c.property))
  rw [show history x u N = decode base u N ∘ restrictInputs x u N from funext he,
    show history y u N = decode base u N ∘ restrictInputs y u N from funext he',
    ← Measure.map_map (decode_measurable base u N) hm,
    ← Measure.map_map (decode_measurable base u N) hm', h]

/-- A realization of the original positive-time coordinate law determines the joint
opinion-and-source history law. Unused time-zero coordinates require no law or
independence assumption. The common marginal family can in particular be the
fair opinion, noisy refresh and actual-neighbour laws. -/
theorem history_law_of_positive_coordinate_laws [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (x : (c : Coord V) → Ω → Value G c)
    (y : (c : Coord V) → Ω' → Value G c)
    (μ : (c : {c : Coord V // positive c}) → Measure (Value G c.val))
    (hx : ∀ c, positive c → Measurable (x c))
    (hy : ∀ c, positive c → Measurable (y c))
    (hix : iIndepFun (fun c : {c : Coord V // positive c} => x c.val) P)
    (hiy : iIndepFun (fun c : {c : Coord V // positive c} => y c.val) Q)
    (hlx : ∀ c : {c : Coord V // positive c}, HasLaw (x c.val) (μ c) P)
    (hly : ∀ c : {c : Coord V // positive c}, HasLaw (y c.val) (μ c) Q)
    (u : V) (N : ℕ) :
    P.map (history x u N) = Q.map (history y u N) := by
  classical
  have := hix.isProbabilityMeasure
  have hΩ : Nonempty Ω := by
    by_contra h
    have hz : (Set.univ : Set Ω) = ∅ := by
      ext ω
      exact (h ⟨ω⟩).elim
    have he : P Set.univ = 1 := measure_univ
    rw [hz, measure_empty] at he
    exact zero_ne_one he
  let base (c : Coord V) : Value G c := x c (Classical.choice hΩ)
  let inclusion (c : {c // c ∈ historyInputs (G := G) u N}) : {c : Coord V // positive c} :=
    ⟨c.val, (finite_history_factorization (Ω := Ω) base u N).1 c.val c.property⟩
  have hinj : Function.Injective inclusion := by
    intro a b h
    have hv : a.val = b.val :=
      congrArg (fun c : {c : Coord V // positive c} => c.val) h
    exact Subtype.ext hv
  have hmx : Measurable (restrictInputs x u N) :=
    measurable_pi_iff.mpr (fun c => hx c.val (inclusion c).property)
  have hmy : Measurable (restrictInputs y u N) :=
    measurable_pi_iff.mpr (fun c => hy c.val (inclusion c).property)
  have hX := (hix.precomp hinj).hasLaw_infinitePi
    (fun c => hlx (inclusion c)) hmx.aemeasurable
  have hY := (hiy.precomp hinj).hasLaw_infinitePi
    (fun c => hly (inclusion c)) hmy.aemeasurable
  exact history_map_eq_of_input_map_eq P Q x y hx hy base u N
    (hX.map_eq.trans hY.map_eq.symm)

end D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
