/- GID: D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/PotentialPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unstopped potential paths identify native survival and the first fresh source. -/

/-
proof_shape: potential_path_source_correspondence: content; original_potential_path_bounds: content
admission_basis: escape-witness
escape_witness: prefix_source; A_survives
Reuse: native_source, source_birth_le, survives_iff_old_source, survival_probability,
collision_probability_le, native_variance_lower, finite_history_factorization and
history_law_of_positive_coordinate_laws; Mathlib IdentDistrib and infinitePi.
No literature-originality claim is made.
Declaration | proof_shape | witness | live consumer(s).
path | construction | none | path_tail, A, prefix_source, potential_path_source_correspondence
A | construction | none | A_step, A_survives, potential_path_source_correspondence, original_potential_path_bounds
path_tail | content | path_tail | A_step
A_step | content | path_tail | A_survives
source_nonrefresh | bind-only | none | prefix_source
source_refresh | bind-only | none | potential_path_source_correspondence
prefix_source | content | prefix_source | potential_path_source_correspondence
A_survives | content | A_survives | potential_path_source_correspondence
potential_path_source_correspondence | content | prefix_source, A_survives | original_potential_path_bounds
history_measurable_positive | bind-only | none | original_potential_path_bounds
original_potential_path_bounds | content | A_survives | terminal original-space probability and variance chain
-/

import D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport
import Mathlib.Probability.IdentDistrib

/-! # Unstopped potential copy paths

The path follows choices even after a refresh. Only offsets strictly smaller
than the lag inspect controls; the endpoint's refresh is not inspected.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
open RepetitionVarianceLinear AncestralSources FiniteCausalInputs

variable {V Ω : Type} {G : SimpleGraph V}

/-- Offset k of the potential path starting at absolute time n. -/
def path (x : (c : Coord V) → Ω → Value G c) (n : ℕ) (u : V) (ω : Ω) : ℕ → V
  | 0 => u
  | k+1 => (x (.choice (n-k) (path x n u ω k)) ω).val

/-- The independently defined conjunction of the d inspected nonrefresh controls. -/
def A (x : (c : Coord V) → Ω → Value G c) (i d : ℕ) (u : V) (ω : Ω) : Prop :=
  ∀ k < d, x (.refresh (i+d-k) (path x (i+d) u ω k)) ω = false

private theorem path_tail (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (u : V) (ω : Ω) : ∀ k,
    path x (n+1) u ω (k+1) = path x n (x (.choice (n+1) u) ω).val ω k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change (x (.choice ((n+1)-(k+1)) (path x (n+1) u ω (k+1))) ω).val =
      (x (.choice (n-k) (path x n (x (.choice (n+1) u) ω).val ω k)) ω).val
    rw [ih, Nat.add_sub_add_right]

private theorem A_step (x : (c : Coord V) → Ω → Value G c)
    (i d : ℕ) (u : V) (ω : Ω) :
    A x i (d+1) u ω ↔ x (.refresh (i+d+1) u) ω = false ∧
      A x i d (x (.choice (i+d+1) u) ω).val ω := by
  unfold A
  rw [show i+(d+1) = (i+d)+1 by omega]
  constructor
  · intro h
    refine ⟨by simpa only [Nat.sub_zero, path] using h 0 (by omega), ?_⟩
    intro k hk
    have hh := h (k+1) (by omega)
    rw [path_tail, Nat.add_sub_add_right] at hh
    exact hh
  · rintro ⟨h₀, h⟩ k hk
    cases k with
    | zero => simpa only [Nat.sub_zero, path] using h₀
    | succ k =>
      rw [path_tail, Nat.add_sub_add_right]
      exact h k (by omega)

private theorem source_nonrefresh (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (hn : 0 < n) (v : V) (ω : Ω)
    (hr : x (.refresh n v) ω = false) :
    source x n v ω = source x (n-1) (x (.choice n v) ω).val ω := by
  cases n with
  | zero => omega
  | succ n => simp [source, hr]

private theorem source_refresh (x : (c : Coord V) → Ω → Value G c)
    (n : ℕ) (hn : 0 < n) (v : V) (ω : Ω)
    (hr : x (.refresh n v) ω = true) :
    source x n v ω = .inr ((⟨n, hn⟩ : ℕ+), v) := by
  cases n with
  | zero => omega
  | succ n => simp [source, hr]

private theorem prefix_source (x : (c : Coord V) → Ω → Value G c) :
    ∀ k n u ω, k ≤ n →
    (∀ j < k, x (.refresh (n-j) (path x n u ω j)) ω = false) →
    source x n u ω = source x (n-k) (path x n u ω k) ω := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro n u ω hkn h
    rw [ih n u ω (by omega) (fun j hj => h j (by omega))]
    rw [source_nonrefresh x (n-k) (by omega) _ ω (h k (by omega))]
    simp only [path, Nat.sub_sub]

private theorem A_survives (x : (c : Coord V) → Ω → Value G c) (i : ℕ) :
    ∀ d u ω, A x i d u ω ↔ survives x i d u ω = true := by
  intro d
  induction d with
  | zero => intros; simp [A, survives]
  | succ d ih =>
    intro u ω
    rw [A_step]
    simp only [survives]
    cases x (.refresh (i+d+1) u) ω <;> simp [ih]

/-- Full potential-path/source correspondence, with both extreme first-refresh offsets. -/
theorem potential_path_source_correspondence (x : (c : Coord V) → Ω → Value G c)
    (i d : ℕ) (u : V) (ω : Ω) :
    path x (i+d) u ω 0 = u ∧
    (∀ k < d, path x (i+d) u ω (k+1) =
      (x (.choice (i+d-k) (path x (i+d) u ω k)) ω).val) ∧
    (A x i d u ω ↔ survives x i d u ω = true) ∧
    (A x i d u ω ↔ birth (source x (i+d) u ω) ≤ i) ∧
    (A x i d u ω → source x (i+d) u ω = source x i (path x (i+d) u ω d) ω) ∧
    (∀ k (hk : k < d),
      (∀ j < k, x (.refresh (i+d-j) (path x (i+d) u ω j)) ω = false) →
      x (.refresh (i+d-k) (path x (i+d) u ω k)) ω = true →
      source x (i+d) u ω = .inr (⟨i+d-k, by omega⟩, path x (i+d) u ω k) ∧
      i < birth (source x (i+d) u ω)) ∧
    (¬ A x i d u ω → ∃ k < d,
      (∀ j < k, x (.refresh (i+d-j) (path x (i+d) u ω j)) ω = false) ∧
      x (.refresh (i+d-k) (path x (i+d) u ω k)) ω = true) ∧
    (source x i u ω = source x (i+d) u ω → A x i d u ω) := by
  classical
  have he := A_survives x i d u ω
  have hb := he.trans (survives_iff_old_source x i d u ω)
  refine ⟨rfl, fun _ _ => rfl, he, hb, ?_, ?_, ?_, ?_⟩
  · intro h
    simpa only [Nat.add_sub_cancel_right] using prefix_source x d (i+d) u ω (by omega) h
  · intro k hk hprev hr
    have hs := prefix_source x k (i+d) u ω (by omega) hprev
    have hf : source x (i+d) u ω =
        .inr (⟨i+d-k, by omega⟩, path x (i+d) u ω k) := by
      exact hs.trans (source_refresh x (i+d-k) (by omega) _ ω hr)
    exact ⟨hf, by rw [hf]; dsimp [birth]; omega⟩
  · intro h
    have hex : ∃ k, k < d ∧ x (.refresh (i+d-k) (path x (i+d) u ω k)) ω = true := by
      simpa only [A, not_forall, exists_prop, Bool.not_eq_false] using h
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    refine ⟨k, hk.1, ?_, hk.2⟩
    intro j hj
    have hh := Nat.find_min hex hj
    have hnot : x (.refresh (i+d-j) (path x (i+d) u ω j)) ω ≠ true :=
      fun ht => hh ⟨by omega, ht⟩
    exact Bool.eq_false_iff.mpr hnot
  · intro h
    apply hb.mpr
    rw [← h]
    exact source_birth_le x i u ω

private theorem history_measurable_positive [G.LocallyFinite] [MeasurableSpace Ω]
    (x : (c : Coord V) → Ω → Value G c)
    (hx : ∀ c, positive c → Measurable (x c))
    (base : (c : Coord V) → Value G c) (u : V) (N : ℕ) :
    Measurable (history x u N) := by
  have he : history x u N = decode base u N ∘ restrictInputs x u N :=
    funext ((finite_history_factorization base u N).2 x)
  rw [he]
  exact (decode_measurable base u N).comp (measurable_pi_iff.mpr (fun c =>
    hx c.val ((finite_history_factorization (Ω := Ω) base u N).1 c.val c.property)))

/-- Potential-path probability and the native variance chain on the original positive-time law.
No assumption mentions the unused fresh, refresh or choice slots at time zero. -/
theorem original_potential_path_bounds [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G.Connected)
    (hNbr : ∀ v, ∃ w, G.Adj v w) (ε : unitInterval)
    (hε : 0 < (ε : ℝ)) (hε' : (ε : ℝ) < 1)
    (x : (c : Coord V) → Ω → Value G c)
    (hx : ∀ c, positive c → Measurable (x c))
    (hi : iIndepFun (fun c : {c : Coord V // positive c} => x c.val) P)
    (hl : ∀ c : {c : Coord V // positive c},
      HasLaw (x c.val) (coordinateLaw G ε hNbr c.val) P)
    (u : V) (d t : ℕ) :
    (∀ i : ℕ, MeasurableSet {ω | A x i d u ω} ∧
      P {ω | A x i d u ω} = (unitInterval.toNNReal (unitInterval.symm ε) : ℝ≥0∞)^d ∧
      {ω | source x i u ω = source x (i+d) u ω} ⊆ {ω | A x i d u ω} ∧
      P {ω | source x i u ω = source x (i+d) u ω} ≤
        (unitInterval.toNNReal (unitInterval.symm ε) : ℝ≥0∞)^d ∧
      1 - (1-(ε : ℝ))^d ≤ P.real {ω | source x i u ω ≠ source x (i+d) u ω}) ∧
    ((1/4 : ℝ) * ∑ i ∈ Finset.Icc 1 t,
      P.real {ω | source x i u ω ≠ source x (i+d) u ω} ≤ variance (W x u d t) P) ∧
    ((t : ℝ) * (1-(1-(ε : ℝ))^d) / 4 ≤
      (1/4 : ℝ) * ∑ i ∈ Finset.Icc 1 t,
        P.real {ω | source x i u ω ≠ source x (i+d) u ω}) := by
  classical
  have : Countable V := RectangularSupport.vertices_countable hG u
  let S := (c : Coord V) → Value G c
  let Q : Measure S := Measure.infinitePi (coordinateLaw G ε hNbr)
  let y (c : Coord V) (z : S) : Value G c := z c
  let M : Model G Q := {
    probability := inferInstance
    connected := hG
    hasNeighbor := hNbr
    ε := ε
    positiveNoise := hε
    belowOne := hε'
    coordinate := y
    measurable_coordinate := fun c => measurable_pi_apply c
    independent := iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
    laws := fun c => ⟨(measurable_pi_apply c).aemeasurable,
      (measurePreserving_eval_infinitePi (coordinateLaw G ε hNbr) c).map_eq⟩ }
  let base (c : Coord V) : Value G c :=
    match c with
    | .initial _ | .fresh _ _ | .refresh _ _ => false
    | .choice _ v => ⟨(hNbr v).choose, (hNbr v).choose_spec⟩
  have hy (c : Coord V) : Measurable (y c) := measurable_pi_apply c
  have hiy : iIndepFun (fun c : {c : Coord V // positive c} => y c.val) Q :=
    M.independent.precomp Subtype.val_injective
  have hid (N : ℕ) : IdentDistrib (history x u N) (history y u N) P Q := {
    aemeasurable_fst := (history_measurable_positive x hx base u N).aemeasurable
    aemeasurable_snd := (history_measurable_positive y (fun c _ => hy c) base u N).aemeasurable
    map_eq := history_law_of_positive_coordinate_laws P Q x y
      (fun c => coordinateLaw G ε hNbr c.val) hx (fun c _ => hy c) hi hiy hl
        (fun c => M.laws c.val) u N }
  have hcol (i : ℕ) :
      P {ω | source x i u ω = source x (i+d) u ω} =
      Q {z | source y i u z = source y (i+d) u z} := by
    let B : Set (Fin (i+d+1) → Bool × Label V) :=
      {z | (z ⟨i, by omega⟩).2 = (z ⟨i+d, by omega⟩).2}
    exact (hid (i+d)).measure_mem_eq (s := B) (Set.to_countable B).measurableSet
  have hcolmeas (i : ℕ) :
      MeasurableSet {ω | source x i u ω = source x (i+d) u ω} := by
    let B : Set (Fin (i+d+1) → Bool × Label V) :=
      {z | (z ⟨i, by omega⟩).2 = (z ⟨i+d, by omega⟩).2}
    exact (history_measurable_positive x hx base u (i+d))
      ((Set.to_countable B).measurableSet)
  have hA (i : ℕ) : MeasurableSet {ω | A x i d u ω} ∧
      P {ω | A x i d u ω} = (unitInterval.toNNReal (unitInterval.symm ε) : ℝ≥0∞)^d := by
    let B : Set (Fin (i+d+1) → Bool × Label V) :=
      {z | birth (z ⟨i+d, by omega⟩).2 ≤ i}
    have hset : {ω | A x i d u ω} = history x u (i+d) ⁻¹' B := by
      ext ω
      exact (potential_path_source_correspondence x i d u ω).2.2.2.1
    have hsetQ : {z | survives y i d u z = true} = history y u (i+d) ⁻¹' B := by
      ext z
      exact survives_iff_old_source y i d u z
    refine ⟨hset ▸ (history_measurable_positive x hx base u (i+d))
      ((Set.to_countable B).measurableSet), ?_⟩
    rw [hset, (hid (i+d)).measure_mem_eq (Set.to_countable B).measurableSet, ← hsetQ]
    exact survival_probability Q M i d u
  have hnoncol (i : ℕ) : P.real {ω | source x i u ω ≠ source x (i+d) u ω} =
      1 - Q.real {z | source y i u z = source y (i+d) u z} := by
    rw [show {ω | source x i u ω ≠ source x (i+d) u ω} =
      {ω | source x i u ω = source x (i+d) u ω}ᶜ from rfl,
      measureReal_compl (hcolmeas i)]
    simp only [Measure.real, hcol, measure_univ, ENNReal.toReal_one]
  have hlo (i : ℕ) :
      1 - (1-(ε : ℝ))^d ≤ P.real {ω | source x i u ω ≠ source x (i+d) u ω} := by
    rw [hnoncol]
    apply sub_le_sub_left
    have hh := ENNReal.toReal_mono
      (show (unitInterval.toNNReal (unitInterval.symm ε) : ℝ≥0∞)^d ≠ ⊤ by finiteness)
      (collision_probability_le Q M i d u)
    simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.coe_toReal,
      unitInterval.coe_toNNReal, unitInterval.coe_symm_eq] using hh
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨(hA i).1, (hA i).2, ?_, ?_, hlo i⟩
    · intro ω h
      exact (potential_path_source_correspondence x i d u ω).2.2.2.2.2.2.2 h
    · rw [hcol]
      exact collision_probability_le Q M i d u
  · have hv : variance (W x u d t) P = variance (W y u d t) Q := by
      let N := t+d
      let f (z : Fin (N+1) → Bool × Label V) : ℝ :=
        ∑ j ∈ Finset.Icc 1 t,
          if (z ⟨min j N, by omega⟩).1 = (z ⟨min (j+d) N, by omega⟩).1 then 1 else 0
      have hf : Measurable f := measurable_of_countable f
      have he (z : (c : Coord V) → Ω → Value G c) (ω : Ω) :
          f (history z u N ω) = W z u d t ω := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjt := (Finset.mem_Icc.mp hj).2
        simp only [history, Nat.min_eq_left (show j ≤ N by dsimp [N]; omega),
          Nat.min_eq_left (show j+d ≤ N by dsimp [N]; omega)]
      have heQ (z : S) : f (history y u N z) = W y u d t z := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjt := (Finset.mem_Icc.mp hj).2
        simp only [history, Nat.min_eq_left (show j ≤ N by dsimp [N]; omega),
          Nat.min_eq_left (show j+d ≤ N by dsimp [N]; omega)]
      simpa only [Function.comp_def, he, heQ] using ((hid N).comp hf).variance_eq
    rw [hv]
    simpa only [hnoncol, M] using native_variance_lower Q M u d t
  · have hh := Finset.sum_le_sum (s := Finset.Icc 1 t) (fun i _ => hlo i)
    have hs : (t : ℝ) * (1-(1-(ε : ℝ))^d) ≤
        ∑ i ∈ Finset.Icc 1 t, P.real {ω | source x i u ω ≠ source x (i+d) u ω} := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
        Nat.add_sub_cancel_right] at hh
      nlinarith
    nlinarith

end D5.S3.StatisticalMechanics.NoisyVoter.PotentialPaths
