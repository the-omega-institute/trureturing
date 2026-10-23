/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationary binary presentations construct their original integer-time hidden and output law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
import D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function
open scoped BigOperators ENNReal Classical
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw

universe u

/-- Translation on both of the original integer clocks. -/
def shift {H : Type*} (a : ℤ) (z : PathSpace H) : PathSpace H :=
  (fun t => z.1 (a + t), fun t => z.2 (a + t))

private theorem bilateral_chain {S : Type u} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : S → ℝ≥0∞) (Q : S → S → ℝ≥0∞)
    (π_sum : ∑ s, π s = 1) (Q_sum : ∀ s, ∑ t, Q s t = 1)
    (Q_stationary : ∀ t, ∑ s, π s * Q s t = π t) :
    ∃ ν : ProbabilityMeasure (ℤ → S),
      (∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → S),
        ((ν : Measure (ℤ → S)).map (fun x (i : Fin (n + 1)) => x (t + i.val))) {w} =
          π (w 0) * ∏ i : Fin n, Q (w i.castSucc) (w i.succ)) ∧
      (∀ a : ℤ, (ν : Measure (ℤ → S)).map (fun x t => x (a + t)) = (ν : Measure (ℤ → S))) := by
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : BorelSpace S := by
    have hm : (inferInstance : MeasurableSpace S) = ⊤ :=
      top_unique (fun s _ => (Set.toFinite s).measurableSet)
    exact ⟨hm.trans borel_eq_top_of_discrete.symm⟩
  let mass (n : ℕ) (w : Fin (n + 1) → S) : ℝ≥0∞ :=
    π (w 0) * ∏ i : Fin n, Q (w i.castSucc) (w i.succ)
  have mass_cons (n : ℕ) (s : S) (w : Fin (n + 1) → S) :
      mass (n + 1) (Fin.cons s w) =
        π s * Q s (w 0) * ∏ i : Fin n, Q (w i.castSucc) (w i.succ) := by
    simp [mass, Fin.prod_univ_succ, mul_assoc]
  have mass_snoc (n : ℕ) (s : S) (w : Fin (n + 1) → S) :
      mass (n + 1) (Fin.snoc w s) = mass n w * Q (w (Fin.last n)) s := by
    simp [mass, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      -Fin.castSucc_succ, Fin.succ_castSucc, mul_assoc]
  have sum_cons (n : ℕ) (w : Fin (n + 1) → S) :
      ∑ s, mass (n + 1) (Fin.cons s w) = mass n w := by
    simp_rw [mass_cons]
    rw [← Finset.sum_mul, Q_stationary]
  have sum_snoc (n : ℕ) (w : Fin (n + 1) → S) :
      ∑ s, mass (n + 1) (Fin.snoc w s) = mass n w := by
    simp_rw [mass_snoc]
    rw [← Finset.mul_sum, Q_sum, mul_one]
  have mass_sum (n : ℕ) : ∑ w, mass n w = 1 := by
    induction n with
    | zero =>
      simpa [mass] using ((Equiv.funUnique (Fin 1) (S)).sum_comp π).trans π_sum
    | succ n ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 2) => S)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk]
      rw [Finset.sum_comm]
      simp_rw [sum_cons]
      exact ih
  let pLaw (n : ℕ) : PMF (Fin (n + 1) → S) := PMF.ofFintype (mass n) (mass_sum n)
  have tail_law (n : ℕ) : (pLaw (n + 1)).map Fin.tail = pLaw n := by
    ext w
    rw [PMF.map_apply, tsum_fintype,
      ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 2) => S)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk,
      Fin.tail_cons, pLaw, PMF.ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_cons n w
  have init_law (n : ℕ) : (pLaw (n + 1)).map Fin.init = pLaw n := by
    ext w
    rw [PMF.map_apply, tsum_fintype,
      ← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 2) => S)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk,
      Fin.init_snoc, pLaw, PMF.ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_snoc n w
  let crop (N a n : ℕ) (h : a + n ≤ N) (w : Fin (N + 1) → S) :
      Fin (n + 1) → S := fun i => w ⟨a + i.val, by omega⟩
  have crop_law (N a n : ℕ) (h : a + n ≤ N) :
      (pLaw N).map (crop N a n h) = pLaw n := by
    induction N generalizing a n with
    | zero =>
      have ha : a = 0 := by omega
      have hn : n = 0 := by omega
      subst a n
      have he : crop 0 0 0 h = id := by
        funext w i
        dsimp [crop]
        congr 1
        exact Fin.ext (Nat.zero_add _)
      rw [he, PMF.map_id]
    | succ N ih =>
      rcases a with _ | a
      · by_cases hn : n = N + 1
        · subst n
          have he : crop (N + 1) 0 (N + 1) h = id := by
            funext w i
            dsimp [crop]
            congr 1
            exact Fin.ext (Nat.zero_add _)
          rw [he, PMF.map_id]
        · have hn' : 0 + n ≤ N := by omega
          have he : crop (N + 1) 0 n h = crop N 0 n hn' ∘ Fin.init := by
            funext w i
            rfl
          rw [he, ← PMF.map_comp, init_law]
          exact ih 0 n hn'
      · have ha : a + n ≤ N := by omega
        have he : crop (N + 1) (a + 1) n h = crop N a n ha ∘ Fin.tail := by
          funext w i
          dsimp [crop, Fin.tail]
          congr 1
          apply Fin.ext
          dsimp
          omega
        rw [he, ← PMF.map_comp, tail_law]
        exact ih a n ha
  let B (l : ℕ) := Fin (2 * l + 1) → S
  let bond (l : ℕ) (w : B (l + 1)) : B l := fun i => w ⟨i.val + 1, by omega⟩
  have bond_surjective (l : ℕ) : Function.Surjective (bond l) := by
    intro w
    refine ⟨fun i => w ⟨min (i.val - 1) (2 * l), by omega⟩, ?_⟩
    funext i
    dsimp [bond]
    congr 1
    apply Fin.ext
    dsimp
    have := i.isLt
    omega
  let finiteLaw (n : ℕ) : ProbabilityMeasure (Fin (n + 1) → S) :=
    ⟨(pLaw n).toMeasure, inferInstance⟩
  let laws (l : ℕ) : ProbabilityMeasure (Fin 1 → B l) :=
    (finiteLaw (2 * l)).map (fun w _ => w)
  have laws_compatible (l : ℕ) :
      (laws (l + 1) : Measure (Fin 1 → B (l + 1))).map (fun y j => bond l (y j)) =
        (laws l : Measure (Fin 1 → B l)) := by
    change (((pLaw (2 * (l + 1))).toMeasure).map (fun w _ => w)).map
      (fun y j => bond l (y j)) = ((pLaw (2 * l)).toMeasure).map (fun w _ => w)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hb : bond l = crop (2 * (l + 1)) 1 (2 * l) (by omega) := by
      funext w i
      dsimp [bond, crop]
      congr 1
      apply Fin.ext
      dsimp
      omega
    have hc := congrArg PMF.toMeasure (crop_law (2 * (l + 1)) 1 (2 * l) (by omega))
    rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), ← hb] at hc
    rw [← hc, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  obtain ⟨threadLaw, hthread, unique_thread⟩ :=
    exists_unique_probability_extension bond bond_surjective 1 laws laws_compatible
  let T := Thread B bond
  have descend (x : T) (l m : ℕ) (h : l ≤ m) (i : Fin (2 * l + 1)) :
      x.val m ⟨i.val + (m - l), by omega⟩ = x.val l i := by
    induction h with
    | refl => simp
    | @step m h ih =>
      have hlm : l ≤ m := h
      have hstep := congrFun (x.property m) (⟨i.val + (m - l), by omega⟩ : Fin (2 * m + 1))
      dsimp [bond] at hstep
      rw [← ih, ← hstep]
      change x.val (m + 1) _ = x.val (m + 1) _
      apply congrArg (x.val (m + 1))
      apply Fin.ext
      dsimp
      omega
  let unpack (x : T) (t : ℤ) : S :=
    x.val t.natAbs ⟨(t + t.natAbs).toNat, by
      have h1 := Int.natCast_natAbs t
      have h2 := (Int.le_natAbs (a := t))
      have h3 : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
      omega⟩
  have unpack_measurable : Measurable unpack := by
    apply Measurable.of_eval
    intro t
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_subtype_coe)
  have unpack_block (x : T) (l : ℕ) (i : Fin (2 * l + 1)) :
      unpack x ((i.val : ℤ) - l) = x.val l i := by
    let t : ℤ := (i.val : ℤ) - l
    let m := max l t.natAbs
    have h1 := descend x t.natAbs m (Nat.le_max_right _ _) ⟨(t + t.natAbs).toNat, by
      have := (Int.le_natAbs (a := t))
      have : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
      omega⟩
    have h2 := descend x l m (Nat.le_max_left _ _) i
    change x.val t.natAbs _ = x.val l i
    rw [← h1, ← h2]
    apply congrArg (x.val m)
    apply Fin.ext
    dsimp
    have : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
    have hm1 : l ≤ m := Nat.le_max_left _ _
    have hm2 : t.natAbs ≤ m := Nat.le_max_right _ _
    dsimp [t] at *
    omega
  let ν : ProbabilityMeasure (ℤ → S) :=
    threadLaw.map (fun z => unpack (z 0))
  have ν_center (l : ℕ) :
      (ν : Measure (ℤ → S)).map (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) =
        (pLaw (2 * l)).toMeasure := by
    change ((threadLaw : Measure (Fin 1 → T)).map (fun z => unpack (z 0))).map _ = _
    rw [Measure.map_map (f := fun z : Fin 1 → T => unpack (z 0))
      (by fun_prop) (by exact unpack_measurable.comp (measurable_pi_apply 0))]
    have he : (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) ∘
        (fun z : Fin 1 → T => unpack (z 0)) =
        (fun w : Fin 1 → B l => w 0) ∘ levelProjection bond 1 l := by
      funext z i
      exact unpack_block (z 0) l i
    rw [he, ← Measure.map_map (f := levelProjection bond 1 l)
      (by fun_prop) (by
        exact Measurable.of_eval fun j =>
          (measurable_pi_apply l).comp
            (measurable_subtype_coe.comp (measurable_pi_apply j))), hthread]
    change (((pLaw (2 * l)).toMeasure).map (fun w (_ : Fin 1) => w)).map
      (fun w : Fin 1 → B l => w 0) = _
    rw [Measure.map_map (by fun_prop) (measurable_of_countable _)]
    exact Measure.map_id
  have ν_block (ell : ℤ) (n : ℕ) :
      (ν : Measure (ℤ → S)).map (fun x (i : Fin (n + 1)) => x (ell + i.val)) =
        (pLaw n).toMeasure := by
    let l := ell.natAbs + n
    have hel := (Int.le_natAbs (a := ell))
    have heg : -ell ≤ (ell.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -ell))
    have ha : (ell + l).toNat + n ≤ 2 * l := by dsimp [l]; omega
    have he : (fun x : ℤ → S => fun i : Fin (n + 1) => x (ell + i.val)) =
        crop (2 * l) (ell + l).toNat n ha ∘
          (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) := by
      funext x i
      dsimp [crop]
      congr 1
      dsimp [l]
      omega
    rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), ν_center,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
    exact congrArg PMF.toMeasure (crop_law (2 * l) (ell + l).toNat n ha)
  let pack (x : ℤ → S) : Fin 1 → T := fun _ =>
    ⟨fun l i => x ((i.val : ℤ) - l), fun l => by
      funext i
      dsimp [bond]
      congr 1
      omega⟩
  have pack_measurable : Measurable pack := by
    dsimp [pack]
    fun_prop
  have unpack_pack (x : ℤ → S) : unpack (pack x 0) = x := by
    funext t
    dsimp [pack, unpack]
    congr 1
    have hneg : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
    omega
  have ν_unique (ρ : ProbabilityMeasure (ℤ → S))
      (hρ : ∀ l, (ρ : Measure (ℤ → S)).map
        (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) =
        (pLaw (2 * l)).toMeasure) : ρ = ν := by
    have hu : ρ.map pack = threadLaw := by
      apply unique_thread
      intro l
      change ((ρ : Measure (ℤ → S)).map pack).map (levelProjection bond 1 l) = _
      rw [Measure.map_map (by
        exact Measurable.of_eval fun j =>
          (measurable_pi_apply l).comp
            (measurable_subtype_coe.comp (measurable_pi_apply j))) pack_measurable]
      have he : levelProjection bond 1 l ∘ pack =
          (fun w (_ : Fin 1) => w) ∘
            (fun x : ℤ → S => fun i : Fin (2 * l + 1) => x ((i.val : ℤ) - l)) := rfl
      rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), hρ]
      rfl
    have he := congrArg (fun ζ : ProbabilityMeasure (Fin 1 → T) =>
      (ζ : Measure (Fin 1 → T)).map (fun z => unpack (z 0))) hu
    change (((ρ : Measure (ℤ → S)).map pack).map (fun z => unpack (z 0))) =
      (ν : Measure (ℤ → S)) at he
    rw [Measure.map_map (by exact unpack_measurable.comp (measurable_pi_apply 0))
      pack_measurable] at he
    have hid : (fun z : Fin 1 → T => unpack (z 0)) ∘ pack = id := funext unpack_pack
    rw [hid, Measure.map_id] at he
    exact ProbabilityMeasure.toMeasure_injective he
  have ν_shift (a : ℤ) : (ν : Measure (ℤ → S)).map (fun x t => x (a + t)) = ν := by
    have hm : Measurable (fun x : ℤ → S => fun t => x (a + t)) := by fun_prop
    have hu := ν_unique (ν.map (fun x t => x (a + t))) (fun l => by
      change ((ν : Measure (ℤ → S)).map (fun x t => x (a + t))).map _ = _
      rw [Measure.map_map (by fun_prop) hm]
      have he : (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) ∘
          (fun x : ℤ → S => fun t => x (a + t)) =
          (fun x (i : Fin (2 * l + 1)) => x ((a - l) + i.val)) := by
        funext x i
        change x (a + ((i.val : ℤ) - l)) = x ((a - l) + i.val)
        congr 1
        omega
      rw [he, ν_block])
    exact congrArg ProbabilityMeasure.toMeasure hu
  refine ⟨ν, ?_, ν_shift⟩
  intro t n w
  rw [ν_block, (pLaw n).toMeasure_apply_singleton w (measurableSet_singleton w)]
  rfl


variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

private def arrival (θ : Presentation H) (s : H × Bool) : ℝ :=
  ∑ i, θ.initial i * θ.matrix s.2 i s.1

private theorem arrival_nonneg (θ : Presentation H) (s : H × Bool) : 0 ≤ arrival θ s :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (θ.initial_nonneg i) (θ.matrix_nonneg _ _ _))

private theorem arrival_sum (θ : Presentation H) (i : H) :
    ∑ b : Bool, arrival θ (i,b) = θ.initial i := by
  simp only [arrival, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  simpa only [← mul_add, add_comm] using θ.stationary i

theorem cylinder_measurable (t : ℤ) (n : ℕ)
    (h : Fin (n + 1) → H) (w : Fin n → Bool) :
    MeasurableSet (MarkedPredictiveQuotient.cylinder t n h w) := by
  simp only [MarkedPredictiveQuotient.cylinder, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun k => (measurableSet_singleton (h k)).preimage
    ((measurable_pi_apply _).comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => (measurableSet_singleton (w k)).preimage
      ((measurable_pi_apply _).comp measurable_snd))

theorem path_nonneg (θ : Presentation H) (n : ℕ)
    (h : Fin (n + 1) → H) (w : Fin n → Bool) : 0 ≤ pathMass θ.matrix n h w :=
  Finset.prod_nonneg (fun k _ => θ.matrix_nonneg _ _ _)

/-- The arriving-symbol chain realizes every original finite marked cylinder. -/
private theorem raw_law (θ : Presentation H) :
    ∃ J : ProbabilityMeasure (PathSpace H), HasOriginalCylinders (J : Measure (PathSpace H)) θ ∧
      ∀ a : ℤ, (J : Measure (PathSpace H)).map (shift a) = (J : Measure (PathSpace H)) := by
  haveI : Nonempty H := by
    by_contra hn
    haveI : IsEmpty H := not_nonempty_iff.mp hn
    have he := θ.initial_sum
    simp at he
  let π : H × Bool → ℝ≥0∞ := fun s => ENNReal.ofReal (arrival θ s)
  let Q : (H × Bool) → (H × Bool) → ℝ≥0∞ := fun s t =>
    ENNReal.ofReal (θ.matrix t.2 s.1 t.1)
  have hπ : ∑ s, π s = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => arrival_nonneg θ s)]
    have he : ∑ s, arrival θ s = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [arrival_sum]
      exact θ.initial_sum
    rw [he]; simp
  have hQ (s : H × Bool) : ∑ t, Q s t = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => θ.matrix_nonneg _ _ _)]
    have he : ∑ t : H × Bool, θ.matrix t.2 s.1 t.1 = 1 := by
      rw [Fintype.sum_prod_type]
      simpa only [Fintype.sum_bool, add_comm] using θ.stochastic s.1
    rw [he]; simp
  have hstat (t : H × Bool) : ∑ s, π s * Q s t = π t := by
    simp_rw [π, Q, ← ENNReal.ofReal_mul (arrival_nonneg θ _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ =>
      mul_nonneg (arrival_nonneg θ s) (θ.matrix_nonneg _ _ _))]
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul, arrival_sum]
    rfl
  obtain ⟨ν, hν, hsν⟩ := bilateral_chain π Q hπ hQ hstat
  let decode : (ℤ → H × Bool) → PathSpace H := fun z =>
    (fun t => (z t).1, fun t => (z (t + 1)).2)
  have hd : Measurable decode := by dsimp [decode]; fun_prop
  let J : ProbabilityMeasure (PathSpace H) := ν.map decode
  refine ⟨J, ?_, ?_⟩
  · intro t n h w
    let v (b : Bool) : Fin (n + 1) → H × Bool :=
      Fin.cons (h 0,b) (fun k => (h k.succ, w k))
    have hv (b : Bool) (k : Fin (n + 1)) : (v b k).1 = h k := by
      refine Fin.cases ?_ (fun i => ?_) k <;> rfl
    have hvs (b : Bool) (k : Fin n) : (v b k.succ).2 = w k := rfl
    let ev : (ℤ → H × Bool) → (Fin (n + 1) → H × Bool) :=
      fun z k => z (t + k.val)
    have hm : Measurable ev := by dsimp [ev]; fun_prop
    have he : decode ⁻¹' MarkedPredictiveQuotient.cylinder t n h w =
        ev ⁻¹' {v false} ∪ ev ⁻¹' {v true} := by
      ext z
      simp only [Set.mem_preimage, MarkedPredictiveQuotient.cylinder, Set.mem_setOf_eq,
        Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hh, hw⟩
        have hz : ev z = v ((z t).2) := by
          funext k
          refine Fin.cases ?_ (fun i => ?_) k
          · exact Prod.ext (by simpa [ev, decode, v] using hh 0) (by simp [ev, v])
          · apply Prod.ext
            · exact hh i.succ
            · simpa [decode, ev, v, show t + (i.val : ℤ) + 1 =
                t + (i.succ.val : ℤ) by simp; omega] using hw i
        cases hb : (z t).2
        · exact Or.inl (by simpa [hb] using hz)
        · exact Or.inr (by simpa [hb] using hz)
      · intro hz
        have hb : ∃ b, ev z = v b := by
          rcases hz with hz | hz
          · exact ⟨false,hz⟩
          · exact ⟨true,hz⟩
        obtain ⟨b,hb⟩ := hb
        constructor
        · intro k
          exact (congrArg Prod.fst (congrFun hb k)).trans (hv b k)
        · intro k
          have hh := congrArg Prod.snd (congrFun hb k.succ)
          simpa [decode, ev, v, show t + (k.val : ℤ) + 1 =
            t + (k.succ.val : ℤ) by simp; omega] using hh
    have hdis : Disjoint (ev ⁻¹' {v false}) (ev ⁻¹' {v true}) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      have hh : v false = v true := hz.symm.trans hz'
      have hh' := congrArg (fun f => (f 0).2) hh
      exact Bool.noConfusion hh'
    have hmass (b : Bool) : (ν : Measure _) (ev ⁻¹' {v b}) =
        π (h 0,b) * ENNReal.ofReal (pathMass θ.matrix n h w) := by
      rw [← Measure.map_apply hm (measurableSet_singleton _), hν]
      change π (h 0,b) * (∏ k : Fin n, Q (v b k.castSucc) (v b k.succ)) = _
      congr 1
      unfold pathMass
      rw [ENNReal.ofReal_prod_of_nonneg (fun k _ => θ.matrix_nonneg (w k) (h k.castSucc) (h k.succ))]
      apply Finset.prod_congr rfl
      intro k _
      change ENNReal.ofReal (θ.matrix (v b k.succ).2 (v b k.castSucc).1 (v b k.succ).1) = _
      rw [hvs, hv, hv]
    have hj : (J : Measure _) (MarkedPredictiveQuotient.cylinder t n h w) =
        ENNReal.ofReal (θ.initial (h 0) * pathMass θ.matrix n h w) := by
      change (ν : Measure _).map decode _ = _
      rw [Measure.map_apply hd (cylinder_measurable t n h w), he,
        measure_union hdis ((measurableSet_singleton _).preimage hm), hmass, hmass,
        ← add_mul, ENNReal.ofReal_mul (θ.initial_nonneg _)]
      congr 1
      change ENNReal.ofReal (arrival θ (h 0,false)) +
        ENNReal.ofReal (arrival θ (h 0,true)) = _
      rw [← ENNReal.ofReal_add (arrival_nonneg θ _) (arrival_nonneg θ _)]
      congr 1
      simpa only [Fintype.sum_bool, add_comm] using arrival_sum θ (h 0)
    exact (congrArg ENNReal.toReal hj).trans
      (ENNReal.toReal_ofReal (mul_nonneg (θ.initial_nonneg _) (path_nonneg θ n h w)))
  · intro a
    change ((ν : Measure _).map decode).map (shift a) = (ν : Measure _).map decode
    rw [Measure.map_map (by
      exact (Measurable.of_eval fun t => (measurable_pi_apply (a + t)).comp measurable_fst).prodMk
        (Measurable.of_eval fun t => (measurable_pi_apply (a + t)).comp measurable_snd)) hd]
    have he : shift a ∘ decode = decode ∘ (fun z t => z (a + t)) := by
      funext z
      apply Prod.ext <;> funext t
      · rfl
      · dsimp [shift, decode]
        congr 2
        omega
    rw [he, ← Measure.map_map hd (by fun_prop), hsν]


/-- The original finite output event, with an empty observation at length zero. -/
def visibleCylinder (t : ℤ) (n : ℕ) (w : Fin n → Bool) : Set (ℤ → Bool) :=
  {z | ∀ k, z (t + (k.val : ℤ)) = w k}

theorem sum_path_tails (θ : Presentation H) (n : ℕ) (i : H) (w : Fin n → Bool) :
    (∑ h : Fin n → H, pathMass θ.matrix n (Fin.cons i h) w) =
      futureMass θ.matrix i n w := by
  induction n generalizing i with
  | zero => simp [pathMass, futureMass, wordMatrix, Matrix.one_apply]
  | succ n ih =>
    rw [sum_paths]
    calc
      _ = ∑ j, θ.matrix (w 0) i j * futureMass θ.matrix j n (Fin.tail w) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [path_step, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
        rw [← Finset.mul_sum, ih]
      _ = _ := by
        simp only [futureMass, wordMatrix, Matrix.mul_apply]
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm

theorem visible_masses (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (hc : HasOriginalCylinders J θ) (t : ℤ) (n : ℕ) (w : Fin n → Bool) :
    (J.map Prod.snd).real (visibleCylinder t n w) =
      ∑ i, θ.initial i * futureMass θ.matrix i n w := by
  have hv : MeasurableSet (visibleCylinder t n w) := by
    simp only [visibleCylinder, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => (measurableSet_singleton (w k)).preimage
      (measurable_pi_apply _)
  have he : Prod.snd ⁻¹' visibleCylinder t n w =
      ⋃ h : Fin (n + 1) → H, MarkedPredictiveQuotient.cylinder t n h w := by
    ext z
    simp only [Set.mem_preimage, visibleCylinder, MarkedPredictiveQuotient.cylinder,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun hz => ⟨(fun k => z.1 (t + k.val)), fun _ => rfl, hz⟩,
      fun ⟨_,_,hw⟩ => hw⟩
  have hdis : Pairwise (fun h k : Fin (n + 1) → H =>
      Disjoint (MarkedPredictiveQuotient.cylinder t n h w)
        (MarkedPredictiveQuotient.cylinder t n k w)) := by
    intro h k hne
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hne (funext fun j => (hz.1 j).symm.trans (hz'.1 j))
  rw [measureReal_def, Measure.map_apply measurable_snd hv, he]
  change J.real _ = _
  rw [measureReal_iUnion_fintype hdis (fun h => cylinder_measurable t n h w)]
  have hf (h : Fin (n + 1) → H) : J.real (MarkedPredictiveQuotient.cylinder t n h w) =
      θ.initial (h 0) * pathMass θ.matrix n h w := hc t n h w
  simp_rw [hf]
  rw [sum_paths]
  simp_rw [Fin.cons_zero, ← Finset.mul_sum, sum_path_tails]

theorem visible_no11 (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (hc : HasOriginalCylinders J θ) :
    ∀ᵐ z ∂(J.map Prod.snd), ∀ t : ℤ, ¬(z t = true ∧ z (t + 1) = true) := by
  rw [ae_all_iff]
  intro t
  have hz : (J.map Prod.snd).real (visibleCylinder t 2 (fun _ => true)) = 0 := by
    rw [visible_masses θ J hc]
    simpa [futureMass, wordMatrix, Matrix.mul_one, Finset.mul_sum, Fin.tail] using θ.no11
  have he : {z : ℤ → Bool | ¬ ¬(z t = true ∧ z (t + 1) = true)} =
      visibleCylinder t 2 (fun _ => true) := by
    ext z
    simp only [not_not, visibleCylinder, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0,h1⟩ k
      fin_cases k <;> simpa
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
  rw [ae_iff, he]
  exact (measureReal_eq_zero_iff).mp hz


/-- Every original presentation has a stationary integer-time law with its
entire original cylinder family and its actual no11 visible pushforward. -/
theorem original_law (θ : Presentation H) :
    ∃ J : ProbabilityMeasure (PathSpace H),
      HasOriginalCylinders (J : Measure (PathSpace H)) θ ∧
      (∀ a : ℤ, (J : Measure (PathSpace H)).map (shift a) = J) ∧
      (∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
        ((J : Measure (PathSpace H)).map Prod.snd).real (visibleCylinder t n w) =
          ∑ i, θ.initial i * futureMass θ.matrix i n w) ∧
      (∀ᵐ z ∂((J : Measure (PathSpace H)).map Prod.snd),
        ∀ t : ℤ, ¬(z t = true ∧ z (t + 1) = true)) := by
  obtain ⟨J,hc,hs⟩ := raw_law θ
  exact ⟨J,hc,hs,visible_masses θ (J : Measure _) hc,visible_no11 θ (J : Measure _) hc⟩

#print axioms original_law
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
