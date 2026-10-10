/- GID: D5/S3/Arith/AffineNetworks/AffineModularBehavior
   generality: G
   mirror-B: D5/B/S3/Arith/AffineNetworks/AffineModularBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual path and adaptive transcripts have the exact all-path congruence boundary. -/

import D5.S3.Arith.AffineNetworks.AffineModularStopping
import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.AffineNetworks.AffineModularBehavior

open Quiver
open D5.S3.Arith.AffineNetworks.AffineModularStopping
open D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

/-- A public event records a named edge or a vertex and its actual port answer. -/
inductive Event (N : Network) where
  | edge (e : N.E)
  | port (v : N.V) (answer : ZMod (N.d v))

/-- A fixed legal path records the initial port and every subsequent edge and port. -/
def pathTranscript {N : Network} : ∀ {v w : N.V},
    NPath N v w → ZMod N.m → List (Event N)
  | v, _, .nil, t => [.port v (portRead N v t)]
  | _, w, .cons q e, t => pathTranscript q t ++
      [.edge e.1, .port w (portRead N w (pathRun (q.cons e) t))]

/-- Physical phase is stored separately from public history and internal control. -/
structure Execution (N : Network) (Control : Type) where
  vertex : N.V
  phase : ZMod N.m
  control : Control
  history : List (Event N)
  halted : Bool

/-- The selector sees only the current public vertex, history and internal control.
Its dependent edge result enforces legality without inspecting the hidden phase. -/
def step {N : Network} {Control : Type}
    (select : (v : N.V) → List (Event N) → Control →
      Option ({e : N.E // N.src e = v} × Control))
    (s : Execution N Control) : Execution N Control :=
  if s.halted then s else
    match select s.vertex s.history s.control with
    | none => {s with halted := true}
    | some (e, control) =>
        let phase := (N.a e.1 : ZMod N.m) * s.phase + N.c e.1
        ⟨N.dst e.1, phase, control,
          s.history ++ [.edge e.1, .port (N.dst e.1) (portRead N (N.dst e.1) phase)],
          false⟩

/-- A finite horizon includes the initial observation; halting is absorbing. -/
def execute {N : Network} {Control : Type}
    (select : (v : N.V) → List (Event N) → Control →
      Option ({e : N.E // N.src e = v} × Control))
    (n : ℕ) (v : N.V) (t : ZMod N.m) (control : Control) : Execution N Control :=
  (step select)^[n] ⟨v, t, control, [.port v (portRead N v t)], false⟩

/-- The actual congruence boundary, using the independent original all-path modulus. -/
noncomputable def boundary (N : Network) (v : N.V) : ZMod N.m → ZMod (allPathModulus N v) :=
  ZMod.castHom ((theorem11_3 N).1 v).2 _

/-- The complete deterministic all-path boundary theorem, including all finite legal
adaptive protocols with a common internal initial state and minimum realized size. -/
theorem theorem11_2 (N : Network) (v : N.V) :
    (0 < allPathModulus N v ∧ allPathModulus N v ∣ N.m) ∧
    (∀ t t' : ZMod N.m,
      (∀ (w : N.V) (p : NPath N v w), pathTranscript p t = pathTranscript p t') ↔
        boundary N v t = boundary N v t') ∧
    (∀ t t' : ZMod N.m,
      (∀ (Control : Type)
        (select : (w : N.V) → List (Event N) → Control →
          Option ({e : N.E // N.src e = w} × Control))
        (control : Control) (n : ℕ),
        (execute select n v t control).history =
          (execute select n v t' control).history) ↔
        boundary N v t = boundary N v t') ∧
    Function.Surjective (boundary N v) ∧
    Nat.card (Set.range (boundary N v)) = allPathModulus N v ∧
    (∀ (State : Type) (readout : ZMod N.m → State),
      (∀ t t', readout t = readout t' →
        ∀ (w : N.V) (p : NPath N v w), pathTranscript p t = pathTranscript p t') →
      allPathModulus N v ≤ Nat.card (Set.range readout)) := by
  classical
  let : NeZero N.m := ⟨N.hm.ne'⟩
  have hd := (theorem11_3 N).1 v
  let : NeZero (allPathModulus N v) := ⟨hd.1.ne'⟩
  have difference : ∀ {i j : N.V} (p : NPath N i j) (t t' : ZMod N.m),
      pathRun p t' - pathRun p t = (pathMultiplier p : ZMod N.m) * (t' - t) := by
    intro i j p t t'
    induction p with
    | nil => simp [pathRun, pathMultiplier]
    | cons q e ih =>
        have hm : pathMultiplier (q.cons e) = pathMultiplier q * N.a e.1 :=
          Path.weight_cons _ q e
        simp only [pathRun, hm, Nat.cast_mul]
        calc
          _ = (N.a e.1 : ZMod N.m) * (pathRun q t' - pathRun q t) := by ring
          _ = _ := by rw [ih]; ring
  have attenuation (d a x : ℕ) (h : 0 < d) :
      d / Nat.gcd d a ∣ x ↔ d ∣ a * x := by
    rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left d a)
      (Nat.gcd_pos_of_pos_left a h), Nat.dvd_gcd_mul_iff_dvd_mul]
  have quotient_dvd : ∀ {i j : N.V} (p : NPath N i j), pathQuotient p ∣ N.m := by
    intro i j p
    exact (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)).trans (N.hd j).2
  have image_mem (q : ℕ) : q ∈ allPathDivisorImage N v ↔
      ∃ (w : N.V) (p : NPath N v w), pathQuotient p = q := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · rintro ⟨w, p, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨quotient_dvd p, N.hm.ne'⟩, w, p, rfl⟩
  have cast_kernel (d : ℕ) (h : d ∣ N.m) (t t' : ZMod N.m) :
      ZMod.castHom h (ZMod d) t = ZMod.castHom h (ZMod d) t' ↔
        d ∣ ((t'.val : ℤ) - (t.val : ℤ)).natAbs := by
    have ht : ((t.val : ℤ) : ZMod N.m) = t := by
      simp
    have ht' : ((t'.val : ℤ) : ZMod N.m) = t' := by
      simp
    rw [← ht, ← ht']
    simp only [map_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd]
    simp only [ht, ht']
  have endpoint : ∀ {i j : N.V} (p : NPath N i j) (t t' : ZMod N.m),
      portRead N j (pathRun p t) = portRead N j (pathRun p t') ↔
        pathQuotient p ∣ ((t'.val : ℤ) - (t.val : ℤ)).natAbs := by
    intro i j p t t'
    have rep : (ZMod.castHom (N.hd j).2 (ZMod (N.d j))) (t' - t) =
        (((t'.val : ℤ) - (t.val : ℤ) : ℤ) : ZMod (N.d j)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val t', ← ZMod.natCast_zmod_val t]
      simp only [map_sub, map_natCast, Int.cast_sub, Int.cast_natCast]
    calc
      _ ↔ (portRead N j (pathRun p t') - portRead N j (pathRun p t)) = 0 := by
        rw [sub_eq_zero, eq_comm]
      _ ↔ (ZMod.castHom (N.hd j).2 (ZMod (N.d j)))
          (pathRun p t' - pathRun p t) = 0 := by rw [map_sub]; rfl
      _ ↔ ((pathMultiplier p : ℤ) * ((t'.val : ℤ) - (t.val : ℤ)) : ℤ) =
          (0 : ZMod (N.d j)) := by
        rw [difference, map_mul, map_natCast, rep]
        simp only [Int.cast_mul, Int.cast_natCast]
      _ ↔ (N.d j : ℤ) ∣ (pathMultiplier p : ℤ) * ((t'.val : ℤ) - (t.val : ℤ)) := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      _ ↔ _ := by
        rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
        exact (attenuation _ _ _ (N.hd j).1).symm
  have all_endpoints (t t' : ZMod N.m) :
      (∀ (w : N.V) (p : NPath N v w),
        portRead N w (pathRun p t) = portRead N w (pathRun p t')) ↔
        boundary N v t = boundary N v t' := by
    rw [boundary, cast_kernel]
    change _ ↔ (allPathDivisorImage N v).lcm id ∣ _
    rw [Finset.lcm_dvd_iff]
    constructor
    · intro h q hq
      obtain ⟨w, p, rfl⟩ := (image_mem q).mp hq
      exact (endpoint p t t').mp (h w p)
    · intro h w p
      exact (endpoint p t t').mpr (h _ ((image_mem _).mpr ⟨w, p, rfl⟩))
  have last_port : ∀ {i j : N.V} (p : NPath N i j) (t : ZMod N.m),
      (pathTranscript p t).getLast? = some (.port j (portRead N j (pathRun p t))) := by
    intro i j p t
    cases p <;> simp [pathTranscript, pathRun]
  have transcript_kernel (t t' : ZMod N.m) :
      (∀ (w : N.V) (p : NPath N v w), pathTranscript p t = pathTranscript p t') ↔
        boundary N v t = boundary N v t' := by
    rw [← all_endpoints]
    constructor
    · intro h w p
      have hlast := congrArg List.getLast? (h w p)
      rw [last_port, last_port] at hlast
      exact eq_of_heq (Event.port.inj (Option.some.inj hlast)).2
    · intro h w p
      induction p with
      | nil =>
          simpa only [pathTranscript, pathRun] using
            congrArg (fun y => [Event.port v y]) (h v Path.nil)
      | cons q e ih => simp only [pathTranscript, ih, h _ (q.cons e)]
  have adaptive_forward (t t' : ZMod N.m)
      (h : boundary N v t = boundary N v t') (Control : Type)
      (select : (w : N.V) → List (Event N) → Control →
        Option ({e : N.E // N.src e = w} × Control)) (control : Control) (n : ℕ) :
      (execute select n v t control).history = (execute select n v t' control).history := by
    have ports := (all_endpoints t t').mpr h
    have coupled : ∀ n, ∃ (w : N.V) (p : NPath N v w) (c : Control)
        (history : List (Event N)) (halted : Bool),
        execute select n v t control = ⟨w, pathRun p t, c, history, halted⟩ ∧
        execute select n v t' control = ⟨w, pathRun p t', c, history, halted⟩ := by
      intro n
      induction n with
      | zero =>
          refine ⟨v, Path.nil, control, [.port v (portRead N v t)], false, rfl, ?_⟩
          have hzero : portRead N v t = portRead N v t' := ports v Path.nil
          simp only [execute, Function.iterate_zero_apply, pathRun]
          rw [hzero]
      | succ n ih =>
          obtain ⟨w, p, c, history, halted, ht, ht'⟩ := ih
          simp only [execute, Function.iterate_succ_apply']
          change ∃ w p c history halted,
            step select (execute select n v t control) = _ ∧
            step select (execute select n v t' control) = _
          rw [ht, ht']
          cases halted with
          | true => exact ⟨w, p, c, history, true, rfl, rfl⟩
          | false =>
              cases he : select w history c with
              | none => exact ⟨w, p, c, history, true, by simp [step, he], by simp [step, he]⟩
              | some ec =>
                  obtain ⟨e, c'⟩ := ec
                  let edge : (networkQuiver N).Hom w (N.dst e.1) := ⟨e.1, e.2, rfl⟩
                  refine ⟨N.dst e.1, p.cons edge, c',
                    history ++ [.edge e.1,
                      .port (N.dst e.1) (portRead N (N.dst e.1) (pathRun (p.cons edge) t))],
                    false, ?_, ?_⟩
                  · simp [step, he, edge, pathRun]
                  · have hp := ports (N.dst e.1) (p.cons edge)
                    change portRead N (N.dst e.1)
                        ((N.a e.1 : ZMod N.m) * pathRun p t + N.c e.1) =
                      portRead N (N.dst e.1)
                        ((N.a e.1 : ZMod N.m) * pathRun p t' + N.c e.1) at hp
                    simp only [step, Bool.false_eq_true, ↓reduceIte, he]
                    rw [← hp]
                    rfl
    obtain ⟨w, p, c, history, halted, ht, ht'⟩ := coupled n
    rw [ht, ht']
  let replay : (w : N.V) → List (Event N) → List N.E →
      Option ({e : N.E // N.src e = w} × List N.E) :=
    fun w _ es => match es with
    | [] => none
    | e :: es => if h : N.src e = w then some (⟨e, h⟩, es) else none
  have replay_path : ∀ {i j : N.V} (p : NPath N i j) (rest : List N.E)
      (t : ZMod N.m) (history : List (Event N)),
      (step replay)^[p.length]
        ⟨i, t, pathEdges p ++ rest, history ++ [.port i (portRead N i t)], false⟩ =
        ⟨j, pathRun p t, rest, history ++ pathTranscript p t, false⟩ := by
    intro i j p
    induction p with
    | nil =>
        intro rest t history
        simp only [Path.length_nil, Function.iterate_zero_apply, pathEdges,
          List.nil_append, pathRun, pathTranscript]
    | @cons j k q e ih =>
        intro rest t history
        simp only [Path.length_cons, Function.iterate_succ_apply', pathEdges,
          List.append_assoc, List.singleton_append]
        rw [ih]
        simp [step, replay, e.2.1, e.2.2, pathRun, pathTranscript, List.append_assoc]
        have transport : ∀ (x y : N.V), x = y → ∀ z : ZMod N.m,
            HEq (portRead N x z) (portRead N y z) := by
          intro x y hxy z
          subst y
          rfl
        exact transport _ _ e.2.2 _
  have adaptive_kernel (t t' : ZMod N.m) :
      (∀ (Control : Type)
        (select : (w : N.V) → List (Event N) → Control →
          Option ({e : N.E // N.src e = w} × Control)) (control : Control) (n : ℕ),
        (execute select n v t control).history =
          (execute select n v t' control).history) ↔ boundary N v t = boundary N v t' := by
    constructor
    · intro h
      apply (transcript_kernel t t').mp
      intro w p
      have ht := replay_path p [] t []
      have ht' := replay_path p [] t' []
      simp only [List.append_nil, List.nil_append] at ht ht'
      have heq := h (List N.E) replay (pathEdges p) p.length
      unfold execute at heq
      rw [ht, ht'] at heq
      exact heq
    · intro h Control select control n
      exact adaptive_forward t t' h Control select control n
  have surj : Function.Surjective (boundary N v) := ZMod.castHom_surjective hd.2
  have range_card : Nat.card (Set.range (boundary N v)) = allPathModulus N v := by
    calc
      _ = Nat.card (ZMod (allPathModulus N v)) :=
        Nat.card_eq_of_bijective Subtype.val
          ⟨Subtype.val_injective, fun y => ⟨⟨y, surj y⟩, rfl⟩⟩
      _ = _ := by simp [Nat.card_eq_fintype_card, ZMod.card]
  refine ⟨hd, transcript_kernel, adaptive_kernel, surj, range_card, ?_⟩
  intro State readout sufficient
  have hker : Setoid.ker readout ≤ Setoid.ker (boundary N v) := by
    intro t t' h
    exact (transcript_kernel t t').mp (sufficient t t' h)
  obtain ⟨factor, hf, _⟩ :=
    (realized_image_unique_factorization_iff_reverse_kernel (boundary N v) readout).mpr hker
  have factor_surj : Function.Surjective factor := by
    intro y
    obtain ⟨t, ht⟩ := Set.rangeFactorization_surjective y
    refine ⟨Set.rangeFactorization readout t, ?_⟩
    exact (congrFun hf t).symm.trans ht
  rw [← range_card]
  exact Nat.card_le_card_of_surjective factor factor_surj

#print axioms theorem11_2

end D5.S3.Arith.AffineNetworks.AffineModularBehavior
