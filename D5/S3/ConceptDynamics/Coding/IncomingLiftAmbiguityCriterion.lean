/- GID: D5/S3/ConceptDynamics/Coding/IncomingLiftAmbiguityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/IncomingLiftAmbiguityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unordered fiber ambiguity classifies the specified incoming lift and its exact memory. -/

import D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Instances.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound

/-- The specified original-edge code, exact longest ambiguity, and bounded
    actual bilateral periodic collisions for a finite incoming lift. -/
theorem incoming_lift_ambiguity_criterion {n : ℕ} (hn : 0 < n)
    (A : CountMat n n) {Q : Type} [Fintype Q] (L : IncomingLift A Q)
    (hA : (∀ i, ∃ j, A i j ≠ 0) ∧ (∀ j, ∃ i, A i j ≠ 0)) :
    letI : DecidableEq Q := Classical.decEq Q
    let e := Fintype.equivFin Q
    let actualEdge := fun u v : Fin (Fintype.card Q) =>
      {a : Edge A // ∃ h : L.project (e.symm v) = a.target,
        (L.lift a ⟨e.symm v, h⟩).val = e.symm u}
    let C : CountMat (Fintype.card Q) (Fintype.card Q) :=
      fun u v => Fintype.card (actualEdge u v)
    let read := fun a : Edge C =>
      ((Fintype.equivFin (actualEdge a.source a.target)).symm a.number).val
    let Pair := Σ v : Fin n, {s : Finset {q : Q // L.project q = v} // s.card = 2}
    let pairEdge := fun x y : Pair => ∃ a : Edge A,
      ∃ ht : x.1 = a.target, ∃ hs : y.1 = a.source,
        y.2.val.image Subtype.val = x.2.val.image
          (fun u => (L.lift a ⟨u.val, u.property.trans ht⟩).val)
    let walk := fun d : ℕ => ∃ f : Fin (d + 1) → Pair,
      ∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)
    let acyclic := ∀ d : ℕ, 0 < d → ∀ f : Fin (d + 1) → Pair,
      (∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)) →
        f ⟨0, Nat.zero_lt_succ d⟩ ≠ f (Fin.last d)
    let P := ∑ v : Fin n, Nat.choose (Fintype.card {q : Q // L.project q = v}) 2
    ((∀ u, ∃ v, C u v ≠ 0) ∧ (∀ v, ∃ u, C u v ≠ 0)) →
    Nat.card Pair = P ∧
    (∀ d, ¬ Forgets L d ↔ walk d) ∧
    (P = 0 → IsLeast {d | Forgets L d} 0) ∧
    (0 < P → acyclic → ∃ ell,
      IsGreatest {d | walk d} ell ∧ IsLeast {d | Forgets L d} (ell + 1) ∧
      ∀ d ≤ ell, ¬ Forgets L d) ∧
    ∃ pi : Path C → Path A,
      (∀ x i, (pi x).val i = read (x.val i)) ∧ Continuous pi ∧
      (∀ x, pi (shift C x) = shift A (pi x)) ∧
      (let conjugacy := ∃ H : Path C ≃ₜ Path A,
        (∀ x, H x = pi x) ∧ ∀ x, H (shift C x) = shift A (H x)
       List.TFAE [Function.Injective pi, conjugacy, ∃ d, Forgets L d, acyclic] ∧
       (∀ d, Forgets L d → ∃ inv : Path A → Path C,
         Continuous inv ∧ Function.LeftInverse inv pi ∧ Function.RightInverse inv pi ∧
         (∀ x, inv (shift A x) = shift C (inv x)) ∧
         ∀ x y i, (∀ j : ℕ, j ≤ d → x.val (i + j) = y.val (i + j)) →
           (inv x).val i = (inv y).val i) ∧
       ((¬ ∃ d, Forgets L d) → ∃ c : ℕ, 0 < c ∧ c ≤ P ∧
         ∃ x x' : Path C, x ≠ x' ∧ pi x = pi x' ∧
           (∀ i : ℤ, (pi x).val (i + c) = (pi x).val i) ∧
           (∀ i : ℤ, x.val (i + 2 * c) = x.val i) ∧
           (∀ i : ℤ, x'.val (i + 2 * c) = x'.val i)) ∧
       (conjugacy ↔ ¬ ∃ k : ℕ, 0 < k ∧ k ≤ 2 * P ∧
         ∃ x x' : Path C, x ≠ x' ∧ pi x = pi x' ∧
           (∀ i : ℤ, x.val (i + k) = x.val i) ∧
           (∀ i : ℤ, x'.val (i + k) = x'.val i)) ∧
       (conjugacy ↔ ¬ ∃ k k' : ℕ, 0 < k ∧ k ≤ 2 * P ∧ 0 < k' ∧ k' ≤ 2 * P ∧
         ∃ x x' : Path C, x ≠ x' ∧ pi x = pi x' ∧
           (∀ i : ℤ, x.val (i + k) = x.val i) ∧
           (∀ i : ℤ, x'.val (i + k') = x'.val i))) := by
  letI : DecidableEq Q := Classical.decEq Q
  dsimp only
  intro hC
  let e := Fintype.equivFin Q
  let actualEdge := fun u v : Fin (Fintype.card Q) =>
    {a : Edge A // ∃ h : L.project (e.symm v) = a.target,
      (L.lift a ⟨e.symm v, h⟩).val = e.symm u}
  let C : CountMat (Fintype.card Q) (Fintype.card Q) :=
    fun u v => Fintype.card (actualEdge u v)
  let read := fun a : Edge C =>
    ((Fintype.equivFin (actualEdge a.source a.target)).symm a.number).val
  let Pair := Σ v : Fin n, {s : Finset {q : Q // L.project q = v} // s.card = 2}
  let pairEdge := fun x y : Pair => ∃ a : Edge A,
    ∃ ht : x.1 = a.target, ∃ hs : y.1 = a.source,
      y.2.val.image Subtype.val = x.2.val.image
        (fun u => (L.lift a ⟨u.val, u.property.trans ht⟩).val)
  let walk := fun d : ℕ => ∃ f : Fin (d + 1) → Pair,
    ∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)
  let acyclic := ∀ d : ℕ, 0 < d → ∀ f : Fin (d + 1) → Pair,
    (∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)) →
      f ⟨0, Nat.zero_lt_succ d⟩ ≠ f (Fin.last d)
  let P := ∑ v : Fin n, Nat.choose (Fintype.card {q : Q // L.project q = v}) 2
  have pair_card : Nat.card Pair = P := by
    rw [Nat.card_eq_fintype_card]
    simp [Pair, P, Fintype.card_sigma, Fintype.card_finset_len]
  have read_target (a : Edge C) :
      (read a).target = L.project (e.symm a.target) := by
    obtain ⟨h, _⟩ :=
      ((Fintype.equivFin (actualEdge a.source a.target)).symm a.number).property
    exact h.symm
  have read_lift (a : Edge C) :
      (L.lift (read a) ⟨e.symm a.target, (read_target a).symm⟩).val =
        e.symm a.source := by
    obtain ⟨_, h⟩ :=
      ((Fintype.equivFin (actualEdge a.source a.target)).symm a.number).property
    exact h
  have read_source (a : Edge C) :
      (read a).source = L.project (e.symm a.source) := by
    calc
      (read a).source =
          L.project (L.lift (read a) ⟨e.symm a.target, (read_target a).symm⟩).val :=
        (L.lift (read a) ⟨e.symm a.target, (read_target a).symm⟩).property.symm
      _ = L.project (e.symm a.source) := congrArg L.project (read_lift a)
  let pi : Path C → Path A := fun x => ⟨fun i => read (x.val i), fun i => by
    rw [read_target, read_source, x.property i]⟩
  have pi_continuous : Continuous pi := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology (f := read)).comp
      ((continuous_apply i).comp continuous_subtype_val)
  have pi_shift (x : Path C) : pi (shift C x) = shift A (pi x) := by
    rfl
  let window (x : Path A) (d : ℕ) : (i : ℤ) →
      FinitePath A d (x.val i).source (x.val (i + d)).source :=
    Nat.rec (motive := fun d => (i : ℤ) →
      FinitePath A d (x.val i).source (x.val (i + d)).source)
      (fun i => by simpa only [Int.natCast_zero, add_zero] using
        FinitePath.nil (x.val i).source)
      (fun d prev i => by
        let a : Fin (A (x.val i).source (x.val (i + 1)).source) :=
          (x.property i) ▸ (x.val i).number
        have p := FinitePath.cons a (prev (i + 1))
        simpa only [Int.natCast_add, Int.natCast_one, Int.natCast_succ, add_assoc, add_comm,
          add_left_comm] using p) d
  let step : Edge A → Q → Q := fun a q =>
    if h : L.project q = a.target then (L.lift a ⟨q, h⟩).val else q
  have read_step (a : Edge C) : step (read a) (e.symm a.target) = e.symm a.source := by
    dsimp only [step]
    rw [dif_pos (read_target a).symm]
    exact read_lift a
  have edge_unique (a b : Edge C) (ht : a.target = b.target)
      (hr : read a = read b) : a = b := by
    have hs : a.source = b.source := by
      apply e.symm.injective
      rw [← read_step a, ← read_step b, hr, ht]
    rcases a with ⟨u, v, k⟩
    rcases b with ⟨u', v', k'⟩
    cases hs
    cases ht
    congr 1
    apply (Fintype.equivFin (actualEdge u v)).symm.injective
    exact Subtype.ext hr
  let chooseState : Fin n → Q := fun v => (L.onto v).choose
  have chooseState_project (v : Fin n) : L.project (chooseState v) = v :=
    (L.onto v).choose_spec
  let run (x : Path A) (d : ℕ) (i : ℤ) (q : Q) : Q :=
    Nat.rec (motive := fun _ => ℤ → Q → Q) (fun _ q => q)
      (fun _ prev i q => step (x.val i) (prev (i + 1) q)) d i q
  have run_zero (x : Path A) (i : ℤ) (q : Q) : run x 0 i q = q := rfl
  have run_succ (x : Path A) (d : ℕ) (i : ℤ) (q : Q) :
      run x (d + 1) i q = step (x.val i) (run x d (i + 1) q) := rfl
  have lift_cast (a : Edge A) (v : Fin n) (h : a.target = v)
      (q : {q : Q // L.project q = v}) :
      (L.lift ⟨a.source, v, h ▸ a.number⟩ q).val = step a q.val := by
    cases h
    dsimp only [step]
    rw [dif_pos q.property]
  have run_realization : ∀ (d : ℕ) (x : Path A) (i : ℤ),
      ∃ p : FinitePath A d (x.val i).source (x.val (i + d)).source,
        ∀ (q : Q) (hq : L.project q = (x.val (i + d)).source),
          run x d i q = (L.liftPath p ⟨q, hq⟩).val := by
    intro d
    induction d with
    | zero =>
        intro x i
        simp only [Int.natCast_zero]
        rw [add_zero]
        exact ⟨FinitePath.nil (A := A) (x.val i).source,
          fun q hq => run_zero x i q⟩
    | succ d ih =>
        intro x i
        have hindex : i + (↑(d + 1) : ℤ) = i + 1 + d := by
          simp only [Int.natCast_add, Int.natCast_one]; omega
        change ∃ p : FinitePath A (d + 1) _ _, _
        rw [hindex]
        obtain ⟨p, hp⟩ := ih x (i + 1)
        let a : Fin (A (x.val i).source (x.val (i + 1)).source) :=
          (x.property i) ▸ (x.val i).number
        refine ⟨.cons a p, ?_⟩
        intro q hq
        rw [run_succ]
        change step (x.val i) (run x d (i + 1) q) =
          (L.lift ⟨(x.val i).source, (x.val (i + 1)).source, a⟩
            (L.liftPath p ⟨q, hq⟩)).val
        rw [lift_cast (x.val i) _ (x.property i)]
        rw [hp q hq]
  have run_project (d : ℕ) (x : Path A) (i : ℤ) (q : Q)
      (hq : L.project q = (x.val (i + d)).source) :
      L.project (run x d i q) = (x.val i).source := by
    obtain ⟨p, hp⟩ := run_realization d x i
    rw [hp q hq]
    exact (L.liftPath p ⟨q, hq⟩).property
  have run_forgets (d : ℕ) (hd : Forgets L d) (x : Path A) (i : ℤ) (q r : Q)
      (hq : L.project q = (x.val (i + d)).source)
      (hr : L.project r = (x.val (i + d)).source) :
      run x d i q = run x d i r := by
    obtain ⟨p, hp⟩ := run_realization d x i
    rw [hp q hq, hp r hr]
    exact congrArg Subtype.val (hd _ _ p ⟨q, hq⟩ ⟨r, hr⟩)
  have run_snoc : ∀ (d : ℕ) (x : Path A) (i : ℤ) (q : Q),
      run x (d + 1) i q = run x d i (step (x.val (i + d)) q) := by
    intro d
    induction d with
    | zero => intro x i q; simp only [run_succ, run_zero, Int.natCast_zero, add_zero]
    | succ d ih =>
        intro x i q
        change step (x.val i) (run x (d + 1) (i + 1) q) =
          step (x.val i) (run x d (i + 1) (step (x.val (i + (d + 1))) q))
        rw [ih x (i + 1) q]
        congr 2
        congr 1
        simp only [Int.natCast_add, Int.natCast_one, add_assoc,
          add_comm, add_left_comm]
  let state : ℕ → Path A → ℤ → Q := fun d x i =>
    run x d i (chooseState (x.val (i + d)).source)
  have state_project (d : ℕ) (x : Path A) (i : ℤ) :
      L.project (state d x i) = (x.val i).source :=
    run_project d x i _ (chooseState_project _)
  have state_step (d : ℕ) (hd : Forgets L d) (x : Path A) (i : ℤ) :
      step (x.val i) (state d x (i + 1)) = state d x i := by
    let q := chooseState (x.val (i + (d + 1))).source
    have hq : L.project q = (x.val (i + 1 + d)).source := by
      simpa only [q, Int.natCast_add, Int.natCast_one, add_assoc,
        add_comm, add_left_comm] using chooseState_project (x.val (i + (d + 1))).source
    have hlast : L.project q = (x.val (i + d)).target := by
      rw [x.property (i + d)]
      simpa only [Int.natCast_add, Int.natCast_one, add_assoc,
        add_comm, add_left_comm] using hq
    have hs : L.project (step (x.val (i + d)) q) = (x.val (i + d)).source := by
      dsimp only [step]
      rw [dif_pos hlast]
      exact (L.lift (x.val (i + d)) ⟨q, hlast⟩).property
    calc
      step (x.val i) (state d x (i + 1)) = run x (d + 1) i q := by
        dsimp only [state, run, q]
        congr 2
        congr 2
        simp only [Int.natCast_add, Int.natCast_one, add_assoc,
          add_comm, add_left_comm]
      _ = run x d i (step (x.val (i + d)) q) := run_snoc d x i q
      _ = state d x i := run_forgets d hd x i _ _ hs (chooseState_project _)
  let encode (a : Edge A) (q : Q) (h : L.project q = a.target) : Edge C :=
    { source := e (L.lift a ⟨q, h⟩).val
      target := e q
      number := Fintype.equivFin
        (actualEdge (e (L.lift a ⟨q, h⟩).val) (e q))
        ⟨a, by simp only [actualEdge, Equiv.symm_apply_apply]; exact ⟨h, trivial⟩⟩ }
  have encode_read (a : Edge A) (q : Q) (h : L.project q = a.target) :
      read (encode a q h) = a := by
    dsimp only [read, encode]
    exact congrArg Subtype.val ((Fintype.equivFin
      (actualEdge (e (L.lift a ⟨q, h⟩).val) (e q))).symm_apply_apply _)
  have state_history (d : ℕ) (hd : Forgets L d) (x : Path C) (i : ℤ) :
      state d (pi x) i = e.symm (x.val i).source := by
    have trace : ∀ (k : ℕ) (j : ℤ),
        run (pi x) k j (e.symm (x.val (j + k)).source) = e.symm (x.val j).source := by
      intro k
      induction k with
      | zero => intro j; simp only [run_zero, Int.natCast_zero, add_zero]
      | succ k ih =>
          intro j
          rw [run_succ]
          have hindex : j + (↑k + 1 : ℤ) = j + 1 + k := by omega
          simp only [Int.natCast_add, Int.natCast_one]
          rw [hindex, ih (j + 1)]
          change step (read (x.val j)) _ = _
          rw [← x.property j, read_step]
    have hp : L.project (e.symm (x.val (i + d)).source) = ((pi x).val (i + d)).source :=
      (read_source _).symm
    exact (run_forgets d hd (pi x) i _ _ (chooseState_project _) hp).trans (trace d i)
  have run_congr : ∀ (d : ℕ) (x y : Path A) (i : ℤ) (q : Q),
      (∀ j : ℕ, j < d → x.val (i + j) = y.val (i + j)) →
      run x d i q = run y d i q := by
    intro d
    induction d with
    | zero => intro x y i q h; rfl
    | succ d ih =>
        intro x y i q h
        rw [run_succ, run_succ]
        rw [show x.val i = y.val i from by simpa using h 0 (by omega)]
        rw [ih x y (i + 1) q]
        intro j hj
        simpa only [Int.natCast_add, Int.natCast_one, add_assoc,
          add_comm, add_left_comm] using h (j + 1) (by omega)
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  have run_continuous : ∀ (d : ℕ) (i : ℤ) (f : Path A → Q), Continuous f →
      Continuous (fun x => run x d i (f x)) := by
    intro d
    induction d with
    | zero => intro i f hf; exact hf
    | succ d ih =>
        intro i f hf
        exact (continuous_of_discreteTopology
          (f := fun z : Edge A × Q => step z.1 z.2)).comp
          (((continuous_apply i).comp continuous_subtype_val).prodMk
            (ih (i + 1) f hf))
  have state_continuous (d : ℕ) (i : ℤ) : Continuous (fun x => state d x i) := by
    exact run_continuous d i _
      ((continuous_of_discreteTopology
        (f := fun a : Edge A => chooseState a.source)).comp
          ((continuous_apply (i + d)).comp continuous_subtype_val))
  have finite_window_inverse (d : ℕ) (hd : Forgets L d) :
      ∃ inv : Path A → Path C,
        Continuous inv ∧ Function.LeftInverse inv pi ∧ Function.RightInverse inv pi ∧
        (∀ x, inv (shift A x) = shift C (inv x)) ∧
        ∀ x y i, (∀ j : ℕ, j ≤ d → x.val (i + j) = y.val (i + j)) →
          (inv x).val i = (inv y).val i := by
    let encoded : Path A → ℤ → Edge C := fun x i =>
      encode (x.val i) (state d x (i + 1))
        ((state_project d x (i + 1)).trans (x.property i).symm)
    have source_encoded (x : Path A) (i : ℤ) :
        (encoded x i).source = e (state d x i) := by
      dsimp only [encoded, encode]
      apply congrArg e
      rw [← state_step d hd x i]
      dsimp only [step]
      rw [dif_pos ((state_project d x (i + 1)).trans (x.property i).symm)]
    let inv : Path A → Path C := fun x => ⟨encoded x, fun i => by
      change e (state d x (i + 1)) = (encoded x (i + 1)).source
      exact (source_encoded x (i + 1)).symm⟩
    have hinv : Continuous inv := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      let domain := {z : Edge A × Q // L.project z.2 = z.1.target}
      let enc : domain → Edge C := fun z => encode z.val.1 z.val.2 z.property
      exact (continuous_of_discreteTopology (f := enc)).comp
        (Continuous.subtype_mk
          (((continuous_apply i).comp continuous_subtype_val).prodMk
            (state_continuous d (i + 1)))
          (fun x => (state_project d x (i + 1)).trans (x.property i).symm))
    have hright : Function.RightInverse inv pi := by
      intro x
      apply Subtype.ext
      funext i
      exact encode_read _ _ _
    have hleft : Function.LeftInverse inv pi := by
      intro x
      apply Subtype.ext
      funext i
      apply edge_unique
      · change e (state d (pi x) (i + 1)) = (x.val i).target
        rw [state_history d hd x (i + 1), ← x.property i, Equiv.apply_symm_apply]
      · exact encode_read _ _ _
    refine ⟨inv, hinv, hleft, hright, ?_, ?_⟩
    · intro x
      apply hleft.injective
      rw [hright, pi_shift, hright]
    · intro x y i hxy
      have hbase : x.val i = y.val i := by simpa using hxy 0 (Nat.zero_le d)
      have hboundary : (x.val (i + 1 + d)).source = (y.val (i + 1 + d)).source := by
        have hlast := congrArg Edge.target (hxy d (Nat.le_refl d))
        rw [x.property (i + d), y.property (i + d)] at hlast
        simpa only [add_assoc, add_comm, add_left_comm] using hlast
      have hstate : state d x (i + 1) = state d y (i + 1) := by
        dsimp only [state]
        rw [hboundary]
        apply run_congr
        intro j hj
        simpa only [Int.natCast_add, Int.natCast_one, add_assoc,
          add_comm, add_left_comm] using hxy (j + 1) (by omega)
      apply edge_unique
      · change e (state d x (i + 1)) = e (state d y (i + 1))
        rw [hstate]
      · change read (encoded x i) = read (encoded y i)
        rw [encode_read, encode_read, hbase]
  have zero_forgetting (hP : P = 0) : IsLeast {d | Forgets L d} 0 := by
    have singleton (v : Fin n) (u w : {q : Q // L.project q = v}) : u = w := by
      have hv : Nat.choose (Fintype.card {q : Q // L.project q = v}) 2 = 0 := by
        have hle := Finset.single_le_sum
          (f := fun v : Fin n => Nat.choose (Fintype.card {q : Q // L.project q = v}) 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        change _ ≤ P at hle
        omega
      have hlt := Nat.choose_eq_zero_iff.mp hv
      exact Fintype.card_le_one_iff.mp (by omega) u w
    refine ⟨?_, fun d _ => Nat.zero_le d⟩
    intro i j p u w
    rw [singleton j u w]
  let pairOf (v : Fin n) (u w : {q : Q // L.project q = v}) (h : u ≠ w) : Pair :=
    ⟨v, ⟨{u, w}, by simp [h]⟩⟩
  have ambiguity_walk : ∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j)
      (u w : {q : Q // L.project q = j})
      (h : L.liftPath p u ≠ L.liftPath p w),
      ∃ f : Fin (d + 1) → Pair,
        f ⟨0, Nat.zero_lt_succ d⟩ =
          pairOf j u w (fun he => h (congrArg (L.liftPath p) he)) ∧
        f (Fin.last d) = pairOf i (L.liftPath p u) (L.liftPath p w) h ∧
        ∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ) := by
    intro d i j p
    induction p with
    | nil i =>
        intro u w h
        refine ⟨fun _ => pairOf i u w h, rfl, rfl, ?_⟩
        intro k
        exact Fin.elim0 k
    | @cons d i j k a tail ih =>
        intro u w h
        have ht : L.liftPath tail u ≠ L.liftPath tail w := by
          intro he
          apply h
          exact congrArg (L.lift ⟨i, j, a⟩) he
        obtain ⟨f, hf0, hflast, hf⟩ := ih u w ht
        let lastPair := pairOf i (L.liftPath (.cons a tail) u)
          (L.liftPath (.cons a tail) w) h
        let g : Fin (d + 1 + 1) → Pair := Fin.lastCases lastPair f
        refine ⟨g, ?_, ?_, ?_⟩
        · change g ((0 : Fin (d + 1)).castSucc) = _
          simpa only [g, Fin.lastCases_castSucc, Fin.mk_zero] using hf0
        · exact Fin.lastCases_last
        · intro index
          refine Fin.lastCases ?_ (fun index => ?_) index
          · simp only [g, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last]
            rw [hflast]
            refine ⟨⟨i, j, a⟩, rfl, rfl, ?_⟩
            simp only [pairOf, lastPair, Finset.image_insert, Finset.image_singleton,
              IncomingLift.liftPath]
          · simpa only [g, Fin.succ_castSucc,
              Fin.lastCases_castSucc] using hf index
  have ambiguity_to_walk (d : ℕ) (h : ¬ Forgets L d) : walk d := by
    simp only [Forgets, not_forall] at h
    obtain ⟨i, j, p, u, w, h⟩ := h
    obtain ⟨f, _, _, hf⟩ := ambiguity_walk p u w h
    exact ⟨f, hf⟩
  have pair_step (x y : Pair) (h : pairEdge x y) :
      ∃ a : Fin (A y.1 x.1),
        y.2.val.image Subtype.val = x.2.val.image
          (fun q => (L.lift ⟨y.1, x.1, a⟩ q).val) := by
    rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    obtain ⟨⟨src, dst, a⟩, ht, hs, he⟩ := h
    dsimp only at ht hs
    subst src
    subst dst
    exact ⟨a, he⟩
  have walk_transport : ∀ (d : ℕ) (f : Fin (d + 1) → Pair),
      (∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)) →
      ∃ p : FinitePath A d (f (Fin.last d)).1 (f 0).1,
        (f 0).2.val.image (fun q => (L.liftPath p q).val) =
          (f (Fin.last d)).2.val.image Subtype.val := by
    intro d
    induction d with
    | zero =>
        intro f hf
        exact ⟨.nil (f 0).1, rfl⟩
    | succ d ih =>
        intro f hf
        let g : Fin (d + 1) → Pair := fun k => f k.castSucc
        have hg : ∀ k : Fin d, pairEdge (g k.castSucc) (g k.succ) := by
          intro k
          exact hf k.castSucc
        obtain ⟨p, hp⟩ := ih g hg
        obtain ⟨a, ha⟩ := pair_step _ _ (hf (Fin.last d))
        have ha' : (f (Fin.last (d + 1))).2.val.image Subtype.val =
            (g (Fin.last d)).2.val.image
              (fun q => (L.lift ⟨(f (Fin.last (d + 1))).1,
                (g (Fin.last d)).1, a⟩ q).val) := ha
        refine ⟨.cons a p, ?_⟩
        let edge : Edge A := ⟨(f (Fin.last (d + 1))).1, (g (Fin.last d)).1, a⟩
        have hs (q : {q : Q // L.project q = (g (Fin.last d)).1}) :
            step edge q.val = (L.lift edge q).val := by
          dsimp only [step, edge]
          rw [dif_pos q.property]
        have hp' := congrArg (Finset.image (step edge)) hp
        rw [Finset.image_image, Finset.image_image] at hp'
        calc
          (f 0).2.val.image (fun q => (L.liftPath (.cons a p) q).val) =
              (g 0).2.val.image (fun q => step edge (L.liftPath p q).val) := by
            apply Finset.image_congr
            intro q hq
            exact (hs (L.liftPath p q)).symm
          _ = (g (Fin.last d)).2.val.image (fun q => step edge q.val) := hp'
          _ = (g (Fin.last d)).2.val.image (fun q => (L.lift edge q).val) := by
            apply Finset.image_congr
            intro q hq
            exact hs q
          _ = (f (Fin.last (d + 1))).2.val.image Subtype.val := ha'.symm
  have walk_to_ambiguity (d : ℕ) (hw : walk d) : ¬ Forgets L d := by
    obtain ⟨f, hf⟩ := hw
    obtain ⟨p, hp⟩ := walk_transport d f hf
    intro hforget
    have hcard : ((f (Fin.last d)).2.val.image Subtype.val).card = 2 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact (f (Fin.last d)).2.property
    rw [← hp] at hcard
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [(f 0).2.property]; decide :
      0 < (f 0).2.val.card)
    have himage : (f 0).2.val.image (fun q => (L.liftPath p q).val) =
        {(L.liftPath p u).val} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
      intro q hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      exact congrArg Subtype.val (hforget _ _ p v u)
    rw [himage, Finset.card_singleton] at hcard
    omega
  have acyclic_trace_injective (ha : acyclic) (d : ℕ) (f : Fin (d + 1) → Pair)
      (hf : ∀ k : Fin d, pairEdge (f k.castSucc) (f k.succ)) :
      Function.Injective f := by
    have ordered (u v : Fin (d + 1)) (hlt : u.val < v.val) (heq : f u = f v) :
        False := by
      let c := v.val - u.val
      have hc : 0 < c := Nat.sub_pos_of_lt hlt
      let g : Fin (c + 1) → Pair := fun k => f ⟨u.val + k.val, by dsimp [c] at *; omega⟩
      have hg : ∀ k : Fin c, pairEdge (g k.castSucc) (g k.succ) := by
        intro k
        exact hf ⟨u.val + k.val, by dsimp [c] at *; omega⟩
      apply ha c hc g hg
      change f ⟨u.val + 0, _⟩ = f ⟨u.val + c, _⟩
      convert heq using 1 <;> congr 1 <;> apply Fin.ext <;> dsimp [c] <;> omega
    intro u v heq
    apply Fin.ext
    by_contra hne
    by_cases hlt : u.val < v.val
    · exact ordered u v hlt heq
    · exact ordered v u (by omega) heq.symm
  have acyclic_walk_bound (ha : acyclic) (d : ℕ) (hd : walk d) : d < P := by
    obtain ⟨f, hf⟩ := hd
    have hle := Fintype.card_le_of_injective f (acyclic_trace_injective ha d f hf)
    have hcard : Fintype.card Pair = P := by
      simpa only [Nat.card_eq_fintype_card] using pair_card
    simpa only [Fintype.card_fin, hcard, Nat.succ_le_iff] using hle
  have attained_longest (hP : 0 < P) (ha : acyclic) :
      ∃ ell, IsGreatest {d | walk d} ell := by
    have hcard : 0 < Fintype.card Pair := by
      have hp : 0 < Nat.card Pair := by rw [pair_card]; exact hP
      simpa only [Nat.card_eq_fintype_card] using hp
    obtain ⟨z⟩ := Fintype.card_pos_iff.mp hcard
    have hw0 : walk 0 := ⟨fun _ => z, fun k => Fin.elim0 k⟩
    let lengths := (Finset.range P).filter walk
    have members (d : ℕ) : d ∈ lengths ↔ walk d := by
      simp only [lengths, Finset.mem_filter, Finset.mem_range]
      exact ⟨And.right, fun hd => ⟨acyclic_walk_bound ha d hd, hd⟩⟩
    have hne : lengths.Nonempty := ⟨0, (members 0).mpr hw0⟩
    refine ⟨lengths.max' hne, ?_, ?_⟩
    · exact (members _).mp (lengths.max'_mem hne)
    · intro d hd
      exact lengths.le_max' d ((members d).mpr hd)
  have acyclic_forgetting (ha : acyclic) : ∃ d, Forgets L d := by
    refine ⟨P, ?_⟩
    by_contra h
    exact Nat.lt_irrefl P (acyclic_walk_bound ha P (ambiguity_to_walk P h))
  have longest_forgetting (ell : ℕ) (hmax : IsGreatest {d | walk d} ell) :
      Forgets L (ell + 1) := by
    by_contra h
    exact Nat.not_succ_le_self ell (hmax.2 (ambiguity_to_walk (ell + 1) h))
  have walk_prefix (ell d : ℕ) (hle : d ≤ ell) (hw : walk ell) : walk d := by
    obtain ⟨f, hf⟩ := hw
    let g : Fin (d + 1) → Pair := fun k => f ⟨k.val, by omega⟩
    refine ⟨g, ?_⟩
    intro k
    exact hf ⟨k.val, by omega⟩
  have cycle_repeat (c : ℕ) (hc : 0 < c) (f : Fin (c + 1) → Pair)
      (hf : ∀ k : Fin c, pairEdge (f k.castSucc) (f k.succ))
      (hclosed : f 0 = f (Fin.last c)) (d : ℕ) : walk d := by
    let g : Fin (d + 1) → Pair := fun k => f ⟨k.val % c, by
      have := Nat.mod_lt k.val hc; omega⟩
    refine ⟨g, ?_⟩
    intro k
    let r := k.val % c
    have hr : r < c := Nat.mod_lt k.val hc
    have hmod : (k.val + 1) % c = (r + 1) % c := by
      exact (Nat.mod_add_mod k.val c 1).symm
    have hs : f ⟨(r + 1) % c, by have := Nat.mod_lt (r + 1) hc; omega⟩ =
        f ⟨r + 1, by omega⟩ := by
      by_cases hlast : r + 1 = c
      · simp only [hlast, Nat.mod_self]
        exact hclosed
      · apply congrArg f
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega : r + 1 < c)
    have hh := hf ⟨r, hr⟩
    change pairEdge (f ⟨r, by omega⟩)
      (f ⟨(k.val + 1) % c, by have := Nat.mod_lt (k.val + 1) hc; omega⟩)
    have hfin : (⟨(k.val + 1) % c, by
        have := Nat.mod_lt (k.val + 1) hc; omega⟩ : Fin (c + 1)) =
        ⟨(r + 1) % c, by have := Nat.mod_lt (r + 1) hc; omega⟩ := Fin.ext hmod
    rw [hfin, hs]
    exact hh
  have forgetting_acyclic (d : ℕ) (hd : Forgets L d) : acyclic := by
    intro c hc f hf heq
    exact walk_to_ambiguity d (cycle_repeat c hc f hf heq d) hd
  have forgetting_iff_acyclic : (∃ d, Forgets L d) ↔ acyclic :=
    ⟨fun ⟨d, hd⟩ => forgetting_acyclic d hd, acyclic_forgetting⟩
  have bounded_cycle (hnof : ¬ ∃ d, Forgets L d) :
      ∃ c : ℕ, 0 < c ∧ c ≤ P ∧ ∃ f : Fin (c + 1) → Pair,
        (∀ k : Fin c, pairEdge (f k.castSucc) (f k.succ)) ∧
        f 0 = f (Fin.last c) ∧ Function.Injective (fun k : Fin c => f k.castSucc) := by
    have hna : ¬ acyclic := fun ha => hnof (acyclic_forgetting ha)
    have hex : ∃ c : ℕ, 0 < c ∧ ∃ f : Fin (c + 1) → Pair,
        (∀ k : Fin c, pairEdge (f k.castSucc) (f k.succ)) ∧ f 0 = f (Fin.last c) := by
      simpa only [acyclic, not_forall, not_ne_iff, exists_prop, Fin.mk_zero] using hna
    let c := Nat.find hex
    obtain ⟨hc, f, hf, hclosed⟩ := Nat.find_spec hex
    have hminimal : ∀ b < c, ¬ (0 < b ∧ ∃ g : Fin (b + 1) → Pair,
        (∀ k : Fin b, pairEdge (g k.castSucc) (g k.succ)) ∧ g 0 = g (Fin.last b)) := by
      intro b hb
      exact Nat.find_min hex hb
    have hordered (u v : Fin c) (hlt : u.val < v.val)
        (heq : f u.castSucc = f v.castSucc) : False := by
      let b := v.val - u.val
      have hb : 0 < b := Nat.sub_pos_of_lt hlt
      let g : Fin (b + 1) → Pair := fun k => f ⟨u.val + k.val, by dsimp [b] at *; omega⟩
      have hg : ∀ k : Fin b, pairEdge (g k.castSucc) (g k.succ) := by
        intro k
        exact hf ⟨u.val + k.val, by dsimp [b] at *; omega⟩
      apply hminimal b (by dsimp [b]; omega)
      refine ⟨hb, g, hg, ?_⟩
      change f ⟨u.val + 0, _⟩ = f ⟨u.val + b, _⟩
      convert heq using 1 <;> congr 1 <;> apply Fin.ext <;> dsimp [b] <;> omega
    have hinj : Function.Injective (fun k : Fin c => f k.castSucc) := by
      intro u v heq
      apply Fin.ext
      by_contra hne
      by_cases hlt : u.val < v.val
      · exact hordered u v hlt heq
      · exact hordered v u (by omega) heq.symm
    have hle := Fintype.card_le_of_injective _ hinj
    have hcard : Fintype.card Pair = P := by simpa only [Nat.card_eq_fintype_card] using pair_card
    refine ⟨c, hc, ?_, f, hf, hclosed, hinj⟩
    simpa only [Fintype.card_fin, hcard] using hle
  have forgetting_conjugacy (d : ℕ) (hd : Forgets L d) :
      ∃ H : Path C ≃ₜ Path A, (∀ x, H x = pi x) ∧
        ∀ x, H (shift C x) = shift A (H x) := by
    obtain ⟨inv, hinv, hleft, hright, _, _⟩ := finite_window_inverse d hd
    let H : Path C ≃ₜ Path A :=
      { toEquiv := { toFun := pi, invFun := inv, left_inv := hleft, right_inv := hright }
        continuous_toFun := pi_continuous
        continuous_invFun := hinv }
    exact ⟨H, fun _ => rfl, pi_shift⟩
  have conjugacy_injective
      (h : ∃ H : Path C ≃ₜ Path A, (∀ x, H x = pi x) ∧
        ∀ x, H (shift C x) = shift A (H x)) : Function.Injective pi := by
    obtain ⟨H, hH, _⟩ := h
    intro x y hxy
    exact H.injective ((hH x).trans (hxy.trans (hH y).symm))
  have concatenate_paths : ∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j)
      {b : ℕ} {k : Fin n} (q : FinitePath A b j k),
      ∃ r : FinitePath A (d + b) i k,
        pathWord r = pathWord p ++ pathWord q ∧
        ∀ z : {z : Q // L.project z = k},
          L.liftPath r z = L.liftPath p (L.liftPath q z) := by
    intro d i j p
    induction p with
    | nil i =>
        intro b k q
        rw [Nat.zero_add]
        exact ⟨q, rfl, fun _ => rfl⟩
    | @cons d i j k a tail ih =>
        intro b z q
        obtain ⟨r, hw, hr⟩ := ih q
        rw [show d + 1 + b = d + b + 1 by omega]
        refine ⟨.cons a r, ?_, ?_⟩
        · simp only [pathWord, List.cons_append, hw]
        · intro w
          dsimp only [IncomingLift.liftPath]
          rw [hr]
  have actual_path_lift : ∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j)
      (q : {q : Q // L.project q = j}),
      ∃ r : FinitePath C d (e (L.liftPath p q).val) (e q.val),
        (pathWord r).map read = pathWord p := by
    intro d i j p
    induction p with
    | nil i =>
        intro q
        exact ⟨.nil (e q.val), rfl⟩
    | @cons d i j k a tail ih =>
        intro q
        obtain ⟨r, hr⟩ := ih q
        let edge := encode ⟨i, j, a⟩ (L.liftPath tail q).val (L.liftPath tail q).property
        refine ⟨.cons edge.number r, ?_⟩
        change read edge :: (pathWord r).map read = _
        rw [hr, encode_read]
        rfl
  have periodic_collision (hnof : ¬ ∃ d, Forgets L d) :
      ∃ c : ℕ, 0 < c ∧ c ≤ P ∧ ∃ x x' : Path C,
        x ≠ x' ∧ pi x = pi x' ∧
        (∀ i : ℤ, (pi x).val (i + c) = (pi x).val i) ∧
        (∀ i : ℤ, x.val (i + 2 * c) = x.val i) ∧
        (∀ i : ℤ, x'.val (i + 2 * c) = x'.val i) := by
    obtain ⟨c, hc, hbound, f, hf, hclosed, hinj⟩ := bounded_cycle hnof
    have hloop : ∃ p : FinitePath A c (f 0).1 (f 0).1,
        (f 0).2.val.image (fun q => (L.liftPath p q).val) =
          (f 0).2.val.image Subtype.val := by
      have ht := walk_transport c f hf
      rw [hclosed.symm] at ht
      exact ht
    obtain ⟨p, hp⟩ := hloop
    obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.mp (f 0).2.property
    have hpair : ({(L.liftPath p u).val, (L.liftPath p v).val} : Finset Q) = {u.val, v.val} := by
      simpa only [hset, Finset.image_insert, Finset.image_singleton] using hp
    have hdistinct : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hperm :
        (L.liftPath p u = u ∧ L.liftPath p v = v) ∨
        (L.liftPath p u = v ∧ L.liftPath p v = u) := by
      have hu : (L.liftPath p u).val = u.val ∨ (L.liftPath p u).val = v.val := by
        have hm : (L.liftPath p u).val ∈ ({u.val, v.val} : Finset Q) := by
          rw [← hpair]; simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl trivial
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      have hv : (L.liftPath p v).val = u.val ∨ (L.liftPath p v).val = v.val := by
        have hm : (L.liftPath p v).val ∈ ({u.val, v.val} : Finset Q) := by
          rw [← hpair]; simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr trivial
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      have hne : (L.liftPath p u).val ≠ (L.liftPath p v).val := by
        intro he
        have hcard := congrArg Finset.card hpair
        simp only [he, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
          Finset.card_singleton, Finset.card_pair hdistinct] at hcard
        omega
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact False.elim (hne (hu.trans hv.symm))
      · exact Or.inl ⟨Subtype.ext hu, Subtype.ext hv⟩
      · exact Or.inr ⟨Subtype.ext hu, Subtype.ext hv⟩
      · exact False.elim (hne (hu.trans hv.symm))
    have hsquare : L.liftPath p (L.liftPath p u) = u ∧
        L.liftPath p (L.liftPath p v) = v := by
      rcases hperm with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · constructor <;> simp only [hu, hv]
      · constructor <;> simp only [hu, hv]
    obtain ⟨doubled, hdword, hdlift⟩ := concatenate_paths p p
    have hdu : L.liftPath doubled u = u := (hdlift u).trans hsquare.1
    have hdv : L.liftPath doubled v = v := (hdlift v).trans hsquare.2
    have closed_u : ∃ r : FinitePath C (c + c) (e u.val) (e u.val),
        (pathWord r).map read = pathWord p ++ pathWord p := by
      have hex := actual_path_lift doubled u
      rw [hdu] at hex
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, hr.trans hdword⟩
    have closed_v : ∃ r : FinitePath C (c + c) (e v.val) (e v.val),
        (pathWord r).map read = pathWord p ++ pathWord p := by
      have hex := actual_path_lift doubled v
      rw [hdv] at hex
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, hr.trans hdword⟩
    have distinct_endpoints : e u.val ≠ e v.val := fun he => hdistinct (e.injective he)
    fail "OPEN: repeat the two actual closed doubled words over all integer indices, including every seam"

  refine ⟨pair_card, ?_, zero_forgetting, ?_, pi, ?_, pi_continuous, pi_shift, ?_⟩
  · intro d
    constructor
    · exact ambiguity_to_walk d
    · exact walk_to_ambiguity d
  · intro hP ha
    obtain ⟨ell, hmax⟩ := attained_longest hP ha
    refine ⟨ell, hmax, ⟨longest_forgetting ell hmax, ?_⟩, ?_⟩
    · intro d hd
      by_contra hlt
      exact walk_to_ambiguity d (walk_prefix ell d (by omega) hmax.1) hd
    · intro d hle
      exact walk_to_ambiguity d (walk_prefix ell d hle hmax.1)
  · intro x i
    rfl
  · refine ⟨?_, finite_window_inverse, periodic_collision, ?_, ?_⟩
    · tfae_have 2 → 1 := conjugacy_injective
      tfae_have 3 → 2 := by
        intro h
        obtain ⟨d, hd⟩ := h
        exact forgetting_conjugacy d hd
      tfae_have 3 ↔ 4 := forgetting_iff_acyclic
      tfae_have 1 → 3 := by
        intro hi
        by_contra hn
        obtain ⟨c, hc, hb, x, x', hne, he, _⟩ := periodic_collision hn
        exact hne (hi he)
      tfae_finish
    · constructor
      · intro h hcollision
        obtain ⟨k, hk, hb, x, x', hne, he, _, _⟩ := hcollision
        exact hne (conjugacy_injective h he)
      · intro hnone
        by_contra hn
        have hnof : ¬ ∃ d, Forgets L d := fun ⟨d, hd⟩ => hn (forgetting_conjugacy d hd)
        obtain ⟨c, hc, hb, x, x', hne, he, _, hx, hx'⟩ := periodic_collision hnof
        apply hnone
        refine ⟨2 * c, by omega, by omega, x, x', hne, he, ?_, ?_⟩
        · simpa only [Int.natCast_mul, Nat.cast_ofNat] using hx
        · simpa only [Int.natCast_mul, Nat.cast_ofNat] using hx'
    · constructor
      · intro h hcollision
        obtain ⟨k, k', hk, hb, hk', hb', x, x', hne, he, _, _⟩ := hcollision
        exact hne (conjugacy_injective h he)
      · intro hnone
        by_contra hn
        have hnof : ¬ ∃ d, Forgets L d := fun ⟨d, hd⟩ => hn (forgetting_conjugacy d hd)
        obtain ⟨c, hc, hb, x, x', hne, he, _, hx, hx'⟩ := periodic_collision hnof
        apply hnone
        refine ⟨2 * c, 2 * c, by omega, by omega, by omega, by omega,
          x, x', hne, he, ?_, ?_⟩
        · simpa only [Int.natCast_mul, Nat.cast_ofNat] using hx
        · simpa only [Int.natCast_mul, Nat.cast_ofNat] using hx'


end D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
