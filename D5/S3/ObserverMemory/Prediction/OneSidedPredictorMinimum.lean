/- GID: D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A decaying one-sided history law has an attained sharp total-update state minimum. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section

namespace D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum

open Filter Topology
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

/-- The state contains all persistent information; update receives only a bit. -/
structure Predictor (S : Type*) where
  initial : S
  update : Bool → S → S
  output : S → ℝ
  output_mem : ∀ s, output s ∈ Set.Icc 0 1

def Predictor.run {S : Type*} (M : Predictor S) (h : List Bool) : S :=
  runWord M.update h M.initial

/-- A reset word has already contained outcome zero; otherwise its length is the age. -/
def historyLaw (x : ℝ) (p : ℕ → ℝ) (h : List Bool) : ℝ :=
  if false ∈ h then x else p h.length

def Correct {S : Type*} (M : Predictor S) (x : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ h, |M.output (M.run h) - historyLaw x p h| ≤ ε

private theorem run_append {S : Type*} (u : Bool → S → S) (a b : List Bool) (s : S) :
    runWord u (a ++ b) s = runWord u b (runWord u a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons t a ih => exact ih (u t s)

private theorem run_ones {S : Type*} (u : Bool → S → S) (n : ℕ) (s : S) :
    runWord u (List.replicate n true) s = (u true)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, runWord, Function.iterate_succ_apply] using ih (u true s)

private theorem recurrent_output {S : Type*} (M : Predictor S) (x ε : ℝ) (p : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 0)) (hM : Correct M x p ε)
    (i j : ℕ) (hij : i < j)
    (he : M.run (List.replicate i true) = M.run (List.replicate j true)) :
    p i ≤ 2 * ε := by
  let F := M.update true
  have he' : F^[i] M.initial = F^[j] M.initial := by
    simpa [Predictor.run, run_ones, F] using he
  have hfix : F^[j-i] (F^[i] M.initial) = F^[i] M.initial := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hij)]
    exact he'.symm
  have hrec (k : ℕ) : M.run (List.replicate (i+k*(j-i)) true) = M.run (List.replicate i true) := by
    simp only [Predictor.run, run_ones]
    change F^[i+k*(j-i)] M.initial = F^[i] M.initial
    rw [Nat.add_comm i, Function.iterate_add_apply, Nat.mul_comm k, Function.iterate_mul]
    exact Function.iterate_fixed hfix k
  have hindex : Tendsto (fun k : ℕ => i+k*(j-i)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => k) _ tendsto_id
    intro k
    have := Nat.le_mul_of_pos_right k (show 0 < j-i by omega)
    omega
  have hout : M.output (M.run (List.replicate i true)) ≤ ε := by
    apply ge_of_tendsto (by simpa using (hp.comp hindex).add_const ε)
    exact Eventually.of_forall fun k => by
      have hh := (abs_le.mp (hM (List.replicate (i+k*(j-i)) true))).2
      simp only [historyLaw, List.mem_replicate, Bool.false_eq_true, and_false,
        ↓reduceIte, List.length_replicate] at hh
      rw [hrec k] at hh
      linarith
  have hi := (abs_le.mp (hM (List.replicate i true))).1
  simp [historyLaw] at hi
  linarith

private theorem reset_ne_ones {S : Type*} (M : Predictor S) (x ε : ℝ) (p : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 0)) (hM : Correct M x p ε) (hsmall : 2*ε < x)
    (i : ℕ) : M.run [false] ≠ M.run (List.replicate i true) := by
  intro he
  have hbound (k : ℕ) : x ≤ p (i+k) + 2*ε := by
    have h1 := abs_le.mp (hM ([false] ++ List.replicate k true))
    have h2 := abs_le.mp (hM (List.replicate (i+k) true))
    have hr : M.run ([false] ++ List.replicate k true) = M.run (List.replicate (i+k) true) := by
      simp only [Predictor.run, run_append, List.replicate_add]
      exact congrArg (runWord M.update (List.replicate k true)) he
    simp only [historyLaw, List.mem_append, List.mem_singleton, true_or,
      ↓reduceIte] at h1
    simp [historyLaw] at h2
    rw [hr] at h1
    linarith [h1.1, h2.2]
  have hl : Tendsto (fun k => p (i+k)+2*ε) atTop (𝓝 (2*ε)) := by
    simpa using (hp.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat i)).add_const (2*ε)
  exact (not_le_of_gt hsmall) (ge_of_tendsto hl (Eventually.of_forall hbound))

private def machineUpdate (N : ℕ) : Bool → Fin (N+1) ⊕ Unit → Fin (N+1) ⊕ Unit
  | false, _ => .inr ()
  | true, .inr _ => .inr ()
  | true, .inl n => .inl ⟨min (n.val+1) N, by omega⟩

private theorem reset_run (N : ℕ) (h : List Bool) :
    runWord (machineUpdate N) h (.inr ()) = .inr () := by
  induction h with
  | nil => rfl
  | cons b h ih => cases b <;> simpa [runWord,machineUpdate] using ih

private theorem saturated_run (N : ℕ) (h : List Bool) (n : ℕ) :
    runWord (machineUpdate N) h (.inl ⟨min n N,by omega⟩) =
      if false ∈ h then .inr () else .inl ⟨min (n+h.length) N,by omega⟩ := by
  induction h generalizing n with
  | nil => simp [runWord]
  | cons b h ih =>
    cases b
    · simp [runWord,machineUpdate,reset_run]
    · have he : (Sum.inl ⟨min (min n N+1) N,by omega⟩ : Fin (N+1) ⊕ Unit) =
          .inl ⟨min (n+1) N,by omega⟩ := by
        congr 1
        apply Fin.ext
        dsimp
        omega
      simp only [runWord,machineUpdate]
      rw [he,ih]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- For any nonnegative decreasing law tending to zero, the first nonstrict cutoff
at twice the error gives the exact attained number of fully charged states.
This is a history-law theorem; a physical instrument needs a separate trace bridge. -/
theorem sharp_predictor_minimum (x ε : ℝ) (p : ℕ → ℝ) (N : ℕ)
    (hx : x ∈ Set.Ioc 0 1) (hε : 0 ≤ ε) (hsmall : 2*ε < x)
    (hp0 : ∀ n, 0 ≤ p n) (hpx : ∀ n, p n ≤ x)
    (hmono : Antitone p) (hlim : Tendsto p atTop (𝓝 0))
    (hcut : ∀ n, p n ≤ 2*ε ↔ N ≤ n) :
    (∃ M : Predictor (Fin (N+1) ⊕ Unit), Correct M x p ε) ∧
      Fintype.card (Fin (N+1) ⊕ Unit) = N+2 ∧
      (∀ (S : Type*) [Fintype S] (M : Predictor S), Correct M x p ε → N+2 ≤ Fintype.card S) := by
  constructor
  · let out : Fin (N+1) ⊕ Unit → ℝ := fun s => match s with
      | .inr _ => x
      | .inl n => if n.val < N then p n.val else p N / 2
    let M : Predictor (Fin (N+1) ⊕ Unit) := {
      initial := .inl ⟨0,by omega⟩
      update := machineUpdate N
      output := out
      output_mem := by
        intro s
        cases s with
        | inr _ => exact ⟨hx.1.le,hx.2⟩
        | inl n =>
          dsimp [out]
          split_ifs
          · exact ⟨hp0 _,(hpx _).trans hx.2⟩
          · constructor <;> linarith [hp0 N,hpx N,hx.2] }
    refine ⟨M,fun h => ?_⟩
    have hr : M.run h = if false ∈ h then .inr () else .inl ⟨min h.length N,by omega⟩ := by
      simpa [M,Predictor.run] using saturated_run N h 0
    rw [hr]
    by_cases hz : false ∈ h
    · simpa [M,out,historyLaw,hz] using hε
    · simp only [historyLaw,hz,↓reduceIte]
      change |(if min h.length N < N then p (min h.length N) else p N/2) - p h.length| ≤ ε
      by_cases hn : h.length < N
      · simp [min_eq_left hn.le,hn,hε]
      · rw [min_eq_right (by omega : N ≤ h.length),if_neg (lt_irrefl N)]
        have ht := (hcut N).mpr le_rfl
        have hm := hmono (show N ≤ h.length by omega)
        exact abs_le.mpr ⟨by linarith [hp0 h.length],by linarith [hp0 h.length]⟩
  · refine ⟨by simp, ?_⟩
    intro S _ M hM
    let f : Fin (N+1) ⊕ Unit → S := fun s => match s with
      | .inl n => M.run (List.replicate n.val true)
      | .inr _ => M.run [false]
    have hf : Function.Injective f := by
      intro a b hab
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          congr 1
          apply Fin.ext
          rcases lt_trichotomy i.val j.val with h | h | h
          · have hc := (hcut i.val).mp (recurrent_output M x ε p hlim hM i.val j.val h hab)
            omega
          · exact h
          · have hc := (hcut j.val).mp (recurrent_output M x ε p hlim hM j.val i.val h hab.symm)
            omega
        | inr u => exact (reset_ne_ones M x ε p hlim hM hsmall i.val hab.symm).elim
      | inr u =>
        cases b with
        | inl j => exact (reset_ne_ones M x ε p hlim hM hsmall j.val hab).elim
        | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hc
    omega

/-- A strictly positive decaying age law cannot be predicted exactly by finitely many total-update states. -/
theorem exact_prediction_impossible (x : ℝ) (p : ℕ → ℝ)
    (hpos : ∀ n, 0 < p n) (hlim : Tendsto p atTop (𝓝 0))
    {S : Type*} [Fintype S] (M : Predictor S) : ¬ Correct M x p 0 := by
  intro hM
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card S+1) => M.run (List.replicate i.val true)) (by simp)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := recurrent_output M x 0 p hlim hM i.val j.val h he
    linarith [hpos i.val]
  · have hh := recurrent_output M x 0 p hlim hM j.val i.val h he.symm
    linarith [hpos j.val]

#print axioms sharp_predictor_minimum
#print axioms exact_prediction_impossible

end D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
