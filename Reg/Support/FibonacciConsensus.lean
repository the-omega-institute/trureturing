import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Mathlib.Data.Nat.Find

namespace Reg.Support.FibonacciConsensus
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
noncomputable section

/-- Closed observation constraints are internal candidates; the original Record is unchanged. -/
def Candidate (theta : ℝ) (h : List Color) (alpha : ℕ → Label) : Prop :=
  ∃ x : ℕ → ℝ, OperationOmega alpha x ∧
    ∀ p (hp : p < h.length), ClosedExpanded theta h[p] (x p)

def inhabited (theta : ℝ) (h : List Color) : Prop := ∃ alpha, Candidate theta h alpha

def representative (theta : ℝ) (h : List Color) : ℕ → Label := by
  classical
  exact if hc : inhabited theta h then hc.choose else fun _ => .L0

def Agreement (theta : ℝ) (h : List Color) (n : ℕ) : Prop :=
  ∀ alpha, Candidate theta h alpha → ∀ p, p < n → alpha p = representative theta h p

def width (theta : ℝ) (h : List Color) : ℕ := by
  classical
  exact Nat.findGreatest (Agreement theta h) h.length

def output (theta : ℝ) (h : List Color) : List Label := by
  classical
  exact if inhabited theta h then List.ofFn (fun p : Fin (width theta h) =>
    representative theta h p) else []

abbrev Configuration := List Color × ℕ

def initial : Configuration := ([],0)

def action (theta : ℝ) (s : Configuration) : Op Configuration Color Label :=
  .acquire (fun c =>
    let h := s.1 ++ [c]
    some ((h,(output theta h).length), (output theta h).drop s.2))

private theorem representative_candidate {theta : ℝ} {h : List Color}
    (hc : inhabited theta h) : Candidate theta h (representative theta h) := by
  classical
  simpa only [representative, dif_pos hc] using hc.choose_spec

private theorem width_bound (theta : ℝ) (h : List Color) : width theta h ≤ h.length := by
  classical
  exact Nat.findGreatest_le _

private theorem width_agreement (theta : ℝ) (h : List Color) :
    Agreement theta h (width theta h) := by
  classical
  apply Nat.findGreatest_spec (Nat.zero_le h.length)
  intro alpha ha p hp
  omega

private theorem output_length {theta : ℝ} {h : List Color} (hc : inhabited theta h) :
    (output theta h).length = width theta h := by
  classical
  simp [output,hc]

private theorem output_agrees {theta : ℝ} {h : List Color} {alpha : ℕ → Label}
    (ha : Candidate theta h alpha) (p : ℕ) (hp : p < (output theta h).length) :
    (output theta h)[p] = alpha p := by
  classical
  have hc : inhabited theta h := ⟨alpha,ha⟩
  have hp' : p < width theta h := by simpa [output_length hc] using hp
  simpa [output,hc] using (width_agreement theta h alpha ha p hp').symm

private theorem candidate_prefix {theta : ℝ} {h j : List Color} (hj : h <+: j)
    {alpha : ℕ → Label} (ha : Candidate theta j alpha) : Candidate theta h alpha := by
  obtain ⟨x,hx,hobs⟩ := ha
  refine ⟨x,hx,?_⟩
  intro p hp
  have hpj := lt_of_lt_of_le hp hj.length_le
  simpa only [hj.getElem hp] using hobs p hpj

private theorem output_prefix {theta : ℝ} {h j : List Color}
    (hj : h <+: j) (hc : inhabited theta j) : output theta h <+: output theta j := by
  classical
  have old : inhabited theta h := ⟨hc.choose,candidate_prefix hj hc.choose_spec⟩
  have newBase := representative_candidate hc
  have oldBase := candidate_prefix hj newBase
  have hwidth : width theta h ≤ width theta j := by
    apply Nat.le_findGreatest ((width_bound theta h).trans hj.length_le)
    intro alpha ha p hp
    have a := width_agreement theta h alpha (candidate_prefix hj ha) p hp
    have b := width_agreement theta h (representative theta j) oldBase p hp
    exact a.trans b.symm
  apply List.prefix_iff_getElem.mpr
  refine ⟨?_,?_⟩
  · rw [output_length old, output_length hc]
    exact hwidth
  · intro p hp
    have hpj : p < (output theta j).length := by
      rw [output_length hc]
      exact lt_of_lt_of_le (by simpa only [output_length old] using hp) hwidth
    rw [output_agrees oldBase p hp, output_agrees newBase p hpj]

private theorem original_candidate (o : Ownership) (theta : ℝ) (htheta : 0 ≤ theta)
    (alpha : ℕ → Label) (r : ℕ → Color) (hr : OperationRecord o theta .closed alpha r)
    (n : ℕ) : Candidate theta (front r n) alpha := by
  obtain ⟨x,omega,err,herr,hobs⟩ := hr
  obtain ⟨path,h0,hedge,hsupport,hrec⟩ := omega
  refine ⟨x,⟨path,h0,hedge,hsupport,hrec⟩,?_⟩
  intro p hp
  have hs : InSupport .G0 (x p) := by
    have hh := hsupport p
    cases he : path p <;> simp only [he,InSupport,supportUpper] at hh
    · exact hh
    · refine ⟨hh.1,hh.2.trans ?_⟩
      change t ≤ 1+t
      linarith
  have owned := (owned_color_error o theta (r p) (x p) hs).mpr
    ⟨err p,herr p,hobs p⟩
  have interval := (owned_color_interval o theta htheta (r p) (x p)).mp owned
  simpa [ClosedExpanded,front] using
    (show InSupport .G0 (x p) ∧ cut (r p).val-theta ≤ x p ∧
      x p ≤ cut ((r p).val+1)+theta from ⟨hs,interval.2.1,interval.2.2.1⟩)

private theorem front_succ (r : ℕ → Color) (n : ℕ) :
    front r (n+1) = front r n ++ [r n] := by
  unfold front
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl

private theorem output_nil (theta : ℝ) : output theta [] = [] := by
  classical
  by_cases hc : inhabited theta [] <;> simp [output,hc,width]

/-- Every original Run retains the genuine history and the maximal consensus output. -/
theorem run_invariant (o : Ownership) (theta : ℝ) (htheta : 0 ≤ theta)
    (alpha : ℕ → Label) (r : ℕ → Color) (hr : OperationRecord o theta .closed alpha r)
    (t : Frame Configuration Label)
    (run : Run (action theta) (full r) ⟨initial,0,[]⟩ t) :
    t.state = (front r t.acquired,(output theta (front r t.acquired)).length) ∧
    t.output = output theta (front r t.acquired) := by
  obtain ⟨vertices,trace⟩ := run
  induction trace with
  | refl => simp [initial,front,output_nil]
  | @tail middle finish vertices trace edge ih =>
    cases edge with
    | internal c d q out batch instruction => cases instruction
    | acquire c d q out batch f a instruction available result =>
      have ha : a = r q := Option.some.inj available.symm
      subst a
      have hf : f = (fun a =>
        let h := c.1 ++ [a]
        some ((h,(output theta h).length),(output theta h).drop c.2)) :=
        Op.acquire.inj instruction.symm
      rw [hf] at result
      have hc := ih.1
      have ho := ih.2
      dsimp only at hc ho
      rw [hc] at result
      simp only [front_succ] at result
      have pair := Option.some.inj result
      have hd := congrArg Prod.fst pair
      have hb := congrArg Prod.snd pair
      dsimp only at hd hb
      subst d
      subst batch
      have pref : output theta (front r q) <+: output theta (front r (q+1)) :=
        output_prefix (by rw [front_succ]; exact List.prefix_append _ _)
          ⟨alpha,original_candidate o theta htheta alpha r hr (q+1)⟩
      refine ⟨by simp [front_succ],?_⟩
      dsimp only
      rw [ho]
      obtain ⟨suffix,hsuffix⟩ := pref
      have take : (output theta (front r (q+1))).take
          (output theta (front r q)).length = output theta (front r q) := by
        rw [← hsuffix]
        simp
      rw [front_succ] at take ⊢
      calc
        _ = (output theta (front r q ++ [r q])).take
            (output theta (front r q)).length ++
            (output theta (front r q ++ [r q])).drop
              (output theta (front r q)).length := by rw [take]
        _ = _ := List.take_append_drop _ _

/-- Exact safety quantifies over every original record, including infinite sources. -/
theorem safety (o : Ownership) (theta : ℝ) (htheta : 0 ≤ theta) :
    ∀ alpha r, OperationRecord o theta .closed alpha r → ∀ t,
      Run (action theta) (full r) ⟨initial,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p := by
  intro alpha r hr t run p hp
  have inv := run_invariant o theta htheta alpha r hr t run
  have ha := original_candidate o theta htheta alpha r hr t.acquired
  simpa only [inv.2] using output_agrees ha p (by simpa only [inv.2] using hp)

/-- Ready includes acquire; zero-step Drain proves the complete original postprocessing premise. -/
theorem postprocessing (o : Ownership) (theta : ℝ) :
    ∀ alpha r, OperationRecord o theta .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run (action theta) (full r) ⟨initial,0,[]⟩ ⟨c,q,out⟩ →
      action theta c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain (action theta) ⟨d,q+1,out++batch⟩ t := by
  intro alpha r hr c d q out batch f run instruction result
  exact ⟨_,⟨[d],.refl⟩,Or.inr ⟨_,rfl⟩⟩

/-- A finite prefix must isolate each finite-source output prefix in the closed candidate set. -/
def FiniteIsolation (o : Ownership) (theta : ℝ) : Prop :=
  ∀ alpha r, OperationRecord o theta .closed alpha r → OperationFiniteSource alpha →
    ∀ p, ∃ N, p < N ∧ ∀ beta, Candidate theta (front r N) beta →
      ∀ j, j ≤ p → beta j = alpha j

private theorem acquisitions (theta : ℝ) (r : ℕ → Color) (n : ℕ) :
    ∃ t : Frame Configuration Label,
      Run (action theta) (full r) ⟨initial,0,[]⟩ t ∧ t.acquired = n := by
  induction n with
  | zero => exact ⟨_,⟨_,.refl⟩,rfl⟩
  | succ n ih =>
    obtain ⟨t,run,hq⟩ := ih
    let h := t.state.1 ++ [r t.acquired]
    refine ⟨⟨(h,(output theta h).length),t.acquired+1,
      t.output ++ (output theta h).drop t.state.2⟩,?_,by simpa [hq]⟩
    apply run_trans run
    exact ⟨_,Trace.tail Trace.refl
      (Step.acquire _ _ _ _ _ _ _ rfl rfl rfl)⟩

/-- Isolation is the remaining geometric premise; this theorem does not assert it. -/
theorem liveness_of_isolation (o : Ownership) (theta : ℝ) (htheta : 0 ≤ theta)
    (isolate : FiniteIsolation o theta) :
    ∀ alpha r, OperationRecord o theta .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run (action theta) (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length := by
  classical
  intro alpha r hr finite p
  obtain ⟨N,hN,isolation⟩ := isolate alpha r hr finite p
  have ca := original_candidate o theta htheta alpha r hr N
  have hc : inhabited theta (front r N) := ⟨alpha,ca⟩
  have base := representative_candidate hc
  have width_large : p+1 ≤ width theta (front r N) := by
    apply Nat.le_findGreatest (by simpa [front] using hN)
    intro beta cb j hj
    exact (isolation beta cb j (by omega)).trans
      (isolation _ base j (by omega)).symm
  obtain ⟨t,run,hq⟩ := acquisitions theta r N
  have invariant := run_invariant o theta htheta alpha r hr t run
  refine ⟨t,run,?_⟩
  rw [invariant.2,hq,output_length hc]
  omega

#print axioms safety
#print axioms postprocessing
#print axioms liveness_of_isolation
end
end Reg.Support.FibonacciConsensus
