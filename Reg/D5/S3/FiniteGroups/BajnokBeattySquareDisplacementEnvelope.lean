/- Faithful source-owner Reg attempt. No declared_validated claim.
The original telescope, complete integer spans, actual W readouts, infinite q
domain and both band endpoints are retained. State is the full signed triple;
the original domain and band remain hypotheses of Law, not hidden truncations.
Whole-role interventions zero an entire count family. Actual count variation
is proved below for EVERY admissible p,q,t, by diagonal binomial growth.

Minimal extra visibility needed: remove `private` from the EXISTING
Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope.choose_grow_diagonal
(proof unchanged). Its source is a supplier, not copied here.
The source-occurrence selector, escapeFrom and current binding evidence remain
unfinished: https://github.com/the-omega-institute/trureturing/issues/25856 .
No external audit is assumed and continuation is unknown. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope
import Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope

open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth
open _root_.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

private noncomputable def actualCounts (p q t : ℤ) : ℕ × ℕ :=
  let m : ℤ := 2*q*t-1
  let n : ℕ := (p*m).toNat
  let v1a : Plane := ![p*(m-1)/2,p*(m+1)/2]
  let v2a : Plane := ![p*(m-q^2)/2,-(p*(m+q^2)/2)]
  let v1q : Plane := ![p*(m-q)/2,p*(m+q)/2]
  let v2q : Plane := ![p*(m-q)/2,-(p*(m+q)/2)]
  let Ka := Submodule.span ℤ (Set.range ![v1a,v2a])
  let Kq := Submodule.span ℤ (Set.range ![v1q,v2q])
  let Fa : Plane →+ (Plane ⧸ Ka) := Ka.mkQ.toAddMonoidHom
  let Fq : Plane →+ (Plane ⧸ Kq) := Kq.mkQ.toAddMonoidHom
  (W Fa n,W Fq n)

abbrev envelopeSignature : Signature where
  Params := Unit
  State _ := ℤ × ℤ × ℤ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def envelopeActual : Realization envelopeSignature :=
  realize envelopeSignature
    (fun i _ x => if i = 0 then (actualCounts x.1 x.2.1 x.2.2).1
      else (actualCounts x.1 x.2.1 x.2.2).2)
    (fun e => nomatch e)

noncomputable def envelopeZero (i : Fin 2) : Realization envelopeSignature :=
  realize envelopeSignature
    (fun j p x => if j = i then 0 else envelopeActual.readout j p x)
    (fun e => nomatch e)

/-- Only the two original actual count occurrences are abstracted. -/
def envelopeLaw (R : Realization envelopeSignature) : Prop :=
  ∀ (p q t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q)
      (hqo : Odd q) (ht : q+1 ≤ 2*t),
    let m : ℤ := 2*q*t-1
    let n : ℕ := (p*m).toNat
    let v1a : Plane := ![p*(m-1)/2,p*(m+1)/2]
    let v2a : Plane := ![p*(m-q^2)/2,-(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2,p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2,-(p*(m+q)/2)]
    let Ka := Submodule.span ℤ (Set.range ![v1a,v2a])
    let Kq := Submodule.span ℤ (Set.range ![v1q,v2q])
    let Fa : Plane →+ (Plane ⧸ Ka) := Ka.mkQ.toAddMonoidHom
    let Fq : Plane →+ (Plane ⧸ Kq) := Kq.mkQ.toAddMonoidHom
    let Wa := R.readout 0 () (p,q,t)
    let Wq := R.readout 1 () (p,q,t)
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1))
    let nu : ℝ := (q : ℝ)^2
    let C : ℝ := 2*(nu+1)/(3*(nu-1)^2)
    let G : ℝ := Real.exp s+Real.exp (-nu*s)
    let H : ℝ := C*s^3*(Real.exp s-nu^2*Real.exp (-nu*s))
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*(Wa : ℝ)/(Wq : ℝ)-G-H/(p : ℝ)^2| ≤ 1/(5*(p : ℝ)^4)

abbrev envelopeArena : Arena where
  signature := envelopeSignature
  Law := envelopeLaw

private theorem actual_bridge : (type_of% actual_square_displacement_envelope) ↔
    envelopeArena.Law envelopeActual := by
  rfl

private theorem actual_law : envelopeArena.Law envelopeActual := by
  exact actual_bridge.mp actual_square_displacement_envelope

/-- Generic analytic rejection of a zero ratio on the WHOLE envelope band. -/
private theorem zero_ratio_fails {P v s : ℝ} (hP : 5 ≤ P) (hv : 9 ≤ v)
    (hs : (2/3 : ℝ) ≤ s) :
    ¬ |0-(Real.exp s+Real.exp (-v*s))-
      (2*(v+1)/(3*(v-1)^2))*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2| ≤
        1/(5*P^4) := by
  have hs0 : 0 < s := by linarith
  have hP0 : 0 < P := by linarith
  have htail := real_rational_tail_on_ray hv hs
  have he := Real.add_one_le_exp s
  have hpos : 0 < Real.exp s-v^2*Real.exp (-v*s) := by linarith [htail.2.2]
  have hv0 : 0 < v := by linarith
  have hvm : 0 < v-1 := by linarith
  have hC : 0 < 2*(v+1)/(3*(v-1)^2) := by positivity
  have hcorr : 0 ≤ (2*(v+1)/(3*(v-1)^2))*s^3*
      (Real.exp s-v^2*Real.exp (-v*s))/P^2 := by positivity
  have herror : 1/(5*P^4) < 1 := by
    apply (div_lt_iff₀ (show 0 < 5*P^4 by positivity)).2
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5) hP 4
    norm_num at hh; linarith only [hh]
  intro h
  have hh := (abs_le.mp h).1
  linarith [Real.exp_pos (-v*s)]

private theorem rejected_law (i : Fin 2) : ¬ envelopeArena.Law (envelopeZero i) := by
  intro h
  have hh := h 5 3 5 (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
  let s : ℝ := ((3:ℝ)^2-1)*(5:ℝ)^2/(2*((145:ℝ)+1))
  have hs : (2/3:ℝ) ≤ s := by norm_num [s]
  have hshi : s ≤ 5/7 := by norm_num [s]
  have hz := zero_ratio_fails (P := (5:ℝ)) (v := (3:ℝ)^2) (s := s)
    (by norm_num) (by norm_num) hs
  apply hz
  fin_cases i <;>
    simpa [envelopeArena,envelopeLaw,envelopeZero,envelopeActual,realize,s]
      using hh hs hshi

/-- Exact classification at arbitrary signed p,q,t. No cardinality is assumed. -/
private theorem counts_formula (p q t : ℤ) (hp : 0 < p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (ht : q+1 ≤ 2*t) :
    let m := 2*q*t-1
    let n := (p*m).toNat
    (actualCounts p q t).1 = 2*(Nat.choose n (p*(m+1)/2).toNat+
      Nat.choose n (p*(m+q^2)/2).toNat) ∧
    (actualCounts p q t).2 = 4*Nat.choose n (p*(m+q)/2).toNat := by
  let m := 2*q*t-1
  have hq : 0 < q := by omega
  have hqm : q^2 < m := by
    have hh := mul_le_mul_of_nonneg_left ht hq.le
    dsimp [m]; nlinarith only [hh,hq3]
  have hmo : Odd m := ⟨q*t-1,by dsimp [m]; ring⟩
  have hq2o : Odd (q^2) := by simpa only [pow_two] using hqo.mul hqo
  have h1m : 1 < m := by nlinarith [sq_nonneg (q-3)]
  have hqm' : q < m := by nlinarith [sq_nonneg (q-3)]
  obtain ⟨_,hv1a,hv2a,_⟩ := asymmetric_rank_one_actual_data p m 1 (q^2)
    hp hpo hmo odd_one hq2o (by norm_num) h1m (pow_pos hq 2) hqm
  obtain ⟨_,hv1q,hv2q,_⟩ := asymmetric_rank_one_actual_data p m q q
    hp hpo hmo hqo hqo hq hqm' hq hqm'
  have ha := odd_boundary_count_of_sumDiff p m 1 (q^2) _ _
    hp hpo hmo odd_one hq2o (by norm_num) h1m (pow_pos hq 2) hqm hv1a hv2a
  have hb := odd_boundary_count_of_sumDiff p m q q _ _
    hp hpo hmo hqo hqo hq hqm' hq hqm' hv1q hv2q
  constructor
  · exact ha
  · dsimp [actualCounts]
    dsimp only at hb
    convert hb using 1 <;> ring

/-- All admissible native count states vary under t↦t+1, for every odd q.
The existing generic diagonal-growth supplier proves the strict inequalities. -/
private theorem strict_counts_step (p q t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (ht : q+1 ≤ 2*t) :
    (actualCounts p q t).1 < (actualCounts p q (t+1)).1 ∧
      (actualCounts p q t).2 < (actualCounts p q (t+1)).2 := by
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have ht0 : 0 < t := by omega
  let m := 2*q*t-1
  let m' := 2*q*(t+1)-1
  let n := (p*m).toNat
  let n' := (p*m').toNat
  let d := (p*q).toNat
  have hqm : q^2 < m := by
    have hh := mul_le_mul_of_nonneg_left ht hq.le
    dsimp [m]; nlinarith only [hh,hq3]
  have hm : 0 < m := by nlinarith [sq_nonneg q]
  have hmstep : m' = m+2*q := by dsimp only [m,m']; ring
  have hm' : 0 < m' := by rw [hmstep]; omega
  have hmo : Odd m := ⟨q*t-1,by dsimp [m]; ring⟩
  have hmo' : Odd m' := ⟨q*(t+1)-1,by dsimp [m']; ring⟩
  have hn : (n : ℤ) = p*m := Int.toNat_of_nonneg (mul_pos hp hm).le
  have hn' : (n' : ℤ) = p*m' := Int.toNat_of_nonneg (mul_pos hp hm').le
  have hd : (d : ℤ) = p*q := Int.toNat_of_nonneg (mul_pos hp hq).le
  have hd0 : 0 < d := by exact_mod_cast (show (0:ℤ)<(d:ℤ) by rw [hd]; positivity)
  have hnstep : n' = n+2*d := by
    have hh : (n' : ℤ) = ((n+2*d : ℕ) : ℤ) := by
      push_cast; rw [hn,hn',hd]; dsimp [m,m']; ring
    exact_mod_cast hh
  have hchoose (b : ℤ) (hbo : Odd b) (hb : 0 < b) (hbm : b < m) :
      Nat.choose n (p*(m+b)/2).toNat < Nat.choose n' (p*(m'+b)/2).toNat := by
    have hi2 : 2*(p*(m+b)/2) = p*(m+b) := by
      simpa only [mul_comm] using Int.ediv_mul_cancel (((hmo.add_odd hbo).mul_left p).two_dvd)
    have hj2 : 2*(p*(m'+b)/2) = p*(m'+b) := by
      simpa only [mul_comm] using Int.ediv_mul_cancel (((hmo'.add_odd hbo).mul_left p).two_dvd)
    have hi0 : 0 ≤ p*(m+b)/2 := by nlinarith [mul_pos hp (show 0 < m+b by omega)]
    have hj0 : 0 ≤ p*(m'+b)/2 := by nlinarith [mul_pos hp (show 0 < m'+b by omega)]
    have hi : ((p*(m+b)/2).toNat : ℤ) = p*(m+b)/2 := Int.toNat_of_nonneg hi0
    have hj : ((p*(m'+b)/2).toNat : ℤ) = p*(m'+b)/2 := Int.toNat_of_nonneg hj0
    have hfit : (p*(m+b)/2).toNat ≤ n := by
      have hh : ((p*(m+b)/2).toNat : ℤ) ≤ (n : ℤ) := by
        rw [hi,hn]
        have hgap := mul_pos hp (sub_pos.mpr hbm)
        nlinarith only [hi2,hgap]
      exact_mod_cast hh
    have histep : (p*(m'+b)/2).toNat = (p*(m+b)/2).toNat+d := by
      have hh : ((p*(m'+b)/2).toNat : ℤ) =
          (((p*(m+b)/2).toNat+d : ℕ) : ℤ) := by
        push_cast; rw [hi,hj,hd]; dsimp [m,m'] at hi2 hj2
        nlinarith only [hi2,hj2]
      exact_mod_cast hh
    rw [hnstep,histep]
    exact choose_grow_diagonal n _ d hfit hd0
  have hA := hchoose 1 odd_one (by norm_num) (by nlinarith [sq_nonneg (q-3)])
  have hB := hchoose q hqo hq (by nlinarith [sq_nonneg (q-3)])
  have hD := hchoose (q^2) (by simpa only [pow_two] using hqo.mul hqo) (pow_pos hq 2) hqm
  have hc := counts_formula p q t hp hpo hq3 hqo ht
  have hc' := counts_formula p q (t+1) hp hpo hq3 hqo (by omega)
  dsimp only at hc hc'
  rw [hc.1,hc'.1,hc.2,hc'.2]
  dsimp only [n,n',m,m'] at hA hB hD
  exact ⟨by omega,by omega⟩

private theorem actual_dependence : ObservationalDependence envelopeSignature envelopeActual := by
  intro i
  refine ⟨(),(25,3,24),(25,3,25),?_⟩
  have hh := strict_counts_step 25 3 24 (by norm_num) (by decide)
    (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · simpa [envelopeActual,realize] using ne_of_lt hh.1
  · simpa [envelopeActual,realize] using ne_of_lt hh.2

noncomputable def envelopeSource : Registration envelopeArena
    (type_of% actual_square_displacement_envelope) where
  actual := envelopeActual
  bridge := actual_bridge
  variation := ⟨actual_law,envelopeZero 0,rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨envelopeZero i,?_,rfl,rejected_law i⟩
      intro j hj
      funext p x
      simp [envelopeZero,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def envelopeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_square_displacement_envelope)
      (Realization envelopeSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope.actual_square_displacement_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope.envelopeSource
  realizationSource := none
  generated := false
  arena := .source ⟨envelopeArena⟩
  objectArena := .source ⟨envelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source envelopeArena ⟨envelopeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize envelopeSignature
    (fun i _ x => if i = 0 then (actualCounts x.1 x.2.1 x.2.2).1
      else (actualCounts x.1 x.2.1 x.2.2).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope
