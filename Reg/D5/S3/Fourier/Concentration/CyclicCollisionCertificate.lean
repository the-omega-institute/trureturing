import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.CyclicCollisionCertificate

/-! Source readouts of the real spectrum and weights in the cyclic collision certificate. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicCollisionCertificate
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
  (tailCollisionMass nearCollisionMass)
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
  (monomialWeight monomialFrequency)
open _root_.D5.S3.Fourier.FinitePoisson (character)
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

private abbrev Probe := ULift.{u} Bool
private def counts (v : Bool) (j : Probe.{u}) : ℕ := if j.down = v then 1 else 0
private def spectrum (j : Probe.{u}) : ℝ := if j.down then 1 else 0
private def lattice (j : Probe.{u}) : ℤ := if j.down then 1 else 0

private theorem probe_univ : (univ : Finset Probe.{u}) = {ULift.up false, ULift.up true} := by
  ext j
  rcases j with ⟨b⟩
  cases b <;> simp

private theorem counts_ne : counts.{u} false ≠ counts true := by
  intro e
  have h := congrFun e (ULift.up false)
  norm_num [counts] at h

private theorem counts_not_mem : counts.{u} false ∉ ({counts true} : Finset (Probe.{u} → ℕ)) :=
  fun h => counts_ne (mem_singleton.mp h)

private theorem probe_degree_one : piAntidiag (univ : Finset Probe.{u}) 1 =
    {counts false, counts true} := by
  ext m
  simp only [mem_piAntidiag, mem_univ, implies_true, and_true, mem_insert, mem_singleton]
  rw [probe_univ, sum_insert (by decide), sum_singleton]
  constructor
  · intro hm
    by_cases h : m (ULift.up false) = 1
    · left
      ext j
      rcases j with ⟨b⟩
      cases b <;> simp [counts] <;> omega
    · right
      ext j
      rcases j with ⟨b⟩
      cases b <;> simp [counts] <;> omega
  · rintro (rfl | rfl) <;> rfl

private theorem probe_sum {A : Type} [AddCommMonoid A] (f : Probe.{u} → A) :
    (∑ j, f j) = f (ULift.up false) + f (ULift.up true) := by
  rw [probe_univ, sum_insert (by decide), sum_singleton]

private theorem probe_multinomial (v : Bool) :
    Nat.multinomial (univ : Finset Probe.{u}) (counts v) = 1 := by
  rw [Nat.multinomial, probe_sum, probe_univ, prod_insert (by decide), prod_singleton]
  cases v <;> rfl

private theorem probe_weight (v : Bool) : monomialWeight (1 : Probe.{u} → ℝ) (counts v) = 1 := by
  simp [monomialWeight, probe_multinomial]

private theorem probe_frequency (c : ℝ) (v : Bool) :
    monomialFrequency (fun j => c * spectrum j) (counts.{u} v) = if v then c else 0 := by
  cases v <;> norm_num [monomialFrequency, spectrum, counts, probe_sum]

private def upperRejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev upperArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (a : J → ℤ) (_ : ∀ j, 0 ≤ w j) (q p : ℕ)
    {step e η : ℝ} (_ : 0 < step) (_ : 0 ≤ e) (_ : ∀ j, |g j - step * (a j : ℝ)| ≤ e),
    let H := ⌊(η + 2 * p * e) / step⌋
    tailCollisionMass (V.readout () ⟨J, g⟩) w p η ≤ cyclicCollisionMass q a w p
      ((Icc (-H) H).image (fun x : ℤ => (x : ZMod q)))

private theorem upperRejected_law : ¬ upperArena.{u}.Law upperRejected := by
  intro law
  have h := law spectrum 1 lattice (fun _ => zero_le_one) 2 1
    (step := 1) (e := 0) (η := 0) zero_lt_one le_rfl (by
      intro j
      rcases j with ⟨b⟩
      cases b <;> norm_num [spectrum, lattice])
  change tailCollisionMass (fun _ : Probe.{u} => 0) 1 1 0 ≤ _ at h
  norm_num at h
  have hfalse : (latticeFrequency lattice (counts.{u} false) : ZMod 2) = 0 := by
    norm_num [latticeFrequency, lattice, counts, probe_sum]
  have htrue : (latticeFrequency lattice (counts.{u} true) : ZMod 2) = 1 := by
    norm_num [latticeFrequency, lattice, counts, probe_sum]
  have hne : (0 : ZMod 2) ≠ 1 := by decide
  simp only [tailCollisionMass, nearCollisionMass, cyclicCollisionMass, probe_degree_one,
    sum_insert counts_not_mem, sum_singleton, probe_weight, one_mul,
    monomialFrequency, mul_zero, sum_const_zero, sub_self, abs_zero, ite_eq_left le_rfl,
    Int.cast_sub, mem_singleton] at h
  simp only [sub_eq_zero] at h
  first
  | norm_num [hfalse, htrue, hne, hne.symm] at h <;> done
  | norm_num [latticeFrequency, lattice, counts, probe_sum, hne, hne.symm] at h <;> done
  | set_option pp.all true in trace_state

private def lowerRejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ q j => 3 * q.2 j) (fun e => nomatch e)

abbrev lowerArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (a : J → ℤ) (_ : ∀ j, 0 ≤ w j) (q p : ℕ) (H lo hi : ℤ)
    {step e : ℝ} (_ : 0 ≤ step) (_ : 0 ≤ e)
    (_ : ∀ j, |g j - step * (a j : ℝ)| ≤ e) (_ : ∀ j, a j ∈ Set.Icc lo hi)
    (_ : (p : ℤ) * (hi - lo) + H < q),
    cyclicCollisionMass q a w p ((Icc (-H) H).image (fun x : ℤ => (x : ZMod q))) ≤
      tailCollisionMass (V.readout () ⟨J, g⟩) w p (step * (H : ℝ) + 2 * p * e)

private theorem lowerRejected_law : ¬ lowerArena.{u}.Law lowerRejected := by
  intro law
  have h := law spectrum 1 0 (fun _ => zero_le_one) 1 1 0 0 0
    (step := 1) (e := 1) zero_le_one zero_le_one (by
      intro j
      rcases j with ⟨b⟩
      cases b <;> norm_num [spectrum]) (by simp) (by norm_num)
  change _ ≤ tailCollisionMass (fun j : Probe.{u} => 3 * spectrum j) 1 1 _ at h
  have hband : (Icc (-(0 : ℤ)) 0).image (fun x : ℤ => (x : ZMod 1)) = {0} := by simp
  have hfreq (m : Probe.{u} → ℕ) : latticeFrequency 0 m = 0 := by simp [latticeFrequency]
  simp only [cyclicCollisionMass, tailCollisionMass, nearCollisionMass, hband, probe_degree_one,
    sum_insert counts_not_mem, sum_singleton, probe_weight, one_mul,
    hfreq, sub_self, Int.cast_zero, mem_singleton, probe_frequency] at h
  norm_num at h

private def fourierRejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fourierArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (q : ℕ) [NeZero q] (a : J → ℤ) (w : J → ℝ) (p : ℕ) (R : Finset (ZMod q)),
    (q : ℂ) * (cyclicCollisionMass q a (V.readout () ⟨J, w⟩) p R : ℂ) =
      ∑ k : ZMod q, ((‖∑ j, (w j : ℂ) * character k (a j : ZMod q)‖ ^ (2 * p) : ℝ) : ℂ) *
        ∑ y ∈ R, character k (-y)

private theorem fourierRejected_law : ¬ fourierArena.{u}.Law fourierRejected := by
  intro law
  have h := law (J := Probe.{u}) 1 0 1 1 {0}
  have hw (v : Bool) : monomialWeight (fun _ : Probe.{u} => 0) (counts v) = 0 := by
    rw [monomialWeight, probe_multinomial, probe_univ, prod_insert (by decide), prod_singleton]
    cases v <;> norm_num [counts]
  have huniv : (univ : Finset (ZMod 1)) = {0} := by
    ext k
    simp only [mem_univ, mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  have hv : cyclicCollisionMass 1 0 (fun _ : Probe.{u} => 0) 1 {0} = 0 := by
    unfold cyclicCollisionMass
    rw [probe_degree_one]
    simp only [sum_insert counts_not_mem, sum_singleton, hw, zero_mul, ite_self,
      add_zero]
  change ((1 : ℕ) : ℂ) * (cyclicCollisionMass 1 0 (fun _ : Probe.{u} => 0) 1 {0} : ℂ) = _ at h
  rw [hv, huniv] at h
  norm_num [probe_sum] at h

def upperEvidence :
    Registration upperArena.{u} (type_of% @tailCollisionMass_le_cyclic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tailCollisionMass_le_cyclic.{u}, upperRejected, upperRejected_law⟩
  sensitivity := sensitivity upperArena.Law actual upperRejected upperRejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def upperRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tailCollisionMass_le_cyclic.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.upperUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.upperEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena.{u}⟩
  objectArena := .source ⟨upperArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena.{u} ⟨upperEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicCollisionCertificate
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def lowerEvidence :
    Registration lowerArena.{u} (type_of% @cyclicCollisionMass_le_tail_of_no_wrap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclicCollisionMass_le_tail_of_no_wrap.{u}, lowerRejected, lowerRejected_law⟩
  sensitivity := sensitivity lowerArena.Law actual lowerRejected lowerRejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def lowerRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclicCollisionMass_le_tail_of_no_wrap.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.lowerUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.lowerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena.{u}⟩
  objectArena := .source ⟨lowerArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena.{u} ⟨lowerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicCollisionCertificate
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn",
        "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fourierEvidence :
    Registration fourierArena.{u} (type_of% @cyclicCollisionMass_fourier.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclicCollisionMass_fourier.{u}, fourierRejected, fourierRejected_law⟩
  sensitivity := sensitivity fourierArena.Law actual fourierRejected fourierRejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def fourierRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclicCollisionMass_fourier.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.fourierUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate.fourierEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨fourierArena.{u}⟩
  objectArena := .source ⟨fourierArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fourierArena.{u} ⟨fourierEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicCollisionCertificate
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms upperRegistration
#print axioms lowerRegistration
#print axioms fourierRegistration

end
end Reg.D5.S3.Fourier.Concentration.CyclicCollisionCertificate
