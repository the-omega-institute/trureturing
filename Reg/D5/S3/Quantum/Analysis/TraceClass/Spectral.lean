import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit TraceClassSpectral
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral

structure Carrier where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
attribute [instance] Carrier.normed Carrier.inner Carrier.complete
abbrev TraceState (p : Carrier.{u}) := {T : p.H →L[ℂ] p.H // IsTraceClass T}
abbrev spectralSignature : Signature where
  Params := Carrier.{u}
  State p := TraceState p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected := realize spectralSignature.{u} (fun _ _ _ => False) (fun a => nomatch a)

abbrev K := EuclideanSpace ℂ (ULift.{u} Unit)
abbrev sample : Carrier.{u} := ⟨K⟩

theorem finiteTrace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] (T : V →L[ℂ] V) (ht : IsTraceClass T) :
    trace T ht = LinearMap.trace ℂ V T.toLinearMap := by
  unfold trace
  exact (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional T ht.choose_spec.choose).symm

theorem sampleTraceOne : trace (1 : K →L[ℂ] K) (isTraceClass_of_finiteDimensional _) = 1 := by
  rw [finiteTrace]
  simp [K, finrank_euclideanSpace]

theorem sampleTraceNegOne : trace (-1 : K →L[ℂ] K) (isTraceClass_of_finiteDimensional _) = -1 := by
  rw [finiteTrace]
  simp [K, finrank_euclideanSpace]

theorem zeroPositiveImpossible {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (b : HilbertBasis ι ℂ V) (s : ι → ℝ)
    (he : ∀ i, (0 : V →L[ℂ] V) (b i) = (s i : ℂ) • b i)
    (hs : HasSum s 1) : False := by
  have hz (i) : s i = 0 := by
    have hsm : (s i : ℂ) • b i = 0 := by simpa using (he i).symm
    have hcast : (s i : ℂ) = 0 := (smul_eq_zero.mp hsm).resolve_right (b.orthonormal.ne_zero i)
    exact_mod_cast hcast
  have hzero : HasSum s 0 := by
    rw [show s = (fun _ => 0) from funext hz]
    exact hasSum_zero
  exact zero_ne_one (hzero.unique hs)

def fullPredicate (p : Carrier.{u}) (z : TraceState p) : Prop :=
    ∃ (w : Set p.H) (b : HilbertBasis w ℂ p.H) (s : w → ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, z.val (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s (trace z.val z.property).re ∧
      HasSum (fun i => (s i : ℂ)) (trace z.val z.property) ∧
      ∀ x : p.H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (z.val x)

def fullActual := realize spectralSignature.{u} (fun _ p z => fullPredicate p z) (fun a => nomatch a)

def fullLaw (R : Realization spectralSignature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hTpos : 0 ≤ T) (hTtc : IsTraceClass T), R.readout () ⟨H⟩ ⟨T, hTtc⟩
abbrev fullArena : Arena where
  signature := spectralSignature.{u}
  Law := fullLaw

theorem fullActualLaw : fullArena.{u}.Law fullActual := by
  intro H _ _ _ T hTpos hTtc
  exact exists_nonneg_trace_spectral_data hTpos hTtc

theorem fullRejectedLaw : ¬ fullArena.{u}.Law rejected := by
  intro h
  exact h (H := K) (T := 0) (by simp) (isTraceClass_of_finiteDimensional _)

theorem fullDependence : ObservationalDependence spectralSignature.{u} fullActual := by
  intro i
  refine ⟨sample, ⟨0, isTraceClass_of_finiteDimensional _⟩,
    ⟨-1, isTraceClass_of_finiteDimensional _⟩, ?_⟩
  change fullPredicate sample ⟨0, _⟩ ≠ fullPredicate sample ⟨-1, _⟩
  intro heq
  have hgood := exists_nonneg_trace_spectral_data (H := K) (T := 0)
    (by simp) (isTraceClass_of_finiteDimensional _)
  have hbad : fullPredicate sample ⟨-1, _⟩ := Eq.mp heq hgood
  obtain ⟨w, b, s, hn, _, _, hs, _⟩ := hbad
  have hntrace : 0 ≤ (trace (-1 : K →L[ℂ] K) (isTraceClass_of_finiteDimensional _)).re := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg hn
  rw [sampleTraceNegOne] at hntrace
  norm_num at hntrace

def fullFamily : Registration fullArena (fullArena.Law fullActual) where
  actual := realize spectralSignature.{u} (fun _ p z => fullPredicate p z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨fullActualLaw, rejected, fullRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, fullRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := fullDependence

def fullRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TraceClassSpectral.exists_nonneg_trace_spectral_data.{u})
    (type_of% (realize spectralSignature.{u} (fun _ p z => fullPredicate p z) (fun a => nomatch a))) (type_of% (@IsTraceClass.{u})) Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.fullUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.fullFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fullArena⟩
  objectArena := .source ⟨fullArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullArena ⟨fullFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectralSignature.{u} (fun _ p z => fullPredicate p z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Spectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def faithfulPredicate (p : Carrier.{u}) (z : TraceState p) : Prop :=
    ∃ (w : Set p.H) (b : HilbertBasis w ℂ p.H) (s : w → ℝ),
      (∀ i, 0 < s i) ∧ (∀ i, z.val (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      (∀ x : p.H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (z.val x)) ∧
      Countable w

def faithfulActual := realize spectralSignature.{u} (fun _ p z => faithfulPredicate p z) (fun a => nomatch a)

def faithfulLaw (R : Realization spectralSignature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : H →L[ℂ] H} (hσpos : 0 ≤ σ) (hσtc : IsTraceClass σ)
    (hker : σ.toLinearMap.ker = ⊥) (htrace : trace σ hσtc = 1), R.readout () ⟨H⟩ ⟨σ, hσtc⟩
abbrev faithfulArena : Arena where
  signature := spectralSignature.{u}
  Law := faithfulLaw

theorem faithfulActualLaw : faithfulArena.{u}.Law faithfulActual := by
  intro H _ _ _ σ hσpos hσtc hker htrace
  exact exists_faithful_reference_spectral_data hσpos hσtc hker htrace

theorem faithfulRejectedLaw : ¬ faithfulArena.{u}.Law rejected := by
  intro h
  exact h (H := K) (σ := 1) (by exact zero_le_one) (isTraceClass_of_finiteDimensional _) (by ext x; simp) sampleTraceOne

theorem faithfulDependence : ObservationalDependence spectralSignature.{u} faithfulActual := by
  intro i
  refine ⟨sample, ⟨1, isTraceClass_of_finiteDimensional _⟩,
    ⟨0, isTraceClass_of_finiteDimensional _⟩, ?_⟩
  change faithfulPredicate sample ⟨1, _⟩ ≠ faithfulPredicate sample ⟨0, _⟩
  intro heq
  have hgood := exists_faithful_reference_spectral_data (H := K) (σ := 1)
    (by exact zero_le_one) (isTraceClass_of_finiteDimensional _) (by ext x; simp) sampleTraceOne
  have hbad : faithfulPredicate sample ⟨0, _⟩ := Eq.mp heq hgood
  obtain ⟨w, b, s, _, he, _, hs, _⟩ := hbad
  exact zeroPositiveImpossible b s he hs

def faithfulFamily : Registration faithfulArena (faithfulArena.Law faithfulActual) where
  actual := realize spectralSignature.{u} (fun _ p z => faithfulPredicate p z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨faithfulActualLaw, rejected, faithfulRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, faithfulRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := faithfulDependence

def faithfulRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TraceClassSpectral.exists_faithful_reference_spectral_data.{u})
    (type_of% (realize spectralSignature.{u} (fun _ p z => faithfulPredicate p z) (fun a => nomatch a))) (type_of% (@IsTraceClass.{u})) Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.faithfulUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.faithfulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨faithfulArena⟩
  objectArena := .source ⟨faithfulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source faithfulArena ⟨faithfulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectralSignature.{u} (fun _ p z => faithfulPredicate p z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Spectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def branchesPredicate (p : Carrier.{u}) (z : TraceState p) : Prop :=
    (∃ (n : ℕ) (b : HilbertBasis (Fin n) ℂ p.H) (s : Fin n → ℝ),
      FiniteDimensional ℂ p.H ∧ (∀ i, 0 < s i) ∧
      (∀ i, z.val (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      ∀ x : p.H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (z.val x)) ∨
    (∃ (w : Set p.H) (c : HilbertBasis w ℂ p.H) (e : w ≃ ℕ)
      (b : HilbertBasis ℕ ℂ p.H) (s : ℕ → ℝ),
      (∀ i, b i = c (e.symm i)) ∧ (∀ i, 0 < s i) ∧ (∀ i, z.val (b i) = (s i : ℂ) • b i) ∧
      Summable s ∧ HasSum s 1 ∧ HasSum (fun i => (s i : ℂ)) 1 ∧
      ∀ x : p.H, HasSum (fun i => (b.repr x i * (s i : ℂ)) • b i) (z.val x))

def branchesActual := realize spectralSignature.{u} (fun _ p z => branchesPredicate p z) (fun a => nomatch a)

def branchesLaw (R : Realization spectralSignature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : H →L[ℂ] H} (hσpos : 0 ≤ σ) (hσtc : IsTraceClass σ)
    (hker : σ.toLinearMap.ker = ⊥) (htrace : trace σ hσtc = 1), R.readout () ⟨H⟩ ⟨σ, hσtc⟩
abbrev branchesArena : Arena where
  signature := spectralSignature.{u}
  Law := branchesLaw

theorem branchesActualLaw : branchesArena.{u}.Law branchesActual := by
  intro H _ _ _ σ hσpos hσtc hker htrace
  exact faithful_reference_finite_or_nat hσpos hσtc hker htrace

theorem branchesRejectedLaw : ¬ branchesArena.{u}.Law rejected := by
  intro h
  exact h (H := K) (σ := 1) (by exact zero_le_one) (isTraceClass_of_finiteDimensional _) (by ext x; simp) sampleTraceOne

theorem branchesDependence : ObservationalDependence spectralSignature.{u} branchesActual := by
  intro i
  refine ⟨sample, ⟨1, isTraceClass_of_finiteDimensional _⟩,
    ⟨0, isTraceClass_of_finiteDimensional _⟩, ?_⟩
  change branchesPredicate sample ⟨1, _⟩ ≠ branchesPredicate sample ⟨0, _⟩
  intro heq
  have hgood := faithful_reference_finite_or_nat (H := K) (σ := 1)
    (by exact zero_le_one) (isTraceClass_of_finiteDimensional _) (by ext x; simp) sampleTraceOne
  have hbad : branchesPredicate sample ⟨0, _⟩ := Eq.mp heq hgood
  rcases hbad with ⟨n, b, s, _, _, he, _, hs, _⟩ | ⟨w, c, e, b, s, _, _, he, _, hs, _⟩
  · exact zeroPositiveImpossible b s he hs
  · exact zeroPositiveImpossible b s he hs

def branchesFamily : Registration branchesArena (branchesArena.Law branchesActual) where
  actual := realize spectralSignature.{u} (fun _ p z => branchesPredicate p z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨branchesActualLaw, rejected, branchesRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, branchesRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := branchesDependence

def branchesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TraceClassSpectral.faithful_reference_finite_or_nat.{u})
    (type_of% (realize spectralSignature.{u} (fun _ p z => branchesPredicate p z) (fun a => nomatch a))) (type_of% (@IsTraceClass.{u})) Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.branchesUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral.branchesFamily
  realizationSource := none
  generated := false
  arena := .source ⟨branchesArena⟩
  objectArena := .source ⟨branchesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source branchesArena ⟨branchesFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectralSignature.{u} (fun _ p z => branchesPredicate p z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Spectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.TraceClass.Spectral
