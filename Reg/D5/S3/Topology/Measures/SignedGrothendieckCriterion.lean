import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedGrothendieckCriterion

/-!
# Exact source families for the signed splitting and sufficient criterion

The readouts retain the original theorem telescopes and observe final scalar
neighborhoods or equality of points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.Measures
open _root_.D5.S3.Topology.Measures.SignedGrothendieckCriterion
universe u

@[reducible] def rawSignature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rawActual : DependentFamily.Realization rawSignature :=
  DependentFamily.realize rawSignature (fun _ _ (r : ℝ) => 𝓝 r) (fun a => nomatch a)

def rawLaw (R : DependentFamily.Realization rawSignature) : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K],
  ∀ (s : ℕ → SignedMeasure K)
    (hs : ∀ n, (s n).totalVariation.Regular)
    (hb : ∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) ,
    ∃ (j : ℕ → ℕ) (E : ℕ → Set K) (r : ℝ) (sInf : SignedMeasure K),
      StrictMono j ∧ (∀ n, MeasurableSet (E n)) ∧
      Pairwise (fun i n => Disjoint (E i) (E n)) ∧
      (∀ n, s (j n) = (s (j n)).restrict (E n) + (s (j n)).restrict (E n)ᶜ) ∧
      (∀ n, (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).Regular ∧
        (SignedMeasure.totalVariation ((s (j n)).restrict (E n)ᶜ)).Regular) ∧
      (∀ n, (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ +
        (SignedMeasure.totalVariation ((s (j n)).restrict (E n)ᶜ)).real univ =
        (s (j n)).totalVariation.real univ) ∧
      0 ≤ r ∧ Tendsto
        (fun n => (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ)
        atTop (𝓝 r) ∧ sInf.totalVariation.Regular ∧
      ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
        Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional
          ((s (j n)).restrict (E n)ᶜ))) atTop
          (R.readout () () (Φ (NormPreservingLifts.signedFunctional sInf)))

@[reducible] def rawArena : DependentFamily.Arena where
  signature := rawSignature
  Law := rawLaw.{u}
abbrev rawScope := type_of% (@exists_signed_raw_restriction_splitting.{u})
theorem rawBridge : rawScope.{u} ↔ rawArena.{u}.Law rawActual := Iff.rfl

def rawRejected : DependentFamily.Realization rawSignature :=
  DependentFamily.realize rawSignature (fun _ _ _ => (⊥ : Filter ℝ)) (fun a => nomatch a)

theorem rawPositive : rawArena.{u}.Law rawActual :=
  rawBridge.mp (@exists_signed_raw_restriction_splitting.{u})

theorem rawNegative : ¬ rawArena.{u}.Law rawRejected := by
  intro h
  have hr := h (K := ULift.{u} Unit) (fun _ => (0 : SignedMeasure (ULift.{u} Unit)))
    (by intro n; simp only [SignedMeasure.totalVariation_zero]; infer_instance)
    ⟨0, by intro n; simp [SignedMeasure.totalVariation_zero]⟩
  obtain ⟨j, E, r, sInf, hj, hE, hd, hdec, hreg, hm, hr, hmass, hsInf, hweak⟩ := hr
  have ht := hweak 0
  have hbot : (⊥ : Filter ℝ).NeBot := by
    simpa only [rawRejected, DependentFamily.realize] using ht.neBot
  exact (Filter.not_neBot.mpr rfl) hbot

def rawFamily : DependentFamily.Registration rawArena.{u} rawScope.{u} where
  actual := rawActual
  bridge := rawBridge
  variation := ⟨rawPositive, rawRejected, rawNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rawRejected, ?_, rfl, rawNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (𝓝 (0 : ℝ)) ≠ (𝓝 (1 : ℝ))
    exact fun he => zero_ne_one (nhds_injective he)

@[reducible] def weakSignature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weakActual : DependentFamily.Realization weakSignature :=
  DependentFamily.realize weakSignature (fun _ _ r => 𝓝 r) (fun a => nomatch a)

def weakLaw (R : DependentFamily.Realization weakSignature) : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K],
  ∀
    (H : ∀ s : ℕ → SignedMeasure K,
      (∀ n, (s n).totalVariation.Regular) →
      (∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) →
      (∀ g : C(K, ℝ), Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s n) g) atTop (𝓝 0)) →
      ∀ E : ℕ → Set K, (∀ n, MeasurableSet (E n)) →
        Pairwise (fun i n => Disjoint (E i) (E n)) →
        Tendsto (fun n =>
          (SignedMeasure.totalVariation ((s n).restrict (E n))).real univ) atTop (𝓝 0))
    (F : ℕ → StrongDual ℝ C(K, ℝ)) (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) ,
    ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (F n)) atTop (R.readout () () (Φ FInf))

@[reducible] def weakArena : DependentFamily.Arena where
  signature := weakSignature
  Law := weakLaw.{u}
abbrev weakScope := type_of% (@weak_of_disjoint_diagonal_variation.{u})
theorem weakBridge : weakScope.{u} ↔ weakArena.{u}.Law weakActual := Iff.rfl

def weakRejected : DependentFamily.Realization weakSignature :=
  DependentFamily.realize weakSignature (fun _ _ _ => (⊥ : Filter ℝ)) (fun a => nomatch a)

theorem weakPositive : weakArena.{u}.Law weakActual :=
  weakBridge.mp (@weak_of_disjoint_diagonal_variation.{u})

theorem weakNegative : ¬ weakArena.{u}.Law weakRejected := by
  intro h
  have Hempty : ∀ s : ℕ → SignedMeasure (ULift.{u} Empty),
      (∀ n, (s n).totalVariation.Regular) →
      (∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) →
      (∀ g : C(ULift.{u} Empty, ℝ), Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s n) g) atTop (𝓝 0)) →
      ∀ E : ℕ → Set (ULift.{u} Empty), (∀ n, MeasurableSet (E n)) →
        Pairwise (fun i n => Disjoint (E i) (E n)) →
        Tendsto (fun n =>
          (SignedMeasure.totalVariation ((s n).restrict (E n))).real univ) atTop (𝓝 0) := by
    intro s hs hb hz E hE hd
    have heq (n : ℕ) : (s n).restrict (E n) = 0 := by
      ext A hA
      have ha : A = ∅ := Subsingleton.elim A ∅
      simp [ha]
    simp only [heq, SignedMeasure.totalVariation_zero]
    simpa using (tendsto_const_nhds (x := (0 : ℝ)))
  have ht := h (K := ULift.{u} Empty) Hempty (fun _ => 0) 0
    (fun g => by simpa using tendsto_const_nhds) 0
  have hbot : (⊥ : Filter ℝ).NeBot := by simpa only [weakRejected, DependentFamily.realize] using ht.neBot
  exact (Filter.not_neBot.mpr rfl) hbot

def weakFamily : DependentFamily.Registration weakArena.{u} weakScope.{u} where
  actual := weakActual
  bridge := weakBridge
  variation := ⟨weakPositive, weakRejected, weakNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weakRejected, ?_, rfl, weakNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (𝓝 (0 : ℝ)) ≠ (𝓝 (1 : ℝ))
    exact fun he => zero_ne_one (nhds_injective he)

def rawRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_signed_raw_restriction_splitting.{u})
      (DependentFamily.Realization rawSignature) Type Unit where
  unitName := `D5.S3.Topology.Measures.SignedGrothendieckCriterion.exists_signed_raw_restriction_splitting.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion.rawFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rawArena.{u}⟩
  objectArena := .source ⟨rawArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rawArena.{u} ⟨rawFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize rawSignature
    (fun _ _ (r : ℝ) => 𝓝 r) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.SignedGrothendieckCriterion
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def weakRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@weak_of_disjoint_diagonal_variation.{u})
      (DependentFamily.Realization weakSignature) Type Unit where
  unitName := `D5.S3.Topology.Measures.SignedGrothendieckCriterion.weak_of_disjoint_diagonal_variation.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion.weakFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weakArena.{u}⟩
  objectArena := .source ⟨weakArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weakArena.{u} ⟨weakFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize weakSignature
    (fun _ _ r => 𝓝 r) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.SignedGrothendieckCriterion
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

@[reducible] def oscillationSignature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def oscillationActual : DependentFamily.Realization oscillationSignature :=
  DependentFamily.realize oscillationSignature (fun _ _ r => 𝓝 r) (fun a => nomatch a)

def oscillationLaw (R : DependentFamily.Realization oscillationSignature) : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K],
  ∀ [ZeroDimensionalSpace K],
  ∀ (O : ∀ t : ℕ → SignedMeasure K, ∀ W : ℕ → Set K,
    (∀ n, (t n).totalVariation.Regular) →
    (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
    Pairwise (fun i n => Disjoint (W i) (W n)) →
    (∀ n, (t n).totalVariation.real univ = 1) →
    (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
    (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
    ∃ Z : Set K, IsClopen Z ∧
      {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧ {n | t n Z = 0}.Infinite)
    (F : ℕ → StrongDual ℝ C(K, ℝ)) (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) ,
    ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (F n)) atTop (R.readout () () (Φ FInf))

@[reducible] def oscillationArena : DependentFamily.Arena where
  signature := oscillationSignature
  Law := oscillationLaw.{u}
abbrev oscillationScope := type_of% (@weak_of_signed_clopen_oscillation.{u})
theorem oscillationBridge : oscillationScope.{u} ↔ oscillationArena.{u}.Law oscillationActual := Iff.rfl

def oscillationRejected : DependentFamily.Realization oscillationSignature :=
  DependentFamily.realize oscillationSignature (fun _ _ _ => (⊥ : Filter ℝ)) (fun a => nomatch a)

theorem oscillationPositive : oscillationArena.{u}.Law oscillationActual :=
  oscillationBridge.mp (@weak_of_signed_clopen_oscillation.{u})

theorem oscillationNegative : ¬ oscillationArena.{u}.Law oscillationRejected := by
  intro h
  have Oempty : ∀ t : ℕ → SignedMeasure (ULift.{u} Empty),
      ∀ W : ℕ → Set (ULift.{u} Empty),
      (∀ n, (t n).totalVariation.Regular) →
      (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
      Pairwise (fun i n => Disjoint (W i) (W n)) →
      (∀ n, (t n).totalVariation.real univ = 1) →
      (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
      (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
      ∃ Z : Set (ULift.{u} Empty), IsClopen Z ∧
        {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧ {n | t n Z = 0}.Infinite := by
    intro t W ht hW hd hn hp hc
    obtain ⟨x, hx⟩ := (hW 0).2
    exact x.down.elim
  have ht := h (K := ULift.{u} Empty) Oempty (fun _ => 0) 0
    (fun g => by simpa using tendsto_const_nhds) 0
  have hbot : (⊥ : Filter ℝ).NeBot := by simpa only [oscillationRejected, DependentFamily.realize] using ht.neBot
  exact (Filter.not_neBot.mpr rfl) hbot

def oscillationFamily : DependentFamily.Registration oscillationArena.{u} oscillationScope.{u} where
  actual := oscillationActual
  bridge := oscillationBridge
  variation := ⟨oscillationPositive, oscillationRejected, oscillationNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨oscillationRejected, ?_, rfl, oscillationNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (𝓝 (0 : ℝ)) ≠ (𝓝 (1 : ℝ))
    exact fun he => zero_ne_one (nhds_injective he)


def oscillationRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@weak_of_signed_clopen_oscillation.{u})
      (DependentFamily.Realization oscillationSignature) Type Unit where
  unitName := `D5.S3.Topology.Measures.SignedGrothendieckCriterion.weak_of_signed_clopen_oscillation.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion.oscillationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨oscillationArena.{u}⟩
  objectArena := .source ⟨oscillationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oscillationArena.{u} ⟨oscillationFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize oscillationSignature
    (fun _ _ r => 𝓝 r) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.SignedGrothendieckCriterion
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

@[reducible] def pointSignature : DependentFamily.Signature where
  Params := Type u
  State := fun K => K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ K => K → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def pointActual : DependentFamily.Realization pointSignature.{u} :=
  DependentFamily.realize pointSignature (fun _ _ a b => a = b) (fun a => nomatch a)

def pointLaw (R : DependentFamily.Realization pointSignature) : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K],
  ∀ [ZeroDimensionalSpace K],
  ∀ (O : ∀ t : ℕ → SignedMeasure K, ∀ W : ℕ → Set K,
    (∀ n, (t n).totalVariation.Regular) →
    (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
    Pairwise (fun i n => Disjoint (W i) (W n)) →
    (∀ n, (t n).totalVariation.real univ = 1) →
    (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
    (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
    ∃ Z : Set K, IsClopen Z ∧
      {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧ {n | t n Z = 0}.Infinite)
    (x : ℕ → K) (p : K) (hlim : Tendsto x atTop (𝓝 p)),
    ∀ᶠ n in atTop, R.readout () K (x n) p

@[reducible] def pointArena : DependentFamily.Arena where
  signature := pointSignature.{u}
  Law := pointLaw.{u}
abbrev pointScope := type_of% (@eventually_eq_of_signed_clopen_oscillation.{u})
theorem pointBridge : pointScope.{u} ↔ pointArena.{u}.Law pointActual := Iff.rfl

def pointRejected : DependentFamily.Realization pointSignature.{u} :=
  DependentFamily.realize pointSignature (fun _ _ _ _ => False) (fun a => nomatch a)

theorem pointPositive : pointArena.{u}.Law pointActual :=
  pointBridge.mp (@eventually_eq_of_signed_clopen_oscillation.{u})

theorem pointNegative : ¬ pointArena.{u}.Law pointRejected := by
  intro h
  have Ounit : ∀ t : ℕ → SignedMeasure (ULift.{u} Unit),
      ∀ W : ℕ → Set (ULift.{u} Unit),
      (∀ n, (t n).totalVariation.Regular) →
      (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
      Pairwise (fun i n => Disjoint (W i) (W n)) →
      (∀ n, (t n).totalVariation.real univ = 1) →
      (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
      (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
      ∃ Z : Set (ULift.{u} Unit), IsClopen Z ∧
        {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧ {n | t n Z = 0}.Infinite := by
    intro t W ht hW hd hn hp hc
    obtain ⟨a, ha⟩ := (hW 0).2
    obtain ⟨b, hb⟩ := (hW 1).2
    exact ((disjoint_left.mp (hd Nat.zero_ne_one)) ha
      (by simpa only [Subsingleton.elim b a] using hb)).elim
  have ht := h (K := ULift.{u} Unit) Ounit (fun _ => ⟨()⟩) ⟨()⟩ tendsto_const_nhds
  have hf : ∀ᶠ _ : ℕ in atTop, False := ht
  obtain ⟨n, hn⟩ := hf.exists
  exact hn

def pointFamily : DependentFamily.Registration pointArena.{u} pointScope.{u} where
  actual := pointActual
  bridge := pointBridge
  variation := ⟨pointPositive, pointRejected, pointNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pointRejected, ?_, rfl, pointNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro he
    have he' := congrFun he ⟨false⟩
    have ht : (ULift.up true : ULift.{u} Bool) = ULift.up false := by
      exact Eq.mp he' rfl
    cases congrArg ULift.down ht

def pointRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, u, 0, 0}
      (@eventually_eq_of_signed_clopen_oscillation.{u})
      (DependentFamily.Realization pointSignature.{u}) Type Unit where
  unitName := `D5.S3.Topology.Measures.SignedGrothendieckCriterion.eventually_eq_of_signed_clopen_oscillation.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion.pointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pointArena.{u}⟩
  objectArena := .source ⟨pointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pointArena.{u} ⟨pointFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize pointSignature.{u}
    (fun _ _ a b => a = b) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.SignedGrothendieckCriterion
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion
