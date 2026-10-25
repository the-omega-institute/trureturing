import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedGrothendieckCriterion

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

def rawSignature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rawActual : DependentFamily.Realization rawSignature :=
  DependentFamily.realize rawSignature (fun _ _ r => 0 ≤ r) (fun a => nomatch a)

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
      R.readout () () r ∧ Tendsto
        (fun n => (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ)
        atTop (𝓝 r) ∧ sInf.totalVariation.Regular ∧
      ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
        Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional
          ((s (j n)).restrict (E n)ᶜ))) atTop
          (𝓝 (Φ (NormPreservingLifts.signedFunctional sInf)))

def rawArena : DependentFamily.Arena where
  signature := rawSignature
  Law := rawLaw.{u}
abbrev rawScope := type_of% (@exists_signed_raw_restriction_splitting.{u})
theorem rawBridge : rawScope.{u} ↔ rawArena.{u}.Law rawActual := Iff.rfl

def rawRejected : DependentFamily.Realization rawSignature :=
  DependentFamily.realize rawSignature (fun _ _ _ => False) (fun a => nomatch a)

theorem rawPositive : rawArena.{u}.Law rawActual :=
  rawBridge.mp (@exists_signed_raw_restriction_splitting.{u})

theorem rawNegative : ¬ rawArena.{u}.Law rawRejected := by
  intro h
  have hr := h (K := ULift.{u} Unit) (fun _ => (0 : SignedMeasure (ULift.{u} Unit)))
    (by intro n; simp only [SignedMeasure.totalVariation_zero]; infer_instance)
    ⟨0, by intro n; simp [SignedMeasure.totalVariation_zero]⟩
  obtain ⟨j, E, r, sInf, hj, hE, hd, hdec, hreg, hm, hr, _⟩ := hr
  exact hr

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
    refine ⟨(), 0, -1, ?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    norm_num

def weakSignature : DependentFamily.Signature where
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

def weakArena : DependentFamily.Arena where
  signature := weakSignature
  Law := weakLaw.{u}
abbrev weakScope := type_of% (@weak_of_disjoint_diagonal_variation.{u})
theorem weakBridge : weakScope.{u} ↔ weakArena.{u}.Law weakActual := Iff.rfl

def weakRejected : DependentFamily.Realization weakSignature :=
  DependentFamily.realize weakSignature (fun _ _ _ => ⊥) (fun a => nomatch a)

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
      have ha : A = ∅ := Set.eq_empty_iff_forall_not_mem.2 (fun x _ => isEmptyElim x)
      simp [ha]
    simp only [heq, SignedMeasure.totalVariation_zero]
    simpa using (tendsto_const_nhds (x := (0 : ℝ)))
  have ht := h (K := ULift.{u} Empty) Hempty (fun _ => 0) 0
    (fun g => by simpa using tendsto_const_nhds) 0
  exact (Filter.not_neBot.mpr rfl) ht.neBot

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
    (fun _ _ r => 0 ≤ r) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
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
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Measures.SignedGrothendieckCriterion
