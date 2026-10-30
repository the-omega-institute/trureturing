/- GID: D5/S3/Topology/InverseLimit/SignedBirthEnumeration
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedBirthEnumeration
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Countable-generator coding and genuine exhaustive legal signed births under CH. -/

import D5.S3.Topology.InverseLimit.SignedProperLimit
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Topology.ClopenBox
import Mathlib.Analysis.Real.Cardinality

/-! Legal birth data are nonempty and exhaustively enumerable under CH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal ENNReal

namespace D5.S3.Topology.InverseLimit.SignedBirthEnumeration

open SignedProperLimit

universe u v

/-- The finite intersections include the empty intersection, the whole space. -/
noncomputable def signedCode {X : Type u} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (μ : SignedMeasure X) : Finset ℕ → ℝ :=
  fun t => μ (⋂ i ∈ t, MeasurableSpace.natGeneratingSequence X i)

private theorem signedCode_injective {X : Type u} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] : Injective (signedCode (X := X)) := by
  intro μ ν h
  let G := MeasurableSpace.natGeneratingSequence X
  apply VectorMeasure.ext_of_generateFrom (piiUnionInter (fun i => {G i}) univ)
  · intro s hs
    rw [piiUnionInter_singleton_left] at hs
    obtain ⟨t, _, rfl⟩ := hs
    exact congrFun h t
  · rw [generateFrom_piiUnionInter_singleton_left]
    have hG : {t | ∃ k ∈ (univ : Set ℕ), G k = t} = range G := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, true_and, mem_range]
    rw [hG]
    exact (MeasurableSpace.generateFrom_natGeneratingSequence X).symm
  · exact isPiSystem_piiUnionInter _ (fun i => IsPiSystem.singleton (G i)) _
  · simpa [signedCode] using congrFun h ∅

/-- One real sequence codes a whole sequence of signed measures. -/
noncomputable def signedSequenceCode {X : Type u} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (μ : ℕ → SignedMeasure X) :
    (ℕ × Finset ℕ) → ℝ := fun p => signedCode (μ p.1) p.2

private theorem signedSequenceCode_injective {X : Type u} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] : Injective (signedSequenceCode (X := X)) := by
  intro μ ν h
  funext n
  apply signedCode_injective
  funext t
  exact congrFun h (n, t)

/-- No positivity, regularity, norm restriction or representation theorem is
needed for the continuum bound on countably generated signed measures. -/
theorem signed_sequences_card_le_continuum {X : Type u} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] :
    Cardinal.mk (ℕ → SignedMeasure X) ≤ Cardinal.continuum := by
  have h := Cardinal.lift_mk_le_lift_mk_of_injective
    (signedSequenceCode_injective (X := X))
  simpa only [Cardinal.lift_id, Cardinal.lift_uzero, Cardinal.mk_arrow,
    Cardinal.mk_real, Cardinal.lift_continuum, Cardinal.mk_denumerable,
    Cardinal.lift_aleph0, Cardinal.continuum_power_aleph0] using h

/-- The support family is genuinely disjoint and nonempty at every natural index. -/
structure SupportFamily (X : Type u) [TopologicalSpace X] where
  clopen : ℕ → Clopens X
  nonempty : ∀ n, (clopen n : Set X).Nonempty
  disjoint : Pairwise fun m n => Disjoint (clopen m : Set X) (clopen n : Set X)

/-- The actual projection transports an old support sequence to its launch
carrier without changing its indexing. Onto is used only for nonemptiness. -/
def SupportFamily.pullback {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (V : SupportFamily Y)
    (p : C(X, Y)) (hp : Surjective p) : SupportFamily X where
  clopen n := ⟨p ⁻¹' (V.clopen n : Set Y), (V.clopen n).isClopen.preimage p.continuous⟩
  nonempty n := by
    obtain ⟨y, hy⟩ := V.nonempty n
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨x, hy⟩
  disjoint := fun _ _ h => (V.disjoint h).preimage p

/-- Every value is an actual regular signed sequence. Optional candidates are
not values of this type. The complement nullity is a separate certificate. -/
def BornData {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (V : SupportFamily X) :=
  {μ : ℕ → RegularSigned X // ∀ n,
    (μ n).1.totalVariation univ = 1 ∧
    (μ n).1.totalVariation (V.clopen n : Set X)ᶜ = 0 ∧
    (1 / 2 : ℝ≥0∞) ≤ (μ n).1.toJordanDecomposition.posPart univ}

noncomputable def pointJordan {X : Type u} [MeasurableSpace X] (x : X) :
    JordanDecomposition X :=
  ⟨Measure.dirac x, 0, Measure.MutuallySingular.zero_right⟩

noncomputable def regularPoint {X : Type u} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : X) : RegularSigned X :=
  ⟨(pointJordan x).toSignedMeasure, by
    simp only [JordanDecomposition.toJordanDecomposition_toSignedMeasure]
    exact ⟨inferInstanceAs (Measure.Regular (Measure.dirac x)),
      inferInstanceAs (Measure.Regular (0 : Measure X))⟩⟩

/-- The original Dirac construction applied to an entire supplied point list.
The support index is unchanged; this is one legal BornData value. -/
noncomputable def pointBornData {X : Type u} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : SupportFamily X) (x : ℕ → X) (hx : ∀ n, x n ∈ (V.clopen n : Set X)) :
    BornData V := by
  classical
  refine ⟨fun n => regularPoint (x n), fun n => ?_⟩
  simp only [regularPoint, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure, pointJordan,
    add_zero]
  refine ⟨Measure.dirac_apply_of_mem (mem_univ _), ?_, ?_⟩
  · rw [Measure.dirac_apply' _ (V.clopen n).isClopen.1.measurableSet.compl,
      Set.indicator_of_notMem (show x n ∉ (V.clopen n : Set X)ᶜ from not_not.mpr (hx n))]
  · rw [Measure.dirac_apply_of_mem (mem_univ _)]
    norm_num

private theorem born_nonempty {X : Type u} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : SupportFamily X) : Nonempty (BornData V) := by
  classical
  choose x hx using V.nonempty
  exact ⟨pointBornData V x hx⟩

private theorem born_card_le {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (V : SupportFamily X) :
    Cardinal.mk (BornData V) ≤ Cardinal.continuum := by
  let f : BornData V → ℕ → SignedMeasure X := fun μ n => (μ.1 n).1
  have hf : Injective f := by
    intro μ ν h
    apply Subtype.ext
    funext n
    exact Subtype.ext (congrFun h n)
  exact (Cardinal.mk_le_of_injective hf).trans signed_sequences_card_le_continuum

/-- CH and the actual point measures give a genuine total exhaustive enumeration,
including all labels not yet eligible for convergence bookkeeping. -/
theorem exists_signed_enumeration {X : Type 1} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (V : SupportFamily X)
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    ∃ ν : Label → BornData V, Surjective ν := by
  letI : Nonempty (BornData V) := born_nonempty V
  apply Function.exists_surjective_iff.mpr
  refine ⟨inferInstance, ?_⟩
  apply (Cardinal.le_def _ _).mp
  have hc : Cardinal.continuum.{1} = ℵ₁ := by
    simpa using congrArg Cardinal.lift.{1} hCH
  simpa only [Label, Cardinal.mk_Iio_ordinal, Ordinal.card_omega,
    Cardinal.lift_aleph, Ordinal.lift_one, hc] using born_card_le V

private def natCoord (n : ℕ) : Coord (ω : Ordinal.{0}) :=
  ⟨n, Ordinal.natCast_lt_omega0 n⟩

private def cantorSupport (n : ℕ) : Set (Cube (ω : Ordinal.{0})) :=
  {x | x (natCoord n) = true} ∩ ⋂ i : Fin n, {x | x (natCoord i) = false}

private theorem cantorSupport_clopen (n : ℕ) : IsClopen (cantorSupport n) := by
  apply IsClopen.inter
  · exact (isClopen_discrete {true}).preimage (continuous_apply (natCoord n))
  · exact isClopen_iInter_of_finite fun i : Fin n =>
      (isClopen_discrete {false}).preimage (continuous_apply (natCoord i))

private theorem cantorSupport_nonempty (n : ℕ) : (cantorSupport n).Nonempty := by
  classical
  refine ⟨fun i => decide (i = natCoord n), ?_, ?_⟩
  · simp
  · simp only [mem_iInter, mem_ofPred_eq, decide_eq_false_iff_not]
    intro i hi
    have he : (i.val : Ordinal.{0}) = n := congrArg Subtype.val hi
    have : i.val = n := by exact_mod_cast he
    exact (Nat.ne_of_lt i.isLt) this

private theorem cantorSupport_disjoint :
    Pairwise fun m n => Disjoint (cantorSupport m) (cantorSupport n) := by
  intro m n hmn
  apply disjoint_left.mpr
  intro x hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hh := mem_iInter.mp hn.2 ⟨m, h⟩
    exact Bool.noConfusion (hm.1.symm.trans hh)
  · have hh := mem_iInter.mp hm.2 ⟨n, h⟩
    exact Bool.noConfusion (hn.1.symm.trans hh)

/-- Onto projection to the actual base cube supplies legal supports without an
extra existence premise. -/
theorem exists_supportFamily {X : Type u} [TopologicalSpace X]
    (p : C(X, Cube (ω : Ordinal.{0}))) (hp : Surjective p) :
    Nonempty (SupportFamily X) := by
  let V : SupportFamily (Cube (ω : Ordinal.{0})) :=
    ⟨fun n => ⟨cantorSupport n, cantorSupport_clopen n⟩,
      cantorSupport_nonempty, cantorSupport_disjoint⟩
  exact ⟨V.pullback p hp⟩

private theorem support_card_le {X : Type 1} [TopologicalSpace X]
    [Countable (Clopens X)] : Cardinal.mk (SupportFamily X) ≤ Cardinal.continuum := by
  have hi : Injective (SupportFamily.clopen (X := X)) := by
    intro V W h
    cases V
    cases W
    cases h
    rfl
  apply (Cardinal.mk_le_of_injective hi).trans
  rw [Cardinal.mk_arrow]
  simpa only [Cardinal.lift_id, Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0,
    Cardinal.aleph0_power_aleph0] using
    (Cardinal.power_le_power_right (Cardinal.mk_le_aleph0 (α := Clopens X)) :
      Cardinal.mk (Clopens X) ^ ℵ₀ ≤ ℵ₀ ^ ℵ₀)

/-- At any actual proper compact countable cube stage with onto base projection,
CH supplies all disjoint nonempty clopen sequences and a Nat clopen enumeration. -/
theorem exists_clopen_enumerations {X : Type 1} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [SecondCountableTopology X]
    (p : C(X, Cube (ω : Ordinal.{0}))) (hp : Surjective p)
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    (∃ U : Label → SupportFamily X, Surjective U) ∧
    (∃ P : ℕ → Clopens X, Surjective P) := by
  letI : Nonempty (SupportFamily X) := exists_supportFamily p hp
  letI : Countable (Clopens X) := Clopens.countable_iff_secondCountable.mpr inferInstance
  constructor
  · apply Function.exists_surjective_iff.mpr
    refine ⟨inferInstance, ?_⟩
    apply (Cardinal.le_def _ _).mp
    have hc : Cardinal.continuum.{1} = ℵ₁ := by
      simpa using congrArg Cardinal.lift.{1} hCH
    simpa only [Label, Cardinal.mk_Iio_ordinal, Ordinal.card_omega,
      Cardinal.lift_aleph, Ordinal.lift_one, hc] using (support_card_le (X := X))
  · exact exists_surjective_nat _

end D5.S3.Topology.InverseLimit.SignedBirthEnumeration
