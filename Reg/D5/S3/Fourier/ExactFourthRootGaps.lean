import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.ExactFourthRootGaps
import Reg.Support.DependentFamily

/-! Source-bound observations of the threshold, support maximum and weighted phase profiles. -/

namespace Reg.D5.S3.Fourier.ExactFourthRootGaps

open _root_.D5.S3.Fourier.ExactFourthRootGaps
open _root_.D5.S3.Fourier.PhaseObstructionLengths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section

universe u v

abbrev signature (P : Type u) (X : P → Type v) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem sensitivity {P : Type u} {X : P → Type v}
    (law : Realization (signature P X) → Prop)
    (actual rejected : Realization (signature P X)) (h : ¬ law rejected) :
    Sensitivity ⟨signature P X, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
      (funext fun e => nomatch e), h⟩
  · intro e
    exact nomatch e

private abbrev One := ULift.{u} Unit
private abbrev oneIndex : One.{u} := ⟨()⟩
private abbrev singleton : Finset One.{u} := {oneIndex}
private abbrev zeroFrequency : One.{u} → ℝ := fun _ => 0
private abbrev unitWeight : One.{u} → ℝ := fun _ => 1
private abbrev unitRelation : One.{u} → ℤ := fun _ => 1

private theorem singletonRelation :
    IncompatibleRelation singleton.{u} zeroFrequency unitRelation := by
  norm_num [IncompatibleRelation, coefficientSum]

private theorem singletonSupport :
    relationSupport singleton.{u} unitRelation = singleton := by
  simp [relationSupport]

private theorem singletonTau : tau singleton.{u} unitRelation = 1 := by
  change ‖(1 : ℂ) - Complex.I ^ (coefficientSum singleton.{u} unitRelation)‖ ^ 2 /
    (2 * (relationLength singleton.{u} unitRelation : ℝ) ^ 2) = 1
  rw [show coefficientSum singleton.{u} unitRelation = 1 by simp [coefficientSum],
    zpow_one, Complex.sq_norm, Complex.normSq_apply]
  norm_num [relationLength, Complex.sub_re, Complex.sub_im]

private theorem emptyQ (J : Type u) [DecidableEq J] (g w : J → ℝ) (x : ℝ) :
    Q ∅ g w x = 0 := by
  have h := (least_hitting_weight (∅ : Finset J) g w x).1
  obtain ⟨_, _, _, h⟩ := h
  simpa using h

private theorem singletonQ :
    Q singleton.{u} zeroFrequency unitWeight 1 = 1 ∧
      Q singleton.{u} zeroFrequency unitWeight 3 = 0 := by
  constructor
  · obtain ⟨u, hu, hhit, heq⟩ :=
      (least_hitting_weight singleton.{u} zeroFrequency unitWeight 1).1
    have hu' : u = ∅ := by
      rcases Finset.subset_singleton_iff.mp hu with h | h
      · exact h
      · subst u
        obtain ⟨j, hj, _⟩ := hhit unitRelation singletonRelation singletonTau.ge
        simp at hj
    simpa [hu'] using heq
  · have hleast := least_hitting_weight singleton.{u} zeroFrequency unitWeight 3
    have hzero : (0 : ℝ) ∈ {p | ∃ u ⊆ singleton.{u},
        (∀ k, IncompatibleRelation singleton zeroFrequency k → 3 ≤ tau singleton k →
          ∃ j ∈ singleton \ u, k j ≠ 0) ∧ p = mass (singleton \ u) unitWeight /
            mass singleton unitWeight} := by
      refine ⟨singleton, Subset.rfl, ?_, by simp [mass]⟩
      intro k hk ht
      exact (by linarith [(coordinate_loss_same_time _ _ k hk 0).2.1.2] : False).elim
    apply le_antisymm (hleast.2 hzero)
    obtain ⟨u, _, _, heq⟩ := hleast.1
    rw [heq]
    positivity

private theorem emptyCuts (J : Type u) (g : J → ℝ) :
    breakpoints ∅ g = {0, 2} := by
  have h := supportMaximum_zero_or_attained (∅ : Finset J) g ∅
  have hz : supportMaximum ∅ g ∅ = 0 := by
    rcases h with h | ⟨k, hk, _, _⟩
    · exact h.1
    · simp [IncompatibleRelation, coefficientSum] at hk
  simp [breakpoints, hz, Finset.pair_comm]

private theorem previousTwo : predecessor ({0, 2} : Finset ℝ) 2 = 0 := by
  classical
  have he : ({0, 2} : Finset ℝ).filter (· < 2) = {0} := by
    ext x
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hx⟩
      · rfl
      · exact (lt_irrefl _ hx).elim
    · rintro rfl
      norm_num
  unfold predecessor
  simp [he]

private theorem integral_step :
    (∫ x in (0 : ℝ)..2, if x ≤ (1 : ℝ) then (1 : ℝ) else 0) = 1 := by
  let f : ℝ → ℝ := fun _ => 1
  have h (x : ℝ) : (if x ≤ (1 : ℝ) then (1 : ℝ) else 0) = (Iic 1).indicator f x := by
    simp [indicator, f]
  simp_rw [h]
  change (∫ x in (0 : ℝ)..2, {x | x ≤ (1 : ℝ)}.indicator f x) = 1
  rw [intervalIntegral.integral_indicator (f := f) (by norm_num)]
  norm_num [f, intervalIntegral.integral_const]

abbrev WeightedSystem := Σ J : Type u, Σ _ : DecidableEq J, Σ _ : Finset J, Σ _ : J → ℝ, J → ℝ
abbrev thresholdSignature := signature WeightedSystem.{u} (fun _ => ℝ)

def thresholdActual : Realization thresholdSignature.{u} :=
  realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x)
    (fun e => nomatch e)

def thresholdNegative : Realization thresholdSignature.{u} :=
  realize thresholdSignature (fun _ _ _ => -1) (fun e => nomatch e)

def thresholdStep : Realization thresholdSignature.{u} :=
  realize thresholdSignature (fun _ _ x => if x ≤ 1 then 1 else 0) (fun e => nomatch e)

private theorem thresholdDependence : ObservationalDependence thresholdSignature.{u} thresholdActual := by
  intro _
  refine ⟨⟨One.{u}, inferInstance, singleton, zeroFrequency, unitWeight⟩, 1, 3, ?_⟩
  change Q singleton.{u} zeroFrequency unitWeight 1 ≠ Q singleton zeroFrequency unitWeight 3
  rcases singletonQ.{u} with ⟨h1, h3⟩
  rw [h1, h3]
  norm_num

abbrev hittingArena : Arena where
  signature := thresholdSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ) (x : ℝ),
    let P := r.readout () ⟨J, inst, s, g, w⟩ x
    IsLeast {p | ∃ u ⊆ s, (∀ k, IncompatibleRelation s g k → x ≤ tau s k →
      ∃ j ∈ s \ u, k j ≠ 0) ∧ p = (∑ j ∈ s \ u, w j) / ∑ j ∈ s, w j} P

private theorem hittingRejected : ¬ hittingArena.{u}.Law thresholdNegative := by
  intro h
  obtain ⟨v, _, _, heq⟩ := (h (∅ : Finset One.{u}) zeroFrequency unitWeight 1).1
  change (-1 : ℝ) = (∑ j ∈ (∅ : Finset One.{u}) \ v, unitWeight j) /
    ∑ j ∈ (∅ : Finset One.{u}), unitWeight j at heq
  norm_num at heq

abbrev partitionArena : Arena where
  signature := thresholdSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ),
    let cuts := breakpoints s g
    let rights := cuts.erase 0
    let cell := fun b => Ioc (predecessor cuts b) b
    let q := r.readout () ⟨J, inst, s, g, w⟩
    ((rights : Set ℝ).PairwiseDisjoint cell) ∧ (⋃ b ∈ rights, cell b) = Ioc 0 2 ∧
      ∀ b ∈ rights, ∀ x ∈ cell b, q x = q b

private theorem partitionRejected : ¬ partitionArena.{u}.Law thresholdStep := by
  intro h
  have hm : (2 : ℝ) ∈ (breakpoints (∅ : Finset One.{u}) zeroFrequency).erase 0 := by
    rw [emptyCuts]
    norm_num
  have hx : (1 : ℝ) ∈ Ioc (predecessor (breakpoints ∅ zeroFrequency.{u}) 2) 2 := by
    rw [emptyCuts, previousTwo]
    norm_num
  have hbad := (h (∅ : Finset One.{u}) zeroFrequency unitWeight).2.2 2 hm 1 hx
  change (if (1 : ℝ) ≤ 1 then (1 : ℝ) else 0) = (if (2 : ℝ) ≤ 1 then 1 else 0) at hbad
  norm_num at hbad

abbrev stepIntegralArena : Arena where
  signature := thresholdSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ),
    let q := r.readout () ⟨J, inst, s, g, w⟩
    let cuts := breakpoints s g
    (∫ x in (0 : ℝ)..2, q x) =
      ∑ b ∈ cuts.erase 0, (b - predecessor cuts b) * q b

private theorem stepIntegralRejected : ¬ stepIntegralArena.{u}.Law thresholdStep := by
  intro h
  have hbad := h (∅ : Finset One.{u}) zeroFrequency unitWeight
  change (∫ x in (0 : ℝ)..2, if x ≤ (1 : ℝ) then (1 : ℝ) else 0) =
    ∑ b ∈ (breakpoints ∅ zeroFrequency.{u}).erase 0,
      (b - predecessor (breakpoints ∅ zeroFrequency.{u}) b) *
        (if b ≤ (1 : ℝ) then (1 : ℝ) else 0) at hbad
  rw [integral_step, emptyCuts] at hbad
  have he : ({0, 2} : Finset ℝ).erase 0 = {2} := by
    ext x
    simp
  rw [he] at hbad
  norm_num at hbad

private theorem emptyOmission (n : ℕ) :
    omissionFraction (∅ : Finset One.{u}) zeroFrequency unitWeight n = 0 := by
  obtain ⟨v, _, _, heq⟩ := (omissionFraction_isLeast (∅ : Finset One.{u}) zeroFrequency unitWeight n).1
  change _ = mass ((∅ : Finset One.{u}) \ v) unitWeight / mass ∅ unitWeight at heq
  simpa [mass] using heq

abbrev partialLengthArena : Arena where
  signature := thresholdSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ)
      (_hw : ∀ j ∈ s, 0 ≤ w j) (N : ℕ),
    let q := r.readout () ⟨J, inst, s, g, w⟩
    (∑ n ∈ Finset.range N, summand s g w (n + 1)) + perScale s g w (N + 1) ≤
      ∫ x in (0 : ℝ)..2, q x

private theorem partialLengthRejected : ¬ partialLengthArena.{u}.Law thresholdNegative := by
  intro h
  have hbad := h (∅ : Finset One.{u}) zeroFrequency unitWeight (by simp) 0
  change (∑ n ∈ Finset.range 0, summand (∅ : Finset One.{u}) zeroFrequency unitWeight (n + 1)) +
    perScale (∅ : Finset One.{u}) zeroFrequency unitWeight 1 ≤
      ∫ _ in (0 : ℝ)..2, (-1 : ℝ) at hbad
  norm_num [perScale, emptyOmission, intervalIntegral.integral_const] at hbad

abbrev lengthSeriesArena : Arena where
  signature := thresholdSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ)
      (_hw : ∀ j ∈ s, 0 ≤ w j),
    let q := r.readout () ⟨J, inst, s, g, w⟩
    (∑' n, summand s g w (n + 1)) ≤ ∫ x in (0 : ℝ)..2, q x

private theorem lengthSeriesRejected : ¬ lengthSeriesArena.{u}.Law thresholdNegative := by
  intro h
  have hbad := h (∅ : Finset One.{u}) zeroFrequency unitWeight (by simp)
  change (∑' n, summand (∅ : Finset One.{u}) zeroFrequency unitWeight (n + 1)) ≤
    ∫ _ in (0 : ℝ)..2, (-1 : ℝ) at hbad
  norm_num [summand, emptyOmission, intervalIntegral.integral_const] at hbad

abbrev PairSignature := signature ℝ (fun _ => ℝ)

def pairActual : Realization PairSignature :=
  realize PairSignature (fun _ w x => Q pairIndices pairFrequency (fun _ => w) x) (fun e => nomatch e)

def pairRejected : Realization PairSignature :=
  realize PairSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem pairDependence : ObservationalDependence PairSignature pairActual := by
  intro _
  refine ⟨1, 0, 1, ?_⟩
  change Q pairIndices pairFrequency (fun _ => 1) 0 ≠ Q pairIndices pairFrequency (fun _ => 1) 1
  norm_num [pair_exact_Q _ (by norm_num : (0 : ℝ) < 1)]

abbrev pairCostArena : Arena where
  signature := PairSignature
  Law r := ∀ (w : ℝ) (_hw : 0 < w) (x : ℝ),
    let q := r.readout () w x
    q = if x ≤ (1 : ℝ) / 8 then 1 / 2 else 0

private theorem pairCostRejected : ¬ pairCostArena.Law pairRejected := by
  intro h
  have hbad := h 1 (by norm_num) 0
  change (0 : ℝ) = if (0 : ℝ) ≤ 1 / 8 then 1 / 2 else 0 at hbad
  norm_num at hbad

abbrev pairStrictArena : Arena where
  signature := PairSignature
  Law r := ∀ (w : ℝ) (_hw : 0 < w),
    let q := r.readout () w
    let lengthSeries := ∑' n, summand pairIndices pairFrequency (fun _ => w) (n + 1)
    let exactIntegral := ∫ x in (0 : ℝ)..2, q x
    lengthSeries = 1 / 32 ∧ exactIntegral = 1 / 16 ∧ lengthSeries < exactIntegral

private theorem pairStrictRejected : ¬ pairStrictArena.Law pairRejected := by
  intro h
  have hbad := (h 1 (by norm_num)).2.1
  change (∫ _ in (0 : ℝ)..2, (0 : ℝ)) = 1 / 16 at hbad
  norm_num at hbad

abbrev BareSystem := Σ J : Type u, Σ _ : Finset J, Σ _ : J → ℝ, J → ℝ
abbrev timeSignature := signature BareSystem.{u} (fun _ => ℝ)
abbrev deficitSignature := signature BareSystem.{u} (fun _ => Set ℝ)

def timeActual : Realization timeSignature.{u} :=
  realize timeSignature (fun _ p t => average p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e)

def timeBad : Realization timeSignature.{u} :=
  realize timeSignature (fun _ _ _ => 2) (fun e => nomatch e)

def deficitActual : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ p T => deficit p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e)

def deficitBad : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem singletonAverage (t : ℝ) :
    average singleton.{u} (fun _ => 1) unitWeight t = Real.sin t := by
  simp [average, mass]

private theorem timeDependence : ObservationalDependence timeSignature.{u} timeActual := by
  intro _
  refine ⟨⟨One.{u}, singleton, fun _ => 1, unitWeight⟩, 0, Real.pi / 2, ?_⟩
  change average singleton.{u} (fun _ => 1) unitWeight 0 ≠
    average singleton.{u} (fun _ => 1) unitWeight (Real.pi / 2)
  simp [singletonAverage]

private theorem deficitDependence : ObservationalDependence deficitSignature.{u} deficitActual := by
  intro _
  refine ⟨⟨One.{u}, singleton, fun _ => 1, unitWeight⟩, {0}, {Real.pi / 2}, ?_⟩
  change deficit singleton.{u} (fun _ => 1) unitWeight {0} ≠
    deficit singleton.{u} (fun _ => 1) unitWeight {Real.pi / 2}
  simp [deficit, singletonAverage]

abbrev timeArena : Arena where
  signature := timeSignature.{u}
  Law r := ∀ {J : Type u} [DecidableEq J] (s : Finset J) (g w : J → ℝ)
      (_hw : ∀ j ∈ s, 0 ≤ w j) (t : ℝ),
    let A := r.readout () ⟨J, s, g, w⟩ t
    (∫ x in (0 : ℝ)..2, Q s g w x) ≤ 1 - A

abbrev deficitArena : Arena where
  signature := deficitSignature.{u}
  Law r := ∀ {J : Type u} [DecidableEq J] (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
      (_hw : ∀ j ∈ s, 0 ≤ w j),
    let D := r.readout () ⟨J, s, g, w⟩ T
    (∫ x in (0 : ℝ)..2, Q s g w x) ≤ D

private theorem timeRejected : ¬ timeArena.{u}.Law timeBad := by
  intro h
  have hbad := h (∅ : Finset One.{u}) zeroFrequency unitWeight (by simp) 0
  change (∫ x in (0 : ℝ)..2, Q ∅ zeroFrequency.{u} unitWeight x) ≤ 1 - (2 : ℝ) at hbad
  simp_rw [emptyQ] at hbad
  norm_num at hbad

private theorem deficitRejected : ¬ deficitArena.{u}.Law deficitBad := by
  intro h
  have hbad := h (∅ : Finset One.{u}) zeroFrequency unitWeight ∅ (by simp)
  change (∫ x in (0 : ℝ)..2, Q ∅ zeroFrequency.{u} unitWeight x) ≤ -1 at hbad
  simp_rw [emptyQ] at hbad
  norm_num at hbad

abbrev RelationSystem := Σ J : Type u, Finset J
abbrev coefficientSignature := signature RelationSystem.{u} (fun p => p.1 → ℤ)

def coefficientActual : Realization coefficientSignature.{u} :=
  realize coefficientSignature (fun _ p k => tau p.2 k) (fun e => nomatch e)

def coefficientBad : Realization coefficientSignature.{u} :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev coefficientArena : Arena where
  signature := coefficientSignature.{u}
  Law r := ∀ {J : Type u} (s : Finset J) (g : J → ℝ) (k : J → ℤ)
      (_hk : IncompatibleRelation s g k) (t : ℝ),
    let threshold := r.readout () ⟨J, s⟩ k
    0 < relationLength s k ∧ threshold ∈ Ioc (0 : ℝ) 2 ∧
      ∃ j ∈ relationSupport s k, threshold ≤ loss g t j

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature.{u} coefficientActual := by
  intro _
  refine ⟨⟨One.{u}, singleton⟩, unitRelation, fun _ => 0, ?_⟩
  change tau singleton.{u} unitRelation ≠ tau singleton.{u} (fun _ => 0)
  rw [singletonTau]
  change (1 : ℝ) ≠ ‖(1 : ℂ) - Complex.I ^ (coefficientSum singleton.{u} (fun _ => 0))‖ ^ 2 /
    (2 * (relationLength singleton.{u} (fun _ => 0) : ℝ) ^ 2)
  norm_num [coefficientSum, relationLength]

private theorem coefficientRejected : ¬ coefficientArena.{u}.Law coefficientBad := by
  intro h
  have hbad := (h singleton.{u} zeroFrequency unitRelation singletonRelation 0).2.1.1
  exact (lt_irrefl (0 : ℝ)) hbad

abbrev SupportSystem := Σ J : Type u, Σ _ : Finset J, J → ℝ
abbrev supportSignature := signature SupportSystem.{u} (fun p => Finset p.1)

def supportActual : Realization supportSignature.{u} :=
  realize supportSignature (fun _ p v => supportMaximum p.2.1 p.2.2 v) (fun e => nomatch e)

def supportBad : Realization supportSignature.{u} :=
  realize supportSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev supportArena : Arena where
  signature := supportSignature.{u}
  Law r := ∀ {J : Type u} (s : Finset J) (g : J → ℝ) (v : Finset J),
    let maximum := r.readout () ⟨J, s, g⟩ v
    (maximum = 0 ∧ ¬ ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v) ∨
      ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧ maximum = tau s k ∧
        0 < maximum ∧ ∀ r, IncompatibleRelation s g r → relationSupport s r = v → tau s r ≤ maximum

private theorem emptySupport (s : Finset One.{u}) (k : One.{u} → ℤ)
    (hk : IncompatibleRelation s zeroFrequency k) : relationSupport s k ≠ ∅ := by
  intro h
  obtain ⟨j, hj, _⟩ := (coordinate_loss_same_time _ _ k hk 0).2.2
  simp [h] at hj

private theorem supportDependence : ObservationalDependence supportSignature.{u} supportActual := by
  intro _
  refine ⟨⟨One.{u}, singleton, zeroFrequency⟩, ∅, singleton, ?_⟩
  change supportMaximum singleton.{u} zeroFrequency ∅ ≠
    supportMaximum singleton.{u} zeroFrequency singleton
  have h0 : supportMaximum singleton.{u} zeroFrequency ∅ = 0 := by
    rcases supportMaximum_zero_or_attained singleton.{u} zeroFrequency ∅ with h | ⟨k, hk, hs, _⟩
    · exact h.1
    · exact (emptySupport singleton k hk hs).elim
  rcases supportMaximum_zero_or_attained singleton.{u} zeroFrequency singleton with h | ⟨_, _, _, _, hp, _⟩
  · exact (h.2 ⟨unitRelation, singletonRelation, singletonSupport⟩).elim
  rw [h0]
  exact hp.ne

private theorem supportRejected : ¬ supportArena.{u}.Law supportBad := by
  intro h
  rcases h singleton.{u} zeroFrequency ∅ with h | ⟨k, hk, hs, _⟩
  · exact (by norm_num : ¬ (-1 : ℝ) = 0) h.1
  · exact emptySupport singleton k hk hs

def coefficientSource : Registration coefficientArena.{u} (type_of% @coordinate_loss_same_time.{u}) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@coordinate_loss_same_time.{u}, coefficientBad, coefficientRejected⟩
  sensitivity := sensitivity coefficientArena.{u}.Law coefficientActual coefficientBad coefficientRejected
  dependence := coefficientDependence

def coefficientAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coordinate_loss_same_time.{u}) (Realization coefficientSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.coefficientUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.coefficientSource
  realizationSource := none
  generated := false
  arena := .source ⟨coefficientArena.{u}⟩
  objectArena := .source ⟨coefficientArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficientArena.{u} ⟨coefficientSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ p k => tau p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def supportSource : Registration supportArena.{u} (type_of% @supportMaximum_zero_or_attained.{u}) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@supportMaximum_zero_or_attained.{u}, supportBad, supportRejected⟩
  sensitivity := sensitivity supportArena.{u}.Law supportActual supportBad supportRejected
  dependence := supportDependence

def supportAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@supportMaximum_zero_or_attained.{u}) (Realization supportSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.supportUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.supportSource
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena.{u}⟩
  objectArena := .source ⟨supportArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena.{u} ⟨supportSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ p v => supportMaximum p.2.1 p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def hittingSource : Registration hittingArena.{u} (type_of% @least_hitting_weight.{u}) where
  actual := thresholdActual
  bridge := Iff.rfl
  variation := ⟨@least_hitting_weight.{u}, thresholdNegative, hittingRejected⟩
  sensitivity := sensitivity hittingArena.{u}.Law thresholdActual thresholdNegative hittingRejected
  dependence := thresholdDependence

def hittingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@least_hitting_weight.{u}) (Realization thresholdSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.hittingUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.hittingSource
  realizationSource := none
  generated := false
  arena := .source ⟨hittingArena.{u}⟩
  objectArena := .source ⟨hittingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hittingArena.{u} ⟨hittingSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def partitionSource : Registration partitionArena.{u} (type_of% @breakpoint_partition.{u}) where
  actual := thresholdActual
  bridge := Iff.rfl
  variation := ⟨@breakpoint_partition.{u}, thresholdStep, partitionRejected⟩
  sensitivity := sensitivity partitionArena.{u}.Law thresholdActual thresholdStep partitionRejected
  dependence := thresholdDependence

def partitionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@breakpoint_partition.{u}) (Realization thresholdSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.partitionUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.partitionSource
  realizationSource := none
  generated := false
  arena := .source ⟨partitionArena.{u}⟩
  objectArena := .source ⟨partitionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source partitionArena.{u} ⟨partitionSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def stepIntegralSource : Registration stepIntegralArena.{u} (type_of% @finite_step_integral.{u}) where
  actual := thresholdActual
  bridge := Iff.rfl
  variation := ⟨@finite_step_integral.{u}, thresholdStep, stepIntegralRejected⟩
  sensitivity := sensitivity stepIntegralArena.{u}.Law thresholdActual thresholdStep stepIntegralRejected
  dependence := thresholdDependence

def stepIntegralAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_step_integral.{u}) (Realization thresholdSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.stepIntegralUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.stepIntegralSource
  realizationSource := none
  generated := false
  arena := .source ⟨stepIntegralArena.{u}⟩
  objectArena := .source ⟨stepIntegralArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stepIntegralArena.{u} ⟨stepIntegralSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def timeSource : Registration timeArena.{u} (type_of% @integrated_Q_same_time.{u}) where
  actual := timeActual
  bridge := Iff.rfl
  variation := ⟨@integrated_Q_same_time.{u}, timeBad, timeRejected⟩
  sensitivity := sensitivity timeArena.{u}.Law timeActual timeBad timeRejected
  dependence := timeDependence

def timeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrated_Q_same_time.{u}) (Realization timeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.timeUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.timeSource
  realizationSource := none
  generated := false
  arena := .source ⟨timeArena.{u}⟩
  objectArena := .source ⟨timeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeArena.{u} ⟨timeSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeSignature (fun _ p t => average p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def deficitSource : Registration deficitArena.{u} (type_of% @integrated_Q_le_deficit.{u}) where
  actual := deficitActual
  bridge := Iff.rfl
  variation := ⟨@integrated_Q_le_deficit.{u}, deficitBad, deficitRejected⟩
  sensitivity := sensitivity deficitArena.{u}.Law deficitActual deficitBad deficitRejected
  dependence := deficitDependence

def deficitAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrated_Q_le_deficit.{u}) (Realization deficitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.deficitUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.deficitSource
  realizationSource := none
  generated := false
  arena := .source ⟨deficitArena.{u}⟩
  objectArena := .source ⟨deficitArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deficitArena.{u} ⟨deficitSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitSignature (fun _ p T => deficit p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def partialLengthSource : Registration partialLengthArena.{u} (type_of% @partial_length_le_integral.{u}) where
  actual := thresholdActual
  bridge := Iff.rfl
  variation := ⟨@partial_length_le_integral.{u}, thresholdNegative, partialLengthRejected⟩
  sensitivity := sensitivity partialLengthArena.{u}.Law thresholdActual thresholdNegative partialLengthRejected
  dependence := thresholdDependence

def partialLengthAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@partial_length_le_integral.{u}) (Realization thresholdSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.partialLengthUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.partialLengthSource
  realizationSource := none
  generated := false
  arena := .source ⟨partialLengthArena.{u}⟩
  objectArena := .source ⟨partialLengthArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source partialLengthArena.{u} ⟨partialLengthSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def lengthSeriesSource : Registration lengthSeriesArena.{u} (type_of% @length_series_le_integral.{u}) where
  actual := thresholdActual
  bridge := Iff.rfl
  variation := ⟨@length_series_le_integral.{u}, thresholdNegative, lengthSeriesRejected⟩
  sensitivity := sensitivity lengthSeriesArena.{u}.Law thresholdActual thresholdNegative lengthSeriesRejected
  dependence := thresholdDependence

def lengthSeriesAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@length_series_le_integral.{u}) (Realization thresholdSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.lengthSeriesUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.lengthSeriesSource
  realizationSource := none
  generated := false
  arena := .source ⟨lengthSeriesArena.{u}⟩
  objectArena := .source ⟨lengthSeriesArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthSeriesArena.{u} ⟨lengthSeriesSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature (fun _ p x => @Q p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pairCostSource : Registration pairCostArena (type_of% @pair_exact_Q) where
  actual := pairActual
  bridge := Iff.rfl
  variation := ⟨@pair_exact_Q, pairRejected, pairCostRejected⟩
  sensitivity := sensitivity pairCostArena.Law pairActual pairRejected pairCostRejected
  dependence := pairDependence

def pairCostAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_exact_Q) (Realization PairSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.pairCostUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.pairCostSource
  realizationSource := none
  generated := false
  arena := .source ⟨pairCostArena⟩
  objectArena := .source ⟨pairCostArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairCostArena ⟨pairCostSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PairSignature (fun _ w x => Q pairIndices pairFrequency (fun _ => w) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pairStrictSource : Registration pairStrictArena (type_of% @pair_strict) where
  actual := pairActual
  bridge := Iff.rfl
  variation := ⟨@pair_strict, pairRejected, pairStrictRejected⟩
  sensitivity := sensitivity pairStrictArena.Law pairActual pairRejected pairStrictRejected
  dependence := pairDependence

def pairStrictAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_strict) (Realization PairSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.pairStrictUnit
  realizationName := `Reg.D5.S3.Fourier.ExactFourthRootGaps.pairStrictSource
  realizationSource := none
  generated := false
  arena := .source ⟨pairStrictArena⟩
  objectArena := .source ⟨pairStrictArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairStrictArena ⟨pairStrictSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PairSignature (fun _ w x => Q pairIndices pairFrequency (fun _ => w) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ExactFourthRootGaps
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.ExactFourthRootGaps
