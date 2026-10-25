import CFMPActualPositivePrimitive279Transient
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.DiscreteSubset

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPActualExtendedAngle268Transient
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Genuine Sector positive_classification)
open private delta interior_of_negative sector_exists from
  D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPActualAnalyticDiscriminant280Transient

/-- The original classification discriminant, with its original cosh inputs. -/
def discriminant (a : Lengths) : ℝ := delta (fun q => Real.cosh (a q))

def lineDiscriminant (a b : Lengths) (t : ℝ) : ℝ :=
  discriminant (AffineMap.lineMap a b t)

theorem genuine_iff_discriminant_neg (a : Lengths) (ha : a ∈ positiveLengths) :
    genuine a ↔ discriminant a < 0 := by
  have hcosh (q : Fin 6) : 1 < Real.cosh (a q) := Real.one_lt_cosh.mpr (ha q).ne'
  constructor
  · intro hg
    by_contra hd
    obtain ⟨k,hk⟩ := sector_exists (fun q => Real.cosh (a q)) hcosh (le_of_not_gt hd)
    exact (not_le_of_gt (hg.2 (k.castAdd 3)).1) hk
  · intro hd
    exact ⟨ha,interior_of_negative (fun q => Real.cosh (a q)) hcosh hd⟩

theorem lineDiscriminant_analytic (a b : Lengths) :
    AnalyticOnNhd ℝ (lineDiscriminant a b) univ := by
  intro t _
  change AnalyticAt ℝ
    (fun s : ℝ => delta (fun q => Real.cosh (s * (b q - a q) + a q))) t
  dsimp only [delta]
  fun_prop

/-- A line restriction is identically zero, or has only finitely many zeros
on each closed bounded parameter interval. This includes tangencies. -/
theorem lineDiscriminant_zero_or_finite (a b : Lengths) (l r : ℝ) :
    (∀ t : ℝ, lineDiscriminant a b t = 0) ∨
      {t : ℝ | t ∈ Icc l r ∧ lineDiscriminant a b t = 0}.Finite := by
  rcases (lineDiscriminant_analytic a b).eqOn_zero_or_eventually_ne_zero_of_preconnected
      isPreconnected_univ with hzero | hnonzero
  · exact Or.inl (fun t => hzero (mem_univ t))
  · right
    have hgood : {t : ℝ | lineDiscriminant a b t ≠ 0} ∈ codiscreteWithin (Icc l r) :=
      hnonzero.filter_mono (codiscreteWithin_mono (subset_univ (Icc l r)))
    have hfinite := (isCompact_Icc : IsCompact (Icc l r)).finite_sdiff_of_mem_codiscreteWithin hgood
    convert hfinite using 1
    ext t
    simp

theorem zero_discriminant_has_flat_covector (a : Lengths) (ha : a ∈ positiveLengths)
    (hd : discriminant a = 0) :
    ∃ k : Fin 3, sourceDifferential a = flatDifferential k := by
  have hng : ¬ Genuine (fun q => Real.cosh (a q)) := by
    intro hg
    have hneg := (genuine_iff_discriminant_neg a ha).mp ⟨ha,hg⟩
    rw [hd] at hneg
    exact (lt_irrefl 0) hneg
  obtain ⟨k,hk,_⟩ :=
    (positive_classification (fun q => Real.cosh (a q))
      (fun q => Real.one_lt_cosh.mpr (ha q).ne')).2.1.resolve_left hng
  exact ⟨k,sourceDifferential_eq_flat a ha k hk⟩

end CFMPActualAnalyticDiscriminant280Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualAnalyticDiscriminant280Transient.genuine_iff_discriminant_neg,
      ``CFMPActualAnalyticDiscriminant280Transient.lineDiscriminant_zero_or_finite,
      ``CFMPActualAnalyticDiscriminant280Transient.zero_discriminant_has_flat_covector] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP280 original analytic discriminant absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP280 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP280 CHECKED {name} axioms={axioms}"
