/- GID: D5/S3/Weil/ZetaBridge/FiniteOrbitBurnolPacket
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteOrbitBurnolPacket
   mirror-E: none(waiver:finite-multiorbit-localization)
   anchors: []
   digest: Construct a common unit peak and an entire interpolation basis annihilating the same finite exceptional complement. -/

import D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
import D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation

/-!
# Simultaneous Burnol packet construction

The analytic localization data is constructed here, not assumed. A common
peak equals one on the finite union of target orbits. Closed-strip Fourier
Laplace decay produces one finite exceptional spectral ball outside which
both conjugate evaluations are at most one half. Reflection-compatible finite
interpolation then constructs every basis killer on that same ball.

Sign separation in the existing orbit-frame type is also proved to imply
pairwise disjointness of the actual four-point zero orbits. Consequently no
extra disjointness or zero-tail hypothesis is hidden in the packet constructor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped BigOperators ComplexConjugate

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite union of all selected four-point zero orbits. -/
def frameTargetIndices (F : FiniteEvenWeilOrbitFrame Z ι) : Finset ℕ :=
  Finset.univ.biUnion (fun i => zeroOrbit Z (F.index i))

/-- Every individual target orbit is contained in the selected union. -/
theorem orbit_subset_frameTargetIndices
    (F : FiniteEvenWeilOrbitFrame Z ι) (i : ι) :
    zeroOrbit Z (F.index i) ⊆ frameTargetIndices F := by
  intro n hn
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hn⟩

/-- The node/sign-separation certificate already stored by a frame implies
pairwise disjointness of the corresponding actual zero orbits. -/
theorem frame_orbits_pairwise_disjoint
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) (hij : i ≠ j) :
    Disjoint (zeroOrbit Z (F.index i)) (zeroOrbit Z (F.index j)) := by
  classical
  have hnode (u v : Sum ι ι) (h : u ≠ v) :
      (F.nodeEquiv u).1 ≠ (F.nodeEquiv v).1 := by
    intro heq
    exact h (F.nodeEquiv.injective (Subtype.ext heq))
  have hnegative (u v : Sum ι ι) (h : u ≠ v) :
      (F.nodeEquiv u).1 ≠ -(F.nodeEquiv v).1 :=
    F.signSeparated (F.nodeEquiv u).property (F.nodeEquiv v).property
      (hnode u v h)
  have hpp : Z.gamma (F.index i) ≠ Z.gamma (F.index j) := by
    simpa only [F.plusNode] using hnode (.inl i) (.inl j) (by simp [hij])
  have hpm : Z.gamma (F.index i) ≠ conj (Z.gamma (F.index j)) := by
    simpa only [F.plusNode, F.minusNode] using hnode (.inl i) (.inr j) (by simp)
  have hmp : conj (Z.gamma (F.index i)) ≠ Z.gamma (F.index j) := by
    simpa only [F.plusNode, F.minusNode] using hnode (.inr i) (.inl j) (by simp)
  have hmm : conj (Z.gamma (F.index i)) ≠ conj (Z.gamma (F.index j)) := by
    simpa only [F.minusNode] using hnode (.inr i) (.inr j) (by simp [hij])
  have hnpp : Z.gamma (F.index i) ≠ -Z.gamma (F.index j) := by
    simpa only [F.plusNode] using hnegative (.inl i) (.inl j) (by simp [hij])
  have hnpm : Z.gamma (F.index i) ≠ -conj (Z.gamma (F.index j)) := by
    simpa only [F.plusNode, F.minusNode] using hnegative (.inl i) (.inr j) (by simp)
  have hnmp : conj (Z.gamma (F.index i)) ≠ -Z.gamma (F.index j) := by
    simpa only [F.plusNode, F.minusNode] using hnegative (.inr i) (.inl j) (by simp)
  have hnmm : conj (Z.gamma (F.index i)) ≠ -conj (Z.gamma (F.index j)) := by
    simpa only [F.minusNode] using hnegative (.inr i) (.inr j) (by simp [hij])
  have hfreq (k n : ℕ) (hn : n ∈ zeroOrbit Z k) :
      Z.gamma n = Z.gamma k ∨ Z.gamma n = -Z.gamma k ∨
        Z.gamma n = -conj (Z.gamma k) ∨ Z.gamma n = conj (Z.gamma k) := by
    simp only [zeroOrbit, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> simp
  apply Finset.disjoint_left.mpr
  intro n hi hj
  rcases hfreq (F.index i) n hi with hi | hi | hi | hi <;>
    rcases hfreq (F.index j) n hj with hj | hj | hj | hj
  all_goals
    have heq := hi.symm.trans hj
    simp only [neg_inj, neg_eq_iff_eq_neg] at heq
    first
    | exact hpp heq
    | exact hpm heq
    | exact hmp heq
    | exact hmm heq
    | exact hnpp heq
    | exact hnpm heq
    | exact hnmp heq
    | exact hnmm heq

/-- Reflection-compatible signed data on one orbit: plus on its reflection
pair, minus on the conjugate reflection pair, and zero elsewhere. -/
def orbitSignedAssignment (Z : ZeroData) (n j : ℕ) : ℂ :=
  if reflectionRep Z j = reflectionRep Z n then 1
  else if reflectionRep Z j = reflectionRep Z (Z.conjugation n) then -1
  else 0

theorem orbitSignedAssignment_reflection (Z : ZeroData) (n j : ℕ) :
    orbitSignedAssignment Z n (Z.reflection j) = orbitSignedAssignment Z n j := by
  simp only [orbitSignedAssignment, reflectionRep_reflection]

/-- The two sign representatives of a nonreal off-line orbit are distinct. -/
theorem frame_reflection_representatives_ne
    (F : FiniteEvenWeilOrbitFrame Z ι) (i : ι) :
    reflectionRep Z (F.index i) ≠
      reflectionRep Z (Z.conjugation (F.index i)) := by
  intro heq
  rcases reflectionRep_eq_or Z (F.index i)
      (Z.conjugation (F.index i)) heq with h | h
  · exact F.conjugateMove i h.symm
  · have hfixed : Z.conjugation (Z.reflection (F.index i)) = F.index i := by
      calc
        Z.conjugation (Z.reflection (F.index i)) =
            Z.reflection (Z.conjugation (F.index i)) :=
          (zero_symmetries_commute Z (F.index i)).symm
        _ = F.index i := h.symm
    exact F.offLine i ((mirror_index_fixed_iff_critical Z (F.index i)).1 hfixed)

/-- Signed orbit data is zero away from that actual orbit. -/
theorem orbitSignedAssignment_zero_of_not_mem (Z : ZeroData) (n j : ℕ)
    (hj : j ∉ zeroOrbit Z n) : orbitSignedAssignment Z n j = 0 := by
  have hfirst : reflectionRep Z j ≠ reflectionRep Z n := by
    intro h
    rcases reflectionRep_eq_or Z j n h with h | h
    · exact hj (by simp [zeroOrbit, h])
    · exact hj (by simp [zeroOrbit, h])
  have hsecond : reflectionRep Z j ≠ reflectionRep Z (Z.conjugation n) := by
    intro h
    rcases reflectionRep_eq_or Z j (Z.conjugation n) h with h | h
    · exact hj (by simp [zeroOrbit, h])
    · have heq : j = Z.conjugation (Z.reflection n) :=
        h.trans (zero_symmetries_commute Z n)
      exact hj (by simp [zeroOrbit, heq])
  simp [orbitSignedAssignment, hfirst, hsecond]

/-- The signed orbit assignments are simultaneous Kronecker data on the frame. -/
theorem orbitSignedAssignment_on_frame
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    orbitSignedAssignment Z (F.index i) (F.index j) = frameDelta i j ∧
      orbitSignedAssignment Z (F.index i) (Z.conjugation (F.index j)) =
        -frameDelta i j := by
  classical
  by_cases hij : j = i
  · subst j
    have hne := (frame_reflection_representatives_ne F i).symm
    simp [orbitSignedAssignment, frameDelta, hne]
  · have hdis := frame_orbits_pairwise_disjoint F i j hij.symm
    have hnot : F.index j ∉ zeroOrbit Z (F.index i) := by
      intro h
      exact Finset.disjoint_left.mp hdis h (by simp [zeroOrbit])
    have hcnot : Z.conjugation (F.index j) ∉ zeroOrbit Z (F.index i) := by
      intro h
      exact Finset.disjoint_left.mp hdis h (by simp [zeroOrbit])
    rw [orbitSignedAssignment_zero_of_not_mem Z _ _ hnot,
      orbitSignedAssignment_zero_of_not_mem Z _ _ hcnot]
    simp [frameDelta, hij]

/-- A compact smooth test has a single finite exceptional spectral ball
outside which both conjugate transforms are at most one half. The ball can
be required to contain any specified finite index set. -/
theorem exists_common_exceptional_ball (Z : ZeroData)
    (b : WeilTestFunction) (O : Finset ℕ) :
    ∃ E : Finset ℕ, O ⊆ E ∧
      ∀ j ∉ E,
        ‖fourierLaplace b (Z.gamma j)‖ ≤ (1 / 2 : ℝ) ∧
        ‖fourierLaplace b (conj (Z.gamma j))‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hdecay⟩ :=
    fourierLaplace_decay_closedStrip b (1 / 2) (by norm_num)
  let R : ℝ := max (2 * C + 1) (∑ j ∈ O, ‖Z.gamma j‖)
  refine ⟨Z.symmetricIndices R, ?_, ?_⟩
  · intro j hj
    rw [Z.mem_symmetricIndices]
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (Z.gamma k)) hj).trans
      (le_max_right _ _)
  · intro j hj
    have him : |(Z.gamma j).im| ≤ (1 / 2 : ℝ) := by
      rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
      exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial j).2).le
    have hnot : ¬ ‖Z.gamma j‖ ≤ R := by
      simpa only [Z.mem_symmetricIndices] using hj
    have hlarge : 2 * C + 1 < ‖Z.gamma j‖ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hnot)
    have hnormsq : ‖Z.gamma j‖ ^ 2 =
        (Z.gamma j).re ^ 2 + (Z.gamma j).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have himsq : (Z.gamma j).im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have h : |(Z.gamma j).im| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        nlinarith [abs_nonneg (Z.gamma j).im]
      simpa only [sq_abs] using h
    have hsq : (2 * C + 1) ^ 2 < ‖Z.gamma j‖ ^ 2 := by
      nlinarith [norm_nonneg (Z.gamma j)]
    have hden : 2 * C ≤ 1 + (Z.gamma j).re ^ 2 := by
      nlinarith [sq_nonneg C]
    have hratio : C / (1 + (Z.gamma j).re ^ 2) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + (Z.gamma j).re ^ 2)).2
      nlinarith
    refine ⟨(hdecay _ him).trans hratio, ?_⟩
    have himc : |(conj (Z.gamma j)).im| ≤ (1 / 2 : ℝ) := by simpa using him
    exact (hdecay _ himc).trans (by simpa using hratio)

/-- Constructed data for a single common peak and simultaneous killers. -/
structure OrbitBurnolPacket (F : FiniteEvenWeilOrbitFrame Z ι) where
  peak : WeilTestFunction
  killer : ι → WeilTestFunction
  exceptional : Finset ℕ
  target_subset : frameTargetIndices F ⊆ exceptional
  peak_values : ∀ i,
    fourierLaplace peak (Z.gamma (F.index i)) = 1 ∧
      fourierLaplace peak (conj (Z.gamma (F.index i))) = 1
  killer_values : ∀ i j,
    fourierLaplace (killer i) (Z.gamma (F.index j)) = frameDelta i j ∧
      fourierLaplace (killer i) (conj (Z.gamma (F.index j))) = -frameDelta i j
  kills_exception : ∀ i j, j ∈ exceptional → j ∉ frameTargetIndices F →
    fourierLaplace (killer i) (Z.gamma j) = 0
  peak_tail : ∀ j ∉ exceptional,
    ‖fourierLaplace peak (Z.gamma j)‖ ≤ (1 / 2 : ℝ) ∧
      ‖fourierLaplace peak (conj (Z.gamma j))‖ ≤ (1 / 2 : ℝ)

/-- Every separated finite orbit frame admits simultaneous localization data.
All analytic estimates in the packet follow from the existing closed-strip
decay theorem and actual finite interpolation. -/
theorem exists_orbitBurnolPacket (F : FiniteEvenWeilOrbitFrame Z ι) :
    Nonempty (OrbitBurnolPacket F) := by
  classical
  obtain ⟨b, hb⟩ := exists_even_weil_finite_unit_peak Z (frameTargetIndices F)
  obtain ⟨E, hOE, htail⟩ := exists_common_exceptional_ball Z b (frameTargetIndices F)
  have hkexists (i : ι) : ∃ k : WeilTestFunction, ∀ j ∈ E,
      fourierLaplace k (Z.gamma j) = orbitSignedAssignment Z (F.index i) j :=
    even_weil_interpolation_on_finite_indices Z E
      (orbitSignedAssignment Z (F.index i))
      (orbitSignedAssignment_reflection Z (F.index i))
  choose k hk using hkexists
  have hn (i : ι) : F.index i ∈ frameTargetIndices F :=
    orbit_subset_frameTargetIndices F i (by simp [zeroOrbit])
  have hcn (i : ι) : Z.conjugation (F.index i) ∈ frameTargetIndices F :=
    orbit_subset_frameTargetIndices F i (by simp [zeroOrbit])
  have hconjEval (g : WeilTestFunction) (j : ℕ) :
      fourierLaplace g (conj (Z.gamma j)) =
        fourierLaplace g (Z.gamma (Z.conjugation j)) := by
    rw [Z.gamma_conjugation, fourierLaplace_neg]
  refine ⟨{ peak := b, killer := k, exceptional := E,
    target_subset := hOE, peak_values := ?_, killer_values := ?_,
    kills_exception := ?_, peak_tail := htail }⟩
  · intro i
    exact ⟨hb _ (hn i), (hconjEval b _).trans (hb _ (hcn i))⟩
  · intro i j
    have hvalues := orbitSignedAssignment_on_frame F i j
    exact ⟨(hk i _ (hOE (hn j))).trans hvalues.1,
      (hconjEval (k i) _).trans ((hk i _ (hOE (hcn j))).trans hvalues.2)⟩
  · intro i j hj hjO
    rw [hk i j hj]
    apply orbitSignedAssignment_zero_of_not_mem
    exact fun h => hjO (orbit_subset_frameTargetIndices F i h)

/-- A fixed packet selected from the proved existence theorem. -/
def chosenOrbitBurnolPacket (F : FiniteEvenWeilOrbitFrame Z ι) :
    OrbitBurnolPacket F := Classical.choice (exists_orbitBurnolPacket F)

#print axioms frame_orbits_pairwise_disjoint
#print axioms exists_common_exceptional_ball
#print axioms exists_orbitBurnolPacket

end D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
