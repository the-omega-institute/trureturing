/- GID: D5/S3/Midline/Cayley/FiniteMirrorKreinIndex
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/FiniteMirrorKreinIndex
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Count one strictly negative odd coordinate per nonfixed mirror pair and analytic multiplicity in every finite zero window. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
import Mathlib.Tactic

/-!
# Finite mirror Krein index

A finite symmetric zero window is stable under the same-height mirror.  Every
nonfixed mirror orbit has two indices.  Choosing the smaller index selects one
representative, and analytic multiplicity supplies that many independent odd
coordinates.  The negative quadratic form on this finite coordinate space is
strictly negative away from zero.

The resulting finite index vanishes exactly when every zero in the window lies
on the critical line.  The construction is combinatorial and does not depend
on the choice of a height ordering for the global `ZeroData` presentation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.FiniteMirrorKreinIndex

open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
open scoped BigOperators

/-- The canonical representative of a two-point mirror orbit. -/
def mirrorRepresentative (Z : ZeroData) (n : ℕ) : ℕ :=
  min n (mirrorIndex Z n)

/-- Mirror transport preserves every symmetric spectral-radius window. -/
@[simp]
theorem mirrorIndex_mem_symmetricIndices (Z : ZeroData) {T : ℝ} {n : ℕ} :
    mirrorIndex Z n ∈ Z.symmetricIndices T ↔ n ∈ Z.symmetricIndices T := by
  change Z.conjugation (Z.reflection n) ∈ Z.symmetricIndices T ↔ _
  rw [Z.conjugation_mem_symmetricIndices,
    Z.reflection_mem_symmetricIndices]

/-- The canonical representative is constant on a mirror orbit. -/
@[simp]
theorem mirrorRepresentative_mirror (Z : ZeroData) (n : ℕ) :
    mirrorRepresentative Z (mirrorIndex Z n) = mirrorRepresentative Z n := by
  simp [mirrorRepresentative, mirrorIndex_involutive, Nat.min_comm]

/-- One representative from every nonfixed mirror pair in the finite window. -/
noncomputable def mirrorPairRepresentatives (Z : ZeroData) (T : ℝ) : Finset ℕ :=
  (Z.symmetricIndices T).filter fun n => n < mirrorIndex Z n

/-- Every nonfixed index in the window determines a selected representative. -/
theorem mirrorRepresentative_mem_pairRepresentatives (Z : ZeroData)
    {T : ℝ} {n : ℕ} (hn : n ∈ Z.symmetricIndices T)
    (hmove : mirrorIndex Z n ≠ n) :
    mirrorRepresentative Z n ∈ mirrorPairRepresentatives Z T := by
  by_cases hlt : n < mirrorIndex Z n
  · have hle : n ≤ mirrorIndex Z n := hlt.le
    simp [mirrorRepresentative, mirrorPairRepresentatives,
      Nat.min_eq_left hle, hn, hlt]
  · have hge : mirrorIndex Z n ≤ n := Nat.le_of_not_gt hlt
    have hstrict : mirrorIndex Z n < n := lt_of_le_of_ne hge hmove
    have hmem : mirrorIndex Z n ∈ Z.symmetricIndices T :=
      (mirrorIndex_mem_symmetricIndices Z).2 hn
    simp [mirrorRepresentative, mirrorPairRepresentatives,
      Nat.min_eq_right hge, hmem, hstrict, mirrorIndex_involutive]

/-- A selected representative is the minimum of its own mirror pair. -/
theorem mirrorRepresentative_eq_self_of_mem (Z : ZeroData) {T : ℝ} {n : ℕ}
    (hn : n ∈ mirrorPairRepresentatives Z T) :
    mirrorRepresentative Z n = n := by
  have hlt := (Finset.mem_filter.mp hn).2
  exact Nat.min_eq_left hlt.le

/-- There are no selected pairs exactly when every index in the finite window
is mirror fixed. -/
theorem mirrorPairRepresentatives_eq_empty_iff (Z : ZeroData) (T : ℝ) :
    mirrorPairRepresentatives Z T = ∅ ↔
      ∀ n ∈ Z.symmetricIndices T, mirrorIndex Z n = n := by
  constructor
  · intro hempty n hn
    by_contra hmove
    have hmem := mirrorRepresentative_mem_pairRepresentatives Z hn hmove
    rw [hempty] at hmem
    simp at hmem
  · intro hfixed
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hmirror := hfixed n hn'.1
    simpa [hmirror] using hn'.2

/-- The finite mirror Krein index, with one odd coordinate for each analytic
multiplicity copy of each nonfixed mirror pair. -/
noncomputable def finiteMirrorKreinIndex (Z : ZeroData) (T : ℝ) : ℕ :=
  ∑ n ∈ mirrorPairRepresentatives Z T, Z.multiplicity n

/-- The finite index is zero exactly when there is no nonfixed mirror pair. -/
theorem finiteMirrorKreinIndex_eq_zero_iff_representatives_empty
    (Z : ZeroData) (T : ℝ) :
    finiteMirrorKreinIndex Z T = 0 ↔ mirrorPairRepresentatives Z T = ∅ := by
  constructor
  · intro hzero
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    have hle : Z.multiplicity n ≤ finiteMirrorKreinIndex Z T := by
      unfold finiteMirrorKreinIndex
      exact Finset.single_le_sum
        (fun i _ => Nat.zero_le (Z.multiplicity i)) hn
    rw [hzero] at hle
    omega
  · intro hempty
    simp [finiteMirrorKreinIndex, hempty]

/-- The finite index vanishes exactly when the mirror acts trivially on the
whole window. -/
theorem finiteMirrorKreinIndex_eq_zero_iff_all_fixed
    (Z : ZeroData) (T : ℝ) :
    finiteMirrorKreinIndex Z T = 0 ↔
      ∀ n ∈ Z.symmetricIndices T, mirrorIndex Z n = n := by
  rw [finiteMirrorKreinIndex_eq_zero_iff_representatives_empty,
    mirrorPairRepresentatives_eq_empty_iff]

/-- Vanishing finite mirror index is exactly critical-line location throughout
the finite window. -/
theorem finite_mirror_krein_index_zero_iff_critical
    (Z : ZeroData) (T : ℝ) :
    finiteMirrorKreinIndex Z T = 0 ↔
      ∀ n ∈ Z.symmetricIndices T,
        (Z.zero n).re = criticalAbscissa := by
  rw [finiteMirrorKreinIndex_eq_zero_iff_all_fixed]
  exact forall_congr' fun n => forall_congr' fun _ =>
    mirrorIndex_fixed_iff_critical Z n

/-- The finite index is positive exactly when the window contains an off-line
zero. -/
theorem finiteMirrorKreinIndex_pos_iff_exists_offLine
    (Z : ZeroData) (T : ℝ) :
    0 < finiteMirrorKreinIndex Z T ↔
      ∃ n ∈ Z.symmetricIndices T,
        (Z.zero n).re ≠ criticalAbscissa := by
  constructor
  · intro hpos
    by_contra hnone
    have hall : ∀ n ∈ Z.symmetricIndices T,
        (Z.zero n).re = criticalAbscissa := by
      intro n hn
      by_contra hoff
      exact hnone ⟨n, hn, hoff⟩
    have hzero := (finite_mirror_krein_index_zero_iff_critical Z T).2 hall
    omega
  · rintro ⟨n, hn, hoff⟩
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hoff ((finite_mirror_krein_index_zero_iff_critical Z T).1 hzero n hn)

/-- The finite set of selected mirror-pair representatives as a type. -/
abbrev MirrorPairRepresentative (Z : ZeroData) (T : ℝ) :=
  {n : ℕ // n ∈ mirrorPairRepresentatives Z T}

/-- One odd coordinate for every selected mirror pair and every analytic
multiplicity copy. -/
abbrev MirrorOddCoordinate (Z : ZeroData) (T : ℝ) :=
  Sigma fun n : MirrorPairRepresentative Z T => Fin (Z.multiplicity n.1)

/-- The cardinality of the finite odd-coordinate sector is exactly the finite
mirror Krein index. -/
theorem mirrorOddCoordinate_card (Z : ZeroData) (T : ℝ) :
    Fintype.card (MirrorOddCoordinate Z T) = finiteMirrorKreinIndex Z T := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ n : {n : ℕ // n ∈ mirrorPairRepresentatives Z T},
      Z.multiplicity n.1) =
    ∑ n ∈ mirrorPairRepresentatives Z T, Z.multiplicity n
  rw [← Finset.sum_subtype
    (p := fun n : ℕ => n ∈ mirrorPairRepresentatives Z T)
    (mirrorPairRepresentatives Z T) (by simp)]

/-- The standard negative form on the finite mirror-odd coordinate sector. -/
def finiteMirrorOddQuadratic (Z : ZeroData) (T : ℝ)
    (v : MirrorOddCoordinate Z T → Complex) : ℝ :=
  -∑ i, Complex.normSq (v i)

/-- The finite mirror-odd form is nonpositive. -/
theorem finiteMirrorOddQuadratic_nonpos (Z : ZeroData) (T : ℝ)
    (v : MirrorOddCoordinate Z T → Complex) :
    finiteMirrorOddQuadratic Z T v ≤ 0 := by
  unfold finiteMirrorOddQuadratic
  exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i))

/-- The finite mirror-odd form is strictly negative away from zero. -/
theorem finiteMirrorOddQuadratic_strictly_negative (Z : ZeroData) (T : ℝ)
    (v : MirrorOddCoordinate Z T → Complex) (hv : v ≠ 0) :
    finiteMirrorOddQuadratic Z T v < 0 := by
  have hexists : ∃ i, v i ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hv
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hexists
  have hsum : 0 < ∑ j, Complex.normSq (v j) := by
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (v j))
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  simpa [finiteMirrorOddQuadratic] using neg_lt_zero.mpr hsum

/-- Complete finite-window certificate: exact odd-sector dimension, strict
negative definiteness, and the critical-line vanishing criterion. -/
theorem finite_mirror_krein_index_spec (Z : ZeroData) (T : ℝ) :
    Fintype.card (MirrorOddCoordinate Z T) = finiteMirrorKreinIndex Z T ∧
      (∀ v : MirrorOddCoordinate Z T → Complex,
        v ≠ 0 → finiteMirrorOddQuadratic Z T v < 0) ∧
      (finiteMirrorKreinIndex Z T = 0 ↔
        ∀ n ∈ Z.symmetricIndices T,
          (Z.zero n).re = criticalAbscissa) := by
  exact ⟨mirrorOddCoordinate_card Z T,
    finiteMirrorOddQuadratic_strictly_negative Z T,
    finite_mirror_krein_index_zero_iff_critical Z T⟩

/-- The finite Krein index of the parameter-free zeta-zero presentation. -/
noncomputable def zetaFiniteMirrorKreinIndex (T : ℝ) : ℕ :=
  finiteMirrorKreinIndex zetaZeroData T

/-- The canonical zeta finite index vanishes exactly when every zero in the
window is critical. -/
theorem zetaFiniteMirrorKreinIndex_zero_iff_critical (T : ℝ) :
    zetaFiniteMirrorKreinIndex T = 0 ↔
      ∀ n ∈ zetaZeroData.symmetricIndices T,
        (zetaZeroData.zero n).re = criticalAbscissa := by
  exact finite_mirror_krein_index_zero_iff_critical zetaZeroData T

#print axioms mirrorPairRepresentatives_eq_empty_iff
#print axioms finite_mirror_krein_index_zero_iff_critical
#print axioms mirrorOddCoordinate_card
#print axioms finiteMirrorOddQuadratic_strictly_negative
#print axioms finite_mirror_krein_index_spec

end D5.S3.Midline.Cayley.FiniteMirrorKreinIndex
