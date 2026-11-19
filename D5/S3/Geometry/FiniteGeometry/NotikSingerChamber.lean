/- GID: D5/S3/Geometry/FiniteGeometry/NotikSingerChamber
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/NotikSingerChamber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cutting a cyclic perfect difference set at a largest gap gives chamber uniqueness. -/

module

public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Notik's Singer ruler conjecture

Esther Notik, *Golomb rulers with real marks: the real and integer optima agree
up to ten marks*, arXiv:2611.22656v1, §7.

Cut a cyclic perfect difference set at a largest gap of size `G`. The ordinary
distances contain every positive integer below `G`. In the real chamber these
distances form a chain of unit separations below each kept adjacent gap.
-/

set_option autoImplicit false

@[expose] public section

namespace D5.S3.Geometry.FiniteGeometry.NotikSingerChamber

variable {m : ℕ}

/-- Each nonzero residue has exactly one ordered pair of distinct marks.
The pair `(i, j)` represents the signed difference `x j - x i`. -/
def CyclicPerfectDifference (x : Fin (m + 1) → ℕ) (N : ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → d < N →
    ∃! p : Fin (m + 1) × Fin (m + 1),
      p.1 ≠ p.2 ∧ Int.ModEq (N : ℤ) ((x p.2 : ℤ) - (x p.1 : ℤ)) (d : ℤ)

/-- The normalized real chamber. Each labelled distance is at least one, and
every strictly ordered pair of reference distances is separated by at least one. -/
def Chamber (x : Fin (m + 1) → ℕ) (y : Fin (m + 1) → ℝ) : Prop :=
  y 0 = 0 ∧
    (∀ i j : Fin (m + 1), i < j → 1 ≤ y j - y i) ∧
    (∀ i j k l : Fin (m + 1), i < j → k < l → x j - x i < x l - x k →
      (y j - y i) + 1 ≤ y l - y k)

/-- Positive ordinary distances inherit uniqueness from the cyclic residues. -/
private theorem distance_unique {x : Fin (m + 1) → ℕ} (hx : StrictMono x)
    {G : ℕ} (hG : 0 < G) (hperfect : CyclicPerfectDifference x (x (Fin.last m) + G))
    {i j k l : Fin (m + 1)} (hij : i < j) (hkl : k < l)
    (heq : x j - x i = x l - x k) : (i, j) = (k, l) := by
  have hpos := Nat.sub_pos_of_lt (hx hij)
  have hj := hx.monotone (Fin.le_last j)
  have hlt : x j - x i < x (Fin.last m) + G := by omega
  have hi : (x j : ℤ) - (x i : ℤ) = ((x j - x i : ℕ) : ℤ) :=
    (Nat.cast_sub (hx.monotone hij.le)).symm
  have hk : (x l : ℤ) - (x k : ℤ) = ((x j - x i : ℕ) : ℤ) := by
    rw [heq]
    exact (Nat.cast_sub (hx.monotone hkl.le)).symm
  apply (hperfect _ hpos hlt).unique
  · exact ⟨hij.ne, by change Int.ModEq _ ((x j : ℤ) - (x i : ℤ)) _; rw [hi]⟩
  · exact ⟨hkl.ne, by change Int.ModEq _ ((x l : ℤ) - (x k : ℤ)) _; rw [hk]⟩

/-- A residue below the cut gap cannot be represented by a wrapped difference. -/
private theorem exists_distance_below_cut {x : Fin (m + 1) → ℕ} (hx : StrictMono x)
    {G : ℕ} (hperfect : CyclicPerfectDifference x (x (Fin.last m) + G))
    {d : ℕ} (hd : 0 < d) (hdG : d < G) :
    ∃ i j : Fin (m + 1), i < j ∧ x j - x i = d := by
  let N := x (Fin.last m) + G
  have hdN : d < N := by
    dsimp [N]
    omega
  obtain ⟨⟨i, j⟩, ⟨hne, hmod⟩, _⟩ := hperfect d hd hdN
  change i ≠ j at hne
  have hi := hx.monotone (Fin.le_last i)
  have hj := hx.monotone (Fin.le_last j)
  change ((x j : ℤ) - (x i : ℤ)) % (N : ℤ) = (d : ℤ) % (N : ℤ) at hmod
  have hdmod : (d : ℤ) % (N : ℤ) = (d : ℤ) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [hdmod] at hmod
  have hN : (N : ℤ) = (x (Fin.last m) : ℤ) + (G : ℤ) := by simp [N]
  rcases lt_or_gt_of_ne hne with hij | hji
  · have horder : x i < x j := hx hij
    have hordinary :
        ((x j : ℤ) - (x i : ℤ)) % (N : ℤ) = (x j : ℤ) - (x i : ℤ) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hordinary] at hmod
    exact ⟨i, j, hij, by omega⟩
  · have horder : x j < x i := hx hji
    have hwrapped :
        ((x j : ℤ) - (x i : ℤ)) % (N : ℤ) = (x j : ℤ) - (x i : ℤ) + (N : ℤ) := by
      calc
        _ = ((x j : ℤ) - (x i : ℤ) + (N : ℤ)) % (N : ℤ) := (Int.add_emod_right _ _).symm
        _ = _ := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hwrapped] at hmod
    omega

/-- Casting positive ordered integer distances into the reals preserves feasibility. -/
private theorem reference_mem_chamber {x : Fin (m + 1) → ℕ}
    (hzero : x 0 = 0) (hx : StrictMono x) : Chamber x (fun i => (x i : ℝ)) := by
  have cast_distance (i j : Fin (m + 1)) (hij : i < j) :
      ((x j - x i : ℕ) : ℝ) = (x j : ℝ) - (x i : ℝ) :=
    Nat.cast_sub (hx.monotone hij.le)
  refine ⟨by simp [hzero], ?_, ?_⟩
  · intro i j hij
    rw [← cast_distance i j hij]
    exact_mod_cast (Nat.sub_pos_of_lt (hx hij) : 1 ≤ x j - x i)
  · intro i j k l hij hkl hlt
    rw [← cast_distance i j hij, ← cast_distance k l hkl]
    exact_mod_cast (Nat.succ_le_of_lt hlt)

/-- For each reference distance at most `G`, the smaller consecutive integer
distances force the same lower bound in the chamber. -/
private theorem chamber_distance_ge {x : Fin (m + 1) → ℕ} (hx : StrictMono x)
    {G : ℕ} (hperfect : CyclicPerfectDifference x (x (Fin.last m) + G))
    {y : Fin (m + 1) → ℝ} (hy : Chamber x y) :
    ∀ d : ℕ, d ≤ G → ∀ i j : Fin (m + 1), i < j →
      x j - x i = d → (d : ℝ) ≤ y j - y i := by
  obtain ⟨_, hmin, hseparation⟩ := hy
  intro d
  induction d with
  | zero =>
    intro _ i j hij hd
    have := Nat.sub_pos_of_lt (hx hij)
    omega
  | succ d ih =>
    intro hdG i j hij hdij
    by_cases hd : d = 0
    · subst d
      simpa using hmin i j hij
    · obtain ⟨k, l, hkl, hdkl⟩ := exists_distance_below_cut hx hperfect
        (show 0 < d by omega) (show d < G by omega)
      have hprevious := ih (by omega) k l hkl hdkl
      have hstep := hseparation k l i j hkl hij (by rw [hdkl, hdij]; omega)
      rw [Nat.cast_succ]
      linarith

/-- A cyclic perfect difference set cut at a largest gap has distinct ordinary
distances and gives the unique point of minimum length in its real chamber. -/
theorem result {x : Fin (m + 1) → ℕ} {G : ℕ}
    (_hm : 0 < m) (hzero : x 0 = 0) (hx : StrictMono x) (hG : 0 < G)
    (hgap : ∀ i : Fin m, x i.succ - x i.castSucc ≤ G)
    (hperfect : CyclicPerfectDifference x (x (Fin.last m) + G)) :
    (∀ i j k l : Fin (m + 1), i < j → k < l → x j - x i = x l - x k → (i, j) = (k, l)) ∧
    Chamber x (fun i => (x i : ℝ)) ∧
      ∀ y : Fin (m + 1) → ℝ, Chamber x y → y (Fin.last m) ≤ (x (Fin.last m) : ℝ) →
        ∀ i : Fin (m + 1), y i = (x i : ℝ) := by
  refine ⟨fun _ _ _ _ => distance_unique hx hG hperfect, reference_mem_chamber hzero hx, ?_⟩
  intro y hy hlength i
  let z (j : Fin (m + 1)) : ℝ := y j - (x j : ℝ)
  have hz : Monotone z := Fin.monotone_iff_le_succ.mpr fun j => by
    have hj : j.castSucc < j.succ := Fin.castSucc_lt_succ
    have hbound := chamber_distance_ge hx hperfect hy _ (hgap j) _ _ hj rfl
    rw [Nat.cast_sub (hx.monotone hj.le)] at hbound
    dsimp [z]
    linarith
  have hfirst : z 0 = 0 := by simp [z, hy.1, hzero]
  have hlast : z (Fin.last m) ≤ 0 := sub_nonpos.mpr hlength
  have hlow : 0 ≤ z i := hfirst ▸ hz (Fin.zero_le i)
  have hhigh : z i ≤ 0 := (hz (Fin.le_last i)).trans hlast
  exact sub_eq_zero.mp (le_antisymm hhigh hlow)

end D5.S3.Geometry.FiniteGeometry.NotikSingerChamber
