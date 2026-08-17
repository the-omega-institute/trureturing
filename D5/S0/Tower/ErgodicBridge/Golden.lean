/- GID: D5/S0/Tower/ErgodicBridge/Golden
   generality: I
   mirror-B: D5/B/S0/Tower/ErgodicBridge/Golden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden name-grid liminf equals the lower arm value of its expanding gap orbit. -/

import D5.S0.Tower.Champions.GoldenAsymptotic
import D5.S0.Tower.Champions.GoldenSurvivorTubes

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact grid survivor, typed containing-gap arms,
     gap substitution, expanding transition, and periodic maximin, but no theorem
     connecting a general grid point to an iterated transition state.
   * Pinned mathlib supplies `Filter.liminf_congr` and `Filter.liminf_nat_add`;
     neither contains geometry specific to golden-name grids.
   * The bridge therefore proves pointwise arm equality and both realization
     directions locally; no third-party package or measure-theoretic assumption is used. -/

/- The carrier below is the internal name-grid hull.  Its omitted right terminal
   point has a one-sided terminal gap, not a state of the two-ended expanding map. -/

namespace D5.S0.Tower.ErgodicBridge.Golden

local notation "phi" => Real.goldenRatio

def GoldenUnitState
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState) : Prop :=
  0 <= state.coordinate /\ state.coordinate <= 1

def GoldenGridCoding (Q : Nat) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState) : Prop :=
  GoldenUnitState state /\
    match state.kind with
    | .large =>
        D5.S0.Tower.Champions.GoldenAsymptotic.IsGoldenOrbitGap Q x
          state.coordinate (1 - state.coordinate)
    | .small =>
        D5.S0.Tower.Champions.GoldenAsymptotic.IsGoldenOrbitGap Q x
          (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * state.coordinate)
          (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
            (1 - state.coordinate))

noncomputable def goldenOrbitLowerValue
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState) : Real :=
  Filter.liminf
    (fun n => D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenStateArm
      ((D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition^[n]) state))
    Filter.atTop

theorem golden_inverse_scale (Q : Nat) :
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
        phi ^ (-(Q : Int)) =
      phi ^ (-((Q + 1 : Nat) : Int)) := by
  unfold D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse
  rw [← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

theorem golden_phi_sq_mul_inverse :
    phi ^ 2 * D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse = phi := by
  calc
    phi ^ 2 * D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse =
        phi * (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * phi) := by
      ring
    _ = phi := by
      rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_mul]
      ring

theorem golden_inverse_mul_phi_sq :
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * phi ^ 2 = phi := by
  rw [mul_comm]
  exact golden_phi_sq_mul_inverse

theorem golden_survivor_eq_state_arm (Q : Nat) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hcode : GoldenGridCoding Q x state) :
    D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor Q x =
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenStateArm state := by
  rcases state with ⟨kind, u⟩
  cases kind with
  | large =>
      rcases hcode with ⟨⟨hu0, hu1⟩, hgap⟩
      have hnearest : min u (1 - u) = u ∨ min u (1 - u) = 1 - u := by
        by_cases h : u <= 1 - u
        · left
          exact min_eq_left h
        · right
          exact min_eq_right (le_of_not_ge h)
      exact D5.S0.Tower.Champions.GoldenAsymptotic.goldenSurvivor_eq_of_orbit_gap
        Q x u (1 - u) (min u (1 - u)) hgap hu0 (by linarith)
          (min_le_left _ _) (min_le_right _ _) hnearest
  | small =>
      rcases hcode with ⟨⟨hu0, hu1⟩, hgap⟩
      have hinv0 :
          0 <= D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse :=
        D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_pos.le
      have hnearest :
          D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * min u (1 - u) =
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u ∨
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * min u (1 - u) =
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) := by
        by_cases h : u <= 1 - u
        · left
          rw [min_eq_left h]
        · right
          rw [min_eq_right (le_of_not_ge h)]
      exact D5.S0.Tower.Champions.GoldenAsymptotic.goldenSurvivor_eq_of_orbit_gap
        Q x
          (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u)
          (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u))
          (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * min u (1 - u))
          hgap (mul_nonneg hinv0 hu0) (mul_nonneg hinv0 (by linarith))
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hinv0)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hinv0) hnearest

theorem golden_grid_coding_transition (Q : Nat) (hQ : 2 <= Q) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hcode : GoldenGridCoding Q x state) :
    GoldenGridCoding (Q + 1) x
      (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition state) := by
  rcases state with ⟨kind, u⟩
  cases kind with
  | large =>
      rcases hcode with ⟨⟨hu0, hu1⟩, i, hleft, hright⟩
      change 0 <= u at hu0
      change u <= 1 at hu1
      change x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
        u * phi ^ (-(Q : Int)) at hleft
      change D5.S0.Tower.GoldenGaps.indexedNameValue Q
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x =
        (1 - u) * phi ^ (-(Q : Int)) at hright
      have hlarge :
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
            phi ^ (-(Q : Int)) := by
        calc
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
              (D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x) +
                (x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) := by ring
          _ = ((1 - u) + u) * phi ^ (-(Q : Int)) := by
            rw [hleft, hright]
            ring
          _ = phi ^ (-(Q : Int)) := by ring
      obtain ⟨j, hset, hjleft, hjright⟩ :=
        (D5.S0.Tower.GoldenSubstitution.golden_gap_substitution Q hQ i).2 (by
          simpa [D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft,
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using hlarge)
      change D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j -
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
        phi ^ (-((Q + 1 : Nat) : Int)) at hjleft
      change D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
          D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j =
        phi ^ (-((Q + 2 : Nat) : Int)) at hjright
      have hpositions :=
        D5.S0.Tower.Champions.GoldenAsymptotic.inserted_singleton_positions Q i j hset
      by_cases hbranch :
          u <= D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse
      · let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
          ⟨(D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
              (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)).1, by
            change (D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
              (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)).1 <
                Nat.fib (Q + 3) - 1
            have hjbound := j.2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft (Q + 1) next =
              D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) := by
          apply Fin.ext
          simp [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft]
        have hnextRight :
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight (Q + 1) next = j := by
          apply Fin.ext
          simpa [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using
            hpositions.1
        have hv0 : 0 <= phi * u := mul_nonneg Real.goldenRatio_pos.le hu0
        have hv1 : phi * u <= 1 := by
          have hmul := mul_le_mul_of_nonneg_left hbranch Real.goldenRatio_pos.le
          nlinarith [hmul,
            D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_mul]
        simp only [D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition,
          hbranch, GoldenGridCoding, GoldenUnitState]
        refine ⟨⟨hv0, hv1⟩, next, ?_, ?_⟩
        · rw [hnextLeft, D5.S0.Tower.GoldenSubstitution.levelEmbedding_value]
          calc
            x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
                u * phi ^ (-(Q : Int)) := hleft
            _ = (phi * u) * phi ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Champions.GoldenAsymptotic.golden_scale_succ Q]
              ring
        · rw [hnextRight]
          calc
            D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j - x =
                (D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.GoldenGaps.indexedNameValue Q
                      (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) -
                  (x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) := by ring
            _ = phi ^ (-((Q + 1 : Nat) : Int)) -
                u * phi ^ (-(Q : Int)) := by rw [hjleft, hleft]
            _ = (1 - phi * u) * phi ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Champions.GoldenAsymptotic.golden_scale_succ Q]
              ring
      · let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
          ⟨j.1, by
            change j.1 < Nat.fib (Q + 3) - 1
            have hrightbound :=
              (D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i)).2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft (Q + 1) next = j := by
          apply Fin.ext
          simp [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft]
        have hnextRight :
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight (Q + 1) next =
              D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) := by
          apply Fin.ext
          simpa [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using
            hpositions.2
        let v := phi ^ 2 * u - phi
        have hv0 : 0 <= v := by
          have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hbranch) (sq_pos_of_pos Real.goldenRatio_pos)
          rw [golden_phi_sq_mul_inverse] at hmul
          exact (sub_pos.mpr hmul).le
        have hv1 : v <= 1 := by
          have hmul := mul_le_mul_of_nonneg_left hu1 (sq_nonneg phi)
          dsimp [v]
          nlinarith [hmul, Real.goldenRatio_sq]
        have hinvV :
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * v =
              phi * u - 1 := by
          dsimp [v]
          calc
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                (phi ^ 2 * u - phi) =
              (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * phi ^ 2) * u -
                D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * phi := by ring
            _ = phi * u - 1 := by
              rw [golden_inverse_mul_phi_sq,
                D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_mul]
        have hinvOneSubV :
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - v) =
              phi * (1 - u) := by
          dsimp [v]
          calc
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                (1 - (phi ^ 2 * u - phi)) =
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                (phi ^ 2 * (1 - u)) := by rw [Real.goldenRatio_sq]; ring
            _ = (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * phi ^ 2) *
                (1 - u) := by ring
            _ = phi * (1 - u) := by rw [golden_inverse_mul_phi_sq]
        simp only [D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition,
          hbranch, GoldenGridCoding, GoldenUnitState]
        change (0 <= v /\ v <= 1) /\
          D5.S0.Tower.Champions.GoldenAsymptotic.IsGoldenOrbitGap (Q + 1) x
            (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * v)
            (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - v))
        refine ⟨⟨hv0, hv1⟩, next, ?_, ?_⟩
        · rw [hnextLeft]
          calc
            x - D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j =
                (x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) -
                  (D5.S0.Tower.GoldenGaps.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.GoldenGaps.indexedNameValue Q
                      (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) := by ring
            _ = u * phi ^ (-(Q : Int)) -
                phi ^ (-((Q + 1 : Nat) : Int)) := by rw [hleft, hjleft]
            _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * v *
                phi ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Champions.GoldenAsymptotic.golden_scale_succ Q]
              rw [hinvV]
              ring
        · rw [hnextRight, D5.S0.Tower.GoldenSubstitution.levelEmbedding_value]
          calc
            D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x =
                (1 - u) * phi ^ (-(Q : Int)) := hright
            _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - v) *
                phi ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Champions.GoldenAsymptotic.golden_scale_succ Q]
              rw [hinvOneSubV]
              ring
  | small =>
      rcases hcode with ⟨⟨hu0, hu1⟩, i, hleft, hright⟩
      change 0 <= u at hu0
      change u <= 1 at hu1
      change x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
          phi ^ (-(Q : Int)) at hleft
      change D5.S0.Tower.GoldenGaps.indexedNameValue Q
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
          phi ^ (-(Q : Int)) at hright
      have hsmall :
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
            phi ^ (-((Q + 1 : Nat) : Int)) := by
        calc
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
              (D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x) +
                (x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                  (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)) := by ring
          _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                ((1 - u) + u) * phi ^ (-(Q : Int)) := by rw [hleft, hright]; ring
          _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
              phi ^ (-(Q : Int)) := by ring
          _ = phi ^ (-((Q + 1 : Nat) : Int)) := golden_inverse_scale Q
      obtain ⟨hset, _⟩ :=
        (D5.S0.Tower.GoldenSubstitution.golden_gap_substitution Q hQ i).1 (by
          simpa [D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft,
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using hsmall)
      have hpositions :=
        D5.S0.Tower.Champions.GoldenAsymptotic.inserted_empty_positions Q i hset
      let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
        ⟨(D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)).1, by
          change (D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)).1 <
              Nat.fib (Q + 3) - 1
          have hrightbound :=
            (D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
              (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i)).2
          omega⟩
      have hnextLeft :
          D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft (Q + 1) next =
            D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
              (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) := by
        apply Fin.ext
        simp [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft]
      have hnextRight :
          D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight (Q + 1) next =
            D5.S0.Tower.GoldenSubstitution.levelEmbedding Q
              (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) := by
        apply Fin.ext
        simpa [next, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using
          hpositions.symm
      simp only [D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition,
        GoldenGridCoding, GoldenUnitState]
      refine ⟨⟨hu0, hu1⟩, next, ?_, ?_⟩
      · rw [hnextLeft, D5.S0.Tower.GoldenSubstitution.levelEmbedding_value]
        calc
          x - D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
                phi ^ (-(Q : Int)) := hleft
          _ = u * phi ^ (-((Q + 1 : Nat) : Int)) := by
            calc
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
                    phi ^ (-(Q : Int)) =
                  u * (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                    phi ^ (-(Q : Int))) := by ring
              _ = u * phi ^ (-((Q + 1 : Nat) : Int)) := by rw [golden_inverse_scale]
      · rw [hnextRight, D5.S0.Tower.GoldenSubstitution.levelEmbedding_value]
        calc
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) - x =
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
                phi ^ (-(Q : Int)) := hright
          _ = (1 - u) * phi ^ (-((Q + 1 : Nat) : Int)) := by
            calc
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
                    phi ^ (-(Q : Int)) =
                  (1 - u) * (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
                    phi ^ (-(Q : Int))) := by ring
              _ = (1 - u) * phi ^ (-((Q + 1 : Nat) : Int)) := by
                rw [golden_inverse_scale]

theorem golden_grid_coding_iterate (Q : Nat) (hQ : 2 <= Q) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hcode : GoldenGridCoding Q x state) (n : Nat) :
    GoldenGridCoding (Q + n) x
      ((D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition^[n]) state) := by
  induction n with
  | zero => simpa using hcode
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.add_assoc] using golden_grid_coding_transition (Q + n) (by omega) x _ ih

theorem golden_survivor_eq_orbit_arm (Q : Nat) (hQ : 2 <= Q) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hcode : GoldenGridCoding Q x state) (n : Nat) :
    D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor (Q + n) x =
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenStateArm
        ((D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition^[n]) state) := by
  exact golden_survivor_eq_state_arm (Q + n) x _
    (golden_grid_coding_iterate Q hQ x state hcode n)

theorem golden_ergodic_bridge_of_coding (Q : Nat) (hQ : 2 <= Q) (x : Real)
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hcode : GoldenGridCoding Q x state) :
    Filter.liminf
        (fun level =>
          D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor level x)
        Filter.atTop =
      goldenOrbitLowerValue state := by
  rw [← Filter.liminf_nat_add
    (fun level => D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor level x) Q]
  unfold goldenOrbitLowerValue
  apply Filter.liminf_congr
  filter_upwards [] with n
  simpa [Nat.add_comm] using golden_survivor_eq_orbit_arm Q hQ x state hcode n

theorem golden_grid_coding_exists_of_mem_hull (Q : Nat) (x : Real)
    (hx : x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull Q) :
    ∃ state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState,
      GoldenGridCoding Q x state := by
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let a := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)
  let b := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i)
  change a <= x /\ x <= b at hxi
  have hgap : b - a = phi ^ (-(Q : Int)) ∨
      b - a = phi ^ (-((Q + 1 : Nat) : Int)) := by
    simpa [a, b, D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft,
      D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight] using
        D5.S0.Tower.GoldenGaps.consecutive_nameValue_gap Q i
  let u := (x - a) / (b - a)
  have hgapPos : 0 < b - a := by
    rcases hgap with hlarge | hsmall
    · rw [hlarge]
      positivity
    · rw [hsmall]
      positivity
  have hgapNe : b - a ≠ 0 := ne_of_gt hgapPos
  have hu0 : 0 <= u := by
    exact div_nonneg (sub_nonneg.mpr hxi.1) hgapPos.le
  have hu1 : u <= 1 := by
    apply (div_le_one hgapPos).2
    linarith
  have hleftRatio : x - a = u * (b - a) := by
    dsimp [u]
    field_simp
  have hrightRatio : b - x = (1 - u) * (b - a) := by
    dsimp [u]
    field_simp
    ring
  rcases hgap with hlarge | hsmall
  · refine ⟨⟨D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenGapKind.large, u⟩,
      ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩⟩
    · change x - a = u * phi ^ (-(Q : Int))
      rw [hleftRatio, hlarge]
    · change b - x = (1 - u) * phi ^ (-(Q : Int))
      rw [hrightRatio, hlarge]
  · refine ⟨⟨D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenGapKind.small, u⟩,
      ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩⟩
    · change x - a =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
          phi ^ (-(Q : Int))
      calc
        x - a = u * (b - a) := hleftRatio
        _ = u * phi ^ (-((Q + 1 : Nat) : Int)) := by rw [hsmall]
        _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
            phi ^ (-(Q : Int)) := by rw [← golden_inverse_scale Q]; ring
    · change b - x =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
          phi ^ (-(Q : Int))
      calc
        b - x = (1 - u) * (b - a) := hrightRatio
        _ = (1 - u) * phi ^ (-((Q + 1 : Nat) : Int)) := by rw [hsmall]
        _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
            phi ^ (-(Q : Int)) := by rw [← golden_inverse_scale Q]; ring

/-- Every point in an internal golden-name hull has exactly the same lower
asymptotic survivor value as the arm observable on a golden transition orbit. -/
theorem golden_ergodic_bridge (Q : Nat) (hQ : 2 <= Q) (x : Real)
    (hx : x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull Q) :
    ∃ state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState,
      GoldenUnitState state /\
        Filter.liminf
            (fun level =>
              D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor level x)
            Filter.atTop =
          goldenOrbitLowerValue state := by
  obtain ⟨state, hcode⟩ := golden_grid_coding_exists_of_mem_hull Q x hx
  exact ⟨state, hcode.1, golden_ergodic_bridge_of_coding Q hQ x state hcode⟩

theorem golden_large_state_realized_in_gap (Q : Nat)
    (i : Fin (Nat.fib (Q + 2) - 1)) (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hlarge :
      D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
        phi ^ (-(Q : Int))) :
    ∃ x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull Q,
      GoldenGridCoding Q x
        ⟨D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenGapKind.large, u⟩ := by
  let a := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)
  let b := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i)
  let x := a + u * (b - a)
  have hgapPos : 0 < b - a := by rw [hlarge]; positivity
  have hleft : a <= x := by
    dsimp [x]
    nlinarith [mul_nonneg hu0 hgapPos.le]
  have hright : x <= b := by
    have hmul := mul_le_mul_of_nonneg_right hu1 hgapPos.le
    dsimp [x]
    nlinarith
  refine ⟨x, Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
  · exact ⟨hleft, hright⟩
  · refine ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩
    · change x - a = u * phi ^ (-(Q : Int))
      dsimp [x]
      rw [hlarge]
      ring
    · change b - x = (1 - u) * phi ^ (-(Q : Int))
      calc
        b - x = (1 - u) * (b - a) := by dsimp [x]; ring
        _ = (1 - u) * phi ^ (-(Q : Int)) := by rw [hlarge]

theorem golden_small_state_realized_in_gap (Q : Nat)
    (i : Fin (Nat.fib (Q + 2) - 1)) (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsmall :
      D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i) -
          D5.S0.Tower.GoldenGaps.indexedNameValue Q
            (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i) =
        phi ^ (-((Q + 1 : Nat) : Int))) :
    ∃ x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull Q,
      GoldenGridCoding Q x
        ⟨D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenGapKind.small, u⟩ := by
  let a := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft Q i)
  let b := D5.S0.Tower.GoldenGaps.indexedNameValue Q
    (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight Q i)
  let x := a + u * (b - a)
  have hgapPos : 0 < b - a := by rw [hsmall]; positivity
  have hleft : a <= x := by
    dsimp [x]
    nlinarith [mul_nonneg hu0 hgapPos.le]
  have hright : x <= b := by
    have hmul := mul_le_mul_of_nonneg_right hu1 hgapPos.le
    dsimp [x]
    nlinarith
  refine ⟨x, Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
  · exact ⟨hleft, hright⟩
  · refine ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩
    · change x - a =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * u *
          phi ^ (-(Q : Int))
      dsimp [x]
      rw [hsmall, ← golden_inverse_scale Q]
      ring
    · change b - x =
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
          phi ^ (-(Q : Int))
      calc
        b - x = (1 - u) * (b - a) := by dsimp [x]; ring
        _ = (1 - u) * phi ^ (-((Q + 1 : Nat) : Int)) := by rw [hsmall]
        _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse * (1 - u) *
            phi ^ (-(Q : Int)) := by rw [← golden_inverse_scale Q]; ring

theorem golden_level_two_second_gap_value :
    D5.S0.Tower.GoldenGaps.indexedNameValue 2
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight 2
            (⟨1, by norm_num [Nat.fib]⟩ : Fin (Nat.fib (2 + 2) - 1))) -
        D5.S0.Tower.GoldenGaps.indexedNameValue 2
          (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft 2
            (⟨1, by norm_num [Nat.fib]⟩ : Fin (Nat.fib (2 + 2) - 1))) =
      phi ^ (-3 : Int) := by
  change
    ((D5.S0.Conventions.wdigits 2).map fun k : Nat =>
        phi ^ ((k : Int) - (((2 : Nat) + 2 : Nat) : Int))).sum -
      ((D5.S0.Conventions.wdigits 1).map fun k : Nat =>
        phi ^ ((k : Int) - (((2 : Nat) + 2 : Nat) : Int))).sum =
      phi ^ (-3 : Int)
  rw [show D5.S0.Conventions.wdigits 2 = [3] by
      symm
      apply D5.S0.Conventions.wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib],
    show D5.S0.Conventions.wdigits 1 = [2] by
      symm
      apply D5.S0.Conventions.wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  norm_num only
  rw [show (-1 : Int) = -3 + 2 by omega, zpow_add₀ Real.goldenRatio_ne_zero,
    show (-2 : Int) = -3 + 1 by omega, zpow_add₀ Real.goldenRatio_ne_zero]
  norm_num only [zpow_ofNat, pow_one]
  rw [Real.goldenRatio_sq]
  ring

/-- Conversely, every unit state of the golden expanding map is realized by
an internal level-two name-grid gap. -/
theorem golden_unit_state_has_grid_realization
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hunit : GoldenUnitState state) :
    ∃ x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull 2,
      GoldenGridCoding 2 x state := by
  rcases state with ⟨kind, u⟩
  rcases hunit with ⟨hu0, hu1⟩
  change 0 <= u at hu0
  change u <= 1 at hu1
  cases kind with
  | large =>
      let i := D5.S0.Tower.MetricGeometry.GoldenSurvivor.firstGoldenGap 2 (by omega)
      have hlarge :
          D5.S0.Tower.GoldenGaps.indexedNameValue 2
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight 2 i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue 2
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft 2 i) =
            phi ^ (-2 : Int) := by
        simpa [i] using
          D5.S0.Tower.MetricGeometry.GoldenSurvivor.first_golden_gap_value 2 (by omega)
      exact golden_large_state_realized_in_gap 2 i u hu0 hu1 hlarge
  | small =>
      let i : Fin (Nat.fib (2 + 2) - 1) := ⟨1, by norm_num [Nat.fib]⟩
      have hsmall :
          D5.S0.Tower.GoldenGaps.indexedNameValue 2
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapRight 2 i) -
              D5.S0.Tower.GoldenGaps.indexedNameValue 2
                (D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenGapLeft 2 i) =
            phi ^ (-3 : Int) := by
        simpa [i] using golden_level_two_second_gap_value
      exact golden_small_state_realized_in_gap 2 i u hu0 hu1 hsmall

theorem golden_ergodic_bridge_reverse
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState)
    (hunit : GoldenUnitState state) :
    ∃ x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull 2,
      Filter.liminf
          (fun level =>
            D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor level x)
          Filter.atTop =
        goldenOrbitLowerValue state := by
  obtain ⟨x, hx, hcode⟩ := golden_unit_state_has_grid_realization state hunit
  exact ⟨x, hx, golden_ergodic_bridge_of_coding 2 (by omega) x state hcode⟩

/-- Lower asymptotic values attained by points carried by an internal
golden-name hull. -/
def goldenGridLowerValues : Set Real :=
  {value | ∃ Q : Nat, 2 <= Q /\
    ∃ x ∈ D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull Q,
      value = Filter.liminf
        (fun level =>
          D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor level x)
        Filter.atTop}

/-- Lower asymptotic arm values attained by unit states of the expanding map. -/
def goldenErgodicLowerValues : Set Real :=
  {value | ∃ state :
      D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState,
    GoldenUnitState state /\ value = goldenOrbitLowerValue state}

/-- The internal name-grid problem and the unit-state dynamical problem attain
exactly the same lower asymptotic values. -/
theorem golden_lower_value_sets_eq :
    goldenGridLowerValues = goldenErgodicLowerValues := by
  ext value
  constructor
  · rintro ⟨Q, hQ, x, hx, hvalue⟩
    obtain ⟨state, hunit, hbridge⟩ := golden_ergodic_bridge Q hQ x hx
    exact ⟨state, hunit, hvalue.trans hbridge⟩
  · rintro ⟨state, hunit, hvalue⟩
    obtain ⟨x, hx, hbridge⟩ := golden_ergodic_bridge_reverse state hunit
    exact ⟨2, by omega, x, hx, hvalue.trans hbridge.symm⟩

/-- The name-grid champion objective on the internal carrier. -/
noncomputable def goldenGridOptimalValue : Real := sSup goldenGridLowerValues

/-- Ergodic maximin objective for the arm observable on unit states. -/
noncomputable def goldenErgodicOptimalValue : Real := sSup goldenErgodicLowerValues

/-- Bidirectional coding turns the internal golden champion problem into
ergodic optimization of the lower arm observable. -/
theorem golden_optimal_value_eq_ergodic_optimal_value :
    goldenGridOptimalValue = goldenErgodicOptimalValue := by
  rw [goldenGridOptimalValue, goldenErgodicOptimalValue, golden_lower_value_sets_eq]

end D5.S0.Tower.ErgodicBridge.Golden
