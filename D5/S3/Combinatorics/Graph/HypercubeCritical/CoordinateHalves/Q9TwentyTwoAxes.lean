/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoAxes
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: Normalize the first three axes and two-step move in a singleton compression. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Relabel the cut, the three solid root axes, and the at most two remaining
axes in the first subdivided edge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoAxes

open BalancedCriticalSpectrum (Q)
open CubeCoordinateNormalization (normalize origin)
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
open private firstPointAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
local notation "flip" => BalancedCriticalSpectrum.flip

/-- Prescribe the axes of the cut and the three root edges. Any other axes
used in the first two-step move then occupy consecutive indices starting at
four. -/
theorem normalize_first_axes (first : Fin 3 ↪ Fin 9) (hzero : ∀ i, first i ≠ 0)
    (a b : Fin 9) :
    let fixed : Fin 4 → Fin 9 := Fin.cases 0 first
    let extra := ({a, b} : Finset (Fin 9)) \ (Finset.univ.image fixed)
    ∃ σ : Equiv.Perm (Fin 9),
      (∀ i : Fin 4, (σ (fixed i)).val = i.val) ∧
      extra.image σ =
        Finset.univ.filter (fun i : Fin 9 => 4 ≤ i.val ∧ i.val < 4 + extra.card) := by
  classical
  let fixed : Fin 4 → Fin 9 := Fin.cases 0 first
  let extra := ({a, b} : Finset (Fin 9)) \ (Finset.univ.image fixed)
  have hfixed : Function.Injective fixed := by
    intro i j h
    revert h
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · exact fun h => (hzero j h.symm).elim
    · exact fun h => (hzero i h).elim
    · exact fun h => congrArg Fin.succ (first.injective h)
  have hcard : extra.card ≤ 2 := by
    calc
      _ ≤ ({a, b} : Finset (Fin 9)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ 2 := Finset.card_insert_le _ _
  let e := Fintype.equivFinOfCardEq (Fintype.card_coe extra)
  let new (i : (extra : Set (Fin 9))) : Fin 9 := ⟨4 + (e i).val, by have h := (e i).isLt; omega⟩
  let oldLabel : Fin 4 ⊕ (extra : Set (Fin 9)) → Fin 9 := Sum.elim fixed Subtype.val
  let newLabel : Fin 4 ⊕ (extra : Set (Fin 9)) → Fin 9 :=
    Sum.elim (Fin.castLE (by decide : 4 ≤ 9)) new
  have hold : Function.Injective oldLabel := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (hfixed h)
    · have hj : j.val ∉ Finset.univ.image fixed := (Finset.mem_sdiff.mp j.property).2
      exact (hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)).elim
    · have hi : i.val ∉ Finset.univ.image fixed := (Finset.mem_sdiff.mp i.property).2
      exact (hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h.symm⟩)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  have hnew : Function.Injective newLabel := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))
    · have hv := congrArg Fin.val h
      change i.val = 4 + (e j).val at hv
      omega
    · have hv := congrArg Fin.val h
      change 4 + (e i).val = j.val at hv
      omega
    · have hv := congrArg Fin.val h
      change 4 + (e i).val = 4 + (e j).val at hv
      exact congrArg Sum.inr (e.injective (Fin.ext (by omega)))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair oldLabel newLabel hold hnew
  have hmap (i : (extra : Set (Fin 9))) : σ i.val = new i := hσ (Sum.inr i)
  refine ⟨σ, fun i => congrArg Fin.val (hσ (Sum.inl i)), ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    rw [← hji, hmap ⟨j, hj⟩]
    change 4 ≤ 4 + (e ⟨j, hj⟩).val ∧ 4 + (e ⟨j, hj⟩).val < 4 + extra.card
    exact ⟨by omega, Nat.add_lt_add_left (e ⟨j, hj⟩).isLt 4⟩
  · rintro ⟨hi, himax⟩
    change i.val < 4 + extra.card at himax
    let j : Fin extra.card := ⟨i.val - 4, by omega⟩
    refine Finset.mem_image.mpr ⟨(e.symm j).val, (e.symm j).property, ?_⟩
    rw [hmap (e.symm j)]
    apply Fin.ext
    change 4 + (e (e.symm j)).val = i.val
    rw [e.apply_symm_apply]
    dsimp [j]
    omega

#print axioms normalize_first_axes

private theorem first_point_check :
    ∀ (a b : Fin 9) (k : Fin 3),
      ({a, b} : Finset (Fin 9)).filter (fun i => 4 ≤ i.val) =
        Finset.univ.filter (fun i : Fin 9 => 4 ≤ i.val ∧ i.val < 4 + k.val) →
      firstPointAxes (toggle (toggle 2 a) b) = true := by
  decide +kernel

/-- Translate a root to zero and relabel its three edge directions. The
first cycle point, two steps from the first root neighbor, meets the
initial coordinate restriction of the embedding search. -/
theorem normalize_root_and_first_point (o : Q 9) (first : Fin 3 ↪ Fin 9)
    (hzero : ∀ i, first i ≠ 0) (a b : Fin 9) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Equiv.Perm (Fin 9)),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = o 0) ∧
      g o = cubeBitVec 9 0 ∧
      (∀ i : Fin 3, g (flip o (first i)) =
        cubeBitVec 9 (BitVec.ofNat 9 (2 ^ (i.val + 1)))) ∧
      firstPointAxes ((cubeBitVec 9).symm (g (flip (flip (flip o (first 0)) a) b))) =
        true := by
  classical
  let fixed : Fin 4 → Fin 9 := Fin.cases 0 first
  let extra := ({a, b} : Finset (Fin 9)) \ (Finset.univ.image fixed)
  obtain ⟨σ, hσ, hσextra⟩ := normalize_first_axes first hzero a b
  change ∀ i : Fin 4, (σ (fixed i)).val = i.val at hσ
  change extra.image σ = _ at hσextra
  let g := normalize σ.symm o
  have h0 : σ 0 = 0 := Fin.ext (hσ 0)
  have h1 (i : Fin 3) : σ (first i) = ⟨i.val + 1, by omega⟩ :=
    Fin.ext (hσ i.succ)
  have hg0 : g o = origin := normalize_center σ.symm o
  have hplane (x : Q 9) : g x 0 = false ↔ x 0 = o 0 := by
    have hs : σ.symm 0 = 0 := (σ.symm_apply_eq).mpr h0.symm
    change (x (σ.symm 0) != o (σ.symm 0)) = false ↔ _
    simp [hs]
  have hcard : extra.card ≤ 2 := by
    calc
      _ ≤ ({a, b} : Finset (Fin 9)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ 2 := Finset.card_insert_le _ _
  let k : Fin 3 := ⟨extra.card, by omega⟩
  have hextra : ({σ a, σ b} : Finset (Fin 9)).filter (fun i => 4 ≤ i.val) =
      extra.image σ := by
    apply Finset.ext
    intro i
    constructor
    · rintro hi
      obtain ⟨hi, hbig⟩ := Finset.mem_filter.mp hi
      let j := σ.symm i
      have hji : σ j = i := σ.apply_symm_apply i
      have hj : j ∈ ({a, b} : Finset (Fin 9)) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, ← hji, σ.injective.eq_iff] using hi
      have hn : j ∉ Finset.univ.image fixed := by
        rintro hj
        obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hj
        have hs : (σ j).val = r.val := by rw [← hr, hσ]
        rw [hji] at hs
        have := r.isLt
        omega
      exact Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hj, hn⟩, hji⟩
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hj' := (Finset.mem_sdiff.mp hj).1
      have hbig : 4 ≤ (σ j).val := by
        rw [hσextra] at hi
        exact (Finset.mem_filter.mp hi).2.1
      exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_insert, Finset.mem_singleton,
        σ.injective.eq_iff] using hj', hbig⟩
  have hb0 : cubeBitVec 9 (0 : BitVec 9) = origin := by decide
  have hb1 (i : Fin 3) : cubeBitVec 9 (BitVec.ofNat 9 (2 ^ (i.val + 1))) =
      flip origin ⟨i.val + 1, by omega⟩ := by
    have h := cubeBitVec_xor_single (0 : BitVec 9) (⟨i.val + 1, by omega⟩ : Fin 9)
    change cubeBitVec 9 (0#9 ^^^ BitVec.ofNat 9 (2 ^ (i.val + 1))) =
      flip (cubeBitVec 9 0) ⟨i.val + 1, by omega⟩ at h
    rw [BitVec.zero_xor, hb0] at h
    exact h
  refine ⟨g, σ, normalize_flip σ o, hplane, hg0.trans hb0.symm, ?_, ?_⟩
  · intro i
    change normalize σ.symm o (flip o (first i)) = _
    rw [normalize_flip, hg0, h1 i, hb1]
  · have hcheck := first_point_check (σ a) (σ b) k (hextra.trans hσextra)
    have hv : g (flip (flip (flip o (first 0)) a) b) =
        cubeBitVec 9 (toggle (toggle 2 (σ a)) (σ b)) := by
      simp only [g, normalize_flip, hg0, h1 0, ← hb1 0]
      simp only [toggle, cubeBitVec_xor_single]
      rfl
    simpa only [hv, Equiv.symm_apply_apply] using hcheck

#print axioms normalize_root_and_first_point

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoAxes
