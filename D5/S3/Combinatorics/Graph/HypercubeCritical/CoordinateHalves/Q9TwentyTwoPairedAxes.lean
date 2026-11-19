/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedAxes
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: Reduce paired compressions to two standard choices of root axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization

/-! Normalize the two subdivided paths and the matched edge at a paired root. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedAxes

open BalancedCriticalSpectrum (Q flip_adj flip_apply_same)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open CubeCoordinateNormalization (normalize origin)
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
local notation "flip" => BalancedCriticalSpectrum.flip

private theorem seed_axes (a b e c d : Fin 9)
    (ha : a ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e)
    (hca : c ≠ a) (hcb : c ≠ b) (hce : c ≠ e)
    (hda : d ≠ a) (hdb : d ≠ b) (hde : d ≠ e) :
    ∃ σ : Equiv.Perm (Fin 9),
      σ 0 = 0 ∧ σ a = 1 ∧ σ b = 2 ∧ σ e = 3 ∧ σ c = 4 ∧
        σ d = (if c = d then 4 else 5) := by
  classical
  by_cases h : c = d
  · subst d
    let axes : Fin 5 → Fin 9 := ![0, a, b, e, c]
    have injective : Function.Injective axes := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [axes, Ne.symm]
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair axes
      (Fin.castLE (by decide : 5 ≤ 9)) injective (Fin.castLE_injective _)
    exact ⟨σ, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, by simpa [axes] using hσ 4⟩
  · let axes : Fin 6 → Fin 9 := ![0, a, b, e, c, d]
    have injective : Function.Injective axes := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [axes, Ne.symm]
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair axes
      (Fin.castLE (by decide : 6 ≤ 9)) injective (Fin.castLE_injective _)
    exact ⟨σ, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, by simpa [axes, h] using hσ 5⟩

/-- The root, its two hubs and its matched terminal have the two seed shapes
of the paired search. The shape records whether the two second axes coincide. -/
theorem normalize_paired_root (o : Q 9) (a b e c d : Fin 9)
    (ha : a ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e)
    (hca : c ≠ a) (hcb : c ≠ b) (hce : c ≠ e)
    (hda : d ≠ a) (hdb : d ≠ b) (hde : d ≠ e) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Equiv.Perm (Fin 9)),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = o 0) ∧
      g o = cubeBitVec 9 0 ∧
      g (flip (flip o a) c) = cubeBitVec 9 18 ∧
      g (flip (flip o b) d) = cubeBitVec 9 (if c = d then 20 else 36) ∧
      g (flip o e) = cubeBitVec 9 8 := by
  obtain ⟨σ, hzero, h1, h2, h3, h4, h5⟩ :=
    seed_axes a b e c d ha hb he hc hd hab hae hbe hca hcb hce hda hdb hde
  let g := normalize σ.symm o
  have hflip (x : Q 9) (i : Fin 9) : g (flip x i) = flip (g x) (σ i) := by
    exact normalize_flip σ o x i
  have hplane (x : Q 9) : g x 0 = false ↔ x 0 = o 0 := by
    have hs : σ.symm 0 = 0 := (σ.symm_apply_eq).mpr hzero.symm
    change (x (σ.symm 0) != o (σ.symm 0)) = false ↔ _
    simp [hs]
  have hroot : g o = origin := normalize_center σ.symm o
  refine ⟨g, σ, hflip, hplane, hroot.trans (by decide), ?_, ?_, ?_⟩
  · rw [hflip, hflip, hroot, h1, h4]
    decide +kernel
  · rw [hflip, hflip, hroot, h2, h5]
    by_cases h : c = d <;> simp only [h, ite_true, ite_false] <;> decide +kernel
  · rw [hflip, hroot, h3]
    decide +kernel

#print axioms normalize_paired_root

private theorem non_cut_axis {x y : Q 9} (same : y 0 = x 0) {i : Fin 9}
    (h : y = flip x i) : i ≠ 0 := by
  rintro rfl
  rw [h, flip_apply_same] at same
  exact (Bool.not_eq_self (x 0)).mp same

private theorem second_axis_ne {o z : Q 9} {a c t : Fin 9}
    (hz : z = flip (flip o a) c) (hn : ¬ (hypercube 9).Adj z (flip o t)) : c ≠ t := by
  rintro rfl
  rw [hz, flip_comm o a c] at hn
  exact hn (flip_adj (flip o c) a).symm

/-- In an actual coordinate half, the two root paths and the matched edge
normalize to one of the two placements used in the paired search. -/
theorem normalize_paired_paths {o m n u v w : Q 9}
    (mPlane : m 0 = o 0) (nPlane : n 0 = o 0) (uPlane : u 0 = o 0)
    (vPlane : v 0 = o 0) (wPlane : w 0 = o 0)
    (om : (hypercube 9).Adj o m) (on : (hypercube 9).Adj o n)
    (ow : (hypercube 9).Adj o w) (mu : (hypercube 9).Adj m u)
    (nv : (hypercube 9).Adj n v)
    (hmn : m ≠ n) (hmw : m ≠ w) (hnw : n ≠ w) (huo : u ≠ o) (hvo : v ≠ o)
    (hun : ¬ (hypercube 9).Adj u n) (huw : ¬ (hypercube 9).Adj u w)
    (hvm : ¬ (hypercube 9).Adj v m) (hvw : ¬ (hypercube 9).Adj v w) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Equiv.Perm (Fin 9)) (sameAxis : Bool),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = o 0) ∧
      g o = cubeBitVec 9 0 ∧ g u = cubeBitVec 9 18 ∧
      g v = cubeBitVec 9 (if sameAxis then 20 else 36) ∧ g w = cubeBitVec 9 8 := by
  obtain ⟨a, ha⟩ := adjacent_exists_flip om
  obtain ⟨b, hb⟩ := adjacent_exists_flip on
  obtain ⟨e, he⟩ := adjacent_exists_flip ow
  obtain ⟨c, hc⟩ := adjacent_exists_flip mu
  obtain ⟨d, hd⟩ := adjacent_exists_flip nv
  have huc : u = flip (flip o a) c := hc.trans (congrArg (fun x => flip x c) ha)
  have hvd : v = flip (flip o b) d := hd.trans (congrArg (fun x => flip x d) hb)
  have hab : a ≠ b := fun h => hmn (ha.trans ((congrArg (flip o) h).trans hb.symm))
  have hae : a ≠ e := fun h => hmw (ha.trans ((congrArg (flip o) h).trans he.symm))
  have hbe : b ≠ e := fun h => hnw (hb.trans ((congrArg (flip o) h).trans he.symm))
  have hca : c ≠ a := by
    intro h
    exact huo (by simpa [h] using huc)
  have hdb : d ≠ b := by
    intro h
    exact hvo (by simpa [h] using hvd)
  obtain ⟨g, σ, hf, hp, h0, h1, h2, h3⟩ := normalize_paired_root o a b e c d
    (non_cut_axis mPlane ha) (non_cut_axis nPlane hb) (non_cut_axis wPlane he)
    (non_cut_axis (uPlane.trans mPlane.symm) hc) (non_cut_axis (vPlane.trans nPlane.symm) hd)
    hab hae hbe hca (second_axis_ne huc (hb ▸ hun)) (second_axis_ne huc (he ▸ huw))
    (second_axis_ne hvd (ha ▸ hvm)) hdb (second_axis_ne hvd (he ▸ hvw))
  refine ⟨g, σ, decide (c = d), hf, hp, h0, huc ▸ h1, ?_, he ▸ h3⟩
  rw [hvd, h2]
  by_cases h : c = d <;> simp [h]

#print axioms normalize_paired_paths

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedAxes
