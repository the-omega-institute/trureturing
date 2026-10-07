/- GID: D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Nilpotent]
   utility: none
   digest: Uniform generator-word commutator vanishing implies generated-subgroup nilpotence. -/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GroupWords.UniformCommutatorNilpotence

open scoped commutatorElement

/-- A uniform bound for arbitrary nested commutators of generators implies nilpotence
of their actual generated subgroup. The generating set need not be finite, symmetric,
normal, or contain the identity. The word is processed from left to right. -/
theorem result {G : Type*} [Group G] (S : Set G) (N : ℕ)
    (hvan : ∀ (l : List G), (∀ a ∈ l, a ∈ S) → l.length = N →
      ∀ b ∈ S, l.foldl (fun z a => ⁅a, z⁆) b = 1) :
    Group.IsNilpotent (Subgroup.closure S) := by
  let H := Subgroup.closure S
  let T : Set H := ((↑) : H → G) ⁻¹' S
  have hT : Subgroup.closure T = ⊤ := Subgroup.closure_closure_coe_preimage
  have hcentral : ∀ (n : ℕ) (x : H),
      (∀ (l : List H), (∀ a ∈ l, a ∈ T) → l.length = n →
        l.foldl (fun z a => ⁅a, z⁆) x = 1) →
      x ∈ Subgroup.upperCentralSeries H n := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hx1 : x = 1 := hx [] (by simp) rfl
        simpa only [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] using hx1
    | succ n ih =>
        intro x hx
        let U := Subgroup.upperCentralSeries H n
        let q := QuotientGroup.mk' U
        let C := (Subgroup.centralizer ({q x} : Set (H ⧸ U))).comap q
        have hgen : ∀ a ∈ T, ⁅a, x⁆ ∈ U := by
          intro a ha
          apply ih
          intro l hl hlen
          exact hx (a :: l) (by
            intro b hb
            rcases List.mem_cons.mp hb with hb | hb
            · exact hb ▸ ha
            · exact hl b hb) (by simp [hlen])
        have hTC : T ⊆ C := by
          intro a ha
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          have hc : ⁅q a, q x⁆ = 1 := by
            rw [← map_commutatorElement q]
            exact (QuotientGroup.eq_one_iff _).mpr (hgen a ha)
          exact commutatorElement_eq_one_iff_mul_comm.mp hc
        have hC : C = ⊤ := by
          apply top_unique
          rw [← hT]
          exact (Subgroup.closure_le C).mpr hTC
        apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
        intro y
        have hy : y ∈ C := by rw [hC]; trivial
        have hcomm : q x * q y = q y * q x :=
          (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
        apply (QuotientGroup.eq_one_iff _).mp
        change q ⁅x, y⁆ = 1
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hcoe : ∀ (l : List H) (x : H),
      ((l.foldl (fun z a => ⁅a, z⁆) x : H) : G) =
        (l.map ((↑) : H → G)).foldl (fun z a => ⁅a, z⁆) (x : G) := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons a l ih =>
        intro x
        simpa only [List.foldl_cons, List.map_cons, Subgroup.coe_mul,
          Subgroup.coe_inv, commutatorElement_def] using ih ⁅a, x⁆
  have hTN : T ⊆ Subgroup.upperCentralSeries H N := by
    intro x hx
    apply hcentral N x
    intro l hl hlen
    apply Subtype.ext
    rw [hcoe]
    exact hvan (l.map ((↑) : H → G)) (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
      exact hl b hb) (by simpa using hlen) (x : G) hx
  refine ⟨⟨N, ?_⟩⟩
  apply top_unique
  rw [← hT]
  exact (Subgroup.closure_le _).mpr hTN

end D5.S3.Combinatorics.GroupWords.UniformCommutatorNilpotence
