/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates
   mirror-E: none(waiver:symbolic-existence-and-bounds)
   anchors: []
   utility: none
   digest: Real and rational row-image optimum certificates and their exact product. -/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Logic.Function.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates


open Classical in
/-- Actual row-image covering and packing have real extrema against all real feasible vectors.
The two extrema are separate; this statement does not identify their objective values. -/
theorem row_image_real_extrema {X Y Z : Type*} [Fintype X] [Fintype Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    (∃ lam : X → ℝ,
      (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      ∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
    (∃ w : Z → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  constructor
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (X → ℝ) := {lam | (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      ∀ z, 1 ≤ ∑ x, if A x z then lam x else 0}
    have hc : IsClosed K := by
      have heq : K = (⋂ x, {lam : X → ℝ | 0 ≤ lam x ∧ lam x ≤ 1}) ∩
          (⋂ z, {lam : X → ℝ | 1 ≤ ∑ x, if A x z then lam x else 0}) := by
        ext lam
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · apply isClosed_iInter
        intro x
        exact (isClosed_le continuous_const (continuous_apply x)).inter
          (isClosed_le (continuous_apply x) continuous_const)
      · apply isClosed_iInter
        intro z
        apply isClosed_le continuous_const
        apply continuous_finsetSum
        intro x hx
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply x
        · exact continuous_const
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro lam hlam
      exact ⟨fun x => (hlam.1 x).1, fun x => (hlam.1 x).2⟩)
    have hn : K.Nonempty := by
      refine ⟨fun _ => 1, (fun x => ⟨zero_le_one, le_rfl⟩), ?_⟩
      intro z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        (1 : ℝ) = (if A x z then 1 else 0) := by simp [ha]
        _ ≤ ∑ u : X, if A u z then (1 : ℝ) else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : X => if A u z then (1 : ℝ) else 0)
              (fun u _ => by split_ifs <;> positivity) (Finset.mem_univ x))
    obtain ⟨lam,hlam,hmin⟩ := hk.exists_isMinOn hn
      (show Continuous (fun lam : X → ℝ => ∑ x, lam x) by fun_prop).continuousOn
    refine ⟨lam,hlam.1,hlam.2,?_⟩
    intro μ hμ hcover
    let ν : X → ℝ := fun x => min (μ x) 1
    have hν : ν ∈ K := by
      refine ⟨fun x => ⟨le_min (hμ x) zero_le_one, min_le_right _ _⟩,?_⟩
      intro z
      by_cases hlarge : ∃ x, A x z ∧ 1 ≤ μ x
      · obtain ⟨x,ha,hx⟩ := hlarge
        calc
          (1 : ℝ) = (if A x z then ν x else 0) := by simp [ha,ν,min_eq_right hx]
          _ ≤ ∑ u : X, if A u z then ν u else 0 :=
            by
              simpa using (Finset.single_le_sum (s := Finset.univ)
                (f := fun u : X => if A u z then ν u else 0)
                (fun u _ => by
                  split_ifs
                  · exact le_min (hμ u) zero_le_one
                  · exact le_rfl) (Finset.mem_univ x))
      · have he : (∑ x, if A x z then ν x else 0) =
            ∑ x, if A x z then μ x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases ha : A x z
          · have hlt : μ x < 1 := lt_of_not_ge (fun h => hlarge ⟨x,ha,h⟩)
            simp [ha,ν,min_eq_left hlt.le]
          · simp [ha]
        rw [he]
        exact hcover z
    exact (hmin hν).trans (Finset.sum_le_sum (fun x _ => min_le_left (μ x) 1))
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (Z → ℝ) := {w | (∀ z, 0 ≤ w z) ∧
      ∀ x, (∑ z, if A x z then w z else 0) ≤ 1}
    have hc : IsClosed K := by
      have heq : K = (⋂ z, {w : Z → ℝ | 0 ≤ w z}) ∩
          (⋂ x, {w : Z → ℝ | (∑ z, if A x z then w z else 0) ≤ 1}) := by
        ext w
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · exact isClosed_iInter (fun z => isClosed_le continuous_const (continuous_apply z))
      · apply isClosed_iInter
        intro x
        apply isClosed_le _ continuous_const
        apply continuous_finsetSum
        intro z hz
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply z
        · exact continuous_const
    have hbound : ∀ w ∈ K, ∀ z, w z ≤ 1 := by
      intro w hw z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        w z = (if A x z then w z else 0) := by simp [ha]
        _ ≤ ∑ u : Z, if A x u then w u else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : Z => if A x u then w u else 0)
              (fun u _ => by
              split_ifs
              · exact hw.1 u
              · exact le_rfl) (Finset.mem_univ z))
        _ ≤ 1 := hw.2 x
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro w hw
      exact ⟨hw.1, hbound w hw⟩)
    have hn : K.Nonempty := ⟨fun _ => 0, (fun _ => le_rfl), by simp⟩
    obtain ⟨w,hw,hmax⟩ := hk.exists_isMaxOn hn
      (show Continuous (fun w : Z → ℝ => ∑ z, w z) by fun_prop).continuousOn
    exact ⟨w,(fun z => ⟨hw.1 z,hbound w hw z⟩),hw.2,
      fun v hv hc => hmax ⟨hv,hc⟩⟩

open Classical in
/-- Actual row-image incidence admits equal real cover and packing optima.
Both optimizing comparisons range over every real feasible competitor. -/
theorem row_image_real_duality {X Y Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ lam : X → ℝ, ∃ w : Z → ℝ,
      (∀ x, 0 ≤ lam x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, lam x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  classical
  obtain ⟨lam,hlam,hcover,hmin⟩ := (row_image_real_extrema φ hφ).1
  let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
  let τ : ℝ := ∑ x, lam x
  have hτ : 0 < τ := by
    have hz := hcover (Classical.arbitrary Z)
    have hs : (∑ x, if A x (Classical.arbitrary Z) then lam x else 0) ≤ τ := by
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      · exact le_rfl
      · exact (hlam x).1
    linarith
  let γ := τ⁻¹
  have hγ : 0 < γ := inv_pos.mpr hτ
  let L : (X → ℝ) →ₗ[ℝ] (Z → ℝ) := {
    toFun := fun p z => ∑ x, if A x z then p x else 0
    map_add' := by
      intro p q
      funext z
      change (∑ x, if A x z then p x + q x else 0) =
        (∑ x, if A x z then p x else 0) + ∑ x, if A x z then q x else 0
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    map_smul' := by
      intro c p
      funext z
      change (∑ x, if A x z then c * p x else 0) =
        c * ∑ x, if A x z then p x else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp }
  let K := L '' stdSimplex ℝ X
  let U : Set (Z → ℝ) := {v | ∀ z, γ < v z}
  have hUeq : U = ⋂ z, {v : Z → ℝ | γ < v z} := by
    ext v; simp [U]
  have hUconv : Convex ℝ U := by
    rw [hUeq]
    apply convex_iInter
    intro z
    exact (show Convex ℝ (Set.Ioi γ) from convex_Ioi γ).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Z => ℝ) z)
  have hUopen : IsOpen U := by
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun z => isOpen_lt continuous_const (continuous_apply z))
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ X).linear_image L
  have hdisj : Disjoint U K := by
    apply Set.disjoint_left.mpr
    intro k hkU hkK
    obtain ⟨p,hp,rfl⟩ := hkK
    let V := Finset.univ.image (L p)
    have hV : V.Nonempty := ⟨L p (Classical.arbitrary Z), Finset.mem_image.mpr
      ⟨Classical.arbitrary Z,Finset.mem_univ _,rfl⟩⟩
    let β := V.min' hV
    have hγβ : γ < β := by
      obtain ⟨z,hz,hval⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
      change γ < V.min' hV
      rw [← hval]
      exact hkU z
    have hβ : 0 < β := hγ.trans hγβ
    have hβle : ∀ z, β ≤ L p z := fun z => Finset.min'_le V _
      (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩)
    have hμcover : ∀ z, 1 ≤ ∑ x, if A x z then p x / β else 0 := by
      intro z
      have he : (∑ x, if A x z then p x / β else 0) = L p z / β := by
        dsimp [L]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      rw [he]
      exact (le_div_iff₀ hβ).mpr (by simpa using hβle z)
    have hm := hmin (fun x => p x / β) (fun x => div_nonneg (hp.1 x) hβ.le) hμcover
    have hsum : (∑ x, p x / β) = β⁻¹ := by rw [← Finset.sum_div, hp.2, one_div]
    have hlt : β⁻¹ < τ := by
      have hh := (inv_lt_inv₀ hβ hγ).mpr hγβ
      simpa [γ] using hh
    rw [hsum] at hm
    exact (not_lt_of_ge hm hlt)
  obtain ⟨f,u,hfu,hfk⟩ := geometric_hahn_banach_open hUconv hUopen hKconv hdisj
  let a : Z → ℝ := fun z => - f (Pi.single z 1)
  have frep : ∀ v : Z → ℝ, f v = ∑ z, f (Pi.single z 1) * v z := by
    intro v
    have hv : v = ∑ z, v z • (Pi.single z 1) := by
      funext z
      simp [Finset.sum_apply,Pi.single_apply]
    calc
      f v = f (∑ z, v z • Pi.single z 1) := congrArg f hv
      _ = ∑ z, f (Pi.single z 1) * v z := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro z hz
        simp [map_smul,smul_eq_mul,mul_comm]
  have ha : ∀ z, 0 ≤ a z := by
    intro z
    change 0 ≤ - f (Pi.single z 1)
    apply neg_nonneg.mpr
    by_contra hn
    have hf : 0 < f (Pi.single z 1) := lt_of_not_ge hn
    let v₀ : Z → ℝ := fun _ => γ + 1
    have h₀ : v₀ ∈ U := by intro j; dsimp [v₀]; linarith
    have hbase := hfu v₀ h₀
    let t := (u - f v₀ + 1) / f (Pi.single z 1)
    have ht : 0 ≤ t := div_nonneg (by linarith) hf.le
    have hv : v₀ + t • Pi.single z 1 ∈ U := by
      intro j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hj : j = z
      · subst j; simp [v₀] <;> linarith
      · simp [v₀,Pi.single_eq_of_ne hj]
    have hsep := hfu _ hv
    have he : f (v₀ + t • Pi.single z 1) = u + 1 := by
      rw [map_add,map_smul]
      change f v₀ + ((u - f v₀ + 1) / f (Pi.single z 1)) * f (Pi.single z 1) = u + 1
      field_simp <;> ring
    linarith
  let S := ∑ z, a z
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ => ha z)
    by_contra hn
    have hzero : S = 0 := le_antisymm (le_of_not_gt hn) hS0
    have haz : ∀ z, a z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => ha z)).mp hzero z (Finset.mem_univ z)
    have hfzero : ∀ v : Z → ℝ, f v = 0 := by
      intro v
      rw [frep]
      have he : ∀ z, f (Pi.single z 1) = 0 := fun z => neg_eq_zero.mp (haz z)
      simp [he]
    obtain ⟨x,y,hxy⟩ := hφ (Classical.arbitrary Z)
    have hleft := hfu (fun _ => γ + 1) (by intro z; linarith)
    have hright := hfk (L (Pi.single x 1))
      (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    rw [hfzero] at hleft hright
    linarith
  have hb : ∀ k ∈ K, (∑ z, a z * k z) ≤ γ * S := by
    intro k hk
    by_contra hn
    have hg : γ * S < ∑ z, a z * k z := lt_of_not_ge hn
    let ε := ((∑ z, a z * k z) / S - γ) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      have hgt : γ < (∑ z, a z * k z) / S := (lt_div_iff₀ hS).mpr hg
      linarith
    have hv : (fun _ : Z => γ + ε) ∈ U := by intro z; linarith
    have hleft := hfu _ hv
    have hright := hfk k hk
    rw [frep] at hleft hright
    have hfconst : (∑ z, f (Pi.single z 1) * (γ + ε)) = -(S * (γ + ε)) := by
      rw [Finset.sum_mul]
      simp [a,Finset.sum_neg_distrib]
    have hfkneg : (∑ z, f (Pi.single z 1) * k z) = -(∑ z, a z * k z) := by
      dsimp [a]
      simp [Finset.sum_neg_distrib]
    rw [hfconst] at hleft
    rw [hfkneg] at hright
    have hεeq : S * ε = ((∑ z, a z * k z) - S * γ) / 2 := by
      dsimp [ε]; field_simp
    nlinarith
  let w : Z → ℝ := fun z => a z / (γ * S)
  have hw : ∀ z, 0 ≤ w z := fun z => div_nonneg (ha z) (mul_pos hγ hS).le
  have hload : ∀ x, (∑ z, if A x z then w z else 0) ≤ 1 := by
    intro x
    have hbcol := hb (L (Pi.single x 1)) (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    have he : (∑ z, if A x z then w z else 0) =
        (∑ z, a z * L (Pi.single x 1) z) / (γ * S) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      have hL : L (Pi.single x 1) z = if A x z then 1 else 0 := by
        dsimp [L]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b hb hbx
          simp [Pi.single_eq_of_ne hbx]
        · simp
      rw [hL]
      by_cases har : A x z <;> simp [har,w]
    rw [he]
    exact (div_le_one (mul_pos hγ hS)).mpr hbcol
  have heq : (∑ z, w z) = τ := by
    dsimp [w]
    rw [← Finset.sum_div]
    change S / (γ * S) = τ
    dsimp [γ]
    field_simp
  have hweak : ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
      (∀ x, (∑ z, if A x z then v z else 0) ≤ 1) → (∑ z, v z) ≤ τ := by
    intro v hv hvl
    calc
      (∑ z, v z) = ∑ z, v z * 1 := by simp
      _ ≤ ∑ z, v z * (∑ x, if A x z then lam x else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hcover z) (hv z)
      _ = ∑ x, lam x * (∑ z, if A x z then v z else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro z hz
        split_ifs <;> ring
      _ ≤ ∑ x, lam x * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hvl x) (hlam x).1
      _ = τ := by simp [τ]
  refine ⟨lam,w,(fun x => (hlam x).1),hcover,hw,hload,heq.symm,hmin,?_⟩
  intro v hv hvl
  rw [heq]
  exact hweak v hv hvl

open Classical in
/-- Every real direction annihilated by the original active normals at an extreme point vanishes. -/
theorem active_constraint_kernel_zero {I J : Type*} [Fintype I] [Fintype J]
    (a : J → (I → ℝ) →ₗ[ℝ] ℝ) (b : J → ℝ) (v : I → ℝ)
    (hv : v ∈ Set.extremePoints ℝ {u : I → ℝ | ∀ j, a j u ≤ b j})
    (d : I → ℝ) (hd : ∀ j, a j v = b j → a j d = 0) : d = 0 := by
  classical
  let δ : J → ℝ := fun j => if a j v = b j then 1 else
    (b j - a j v) / (|a j d| + 1)
  have hδ : ∀ j, 0 < δ j := by
    intro j
    dsimp [δ]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hv.1 j) h)) (by positivity)
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let ε := S.min' hS
  have hε : 0 < ε := by
    have ht : ε ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]; exact zero_lt_one
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ht
      rw [← hj]; exact hδ j
  have hεle : ∀ j, ε ≤ δ j := fun j => Finset.min'_le S _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hfeas : ∀ t : ℝ, |t| ≤ ε → ∀ j, a j (v + t • d) ≤ b j := by
    intro t ht j
    rw [map_add,map_smul]
    change a j v + t * a j d ≤ b j
    by_cases hj : a j v = b j
    · rw [hd j hj, mul_zero, add_zero, hj]
    · have hs : ε * (|a j d| + 1) ≤ b j - a j v := by
        apply (le_div_iff₀ (by positivity : 0 < |a j d| + 1)).mp
        simpa [δ,hj] using hεle j
      have hab : |t * a j d| ≤ ε * |a j d| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      have hu := le_abs_self (t * a j d)
      have ha := abs_nonneg (a j d)
      nlinarith
  have hp := hfeas ε (by rw [abs_of_pos hε])
  have hm := hfeas (-ε) (by rw [abs_neg,abs_of_pos hε])
  have hmid : v ∈ openSegment ℝ (v + ε • d) (v + (-ε) • d) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have he := hv.2 hp hm hmid
  apply funext
  intro i
  have hi := congrFun he i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
  change d i = 0
  have hz : ε * d i = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hε)



/-- An extreme point of finite original rational inequalities has rational coordinates. -/
theorem rational_extreme_point {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℚ) (b : J → ℚ) (v : I → ℝ)
    (hv : v ∈ Set.extremePoints ℝ
      {u : I → ℝ | ∀ j, (∑ i, (A j i : ℝ) * u i) ≤ (b j : ℝ)}) :
    ∃ q : I → ℚ, (fun i => (q i : ℝ)) = v := by
  classical
  let a : J → (I → ℝ) →ₗ[ℝ] ℝ := fun j =>
    (LinearMap.proj j).comp (Matrix.mulVecLin (fun j i => (A j i : ℝ)))
  let K := {j : J // a j v = (b j : ℝ)}
  let M : Matrix K I ℚ := fun j i => A j.val i
  let N : Matrix K I ℝ := fun j i => (M j i : ℝ)
  let c : K → ℚ := fun j => b j.val
  have hN : ∀ d : I → ℝ, N.mulVec d = 0 → d = 0 := by
    intro d hd
    apply active_constraint_kernel_zero a (fun j => (b j : ℝ)) v hv d
    intro j hj
    have h := congrFun hd (⟨j,hj⟩ : K)
    change (∑ i, (A j i : ℝ) * d i) = 0
    simpa [N,M,Matrix.mulVec,dotProduct] using h
  have hM : ∀ d : I → ℚ, M.mulVec d = 0 → d = 0 := by
    intro d hd
    have hr : N.mulVec (fun i => (d i : ℝ)) = 0 := by
      funext j
      have h := congrArg (fun t : ℚ => (t : ℝ)) (congrFun hd j)
      simpa [N,Matrix.mulVec,dotProduct] using h
    have hh := hN _ hr
    funext i
    have hi := congrFun hh i
    change (d i : ℝ) = 0 at hi
    change d i = 0
    exact_mod_cast hi
  have hG : Function.Injective (N.transpose * N).mulVec := by
    change Function.Injective (N.transpose * N).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot'.mpr (by simpa only [Matrix.mulVecLin_apply] using hN)
  have hB : Function.Injective (M.transpose * M).mulVec := by
    change Function.Injective (M.transpose * M).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot'.mpr (by simpa only [Matrix.mulVecLin_apply] using hM)
  obtain ⟨q,hq⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hB)) (M.transpose.mulVec c)
  refine ⟨q,hG ?_⟩
  have hvN : N.mulVec v = fun j => (c j : ℝ) := by
    funext j
    exact j.property
  have hqR : (N.transpose * N).mulVec (fun i => (q i : ℝ)) =
      N.transpose.mulVec (fun j => (c j : ℝ)) := by
    funext i
    have hh := congrArg (fun t : ℚ => (t : ℝ)) (congrFun hq i)
    change (∑ k, (∑ j, (M j i : ℝ) * (M j k : ℝ)) * (q k : ℝ)) =
      ∑ j, (M j i : ℝ) * (c j : ℝ)
    simpa [Matrix.mulVec,Matrix.mul_apply,Matrix.transpose_apply,dotProduct] using hh
  rw [hqR, ← Matrix.mulVec_mulVec, hvN]

private theorem rational_point_on_compact_face {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℚ) (b : J → ℚ) (F : Set (I → ℝ))
    (hcompact : IsCompact F) (hne : F.Nonempty)
    (hexposed : IsExposed ℝ
      {u : I → ℝ | ∀ j, (∑ i, (A j i : ℝ) * u i) ≤ (b j : ℝ)} F) :
    ∃ q : I → ℚ, (fun i => (q i : ℝ)) ∈ F := by
  obtain ⟨v,hv⟩ := hcompact.extremePoints_nonempty hne
  obtain ⟨q,hq⟩ := rational_extreme_point A b v
    (hexposed.isExtreme.extremePoints_subset_extremePoints hv)
  exact ⟨q, hq.symm ▸ hv.1⟩

open Classical in
/-- Equal rational actual row-image certificates attain both optima against all real competitors. -/
theorem row_image_rational_duality {X Y Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ lam : X → ℚ, ∃ w : Z → ℚ,
      (∀ x, 0 ≤ lam x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, lam x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, (lam x : ℝ)) ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, (w z : ℝ)) := by
  classical
  obtain ⟨lam,w,hl,hcover,hw,hpack,heq,hmin,hmax⟩ := row_image_real_duality φ hφ
  let AP : Matrix (X ⊕ Z) X ℚ := fun j i => match j with
    | .inl x => if i = x then -1 else 0
    | .inr z => if (∃ y, φ i y = z) then -1 else 0
  let bP : X ⊕ Z → ℚ := fun j => match j with
    | .inl _ => 0
    | .inr _ => -1
  let AD : Matrix (Z ⊕ X) Z ℚ := fun j i => match j with
    | .inl z => if i = z then -1 else 0
    | .inr x => if (∃ y, φ x y = i) then 1 else 0
  let bD : Z ⊕ X → ℚ := fun j => match j with
    | .inl _ => 0
    | .inr _ => 1
  let P : Set (X → ℝ) := {u | ∀ j, (∑ i, (AP j i : ℝ) * u i) ≤ (bP j : ℝ)}
  let D : Set (Z → ℝ) := {u | ∀ j, (∑ i, (AD j i : ℝ) * u i) ≤ (bD j : ℝ)}
  have ep : ∀ u : X → ℝ, u ∈ P ↔ (∀ x, 0 ≤ u x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then u x else 0) := by
    intro u
    have row : ∀ z, (∑ i, (AP (.inr z) i : ℝ) * u i) =
        -(∑ i, if (∃ y, φ i y = z) then u i else 0) := by
      intro z
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : ∃ y, φ i y = z <;> simp [AP,h]
    have diag : ∀ x, (∑ i, (AP (.inl x) i : ℝ) * u i) = -u x := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [AP]
      · intro i hi hn; simp [AP,hn]
      · simp
    constructor
    · intro hu
      refine ⟨fun x => ?_, fun z => ?_⟩
      · have hh := hu (.inl x)
        simpa [bP,diag] using hh
      · have hh := hu (.inr z)
        rw [row] at hh
        simpa [bP] using hh
    · rintro ⟨hu,hc⟩ j
      cases j with
      | inl x => simpa [bP,diag] using hu x
      | inr z => rw [row]; simpa [bP] using hc z
  have ed : ∀ u : Z → ℝ, u ∈ D ↔ (∀ z, 0 ≤ u z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then u z else 0) ≤ 1) := by
    intro u
    have row : ∀ x, (∑ i, (AD (.inr x) i : ℝ) * u i) =
        ∑ i, if (∃ y, φ x y = i) then u i else 0 := by
      intro x
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : ∃ y, φ x y = i <;> simp [AD,h]
    have diag : ∀ z, (∑ i, (AD (.inl z) i : ℝ) * u i) = -u z := by
      intro z
      rw [Finset.sum_eq_single z]
      · simp [AD]
      · intro i hi hn; simp [AD,hn]
      · simp
    constructor
    · intro hu
      refine ⟨fun z => ?_, fun x => ?_⟩
      · have hh := hu (.inl z)
        simpa [bD,diag] using hh
      · have hh := hu (.inr x)
        rw [row] at hh
        simpa [bD] using hh
    · rintro ⟨hu,hc⟩ j
      cases j with
      | inl z => simpa [bD,diag] using hu z
      | inr x => rw [row]; simpa [bD] using hc x
  have hPc : IsClosed P := by
    have hp : P = ⋂ j, {u : X → ℝ | (∑ i, (AP j i : ℝ) * u i) ≤ (bP j : ℝ)} := by
      ext u; simp [P]
    rw [hp]
    exact isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const)
  have hDc : IsClosed D := by
    have hp : D = ⋂ j, {u : Z → ℝ | (∑ i, (AD j i : ℝ) * u i) ≤ (bD j : ℝ)} := by
      ext u; simp [D]
    rw [hp]
    exact isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const)
  let FP : Set (X → ℝ) := {u | u ∈ P ∧ (∑ x, u x) = ∑ x, lam x}
  let FD : Set (Z → ℝ) := {u | u ∈ D ∧ (∑ z, u z) = ∑ z, w z}
  have hlam : lam ∈ P := (ep lam).mpr ⟨hl,hcover⟩
  have hwD : w ∈ D := (ed w).mpr ⟨hw,hpack⟩
  have hFPc : IsClosed FP := hPc.inter (isClosed_eq (by fun_prop) continuous_const)
  have hFDc : IsClosed FD := hDc.inter (isClosed_eq (by fun_prop) continuous_const)
  have hFPk : IsCompact FP := isCompact_Icc.of_isClosed_subset hFPc (by
    intro u hu
    have hn := ((ep u).mp hu.1).1
    refine ⟨hn,fun x => ?_⟩
    change u x ≤ ∑ x, lam x
    rw [← hu.2]
    exact Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ x))
  have hFDk : IsCompact FD := isCompact_Icc.of_isClosed_subset hFDc (by
    intro u hu
    obtain ⟨hn,hc⟩ := (ed u).mp hu.1
    refine ⟨hn,fun z => ?_⟩
    obtain ⟨x,y,hxy⟩ := hφ z
    have ha : ∃ y, φ x y = z := ⟨y,hxy⟩
    calc
      u z = (if (∃ y, φ x y = z) then u z else 0) := by simp [ha]
      _ ≤ ∑ t, if (∃ y, φ x y = t) then u t else 0 :=
        Finset.single_le_sum (f := fun t => if (∃ y, φ x y = t) then u t else 0)
          (fun t _ => by split_ifs; exact hn t; exact le_rfl) (Finset.mem_univ z)
      _ ≤ 1 := hc x)
  have hFPexp : IsExposed ℝ P FP := by
    intro _
    refine ⟨-(∑ x : X, ContinuousLinearMap.proj x), ?_⟩
    ext u
    constructor
    · rintro ⟨hu,he⟩
      refine ⟨hu,fun t ht => ?_⟩
      have hm := hmin t ((ep t).mp ht).1 ((ep t).mp ht).2
      simp only [neg_apply, sum_apply,
        ContinuousLinearMap.proj_apply]
      linarith
    · rintro ⟨hu,hm⟩
      have hh := hm lam hlam
      have hlower := hmin u ((ep u).mp hu).1 ((ep u).mp hu).2
      simp only [neg_apply, sum_apply,
        ContinuousLinearMap.proj_apply] at hh
      exact ⟨hu, by linarith⟩
  have hFDexp : IsExposed ℝ D FD := by
    intro _
    refine ⟨∑ z : Z, ContinuousLinearMap.proj z, ?_⟩
    ext u
    constructor
    · rintro ⟨hu,he⟩
      refine ⟨hu,fun t ht => ?_⟩
      have hm := hmax t ((ed t).mp ht).1 ((ed t).mp ht).2
      simp only [sum_apply, ContinuousLinearMap.proj_apply]
      linarith
    · rintro ⟨hu,hm⟩
      have hh := hm w hwD
      have hupper := hmax u ((ed u).mp hu).1 ((ed u).mp hu).2
      simp only [sum_apply, ContinuousLinearMap.proj_apply] at hh
      exact ⟨hu, by linarith⟩
  obtain ⟨q,hq⟩ := rational_point_on_compact_face AP bP FP hFPk ⟨lam,hlam,rfl⟩ hFPexp
  obtain ⟨r,hr⟩ := rational_point_on_compact_face AD bD FD hFDk ⟨w,hwD,rfl⟩ hFDexp
  have hpq := (ep (fun x => (q x : ℝ))).mp hq.1
  have hdr := (ed (fun z => (r z : ℝ))).mp hr.1
  refine ⟨q,r,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x; exact_mod_cast hpq.1 x
  · intro z
    have hc : ((∑ x, if (∃ y, φ x y = z) then q x else 0 : ℚ) : ℝ) =
        ∑ x, if (∃ y, φ x y = z) then (q x : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    have hh := hpq.2 z
    rw [← hc] at hh
    exact_mod_cast hh
  · intro z; exact_mod_cast hdr.1 z
  · intro x
    have hc : ((∑ z, if (∃ y, φ x y = z) then r z else 0 : ℚ) : ℝ) =
        ∑ z, if (∃ y, φ x y = z) then (r z : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp
    have hh := hdr.2 x
    rw [← hc] at hh
    exact_mod_cast hh
  · have hh : (∑ x, (q x : ℝ)) = ∑ z, (r z : ℝ) := hq.2.trans (heq.trans hr.2.symm)
    exact_mod_cast hh
  · intro μ hn hc
    rw [hq.2]
    exact hmin μ hn hc
  · intro v hn hc
    rw [hr.2]
    exact hmax v hn hc


/-- A rational optimal cover supplied by the existing real-optimal certificate theorem. -/
noncomputable def optimalRowCover {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) : X → ℚ := by
  classical
  letI : Nonempty Z := ⟨φ (Classical.arbitrary X) (Classical.arbitrary Y)⟩
  exact Classical.choose (row_image_rational_duality φ hφ)

noncomputable def rowCoverNumber {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) : ℝ :=
  ∑ x, (optimalRowCover φ hφ x : ℝ)

open Classical in
theorem optimal_row_cover_spec {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ w : Z → ℚ,
      (∀ x, 0 ≤ optimalRowCover φ hφ x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then optimalRowCover φ hφ x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, optimalRowCover φ hφ x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        rowCoverNumber φ hφ ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ rowCoverNumber φ hφ) := by
  classical
  letI : Nonempty Z := ⟨φ (Classical.arbitrary X) (Classical.arbitrary Y)⟩
  obtain ⟨w,hn,hc,hw,hl,he,hm,hmax⟩ := Classical.choose_spec (row_image_rational_duality φ hφ)
  refine ⟨w,hn,hc,hw,hl,he,hm,?_⟩
  intro v hv hc
  have h := hmax v hv hc
  have eq : (∑ z, (w z : ℝ)) = rowCoverNumber φ hφ := by
    dsimp [rowCoverNumber,optimalRowCover]
    exact_mod_cast he.symm
  rwa [eq] at h

open Classical in
theorem product_cover_value {J : Type*} [Fintype J] [DecidableEq J] {X Y Z : J → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (hφ : ∀ i z, ∃ x y, φ i x y = z)
    (hprod : ∀ z : (∀ i, Z i), ∃ (x : ∀ i, X i) (y : ∀ i, Y i), (fun i => φ i (x i) (y i)) = z) :
    rowCoverNumber (fun (x : ∀ i, X i) (y : ∀ i, Y i) i => φ i (x i) (y i)) hprod =
      ∏ i, rowCoverNumber (φ i) (hφ i) := by
  classical
  choose dual hn hc hd hl he hm hmax using fun i => optimal_row_cover_spec (φ i) (hφ i)
  let lam : (∀ i, X i) → ℝ := fun x => ∏ i, (optimalRowCover (φ i) (hφ i) (x i) : ℝ)
  let v : (∀ i, Z i) → ℝ := fun z => ∏ i, (dual i (z i) : ℝ)
  have incidence (x : ∀ i, X i) (z : ∀ i, Z i) :
      (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) ↔ ∀ i, ∃ y, φ i (x i) y = z i := by
    constructor
    · rintro ⟨y,hy⟩ i; exact ⟨y i,congrFun hy i⟩
    · intro h
      choose y hy using h
      exact ⟨y,funext hy⟩
  have hln : ∀ x, 0 ≤ lam x := fun x => Finset.prod_nonneg
    (fun i _ => by exact_mod_cast hn i (x i))
  have hvn : ∀ z, 0 ≤ v z := fun z => Finset.prod_nonneg
    (fun i _ => by exact_mod_cast hd i (z i))
  have hcoverage : ∀ z : (∀ i, Z i), 1 ≤ ∑ x, if (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) then lam x else 0 := by
    intro z
    have eq : (∑ x, if (∀ i, ∃ y, φ i (x i) y = z i) then lam x else 0) =
        ∏ i, ∑ x, if (∃ y, φ i x y = z i) then (optimalRowCover (φ i) (hφ i) x : ℝ) else 0 := by
      simp only [lam,← Fintype.prod_ite_zero]
      exact (Fintype.prod_sum (fun i x => if (∃ y, φ i x y = z i) then
        (optimalRowCover (φ i) (hφ i) x : ℝ) else 0)).symm
    simp_rw [incidence]
    rw [eq]
    apply Finset.one_le_prod
    intro i hi
    have hh : (1 : ℝ) ≤ ((∑ x, if (∃ y, φ i x y = z i) then
        optimalRowCover (φ i) (hφ i) x else 0 : ℚ) : ℝ) := by exact_mod_cast hc i (z i)
    have eq : ((∑ x, if (∃ y, φ i x y = z i) then
        optimalRowCover (φ i) (hφ i) x else 0 : ℚ) : ℝ) =
        ∑ x, if (∃ y, φ i x y = z i) then (optimalRowCover (φ i) (hφ i) x : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx; split_ifs <;> simp
    rwa [eq] at hh
  have hpacking : ∀ x : (∀ i, X i), (∑ z, if (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) then v z else 0) ≤ 1 := by
    intro x
    have eq : (∑ z, if (∀ i, ∃ y, φ i (x i) y = z i) then v z else 0) =
        ∏ i, ∑ z, if (∃ y, φ i (x i) y = z) then (dual i z : ℝ) else 0 := by
      simp only [v,← Fintype.prod_ite_zero]
      exact (Fintype.prod_sum (fun i z => if (∃ y, φ i (x i) y = z) then
        (dual i z : ℝ) else 0)).symm
    simp_rw [incidence]
    rw [eq]
    apply Finset.prod_le_one
    · intro i hi; exact Finset.sum_nonneg (fun z _ => by split_ifs; exact_mod_cast hd i z; exact le_rfl)
    · intro i hi
      have hh : ((∑ z, if (∃ y, φ i (x i) y = z) then dual i z else 0 : ℚ) : ℝ) ≤ 1 := by
        exact_mod_cast hl i (x i)
      have eq : ((∑ z, if (∃ y, φ i (x i) y = z) then dual i z else 0 : ℚ) : ℝ) =
          ∑ z, if (∃ y, φ i (x i) y = z) then (dual i z : ℝ) else 0 := by
        rw [Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro z hz; split_ifs <;> simp
      rwa [eq] at hh
  have hlamval : (∑ x, lam x) = ∏ i, rowCoverNumber (φ i) (hφ i) := by
    exact (Fintype.prod_sum (fun i x => (optimalRowCover (φ i) (hφ i) x : ℝ))).symm
  have hvval : (∑ z, v z) = ∏ i, rowCoverNumber (φ i) (hφ i) := by
    rw [show (∑ z, v z) = ∏ i, ∑ z, (dual i z : ℝ) from (Fintype.prod_sum (fun i z => (dual i z : ℝ))).symm]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [rowCoverNumber]
    exact_mod_cast (he i).symm
  obtain ⟨pd,pn,pc,pdn,pdc,peq,pmin,pmax⟩ :=
    optimal_row_cover_spec (fun (x : ∀ i, X i) (y : ∀ i, Y i) i => φ i (x i) (y i)) hprod
  apply le_antisymm
  · apply le_trans (pmin lam hln ?_) hlamval.le
    intro z
    convert hcoverage z using 1
    congr 1
    funext x
    split_ifs <;> rfl
  · apply le_trans hvval.ge (pmax v hvn ?_)
    intro x
    convert hpacking x using 1
    congr 1
    funext z
    split_ifs <;> rfl

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates
