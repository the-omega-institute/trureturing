/- GID: D5/S3/Analytic/WeightedCapacity/InfiniteActiveNonIsolation
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/InfiniteActiveNonIsolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinite active capacities make every finite state non-isolated in the rational probe topology. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.InfiniteActiveNonIsolation

open DyadicTailFilling ProbeTopologySequences Set Filter TopologicalSpace
open scoped Topology BigOperators

/-- Finite coordinate constraints and rational character balls centered at a finite state. -/
def basicNhd (A : ℕ → ℕ) (u : B A) (I : Finset ℕ) {m : ℕ}
    (rs : Fin m → ℕ → ℚ) (eps : Fin m → ℚ) : Set (B A) :=
  {w | (∀ n ∈ I, w.val n = u.val n) ∧
    ∀ a, dist (chi (rs a) w) (chi (rs a) u) < (eps a : ℝ)}

/-- Infinitely many active capacities make every finite state non-isolated. More precisely,
for each finite family of coordinate constraints and positive rational character tolerances,
there is a positive integer Q with reciprocal below every tolerance and an increasing list of
Q^m unused active indices whose nonempty consecutive block adds a different state in the
prescribed neighborhood. List positions are numbered from zero, so the block is [i,j). -/
theorem not_isolated_of_infinite_active (A : ℕ → ℕ)
    (hA : Set.Infinite {n : ℕ | 0 < A n}) (u : B A) :
    (∀ U : Set (B A), U ∈ @nhds _ (tauPlus A) u → ∃ w ∈ U, w ≠ u) ∧
    (∀ (I : Finset ℕ) (m : ℕ) (rs : Fin m → ℕ → ℚ) (eps : Fin m → ℚ),
      (∀ a, 0 < eps a) →
      ∃ Q : ℕ, 0 < Q ∧ (∀ a, 1 / (Q : ℝ) < (eps a : ℝ)) ∧
        ∃ n : ℕ → ℕ, StrictMonoOn n (Set.Iio (Q ^ m)) ∧
          (∀ h < Q ^ m, 0 < A (n h) ∧ n h ∉ I ∧ (u.val (n h) : ℕ) = 0) ∧
          ∃ i j : ℕ, i < j ∧ j ≤ Q ^ m ∧
            ∃ w ∈ basicNhd A u I rs eps, w ≠ u ∧
              ∀ k, (w.val k : ℕ) = (u.val k : ℕ) +
                ∑ h ∈ Finset.Ico i j, if k = n h then 1 else 0) := by
  classical
  have hpigeon (m Q : ℕ) (hQ : 0 < Q) (eps : Fin m → ℚ)
      (hsmall : ∀ a, 1 / (Q : ℝ) < (eps a : ℝ))
      (z : ℕ → Fin m → AddCircle (1 : ℝ)) :
      ∃ i j : ℕ, i < j ∧ j ≤ Q ^ m ∧
        ∀ a, dist (∑ h ∈ Finset.Ico i j, z h a) 0 < (eps a : ℝ) := by
    classical
    let p (k : ℕ) (a : Fin m) := ∑ h ∈ Finset.range k, z h a
    let x (k : ℕ) (a : Fin m) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (p k a)).val
    have hx (k : ℕ) (a : Fin m) : 0 ≤ x k a ∧ x k a < 1 := by
      simpa [x] using (AddCircle.equivIco (1 : ℝ) 0 (p k a)).property
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    let box (k : Fin (Q ^ m + 1)) (a : Fin m) : Fin Q :=
      ⟨⌊(Q : ℝ) * x k a⌋₊, (Nat.floor_lt (mul_nonneg hQr.le (hx k a).1)).mpr
        (by nlinarith [(hx k a).2])⟩
    obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt box
      (by simp only [Fintype.card_fun, Fintype.card_fin]; omega)
    have hpair (i j : Fin (Q ^ m + 1)) (hij : i < j) (heq : box i = box j) :
        ∀ a, dist (∑ h ∈ Finset.Ico i.val j.val, z h a) 0 < (eps a : ℝ) := by
      intro a
      have hf : ⌊(Q : ℝ) * x i a⌋₊ = ⌊(Q : ℝ) * x j a⌋₊ :=
        congrArg Fin.val (congrFun heq a)
      have hli := Nat.floor_le (mul_nonneg hQr.le (hx i a).1)
      have hlj := Nat.floor_le (mul_nonneg hQr.le (hx j a).1)
      have hui := Nat.lt_floor_add_one ((Q : ℝ) * x i a)
      have huj := Nat.lt_floor_add_one ((Q : ℝ) * x j a)
      rw [hf] at hli hui
      have hd : |x j a - x i a| < 1 / (Q : ℝ) := by
        apply abs_lt.mpr
        constructor
        · have hh : x i a - x j a < 1 / (Q : ℝ) := by
            apply (lt_div_iff₀ hQr).mpr
            nlinarith
          linarith
        · apply (lt_div_iff₀ hQr).mpr
          nlinarith
      have hcoe (k : ℕ) : ((x k a : ℝ) : AddCircle (1 : ℝ)) = p k a :=
        AddCircle.coe_equivIco
      calc
        dist (∑ h ∈ Finset.Ico i.val j.val, z h a) 0 =
            ‖((x j a - x i a : ℝ) : AddCircle (1 : ℝ))‖ := by
          rw [Finset.sum_Ico_eq_sub _ hij.le, dist_zero_right, AddCircle.coe_sub, hcoe, hcoe]
        _ ≤ |x j a - x i a| := QuotientAddGroup.norm_mk_le_norm
        _ < (eps a : ℝ) := hd.trans (hsmall a)
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i, j, hij, by omega, hpair i j hij heq⟩
    · exact ⟨j, i, hji, by omega, hpair j i hji heq.symm⟩
  have hquant (I : Finset ℕ) (m : ℕ) (rs : Fin m → ℕ → ℚ) (eps : Fin m → ℚ)
      (heps : ∀ a, 0 < eps a) :
      ∃ Q : ℕ, 0 < Q ∧ (∀ a, 1 / (Q : ℝ) < (eps a : ℝ)) ∧
        ∃ n : ℕ → ℕ, StrictMonoOn n (Set.Iio (Q ^ m)) ∧
          (∀ h < Q ^ m, 0 < A (n h) ∧ n h ∉ I ∧ (u.val (n h) : ℕ) = 0) ∧
          ∃ i j : ℕ, i < j ∧ j ≤ Q ^ m ∧
            ∃ w ∈ basicNhd A u I rs eps, w ≠ u ∧
              ∀ k, (w.val k : ℕ) = (u.val k : ℕ) +
                ∑ h ∈ Finset.Ico i j, if k = n h then 1 else 0 := by
    have heps' (a : Fin m) : (0 : ℝ) < eps a := by exact_mod_cast heps a
    choose q hq using fun a => exists_nat_one_div_lt (heps' a)
    let Q := Finset.univ.sup q + 1
    have hQ : 0 < Q := Nat.succ_pos _
    have hsmall (a : Fin m) : 1 / (Q : ℝ) < (eps a : ℝ) := by
      apply lt_of_le_of_lt _ (hq a)
      apply one_div_le_one_div_of_le (by positivity)
      have hle : q a ≤ Finset.univ.sup q := Finset.le_sup (Finset.mem_univ a)
      dsimp [Q]
      exact_mod_cast Nat.add_le_add_right hle 1
    let S : Set ℕ := {n : ℕ | 0 < A n} \ (↑I ∪
      Function.support (fun n => (u.val n : ℕ)))
    have hS : S.Infinite := hA.sdiff (I.finite_toSet.union u.property)
    obtain ⟨n, hnmono, hnS⟩ := Nat.exists_strictMono_subsequence (P := fun n => n ∈ S)
      (fun N => by obtain ⟨n, hn, hN⟩ := hS.exists_gt N; exact ⟨n, hN, hn⟩)
    have hn (h : ℕ) : 0 < A (n h) ∧ n h ∉ I ∧ (u.val (n h) : ℕ) = 0 := by
      simpa [S, Function.support, not_or] using hnS h
    obtain ⟨i, j, hij, hj, hblock⟩ :=
      hpigeon m Q hQ eps hsmall (fun h a => ((rs a (n h) : ℚ) : ℝ))
    let s := (Finset.Ico i j).image n
    have hs (k : ℕ) (hk : k ∈ s) : 0 < A k ∧ k ∉ I ∧ (u.val k : ℕ) = 0 := by
      obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hk
      exact hn h
    have hni : n i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, hij⟩, rfl⟩
    let w : B A := ⟨fun k => if hk : k ∈ s then ⟨1, by have := (hs k hk).1; omega⟩
        else u.val k, by
      apply (s.finite_toSet.union u.property).subset
      intro k hk
      by_cases hks : k ∈ s
      · exact Or.inl hks
      · exact Or.inr (by simpa [Function.support, hks] using hk)⟩
    have hw (k : ℕ) : (w.val k : ℕ) = if k ∈ s then 1 else (u.val k : ℕ) := by
      by_cases hk : k ∈ s <;> simp [w, hk]
    let v (b : B A) : ℕ →₀ ℤ := Finsupp.ofSupportFinite
      (fun k => ((b.val k : ℕ) : ℤ)) (by
        apply b.property.subset
        intro k hk
        change ((b.val k : ℕ) : ℤ) ≠ 0 at hk
        change (b.val k : ℕ) ≠ 0
        exact fun hz => hk (by rw [hz]; rfl))
    have hv (b : B A) (k : ℕ) : v b k = ((b.val k : ℕ) : ℤ) := rfl
    have hvs (b : B A) : (v b).support = b.property.toFinset := by
      ext k
      simp [Finsupp.mem_support_iff, hv]
    let d : ℕ →₀ ℤ := ∑ k ∈ s, Finsupp.single k 1
    have hd (k : ℕ) : d k = if k ∈ s then 1 else 0 := by
      simp [d, Finsupp.single_apply]
    have hvw : v w = v u + d := by
      ext k
      rw [Finsupp.add_apply, hv, hv, hd, hw]
      by_cases hk : k ∈ s
      · simp [hk, (hs k hk).2.2]
      · simp [hk]
    let F (r : ℕ → ℚ) : (ℕ →₀ ℤ) →+ AddCircle (1 : ℝ) := {
      toFun := fun b => (((b.sum fun k a => r k * (a : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ))
      map_zero' := by simp
      map_add' := by
        intro b c
        rw [Finsupp.sum_add_index (by intros; simp) (by intros; push_cast; ring)]
        push_cast
        rfl }
    have hF (r : ℕ → ℚ) (b : B A) : F r (v b) = chi r b := by
      simp [F, Finsupp.sum, hvs, chi, hv]
    have hFd (r : ℕ → ℚ) : F r d =
        ∑ h ∈ Finset.Ico i j, (((r (n h) : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
      change F r (∑ k ∈ s, Finsupp.single k 1) = _
      have hsingle (k : ℕ) : F r (Finsupp.single k 1) =
          (((r k : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by simp [F]
      simp only [map_sum, hsingle]
      exact Finset.sum_image (fun _ _ _ _ h => hnmono.injective h)
    have hchi (a : Fin m) : chi (rs a) w - chi (rs a) u =
        ∑ h ∈ Finset.Ico i j, (((rs a (n h) : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← hF, hvw, map_add, hF, add_sub_cancel_left, hFd]
    refine ⟨Q, hQ, hsmall, n, hnmono.strictMonoOn _, fun h _ => hn h,
      i, j, hij, hj, w, ?_, ?_, ?_⟩
    · constructor
      · intro k hk
        have hks : k ∉ s := fun h => (hs k h).2.1 hk
        simp [w, hks]
      · intro a
        rw [dist_eq_norm, hchi]
        simpa only [dist_zero_right] using hblock a
    · intro heq
      have he := congrArg (fun b : B A => (b.val (n i) : ℕ)) heq
      rw [hw] at he
      simp [hni, (hn i).2.2] at he
    · intro k
      have hsum : (∑ h ∈ Finset.Ico i j, if k = n h then 1 else 0 : ℕ) =
          if k ∈ s then 1 else 0 := by
        rw [← Finset.sum_image (f := fun l => if k = l then (1 : ℕ) else 0)
          (fun _ _ _ _ h => hnmono.injective h)]
        exact Finset.sum_ite_eq _ _ _
      rw [hw, hsum]
      by_cases hk : k ∈ s
      · simp [hk, (hs k hk).2.2]
      · simp [hk]
  refine ⟨?_, hquant⟩
  intro U hU
  have hbasis : ∃ (I : Finset ℕ) (m : ℕ) (rs : Fin m → ℕ → ℚ) (eps : Fin m → ℚ),
      (∀ a, 0 < eps a) ∧ basicNhd A u I rs eps ⊆ U := by
    let Y := (ℕ → AddCircle (1 : ℝ)) × ((ℕ → ℚ) → AddCircle (1 : ℝ))
    let E : B A → Y := fun w => (psi w, fun r => chi r w)
    have htop : tauPlus A = induced E inferInstance := by
      simp only [tauPlus, E, instTopologicalSpaceProd, Pi.topologicalSpace,
        induced_inf, induced_iInf, induced_compose, Function.comp_def]
    rw [htop, nhds_induced, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨V₁, hV₁, V₂, hV₂, hpair⟩ := mem_nhds_prod_iff.mp hV
    rw [nhds_pi, Filter.mem_pi'] at hV₁ hV₂
    obtain ⟨I, O, hO, hOV⟩ := hV₁
    obtain ⟨R, T, hT, hTV⟩ := hV₂
    have hrad (r : ℕ → ℚ) : ∃ e : ℚ, 0 < e ∧
        Metric.ball (chi r u) (e : ℝ) ⊆ T r := by
      obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT r)
      obtain ⟨e, he, heδ⟩ := exists_rat_btwn hδ
      exact ⟨e, by exact_mod_cast he, (Metric.ball_subset_ball heδ.le).trans hδT⟩
    choose e he heT using hrad
    let rs : Fin R.card → ℕ → ℚ := fun a => (R.equivFin.symm a).val
    refine ⟨I, R.card, rs, fun a => e (rs a), fun a => he _, ?_⟩
    intro w hw
    apply hVU
    apply hpair
    constructor
    · apply hOV
      intro k hk
      have hcoord := hw.1 k hk
      change psi w k ∈ O k
      have heq : psi w k = psi u k := by simp only [psi, hcoord]
      rw [heq]
      exact mem_of_mem_nhds (hO k)
    · apply hTV
      intro r hr
      let a : Fin R.card := R.equivFin ⟨r, hr⟩
      have hra : rs a = r := by simp [rs, a]
      apply heT r
      have h := hw.2 a
      simpa only [hra, Metric.mem_ball] using h
  obtain ⟨I, m, rs, eps, heps, hsub⟩ := hbasis
  obtain ⟨Q, _, _, n, _, _, i, j, _, _, w, hw, hne, _⟩ := hquant I m rs eps heps
  exact ⟨w, hsub hw, hne⟩

end D5.S3.Analytic.WeightedCapacity.InfiniteActiveNonIsolation
