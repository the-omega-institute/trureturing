/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Krawtchouk eigenvalues and binomial formulas for Walsh coefficients. -/

import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages
import Mathlib.Data.Finset.Powerset

/-! Regroup ordered Walsh pairs by their two support counts. -/

section

open scoped BigOperators Topology

set_option autoImplicit false

namespace HypercubeWalsh

open Finset

def support {d : ℕ} (a : Cube d) : Finset (Fin d) := univ.filter fun i => a i = true

def weight {d : ℕ} (a : Cube d) : ℕ := (support a).card

def ofSupport {d : ℕ} (s : Finset (Fin d)) : Cube d := fun i => decide (i ∈ s)

@[simp] theorem mem_support {d : ℕ} (a : Cube d) (i : Fin d) :
    i ∈ support a ↔ a i = true := by simp [support]

@[simp] private theorem support_ofSupport {d : ℕ} (s : Finset (Fin d)) :
    support (ofSupport s) = s := by
  ext i
  simp [ofSupport]

@[simp] private theorem ofSupport_support {d : ℕ} (a : Cube d) : ofSupport (support a) = a := by
  ext i
  simp [ofSupport]

private theorem support_injective {d : ℕ} : Function.Injective (support (d := d)) := by
  intro a b h
  simpa using congrArg ofSupport h

@[simp] private theorem support_origin (d : ℕ) : support (origin : Cube d) = ∅ := by
  ext i
  simp [origin]

@[simp] private theorem weight_origin (d : ℕ) : weight (origin : Cube d) = 0 := by simp [weight]

private theorem weight_le {d : ℕ} (a : Cube d) : weight a ≤ d := by
  simpa [weight] using card_le_card (subset_univ (support a))

private theorem weight_split {d : ℕ} (a c : Cube d) :
    weight a = (support a \ support c).card + (support a ∩ support c).card :=
  (card_sdiff_add_card_inter _ _).symm

private theorem weight_xor_split {d : ℕ} (a c : Cube d) :
    weight (xor a c) = (support a \ support c).card + weight c - (support a ∩ support c).card := by
  have h₁ : support (xor a c) \ support c = support a \ support c := by
    ext i
    simp only [mem_sdiff, mem_support, xor]
    cases a i <;> cases c i <;> simp
  have h₂ : support (xor a c) ∩ support c = support c \ (support a ∩ support c) := by
    ext i
    simp only [mem_inter, mem_sdiff, mem_support, xor]
    cases a i <;> cases c i <;> simp
  rw [weight_split (xor a c) c, h₁, h₂, card_sdiff_of_subset inter_subset_right, weight]
  have hle := card_le_card (inter_subset_right : support a ∩ support c ⊆ support c)
  omega

private theorem character_overlap {d : ℕ} (a c : Cube d) :
    character a c = (-1 : ℝ) ^ (support a ∩ support c).card := by
  rw [← Finset.prod_const]
  have hs : support a ∩ support c = univ.filter (fun i => (a i && c i) = true) := by
    ext i
    simp
  rw [hs, Finset.prod_filter]
  rfl

private theorem sum_powerset_card {ι : Type*}
    (s : Finset ι) (f : ℕ → ℝ) :
    ∑ u ∈ s.powerset, f u.card =
      ∑ k ∈ range (s.card + 1), (s.card.choose k : ℝ) * f k := by
  classical
  have hm (u : Finset ι) (hu : u ∈ s.powerset) : u.card ∈ range (s.card + 1) :=
    mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_powerset.1 hu)))
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) hm]
  apply sum_congr rfl
  intro k _
  rw [← powersetCard_eq_filter]
  calc
    _ = ∑ _ ∈ s.powersetCard k, f k := by
      apply sum_congr rfl
      intro u hu
      rw [(mem_powersetCard.1 hu).2]
    _ = _ := by simp [card_powersetCard]

private theorem sum_support_split {d : ℕ} (c : Cube d) (f : ℕ → ℕ → ℝ) :
    (∑ a : Cube d, f (support a \ support c).card (support a ∩ support c).card) =
      ∑ i ∈ range (d - weight c + 1), ∑ j ∈ range (weight c + 1),
        ((d - weight c).choose i : ℝ) * ((weight c).choose j : ℝ) * f i j := by
  let s := (univ : Finset (Fin d)) \ support c
  let t := support c
  have hr : (∑ a : Cube d, f (support a \ support c).card (support a ∩ support c).card) =
      ∑ uv ∈ s.powerset ×ˢ t.powerset, f uv.1.card uv.2.card := by
    refine sum_bij (fun a _ => (support a \ t, support a ∩ t)) ?_ ?_ ?_ ?_
    · intro a _
      simp only [mem_product, mem_powerset]
      exact ⟨by intro i hi; exact mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 hi).2⟩, inter_subset_right⟩
    · intro a _ b _ h
      apply support_injective
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      change support a \ t = support b \ t at h₁
      change support a ∩ t = support b ∩ t at h₂
      rw [← sdiff_union_inter (support a) t, ← sdiff_union_inter (support b) t, h₁, h₂]
    · rintro ⟨u,v⟩ huv
      rcases mem_product.1 huv with ⟨hu,hv⟩
      have hu' : u ⊆ s := mem_powerset.1 hu
      have hv' : v ⊆ t := mem_powerset.1 hv
      refine ⟨ofSupport (u ∪ v), mem_univ _, ?_⟩
      apply Prod.ext
      · simp only [support_ofSupport]
        ext i
        have hui (h : i ∈ u) : i ∉ t := (mem_sdiff.1 (hu' h)).2
        have hvi (h : i ∈ v) : i ∈ t := hv' h
        simp only [mem_sdiff, mem_union]
        tauto
      · simp only [support_ofSupport]
        ext i
        have hui (h : i ∈ u) : i ∉ t := (mem_sdiff.1 (hu' h)).2
        have hvi (h : i ∈ v) : i ∈ t := hv' h
        simp only [mem_inter, mem_union]
        tauto
    · intro _ _
      rfl
  rw [hr, sum_product]
  simp_rw [sum_powerset_card t]
  rw [sum_powerset_card s (fun i => ∑ j ∈ range (t.card + 1), (t.card.choose j : ℝ) * f i j)]
  have hs : s.card = d - weight c := by simp [s, weight, card_sdiff_of_subset (subset_univ _)]
  rw [hs]
  change (∑ i ∈ range (d - weight c + 1),
        ((d - weight c).choose i : ℝ) *
        ∑ j ∈ range (weight c + 1), ((weight c).choose j : ℝ) * f i j) = _
  simp only [mul_sum, mul_assoc]

private theorem sum_by_weight {d : ℕ} (f : ℕ → ℝ) :
    (∑ a : Cube d, f (weight a)) = ∑ h ∈ range (d + 1), (d.choose h : ℝ) * f h := by
  simpa [weight] using sum_support_split (origin : Cube d) (fun i _ => f i)

noncomputable def shellKernel (d : ℕ) (w : ℕ → ℝ)
    (hw : ∀ h ≤ d, 0 ≤ w h) (ht : ∑ h ∈ range (d + 1), w h = 1) : Kernel (Cube d) where
  p y := w (weight y) / d.choose (weight y)
  nonneg y := div_nonneg (hw _ (weight_le y)) (Nat.cast_nonneg _)
  total := by
    rw [sum_by_weight (fun h => w h / (d.choose h : ℝ))]
    calc
      _ = ∑ h ∈ range (d + 1), w h := by
        apply sum_congr rfl
        intro h hh
        have hc : (d.choose h : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hh))).ne'
        field_simp
      _ = 1 := ht

noncomputable def shellEigen (d : ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (d - k + 1), ∑ j ∈ range (k + 1),
    ((d - k).choose i : ℝ) * (k.choose j : ℝ) * (w (i + j) / d.choose (i + j) * (-1 : ℝ) ^ j)

private theorem eigen_shell {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (a : Cube d) :
    eigen (shellKernel d w hw ht) a = shellEigen d w (weight a) := by
  rw [eigen_eq]
  trans ∑ y : Cube d,
    (fun i j => w (i + j) / (d.choose (i + j) : ℝ) * (-1 : ℝ) ^ j)
      (support y \ support a).card (support y ∩ support a).card
  · apply sum_congr rfl
    intro y _
    change w (weight y) / (d.choose (weight y) : ℝ) * character a y = _
    rw [character_comm, character_overlap, weight_split y a]
  · unfold shellEigen
    exact sum_support_split a (fun i j => w (i + j) / (d.choose (i + j) : ℝ) * (-1 : ℝ) ^ j)

/-- Krawtchouk value of order `h` at weight `k`. Terms with `j > h` vanish. -/
def krawtchouk (d k h : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), if j ≤ h then
    (-1 : ℝ) ^ j * (k.choose j : ℝ) * ((d - k).choose (h - j) : ℝ)
  else 0

private theorem sum_choose_diagonal (m j h : ℕ) :
    (∑ i ∈ range (m + 1), if i + j = h then (m.choose i : ℝ) else 0) =
      if j ≤ h then (m.choose (h - j) : ℝ) else 0 := by
  by_cases hj : j ≤ h
  · have he (i : ℕ) : i + j = h ↔ i = h - j := by omega
    simp only [he, ite_eq_left hj, sum_ite_eq']
    by_cases hi : h - j ∈ range (m + 1)
    · simp [hi]
    · have hz : m < h - j := by
        have hn := mt mem_range.2 hi
        omega
      simp [hi, Nat.choose_eq_zero_of_lt hz]
  · rw [ite_eq_right hj]
    apply sum_eq_zero
    intro i _
    exact ite_eq_right (by omega)

private theorem krawtchouk_diagonal (d k h : ℕ) :
    krawtchouk d k h =
      ∑ i ∈ range (d - k + 1), ∑ j ∈ range (k + 1),
        if i + j = h then
          ((d - k).choose i : ℝ) * (k.choose j : ℝ) * (-1 : ℝ) ^ j
        else 0 := by
  rw [sum_comm]
  unfold krawtchouk
  apply sum_congr rfl
  intro j _
  symm
  calc
    _ = ((-1 : ℝ) ^ j * (k.choose j : ℝ)) *
        ∑ i ∈ range (d - k + 1), if i + j = h then ((d - k).choose i : ℝ) else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      split <;> ring
    _ = _ := by rw [sum_choose_diagonal]; split <;> simp

private theorem shellEigen_eq_krawtchouk (d : ℕ) (w : ℕ → ℝ) (k : ℕ) (hk : k ≤ d) :
    shellEigen d w k =
      ∑ h ∈ range (d + 1), w h / (d.choose h : ℝ) * krawtchouk d k h := by
  unfold shellEigen
  simp_rw [krawtchouk_diagonal, mul_sum]
  rw [sum_comm (s := range (d + 1)) (t := range (d - k + 1))]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm (s := range (d + 1)) (t := range (k + 1))]
  apply sum_congr rfl
  intro j hj
  have hh : i + j ∈ range (d + 1) := by
    have hi' := mem_range.1 hi
    have hj' := mem_range.1 hj
    exact mem_range.2 (by omega)
  simp_rw [mul_ite, mul_zero]
  rw [sum_ite_eq, ite_eq_left hh]
  ring

/-- The eigenvalue profile from equation (8) of Ide–Konno–Mano. -/
noncomputable def rho (d : ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ h ∈ range (d + 1), w h / (d.choose h : ℝ) * krawtchouk d k h

theorem eigen_eq_krawtchouk {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (a : Cube d) :
    eigen (shellKernel d w hw ht) a = rho d w (weight a) := by
  rw [eigen_shell, shellEigen_eq_krawtchouk d w _ (weight_le a), rho]

noncomputable def shellGap (ρ : ℕ → ℝ) (k u v : ℕ) : ℝ :=
  if ρ u = ρ v ∧ |ρ u| < 1 then (1 - ρ k) / (2 * (1 - (ρ u) ^ 2)) else 0

noncomputable def shellPairSum (d k : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ i ∈ range (d - k + 1), ∑ j ∈ range (k + 1),
    ((d - k).choose i : ℝ) * (k.choose j : ℝ) * f (i + j) (i + k - j)

noncomputable def delta (d : ℕ) (ρ : ℕ → ℝ) (k : ℕ) : ℝ :=
  shellPairSum d k (shellGap ρ k)

noncomputable def collisions (d : ℕ) (ρ : ℕ → ℝ) (k : ℕ) : ℝ :=
  shellPairSum d k (fun u v => if ρ u = ρ v then 1 else 0)

private theorem sum_shellPair {d : ℕ} (c : Cube d) (f : ℕ → ℕ → ℝ) :
    ((2 : ℝ) ^ d)⁻¹ * ∑ a : Cube d, f (weight a) (weight (xor a c)) =
      shellPairSum d (weight c) f := by
  unfold shellPairSum
  congr 1
  calc
    _ = ∑ a : Cube d, (fun i j => f (i + j) (i + weight c - j))
        (support a \ support c).card (support a ∩ support c).card := by
      apply sum_congr rfl
      intro a _
      rw [weight_xor_split, weight_split a c]
    _ = _ := sum_support_split c (fun i j => f (i + j) (i + weight c - j))

theorem finite_shell_gap_of_profile {d : ℕ} (K : Kernel (Cube d)) (ρ : ℕ → ℝ)
    (hρ : ∀ a, eigen K a = ρ (weight a)) (c : Cube d) :
    walshCoefficient (continuousAverage K) c - walshCoefficient (discreteAverage K) c =
      delta d ρ (weight c) := by
  rw [finite_walsh_gap, delta, ← sum_shellPair]
  congr 1
  apply sum_congr rfl
  intro a _
  simp only [gap, shellGap, hρ]

theorem finite_shell_collisions_of_profile {d : ℕ} (K : Kernel (Cube d)) (ρ : ℕ → ℝ)
    (hρ : ∀ a, eigen K a = ρ (weight a)) (c : Cube d) :
    walshCoefficient (continuousAverage K) c = collisions d ρ (weight c) := by
  simp_rw [continuousWalsh_eq, hρ, collisions, ← sum_shellPair]

theorem finite_shell_gap {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (c : Cube d) :
    walshCoefficient (continuousAverage (shellKernel d w hw ht)) c -
      walshCoefficient (discreteAverage (shellKernel d w hw ht)) c =
      delta d (rho d w) (weight c) :=
  finite_shell_gap_of_profile _ _ (eigen_eq_krawtchouk w hw ht) c

theorem finite_shell_collisions {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (c : Cube d) :
    walshCoefficient (continuousAverage (shellKernel d w hw ht)) c =
      collisions d (rho d w) (weight c) :=
  finite_shell_collisions_of_profile _ _ (eigen_eq_krawtchouk w hw ht) c

open Filter in
theorem tendsto_finite_shell_gap {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (c : Cube d) :
    Tendsto (fun T : ℝ × ℕ =>
      continuousRealMean
        (fun t => walshCoefficient (continuousMass (shellKernel d w hw ht) t) c) T.1 -
        discreteMean (fun n => walshCoefficient (discreteMass (shellKernel d w hw ht) n) c) T.2)
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℕ))
      (𝓝 (delta d (rho d w) (weight c))) := by
  rw [← finite_shell_gap w hw ht c, finite_walsh_gap]
  exact tendsto_finite_walsh_gap _ c

open Filter in
theorem tendsto_finite_shell_collisions {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (c : Cube d) :
    Tendsto (continuousRealMean
      (fun t => walshCoefficient (continuousMass (shellKernel d w hw ht) t) c))
      atTop (𝓝 (collisions d (rho d w) (weight c))) := by
  rw [← finite_shell_collisions w hw ht c]
  exact tendsto_continuousWalsh _ c

theorem finite_shell_gap_mem_Icc {d : ℕ} (w : ℕ → ℝ) (hw : ∀ h ≤ d, 0 ≤ w h)
    (ht : ∑ h ∈ range (d + 1), w h = 1) (c : Cube d) :
    delta d (rho d w) (weight c) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← finite_shell_gap w hw ht c]
  exact finite_walsh_gap_mem_Icc _ c

end HypercubeWalsh

end
