/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformGrayReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/EightUniformGrayReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual eight-uniform balanced cubic 54-supports of Q9 have Gray reconstruction. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AdjacentLayerRigidity
import D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformHeightSpan
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import Mathlib.Logic.Equiv.Bool
import Batteries.Tactic.OpenPrivate

/-! Actual eight-direction edge uniformity reconstructs the Gray cube image. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
noncomputable section
namespace D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformGrayReconstruction

open scoped BigOperators
attribute [local instance] Classical.propDecidable
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced directionEdges direction_edge_count)
open BalancedCriticalSpectrum (flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mismatchSet weight centeredHeight height_step height_span
    induced_degree_eq_neighbor_card lower_bound_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformHeightSpan
local notation "flip" => BalancedCriticalSpectrum.flip

private abbrev Q9 := Q 9
private abbrev Coord := Fin 9

private theorem mismatch_card_bool (s : Finset Coord) (a : Coord → Bool) (x : Q9) :
    ((s.filter (fun i => x i ≠ a i)).card : Bool) =
      (∑ i ∈ s, (x i + a i)) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases hx : x i <;> cases ha : a i <;> simp [hx, ha] <;> decide

private theorem weight_bool_even {j : Coord} {a : Coord → Bool} {x : Q9}
    (hp : cubeParity x = false) :
    ((weight j a x : Bool)) = x j + (∑ i ∈ Finset.univ.erase j, a i) := by
  have hpar := hp
  unfold cubeParity at hpar
  rw [← Finset.add_sum_erase Finset.univ x (Finset.mem_univ j)] at hpar
  have hxsum : x j = (∑ i ∈ Finset.univ.erase j, x i) := by
    cases hxj : x j <;> cases hs : (∑ i ∈ Finset.univ.erase j, x i) <;>
      simp [hxj, hs] at hpar ⊢
  have hw := mismatch_card_bool (Finset.univ.erase j) a x
  have hw' : ((weight j a x : Bool)) =
      (∑ i ∈ Finset.univ.erase j, (x i + a i)) := by
    rw [weight, mismatchSet]
    exact hw
  rw [hw', Finset.sum_add_distrib, ← hxsum]

private def chooseBits {C : Finset Q9} (j : Coord)
    (huniform : ∀ i : Coord, i ≠ j → ∃ b : Bool,
      ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = b) : Coord → Bool := by
  classical exact fun i => if h : i = j then false else Classical.choose (huniform i h)

private theorem chooseBits_spec {C : Finset Q9} {j : Coord}
    (huniform : ∀ i : Coord, i ≠ j → ∃ b : Bool,
      ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = b)
    {i : Coord} (hij : i ≠ j) :
    ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = chooseBits j huniform i := by
  classical
  dsimp [chooseBits]
  rw [dif_neg hij]
  exact Classical.choose_spec (huniform i hij)

private def fullMismatchSet (a : Coord → Bool) (x : Q9) : Finset Coord :=
  Finset.univ.filter (fun i => x i ≠ a i)

private def fullWeight (a : Coord → Bool) (x : Q9) : Nat :=
  (fullMismatchSet a x).card

private def fullCenteredHeight (a : Coord → Bool) (x : Q9) : Int :=
  (fullWeight a x : Int) - if cubeParity x then 1 else 0

private theorem full_height_flip {C : Finset Q9} {a : Coord → Bool}
    (ha : ∀ i, ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = a i)
    {x : Q9} (hx : x ∈ C) (i : Coord) (hiC : flip x i ∈ C) :
    fullCenteredHeight a (flip x i) = fullCenteredHeight a x := by
  have hweight_even {y : Q9} (hy : y ∈ C) (k : Coord)
      (hkC : flip y k ∈ C) (hp : cubeParity y = false) :
      fullWeight a (flip y k) = fullWeight a y + 1 := by
    have hu := ha k y hy hp hkC
    have hnot : k ∉ fullMismatchSet a y := by simp [fullMismatchSet, hu]
    have heq : fullMismatchSet a (flip y k) = insert k (fullMismatchSet a y) := by
      ext l
      by_cases hl : l = k
      · subst l
        simp [fullMismatchSet, hu]
      · simp [fullMismatchSet, hl, BalancedCriticalSpectrum.flip]
    change (fullMismatchSet a (flip y k)).card = (fullMismatchSet a y).card + 1
    rw [heq, Finset.card_insert_of_notMem hnot]
  have hpar : cubeParity (flip x i) ≠ cubeParity x :=
    cubeParity_ne_of_adj (flip_adj x i).symm
  by_cases hp : cubeParity x = false
  · have htrue : cubeParity (flip x i) = true := by
      cases hq : cubeParity (flip x i) <;> simp_all
    have hw := hweight_even hx i hiC hp
    unfold fullCenteredHeight
    simp [hp, htrue]
    omega
  · have hp' : cubeParity (flip x i) = false := by
      cases hq : cubeParity (flip x i) <;> simp_all
    have hw := hweight_even (by simpa using hiC) i (by simpa using hx) hp'
    have hback : fullWeight a x = fullWeight a (flip x i) + 1 := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using hw
    have htrue : cubeParity x = true := by cases hq : cubeParity x <;> simp_all
    unfold fullCenteredHeight
    simp [hp', htrue]
    omega

set_option maxHeartbeats 1000000 in
/-- The actual eight-direction hypothesis reconstructs the Gray support. -/
theorem eight_uniform_gray_reconstruction {C : Finset Q9}
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) (j : Coord)
    (huniform : ∀ i, i ≠ j → ∃ b : Bool,
      ∀ x ∈ C, (∑ k, x k) = false → flip x i ∈ C → x i = b) :
    ∃ (g : Q9 ≃ Q9) (pi : Coord ≃ Coord),
      (∀ x i, g (flip x i) = flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  classical
  have hC : C.Nonempty := Finset.card_pos.mp (by omega)
  let a : Coord → Bool := chooseBits j huniform
  have ha : ∀ i, i ≠ j → ∀ x ∈ C, cubeParity x = false →
      flip x i ∈ C → x i = a i := by
    intro i hi x hx hp hy
    exact chooseBits_spec huniform hi x hx hp hy
  let h : Q9 → Int := centeredHeight j a
  let H : Finset Int := C.image h
  have hH : H.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨h x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let m : Int := H.min' hH
  let M : Int := H.max' hH
  have hmin_mem : m ∈ H := by
    exact Finset.min'_mem H hH
  have hmax_mem : M ∈ H := by
    exact Finset.max'_mem H hH
  have hmin_le (x : Q9) (hx : x ∈ C) : m ≤ h x := by
    exact Finset.min'_le H (h x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hle_max (x : Q9) (hx : x ∈ C) : h x ≤ M := by
    exact Finset.le_max' H (h x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hstep' {x : Q9} (hx : x ∈ C) (i : Coord) (hiC : flip x i ∈ C) :
      (i = j ∧ cubeParity x = false ∧ h (flip x i) = h x - 1) ∨
        (i = j ∧ cubeParity x = true ∧ h (flip x i) = h x + 1) ∨
        (i ≠ j ∧ h (flip x i) = h x) := by
    exact height_step ha hx i hiC
  have hspan_le : M - m ≤ 1 := by
    obtain ⟨u, hu, hum⟩ := Finset.mem_image.mp hmin_mem
    obtain ⟨v, hv, hvM⟩ := Finset.mem_image.mp hmax_mem
    have hd := height_span hC hr hb hcard j a ha v hv u hu
    change h v ≤ h u + 1 at hd
    rw [hum, hvM] at hd
    omega
  let F : Finset Q9 := C.filter (fun x => x j = false ∧ flip x j ∈ C)
  have hFcard : F.card = 9 := by
    have he := direction_edge_count (d := 3) C hr hb j
    have he' : 6 * F.card = 54 := by
      simpa [F, directionEdges, hcard] using he
    omega
  let E : Finset Q9 := C.filter (fun x => cubeParity x = false ∧ flip x j ∈ C)
  have hE_nonempty : E.Nonempty := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    have huC : u ∈ C := (Finset.filter_subset _ _) hu
    have hcross : flip u j ∈ C := (Finset.mem_filter.mp hu).2.2
    by_cases hp : cubeParity u = false
    · exact ⟨u, by simp [E, huC, hp, hcross]⟩
    · have hp' : cubeParity (flip u j) = false := by
        have hne := cubeParity_ne_of_adj (flip_adj u j)
        cases hq : cubeParity (flip u j) <;> simp_all
      exact ⟨flip u j, by simp [E, hcross, hp', huC, BalancedCriticalSpectrum.flip_flip]⟩
  have hE_height {x : Q9} (hx : x ∈ E) : h x = M := by
    have hxC : x ∈ C := (Finset.filter_subset _ _) hx
    have hcross := (Finset.mem_filter.mp hx).2.2
    have hrel := hstep' hxC j hcross
    have hh : h (flip x j) = h x - 1 := by
      rcases hrel with ⟨_, hp, hh⟩ | ⟨_, hp, hh⟩ | hne
      · exact hh
      · have hbad : (true : Bool) = false :=
          hp.symm.trans (Finset.mem_filter.mp hx).2.1
        cases hbad
      · exact (hne.1 rfl).elim
    have hlow := hmin_le (flip x j) hcross
    have hhigh := hle_max x hxC
    omega
  obtain ⟨x₀, hx₀⟩ := hE_nonempty
  let b : Bool := x₀ j
  have hE_j {x : Q9} (hx : x ∈ E) : x j = b := by
    have hxC : x ∈ C := (Finset.filter_subset _ _) hx
    have hp : cubeParity x = false := (Finset.mem_filter.mp hx).2.1
    have hp₀ : cubeParity x₀ = false := (Finset.mem_filter.mp hx₀).2.1
    have hxM := hE_height hx
    have h₀M := hE_height hx₀
    have hxW : (weight j a x : Int) = M := by
      simpa [h, centeredHeight, hp] using hxM
    have h₀W : (weight j a x₀ : Int) = M := by
      simpa [h, centeredHeight, hp₀] using h₀M
    have hWi : (weight j a x : Int) = (weight j a x₀ : Int) := hxW.trans h₀W.symm
    have hW : weight j a x = weight j a x₀ := by exact_mod_cast hWi
    have hWB := congrArg (fun n : Nat => (n : Bool)) hW
    have hparx := weight_bool_even (j := j) (a := a) (x := x) hp
    have hpar₀ := weight_bool_even (j := j) (a := a) (x := x₀) hp₀
    have hsum : x j + (∑ i ∈ Finset.univ.erase j, a i) =
        x₀ j + (∑ i ∈ Finset.univ.erase j, a i) := by
      simpa [hparx, hpar₀] using hWB
    have heq : x j = x₀ j := by
      cases hxj : x j <;> cases h₀j : x₀ j <;>
        cases hs : (∑ i ∈ Finset.univ.erase j, a i) <;>
        simp [hxj, h₀j, hs] at hsum ⊢
    exact heq
  let afull : Coord → Bool := fun i => if i = j then b else a i
  have ha_full : ∀ i, ∀ x ∈ C, cubeParity x = false →
      flip x i ∈ C → x i = afull i := by
    intro i x hx hp hxi
    by_cases hi : i = j
    · subst i
      have hxe : x ∈ E := by simp [E, hx, hp, hxi]
      simpa [afull, b] using hE_j hxe
    · simpa [afull, hi] using ha i hi x hx hp hxi
  have hfull_step {x : Q9} (hx : x ∈ C) (i : Coord)
      (hiC : flip x i ∈ C) :
      fullCenteredHeight afull (flip x i) = fullCenteredHeight afull x :=
    full_height_flip ha_full hx i hiC
  let q : Int := fullCenteredHeight afull x₀
  let T : Finset Q9 := C.filter (fun x => fullCenteredHeight afull x = q)
  have hT_nonempty : T.Nonempty := by
    have hx₀C : x₀ ∈ C := (Finset.filter_subset _ _) hx₀
    exact ⟨x₀, by simp [T, q, hx₀C]⟩
  have hT_closed : ∀ x ∈ T, ∀ y ∈ C,
      (hypercube 9).Adj x y → y ∈ T := by
    intro x hx y hy hxy
    obtain ⟨i, hi⟩ := adjacent_exists_flip hxy
    subst y
    have hstep := hfull_step (Finset.mem_filter.mp hx).1 i hy
    apply Finset.mem_filter.mpr
    exact ⟨hy, by rw [hstep, (Finset.mem_filter.mp hx).2]⟩
  have hT_lower := lower_bound_neighbor_closed hr hb hT_nonempty
    (Finset.filter_subset _ _) hT_closed
  have hT_card : T.card = C.card := by
    have hle := Finset.card_le_card (Finset.filter_subset _ _ : T ⊆ C)
    have hle' : T.card ≤ 54 := by simpa [hcard] using hle
    omega
  have hT_eq : T = C := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro x hx
    by_contra hnot
    have hss : T ⊂ C := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun heq => by
        apply hnot
        have hxT : x ∈ T := heq.symm ▸ hx
        change x ∈ T at hxT
        exact hxT⟩
    have hlt := Finset.card_lt_card hss
    omega
  have hlevel {x : Q9} (hx : x ∈ C) :
      fullCenteredHeight afull x = q := by
    have hxT : x ∈ T := by
      exact hT_eq.symm ▸ hx
    change x ∈ T at hxT
    exact (Finset.mem_filter.mp hxT).2
  have hp₀ : cubeParity x₀ = false := (Finset.mem_filter.mp hx₀).2.1
  let r : Nat := fullWeight afull x₀
  have hfull_band {x : Q9} (hx : x ∈ C) :
      fullWeight afull x = r ∨ fullWeight afull x = r + 1 := by
    have hh := hlevel hx
    by_cases hp : cubeParity x = false
    · left
      have hi : (fullWeight afull x : Int) = (fullWeight afull x₀ : Int) := by
        simpa [fullCenteredHeight, q, hp, hp₀] using hh
      exact_mod_cast hi
    · right
      have hp' : cubeParity x = true := by cases hq : cubeParity x <;> simp_all
      have hi : (fullWeight afull x : Int) - 1 = (fullWeight afull x₀ : Int) := by
        simpa [fullCenteredHeight, q, hp', hp₀] using hh
      push_cast at hi
      dsimp [r]
      omega
  let t : Q9 ≃ Q9 :=
    Equiv.piCongrRight (fun i => if afull i then Equiv.boolNot else Equiv.refl Bool)
  have htflip : ∀ x i, t (flip x i) = flip (t x) i := by
    intro x i
    funext k
    by_cases hk : k = i
    · subst k
      by_cases hai : afull i = true
      · simp [t, Equiv.piCongrRight, BalancedCriticalSpectrum.flip, hai]
      · simp [t, Equiv.piCongrRight, BalancedCriticalSpectrum.flip, hai]
    · by_cases hai : afull k = true
      · simp [t, Equiv.piCongrRight, BalancedCriticalSpectrum.flip, hk, hai]
      · simp [t, Equiv.piCongrRight, BalancedCriticalSpectrum.flip, hk, hai]
  have htweight (x : Q9) :
      (Finset.univ.filter (fun i => (t x) i = true)).card =
        fullWeight afull x := by
    have heq : Finset.univ.filter (fun i => (t x) i = true) =
        fullMismatchSet afull x := by
      ext i
      by_cases hai : afull i = true
      · simp [t, Equiv.piCongrRight, fullMismatchSet, hai]
      · simp [t, Equiv.piCongrRight, fullMismatchSet, hai]
    rw [heq]
    rfl
  let D : Finset Q9 := C.image t
  have hD_nonempty : D.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨t x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hD_card : D.card = 54 := by
    have hi : (C.image t).card = C.card := by
      rw [Finset.card_image_iff]
      intro x _ y _ hxy
      exact t.injective hxy
    simpa [D, hcard] using hi
  have hD_regular : ((hypercube 9).induce (D : Set Q9)).IsRegularOfDegree 3 := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
    have hy_eq : y = ⟨t x, (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩ :=
      Subtype.ext hxy.symm
    rw [hy_eq]
    rw [induced_degree_eq_neighbor_card]
    have hN' : ((hypercube 9).neighborFinset x ∩ C).card =
        ((hypercube 9).neighborFinset (t x) ∩ D).card := by
      apply Finset.card_bij (fun z _ => t z)
      · intro z hz
        have hzmem := Finset.mem_inter.mp hz
        have hzadj : (hypercube 9).Adj x z :=
          ((hypercube 9).mem_neighborFinset x z).mp hzmem.1
        obtain ⟨i, hi⟩ := adjacent_exists_flip hzadj
        have htadj : (hypercube 9).Adj (t x) (t z) := by
          rw [hi, htflip]
          exact flip_adj _ _
        have htarget : t z ∈
            ((hypercube 9).neighborFinset (t x) ∩ D) :=
          Finset.mem_inter.mpr
            ⟨((hypercube 9).mem_neighborFinset (t x) (t z)).mpr htadj,
              Finset.mem_image.mpr ⟨z, hzmem.2, rfl⟩⟩
        exact htarget
      · intro z hz w hw hzw
        exact t.injective hzw
      · intro z hz
        have hzmem := Finset.mem_inter.mp hz
        have hzD := hzmem.2
        obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp hzD
        have hzadj : (hypercube 9).Adj (t x) z :=
          ((hypercube 9).mem_neighborFinset (t x) z).mp hzmem.1
        obtain ⟨i, hi⟩ := adjacent_exists_flip hzadj
        have hpre : u = flip x i := by
          apply t.injective
          calc
            t u = z := htu
            _ = flip (t x) i := hi
            _ = t (flip x i) := (htflip x i).symm
        refine ⟨flip x i, ?_, ?_⟩
        · have hsrc : flip x i ∈
              ((hypercube 9).neighborFinset x ∩ C) :=
            Finset.mem_inter.mpr
              ⟨((hypercube 9).mem_neighborFinset x (flip x i)).mpr
                  (flip_adj _ _),
                hpre ▸ hu⟩
          exact hsrc
        · calc
            t (flip x i) = flip (t x) i := htflip x i
            _ = z := hi.symm
    rw [← hN', ← induced_degree_eq_neighbor_card C ⟨x, hx⟩]
    exact hr.degree_eq _
  obtain ⟨sigma, hsigma⟩ := hb
  obtain ⟨theta, htheta, hedge, _⟩ :=
    HuangCubeCovariance.exists_signed_covariance t (Equiv.refl Coord) htflip
  let sigmaD : Q9 → ℝ := fun y => theta (t.symm y) * sigma (t.symm y)
  have hD_balanced : IsBalanced D := by
    refine ⟨sigmaD, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rcases htheta x with hθ | hθ
      · rcases hsigma.1 x hx with hσ | hσ
        · simp only [sigmaD, t.symm_apply_apply]
          change theta x * sigma x = 1 ∨ theta x * sigma x = -1
          simp [hθ, hσ]
        · simp only [sigmaD, t.symm_apply_apply]
          change theta x * sigma x = 1 ∨ theta x * sigma x = -1
          simp [hθ, hσ]
      · rcases hsigma.1 x hx with hσ | hσ
        · simp only [sigmaD, t.symm_apply_apply]
          change theta x * sigma x = 1 ∨ theta x * sigma x = -1
          simp [hθ, hσ]
        · simp only [sigmaD, t.symm_apply_apply]
          change theta x * sigma x = 1 ∨ theta x * sigma x = -1
          simp [hθ, hσ]
    · intro y hy z hz hyz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, hi⟩ := adjacent_exists_flip hyz
      have hpre : u = flip x i := by
        apply t.injective
        rw [htflip]
        exact hi
      have hsource : flip x i ∈ C := by simpa [hpre] using hu
      have hs := hsigma.2 x hx (flip x i) hsource (flip_adj _ _)
      have he := hedge x i
      dsimp [sigmaD]
      simp only [t.symm_apply_apply]
      rw [hpre, he, hs]
      ring_nf
  have hbandD : ∀ y ∈ D,
      (Finset.univ.filter (fun i => y i = true)).card = r ∨
        (Finset.univ.filter (fun i => y i = true)).card = r + 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hw := hfull_band hx
    rw [htweight]
    exact hw
  obtain ⟨g₁, pi, hg₁, hDimage⟩ :=
    AdjacentLayerRigidity.adjacent_layers_gray_reconstruction hD_nonempty
      hD_regular hD_balanced hD_card r hbandD
  have htsymm : ∀ y i, t.symm (flip y i) = flip (t.symm y) i := by
    intro y i
    have hh := congrArg t.symm (htflip (t.symm y) i)
    simpa only [t.apply_symm_apply, t.symm_apply_apply] using hh.symm
  let g : Q9 ≃ Q9 := g₁.trans t.symm
  have hg : ∀ x i, g (flip x i) = flip (g x) (pi i) := by
    intro x i
    dsimp [g]
    rw [hg₁, htsymm]
  have hback : D.image t.symm = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
      have hyx : y = t x := by simpa using congrArg t hxy
      have : x = z := by
        apply t.injective
        exact hyx.symm.trans hzy.symm
      simpa [this] using hz
    · intro hx
      exact Finset.mem_image.mpr ⟨t x,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩, t.symm_apply_apply _⟩
  refine ⟨g, pi, hg, ?_⟩
  calc
    C = D.image t.symm := hback.symm
    _ = ((GrayGridComponent.support 3).image g₁).image t.symm := by rw [hDimage]
    _ = (GrayGridComponent.support 3).image g := by
      rw [Finset.image_image]
      rfl


end D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformGrayReconstruction
