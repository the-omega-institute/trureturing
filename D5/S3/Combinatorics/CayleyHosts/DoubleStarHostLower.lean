/- GID: D5/S3/Combinatorics/CayleyHosts/DoubleStarHostLower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleyHosts/DoubleStarHostLower
   mirror-E: none(waiver:abelian-host-lower-bound)
   anchors: []
   utility: none
   digest: Leaf differences force three disjoint subgroup cosets in every double-star host. -/

import D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDefs
import D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

namespace D5.S3.Combinatorics.CayleyHosts.DoubleStarHostLower

open DoubleStarHostDefs

/-- Every finite abelian Cayley host of the double star has at least `5q` vertices. -/
theorem lower_bound {Γ : Type*} [AddCommGroup Γ] [Fintype Γ]
    (q : ℕ) (hq : 2 ≤ q) (s : Set Γ) (f : Bool × Option (Fin q) → Γ)
    (h : IsInducedEmbedding (doubleStar q) s f) :
    5 * q ≤ Fintype.card Γ := by
  classical
  let S : Set Γ := {x | x ≠ 0 ∧ (x ∈ s ∨ -x ∈ s)}
  have hadj (u v : Γ) : (SimpleGraph.addCayley s).Adj u v ↔ v - u ∈ S := by
    simp only [SimpleGraph.addCayley_adj, S, Set.mem_ofPred_eq, ne_eq,
      sub_eq_zero, neg_sub]
    simp [sub_eq_add_neg, add_comm, eq_comm]
  let a : Fin q → Γ := fun i => f (false, some i)
  let z : Fin q → Γ := fun i => f (true, some i)
  let c : Γ := f (false, none)
  let d : Γ := f (true, none)
  let A : Finset Γ := Finset.univ.image a
  let B : Finset Γ := Finset.univ.image z
  let L : Finset Γ := A ∪ B
  let D : Finset Γ := L - L
  have ha : Function.Injective a := by
    intro i j hij
    exact Option.some.inj (congrArg Prod.snd (h.1 hij))
  have hz : Function.Injective z := by
    intro i j hij
    exact Option.some.inj (congrArg Prod.snd (h.1 hij))
  have hAc : A.card = q := by simp [A, Finset.card_image_of_injective _ ha]
  have hBc : B.card = q := by simp [B, Finset.card_image_of_injective _ hz]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxA
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxB
    have hh := congrArg Prod.fst (h.1 (hi.trans hj.symm))
    simp at hh
  have hLc : L.card = 2 * q := by
    change (A ∪ B).card = _
    rw [Finset.card_union_of_disjoint hAB, hAc, hBc]
    omega
  have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
  have hDS : ∀ x ∈ D, x ∉ S := by
    intro x hx hxS
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    have huv : u ≠ v := by
      intro heq
      exact hxS.1 (by simp [heq])
    have hed : (SimpleGraph.addCayley s).Adj v u := (hadj v u).mpr hxS
    have hleaves : ∀ w ∈ L, ∃ t : Bool × Option (Fin q),
        t.2 ≠ none ∧ f t = w := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hw
        exact ⟨(false, some i), by simp, hi⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hw
        exact ⟨(true, some i), by simp, hi⟩
    obtain ⟨tu, htu, hfu⟩ := hleaves u hu
    obtain ⟨tv, htv, hfv⟩ := hleaves v hv
    have htne : tv ≠ tu := by
      intro heq
      apply huv
      exact hfu.symm.trans ((congrArg f heq).symm.trans hfv)
    have hgraph := (h.2 tv tu htne).mp (by simpa [hfu, hfv] using hed)
    simp [doubleStar, SimpleGraph.fromRel_adj, htu, htv] at hgraph
  have hAS : ∀ x ∈ A, x - c ∈ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply (hadj c (a i)).mp
    apply (h.2 (false, none) (false, some i) (by simp)).mpr
    simp [doubleStar, SimpleGraph.fromRel_adj]
  have hBS : ∀ x ∈ B, x - d ∈ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply (hadj d (z i)).mp
    apply (h.2 (true, none) (true, some i) (by simp)).mpr
    simp [doubleStar, SimpleGraph.fromRel_adj]
  have hdcS : d - c ∈ S := by
    apply (hadj c d).mp
    apply (h.2 (false, none) (true, none) (by simp)).mpr
    simp [doubleStar, SimpleGraph.fromRel_adj]
  let P₀ : Finset Γ := A.image (fun x => x - c)
  let P₁ : Finset Γ := B.image (fun x => x - d)
  have hP₀c : P₀.card = q := by
    rw [Finset.card_image_of_injective _ (sub_left_injective), hAc]
  have hP₁c : P₁.card = q := by
    rw [Finset.card_image_of_injective _ (sub_left_injective), hBc]
  have hPP : Disjoint P₀ P₁ := by
    apply Finset.disjoint_left.mpr
    intro x hx₀ hx₁
    obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp hx₀
    obtain ⟨v, hv, hv_eq⟩ := Finset.mem_image.mp hx₁
    apply hDS (d - c) _ hdcS
    apply Finset.mem_sub.mpr
    refine ⟨v, Finset.mem_union_right A hv, u, Finset.mem_union_left B hu, ?_⟩
    have heq := hu_eq.trans hv_eq.symm
    have : v - u = d - c := by
      apply (sub_eq_sub_iff_add_eq_add).mpr
      have heq' := (sub_eq_sub_iff_add_eq_add).mp heq
      calc
        v + c = u + d := heq'.symm
        _ = d + u := add_comm _ _
    exact this
  let P : Finset Γ := P₀ ∪ P₁
  have hPc : P.card = 2 * q := by
    change (P₀ ∪ P₁).card = _
    rw [Finset.card_union_of_disjoint hPP, hP₀c, hP₁c]
    omega
  have hPS : ∀ x ∈ P, x ∈ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hAS u hu
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hBS u hu
  have hDP : Disjoint D P := Finset.disjoint_left.mpr fun x hxD hxP =>
    hDS x hxD (hPS x hxP)
  have hcount : D.card + 2 * q ≤ Fintype.card Γ := by
    have := (D ∪ P).card_le_univ
    rwa [Finset.card_union_of_disjoint hDP, hPc] at this
  by_contra! hsmall
  have hDsmall : 2 * (L - L).card < 3 * L.card := by
    change 2 * D.card < 3 * L.card
    omega
  obtain ⟨H, hH⟩ := DoubleStarHostDifference.difference_subgroup L hLne hDsmall
  have hHD (x : Γ) : x ∈ H ↔ x ∈ D := by
    change x ∈ (H : Set Γ) ↔ x ∈ D
    rw [hH]
    rfl
  let T : Finset Γ := Finset.univ.filter (fun x => x ∈ H)
  have hT (x : Γ) : x ∈ T ↔ x ∈ H := by simp [T]
  obtain ⟨l, hl⟩ := hLne
  have hxH : ∀ x ∈ L, x - l ∈ H := by
    intro x hx
    apply (hHD _).mpr
    exact Finset.mem_sub.mpr ⟨x, hx, l, hl, rfl⟩
  have hLT : 2 * q ≤ T.card := by
    have hsub : L.image (fun x => x - l) ⊆ T := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hT _).mpr (hxH x hx)
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ sub_left_injective, hLc] at this
  have hHS : ∀ x ∈ H, x ∉ S := fun x hx => hDS x ((hHD x).mp hx)
  have hAcne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBcne : B.Nonempty := Finset.card_pos.mp (by omega)
  have hlc : l - c ∉ H := by
    intro hh
    obtain ⟨x, hx⟩ := hAcne
    have hm : x - c ∈ H := by
      have := H.add_mem (hxH x (Finset.mem_union_left B hx)) hh
      simpa only [sub_add_sub_cancel] using this
    exact hHS _ hm (hAS x hx)
  have hld : l - d ∉ H := by
    intro hh
    obtain ⟨x, hx⟩ := hBcne
    have hm : x - d ∈ H := by
      have := H.add_mem (hxH x (Finset.mem_union_right A hx)) hh
      simpa only [sub_add_sub_cancel] using this
    exact hHS _ hm (hBS x hx)
  have hdc : d - c ∉ H := fun hh => hHS _ hh hdcS
  let C : Finset Γ := T.image (fun x => l - c + x)
  let E : Finset Γ := T.image (fun x => l - d + x)
  have hCc : C.card = T.card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hEc : E.card = T.card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hTC : Disjoint T C := by
    apply Finset.disjoint_left.mpr
    intro x hx hxC
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hxC
    apply hlc
    have hh := H.sub_mem ((hT x).mp hx) ((hT y).mp hy)
    simpa [← heq] using hh
  have hTE : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    intro x hx hxE
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hxE
    apply hld
    have hh := H.sub_mem ((hT x).mp hx) ((hT y).mp hy)
    simpa [← heq] using hh
  have hCE : Disjoint C E := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxE
    obtain ⟨y, hy, heqY⟩ := Finset.mem_image.mp hxC
    obtain ⟨z, hz, heqZ⟩ := Finset.mem_image.mp hxE
    apply hdc
    have hh := H.sub_mem ((hT z).mp hz) ((hT y).mp hy)
    have heq : d - c = z - y := by
      have heq := heqY.trans heqZ.symm
      exact (sub_eq_sub_iff_add_eq_add).mpr (by
        have hyz : y - c = z - d := (add_right_inj l).mp (by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using heq)
        exact (add_comm d y).trans ((sub_eq_sub_iff_add_eq_add).mp hyz))
    rwa [← heq] at hh
  have hthree : 3 * T.card ≤ Fintype.card Γ := by
    have := ((T ∪ C) ∪ E).card_le_univ
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hTE, hCE⟩),
      Finset.card_union_of_disjoint hTC, hCc, hEc] at this
    omega
  omega

end D5.S3.Combinatorics.CayleyHosts.DoubleStarHostLower
