/- GID: D5/S3/Quantum/Algebra/AuricOcticRanks
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/AuricOcticRanks
   mirror-E: none(waiver:symbolic-rank-inequalities)
   anchors: []
   utility: none
   digest: Connected invariant half-ranks and cut-free operators on eight labels. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Module LinearMap
open scoped Classical

section CoordinateRanks

variable {K Ω : Type*} [Field K] [Fintype Ω] [DecidableEq Ω]

def coordinateProject (S : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K) where
  toFun x i := if i ∈ S then x i else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

def projected (U : Submodule K (Ω → K)) (S : Finset Ω) :
    Submodule K (Ω → K) := U.map (coordinateProject S)

def rowRank (U : Submodule K (Ω → K)) (S : Finset Ω) : ℕ :=
  finrank K (projected U S)

private def coordinateKernel (U : Submodule K (Ω → K)) (S : Finset Ω) : Submodule K U :=
  LinearMap.ker ((coordinateProject S).domRestrict U)

private theorem mem_coordinateKernel (U : Submodule K (Ω → K)) (S : Finset Ω) (x : U) :
    x ∈ coordinateKernel U S ↔ ∀ i ∈ S, (x : Ω → K) i = 0 := by
  change coordinateProject S (x : Ω → K) = 0 ↔ _
  constructor
  · intro hx i hi
    simpa [coordinateProject, hi] using congrFun hx i
  · intro hx
    ext i
    by_cases hi : i ∈ S <;> simp [coordinateProject, hi, hx]

private theorem coordinate_rank_nullity (U : Submodule K (Ω → K)) (S : Finset Ω) :
    rowRank U S + finrank K (coordinateKernel U S) = finrank K U := by
  have hn := LinearMap.finrank_range_add_finrank_ker ((coordinateProject S).domRestrict U)
  rw [LinearMap.range_domRestrict] at hn
  exact hn

private theorem rowRank_empty (U : Submodule K (Ω → K)) : rowRank U ∅ = 0 := by
  have he : (coordinateProject (∅ : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K)) = 0 := by
    ext x i
    simp [coordinateProject]
  rw [rowRank, projected, he, Submodule.map_zero, finrank_bot]

private theorem rowRank_univ (U : Submodule K (Ω → K)) : rowRank U Finset.univ = finrank K U := by
  have he : (coordinateProject (Finset.univ : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K)) = .id := by
    ext x i
    simp [coordinateProject]
  rw [rowRank, projected, he, Submodule.map_id]

private theorem rowRank_mono (U : Submodule K (Ω → K)) {S T : Finset Ω} (h : S ⊆ T) :
    rowRank U S ≤ rowRank U T := by
  have hk : coordinateKernel U T ≤ coordinateKernel U S := by
    intro x hx
    rw [mem_coordinateKernel] at hx ⊢
    exact fun i hi => hx i (h hi)
  have hl := Submodule.finrank_mono hk
  have hs := coordinate_rank_nullity U S
  have ht := coordinate_rank_nullity U T
  omega

private theorem rowRank_submodular (U : Submodule K (Ω → K)) (S T : Finset Ω) :
    rowRank U (S ∪ T) + rowRank U (S ∩ T) ≤ rowRank U S + rowRank U T := by
  have hc : coordinateKernel U (S ∪ T) = coordinateKernel U S ⊓ coordinateKernel U T := by
    ext x
    simp only [Submodule.mem_inf, mem_coordinateKernel, Finset.mem_union]
    aesop
  have hi : coordinateKernel U S ⊔ coordinateKernel U T ≤ coordinateKernel U (S ∩ T) := by
    apply sup_le
    · intro x hx
      rw [mem_coordinateKernel] at hx ⊢
      exact fun i hi => hx i (Finset.mem_inter.mp hi).1
    · intro x hx
      rw [mem_coordinateKernel] at hx ⊢
      exact fun i hi => hx i (Finset.mem_inter.mp hi).2
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (coordinateKernel U S) (coordinateKernel U T)
  have hl := Submodule.finrank_mono hi
  have hS := coordinate_rank_nullity U S
  have hT := coordinate_rank_nullity U T
  have hC := coordinate_rank_nullity U (S ∪ T)
  have hI := coordinate_rank_nullity U (S ∩ T)
  rw [hc] at hC
  omega

private theorem project_add_complement (S : Finset Ω) (x : Ω → K) :
    coordinateProject S x + coordinateProject Sᶜ x = x := by
  ext i
  by_cases h : i ∈ S <;> simp [coordinateProject, h]

theorem projected_disjoint (U : Submodule K (Ω → K)) (S : Finset Ω) :
    Disjoint (projected U S) (projected U Sᶜ) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  rintro x ⟨⟨v, hv, rfl⟩, w, hw, he⟩
  change coordinateProject S v = 0
  ext i
  have hi := congrFun he i
  by_cases hs : i ∈ S <;> simp_all [coordinateProject]

theorem window_le_projected_sup (U : Submodule K (Ω → K)) (S : Finset Ω) :
    U ≤ projected U S ⊔ projected U Sᶜ := by
  intro x hx
  rw [← project_add_complement S x]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩

theorem projection_stable_of_rank_equality (U : Submodule K (Ω → K))
    (S : Finset Ω) (h : rowRank U S + rowRank U Sᶜ = finrank K U) :
    ∀ x ∈ U, coordinateProject S x ∈ U := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (projected U S) (projected U Sᶜ)
  rw [(projected_disjoint U S).eq_bot, finrank_bot, add_zero] at hd
  have he : U = projected U S ⊔ projected U Sᶜ :=
    Submodule.eq_of_le_of_finrank_eq (window_le_projected_sup U S)
      (h.symm.trans hd.symm)
  intro x hx
  rw [he]
  exact (show projected U S ≤ projected U S ⊔ projected U Sᶜ from le_sup_left)
    (show coordinateProject S x ∈ projected U S from ⟨x, hx, rfl⟩)

end CoordinateRanks


section TightRankRigidity

variable {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Group G] [Fintype G] [MulAction G Ω]

def orbitSet (S : Finset Ω) (g : G) : Finset Ω := S.image (g • ·)

private theorem orbitSet_card (S : Finset Ω) (g : G) : (orbitSet S g).card = S.card :=
  Finset.card_image_of_injective _ (MulAction.injective g)

theorem mem_orbitSet (S : Finset Ω) (g : G) (i : Ω) :
    i ∈ orbitSet S g ↔ g⁻¹ • i ∈ S := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa using hj
  · intro hi
    exact Finset.mem_image.mpr ⟨g⁻¹ • i, hi, by simp⟩

private theorem invariant_half_rank_weak {K : Type*} [Field K]
    (U : Submodule K (Ω → K)) (hΩ : Fintype.card Ω = 8) (hU : finrank K U = 4)
    (htrans : ∀ x y : Ω, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) S, rowRank U (orbitSet S g) = rowRank U S)
    (S : Finset Ω) : S.card ≤ 2 * rowRank U S := by
  classical
  by_cases hS : S.Nonempty
  swap
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [this, rowRank_empty]
  obtain ⟨s, hs⟩ := hS
  let C : Ω → Finset G := fun i => Finset.univ.filter (fun g => i ∈ orbitSet S g)
  let d := (C s).card
  have hdeg : ∀ i, (C i).card = d := by
    intro i
    obtain ⟨h, hh⟩ := htrans s i
    symm
    apply Finset.card_equiv (Equiv.mulLeft h)
    intro g
    change g ∈ C s ↔ h * g ∈ C i
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, mem_orbitSet]
    rw [← hh, mul_inv_rev, mul_smul, inv_smul_smul]
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [orbitSet] using hs
  have hdouble : Fintype.card G * S.card = Fintype.card Ω * d := by
    have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := Finset.univ) (fun (g : G) (i : Ω) => i ∈ orbitSet S g)
    have hleft (g : G) : Finset.univ.bipartiteAbove
        (fun (g : G) (i : Ω) => i ∈ orbitSet S g) g = orbitSet S g := by
      ext i
      simp [Finset.bipartiteAbove]
    have hright (i : Ω) : Finset.univ.bipartiteBelow
        (fun (g : G) (i : Ω) => i ∈ orbitSet S g) i = C i := rfl
    simpa only [hleft, hright, orbitSet_card, hdeg, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul] using hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcover : ∀ i ∈ (Finset.univ : Finset Ω),
      (1 : ℝ) ≤ ∑ g : G, if i ∈ orbitSet S g then (d : ℝ)⁻¹ else 0 := by
    intro i _
    rw [← Finset.sum_filter]
    change 1 ≤ ∑ _ ∈ C i, (d : ℝ)⁻¹
    simp only [Finset.sum_const, nsmul_eq_mul, hdeg]
    rw [mul_inv_cancel₀ hdR.ne']
  have hbound :=
    D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses.fractional_submodular_cover
      (fun T => (rowRank U T : ℝ)) (by simp only [rowRank_empty, Nat.cast_zero])
      (fun A B h => by exact_mod_cast rowRank_mono U h)
      (fun A B => by exact_mod_cast rowRank_submodular U A B)
      Finset.univ (orbitSet S) (fun _ => Finset.subset_univ _)
      (fun _ => (d : ℝ)⁻¹) (fun _ => le_of_lt (inv_pos.mpr hdR)) hcover
  have hb : (4 : ℝ) ≤ (Fintype.card G : ℝ) * (rowRank U S : ℝ) / d := by
    simpa only [rowRank_univ, hU, hinv, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, div_eq_mul_inv, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hbound
  have hb' := (le_div_iff₀ hdR).mp hb
  have hdc : (Fintype.card G : ℝ) * S.card = 8 * (d : ℝ) := by
    exact_mod_cast (hdouble.trans (by rw [hΩ]))
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hh : (S.card : ℝ) ≤ 2 * rowRank U S := by nlinarith
  exact_mod_cast hh

/-- Equality rigidity for a nonnegative invariant submodular defect. -/
private theorem tight_complement (f : Finset Ω → ℤ)
    (hzero : f ∅ = 0) (hnonneg : ∀ S, 0 ≤ f S)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T)
    (htrans : ∀ x y : Ω, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) S, f (orbitSet S g) = f S)
    (S : Finset Ω) (hS : S.Nonempty) (htight : f S = 0) : f Sᶜ = 0 := by
  classical
  have hunion {A B : Finset Ω} (hA : f A = 0) (hB : f B = 0) : f (A ∪ B) = 0 := by
    have hh := hsub A B
    have h1 := hnonneg (A ∪ B)
    have h2 := hnonneg (A ∩ B)
    omega
  have hinter {A B : Finset Ω} (hA : f A = 0) (hB : f B = 0) : f (A ∩ B) = 0 := by
    have hh := hsub A B
    have h1 := hnonneg (A ∪ B)
    have h2 := hnonneg (A ∩ B)
    omega
  let Bset := (Finset.univ : Finset Ω).powerset.filter (fun B => B.Nonempty ∧ f B = 0)
  have hSset : S ∈ Bset := by simp [Bset, hS, htight]
  obtain ⟨B, hBset, hmin⟩ := Bset.exists_min_image Finset.card ⟨S, hSset⟩
  have hB := (Finset.mem_filter.mp hBset).2
  obtain ⟨b, hb⟩ := hB.1
  let A : Finset G := Finset.univ.filter (fun g => orbitSet B g ⊆ Sᶜ)
  have he : A.biUnion (orbitSet B) = Sᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hg).2 hxg
    · intro hx
      obtain ⟨g, hg⟩ := htrans b x
      have hxg : x ∈ orbitSet B g := Finset.mem_image.mpr ⟨b, hb, hg⟩
      have hsubset : orbitSet B g ⊆ Sᶜ := by
        intro y hy
        apply Finset.mem_compl.mpr
        intro hys
        have hi : (orbitSet B g ∩ S).Nonempty := ⟨y, Finset.mem_inter.mpr ⟨hy, hys⟩⟩
        have hti : f (orbitSet B g ∩ S) = 0 := hinter ((hinv g B).trans hB.2) htight
        have himem : orbitSet B g ∩ S ∈ Bset := by simp [Bset, hi, hti]
        have hcard := hmin _ himem
        have hie : orbitSet B g ∩ S = orbitSet B g :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
            simpa only [orbitSet_card] using hcard)
        have hxs : x ∈ S := (Finset.mem_inter.mp (hie.symm ▸ hxg)).2
        exact (Finset.mem_compl.mp hx) hxs
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsubset⟩, hxg⟩
  have hall : ∀ T : Finset G, f (T.biUnion (orbitSet B)) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hzero
    | @insert g T hg ih =>
        rw [Finset.biUnion_insert]
        exact hunion ((hinv g B).trans hB.2) ih
  rw [← he]
  exact hall A

theorem invariant_half_rank_strict {K : Type*} [Field K]
    (U : Submodule K (Ω → K)) (hΩ : Fintype.card Ω = 8) (hU : finrank K U = 4)
    (htrans : ∀ x y : Ω, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) S, rowRank U (orbitSet S g) = rowRank U S)
    (hconn : ∀ S : Finset Ω, S.Nonempty → Sᶜ.Nonempty →
      4 < rowRank U S + rowRank U Sᶜ)
    (S : Finset Ω) (hs : S.Nonempty) (ht : Sᶜ.Nonempty) :
    S.card + 1 ≤ 2 * rowRank U S := by
  let f : Finset Ω → ℤ := fun T => 2 * (rowRank U T : ℤ) - T.card
  have hw (T : Finset Ω) := invariant_half_rank_weak U hΩ hU htrans hinv T
  have hn (T : Finset Ω) : 0 ≤ f T := by dsimp [f]; have hh := hw T; omega
  have hf0 : f ∅ = 0 := by simp [f, rowRank_empty]
  have hsub (A B : Finset Ω) : f (A ∪ B) + f (A ∩ B) ≤ f A + f B := by
    have hr := rowRank_submodular U A B
    have hc := Finset.card_union_add_card_inter A B
    dsimp [f]
    omega
  have hfi (g : G) (T : Finset Ω) : f (orbitSet T g) = f T := by
    simp only [f, hinv, orbitSet_card]
  by_contra hbad
  have he : f S = 0 := by dsimp [f]; have hh := hw S; omega
  have hec := tight_complement f hf0 hn hsub htrans hfi S hs he
  have hcard : S.card + Sᶜ.card = 8 := by
    simpa [hΩ] using Finset.card_add_card_compl S
  have hc := hconn S hs ht
  dsimp [f] at he hec
  omega

end TightRankRigidity


section NoTripleBlocks

variable {Ω G K : Type*} [Fintype Ω] [DecidableEq Ω] [Group G] [Fintype G]
variable [MulAction G Ω] [Field K]

private theorem no_tight_triple (U : Submodule K (Ω → K))
    (hΩ : Fintype.card Ω = 8)
    (htrans : ∀ x y : Ω, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) S, rowRank U (orbitSet S g) = rowRank U S)
    (hstrict : ∀ S : Finset Ω, 0 < S.card → S.card < 8 →
      S.card + 1 ≤ 2 * rowRank U S)
    (C : Finset Ω) (hC : C.card = 3) (hrC : rowRank U C = 2)
    (hrCc : rowRank U Cᶜ = 3) : False := by
  classical
  have hcomp (S : Finset Ω) : Sᶜ.card + S.card = 8 := by
    simpa [hΩ] using Finset.card_compl_add_card S
  have hgc (g : G) : (orbitSet C g)ᶜ = orbitSet Cᶜ g := by
    ext i
    simp [mem_orbitSet]
  have hpair (A B : Finset Ω) (hA : A.card = 3) (hB : B.card = 3)
      (hrA : rowRank U A = 2) (hrB : rowRank U B = 2)
      (hrBc : rowRank U Bᶜ = 3) : A = B ∨ Disjoint A B := by
    have hi := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
    have hc := Finset.card_union_add_card_inter A B
    by_cases he : (A ∩ B).card = 3
    · left
      have heA : A ∩ B = A := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      apply Finset.eq_of_subset_of_card_le _ (by omega)
      intro x hx
      exact (Finset.mem_inter.mp (heA.symm ▸ hx)).2
    right
    have hzero : (A ∩ B).card = 0 := by
      by_contra hn
      have hcases : (A ∩ B).card = 1 ∨ (A ∩ B).card = 2 := by omega
      rcases hcases with h1 | h2
      · have hd : (A ∩ Bᶜ).card = 2 := by
          have hh := Finset.card_inter_add_card_sdiff A B
          rw [Finset.sdiff_eq_inter_compl] at hh
          omega
        have hu : (A ∪ Bᶜ).card = 6 := by
          have hh := Finset.card_union_add_card_inter A Bᶜ
          have hb := hcomp B
          omega
        have hs1 := hstrict (A ∩ Bᶜ) (by omega) (by omega)
        have hs2 := hstrict (A ∪ Bᶜ) (by omega) (by omega)
        have hsub := rowRank_submodular U A Bᶜ
        omega
      · have hu : (A ∪ B).card = 4 := by omega
        have hs1 := hstrict (A ∩ B) (by omega) (by omega)
        have hs2 := hstrict (A ∪ B) (by omega) (by omega)
        have hsub := rowRank_submodular U A B
        omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  let O := (Finset.univ : Finset G).image (orbitSet C)
  have horbit : O.biUnion _root_.id = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    obtain ⟨g, hg⟩ := htrans c i
    exact Finset.mem_biUnion.mpr ⟨orbitSet C g,
      Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, hg⟩⟩
  have hdis : (O : Set (Finset Ω)).PairwiseDisjoint _root_.id := by
    intro A hA B hB hne
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hB
    exact (hpair _ _ ((orbitSet_card C g).trans hC) ((orbitSet_card C h).trans hC)
      ((hinv g C).trans hrC) ((hinv h C).trans hrC)
      (by rw [hgc, hinv]; exact hrCc)).resolve_left hne
  have hcount := Finset.card_biUnion hdis
  have hcards : ∀ A ∈ O, A.card = 3 := by
    intro A hA
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hA
    exact (orbitSet_card C g).trans hC
  rw [horbit, Finset.card_univ, hΩ] at hcount
  have hsum : ∑ A ∈ O, A.card = O.card * 3 := by
    calc
      _ = ∑ _ ∈ O, 3 := Finset.sum_congr rfl (fun A hA => hcards A hA)
      _ = _ := by simp
  change 8 = ∑ A ∈ O, A.card at hcount
  rw [hsum] at hcount
  omega

end NoTripleBlocks


section CutRanks

variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [Field K]

private def coordinateExtend (S : Finset Ω) : (S → K) →ₗ[K] (Ω → K) where
  toFun x i := if h : i ∈ S then x ⟨i, h⟩ else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

private theorem coordinateExtend_injective (S : Finset Ω) :
    Function.Injective (coordinateExtend (K := K) S) := by
  intro x y h
  ext i
  simpa [coordinateExtend, i.property] using congrFun h i

def crossRank (n : (Ω → K) →ₗ[K] (Ω → K)) (S : Finset Ω) : ℕ :=
  finrank K (LinearMap.range ((coordinateProject S).comp (n.comp (coordinateExtend Sᶜ))))


theorem crossRank_matrix (n : (Ω → K) →ₗ[K] (Ω → K)) (S : Finset Ω) :
    ((LinearMap.toMatrix' n).submatrix (fun i : S => (i : Ω))
      (fun j : ↥(Sᶜ) => (j : Ω))).rank = crossRank n S := by
  let M := (LinearMap.toMatrix' n).submatrix (fun i : S => (i : Ω))
    (fun j : ↥(Sᶜ) => (j : Ω))
  have hext (j : ↥(Sᶜ)) : coordinateExtend (K := K) Sᶜ (Pi.single j 1) =
      Pi.single (j : Ω) 1 := by
    ext i
    by_cases hi : i ∈ Sᶜ
    · have his : i ∉ S := Finset.mem_compl.mp hi
      simp [coordinateExtend, his, Pi.single_apply, Subtype.ext_iff]
    · have his : i ∈ S := by simpa using hi
      have hij : i ≠ (j : Ω) := fun h => hi (h ▸ j.property)
      simp [coordinateExtend, his, Pi.single_apply, hij]
  have hmap : (coordinateExtend S).comp M.mulVecLin =
      (coordinateProject S).comp (n.comp (coordinateExtend Sᶜ)) := by
    apply (Pi.basisFun K ↥(Sᶜ)).ext
    intro j
    ext i
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, hext]
    by_cases hi : i ∈ S <;>
      simp [coordinateExtend, coordinateProject, hi, M, Matrix.submatrix_apply,
        LinearMap.toMatrix'_apply]
  change finrank K M.mulVecLin.range = _
  rw [crossRank, ← hmap, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (coordinateExtend S)
    (coordinateExtend_injective S) M.mulVecLin.range).finrank_eq

private theorem cross_rank_bound (U : Submodule K (Ω → K))
    (n : (Ω → K) →ₗ[K] (Ω → K)) (hker : n.ker = U) (hrange : n.range = U)
    (hΩ : Fintype.card Ω = 8) (hU : finrank K U = 4) (S : Finset Ω) :
    2 * rowRank U S ≤ S.card + crossRank n S := by
  let f : (↥(Sᶜ) → K) →ₗ[K] U := (n.comp (coordinateExtend Sᶜ)).codRestrict U (by
    intro x
    rw [← hrange]
    exact ⟨coordinateExtend Sᶜ x, rfl⟩)
  let g := (coordinateProject (K := K) S).domRestrict U
  let j : f.ker →ₗ[K] coordinateKernel U S :=
    { toFun := fun x => ⟨⟨coordinateExtend Sᶜ x, by
        exact hker ▸ (show coordinateExtend Sᶜ x ∈ n.ker from
          congrArg Subtype.val x.property)⟩, by
        rw [mem_coordinateKernel]
        intro i hi
        simp [coordinateExtend, hi]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        exact map_add (coordinateExtend (K := K) Sᶜ) (x : ↥(Sᶜ) → K) (y : ↥(Sᶜ) → K)
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        exact map_smul (coordinateExtend (K := K) Sᶜ) c (x : ↥(Sᶜ) → K) }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply coordinateExtend_injective Sᶜ
    exact congrArg (fun z : coordinateKernel U S => (z : Ω → K)) h
  have hkf := LinearMap.finrank_le_finrank_of_injective hj
  have hkg : finrank K g.ker = finrank K (coordinateKernel U S) := rfl
  have hcomp : finrank K (g.comp f).ker ≤ finrank K g.ker + finrank K f.ker := by
    have H := f.lift_rank_comap_le g.ker
    simp only [← Submodule.finrank_eq_rank, Cardinal.lift_natCast] at H
    exact_mod_cast H
  have hnull := (g.comp f).finrank_range_add_finrank_ker
  have hr : finrank K (g.comp f).range = crossRank n S := rfl
  have hc : Sᶜ.card + S.card = 8 := by
    simpa [hΩ] using Finset.card_compl_add_card S
  have hdim : finrank K (↥(Sᶜ) → K) = Sᶜ.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hu := coordinate_rank_nullity U S
  rw [hU] at hu
  rw [hr, hdim] at hnull
  omega


theorem cut_free_of_actual_ranks {G : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (U : Submodule K (Ω → K)) (n : (Ω → K) →ₗ[K] (Ω → K))
    (hker : n.ker = U) (hrange : n.range = U)
    (hΩ : Fintype.card Ω = 8) (hU : finrank K U = 4)
    (htrans : ∀ x y : Ω, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) S, rowRank U (orbitSet S g) = rowRank U S)
    (hstrict : ∀ S : Finset Ω, 0 < S.card → S.card < 8 →
      S.card + 1 ≤ 2 * rowRank U S)
    (S : Finset Ω) (hS2 : 2 ≤ S.card) (hS6 : S.card ≤ 6) :
    2 ≤ crossRank n S ∨ 2 ≤ crossRank n Sᶜ := by
  by_contra hbad
  push_neg at hbad
  have hb1 := cross_rank_bound U n hker hrange hΩ hU S
  have hb2 := cross_rank_bound U n hker hrange hΩ hU Sᶜ
  have hc : Sᶜ.card + S.card = 8 := by
    simpa [hΩ] using Finset.card_compl_add_card S
  have hs1 := hstrict S (by omega) (by omega)
  have hs2 := hstrict Sᶜ (by omega) (by omega)
  have hcases : (S.card = 3 ∧ rowRank U S = 2 ∧ rowRank U Sᶜ = 3) ∨
      (Sᶜ.card = 3 ∧ rowRank U Sᶜ = 2 ∧ rowRank U S = 3) := by omega
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact no_tight_triple U hΩ htrans hinv hstrict S h1 h2 h3
  · exact no_tight_triple U hΩ htrans hinv hstrict Sᶜ h1 h2 (by simpa using h3)

end CutRanks

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
