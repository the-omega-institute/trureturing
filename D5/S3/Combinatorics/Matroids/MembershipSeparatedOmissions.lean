/- GID: D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/MembershipSeparatedOmissions
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Common-pivot omitted bases distinguished by membership classes. -/

module

public import D5.S3.Combinatorics.Matroids.PrivatePairOmissionFamily
public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Conditions and counts for omitted sets distinguished by membership classes. -/

namespace D5.S3.Combinatorics.Matroids.MembershipSeparatedOmissions

open Finset
set_option autoImplicit false

/-- Distinct omitted sets differ on a membership class containing at least two indices. -/
def HasSeparatedMembership {I : Type*} (family : Finset (Finset I)) : Prop :=
  ∀ F ∈ family, ∀ G ∈ family, F ≠ G → ∃ i j, i ≠ j ∧
    (∀ T ∈ family, i ∈ T ↔ j ∈ T) ∧
    ((i ∈ F ∧ i ∉ G) ∨ (i ∈ G ∧ i ∉ F))

theorem HasSeparatedMembership.mono {I : Type*} {family subfamily : Finset (Finset I)}
    (h : HasSeparatedMembership family) (hsub : subfamily ⊆ family) :
    HasSeparatedMembership subfamily := by
  intro F hF G hG hne
  obtain ⟨i, j, hij, hsame, hdiff⟩ := h F (hsub hF) G (hsub hG) hne
  exact ⟨i, j, hij, fun T hT => hsame T (hsub hT), hdiff⟩

private theorem inter_le_of_two_in_difference {I : Type*} [DecidableEq I] {F G : Finset I}
    {i j : I} (hij : i ≠ j) (hi : i ∈ F) (hj : j ∈ F) (hiG : i ∉ G) (hjG : j ∉ G) :
    (F ∩ G).card + 2 ≤ F.card := by
  have hiInter : i ∉ F ∩ G := fun h => hiG (mem_inter.mp h).2
  have hjInter : j ∉ F ∩ G := fun h => hjG (mem_inter.mp h).2
  have hiInsert : i ∉ insert j (F ∩ G) := by simp [hij, hiInter]
  have le := card_le_card (insert_subset hi (insert_subset hj inter_subset_left) :
    insert i (insert j (F ∩ G)) ⊆ F)
  rwa [card_insert_of_notMem hiInsert, card_insert_of_notMem hjInter] at le

theorem HasSeparatedMembership.inter_card_add_two_le {I : Type*} [DecidableEq I]
    {family : Finset (Finset I)} (h : HasSeparatedMembership family)
    {F G : Finset I} (hF : F ∈ family) (hG : G ∈ family) (hne : F ≠ G)
    (hsize : F.card = G.card) : (F ∩ G).card + 2 ≤ F.card := by
  obtain ⟨i, j, hij, hsame, hdiff⟩ := h F hF G hG hne
  rcases hdiff with hs | ht
  · exact inter_le_of_two_in_difference hij hs.1 ((hsame F hF).mp hs.1) hs.2
      (fun hj => hs.2 ((hsame G hG).mpr hj))
  · have le := inter_le_of_two_in_difference hij ht.1 ((hsame G hG).mp ht.1) ht.2
      (fun hj => ht.2 ((hsame F hF).mpr hj))
    simpa only [inter_comm G F, ← hsize] using le


/-- Private pairs separate their own omitted set from all other members. -/
theorem HasSeparatedMembership.of_private_pairs {I : Type*} {family : Finset (Finset I)}
    (h : PrivatePairOmissionFamily.HasPrivatePairs family) :
    HasSeparatedMembership family := by
  classical
  intro F hF G hG hne
  obtain ⟨i, hi, j, hj, hij, hother⟩ := h F hF
  refine ⟨i, j, hij, ?_, Or.inl ⟨hi, (hother G hG hne.symm).1⟩⟩
  intro T hT
  by_cases ht : T = F
  · subst T
    simp [hi, hj]
  · obtain ⟨hiT, hjT⟩ := hother T hT ht
    simp [hiT, hjT]

private theorem lower_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x : I) {family : Finset (Finset I)} {s : ℕ} (hs : 0 < s)
    (hsize : ∀ A ∈ family, A.card = s)
    (hsep : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card + 2 ≤ s) :
    family.card ≤ (Fintype.card I - 1).choose (s - 1) := by
  have hdelete (A : family) : ∃ R : Finset I, R ⊆ A.val ∧ x ∉ R ∧ R.card = s - 1 := by
    by_cases hx : x ∈ A.val
    · exact ⟨A.val.erase x, erase_subset _ _, notMem_erase _ _,
        by rw [card_erase_of_mem hx, hsize _ A.prop]⟩
    · have hpos : 0 < A.val.card := by simpa [hsize _ A.prop] using hs
      obtain ⟨y, hy⟩ := card_pos.mp hpos
      exact ⟨A.val.erase y, erase_subset _ _, fun h => hx (mem_of_mem_erase h),
        by rw [card_erase_of_mem hy, hsize _ A.prop]⟩
  choose delete hsub hxout hcard using hdelete
  let remaining := (univ : Finset I).erase x
  let target := remaining.powersetCard (s - 1)
  let embed (A : family) : target :=
    ⟨delete A, mem_powersetCard.mpr
      ⟨fun y hy => mem_erase.mpr ⟨fun h => hxout A (h ▸ hy), mem_univ _⟩, hcard A⟩⟩
  have hinj : Function.Injective embed := by
    intro A B heq
    apply Subtype.ext
    by_contra hne
    have heq' : delete A = delete B := congrArg Subtype.val heq
    have hcontained : delete A ⊆ A.val ∩ B.val := subset_inter (hsub A) (heq' ▸ hsub B)
    have hle := card_le_card hcontained
    rw [hcard A] at hle
    have hsmall := hsep A.val A.prop B.val B.prop hne
    omega
  have hle := Fintype.card_le_of_injective embed hinj
  simp only [Fintype.card_coe] at hle
  have htarget : target.card = (Fintype.card I - 1).choose (s - 1) := by
    change (remaining.powersetCard (s - 1)).card = _
    rw [card_powersetCard]
    simp [remaining, card_erase_of_mem (mem_univ x)]
  rwa [htarget] at hle

private theorem multiplicity_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (x : I) {family : Finset (Finset I)} {s : ℕ}
    (hs : 0 < s) (hlt : s < Fintype.card I)
    (hsize : ∀ A ∈ family, A.card = s)
    (hsep : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card + 2 ≤ s) :
    family.card ≤ (Fintype.card I - 1).choose (s - 1) ∧
      family.card ≤ (Fintype.card I - 1).choose s := by
  refine ⟨lower_bound x hs hsize hsep, ?_⟩
  let n := Fintype.card I
  have hcomp_size : ∀ A ∈ family.compls, A.card = n - s := by
    intro A hA
    have hab := Finset.mem_compls.mp hA
    rw [← compl_compl A, Finset.card_compl, hsize Aᶜ hab]
  have hcomp_sep :
      ∀ A ∈ family.compls, ∀ B ∈ family.compls, A ≠ B → (A ∩ B).card + 2 ≤ n - s := by
    intro A hA B hB hne
    have hab := Finset.mem_compls.mp hA
    have hbb := Finset.mem_compls.mp hB
    have hne' : Aᶜ ≠ Bᶜ := fun h => hne (compl_injective h)
    have hsmall := hsep Aᶜ hab Bᶜ hbb hne'
    have hunion := card_union_add_card_inter Aᶜ Bᶜ
    rw [hsize Aᶜ hab, hsize Bᶜ hbb] at hunion
    rw [← compl_compl A, ← compl_compl B, ← Finset.compl_union, Finset.card_compl]
    have hle := card_le_univ (Aᶜ ∪ Bᶜ)
    change (Aᶜ ∪ Bᶜ).card ≤ n at hle
    change s < n at hlt
    change n - (Aᶜ ∪ Bᶜ).card + 2 ≤ n - s
    omega
  have h := lower_bound x (Nat.sub_pos_of_lt hlt) hcomp_size hcomp_sep
  have hsymm : (n - 1).choose (n - s - 1) = (n - 1).choose s := by
    have hsle : s ≤ n - 1 := by dsimp [n]; omega
    rw [show n - s - 1 = n - 1 - s by omega, Nat.choose_symm hsle]
  change family.compls.card ≤ (n - 1).choose (n - s - 1) at h
  rwa [Finset.card_compls, hsymm] at h

/-- The two uniform multiplicities bound the size of a pairwise separated family. -/
theorem omission_multiplicities {k d : ℕ} (root : Fin (k + 2))
    {family : Finset (Finset (Fin (k + 2)))}
    (hd : 1 ≤ d) (hr : d < k)
    (hsize : ∀ T ∈ family, T.card = d + 2)
    (hroot : ∀ T ∈ family, root ∈ T)
    (hinter : ∀ T ∈ family, ∀ U ∈ family, T ≠ U → (T ∩ U).card + 2 ≤ d + 2) :
    family.card ≤ k.choose d ∧ family.card ≤ k.choose (d + 1) := by
  classical
  let I := {i : Fin (k + 2) // i ≠ root}
  let petal (T : Finset (Fin (k + 2))) : Finset I := T.subtype (· ≠ root)
  have hdim : Fintype.card I = k + 1 := by
    change Fintype.card {i : Fin (k + 2) // i ≠ root} = _
    rw [Fintype.card_subtype, filter_ne', card_erase_of_mem (mem_univ _)]
    simp
  obtain ⟨x⟩ : Nonempty I := Fintype.card_pos_iff.mp (by rw [hdim]; omega)
  have hcard (T : Finset (Fin (k + 2))) (hT : root ∈ T) : (petal T).card = T.card - 1 := by
    change (T.subtype (· ≠ root)).card = _
    rw [Finset.card_subtype, filter_ne', card_erase_of_mem hT]
  have petal_mem (T : Finset (Fin (k + 2))) (i : I) : i ∈ petal T ↔ i.val ∈ T := by
    exact Finset.mem_subtype
  have hinj : (↑family : Set (Finset (Fin (k + 2)))).InjOn petal := by
    intro T hT U hU he
    ext i
    by_cases hi : i = root
    · subst i
      simp [hroot T hT, hroot U hU]
    · let j : I := ⟨i, hi⟩
      have h := congrArg (fun R : Finset I => j ∈ R) he
      exact (petal_mem T j).symm.trans ((iff_of_eq h).trans (petal_mem U j))
  let petals := family.image petal
  have hpetals : ∀ F ∈ petals, F.card = d + 1 := by
    intro F hF
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hF
    rw [hcard T (hroot T hT), hsize T hT]
    omega
  have hpetalSep : ∀ F ∈ petals, ∀ G ∈ petals, F ≠ G → (F ∩ G).card + 2 ≤ d + 1 := by
    intro F hF G hG hne
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hF
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hG
    have hne' : T ≠ U := fun e => hne (congrArg petal e)
    have h := hinter T hT U hU hne'
    have hrootInter := mem_inter.mpr ⟨hroot T hT, hroot U hU⟩
    have hcommute : petal T ∩ petal U = petal (T ∩ U) := by
      ext i
      simp only [mem_inter, petal_mem]
    rw [hcommute, hcard _ hrootInter]
    have hpos := card_pos.mpr ⟨root, hrootInter⟩
    omega
  obtain ⟨a, b⟩ := multiplicity_bounds x (by omega) (show d + 1 < Fintype.card I by omega)
    hpetals hpetalSep
  have heq : petals.card = family.card := card_image_of_injOn hinj
  rw [heq, hdim] at a b
  simpa using And.intro a b

end D5.S3.Combinatorics.Matroids.MembershipSeparatedOmissions
