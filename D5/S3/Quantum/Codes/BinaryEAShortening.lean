/- GID: D5/S3/Quantum/Codes/BinaryEAShortening
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAShortening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shortening on surjective radical coordinates and the five-site spread obstruction. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.Pi
import OmegaBuild.Commands

/-! Binary symplectic shortening and the five-site spread argument. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Codes.BinaryEAShortening

open scoped BigOperators
open D5.S3.Quantum.Information.BinaryLagrangianGraphForm (sp)
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (spForm sp_alt sp_nondegenerate)

local notation "F₂" => ZMod 2
local notation "Symbol" => (F₂ × F₂)
local notation "Word" n:arg => ((Fin n → F₂) × (Fin n → F₂))

/-- Read the two binary coordinates at a single site. -/
def site {n : ℕ} (i : Fin n) : Word n →ₗ[F₂] Symbol where
  toFun x := (x.1 i, x.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Joint projection to the sites in a finite set. -/
def restrictSites {n : ℕ} (I : Finset (Fin n)) : Word n →ₗ[F₂] (I → Symbol) :=
  LinearMap.pi (fun i : I => site i)

/-- The zero sites among a specified set of coordinates. -/
def zeroSites {n : ℕ} (I : Finset (Fin n)) (x : Word n) : Finset (Fin n) :=
  I.filter (fun i => site i x = 0)

/-- The subspace of words that vanish on every shortened site. -/
def shortened {n : ℕ} (I : Finset (Fin n)) (S : Submodule F₂ (Word n)) :
    Submodule F₂ (Word n) :=
  S ⊓ (restrictSites I).ker

private lemma mem_shortened {n : ℕ} {I : Finset (Fin n)} {S : Submodule F₂ (Word n)}
    {x : Word n} : x ∈ shortened I S ↔ x ∈ S ∧ ∀ i ∈ I, site i x = 0 := by
  change (x ∈ S ∧ restrictSites I x = 0) ↔ _
  simp only [and_congr_right_iff]
  intro _
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.property

private lemma finrank_symbols {n : ℕ} (I : Finset (Fin n)) :
    Module.finrank F₂ (I → Symbol) = 2 * I.card := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_comm]

private lemma shortened_rank_nullity {n : ℕ} (I : Finset (Fin n))
    (S : Submodule F₂ (Word n)) :
    Module.finrank F₂ ((restrictSites I).domRestrict S).range +
      Module.finrank F₂ (shortened I S) = Module.finrank F₂ S := by
  have h := ((restrictSites I).domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.ker_domRestrict] at h
  have hk := Submodule.finrank_map_subtype_eq S ((restrictSites I).ker.comap S.subtype)
  rw [Submodule.map_comap_subtype, ← shortened] at hk
  rwa [← hk] at h

private lemma finrank_shortened_of_surjective {n : ℕ} (I : Finset (Fin n))
    (S : Submodule F₂ (Word n))
    (hS : Function.Surjective ((restrictSites I).domRestrict S)) :
    Module.finrank F₂ (shortened I S) + 2 * I.card = Module.finrank F₂ S := by
  have h := shortened_rank_nullity I S
  rw [LinearMap.range_eq_top.mpr hS, finrank_top, finrank_symbols] at h
  omega

/-- If the radical projects onto the removed symbols, every codeword can be shifted
by a radical word into the shortened code, with the pairing of any two words preserved. -/
theorem shorten_of_radical_surjective {n : ℕ} (I : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hHU : H ≤ U)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (honto : Function.Surjective ((restrictSites I).domRestrict H)) :
    Module.finrank F₂ (shortened I H) + 2 * I.card = Module.finrank F₂ H ∧
    Module.finrank F₂ (shortened I U) + 2 * I.card = Module.finrank F₂ U ∧
    ∀ x ∈ U, ∃ y ∈ shortened I U, x - y ∈ H ∧
      ∀ u ∈ U, spForm n y u = spForm n x u := by
  have hontoU : Function.Surjective ((restrictSites I).domRestrict U) := by
    intro w
    obtain ⟨h, hh⟩ := honto w
    exact ⟨⟨h, hHU h.property⟩, hh⟩
  refine ⟨finrank_shortened_of_surjective I H honto,
    finrank_shortened_of_surjective I U hontoU, ?_⟩
  intro x hx
  obtain ⟨h, hh⟩ := honto (restrictSites I x)
  change restrictSites I (h : Word n) = restrictSites I x at hh
  refine ⟨x - h, ⟨U.sub_mem hx (hHU h.property), ?_⟩, ?_, ?_⟩
  · change restrictSites I (x - h) = 0
    rw [map_sub, hh, sub_self]
  · simpa only [sub_sub_cancel] using h.property
  · intro u hu
    simp [map_sub, horth h h.property u hu]

private lemma zeroSites_shortened_bound {n k : ℕ} (I : Finset (Fin n))
    (H U : Submodule F₂ (Word n))
    (hzeros : ∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ k)
    {x : Word n} (hx : x ∈ shortened I U) (hxH : x ∉ shortened I H) :
    (zeroSites Iᶜ x).card + I.card ≤ k := by
  obtain ⟨hxU, hxI⟩ := mem_shortened.mp hx
  have hnH : x ∉ H := fun h => hxH (mem_shortened.mpr ⟨h, hxI⟩)
  have hunion : zeroSites Iᶜ x ∪ I = zeroSites Finset.univ x := by
    ext i
    by_cases hi : i ∈ I
    · simp [zeroSites, hi, hxI i hi]
    · simp [zeroSites, hi]
  have hdis : Disjoint (zeroSites Iᶜ x) I := by
    refine Finset.disjoint_left.mpr (fun i hi hi' => ?_)
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hi).1) hi'
  rw [← Finset.card_union_of_disjoint hdis, hunion]
  exact hzeros x hxU hnH

private lemma zeroSites_at_most_one_of_unique {n : ℕ} (J : Finset (Fin n))
    (x : Word n) (h : (zeroSites J x).card ≤ 1) :
    ∀ i ∈ J, ∀ j ∈ J, site i x = 0 → site j x = 0 → i = j := by
  intro i hi j hj hix hjx
  exact Finset.card_le_one.mp h i (Finset.mem_filter.mpr ⟨hi, hix⟩)
    j (Finset.mem_filter.mpr ⟨hj, hjx⟩)

private lemma zeroSites_exactly_one_of_finrank_four {n : ℕ} (J : Finset (Fin n))
    (G : Submodule F₂ (Word n)) (hJ : J.card = 5) (hG : Module.finrank F₂ G = 4)
    (hzero : ∀ x ∈ G, x ≠ 0 → (zeroSites J x).card ≤ 1) :
    ∀ x ∈ G, x ≠ 0 → (zeroSites J x).card = 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let K (i : Fin n) : Finset G := Finset.univ.filter (fun x => x ≠ 0 ∧ site i x = 0)
  have hK (i : Fin n) : 3 ≤ (K i).card := by
    let f := (site i).domRestrict G
    let : Fintype f.ker := Fintype.ofFinite f.ker
    have hdim := f.finrank_range_add_finrank_ker
    have hdimRange : Module.finrank F₂ f.range ≤ 2 :=
      (Submodule.finrank_le f.range).trans (by simp [Module.finrank_prod])
    have hdimKer : 2 ≤ Module.finrank F₂ f.ker := by omega
    have hcardKer : 4 ≤ Fintype.card f.ker := by
      rw [Module.card_eq_pow_finrank (K := F₂), ZMod.card]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hdimKer
    have he : (Finset.univ.image (fun a : f.ker => (a : G))) = insert 0 (K i) := by
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
        K, Finset.mem_filter]
      constructor
      · rintro ⟨b, rfl⟩
        by_cases he : (b : G) = 0
        · exact Or.inl he
        · exact Or.inr ⟨he, b.property⟩
      · rintro (rfl | ⟨_, hz⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨⟨a, hz⟩, rfl⟩
    have hcard := Finset.card_image_of_injective
      (s := (Finset.univ : Finset f.ker)) Subtype.val_injective
    rw [he, Finset.card_insert_of_notMem (by simp [K]), Finset.card_univ] at hcard
    omega
  have hdis : (J : Set (Fin n)).PairwiseDisjoint K := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr (fun x hxi hxj => hij ?_)
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    have hx : (x : Word n) ≠ 0 := by simpa using hxi.1
    exact zeroSites_at_most_one_of_unique J x (hzero x x.property hx)
      i hi j hj hxi.2 hxj.2
  let nonzero : Finset G := Finset.univ.erase 0
  have hsub : J.biUnion K ⊆ nonzero := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    simpa [nonzero] using (Finset.mem_filter.mp hi).2.1
  have hnonzero : nonzero.card = 15 := by
    dsimp only [nonzero]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
      Module.card_eq_pow_finrank (K := F₂), ZMod.card, hG]
    decide
  have hsum : 15 ≤ (J.biUnion K).card := by
    rw [Finset.card_biUnion hdis]
    calc
      15 = ∑ _i ∈ J, 3 := by simp [hJ]
      _ ≤ ∑ i ∈ J, (K i).card := Finset.sum_le_sum (fun i _ => hK i)
  have hEq := Finset.eq_of_subset_of_card_le hsub (hnonzero ▸ hsum)
  intro x hx hnx
  have hx' : (⟨x, hx⟩ : G) ∈ J.biUnion K := by
    rw [hEq]
    simp [nonzero, Subtype.ext_iff, hnx]
  obtain ⟨i, hi, hix⟩ := Finset.mem_biUnion.mp hx'
  have hm : i ∈ zeroSites J x := Finset.mem_filter.mpr ⟨hi, (Finset.mem_filter.mp hix).2.2⟩
  have hpos := Finset.card_pos.mpr ⟨i, hm⟩
  exact Nat.le_antisymm (hzero x hx hnx) hpos

private lemma local_pairing_zero_indicators (a b : Symbol) :
    a.1 * b.2 + a.2 * b.1 =
      1 + (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) +
        (if a + b = 0 then 1 else 0) := by
  revert a b
  decide

/-- Five sites and four binary dimensions force the restricted Gram to vanish when
each nonzero word vanishes at most once on those sites. -/
theorem five_site_gram_zero {n : ℕ} (J : Finset (Fin n))
    (G : Submodule F₂ (Word n)) (hJ : J.card = 5) (hG : Module.finrank F₂ G = 4)
    (hzero : ∀ x ∈ G, x ≠ 0 → (zeroSites J x).card ≤ 1) :
    ∀ x ∈ G, ∀ y ∈ G, ∑ i ∈ J, (x.1 i * y.2 i + x.2 i * y.1 i) = 0 := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    exact Finset.sum_eq_zero (fun i _ => by
      rw [mul_comm (x.2 i) (x.1 i), CharTwo.add_self_eq_zero])
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hsum0 : x + y ≠ 0 := by
    intro h
    apply hxy
    apply Prod.ext <;> funext i
    · exact CharTwo.add_eq_zero.mp (congrFun (congrArg Prod.fst h) i)
    · exact CharTwo.add_eq_zero.mp (congrFun (congrArg Prod.snd h) i)
  have hcount (z : Word n) (hz : z ∈ G) (hz0 : z ≠ 0) :
      ∑ i ∈ J, (if site i z = 0 then (1 : F₂) else 0) = 1 := by
    rw [← Finset.sum_filter, Finset.sum_const]
    change (zeroSites J z).card • (1 : F₂) = 1
    rw [zeroSites_exactly_one_of_finrank_four J G hJ hG hzero z hz hz0, one_nsmul]
  calc
    (∑ i ∈ J, (x.1 i * y.2 i + x.2 i * y.1 i)) =
      ∑ i ∈ J, ((1 : F₂) + (if site i x = 0 then 1 else 0) +
        (if site i y = 0 then 1 else 0) + (if site i (x + y) = 0 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_add]
      exact local_pairing_zero_indicators (site i x) (site i y)
    _ = 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hcount x hx hx0, hcount y hy hy0, hcount (x + y) (G.add_mem hx hy) hsum0,
        Finset.sum_const, hJ]
      decide

/-- At length seven, two sites with a surjective joint radical projection are
incompatible with an eight-dimensional code and the three-zero bound. -/
theorem length_seven_no_surjective_radical_pair
    (H U : Submodule F₂ (Word 7)) (hHU : H ≤ U)
    (hH : Module.finrank F₂ H = 4) (hU : Module.finrank F₂ U = 8)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm 7 h u = 0)
    (hzeros : ∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ 3)
    (I : Finset (Fin 7)) (hI : I.card = 2)
    (honto : Function.Surjective ((restrictSites I).domRestrict H)) : False := by
  obtain ⟨hHd, hUd, hrep⟩ := shorten_of_radical_surjective I H U hHU horth honto
  have hH' : shortened I H = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hU' : Module.finrank F₂ (shortened I U) = 4 := by omega
  have hJ : (Iᶜ : Finset (Fin 7)).card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hI]
  have hzero' : ∀ x ∈ shortened I U, x ≠ 0 → (zeroSites Iᶜ x).card ≤ 1 := by
    intro x hx hnx
    have hnH : x ∉ shortened I H := by simpa [hH'] using hnx
    have hh := zeroSites_shortened_bound I H U hzeros hx hnH
    omega
  have hshort : ∀ x ∈ shortened I U, ∀ y ∈ shortened I U, spForm 7 x y = 0 := by
    intro x hx y hy
    have hGram := five_site_gram_zero Iᶜ (shortened I U) hJ hU' hzero' x hx y hy
    change sp x y = 0
    unfold sp
    rw [← Finset.sum_add_sum_compl I]
    have hvanish : ∀ i ∈ I, (x.1 i * y.2 i + x.2 i * y.1 i) = 0 := by
      intro i hi
      have hh := (mem_shortened.mp hx).2 i hi
      change (x.1 i, x.2 i) = (0, 0) at hh
      simp [Prod.mk.inj hh]
    rw [Finset.sum_eq_zero hvanish, hGram, add_zero]
  have hUiso : U ≤ (spForm 7).orthogonal U := by
    intro y hy x hx
    obtain ⟨a, ha, _, hax⟩ := hrep x hx
    obtain ⟨b, hb, _, hby⟩ := hrep y hy
    have hs (v w : Word 7) : spForm 7 v w = spForm 7 w v := by
      simpa only [CharTwo.neg_eq] using (sp_alt 7).neg_eq v w
    change spForm 7 x y = 0
    rw [← hax y hy, hs a y]
    rw [← hby a (mem_shortened.mp ha).1]
    exact hshort b hb a ha
  have hmono := Submodule.finrank_mono hUiso
  have hd := (spForm 7).finrank_orthogonal (sp_nondegenerate 7) U
  have hV : Module.finrank F₂ (Word 7) = 14 := by simp [Module.finrank_prod]
  rw [hV, hU] at hd
  omega

private lemma restrictSites_apply {n : ℕ} {I : Finset (Fin n)} (x : Word n) (i : I) :
    restrictSites I x i = site i x := rfl

private lemma singleton_shortened_rank {n : ℕ} (S : Submodule F₂ (Word n)) (i : Fin n) :
    Module.finrank F₂ (shortened {i} S) + 2 ≥ Module.finrank F₂ S := by
  have h := shortened_rank_nullity {i} S
  have hb := Submodule.finrank_le ((restrictSites {i}).domRestrict S).range
  simp only [finrank_symbols, Finset.card_singleton, Nat.mul_one] at hb
  omega

private def words {n : ℕ} (S : Submodule F₂ (Word n)) : Finset (Word n) :=
  let _ : Fintype (S : Set (Word n)) := Fintype.ofFinite _
  (S : Set (Word n)).toFinset

private lemma mem_words {n : ℕ} {S : Submodule F₂ (Word n)} {x : Word n} :
    x ∈ words S ↔ x ∈ S := by
  let : Fintype (S : Set (Word n)) := Fintype.ofFinite _
  unfold words
  exact Set.mem_toFinset

private lemma card_words {n : ℕ} (S : Submodule F₂ (Word n)) :
    (words S).card = 2 ^ Module.finrank F₂ S := by
  let : Fintype (S : Set (Word n)) := Fintype.ofFinite _
  rw [words, Set.toFinset_card]
  change Fintype.card S = _
  rw [Module.card_eq_pow_finrank (K := F₂), ZMod.card]

private lemma radical_singleton_kernel {n : ℕ} (H : Submodule F₂ (Word n)) (i : Fin n)
    (hH : Module.finrank F₂ H = 2) (hne : (site i).domRestrict H ≠ 0)
    (hns : ¬ Function.Surjective ((site i).domRestrict H)) :
    ∃ h ∈ H, h ≠ 0 ∧ site i h = 0 ∧ words (shortened {i} H) = {0, h} := by
  let f := (site i).domRestrict H
  have hr := f.finrank_range_add_finrank_ker
  have hrPos : 0 < Module.finrank F₂ f.range := by
    by_contra hh
    have hz : Module.finrank F₂ f.range = 0 := Nat.eq_zero_of_not_pos hh
    exact hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
  have hrSmall : Module.finrank F₂ f.range < 2 := by
    by_contra! hh
    have htop : f.range = ⊤ := Submodule.eq_top_of_finrank_eq (by
      have hle := Submodule.finrank_le f.range
      have hdim : Module.finrank F₂ Symbol = 2 := by simp [Module.finrank_prod]
      omega)
    exact hns (LinearMap.range_eq_top.mp htop)
  have hker : Module.finrank F₂ f.ker = 1 := by omega
  have hkerMap : f.ker.map H.subtype = shortened {i} H := by
    ext x
    constructor
    · rintro ⟨y, hky, rfl⟩
      refine mem_shortened.mpr ⟨y.property, fun j hj => ?_⟩
      rw [Finset.mem_singleton.mp hj]
      exact LinearMap.mem_ker.mp hky
    · intro hx
      obtain ⟨hxH, hx0⟩ := mem_shortened.mp hx
      exact ⟨⟨x, hxH⟩, hx0 i (by simp), rfl⟩
  have hcount : (words (shortened {i} H)).card = 2 := by
    rw [card_words, ← hkerMap, Submodule.finrank_map_subtype_eq, hker]
    decide
  have hz : 0 ∈ words (shortened {i} H) := mem_words.mpr (Submodule.zero_mem _)
  obtain ⟨h, hh, hne0⟩ := Finset.exists_mem_ne (by omega : 1 < (words (shortened {i} H)).card) 0
  obtain ⟨hhH, hh0⟩ := mem_shortened.mp (mem_words.mp hh)
  refine ⟨h, hhH, hne0, hh0 i (by simp), ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hz hh
  · rw [hcount, Finset.card_pair (Ne.symm hne0)]

private lemma local_pairing_nonzero {n : ℕ} {x : Word n} {i : Fin n} (hx : site i x ≠ 0) :
    ∃ b : Symbol, (x.1 i * b.2 + x.2 i * b.1) ≠ 0 := by
  have h : ∀ a : Symbol, a ≠ 0 → ∃ b : Symbol, (a.1 * b.2 + a.2 * b.1) ≠ 0 := by decide
  exact h (site i x) hx

private lemma triple_projection_surjective {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hU : Module.finrank F₂ U = 6)
    (hzero : ∀ x ∈ U, x ∉ H → (zeroSites J x).card ≤ 2)
    {T : Finset (Fin n)} (hTJ : T ⊆ J) (hT : T.card = 3)
    (hHinj : Function.Injective ((restrictSites T).domRestrict H)) :
    Function.Surjective ((restrictSites T).domRestrict U) := by
  have hui : Function.Injective ((restrictSites T).domRestrict U) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    change restrictSites T (x : Word n) = 0 at hx
    have hT0 (i : Fin n) (hi : i ∈ T) : site i x = 0 := congrFun hx ⟨i, hi⟩
    have hxH : (x : Word n) ∈ H := by
      by_contra hnh
      have hc := Finset.card_le_card
        (show T ⊆ zeroSites J x from fun i hi => Finset.mem_filter.mpr ⟨hTJ hi, hT0 i hi⟩)
      have hb := hzero x x.property hnh
      omega
    have h' : (⟨(x : Word n), hxH⟩ : H) = 0 := hHinj (by simpa using hx)
    exact Subtype.ext (congrArg (fun y : H => (y : Word n)) h')
  have hdim : Module.finrank F₂ U = Module.finrank F₂ (T → Symbol) := by
    rw [hU, finrank_symbols, hT]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hui

private lemma triple_surjectivity_obstruction {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hU : Module.finrank F₂ U = 6)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (hzero : ∀ x ∈ U, x ∉ H → (zeroSites J x).card ≤ 2)
    {T : Finset (Fin n)} (hTJ : T ⊆ J) (hT : T.card = 3)
    (hHinj : Function.Injective ((restrictSites T).domRestrict H))
    {h : Word n} (hhH : h ∈ H) (hh0 : ∀ i ∉ T, site i h = 0)
    {j : Fin n} (hj : j ∈ T) (hnz : site j h ≠ 0) : False := by
  have hsurj := triple_projection_surjective J H U hU hzero hTJ hT hHinj
  obtain ⟨b, hb⟩ := local_pairing_nonzero hnz
  obtain ⟨u, hu⟩ := hsurj (fun i => if i.val = j then b else 0)
  have hu' (i : Fin n) (hi : i ∈ T) : site i u = if i = j then b else 0 :=
    congrFun hu ⟨i, hi⟩
  have hp := horth h hhH u u.property
  change sp h (u : Word n) = 0 at hp
  have hs (i : Fin n) (hi : i ≠ j) :
      h.1 i * (u : Word n).2 i + h.2 i * (u : Word n).1 i = 0 := by
    by_cases hit : i ∈ T
    · have hh := hu' i hit
      simp only [ite_eq_right hi] at hh
      change (u.val.1 i, u.val.2 i) = (0, 0) at hh
      simp [Prod.mk.inj hh]
    · have hh := hh0 i hit
      change (h.1 i, h.2 i) = (0, 0) at hh
      simp [Prod.mk.inj hh]
  rw [sp, Finset.sum_eq_single j (fun i _ hi => hs i hi) (by simp)] at hp
  have hju : site j u = b := by simpa using hu' j hj
  apply hb
  rw [← hju]
  exact hp

/-- A six-dimensional shortened code on seven surviving sites is impossible if its
two-dimensional radical is supported on those sites with each projection of rank at most one. -/
theorem seven_surviving_sites_no_rank_one_radical {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hHU : H ≤ U)
    (hJ : J.card = 7) (hH : Module.finrank F₂ H = 2) (hU : Module.finrank F₂ U = 6)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (hsupp : ∀ h ∈ H, ∀ i ∉ J, site i h = 0)
    (hns : ∀ i ∈ J, ¬ Function.Surjective ((site i).domRestrict H))
    (hzero : ∀ x ∈ U, x ∉ H → (zeroSites J x).card ≤ 2) : False := by
  classical
  have hexi : ∃ i ∈ J, (site i).domRestrict H ≠ 0 := by
    by_contra! hn
    have hbot : H = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hz (i : Fin n) : site i x = 0 := by
        by_cases hi : i ∈ J
        · exact congrArg (fun f : H →ₗ[F₂] Symbol => f ⟨x, hx⟩) (hn i hi)
        · exact hsupp x hx i hi
      apply Prod.ext <;> funext i
      · exact congrArg Prod.fst (hz i)
      · exact congrArg Prod.snd (hz i)
    rw [hbot, finrank_bot] at hH
    omega
  obtain ⟨i, hi, hi'⟩ := hexi
  obtain ⟨h, hhH, hhne, hhi, hrad⟩ := radical_singleton_kernel H i hH hi' (hns i hi)
  let W := shortened {i} U
  let R := words (shortened {i} H)
  let D := words W \ R
  let K (j : Fin n) := words (shortened {j} W) \ R
  let q := 2 ^ (Module.finrank F₂ W - 2)
  have hWdim : 4 ≤ Module.finrank F₂ W := by
    have := singleton_shortened_rank U i
    change Module.finrank F₂ W + 2 ≥ Module.finrank F₂ U at this
    omega
  have hq : 4 ≤ q := by
    change 2 ^ 2 ≤ 2 ^ (Module.finrank F₂ W - 2)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hWcard : (words W).card = 4 * q := by
    rw [card_words, show Module.finrank F₂ W = 2 + (Module.finrank F₂ W - 2) by omega,
      Nat.pow_add]
  have hR : R = {0, h} := hrad
  have hA (j : Fin n) : q ≤ (words (shortened {j} W)).card := by
    rw [card_words]
    exact Nat.pow_le_pow_right (by decide) (by
      have := singleton_shortened_rank W j
      omega)
  have hKbound (j : Fin n) : q ≤ (K j).card + 1 + (if site j h = 0 then 1 else 0) := by
    have hh := hA j
    have hs := Finset.card_sdiff_add_card_inter (words (shortened {j} W)) R
    change (K j).card + _ = _ at hs
    have hinter : (words (shortened {j} W) ∩ R).card ≤ 1 + (if site j h = 0 then 1 else 0) := by
      by_cases hj : site j h = 0
      · have hc := Finset.card_le_card (Finset.inter_subset_right :
            words (shortened {j} W) ∩ R ⊆ R)
        have hRcard : R.card = 2 := by rw [hR, Finset.card_pair (Ne.symm hhne)]
        simpa [hRcard, hj] using hc
      · have hs' : words (shortened {j} W) ∩ R ⊆ {0} := by
          intro z hz
          obtain ⟨hz, hzR⟩ := Finset.mem_inter.mp hz
          rw [hR, Finset.mem_insert, Finset.mem_singleton] at hzR
          rcases hzR with rfl | rfl
          · simp
          · exact (hj ((mem_shortened.mp (mem_words.mp hz)).2 j (by simp))).elim
        simpa [hj] using Finset.card_le_card hs'
    omega
  have hDcard : D.card = 4 * q - 2 := by
    have hsub : R ⊆ words W := fun x hx =>
      mem_words.mpr ⟨hHU (mem_words.mp hx).1, (mem_words.mp hx).2⟩
    change (words W \ R).card = _
    rw [Finset.card_sdiff_of_subset hsub, hWcard, hR, Finset.card_pair (Ne.symm hhne)]
  have hdis : ((J.erase i : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint K := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr (fun x hxa hxb => ?_)
    obtain ⟨hxa, hxR⟩ := Finset.mem_sdiff.mp hxa
    have hxb := (Finset.mem_sdiff.mp hxb).1
    have hw := (mem_shortened.mp (mem_words.mp hxa)).1
    have hxU := (mem_shortened.mp hw).1
    have hxi := (mem_shortened.mp hw).2 i (by simp)
    have hna : a ≠ i := (Finset.mem_erase.mp ha).1
    have hnb : b ≠ i := (Finset.mem_erase.mp hb).1
    have hxH : x ∉ H := fun hx => hxR (mem_words.mpr ⟨hx, hw.2⟩)
    have hbnd := hzero x hxU hxH
    have hh : ({i, a, b} : Finset (Fin n)) ⊆ zeroSites J x := by
      apply Finset.insert_subset_iff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hi, hxi⟩, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp ha).2,
          (mem_shortened.mp (mem_words.mp hxa)).2 a (by simp)⟩
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr
          ⟨(Finset.mem_erase.mp hb).2, (mem_shortened.mp (mem_words.mp hxb)).2 b (by simp)⟩)
    have hc := Finset.card_le_card hh
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hna, Ne.symm hnb]),
      Finset.card_pair hab] at hc
    omega
  have hsub : (J.erase i).biUnion K ⊆ D := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hjW, hjR⟩ := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr ⟨mem_words.mpr (mem_shortened.mp (mem_words.mp hjW)).1, hjR⟩
  have hsumUpper := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis, hDcard] at hsumUpper
  have hErase : (J.erase i).card = 6 := by rw [Finset.card_erase_of_mem hi, hJ]
  have hsumLower := Finset.sum_le_sum (s := J.erase i) (fun j _ => hKbound j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    hErase, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    mul_one, mul_one] at hsumLower
  change 6 * q ≤ (∑ j ∈ J.erase i, (K j).card) + 6 +
    ((J.erase i).filter (fun j => site j h = 0)).card at hsumLower
  let P := J.filter (fun j => site j h ≠ 0)
  have hcountP : P.card ≤ 2 := by
    have hP : P = (J.erase i).filter (fun j => site j h ≠ 0) := by
      ext j
      by_cases hj : j = i
      · simp [P, hj, hhi]
      · simp [P, hj]
    rw [hP]
    have hc := (J.erase i).card_filter_add_card_filter_not (fun j => site j h = 0)
    rw [hErase] at hc
    change ((J.erase i).filter (fun j => site j h = 0)).card +
      ((J.erase i).filter (fun j => site j h ≠ 0)).card = 6 at hc
    omega
  have hnext : ∃ j ∈ P, site j h ≠ 0 := by
    by_contra! hn
    apply hhne
    have hz (j : Fin n) : site j h = 0 := by
      by_cases hj : j ∈ J
      · by_contra hne
        exact hne (hn j (Finset.mem_filter.mpr ⟨hj, hne⟩))
      · exact hsupp h hhH j hj
    apply Prod.ext <;> funext j
    · exact congrArg Prod.fst (hz j)
    · exact congrArg Prod.snd (hz j)
  obtain ⟨j, hjP, hj0⟩ := hnext
  have hPi : insert i P ⊆ J := Finset.insert_subset_iff.mpr ⟨hi, Finset.filter_subset _ _⟩
  obtain ⟨T, hPT, hTJ, hT⟩ := Finset.exists_subsuperset_card_eq hPi
    (by have := Finset.card_insert_le i P; omega : (insert i P).card ≤ 3) (by omega : 3 ≤ J.card)
  have hiT : i ∈ T := hPT (Finset.mem_insert_self _ _)
  have hjT : j ∈ T := hPT (Finset.mem_insert_of_mem hjP)
  have hHinj : Function.Injective ((restrictSites T).domRestrict H) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    change restrictSites T (y : Word n) = 0 at hy
    have hyi : site i y = 0 := congrFun hy ⟨i, hiT⟩
    have hyR : (y : Word n) ∈ R := mem_words.mpr
      (mem_shortened.mpr ⟨y.property, by simpa using hyi⟩)
    rw [hR, Finset.mem_insert, Finset.mem_singleton] at hyR
    rcases hyR with hy0 | hyh
    · exact Subtype.ext hy0
    · exact (hj0 (hyh ▸ (show site j y = 0 from congrFun hy ⟨j, hjT⟩))).elim
  apply triple_surjectivity_obstruction J H U hU horth hzero hTJ hT hHinj hhH _ hjT hj0
  intro k hk
  by_cases hkJ : k ∈ J
  · by_contra hne
    exact hk (hPT (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hkJ, hne⟩)))
  · exact hsupp h hhH k hkJ

private lemma singleton_surjective {n : ℕ} (H : Submodule F₂ (Word n)) (i : Fin n)
    (hi : Function.Surjective ((site i).domRestrict H)) :
    Function.Surjective ((restrictSites {i}).domRestrict H) := by
  intro w
  obtain ⟨x, hx⟩ := hi (w ⟨i, Finset.mem_singleton_self _⟩)
  refine ⟨x, funext (fun j => ?_)⟩
  obtain ⟨j, hj⟩ := j
  obtain rfl := Finset.mem_singleton.mp hj
  exact hx

private lemma pair_surjective_of_successive_surjective {n : ℕ}
    (H : Submodule F₂ (Word n)) {i j : Fin n}
    (hi : Function.Surjective ((site i).domRestrict H))
    (hj : Function.Surjective ((site j).domRestrict (shortened {i} H))) :
    Function.Surjective ((restrictSites {i, j}).domRestrict H) := by
  intro w
  let wi := w ⟨i, by simp⟩
  let wj := w ⟨j, by simp⟩
  obtain ⟨x, hx⟩ := hi wi
  obtain ⟨y, hy⟩ := hj (wj - site j x)
  have hyH := (mem_shortened.mp y.property).1
  have hy0 := (mem_shortened.mp y.property).2 i (by simp)
  refine ⟨⟨(x : Word n) + y, H.add_mem x.property hyH⟩, funext (fun k => ?_)⟩
  obtain ⟨k, hk⟩ := k
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  change site k ((x : Word n) + (y : Word n)) = w ⟨k, _⟩
  change site i x = wi at hx
  change site j y = wj - site j x at hy
  rw [map_add]
  rcases hk with rfl | rfl
  · rw [hx, hy0, add_zero]
  · rw [hy, add_sub_cancel]

/-- At length seven, if a radical site is surjective, shortening there leaves six
sites, dimensions six and two, and a radical projection of rank at most one at each site. -/
theorem length_seven_rank_two_shortens_to_rank_one
    (H U : Submodule F₂ (Word 7)) (hHU : H ≤ U)
    (hH : Module.finrank F₂ H = 4) (hU : Module.finrank F₂ U = 8)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm 7 h u = 0)
    (hzeros : ∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ 3)
    (i : Fin 7) (hi : Function.Surjective ((site i).domRestrict H)) :
    let I : Finset (Fin 7) := {i}
    Module.finrank F₂ (shortened I H) = 2 ∧
      Module.finrank F₂ (shortened I U) = 6 ∧
      (∀ j ∈ Iᶜ, ¬ Function.Surjective ((site j).domRestrict (shortened I H))) ∧
      (∀ u ∈ shortened I U, u ∉ shortened I H → (zeroSites Iᶜ u).card ≤ 2) := by
  dsimp only
  let I : Finset (Fin 7) := {i}
  obtain ⟨hHd, hUd, _⟩ :=
    shorten_of_radical_surjective I H U hHU horth (singleton_surjective H i hi)
  have hI : I.card = 1 := Finset.card_singleton i
  change Module.finrank F₂ (shortened I H) = 2 ∧
    Module.finrank F₂ (shortened I U) = 6 ∧
    (∀ j ∈ Iᶜ, ¬ Function.Surjective ((site j).domRestrict (shortened I H))) ∧
    (∀ u ∈ shortened I U, u ∉ shortened I H → (zeroSites Iᶜ u).card ≤ 2)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro j hj hjSurj
    have hji : j ≠ i := by simpa [I] using hj
    exact length_seven_no_surjective_radical_pair H U hHU hH hU horth hzeros
      {i, j} (Finset.card_pair (Ne.symm hji))
      (pair_surjective_of_successive_surjective H hi hjSurj)
  · intro u hu hnu
    have h := zeroSites_shortened_bound I H U hzeros hu hnu
    omega

/-- At length eight, a rank-two radical site and the joint rank bound of three for
each pair containing it are incompatible with the three-zero condition. -/
theorem length_eight_no_rank_two_site
    (H U : Submodule F₂ (Word 8)) (hHU : H ≤ U)
    (hH : Module.finrank F₂ H = 4) (hU : Module.finrank F₂ U = 8)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm 8 h u = 0)
    (hzeros : ∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ 3)
    (i : Fin 8) (hi : Function.Surjective ((site i).domRestrict H))
    (hPair : ∀ j : Fin 8, j ≠ i →
      Module.finrank F₂ ((restrictSites {i, j}).domRestrict H).range ≤ 3) : False := by
  let I : Finset (Fin 8) := {i}
  obtain ⟨hHd, hUd, _⟩ :=
    shorten_of_radical_surjective I H U hHU horth (singleton_surjective H i hi)
  have hI : I.card = 1 := Finset.card_singleton i
  have hJ : (Iᶜ : Finset (Fin 8)).card = 7 := by
    rw [Finset.card_compl, Fintype.card_fin, hI]
  have hHU' : shortened I H ≤ shortened I U := inf_le_inf_right _ hHU
  refine seven_surviving_sites_no_rank_one_radical Iᶜ (shortened I H) (shortened I U)
    hHU' hJ (by omega) (by omega) ?_ ?_ ?_ ?_
  · exact fun h hh u hu => horth h hh.1 u hu.1
  · intro h hh j hj
    exact (mem_shortened.mp hh).2 j (by simpa using hj)
  · intro j hj hjSurj
    have hji : j ≠ i := by simpa [I] using hj
    have h := hPair j hji
    have hsurj := pair_surjective_of_successive_surjective H hi hjSurj
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_symbols,
      Finset.card_pair (Ne.symm hji)] at h
    omega
  · intro u hu hnu
    have h := zeroSites_shortened_bound I H U hzeros hu hnu
    omega

private lemma site_ext {n : ℕ} {x : Word n} (hx : ∀ i, site i x = 0) : x = 0 := by
  exact Prod.ext (funext fun i => congrArg Prod.fst (hx i))
    (funext fun i => congrArg Prod.snd (hx i))

private lemma radical_support_with_site_ge_four {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hJ : 3 ≤ J.card)
    (hH : Module.finrank F₂ H = 2) (hU : Module.finrank F₂ U = 6)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (hsupp : ∀ h ∈ H, ∀ i ∉ J, site i h = 0)
    (hns : ∀ i ∈ J, ¬ Function.Surjective ((site i).domRestrict H))
    (hzero : ∀ x ∈ U, x ∉ H → (zeroSites J x).card ≤ 2)
    {h a : Word n} (hh : h ∈ H) (ha : a ∈ H) {i j : Fin n}
    (hi : i ∈ J) (hj : j ∈ J) (hj0 : site j h ≠ 0)
    (hja : site j a = 0) (ha0 : site i a ≠ 0) :
    4 ≤ (insert i (J.filter fun k => site k h ≠ 0)).card := by
  classical
  by_contra! hsmall
  let P := J.filter fun i => site i h ≠ 0
  have hjP : j ∈ P := Finset.mem_filter.mpr ⟨hj, hj0⟩
  have hs (k : Fin n) (hk : k ∉ P) : site k h = 0 := by
    by_cases hkJ : k ∈ J
    · simpa [P, hkJ] using hk
    · exact hsupp h hh k hkJ
  have hjne : (site j).domRestrict H ≠ 0 := by
    intro he
    exact hj0 (congrArg (fun f : H →ₗ[F₂] Symbol => f ⟨h, hh⟩) he)
  obtain ⟨b, _, _, _, hker⟩ := radical_singleton_kernel H j hH hjne (hns j hj)
  have haR : a ∈ words (shortened {j} H) := mem_words.mpr
    (mem_shortened.mpr ⟨ha, fun _ hk => (Finset.mem_singleton.mp hk).symm ▸ hja⟩)
  rw [hker, Finset.mem_insert, Finset.mem_singleton] at haR
  have hab : a = b := haR.resolve_left (fun he => ha0 (by simp [he]))
  subst b
  have hiP : insert i P ⊆ J :=
    Finset.insert_subset_iff.mpr ⟨hi, Finset.filter_subset _ _⟩
  change (insert i P).card < 4 at hsmall
  obtain ⟨T, hPT, hTJ, hT⟩ := Finset.exists_subsuperset_card_eq hiP (by omega) hJ
  have hjT := hPT (Finset.mem_insert_of_mem hjP)
  have hiT := hPT (Finset.mem_insert_self _ _)
  have hHinj : Function.Injective ((restrictSites T).domRestrict H) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    change restrictSites T (y : Word n) = 0 at hy
    have hyR : (y : Word n) ∈ words (shortened {j} H) :=
      mem_words.mpr (mem_shortened.mpr ⟨y.property, fun k hk => by
        rw [Finset.mem_singleton.mp hk]
        exact congrFun hy ⟨j, hjT⟩⟩)
    rw [hker, Finset.mem_insert, Finset.mem_singleton] at hyR
    rcases hyR with hy0 | hya
    · exact Subtype.ext hy0
    · exact (ha0 (hya ▸ (show site i y = 0 from congrFun hy ⟨i, hiT⟩))).elim
  exact triple_surjectivity_obstruction J H U hU horth hzero hTJ hT hHinj hh
    (fun i hi => hs i (fun hiP => hi (hPT (Finset.mem_insert_of_mem hiP)))) hjT hj0

private lemma radical_weight_ge_three {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hJ : 3 ≤ J.card)
    (hH : Module.finrank F₂ H = 2) (hU : Module.finrank F₂ U = 6)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (hsupp : ∀ h ∈ H, ∀ i ∉ J, site i h = 0)
    (hns : ∀ i ∈ J, ¬ Function.Surjective ((site i).domRestrict H))
    (hzero : ∀ x ∈ U, x ∉ H → (zeroSites J x).card ≤ 2)
    {h : Word n} (hh : h ∈ H) (hn : h ≠ 0) :
    3 ≤ (J.filter fun i => site i h ≠ 0).card := by
  classical
  by_contra! hw
  let P := J.filter fun i => site i h ≠ 0
  have hs (i : Fin n) (hi : i ∉ P) : site i h = 0 := by
    by_cases hj : i ∈ J
    · simpa [P, hj] using hi
    · exact hsupp h hh i hj
  obtain ⟨j, hjP⟩ := Finset.card_pos.mp (show 0 < P.card by
    by_contra! hP
    exact hn (site_ext (fun i => hs i (by simp [Finset.card_eq_zero.mp (by omega : P.card = 0)]))))
  have hj := (Finset.mem_filter.mp hjP).1
  have hj0 := (Finset.mem_filter.mp hjP).2
  have hjne : (site j).domRestrict H ≠ 0 := by
    intro he
    exact hj0 (congrArg (fun f : H →ₗ[F₂] Symbol => f ⟨h, hh⟩) he)
  obtain ⟨a, ha, hane, haj, _⟩ := radical_singleton_kernel H j hH hjne (hns j hj)
  obtain ⟨i, hi⟩ : ∃ i ∈ J, site i a ≠ 0 := by
    by_contra! hnz
    exact hane (site_ext fun i => if hi : i ∈ J then hnz i hi else hsupp a ha i hi)
  have hbig := radical_support_with_site_ge_four J H U hJ hH hU horth hsupp hns hzero
    hh ha hi.1 hj hj0 haj hi.2
  have := Finset.card_insert_le i P
  change P.card < 3 at hw
  change 4 ≤ (insert i P).card at hbig
  omega

private def bitPairing (a b : Symbol) : F₂ := a.1 * b.2 + a.2 * b.1

private def dotPair (a b : Symbol) : F₂ := a.1 * b.1 + a.2 * b.2

private def lineAxis (a b : Symbol) : Symbol := if a = 0 then b else a

private def lineComplement (a : Symbol) : Symbol :=
  if a.1 = 0 then (1, 0) else (0, 1)

private def lineCoordinates (a : Symbol) : Symbol →ₗ[F₂] Symbol where
  toFun b := (bitPairing b (lineComplement a), bitPairing a b)
  map_add' b c := by
    ext <;> simp only [bitPairing, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' t b := by
    apply Prod.ext
    · change (t * b.1) * _ + (t * b.2) * _ = t * (_ + _)
      ring
    · change a.1 * (t * b.2) + a.2 * (t * b.1) = t * (_ + _)
      ring

private lemma lineCoordinates_good : ∀ a b c : Symbol, a ≠ 0 →
    (lineCoordinates a b = 0 ↔ b = 0) ∧
    bitPairing (lineCoordinates a b) (lineCoordinates a c) = bitPairing b c := by decide

private lemma lineCoordinates_radical : ∀ a b p : Symbol, bitPairing a b = 0 →
    lineCoordinates (if lineAxis a b = 0 then (1, 0) else lineAxis a b)
      (p.1 • a + p.2 • b) = (dotPair (if a = 0 then 0 else 1, if b = 0 then 0 else 1) p, 0) := by decide

private lemma rank_one_pairing {n : ℕ} {H : Submodule F₂ (Word n)} {i : Fin n}
    (hr : ¬ Function.Surjective ((site i).domRestrict H)) (a b : H) :
    bitPairing (site i a) (site i b) = 0 := by
  by_contra h
  have hc : ∀ x y : Symbol, bitPairing x y ≠ 0 →
      ∀ z : Symbol, ∃ p q : F₂, p • x + q • y = z := by decide
  apply hr
  intro z
  obtain ⟨p,q,hpq⟩ := hc _ _ h z
  refine ⟨p • a + q • b, ?_⟩
  change site i (p • (a : Word n) + q • (b : Word n)) = z
  simpa only [map_add, map_smul] using hpq

private def patterns222 : Fin 6 → Symbol :=
  ![(1, 0), (1, 0), (0, 1), (0, 1), (1, 1), (1, 1)]

private def patterns33 (a b : Symbol) : Fin 6 → Symbol :=
  fun i => if i.val < 3 then a else b

private def radicalMask (t : Fin 6 → Symbol) (p : Symbol) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => dotPair (t i) p ≠ 0)

private def typeCount (t : Fin 6 → Symbol) (a : Symbol) : ℕ :=
  (Finset.univ.filter (fun i => t i = a)).card

private lemma symbol_cases : ∀ a : Symbol, a = (0,0) ∨ a = (1,0) ∨ a = (0,1) ∨ a = (1,1) := by decide

private lemma type_pairs_card (t : Fin 6 → Symbol) {a b : Symbol} (hab : a ≠ b) :
    (Finset.univ.filter (fun i => t i = a ∨ t i = b)).card =
      typeCount t a + typeCount t b := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · rfl
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hia : t i = a := (Finset.mem_filter.mp hi).2
  have hib : t i = b := (Finset.mem_filter.mp hj).2
  exact hab (hia.symm.trans hib)

private lemma radical_type_counts (t : Fin 6 → Symbol)
    (hw : ∀ p : Symbol, p ≠ 0 → 3 ≤ (radicalMask t p).card)
    (hm : ∀ p : Symbol, ∀ i j : Fin 6, i ∈ radicalMask t p → j ∈ radicalMask t p →
      t i ≠ t j → 4 ≤ (radicalMask t p).card) :
    (∃ a b : Symbol, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      ∀ c, typeCount t c = typeCount (patterns33 a b) c) ∨
    (∀ c, typeCount t c = typeCount patterns222 c) := by
  let x : Symbol := (1,0)
  let y : Symbol := (0,1)
  let z : Symbol := (1,1)
  have hsum : typeCount t 0 + typeCount t x + typeCount t y + typeCount t z = 6 := by
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
      (fun i => t i = (0,0) ∨ t i = x)
    have he : (Finset.univ.filter (fun i => ¬ (t i = (0,0) ∨ t i = x))) =
        Finset.univ.filter (fun i => t i = y ∨ t i = z) := by
      ext i
      rcases symbol_cases (t i) with h | h | h | h <;> simp [h, x, y, z]
    rw [he, type_pairs_card t (by decide), type_pairs_card t (by decide),
      Finset.card_univ, Fintype.card_fin] at hc
    change (typeCount t 0 + typeCount t x) + (typeCount t y + typeCount t z) = 6 at hc
    omega
  have test (p a b : Symbol) (hp : p ≠ 0) (hab : a ≠ b)
      (he : ∀ c : Symbol, dotPair c p ≠ 0 ↔ c = a ∨ c = b) :
      3 ≤ typeCount t a + typeCount t b ∧
      (0 < typeCount t a → 0 < typeCount t b → 4 ≤ typeCount t a + typeCount t b) := by
    have hs : (radicalMask t p).card = typeCount t a + typeCount t b := by
      simp only [radicalMask, he]
      exact type_pairs_card t hab
    refine ⟨hs ▸ hw p hp, ?_⟩
    intro ha hb
    obtain ⟨i, hi⟩ := Finset.card_pos.mp ha
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hb
    have hai := (Finset.mem_filter.mp hi).2
    have hbj := (Finset.mem_filter.mp hj).2
    exact hs ▸ hm p i j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (he _).mpr (Or.inl hai)⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (he _).mpr (Or.inr hbj)⟩)
      (by rwa [hai, hbj])
  obtain ⟨hxy,hxy'⟩ := test z x y (by decide) (by decide) (by decide)
  obtain ⟨hxz,hxz'⟩ := test x x z (by decide) (by decide) (by decide)
  obtain ⟨hyz,hyz'⟩ := test y y z (by decide) (by decide) (by decide)
  have hc0 : typeCount t 0 = 0 := by
    by_cases hx : typeCount t x = 0 <;> by_cases hy : typeCount t y = 0 <;>
      by_cases hz : typeCount t z = 0 <;> omega
  by_cases hx : typeCount t x = 0
  · have hy : typeCount t y = 3 := by omega
    have hz : typeCount t z = 3 := by omega
    left
    refine ⟨y, z, by decide, by decide, by decide, fun c => ?_⟩
    rcases symbol_cases c with h | h | h | h
    · exact h.symm ▸ hc0.trans (by decide)
    · exact h.symm ▸ hx.trans (by decide)
    · exact h.symm ▸ hy.trans (by decide)
    · exact h.symm ▸ hz.trans (by decide)
  by_cases hy : typeCount t y = 0
  · have hx3 : typeCount t x = 3 := by omega
    have hz : typeCount t z = 3 := by omega
    left
    refine ⟨x, z, by decide, by decide, by decide, fun c => ?_⟩
    rcases symbol_cases c with h | h | h | h
    · exact h.symm ▸ hc0.trans (by decide)
    · exact h.symm ▸ hx3.trans (by decide)
    · exact h.symm ▸ hy.trans (by decide)
    · exact h.symm ▸ hz.trans (by decide)
  by_cases hz : typeCount t z = 0
  · have hx3 : typeCount t x = 3 := by omega
    have hy3 : typeCount t y = 3 := by omega
    left
    refine ⟨x, y, by decide, by decide, by decide, fun c => ?_⟩
    rcases symbol_cases c with h | h | h | h
    · exact h.symm ▸ hc0.trans (by decide)
    · exact h.symm ▸ hx3.trans (by decide)
    · exact h.symm ▸ hy3.trans (by decide)
    · exact h.symm ▸ hz.trans (by decide)
  have hx2 : typeCount t x = 2 := by omega
  have hy2 : typeCount t y = 2 := by omega
  have hz2 : typeCount t z = 2 := by omega
  right
  intro c
  rcases symbol_cases c with h | h | h | h
  · exact h.symm ▸ hc0.trans (by decide)
  · exact h.symm ▸ hx2.trans (by decide)
  · exact h.symm ▸ hy2.trans (by decide)
  · exact h.symm ▸ hz2.trans (by decide)

private lemma reindex_type_count {s t : Fin 6 → Symbol}
    (h : ∀ a, typeCount s a = typeCount t a) :
    ∃ e : Equiv.Perm (Fin 6), ∀ i, t (e i) = s i := by
  classical
  have hc (a : Symbol) (r : Fin 6 → Symbol) :
      Fintype.card { i // r i = a } = typeCount r a := by
    rw [typeCount, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
  let p (a : Symbol) : {i // s i = a} ≃ {i // t i = a} :=
    Fintype.equivOfCardEq (by rw [hc, hc, h])
  exact ⟨Equiv.ofFiberEquiv p, Equiv.ofFiberEquiv_map p⟩

private lemma dot_separates : ∀ a b : Symbol, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ p : Symbol, dotPair a p = 0 ∧ dotPair b p ≠ 0 := by decide

private def radicalWord (t : Fin 6 → Symbol) : Symbol →ₗ[F₂] Word 6 where
  toFun p := (fun i => dotPair (t i) p, 0)
  map_add' a b := by
    apply Prod.ext
    · funext i
      change dotPair (t i) (a+b) = dotPair (t i) a + dotPair (t i) b
      simp only [dotPair, Prod.fst_add, Prod.snd_add]
      ring
    · simp
  map_smul' a p := by
    apply Prod.ext
    · funext i
      change (t i).1 * (a*p.1) + (t i).2 * (a*p.2) =
        a * ((t i).1*p.1 + (t i).2*p.2)
      ring
    · simp

private def sixZ : Word 6 →ₗ[F₂] (Fin 6 → F₂) :=
  LinearMap.snd F₂ _ _

private def syndrome (t : Fin 6 → Symbol) : (Fin 6 → F₂) →ₗ[F₂] Symbol where
  toFun z := ∑ i, z i • t i
  map_add' a b := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [Pi.smul_apply, mul_smul, Finset.smul_sum]

private def allowedShift (t : Fin 6 → Symbol) (x z : Fin 6 → F₂) : Prop :=
  ∀ p : Symbol,
    (Finset.univ.filter fun i => z i = 0 ∧ x i + dotPair (t i) p = 0).card ≤ 2

private instance (t : Fin 6 → Symbol) (x z : Fin 6 → F₂) :
    Decidable (allowedShift t x z) := inferInstanceAs (Decidable (∀ p : Symbol,
      (Finset.univ.filter fun i => z i = 0 ∧ x i + dotPair (t i) p = 0).card ≤ 2))

private lemma six_shift_bound (t : Fin 6 → Symbol) (S : Submodule F₂ (Word 6))
    (hR : (radicalWord t).range ≤ S)
    (hz : ∀ u ∈ S, u ∉ (radicalWord t).range → (zeroSites Finset.univ u).card ≤ 2)
    {u : Word 6} (hu : u ∈ S) (hn : u ∉ (radicalWord t).range) :
    allowedShift t u.1 u.2 := by
  intro p
  have hp : radicalWord t p ∈ (radicalWord t).range := LinearMap.mem_range_self _ _
  have hnu : u + radicalWord t p ∉ (radicalWord t).range := by
    intro h
    exact hn (by simpa using (radicalWord t).range.sub_mem h hp)
  have h := hz _ (S.add_mem hu (hR hp)) hnu
  simpa only [zeroSites, site, radicalWord, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero, Prod.mk_eq_zero, and_comm]
    using h

private lemma syndrome_of_orthogonal (t : Fin 6 → Symbol) {u : Word 6}
    (h : ∀ p : Symbol, spForm 6 (radicalWord t p) u = 0) : syndrome t u.2 = 0 := by
  apply Prod.ext
  · have h0 := h (1,0)
    change sp (radicalWord t (1,0)) u = 0 at h0
    change (∑ i, u.2 i • t i).1 = 0
    rw [show (∑ i, u.2 i • t i).1 = ∑ i, u.2 i * (t i).1 from
      by
        change (LinearMap.fst F₂ F₂ F₂) (∑ i, u.2 i • t i) = _
        rw [map_sum]
        rfl]
    simpa [sp, radicalWord, dotPair, mul_comm] using h0
  · have h1 := h (0,1)
    change sp (radicalWord t (0,1)) u = 0 at h1
    change (∑ i, u.2 i • t i).2 = 0
    rw [show (∑ i, u.2 i • t i).2 = ∑ i, u.2 i * (t i).2 from
      by
        change (LinearMap.snd F₂ F₂ F₂) (∑ i, u.2 i • t i) = _
        rw [map_sum]
        rfl]
    simpa [sp, radicalWord, dotPair, mul_comm] using h1

private lemma dot_independent : ∀ a b : Symbol, a ≠ 0 → b ≠ 0 → a ≠ b →
    (∀ p : Symbol, dotPair a p = 0 → dotPair b p = 0 → p = 0) ∧
    (∀ y : Symbol, ∃ r s : F₂, r • a + s • b = y) := by decide

private lemma six_z_projection (t : Fin 6 → Symbol) (S : Submodule F₂ (Word 6))
    (hS : Module.finrank F₂ S = 6)
    (hR : (radicalWord t).range ≤ S)
    (ho : ∀ u ∈ S, ∀ p : Symbol, spForm 6 (radicalWord t p) u = 0)
    (hb : ∀ x : Fin 6 → F₂, ¬ allowedShift t x 0)
    (hz : ∀ u ∈ S, u ∉ (radicalWord t).range → (zeroSites Finset.univ u).card ≤ 2)
    (i j : Fin 6) (hi : t i ≠ 0) (hj : t j ≠ 0) (hij : t i ≠ t j) :
    (sixZ.domRestrict S).range = (syndrome t).ker ∧
    ∀ u ∈ S, u.2 = 0 → u ∈ (radicalWord t).range := by
  classical
  have hRI : Function.Injective (radicalWord t) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    have hp' : radicalWord t p = 0 := LinearMap.mem_ker.mp hp
    exact (dot_independent _ _ hi hj hij).1 p
      (congrFun (congrArg Prod.fst hp') i) (congrFun (congrArg Prod.fst hp') j)
  have hRdim : Module.finrank F₂ (radicalWord t).range = 2 := by
    rw [LinearMap.finrank_range_of_inj hRI]
    simp [Module.finrank_prod]
  have hzero (u : Word 6) (hu : u ∈ S) (hzu : u.2 = 0) :
      u ∈ (radicalWord t).range := by
    by_contra hn
    have h := six_shift_bound t S hR hz hu hn
    rw [hzu] at h
    exact hb u.1 h
  let f := sixZ.domRestrict S
  have hker : f.ker.map S.subtype = (radicalWord t).range := by
    ext u
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hzero a a.property (LinearMap.mem_ker.mp ha)
    · rintro ⟨p, rfl⟩
      exact ⟨⟨_, hR (LinearMap.mem_range_self _ p)⟩, rfl, rfl⟩
  have hmap := Submodule.finrank_map_subtype_eq S f.ker
  rw [hker, hRdim] at hmap
  have hdim := f.finrank_range_add_finrank_ker
  have hs : Function.Surjective (syndrome t) := by
    intro y
    obtain ⟨a,b,h⟩ := (dot_independent _ _ hi hj hij).2 y
    refine ⟨Pi.single i a + Pi.single j b, ?_⟩
    have he (k : Fin 6) (v : F₂) : syndrome t (Pi.single k v) = v • t k := by
      change (∑ l, (Pi.single k v : Fin 6 → F₂) l • t l) = _
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        simp [Pi.single_eq_of_ne hl]
      · simp
    rwa [map_add, he, he]
  have hr := (syndrome t).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  have hSymbol : Module.finrank F₂ Symbol = 2 := by simp [Module.finrank_prod]
  have hbits : Module.finrank F₂ (Fin 6 → F₂) = 6 := by simp
  rw [hSymbol, hbits] at hr
  refine ⟨Submodule.eq_of_le_of_finrank_le ?_ (by change _ ≤ Module.finrank F₂ f.range; omega), hzero⟩
  rintro z ⟨u, rfl⟩
  exact syndrome_of_orthogonal t (ho u u.property)

private def zTable222 : Fin 4 → (Fin 6 → F₂) :=
  ![![1,1,0,0,0,0], ![0,0,1,1,0,0], ![0,0,0,0,1,1], ![0,1,0,1,0,1]]

private def z33 : Fin 6 → F₂ := ![1,1,0,0,0,0]

private lemma z33_syndrome (a b : Symbol) : syndrome (patterns33 a b) z33 = 0 := by
  change (∑ i, z33 i • patterns33 a b i) = 0
  have h : ∀ c : Symbol, c + c = 0 := by decide
  simp [Fin.sum_univ_succ, z33, patterns33, h]

private lemma z222_syndrome : ∀ j : Fin 4, syndrome patterns222 (zTable222 j) = 0 := by decide

set_option maxHeartbeats 4000000 in
private lemma shifts33_test : ∀ x : Fin 6 → F₂,
    ¬ allowedShift (patterns33 (1,0) (0,1)) x 0 ∧
    ¬ allowedShift (patterns33 (1,0) (0,1)) x z33 := by decide

private lemma shifts33_standard (a b : Symbol) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    {x z : Fin 6 → F₂} (h : allowedShift (patterns33 a b) x z) :
    allowedShift (patterns33 (1,0) (0,1)) x z := by
  have ht : ∀ a b : Symbol, a ≠ 0 → b ≠ 0 → a ≠ b →
      ∀ r s : F₂, ∃ p : Symbol, dotPair a p = r ∧ dotPair b p = s := by decide
  intro q
  obtain ⟨p, hp, hq⟩ := ht a b ha hb hab q.1 q.2
  have he (i : Fin 6) : dotPair (patterns33 a b i) p =
      dotPair (patterns33 (1,0) (0,1) i) q := by
    by_cases hi : i.val < 3
    · rw [patterns33, ite_eq_left hi, patterns33, ite_eq_left hi, hp]
      simp [dotPair]
    · rw [patterns33, ite_eq_right hi, patterns33, ite_eq_right hi, hq]
      simp [dotPair]
  simpa only [he] using h p

private def pairHead (j : Fin 3) : Fin 6 := ⟨2*j.val, by omega⟩
private def pairTail (j : Fin 3) : Fin 6 := ⟨2*j.val+1, by omega⟩

private def pairDifference (x : Fin 6 → F₂) (j : Fin 3) : F₂ :=
  x (pairHead j) + x (pairTail j)

private def selectedParity (x : Fin 6 → F₂) (j : Fin 4) : F₂ :=
  ∑ k : Fin 3, x (if k.val = j.val then pairTail k else pairHead k)

set_option maxHeartbeats 4000000 in
private lemma shifts222_zero : ∀ x : Fin 6 → F₂, ¬ allowedShift patterns222 x 0 := by decide

set_option maxHeartbeats 4000000 in
private lemma shifts222_mismatch : ∀ (x : Fin 6 → F₂) (j k : Fin 3), j ≠ k →
    allowedShift patterns222 x (zTable222 j.castSucc) → pairDifference x k = 1 := by decide

set_option maxHeartbeats 4000000 in
private lemma shifts222_parity : ∀ (x : Fin 6 → F₂) (j : Fin 4),
    allowedShift patterns222 x (if j = 3 then zTable222 3 else zTable222 3 + zTable222 j) →
    selectedParity x j = 1 := by decide

private lemma spForm_symm {n : ℕ} (u v : Word n) : spForm n u v = spForm n v u := by
  simpa only [CharTwo.neg_eq] using (sp_alt n).neg_eq u v

private lemma z222_decompose (z : Fin 6 → F₂) (hz : syndrome patterns222 z = 0) :
    z = ∑ j : Fin 4, (![z 0, z 2, z 4, z 4 + z 5] : Fin 4 → F₂) j • zTable222 j := by
  have hh : z 0 + z 1 + (z 4 + z 5) = 0 := by
    have h := congrArg Prod.fst hz
    simp [syndrome, patterns222, Fin.sum_univ_succ] at h
    convert h using 1
    abel
  have ht : z 2 + z 3 + (z 4 + z 5) = 0 := by
    simpa [syndrome, patterns222, Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm]
      using congrArg Prod.snd hz
  have h1 : z 0 + (z 4 + z 5) = z 1 := by
    apply CharTwo.add_eq_zero.mp
    simpa only [add_right_comm] using hh
  have h3 : z 2 + (z 4 + z 5) = z 3 := by
    apply CharTwo.add_eq_zero.mp
    simpa only [add_right_comm] using ht
  funext i
  fin_cases i <;> simp [Fin.sum_univ_succ, zTable222, h1, h3, ← add_assoc,
    CharTwo.add_self_eq_zero]

set_option maxHeartbeats 1000000 in
private lemma basis222_gram (u : Fin 4 → Word 6)
    (hz : ∀ j, (u j).2 = zTable222 j)
    (hb : ∀ j, allowedShift patterns222 (u j).1 (zTable222 j))
    (hs : ∀ j : Fin 3,
      allowedShift patterns222 (u 3 + u j.castSucc).1 (zTable222 3 + zTable222 j.castSucc)) :
    ∀ j k : Fin 4, spForm 6 (u j) (u k) = 0 := by
  have hδ (j k : Fin 3) (hjk : j ≠ k) : pairDifference (u j.castSucc).1 k = 1 :=
    shifts222_mismatch _ _ _ hjk (hb _)
  have he : selectedParity (u 3).1 3 = 1 :=
    shifts222_parity _ 3 (by simpa using hb 3)
  have hm (j : Fin 3) : selectedParity (u 3 + u j.castSucc).1 j.castSucc = 1 := by
    apply shifts222_parity
    have h : j.castSucc ≠ (3 : Fin 4) := by
      intro hh
      have := congrArg Fin.val hh
      simp at this
      omega
    simpa only [ite_eq_right h] using hs j
  have hpair (j k : Fin 3) : spForm 6 (u j.castSucc) (u k.castSucc) = 0 := by
    by_cases hjk : j = k
    · subst k
      exact sp_alt 6 _
    have h := hδ j k hjk
    have h' := hδ k j (Ne.symm hjk)
    change sp (u j.castSucc) (u k.castSucc) = 0
    rw [sp, hz, hz]
    fin_cases j <;> fin_cases k <;> first
      | contradiction
      | simp only [pairDifference, pairHead, pairTail] at h h'
        simp [Fin.sum_univ_succ, zTable222]
        linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide]; abel)) h + h'
  have hmix (j : Fin 3) : spForm 6 (u 3) (u j.castSucc) = 0 := by
    have hp := hm j
    change sp (u 3) (u j.castSucc) = 0
    rw [sp, hz, hz]
    fin_cases j
    · have hk := hδ 0 1 (by decide)
      have hl := hδ 0 2 (by decide)
      simp [selectedParity, pairDifference, pairHead, pairTail, Fin.sum_univ_succ,
        zTable222] at hp hk hl ⊢
      simp [selectedParity, pairHead, Fin.sum_univ_succ] at he
      linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide, show (4 : F₂) = 0 by decide])) hp + he + hk + hl
    · have hk := hδ 1 0 (by decide)
      have hl := hδ 1 2 (by decide)
      simp [selectedParity, pairDifference, pairHead, pairTail, Fin.sum_univ_succ,
        zTable222] at hp hk hl ⊢
      simp [selectedParity, pairHead, Fin.sum_univ_succ] at he
      linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide, show (4 : F₂) = 0 by decide])) hp + he + hk + hl
    · have hk := hδ 2 0 (by decide)
      have hl := hδ 2 1 (by decide)
      simp [selectedParity, pairDifference, pairHead, pairTail, Fin.sum_univ_succ,
        zTable222] at hp hk hl ⊢
      simp [selectedParity, pairHead, Fin.sum_univ_succ] at he
      linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide, show (4 : F₂) = 0 by decide])) hp + he + hk + hl
  intro j k
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine Fin.lastCases (sp_alt 6 _) hmix k
  · refine Fin.lastCases ?_ (hpair j) k
    rw [spForm_symm]
    exact hmix j

private lemma canonical_six_gram_zero (t : Fin 6 → Symbol) (S : Submodule F₂ (Word 6))
    (hS : Module.finrank F₂ S = 6)
    (hR : (radicalWord t).range ≤ S)
    (ho : ∀ u ∈ S, ∀ p : Symbol, spForm 6 (radicalWord t p) u = 0)
    (hz : ∀ u ∈ S, u ∉ (radicalWord t).range → (zeroSites Finset.univ u).card ≤ 2)
    (ht : (∃ a b : Symbol, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ t = patterns33 a b) ∨
      t = patterns222) :
    ∀ x ∈ S, ∀ y ∈ S, spForm 6 x y = 0 := by
  classical
  rcases ht with ⟨a,b,ha,hb,hab,rfl⟩ | rfl
  · have hb0 (x : Fin 6 → F₂) : ¬ allowedShift (patterns33 a b) x 0 :=
      fun h => (shifts33_test x).1 (shifts33_standard a b ha hb hab h)
    have hp := (six_z_projection _ S hS hR ho hb0 hz 0 3 ha hb hab).1
    have hmem : z33 ∈ (sixZ.domRestrict S).range := by
      rw [hp]
      exact LinearMap.mem_ker.mpr (z33_syndrome a b)
    obtain ⟨u, hzu⟩ := hmem
    have hnz : z33 ≠ 0 := by decide
    have hnu : (u : Word 6) ∉ (radicalWord (patterns33 a b)).range := by
      rintro ⟨p, hp⟩
      exact hnz (hzu.symm.trans (congrArg Prod.snd hp).symm)
    intro _ _ _ _
    exfalso
    exact (shifts33_test u.val.1).2
      (shifts33_standard a b ha hb hab (hzu ▸ six_shift_bound _ S hR hz u.property hnu))
  · obtain ⟨hrange, hker⟩ :=
      six_z_projection patterns222 S hS hR ho shifts222_zero hz 0 2
        (by decide) (by decide) (by decide)
    have htable (j : Fin 4) : zTable222 j ∈ (sixZ.domRestrict S).range := by
      rw [hrange]
      exact LinearMap.mem_ker.mpr (z222_syndrome j)
    choose u hu using htable
    have huZ (j : Fin 4) : (u j).val.2 = zTable222 j := hu j
    let w (j : Fin 4) : Word 6 := u j
    have hwb (v : Word 6) (hv : v ∈ S) (hvn : v.2 ≠ 0) :
        allowedShift patterns222 v.1 v.2 := by
      apply six_shift_bound _ S hR hz hv
      rintro ⟨p, rfl⟩
      exact hvn rfl
    have hwZ (j : Fin 4) : (w j).2 = zTable222 j := huZ j
    have hB (j : Fin 4) : allowedShift patterns222 (w j).1 (zTable222 j) := by
      have h : ∀ j : Fin 4, zTable222 j ≠ 0 := by decide
      exact hwZ j ▸ hwb _ (u j).property (hwZ j ▸ h j)
    have hBS (j : Fin 3) :
        allowedShift patterns222 (w 3 + w j.castSucc).1 (zTable222 3 + zTable222 j.castSucc) := by
      have h : ∀ j : Fin 3, zTable222 3 + zTable222 j.castSucc ≠ 0 := by decide
      have hh : (w 3 + w j.castSucc).2 = zTable222 3 + zTable222 j.castSucc := by
        rw [Prod.snd_add, hwZ, hwZ]
      exact hh ▸ hwb _ (S.add_mem (u 3).property (u j.castSucc).property) (hh ▸ h j)
    have hGram := basis222_gram w hwZ hB hBS
    have hrep (v : Word 6) (hv : v ∈ S) :
        ∃ (c : Fin 4 → F₂) (p : Symbol),
          v = (∑ j, c j • w j) + radicalWord patterns222 p := by
      have hsv := syndrome_of_orthogonal patterns222 (ho v hv)
      obtain ⟨c, hc⟩ : ∃ c : Fin 4 → F₂, v.2 = ∑ j, c j • zTable222 j :=
        ⟨_, z222_decompose v.2 hsv⟩
      let a : Word 6 := ∑ j, c j • w j
      have ha : a ∈ S :=
        S.sum_mem fun j _ => S.smul_mem _ (u j).property
      have haZ : a.2 = v.2 := by
        change sixZ (∑ j, c j • w j) = v.2
        rw [map_sum, hc]
        congr 1
        funext j
        rw [map_smul]
        exact congrArg (c j • ·) (hwZ j)
      have hdiff : (v - a).2 = 0 := by rw [Prod.snd_sub, haZ, sub_self]
      obtain ⟨p,hp⟩ := hker _ (S.sub_mem hv ha) hdiff
      refine ⟨c,p,?_⟩
      change v = a + radicalWord patterns222 p
      rw [hp, add_sub_cancel]
    intro x hx y hy
    obtain ⟨c,p,hx'⟩ := hrep x hx
    obtain ⟨d,q,hy'⟩ := hrep y hy
    have hxc : (∑ j, c j • w j) ∈ S :=
      S.sum_mem fun j _ => S.smul_mem _ (u j).property
    rw [hx', map_add, LinearMap.add_apply, ho y hy p, add_zero, hy', map_add,
      spForm_symm _ (radicalWord patterns222 q), ho _ hxc q, add_zero, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [spForm_symm, map_smul, LinearMap.smul_apply, map_sum]
    rw [Finset.sum_eq_zero]
    · simp
    · intro k _
      rw [map_smul, hGram, smul_zero]

private lemma support_pulled_back {n : ℕ} {J : Finset (Fin n)} (e : Fin 6 ≃ J)
    (t : Fin 6 → Symbol) (p : Symbol) (u : Word n)
    (he : ∀ i, dotPair (t i) p ≠ 0 ↔ site (e i).val u ≠ 0) :
    (radicalMask t p).map (e.toEmbedding.trans (Function.Embedding.subtype _)) =
      J.filter (fun i => site i u ≠ 0) := by
  classical
  ext i
  simp only [Finset.mem_map, radicalMask, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(e j).property, (he j).mp hj⟩
  · rintro ⟨hi, hu⟩
    have hq := e.apply_symm_apply ⟨i, hi⟩
    refine ⟨e.symm ⟨i, hi⟩, (he _).mpr ?_, congrArg Subtype.val hq⟩
    rwa [hq]

private def rebaseSix {n : ℕ} {J : Finset (Fin n)} (e : Fin 6 ≃ J)
    (axis : Fin n → Symbol) : Word n →ₗ[F₂] Word 6 :=
  (LinearMap.pi fun i => (LinearMap.fst F₂ F₂ F₂).comp
    ((lineCoordinates (axis (e i).val)).comp (site (e i).val))).prod
  (LinearMap.pi fun i => (LinearMap.snd F₂ F₂ F₂).comp
    ((lineCoordinates (axis (e i).val)).comp (site (e i).val)))

private lemma six_rebased_gram_zero {n : ℕ} (J : Finset (Fin n))
    (H U : Submodule F₂ (Word n)) (hHU : H ≤ U)
    (hJ : J.card = 6) (hH : Module.finrank F₂ H = 2) (hU : Module.finrank F₂ U = 6)
    (ho : ∀ h ∈ H, ∀ u ∈ U, spForm n h u = 0)
    (hs : ∀ u ∈ U, ∀ i ∉ J, site i u = 0)
    (hns : ∀ i ∈ J, ¬ Function.Surjective ((site i).domRestrict H))
    (hz : ∀ u ∈ U, u ∉ H → (zeroSites J u).card ≤ 2) :
    ∀ u ∈ U, ∀ v ∈ U, spForm n u v = 0 := by
  classical
  let B := Module.finBasisOfFinrankEq F₂ H hH
  let g : Symbol ≃ₗ[F₂] H := (LinearEquiv.finTwoArrow F₂ F₂).symm.trans B.equivFun.symm
  have hg (p : Symbol) : (g p : Word n) = p.1 • (B 0 : Word n) + p.2 • (B 1 : Word n) := by
    simp [g, LinearEquiv.finTwoArrow, Fin.sum_univ_two]
  let a (i : Fin n) := site i (B 0)
  let b (i : Fin n) := site i (B 1)
  let axis (i : Fin n) : Symbol :=
    if lineAxis (a i) (b i) = 0 then (1,0) else lineAxis (a i) (b i)
  let t (i : Fin n) : Symbol := (if a i = 0 then 0 else 1, if b i = 0 then 0 else 1)
  have haxis (i : Fin n) : axis i ≠ 0 := by
    dsimp only [axis]
    split <;> simp_all
  have hat (i : Fin n) (hi : i ∈ J) (p : Symbol) :
      lineCoordinates (axis i) (site i (g p)) = (dotPair (t i) p, 0) := by
    rw [hg, map_add, map_smul, map_smul]
    exact lineCoordinates_radical (a i) (b i) p (rank_one_pairing (hns i hi) (B 0) (B 1))
  have ht (i : Fin n) (hi : i ∈ J) (p : Symbol) :
      dotPair (t i) p = 0 ↔ site i (g p) = 0 := by
    have h := (lineCoordinates_good (axis i) (site i (g p)) 0 (haxis i)).1
    rw [hat i hi p] at h
    simpa using h
  let E := (J.equivFinOfCardEq hJ).symm
  let types (i : Fin 6) := t (E i).val
  have hhH (h : Word n) (hh : h ∈ H) (i : Fin n) (hi : i ∉ J) : site i h = 0 :=
    hs h (hHU hh) i hi
  have hJ3 : 3 ≤ J.card := by omega
  have hmask (p : Symbol) := support_pulled_back E types p (g p)
    (fun i => not_congr (ht (E i).val (E i).property p))
  have hcard (p : Symbol) : (radicalMask types p).card =
      (J.filter fun i => site i (g p) ≠ 0).card := by
    rw [← hmask p, Finset.card_map]
  have hweight (p : Symbol) (hp : p ≠ 0) : 3 ≤ (radicalMask types p).card := by
    rw [hcard]
    refine radical_weight_ge_three J H U hJ3 hH hU ho hhH hns hz (g p).property ?_
    intro hh
    apply hp
    apply g.injective
    exact Subtype.ext (by simpa using hh)
  have hmixed (p : Symbol) (i j : Fin 6) (hi : i ∈ radicalMask types p)
      (hj : j ∈ radicalMask types p) (hij : types i ≠ types j) :
      4 ≤ (radicalMask types p).card := by
    have hi0 : dotPair (types i) p ≠ 0 := (Finset.mem_filter.mp hi).2
    have hj0 : dotPair (types j) p ≠ 0 := (Finset.mem_filter.mp hj).2
    have hti : types i ≠ 0 := fun h => hi0 (by simp [h, dotPair])
    have htj : types j ≠ 0 := fun h => hj0 (by simp [h, dotPair])
    obtain ⟨q, hqj, hqi⟩ := dot_separates _ _ htj hti (Ne.symm hij)
    have hpj := (not_congr (ht _ (E j).property p)).mp hj0
    have hqj' := (ht _ (E j).property q).mp hqj
    have hqi' := (not_congr (ht _ (E i).property q)).mp hqi
    have hh := radical_support_with_site_ge_four J H U hJ3 hH hU ho hhH hns hz
      (g p).property (g q).property (E i).property (E j).property hpj hqj' hqi'
    have hiP : (E i).val ∈ J.filter (fun k => site k (g p) ≠ 0) := Finset.mem_filter.mpr
      ⟨(E i).property, (not_congr (ht _ (E i).property p)).mp hi0⟩
    rwa [Finset.insert_eq_of_mem hiP, ← hcard] at hh
  obtain ⟨T, e, he, hT⟩ : ∃ (T : Fin 6 → Symbol) (e : Fin 6 ≃ J),
      (∀ i, t (e i).val = T i) ∧
      ((∃ a b : Symbol, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ T = patterns33 a b) ∨ T = patterns222) := by
    rcases radical_type_counts types hweight hmixed with ⟨a,b,ha,hb,hab,hc⟩ | hc
    · obtain ⟨p,hp⟩ := reindex_type_count (fun c => (hc c).symm)
      exact ⟨_,p.trans E,hp,Or.inl ⟨a,b,ha,hb,hab,rfl⟩⟩
    · obtain ⟨p,hp⟩ := reindex_type_count (fun c => (hc c).symm)
      exact ⟨_,p.trans E,hp,Or.inr rfl⟩
  let f := rebaseSix e axis
  have hf (u : Word n) (i : Fin 6) :
      site i (f u) = lineCoordinates (axis (e i).val) (site (e i).val u) := rfl
  have hzeros (u : Word n) (i : Fin 6) : site i (f u) = 0 ↔ site (e i).val u = 0 := by
    rw [hf]
    exact (lineCoordinates_good _ _ 0 (haxis _)).1
  have hmapH (p : Symbol) : f (g p) = radicalWord T p := by
    apply sub_eq_zero.mp
    apply site_ext
    intro i
    rw [map_sub, hf, hat _ (e i).property p, he]
    exact sub_self (dotPair (T i) p, (0 : F₂))
  have hfinj : Function.Injective (f.domRestrict U) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    apply Subtype.ext
    apply site_ext
    intro i
    by_cases hi : i ∈ J
    · have hv := (hzeros u (e.symm ⟨i,hi⟩)).mp (by
        change f u = 0 at hu
        simp [hu])
      rwa [e.apply_symm_apply] at hv
    · exact hs u u.property i hi
  have hpair (u : Word n) (hu : u ∈ U) (v : Word n) :
      spForm 6 (f u) (f v) = spForm n u v := by
    change sp (f u) (f v) = sp u v
    change (∑ i : Fin 6, bitPairing (site i (f u)) (site i (f v))) =
      ∑ i : Fin n, bitPairing (site i u) (site i v)
    rw [← Finset.sum_add_sum_compl J, Finset.sum_eq_zero (s := Jᶜ) (fun i hi => ?_), add_zero]
    · rw [← Finset.sum_coe_sort J, ← e.sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      rw [hf, hf, (lineCoordinates_good _ _ _ (haxis _)).2]
    · simp [hs u hu i (Finset.mem_compl.mp hi), bitPairing]
  let S := U.map f
  have hS : Module.finrank F₂ S = 6 := by
    rw [show S = U.map f from rfl, ← LinearMap.range_domRestrict,
      LinearMap.finrank_range_of_inj hfinj, hU]
  have hR : (radicalWord T).range ≤ S := by
    rintro _ ⟨p,rfl⟩
    exact ⟨g p, hHU (g p).property, hmapH p⟩
  have hO : ∀ u ∈ S, ∀ p : Symbol, spForm 6 (radicalWord T p) u = 0 := by
    rintro _ ⟨u,hu,rfl⟩ p
    rw [← hmapH, hpair _ (hHU (g p).property)]
    exact ho _ (g p).property _ hu
  have hZ : ∀ u ∈ S, u ∉ (radicalWord T).range → (zeroSites Finset.univ u).card ≤ 2 := by
    rintro _ ⟨u,hu,rfl⟩ hn
    have hnu : u ∉ H := by
      intro h
      obtain ⟨p,hp⟩ := g.surjective ⟨u,h⟩
      have hh := congrArg (fun v : H => (v : Word n)) hp
      exact hn ⟨p, (hmapH p).symm.trans (congrArg f hh)⟩
    have hsets : (zeroSites Finset.univ (f u)).map
        (e.toEmbedding.trans (Function.Embedding.subtype _)) = zeroSites J u := by
      ext i
      simp only [zeroSites, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(e j).property, (hzeros u j).mp hj⟩
      · rintro ⟨hi, hi0⟩
        have hh := e.apply_symm_apply ⟨i, hi⟩
        refine ⟨e.symm ⟨i,hi⟩, (hzeros u _).mpr ?_, congrArg Subtype.val hh⟩
        rwa [hh]
    simpa only [← hsets, Finset.card_map] using hz u hu hnu
  intro u hu v hv
  rw [← hpair u hu v]
  exact canonical_six_gram_zero T S hS hR hO hZ hT (f u) ⟨u, hu, rfl⟩ (f v) ⟨v, hv, rfl⟩

/-- An eight-dimensional binary symplectic code with a four-dimensional orthogonal
subspace and at most three zeros outside that subspace has no surjective radical
site at length seven. -/
theorem length_seven_no_rank_two_site
    (H U : Submodule F₂ (Word 7)) (hHU : H ≤ U)
    (hH : Module.finrank F₂ H = 4) (hU : Module.finrank F₂ U = 8)
    (horth : ∀ h ∈ H, ∀ u ∈ U, spForm 7 h u = 0)
    (hzeros : ∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ 3)
    (i : Fin 7) (hi : Function.Surjective ((site i).domRestrict H)) : False := by
  let I : Finset (Fin 7) := {i}
  obtain ⟨hdH, hdU, hnS, hz⟩ :=
    length_seven_rank_two_shortens_to_rank_one H U hHU hH hU horth hzeros i hi
  have hJ : (Iᶜ : Finset (Fin 7)).card = 6 := by simp [I, Finset.card_compl]
  have hiso := six_rebased_gram_zero Iᶜ (shortened I H) (shortened I U)
    (inf_le_inf_right _ hHU) hJ hdH hdU (fun h hh u hu => horth h hh.1 u hu.1)
    (fun u hu j hj => (mem_shortened.mp hu).2 j (by simpa using hj)) hnS hz
  obtain ⟨_, _, hrep⟩ :=
    shorten_of_radical_surjective I H U hHU horth (singleton_surjective H i hi)
  have hUiso : U ≤ (spForm 7).orthogonal U := by
    intro y hy x hx
    obtain ⟨a, ha, _, hax⟩ := hrep x hx
    obtain ⟨b, hb, _, hby⟩ := hrep y hy
    change spForm 7 x y = 0
    rw [← hax y hy, spForm_symm a y, ← hby a ha.1]
    exact hiso b hb a ha
  have hmono := Submodule.finrank_mono hUiso
  have hd := (spForm 7).finrank_orthogonal (sp_nondegenerate 7) U
  have hV : Module.finrank F₂ (Word 7) = 14 := by simp [Module.finrank_prod]
  rw [hV, hU] at hd
  omega

#print axioms length_seven_no_rank_two_site

#print axioms shorten_of_radical_surjective
#print axioms five_site_gram_zero
#print axioms length_seven_no_surjective_radical_pair
#print axioms seven_surviving_sites_no_rank_one_radical
#print axioms length_seven_rank_two_shortens_to_rank_one
#print axioms length_eight_no_rank_two_site

end D5.S3.Quantum.Codes.BinaryEAShortening
