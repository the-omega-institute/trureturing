/- GID: D5/S3/Quantum/Codes/BinaryEAShortening
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAShortening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shortening on surjective radical coordinates and the five-site spread obstruction. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.Pi
import OmegaBuild.Commands

/-! Binary symplectic shortening and the five-site spread argument. [Helper escape audits](https://github.com/the-omega-institute/trureturing/issues/34915). -/

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

lemma mem_shortened {n : ℕ} {I : Finset (Fin n)} {S : Submodule F₂ (Word n)}
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

def words {n : ℕ} (S : Submodule F₂ (Word n)) : Finset (Word n) :=
  let _ : Fintype (S : Set (Word n)) := Fintype.ofFinite _
  (S : Set (Word n)).toFinset

lemma mem_words {n : ℕ} {S : Submodule F₂ (Word n)} {x : Word n} :
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

lemma radical_singleton_kernel {n : ℕ} (H : Submodule F₂ (Word n)) (i : Fin n)
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

lemma triple_surjectivity_obstruction {n : ℕ} (J : Finset (Fin n))
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

lemma singleton_surjective {n : ℕ} (H : Submodule F₂ (Word n)) (i : Fin n)
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


#print axioms shorten_of_radical_surjective
#print axioms five_site_gram_zero
#print axioms length_seven_no_surjective_radical_pair
#print axioms seven_surviving_sites_no_rank_one_radical
#print axioms length_seven_rank_two_shortens_to_rank_one
#print axioms length_eight_no_rank_two_site

end D5.S3.Quantum.Codes.BinaryEAShortening
