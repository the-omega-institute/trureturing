/- GID: D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAShorteningLengthSeven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The six-site residual Gram obstruction for the length-seven rank-two case. -/

import D5.S3.Quantum.Codes.BinaryEAShortening
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.Pi
import OmegaBuild.Commands

/-! The six-site residual obstruction for the length-seven rank-two case. [Helper escape audits](https://github.com/the-omega-institute/trureturing/issues/34915). -/

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

end D5.S3.Quantum.Codes.BinaryEAShortening
