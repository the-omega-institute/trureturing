/- GID: D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschThreshold
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/Steiner/SteinerPaschThreshold
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A Pasch-count bound suffices for one binary labelling to maximize every pivot-pair switch count. -/

import D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschSwitchCount
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.FieldTheory.Finiteness
import Mathlib.Order.Preorder.Finite


namespace D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschThreshold

open Finset
open scoped BigOperators

private abbrev Four := Fin 4 → ZMod 2

private theorem binary (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem toggle (x : ZMod 2) : x = 0 ↔ x + 1 ≠ 0 := by
  have cancel : (1 : ZMod 2) + 1 = 0 := by decide
  rcases binary x with rfl | rfl <;> simp [cancel]

private def weight {I : Type*} [Fintype I] (word : I → ZMod 2) : ℕ :=
  (univ.filter fun i => word i ≠ 0).card

private theorem column_dvd {I : Type*} (code : Four →ₗ[ZMod 2] (I → ZMod 2)) (i : I) :
    8 ∣ (univ.filter fun x : Four => code x i ≠ 0).card := by
  classical
  by_cases all : ∀ x : Four, code x i = 0
  · simp [all]
  · push Not at all
    obtain ⟨x, nonzero⟩ := all
    have one : code x i = 1 := (binary _).resolve_left nonzero
    let p (v : Four) := code v i = 0
    let e : {v : Four // p v} ≃ {v : Four // ¬ p v} :=
      (Equiv.addRight x).subtypeEquiv fun v => by
        change code v i = 0 ↔ code (v + x) i ≠ 0
        rw [map_add, Pi.add_apply, one]
        exact toggle _
    have same := Fintype.card_congr e
    rw [Fintype.card_subtype_compl] at same
    have size : Fintype.card Four = 16 := by
      simp [Four]
    rw [size] at same
    have half : Fintype.card {v : Four // ¬ p v} = 8 := by
      rw [Fintype.card_subtype_compl, size]
      omega
    change 8 ∣ (univ.filter (fun x : Four => ¬ p x)).card
    rw [← Fintype.card_subtype, half]

private theorem noFourDimensionalWeightFourCode {I : Type*} [Fintype I]
    (code : Four →ₗ[ZMod 2] (I → ZMod 2)) :
    ¬ ∀ x : Four, x ≠ 0 → weight (code x) = 4 := by
  classical
  intro four
  have each (x : Four) : weight (code x) = if x = 0 then 0 else 4 := by
    by_cases zero : x = 0
    · subst x
      simp [weight]
    · simp [zero, four x zero]
  have total : (∑ x : Four, weight (code x)) = 60 := by
    simp only [each, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have size : Fintype.card {x : Four // x ≠ 0} = 15 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      simp [Four]
    rw [Fintype.card_subtype] at size
    rw [size]
    decide
  have counted :
      (∑ x : Four, weight (code x)) =
        ∑ i : I, (univ.filter fun x : Four => code x i ≠ 0).card := by
    calc
      _ = ∑ x : Four, ∑ i : I, (if code x i ≠ 0 then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Finset.sum_boole (R := ℕ) (fun i => code x i ≠ 0) univ).symm
      _ = ∑ i : I, ∑ x : Four, (if code x i ≠ 0 then 1 else 0 : ℕ) := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_boole (R := ℕ) (fun x : Four => code x i ≠ 0) univ
  have divisible : 8 ∣ ∑ i : I, (univ.filter fun x : Four => code x i ≠ 0).card :=
    Finset.dvd_sum fun i _ => column_dvd code i
  rw [← counted, total] at divisible
  norm_num at divisible
open Finset Submodule

private theorem span_line_binary {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (u v : V) :
    u ∈ span (ZMod 2) ({v} : Set V) ↔ u = 0 ∨ u = v := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h
    rcases binary a with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact mem_span_singleton_self _

private theorem existsAvoidingKernelFromProjectedBound {V : Type*} [Finite V] [AddCommGroup V]
    [Module (ZMod 2) V] (S : Finset V) (d : ℕ) (H : Submodule (ZMod 2) V)
    (avoid : ∀ x ∈ S, x ∉ H)
    (bound : by
      classical
      exact (S.image H.mkQ).card < 2 ^ (d + 1) - 1) :
    ∃ K : Submodule (ZMod 2) V, H ≤ K ∧
      (∀ x ∈ S, x ∉ K) ∧ Module.finrank (ZMod 2) (V ⧸ K) ≤ d := by
  classical
  let candidates : Set (Submodule (ZMod 2) V) := {K | H ≤ K ∧ ∀ x ∈ S, x ∉ K}
  let _ : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) V => (K : Set V)) SetLike.coe_injective
  obtain ⟨K, chosen⟩ := (Set.toFinite candidates).exists_maximal ⟨H, le_rfl, avoid⟩
  have hle : H ≤ K := chosen.1.1
  have avoids : ∀ x ∈ S, x ∉ K := chosen.1.2
  let _ : Finite (V ⧸ K) := Finite.of_surjective K.mkQ K.mkQ_surjective
  let _ := Fintype.ofFinite (V ⧸ K)
  have quotientZero (x : V) : K.mkQ x = 0 ↔ x ∈ K :=
    Submodule.Quotient.mk_eq_zero K
  let changeQuotient : (V ⧸ H) →ₗ[ZMod 2] (V ⧸ K) :=
    H.mapQ K LinearMap.id (by simpa using hle)
  have factor : (S.image H.mkQ).image changeQuotient = S.image K.mkQ := by
    rw [Finset.image_image]
    rfl
  have projected : (S.image K.mkQ).card ≤ (S.image H.mkQ).card := by
    rw [← factor]
    exact Finset.card_image_le
  have covers : S.image K.mkQ = univ.erase 0 := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro member
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp member
      exact fun zero => avoids x hx ((quotientZero _).mp zero)
    · intro nonzero
      by_contra missing
      let T := (span (ZMod 2) ({u} : Set (V ⧸ K))).comap K.mkQ
      have grow : K ≤ T := by
        intro x hx
        change K.mkQ x ∈ span (ZMod 2) ({u} : Set (V ⧸ K))
        rw [(quotientZero _).mpr hx]
        exact Submodule.zero_mem _
      have keeps : ∀ x ∈ S, x ∉ T := by
        intro x hx found
        have visited : K.mkQ x ∈ span (ZMod 2) ({u} : Set (V ⧸ K)) := found
        rcases (span_line_binary _ _).mp visited with zero | equal
        · exact avoids x hx ((quotientZero _).mp zero)
        · exact missing (Finset.mem_image.mpr ⟨x, hx, equal⟩)
      have back : T ≤ K := chosen.2 (show T ∈ candidates from ⟨hle.trans grow, keeps⟩) grow
      obtain ⟨v, hv⟩ := K.mkQ_surjective u
      have vIn : v ∈ T := by
        change K.mkQ v ∈ span (ZMod 2) ({u} : Set (V ⧸ K))
        rw [hv]
        exact mem_span_singleton_self _
      exact nonzero (hv ▸ (quotientZero _).mpr (back vIn))
  refine ⟨K, hle, avoids, ?_⟩
  have size : (S.image K.mkQ).card = 2 ^ Module.finrank (ZMod 2) (V ⧸ K) - 1 := by
    rw [covers, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  rw [size] at projected
  by_contra! larger
  have exponent : d + 1 ≤ Module.finrank (ZMod 2) (V ⧸ K) := by omega
  have compare := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) exponent
  omega

private theorem weightFourAvoidance {I : Type*} [Fintype I]
    (S : Finset (I → ZMod 2)) (d : ℕ) (hd : 3 ≤ d)
    (weights : ∀ x ∈ S, weight x = 4) (bound : S.card ≤ 2 ^ (d + 1) - 1) :
    ∃ K : Submodule (ZMod 2) (I → ZMod 2),
      (∀ x ∈ S, x ∉ K) ∧ Module.finrank (ZMod 2) ((I → ZMod 2) ⧸ K) ≤ d := by
  classical
  have nonzero (x) (hx : x ∈ S) : x ≠ 0 := by
    rintro rfl
    simpa [weight] using weights 0 hx
  by_cases small : S.card < 2 ^ (d + 1) - 1
  · let H : Submodule (ZMod 2) (I → ZMod 2) := ⊥
    obtain ⟨K, _, avoids, dimension⟩ :=
      existsAvoidingKernelFromProjectedBound S d H
        (fun x hx => nonzero x hx) ((Finset.card_image_le (f := H.mkQ)).trans_lt small)
    exact ⟨K, avoids, dimension⟩
  have missing : ∃ x ∈ S, ∃ y ∈ S, x + y ≠ 0 ∧ x + y ∉ S := by
    by_contra! closed
    let W : Submodule (ZMod 2) (I → ZMod 2) :=
      { carrier := {x | x = 0 ∨ x ∈ S}
        zero_mem' := Or.inl rfl
        add_mem' := by
          intro x y hx hy
          rcases hx with rfl | hx
          · simpa using hy
          rcases hy with rfl | hy
          · simpa using (Or.inr hx : x = 0 ∨ x ∈ S)
          by_cases hz : x + y = 0
          · exact Or.inl hz
          · exact Or.inr (closed x hx y hy hz)
        smul_mem' := by
          intro a x hx
          rcases binary a with rfl | rfl
          · exact Or.inl (zero_smul _ _)
          · simpa using hx }
    let _ := Fintype.ofFinite W
    have wsize : Fintype.card W = S.card + 1 := by
      have same : {x | x ∈ W} = (↑(insert 0 S) : Set (I → ZMod 2)) := by
        ext x
        exact (Finset.mem_insert).symm
      change Fintype.card {x // x ∈ W} = _
      rw [Fintype.card_of_subtype (insert 0 S) (fun x => by
        change x ∈ (↑(insert 0 S) : Set (I → ZMod 2)) ↔ x ∈ W
        rw [← same]
        rfl)]
      exact Finset.card_insert_of_notMem (fun hz => nonzero 0 hz rfl)
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at wsize
    have fourdim : 4 ≤ Module.finrank (ZMod 2) W := by
      by_contra! lt
      have power : 0 < (2 : ℕ) ^ (d + 1) := by positivity
      have large := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 4 ≤ d + 1 by omega)
      have cap := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (show Module.finrank (ZMod 2) W ≤ 3 by omega)
      omega
    have dimensions : Module.finrank (ZMod 2) Four ≤ Module.finrank (ZMod 2) W := by
      simpa [Four, Module.finrank_pi_fintype] using fourdim
    obtain ⟨embed, injective⟩ := finrank_le_iff_exists_linearMap.mp dimensions
    apply noFourDimensionalWeightFourCode (W.subtype.comp embed)
    intro x hx
    have h : (embed x : I → ZMod 2) ≠ 0 := by
      intro hz
      exact hx (injective (by simpa using Subtype.ext hz))
    rcases (embed x).property with hz | member
    · exact False.elim (h hz)
    · exact weights _ member
  obtain ⟨x, hx, y, hy, sum_ne, sum_missing⟩ := missing
  let H := Submodule.span (ZMod 2) ({x + y} : Set (I → ZMod 2))
  have avoid (v) (hv : v ∈ S) : v ∉ H := by
    intro line
    rcases (span_line_binary _ _).mp line with hz | hz
    · exact nonzero v hv hz
    · exact sum_missing (hz ▸ hv)
  have cancel (v : I → ZMod 2) : v + v = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • v) two
  have merge : H.mkQ x = H.mkQ y := by
    have diff : x - y = x + y := by
      have neg : -y = y := (neg_eq_iff_add_eq_zero).mpr (cancel y)
      rw [sub_eq_add_neg, neg]
    rw [← sub_eq_zero, ← map_sub, diff]
    exact (Submodule.Quotient.mk_eq_zero H).mpr (mem_span_singleton_self _)
  have apart : x ≠ y := fun eq => sum_ne (eq ▸ cancel x)
  have shrink : (S.image H.mkQ).card < S.card := by
    apply lt_of_le_of_ne Finset.card_image_le
    intro eq
    exact apart ((Finset.injOn_of_card_image_eq eq) hx hy merge)
  obtain ⟨K, _, avoids, dimension⟩ :=
    existsAvoidingKernelFromProjectedBound S d H avoid (shrink.trans_le bound)
  exact ⟨K, avoids, dimension⟩

open Function
open scoped BigOperators
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
open D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
open D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
open D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschSwitchCount
open D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
open D5.S3.Combinatorics.Matroids.SteinerSwitchSupport

private noncomputable def fourBlocks {L : Type*} (p q a b c d : L) : Finset (Set L) := by
  classical
  exact {{q, a, b}, {p, b, c}, {q, c, d}, {p, d, a}}

/-- The Pasches are counted as unordered sets of four original blocks. -/
noncomputable def paschBlockSets {L : Type*} [Mul L] [Finite L] (e : L) :
    Finset (Finset (Set L)) := by
  classical
  exact Set.Finite.toFinset (s := {T | ∃ p q a b c d : L,
    [e, p, q, a, b, c, d].Nodup ∧
    q * a = b ∧ p * b = c ∧ q * c = d ∧ p * d = a ∧ T = fourBlocks p q a b c d})
    (Set.toFinite _)

private theorem fourBlocks_nodup {L : Type*} {e p q a b c d : L}
    (distinct : [e, p, q, a, b, c, d].Nodup) :
    [({q, a, b} : Set L), {p, b, c}, {q, c, d}, {p, d, a}].Nodup := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have separated {U V : Set L} (x : L) (hU : x ∈ U) (hV : x ∉ V) : U ≠ V := by
    rintro rfl
    exact hV hU
  have first_second : ({q, a, b} : Set L) ≠ {p, b, c} :=
    separated q (by simp) (by simp [show q ≠ p by tauto, show q ≠ b by tauto, show q ≠ c by tauto])
  have first_third : ({q, a, b} : Set L) ≠ {q, c, d} :=
    separated a (by simp) (by simp [show a ≠ q by tauto, show a ≠ c by tauto, show a ≠ d by tauto])
  have first_fourth : ({q, a, b} : Set L) ≠ {p, d, a} :=
    separated q (by simp) (by simp [show q ≠ p by tauto, show q ≠ d by tauto, show q ≠ a by tauto])
  have second_third : ({p, b, c} : Set L) ≠ {q, c, d} :=
    separated p (by simp) (by simp [show p ≠ q by tauto, show p ≠ c by tauto, show p ≠ d by tauto])
  have second_fourth : ({p, b, c} : Set L) ≠ {p, d, a} :=
    separated b (by simp) (by simp [show b ≠ p by tauto, show b ≠ d by tauto, show b ≠ a by tauto])
  have third_fourth : ({q, c, d} : Set L) ≠ {p, d, a} :=
    separated q (by simp) (by simp [show q ≠ p by tauto, show q ≠ d by tauto, show q ≠ a by tauto])
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨first_second, first_third, first_fourth⟩, ⟨second_third, second_fourth⟩, third_fourth⟩

private theorem fourBlocks_card {L : Type*} {e p q a b c d : L}
    (distinct : [e, p, q, a, b, c, d].Nodup) : (fourBlocks p q a b c d).card = 4 := by
  classical
  have blocks := fourBlocks_nodup distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at blocks
  rcases blocks with ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
  change Finset.card (insert ({q, a, b} : Set L)
    (insert {p, b, c} (insert {q, c, d} ({({p, d, a} : Set L)} : Finset (Set L))))) = _
  rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
    Finset.card_insert_of_notMem (by simp [h23, h24]),
    Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]

private noncomputable def blockWord {L : Type*} (T : Finset (Set L)) : Set L → ZMod 2 := by
  classical
  exact fun B => if B ∈ T then 1 else 0

private theorem weight_blockWord {L : Type*} [Fintype (Set L)] (T : Finset (Set L)) :
    weight (blockWord T) = T.card := by
  classical
  unfold weight
  congr 1
  ext B
  by_cases h : B ∈ T <;> simp [blockWord, h]

private theorem square_distinct {L : Type*} [Mul L] {e p q x : L}
    (unit : ∀ z, e * z = z) (comm : ∀ u v : L, u * v = v * u)
    (invol : ∀ u v : L, u * (u * v) = v)
    (hp : p ≠ e) (hq : q ≠ e) (hpq : p ≠ q)
    (outside : x ∉ ({e, p, q, p * q} : Set L))
    (closes : p * (q * (p * (q * x))) = x) :
    [e, p, q, x, q * x, p * (q * x), q * (p * (q * x))].Nodup := by
  let M := loopPivotMatchings e p q unit comm invol hp hq hpq
  have rightUnit (z : L) : z * e = z := (comm z e).trans (unit z)
  have qpr : q * (p * q) = p := by rw [comm p q, invol]
  have ppr : p * (p * q) = q := invol _ _
  have specialP {z : L} (hz : z ∈ ({e, p, q, p * q} : Set L)) :
      p * z ∈ ({e, p, q, p * q} : Set L) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    have self : p * p = e := by simpa only [rightUnit] using invol p e
    rcases hz with hz | hz | hz | hz <;> rw [hz] <;> simp [rightUnit, self, ppr]
  have specialQ {z : L} (hz : z ∈ ({e, p, q, p * q} : Set L)) :
      q * z ∈ ({e, p, q, p * q} : Set L) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    have self : q * q = e := by simpa only [rightUnit] using invol q e
    rcases hz with hz | hz | hz | hz <;> rw [hz] <;> simp [rightUnit, self, qpr, comm q p]
  have away1 : q * x ∉ ({e, p, q, p * q} : Set L) := by
    intro h
    exact outside (by simpa only [invol] using specialQ h)
  have away2 : p * (q * x) ∉ ({e, p, q, p * q} : Set L) := by
    intro h
    exact away1 (by simpa only [invol] using specialP h)
  have away3 : q * (p * (q * x)) ∉ ({e, p, q, p * q} : Set L) := by
    intro h
    exact away2 (by simpa only [invol] using specialQ h)
  have closeEdge : q * (p * (q * x)) = p * x := by
    simpa only [invol] using congrArg (p * ·) closes
  have ab : x ≠ q * x := (M.second_ne_self x).symm
  have bc : q * x ≠ p * (q * x) := (M.first_ne_self (q * x)).symm
  have cd : p * (q * x) ≠ q * (p * (q * x)) := (M.second_ne_self (p * (q * x))).symm
  have ad : x ≠ q * (p * (q * x)) := by
    rw [closeEdge]
    exact (M.first_ne_self x).symm
  have ac : x ≠ p * (q * x) :=
    fun eq => M.partners_ne (q * x) (eq.symm.trans (invol q x).symm)
  have bd : q * x ≠ q * (p * (q * x)) :=
    (show Involutive (q * ·) from invol q).injective.ne ac
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at outside away1 away2 away3
  tauto


private theorem square_row {L : Type*} [Mul L] {e p q a b c d : L}
    (comm : ∀ x y : L, x * y = y * x) (invol : ∀ x y : L, x * (x * y) = y)
    (distinct : [e, p, q, a, b, c, d].Nodup)
    (hab : q * a = b) (hbc : p * b = c) (hcd : q * c = d) (hda : p * d = a) :
    (returnRow e p q a : Set L → ZMod 2) = blockWord (fourBlocks p q a b c d) := by
  classical
  have closes : (fun z => p * (q * z))^[2] a = a := by
    rw [iterate_succ_apply', iterate_one, hab, hbc, hcd, hda]
  have blocks := fourBlocks_nodup distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct blocks
  have period := steinerSquarePeriod comm invol (show p ≠ q by tauto) closes
  have nondegenerate (u v : L) (hu : u ≠ e) (hv : v ≠ e) (different : u ≠ v) :
      D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.factor e (fun t => Finsupp.single t (1 : ZMod 2)) u v =
        Finsupp.single ({u, v, u * v} : Set L) (1 : ZMod 2) := by
    rw [D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.factor, ite_eq_right (by tauto)]
    rfl
  have f1 := nondegenerate q a (by tauto) (by tauto) (by tauto)
  have f2 := nondegenerate p b (by tauto) (by tauto) (by tauto)
  have f3 := nondegenerate q c (by tauto) (by tauto) (by tauto)
  have f4 := nondegenerate p d (by tauto) (by tauto) (by tauto)
  funext B
  simp only [returnRow, period, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iterate_zero, id_eq, iterate_one, hab, hbc, hcd, f1, f2, f3, f4, hda,
    Finsupp.add_apply, Finsupp.single_apply]
  rcases blocks with ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
  have sum : (∑ T ∈ fourBlocks p q a b c d, (if T = B then 1 else 0 : ZMod 2)) =
      ((if ({q,a,b} : Set L) = B then 1 else 0) +
       (if ({p,b,c} : Set L) = B then 1 else 0)) +
      ((if ({q,c,d} : Set L) = B then 1 else 0) +
       (if ({p,d,a} : Set L) = B then 1 else 0)) := by
    unfold fourBlocks
    rw [Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
    simp only [add_assoc]
  rw [← sum]
  simp [blockWord]

private theorem square_row_in_family {L : Type*} [Finite L] [Mul L] {e p q x : L}
    (unit : ∀ z, e * z = z) (comm : ∀ u v : L, u * v = v * u)
    (invol : ∀ u v : L, u * (u * v) = v)
    (hp : p ≠ e) (hq : q ≠ e) (hpq : p ≠ q)
    (outside : x ∉ ({e, p, q, p * q} : Set L))
    (closes : p * (q * (p * (q * x))) = x) :
    ∃ B ∈ paschBlockSets e, (returnRow e p q x : Set L → ZMod 2) = blockWord B := by
  classical
  have distinct := square_distinct unit comm invol hp hq hpq outside closes
  refine ⟨fourBlocks p q x (q * x) (p * (q * x)) (q * (p * (q * x))), ?_, ?_⟩
  · unfold paschBlockSets
    rw [Set.Finite.mem_toFinset]
    exact ⟨p, q, x, q * x, p * (q * x), q * (p * (q * x)), distinct, rfl, rfl, rfl, closes, rfl⟩
  · exact square_row comm invol distinct rfl rfl rfl closes

open SimpleGraph

/-- A single normalized binary table attains every pivot pair's individual maximum
whenever the number of Pasches is at most the stated bound. -/
theorem commonMaximum_of_paschCount {L A : Type*} [Finite L] [Finite A]
    [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (unit : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centre : Set.center L = {e})
    (hd : 3 ≤ Module.finrank (ZMod 2) A)
    (bound : (paschBlockSets e).card ≤ 2 ^ (Module.finrank (ZMod 2) A + 1) - 1) :
    let count (p q : L) (labels : Set L → A) : ℕ :=
      letI := extensionMul e labels
      ({x : L × A | (q, 0) * ((p, 0) * x) ≠ (p, 0) * ((q, 0) * x)} : Set (L × A)).ncard
    ∃ labels : Set L → A, ∀ p q : L, p ≠ e → q ≠ e → p ≠ q →
      ∀ other : Set L → A, count p q other ≤ count p q labels := by
  classical
  dsimp only
  let _ := Fintype.ofFinite (Set L)
  let S := (paschBlockSets e).image blockWord
  have weights (x) (hx : x ∈ S) : weight x = 4 := by
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
    rw [weight_blockWord]
    unfold paschBlockSets at hT
    rw [Set.Finite.mem_toFinset] at hT
    obtain ⟨p, q, a, b, c, d, distinct, _, _, _, _, rfl⟩ := hT
    exact fourBlocks_card distinct
  obtain ⟨K, avoids, dimension⟩ := weightFourAvoidance S _ hd weights
    (Finset.card_image_le.trans bound)
  obtain ⟨evaluate, injective⟩ := finrank_le_iff_exists_linearMap.mp dimension
  let readWord := Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Set L)
  let f := evaluate.comp (K.mkQ.comp readWord.toLinearMap)
  let coefficients := Finsupp.lift A (ZMod 2) (Set L)
  let labels := coefficients.symm f
  have table : Finsupp.linearCombination (ZMod 2) labels = f := by
    apply LinearMap.ext
    intro row
    rw [Finsupp.linearCombination_apply, ← Finsupp.lift_apply]
    exact LinearMap.congr_fun (coefficients.apply_symm_apply f) row
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  have law (table : Set L → A) := (extensionSteinerAndCentre e table unit comm invol twice centre).2.2.1
  refine ⟨labels, fun p q hp hq hpq other => ?_⟩
  let g : L → L := fun z => p * (q * z)
  let M := loopPivotMatchings e p q unit comm invol hp hq hpq
  have rightUnit (x : L) : x * e = x := (comm x e).trans (unit x)
  have identitySquare : (M.graph.connectedComponentMk e).supp = {e, p, q, p * q} := by
    have here : M.first (M.second e) = M.second (M.first e) := by
      change p * (q * e) = q * (p * e)
      rw [rightUnit, rightUnit, comm p q]
    have support := M.component_eq_square here
    change (M.graph.connectedComponentMk e).supp = {e, p * e, q * e, p * (q * e)} at support
    simpa only [rightUnit] using support
  have edges (u v : L) : M.graph.Adj u v ↔ p * u = v ∨ q * u = v := Iff.rfl
  have special {x : L} (hx : x ∈ ({e, p, q, p * q} : Set L)) :
      Finsupp.linearCombination (ZMod 2) other (returnRow e p q x) = 0 := by
    let _ := extensionMul e other
    have path : M.graph.Reachable e x := by
      rw [← identitySquare, ConnectedComponent.mem_supp_iff] at hx
      exact ConnectedComponent.exact hx.symm
    have atE (a : A) :
        (fun z : L × A => (p, 0) * ((q, 0) * z))^[minimalPeriod g e] (e, a) = (e, a + 0) := by
      obtain ⟨period, stable⟩ := identityReturn e p q other a unit comm invol twice hpq
      rw [pairedLift_eq_mul e other p q] at stable
      have pe : minimalPeriod g e = 2 := period
      rw [pe, add_zero]
      exact stable
    have moved := returnAlongComponent M.graph e p q other invol twice edges (law other)
      path 0 atE 0
    have target := firstReturn e other p q x (0 : A)
    have same := congrArg Prod.snd (target.symm.trans moved)
    simpa using same
  have outsideRet {x : L} (hx : x ∉ ({e, p, q, p * q} : Set L))
      (closes : g (g x) = x) :
      Finsupp.linearCombination (ZMod 2) labels (returnRow e p q x) ≠ 0 := by
    obtain ⟨B, hB, row⟩ := square_row_in_family unit comm invol hp hq hpq hx closes
    rw [table]
    change evaluate (K.mkQ (returnRow e p q x : Set L → ZMod 2)) ≠ 0
    rw [row, ← evaluate.map_zero, injective.ne_iff]
    exact fun h => avoids _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
      ((Submodule.Quotient.mk_eq_zero K).mp h)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro ⟨x, a⟩ chosen
  have old := (selectedByRow e p q x other a comm invol hpq (law other)).mp chosen
  apply (selectedByRow e p q x labels a comm invol hpq (law labels)).mpr
  rcases old with long | ret
  · exact Or.inl long
  · by_cases closes : g (g x) = x
    · exact Or.inr (outsideRet (fun hx => ret (special hx)) closes)
    · exact Or.inl closes

end D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschThreshold
