/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Every ten vertices in P(n,3), for n at least fourteen, have eight boundary vertices. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRootSupport
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover6G0
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7AG0
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7AG1
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7AG2
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7BG0
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7BG1
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7BG2
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G0
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G1
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G2
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G3
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G4
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G5
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover8G6
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
import Mathlib.Data.Fin.Rev
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapLong
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSymmetry
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
private def translateToZero (base : Fin 14) : Bool × Fin 14 ≃ Bool × Fin 14 where
  toFun v := (v.1, v.2 - base)
  invFun v := (v.1, v.2 + base)
  left_inv := by intro ⟨b, i⟩; simp
  right_inv := by intro ⟨b, i⟩; simp
/-- Reflection of the fourteen-column graph about column three. -/
private def reflect3 : Bool × Fin 14 ≃ Bool × Fin 14 where
  toFun v := (v.1, (3 : Fin 14) - v.2)
  invFun v := (v.1, (3 : Fin 14) - v.2)
  left_inv := by intro ⟨b, i⟩; simp
  right_inv := by intro ⟨b, i⟩; simp
/-- Reflection preserves spokes and reverses each of the two layer cycles. -/
private theorem reflect3_adj (v w : Bool × Fin 14) :
    (gp 14 3).Adj (reflect3 v) (reflect3 w) ↔ (gp 14 3).Adj v w := by
  have hneighbors (q : Nat) [NeZero q] (hq : 14 ≤ q) (v w : Bool × Fin q) :
      (gp q 3).Adj v w ↔
        (if v.1 then w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 3) ∨ w = (true, v.2 - Fin.ofNat q 3)
         else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨ w = (false, v.2 - Fin.ofNat q 1)) := by
    have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
        i + Fin.ofNat q k ≠ i := by
      intro h
      have hz : (Fin.ofNat q k : Fin q) = 0 := by
        apply add_left_cancel (a := i); simpa using h
      have := congrArg Fin.val hz
      simp [Nat.mod_eq_of_lt hk] at this
      omega
    have hreverse (k : Nat) (x y : Fin q) :
        x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
      constructor <;> intro h <;> rw [h] <;> simp
    have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
        (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
          y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
      rw [← hreverse k x y]
      constructor
      · exact And.right
      · intro h; refine ⟨?_, h⟩
        intro hxy; subst y
        rcases h with h | h <;> exact hstep k hk hpos x h.symm
    rcases v with ⟨vb, vi⟩; rcases w with ⟨wb, wi⟩
    cases vb <;> cases wb
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 1 (by omega) (by omega) vi wi
    · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
    · simp [gp, SimpleGraph.fromRel_adj]
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 3 (by omega) (by omega) vi wi
  have href (k i j : Fin 14) :
      (3 : Fin 14) - j = ((3 : Fin 14) - i) + k ↔ j = i - k := by
    constructor
    · intro h
      have hh := congrArg (fun x : Fin 14 => (3 : Fin 14) - x) h
      convert hh using 1 <;> abel
    · intro h
      rw [h]
      abel
  rw [hneighbors 14 (by omega), hneighbors 14 (by omega)]
  rcases v with ⟨b, i⟩
  rcases w with ⟨d, j⟩
  cases b <;> cases d <;>
    simp only [reflect3, Equiv.coe_fn_mk, Prod.fst, Prod.snd, Bool.false_eq_true,
      Bool.true_eq_false, false_or, false_and, true_or, true_and, Prod.mk.injEq] <;>
    try simp [sub_left_inj]
  · have hleft : (3 : Fin 14) - j = ((3 : Fin 14) - i) + 1 ↔ j = i - 1 :=
      href 1 i j
    have hright : (3 : Fin 14) - j = ((3 : Fin 14) - i) - 1 ↔ j = i + 1 := by
      convert href (-1) i j using 1 <;> abel
    exact (or_congr hleft hright).trans or_comm
  · have hleft : (3 : Fin 14) - j = ((3 : Fin 14) - i) + 3 ↔ j = i - 3 :=
      href 3 i j
    have hright : (3 : Fin 14) - j = -i ↔ j = i + 3 := by
      convert href (-3) i j using 1 <;> abel
    exact (or_congr hleft hright).trans or_comm
/-- A graph equivalence transports the external boundary exactly. -/
private theorem boundary_image (n : Nat) (e : Bool × Fin n ≃ Bool × Fin n)
    (hadj : ∀ v w, (gp n 3).Adj (e v) (e w) ↔ (gp n 3).Adj v w)
    (X : Finset (Bool × Fin n)) :
    externalBoundary n (X.image e) = (externalBoundary n X).image e := by
  have himage (S : Finset (Bool × Fin n)) (v : Bool × Fin n) :
      v ∈ S.image e ↔ e.symm v ∈ S := by
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      have heq : u = e.symm v := by
        apply e.injective
        simpa using huv
      exact heq ▸ hu
    · intro hv
      exact Finset.mem_image.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩
  ext v
  rw [himage]
  simp only [externalBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [himage]
  constructor
  · rintro ⟨hv, u, hu, huv⟩
    obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp hu
    refine ⟨hv, x, hx, ?_⟩
    have h' : (gp n 3).Adj (e x) (e (e.symm v)) := by
      simpa [hux] using huv
    exact (hadj x (e.symm v)).mp h'
  · rintro ⟨hv, u, hu, huv⟩
    refine ⟨hv, e u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    simpa using (hadj u (e.symm v)).mpr huv
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSymmetry
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExceptional
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExactBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapClassify
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRootSupport
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSupport
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSymmetry
open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
/-- Four exact support checks close every bounded-gap exception after graph symmetries. -/
private theorem exceptional_boundary (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (X : Finset (Bool × Fin n)) (hX : X.card = 10)
    (hc5 : 5 ≤ (columns X).card) (hc8 : (columns X).card ≤ 8)
    (hgap : ∀ i : Fin (columns X).card, gapWord (columns X) i ≤ 7)
    (hlarge : 4 * (columns X).card + 6 ≤ T (gapWord (columns X)))
    (hExact : ∀ p ∈ [positions6, positions7a, positions7b, positions8],
      ∀ code < 3 ^ p.length, exactRow p code = true) :
    8 ≤ (externalBoundary n X).card := by
  have hneighbors (q : Nat) [NeZero q] (hq : 14 ≤ q) (v w : Bool × Fin q) :
      (gp q 3).Adj v w ↔
        (if v.1 then w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 3) ∨ w = (true, v.2 - Fin.ofNat q 3)
         else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨ w = (false, v.2 - Fin.ofNat q 1)) := by
    have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
        i + Fin.ofNat q k ≠ i := by
      intro h
      have hz : (Fin.ofNat q k : Fin q) = 0 := by
        apply add_left_cancel (a := i); simpa using h
      have := congrArg Fin.val hz
      simp [Nat.mod_eq_of_lt hk] at this
      omega
    have hreverse (k : Nat) (x y : Fin q) :
        x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
      constructor <;> intro h <;> rw [h] <;> simp
    have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
        (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
          y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
      rw [← hreverse k x y]
      constructor
      · exact And.right
      · intro h; refine ⟨?_, h⟩
        intro hxy; subst y
        rcases h with h | h <;> exact hstep k hk hpos x h.symm
    rcases v with ⟨vb, vi⟩; rcases w with ⟨wb, wi⟩
    cases vb <;> cases wb
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 1 (by omega) (by omega) vi wi
    · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
    · simp [gp, SimpleGraph.fromRel_adj]
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 3 (by omega) (by omega) vi wi
  let C := columns X
  have hpositive (j : Fin C.card) : 0 < gapWord C j := by
    have hi : j.val < C.card := j.isLt
    have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
      by_cases hj : j.val + 1 < C.card
      · simp only [extendedColumn, dif_pos hi, dif_pos hj]
        exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega)))
      · have heq : j.val + 1 = C.card := by omega
        simp only [extendedColumn, dif_pos hi, dif_neg hj]
        exact (sortedColumn C ⟨j.val, hi⟩).isLt
    unfold gapWord; omega
  have hC : C.Nonempty := Finset.card_pos.mp (by dsimp [C]; omega)
  letI : NeZero C.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hC)⟩
  have hlo : ∀ i : Fin C.card, 1 ≤ gapWord C i := by
    intro i
    exact hpositive i
  have hsum : 14 ≤ ∑ i : Fin C.card, gapWord C i := by
    have hsumEq : (∑ j : Fin C.card, gapWord C j) = n := by
      let z : Fin C.card := ⟨0, Finset.card_pos.mpr hC⟩
      have h := positivePrefix_lifted C z C.card le_rfl
      simp [positivePrefix, cyclicIndex, liftedColumn, extendedColumn, z, hC] at h
      change (∑ x ∈ Finset.range C.card, gapWord C (Fin.ofNat C.card x)) = n at h
      simpa only [Fin.ofNat_val_eq_self] using
        (Fin.sum_univ_eq_sum_range
          (fun x : Nat => gapWord C (Fin.ofNat C.card x)) C.card).trans h
    rw [hsumEq]
    exact hn
  obtain ⟨r, e, he, helen, hword⟩ := bounded_gap_exception C.card
    (by simpa [C] using hc5) (by simpa [C] using hc8)
    (gapWord C) hlo (by simpa [C] using hgap) hsum
    (by simpa [C] using hlarge)
  have hn14 := exceptionalRoot_circumference C r e he helen hword
  subst n
  let base := sortedColumn C r
  have hsupport := support_from_gaps C r
  have hsupport' : C.image (fun x => x - base) =
      wordSupport (rotateWord (gapWord C) r) := by
    unfold wordSupport
    convert hsupport using 1
    congr 1
  obtain ⟨p, hp, hpSupport⟩ :=
    exceptionalRoot_support (rotateWord (gapWord C) r) e he helen hword
  rw [hpSupport] at hsupport'
  let Y := X.image (translateToZero base)
  have hYcard : Y.card = 10 := by
    simpa [Y] using (Finset.card_image_of_injective X (translateToZero base).injective).trans hX
  have hYcolumns : columns Y = supportSet p := by
    calc
      columns Y = C.image (fun i => i - base) := by
        simp only [Y, C, columns, Finset.image_image]
        rfl
      _ = supportSet p := hsupport'
  have hYboundary : (externalBoundary 14 Y).card = (externalBoundary 14 X).card := by
    have hadj (v w : Bool × Fin 14) :
        (gp 14 3).Adj (translateToZero base v) (translateToZero base w) ↔
          (gp 14 3).Adj v w := by
      have hcancel (a b k : Fin 14) :
          a + -base = b + (k + -base) ↔ a = b + k := by
        constructor
        · intro h
          have hh := congrArg (fun z : Fin 14 => z + base) h
          simpa [add_assoc, add_comm, add_left_comm] using hh
        · intro h
          rw [h]
          abel
      rw [hneighbors 14 (by omega), hneighbors 14 (by omega)]
      rcases v with ⟨b, i⟩
      rcases w with ⟨d, j⟩
      cases b <;> cases d <;>
        simp [translateToZero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      all_goals simp only [hcancel]
    rw [show Y = X.image (translateToZero base) from rfl,
      boundary_image 14 (translateToZero base) hadj X,
      Finset.card_image_of_injective _ (translateToZero base).injective]
  have finish (q : List Nat)
      (hq : q ∈ [positions6, positions7a, positions7b, positions8])
      (Z : Finset (Bool × Fin 14)) (hZcard : Z.card = 10)
      (hZcolumns : columns Z = supportSet q) :
      8 ≤ (externalBoundary 14 Z).card := by
    obtain ⟨hpos, hsupportCard⟩ := canonical_support_facts.1 q hq
    let code := layerCode q Z
    have hrepr := labelledSupport_layerCode q hpos Z hZcolumns
    have hcode : code < 3 ^ q.length := by
      have hsmall : ∀ d ∈ layerDigits q Z, d < 3 := by
        intro d hd
        simp only [layerDigits, List.mem_ofFn] at hd
        obtain ⟨i, rfl⟩ := hd
        unfold layerDigit
        split_ifs <;> omega
      simpa [code, layerCode, layerDigits] using
        Nat.ofDigits_lt_base_pow_length (by omega : 1 < 3) hsmall
    have hchecked := hExact q hq code hcode
    have hdecodedCard : (labelledSupport q code).card = 10 := by
      rw [hrepr]
      exact hZcard
    have hscore : I 14 Z + K 14 Z ≤ 2 * q.length + 2 := by
      simp only [exactRow, decide_eq_true_eq] at hchecked
      rcases hchecked with hbad | hgood
      · exact (hbad hdecodedCard).elim
      · change directScore (labelledSupport q (layerCode q Z)) ≤
          2 * q.length + 2 at hgood
        rw [hrepr] at hgood
        simpa [directScore_eq] using hgood
    have hcols : (columns Z).card = q.length := by
      rw [hZcolumns, hsupportCard]
    have hid := boundary_request_identity 14 (by omega) Z
    omega
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp
  · subst p
    exact (hYboundary ▸ finish positions6 (by decide) Y hYcard hYcolumns)
  · subst p
    let Z := Y.image reflect3
    have hZcolumns : columns Z = supportSet positions7a := by
      calc
        columns Z = (columns Y).image (fun i : Fin 14 => (3 : Fin 14) - i) := by
          simp only [Z, columns, Finset.image_image]
          rfl
        _ = supportSet positions7a := by
          rw [hYcolumns]
          exact canonical_support_facts.2.1
    have hZcard : Z.card = 10 := by
      simpa [Z] using (Finset.card_image_of_injective Y reflect3.injective).trans hYcard
    have hZboundary : (externalBoundary 14 Z).card =
        (externalBoundary 14 Y).card := by
      rw [show Z = Y.image reflect3 from rfl,
        boundary_image 14 reflect3 reflect3_adj Y,
        Finset.card_image_of_injective _ reflect3.injective]
    have hz := finish positions7a (by decide) Z hZcard hZcolumns
    omega
  · subst p
    exact (hYboundary ▸ finish positions7a (by decide) Y hYcard hYcolumns)
  · subst p
    exact (hYboundary ▸ finish positions7b (by decide) Y hYcard hYcolumns)
  · subst p
    let Z := Y.image reflect3
    have hZcolumns : columns Z = supportSet positions8 := by
      calc
        columns Z = (columns Y).image (fun i : Fin 14 => (3 : Fin 14) - i) := by
          simp only [Z, columns, Finset.image_image]
          rfl
        _ = supportSet positions8 := by
          rw [hYcolumns]
          exact canonical_support_facts.2.2
    have hZcard : Z.card = 10 := by
      simpa [Z] using (Finset.card_image_of_injective Y reflect3.injective).trans hYcard
    have hZboundary : (externalBoundary 14 Z).card =
        (externalBoundary 14 Y).card := by
      rw [show Z = Y.image reflect3 from rfl,
        boundary_image 14 reflect3 reflect3_adj Y,
        Finset.card_image_of_injective _ reflect3.injective]
    have hz := finish positions8 (by decide) Z hZcard hZcolumns
    omega
  · subst p
    exact (hYboundary ▸ finish positions8 (by decide) Y hYcard hYcolumns)
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExceptional
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapBounded
open D5.S3.Combinatorics.GeneralizedPetersen
open ZeroForcingThreeGapExact
open ZeroForcingThreeGapExceptional
open ZeroForcingThreeBoundary
open ZeroForcingThreeRequests
/-- Parity closes the relaxed words; exact checked labellings close the four remaining supports. -/
theorem bounded_gap_boundary (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (X : Finset (Bool × Fin n)) (hX : X.card = 10)
    (hc5 : 5 ≤ (columns X).card) (hc8 : (columns X).card ≤ 8)
    (hgap : ∀ i : Fin (columns X).card, gapWord (columns X) i ≤ 7) :
    8 ≤ (externalBoundary n X).card := by
  have hrows : ∀ p ∈ [positions6, positions7a, positions7b, positions8],
      ∀ code < 3 ^ p.length, exactRow p code = true := by
    intro p hp code hcode
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · have hc : code < 729 := by simpa [positions6] using hcode
      exact ZeroForcingThreeGapCover6G0.covers code (by omega) hc
    · have hc : code < 2187 := by simpa [positions7a] using hcode
      by_cases h0 : code < 1024
      · exact ZeroForcingThreeGapCover7AG0.covers code (by omega) h0
      by_cases h1 : code < 2048
      · exact ZeroForcingThreeGapCover7AG1.covers code (by omega) h1
      exact ZeroForcingThreeGapCover7AG2.covers code (by omega) hc
    · have hc : code < 2187 := by simpa [positions7b] using hcode
      by_cases h0 : code < 1024
      · exact ZeroForcingThreeGapCover7BG0.covers code (by omega) h0
      by_cases h1 : code < 2048
      · exact ZeroForcingThreeGapCover7BG1.covers code (by omega) h1
      exact ZeroForcingThreeGapCover7BG2.covers code (by omega) hc
    · have hc : code < 6561 := by simpa [positions8] using hcode
      by_cases h0 : code < 1024
      · exact ZeroForcingThreeGapCover8G0.covers code (by omega) h0
      by_cases h1 : code < 2048
      · exact ZeroForcingThreeGapCover8G1.covers code (by omega) h1
      by_cases h2 : code < 3072
      · exact ZeroForcingThreeGapCover8G2.covers code (by omega) h2
      by_cases h3 : code < 4096
      · exact ZeroForcingThreeGapCover8G3.covers code (by omega) h3
      by_cases h4 : code < 5120
      · exact ZeroForcingThreeGapCover8G4.covers code (by omega) h4
      by_cases h5 : code < 6144
      · exact ZeroForcingThreeGapCover8G5.covers code (by omega) h5
      exact ZeroForcingThreeGapCover8G6.covers code (by omega) hc
  by_cases hsafe : T (gapWord (columns X)) ≤ 4 * (columns X).card + 5
  · have hslot := slot_domination n hn X hX
    have hid := boundary_request_identity n hn X
    omega
  · have hlarge : 4 * (columns X).card + 6 ≤ T (gapWord (columns X)) := by omega
    exact exceptional_boundary n hn X hX hc5 hc8 hgap hlarge hrows
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapBounded
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeDeletion
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
/-- The relabelling that skips one column, on both layers. -/
private def insertColumn {m : Nat} (t : Fin (m + 1)) (v : Bool × Fin m) : Bool × Fin (m + 1) :=
  (v.1, t.succAbove v.2)
/-- No selected column lies within three cyclic steps of the deleted column. -/
private def EmptyBuffer {m : Nat} (t : Fin (m + 1)) (X : Finset (Bool × Fin (m + 1))) : Prop :=
  ∀ v ∈ X, ∀ k : Nat, k ≤ 3 →
    v.2 ≠ t + Fin.ofNat (m + 1) k ∧ v.2 ≠ t - Fin.ofNat (m + 1) k
/-- A gap of at least eight supplies a column with a three-column empty buffer. -/
private theorem long_gap_has_buffer {n : Nat} [NeZero n] (hn : 15 ≤ n)
    (X : Finset (Bool × Fin n))
    (i : Fin (columns X).card) (hgap : 8 ≤ gapWord (columns X) i) :
    ∃ t : Fin n, ∀ v ∈ X, ∀ k : Nat, k ≤ 3 →
      v.2 ≠ t + Fin.ofNat n k ∧ v.2 ≠ t - Fin.ofNat n k := by
  let C := columns X
  let p := sortedColumn C i
  have hnone (d : Nat) (hd0 : 1 ≤ d) (hd7 : d ≤ 7) :
      p + Fin.ofNat n d ∉ C := by
    intro hd
    obtain ⟨k, hk, heq⟩ := positive_request_prefix C i d hd0 (by omega) hd
    have hs : ({0} : Finset Nat) ⊆ Finset.range k := by
      intro x hx
      have hx0 : x = 0 := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_range.mpr (Finset.mem_Icc.mp hk).1
    have hfirst : gapWord C i ≤ positivePrefix (gapWord C) i k := by
      have hsum := Finset.sum_le_sum_of_subset
        (f := fun j => gapWord C (cyclicIndex i j)) hs
      have hz : cyclicIndex i 0 = i := by
        apply Fin.ext
        change (i.val + 0) % C.card = i.val
        exact Nat.mod_eq_of_lt i.isLt
      simpa [positivePrefix, hz] using hsum
    change 8 ≤ gapWord C i at hgap
    omega
  refine ⟨p + Fin.ofNat n 4, ?_⟩
  intro v hv k hk
  have hvC : v.2 ∈ C := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hplus : p + Fin.ofNat n 4 + Fin.ofNat n k =
      p + Fin.ofNat n (4 + k) := by
    rw [add_assoc]
    congr 1
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod]
  have hminus : p + Fin.ofNat n 4 - Fin.ofNat n k =
      p + Fin.ofNat n (4 - k) := by
    have hsum : Fin.ofNat n (4 - k) + Fin.ofNat n k = Fin.ofNat n 4 := by
      calc
        _ = Fin.ofNat n (4 - k + k) := by
          apply Fin.ext
          simp [Fin.val_add, Nat.add_mod]
        _ = Fin.ofNat n 4 := by congr 1; omega
    apply sub_eq_iff_eq_add.mpr
    rw [add_assoc, hsum]
  constructor
  · rw [hplus]
    exact fun heq => hnone (4 + k) (by omega) (by omega) (heq ▸ hvC)
  · rw [hminus]
    exact fun heq => hnone (4 - k) (by omega) (by omega) (heq ▸ hvC)
/-- A cyclic unit step commutes with insertion unless it crosses the missing column. -/
private theorem insertColumn_step {m : Nat} [NeZero m] (hm : 2 ≤ m)
    (t : Fin (m + 1)) (i : Fin m)
    (hi : t.succAbove i ≠ t - Fin.ofNat (m + 1) 1) :
    t.succAbove (i + Fin.ofNat m 1) =
      t.succAbove i + Fin.ofNat (m + 1) 1 := by
  have hins (j : Fin m) : (t.succAbove j).val =
      if j.val < t.val then j.val else j.val + 1 := by
    by_cases h : j.val < t.val
    · simp [Fin.succAbove, Fin.lt_def, h]
    · simp [Fin.succAbove, Fin.lt_def, h]
  have hstep (l : Nat) [NeZero l] (hl : 2 ≤ l) (j : Fin l) :
      (j + Fin.ofNat l 1).val = if j.val + 1 < l then j.val + 1 else 0 := by
    rw [Fin.val_add]
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < l by omega)]
    by_cases hj : j.val + 1 < l
    · simp [hj, Nat.mod_eq_of_lt hj]
    · have heq : j.val + 1 = l := by omega
      simp [heq]
  have hminus : (t - Fin.ofNat (m + 1) 1).val =
      if t.val = 0 then m else t.val - 1 := by
    have hone : (Fin.ofNat (m + 1) 1 : Fin (m + 1)) = 1 := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (show 1 < m + 1 by omega)]
    rw [hone]
    by_cases ht : t.val = 0
    · have ht0 : t = 0 := Fin.ext ht
      subst t
      simp [Fin.coe_neg_one]
    · simp [ht, Fin.val_sub_one_of_ne_zero (Fin.ne_of_val_ne ht)]
  have hne : (t.succAbove i).val ≠ (t - Fin.ofNat (m + 1) 1).val :=
    fun heq => hi (Fin.ext heq)
  apply Fin.ext
  rw [hstep (m + 1) (by omega) (t.succAbove i), hins i,
    hins (i + Fin.ofNat m 1), hstep m hm i]
  rw [hins i, hminus] at hne
  by_cases hwrap : i.val + 1 < m
  · by_cases hcross : i.val + 1 = t.val
    · simp only [if_pos hwrap] at *
      have hib : i.val < t.val := by omega
      have ht0 : t.val ≠ 0 := by omega
      have hbad : i.val = t.val - 1 := by omega
      have heq : (if i.val < t.val then i.val else i.val + 1) =
          if t.val = 0 then m else t.val - 1 := by
        rw [if_pos hib, if_neg ht0]
        exact hbad
      exact (hne heq).elim
    · simp only [if_pos hwrap] at *
      split_ifs at * <;> omega
  · have hlast : i.val + 1 = m := by omega
    simp only [if_neg hwrap] at *
    split_ifs at * <;> omega
/-- All forward displacements of at most three survive when their source has a buffer. -/
private theorem insertColumn_forward {m : Nat} [NeZero m] (hm : 14 ≤ m)
    (t : Fin (m + 1)) (i : Fin m) (k : Nat) (hk : k ≤ 3)
    (hbuffer : ∀ d : Nat, 1 ≤ d → d ≤ 3 →
      t.succAbove i ≠ t - Fin.ofNat (m + 1) d) :
    t.succAbove (i + Fin.ofNat m k) =
      t.succAbove i + Fin.ofNat (m + 1) k := by
  have hcast (l a b : Nat) [NeZero l] :
      Fin.ofNat l (a + b) = Fin.ofNat l a + Fin.ofNat l b := by
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod]
  induction k with
  | zero => simp
  | succ j ih =>
      have hj : j ≤ 3 := by omega
      have hji := ih hj
      have hsrc : t.succAbove (i + Fin.ofNat m j) ≠
          t - Fin.ofNat (m + 1) 1 := by
        intro he
        have he' : t.succAbove i + Fin.ofNat (m + 1) j =
            t - Fin.ofNat (m + 1) 1 := by rw [← hji]; exact he
        have heq : t.succAbove i + Fin.ofNat (m + 1) (j + 1) = t := by
          rw [hcast, ← add_assoc, he']
          simp
        exact hbuffer (j + 1) (by omega) (by omega)
          ((eq_sub_iff_add_eq).mpr heq)
      have hs := insertColumn_step (by omega : 2 ≤ m) t
        (i + Fin.ofNat m j) hsrc
      calc
        t.succAbove (i + Fin.ofNat m (j + 1)) =
            t.succAbove (i + Fin.ofNat m j + Fin.ofNat m 1) := by
              rw [hcast m j 1, ← add_assoc]
        _ = t.succAbove (i + Fin.ofNat m j) + Fin.ofNat (m + 1) 1 := hs
        _ = t.succAbove i + Fin.ofNat (m + 1) (j + 1) := by
          rw [hji, hcast (m + 1) j 1, ← add_assoc]
/-- Reverse displacements of at most three also survive the buffer. -/
private theorem insertColumn_backward {m : Nat} [NeZero m] (hm : 14 ≤ m)
    (t : Fin (m + 1)) (i : Fin m) (k : Nat) (hk : k ≤ 3)
    (hbuffer : ∀ d : Nat, 1 ≤ d → d ≤ 3 →
      t.succAbove i ≠ t + Fin.ofNat (m + 1) d) :
    t.succAbove (i - Fin.ofNat m k) =
      t.succAbove i - Fin.ofNat (m + 1) k := by
  have hrevsub {q : Nat} [NeZero q] (a b : Fin q) :
      (a - b).rev = a.rev + b := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    rw [← Fin.last_sub, ← Fin.last_sub]
    abel
  have hrevadd {q : Nat} [NeZero q] (a b : Fin q) :
      (a + b).rev = a.rev - b := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    rw [← Fin.last_sub, ← Fin.last_sub]
    abel
  have hreverseBuffer (d : Nat) (hd0 : 1 ≤ d) (hd3 : d ≤ 3) :
      t.rev.succAbove i.rev ≠ t.rev - Fin.ofNat (m + 1) d := by
    rw [← Fin.rev_succAbove, ← hrevadd]
    intro he
    have he' := congrArg Fin.rev he
    exact hbuffer d hd0 hd3 (by simpa only [Fin.rev_rev] using he')
  have hf := insertColumn_forward hm t.rev i.rev k hk hreverseBuffer
  apply Fin.rev_injective
  rw [Fin.rev_succAbove t (i - Fin.ofNat m k),
    hrevsub i (Fin.ofNat m k),
    hrevsub (t.succAbove i) (Fin.ofNat (m + 1) k),
    Fin.rev_succAbove t i]
  exact hf
/-- Incident graph edges are exactly preserved by buffered column insertion. -/
private theorem insertColumn_adj {m : Nat} [NeZero m] (hm : 14 ≤ m)
    (t : Fin (m + 1)) (u v : Bool × Fin m)
    (hbuffer : ∀ k : Nat, k ≤ 3 →
      (insertColumn t u).2 ≠ t + Fin.ofNat (m + 1) k ∧
      (insertColumn t u).2 ≠ t - Fin.ofNat (m + 1) k) :
    (gp m 3).Adj u v ↔
      (gp (m + 1) 3).Adj (insertColumn t u) (insertColumn t v) := by
  have hneighbors (q : Nat) [NeZero q] (hq : 14 ≤ q) (v w : Bool × Fin q) :
      (gp q 3).Adj v w ↔
        (if v.1 then w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 3) ∨ w = (true, v.2 - Fin.ofNat q 3)
         else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨ w = (false, v.2 - Fin.ofNat q 1)) := by
    have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
        i + Fin.ofNat q k ≠ i := by
      intro h
      have hz : (Fin.ofNat q k : Fin q) = 0 := by
        apply add_left_cancel (a := i); simpa using h
      have := congrArg Fin.val hz
      simp [Nat.mod_eq_of_lt hk] at this
      omega
    have hreverse (k : Nat) (x y : Fin q) :
        x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
      constructor <;> intro h <;> rw [h] <;> simp
    have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
        (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
          y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
      rw [← hreverse k x y]
      constructor
      · exact And.right
      · intro h; refine ⟨?_, h⟩
        intro hxy; subst y
        rcases h with h | h <;> exact hstep k hk hpos x h.symm
    rcases v with ⟨vb, vi⟩; rcases w with ⟨wb, wi⟩
    cases vb <;> cases wb
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 1 (by omega) (by omega) vi wi
    · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
    · simp [gp, SimpleGraph.fromRel_adj]
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 3 (by omega) (by omega) vi wi
  have hforward (d : Nat) (hd : d = 1 ∨ d = 3) :
      t.succAbove (u.2 + Fin.ofNat m d) =
        t.succAbove u.2 + Fin.ofNat (m + 1) d := by
    apply insertColumn_forward hm t u.2 d (by rcases hd with h | h <;> omega)
    intro k hk0 hk3
    exact (hbuffer k hk3).2
  have hbackward (d : Nat) (hd : d = 1 ∨ d = 3) :
      t.succAbove (u.2 - Fin.ofNat m d) =
        t.succAbove u.2 - Fin.ofNat (m + 1) d := by
    apply insertColumn_backward hm t u.2 d (by rcases hd with h | h <;> omega)
    intro k hk0 hk3
    exact (hbuffer k hk3).1
  rw [hneighbors m hm u v,
    hneighbors (m + 1) (by omega) (insertColumn t u) (insertColumn t v)]
  rcases u with ⟨b, i⟩
  rcases v with ⟨c, j⟩
  cases b <;> cases c
  all_goals simp only [insertColumn,
    Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
    Prod.mk.injEq, true_and,
    false_and, false_or]
  all_goals try simp only [← hforward 1 (Or.inl rfl),
    ← hbackward 1 (Or.inl rfl), ← hforward 3 (Or.inr rfl),
    ← hbackward 3 (Or.inr rfl)]
  all_goals simp only [Fin.succAbove_right_inj]
/-- Removing a buffered column preserves the selected set, occupied columns, and
    the entire external boundary under the order-preserving relabelling. -/
theorem buffered_deletion {m : Nat} [NeZero m] (hm : 14 ≤ m)
    (t : Fin (m + 1)) (X : Finset (Bool × Fin (m + 1)))
    (hbuffer : EmptyBuffer t X) :
    ∃ X' : Finset (Bool × Fin m),
      X'.card = X.card ∧
      (externalBoundary m X').card = (externalBoundary (m + 1) X).card ∧
      X'.image (insertColumn t) = X ∧
      (externalBoundary m X').image (insertColumn t) =
        externalBoundary (m + 1) X ∧
      (columns X').image t.succAbove = columns X := by
  have hneighbors (q : Nat) [NeZero q] (hq : 14 ≤ q) (v w : Bool × Fin q) :
      (gp q 3).Adj v w ↔
        (if v.1 then w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 3) ∨ w = (true, v.2 - Fin.ofNat q 3)
         else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨ w = (false, v.2 - Fin.ofNat q 1)) := by
    have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
        i + Fin.ofNat q k ≠ i := by
      intro h
      have hz : (Fin.ofNat q k : Fin q) = 0 := by
        apply add_left_cancel (a := i); simpa using h
      have := congrArg Fin.val hz
      simp [Nat.mod_eq_of_lt hk] at this
      omega
    have hreverse (k : Nat) (x y : Fin q) :
        x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
      constructor <;> intro h <;> rw [h] <;> simp
    have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
        (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
          y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
      rw [← hreverse k x y]
      constructor
      · exact And.right
      · intro h; refine ⟨?_, h⟩
        intro hxy; subst y
        rcases h with h | h <;> exact hstep k hk hpos x h.symm
    rcases v with ⟨vb, vi⟩; rcases w with ⟨wb, wi⟩
    cases vb <;> cases wb
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 1 (by omega) (by omega) vi wi
    · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
    · simp [gp, SimpleGraph.fromRel_adj]
    · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
        using hcycle 3 (by omega) (by omega) vi wi
  let e := insertColumn t
  let X' : Finset (Bool × Fin m) := Finset.univ.filter fun v => e v ∈ X
  have heinj : Function.Injective e := by
    intro a b hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    have h₁ : a₁ = b₁ := congrArg Prod.fst hab
    have h₂ : t.succAbove a₂ = t.succAbove b₂ := congrArg Prod.snd hab
    exact Prod.ext h₁ (Fin.succAbove_right_injective h₂)
  have hnoX (x : Bool × Fin (m + 1)) (hx : x ∈ X) : x.2 ≠ t := by
    have h := hbuffer x hx 0 (by omega)
    simpa [EmptyBuffer] using h.1
  have hXimage : X'.image e = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    · intro hx
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hnoX x hx)
      apply Finset.mem_image.mpr
      refine ⟨(x.1, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e, insertColumn, hj] using hx⟩
      · exact Prod.ext rfl hj
  have hnoBoundary (w : Bool × Fin (m + 1))
      (hw : w ∈ externalBoundary (m + 1) X) : w.2 ≠ t := by
    obtain ⟨x, hx, hadj⟩ := (Finset.mem_filter.mp hw).2.2
    have hb (d : Nat) (hd : d = 1 ∨ d = 3) :
        x.2 ≠ t + Fin.ofNat (m + 1) d ∧
        x.2 ≠ t - Fin.ofNat (m + 1) d :=
      hbuffer x hx d (by rcases hd with h | h <;> omega)
    have hzero : x.2 ≠ t := hnoX x hx
    rcases x with ⟨b, i⟩
    cases b
    · rcases (hneighbors (m + 1) (by omega)
        (false, i) w).mp hadj with hs | hp | hm'
      · rw [hs]
        exact hzero
      · rw [hp]
        intro he
        exact (hb 1 (Or.inl rfl)).2 ((eq_sub_iff_add_eq).mpr he)
      · rw [hm']
        intro he
        exact (hb 1 (Or.inl rfl)).1 ((sub_eq_iff_eq_add).mp he)
    · rcases (hneighbors (m + 1) (by omega)
        (true, i) w).mp hadj with hs | hp | hm'
      · rw [hs]
        exact hzero
      · rw [hp]
        intro he
        exact (hb 3 (Or.inr rfl)).2 ((eq_sub_iff_add_eq).mpr he)
      · rw [hm']
        intro he
        exact (hb 3 (Or.inr rfl)).1 ((sub_eq_iff_eq_add).mp he)
  have hBimage : (externalBoundary m X').image e =
      externalBoundary (m + 1) X := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨_, hvnot, u, hu, huv⟩ := Finset.mem_filter.mp hv
      have huX : e u ∈ X := (Finset.mem_filter.mp hu).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, e u, huX, ?_⟩
      · intro h
        exact hvnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact (insertColumn_adj hm t u v
          (fun k hk => hbuffer (e u) huX k hk)).mp huv
    · intro hw
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hnoBoundary w hw)
      let v : Bool × Fin m := (w.1, j)
      have hvw : e v = w := Prod.ext rfl hj
      obtain ⟨_, hnot, x, hx, hadj⟩ := Finset.mem_filter.mp hw
      have hximage : x ∈ X'.image e := hXimage.symm ▸ hx
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hximage
      apply Finset.mem_image.mpr
      refine ⟨v, ?_, hvw⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, u, hu, ?_⟩
      · intro hv
        exact hnot (hvw ▸ (Finset.mem_filter.mp hv).2)
      · apply (insertColumn_adj hm t u v
          (fun k hk => hbuffer (e u) ((Finset.mem_filter.mp hu).2) k hk)).mpr
        change (gp (m + 1) 3).Adj (e u) (e v)
        rw [hux, hvw]
        exact hadj
  have hcardX : X'.card = X.card := by
    have h : (X'.image e).card = X'.card :=
      Finset.card_image_iff.mpr heinj.injOn
    rw [hXimage] at h
    exact h.symm
  have hcardB : (externalBoundary m X').card =
      (externalBoundary (m + 1) X).card := by
    have h : ((externalBoundary m X').image e).card =
        (externalBoundary m X').card :=
      Finset.card_image_iff.mpr heinj.injOn
    rw [hBimage] at h
    exact h.symm
  have hcolumns : (columns X').image t.succAbove = columns X := by
    ext j
    simp only [columns, Finset.mem_image]
    constructor
    · rintro ⟨i, ⟨u, hu, hui⟩, rfl⟩
      exact ⟨e u, (Finset.mem_filter.mp hu).2,
        by simpa [e, insertColumn] using congrArg (t.succAbove) hui⟩
    · rintro ⟨x, hx, hxi⟩
      have hximage : x ∈ X'.image e := hXimage.symm ▸ hx
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hximage
      refine ⟨u.2, ⟨u, hu, rfl⟩, ?_⟩
      simpa [e, insertColumn] using (congrArg Prod.snd hux).trans hxi
  exact ⟨X', hcardX, hcardB, hXimage, hBimage, hcolumns⟩
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeDeletion
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeTenBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeDeletion
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapLong
/-- Strong induction on the circumference closes every ten-set boundary case. -/
theorem p3_ten_boundary (n : Nat) [NeZero n] (hn : 14 ≤ n)
    (X : Finset (Bool × Fin n)) (hX : X.card = 10) :
    8 ≤ (externalBoundary n X).card := by
  suffices h : ∀ m : Nat, 14 ≤ m →
      ∀ Y : Finset (Bool × Fin m), Y.card = 10 →
        8 ≤ (externalBoundary m Y).card from h n hn X hX
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm Y hY
    letI : NeZero m := ⟨by omega⟩
    let C := columns Y
    have hpositive (j : Fin C.card) : 0 < gapWord C j := by
      have hi : j.val < C.card := j.isLt
      have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
        by_cases hj : j.val + 1 < C.card
        · simp only [extendedColumn, dif_pos hi, dif_pos hj]
          exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega)))
        · have heq : j.val + 1 = C.card := by omega
          simp only [extendedColumn, dif_pos hi, dif_neg hj]
          exact (sortedColumn C ⟨j.val, hi⟩).isLt
      unfold gapWord; omega
    let c := C.card
    have hoccupied : (occupiedVertices Y \ Y).card + Y.card =
        2 * (columns Y).card := by
      have hsub : Y ⊆ occupiedVertices Y := by
        intro v hv
        change v ∈ Finset.univ.product (columns Y)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
      have hcard : (occupiedVertices Y).card = 2 * (columns Y).card := by
        simp [occupiedVertices, Finset.card_product]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      have hYle : Y.card ≤ (occupiedVertices Y).card := Finset.card_le_card hsub
      omega
    change (occupiedVertices Y \ Y).card + Y.card = 2 * c at hoccupied
    have hc5 : 5 ≤ c := by omega
    by_cases hc9 : 9 ≤ c
    · have hsub : occupiedVertices Y \ Y ⊆ externalBoundary m Y := by
        intro v hv
        have hvocc : v ∈ occupiedVertices Y := (Finset.mem_sdiff.mp hv).1
        have hvnot : v ∉ Y := (Finset.mem_sdiff.mp hv).2
        change v ∈ Finset.univ.product (columns Y) at hvocc
        have hcol : v.2 ∈ columns Y := (Finset.mem_product.mp hvocc).2
        obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hcol
        have husnd : u.2 = v.2 := huv
        have hfirst : u.1 ≠ v.1 := by
          intro h
          have heq : u = v := Prod.ext h husnd
          exact hvnot (heq ▸ hu)
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, hvnot, u, hu, ?_⟩
        unfold D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation.gp; rw [SimpleGraph.fromRel_adj]
        rcases u with ⟨ub, ui⟩; rcases v with ⟨vb, vi⟩
        cases ub <;> cases vb <;> simp_all
      have hcard := Finset.card_le_card hsub
      omega
    have hc8 : c ≤ 8 := by omega
    by_cases hgap : ∀ i : Fin c, gapWord C i ≤ 7
    · exact ZeroForcingThreeGapBounded.bounded_gap_boundary m hm Y hY
        hc5 hc8 hgap
    push Not at hgap
    obtain ⟨i, hi⟩ := hgap
    have hlarge : 8 ≤ gapWord C i := by omega
    by_cases hbase : m = 14
    · have hnonempty : C.Nonempty := Finset.card_pos.mp (by omega : 0 < C.card)
      have hsumEq : (∑ j : Fin C.card, gapWord C j) = m := by
        letI : NeZero C.card := ⟨by have := Finset.card_pos.mpr hnonempty; omega⟩
        let z : Fin C.card := ⟨0, Finset.card_pos.mpr hnonempty⟩
        have h := positivePrefix_lifted C z C.card le_rfl
        simp [positivePrefix, cyclicIndex, liftedColumn, extendedColumn, z, hnonempty] at h
        change (∑ x ∈ Finset.range C.card, gapWord C (Fin.ofNat C.card x)) = m at h
        simpa only [Fin.ofNat_val_eq_self] using
          (Fin.sum_univ_eq_sum_range
            (fun x : Nat => gapWord C (Fin.ofNat C.card x)) C.card).trans h
      have hsum := hsumEq
      have hsum14 : (∑ j : Fin c, gapWord C j) = 14 := by simpa [hbase] using hsum
      have hscore := long_gap_score c hc5 hc8 (gapWord C) hpositive hsum14 i hlarge
      have hslot := slot_domination m hm Y hY
      have hid := boundary_request_identity m hm Y
      dsimp [C, c] at *; omega
    have hm15 : 15 ≤ m := by omega
    cases m with
    | zero => omega
    | succ k =>
      letI : NeZero k := ⟨by omega⟩
      obtain ⟨t, ht⟩ := long_gap_has_buffer (n := k + 1) hm15 Y i hlarge
      obtain ⟨Y', hY'card, hboundary, _, _, _⟩ :=
        buffered_deletion (m := k) (by omega : 14 ≤ k) t Y ht
      have hsmall := ih k (by omega : k < k + 1) (by omega : 14 ≤ k) Y' (by omega : Y'.card = 10)
      omega
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeTenBoundary
