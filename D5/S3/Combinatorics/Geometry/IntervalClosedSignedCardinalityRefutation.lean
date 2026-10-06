/- GID: D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.claim; result=D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.result; claim=D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.claim
   digest: A literal 73-state orbit on a 3 by 12 rectangle has signed-cardinality sum minus one. -/
/-
result:
  proof_shape: content
  escape_witness: result (the certified nonzero literal orbit and its encoding bridge)
  admission_basis: open-problem-resolution (#13084; Refuted)
Direct frozen dependencies:
  D5/S3/Combinatorics/Geometry/RectangularCorner.Point
    statement_id: sha256:3d12046760a812babaf3c530e33438dc9b23acb0d0bbd6782232b3625ae2da47
  D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.ReverseExtension
    statement_id: sha256:70982fe9aed927d9b926973c7cc2bf243c8595ea20bc8c5e8221e5a74ccd6d96
  D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.toggle
    statement_id: sha256:cdc8b92c12e8081e62cef5a7a142fc1366bbe32b48ef55cd84c22a24efee16b5
  D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.trace
    statement_id: sha256:142ffbc0996d07836be3808f9b8ed0bd049c572dce8b782a81ebd854a3c95d06
  D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.literalOrbit
    statement_id: sha256:7b9af9c4f7a830722a819336be5bb6281f67f3873550b8c873edaaea9a12d34c
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Combinatorics.Geometry.RectangleRowmotionHomomesy
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.IntervalClosedSignedCardinalityRefutation
open D5.S3.Combinatorics.Geometry.RectangularCorner
open D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open D5.S3.Combinatorics.Geometry.RectangleRowmotionHomomesy (literalOrbit)
open scoped BigOperators symmDiff

/-- Definition 3.17: zero-based coordinates have rank equal to their sum. -/
def signedWeight {m n : ℕ} (x : Point m n) : ℤ :=
  if Even (x.1.val + x.2.val) then 1 else -1

/-- The sum of the point statistic over the members of the set. -/
noncomputable def signedCardinality {m n : ℕ} (I : Set (Point m n)) : ℤ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x => x ∈ I), signedWeight x

/-- Conjecture 4.12, with every linear extension and every interval-closed set. -/
def claim : Prop :=
  ∀ (m n N : ℕ), (m = 2 ∨ m = 3) → 1 ≤ n → Even (m + n - 1) →
    ∀ (e : Fin N ≃ Point m n), ReverseExtension e →
      ∀ (I : Set (Point m n)), I.OrdConnected →
        ∑ S ∈ literalOrbit e I, signedCardinality S = 0

private def decode (s : ℕ) : Set (Point 3 12) :=
  {x | s.testBit (finProdFinEquiv x).val = true}

private def lowerMasks : Array ℕ := #[
  1, 3, 7, 15, 31, 63,
  127, 255, 511, 1023, 2047, 4095,
  4097, 12291, 28679, 61455, 127007, 258111,
  520319, 1044735, 2093567, 4191231, 8386559, 16777215,
  16781313, 50343939, 117469191, 251719695, 520220703, 1057222719,
  2131226751, 4279234815, 8575250943, 17167283199, 34351347711, 68719476735]

private def upperMasks : Array ℕ := #[
  68719476735, 68702695422, 68669132796, 68602007544, 68467757040, 68199256032,
  67662254016, 66588249984, 64440241920, 60144225792, 51552193536, 34368129024,
  68719472640, 68702691328, 68669128704, 68602003456, 68467752960, 68199251968,
  67662249984, 66588246016, 64440238080, 60144222208, 51552190464, 34368126976,
  68702699520, 68685922304, 68652367872, 68585259008, 68451041280, 68182605824,
  67645734912, 66571993088, 64424509440, 60129542144, 51539607552, 34359738368]

private def convexMask (s : ℕ) : Bool :=
  (List.finRange 36).all fun y => s.testBit y.val ||
    decide (s &&& lowerMasks[y.val]! = 0) || decide (s &&& upperMasks[y.val]! = 0)

private def toggleMask (s k : ℕ) : ℕ :=
  let t := s ^^^ (2 ^ k)
  if convexMask t then t else s

private def extension : Fin 36 ≃ Point 3 12 :=
  Fin.revPerm.trans (finProdFinEquiv : Point 3 12 ≃ Fin 36).symm

private def traceMask (s : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => if k < 36 then toggleMask (traceMask s k) (35 - k) else traceMask s k

private def cycleMasks : Array ℕ := #[
  503316544, 1007140992, 2131722496, 4263444992, 8526889984, 17053779968,
  34107555840, 68198338304, 521138431, 1057223166, 517116, 51365880,
  102731760, 205456352, 402655168, 805769088, 2131623936, 4263251904,
  8527004544, 17167255296, 8326656, 536742912, 1040188352, 17299328,
  51375872, 102744064, 205492216, 411011056, 1057165280, 393280,
  1056964736, 2114969856, 4280271360, 8560542720, 17121085440, 34242166784,
  68467560384, 251916351, 520220798, 254204, 50840056, 101680112,
  203360224, 406720448, 813434752, 1610616576, 3223060480, 8576831360,
  17154696960, 34351336960, 16747520, 251659248, 128992, 17035200,
  34062336, 68128760, 136282608, 520160224, 133056, 1057230720,
  2114453504, 4228910848, 8459878912, 17167221760, 8259584, 1073479680,
  2113933184, 17821696, 52424702, 104850428, 251709432, 102384,
  251854880]

private def cycleMask (i : Fin 73) : ℕ := cycleMasks[i.val]!

/-- The conjecture fails on a literal orbit of interval-closed sets of [3] × [12]. -/
theorem result : ¬ claim := by
  classical
  have lowerBound : ∀ y : Fin 36, lowerMasks[y.val]! < 2 ^ 36 := by decide +kernel
  have upperBound : ∀ y : Fin 36, upperMasks[y.val]! < 2 ^ 36 := by decide +kernel
  have lowerBits (y : Fin 36) : ∀ x : Fin 36,
      lowerMasks[y.val]!.testBit x.val = true ↔
        (finProdFinEquiv.symm x : Point 3 12) ≤ finProdFinEquiv.symm y := by
    fin_cases y <;> decide +kernel
  have upperBits (y : Fin 36) : ∀ z : Fin 36,
      upperMasks[y.val]!.testBit z.val = true ↔
        (finProdFinEquiv.symm y : Point 3 12) ≤ finProdFinEquiv.symm z := by
    fin_cases y <;> decide +kernel
  have intersects (s a : ℕ) (ha : a < 2 ^ 36) :
      s &&& a ≠ 0 ↔ ∃ x : Fin 36, s.testBit x.val = true ∧ a.testBit x.val = true := by
    constructor
    · intro h
      by_contra hn
      apply h
      apply Nat.zero_of_testBit_eq_false
      intro k
      rw [Nat.testBit_land]
      by_cases hk : k < 36
      · have hh : ¬ (s.testBit k = true ∧ a.testBit k = true) :=
          fun h => hn ⟨⟨k, hk⟩, h⟩
        cases hs : s.testBit k <;> cases ha' : a.testBit k <;> simp_all
      · have hp : 2 ^ 36 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_eq_false_of_lt (ha.trans_le hp), Bool.and_false]
    · rintro ⟨x, hx, hax⟩ he
      have hh := congrArg (fun z : ℕ => z.testBit x.val) he
      simp only [Nat.testBit_land, hx, hax, Bool.and_true, Nat.zero_testBit] at hh
      contradiction
  have convex (s : ℕ) : convexMask s = true ↔ (decode s).OrdConnected := by
    have all : convexMask s = true ↔ ∀ y : Fin 36,
        s.testBit y.val = true ∨ ¬
          ((∃ x : Fin 36, s.testBit x.val = true ∧
            (finProdFinEquiv.symm x : Point 3 12) ≤ finProdFinEquiv.symm y) ∧
          (∃ z : Fin 36, s.testBit z.val = true ∧
            (finProdFinEquiv.symm y : Point 3 12) ≤ finProdFinEquiv.symm z)) := by
      simp only [convexMask, List.all_eq_true, List.mem_finRange, forall_true_left,
        Bool.or_eq_true, decide_eq_true_eq]
      apply forall_congr'
      intro y
      have hl := intersects s lowerMasks[y.val]! (lowerBound y)
      have hu := intersects s upperMasks[y.val]! (upperBound y)
      simp_rw [lowerBits] at hl
      simp_rw [upperBits] at hu
      have hl' : s &&& lowerMasks[y.val]! = 0 ↔ ¬ ∃ x : Fin 36,
          s.testBit x.val = true ∧
            (finProdFinEquiv.symm x : Point 3 12) ≤ finProdFinEquiv.symm y := by
        simpa only [not_not] using not_congr hl
      have hu' : s &&& upperMasks[y.val]! = 0 ↔ ¬ ∃ z : Fin 36,
          s.testBit z.val = true ∧
            (finProdFinEquiv.symm y : Point 3 12) ≤ finProdFinEquiv.symm z := by
        simpa only [not_not] using not_congr hu
      rw [hl', hu']
      rw [not_and_or, or_assoc]
    rw [all]
    constructor
    · intro h
      constructor
      intro x hx z hz y hy
      rcases h (finProdFinEquiv y) with h | h
      · exact h
      · exact False.elim (h ⟨⟨finProdFinEquiv x, hx, by simpa using hy.1⟩,
          ⟨finProdFinEquiv z, hz, by simpa using hy.2⟩⟩)
    · intro h y
      by_cases hy : s.testBit y.val = true
      · exact Or.inl hy
      · refine Or.inr ?_
        rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩
        apply hy
        have hx' : finProdFinEquiv.symm x ∈ decode s := by simpa [decode] using hx
        have hz' : finProdFinEquiv.symm z ∈ decode s := by simpa [decode] using hz
        simpa [decode] using h.out hx' hz' ⟨hxy, hyz⟩
  have flip (s : ℕ) (k : Fin 36) :
      decode (s ^^^ 2 ^ k.val) = decode s ∆ {finProdFinEquiv.symm k} := by
    ext x
    simp only [decode, Set.mem_ofPred_eq, Nat.testBit_xor, Nat.testBit_two_pow,
      Set.mem_symmDiff, Set.mem_singleton_iff]
    have eq : (finProdFinEquiv x).val = k.val ↔ x = finProdFinEquiv.symm k := by
      rw [← Fin.ext_iff, ← Equiv.eq_symm_apply]
    by_cases h : x = finProdFinEquiv.symm k
    · simp [h]
    · have hh : (finProdFinEquiv x).val ≠ k.val := mt eq.mp h
      simp [Ne.symm hh, h]
  have step (s : ℕ) (k : Fin 36) :
      decode (toggleMask s k.val) = toggle (finProdFinEquiv.symm k) (decode s) := by
    unfold toggleMask toggle
    rw [← flip]
    by_cases h : convexMask (s ^^^ 2 ^ k.val) = true
    · rw [if_pos h, if_pos ((convex _).mp h)]
    · rw [if_neg h, if_neg (mt (convex _).mpr h)]
  have transport (s : ℕ) (k : ℕ) :
      decode (traceMask s k) = trace extension (decode s) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      unfold traceMask trace
      by_cases hk : k < 36
      · simp only [dif_pos hk, if_pos hk]
        rw [← ih]
        have hk' : 35 - k = (Fin.revPerm (⟨k, hk⟩ : Fin 36)).val := by
          change 35 - k = 36 - (k + 1)
          omega
        rw [hk']
        simpa only [extension, Equiv.trans_apply] using step (traceMask s k) (Fin.revPerm ⟨k, hk⟩)
      · simp only [dif_neg hk, if_neg hk, ih]
  have legal : ReverseExtension extension := by
    intro x y hxy
    have h₁ := hxy.le.1
    have h₂ := hxy.le.2
    have hx₁ := x.1.isLt
    have hx₂ := x.2.isLt
    have hy₁ := y.1.isLt
    have hy₂ := y.2.isLt
    have hc : x.2.val + 12 * x.1.val < y.2.val + 12 * y.1.val := by
      change x.1.val ≤ y.1.val at h₁
      change x.2.val ≤ y.2.val at h₂
      by_contra h
      have he₁ : x.1.val = y.1.val := by omega
      have he₂ : x.2.val = y.2.val := by omega
      exact (ne_of_lt hxy) (Prod.ext (Fin.ext he₁) (Fin.ext he₂))
    change 36 - (y.2.val + 12 * y.1.val + 1) <
      36 - (x.2.val + 12 * x.1.val + 1)
    omega
  have certificate : ∀ i : Fin 73,
      traceMask (cycleMask i) 36 = cycleMask (i + 1) := by
    decide +kernel
  have initial : convexMask (cycleMask 0) = true := by decide +kernel
  have bounded : ∀ i : Fin 73, cycleMask i < 2 ^ 36 := by decide +kernel
  have distinct : Function.Injective cycleMask := by decide +kernel
  let R : Set (Point 3 12) → Set (Point 3 12) := fun S => trace extension S 36
  have next (i : Fin 73) : R (decode (cycleMask i)) = decode (cycleMask (i + 1)) := by
    change trace extension (decode (cycleMask i)) 36 = _
    rw [← transport, certificate]
  have iter (k : ℕ) : R^[k] (decode (cycleMask 0)) = decode (cycleMask (Fin.ofNat 73 k)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, next]
      congr 2
      apply Fin.ext
      change (k % 73 + 1) % 73 = (k + 1) % 73
      omega
  have decodedDistinct : Function.Injective (fun i : Fin 73 => decode (cycleMask i)) := by
    intro i j h
    apply distinct
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 36
    · let x : Point 3 12 := finProdFinEquiv.symm ⟨k, hk⟩
      have hx := Set.ext_iff.mp h x
      have hh : (cycleMask i).testBit k = true ↔ (cycleMask j).testBit k = true := by
        change (cycleMask i).testBit (finProdFinEquiv (finProdFinEquiv.symm ⟨k, hk⟩)).val = true ↔
          (cycleMask j).testBit (finProdFinEquiv (finProdFinEquiv.symm ⟨k, hk⟩)).val = true at hx
        simpa only [Equiv.apply_symm_apply] using hx
      exact Bool.eq_iff_iff.mpr hh
    · have hp : 2 ^ 36 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_eq_false_of_lt ((bounded i).trans_le hp),
        Nat.testBit_eq_false_of_lt ((bounded j).trans_le hp)]
  have orbit : literalOrbit extension (decode (cycleMask 0)) =
      Finset.univ.image (fun i : Fin 73 => decode (cycleMask i)) := by
    ext S
    simp only [literalOrbit, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image] at ⊢
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨Fin.ofNat 73 k, (iter k).symm.trans hk⟩
    · rintro ⟨i, hi⟩
      refine ⟨i.val, ?_⟩
      have hi' : decode (cycleMask (Fin.ofNat 73 i.val)) = S := by
        simpa only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hi
      exact (iter i.val).trans hi'
  have value (s : ℕ) : signedCardinality (decode s) =
      ∑ x : Point 3 12, if s.testBit (finProdFinEquiv x).val then signedWeight x else 0 := by
    unfold signedCardinality
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : s.testBit (finProdFinEquiv x).val = true
    · simp [decode, h]
    · simp [decode, h]
  have total : (∑ i : Fin 73, ∑ x : Point 3 12,
      if (cycleMask i).testBit (finProdFinEquiv x).val then signedWeight x else 0) = -1 := by
    decide +kernel
  intro h
  have hz := h 3 12 36 (Or.inr rfl) (by decide) (by decide)
    extension legal (decode (cycleMask 0)) ((convex _).mp initial)
  rw [orbit, Finset.sum_image (fun i _ j _ hij => decodedDistinct hij)] at hz
  simp_rw [value] at hz
  omega

#print axioms result

end D5.S3.Combinatorics.Geometry.IntervalClosedSignedCardinalityRefutation
