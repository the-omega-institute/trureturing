/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pShortSyndrome
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pShortSyndrome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first nineteen P48p pairing rows distinguish short ternary words. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pShortSyndromeCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.ModEq

/-!
# Short ternary syndromes for P48p

Every word of Hamming weight at most three is represented by its list of
nonzero entries. The enumeration adds its packed pairing columns in base
eight, so each lane stays below eight before reduction modulo three. The
resulting key encodes the first nineteen syndrome trits. Distinctness of the
enumerated keys yields injectivity on short words and excludes norm two in
the catalogue lattice.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pShortSyndrome

open scoped BigOperators Matrix
open LatticeGeneratingFieldLocality (Charge bilinear)
open NormTwoTernarySyndrome (ternarySyndrome)
open P48pShortSyndromeCertificate
  (all_bucket_nodup bucketKeys columnData sparseKeysBucket transcode)
open P48pSyndromeFrame (p48pPairingFrame p48pCatalogueData)

private abbrev Entry (n : ℕ) := Fin n × ZMod 3

/- At each coordinate, choose the first nonzero coefficient, the second, or
   zero. The budget makes this enumeration sparse. -/
private def sparseWords {α : Type*} : List (α × α) → ℕ → List (List α)
  | [], _ => [[]]
  | _ :: _, 0 => [[]]
  | ab :: rest, budget + 1 =>
      ((sparseWords rest budget).map (fun w => ab.1 :: w)) ++
      ((sparseWords rest budget).map (fun w => ab.2 :: w)) ++
      sparseWords rest (budget + 1)

private def choices {n : ℕ} (indices : List (Fin n)) : List (Entry n × Entry n) :=
  indices.map fun i => ((i, 1), (i, 2))

private def entries {n : ℕ} (indices : List (Fin n)) (u : Fin n → ZMod 3) :
    List (Entry n) :=
  (indices.filter fun i => decide (u i ≠ 0)).map fun i => (i, u i)

private theorem trit_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 :=
  (by decide +kernel : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2) a

private theorem entries_mem_sparseWords {n : ℕ} (u : Fin n → ZMod 3)
    (indices : List (Fin n)) (budget : ℕ) (h : (entries indices u).length ≤ budget) :
    entries indices u ∈ sparseWords (choices indices) budget := by
  induction indices generalizing budget with
  | nil => simp [entries, choices, sparseWords]
  | cons i rest ih =>
    cases budget with
    | zero =>
      have he : entries (i :: rest) u = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      simp [he, choices, sparseWords]
    | succ budget =>
      simp only [choices, List.map_cons, sparseWords, List.mem_append]
      by_cases hi : u i = 0
      · have he : entries (i :: rest) u = entries rest u := by
          simp [entries, hi]
        rw [he] at h ⊢
        exact Or.inr (ih _ h)
      · have he : entries (i :: rest) u = (i, u i) :: entries rest u := by
          simp [entries, hi]
        have hrest : (entries rest u).length ≤ budget := by
          simpa only [he, List.length_cons, Nat.succ_le_succ_iff] using h
        have hm := ih budget hrest
        rw [he]
        rcases trit_cases (u i) with hz | h₁ | h₂
        · exact (hi hz).elim
        · rw [h₁]
          exact Or.inl (Or.inl (List.mem_map_of_mem hm))
        · rw [h₂]
          exact Or.inl (Or.inr (List.mem_map_of_mem hm))

private theorem entries_length {n : ℕ} (u : Fin n → ZMod 3) :
    (entries (List.finRange n) u).length = hammingNorm u := by
  unfold entries hammingNorm
  rw [List.length_map, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  rw [List.toFinset_filter, List.toFinset_finRange]
  simp only [decide_eq_true_eq]

private theorem mem_entries {n : ℕ} (u : Fin n → ZMod 3) (j : Fin n) (a : ZMod 3) :
    (j, a) ∈ entries (List.finRange n) u ↔ u j ≠ 0 ∧ u j = a := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hij : i = j := congrArg Prod.fst he
    subst i
    exact ⟨by simpa using (List.mem_filter.mp hi).2, congrArg Prod.snd he⟩
  · rintro ⟨hn, rfl⟩
    exact List.mem_map.mpr
      ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hn⟩, rfl⟩

private theorem entries_injective {n : ℕ} :
    Function.Injective (entries (List.finRange n)) := by
  intro u v h
  funext j
  by_cases hu : u j = 0
  · by_contra huv
    have hv : v j ≠ 0 := fun hz => huv (hu.trans hz.symm)
    have hm := (mem_entries v j (v j)).mpr ⟨hv, rfl⟩
    rw [← h] at hm
    exact ((mem_entries u j (v j)).mp hm).1 hu
  · have hm := (mem_entries u j (u j)).mpr ⟨hu, rfl⟩
    rw [h] at hm
    exact ((mem_entries v j (u j)).mp hm).2.symm

/-- Positional packing with digit zero least significant. -/
private def pack (base : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, digit => digit 0 + base * pack base n (fun i => digit (i + 1))

private theorem pack_add (base n : ℕ) (f g : ℕ → ℕ) :
    pack base n (fun i => f i + g i) = pack base n f + pack base n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack, ih, Nat.mul_add]
    ac_rfl

private theorem pack_sum {α : Type*} (base n : ℕ) (digit : α → ℕ → ℕ) (w : List α) :
    (w.map fun a => pack base n (digit a)).sum =
      pack base n (fun i => (w.map fun a => digit a i).sum) := by
  induction w with
  | nil =>
    change 0 = pack base n (fun _ => 0)
    induction n with
    | zero => rfl
    | succ n ih => rw [pack, ← ih, Nat.mul_zero, Nat.add_zero]
  | cons a w ih =>
    simp only [List.map_cons, List.sum_cons, ih, pack_add]

private theorem transcode_modEq_one (n wide : ℕ) :
    transcode (n + 1) wide ≡ transcode 1 wide [MOD 3] := by
  simp [Nat.ModEq, transcode, Nat.add_mod, Nat.mul_mod]

private theorem transcode_modEq_two (n wide : ℕ) :
    transcode (n + 2) wide ≡ transcode 2 wide [MOD 9] := by
  have h3 : transcode (n + 1) (wide / 8) ≡
      transcode 1 (wide / 8) [MOD 3] :=
    transcode_modEq_one n (wide / 8)
  have h9 : 3 * transcode (n + 1) (wide / 8) ≡
      3 * transcode 1 (wide / 8) [MOD 9] :=
    h3.mul_left' 3
  change
    wide % 8 % 3 + 3 * transcode (n + 1) (wide / 8) ≡
      wide % 8 % 3 + 3 * transcode 1 (wide / 8) [MOD 9]
  exact h9.add_left (wide % 8 % 3)

private theorem transcode_modEq (n wide : ℕ) :
    transcode (n + 3) wide ≡ transcode 3 wide [MOD 27] := by
  have h9 : transcode (n + 2) (wide / 8) ≡
      transcode 2 (wide / 8) [MOD 9] :=
    transcode_modEq_two n (wide / 8)
  have h27 : 3 * transcode (n + 2) (wide / 8) ≡
      3 * transcode 2 (wide / 8) [MOD 27] :=
    h9.mul_left' 3
  change
    wide % 8 % 3 + 3 * transcode (n + 2) (wide / 8) ≡
      wide % 8 % 3 + 3 * transcode 2 (wide / 8) [MOD 27]
  exact h27.add_left (wide % 8 % 3)

private theorem transcode_19_mod_27 (wide : ℕ) :
    transcode 19 wide % 27 = transcode 3 wide := by
  have hlt : transcode 3 wide < 27 := by
    simp only [transcode, Nat.mul_zero, Nat.add_zero]
    have h0 : wide % 8 % 3 < 3 := Nat.mod_lt _ (by decide)
    have h1 : (wide / 8) % 8 % 3 < 3 := Nat.mod_lt _ (by decide)
    have h2 : (wide / 8 / 8) % 8 % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have h : transcode 19 wide % 27 = transcode 3 wide % 27 := transcode_modEq 16 wide
  exact h.trans (Nat.mod_eq_of_lt hlt)

private theorem transcode_pack (n : ℕ) (digit : ℕ → ℕ) (h : ∀ i, digit i < 8) :
    transcode n (pack 8 n digit) = pack 3 n (fun i => digit i % 3) := by
  induction n generalizing digit with
  | zero => rfl
  | succ n ih =>
    simp only [transcode, pack, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ (by decide : 0 < 8),
      Nat.mod_eq_of_lt (h 0), Nat.div_eq_of_lt (h 0), Nat.zero_add]
    rw [ih _ (fun i => h (i + 1))]

private theorem sum_digits_le {α : Type*} (digit : α → ℕ) (h : ∀ a, digit a ≤ 2)
    (w : List α) : (w.map digit).sum ≤ 2 * w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a
    omega

private def rowIndex (i : ℕ) : Fin 48 := ⟨i % 48, Nat.mod_lt _ (by decide)⟩

private def rowEntry (i : ℕ) (a : Entry 48) : ZMod 3 :=
  (p48pPairingFrame (rowIndex i) a.1 : ZMod 3) * a.2

private def wideColumn (a : Entry 48) : ℕ :=
  pack 8 19 (fun i => (rowEntry i a).val)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- Each check reduces the concrete pairing entries for one column.
private theorem columnData_eq (i : Fin 48) :
    columnData.getD i.val (0, 0) = (wideColumn (i, 1), wideColumn (i, 2)) := by
  fin_cases i <;> decide +kernel

/- Accumulate wide columns while enumerating so the computation only retains
   the exact numerical keys. -/
private def sparseKeys (finish : ℕ → ℕ) : List (ℕ × ℕ) → ℕ → ℕ → List ℕ
  | [], _, acc => [finish acc]
  | _ :: _, 0, acc => [finish acc]
  | ab :: rest, budget + 1, acc =>
      sparseKeys finish rest budget (acc + ab.1) ++
      sparseKeys finish rest budget (acc + ab.2) ++
      sparseKeys finish rest (budget + 1) acc

private theorem sparseKeys_eq {α : Type*} (finish : ℕ → ℕ)
    (lift : α → ℕ) (cs : List (α × α)) (budget acc : ℕ) :
    sparseKeys finish (cs.map fun ab => (lift ab.1, lift ab.2)) budget acc =
      (sparseWords cs budget).map fun w => finish (acc + (w.map lift).sum) := by
  induction cs generalizing budget acc with
  | nil => simp [sparseKeys, sparseWords]
  | cons ab cs ih =>
    cases budget with
    | zero => simp [sparseKeys, sparseWords]
    | succ budget =>
      simp [sparseKeys, sparseWords, ih, List.map_map, Function.comp_def, Nat.add_assoc]

private def shortKeys : List ℕ :=
  sparseKeys (transcode 19)
    ((List.finRange 48).map fun i => columnData.getD i.val (0, 0)) 3 0

private def key (w : List (Entry 48)) : ℕ := transcode 19 (w.map wideColumn).sum

private theorem shortKeys_eq :
    shortKeys = (sparseWords (choices (List.finRange 48)) 3).map key := by
  have h : (List.finRange 48).map (fun i => columnData.getD i.val (0, 0)) =
      (choices (List.finRange 48)).map (fun ab => (wideColumn ab.1, wideColumn ab.2)) := by
    simp only [choices, List.map_map, Function.comp_def, columnData_eq]
  unfold shortKeys
  rw [h, sparseKeys_eq]
  simp only [Nat.zero_add]
  rfl

private theorem val_sum {α : Type*} (w : List α) (f : α → ZMod 3) :
    ((w.map f).sum).val = (w.map fun a => (f a).val).sum % 3 := by
  have h : (↑((w.map fun a => (f a).val).sum) : ZMod 3) = (w.map f).sum := by
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def, ZMod.natCast_zmod_val]
  rw [← h, ZMod.val_natCast]

private theorem key_eq_pack (w : List (Entry 48)) (hw : w.length ≤ 3) :
    key w = pack 3 19 (fun i => ((w.map (rowEntry i)).sum).val) := by
  unfold key wideColumn
  rw [pack_sum, transcode_pack]
  · apply congrArg (pack 3 19)
    funext i
    exact (val_sum w (rowEntry i)).symm
  · intro i
    have h := sum_digits_le (fun a => (rowEntry i a).val)
      (fun a => Nat.le_of_lt_succ (ZMod.val_lt (rowEntry i a))) w
    omega

private theorem entry_sum (indices : List (Fin 48)) (u : Fin 48 → ZMod 3) (i : ℕ) :
    ((entries indices u).map (rowEntry i)).sum =
      (indices.map (fun j => rowEntry i (j, u j))).sum := by
  induction indices with
  | nil => rfl
  | cons j rest ih =>
    by_cases h : u j = 0
    · have he : entries (j :: rest) u = entries rest u := by
        simp [entries, h]
      rw [he, ih]
      simp [rowEntry, h]
    · have he : entries (j :: rest) u = (j, u j) :: entries rest u := by
        simp [entries, h]
      rw [he]
      simp only [List.map_cons, List.sum_cons, ih]

private theorem key_entries (u : Fin 48 → ZMod 3) (hu : hammingNorm u ≤ 3) :
    key (entries (List.finRange 48) u) =
      pack 3 19 (fun i => (ternarySyndrome p48pPairingFrame u (rowIndex i)).val) := by
  rw [key_eq_pack _ ((entries_length u).trans_le hu)]
  apply congrArg (pack 3 19)
  funext i
  rw [entry_sum]
  simp only [ternarySyndrome, Matrix.mulVec_apply_eq_sum, Matrix.map_apply, rowEntry, Fin.univ_def]
  rfl

private theorem sparseKeysBucket_eq {α : Type*} (bucket : Fin 27)
    (lift : α → ℕ) (cs : List (α × α)) (budget acc : ℕ) :
    sparseKeysBucket bucket (transcode 19)
        (cs.map fun ab => (lift ab.1, lift ab.2)) budget acc =
      (sparseKeys (transcode 19)
        (cs.map fun ab => (lift ab.1, lift ab.2)) budget acc).filter
        (fun k => decide (k % 27 = bucket.val)) := by
  induction cs generalizing budget acc with
  | nil =>
      by_cases h : transcode 3 acc = bucket.val <;>
        simp [sparseKeysBucket, sparseKeys, transcode_19_mod_27, h]
  | cons ab cs ih =>
      cases budget with
      | zero =>
          by_cases h : transcode 3 acc = bucket.val <;>
            simp [sparseKeysBucket, sparseKeys, transcode_19_mod_27, h]
      | succ budget =>
          simp [sparseKeysBucket, sparseKeys, ih, transcode_19_mod_27,
            Nat.add_assoc]

private theorem bucketKeys_eq (bucket : Fin 27) :
    bucketKeys bucket =
      ((sparseWords (choices (List.finRange 48)) 3).map key).filter
        (fun k => decide (k % 27 = bucket.val)) := by
  have h : (List.finRange 48).map (fun i => columnData.getD i.val (0, 0)) =
      (choices (List.finRange 48)).map (fun ab => (wideColumn ab.1, wideColumn ab.2)) := by
    simp only [choices, List.map_map, Function.comp_def, columnData_eq]
  unfold bucketKeys
  rw [h, sparseKeysBucket_eq]
  have hs : shortKeys =
      sparseKeys (transcode 19)
        ((choices (List.finRange 48)).map
          (fun ab => (wideColumn ab.1, wideColumn ab.2))) 3 0 := by
    unfold shortKeys
    rw [h]
  rw [← hs, shortKeys_eq]

private theorem nodup_of_bucket_filters (ks : List ℕ)
    (h : ∀ bucket : Fin 27,
      (ks.filter (fun k => decide (k % 27 = bucket.val))).Nodup) :
    ks.Nodup := by
  induction ks with
  | nil => simp
  | cons a ks ih =>
      apply List.Nodup.cons
      · intro ha
        let bucket : Fin 27 := ⟨a % 27, Nat.mod_lt _ (by decide)⟩
        have hp : decide (a % 27 = bucket.val) = true := by
          simp [bucket]
        have htail : a ∈ ks.filter
            (fun k => decide (k % 27 = bucket.val)) :=
          List.mem_filter.mpr ⟨ha, hp⟩
        have hfull := h bucket
        have heq : (a :: ks).filter
            (fun k => decide (k % 27 = bucket.val)) =
            a :: ks.filter (fun k => decide (k % 27 = bucket.val)) := by
          simp [hp]
        rw [heq] at hfull
        exact hfull.notMem htail
      · apply ih
        intro bucket
        by_cases hp : decide (a % 27 = bucket.val) = true
        · have heq : (a :: ks).filter
              (fun k => decide (k % 27 = bucket.val)) =
              a :: ks.filter (fun k => decide (k % 27 = bucket.val)) := by
            simp [hp]
          have hfull := h bucket
          rw [heq] at hfull
          exact hfull.of_cons
        · have heq : (a :: ks).filter
              (fun k => decide (k % 27 = bucket.val)) =
              ks.filter (fun k => decide (k % 27 = bucket.val)) := by
            simp [hp]
          have hfull := h bucket
          rw [heq] at hfull
          exact hfull

private theorem shortKeys_nodup :
    ((sparseWords (choices (List.finRange 48)) 3).map key).Nodup := by
  apply nodup_of_bucket_filters
  intro bucket
  rw [← bucketKeys_eq bucket]
  exact all_bucket_nodup bucket

/-- The first nineteen syndrome trits distinguish every two words of Hamming
weight at most three. -/
theorem p48p_short_syndrome_injective :
    Set.InjOn (ternarySyndrome p48pPairingFrame) {u | hammingNorm u ≤ 3} := by
  intro u hu v hv h
  have hkeys := shortKeys_nodup
  have hum := entries_mem_sparseWords u (List.finRange 48) 3 ((entries_length u).trans_le hu)
  have hvm := entries_mem_sparseWords v (List.finRange 48) 3 ((entries_length v).trans_le hv)
  refine entries_injective (List.inj_on_of_nodup_map hkeys hum hvm ?_)
  rw [key_entries u hu, key_entries v hv, h]

/-- The catalogue P48p lattice has no vectors of norm two. -/
theorem p48p_catalogue_rootless (x : Charge p48pCatalogueData) :
    bilinear p48pCatalogueData x x ≠ 2 :=
  P48pSyndromeFrame.p48p_catalogue_rootless p48p_short_syndrome_injective x

#print axioms p48p_short_syndrome_injective
#print axioms p48p_catalogue_rootless

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pShortSyndrome
