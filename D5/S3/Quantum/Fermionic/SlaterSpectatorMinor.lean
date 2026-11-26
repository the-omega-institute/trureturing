/- GID: D5/S3/Quantum/Fermionic/SlaterSpectatorMinor
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterSpectatorMinor
   mirror-E: none(waiver:ordered-coordinate-cofactor)
   anchors: []
   utility: none
   digest: Ordered Slater minors with an appended coordinate orbital. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin

/-! # Ordered Slater minors with an appended orbital -/

namespace D5.S3.Quantum.Fermionic.SlaterSpectatorMinor

open Matrix Finset
open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- Append the coordinate column at the prescribed site. -/
def appendOrbital {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι) :
    Matrix ι (Fin (k + 1)) ℂ :=
  fun s => Fin.snoc (V s) (if s = p then 1 else 0)

private theorem minor_without_spectator {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι)
    (S : Finset ι) (hS : S.card = k + 1) (hp : p ∉ S) :
    ((appendOrbital V p).submatrix (S.orderEmbOfFin hS) id).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last k)
  intro i
  have hne : S.orderEmbOfFin hS i ≠ p := fun he =>
    hp (he ▸ S.orderEmbOfFin_mem hS i)
  simp [Matrix.submatrix_apply, appendOrbital, hne]

private theorem ordered_erase {k : ℕ} (S : Finset ι) (hS : S.card = k + 1)
    (j : Fin (k + 1)) {p : ι} (hj : S.orderEmbOfFin hS j = p)
    (hp : p ∈ S) :
    (fun i : Fin k => S.orderEmbOfFin hS (j.succAbove i)) =
      (S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    apply Finset.mem_erase.mpr
    refine ⟨fun he => ?_, S.orderEmbOfFin_mem hS _⟩
    apply Fin.succAbove_ne j i
    exact (S.orderEmbOfFin hS).injective (he.trans hj.symm)
  · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove j)

private theorem tail_card_of_rank {k : ℕ} (S : Finset ι) (hS : S.card = k + 1)
    (j : Fin (k + 1)) {p : ι} (hj : S.orderEmbOfFin hS j = p) :
    (S.filter (p < ·)).card = k - (j : ℕ) := by
  have he : (Finset.Ioi j).map (S.orderEmbOfFin hS).toEmbedding = S.filter (p < ·) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem hS i,
        hj ▸ (S.orderEmbOfFin hS).strictMono (Finset.mem_Ioi.mp hi)⟩
    · intro hz
      obtain ⟨hs, hlt⟩ := Finset.mem_filter.mp hz
      let i := (S.orderIsoOfFin hS).symm ⟨z, hs⟩
      have hi : S.orderEmbOfFin hS i = z :=
        congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨z, hs⟩)
      refine Finset.mem_map.mpr ⟨i, Finset.mem_Ioi.mpr ?_, hi⟩
      apply (S.orderEmbOfFin hS).strictMono.lt_iff_lt.mp
      simpa only [hj, hi] using hlt
  rw [← he, Finset.card_map, Fin.card_Ioi]
  omega

private theorem minor_with_spectator {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι)
    (S : Finset ι) (hS : S.card = k + 1) (hp : p ∈ S) :
    ((appendOrbital V p).submatrix (S.orderEmbOfFin hS) id).det =
      (-1 : ℂ) ^ (S.filter (p < ·)).card *
        (V.submatrix ((S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp)) id).det := by
  classical
  let j := (S.orderIsoOfFin hS).symm ⟨p, hp⟩
  have hj : S.orderEmbOfFin hS j = p :=
    congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨p, hp⟩)
  let A := (appendOrbital V p).submatrix (S.orderEmbOfFin hS) id
  have hcol (i : Fin (k + 1)) : A i (Fin.last k) = if i = j then 1 else 0 := by
    change (appendOrbital V p) (S.orderEmbOfFin hS i) (Fin.last k) = _
    simp [appendOrbital, ← hj, (S.orderEmbOfFin hS).injective.eq_iff]
  have hminor : A.submatrix j.succAbove (Fin.last k).succAbove =
      V.submatrix ((S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp)) id := by
    ext i l : 1
    have he := congrFun (ordered_erase S hS j hj hp) i
    simp only [A, Matrix.submatrix_apply, id_eq, Fin.succAbove_last, appendOrbital, Fin.snoc_castSucc]
    rw [he]
  change A.det = _
  rw [Matrix.det_succ_column A (Fin.last k)]
  simp_rw [hcol]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, mul_one, hminor, tail_card_of_rank S hS j hj]
    have he : (j : ℕ) + (Fin.last k : ℕ) = (k - (j : ℕ)) + 2 * (j : ℕ) := by
      simp only [Fin.val_last]
      have hjk := j.isLt
      omega
    rw [he, pow_add]
    simp [pow_mul]
  · intro i _ hne
    simp [hne]
  · simp

/-- The increasingly ordered occupied minor, with zero amplitude outside
the particle-number sector. -/
noncomputable def occupiedMinor {k : ℕ} (V : Matrix ι (Fin k) ℂ) (S : Finset ι) : ℂ :=
  if h : S.card = k then (V.submatrix (S.orderEmbOfFin h) id).det else 0

/-- The added coordinate must be occupied. Its cofactor sign is determined by the
number of occupied sites that follow it in the ambient site order. -/
theorem occupiedMinor_append {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (p : ι) (S : Finset ι) :
    occupiedMinor (appendOrbital V p) S =
      if p ∈ S then (-1 : ℂ) ^ (S.filter (p < ·)).card * occupiedMinor V (S.erase p) else 0 := by
  classical
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp]
    by_cases hS : S.card = k + 1
    · have hErase : (S.erase p).card = k := by
        rw [Finset.card_erase_of_mem hp, hS]
        omega
      simp only [occupiedMinor, dite_eq_left hS, dite_eq_left hErase]
      exact minor_with_spectator V p S hS hp
    · have hErase : (S.erase p).card ≠ k := by
        rw [Finset.card_erase_of_mem hp]
        have hpos := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      simp [occupiedMinor, hS, hErase]
  · rw [ite_eq_right hp]
    by_cases hS : S.card = k + 1
    · simpa [occupiedMinor, hS] using minor_without_spectator V p S hS hp
    · simp [occupiedMinor, hS]

theorem append_gram {k : ℕ} [Fintype ι] (V : Matrix ι (Fin k) ℂ)
    (p : ι) (hV : V.conjTranspose * V = 1) (hp : ∀ i, V p i = 0) :
    (appendOrbital V p).conjTranspose * appendOrbital V p = 1 := by
  classical
  ext i j : 1
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · have h := congrFun (congrFun hV i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, appendOrbital, Matrix.one_apply] using h
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, appendOrbital, hp]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, appendOrbital, hp,
      (Fin.castSucc_ne_last j).symm]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, appendOrbital]

private theorem enumerate_insert_max (p : ι) (T : Finset ι)
    (hmax : ∀ q ∈ T, q < p)
    (hcard : (insert p T).card = T.card + 1) :
    (fun j => (insert p T).orderEmbOfFin hcard j) =
      @Fin.snoc T.card (fun _ => ι) (fun j => T.orderEmbOfFin rfl j) p := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Finset.mem_insert_of_mem (T.orderEmbOfFin_mem rfl j)]
  · intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using
          (T.orderEmbOfFin rfl).strictMono (show i < j from hij)
      · rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact hmax _ (T.orderEmbOfFin_mem rfl i)
    · exact (not_lt_of_ge (Fin.le_last j) hij).elim

private theorem occupiedMinor_cast_columns {m n : ℕ} (h : m = n)
    (V : Matrix ι (Fin n) ℂ) (S : Finset ι) :
    occupiedMinor (fun i j => V i (Fin.cast h j) : Matrix ι (Fin m) ℂ) S =
      occupiedMinor V S := by
  subst n
  rfl

omit [LinearOrder ι] in
private theorem gram_cast_columns [Fintype ι] {m n : ℕ} (h : m = n)
    (V : Matrix ι (Fin n) ℂ) (hV : V.conjTranspose * V = 1) :
    let W : Matrix ι (Fin m) ℂ := fun i j => V i (Fin.cast h j)
    W.conjTranspose * W = 1 := by
  subst n
  exact hV

private theorem canonical_extension_exists {k : ℕ} [Fintype ι]
    (V : Matrix ι (Fin k) ℂ) (hV : V.conjTranspose * V = 1) (T : Finset ι)
    (hT : ∀ p ∈ T, ∀ j, V p j = 0) :
    ∃ W : Matrix ι (Fin (k + T.card)) ℂ,
      (∀ i j, W i (Fin.castAdd T.card j) = V i j) ∧
      (∀ i j, W i (Fin.natAdd k j) = if i = T.orderEmbOfFin rfl j then 1 else 0) ∧
      W.conjTranspose * W = 1 ∧
      (∀ q ∉ T, (∀ j, V q j = 0) → ∀ j, W q j = 0) ∧
      ∀ S : Finset ι, occupiedMinor W S =
        if T ⊆ S then
          (-1 : ℂ) ^ (∑ p ∈ T, ((S \ T).filter (p < ·)).card) * occupiedMinor V (S \ T)
        else 0 := by
  classical
  induction T using Finset.induction_on_max with
  | empty =>
    exact ⟨V, fun _ _ => rfl, fun _ j => Fin.elim0 j, hV, fun _ _ h => h, fun S => by simp⟩
  | insert p T hmax ih =>
    have hpT : p ∉ T := fun hp => (lt_irrefl p) (hmax p hp)
    obtain ⟨U, hUfirst, hUlast, hU, hUzero, hminor⟩ :=
      ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    have hpU : ∀ j, U p j = 0 := hUzero p hpT (hT p (Finset.mem_insert_self p T))
    have hcard : (insert p T).card = T.card + 1 := Finset.card_insert_of_notMem hpT
    have hsize : k + (insert p T).card = k + T.card + 1 := by rw [hcard, Nat.add_assoc]
    let W : Matrix ι (Fin (k + (insert p T).card)) ℂ :=
      fun i j => appendOrbital U p i (Fin.cast hsize j)
    refine ⟨W, ?_, ?_, gram_cast_columns hsize _ (append_gram U p hU hpU), ?_, ?_⟩
    · intro i j
      have hindex : Fin.cast hsize (Fin.castAdd (insert p T).card j) =
          (Fin.castAdd T.card j).castSucc := Fin.ext rfl
      change appendOrbital U p i _ = _
      rw [hindex]
      simpa [appendOrbital] using hUfirst i j
    · intro i j
      let j' := Fin.cast hcard j
      have horder : (insert p T).orderEmbOfFin rfl j =
          @Fin.snoc T.card (fun _ => ι) (fun j => T.orderEmbOfFin rfl j) p j' := by
        change (insert p T).orderEmbOfFin hcard j' = _
        exact congrFun (enumerate_insert_max p T hmax hcard) j'
      have hindex : Fin.cast hsize (Fin.natAdd k j) =
          Fin.natAdd k j' := Fin.ext rfl
      change appendOrbital U p i _ = _
      rw [hindex, horder]
      rcases Fin.eq_castSucc_or_eq_last j' with ⟨j', hj'⟩ | hj'
      · rw [hj', Fin.snoc_castSucc]
        have he : Fin.natAdd k j'.castSucc = (Fin.natAdd k j').castSucc := Fin.ext rfl
        rw [he]
        simpa only [appendOrbital, Fin.snoc_castSucc] using hUlast i j'
      · rw [hj', Fin.natAdd_last, Fin.snoc_last]
        simp only [appendOrbital, Fin.snoc_last]
    · intro q hq hVq j
      have hqp : q ≠ p := fun he => hq (he ▸ Finset.mem_insert_self p T)
      have hqT : q ∉ T := fun h => hq (Finset.mem_insert_of_mem h)
      change appendOrbital U p q (Fin.cast hsize j) = 0
      rcases Fin.eq_castSucc_or_eq_last (Fin.cast hsize j) with ⟨j, hj⟩ | hj
      · rw [hj]
        simp [appendOrbital, hUzero q hqT hVq j]
      · rw [hj]
        simp [appendOrbital, hqp]
    · intro S
      change occupiedMinor (fun i j => appendOrbital U p i (Fin.cast hsize j)) S = _
      rw [occupiedMinor_cast_columns hsize, occupiedMinor_append]
      by_cases hpS : p ∈ S
      · rw [ite_eq_left hpS, hminor]
        have hsub : T ⊆ S.erase p ↔ insert p T ⊆ S := by
          rw [Finset.insert_subset_iff, and_iff_right hpS]
          exact ⟨fun h q hq => (Finset.mem_erase.mp (h hq)).2,
            fun h q hq => Finset.mem_erase.mpr ⟨fun he => hpT (he ▸ hq), h hq⟩⟩
        have hsets : S.erase p \ T = S \ insert p T := by
          ext q
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          tauto
        have hfilter : S.filter (p < ·) = (S \ insert p T).filter (p < ·) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          refine ⟨fun h => ⟨⟨h.1, ?_⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
          rintro (rfl | hq)
          · exact (lt_irrefl _) h.2
          · exact (not_lt_of_gt (hmax q hq)) h.2
        by_cases h : insert p T ⊆ S
        · rw [ite_eq_left (hsub.mpr h), ite_eq_left h, hsets,
            Finset.sum_insert hpT, pow_add, ← mul_assoc, hfilter]
        · rw [ite_eq_right (fun hs => h (hsub.mp hs)), ite_eq_right h, mul_zero]
      · rw [ite_eq_right hpS, ite_eq_right (fun h => hpS (h (Finset.mem_insert_self p T)))]

/-- The ordered original and coordinate columns determine the orthonormal extension uniquely. -/
theorem canonical_ordered_spectator_extension {k : ℕ} [Fintype ι]
    (V : Matrix ι (Fin k) ℂ) (hV : V.conjTranspose * V = 1) (T : Finset ι)
    (hT : ∀ p ∈ T, ∀ j, V p j = 0) :
    ∃! W : Matrix ι (Fin (k + T.card)) ℂ,
      (∀ i j, W i (Fin.castAdd T.card j) = V i j) ∧
      (∀ i j, W i (Fin.natAdd k j) = if i = T.orderEmbOfFin rfl j then 1 else 0) ∧
      W.conjTranspose * W = 1 ∧
      (∀ q ∉ T, (∀ j, V q j = 0) → ∀ j, W q j = 0) ∧
      ∀ S : Finset ι, occupiedMinor W S =
        if T ⊆ S then
          (-1 : ℂ) ^ (∑ p ∈ T, ((S \ T).filter (p < ·)).card) * occupiedMinor V (S \ T)
        else 0 := by
  obtain ⟨W, hW⟩ := canonical_extension_exists V hV T hT
  refine ⟨W, hW, ?_⟩
  intro U hU
  ext i j : 1
  exact Fin.addCases (fun j => (hU.1 i j).trans (hW.1 i j).symm)
    (fun j => (hU.2.1 i j).trans (hW.2.1 i j).symm) j

end D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
