/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterFixedFilling
   mirror-E: none(waiver:fixed-filling-marginal)
   anchors: []
   utility: none
   digest: Product spectra and exact compression twins at fixed particle number. -/

import D5.S3.Quantum.Fermionic.OrderedSlaterPrefix
import D5.S3.Quantum.Fermionic.SlaterFixedFillingPhase
import D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
import Mathlib.Logic.Equiv.Set

/-! # Ordered Slater marginal spectra at fixed particle number -/

namespace D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling

open Matrix Finset
open SlaterCutPhase OrderedSlaterCut SlaterSpectatorMinor SlaterFixedFillingPhase
open scoped BigOperators symmDiff

variable {ι : Type*} [LinearOrder ι]

noncomputable local instance [Fintype ι] (I : Set ι) : Fintype (Occupation I) :=
  Fintype.ofFinite _

noncomputable local instance [Fintype ι] (I : Set ι) : Fintype I :=
  Fintype.ofFinite _

private theorem minor_zero_of_occupied_zero_row {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (p : ι) (hV : ∀ i, V p i = 0) (S : Finset ι) (hp : p ∈ S) :
    occupiedMinor V S = 0 := by
  classical
  unfold occupiedMinor
  split_ifs with hS
  · let j := (S.orderIsoOfFin hS).symm ⟨p, hp⟩
    have hj : S.orderEmbOfFin hS j = p :=
      congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨p, hp⟩)
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro i
    change V (S.orderEmbOfFin hS j) i = 0
    rw [hj, hV i]
  · rfl

private theorem orderedCut_eq_minor {k : ℕ} (I : Set ι) (V : Matrix ι (Fin k) ℂ)
    (a : Occupation I) (b : Occupation Iᶜ) :
    orderedCut I V a b = occupiedMinor V (a.val ∪ b.val) := by
  classical
  have hd : Disjoint a.val b.val := Finset.disjoint_left.mpr fun _ ha hb => b.property hb (a.property ha)
  have hU : a.val.disjUnion b.val hd = a.val ∪ b.val := Finset.disjUnion_eq_union a.val b.val hd
  change (if h : a.val.card + b.val.card = k then
    (V.submatrix ((a.val.disjUnion b.val hd).orderEmbOfFin
      ((Finset.card_disjUnion a.val b.val hd).trans h)) id).det else 0) = _
  rw [← hU]
  simp only [occupiedMinor, Finset.card_disjUnion]

private theorem diagonal_sign_inverse {α : Type*} [Fintype α] [DecidableEq α] (h : α → ℕ) :
    let D : Matrix α α ℂ := Matrix.diagonal fun i => (-1) ^ h i
    D.conjTranspose * D = 1 ∧ D * D.conjTranspose = 1 := by
  intro D
  have hstar : D.conjTranspose = D := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [star_pow]
  have hsq : D * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (-1 : ℂ) ^ h i * (-1 : ℂ) ^ h i) = fun _ => 1 := by
      funext i
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    rw [h1, Matrix.diagonal_one]
  simp [hstar, hsq]

private theorem signed_reindexed_gram {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (e : Equiv.Perm A) (f : Equiv.Perm B) (M : Matrix A B ℂ) (l : A → ℕ) (r : B → ℕ) :
    let N : Matrix A B ℂ := fun i j => (-1) ^ l i * ((-1) ^ r j * M (e i) (f j))
    (N * N.conjTranspose).charpoly = (M * M.conjTranspose).charpoly := by
  classical
  intro N
  let Y := M.submatrix e f
  let D : Matrix A A ℂ := Matrix.diagonal fun i => (-1) ^ l i
  let E : Matrix B B ℂ := Matrix.diagonal fun i => (-1) ^ r i
  have hN : N = D * Y * E := by
    ext i j : 1
    change _ = ((Matrix.diagonal (fun i => (-1 : ℂ) ^ l i) * Y) *
      Matrix.diagonal (fun j => (-1 : ℂ) ^ r j)) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    change (-1 : ℂ) ^ l i * ((-1) ^ r j * Y i j) = _
    ring
  have hb : E * E.conjTranspose = 1 := (diagonal_sign_inverse r).2
  have ha : D.conjTranspose * D = 1 := (diagonal_sign_inverse l).1
  have hGram : N * N.conjTranspose = D * (Y * Y.conjTranspose) * D.conjTranspose := by
    rw [hN]
    calc
      _ = D * (Y * (E * E.conjTranspose) * Y.conjTranspose) * D.conjTranspose := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hb, Matrix.mul_one]
  rw [hGram, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ha, Matrix.one_mul]
  change ((M.submatrix e f) * (M.submatrix e f).conjTranspose).charpoly = _
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact Matrix.charpoly_reindex e.symm (M * M.conjTranspose)

private def flipSpectators (I : Set ι) (T : Finset ι) (hT : (T : Set ι) ⊆ I) :
    Equiv.Perm (Occupation I) where
  toFun a := ⟨a.val ∆ T, fun i hi => by
    rcases Finset.mem_symmDiff.mp hi with ha | ht
    · exact a.property ha.1
    · exact hT ht.1⟩
  invFun a := ⟨a.val ∆ T, fun i hi => by
    rcases Finset.mem_symmDiff.mp hi with ha | ht
    · exact a.property ha.1
    · exact hT ht.1⟩
  left_inv a := Subtype.ext (symmDiff_symmDiff_cancel_right _ _)
  right_inv a := Subtype.ext (symmDiff_symmDiff_cancel_right _ _)

private theorem spectator_marginal_of_minors [Fintype ι] {k m : ℕ}
    (I : Set ι) (V : Matrix ι (Fin k) ℂ) (W : Matrix ι (Fin m) ℂ)
    (T : Finset ι) (hT : ∀ p ∈ T, ∀ j, V p j = 0)
    (hminor : ∀ S, occupiedMinor W S = if T ⊆ S then
      (-1 : ℂ) ^ (∑ p ∈ T, ((S \ T).filter (p < ·)).card) * occupiedMinor V (S \ T)
      else 0) :
    (orderedCut I W * (orderedCut I W).conjTranspose).charpoly =
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly := by
  classical
  let L := T.filter (· ∈ I)
  let R := T.filter (· ∉ I)
  let e := flipSpectators I L (fun _ h => (Finset.mem_filter.mp h).2)
  let f := flipSpectators Iᶜ R (fun _ h => (Finset.mem_filter.mp h).2)
  let ex (A : Finset ι) := ∑ p ∈ T, ((A \ T).filter (p < ·)).card
  have heq : orderedCut I W = fun a b => (-1 : ℂ) ^ ex a.val *
      ((-1 : ℂ) ^ ex b.val * orderedCut I V (e a) (f b)) := by
    ext a b : 1
    have hflip : (e a).val ∪ (f b).val = (a.val ∪ b.val) ∆ T := by
      ext q
      have ha := a.property (a := q)
      have hb := b.property (a := q)
      change q ∈ (a.val ∆ L) ∪ (b.val ∆ R) ↔ _
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      by_cases hq : q ∈ I
      · have hnb : q ∉ b.val := fun h => hb h hq
        simp [L, R, hq, hnb]
      · have hna : q ∉ a.val := fun h => hq (ha h)
        simp [L, R, hq, hna]
    rw [orderedCut_eq_minor, orderedCut_eq_minor, hflip]
    change D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.occupiedMinor W (a.val ∪ b.val) = _
    rw [hminor]
    by_cases hs : T ⊆ a.val ∪ b.val
    · rw [ite_eq_left hs]
      have hsdiff : (a.val ∪ b.val) ∆ T = (a.val ∪ b.val) \ T := by
        ext q
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        exact ⟨fun h => h.elim id (fun hh => (hh.2 (hs hh.1)).elim), Or.inl⟩
      rw [hsdiff]
      have hphase : ex (a.val ∪ b.val) = ex a.val + ex b.val := by
        change _ = ∑ p ∈ T, ((a.val \ T).filter (p < ·)).card +
          ∑ p ∈ T, ((b.val \ T).filter (p < ·)).card
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        have hsets : (((a.val ∪ b.val) \ T).filter (p < ·)) =
            ((a.val \ T).filter (p < ·)) ∪ ((b.val \ T).filter (p < ·)) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hsets, Finset.card_union_of_disjoint]
        apply (cut_disjoint a b).mono
        · exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
        · exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
      change (-1 : ℂ) ^ ex (a.val ∪ b.val) * occupiedMinor V ((a.val ∪ b.val) \ T) = _
      rw [hphase, pow_add, mul_assoc]
    · rw [ite_eq_right hs]
      obtain ⟨p, hp, hn⟩ := Finset.not_subset.mp hs
      have hmem : p ∈ (a.val ∪ b.val) ∆ T := Finset.mem_symmDiff.mpr (Or.inr ⟨hp, hn⟩)
      rw [minor_zero_of_occupied_zero_row V p (hT p hp) _ hmem, mul_zero, mul_zero]
  rw [heq]
  exact signed_reindexed_gram e f (orderedCut I V) (fun a => ex a.val) (fun b => ex b.val)

private theorem canonical_spectators_marginal [Fintype ι] {k : ℕ}
    (I : Set ι) (V : Matrix ι (Fin k) ℂ) (hV : V.conjTranspose * V = 1)
    (T : Finset ι) (hT : ∀ p ∈ T, ∀ j, V p j = 0) :
    ∃ W : Matrix ι (Fin (k + T.card)) ℂ, W.conjTranspose * W = 1 ∧
      (∀ i j, W i (Fin.castAdd T.card j) = V i j) ∧
      (∀ i j, W i (Fin.natAdd k j) = if i = T.orderEmbOfFin rfl j then 1 else 0) ∧
      (orderedCut I W * (orderedCut I W).conjTranspose).charpoly =
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly := by
  obtain ⟨W, ⟨hWl, hWr, hW, _, hminor⟩, _⟩ :=
    canonical_ordered_spectator_extension V hV T hT
  exact ⟨W, hW, hWl, hWr, spectator_marginal_of_minors I V W T hT hminor⟩

private theorem append_preserves_marginal_charpoly [Fintype ι] {k : ℕ}
    (I : Set ι) (V : Matrix ι (Fin k) ℂ) (p : ι) (hV : ∀ j, V p j = 0) :
    (orderedCut I (appendOrbital V p) * (orderedCut I (appendOrbital V p)).conjTranspose).charpoly =
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly := by
  apply spectator_marginal_of_minors I V (appendOrbital V p) {p}
  · intro q hq
    simpa only [Finset.mem_singleton.mp hq] using hV
  · intro S
    rw [occupiedMinor_append]
    by_cases hp : p ∈ S
    · have he : (S.erase p).filter (p < ·) = S.filter (p < ·) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨ne_of_gt h.2, h.1⟩, h.2⟩⟩
      simp [hp, Finset.sdiff_singleton_eq_erase, he]
    · simp [hp]

private def singleOccupation (I : Set ι) (i : I) : Occupation I :=
  ⟨{i.val}, fun _ h => (Finset.mem_singleton.mp h).symm ▸ i.property⟩

omit [LinearOrder ι] in
private theorem singleOccupation_injective (I : Set ι) :
    Function.Injective (singleOccupation I) := by
  intro i j h
  apply Subtype.ext
  exact Finset.singleton_injective (congrArg Subtype.val h)

private theorem occupiedMinor_singleton (V : Matrix ι (Fin 1) ℂ) (i : ι) :
    occupiedMinor V ({i} : Finset ι) = V i 0 := by
  unfold occupiedMinor
  rw [dite_eq_left (Finset.card_singleton i), Matrix.det_fin_one]
  simp [Matrix.submatrix_apply, Finset.orderEmbOfFin_singleton]

private theorem one_orbital_cut_column {I : Set ι}
    (V : Matrix ι (Fin 1) ℂ) (hV : ∀ i ∉ I, V i 0 = 0)
    (a : Occupation I) (b : Occupation Iᶜ) :
    orderedCut I V a b =
      if b.val = ∅ then occupiedMinor V a.val else 0 := by
  classical
  rw [orderedCut_eq_minor]
  by_cases hb : b.val = ∅
  · simp [hb]
  · rw [ite_eq_right hb]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    apply minor_zero_of_occupied_zero_row V i _ _ (Finset.mem_union_right _ hi)
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    exact hj ▸ hV i (b.property hi)

open Polynomial in
private theorem one_orbital_retained_charpoly [Fintype ι] {I : Set ι}
    (V : Matrix ι (Fin 1) ℂ) (hV : V.conjTranspose * V = 1)
    (hI : ∀ i ∉ I, V i 0 = 0) :
    (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
      X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  let v (a : Occupation I) : ℂ := occupiedMinor V a.val
  have hv (i : I) : v (singleOccupation I i) = V i.val 0 :=
    occupiedMinor_singleton V i.val
  have hfactor : (orderedCut I V * (orderedCut I V).conjTranspose) =
      Matrix.vecMulVec v (fun a => star (v a)) := by
    ext a a' : 1
    unfold Matrix.vecMulVec
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, one_orbital_cut_column V hI]
    change (∑ b : Occupation Iᶜ, (if b.val = ∅ then v a else 0) *
      star (if b.val = ∅ then v a' else 0)) = _
    let b₀ : Occupation Iᶜ := ⟨∅, by simp⟩
    have he (b : Occupation Iᶜ) : b.val = ∅ ↔ b = b₀ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp [he]
  have hnorm : (∑ a, v a * star (v a)) = 1 := by
    let e : I ↪ Occupation I := ⟨singleOccupation I, singleOccupation_injective I⟩
    have hsum : (∑ a : Occupation I, v a * star (v a)) =
        ∑ i : I, V i.val 0 * star (V i.val 0) := by
      classical
      calc
        _ = ∑ a ∈ (Finset.univ : Finset I).map e, v a * star (v a) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro a _ ha
          have hn : ¬ ∃ i, singleOccupation I i = a := by
            rintro ⟨i, rfl⟩
            exact ha (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
          have hsize : a.val.card ≠ 1 := by
            intro hc
            obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
            have hiI : i ∈ I := a.property (hi.symm ▸ Finset.mem_singleton_self i)
            exact hn ⟨⟨i, hiI⟩, Subtype.ext hi.symm⟩
          simp [v, occupiedMinor, hsize]
        _ = _ := by
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro i _
          change v (singleOccupation I i) * star (v (singleOccupation I i)) = _
          rw [hv]
    have hgram := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hV
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hgram
    rw [hsum, ← hgram]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset ι))
      (p := (· ∈ I))]
    have hz : (∑ i ∈ (Finset.univ : Finset ι).filter (· ∉ I),
        star (V i 0) * V i 0) = 0 := Finset.sum_eq_zero fun i hi => by
      simp [hI i (Finset.mem_filter.mp hi).2]
    rw [hz, add_zero]
    simpa [mul_comm] using
      (Finset.sum_subtype (s := (Finset.univ : Finset ι).filter (· ∈ I))
        (fun i => by simp) (fun i => star (V i 0) * V i 0))
  rw [hfactor, Matrix.charpoly_vecMulVec]
  change X ^ Fintype.card (Occupation I) -
    (∑ a, v a * star (v a)) • X ^ (Fintype.card (Occupation I) - 1) = _
  rw [hnorm, one_smul, mul_sub, mul_one, ← pow_succ]
  have : Nonempty (Occupation I) := ⟨⟨∅, by simp⟩⟩
  rw [Nat.sub_add_cancel Fintype.card_pos]

open Polynomial in
private theorem replace_discarded_orbital [Fintype ι] {I : Set ι}
    (V : Matrix ι (Fin 2) ℂ) (hV : V.conjTranspose * V = 1)
    (hretained : ∀ i ∉ I, V i 0 = 0) (hdiscarded : ∀ i ∈ I, V i 1 = 0)
    (p : ι) (hp : p ∉ I) :
    ∃ W : Matrix ι (Fin 2) ℂ,
      W.conjTranspose * W = 1 ∧ retainedRows I W = retainedRows I V ∧
      (∀ q, q ≠ p → (∀ j, V q j = 0) → ∀ j, W q j = 0) ∧
      (orderedCut I W * (orderedCut I W).conjTranspose).charpoly =
        X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  let U : Matrix ι (Fin 1) ℂ := fun i _ => V i 0
  have hU : U.conjTranspose * U = 1 := by
    ext i j : 1
    fin_cases i
    fin_cases j
    change (∑ j : ι, star (V j 0) * V j 0) = 1
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hV
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] using h
  have hp0 (j : Fin 1) : U p j = 0 := hretained p hp
  refine ⟨appendOrbital U p, append_gram U p hU hp0, ?_, ?_, ?_⟩
  · ext i j : 1
    have hi : i.val ≠ p := fun he => hp (he ▸ i.property)
    fin_cases j
    · change appendOrbital U p i.val (Fin.castSucc (0 : Fin 1)) = V i.val 0
      simp [appendOrbital, U]
    · change appendOrbital U p i.val (Fin.last 1) = V i.val 1
      rw [show appendOrbital U p i.val (Fin.last 1) =
        (if i.val = p then 1 else 0) from Fin.snoc_last _ _,
        ite_eq_right hi, hdiscarded i.val i.property]
  · intro q hqp hq j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · simp [appendOrbital, U, hq]
    · rw [show appendOrbital U p q (Fin.last 1) =
        (if q = p then 1 else 0) from Fin.snoc_last _ _, ite_eq_right hqp]
  · rw [append_preserves_marginal_charpoly I U p hp0]
    exact one_orbital_retained_charpoly U hU hretained

private theorem coordinate_columns_gram {ι : Type*} [LinearOrder ι] (T : Finset ι)
    (i j : ι) :
    (∑ a : Fin T.card, (if i = T.orderEmbOfFin rfl a then (1 : ℂ) else 0) *
      star (if j = T.orderEmbOfFin rfl a then (1 : ℂ) else 0)) =
      if i = j ∧ i ∈ T then 1 else 0 := by
  classical
  by_cases hi : i ∈ T
  · let a := (T.orderIsoOfFin rfl).symm ⟨i, hi⟩
    have ha : T.orderEmbOfFin rfl a = i :=
      congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
    rw [Finset.sum_eq_single a]
    · simp [ha, hi, eq_comm]
    · intro b _ hb
      have hb' : i ≠ T.orderEmbOfFin rfl b := fun he =>
        hb ((T.orderEmbOfFin rfl).injective (he.symm.trans ha.symm))
      simp [hb']
    · simp
  · have hz (a : Fin T.card) : i ≠ T.orderEmbOfFin rfl a := fun he =>
      hi (he ▸ T.orderEmbOfFin_mem rfl a)
    simp [hz, hi]

theorem retention_compression_of_canonical_columns {ι : Type*} [LinearOrder ι] {k : ℕ}
    (T : Finset ι) (I : Set ι) (V : Matrix ι (Fin k) ℂ) (W : Matrix ι (Fin (k + T.card)) ℂ)
    (hl : ∀ i j, W i (Fin.castAdd T.card j) = V i j)
    (hr : ∀ i j, W i (Fin.natAdd k j) = if i = T.orderEmbOfFin rfl j then 1 else 0) :
    retainedRows I W * (retainedRows I W)ᴴ =
      retainedRows I V * (retainedRows I V)ᴴ +
        Matrix.diagonal (fun i : I => if i.val ∈ T then (1 : ℂ) else 0) := by
  classical
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, retainedRows,
    Matrix.submatrix_apply, id_eq, Fin.sum_univ_add, hl, hr]
  rw [coordinate_columns_gram T i.val j.val]
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => h (Subtype.ext he)
    simp [h, hv]

open Polynomial in
private theorem extend_with_compression_twins [Fintype ι] {I : Set ι}
    (V : Matrix ι (Fin 2) ℂ) (hV : V.conjTranspose * V = 1)
    (hretained : ∀ i ∉ I, V i 0 = 0) (hdiscarded : ∀ i ∈ I, V i 1 = 0)
    (p : ι) (hp : p ∉ I) (T : Finset ι) (hpT : p ∉ T)
    (hT : ∀ q ∈ T, ∀ j, V q j = 0) :
    ∃ V' W' : Matrix ι (Fin (2 + T.card)) ℂ,
      V'.conjTranspose * V' = 1 ∧ W'.conjTranspose * W' = 1 ∧
      retainedRows I V' * (retainedRows I V').conjTranspose =
        retainedRows I W' * (retainedRows I W').conjTranspose ∧
      (orderedCut I V' * (orderedCut I V').conjTranspose).charpoly =
        (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ∧
      (orderedCut I W' * (orderedCut I W').conjTranspose).charpoly =
        X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  obtain ⟨W, hW, hrows, hzeros, hpoly⟩ :=
    replace_discarded_orbital V hV hretained hdiscarded p hp
  have hWT (q : ι) (hq : q ∈ T) : ∀ j, W q j = 0 :=
    hzeros q (fun he => hpT (he ▸ hq)) (hT q hq)
  obtain ⟨V', hV', hVl, hVr, hv'⟩ := canonical_spectators_marginal I V hV T hT
  obtain ⟨W', hW', hWl, hWr, hw'⟩ := canonical_spectators_marginal I W hW T hWT
  refine ⟨V', W', hV', hW', ?_, hv', hw'.trans hpoly⟩
  rw [retention_compression_of_canonical_columns T I V V' hVl hVr,
    retention_compression_of_canonical_columns T I W W' hWl hWr, hrows]

open Polynomial in
theorem alternating_fixed_filling_compression_twins [Fintype ι] {I : Set ι}
    (h : Alternates I) {k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ Fintype.card ι - 2) :
    ∃ V W : Matrix ι (Fin k) ℂ,
      V.conjTranspose * V = 1 ∧ W.conjTranspose * W = 1 ∧
      retainedRows I V * (retainedRows I V).conjTranspose =
        retainedRows I W * (retainedRows I W).conjTranspose ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        X ^ (Fintype.card (Occupation I) - 2) * (X - C ((1 : ℂ) / 2)) ^ 2 ∧
      (orderedCut I W * (orderedCut I W).conjTranspose).charpoly =
        X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  obtain ⟨A, p, U, hA, hpA, hp, hU, hleft, hright, hzero, _, _, hpoly⟩ :=
    alternating_cut_supported_obstruction h
  have hrest : (Finset.univ \ A).card = Fintype.card ι - 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA, Finset.card_univ]
  obtain ⟨T, hT, hTc⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ \ A) (n := k - 2) (by omega)
  have hpT : p ∉ T := fun h => (Finset.mem_sdiff.mp (hT h)).2 hpA
  have hUT (q : ι) (hq : q ∈ T) : ∀ j, U q j = 0 :=
    hzero q (Finset.mem_sdiff.mp (hT hq)).2
  have htotal : 2 + T.card = k := by omega
  obtain ⟨V, W, hV, hW, heq, hVpoly, hWpoly⟩ :=
    extend_with_compression_twins U hU hleft hright p hp T hpT hUT
  rw [← htotal]
  exact ⟨V, W, hV, hW, heq, hVpoly.trans hpoly, hWpoly⟩

private theorem normalized_sign_mul {n : ℕ} {l r : ℤ}
    (h : (-1 : ℤ) ^ n = l * r) :
    (-1 : ℂ) ^ n =
      (-1) ^ (if l = -1 then (1 : ℕ) else 0) * (-1) ^ (if r = -1 then (1 : ℕ) else 0) := by
  have hc : (-1 : ℂ) ^ n = (l : ℂ) * (r : ℂ) := by exact_mod_cast h
  rw [hc]
  rcases neg_one_pow_eq_or ℤ n with hpos | hneg
  · rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp (h.symm.trans hpos) with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr]
  · rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp (h.symm.trans hneg) with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr]

private theorem spectra_of_separate_fixed_filling_signs [Fintype ι] {k : ℕ}
    (I : Set ι) (V : Matrix ι (Fin k) ℂ) (L R : Finset ι)
    (hL : ∀ i, i ∈ L ↔ i ∈ I) (hR : ∀ i, i ∈ R ↔ i ∈ Iᶜ)
    (h : Factors L R k) :
    (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly := by
  classical
  obtain ⟨l, r, hsign⟩ := h
  let lin (a : Occupation I) : ℕ := if l a.val = -1 then 1 else 0
  let rin (b : Occupation Iᶜ) : ℕ := if r b.val = -1 then 1 else 0
  have hphase : groupedCut I V = fun a b =>
      (-1 : ℂ) ^ lin a * ((-1 : ℂ) ^ rin b * orderedCut I V a b) := by
    ext a b : 1
    rw [groupedCut_eq_signed]
    by_cases hsize : a.val.card + b.val.card = k
    · rw [normalized_sign_mul (hsign a.val b.val
        (fun i hi => (hL i).mpr (a.property hi))
        (fun i hi => (hR i).mpr (b.property hi)) hsize)]
      exact mul_assoc _ _ _
    · simp [orderedCut_eq_zero_of_card_ne V a b hsize]
  rw [hphase]
  exact signed_reindexed_gram (Equiv.refl _) (Equiv.refl _) (orderedCut I V) lin rin

private theorem extreme_filling_product
    (hprefix : ∀ m n k : ℕ, ∀ W : Matrix (Fin (m + n)) (Fin k) ℂ,
      W.conjTranspose * W = 1 → HasProductSpectrum {i | i.val < m} W)
    {k : ℕ} [Fintype ι] (I : Set ι) (V : Matrix ι (Fin k) ℂ)
    (hV : V.conjTranspose * V = 1) (hk : k ≤ 1 ∨ Fintype.card ι ≤ k + 1) :
    HasProductSpectrum I V := by
  classical
  let L : Finset ι := Finset.univ.filter (· ∈ I)
  let R : Finset ι := Finset.univ.filter (· ∉ I)
  have hLR : L.card + R.card = Fintype.card ι := by
    rw [← Finset.card_union_of_disjoint
      (show Disjoint L R from Finset.disjoint_left.mpr fun i hl hr =>
        (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hl).2)]
    congr 1
    apply Finset.eq_univ_of_forall
    intro i
    by_cases hi : i ∈ I <;> simp [L, R, hi]
  have hFactors := factors_of_extreme_filling L R k (by rw [hLR]; exact hk)
  have hEq := spectra_of_separate_fixed_filling_signs I V L R
    (fun i => by simp [L]) (fun i => by simp [R]) hFactors
  intro ν hν
  exact hEq.symm.trans (grouped_product_from_prefix hprefix I V hV ν hν)


theorem fixed_filling_spectral_criteria [Fintype ι] (I : Set ι) (k : ℕ) :
    let good := k ≤ 1 ∨ Fintype.card ι ≤ k + 1 ∨ ¬ Alternates I
    (good ↔ ∀ V : Matrix ι (Fin k) ℂ, V.conjTranspose * V = 1 → HasProductSpectrum I V) ∧
    (good ↔ ∀ V W : Matrix ι (Fin k) ℂ,
      V.conjTranspose * V = 1 → W.conjTranspose * W = 1 →
      retainedRows I V * (retainedRows I V).conjTranspose =
        retainedRows I W * (retainedRows I W).conjTranspose →
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        (orderedCut I W * (orderedCut I W).conjTranspose).charpoly) := by
  classical
  intro good
  let hprefix := OrderedSlaterPrefix.prefix_product_spectrum
  have hpos (hg : good) (V : Matrix ι (Fin k) ℂ) (hV : V.conjTranspose * V = 1) :
      HasProductSpectrum I V := by
    rcases hg with h | h | h
    · exact extreme_filling_product hprefix I V hV (Or.inl h)
    · exact extreme_filling_product hprefix I V hV (Or.inr h)
    · exact (universal_cut_product_iff_of_prefix hprefix I).mp h k V hV
  have heq_of_product (V W : Matrix ι (Fin k) ℂ)
      (hV : HasProductSpectrum I V) (hW : HasProductSpectrum I W)
      (heq : retainedRows I V * (retainedRows I V).conjTranspose =
        retainedRows I W * (retainedRows I W).conjTranspose) :
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        (orderedCut I W * (orderedCut I W).conjTranspose).charpoly := by
    let Q := retainedRows I V
    let hQ : (Q * Q.conjTranspose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self Q
    let ν : I → ℂ := fun i => (hQ.eigenvalues i : ℂ)
    have hν : (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
        (∏ i : I, (Polynomial.X - Polynomial.C (ν i))) := by
      change (Q * Q.conjTranspose).charpoly = _
      rw [hQ.charpoly_eq]
      rfl
    have hνW := heq ▸ hν
    exact (hV ν hν).trans (hW ν hνW).symm
  have hneg (hg : ¬ good) :
      ∃ V W : Matrix ι (Fin k) ℂ, V.conjTranspose * V = 1 ∧ W.conjTranspose * W = 1 ∧
      retainedRows I V * (retainedRows I V).conjTranspose =
        retainedRows I W * (retainedRows I W).conjTranspose ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ≠
        (orderedCut I W * (orderedCut I W).conjTranspose).charpoly := by
    have hk : 2 ≤ k := by
      have h := fun h : k ≤ 1 => hg (Or.inl h)
      omega
    have hk' : k ≤ Fintype.card ι - 2 := by
      have h := fun h : Fintype.card ι ≤ k + 1 => hg (Or.inr (Or.inl h))
      omega
    have hI : Alternates I := by
      by_contra h
      exact hg (Or.inr (Or.inr h))
    obtain ⟨V, W, hV, hW, heq, hVpoly, hWpoly⟩ :=
      alternating_fixed_filling_compression_twins hI hk hk'
    refine ⟨V, W, hV, hW, heq, ?_⟩
    rw [hVpoly, hWpoly]
    intro h
    have hc := congrArg (Polynomial.eval (1 : ℂ)) h
    simp at hc
    norm_num at hc
  constructor
  · refine ⟨hpos, ?_⟩
    intro h
    by_contra hg
    obtain ⟨V, W, hV, hW, heq, hne⟩ := hneg hg
    exact hne (heq_of_product V W (h V hV) (h W hW) heq)
  · constructor
    · intro hg V W hV hW heq
      exact heq_of_product V W (hpos hg V hV) (hpos hg W hW) heq
    · intro h
      by_contra hg
      obtain ⟨V, W, hV, hW, heq, hne⟩ := hneg hg
      exact hne (h V W hV hW heq)

open Polynomial in
theorem spectator_projector_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (v : ι → ℂ) (hn : ∑ i, v i * star (v i) = 1)
    (hzero : ∀ i ∈ T, v i = 0) :
    (Matrix.vecMulVec v (fun i => star (v i)) +
      Matrix.diagonal (fun i => if i ∈ T then (1 : ℂ) else 0)).charpoly =
        X ^ (Fintype.card ι - T.card - 1) * (X - 1) ^ (T.card + 1) := by
  classical
  let A := {i // i ∈ T}
  let B := {i // i ∉ T}
  let e : A ⊕ B ≃ ι := Equiv.sumCompl (· ∈ T)
  let u : B → ℂ := fun i => v i.val
  let w : B → ℂ := fun i => star (u i)
  let P := Matrix.vecMulVec v (fun i => star (v i)) +
      Matrix.diagonal (fun i => if i ∈ T then (1 : ℂ) else 0)
  have heL (a : A) : e (Sum.inl a) = a.val := rfl
  have heR (b : B) : e (Sum.inr b) = b.val := rfl
  have hblock : Matrix.reindex e.symm e.symm P =
      Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.vecMulVec u w) := by
    ext a b : 1
    change P (e a) (e b) = _
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have ha := hzero a.val a.property
        have hb := hzero b.val b.property
        by_cases h : a.val = b.val
        · have h' : a = b := Subtype.ext h
          subst b
          simp [P, Matrix.vecMulVec, heL, ha, a.property]
        · have h' : a ≠ b := fun e => h (congrArg Subtype.val e)
          simp [P, Matrix.vecMulVec, heL, ha, h, h']
      | inr b =>
        have ha := hzero a.val a.property
        have h : a.val ≠ b.val := fun h => b.property (h ▸ a.property)
        simp [P, Matrix.vecMulVec, heL, heR, ha, h]
    | inr a =>
      cases b with
      | inl b =>
        have hb := hzero b.val b.property
        have h : a.val ≠ b.val := fun h => a.property (h.symm ▸ b.property)
        simp [P, Matrix.vecMulVec, heL, heR, hb, h]
      | inr b =>
        simp [P, Matrix.vecMulVec, heR, u, w, Matrix.diagonal_apply, a.property]
  have hsum : ∑ i : B, u i * w i = 1 := by
    have hs : (∑ i : A ⊕ B, v (e i) * star (v (e i))) = ∑ i : ι, v i * star (v i) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [Fintype.sum_sum_type] at hs
    simpa [heL, heR, u, w, hzero] using hs.trans hn
  have hcard : Fintype.card B = Fintype.card ι - T.card := by
    have hsize := Fintype.card_congr e
    simp only [Fintype.card_sum] at hsize
    have ha : Fintype.card A = T.card := Fintype.card_coe T
    omega
  have hB : Nonempty B := by
    by_contra h
    let : IsEmpty B := not_nonempty_iff.mp h
    simp at hsum
  change P.charpoly = _
  rw [← Matrix.charpoly_reindex e.symm P, hblock, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_one, Matrix.charpoly_vecMulVec]
  change (X - 1) ^ Fintype.card A *
    (X ^ Fintype.card B - (∑ i : B, u i * w i) • X ^ (Fintype.card B - 1)) = _
  rw [hsum, one_smul]
  have hd : Fintype.card B = Fintype.card B - 1 + 1 := by
    have := hB
    exact (Nat.sub_add_cancel Fintype.card_pos).symm
  nth_rw 1 [hd]
  rw [pow_succ, ← mul_sub_one]
  have hA : Fintype.card A = T.card := Fintype.card_coe T
  rw [hA, hcard, pow_succ]
  ac_rfl

end D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling
