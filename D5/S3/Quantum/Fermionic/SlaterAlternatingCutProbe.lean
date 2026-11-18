import D5.S3.Quantum.Fermionic.SlaterCutPhase
import D5.S3.Quantum.Fermionic.SlaterShuffleSignProbe
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The two opposite four-site obstructions on the active occupation rows. -/

open D5.S3.Quantum.Fermionic.SlaterCutPhase

namespace SlaterAlternatingCutProbe

open scoped BigOperators

noncomputable def orbitalEntry {ι : Type*} [DecidableEq ι] (sites : Finset ι) (i : ι) : ℂ :=
  if i ∈ sites then ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) else 0

noncomputable def pairedOrbitals {ι : Type*} [DecidableEq ι] (a b : Finset ι) :
    Matrix ι (Fin 2) ℂ :=
  fun i j => orbitalEntry (if j = 0 then a else b) i

private theorem halfRoot_mul :
    ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) * ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) =
      (1 : ℂ) / 2 := by
  have hp := Real.sq_sqrt (show 0 ≤ (1 : ℝ) / 2 by positivity)
  rw [pow_two] at hp
  rw [← Complex.ofReal_mul, hp, Complex.ofReal_div, Complex.ofReal_one]
  norm_num

private theorem orbital_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) :
    (∑ i, star (orbitalEntry s i) * orbitalEntry t i) =
      ((s ∩ t).card : ℂ) / 2 := by
  calc
    _ = ∑ i, if i ∈ s ∩ t then (1 : ℂ) / 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hstar : star ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) =
          ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) := by simp
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
        simp only [orbitalEntry, hs, ht, Finset.mem_inter, ite_true, ite_false, true_and,
          false_and, and_false, star_zero, zero_mul, mul_zero, hstar, halfRoot_mul]
    _ = _ := by
      rw [Fintype.sum_ite_mem]
      simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Two disjoint two-site supports give orthonormal columns over the entire site type. -/
theorem paired_orbitals_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι) (ha : a.card = 2) (hb : b.card = 2) (h : Disjoint a b) :
    (pairedOrbitals a b).conjTranspose * pairedOrbitals a b = 1 := by
  have hab : a ∩ b = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h
  have hba : b ∩ a = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h.symm
  ext i j
  change (∑ l, star (orbitalEntry (if i = 0 then a else b) l) *
    orbitalEntry (if j = 0 then a else b) l) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [orbital_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, ha, hb, hab, hba]

noncomputable def grouped : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1 / 2

noncomputable def signed {ι : Type*} [LinearOrder ι]
    (a b : Fin 2 → ι) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (-1 : ℂ) ^ crossCount {a i} {b j} * grouped i j

private theorem grouped_det : grouped.det = 0 := by
  rw [Matrix.det_fin_two]
  simp [grouped]

private theorem groupedGram_charpoly :
    (grouped * grouped.conjTranspose).charpoly =
      Polynomial.X * (Polynomial.X - 1) := by
  have ht : (grouped * grouped.conjTranspose).trace = 1 := by
    rw [Matrix.trace_fin_two]
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, grouped]
  rw [Matrix.charpoly_fin_two, Matrix.det_mul, grouped_det, zero_mul, ht]
  simp [pow_two, mul_sub]

private theorem gram_distinct {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.det ≠ 0) (hB : B.det = 0) :
    (A * A.conjTranspose).charpoly ≠ (B * B.conjTranspose).charpoly := by
  intro heq
  have hd : (A * A.conjTranspose).det = (B * B.conjTranspose).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, heq]
  rw [Matrix.det_mul, Matrix.det_mul, hB, zero_mul, Matrix.det_conjTranspose] at hd
  exact (mul_ne_zero hA (by simpa using hA)) hd

private def embedMatrix {ι κ : Type*} [DecidableEq ι] (e : κ ↪ ι) : Matrix ι κ ℂ :=
  fun i j => if i = e j then 1 else 0

private theorem embed_adjoint_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (e : κ ↪ ι) :
    (embedMatrix e).conjTranspose * embedMatrix e = 1 := by
  classical
  ext i j
  change (∑ k, star (if k = e i then (1 : ℂ) else 0) *
      (if k = e j then 1 else 0)) = (1 : Matrix κ κ ℂ) i j
  calc
    _ = ∑ k, if k = e i then (if i = j then (1 : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = e i
      · subst k
        simp [e.injective.eq_iff]
      · simp [h]
    _ = _ := by simp [Matrix.one_apply]

private theorem paddedGram_charpoly {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq α]
    (e : α ↪ ι) (f : β ↪ κ) (B : Matrix α β ℂ) :
    let padded := embedMatrix e * B * (embedMatrix f).conjTranspose
    (padded * padded.conjTranspose).charpoly =
      Polynomial.X ^ (Fintype.card ι - Fintype.card α) * (B * B.conjTranspose).charpoly := by
  classical
  intro padded
  let E := embedMatrix e
  let F := embedMatrix f
  have hE : E.conjTranspose * E = 1 := embed_adjoint_mul e
  have hF : F.conjTranspose * F = 1 := embed_adjoint_mul f
  have hm : padded * padded.conjTranspose = E * ((B * B.conjTranspose) * E.conjTranspose) := by
    change (E * B * F.conjTranspose) * (E * B * F.conjTranspose).conjTranspose = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc (E * B), ← Matrix.mul_assoc F.conjTranspose, hF, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  rw [hm, Matrix.charpoly_mul_comm_of_le E _ (Fintype.card_le_of_injective e e.injective)]
  rw [Matrix.mul_assoc (B * B.conjTranspose) E.conjTranspose E, hE, Matrix.mul_one]

/-- In a nonzero determinant, each occupied site lies in one of the two orbital supports. -/
theorem grouped_nonzero_supported {ι : Type*} [LinearOrder ι]
    (s t a b : Finset ι) (hd : Disjoint a b)
    (hne : SlaterShuffleSignProbe.groupedAmplitude (pairedOrbitals s t) a b hd ≠ 0) :
    a ∪ b ⊆ s ∪ t := by
  intro x hx
  by_contra hxt
  apply hne
  by_cases h : a.card + b.card = 2
  · rw [SlaterShuffleSignProbe.groupedAmplitude, dite_eq_left h]
    let i := (SlaterShuffleSignProbe.groupedRows a b hd).symm
      ⟨x, Finset.mem_disjUnion.mpr (Finset.mem_union.mp hx)⟩
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.cast h i)
    intro j
    have hsite : (SlaterShuffleSignProbe.groupedRows a b hd i : ι) = x := by
      simp [i]
    change pairedOrbitals s t
      (SlaterShuffleSignProbe.groupedRows a b hd (Fin.cast h.symm (Fin.cast h i))) j = 0
    rw [Fin.cast_cast, Fin.cast_eq_self, hsite]
    have hs : x ∉ s := fun hm => hxt (Finset.mem_union_left _ hm)
    have ht : x ∉ t := fun hm => hxt (Finset.mem_union_right _ hm)
    by_cases hj : j = 0 <;> simp [pairedOrbitals, orbitalEntry, hj, hs, ht]
  · simp [SlaterShuffleSignProbe.groupedAmplitude, h]

/-- If the orbital supports lie on opposite sides, a nonzero entry has one particle
on each side and each particle lies in the corresponding support. -/
theorem grouped_nonzero_singletons {ι : Type*} [LinearOrder ι] {I : Set ι}
    (s t a b : Finset ι) (hd : Disjoint a b)
    (hs : (↑s : Set ι) ⊆ I) (ht : (↑t : Set ι) ⊆ Iᶜ)
    (ha : (↑a : Set ι) ⊆ I) (hb : (↑b : Set ι) ⊆ Iᶜ)
    (hne : SlaterShuffleSignProbe.groupedAmplitude (pairedOrbitals s t) a b hd ≠ 0) :
    ∃ x ∈ s, ∃ y ∈ t, a = {x} ∧ b = {y} := by
  classical
  have hsupp := grouped_nonzero_supported s t a b hd hne
  have hsa : a ⊆ s := by
    intro x hx
    rcases Finset.mem_union.mp (hsupp (Finset.mem_union_left b hx)) with hx' | hx'
    · exact hx'
    · exact False.elim (ht hx' (ha hx))
  have htb : b ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp (hsupp (Finset.mem_union_right a hx)) with hx' | hx'
    · exact False.elim (hb hx (hs hx'))
    · exact hx'
  have hc : a.card + b.card = 2 := by
    by_contra hh
    exact hne (by simp [SlaterShuffleSignProbe.groupedAmplitude, hh])
  have hz (c : Fin 2) (hzero : ∀ x ∈ a ∪ b, pairedOrbitals s t x c = 0) : False := by
    apply hne
    rw [SlaterShuffleSignProbe.groupedAmplitude, dite_eq_left hc]
    apply Matrix.det_eq_zero_of_column_eq_zero c
    intro i
    let row := SlaterShuffleSignProbe.groupedRows a b hd (Fin.cast hc.symm i)
    exact hzero row (by simpa only [Finset.mem_disjUnion, Finset.mem_union] using row.2)
  have hapos : 0 < a.card := by
    by_contra! hh
    have he : a = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    apply hz 0
    intro x hx
    have hxb : x ∈ b := by simpa [he] using hx
    have hxs : x ∉ s := fun hm => hb hxb (hs hm)
    simp [pairedOrbitals, orbitalEntry, hxs]
  have hbpos : 0 < b.card := by
    by_contra! hh
    have he : b = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    apply hz 1
    intro x hx
    have hxa : x ∈ a := by simpa [he] using hx
    have hxt : x ∉ t := fun hm => ht hm (ha hxa)
    norm_num [pairedOrbitals, orbitalEntry, hxt]
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show a.card = 1 by omega)
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (show b.card = 1 by omega)
  exact ⟨x, hsa (Finset.mem_singleton_self x), y, htb (Finset.mem_singleton_self y), rfl, rfl⟩

private theorem grouped_singletons {ι : Type*} [LinearOrder ι] (V : Matrix ι (Fin 2) ℂ)
    (x y : ι) (hd : Disjoint ({x} : Finset ι) {y}) :
    SlaterShuffleSignProbe.groupedAmplitude V {x} {y} hd =
      V x 0 * V y 1 - V x 1 * V y 0 := by
  let a : Finset ι := {x}
  let b : Finset ι := {y}
  have hc : a.card + b.card = 2 := by simp [a, b]
  let left : Fin a.card := ⟨0, by simp [a]⟩
  let right : Fin b.card := ⟨0, by simp [b]⟩
  have h0 : Fin.cast hc.symm (0 : Fin 2) = Fin.castAdd b.card left := by
    apply Fin.ext
    rfl
  have h1 : Fin.cast hc.symm (1 : Fin 2) = Fin.natAdd a.card right := by
    apply Fin.ext
    simp [a, right]
  have hrow0 : (SlaterShuffleSignProbe.groupedRows a b hd
      (Fin.cast hc.symm (0 : Fin 2)) : ι) = x := by
    rw [h0]
    have hm : ((a.orderIsoOfFin rfl left : a) : ι) = x :=
      Finset.mem_singleton.mp (a.orderIsoOfFin rfl left).2
    simpa [SlaterShuffleSignProbe.groupedRows] using hm
  have hrow1 : (SlaterShuffleSignProbe.groupedRows a b hd
      (Fin.cast hc.symm (1 : Fin 2)) : ι) = y := by
    rw [h1]
    have hm : ((b.orderIsoOfFin rfl right : b) : ι) = y :=
      Finset.mem_singleton.mp (b.orderIsoOfFin rfl right).2
    simpa [SlaterShuffleSignProbe.groupedRows] using hm
  change SlaterShuffleSignProbe.groupedAmplitude V a b hd = _
  rw [SlaterShuffleSignProbe.groupedAmplitude, dite_eq_left hc, Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, id_eq, hrow0, hrow1]

private theorem grouped_singleton_orbitals {ι : Type*} [LinearOrder ι]
    {s t : Finset ι} {x y : ι} (hdisj : Disjoint s t) (hx : x ∈ s) (hy : y ∈ t)
    (hd : Disjoint ({x} : Finset ι) {y}) :
    SlaterShuffleSignProbe.groupedAmplitude (pairedOrbitals s t) {x} {y} hd = (1 : ℂ) / 2 := by
  have hxt : x ∉ t := fun hm => Finset.disjoint_left.mp hdisj hx hm
  have hys : y ∉ s := fun hm => Finset.disjoint_left.mp hdisj hm hy
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [grouped_singletons]
  simp only [pairedOrbitals, orbitalEntry, hx, hy, hxt, hys, ite_true, ite_false,
    zero_mul, sub_zero, h10, halfRoot_mul]

private theorem eq_padding {ι κ α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ]
    (e : α ↪ ι) (f : β ↪ κ) (M : Matrix ι κ ℂ) (A : Matrix α β ℂ)
    (active : ∀ i j, M (e i) (f j) = A i j)
    (row : ∀ i j, (¬ ∃ a, e a = i) → M i j = 0)
    (column : ∀ i j, (¬ ∃ b, f b = j) → M i j = 0) :
    M = embedMatrix e * A * (embedMatrix f).conjTranspose := by
  classical
  ext i j
  by_cases hrow : ∃ a, e a = i
  · obtain ⟨a, rfl⟩ := hrow
    by_cases hcol : ∃ b, f b = j
    · obtain ⟨b, rfl⟩ := hcol
      rw [active]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedMatrix, e.injective.eq_iff,
        f.injective.eq_iff]
    · rw [column _ _ hcol]
      have hne (b : β) : j ≠ f b := fun h => hcol ⟨b, h.symm⟩
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedMatrix, hne]
  · rw [row _ _ hrow]
    have hne (a : α) : i ≠ e a := fun h => hrow ⟨a, h.symm⟩
    simp [Matrix.mul_apply, embedMatrix, hne]

abbrev Occupation {ι : Type*} (I : Set ι) :=
  {a : Finset ι // (↑a : Set ι) ⊆ I}

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype (Occupation I) :=
  Fintype.ofFinite _

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype I :=
  Fintype.ofFinite _

def retainedRows {ι : Type*} (I : Set ι) {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    Matrix I (Fin k) ℂ := V.submatrix Subtype.val id

private def occupySingle {ι : Type*} [DecidableEq ι] {I : Set ι}
    (v : Fin 2 ↪ ι) (hv : ∀ i, v i ∈ I) : Fin 2 ↪ Occupation I where
  toFun i := ⟨{v i}, by simpa using hv i⟩
  inj' := by
    intro i j hij
    apply v.injective
    exact Finset.singleton_injective (congrArg Subtype.val hij)

private theorem cut_disjoint {ι : Type*} {I : Set ι} (a : Occupation I) (b : Occupation Iᶜ) :
    Disjoint a.1 b.1 :=
  Finset.disjoint_left.mpr fun _ ha hb => b.2 hb (a.2 ha)

noncomputable def orderedCut {ι : Type*} [LinearOrder ι] (I : Set ι) {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) : Matrix (Occupation I) (Occupation Iᶜ) ℂ :=
  fun a b => SlaterShuffleSignProbe.orderedAmplitude V a.1 b.1 (cut_disjoint a b)

noncomputable def groupedCut {ι : Type*} [LinearOrder ι] (I : Set ι) {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) : Matrix (Occupation I) (Occupation Iᶜ) ℂ :=
  fun a b => SlaterShuffleSignProbe.groupedAmplitude V a.1 b.1 (cut_disjoint a b)

private theorem orderedCut_apply {ι : Type*} [LinearOrder ι] {I : Set ι} {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) (a : Occupation I) (b : Occupation Iᶜ) :
    orderedCut I V a b = (-1 : ℂ) ^ crossCount a.1 b.1 * groupedCut I V a b := by
  rw [groupedCut, SlaterShuffleSignProbe.grouped_amplitude_eq_signed]
  change _ = _ * (_ * orderedCut I V a b)
  rw [← mul_assoc, ← mul_pow]
  simp

private theorem compression_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (v w : Fin 2 ↪ ι) (hv : ∀ i, v i ∈ I) (hw : ∀ i, w i ∈ Iᶜ) :
    let X := retainedRows I (pairedOrbitals (Finset.univ.image v) (Finset.univ.image w))
    (X * X.conjTranspose).charpoly =
      Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) := by
  classical
  intro X
  let vi : Fin 2 ↪ I := ⟨fun i => ⟨v i, hv i⟩, fun _ _ hij =>
    v.injective (congrArg Subtype.val hij)⟩
  let r : ℂ := ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ)
  have hstar : star r = r := by simp [r]
  let u : Matrix (Fin 2) Unit ℂ := fun _ _ => r
  let E := embedMatrix vi
  let L := E * u
  have first (i : I) : X i 0 = L i () := by
    change orbitalEntry (Finset.univ.image v) i.1 = (embedMatrix vi * u) i ()
    by_cases hi : ∃ j, v j = i.1
    · obtain ⟨j, hj⟩ := hi
      have hvij : vi j = i := Subtype.ext hj
      have hm : i.1 ∈ Finset.univ.image v := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
      rw [← hvij] at hm ⊢
      rw [Matrix.mul_apply]
      change orbitalEntry (Finset.univ.image v) (vi j).1 =
        ∑ l : Fin 2, (if vi j = vi l then (1 : ℂ) else 0) * r
      simp [orbitalEntry, hm, vi.injective.eq_iff, r]
    · have hm : i.1 ∉ Finset.univ.image v := fun h => by
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
        exact hi ⟨j, hj⟩
      have hne (j : Fin 2) : i ≠ vi j := fun h => hi ⟨j, (congrArg Subtype.val h).symm⟩
      simp [Matrix.mul_apply, embedMatrix, orbitalEntry, hm, hne]
  have second (i : I) : X i 1 = 0 := by
    have hm : i.1 ∉ Finset.univ.image w := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact hw j (hj.symm ▸ i.2)
    norm_num [X, retainedRows, pairedOrbitals, orbitalEntry, hm]
  have hGram : X * X.conjTranspose = L * L.conjTranspose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, first, second]
  have hu : u.conjTranspose * u = (1 : Matrix Unit Unit ℂ) := by
    ext i j
    change (∑ l : Fin 2, star r * r) = (1 : Matrix Unit Unit ℂ) i j
    rw [hstar, show r * r = (1 : ℂ) / 2 from halfRoot_mul]
    norm_num [Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]
  have hinner : L.conjTranspose * L = 1 := by
    change (E * u).conjTranspose * (E * u) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc u.conjTranspose,
      ← Matrix.mul_assoc E.conjTranspose,
      show E.conjTranspose * E = 1 from embed_adjoint_mul vi, Matrix.one_mul, hu]
  have hcard := Fintype.card_le_of_injective vi vi.injective
  simp only [Fintype.card_fin] at hcard
  have hle : Fintype.card Unit ≤ Fintype.card I := by
    simpa using le_trans (by decide : 1 ≤ 2) hcard
  rw [hGram, Matrix.charpoly_mul_comm_of_le L L.conjTranspose hle, hinner, Matrix.charpoly_one]
  simp

private theorem orthonormal_cut_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (v w : Fin 2 ↪ ι)
    (hv : ∀ i, v i ∈ I) (hw : ∀ i, w i ∈ Iᶜ)
    (hminor : (signed v w * (signed v w).conjTranspose).charpoly ≠
      (grouped * grouped.conjTranspose).charpoly) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ((retainedRows I V) * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ≠
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly := by
  classical
  let s := Finset.univ.image v
  let t := Finset.univ.image w
  have hs : (↑s : Set ι) ⊆ I := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hv j
  have ht : (↑t : Set ι) ⊆ Iᶜ := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hw j
  have hst : Disjoint s t := Finset.disjoint_left.mpr fun _ hi hj => ht hj (hs hi)
  have hsc : s.card = 2 := by simp [s, Finset.card_image_of_injective _ v.injective]
  have htc : t.card = 2 := by simp [t, Finset.card_image_of_injective _ w.injective]
  let V := pairedOrbitals s t
  let e := occupySingle v hv
  let f := occupySingle w hw
  have hsupport (a : Occupation I) (b : Occupation Iᶜ) (hn : groupedCut I V a b ≠ 0) :
      (∃ i, e i = a) ∧ (∃ j, f j = b) := by
    obtain ⟨x, hx, y, hy, ha, hb⟩ :=
      grouped_nonzero_singletons s t a.1 b.1 (cut_disjoint a b) hs ht a.2 b.2 hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨i, Subtype.ext ha.symm⟩, ⟨j, Subtype.ext hb.symm⟩⟩
  have hentry (i j) : groupedCut I V (e i) (f j) = grouped i j :=
    grouped_singleton_orbitals hst (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (cut_disjoint (e i) (f j))
  have hrow (a b) (ha : ¬ ∃ i, e i = a) : groupedCut I V a b = 0 := by
    by_contra h
    exact ha (hsupport a b h).1
  have hcol (a b) (hb : ¬ ∃ j, f j = b) : groupedCut I V a b = 0 := by
    by_contra h
    exact hb (hsupport a b h).2
  have hg := eq_padding e f (groupedCut I V) grouped hentry hrow hcol
  have ho := eq_padding e f (orderedCut I V) (signed v w)
    (fun i j => by rw [orderedCut_apply, hentry]; rfl)
    (fun a b ha => by rw [orderedCut_apply, hrow a b ha, mul_zero])
    (fun a b hb => by rw [orderedCut_apply, hcol a b hb, mul_zero])
  refine ⟨V, paired_orbitals_orthonormal s t hsc htc hst,
    compression_charpoly v w hv hw, ?_, ?_⟩
  · rw [hg, paddedGram_charpoly e f grouped, groupedGram_charpoly,
      ← mul_assoc, ← pow_succ]
    have hcard := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at hcard ⊢
    congr 2
    omega
  · rw [hg, ho, paddedGram_charpoly e f (signed v w), paddedGram_charpoly e f grouped]
    intro h
    exact hminor (mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h)

theorem alternatingActiveMinor {ι : Type*} [LinearOrder ι] {x y z w : ι}
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    let first := signed ![x, z] ![y, w]
    let second := signed ![y, w] ![x, z]
    (first * first.conjTranspose).charpoly ≠ (grouped * grouped.conjTranspose).charpoly ∧
    (second * second.conjTranspose).charpoly ≠ (grouped * grouped.conjTranspose).charpoly := by
  have hxw := hxy.trans (hyz.trans hzw)
  constructor
  · apply gram_distinct _ grouped_det
    rw [Matrix.det_fin_two]
    norm_num [signed, grouped, crossCount, Finset.filter_singleton, hyz, not_lt_of_gt hxy,
      not_lt_of_gt hxw, not_lt_of_gt hzw]
  · apply gram_distinct _ grouped_det
    rw [Matrix.det_fin_two]
    norm_num [signed, grouped, crossCount, Finset.filter_singleton, hxy, hxw, hzw, not_lt_of_gt hyz]

private def pairEmbedding {ι : Type*} (a b : ι) (h : a ≠ b) : Fin 2 ↪ ι where
  toFun := ![a, b]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem pair_membership {ι : Type*} {I : Set ι} {a b : ι}
    (h : a ≠ b) (ha : a ∈ I) (hb : b ∈ I) (i : Fin 2) :
    pairEmbedding a b h i ∈ I := by
  fin_cases i
  · exact ha
  · exact hb

/-- Alternation produces an orthonormal two-orbital Slater witness on the full cut. -/
theorem alternating_cut_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (h : Alternates I) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ((retainedRows I V) * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ≠
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly := by
  obtain ⟨x, y, z, w, hxy, hyz, hzw, hsites | hsites⟩ := h
  · obtain ⟨hx, hy, hz, hw⟩ := hsites
    let v := pairEmbedding x z (hxy.trans hyz).ne
    let u := pairEmbedding y w (hyz.trans hzw).ne
    exact orthonormal_cut_obstruction v u
      (pair_membership _ hx hz) (pair_membership _ hy hw)
      (alternatingActiveMinor hxy hyz hzw).1
  · obtain ⟨hx, hy, hz, hw⟩ := hsites
    let v := pairEmbedding y w (hyz.trans hzw).ne
    let u := pairEmbedding x z (hxy.trans hyz).ne
    exact orthonormal_cut_obstruction v u
      (pair_membership _ hy hw) (pair_membership _ hx hz)
      (alternatingActiveMinor hxy hyz hzw).2

/-- The interval condition is exact for equality of the literal and grouped
determinant marginal polynomials for every orthonormal orbital family. -/
theorem universal_cut_spectrum_iff {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι) :
    ¬ Alternates I ↔
      ∀ (k : ℕ) (V : Matrix ι (Fin k) ℂ), V.conjTranspose * V = 1 →
        (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        (groupedCut I V * (groupedCut I V).conjTranspose).charpoly := by
  constructor
  · intro h k V _
    exact (SlaterShuffleSignProbe.grouped_ordered_marginal_charpoly h
      (fun a : Occupation I => a.1) (fun b : Occupation Iᶜ => b.1)
      (fun a => a.2) (fun b => b.2) V).symm
  · intro h hAlt
    obtain ⟨V, hnorm, _, _, hne⟩ := alternating_cut_obstruction hAlt
    exact hne (h 2 V hnorm)

open Polynomial in
private theorem one_nonzero_mode {α : Type*} [Fintype α] (ν : α → ℂ)
    (h : (∏ i : α, (X - C (ν i))) = X ^ (Fintype.card α - 1) * (X - 1)) :
    ∃ j, ν j = 1 ∧ ∀ i, i ≠ j → ν i = 0 := by
  classical
  let m := (Finset.univ : Finset α).val.map ν
  have hm : ((∏ i : α, (X - C (ν i))) : ℂ[X]).roots = m := by
    simpa only [m, Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_apply]
      using roots_multiset_prod_X_sub_C m
  have hfactor : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  have hval : m = (Fintype.card α - 1) • ({0} : Multiset ℂ) + {1} := by
    rw [← hm, h, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hfactor), roots_X_pow]
    rw [← C_1, roots_X_sub_C]
  have hcard : (Finset.univ.filter fun i => ν i = 1).card = 1 := by
    have hm1 : m.count 1 = 1 := by
      rw [hval]
      simp
    dsimp only [m] at hm1
    rw [Multiset.count_map] at hm1
    rw [Finset.card, Finset.filter_val]
    rw [Multiset.filter_congr
      (q := fun i => (1 : ℂ) = ν i) (fun _ _ => eq_comm)]
    exact hm1
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hs (i : α) : ν i = 1 ↔ i = j := by
    have hi : i ∈ Finset.univ.filter (fun t => ν t = 1) ↔ i ∈ ({j} : Finset α) := by
      rw [hj]
    simpa using hi
  refine ⟨j, (hs j).mpr rfl, fun i hi => ?_⟩
  have hm : ν i ∈ m := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  rw [hval, Multiset.mem_add] at hm
  rcases hm with hm | hm
  · exact Multiset.mem_singleton.mp ((Multiset.mem_nsmul.mp hm).2)
  · exact False.elim (hi ((hs i).mp (Multiset.mem_singleton.mp hm)))

noncomputable def bernoulliWeight {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (ν : I → ℂ) (a : Occupation I) : ℂ :=
  ∏ i : I, if i.1 ∈ a.1 then ν i else 1 - ν i

open Polynomial in
private theorem single_mode_bernoulli_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (ν : I → ℂ)
    (h : (∏ i : I, (X - C (ν i))) = X ^ (Fintype.card I - 1) * (X - 1)) :
    (∏ a : Occupation I, (X - C (bernoulliWeight ν a))) =
      X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  obtain ⟨j, hj, h0⟩ := one_nonzero_mode ν h
  let single : Occupation I := ⟨{j.1}, by simp⟩
  have weight (a : Occupation I) : bernoulliWeight ν a = if a = single then 1 else 0 := by
    by_cases he : a = single
    · subst a
      rw [ite_eq_left rfl]
      unfold bernoulliWeight
      apply Finset.prod_eq_one
      intro i _
      by_cases hij : i = j
      · subst i
        simp [single, hj]
      · have hv : i.1 ≠ j.1 := fun hh => hij (Subtype.ext hh)
        simp [single, hv, h0 i hij]
    · rw [ite_eq_right he]
      unfold bernoulliWeight
      by_cases hja : j.1 ∈ a.1
      · have hex : ∃ i ∈ a.1, i ≠ j.1 := by
          by_contra! hn
          apply he
          apply Subtype.ext
          ext i
          constructor
          · intro hi
            exact Finset.mem_singleton.mpr (hn i hi)
          · intro hi
            simpa only [Finset.mem_singleton.mp hi] using hja
        obtain ⟨i, hi, hij⟩ := hex
        let l : I := ⟨i, a.2 hi⟩
        apply Finset.prod_eq_zero (Finset.mem_univ l)
        have hlj : l ≠ j := fun e => hij (congrArg Subtype.val e)
        simp [l, hi, h0 l hlj]
      · apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hja, hj]
  simp_rw [weight]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ single)]
  have hd : ∀ a ∈ (Finset.univ : Finset (Occupation I)) \ {single},
      X - C (if a = single then (1 : ℂ) else 0) = X := by
    intro a ha
    have hne : a ≠ single := by simpa using (Finset.mem_sdiff.mp ha).2
    simp [hne]
  rw [Finset.prod_congr rfl hd, Finset.prod_const]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [mul_comm]

open Polynomial in
/-- The two-particle witness defeats the product formula on both alternating orders.
The quantified mode labels cover every enumeration of the compression spectrum. -/
theorem alternating_cut_bernoulli_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (h : Alternates I) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ∀ ν : I → ℂ,
        (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
          (∏ i : I, (X - C (ν i))) →
        (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ≠
          (∏ a : Occupation I, (X - C (bernoulliWeight ν a))) := by
  obtain ⟨V, hV, hc, hg, ho⟩ := alternating_cut_obstruction h
  refine ⟨V, hV, fun ν hν => ?_⟩
  rw [single_mode_bernoulli_charpoly ν (hν.symm.trans hc), ← hg]
  exact ho

end SlaterAlternatingCutProbe
