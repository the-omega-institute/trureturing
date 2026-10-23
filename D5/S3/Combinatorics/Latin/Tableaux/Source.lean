/- GID: D5/S3/Combinatorics/Latin/Tableaux/Source
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/Tableaux/Source
   mirror-E: none(waiver:source-correspondence)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Literal integer fillings, conjugate multiplicities and row saturation. -/

import Mathlib.Tactic

/-! Source for literal Latin tableaux and their availability graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Latin.Tableaux.Source

/-- Fixed left-aligned cells, indexed in the source's top-to-bottom order. -/
abbrev Cells (lam : List ℕ) := (i : Fin lam.length) × Fin lam[i]

/-- An unrestricted integer filling of the fixed source cells. -/
abbrev Filling (lam : List ℕ) := Cells lam → ℤ

/-- The exact source shape, with the equal bottom rows kept as distinct positions. -/
def shape (k : ℕ) : List ℕ := ((List.range (k - 3)).map (· + 4)).reverse ++ [3,3]

/-- The source's conjugate type, extended by zero to every other integer symbol. -/
def conjugate (lam : List ℕ) (s : ℤ) : ℕ :=
  (Finset.univ.filter (fun i : Fin lam.length => 1 ≤ s ∧ s ≤ (lam[i] : ℤ))).card

/-- Definition 2.5 with literal integer multiplicities and no repeated row or column entry. -/
def SourceLatin (lam : List ℕ) (T : Filling lam) : Prop :=
  (∀ i, Function.Injective (fun j => T ⟨i,j⟩)) ∧
  (∀ (i i' : Fin lam.length) (j : Fin lam[i]) (j' : Fin lam[i']),
    j.val = j'.val → T ⟨i,j⟩ = T ⟨i',j'⟩ → i = i') ∧
  (∀ s : ℤ, (Finset.univ.filter (fun c : Cells lam => T c = s)).card = conjugate lam s)

/-- The literal full count; finiteness is a theorem, never an encoding assumption. -/
noncomputable def LT (k : ℕ) : ℕ := Nat.card {T : Filling (shape k) // SourceLatin (shape k) T}

private theorem saturation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Finset ℤ)
    (quota : ∀ s : ℤ,
      (Finset.univ.filter (fun i => s ∈ R i)).card =
      (Finset.univ.filter (fun i => 1 ≤ s ∧ s ≤ ((R i).card : ℤ))).card) :
    ∀ i, R i = Finset.Icc 1 ((R i).card : ℤ) := by
  have positive (i : ι) (s : ℤ) (hs : s ∈ R i) : 1 ≤ s := by
    by_contra hn
    have hz := quota s
    have he : (Finset.univ.filter (fun i => 1 ≤ s ∧ s ≤ ((R i).card : ℤ))) = ∅ := by
      simp [hn]
    rw [he, Finset.card_empty] at hz
    have : i ∈ (Finset.univ.filter (fun i => s ∈ R i)) := by simp [hs]
    have := Finset.card_pos.mpr ⟨i,this⟩
    omega
  have initial : ∀ n : ℕ, ∀ i : ι, (n : ℤ) + 1 ∈ R i ↔ n + 1 ≤ (R i).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have sub : (Finset.univ.filter (fun i => (n : ℤ) + 1 ∈ R i)) ⊆
          (Finset.univ.filter (fun i => 1 ≤ (n : ℤ) + 1 ∧ (n : ℤ) + 1 ≤ ((R i).card : ℤ))) := by
        intro i hi
        have hm : (n : ℤ) + 1 ∈ R i := (Finset.mem_filter.mp hi).2
        have hlen : n + 1 ≤ (R i).card := by
          by_contra hlen
          have hcard : (R i).card ≤ n := by omega
          have hs : Finset.Icc (1 : ℤ) ((R i).card : ℤ) ⊆ R i := by
            intro t ht
            have ht := Finset.mem_Icc.mp ht
            let m := (t-1).toNat
            have hm : m < n := by dsimp [m]; omega
            have he : (m : ℤ) + 1 = t := by dsimp [m]; omega
            rw [← he]
            exact (ih m hm i).mpr (by omega)
          have hc : (Finset.Icc (1 : ℤ) ((R i).card : ℤ)).card = (R i).card := by
            simp [Int.card_Icc]
          have he := Finset.eq_of_subset_of_card_le hs (by omega)
          rw [← he] at hm
          have := (Finset.mem_Icc.mp hm).2
          omega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have eqs := Finset.eq_of_subset_of_card_le sub (by rw [quota])
      intro i
      have he := Finset.ext_iff.mp eqs i
      simpa using he
  intro i
  ext s
  constructor
  · intro hs
    have hp := positive i s hs
    let n := (s-1).toNat
    have he : (n : ℤ) + 1 = s := by dsimp [n]; omega
    have hm := (initial n i).mp (by rwa [he])
    simp only [Finset.mem_Icc]
    omega
  · intro hs
    have hs := Finset.mem_Icc.mp hs
    let n := (s-1).toNat
    have he : (n : ℤ) + 1 = s := by dsimp [n]; omega
    rw [← he]
    exact (initial n i).mpr (by omega)

/-- The actual symbols in one row, without quotienting any positions. -/
def rowSymbols {lam : List ℕ} (T : Filling lam) (i : Fin lam.length) : Finset ℤ :=
  Finset.univ.image (fun j : Fin lam[i] => T ⟨i,j⟩)

private theorem occurrence_rows {lam : List ℕ} (T : Filling lam)
    (hinj : ∀ i, Function.Injective (fun j => T ⟨i,j⟩)) (s : ℤ) :
    (Finset.univ.filter (fun c : Cells lam => T c = s)).card =
      (Finset.univ.filter (fun i => s ∈ rowSymbols T i)).card := by
  classical
  apply Finset.card_bij (fun c _ => c.1)
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, hc⟩
  · intro c hc d hd he
    have hc := (Finset.mem_filter.mp hc).2
    have hd := (Finset.mem_filter.mp hd).2
    rcases c with ⟨i,j⟩
    rcases d with ⟨i',j'⟩
    dsimp at he
    subst i'
    have hj := hinj i (hc.trans hd.symm)
    subst j'
    rfl
  · intro i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
    exact ⟨⟨i,j⟩, by simpa using hj, rfl⟩

/-- Source conjugate type forces precisely the fixed symbols 1 through each row length. -/
theorem source_row_symbols {lam : List ℕ} (T : Filling lam) (h : SourceLatin lam T) :
    ∀ i, rowSymbols T i = Finset.Icc 1 (lam[i] : ℤ) := by
  classical
  have hc (i : Fin lam.length) : (rowSymbols T i).card = lam[i] := by
    exact (Finset.card_image_of_injective _ (h.1 i)).trans (by simp)
  have hq (s : ℤ) : (Finset.univ.filter (fun i => s ∈ rowSymbols T i)).card = conjugate lam s := by
    rw [← occurrence_rows T h.1 s]
    exact h.2.2 s
  have hs := saturation (rowSymbols T) (fun s => by simpa only [hc, conjugate] using hq s)
  intro i
  simpa only [hc] using hs i

/-- Column compatibility and a permutation of each row's fixed initial interval. -/
def RowLatin (lam : List ℕ) (T : Filling lam) : Prop :=
  (∀ i, Function.Injective (fun j => T ⟨i,j⟩) ∧
    rowSymbols T i = Finset.Icc 1 (lam[i] : ℤ)) ∧
  (∀ (i i' : Fin lam.length) (j : Fin lam[i]) (j' : Fin lam[i']),
    j.val = j'.val → T ⟨i,j⟩ = T ⟨i',j'⟩ → i = i')

/-- Identity on every cell gives both directions of the source/row-permutation bridge. -/
theorem source_iff_rows {lam : List ℕ} (T : Filling lam) :
    SourceLatin lam T ↔ RowLatin lam T := by
  classical
  constructor
  · intro h
    exact ⟨fun i => ⟨h.1 i, source_row_symbols T h i⟩, h.2.1⟩
  · rintro ⟨hr,hcol⟩
    refine ⟨fun i => (hr i).1, hcol, ?_⟩
    intro s
    rw [occurrence_rows T (fun i => (hr i).1) s]
    unfold conjugate
    congr 1
    ext i
    simp [(hr i).2]

/-- The finite carrier retains every literal position and encodes symbol n+1 by n. -/
def FiniteLatin (lam : List ℕ) :=
  {T : (i : Fin lam.length) → Fin lam[i] → Fin lam[i] //
    (∀ i, Function.Injective (T i)) ∧
    ∀ (i i' : Fin lam.length) (j : Fin lam[i]) (j' : Fin lam[i']),
      j.val = j'.val → (T i j).val = (T i' j').val → i = i'}

private def fromFinite {lam : List ℕ} (T : FiniteLatin lam) : Filling lam :=
  fun c => ((T.1 c.1 c.2).val : ℤ) + 1

private theorem fromFinite_latin {lam : List ℕ} (T : FiniteLatin lam) :
    SourceLatin lam (fromFinite T) := by
  apply (source_iff_rows _).mpr
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · intro j j' he
    apply T.2.1 i
    apply Fin.ext
    dsimp [fromFinite] at he
    omega
  · ext s
    simp only [rowSymbols, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨j, rfl⟩
      have hlt : (T.1 i j).val < lam[i.val] := (T.1 i j).isLt
      change 1 ≤ ((T.1 i j).val : ℤ) + 1 ∧ ((T.1 i j).val : ℤ) + 1 ≤ (lam[i.val] : ℤ)
      omega
    · rintro ⟨hs,ht⟩
      let v : Fin lam[i] := ⟨(s-1).toNat, by omega⟩
      obtain ⟨j,hj⟩ := (Finite.injective_iff_bijective.mp (T.2.1 i)).2 v
      refine ⟨j, ?_⟩
      dsimp [fromFinite]
      rw [hj]
      dsimp [v]
      omega
  · intro i i' j j' he hs
    apply T.2.2 i i' j j' he
    dsimp [fromFinite] at hs
    omega

private def toFinite {lam : List ℕ} (T : {T : Filling lam // SourceLatin lam T}) :
    FiniteLatin lam := by
  classical
  have hbound (i : Fin lam.length) (j : Fin lam[i]) :
      1 ≤ T.1 ⟨i,j⟩ ∧ T.1 ⟨i,j⟩ ≤ (lam[i] : ℤ) := by
    apply Finset.mem_Icc.mp
    rw [← source_row_symbols T.1 T.2 i]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  let f : (i : Fin lam.length) → Fin lam[i] → Fin lam[i] :=
    fun i j => ⟨(T.1 ⟨i,j⟩ - 1).toNat, by have := hbound i j; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j j' he
    apply T.2.1 i
    change T.1 ⟨i,j⟩ = T.1 ⟨i,j'⟩
    have h1 := hbound i j
    have h2 := hbound i j'
    have hv := congrArg Fin.val he
    change (T.1 ⟨i,j⟩ - 1).toNat = (T.1 ⟨i,j'⟩ - 1).toNat at hv
    clear he
    omega
  · intro i i' j j' he hs
    apply T.2.2.1 i i' j j' he
    have h1 := hbound i j
    have h2 := hbound i' j'
    dsimp [f] at hs
    omega

/-- Reversible correspondence with all source integer fillings, without any quotient. -/
noncomputable def sourceEquiv (lam : List ℕ) :
    {T : Filling lam // SourceLatin lam T} ≃ FiniteLatin lam where
  toFun := toFinite
  invFun T := ⟨fromFinite T, fromFinite_latin T⟩
  left_inv T := by
    apply Subtype.ext
    funext c
    rcases c with ⟨i,j⟩
    have h := Finset.mem_Icc.mp ((source_row_symbols T.1 T.2 i) ▸
      (show T.1 ⟨i,j⟩ ∈ rowSymbols T.1 i from Finset.mem_image.mpr ⟨j,by simp,rfl⟩))
    dsimp [fromFinite, toFinite]
    omega
  right_inv T := by
    apply Subtype.ext
    funext i j
    apply Fin.ext
    simp [toFinite, fromFinite]

/-- Finiteness of every source conjugate-type Latin tableau family. -/
theorem source_finite (lam : List ℕ) :
    Finite {T : Filling lam // SourceLatin lam T} := by
  classical
  haveI : Finite (FiniteLatin lam) := by unfold FiniteLatin; infer_instance
  exact Finite.of_equiv (FiniteLatin lam) (sourceEquiv lam).symm

end D5.S3.Combinatorics.Latin.Tableaux.Source
