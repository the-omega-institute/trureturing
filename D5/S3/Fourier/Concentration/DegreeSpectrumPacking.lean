/- GID: D5/S3/Fourier/Concentration/DegreeSpectrumPacking
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DegreeSpectrumPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite interval forces a small gap among distinct equal-degree count vectors. -/

import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finset.Sort

/-! Packing bounds for sums of a finite real spectrum with repetitions. -/

set_option autoImplicit false

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialFrequency)

namespace D5.S3.Fourier.Concentration.DegreeSpectrumPacking

private abbrev DegreeVector (J : Type*) [Fintype J] (p : ℕ) :=
  {m : J → ℕ // (∑ j, m j) = p}

private def countAt {J : Type*} [DecidableEq J] (i : J) (n : ℕ) : J → ℕ :=
  Pi.single i n

private theorem weighted_single {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) (i : J) (n : ℕ) :
    (∑ j, (countAt i n j : ℝ) * g j) = (n : ℝ) * g i := by
  calc
    _ = (countAt i n i : ℝ) * g i :=
      sum_eq_single_of_mem i (mem_univ i) fun j _ hj => by
        rw [countAt, Pi.single_eq_of_ne hj, Nat.cast_zero, zero_mul]
    _ = _ := by rw [countAt, Pi.single_eq_same]

private theorem le_weighted_sum_of_ne_single {J : Type*} [Fintype J] [DecidableEq J]
    {p : ℕ} {m : J → ℕ} (hmass : (∑ j, m j) = p) {i : J} (hm : m ≠ countAt i p)
    (w : J → ℝ) {d : ℝ} (hw : ∀ j, 0 ≤ w j) (hd : ∀ j, j ≠ i → d ≤ w j) :
    d ≤ ∑ j, (m j : ℝ) * w j := by
  have hex : ∃ j, j ≠ i ∧ 0 < m j := by
    by_contra! h
    have hi : m i = p :=
      (sum_eq_single_of_mem i (mem_univ i) fun j _ hj => Nat.eq_zero_of_le_zero (h j hj)).symm.trans
        hmass
    apply hm
    funext j
    by_cases hj : j = i
    · subst j
      simpa only [countAt, Pi.single_eq_same] using hi
    · rw [countAt, Pi.single_eq_of_ne hj, Nat.eq_zero_of_le_zero (h j hj)]
  obtain ⟨j, hj, hjpos⟩ := hex
  have hjone : (1 : ℝ) ≤ m j := by exact_mod_cast hjpos
  calc
    d ≤ w j := hd j hj
    _ ≤ (m j : ℝ) * w j := by simpa using mul_le_mul_of_nonneg_right hjone (hw j)
    _ ≤ ∑ k, (m k : ℝ) * w k :=
      single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hw k)) (mem_univ j)

private def pureDegree {J : Type*} [Fintype J] [DecidableEq J] (p : ℕ) (i : J) :
    DegreeVector J p :=
  ⟨countAt i p, Fintype.sum_pi_single' i p⟩

private theorem frequency_pureDegree {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) (p : ℕ) (i : J) :
    monomialFrequency g (pureDegree p i).val = (p : ℝ) * g i :=
  weighted_single g i p

-- A count vector formed by assigning three multiplicities, allowing repeated coordinates.
private def tripleDegree {J : Type*} [Fintype J] [DecidableEq J] {p : ℕ}
    (i j k : J) (u v w : ℕ) (h : u + v + w = p) : DegreeVector J p :=
  ⟨countAt i u + countAt j v + countAt k w, by
    simpa only [Pi.add_apply, sum_add_distrib, countAt, Fintype.sum_pi_single'] using h⟩

private theorem frequency_tripleDegree {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) {p : ℕ} (i j k : J) (u v w : ℕ) (h : u + v + w = p) :
    monomialFrequency g (tripleDegree i j k u v w h).val =
      (u : ℝ) * g i + (v : ℝ) * g j + (w : ℝ) * g k := by
  change (∑ l, ((countAt i u l + countAt j v l + countAt k w l : ℕ) : ℝ) * g l) = _
  simp only [Nat.cast_add, add_mul, sum_add_distrib, weighted_single]

private theorem degree_frequency_mem_Icc {J : Type*} [Fintype J]
    (g : J → ℝ) {p : ℕ} {a b : ℝ} (hg : ∀ j, g j ∈ Set.Icc a b) (m : DegreeVector J p) :
    monomialFrequency g m.val ∈ Set.Icc ((p : ℝ) * a) ((p : ℝ) * b) := by
  have hmass : (∑ j, (m.val j : ℝ)) = p := by exact_mod_cast m.property
  change (p : ℝ) * a ≤ ∑ j, (m.val j : ℝ) * g j ∧
    (∑ j, (m.val j : ℝ) * g j) ≤ (p : ℝ) * b
  rw [← hmass, sum_mul, sum_mul]
  exact ⟨sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j).1 (Nat.cast_nonneg _),
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j).2 (Nat.cast_nonneg _)⟩

private theorem exists_large_frequency_end_gap {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) {p : ℕ} (hJ : 3 ≤ Fintype.card J) (hp : 2 ≤ p) {δ : ℝ}
    (hinj : Function.Injective (fun m : DegreeVector J p => monomialFrequency g m.val))
    (hgap : ∀ m n : DegreeVector J p, m ≠ n →
      δ < |monomialFrequency g m.val - monomialFrequency g n.val|) :
    ∃ lo hi lo₂ hi₂ : J,
      (∀ j, g lo ≤ g j) ∧ (∀ j, g j ≤ g hi) ∧
      (∀ j, j ≠ lo → g lo₂ ≤ g j) ∧ (∀ j, j ≠ hi → g j ≤ g hi₂) ∧
      (2 * δ < g lo₂ - g lo ∨ 2 * δ < g hi - g hi₂) := by
  let x (m : DegreeVector J p) := monomialFrequency g m.val
  change Function.Injective x at hinj
  change ∀ m n : DegreeVector J p, m ≠ n → δ < |x m - x n| at hgap
  have hJpos : 0 < Fintype.card J := by omega
  have huniv : (univ : Finset J).Nonempty := card_pos.mp (by simpa using hJpos)
  have hginj : Function.Injective g := by
    intro i j hij
    have heq : pureDegree p i = pureDegree p j := hinj (by
      change monomialFrequency g (pureDegree p i).val =
        monomialFrequency g (pureDegree p j).val
      rw [frequency_pureDegree, frequency_pureDegree, hij])
    by_contra hne
    have h := congrArg (fun m : DegreeVector J p => m.val i) heq
    change countAt i p i = countAt j p i at h
    simp only [countAt, Pi.single_eq_of_ne hne, Pi.single_eq_same] at h
    omega
  obtain ⟨lo, _, hlo⟩ := exists_min_image univ g huniv
  obtain ⟨hi, _, hhi⟩ := exists_max_image univ g huniv
  have herase (j : J) : 1 < (univ.erase j).card := by
    rw [card_erase_of_mem (mem_univ j), card_univ]
    omega
  obtain ⟨lo₂, hlo₂mem, hlo₂⟩ := exists_min_image (univ.erase lo) g (card_pos.mp (by
    have := herase lo
    omega))
  obtain ⟨hi₂, hhi₂mem, hhi₂⟩ := exists_max_image (univ.erase hi) g (card_pos.mp (by
    have := herase hi
    omega))
  have hlo₂ne : lo₂ ≠ lo := (mem_erase.mp hlo₂mem).1
  have hhi₂ne : hi₂ ≠ hi := (mem_erase.mp hhi₂mem).1
  have hlohi : lo ≠ hi := by
    intro heq
    have hglt := lt_of_le_of_ne (hlo lo₂ (mem_univ _)) (fun h => hlo₂ne (hginj h).symm)
    exact hglt.not_ge (by simpa only [heq] using hhi lo₂ (mem_univ _))
  have hlo₂hi : lo₂ ≠ hi := by
    obtain ⟨j, hj, hjne⟩ := exists_mem_ne (herase lo) hi
    intro heq
    exact hjne (hginj (le_antisymm (hhi j (mem_univ _)) (by simpa only [heq] using hlo₂ j hj)))
  let padded (i : J) : DegreeVector J p := tripleDegree lo i lo (p - 1) 1 0 (by omega)
  have xpadded (i : J) : x (padded i) = ((p - 1 : ℕ) : ℝ) * g lo + g i := by
    change monomialFrequency g (tripleDegree lo i lo (p - 1) 1 0 (by omega)).val = _
    rw [frequency_tripleDegree]
    simp
  have hcoord (i j : J) (hne : i ≠ j) (hle : g i ≤ g j) : δ < g j - g i := by
    have hne' : padded j ≠ padded i := by
      intro heq
      have h := congrArg (fun m : DegreeVector J p => m.val i) heq
      change countAt lo (p - 1) i + countAt j 1 i + countAt lo 0 i =
        countAt lo (p - 1) i + countAt i 1 i + countAt lo 0 i at h
      simp only [countAt, Pi.single_eq_of_ne hne, Pi.single_eq_same] at h
      omega
    have h := hgap (padded j) (padded i) hne'
    rw [xpadded, xpadded, show ((p - 1 : ℕ) : ℝ) * g lo + g j -
      (((p - 1 : ℕ) : ℝ) * g lo + g i) = g j - g i by ring,
      abs_of_nonneg (sub_nonneg.mpr hle)] at h
    exact h
  -- Comparing these two vectors separates the two frequency gaps at the ends.
  let left : DegreeVector J p := tripleDegree lo lo₂ hi₂ (p - 2) 1 1 (by omega)
  let right : DegreeVector J p := padded hi
  have hlr : left ≠ right := by
    intro heq
    have h := congrArg (fun m : DegreeVector J p => m.val hi) heq
    change countAt lo (p - 2) hi + countAt lo₂ 1 hi + countAt hi₂ 1 hi =
      countAt lo (p - 1) hi + countAt hi 1 hi + countAt lo 0 hi at h
    simpa [countAt, Pi.single_eq_of_ne hlohi.symm, Pi.single_eq_of_ne hlo₂hi.symm,
      Pi.single_eq_of_ne hhi₂ne.symm] using h
  have hsep : δ < |(g lo₂ - g lo) - (g hi - g hi₂)| := by
    have h := hgap left right hlr
    have hleft : x left = ((p - 2 : ℕ) : ℝ) * g lo + g lo₂ + g hi₂ := by
      change monomialFrequency g (tripleDegree lo lo₂ hi₂ (p - 2) 1 1 (by omega)).val = _
      rw [frequency_tripleDegree]
      simp
    have hcast : ((p - 1 : ℕ) : ℝ) = ((p - 2 : ℕ) : ℝ) + 1 := by
      rw [show p - 1 = p - 2 + 1 by omega, Nat.cast_add, Nat.cast_one]
    have hright : x right = _ := xpadded hi
    rw [hleft, hright, hcast,
      show ((p - 2 : ℕ) : ℝ) * g lo + g lo₂ + g hi₂ -
          ((((p - 2 : ℕ) : ℝ) + 1) * g lo + g hi) = (g lo₂ - g lo) - (g hi - g hi₂) by
        ring] at h
    exact h
  have hlarge : 2 * δ < g lo₂ - g lo ∨ 2 * δ < g hi - g hi₂ := by
    have hlow := hcoord lo lo₂ hlo₂ne.symm (hlo _ (mem_univ _))
    have hhigh := hcoord hi₂ hi hhi₂ne (hhi _ (mem_univ _))
    rcases lt_abs.mp hsep with h | h
    · exact Or.inl (by linarith only [h, hhigh])
    · exact Or.inr (by linarith only [h, hlow])
  exact ⟨lo, hi, lo₂, hi₂, fun j => hlo j (mem_univ _), fun j => hhi j (mem_univ _),
    fun j hj => hlo₂ j (mem_erase.mpr ⟨hj, mem_univ _⟩),
    fun j hj => hhi₂ j (mem_erase.mpr ⟨hj, mem_univ _⟩), hlarge⟩

private theorem exists_large_degree_step {J : Type*} [Fintype J] [DecidableEq J]
    (g : J → ℝ) {p q : ℕ} {δ : ℝ} (hqpos : 0 < q) (f : Fin (q + 1) ↪o ℝ)
    (hpreimage : ∀ i, ∃ m : DegreeVector J p, monomialFrequency g m.val = f i)
    (hindex : ∀ m : DegreeVector J p, ∃ i, f i = monomialFrequency g m.val)
    {lo hi lo₂ hi₂ : J}
    (hlo : ∀ j, g lo ≤ g j) (hhi : ∀ j, g j ≤ g hi)
    (hlo₂ : ∀ j, j ≠ lo → g lo₂ ≤ g j) (hhi₂ : ∀ j, j ≠ hi → g j ≤ g hi₂)
    (hlarge : 2 * δ < g lo₂ - g lo ∨ 2 * δ < g hi - g hi₂) :
    ∃ i : Fin q, 2 * δ < f i.succ - f i.castSucc := by
  have hactual (m : DegreeVector J p) :
      monomialFrequency g m.val ∈ Set.Icc ((p : ℝ) * g lo) ((p : ℝ) * g hi) :=
    degree_frequency_mem_Icc g (fun j => ⟨hlo j, hhi j⟩) m
  have hmass (m : DegreeVector J p) : (∑ j, (m.val j : ℝ)) = p := by exact_mod_cast m.property
  have hfirst : f 0 = (p : ℝ) * g lo := by
    obtain ⟨i, hi⟩ := hindex (pureDegree p lo)
    obtain ⟨m, hm⟩ := hpreimage 0
    have h : f 0 ≤ f i := f.monotone i.zero_le
    rw [hi, frequency_pureDegree] at h
    exact le_antisymm h (by rw [← hm]; exact (hactual m).1)
  have hlast : f (Fin.last q) = (p : ℝ) * g hi := by
    obtain ⟨i, hi'⟩ := hindex (pureDegree p hi)
    obtain ⟨m, hm⟩ := hpreimage (Fin.last q)
    have h : f i ≤ f (Fin.last q) := f.monotone i.le_last
    rw [hi', frequency_pureDegree] at h
    exact le_antisymm (by rw [← hm]; exact (hactual m).2) h
  rcases hlarge with h | h
  · let i : Fin q := ⟨0, hqpos⟩
    have hizero : i.castSucc = 0 := Fin.ext rfl
    obtain ⟨m, hm⟩ := hpreimage i.succ
    have hne : m.val ≠ countAt lo p := by
      intro heq
      have hmp : m = pureDegree p lo := Subtype.ext heq
      have hlt := f.strictMono i.castSucc_lt_succ
      rw [hizero, hfirst, ← hm, hmp, frequency_pureDegree] at hlt
      exact (lt_irrefl _ hlt)
    have hle := le_weighted_sum_of_ne_single m.property hne (fun j => g j - g lo)
      (fun j => sub_nonneg.mpr (hlo j))
      (fun j hj => sub_le_sub_right (hlo₂ j hj) _)
    change g lo₂ - g lo ≤ ∑ j, (m.val j : ℝ) * (g j - g lo) at hle
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hmass m] at hle
    change g lo₂ - g lo ≤ monomialFrequency g m.val - (p : ℝ) * g lo at hle
    rw [hm, ← hfirst, ← hizero] at hle
    exact ⟨i, h.trans_le hle⟩
  · let i : Fin q := ⟨q - 1, by omega⟩
    have hilast : i.succ = Fin.last q := Fin.ext (by change q - 1 + 1 = q; omega)
    obtain ⟨m, hm⟩ := hpreimage i.castSucc
    have hne : m.val ≠ countAt hi p := by
      intro heq
      have hmp : m = pureDegree p hi := Subtype.ext heq
      have hlt := f.strictMono i.castSucc_lt_succ
      rw [hilast, hlast, ← hm, hmp, frequency_pureDegree] at hlt
      exact (lt_irrefl _ hlt)
    have hle := le_weighted_sum_of_ne_single m.property hne (fun j => g hi - g j)
      (fun j => sub_nonneg.mpr (hhi j))
      (fun j hj => sub_le_sub_left (hhi₂ j hj) _)
    change g hi - g hi₂ ≤ ∑ j, (m.val j : ℝ) * (g hi - g j) at hle
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hmass m] at hle
    change g hi - g hi₂ ≤ (p : ℝ) * g hi - monomialFrequency g m.val at hle
    rw [hm, ← hlast, ← hilast] at hle
    exact ⟨i, h.trans_le hle⟩

private theorem exists_close_degree_vectors_bound {J : Type*} [Fintype J]
    (g : J → ℝ) (p : ℕ) {a b : ℝ} (hg : ∀ j, g j ∈ Set.Icc a b)
    (hmany : 2 ≤ Nat.multichoose (Fintype.card J) p) :
    ∃ m n : J → ℕ, m ≠ n ∧ (∑ j, m j) = p ∧ (∑ j, n j) = p ∧
      |monomialFrequency g m - monomialFrequency g n| ≤
        (p : ℝ) * (b - a) /
          (if 3 ≤ Fintype.card J ∧ 2 ≤ p then (Nat.multichoose (Fintype.card J) p : ℝ)
           else (Nat.multichoose (Fintype.card J) p : ℝ) - 1) := by
  classical
  let M := Nat.multichoose (Fintype.card J) p
  let D := DegreeVector J p
  let equiv : Sym J p ≃ D := Sym.equivNatSumOfFintype J p
  let _ : Fintype D := Fintype.ofEquiv (Sym J p) equiv
  let x (m : D) := monomialFrequency g m.val
  let denom : ℝ := if 3 ≤ Fintype.card J ∧ 2 ≤ p then (M : ℝ) else (M : ℝ) - 1
  let δ := (p : ℝ) * (b - a) / denom
  have hdenom : 0 < denom := by
    have h : (2 : ℝ) ≤ M := by exact_mod_cast hmany
    dsimp [denom]
    split <;> linarith
  have hcardD : Fintype.card D = M := by
    rw [← Fintype.card_congr equiv, Sym.card_sym_eq_multichoose]
  have hnonempty : Nonempty D := Fintype.card_pos_iff.mp (hcardD.symm ▸ (by omega : 0 < M))
  obtain ⟨m⟩ := hnonempty
  have hδ : 0 ≤ δ := by
    apply div_nonneg _ hdenom.le
    linarith [(degree_frequency_mem_Icc g hg m).1.trans (degree_frequency_mem_Icc g hg m).2]
  by_contra! hfar
  have hgap (m n : D) (hne : m ≠ n) : δ < |x m - x n| :=
    hfar m.val n.val (fun h => hne (Subtype.ext h)) m.property n.property
  have hinj : Function.Injective x := by
    intro m n heq
    by_contra hne
    have hbad := hgap m n hne
    rw [heq, sub_self, abs_zero] at hbad
    exact hbad.not_ge hδ
  let s := (univ : Finset D).image x
  let q := M - 1
  have hq : q + 1 = M := by change M - 1 + 1 = M; omega
  have hqpos : 0 < q := by omega
  have hcard : s.card = q + 1 := by
    exact ((card_image_of_injective _ hinj).trans card_univ).trans (hcardD.trans hq.symm)
  let f := s.orderEmbOfFin hcard
  have hpreimage (i : Fin (q + 1)) : ∃ m : D, x m = f i := by
    obtain ⟨m, _, hm⟩ := mem_image.mp (s.orderEmbOfFin_mem hcard i)
    exact ⟨m, hm⟩
  have hf (i : Fin (q + 1)) : f i ∈ Set.Icc ((p : ℝ) * a) ((p : ℝ) * b) := by
    obtain ⟨m, hm⟩ := hpreimage i
    rw [← hm]
    exact degree_frequency_mem_Icc g hg m
  have hstep (i : Fin q) : δ < f i.succ - f i.castSucc := by
    have hlt : f i.castSucc < f i.succ := f.strictMono (by simp)
    obtain ⟨m, hm⟩ := hpreimage i.succ
    obtain ⟨n, hn⟩ := hpreimage i.castSucc
    have hne : m ≠ n := by intro he; subst n; exact hlt.ne (hn.symm.trans hm)
    have h := hgap m n hne
    rwa [hm, hn, abs_of_pos (sub_pos.mpr hlt)] at h
  let z (i : Fin (q + 1)) := f i - (i.val : ℝ) * δ
  have hz : StrictMono z := Fin.strictMono_iff_lt_succ.mpr fun i => by
    have hi := hstep i
    dsimp [z]
    push_cast
    linarith only [hi]
  have hqR : (q : ℝ) = (M : ℝ) - 1 := by
    have h : (q : ℝ) + 1 = M := by exact_mod_cast hq
    linarith
  have hflat : denom * δ = (p : ℝ) * (b - a) := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hdenom.ne'
  have hwidth : f (Fin.last q) - f 0 ≤ (p : ℝ) * (b - a) := by
    linarith [(hf 0).1, (hf (Fin.last q)).2]
  have hspan (ε : ℝ) (h : ε < z (Fin.last q) - z 0) :
      (q : ℝ) * δ + ε < (p : ℝ) * (b - a) := by
    have h' : ε < (f (Fin.last q) - (q : ℝ) * δ) - f 0 := by
      simpa [z] using h
    linarith only [h', hwidth]
  by_cases hstrong : 3 ≤ Fintype.card J ∧ 2 ≤ p
  swap
  · have hends := hz (show (0 : Fin (q + 1)) < Fin.last q from hqpos)
    have h := hspan 0 (sub_pos.mpr hends)
    have heq : denom = (q : ℝ) := by simp [denom, hstrong, hqR]
    rw [heq] at hflat
    linarith only [h, hflat]
  obtain ⟨lo, hi, lo₂, hi₂, hlo, hhi, hlo₂, hhi₂, hlarge⟩ :=
    exists_large_frequency_end_gap g hstrong.1 hstrong.2 hinj hgap
  have hindex (m : D) : ∃ i, f i = x m := by
    change x m ∈ Set.range (s.orderEmbOfFin hcard)
    rw [range_orderEmbOfFin]
    exact mem_image.mpr ⟨m, mem_univ _, rfl⟩
  obtain ⟨i, hi⟩ :=
    exists_large_degree_step g hqpos f hpreimage hindex hlo hhi hlo₂ hhi₂ hlarge
  have hzstep : δ < z i.succ - z i.castSucc := by
    dsimp [z]
    push_cast
    linarith only [hi]
  have hend := hspan δ (hzstep.trans_le (sub_le_sub (hz.monotone i.succ.le_last)
    (hz.monotone i.castSucc.zero_le)))
  have heq : denom = (q : ℝ) + 1 := by simp [denom, hstrong, hqR]
  rw [heq, add_mul, one_mul] at hflat
  exact hend.ne hflat

/-- The gap between some distinct degree vectors is at most the sum interval's width
divided by the number of vectors when there are at least three coordinates and the degree
is at least two. In the other cases the denominator is the number of vectors minus one. -/
theorem exists_close_degree_vectors {J : Type*} [Fintype J]
    (g : J → ℝ) (p : ℕ) {a b : ℝ} (hg : ∀ j, g j ∈ Set.Icc a b)
    (hmany : 2 ≤ Nat.multichoose (Fintype.card J) p) :
    ∃ m n : J → ℕ, m ≠ n ∧ (∑ j, m j) = p ∧ (∑ j, n j) = p ∧
      let gap := |monomialFrequency g m - monomialFrequency g n|
      gap ≤ (p : ℝ) * (b - a) / ((Nat.multichoose (Fintype.card J) p : ℝ) - 1) ∧
        (3 ≤ Fintype.card J ∧ 2 ≤ p →
          gap ≤ (p : ℝ) * (b - a) / (Nat.multichoose (Fintype.card J) p : ℝ)) := by
  obtain ⟨m, n, hne, hm, hn, hgap⟩ := exists_close_degree_vectors_bound g p hg hmany
  refine ⟨m, n, hne, hm, hn, ?_⟩
  by_cases h : 3 ≤ Fintype.card J ∧ 2 ≤ p
  · rw [ite_eq_left h] at hgap
    have hw : 0 ≤ (p : ℝ) * (b - a) := by
      have hspan := degree_frequency_mem_Icc g hg ⟨m, hm⟩
      linarith [hspan.1.trans hspan.2]
    have ht : (2 : ℝ) ≤ Nat.multichoose (Fintype.card J) p := by exact_mod_cast hmany
    exact ⟨hgap.trans (div_le_div_of_nonneg_left hw (by linarith) (by linarith)), fun _ => hgap⟩
  · rw [ite_eq_right h] at hgap
    exact ⟨hgap, fun h' => (h h').elim⟩

#print axioms exists_close_degree_vectors

end D5.S3.Fourier.Concentration.DegreeSpectrumPacking
