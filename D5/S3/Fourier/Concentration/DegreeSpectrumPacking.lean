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

/-- Distinct degree vectors force a gap at most the frequency-sum width divided by
the number of gaps between vectors. Repeated numerical sums contribute a gap of zero. -/
theorem exists_close_degree_vectors {J : Type*} [Fintype J]
    (g : J → ℝ) (p : ℕ) {a b : ℝ} (hg : ∀ j, g j ∈ Set.Icc a b)
    (hmany : 2 ≤ Nat.multichoose (Fintype.card J) p) :
    ∃ m n : J → ℕ, m ≠ n ∧ (∑ j, m j) = p ∧ (∑ j, n j) = p ∧
      |monomialFrequency g m - monomialFrequency g n| ≤
        (p : ℝ) * (b - a) / ((Nat.multichoose (Fintype.card J) p : ℝ) - 1) := by
  classical
  let M := Nat.multichoose (Fintype.card J) p
  let D := {m : J → ℕ // ∑ j, m j = p}
  let equiv : Sym J p ≃ D := Sym.equivNatSumOfFintype J p
  let _ : Fintype D := Fintype.ofEquiv (Sym J p) equiv
  let x (m : D) := monomialFrequency g m.val
  let δ := (p : ℝ) * (b - a) / ((M : ℝ) - 1)
  have hM : 0 < (M : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ M := by exact_mod_cast hmany
    linarith
  have hinterval (m : D) : x m ∈ Set.Icc ((p : ℝ) * a) ((p : ℝ) * b) := by
    have hsum : (∑ j, (m.val j : ℝ)) = p := by exact_mod_cast m.property
    change (p : ℝ) * a ≤ ∑ j, (m.val j : ℝ) * g j ∧
      (∑ j, (m.val j : ℝ) * g j) ≤ (p : ℝ) * b
    rw [← hsum, sum_mul, sum_mul]
    exact ⟨sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j).1 (Nat.cast_nonneg _),
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j).2 (Nat.cast_nonneg _)⟩
  have hcardD : Fintype.card D = M := by
    rw [← Fintype.card_congr equiv, Sym.card_sym_eq_multichoose]
  have hnonempty : Nonempty D := Fintype.card_pos_iff.mp (hcardD.symm ▸ (by omega : 0 < M))
  obtain ⟨m⟩ := hnonempty
  have hδ : 0 ≤ δ := by
    apply div_nonneg _ hM.le
    linarith [(hinterval m).1.trans (hinterval m).2]
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
  have hf (i : Fin (q + 1)) : f i ∈ Set.Icc ((p : ℝ) * a) ((p : ℝ) * b) := by
    obtain ⟨m, _, hm⟩ := mem_image.mp (s.orderEmbOfFin_mem hcard i)
    rw [← hm]
    exact hinterval m
  have hstep (i : Fin q) : δ < f i.succ - f i.castSucc := by
    have hlt : f i.castSucc < f i.succ := f.strictMono (by simp)
    obtain ⟨m, _, hm⟩ := mem_image.mp (s.orderEmbOfFin_mem hcard i.succ)
    obtain ⟨n, _, hn⟩ := mem_image.mp (s.orderEmbOfFin_mem hcard i.castSucc)
    have hne : m ≠ n := by intro he; subst n; exact hlt.ne (hn.symm.trans hm)
    have h := hgap m n hne
    change x m = f i.succ at hm
    change x n = f i.castSucc at hn
    rwa [hm, hn, abs_of_pos (sub_pos.mpr hlt)] at h
  let z (i : Fin (q + 1)) := f i - (i.val : ℝ) * δ
  have hz : StrictMono z := Fin.strictMono_iff_lt_succ.mpr fun i => by
    have hi := hstep i
    dsimp [z]
    push_cast
    nlinarith
  have hends := hz (show (0 : Fin (q + 1)) < Fin.last q from hqpos)
  have hspan : (q : ℝ) * δ < (p : ℝ) * (b - a) := by
    dsimp [z] at hends
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hends
    linarith [(hf 0).1, (hf (Fin.last q)).2]
  have hqR : (q : ℝ) = (M : ℝ) - 1 := by
    have h : (q : ℝ) + 1 = M := by exact_mod_cast hq
    linarith
  have hflat : (q : ℝ) * δ = (p : ℝ) * (b - a) := by
    rw [hqR]
    dsimp [δ]
    field_simp
  exact hspan.ne hflat

#print axioms exists_close_degree_vectors

end D5.S3.Fourier.Concentration.DegreeSpectrumPacking
