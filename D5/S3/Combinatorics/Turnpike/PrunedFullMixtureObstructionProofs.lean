/- GID: D5/S3/Combinatorics/Turnpike/PrunedFullMixtureObstructionProofs
   generality: G
   mirror-B: none(waiver:covered-by-pruned-full-mixture-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A forbidden observation for every real realization -/

module
public import D5.S3.Combinatorics.Turnpike.PrunedFullMixtureData
public import D5.S3.Combinatorics.Turnpike.ActualMixture
public import Mathlib.Order.Interval.Finset.Nat

/-! Omega original.
# A forbidden observation for every real realization

Translation to natural coordinates preserves every interval and its histogram.
Only the bounded integer obstruction is enumerated.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedFullMixture
open Omega.Turnpike
open scoped BigOperators
noncomputable section

def histogram (z : Fin 7 → ℕ) (q : Fin 9) : ℕ :=
  (Finset.univ.filter fun e : Interval 7 => z e.1.2 - z e.1.1 = values q).card

theorem bounded_forbidden :
    ∀ a ∈ Finset.Icc 1 2, ∀ b ∈ Finset.Icc 4 6,
    ∀ c ∈ Finset.Icc (b+1) 7, ∀ d ∈ Finset.Icc (c+1) 8,
    ∀ f ∈ Finset.Icc (d+1) 9,
    ¬ ∀ q, histogram ![0,a,3,b,c,d,f] q = μ q := by
  decide +kernel

theorem nat_forbidden (z : Fin 7 → ℕ) (hm : StrictMono z)
    (hzero : z 0 = 0) (hb : ∀ i, z i ≤ 9)
    (hc : ∀ q, histogram z q = μ q) : z 2 ≠ 3 := by
  intro htwo
  have h01 := hm (show (0 : Fin 7) < 1 by decide)
  have h12 := hm (show (1 : Fin 7) < 2 by decide)
  have h23 := hm (show (2 : Fin 7) < 3 by decide)
  have h34 := hm (show (3 : Fin 7) < 4 by decide)
  have h45 := hm (show (4 : Fin 7) < 5 by decide)
  have h56 := hm (show (5 : Fin 7) < 6 by decide)
  have h6 := hb 6
  have hz : z = ![0,z 1,3,z 3,z 4,z 5,z 6] := by
    funext i
    fin_cases i <;> simp_all
  apply bounded_forbidden (z 1) (by simp only [Finset.mem_Icc]; omega)
    (z 3) (by simp only [Finset.mem_Icc]; omega)
    (z 4) (by simp only [Finset.mem_Icc]; omega)
    (z 5) (by simp only [Finset.mem_Icc]; omega)
    (z 6) (by simp only [Finset.mem_Icc]; omega)
  simpa only [← hz] using hc

theorem real_forbidden (x : Fin 7 → ℝ) (hx : Realizes y μ x) : x 2 - x 0 ≠ y 6 := by
  classical
  have hi : ∀ i : Fin 7, ∃ k : ℕ, k ≤ 9 ∧ x i - x 0 = (k : ℝ) := by
    intro i
    by_cases h : i = 0
    · subst i; exact ⟨0,by omega,by simp⟩
    · have hpos : (0 : Fin 7) < i := Fin.pos_iff_ne_zero.mpr h
      obtain ⟨q,hq⟩ := hx.2.1 ⟨(0,i),hpos⟩
      exact ⟨values q,by fin_cases q <;> decide,hq⟩
  choose z hz using hi
  have hmono : StrictMono z := by
    intro i j hij
    have hm := hx.1 hij
    have hi := (hz i).2
    have hj := (hz j).2
    have ht : (z i : ℝ) < (z j : ℝ) := by linarith
    exact_mod_cast ht
  have hzero : z 0 = 0 := by
    have h := (hz 0).2
    have ht : (z 0 : ℝ) = 0 := by linarith
    exact_mod_cast ht
  have hd (e : Interval 7) :
      x e.1.2 - x e.1.1 = ((z e.1.2 - z e.1.1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (hmono.monotone (le_of_lt e.2))]
    linarith [(hz e.1.1).2,(hz e.1.2).2]
  have hc : ∀ q, histogram z q = μ q := by
    intro q
    rw [← hx.2.2 q]
    unfold histogram
    congr 1
    apply Finset.filter_congr
    intro e _
    rw [hd e]
    change (z e.1.2 - z e.1.1 = values q) ↔
      (((z e.1.2 - z e.1.1 : ℕ) : ℝ) = (values q : ℝ))
    exact_mod_cast (Iff.rfl : (z e.1.2 - z e.1.1 = values q) ↔ _)
  intro h
  have htwo : z 2 = 3 := by
    have ht : (z 2 : ℝ) = 3 := by
      have hh := (hz 2).2
      norm_num [y,values] at h
      linarith
    exact_mod_cast ht
  exact nat_forbidden z hmono hzero (fun i => (hz i).1) hc htwo

theorem not_mixture : ¬ ActualMixture y μ assignment := by
  intro h
  have he := mixture_forbidden h (⟨(0,2),by decide⟩ : Interval 7) 6 real_forbidden
  norm_num [assignment,numerator] at he
end
end Omega.Turnpike.PrunedFullMixture
