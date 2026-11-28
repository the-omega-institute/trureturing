/- GID: D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstructionProofs
   generality: G
   mirror-B: none(waiver:covered-by-distinct-full-mixture-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A forbidden observation for every real realization -/

module
public import D5.S3.Combinatorics.Turnpike.DistinctFullMixtureData
public import D5.S3.Combinatorics.Turnpike.ActualMixture
public import Mathlib.Order.Interval.Finset.Nat

/-! Omega original.
# A forbidden observation for every real realization

Translation to natural coordinates preserves every interval and its histogram.
Only the bounded integer obstruction is enumerated.
-/
@[expose] public section
namespace Omega.Turnpike.DistinctFullMixture
open Omega.Turnpike
open scoped BigOperators
noncomputable section

def histogram (z : Fin 6 → ℕ) (q : Fin 15) : ℕ :=
  (Finset.univ.filter fun e : Interval 6 => z e.1.2 - z e.1.1 = values q).card

theorem bounded_forbidden :
    ∀ a ∈ Finset.Icc 1 7, ∀ b ∈ Finset.Icc (a+1) 8,
    ∀ d ∈ Finset.Icc (b+8) 16, ∀ f ∈ Finset.Icc (d+1) 17,
    ¬ (histogram ![0,a,b,b+7,d,f] 9 = 1 ∧
       histogram ![0,a,b,b+7,d,f] 10 = 1 ∧
       histogram ![0,a,b,b+7,d,f] 14 = 1 ∧
       histogram ![0,a,b,b+7,d,f] 12 = 1) := by
  decide +kernel

theorem nat_forbidden (z : Fin 6 → ℕ) (hm : StrictMono z)
    (hzero : z 0 = 0) (hb : ∀ i, z i ≤ 17)
    (hc : ∀ q, histogram z q = μ q) : z 3 - z 2 ≠ 7 := by
  intro hgap
  have h01 := hm (show (0 : Fin 6) < 1 by decide)
  have h12 := hm (show (1 : Fin 6) < 2 by decide)
  have h23 := hm (show (2 : Fin 6) < 3 by decide)
  have h34 := hm (show (3 : Fin 6) < 4 by decide)
  have h45 := hm (show (4 : Fin 6) < 5 by decide)
  have h5 := hb 5
  have hthree : z 3 = z 2 + 7 := by omega
  have hz : z = ![0,z 1,z 2,z 2+7,z 4,z 5] := by
    funext i
    fin_cases i <;> simp_all
  apply bounded_forbidden (z 1) (by simp only [Finset.mem_Icc]; omega)
    (z 2) (by simp only [Finset.mem_Icc]; omega)
    (z 4) (by simp only [Finset.mem_Icc]; omega)
    (z 5) (by simp only [Finset.mem_Icc]; omega)
  rw [← hz]
  exact ⟨hc 9,hc 10,hc 14,hc 12⟩

theorem real_forbidden (x : Fin 6 → ℝ) (hx : Realizes y μ x) : x 3 - x 2 ≠ y 8 := by
  classical
  have hi : ∀ i : Fin 6, ∃ k : ℕ, k ≤ 17 ∧ x i - x 0 = (k : ℝ) := by
    intro i
    by_cases h : i = 0
    · subst i; exact ⟨0,by omega,by simp⟩
    · have hpos : (0 : Fin 6) < i := Fin.pos_iff_ne_zero.mpr h
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
  have hd (e : Interval 6) :
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
  have hgap : z 3 - z 2 = 7 := by
    have hd23 := hd (⟨(2,3),by decide⟩ : Interval 6)
    have ht : ((z 3 - z 2 : ℕ) : ℝ) = 7 := by
      norm_num [y,values] at h
      change x 3 - x 2 = ((z 3 - z 2 : ℕ) : ℝ) at hd23
      linarith
    exact_mod_cast ht
  exact nat_forbidden z hmono hzero (fun i => (hz i).1) hc hgap

theorem not_mixture : ¬ ActualMixture y μ assignment := by
  intro h
  have he := mixture_forbidden h (⟨(2,3),by decide⟩ : Interval 6) 8 real_forbidden
  norm_num [assignment,numerator] at he
end
end Omega.Turnpike.DistinctFullMixture
