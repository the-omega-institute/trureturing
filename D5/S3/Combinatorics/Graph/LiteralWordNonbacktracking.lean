/- GID: D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LiteralWordNonbacktracking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian, mathlib/module/Mathlib.Algebra.Group.Basic]
   utility: none
   digest: A literal group-product trace with distinct consecutive involutions excludes immediate walk backtracking. -/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Algebra.Group.Basic

/-! Immediate backtracking is excluded by actual generator labels and a
literal right-action scanl trace; no path, cycle or component is assumed. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.LiteralWordNonbacktracking

universe u v
variable {G : Type u} [Group G] {V : Type v} {F : SimpleGraph V}

theorem trace_length {a b : V} (val : V → G) (w : F.Walk a b) (word : List G)
    (htrace : w.support.map val = List.scanl (fun x r => x * r) (val a) word) :
    w.length = word.length := by
  have h := congrArg List.length htrace
  simp only [List.length_map, SimpleGraph.Walk.length_support, List.length_scanl] at h
  omega

theorem trace_step {a b : V} (val : V → G) (w : F.Walk a b) (word : List G)
    (htrace : w.support.map val = List.scanl (fun x r => x * r) (val a) word)
    (i : ℕ) (hi : i < word.length) :
    val (w.getVert (i + 1)) = val (w.getVert i) * word[i] := by
  have hlen := trace_length val w word htrace
  have hget (j : ℕ) (hj : j ≤ word.length) :
      val (w.getVert j) = (List.scanl (fun x r => x * r) (val a) word)[j]'(by simp; omega) := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem w (by omega)]
    have hop := congrArg (fun l : List G => l[j]?) htrace
    rw [List.getElem?_eq_getElem (l := w.support.map val) (by simp; omega),
      List.getElem?_eq_getElem (l := List.scanl (fun x r => x * r) (val a) word)
        (by simp; omega)] at hop
    simpa only [List.getElem_map] using Option.some.inj hop
  rw [hget (i + 1) (by omega), hget i (by omega), List.getElem_succ_scanl (by simp only [List.length_scanl]; omega)]

theorem trace_nonbacktracking {a b : V} (val : V → G) (w : F.Walk a b) (word : List G)
    (htrace : w.support.map val = List.scanl (fun x r => x * r) (val a) word)
    (hinv : ∀ x ∈ word, x * x = 1)
    (hlabels : ∀ i : ℕ, ∀ hi : i + 1 < word.length,
      word[i] ≠ word[i + 1]) :
    ∀ i, i + 2 ≤ w.length → w.getVert i ≠ w.getVert (i + 2) := by
  have hlen := trace_length val w word htrace
  intro i hi he
  have hi0 : i < word.length := by omega
  have hi1 : i + 1 < word.length := by omega
  have hfirst := trace_step val w word htrace i hi0
  have hsecond := trace_step val w word htrace (i + 1) hi1
  have hv := congrArg val he
  rw [show i + 2 = (i + 1) + 1 by omega, hsecond, hfirst] at hv
  have hprod : word[i] * word[i + 1] = 1 := mul_left_cancel (by
    simpa only [mul_assoc, mul_one] using hv.symm)
  have hy := hinv word[i + 1] (List.getElem_mem hi1)
  have hxy := congrArg (fun x => x * word[i + 1]) hprod
  have heq : word[i] = word[i + 1] := by
    simpa only [mul_assoc, hy, mul_one, one_mul] using hxy
  exact hlabels i hi1 heq

#print axioms trace_length
#print axioms trace_step
#print axioms trace_nonbacktracking
end D5.S3.Combinatorics.Graph.LiteralWordNonbacktracking
