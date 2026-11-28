import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! Two four-step paths with opposite signed products cannot both lie in a
Huang-balanced cube support. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SignedEightCycle

open BalancedCriticalSpectrum (Q flip gamma IsBalanced)
open BalancedCubeGirth (flip_comm gamma_anticommute)
open TwentyPointEightWord (wordGamma gamma_square word_switching)

private theorem conjugate_pair {n : Nat} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (f : Q n → ℝ) : gamma a (gamma b (gamma c (gamma a f))) = gamma b (gamma c f) := by
  rw [gamma_anticommute hab (gamma c (gamma a f)), gamma_anticommute hac (gamma a f),
    gamma_square, map_neg, neg_neg]

/-- The paths `a,b,c,a` and `d,c,b,d` to the same two-axis translate
have opposite signed products. They cannot both be selected. -/
theorem no_selected_eight_paths {n : Nat} {S : Finset (Q n)} (hS : IsBalanced S)
    (x : Q n) {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdb : d ≠ b) (hdc : d ≠ c)
    (ha : ∀ y ∈ [a, b, c, a].scanl flip x, y ∈ S)
    (hd : ∀ y ∈ [d, c, b, d].scanl flip x, y ∈ S) : False := by
  obtain ⟨sigma, hs⟩ := hS
  have hend (p q r : Fin n) :
      flip (flip (flip (flip x p) q) r) p = flip (flip x q) r := by
    rw [flip_comm x p q, flip_comm (flip x q) p r, BalancedCriticalSpectrum.flip_flip]
  have hleft := word_switching hs x [a, b, c, a] ha
  have hright := word_switching hs x [d, c, b, d] hd
  simp only [List.foldl_cons, List.foldl_nil, hend, wordGamma, List.foldr_cons,
    List.foldr_nil, conjugate_pair hab hac, conjugate_pair hdc hdb] at hleft hright
  rw [flip_comm x c b] at hright
  have hnegative := congrFun (gamma_anticommute hbc.symm (fun _ : Q n => (1 : ℝ))) x
  simp only [Pi.neg_apply, hleft, hright] at hnegative
  have hstart : x ∈ S := ha x (by simp [List.scanl_cons])
  have hfinish : flip (flip x b) c ∈ S := by
    rw [← hend a b c]
    apply ha
    simp [List.scanl_cons, List.scanl_nil]
  rcases hs.1 x hstart with h | h <;>
    rcases hs.1 _ hfinish with k | k <;>
    norm_num [h, k] at hnegative

#print axioms no_selected_eight_paths

end D5.S3.Combinatorics.Graph.HypercubeCritical.SignedEightCycle
