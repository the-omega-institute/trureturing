/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/JInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/JInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite left inverses of the same-sign and mixed-sign J polynomials. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JointSeries

noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite

def jStencil (same : Bool) (X : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  if same then 2 * (shift 2 0 X p q - 2 * shift 1 1 X p q + shift 0 2 X p q)
  else 2 * (X p q - 2 * shift 1 1 X p q + shift 2 2 X p q)

def jInverse (same : Bool) (S : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  if same then (1 / 2 : ℂ) * ∑ n ∈ Finset.range (q + 1),
    (n + 1 : ℂ) * S (p+n+2) (q-n)
  else (1 / 2 : ℂ) * ∑ n ∈ Finset.range (min p q + 1),
    (n + 1 : ℂ) * S (p-n) (q-n)

private lemma telescope (f : ℕ → ℂ) (q : ℕ) :
    (∑ n ∈ Finset.range (q+1), (n+1 : ℂ) * (f n - 2*f (n+1) + f (n+2))) =
      f 0 - (q+2 : ℂ)*f (q+1) + (q+1 : ℂ)*f (q+2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- A left inverse on actual produced coefficients, with no arbitrary-S existence claim. -/
theorem jInverse_stencil (same : Bool) (X : ℕ → ℕ → ℂ) (p q : ℕ) :
    jInverse same (jStencil same X) p q = X p q := by
  cases same
  · let M := min p q
    let f : ℕ → ℂ := fun n => if n ≤ M then X (p-n) (q-n) else 0
    have he (n : ℕ) (hn : n ∈ Finset.range (M+1)) :
        jStencil false X (p-n) (q-n) = 2*(f n - 2*f (n+1) + f (n+2)) := by
      have hn' : n ≤ M := by simpa using Finset.mem_range.mp hn
      have hp : n ≤ p := hn'.trans (min_le_left _ _)
      have hq : n ≤ q := hn'.trans (min_le_right _ _)
      have hk (k : ℕ) : shift k k X (p-n) (q-n) = f (n+k) := by
        by_cases hh : n+k ≤ M
        · have hg : k ≤ p-n ∧ k ≤ q-n := by dsimp [M] at *; omega
          simp only [shift, if_pos hg, f, if_pos hh]
          congr 1 <;> omega
        · have hg : ¬(k ≤ p-n ∧ k ≤ q-n) := by dsimp [M] at *; omega
          simp only [shift, if_neg hg, f, if_neg hh]
      have h0 : X (p-n) (q-n) = f n := by simp only [f, if_pos hn']
      simp only [jStencil, Bool.false_eq_true, ite_false, h0, hk]
    unfold jInverse
    simp only [Bool.false_eq_true, ite_false]
    change (1 / 2 : ℂ) * (∑ n ∈ Finset.range (M+1), (n+1 : ℂ) *
      jStencil false X (p-n) (q-n)) = _
    have hs : (∑ n ∈ Finset.range (M+1), (n+1 : ℂ)*jStencil false X (p-n) (q-n)) =
        2 * (∑ n ∈ Finset.range (M+1), (n+1 : ℂ)*(f n - 2*f (n+1) + f (n+2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn]
      ring
    rw [hs, telescope]
    simp [f]
  · let f : ℕ → ℂ := fun n => if n ≤ q then X (p+n) (q-n) else 0
    have he (n : ℕ) (hn : n ∈ Finset.range (q+1)) :
        jStencil true X (p+n+2) (q-n) = 2*(f n - 2*f (n+1) + f (n+2)) := by
      have hn' : n ≤ q := by have := Finset.mem_range.mp hn; omega
      have hk (k : ℕ) (hk : k ≤ 2) : shift (2-k) k X (p+n+2) (q-n) = f (n+k) := by
        by_cases hh : n+k ≤ q
        · have hg : 2-k ≤ p+n+2 ∧ k ≤ q-n := by omega
          simp only [shift, if_pos hg, f, if_pos hh]
          congr 1 <;> omega
        · have hg : ¬(2-k ≤ p+n+2 ∧ k ≤ q-n) := by omega
          simp only [shift, if_neg hg, f, if_neg hh]
      have h0 := hk 0 (by omega)
      have h1 := hk 1 (by omega)
      have h2 := hk 2 (by omega)
      norm_num only [Nat.sub_self, Nat.reduceSub, add_zero] at h0 h1 h2
      simp only [jStencil, ite_true, h0, h1, h2]
    unfold jInverse
    simp only [ite_true]
    have hs : (∑ n ∈ Finset.range (q+1), (n+1 : ℂ)*jStencil true X (p+n+2) (q-n)) =
        2 * (∑ n ∈ Finset.range (q+1), (n+1 : ℂ)*(f n - 2*f (n+1) + f (n+2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn]
      ring
    rw [hs, telescope]
    simp [f]

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
