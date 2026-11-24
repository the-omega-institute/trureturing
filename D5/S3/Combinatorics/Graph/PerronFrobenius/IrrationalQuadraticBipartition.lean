/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Charpoly]
   utility: none
   digest: An irrational Perron value with rational square forces weight-preserving symmetries to preserve the bipartition. -/

import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Lemmas

/-! An irrational Perron value with rational square forces every weight-preserving graph symmetry
to act within the two color classes. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition

open Polynomial
open scoped BigOperators Matrix

/-- A rational polynomial vanishing at an irrational square root also vanishes at its negative. -/
private theorem eval₂_neg_eq_zero_of_sq_rat {x : ℝ} {d : ℚ} (hx : Irrational x)
    (hsq : x ^ 2 = (d : ℝ)) {p : ℚ[X]} (hp : p.eval₂ (algebraMap ℚ ℝ) x = 0) :
    p.eval₂ (algebraMap ℚ ℝ) (-x) = 0 := by
  let q : ℚ[X] := X ^ 2 - C d
  have hmonic : q.Monic := monic_X_pow_sub_C d (by decide)
  have hdeg : q.natDegree = 2 := natDegree_X_pow_sub_C
  have hq : q ≠ 1 := by
    intro h
    simp [h] at hdeg
  have hrem : (p %ₘ q).natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt p hmonic hq
    omega
  obtain ⟨a, b, hr⟩ := exists_eq_X_add_C_of_natDegree_le_one hrem
  have heval {t : ℝ} (ht : t ^ 2 = (d : ℝ)) :
      p.eval₂ (algebraMap ℚ ℝ) t = (a : ℝ) * t + (b : ℝ) := by
    have hq_eval : q.eval₂ (algebraMap ℚ ℝ) t = 0 := by
      change (X ^ 2 - C d : ℚ[X]).eval₂ (algebraMap ℚ ℝ) t = 0
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      exact sub_eq_zero.mpr ht
    calc
      _ = (p %ₘ q + q * (p /ₘ q)).eval₂ (algebraMap ℚ ℝ) t :=
        congrArg (fun f : ℚ[X] => f.eval₂ (algebraMap ℚ ℝ) t) (modByMonic_add_div p q).symm
      _ = _ := by
        simp only [hr, eval₂_add, eval₂_mul, hq_eval, zero_mul, add_zero, eval₂_C, eval₂_X]
        rfl
  have hab : (a : ℝ) * x + (b : ℝ) = 0 := (heval hsq).symm.trans hp
  have ha : a = 0 := by
    by_contra ha
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    refine hx ⟨-b / a, ?_⟩
    push_cast
    apply (div_eq_iff ha').2
    rw [mul_comm x (a : ℝ)]
    linarith only [hab]
  have hb : (b : ℝ) = 0 := by simpa [ha] using hab
  simpa [ha, hb] using heval (t := -x) (by simpa only [neg_sq] using hsq)

variable {ι : Type*} [Fintype ι]

/-- Rational matrices have both signs of an irrational quadratic eigenvalue over ℝ. -/
private theorem hasEigenvalue_neg_of_sq_rat [DecidableEq ι] (A : Matrix ι ι ℚ)
    {x : ℝ} {d : ℚ} (hx : Irrational x) (hsq : x ^ 2 = (d : ℝ))
    (h : Module.End.HasEigenvalue (A.map (algebraMap ℚ ℝ)).toLin' x) :
    Module.End.HasEigenvalue (A.map (algebraMap ℚ ℝ)).toLin' (-x) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at h ⊢
  simp only [Matrix.charpoly_toLin', Matrix.charpoly_map, IsRoot, eval_map] at h ⊢
  exact eval₂_neg_eq_zero_of_sq_rat hx hsq h

/-- Opposite eigenvalues with a strictly positive eigenvector at one sign exclude odd closed
walks. The positive-entry quiver includes diagonal edges. -/
private theorem no_odd_closed_walk_of_opposite_eigenvectors {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hSymm : A.IsSymm) {ρ : ℝ} {u v : ι → ℝ}
    (hu_pos : ∀ i, 0 < u i) (hv_ne : v ≠ 0)
    (hu : A *ᵥ u = ρ • u) (hv : A *ᵥ v = (-ρ) • v)
    {i : ι} (p : @Quiver.Path ι A.toQuiver i i) :
    ¬ Odd (@Quiver.Path.length ι A.toQuiver i i p) := by
  classical
  let : Quiver ι := A.toQuiver
  let ratio (j : ι) : ℝ := v j / u j
  let weight (j k : ι) : ℝ := A j k * u j * u k
  let term (j k : ι) : ℝ := weight j k * (ratio j + ratio k)
  have hratio (j : ι) : u j * ratio j = v j := by
    change u j * (v j / u j) = v j
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hu_pos j))]
  have hrow (j : ι) : (∑ k, term j k) = 0 := by
    have hu_row : (∑ k, A j k * u k) = ρ * u j := by
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hu j
    have hv_row : (∑ k, A j k * v k) = -ρ * v j := by
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hv j
    calc
      _ = u j * (ratio j * (∑ k, A j k * u k) + ∑ k, A j k * v k) := by
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hratio k]
        dsimp only [term, weight]
        ring
      _ = 0 := by rw [hu_row, hv_row, ← hratio j]; ring
  have hterm (j k : ι) : term j k = term k j := by
    dsimp only [term, weight]
    rw [hSymm.apply j k]
    ring
  have hleft : (∑ j, ∑ k, ratio j * term j k) = 0 := by
    simp only [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  have hright : (∑ j, ∑ k, ratio k * term j k) = 0 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ k, ratio j * term j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
          congrArg (fun t => ratio j * t) (hterm k j)
      _ = 0 := hleft
  -- The sum of weighted squares is zero by the two eigenvector equations.
  let energy (j k : ι) : ℝ := weight j k * (ratio j + ratio k) ^ 2
  have henergy : (∑ j, ∑ k, energy j k) = 0 := by
    calc
      _ = ∑ j, ∑ k, (ratio j * term j k + ratio k * term j k) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        dsimp only [energy, term]
        ring
      _ = 0 := by simp only [Finset.sum_add_distrib, hleft, hright, add_zero]
  have hnonneg (j k : ι) : 0 ≤ energy j k :=
    mul_nonneg (mul_nonneg (mul_nonneg (hA.nonneg j k) (hu_pos j).le) (hu_pos k).le)
      (sq_nonneg _)
  have hedge {j k : ι} (hjk : 0 < A j k) : ratio k = -ratio j := by
    have hj := Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
      (fun j => Finset.sum_nonneg fun k _ => hnonneg j k) henergy j
    have hzero := Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg (hnonneg j) hj k
    change weight j k * (ratio j + ratio k) ^ 2 = 0 at hzero
    have hw : 0 < weight j k := mul_pos (mul_pos hjk (hu_pos j)) (hu_pos k)
    have hs := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hw)
    have hsum := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hs
    linarith only [hsum]
  have hwalk {a b : ι} (q : Quiver.Path a b) :
      ratio b = (-1 : ℝ) ^ q.length * ratio a := by
    induction q with
    | nil => simp
    | @cons j k q edge ih =>
      calc
        ratio k = -ratio j := hedge edge.down
        _ = (-1 : ℝ) ^ (q.cons edge).length * ratio a := by
          rw [ih, Quiver.Path.length_cons, pow_succ]
          ring
  intro hp
  have hri : ratio i ≠ 0 := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      apply hv_ne
      exact funext fun j => h j
    obtain ⟨q, _⟩ := hA.connected j i
    rw [hwalk q]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (div_ne_zero hj (ne_of_gt (hu_pos j)))
  have heq := hwalk p
  rw [hp.neg_one_pow, neg_one_mul] at heq
  exact hri (by linarith only [heq])

private theorem no_odd_closed_walk_of_irrational_square (A : Matrix ι ι ℚ)
    (hA : (A.map (algebraMap ℚ ℝ)).IsIrreducible)
    (hSymm : (A.map (algebraMap ℚ ℝ)).IsSymm) {ρ : ℝ} {d : ℚ}
    (hρ : Irrational ρ) (hsq : ρ ^ 2 = (d : ℝ)) {u : ι → ℝ}
    (hu_pos : ∀ j, 0 < u j) (hu : A.map (algebraMap ℚ ℝ) *ᵥ u = ρ • u)
    {i : ι} (p : @Quiver.Path ι (A.map (algebraMap ℚ ℝ)).toQuiver i i) :
    ¬ Odd (@Quiver.Path.length ι (A.map (algebraMap ℚ ℝ)).toQuiver i i p) := by
  classical
  let : Nonempty ι := ⟨i⟩
  let B := A.map (algebraMap ℚ ℝ)
  have hpos : Module.End.HasEigenvalue B.toLin' ρ :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := u) <|
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by simpa only [Matrix.toLin'_apply] using hu),
          Pi.ne_zero_of_pos hu_pos⟩
  obtain ⟨v, hv⟩ := (hasEigenvalue_neg_of_sq_rat A hρ hsq hpos).exists_hasEigenvector
  exact no_odd_closed_walk_of_opposite_eigenvectors hA hSymm hu_pos
    (Module.End.hasEigenvector_iff.mp hv).2 hu
    (by simpa only [Matrix.toLin'_apply] using hv.apply_eq_smul) p

/-- An entry-preserving permutation fixes a strictly positive eigenvector of an
irreducible nonnegative matrix. -/
private theorem positive_eigenvector_fixed_by_perm {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j)
    {ρ : ℝ} {u : ι → ℝ} (hu_pos : ∀ i, 0 < u i) (hu : A *ᵥ u = ρ • u) :
    ∀ x, u (p x) = u x := by
  classical
  intro x
  let v : ι → ℝ := fun j => u (p j)
  have hv : A *ᵥ v = ρ • v := by
    funext i
    change (∑ j, A i j * u (p j)) = ρ * u (p i)
    calc
      _ = ∑ j, A (p i) (p j) * u (p j) := by
        exact Finset.sum_congr rfl fun j _ => by rw [hp i j]
      _ = ∑ j, A (p i) j * u j := Equiv.sum_comp p (fun j => A (p i) j * u j)
      _ = _ := by
        simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
          congrFun hu (p i)
  obtain ⟨m, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun j => v j / u j) ⟨x, Finset.mem_univ x⟩
  let c : ℝ := v m / u m
  let δ : ι → ℝ := c • u - v
  have hδ_nonneg (j : ι) : 0 ≤ δ j := by
    change 0 ≤ c * u j - v j
    exact sub_nonneg.mpr ((div_le_iff₀ (hu_pos j)).mp (hmax j (Finset.mem_univ j)))
  have hδ_max : δ m = 0 := by
    change (v m / u m) * u m - v m = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hu_pos m)), sub_self]
  have hδ_eig : A *ᵥ δ = ρ • δ := by
    change A *ᵥ (c • u - v) = ρ • (c • u - v)
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hu, hv]
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- The nonnegative defect vanishes at a maximizer and propagates along every edge.
  have hδ_edge {i j : ι} (hij : 0 < A i j) (hi : δ i = 0) : δ j = 0 := by
    have hsum : (∑ k, A i k * δ k) = 0 := by
      calc
        _ = ρ * δ i := by
          simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
            congrFun hδ_eig i
        _ = 0 := by rw [hi, mul_zero]
    have hz := Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
      (fun k => mul_nonneg (hA.nonneg i k) (hδ_nonneg k)) hsum j
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hij)
  let : Quiver ι := A.toQuiver
  have hδ_path {j : ι} (q : Quiver.Path m j) : δ j = 0 := by
    induction q with
    | nil => exact hδ_max
    | cons q edge ih => exact hδ_edge edge.down ih
  have hscale (j : ι) : v j = c * u j := by
    obtain ⟨q, _⟩ := hA.connected m j
    have hz : c * u j - v j = 0 := hδ_path q
    exact (sub_eq_zero.mp hz).symm
  -- The permutation preserves the total mass, which fixes the scale.
  have hsum_pos : 0 < ∑ j, u j :=
    Finset.sum_pos' (fun j _ => (hu_pos j).le) ⟨x, Finset.mem_univ x, hu_pos x⟩
  have hsum_scale : (∑ j, u j) = c * ∑ j, u j := by
    calc
      _ = ∑ j, v j := (Equiv.sum_comp p u).symm
      _ = ∑ j, c * u j := Finset.sum_congr rfl fun j _ => hscale j
      _ = _ := by rw [Finset.mul_sum]
  have hc : c = 1 := by
    apply mul_right_cancel₀ (ne_of_gt hsum_pos)
    simpa only [one_mul] using hsum_scale.symm
  simpa only [hc, one_mul] using hscale x

/-- Under the quadratic spectral hypothesis every path from a vertex to its image
under an entry-preserving permutation has even length. -/
private theorem no_odd_path_to_perm (A : Matrix ι ι ℚ)
    (hA : (A.map (algebraMap ℚ ℝ)).IsIrreducible)
    (hSymm : (A.map (algebraMap ℚ ℝ)).IsSymm)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j)
    {ρ : ℝ} {d : ℚ} (hρ : Irrational ρ) (hsq : ρ ^ 2 = (d : ℝ))
    {u : ι → ℝ} (hu_pos : ∀ i, 0 < u i) (hu : A.map (algebraMap ℚ ℝ) *ᵥ u = ρ • u)
    {x : ι} (q : @Quiver.Path ι (A.map (algebraMap ℚ ℝ)).toQuiver x (p x)) :
    ¬ Odd (@Quiver.Path.length ι (A.map (algebraMap ℚ ℝ)).toQuiver x (p x) q) := by
  classical
  let R := A.map (algebraMap ℚ ℝ)
  let B : Matrix ι ι ℚ := fun i j => A i j + A i (p j) + A (p i) j
  let S := B.map (algebraMap ℚ ℝ)
  have hentry (i j : ι) : S i j = R i j + R i (p j) + R (p i) j := by
    change (algebraMap ℚ ℝ) (A i j + A i (p j) + A (p i) j) = _
    simp only [map_add]
    rfl
  have hS_symm : S.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [hentry]
    have hs (a b : ι) : R b a = R a b := hSymm.apply a b
    rw [hs i j, hs (p i) j, hs (p j) i]
    ring
  have hkeep {i j : ι} (hij : 0 < R i j) : 0 < S i j := by
    rw [hentry]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hij (hA.nonneg i (p j))) (hA.nonneg (p i) j)
  have hredirect {i j : ι} (hij : 0 < R i (p j)) : 0 < S i j := by
    rw [hentry]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (hA.nonneg i j) hij) (hA.nonneg (p i) j)
  let : Quiver ι := R.toQuiver
  have hS : S.IsIrreducible := by
    constructor
    · intro i j
      rw [hentry]
      exact add_nonneg (add_nonneg (hA.nonneg i j) (hA.nonneg i (p j))) (hA.nonneg (p i) j)
    · intro i j
      obtain ⟨path, hpath⟩ := hA.connected i j
      obtain ⟨lifted, hlength⟩ := Matrix.pathToQuiverOfForallPosImpPos (A := R) (B := S)
        (fun {_ _} hij => hkeep hij) path
      exact ⟨lifted, by simpa only [hlength.down] using hpath⟩
  have hinv : ∀ i, u (p i) = u i :=
    positive_eigenvector_fixed_by_perm (A := R) hA p
      (fun i j => congrArg (algebraMap ℚ ℝ) (hp i j)) hu_pos hu
  have hrow (i : ι) : (∑ j, R i j * u j) = ρ * u i := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hu i
  have hcol (i : ι) : (∑ j, R i (p j) * u j) = ρ * u i := by
    calc
      _ = ∑ j, R i (p j) * u (p j) := Finset.sum_congr rfl fun j _ => by rw [hinv j]
      _ = ∑ j, R i j * u j := Equiv.sum_comp p (fun j => R i j * u j)
      _ = _ := hrow i
  have hS_eig : S *ᵥ u = (3 * ρ) • u := by
    funext i
    change (∑ j, S i j * u j) = (3 * ρ) * u i
    simp only [hentry, add_mul, Finset.sum_add_distrib, hcol, hrow, hinv]
    ring
  have hscaled_irr : Irrational (3 * ρ) := by
    simpa using hρ.natCast_mul (by decide : (3 : ℕ) ≠ 0)
  have hscaled_sq : (3 * ρ) ^ 2 = ((9 * d : ℚ) : ℝ) := by
    calc
      (3 * ρ) ^ 2 = 9 * ρ ^ 2 := by ring
      _ = ((9 * d : ℚ) : ℝ) := by rw [hsq, Rat.cast_mul] <;> norm_num
  intro hodd
  have hlen : 0 < q.length := Nat.pos_of_ne_zero fun hz => Nat.not_odd_zero (hz ▸ hodd)
  obtain ⟨j, initPath, edge, rfl⟩ := Quiver.Path.path_decomposition_last_edge q hlen
  obtain ⟨lifted, hlifted⟩ := Matrix.pathToQuiverOfForallPosImpPos (A := R) (B := S)
    (fun {_ _} hij => hkeep hij) initPath
  -- The translated column sends the last edge from `j` back to `x`.
  let closed : @Quiver.Path ι S.toQuiver x x :=
    @Quiver.Path.cons ι S.toQuiver x j x lifted ⟨hredirect (i := j) (j := x) edge.down⟩
  have hclosed : Odd (@Quiver.Path.length ι S.toQuiver x x closed) := by
    simpa only [closed, Quiver.Path.length_cons, hlifted.down] using hodd
  exact no_odd_closed_walk_of_irrational_square B hS hS_symm hscaled_irr hscaled_sq hu_pos hS_eig closed
    hclosed

/-- An entry-preserving permutation fixes the color of every vertex in a bipartition. -/
theorem preserves_bipartition_of_sq_rat (A : Matrix ι ι ℚ)
    (hA : (A.map (algebraMap ℚ ℝ)).IsIrreducible)
    (hSymm : (A.map (algebraMap ℚ ℝ)).IsSymm)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j)
    {ρ : ℝ} {d : ℚ} (hρ : Irrational ρ) (hsq : ρ ^ 2 = (d : ℝ))
    {u : ι → ℝ} (hu_pos : ∀ i, 0 < u i) (hu : A.map (algebraMap ℚ ℝ) *ᵥ u = ρ • u)
    (color : ι → Bool)
    (hcolor : ∀ {i j : ι}, 0 < (A.map (algebraMap ℚ ℝ)) i j → color j = !color i) :
    ∀ x, color (p x) = color x := by
  intro x
  let : Quiver ι := (A.map (algebraMap ℚ ℝ)).toQuiver
  have hwalk {y : ι} (q : Quiver.Path x y) :
      color y = (Bool.not^[q.length]) (color x) := by
    induction q with
    | nil => rfl
    | cons q edge ih =>
      rw [Quiver.Path.length_cons, Function.iterate_succ_apply', ← ih]
      exact hcolor edge.down
  rcases hA.connected x (p x) with ⟨q, _⟩
  have heven : Even q.length := Nat.not_odd_iff_even.mp
    (no_odd_path_to_perm A hA hSymm p hp hρ hsq hu_pos hu q)
  simpa only [Bool.involutive_not.iterate_even heven, id_eq] using hwalk q

#print axioms preserves_bipartition_of_sq_rat

end D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition
