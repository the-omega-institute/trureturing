/- GID: D5/S3/Combinatorics/Graph/HypercubeSubQuorum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeSubQuorum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The exact sub-quorum chromatic maximum of Boolean cubes in dimensions at least two. -/

import D5.S3.Combinatorics.Graph.Hypercube
import Archive.Sensitivity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube

/-- FromLiterature: Huang's recursively signed cube adjacency operator, kept private here. -/
private noncomputable def huangMatrix (n : Nat) :
    Matrix (Fin n -> Bool) (Fin n -> Bool) Real :=
  fun x y => Sensitivity.ε x (Sensitivity.f n (Sensitivity.e y))

set_option backward.isDefEq.respectTransparency false in
private theorem huangMatrix_symmetric {n : Nat} (x y : Fin n -> Bool) :
    huangMatrix n x y = huangMatrix n y x := by
  induction n with
  | zero =>
      simp [huangMatrix, Sensitivity.f, Sensitivity.e, Sensitivity.ε]
  | succ n ih =>
      dsimp only [huangMatrix, Sensitivity.e, Sensitivity.ε, Sensitivity.f, Sensitivity.V]
      rw [LinearMap.prod_apply]
      dsimp
      cases hx : x 0 <;> cases hy : y 0
      all_goals
        repeat rw [Bool.cond_true]
        repeat rw [Bool.cond_false]
      · simpa [huangMatrix] using ih (Sensitivity.π x) (Sensitivity.π y)
      · simp [Sensitivity.duality, eq_comm]
      · simp [Sensitivity.duality, eq_comm]
      · simpa [huangMatrix] using ih (Sensitivity.π x) (Sensitivity.π y)

private theorem huang_energy (n : Nat) (x : (Fin n -> Bool) -> Real) :
    ∑ v, (Matrix.mulVec (huangMatrix n) x v) ^ 2 =
      n * ∑ v, (x v) ^ 2 := by
  have hcoeff (v : Sensitivity.V n) :
      v = ∑ q : Sensitivity.Q n, (Sensitivity.ε q v) • Sensitivity.e q := by
    rw [← sub_eq_zero]
    apply Sensitivity.epsilon_total
    intro p
    simp [Sensitivity.duality]
  have hmulVec (v : Sensitivity.V n) :
      Matrix.mulVec (huangMatrix n) (fun q => Sensitivity.ε q v) =
        fun p => Sensitivity.ε p (Sensitivity.f n v) := by
    funext p
    rw [Matrix.mulVec, dotProduct]
    calc
      ∑ q, huangMatrix n p q * Sensitivity.ε q v =
          Sensitivity.ε p (Sensitivity.f n
            (∑ q, Sensitivity.ε q v • Sensitivity.e q)) := by
              simp [huangMatrix, map_sum, mul_comm]
      _ = Sensitivity.ε p (Sensitivity.f n v) := by rw [← hcoeff v]
  have hsquare :
      Matrix.mulVec (huangMatrix n) (Matrix.mulVec (huangMatrix n) x) = n • x := by
    let v : Sensitivity.V n :=
      ∑ q : Sensitivity.Q n, x q • Sensitivity.e q
    have hv (q : Sensitivity.Q n) : Sensitivity.ε q v = x q := by
      simp [v, Sensitivity.duality]
    rw [show x = fun q => Sensitivity.ε q v from funext fun q => (hv q).symm]
    rw [hmulVec, hmulVec]
    funext q
    rw [Sensitivity.f_squared]
    simp
  let y := Matrix.mulVec (huangMatrix n) x
  calc
    ∑ v, (Matrix.mulVec (huangMatrix n) x v) ^ 2 = y ⬝ᵥ y := by
      simp [y, dotProduct, pow_two]
    _ = Matrix.vecMul y (huangMatrix n) ⬝ᵥ x :=
      Matrix.dotProduct_mulVec y (huangMatrix n) x
    _ = Matrix.mulVec (huangMatrix n) y ⬝ᵥ x := by
      rw [show Matrix.vecMul y (huangMatrix n) =
          Matrix.mulVec (huangMatrix n) y by
        funext v
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro w _
        rw [huangMatrix_symmetric]
        ring]
    _ = (n • x) ⬝ᵥ x := by
      rw [show Matrix.mulVec (huangMatrix n) y = n • x by
        simpa [y] using hsquare]
    _ = n * ∑ v, (x v) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp [pow_two]
      ring

private noncomputable def extendByZero {n : Nat} (T : Finset (Fin n -> Bool))
    (x : T -> Real) : (Fin n -> Bool) -> Real :=
  fun v => if hv : v ∈ T then x ⟨v, hv⟩ else 0

private noncomputable def boundaryMatrix (n : Nat)
    (T A : Finset (Fin n -> Bool)) :
    Matrix {v // v ∈ Finset.univ \ A} T Real :=
  fun b t => huangMatrix n b t

private theorem huang_row_bound {n : Nat} (T : Finset (Fin n -> Bool))
    (x : T -> Real) (a : Fin n -> Bool) :
    (Matrix.mulVec (huangMatrix n) (extendByZero T x) a) ^ 2 ≤
      (((hypercube n).neighborFinset a ∩ T).card : Real) *
        ∑ v ∈ (hypercube n).neighborFinset a ∩ T, (extendByZero T x v) ^ 2 := by
  let N := (hypercube n).neighborFinset a ∩ T
  have hsupp (v : Fin n -> Bool) :
      |huangMatrix n a v| = if (hypercube n).Adj a v then 1 else 0 := by
    change |Sensitivity.ε a (Sensitivity.f n (Sensitivity.e v))| = _
    rw [Sensitivity.f_matrix v a]
    rw [show v ∈ Sensitivity.Q.adjacent a ↔ (hypercube n).Adj a v by
      change (∃! i, a i ≠ v i) ↔
        (Finset.univ.filter (fun i => a i ≠ v i)).card = 1
      rw [Finset.card_eq_one]
      constructor
      · rintro ⟨i, hi, hunique⟩
        refine ⟨i, Finset.ext fun j => ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hunique j, fun h => h ▸ hi⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_, ?_⟩
        · have := Finset.ext_iff.mp hi i
          simpa using this.symm
        · intro j hj
          have := Finset.ext_iff.mp hi j
          simpa [hj] using this]
  have hsum : Matrix.mulVec (huangMatrix n) (extendByZero T x) a =
      ∑ v ∈ N, huangMatrix n a v * extendByZero T x v := by
    rw [Matrix.mulVec, dotProduct]
    symm
    apply Finset.sum_subset (Finset.subset_univ N)
    intro v _ hvN
    by_cases hvT : v ∈ T
    · have hnadj : ¬ (hypercube n).Adj a v := by
        intro hadj
        exact hvN (by simp [N, SimpleGraph.mem_neighborFinset, hadj, hvT])
      have hz : huangMatrix n a v = 0 := by
        have hs := hsupp v
        rw [if_neg hnadj] at hs
        simpa using (abs_eq_zero.mp hs)
      simp [hz]
    · simp [extendByZero, hvT]
  rw [hsum]
  calc
    (∑ v ∈ N, huangMatrix n a v * extendByZero T x v) ^ 2 ≤
        (N.card : Real) * ∑ v ∈ N,
          (huangMatrix n a v * extendByZero T x v) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (N.card : Real) * ∑ v ∈ N, (extendByZero T x v) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      have hadj : (hypercube n).Adj a v := by
        have hv' : (hypercube n).Adj a v ∧ v ∈ T := by
          simpa [N, SimpleGraph.mem_neighborFinset] using hv
        exact hv'.1
      have hs := hsupp v
      rw [if_pos hadj] at hs
      have hsq := congrArg (fun r : Real => r ^ 2) hs
      have hm : (huangMatrix n a v) ^ 2 = 1 := by
        simpa [sq_abs] using hsq
      rw [mul_pow, hm, one_mul]

private theorem huang_energy_on_A {n : Nat} (T A : Finset (Fin n -> Bool))
    (x : T -> Real)
    (hrow : ∀ a ∈ A,
      ((hypercube n).neighborFinset a ∩ T).card ≤ n - 1)
    (hcol : ∀ t ∈ T,
      ((hypercube n).neighborFinset t ∩ A).card ≤ 1) :
    ∑ a ∈ A, (Matrix.mulVec (huangMatrix n) (extendByZero T x) a) ^ 2 ≤
      (n - 1 : Nat) * ∑ t : T, (x t) ^ 2 := by
  calc
    ∑ a ∈ A, (Matrix.mulVec (huangMatrix n) (extendByZero T x) a) ^ 2 ≤
        ∑ a ∈ A, (n - 1 : Nat) *
          ∑ t ∈ (hypercube n).neighborFinset a ∩ T,
            (extendByZero T x t) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      refine (huang_row_bound T x a).trans ?_
      gcongr
      exact_mod_cast hrow a ha
    _ = (n - 1 : Nat) * ∑ t ∈ T,
        (((hypercube n).neighborFinset t ∩ A).card : Real) *
          (extendByZero T x t) ^ 2 := by
      have hdouble :
        ∑ a ∈ A, ∑ t ∈ (hypercube n).neighborFinset a ∩ T,
            (extendByZero T x t) ^ 2 =
          ∑ t ∈ T,
            (((hypercube n).neighborFinset t ∩ A).card : Real) *
              (extendByZero T x t) ^ 2 := by
        calc
          ∑ a ∈ A, ∑ t ∈ (hypercube n).neighborFinset a ∩ T,
              (extendByZero T x t) ^ 2 =
              ∑ a ∈ A, ∑ t ∈ T,
              if (hypercube n).Adj a t then (extendByZero T x t) ^ 2 else 0 := by
                apply Finset.sum_congr rfl
                intro a _
                rw [← Finset.sum_filter]
                apply Finset.sum_congr
                · ext t
                  simp [SimpleGraph.mem_neighborFinset, and_comm]
                · simp
          _ = ∑ t ∈ T, ∑ a ∈ A,
              if (hypercube n).Adj t a then (extendByZero T x t) ^ 2 else 0 := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro t _
                apply Finset.sum_congr rfl
                intro a _
                rw [(hypercube n).adj_comm]
          _ = ∑ t ∈ T,
            (((hypercube n).neighborFinset t ∩ A).card : Real) *
              (extendByZero T x t) ^ 2 := by
                apply Finset.sum_congr rfl
                intro t _
                rw [← Finset.sum_filter]
                have hf : A.filter (fun a => (hypercube n).Adj t a) =
                    (hypercube n).neighborFinset t ∩ A := by
                  ext a
                  simp [SimpleGraph.mem_neighborFinset, and_comm]
                rw [hf]
                simp [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum, hdouble, Finset.mul_sum]
    _ ≤ (n - 1 : Nat) * ∑ t ∈ T, (extendByZero T x t) ^ 2 := by
      gcongr with t ht
      have hc := hcol t ht
      have hc' : (((hypercube n).neighborFinset t ∩ A).card : Real) ≤ 1 := by
        exact_mod_cast hc
      nlinarith [sq_nonneg (extendByZero T x t)]
    _ = (n - 1 : Nat) * ∑ t : T, (x t) ^ 2 := by
      congr 1
      calc
        ∑ t ∈ T, (extendByZero T x t) ^ 2 =
            ∑ t : T, (extendByZero T x t) ^ 2 :=
          Finset.sum_subtype T (by simp) _
        _ = ∑ t : T, (x t) ^ 2 := by
          apply Finset.sum_congr rfl
          intro t _
          simp [extendByZero]

private theorem feasible_core_card_le_compl
    (n : Nat) (hn : 2 ≤ n)
    (T A : Finset (Fin n -> Bool))
    (hTA : T ⊆ A)
    (hrow : ∀ a ∈ A,
      ((hypercube n).neighborFinset a ∩ T).card ≤ n - 1)
    (hcol : ∀ t ∈ T,
      ((hypercube n).neighborFinset t ∩ A).card ≤ 1) :
    T.card ≤ (Finset.univ \ A).card := by
  let L : (T -> Real) →ₗ[Real] ({v // v ∈ Finset.univ \ A} -> Real) :=
    (boundaryMatrix n T A).mulVecLin
  have hL : Function.Injective L := by
    intro x y hxy
    suffices x - y = 0 by exact sub_eq_zero.mp this
    let z := x - y
    have hLz : L z = 0 := by
      rw [map_sub, hxy, sub_self]
    have hBpoint : ∀ b ∈ Finset.univ \ A,
        Matrix.mulVec (huangMatrix n) (extendByZero T z) b = 0 := by
      intro b hb
      let bs : {v // v ∈ Finset.univ \ A} := ⟨b, hb⟩
      have hboundary :
          Matrix.mulVec (boundaryMatrix n T A) z bs =
            Matrix.mulVec (huangMatrix n) (extendByZero T z) bs := by
        simp only [Matrix.mulVec, dotProduct, boundaryMatrix]
        calc
          ∑ i : T, huangMatrix n bs i * z i =
              ∑ i : T, huangMatrix n bs i * extendByZero T z i := by
                apply Finset.sum_congr rfl
                intro i _
                simp [extendByZero]
          _ = ∑ i ∈ T, huangMatrix n bs i * extendByZero T z i := by
                exact (Finset.sum_subtype T (by simp)
                  (fun i => huangMatrix n bs i * extendByZero T z i)).symm
          _ = ∑ i, huangMatrix n bs i * extendByZero T z i := by
                apply Finset.sum_subset (Finset.subset_univ T)
                intro i _ hi
                simp [extendByZero, hi]
      rw [← hboundary]
      change L z bs = 0
      rw [hLz]
      rfl
    have hB : ∑ b ∈ Finset.univ \ A,
        (Matrix.mulVec (huangMatrix n) (extendByZero T z) b) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [hBpoint b hb]
      norm_num
    have hnorm : ∑ t : T, (z t) ^ 2 = 0 := by
      have hA := huang_energy_on_A T A z hrow hcol
      have hfull := huang_energy n (extendByZero T z)
      have hsplit :
          ∑ v, (Matrix.mulVec (huangMatrix n) (extendByZero T z) v) ^ 2 =
            ∑ a ∈ A, (Matrix.mulVec (huangMatrix n) (extendByZero T z) a) ^ 2 +
              ∑ b ∈ Finset.univ \ A,
                (Matrix.mulVec (huangMatrix n) (extendByZero T z) b) ^ 2 := by
        simpa using (Finset.sum_sdiff (s₁ := A) (s₂ := Finset.univ)
          (Finset.subset_univ A)
          (fun v => (Matrix.mulVec (huangMatrix n) (extendByZero T z) v) ^ 2)).symm
      have hext : ∑ v, (extendByZero T z v) ^ 2 = ∑ t : T, (z t) ^ 2 := by
        calc
          ∑ v, (extendByZero T z v) ^ 2 =
              ∑ v ∈ T, (extendByZero T z v) ^ 2 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ T)
            intro v _ hv
            simp [extendByZero, hv]
          _ = ∑ t : T, (extendByZero T z t) ^ 2 :=
            Finset.sum_subtype T (by simp) _
          _ = ∑ t : T, (z t) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            simp [extendByZero]
      rw [hsplit, hB, add_zero, hext] at hfull
      have hnonneg : 0 ≤ ∑ t : T, (z t) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hfull hA
      nlinarith
    funext t
    have hterm : (z t) ^ 2 ≤ ∑ u : T, (z u) ^ 2 :=
      Finset.single_le_sum (fun u _ => sq_nonneg (z u)) (Finset.mem_univ t)
    rw [hnorm] at hterm
    exact sq_eq_zero_iff.mp (le_antisymm hterm (sq_nonneg _))
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

/-- A source-faithful partial coloring satisfying Definition 2.2.

The colored support is `S`; hence uncolored neighbors never enter either count.
The added `1` is the center of the closed neighborhood, counted exactly once.
-/
def IsSubQuorumColoring {n k : Nat} (S : Finset (Fin n -> Bool))
    (color : S -> Fin k) : Prop :=
  0 < k ∧ Function.Surjective color ∧
    ∀ v : S,
      (1 + (S.attach.filter fun w : S =>
        (hypercube n).Adj v.1 w.1 ∧ color w = color v).card) * 2 ≥
      1 + (S.attach.filter fun w : S => (hypercube n).Adj v.1 w.1).card

/-- The color count `k` is attained by an onto admissible partial coloring. -/
def SubQuorumAttainable (n k : Nat) : Prop :=
  ∃ (S : Finset (Fin n -> Bool)) (color : S -> Fin k),
    IsSubQuorumColoring S color

/-- The bounded maximum from Definition 2.2. -/
noncomputable def subQuorumChromaticNumber (n : Nat) : Nat :=
  Nat.findGreatest (SubQuorumAttainable n) (2 ^ n)

private theorem one_attainable (n : Nat) : SubQuorumAttainable n 1 := by
  let z : Fin n -> Bool := fun _ => false
  let S : Finset (Fin n -> Bool) := {z}
  let color : S -> Fin 1 := fun _ => 0
  refine ⟨S, color, by
    refine ⟨by decide, ?_, ?_⟩
    · intro q
      exact ⟨⟨z, by simp [S]⟩, Subsingleton.elim _ _⟩
    · intro v
      have hv : v.1 = z := Finset.mem_singleton.mp (by simpa [S] using v.2)
      have hv' : v = ⟨z, by simp [S]⟩ := Subtype.ext hv
      subst v
      have hnone : S.attach.filter (fun w : S => (hypercube n).Adj z w.1) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w _ hadj
        have hwz : w.1 = z := Finset.mem_singleton.mp (by simpa [S] using w.2)
        rw [hwz] at hadj
        exact (hypercube n).loopless.irrefl z hadj
      have hnoneColor : S.attach.filter (fun w : S =>
          (hypercube n).Adj z w.1 ∧ color w = color ⟨z, by simp [S]⟩) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w _ hw
        have hwz : w.1 = z := Finset.mem_singleton.mp (by simpa [S] using w.2)
        rw [hwz] at hw
        exact (hypercube n).loopless.irrefl z hw.1
      rw [hnone, hnoneColor]
      norm_num⟩

private def HasColoredEdge {n k : Nat} {S : Finset (Fin n -> Bool)}
    (color : S -> Fin k) (c : Fin k) : Prop :=
  ∃ p : S × S,
    (hypercube n).Adj p.1.1 p.2.1 ∧ color p.1 = c ∧ color p.2 = c

private noncomputable def coloredEdge {n k : Nat}
    {S : Finset (Fin n -> Bool)} {color : S -> Fin k}
    (c : Fin k) (h : HasColoredEdge color c) : S × S :=
  Classical.choose h

private theorem attainable_twice_le_cube_card {n k : Nat} (hn : 2 ≤ n)
    (h : SubQuorumAttainable n k) : 2 * k ≤ 2 ^ n := by
  obtain ⟨S, color, hcolor⟩ := h
  let E : Finset (Fin k) := Finset.univ.filter (HasColoredEdge color)
  let N : Finset (Fin k) := Finset.univ \ E
  have hE (c : Fin k) : c ∈ E ↔ HasColoredEdge color c := by simp [E]
  let edgePair : {c // c ∈ E} -> S × S := fun c =>
    coloredEdge c.1 ((hE c.1).mp c.2)
  have hedgePair (c : {c // c ∈ E}) :
      (hypercube n).Adj (edgePair c).1.1 (edgePair c).2.1 ∧
        color (edgePair c).1 = c.1 ∧ color (edgePair c).2 = c.1 := by
    simpa [edgePair, coloredEdge] using
      (Classical.choose_spec ((hE c.1).mp c.2))
  let rep : {c // c ∈ N} -> S := fun c => Classical.choose (hcolor.2.1 c.1)
  have hrep (c : {c // c ∈ N}) : color (rep c) = c.1 := by
    exact Classical.choose_spec (hcolor.2.1 c.1)
  let D := {c // c ∈ N} ⊕ ({c // c ∈ E} × Bool)
  let selected : D -> S := fun q => match q with
    | Sum.inl c => rep c
    | Sum.inr (c, false) => (edgePair c).1
    | Sum.inr (c, true) => (edgePair c).2
  let selectedColor : D -> Fin k := fun q => match q with
    | Sum.inl c => c.1
    | Sum.inr (c, _) => c.1
  have hselectedColor (q : D) : color (selected q) = selectedColor q := by
    rcases q with c | ⟨c, b⟩
    · exact hrep c
    · cases b <;> simp [selected, selectedColor, (hedgePair c).2]
  have hselected : Function.Injective selected := by
    intro q r hqr
    have hc : selectedColor q = selectedColor r := by
      rw [← hselectedColor q, ← hselectedColor r, hqr]
    rcases q with c | ⟨c, b⟩ <;> rcases r with d | ⟨d, e⟩
    · exact congrArg Sum.inl (Subtype.ext hc)
    · exfalso
      have hcd : c.1 = d.1 := hc
      have hcnot : c.1 ∉ E := (Finset.mem_sdiff.mp c.2).2
      exact hcnot (hcd ▸ d.2)
    · exfalso
      have hcd : c.1 = d.1 := hc
      have hdnot : d.1 ∉ E := (Finset.mem_sdiff.mp d.2).2
      exact hdnot (hcd ▸ c.2)
    · have hcd : c = d := Subtype.ext hc
      subst d
      cases b <;> cases e
      · rfl
      · exact False.elim ((hedgePair c).1.ne (congrArg Subtype.val hqr))
      · exact False.elim ((hedgePair c).1.ne' (congrArg Subtype.val hqr))
      · rfl
  have hrepInjective : Function.Injective rep := by
    intro c d hcd
    apply Subtype.ext
    rw [← hrep c, ← hrep d, hcd]
  let T : Finset (Fin n -> Bool) := Finset.univ.image (fun c : {c // c ∈ N} => (rep c).1)
  let A : Finset (Fin n -> Bool) := Finset.univ.image (fun q : D => (selected q).1)
  have hTcard : T.card = N.card := by
    rw [show T = Finset.univ.image (fun c : {c // c ∈ N} => (rep c).1) from rfl,
      Finset.card_image_of_injective]
    · simp
    · exact fun c d hcd => hrepInjective (Subtype.ext hcd)
  have hAcard : A.card = N.card + 2 * E.card := by
    rw [show A = Finset.univ.image (fun q : D => (selected q).1) from rfl,
      Finset.card_image_of_injective]
    · simp [D, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]
    · exact fun q r hqr => hselected (Subtype.ext hqr)
  have hTA : T ⊆ A := by
    intro v hv
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨c, rfl⟩ := hv
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Sum.inl c, rfl⟩
  have hAS : A ⊆ S := by
    intro v hv
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨q, rfl⟩ := hv
    exact (selected q).2
  have hcol : ∀ t ∈ T,
      ((hypercube n).neighborFinset t ∩ A).card ≤ 1 := by
    intro t ht
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨c, rfl⟩ := ht
    have hsame : (S.attach.filter fun w : S =>
        (hypercube n).Adj (rep c).1 w.1 ∧ color w = color (rep c)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro w _ hw
      have hedge : HasColoredEdge color c.1 :=
        ⟨(rep c, w), hw.1, hrep c, hw.2.trans (hrep c)⟩
      have hcE : c.1 ∈ E := by simp [E, hedge]
      exact (Finset.mem_sdiff.mp c.2).2 hcE
    have hsub : (hypercube n).neighborFinset (rep c).1 ∩ A ⊆
        (hypercube n).neighborFinset (rep c).1 ∩ S := by
      intro w hw
      simp only [Finset.mem_inter] at hw ⊢
      exact ⟨hw.1, hAS hw.2⟩
    refine (Finset.card_le_card hsub).trans ?_
    let F := S.attach.filter fun w : S => (hypercube n).Adj (rep c).1 w.1
    have himage : F.image (fun w : S => w.1) =
        (hypercube n).neighborFinset (rep c).1 ∩ S := by
      ext w
      simp [F, SimpleGraph.mem_neighborFinset, and_comm]
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
    change (S.attach.filter fun w : S =>
      (hypercube n).Adj (rep c).1 w.1).card ≤ 1
    have hq := hcolor.2.2 (rep c)
    rw [hsame] at hq
    omega
  have hrow : ∀ a ∈ A,
      ((hypercube n).neighborFinset a ∩ T).card ≤ n - 1 := by
    intro a ha
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at ha
    obtain ⟨q, rfl⟩ := ha
    rcases q with c | ⟨c, b⟩
    · change ((hypercube n).neighborFinset (rep c).1 ∩ T).card ≤ n - 1
      have hsub : (hypercube n).neighborFinset (rep c).1 ∩ T ⊆
          (hypercube n).neighborFinset (rep c).1 ∩ A := by
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1, hTA hv.2⟩
      have ht : (rep c).1 ∈ T :=
        Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
      have hdegree := (Finset.card_le_card hsub).trans (hcol (rep c).1 ht)
      have hone : 1 ≤ n - 1 := by omega
      exact hdegree.trans hone
    · let partner : S := match b with
        | false => (edgePair c).2
        | true => (edgePair c).1
      have hadj : (hypercube n).Adj (selected (Sum.inr (c, b))).1 partner.1 := by
        cases b
        · exact (hedgePair c).1
        · exact (hedgePair c).1.symm
      have hpartnerT : partner.1 ∉ T := by
        intro hp
        simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨d, hd⟩ := hp
        have hcolors : c.1 = d.1 := by
          cases b
          · calc
              c.1 = color (edgePair c).2 := (hedgePair c).2.2.symm
              _ = color (rep d) := congrArg color (Subtype.ext hd).symm
              _ = d.1 := hrep d
          · calc
              c.1 = color (edgePair c).1 := (hedgePair c).2.1.symm
              _ = color (rep d) := congrArg color (Subtype.ext hd).symm
              _ = d.1 := hrep d
        have hdnot : d.1 ∉ E := (Finset.mem_sdiff.mp d.2).2
        exact hdnot (hcolors ▸ c.2)
      have hsub : (hypercube n).neighborFinset (selected (Sum.inr (c, b))).1 ∩ T ⊆
          (hypercube n).neighborFinset (selected (Sum.inr (c, b))).1 :=
        Finset.inter_subset_left
      have hss : (hypercube n).neighborFinset (selected (Sum.inr (c, b))).1 ∩ T ⊂
          (hypercube n).neighborFinset (selected (Sum.inr (c, b))).1 := by
        rw [Finset.ssubset_iff_of_subset hsub]
        exact ⟨partner.1, by simpa [SimpleGraph.mem_neighborFinset] using hadj, by
          simp [hpartnerT]⟩
      have hlt := Finset.card_lt_card hss
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        (hypercube_regular n).degree_eq] at hlt
      omega
  have hcore := feasible_core_card_le_compl n hn T A hTA hrow hcol
  have hpartition : A.card + (Finset.univ \ A).card = 2 ^ n := by
    have hAle : A.card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ A)
    calc
      A.card + (Finset.univ \ A).card =
          A.card + (Finset.univ.card - A.card) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
      _ = Finset.univ.card := Nat.add_sub_of_le hAle
      _ = 2 ^ n := by
        simp [Fintype.card_bool, Fintype.card_fin]
  have hcolors : A.card + T.card = 2 * k := by
    rw [hAcard, hTcard]
    have hNE : N.card + E.card = k := by
      have hEle : E.card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.subset_univ E)
      calc
        N.card + E.card = (Finset.univ.card - E.card) + E.card := by
          rw [show N = Finset.univ \ E from rfl,
            Finset.card_sdiff_of_subset (Finset.subset_univ E)]
        _ = Finset.univ.card := Nat.sub_add_cancel hEle
        _ = k := by simp
    omega
  rw [← hcolors]
  omega

private def cubeParity {n : Nat} (x : Fin n -> Bool) : Bool :=
  ∑ i, x i

private theorem cubeParity_ne_of_adj {n : Nat} {x y : Fin n -> Bool}
    (hxy : (hypercube n).Adj x y) : cubeParity x ≠ cubeParity y := by
  change (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 at hxy
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hxy
  have hdiff (j : Fin n) : x j ≠ y j ↔ j = i := by
    have hj := Finset.ext_iff.mp hi j
    simpa using hj
  have herase : ∑ j ∈ Finset.univ.erase i, x j =
      ∑ j ∈ Finset.univ.erase i, y j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    by_contra hne
    exact hji ((hdiff j).mp hne)
  intro hp
  unfold cubeParity at hp
  rw [← Finset.add_sum_erase Finset.univ x (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ y (Finset.mem_univ i), herase] at hp
  exact ((hdiff i).mpr rfl) (add_right_cancel hp)

private def evenVertex {m : Nat} (x : Fin m -> Bool) : Fin (m + 1) -> Bool :=
  Fin.cons (∑ i, x i) x

private theorem parity_attainable (m : Nat) :
    SubQuorumAttainable (m + 1) (2 ^ m) := by
  let S : Finset (Fin (m + 1) -> Bool) :=
    Finset.univ.image (@evenVertex m)
  let enum : (Fin m -> Bool) ≃ Fin (2 ^ m) :=
    Fintype.equivFinOfCardEq (by simp)
  let color : S -> Fin (2 ^ m) := fun v => enum (Fin.tail v.1)
  refine ⟨S, color, ?_⟩
  refine ⟨pow_pos (by decide) _, ?_, ?_⟩
  · intro c
    let x : Fin m -> Bool := enum.symm c
    have hx : evenVertex x ∈ S := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    refine ⟨⟨evenVertex x, hx⟩, ?_⟩
    simp [color, x, enum, evenVertex]
  · intro v
    have hvParity : cubeParity v.1 = false := by
      have hv := v.2
      simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨x, hx⟩ := hv
      rw [← hx]
      simp [cubeParity, evenVertex, Fin.sum_univ_succ, Bool.add_eq_xor]
    have hnone : S.attach.filter
        (fun w : S => (hypercube (m + 1)).Adj v.1 w.1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w _ hadj
      have hwParity : cubeParity w.1 = false := by
        have hw := w.2
        simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hw
        obtain ⟨x, hx⟩ := hw
        rw [← hx]
        simp [cubeParity, evenVertex, Fin.sum_univ_succ, Bool.add_eq_xor]
      exact cubeParity_ne_of_adj hadj (hvParity.trans hwParity.symm)
    have hnoneColor : S.attach.filter (fun w : S =>
        (hypercube (m + 1)).Adj v.1 w.1 ∧ color w = color v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w _ hw
      have := Finset.filter_eq_empty_iff.mp hnone (Finset.mem_attach S w)
      exact this hw.1
    rw [hnone, hnoneColor]
    norm_num

/-- Sahbi Conjecture 6.4: every nontrivial Boolean cube has exact
sub-quorum chromatic number equal to one parity class. -/
theorem subQuorumChromaticNumber_hypercube (n : Nat) (hn : 2 ≤ n) :
    subQuorumChromaticNumber n = 2 ^ (n - 1) := by
  have hlower : 2 ^ (n - 1) ≤ subQuorumChromaticNumber n := by
    have hparity : SubQuorumAttainable n (2 ^ (n - 1)) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using parity_attainable (n - 1)
    have hbound : 2 ^ (n - 1) ≤ 2 ^ n := by
      obtain ⟨S, color, _, hsurj, _⟩ := hparity
      have hks : 2 ^ (n - 1) ≤ S.card := by
        simpa only [Fintype.card_fin, Fintype.card_coe] using
          Fintype.card_le_of_surjective color hsurj
      exact hks.trans <| by
        simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
    unfold subQuorumChromaticNumber
    exact Nat.le_findGreatest hbound hparity
  have hmaximum : SubQuorumAttainable n (subQuorumChromaticNumber n) := by
    unfold subQuorumChromaticNumber
    exact Nat.findGreatest_spec Nat.one_le_two_pow (one_attainable n)
  have htwice : 2 * subQuorumChromaticNumber n ≤ 2 ^ n :=
    attainable_twice_le_cube_card hn hmaximum
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  rw [hpow] at htwice
  omega

end D5.S3.Combinatorics.Graph.HypercubeSubQuorum
