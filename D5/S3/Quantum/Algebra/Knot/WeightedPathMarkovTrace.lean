/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Perron path tower and the Markov law for its literal local projection. -/

import D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Star.StarAlgHom

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
namespace D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace

variable {L : Type*} [Fintype L] [DecidableEq L]

attribute [local instance] Classical.propDecidable
local instance (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

/-- Append a legal last edge, retaining the original literal path type. -/
def append (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (x : LegalPath R n s t) : LegalPath R (n + 1) s u := by
  refine ⟨Fin.snoc x.val u, ?_, by simp, ?_⟩
  · simpa using x.property.1
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa [x.property.2.1] using h
    · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using x.property.2.2 j

/-- The changing endpoint fiber splits into its legal predecessor fibers. -/
def splitPath (R : L → L → Prop) (n : ℕ) (s u : L) :
    LegalPath R (n + 1) s u ≃ Σ t : {t : L // R t u}, LegalPath R n s t.val where
  toFun x := ⟨⟨x.val (Fin.last n).castSucc, by
      simpa [x.property.2.1] using x.property.2.2 (Fin.last n)⟩,
    ⟨fun k => x.val k.castSucc, x.property.1, rfl,
      fun k => by simpa using x.property.2.2 k.castSucc⟩⟩
  invFun x := append R n s x.1.val u x.1.property x.2
  left_inv x := by
    apply Subtype.ext
    funext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa [append] using x.property.2.1.symm
    · simp [append]
  right_inv x := by
    rcases x with ⟨⟨t, ht⟩, x⟩
    dsimp only [append]
    have he : Fin.snoc (α := fun _ : Fin (n + 2) => L) x.val u (Fin.last n).castSucc = t := by
      simpa only [Fin.snoc_castSucc] using x.property.2.1
    apply Sigma.ext (Subtype.ext he)
    apply (Subtype.heq_iff_coe_eq (fun z => by simp only [he])).mpr
    funext k
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 2) => L) u x.val k

/-- The full product of fixed-endpoint matrix algebras, including empty fibers. -/
abbrev C (R : L → L → Prop) (n : ℕ) (s : L) :=
  ∀ t : L, Matrix (LegalPath R n s t) (LegalPath R n s t) ℂ

/-- Unweighted, rectangular path-append matrix. -/
def J (R : L → L → Prop) (n : ℕ) (s t u : L) (h : R t u) :
    Matrix (LegalPath R (n + 1) s u) (LegalPath R n s t) ℂ :=
  by
    classical
    exact fun y x => if y = append R n s t u h x then 1 else 0

/-- The actual finite-coordinate tower inclusion. -/
def iota (R : L → L → Prop) (n : ℕ) (s : L) (X : C R n s) : C R (n + 1) s :=
  by
    classical
    exact fun u => (Matrix.blockDiagonal' (fun t : {t : L // R t u} => X t.val)).submatrix
      (splitPath R n s u) (splitPath R n s u)

/-- Weighted compression, in the faithful append coordinates. -/
def F (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (n : ℕ) (s : L)
    (Y : C R (n + 1) s) : C R n s :=
  by
    classical
    exact fun t => ∑ u : {u : L // R t u},
    (((d u.val / (δ * d t) : ℝ) : ℂ) •
      (Y u.val).submatrix (append R n s t u.val u.property)
        (append R n s t u.val u.property))

/-- The normalized weighted endpoint trace. -/
def tau (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (n : ℕ) (s : L)
    (X : C R n s) : ℂ :=
  (∑ t : L, (d t : ℂ) * Matrix.trace (X t)) / ((δ : ℂ) ^ n * (d s : ℂ))

/-- The final local generator is exactly the pre-existing pathProjection. -/
def lastProjection (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (hn : 0 < n) (s : L) : C R (n + 1) s :=
  fun t => pathProjection R d δ (n + 1) s t n ⟨hn, by omega⟩

private theorem split_append (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (x : LegalPath R n s t) :
    splitPath R n s u (append R n s t u h x) = ⟨⟨t, h⟩, x⟩ :=
  (splitPath R n s u).apply_symm_apply ⟨⟨t, h⟩, x⟩

private theorem append_injective (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) : Function.Injective (append R n s t u h) := by
  intro x y hxy
  apply Subtype.ext
  funext k
  have hh := congrArg (fun z : LegalPath R (n + 1) s u => z.val k.castSucc) hxy
  simpa [append] using hh

private theorem iota_append (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (X : C R n s) (x y : LegalPath R n s t) :
    iota R n s X u (append R n s t u h x) (append R n s t u h y) = X t x y := by
  classical
  simp only [iota, Matrix.submatrix_apply, split_append, Matrix.blockDiagonal'_apply_eq]

/-- The original split/append coordinates, exposed for the returning-block consumer. -/
theorem split_append_coordinates (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (x : LegalPath R n s t) :
    splitPath R n s u (append R n s t u h x) = ⟨⟨t, h⟩, x⟩ :=
  split_append R n s t u h x

/-- The original injectivity proof, exposed without removing its frozen private identity. -/
theorem append_isInjective (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) : Function.Injective (append R n s t u h) :=
  append_injective R n s t u h

/-- The original inclusion coordinates, exposed for the returning-block consumer. -/
theorem iota_append_entry (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (X : C R n s) (x y : LegalPath R n s t) :
    iota R n s X u (append R n s t u h x) (append R n s t u h y) = X t x y :=
  iota_append R n s t u h X x y

/-- The coordinate inclusion as an actual unital complex star algebra homomorphism. -/
def iotaHom (R : L → L → Prop) (n : ℕ) (s : L) : C R n s →⋆ₐ[ℂ] C R (n + 1) s := by
  classical
  have hone : iota R n s 1 = 1 := by
    funext u
    change (Matrix.blockDiagonal' (1 : ∀ t : {t : L // R t u},
      Matrix (LegalPath R n s t.val) (LegalPath R n s t.val) ℂ)).submatrix
      (splitPath R n s u) (splitPath R n s u) = 1
    rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
  refine {
    toFun := iota R n s
    map_one' := hone
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_
    commutes' := ?_
    map_star' := ?_ }
  · intro X Y
    funext u
    simp [iota, Matrix.blockDiagonal'_mul, Matrix.submatrix_mul_equiv]
  · funext u
    change (Matrix.blockDiagonal' (0 : ∀ t : {t : L // R t u},
      Matrix (LegalPath R n s t.val) (LegalPath R n s t.val) ℂ)).submatrix
      (splitPath R n s u) (splitPath R n s u) = 0
    simp
  · intro X Y
    funext u
    change (Matrix.blockDiagonal' ((fun t : {t : L // R t u} => X t.val) +
      (fun t : {t : L // R t u} => Y t.val))).submatrix _ _ = _
    rw [Matrix.blockDiagonal'_add]
    rfl
  · intro c
    simp only [Algebra.algebraMap_eq_smul_one]
    change iota R n s (c • 1) = c • 1
    calc
      iota R n s (c • 1) = c • iota R n s 1 := by
        funext u
        change (Matrix.blockDiagonal' (c • (fun t : {t : L // R t u} =>
          (1 : C R n s) t.val))).submatrix _ _ = _
        rw [Matrix.blockDiagonal'_smul]
        rfl
      _ = c • 1 := congrArg (fun X : C R (n + 1) s => c • X) hone
  · intro X
    funext u
    change (Matrix.blockDiagonal' (fun t : {t : L // R t u} => (X t.val)ᴴ)).submatrix _ _ =
      ((Matrix.blockDiagonal' (fun t : {t : L // R t u} => X t.val)).submatrix _ _)ᴴ
    rw [← Matrix.blockDiagonal'_conjTranspose, Matrix.conjTranspose_submatrix]


private theorem J_compression (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (Y : Matrix (LegalPath R (n + 1) s u) (LegalPath R (n + 1) s u) ℂ) :
    (J R n s t u h)ᴴ * Y * J R n s t u h =
      Y.submatrix (append R n s t u h) (append R n s t u h) := by
  classical
  ext x y
  simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem J_isometry (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) : (J R n s t u h)ᴴ * J R n s t u h = 1 := by
  classical
  ext x y
  simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    (append_injective R n s t u h).eq_iff, eq_comm]

private theorem F_iota (R : L → L → Prop) [DecidableRel R]
    (d : L → ℝ) (hd : ∀ t, 0 < d t) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ t, (∑ u : L with R t u, d u) = δ * d t)
    (n : ℕ) (s : L) (X : C R n s) : F R d δ n s (iota R n s X) = X := by
  classical
  funext t
  have hm (u : {u : L // R t u}) :
      (iota R n s X u.val).submatrix (append R n s t u.val u.property)
        (append R n s t u.val u.property) = X t := by
    ext x y
    exact iota_append R n s t u.val u.property X x y
  have hp : (∑ u : {u : L // R t u}, (d u.val : ℂ)) = (δ : ℂ) * (d t : ℂ) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (R t)) (by simp) (fun u => (d u : ℂ))]
    exact_mod_cast hPF t
  have hs : (∑ u : {u : L // R t u}, ((d u.val / (δ * d t) : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [← Finset.sum_div, hp]
    simp [ne_of_gt hδ, ne_of_gt (hd t)]
  simp only [F, hm, ← Finset.sum_smul]
  calc
    _ = (∑ u : {u : L // R t u}, ((d u.val / (δ * d t) : ℝ) : ℂ)) • X t := by
      congr 1
      apply Finset.sum_congr (by ext u; simp)
      intro u _
      rfl
    _ = X t := by rw [hs, one_smul]


private theorem sum_split (R : L → L → Prop) (n : ℕ) (s u : L)
    (g : LegalPath R (n + 1) s u → ℂ) :
    (∑ y, g y) = ∑ t : {t : L // R t u}, ∑ x : LegalPath R n s t.val,
      g (append R n s t.val u t.property x) := by
  classical
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (splitPath R n s u)
  intro x
  exact congrArg g ((splitPath R n s u).symm_apply_apply x).symm

private theorem sum_edges (R : L → L → Prop) (g : ∀ t u, R t u → ℂ) :
    (∑ u : L, ∑ t : {t : L // R t u}, g t.val u t.property) =
      ∑ t : L, ∑ u : {u : L // R t u}, g t u.val u.property := by
  classical
  have hs (p : L → Prop) (f : ∀ x, p x → ℂ) :
      (∑ x : {x : L // p x}, f x.val x.property) =
        ∑ x : L, if h : p x then f x h else 0 := by
    let ff : L → ℂ := fun x => if h : p x then f x h else 0
    calc
      _ = ∑ x : {x : L // p x}, ff x.val := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [ff, dif_pos x.property]
      _ = ∑ x ∈ Finset.univ.filter p, ff x :=
        (Finset.sum_subtype _ (by simp) ff).symm
      _ = _ := by
        simp only [Finset.sum_filter, ff]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
  calc
    _ = ∑ u : L, ∑ t : L, if h : R t u then g t u h else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      exact hs (fun t => R t u) (fun t h => g t u h)
    _ = ∑ t : L, ∑ u : L, if h : R t u then g t u h else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hs (R t) (g t)).symm


private theorem compress_left (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (X : C R n s)
    (Y : Matrix (LegalPath R (n + 1) s u) (LegalPath R (n + 1) s u) ℂ) :
    (iota R n s X u * Y).submatrix (append R n s t u h) (append R n s t u h) =
      X t * Y.submatrix (append R n s t u h) (append R n s t u h) := by
  classical
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_split R n s u]
  rw [Finset.sum_eq_single (⟨t,h⟩ : {t : L // R t u})]
  · simp only [iota_append, Matrix.submatrix_apply]
  · intro v _ hv
    apply Finset.sum_eq_zero
    intro z _
    simp only [iota, Matrix.submatrix_apply, split_append,
      Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hv), zero_mul]
  · simp

private theorem compress_right (R : L → L → Prop) (n : ℕ) (s t u : L)
    (h : R t u) (X : C R n s)
    (Y : Matrix (LegalPath R (n + 1) s u) (LegalPath R (n + 1) s u) ℂ) :
    (Y * iota R n s X u).submatrix (append R n s t u h) (append R n s t u h) =
      Y.submatrix (append R n s t u h) (append R n s t u h) * X t := by
  classical
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_split R n s u]
  rw [Finset.sum_eq_single (⟨t,h⟩ : {t : L // R t u})]
  · simp only [iota_append, Matrix.submatrix_apply]
  · intro v _ hv
    apply Finset.sum_eq_zero
    intro z _
    simp only [iota, Matrix.submatrix_apply, split_append,
      Matrix.blockDiagonal'_apply_ne _ _ _ hv, mul_zero]
  · simp

private theorem F_bimodule (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (A B : C R n s) (Y : C R (n + 1) s) :
    F R d δ n s (iota R n s A * Y * iota R n s B) = A * F R d δ n s Y * B := by
  classical
  funext t
  simp only [F, Pi.mul_apply, compress_right, compress_left]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem trace_F (R : L → L → Prop) [DecidableRel R]
    (d : L → ℝ) (hd : ∀ t, 0 < d t) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (s : L) (Y : C R (n + 1) s) :
    tau R d δ n s (F R d δ n s Y) = tau R d δ (n + 1) s Y := by
  classical
  have hdC (t : L) : (d t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd t)
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  have hw : (∑ t : L, (d t : ℂ) * Matrix.trace (F R d δ n s Y t)) =
      (∑ u : L, (d u : ℂ) * Matrix.trace (Y u)) / (δ : ℂ) := by
    simp only [F, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    push_cast
    have hc (t u : L) (z : ℂ) : (d t : ℂ) * ((d u : ℂ) / ((δ : ℂ) * (d t : ℂ)) * z) =
        (d u : ℂ) * z / (δ : ℂ) := by field_simp [hdC t, hδC]
    simp_rw [hc]
    simp_rw [← Finset.sum_div]
    congr 1
    rw [← sum_edges R (fun t u h => (d u : ℂ) *
      Matrix.trace ((Y u).submatrix (append R n s t u h) (append R n s t u h)))]
    apply Finset.sum_congr rfl
    intro u _
    rw [Matrix.trace, sum_split R n s u]
    simp [Matrix.trace, Matrix.submatrix_apply, Finset.mul_sum]
  unfold tau
  rw [hw, pow_succ]
  field_simp
  <;> ring

theorem tau_smul (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (c : ℂ) (X : C R n s) :
    tau R d δ n s (c • X) = c * tau R d δ n s X := by
  simp only [tau, Pi.smul_apply, Matrix.trace_smul, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (d _ : ℂ) c, mul_assoc]
  rw [← Finset.mul_sum]
  ring

private theorem projection_append (R : L → L → Prop) (d : L → ℝ)
    (hd : ∀ t, 0 < d t) (δ : ℝ) (n : ℕ) (hn : 0 < n)
    (s t u : L) (h : R t u) (x y : LegalPath R n s t) :
    lastProjection R d δ n hn s u (append R n s t u h x) (append R n s t u h y) =
      if x = y ∧ x.val ⟨n - 1, by omega⟩ = u then
        ((d t / (δ * d u) : ℝ) : ℂ) else 0 := by
  classical
  have hmid (z : LegalPath R n s t) :
      (append R n s t u h z).val (⟨n, by omega⟩ : Fin (n + 2)) = t := by
    have hk : (⟨n, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by
      apply Fin.ext; rfl
    rw [hk]
    simpa [append] using z.property.2.1
  have hprev (z : LegalPath R n s t) :
      (append R n s t u h z).val (⟨n - 1, by omega⟩ : Fin (n + 2)) =
        z.val ⟨n - 1, by omega⟩ := by
    have hk : (⟨n - 1, by omega⟩ : Fin (n + 2)) =
        (⟨n - 1, by omega⟩ : Fin (n + 1)).castSucc := by apply Fin.ext; rfl
    rw [hk]
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 2) => L) u z.val _
  have hend (z : LegalPath R n s t) :
      (append R n s t u h z).val (⟨n + 1, by omega⟩ : Fin (n + 2)) = u := by
    have hk : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
      apply Fin.ext; rfl
    rw [hk]
    exact (append R n s t u h z).property.2.1
  have away : (∀ k : Fin (n + 2), k.val ≠ n →
      (append R n s t u h x).val k = (append R n s t u h y).val k) ↔ x = y := by
    constructor
    · intro hh
      apply Subtype.ext
      funext k
      by_cases hk : k.val = n
      · have hk' : k = Fin.last n := Fin.ext hk
        rw [hk', x.property.2.1, y.property.2.1]
      · simpa [append] using hh k.castSucc hk
    · rintro rfl
      simp
  simp only [lastProjection, pathProjection, away, hmid, hprev, hend]
  split_ifs with hxy
  · rw [hxy.2, Real.sqrt_mul_self (le_of_lt (hd t))]
  · rfl

private theorem F_last (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ t, 0 < d t) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 0 < n) (s : L) :
    F R d δ n s (lastProjection R d δ n hn s) = ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  classical
  have hdC (t : L) : (d t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd t)
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  funext t
  ext x y
  simp only [F, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    smul_eq_mul, projection_append R d hd δ n hn]
  by_cases hxy : x = y
  · subst y
    let v : L := x.val ⟨n - 1, by omega⟩
    have hv : R t v := by
      have he := x.property.2.2 (⟨n - 1, by omega⟩ : Fin n)
      have hk : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n := by
        apply Fin.ext; simp; omega
      rw [hk, x.property.2.1] at he
      exact hR.symm _ _ he
    rw [Finset.sum_eq_single (⟨v,hv⟩ : {u : L // R t u})]
    · simp [v, Matrix.one_apply]
      push_cast
      field_simp [hdC, hδC]
      <;> ring
    · intro u _ hu
      have hne : v ≠ u.val := by
        intro he
        exact hu (Subtype.ext he.symm)
      simp [v, hne]
    · simp
  · simp [hxy, Matrix.one_apply]

private theorem tau_zero (R : L → L → Prop) (d : L → ℝ) (hd : ∀ t, 0 < d t)
    (δ : ℝ) (s : L) : tau R d δ 0 s 1 = 1 := by
  classical
  have hsingle : Fintype.card (LegalPath R 0 s s) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨fun _ => s, rfl, rfl, fun k => Fin.elim0 k⟩, ?_⟩
    intro x
    apply Subtype.ext
    funext k
    have hk : k = 0 := Fin.eq_zero k
    simpa [hk] using x.property.1
  have hempty (t : L) (ht : t ≠ s) : IsEmpty (LegalPath R 0 s t) := by
    refine ⟨fun x => ?_⟩
    have hh : s = t := x.property.1.symm.trans x.property.2.1
    exact ht hh.symm
  unfold tau
  rw [Finset.sum_eq_single s]
  · simp [Matrix.trace_one, hsingle, ne_of_gt (hd s)]
  · intro t _ ht
    letI := hempty t ht
    simp [Matrix.trace_one]
  · simp

private theorem J_orthogonal (R : L → L → Prop) (n : ℕ) (s t v u : L)
    (ht : R t u) (hv : R v u) (htv : t ≠ v) :
    (J R n s t u ht)ᴴ * J R n s v u hv = 0 := by
  classical
  ext x z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, J]
  apply Finset.sum_eq_zero
  intro y _
  have hne : append R n s t u ht x ≠ append R n s v u hv z := by
    intro hh
    have he := congrArg (fun p : LegalPath R (n + 1) s u => p.val (Fin.last n).castSucc) hh
    simp only [append, Fin.snoc_castSucc, x.property.2.1, z.property.2.1] at he
    exact htv he
  split_ifs with h1 h2
  · exact (hne (h1.symm.trans h2)).elim
  all_goals simp

/-- The endpoint-block tower, its Perron compression, and the literal last-generator Markov law. -/
theorem weighted_path_markov_trace (R : L → L → Prop) [DecidableRel R]
    (hR : Std.Symm R) (d : L → ℝ) (hd : ∀ t, 0 < d t)
    (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ t, (∑ u : L with R t u, d u) = δ * d t) :
    ∀ (n : ℕ) (s : L),
      Function.Injective (iotaHom R n s) ∧
      (∀ (t u : L) (h : R t u), (J R n s t u h)ᴴ * J R n s t u h = 1) ∧
      (∀ (t v u : L) (ht : R t u) (hv : R v u), t ≠ v →
        (J R n s t u ht)ᴴ * J R n s v u hv = 0) ∧
      (∀ (t u : L) (h : R t u) (Y : C R (n + 1) s),
        (J R n s t u h)ᴴ * Y u * J R n s t u h =
          (Y u).submatrix (append R n s t u h) (append R n s t u h)) ∧
      (∀ X : C R n s, F R d δ n s (iota R n s X) = X) ∧
      (∀ (A B : C R n s) (Y : C R (n + 1) s),
        F R d δ n s (iota R n s A * Y * iota R n s B) =
          A * F R d δ n s Y * B) ∧
      (∀ Y : C R (n + 1) s, tau R d δ n s (F R d δ n s Y) = tau R d δ (n + 1) s Y) ∧
      (∀ X : C R n s, tau R d δ (n + 1) s (iota R n s X) = tau R d δ n s X) ∧
      tau R d δ n s 1 = 1 ∧
      (∀ hn : 0 < n,
        F R d δ n s (lastProjection R d δ n hn s) = ((δ : ℂ)⁻¹ ^ 2) • 1 ∧
        (∀ X : C R n s,
          tau R d δ (n + 1) s (iota R n s X * lastProjection R d δ n hn s) =
            ((δ : ℂ)⁻¹ ^ 2) * tau R d δ n s X) ∧
        star (lastProjection R d δ n hn s) = lastProjection R d δ n hn s ∧
        lastProjection R d δ n hn s * lastProjection R d δ n hn s =
          lastProjection R d δ n hn s) := by
  classical
  have hc (n : ℕ) (s : L) (X : C R n s) :
      tau R d δ (n + 1) s (iota R n s X) = tau R d δ n s X := by
    rw [← trace_F R d hd δ hδ, F_iota R d hd δ hδ hPF]
  have hnorm (n : ℕ) (s : L) : tau R d δ n s 1 = 1 := by
    induction n with
    | zero => exact tau_zero R d hd δ s
    | succ n ih =>
      have hone : iota R n s 1 = 1 := (iotaHom R n s).map_one
      rw [← hone, hc, ih]
  intro n s
  refine ⟨?_, J_isometry R n s, J_orthogonal R n s, (fun t u h Y => J_compression R n s t u h (Y u)),
    F_iota R d hd δ hδ hPF n s, F_bimodule R d δ n s,
    trace_F R d hd δ hδ n s, hc n s, hnorm n s, ?_⟩
  · intro X Y hXY
    have hh := congrArg (F R d δ n s) hXY
    change F R d δ n s (iota R n s X) = F R d δ n s (iota R n s Y) at hh
    rwa [F_iota R d hd δ hδ hPF, F_iota R d hd δ hδ hPF] at hh
  · intro hn
    have he := F_last R hR d hd δ hδ n hn s
    refine ⟨he, ?_, ?_, ?_⟩
    · intro X
      let e := lastProjection R d δ n hn s
      have hone : iota R n s 1 = 1 := (iotaHom R n s).map_one
      have hl : F R d δ n s (iota R n s X * e) = X * F R d δ n s e := by
        simpa only [hone, mul_one] using F_bimodule R d δ n s X 1 e
      have hs : X * F R d δ n s e = ((δ : ℂ)⁻¹ ^ 2) • X := by
        rw [he]
        funext t
        change X t * (((δ : ℂ)⁻¹ ^ 2) • (1 : Matrix (LegalPath R n s t)
          (LegalPath R n s t) ℂ)) = ((δ : ℂ)⁻¹ ^ 2) • X t
        rw [Matrix.mul_smul, mul_one]
      calc
        _ = tau R d δ n s (F R d δ n s (iota R n s X * e)) :=
          (trace_F R d hd δ hδ n s (iota R n s X * e)).symm
        _ = tau R d δ n s (X * F R d δ n s e) := congrArg (tau R d δ n s) hl
        _ = tau R d δ n s (((δ : ℂ)⁻¹ ^ 2) • X) := congrArg (tau R d δ n s) hs
        _ = _ := tau_smul R d δ n s ((δ : ℂ)⁻¹ ^ 2) X
    · funext t
      exact ((weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF (n + 1) s t).1 n
        ⟨hn, by omega⟩).1
    · funext t
      exact ((weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF (n + 1) s t).1 n
        ⟨hn, by omega⟩).2

#print axioms weighted_path_markov_trace

end D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
