/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX four-site window channel and gauge action. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState

open Matrix Filter
open scoped Topology ComplexConjugate

/- Source: Liu et al., arXiv:2501.10552v2, Example VI.6 and Appendix F.
   admission_basis: open-problem-resolution (#23957)
   The first site is the most significant bit of each four-site window.
   Evolution uses the matrix of the superoperator on pairs of configurations.
   No matrix norm instance is installed.
-/

/-- The two-site change of basis in Appendix F. -/
def czxU : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- The signed permutation in Appendix F, with source indices shifted by one. -/
def czxV : Matrix (Fin 16) (Fin 16) ℂ := fun r c =>
  if (r, c) ∈ ({(0, 0), (1, 15), (2, 2), (3, 13), (4, 4), (5, 11),
      (6, 6), (8, 1), (9, 14), (10, 3), (12, 5), (13, 10), (14, 7),
      (15, 8)} : Finset (Fin 16 × Fin 16)) then 1
  else if (r, c) = (7, 9) ∨ (r, c) = (11, 12) then -1 else 0

/-- The common two-site block weight. -/
noncomputable def mu : ℝ := Real.sqrt 3 / 4

/-- The scalar multiplying the four-dimensional multiplicity identity. -/
noncomputable def nu : ℝ := Real.sqrt 3 / 16

/-- The trace of a multiplicity block. -/
noncomputable def mLambda : ℝ := mu

private def block4 (l z : Fin 2) : Fin 4 := ⟨2 * l.val + z.val, by omega⟩

private def block16 (l : Fin 2) (m : Fin 4) (z : Fin 2) : Fin 16 :=
  ⟨8 * l.val + 2 * m.val + z.val, by omega⟩

private def sector4 (r : Fin 4) : Fin 2 := ⟨r.val / 2, by omega⟩

private def bit4 (r : Fin 4) : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩

private def sector16 (r : Fin 16) : Fin 2 := ⟨r.val / 8, by omega⟩

private def multiplicity16 (r : Fin 16) : Fin 4 := ⟨r.val % 8 / 2, by omega⟩

private def bit16 (r : Fin 16) : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Block pinching and partial trace, conjugated by the two source unitaries. -/
noncomputable def renormS (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  czxUᴴ * Matrix.of (fun r s => if sector4 r = sector4 s then
    ∑ m : Fin 4, (czxV * x * czxVᴴ)
      (block16 (sector4 r) m (bit4 r)) (block16 (sector4 s) m (bit4 s))
    else 0) * czxU

/-- Insertion of the normalized multiplicity state, with the source tensor order. -/
noncomputable def renormT (y : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ :=
  czxVᴴ * Matrix.of (fun r s => if sector16 r = sector16 s then
    ((nu / mLambda : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ)
      (multiplicity16 r) (multiplicity16 s) *
      (czxU * y * czxUᴴ) (block4 (sector16 r) (bit16 r))
        (block4 (sector16 s) (bit16 s)) else 0) * czxV

/-- The source four-site channel, T composed with S. -/
noncomputable def localChannel (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ := renormT (renormS x)

/-- Cyclic displacement of a site. -/
def site {n : ℕ} (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- The four bits of a cyclic window, first site most significant. -/
def windowCode {n : ℕ} (i : Fin n) (x : Fin n → Fin 2) : Fin 16 :=
  ⟨8 * (x (site i 0)).val + 4 * (x (site i 1)).val +
      2 * (x (site i 2)).val + (x (site i 3)).val, by
    have := (x (site i 0)).isLt
    have := (x (site i 1)).isLt
    have := (x (site i 2)).isLt
    have := (x (site i 3)).isLt
    omega⟩

private def digit (p : Fin 16) (k : ℕ) : Fin 2 :=
  ⟨p.val / 2 ^ k % 2, Nat.mod_lt _ (by decide)⟩

/-- Write a four-bit word into a cyclic window. -/
def windowUpdate {n : ℕ} (i : Fin n) (x : Fin n → Fin 2) (p : Fin 16) :
    Fin n → Fin 2 :=
  Function.update (Function.update (Function.update (Function.update x
    (site i 0) (digit p 3)) (site i 1) (digit p 2))
    (site i 2) (digit p 1)) (site i 3) (digit p 0)

/-- E tensored with the identity on the complement of a cyclic window. -/
noncomputable def windowChannel (n : ℕ) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  ∑ p : Fin 16, ∑ q : Fin 16,
    localChannel (Matrix.single p q 1) (windowCode i x) (windowCode i y) *
      a (windowUpdate i x p) (windowUpdate i y q)

/-- Matrix of a window channel in the matrix-unit basis. -/
noncomputable def windowSuperoperator (n : ℕ) (i : Fin n) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ := fun x y =>
  windowChannel n i (Matrix.single y.1 y.2 1) x.1 x.2

/-- The parent generator, summed over zero-based even starting sites. -/
noncomputable def parentLindbladian (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0),
    (windowSuperoperator n i - 1)

/-- The tensor power of sigma-x, which flips every bit. -/
def tensorX (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = (fun j => y j + 1) then 1 else 0

/-- Product of the controlled-z gates on every edge of the ring. -/
def cz (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal fun x => (-1 : ℂ) ^ ∑ j : Fin n, (x j).val * (x (site j 1)).val

/-- The CZX symmetry operator, in the source order CZ times X. -/
def czxUnitary (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  cz n * tensorX n

/-- The matrix exponential of the source parent generator acting on an operator. -/
noncomputable def evolution (n : ℕ) (t : ℝ)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  (NormedSpace.exp ((t : ℂ) • parentLindbladian n)).mulVec
    (fun p => a p.1 p.2) (x, y)

/-- The conjecture for every even ring on which the four window sites are distinct. -/
def claim : Prop := ∀ n : ℕ, Even n → 4 ≤ n →
  Tendsto (fun t : ℝ => evolution n t (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
    (𝓝 (((2 : ℂ) ^ n)⁻¹ •
      (1 + (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n)))

private noncomputable def pinching (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ := fun r s =>
  if sector16 r = sector16 s ∧ multiplicity16 r = multiplicity16 s then
    (4 : ℂ)⁻¹ * ∑ m : Fin 4,
      x (block16 (sector16 r) m (bit16 r)) (block16 (sector16 s) m (bit16 s))
  else 0

private lemma local_channel_formula (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel x = czxVᴴ * pinching (czxV * x * czxVᴴ) * czxV := by
  have hu : czxU * czxUᴴ = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [czxU, Matrix.mul_apply, Fin.sum_univ_succ]
  have hc (w : Matrix (Fin 4) (Fin 4) ℂ) :
      czxU * (czxUᴴ * w * czxU) * czxUᴴ = w := by
    calc
      _ = (czxU * czxUᴴ) * w * (czxU * czxUᴴ) := by simp only [mul_assoc]
      _ = w := by rw [hu, one_mul, mul_one]
  have hr : ((nu / mLambda : ℝ) : ℂ) = (4 : ℂ)⁻¹ := by
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    change (((Real.sqrt 3 / 16) / (Real.sqrt 3 / 4) : ℝ) : ℂ) = _
    have hreal : (Real.sqrt 3 / 16) / (Real.sqrt 3 / 4) = (1 / 4 : ℝ) := by
      field_simp [hs]
      <;> ring
    rw [hreal]
    norm_num
  change czxVᴴ * _ * czxV = _
  congr 2
  ext r s
  simp only [renormS, hc, hr, pinching, Matrix.of_apply]
  have hsector (l : Fin 2) (z : Fin 2) : sector4 (block4 l z) = l := by
    apply Fin.ext
    change (2 * l.val + z.val) / 2 = l.val
    omega
  have hbit (l : Fin 2) (z : Fin 2) : bit4 (block4 l z) = z := by
    apply Fin.ext
    change (2 * l.val + z.val) % 2 = z.val
    omega
  simp only [hsector, hbit, Matrix.one_apply]
  split_ifs <;> simp_all only [hsector, hbit, mul_one, mul_zero, zero_mul,
    true_and, and_true, not_true_eq_false, not_false_eq_true]

private lemma local_channel_add (x y : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel (x + y) = localChannel x + localChannel y := by
  have hp (a b : Matrix (Fin 16) (Fin 16) ℂ) :
      pinching (a + b) = pinching a + pinching b := by
    ext r s
    simp only [pinching, Matrix.add_apply]
    split_ifs <;> simp only [Finset.sum_add_distrib, mul_add, add_zero]
  rw [local_channel_formula, local_channel_formula x, local_channel_formula y,
    mul_add, add_mul, hp, mul_add, add_mul]

private lemma pinching_smul (c : ℂ) (a : Matrix (Fin 16) (Fin 16) ℂ) :
    pinching (c • a) = c • pinching a := by
  ext r s
  simp only [pinching, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp only [← Finset.mul_sum, mul_zero] <;> ring

private lemma local_channel_smul (c : ℂ) (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel (c • x) = c • localChannel x := by
  rw [local_channel_formula, local_channel_formula x,
    Matrix.mul_smul, Matrix.smul_mul, pinching_smul, Matrix.mul_smul, Matrix.smul_mul]

private lemma local_channel_expansion (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel x = ∑ p : Fin 16, ∑ q : Fin 16,
      x p q • localChannel (Matrix.single p q 1) := by
  let f : Matrix (Fin 16) (Fin 16) ℂ →ₗ[ℂ] Matrix (Fin 16) (Fin 16) ℂ :=
    { toFun := localChannel
      map_add' := local_channel_add
      map_smul' := local_channel_smul }
  change f x = _
  have hs (p q : Fin 16) : Matrix.single p q (x p q) =
      x p q • Matrix.single p q 1 := by
    rw [Matrix.smul_single]
    simp only [smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum, hs, map_smul]
  rfl

set_option maxHeartbeats 1600000 in
private lemma local_channel_idempotent (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel (localChannel x) = localChannel x := by
  have hv : czxV * czxVᴴ = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [czxV, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  have hc (w : Matrix (Fin 16) (Fin 16) ℂ) :
      czxV * (czxVᴴ * w * czxV) * czxVᴴ = w := by
    calc
      _ = (czxV * czxVᴴ) * w * (czxV * czxVᴴ) := by simp only [mul_assoc]
      _ = w := by rw [hv, one_mul, mul_one]
  have hp (w : Matrix (Fin 16) (Fin 16) ℂ) : pinching (pinching w) = pinching w := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [pinching, sector16, multiplicity16, bit16, block16, Fin.sum_univ_succ] <;> ring
  calc
    localChannel (localChannel x) =
        czxVᴴ * pinching (czxV * localChannel x * czxVᴴ) * czxV :=
      local_channel_formula _
    _ = czxVᴴ * pinching (pinching (czxV * x * czxVᴴ)) * czxV := by
      rw [local_channel_formula x, hc]
    _ = czxVᴴ * pinching (czxV * x * czxVᴴ) * czxV := by rw [hp]
    _ = localChannel x := (local_channel_formula x).symm

private def pack (v : Fin 4 → Fin 2) : Fin 16 :=
  ⟨8 * (v 0).val + 4 * (v 1).val + 2 * (v 2).val + (v 3).val, by
    have := (v 0).isLt
    have := (v 1).isLt
    have := (v 2).isLt
    have := (v 3).isLt
    omega⟩

private def pathPhase (v : Fin 4 → Fin 2) : ℕ :=
  (v 0).val * (v 1).val + (v 1).val * (v 2).val + (v 2).val * (v 3).val

set_option maxHeartbeats 2400000 in
private lemma signed_permutation_action (v : Fin 4 → Fin 2) (r : Fin 16) :
    czxV r (pack v) =
      if r = pack ![v 0 + v 3, v 0 + v 1, v 0 + v 2, v 0] then
        (-1 : ℂ) ^ ((v 0).val * (1 + (v 2).val) * ((v 1).val + (v 3).val))
      else 0 := by
  have h (a b c d : Fin 2) (s : Fin 16) :
      czxV s (pack ![a, b, c, d]) =
        if s = pack ![a + d, a + b, a + c, a] then
          (-1 : ℂ) ^ (a.val * (1 + c.val) * (b.val + d.val)) else 0 := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [czxV, pack, Prod.mk.injEq, eq_comm]
  have hv : ![v 0, v 1, v 2, v 3] = v := by
    funext j
    fin_cases j <;> rfl
  simpa only [hv] using h (v 0) (v 1) (v 2) (v 3) r

private lemma conjugate_matrix_unit (u v : Fin 4 → Fin 2) :
    czxV * Matrix.single (pack u) (pack v) 1 * czxVᴴ =
      ((-1 : ℂ) ^ ((u 0).val * (1 + (u 2).val) * ((u 1).val + (u 3).val)) *
        (-1 : ℂ) ^ ((v 0).val * (1 + (v 2).val) * ((v 1).val + (v 3).val))) •
        Matrix.single (pack ![u 0 + u 3, u 0 + u 1, u 0 + u 2, u 0])
          (pack ![v 0 + v 3, v 0 + v 1, v 0 + v 2, v 0]) 1 := by
  ext r s
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    signed_permutation_action, eq_comm, mul_ite, ite_mul, ite_and]
  split_ifs <;> simp_all

private lemma block16_components (l : Fin 2) (m : Fin 4) (z : Fin 2) :
    sector16 (block16 l m z) = l ∧ multiplicity16 (block16 l m z) = m ∧
      bit16 (block16 l m z) = z := by
  constructor
  · apply Fin.ext
    change (8 * l.val + 2 * m.val + z.val) / 8 = l.val
    omega
  constructor
  · apply Fin.ext
    change (8 * l.val + 2 * m.val + z.val) % 8 / 2 = m.val
    omega
  · apply Fin.ext
    change (8 * l.val + 2 * m.val + z.val) % 2 = z.val
    omega

private lemma block16_eq (l a : Fin 2) (m b : Fin 4) (z c : Fin 2) :
    block16 l m z = block16 a b c ↔ l = a ∧ m = b ∧ z = c := by
  constructor
  · intro h
    have hl := congrArg sector16 h
    have hm := congrArg multiplicity16 h
    have hz := congrArg bit16 h
    simpa only [(block16_components ..).1, (block16_components ..).2.1,
      (block16_components ..).2.2] using And.intro hl (And.intro hm hz)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma block16_eta (p : Fin 16) :
    block16 (sector16 p) (multiplicity16 p) (bit16 p) = p := by
  apply Fin.ext
  change 8 * (p.val / 8) + 2 * (p.val % 8 / 2) + p.val % 2 = p.val
  omega

private lemma block_trace_single
    (l k a b : Fin 2) (m t : Fin 4) (z w c d : Fin 2) :
    (∑ j : Fin 4,
      (Matrix.single (block16 l m z) (block16 k t w) 1 :
        Matrix (Fin 16) (Fin 16) ℂ)
        (block16 a j c) (block16 b j d)) =
      if l = a ∧ k = b ∧ z = c ∧ w = d ∧ m = t then 1 else 0 := by
  simp only [Matrix.single_apply, block16_eq]
  by_cases hm : m = t
  · subst t
    simp [ite_and, Finset.sum_ite_irrel, eq_comm, and_left_comm, and_comm]
  · have hz (j : Fin 4) : ¬ ((l = a ∧ m = j ∧ z = c) ∧
        (k = b ∧ t = j ∧ w = d)) := by
      rintro ⟨⟨_, h₁, _⟩, ⟨_, h₂, _⟩⟩
      exact hm (h₁.trans h₂.symm)
    simp only [if_neg (hz _), Finset.sum_const_zero]
    simp [hm]

private lemma pinching_single_block (l k : Fin 2) (a b : Fin 4) (z t : Fin 2) :
    pinching (Matrix.single (block16 l a z) (block16 k b t) 1) =
      if l = k ∧ a = b then
        (4 : ℂ)⁻¹ • ∑ m : Fin 4,
          Matrix.single (block16 l m z) (block16 k m t) 1
      else 0 := by
  ext r s
  obtain ⟨u, v, w, hr⟩ : ∃ u v w, r = block16 u v w :=
    ⟨sector16 r, multiplicity16 r, bit16 r, (block16_eta r).symm⟩
  obtain ⟨u', v', w', hs⟩ : ∃ u v w, s = block16 u v w :=
    ⟨sector16 s, multiplicity16 s, bit16 s, (block16_eta s).symm⟩
  subst r s
  simp only [pinching, (block16_components ..).1,
    (block16_components ..).2.1, (block16_components ..).2.2,
    block_trace_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.single_apply, block16_eq, Matrix.ite_apply,
    Matrix.zero_apply]
  by_cases hv : v = v'
  · subst v'
    by_cases hl : l = u
    · subst u
      by_cases hk : k = u'
      · subst u'
        by_cases he : l = k
        · subst k
          by_cases ha : a = b <;> by_cases hz : z = w <;> by_cases ht : t = w' <;>
            simp [ha, hz, ht, ite_and, Finset.sum_ite_irrel, eq_comm]
        · simp [he, Ne.symm he, ite_and, Finset.sum_ite_irrel]
      · simp [hk, ite_and, Finset.sum_ite_irrel]
    · simp [hl, ite_and, Finset.sum_ite_irrel]
  · have hz (m : Fin 4) : ¬ ((l = u ∧ m = v ∧ z = w) ∧
        (k = u' ∧ m = v' ∧ t = w')) := by
      rintro ⟨⟨_, h₁, _⟩, ⟨_, h₂, _⟩⟩
      exact hv (h₁.symm.trans h₂)
    simp [hv, hz]

private lemma pinching_single (p q : Fin 16) :
    pinching (Matrix.single p q 1) =
      if sector16 p = sector16 q ∧ multiplicity16 p = multiplicity16 q then
        (4 : ℂ)⁻¹ • ∑ m : Fin 4,
          Matrix.single (block16 (sector16 p) m (bit16 p))
            (block16 (sector16 q) m (bit16 q)) 1
      else 0 := by
  simpa only [block16_eta] using
    pinching_single_block (sector16 p) (sector16 q)
      (multiplicity16 p) (multiplicity16 q) (bit16 p) (bit16 q)

set_option maxHeartbeats 2400000 in
private lemma local_matrix_unit (v d : Fin 4 → Fin 2) :
    localChannel (Matrix.single (pack (v + d)) (pack v) 1) =
      if h : ∀ j, d j = d 0 then
        (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
          let w := Function.update (Function.update v 1 b) 2 c
          (-1 : ℂ) ^ ((d 0).val * (pathPhase v + pathPhase w)) •
            Matrix.single (pack (w + d)) (pack w) 1
      else 0 := by
  let b : Matrix (Fin 16) (Fin 16) ℂ :=
    if ∀ j, d j = d 0 then (4 : ℂ)⁻¹ • ∑ u : Fin 2, ∑ w : Fin 2,
      let z := Function.update (Function.update v 1 u) 2 w
      (-1 : ℂ) ^ ((d 0).val * (pathPhase v + pathPhase z)) •
        Matrix.single (pack (z + d)) (pack z) 1 else 0
  change localChannel (Matrix.single (pack (v + d)) (pack v) 1) = b
  have hv : czxV * czxVᴴ = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [czxV, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  have hvb : czxVᴴ * czxV = 1 := mul_eq_one_comm.mp hv
  suffices h : pinching (czxV * Matrix.single (pack (v + d)) (pack v) 1 * czxVᴴ) =
      czxV * b * czxVᴴ by
    rw [local_channel_formula, h]
    calc
      _ = (czxVᴴ * czxV) * b * (czxVᴴ * czxV) := by simp only [mul_assoc]
      _ = b := by rw [hvb, one_mul, mul_one]
  dsimp only [b]
  rw [conjugate_matrix_unit, pinching_smul, pinching_single]
  simp only [mul_ite, ite_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.mul_sum, Finset.sum_mul, conjugate_matrix_unit, mul_zero, zero_mul]
  obtain ⟨a, c, e, f, hv⟩ : ∃ a c e f, v = ![a, c, e, f] :=
    ⟨v 0, v 1, v 2, v 3, by funext j; fin_cases j <;> rfl⟩
  obtain ⟨g, h, j, k, hd⟩ : ∃ g h j k, d = ![g, h, j, k] :=
    ⟨d 0, d 1, d 2, d 3, by funext j; fin_cases j <;> rfl⟩
  subst v d
  fin_cases a <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    fin_cases g <;> fin_cases h <;> fin_cases j <;> fin_cases k <;>
      norm_num [pack, pathPhase, sector16, multiplicity16, bit16, block16,
        Fin.sum_univ_succ, Function.update_apply, Fin.forall_fin_succ] <;>
      (try simp only [← Matrix.single_neg]) <;> module

private def gauge (n : ℕ) (e : Fin 2) (x : Fin n → Fin 2) : ℂ :=
  (-1 : ℂ) ^ (e.val * ∑ j : Fin n, (x j).val * (x (site j 1)).val)

private lemma site_injective (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (k l : Fin 4) :
    site i k.val = site i l.val ↔ k = l := by
  constructor
  · intro h
    have hm : Nat.ModEq n (i.val + k.val) (i.val + l.val) := congrArg Fin.val h
    apply Fin.ext
    exact (Nat.ModEq.add_left_cancel' i.val hm).eq_of_lt_of_lt (by omega) (by omega)
  · rintro rfl
    rfl

private lemma window_update_site (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (x : Fin n → Fin 2) (p : Fin 16) (k : Fin 4) :
    windowUpdate i x p (site i k.val) = digit p (3 - k.val) := by
  have hd (a b : Fin 4) (h : a ≠ b) : site i a.val ≠ site i b.val :=
    fun he => h ((site_injective n hn i a b).mp he)
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h03 := hd 0 3 (by decide)
  have h12 := hd 1 2 (by decide)
  have h13 := hd 1 3 (by decide)
  have h23 := hd 2 3 (by decide)
  change site i 0 ≠ site i 1 at h01
  change site i 0 ≠ site i 2 at h02
  change site i 0 ≠ site i 3 at h03
  change site i 1 ≠ site i 2 at h12
  change site i 1 ≠ site i 3 at h13
  change site i 2 ≠ site i 3 at h23
  fin_cases k <;> simp [windowUpdate, Function.update_apply, h01, h02, h03, h12, h13, h23,
    Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]

private lemma window_code_update (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (x : Fin n → Fin 2) (p : Fin 16) : windowCode i (windowUpdate i x p) = p := by
  apply Fin.ext
  change 8 * (windowUpdate i x p (site i 0)).val +
    4 * (windowUpdate i x p (site i 1)).val +
    2 * (windowUpdate i x p (site i 2)).val +
    (windowUpdate i x p (site i 3)).val = p.val
  have h0 := window_update_site n hn i x p 0
  have h1 := window_update_site n hn i x p 1
  have h2 := window_update_site n hn i x p 2
  have h3 := window_update_site n hn i x p 3
  change windowUpdate i x p (site i 0) = digit p 3 at h0
  change windowUpdate i x p (site i 1) = digit p 2 at h1
  change windowUpdate i x p (site i 2) = digit p 1 at h2
  change windowUpdate i x p (site i 3) = digit p 0 at h3
  rw [h0, h1, h2, h3]
  fin_cases p <;> rfl

private lemma window_update_update (n : ℕ) (i : Fin n) (x : Fin n → Fin 2)
    (p q : Fin 16) : windowUpdate i (windowUpdate i x p) q = windowUpdate i x q := by
  funext j
  simp only [windowUpdate, Function.update_apply]
  split_ifs <;> rfl

private lemma window_update_code (n : ℕ) (i : Fin n) (x : Fin n → Fin 2) :
    windowUpdate i x (windowCode i x) = x := by
  have he (a b c d : Fin 2) (k : Fin 4) :
      digit (pack ![a, b, c, d]) (3 - k.val) = ![a, b, c, d] k := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases k <;> rfl
  let v := ![x (site i 0), x (site i 1), x (site i 2), x (site i 3)]
  have hv (k : Fin 4) : v k = x (site i k.val) := by fin_cases k <;> rfl
  have hc : windowCode i x = pack v := rfl
  have hd (k : Fin 4) : digit (windowCode i x) (3 - k.val) = x (site i k.val) := by
    rw [hc, ← hv k]
    exact he _ _ _ _ k
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  change digit (windowCode i x) 3 = x (site i 0) at h0
  change digit (windowCode i x) 2 = x (site i 1) at h1
  change digit (windowCode i x) 1 = x (site i 2) at h2
  change digit (windowCode i x) 0 = x (site i 3) at h3
  change Function.update (Function.update (Function.update (Function.update x
    (site i 0) (digit (windowCode i x) 3)) (site i 1) (digit (windowCode i x) 2))
    (site i 2) (digit (windowCode i x) 1)) (site i 3) (digit (windowCode i x) 0) = x
  rw [h0, h1, h2, h3]
  simp only [Function.update_eq_self]

private lemma window_single (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (u v : Fin n → Fin 2) :
    windowChannel n i (Matrix.single u v 1) = ∑ p : Fin 16, ∑ q : Fin 16,
      localChannel (Matrix.single (windowCode i u) (windowCode i v) 1) p q •
        Matrix.single (windowUpdate i u p) (windowUpdate i v q) 1 := by
  have hi (u x : Fin n → Fin 2) (p : Fin 16) :
      u = windowUpdate i x p ↔ p = windowCode i u ∧
        windowUpdate i u (windowCode i x) = x := by
    constructor
    · intro h
      have hc := congrArg (windowCode i) h
      rw [window_code_update n hn] at hc
      refine ⟨hc.symm, ?_⟩
      rw [h, window_update_update, window_update_code]
    · rintro ⟨rfl, h⟩
      rw [← h, window_update_update, window_update_code]
  ext x y
  have hri (p : Fin 16) : windowUpdate i u p = x ↔ p = windowCode i x ∧
      windowUpdate i x (windowCode i u) = u := (eq_comm).trans (hi x u p)
  have hrj (q : Fin 16) : windowUpdate i v q = y ↔ q = windowCode i y ∧
      windowUpdate i y (windowCode i v) = v := (eq_comm).trans (hi y v q)
  have hsu : windowUpdate i x (windowCode i u) = u ↔
      windowUpdate i u (windowCode i x) = x := by
    calc
      _ ↔ u = windowUpdate i x (windowCode i u) := eq_comm
      _ ↔ _ := by simpa only [eq_self_iff_true, true_and] using hi u x (windowCode i u)
  have hsv : windowUpdate i y (windowCode i v) = v ↔
      windowUpdate i v (windowCode i y) = y := by
    calc
      _ ↔ v = windowUpdate i y (windowCode i v) := eq_comm
      _ ↔ _ := by simpa only [eq_self_iff_true, true_and] using hi v y (windowCode i v)
  change (∑ p : Fin 16, ∑ q : Fin 16,
    localChannel (Matrix.single p q 1) (windowCode i x) (windowCode i y) *
      Matrix.single u v 1 (windowUpdate i x p) (windowUpdate i y q)) = _
  simp only [Matrix.single_apply, hi, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, hri, hrj]
  simp [hsu, hsv, ite_and, mul_ite, Finset.sum_ite_irrel]

private lemma gauged_window (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (e : Fin 2) (x : Fin n → Fin 2) :
    windowChannel n i
      (gauge n e x • Matrix.single (x + fun _ => e) x 1) =
      (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
        let y := Function.update (Function.update x (site i 1) b) (site i 2) c
        gauge n e y • Matrix.single (y + fun _ => e) y 1 := by
  sorry

lemma window_channel_comp (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    windowChannel n i (windowChannel n i a) = windowChannel n i a := by
  have hk (r s u v : Fin 16) :
      (∑ p : Fin 16, ∑ q : Fin 16,
        localChannel (Matrix.single p q 1) u v *
          localChannel (Matrix.single r s 1) p q) =
        localChannel (Matrix.single r s 1) u v := by
    have h := congrArg (fun z : Matrix (Fin 16) (Fin 16) ℂ => z u v)
      (local_channel_idempotent (Matrix.single r s 1))
    rw [local_channel_expansion (localChannel (Matrix.single r s 1))] at h
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using h
  ext x y
  change (∑ p : Fin 16, ∑ q : Fin 16,
    localChannel (Matrix.single p q 1) (windowCode i x) (windowCode i y) *
      (∑ r : Fin 16, ∑ s : Fin 16,
        localChannel (Matrix.single r s 1) (windowCode i (windowUpdate i x p))
          (windowCode i (windowUpdate i y q)) *
          a (windowUpdate i (windowUpdate i x p) r)
            (windowUpdate i (windowUpdate i y q) s))) = _
  simp_rw [window_code_update n hn, window_update_update, Finset.mul_sum]
  conv_lhs =>
    arg 2; ext p
    rw [Finset.sum_comm]
    arg 2; ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext r
    rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hk]
  rfl

set_option maxHeartbeats 800000 in
lemma window_superoperator_action (n : ℕ) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : Fin n → Fin 2) :
    (windowSuperoperator n i).mulVec (fun p => a p.1 p.2) (x, y) =
      windowChannel n i a x y := by
  let f : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    { toFun := windowChannel n i
      map_add' := by
        intro a b
        ext u v
        simp only [windowChannel, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext u v
        simp only [windowChannel, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul,
          ← Finset.mul_sum, mul_left_comm] }
  have hs (p q : Fin n → Fin 2) : Matrix.single p q (a p q) =
      a p q • Matrix.single p q 1 := by
    rw [Matrix.smul_single]
    simp only [smul_eq_mul, mul_one]
  have ha : f a = ∑ p, ∑ q, a p q • f (Matrix.single p q 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single a]
    simp only [map_sum, hs, map_smul]
  have hv := congrArg (fun z : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ => z x y) ha
  have hf (b : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
      f b = windowChannel n i b := rfl
  simp only [hf] at hv
  change (∑ p, windowSuperoperator n i (x, y) p * a p.1 p.2) = _
  simp only [windowSuperoperator]
  rw [Fintype.sum_prod_type]
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using hv.symm

lemma window_idempotent (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    IsIdempotentElem (windowSuperoperator n i) := by
  change windowSuperoperator n i * windowSuperoperator n i = windowSuperoperator n i
  ext x y
  change (windowSuperoperator n i).mulVec
    (fun p => windowChannel n i (Matrix.single y.1 y.2 1) p.1 p.2) x = _
  rw [window_superoperator_action, window_channel_comp n hn]
  rfl

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
