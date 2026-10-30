/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX parent Lindbladian has the conjectured even-ring limit. -/

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

private lemma pinching_single (p q : Fin 16) :
    pinching (Matrix.single p q 1) =
      if sector16 p = sector16 q ∧ multiplicity16 p = multiplicity16 q then
        (4 : ℂ)⁻¹ • ∑ m : Fin 4,
          Matrix.single (block16 (sector16 p) m (bit16 p))
            (block16 (sector16 q) m (bit16 q)) 1
      else 0 := by
  have hsum (f : Fin 4 → Fin 16 → Fin 16 → ℂ) (r s : Fin 16) :
      (∑ m, f m) r s = ∑ m, f m r s := Matrix.sum_apply r s Finset.univ f
  have hd (r : Fin 16) : r = block16 (sector16 r) (multiplicity16 r) (bit16 r) := by
    apply Fin.ext
    change r.val = 8 * (r.val / 8) + 2 * (r.val % 8 / 2) + r.val % 2
    omega
  ext r s
  obtain ⟨lp, mp, zp, hp⟩ : ∃ l m z, p = block16 l m z := ⟨_, _, _, hd p⟩
  obtain ⟨lq, mq, zq, hq⟩ : ∃ l m z, q = block16 l m z := ⟨_, _, _, hd q⟩
  obtain ⟨lr, mr, zr, hr⟩ : ∃ l m z, r = block16 l m z := ⟨_, _, _, hd r⟩
  obtain ⟨ls, ms, zs, hs⟩ : ∃ l m z, s = block16 l m z := ⟨_, _, _, hd s⟩
  subst p q r s
  clear hd
  simp only [pinching, (block16_components ..).1, (block16_components ..).2.1,
    (block16_components ..).2.2, Matrix.single_apply, Matrix.smul_apply, Matrix.sum_apply,
    block16_eq, smul_eq_mul]
  split_ifs <;>
    (try simp only [hsum]
     clear hsum
     simp_all [Matrix.single_apply, block16_eq, ite_and, Finset.sum_ite_irrel, eq_comm])

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

private lemma window_channel_comp (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
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
private lemma window_superoperator_action (n : ℕ) (i : Fin n)
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

private lemma window_idempotent (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    IsIdempotentElem (windowSuperoperator n i) := by
  change windowSuperoperator n i * windowSuperoperator n i = windowSuperoperator n i
  ext x y
  change (windowSuperoperator n i).mulVec
    (fun p => windowChannel n i (Matrix.single y.1 y.2 1) p.1 p.2) x = _
  rw [window_superoperator_action, window_channel_comp n hn]
  rfl

private lemma window_commute (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 0) :
    Commute (windowSuperoperator n i) (windowSuperoperator n j) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
private lemma exponential_idempotent {k : Type*} [Fintype k] [DecidableEq k]
    (e : Matrix k k ℂ) (he : IsIdempotentElem e) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (e - 1)) =
      (Real.exp (-t) : ℂ) • (1 : Matrix k k ℂ) +
        (1 - (Real.exp (-t) : ℂ)) • e := by
  let f : (ℂ × ℂ) →+* Matrix k k ℂ :=
    { toFun := fun z => z.1 • e + z.2 • (1 - e)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intro z w
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_mul' := by
        intro z w
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add,
          smul_mul_assoc, mul_smul_comm, smul_smul, he.eq, he.one_sub.eq,
          he.mul_one_sub_self, he.one_sub_mul_self, smul_zero, zero_add, add_zero,
          mul_comm] }
  have hf : Continuous f :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hi : f ((0 : ℂ), -(t : ℂ)) = (t : ℂ) • (e - 1) := by
    change (0 : ℂ) • e + (-(t : ℂ)) • (1 - e) = _
    simp only [zero_smul, zero_add, smul_sub, neg_smul]
    module
  have h := (open scoped Matrix.Norms.Operator in
    NormedSpace.map_exp f hf ((0 : ℂ), -(t : ℂ)))
  rw [hi] at h
  rw [← h]
  change (NormedSpace.exp ((0 : ℂ), -(t : ℂ))).1 • e +
    (NormedSpace.exp ((0 : ℂ), -(t : ℂ))).2 • (1 - e) = _
  rw [Prod.fst_exp, Prod.snd_exp]
  simp only [NormedSpace.exp_zero, one_smul]
  have hexp : NormedSpace.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
    rw [← Complex.ofReal_neg, ← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  rw [hexp]
  module

private lemma finite_projection_limit {k : Type*} [Fintype k] [DecidableEq k]
    (es : List (Matrix k k ℂ))
    (hi : ∀ e ∈ es, IsIdempotentElem e) (hc : es.Pairwise Commute) :
    Tendsto (fun t : ℝ => NormedSpace.exp
      ((t : ℂ) • (es.map (fun e => e - 1)).sum)) atTop (𝓝 es.prod) := by
  induction es with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix k k ℂ)) atTop (𝓝 1))
  | cons e es ih =>
    have he := hi e (List.mem_cons_self ..)
    have hes : ∀ f ∈ es, IsIdempotentElem f := fun f hf => hi f (List.mem_cons_of_mem _ hf)
    have hcs := List.pairwise_cons.mp hc
    have hlim := ih hes hcs.2
    have hsingle : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (e - 1)))
        atTop (𝓝 e) := by
      have hr : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          Real.tendsto_exp_neg_atTop_nhds_zero
      simpa only [exponential_idempotent e he, zero_smul, sub_zero, one_smul,
        zero_add] using (hr.smul_const (1 : Matrix k k ℂ)).add
          (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub hr).smul_const e)
    have hcomm : Commute (e - 1) (es.map (fun f => f - 1)).sum := by
      apply Commute.list_sum_right
      intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact ((hcs.1 g hg).sub_right (Commute.one_right e)).sub_left
        (Commute.one_left (g - 1))
    have heq (t : ℝ) : NormedSpace.exp
        ((t : ℂ) • ((e :: es).map (fun f => f - 1)).sum) =
        NormedSpace.exp ((t : ℂ) • (e - 1)) *
          NormedSpace.exp ((t : ℂ) • (es.map (fun f => f - 1)).sum) := by
      simp only [List.map_cons, List.sum_cons, smul_add]
      exact Matrix.exp_add_of_commute _ _ (hcomm.smul_left (t : ℂ) |>.smul_right (t : ℂ))
    simpa only [heq, List.prod_cons] using hsingle.mul hlim

private noncomputable def projection (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  (((List.finRange n).filter (fun i => i.val % 2 == 0)).map
    (windowSuperoperator n)).prod

private lemma exponential_limit (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n)) := by
  let sites := (List.finRange n).filter (fun i => i.val % 2 == 0)
  have hsum : ((sites.map (windowSuperoperator n)).map (fun e => e - 1)).sum =
      parentLindbladian n := by
    rw [List.map_map, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    change ∑ i ∈ ((List.finRange n).filter _).toFinset, _ = _
    simp only [List.toFinset_filter, List.toFinset_finRange, beq_iff_eq]
    rfl
  have hi : ∀ e ∈ sites.map (windowSuperoperator n), IsIdempotentElem e := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact window_idempotent n hsize i
  have hc : (sites.map (windowSuperoperator n)).Pairwise Commute := by
    apply List.pairwise_map.mpr
    apply List.pairwise_of_forall_mem_list
    intro i hi j hj
    have hei : i.val % 2 = 0 := by simpa [sites] using (List.mem_filter.mp hi).2
    have hej : j.val % 2 = 0 := by simpa [sites] using (List.mem_filter.mp hj).2
    exact window_commute n hn hsize i j hei hej
  have hp : (sites.map (windowSuperoperator n)).prod = projection n := rfl
  simpa only [hsum, hp] using finite_projection_limit (sites.map (windowSuperoperator n)) hi hc

private lemma projection_formula (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (fun x y => (projection n).mulVec (fun p => a p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ • (Matrix.trace a • (1 : Matrix _ _ ℂ) +
        Matrix.trace ((czxUnitary n)ᴴ * a) • czxUnitary n) := by
  sorry

private lemma flip_diagonal (n : ℕ) (hn : 0 < n) (x : Fin n → Fin 2) :
    tensorX n x x = 0 := by
  change (if x = (fun j => x j + 1) then (1 : ℂ) else 0) = 0
  apply if_neg
  intro h
  have hj := congrArg Fin.val (congrFun h (⟨0, hn⟩ : Fin n))
  change (x ⟨0, hn⟩).val = ((x ⟨0, hn⟩).val + 1) % 2 at hj
  have hx := (x (⟨0, hn⟩ : Fin n)).isLt
  omega

private lemma symmetry_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace (czxUnitary n) = 0 := by
  change ∑ x : Fin n → Fin 2, (cz n * tensorX n) x x = 0
  apply Finset.sum_eq_zero
  intro x _
  rw [show cz n = Matrix.diagonal (fun z => (-1 : ℂ) ^
    ∑ j : Fin n, (z j).val * (z (site j 1)).val) from rfl]
  rw [Matrix.diagonal_mul, flip_diagonal n hn, mul_zero]

private lemma tensor_x_unitary (n : ℕ) : tensorX n * (tensorX n)ᴴ = 1 := by
  have hf (x : Fin n → Fin 2) : (fun j => (x j + 1) + 1) = x := by
    funext j
    apply Fin.ext
    change (((x j).val + 1) % 2 + 1) % 2 = (x j).val
    have := (x j).isLt
    omega
  let f : Equiv.Perm (Fin n → Fin 2) :=
    { toFun := fun x j => x j + 1
      invFun := fun x j => x j + 1
      left_inv := hf
      right_inv := hf }
  have hx : tensorX n = f.permMatrix ℂ := by
    ext x y
    have hi : x = f y ↔ f x = y := by
      constructor
      · rintro rfl
        exact hf y
      · intro h
        calc
          x = f (f x) := (hf x).symm
          _ = f y := congrArg f h
    change (if x = f y then (1 : ℂ) else 0) = f.toPEquiv.toMatrix x y
    rw [PEquiv.toMatrix_toPEquiv_apply]
    simp only [Pi.single_apply, hi, eq_comm]
  rw [hx, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

private lemma coefficient_partition (n : ℕ) :
    Matrix.trace ((czxUnitary n)ᴴ * tensorX n) =
      ∑ x : Fin n → Fin 2, (-1 : ℂ) ^
        ∑ j : Fin n, (x j).val * (x (site j 1)).val := by
  change Matrix.trace ((cz n * tensorX n)ᴴ * tensorX n) = _
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    tensor_x_unitary, one_mul, Matrix.trace_conjTranspose]
  rw [show cz n = Matrix.diagonal (fun x => (-1 : ℂ) ^
    ∑ j : Fin n, (x j).val * (x (site j 1)).val) from rfl, Matrix.trace_diagonal]
  simp only [star_sum, star_pow, star_neg, star_one]

private lemma transfer_path (h : Matrix (Fin 2) (Fin 2) ℂ) (m : ℕ) (a b : Fin 2) :
    (h ^ (m + 1)) a b = ∑ x : Fin m → Fin 2, ∏ j : Fin (m + 1),
      h (Fin.cons (α := fun _ => Fin 2) a x j) (Fin.snoc (α := fun _ => Fin 2) x b j) := by
  induction m generalizing b with
  | zero => simp <;> rfl
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2))
    intro p
    change (∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) a p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j)) * h p.1 b =
      ∏ j : Fin (m + 2), h (Fin.cons (α := fun _ => Fin 2) a (Fin.snoc (α := fun _ => Fin 2) p.2 p.1) j)
        (Fin.snoc (α := fun _ => Fin 2) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1) b j)
    conv_rhs => rw [Fin.prod_univ_castSucc]
    simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last]

private lemma partition_transfer (n : ℕ) (hn : 0 < n) :
    (∑ x : Fin n → Fin 2, (-1 : ℂ) ^
      ∑ j : Fin n, (x j).val * (x (site j 1)).val) =
      Matrix.trace ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) ^ n) := by
  let h : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
  have he (a b : Fin 2) : h a b = (-1 : ℂ) ^ (a.val * b.val) := by
    fin_cases a <;> fin_cases b <;> norm_num [h]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  symm
  calc
    Matrix.trace (h ^ (m + 1)) = ∑ a : Fin 2, ∑ x : Fin m → Fin 2,
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) a x j) (Fin.snoc (α := fun _ => Fin 2) x a j) := by
      change (∑ a, (h ^ (m + 1)) a a) = _
      simp_rw [transfer_path]
    _ = ∑ p : Fin 2 × (Fin m → Fin 2),
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : Fin (m + 1) → Fin 2, (-1 : ℂ) ^
        ∑ j : Fin (m + 1), (x j).val * (x (site j 1)).val := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2))
      intro p
      change (∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j)) =
        (-1 : ℂ) ^ ∑ j : Fin (m + 1), (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j).val *
          (Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1)).val
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      have hj : Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1) = Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j := by
        cases j using Fin.lastCases with
        | last =>
          have hs : site (Fin.last m) 1 = 0 := by
            apply Fin.ext
            change (m + 1) % (m + 1) = 0
            exact Nat.mod_self _
          rw [hs, Fin.cons_zero, Fin.snoc_last]
        | cast j =>
          have hs : site j.castSucc 1 = j.succ := by
            apply Fin.ext
            change (j.val + 1) % (m + 1) = j.val + 1
            exact Nat.mod_eq_of_lt (by omega)
          rw [hs, Fin.cons_succ, Fin.snoc_castSucc]
      rw [hj, he]

private lemma transfer_coefficient (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Matrix.trace ((czxUnitary n)ᴴ * tensorX n) = (2 : ℂ) ^ (n / 2 + 1) := by
  let h : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
  have hs : h ^ 2 = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [h, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hm : n = 2 * (n / 2) := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hp : h ^ n = (2 : ℂ) ^ (n / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      h ^ n = h ^ (2 * (n / 2)) := congrArg (h ^ ·) hm
      _ = (h ^ 2) ^ (n / 2) := pow_mul _ _ _
      _ = _ := by rw [hs, smul_pow, one_pow]
  rw [coefficient_partition n, partition_transfer n (by omega)]
  change Matrix.trace (h ^ n) = _
  rw [hp, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul, pow_succ]

private lemma projection_initial (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    (fun x y => (projection n).mulVec
      (fun p => (((2 : ℂ) ^ n)⁻¹ •
        ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) + tensorX n)) p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ •
        ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) +
          (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n) := by
  have hnpos : 0 < n := by omega
  have htx : Matrix.trace (tensorX n) = 0 := by
    change ∑ x, tensorX n x x = 0
    exact Finset.sum_eq_zero (fun x _ => flip_diagonal n hnpos x)
  have hu : Matrix.trace (czxUnitary n)ᴴ = 0 := by
    rw [Matrix.trace_conjTranspose, symmetry_trace n hnpos, star_zero]
  have hcard : (Fintype.card (Fin n → Fin 2) : ℂ) = (2 : ℂ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have ht : Matrix.trace (((2 : ℂ) ^ n)⁻¹ •
      ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) + tensorX n)) = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, htx, add_zero, hcard]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  have hm : n = n / 2 + n / 2 := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hcoef : ((2 : ℂ) ^ n)⁻¹ * (2 : ℂ) ^ (n / 2 + 1) =
      (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
    rw [show (2 : ℂ) ^ n = (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) by
      rw [← pow_add, ← hm], pow_add, pow_one]
    field_simp
    <;> ring
  rw [projection_formula n hn hsize, ht]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_one,
    Matrix.trace_add, hu, transfer_coefficient n hn hsize, zero_add]
  rw [one_smul, smul_eq_mul, hcoef]

private lemma evolution_limit (n : ℕ)
    (h : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n))) :
    Tendsto (fun t : ℝ => evolution n t
      (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
      (𝓝 (fun x y => (projection n).mulVec
        (fun p => (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) (x, y))) := by
  apply tendsto_pi_nhds.mpr
  intro x
  apply tendsto_pi_nhds.mpr
  intro y
  change Tendsto (fun t : ℝ => ∑ p,
    NormedSpace.exp ((t : ℂ) • parentLindbladian n) (x, y) p *
      (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) _ _
  exact tendsto_finset_sum _ fun p _ =>
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h (x, y))) p).mul tendsto_const_nhds

/-- The steady-state conjecture for every even N at least four. -/
theorem result : claim := by
  intro n hn hsize
  have happly := evolution_limit n (exponential_limit n hn hsize)
  rw [projection_initial n hn hsize] at happly
  exact happly

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
