/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX four-site window channel and gauge action. -/
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
/-! Source: Liu et al., arXiv:2501.10552v2, Example VI.6 and Appendix F.
   The first site is the most significant bit of each four-site window.
   Evolution uses the matrix of the superoperator on pairs of configurations.
   No matrix norm instance is installed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
open Matrix Filter
attribute [local instance low] Classical.propDecidable
open scoped Topology ComplexConjugate
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
private def block4 (l z : Fin 2) : Fin 4 := ⟨2 * l.val + z.val, by omega⟩
private def block16 (l : Fin 2) (m : Fin 4) (z : Fin 2) : Fin 16 :=
  ⟨8 * l.val + 2 * m.val + z.val, by omega⟩
/-- Block pinching and partial trace, conjugated by the two source unitaries. -/
noncomputable def renormS (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  czxUᴴ * Matrix.of (fun r s => if @Fin.divNat 2 2 r = @Fin.divNat 2 2 s then
    ∑ m : Fin 4, (czxV * x * czxVᴴ)
      (block16 (@Fin.divNat 2 2 r) m (@Fin.modNat 2 2 r))
      (block16 (@Fin.divNat 2 2 s) m (@Fin.modNat 2 2 s))
    else 0) * czxU
/-- Insertion of the normalized multiplicity state, with the source tensor order. -/
noncomputable def renormT (y : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ :=
  czxVᴴ * Matrix.of (fun r s => if @Fin.divNat 2 8 r = @Fin.divNat 2 8 s then
    ((nu / mu : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ)
      ((@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) r) ((@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) s) *
      (czxU * y * czxUᴴ) (block4 (@Fin.divNat 2 8 r) (@Fin.modNat 8 2 r))
        (block4 (@Fin.divNat 2 8 s) (@Fin.modNat 8 2 s)) else 0) * czxV
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
private noncomputable def pinching (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ := fun r s =>
  if @Fin.divNat 2 8 r = @Fin.divNat 2 8 s ∧
      (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) r = (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) s then
    (4 : ℂ)⁻¹ * ∑ m : Fin 4,
      x (block16 (@Fin.divNat 2 8 r) m (@Fin.modNat 8 2 r))
        (block16 (@Fin.divNat 2 8 s) m (@Fin.modNat 8 2 s))
  else 0
private lemma local_channel_formula (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel x = czxVᴴ * pinching (czxV * x * czxVᴴ) * czxV := by
  have hu : czxU * czxUᴴ = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      (delta czxU; norm_num [Matrix.mul_apply, Fin.sum_univ_succ])
  have hc (w : Matrix (Fin 4) (Fin 4) ℂ) :
      czxU * (czxUᴴ * w * czxU) * czxUᴴ = w := by
    calc
      _ = (czxU * czxUᴴ) * w * (czxU * czxUᴴ) := by simp only [mul_assoc]
      _ = w := by rw [hu, one_mul, mul_one]
  have hr : ((nu / mu : ℝ) : ℂ) = (4 : ℂ)⁻¹ := by
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    change (((Real.sqrt 3 / 16) / (Real.sqrt 3 / 4) : ℝ) : ℂ) = _
    have hreal : (Real.sqrt 3 / 16) / (Real.sqrt 3 / 4) = (1 / 4 : ℝ) := by
      field_simp [hs]
      ring
    rw [hreal]
    norm_num
  change czxVᴴ * _ * czxV = _
  congr 2
  ext r s
  (delta renormS pinching; simp only [hc, hr, Matrix.of_apply])
  have hsector (l : Fin 2) (z : Fin 2) : (@Fin.divNat 2 2) (block4 l z) = l := by
    apply Fin.ext
    change (2 * l.val + z.val) / 2 = l.val
    omega
  have hbit (l : Fin 2) (z : Fin 2) : (@Fin.modNat 2 2) (block4 l z) = z := by
    apply Fin.ext
    change (2 * l.val + z.val) % 2 = z.val
    omega
  simp only [hsector, hbit, Matrix.one_apply]
  split_ifs <;> simp_all only [mul_one, mul_zero, zero_mul,
    true_and, and_true, not_true_eq_false, not_false_eq_true]
private lemma local_channel_add (x y : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel (x + y) = localChannel x + localChannel y := by
  have hp (a b : Matrix (Fin 16) (Fin 16) ℂ) :
      pinching (a + b) = pinching a + pinching b := by
    ext r s
    (delta pinching; simp only [Matrix.add_apply])
    split_ifs <;> simp only [Finset.sum_add_distrib, mul_add, add_zero]
  rw [local_channel_formula, local_channel_formula x, local_channel_formula y,
    mul_add, add_mul, hp, mul_add, add_mul]
private lemma pinching_smul (c : ℂ) (a : Matrix (Fin 16) (Fin 16) ℂ) :
    pinching (c • a) = c • pinching a := by
  ext r s
  (delta pinching; simp only [Matrix.smul_apply, smul_eq_mul])
  split_ifs <;> simp only [← Finset.mul_sum, mul_zero]
  ring
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
  change f x = ∑ p : Fin 16, ∑ q : Fin 16, x p q • f (Matrix.single p q 1)
  classical
  let b := Matrix.stdBasis ℂ (Fin 16) (Fin 16)
  have hr (a : Matrix (Fin 16) (Fin 16) ℂ) (p : Fin 16 × Fin 16) :
      b.repr a p = a p.1 p.2 := by
    simp [b, Matrix.stdBasis]
  have hb (p : Fin 16 × Fin 16) : b p = Matrix.single p.1 p.2 1 :=
    Matrix.stdBasis_eq_single ℂ p.1 p.2
  ext r s
  have h := congrArg (fun v => v (r, s))
    (LinearMap.toMatrix_mulVec_repr b b f x)
  simpa only [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, hr, hb,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm] using h.symm
set_option maxHeartbeats 1600000 in
-- The four-site matrix identity expands all finite indices.
private lemma local_channel_idempotent (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel (localChannel x) = localChannel x := by
  have hv : czxV * czxVᴴ = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      (delta czxV; norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ])
  have hc (w : Matrix (Fin 16) (Fin 16) ℂ) :
      czxV * (czxVᴴ * w * czxV) * czxVᴴ = w := by
    calc
      _ = (czxV * czxVᴴ) * w * (czxV * czxVᴴ) := by simp only [mul_assoc]
      _ = w := by rw [hv, one_mul, mul_one]
  have hp (w : Matrix (Fin 16) (Fin 16) ℂ) : pinching (pinching w) = pinching w := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      (delta pinching Fin.divNat Fin.modNat Function.comp block16;
        norm_num [Fin.sum_univ_succ]) <;> ring
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
-- The signed permutation is checked on all four-site bit patterns.
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
      (delta czxV pack; norm_num [Prod.mk.injEq, eq_comm])
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
    (@Fin.divNat 2 8) (block16 l m z) = l ∧
      (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) (block16 l m z) = m ∧
      (@Fin.modNat 8 2) (block16 l m z) = z := by
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
    have hl := congrArg (@Fin.divNat 2 8) h
    have hm := congrArg (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) h
    have hz := congrArg (@Fin.modNat 8 2) h
    simpa only [(block16_components ..).1, (block16_components ..).2.1,
      (block16_components ..).2.2] using And.intro hl (And.intro hm hz)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl
private lemma block16_eta (p : Fin 16) :
    block16 (@Fin.divNat 2 8 p) ((@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) p)
      (@Fin.modNat 8 2 p) = p := by
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
    simp [ite_and, Finset.sum_ite_irrel, and_left_comm, and_comm]
  · have hz (j : Fin 4) : ¬ ((l = a ∧ m = j ∧ z = c) ∧
        (k = b ∧ t = j ∧ w = d)) := by
      rintro ⟨⟨_, h₁, _⟩, ⟨_, h₂, _⟩⟩
      exact hm (h₁.trans h₂.symm)
    simp only [ite_eq_right (hz _), Finset.sum_const_zero]
    simp [hm]
private lemma pinching_single_block (l k : Fin 2) (a b : Fin 4) (z t : Fin 2) :
    pinching (Matrix.single (block16 l a z) (block16 k b t) 1) =
      if l = k ∧ a = b then
        (4 : ℂ)⁻¹ • ∑ m : Fin 4,
          Matrix.single (block16 l m z) (block16 k m t) 1
      else 0 := by
  ext r s
  obtain ⟨u, v, w, hr⟩ : ∃ u v w, r = block16 u v w :=
    ⟨@Fin.divNat 2 8 r, (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) r,
      @Fin.modNat 8 2 r, (block16_eta r).symm⟩
  obtain ⟨u', v', w', hs⟩ : ∃ u v w, s = block16 u v w :=
    ⟨@Fin.divNat 2 8 s, (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) s,
      @Fin.modNat 8 2 s, (block16_eta s).symm⟩
  subst r s
  (delta pinching; simp only [(block16_components ..).1,
    (block16_components ..).2.1, (block16_components ..).2.2,
    block_trace_single])
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
            simp [ha, hz, ht, eq_comm]
        · simp [he]
      · simp [hk]
    · simp [hl]
  · have hz (m : Fin 4) : ¬ ((l = u ∧ m = v ∧ z = w) ∧
        (k = u' ∧ m = v' ∧ t = w')) := by
      rintro ⟨⟨_, h₁, _⟩, ⟨_, h₂, _⟩⟩
      exact hv (h₁.symm.trans h₂)
    simp [hv, hz]
private lemma pinching_single (p q : Fin 16) :
    pinching (Matrix.single p q 1) =
      if @Fin.divNat 2 8 p = @Fin.divNat 2 8 q ∧
          (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) p = (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) q then
        (4 : ℂ)⁻¹ • ∑ m : Fin 4,
          Matrix.single (block16 (@Fin.divNat 2 8 p) m (@Fin.modNat 8 2 p))
            (block16 (@Fin.divNat 2 8 q) m (@Fin.modNat 8 2 q)) 1
      else 0 := by
  simpa only [block16_eta] using
    pinching_single_block (@Fin.divNat 2 8 p) (@Fin.divNat 2 8 q)
      ((@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) p) ((@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) q)
      (@Fin.modNat 8 2 p) (@Fin.modNat 8 2 q)
set_option maxHeartbeats 2400000 in
-- The local formula compares every four-site matrix entry.
private lemma local_matrix_unit (v d : Fin 4 → Fin 2) :
    localChannel (Matrix.single (pack (v + d)) (pack v) 1) =
      if _h : ∀ j, d j = d 0 then
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
      (delta czxV; norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ])
  have hvb : czxVᴴ * czxV = 1 := mul_eq_one_comm.mp hv
  suffices h : pinching (czxV * Matrix.single (pack (v + d)) (pack v) 1 * czxVᴴ) =
      czxV * b * czxVᴴ by
    rw [local_channel_formula, h]
    calc
      _ = (czxVᴴ * czxV) * b * (czxVᴴ * czxV) := by simp only [mul_assoc]
      _ = b := by rw [hvb, one_mul, mul_one]
  dsimp only [b]
  rw [conjugate_matrix_unit, pinching_smul, pinching_single]
  have hpack (w : Fin 4 → Fin 2) :
      pack ![w 0 + w 3, w 0 + w 1, w 0 + w 2, w 0] =
        block16 (w 0 + w 3) (block4 (w 0 + w 1) (w 0 + w 2)) (w 0) := by
    apply Fin.ext
    change 8 * (w 0 + w 3).val + 4 * (w 0 + w 1).val +
      2 * (w 0 + w 2).val + (w 0).val =
      8 * (w 0 + w 3).val + 2 * (2 * (w 0 + w 1).val + (w 0 + w 2).val) + (w 0).val
    omega
  have h4 (a b c d : Fin 2) : block4 a b = block4 c d ↔ a = c ∧ b = d := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      change 2 * a.val + b.val = 2 * c.val + d.val at hv
      have ha : a.val = c.val := by omega
      have hb : b.val = d.val := by omega
      exact ⟨Fin.ext ha, Fin.ext hb⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hbit (a b e f : Fin 2) :
      (a + e) + (b + f) = a + b ↔ e = f := by
    rw [add_add_add_comm, add_eq_left]
    exact (open scoped Fin.CommRing in CharTwo.add_eq_zero)
  have hmatch :
      ((@Fin.divNat 2 8) (pack ![(v + d) 0 + (v + d) 3, (v + d) 0 + (v + d) 1,
          (v + d) 0 + (v + d) 2, (v + d) 0]) =
        (@Fin.divNat 2 8) (pack ![v 0 + v 3, v 0 + v 1, v 0 + v 2, v 0]) ∧
      (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) (pack ![(v + d) 0 + (v + d) 3, (v + d) 0 + (v + d) 1,
          (v + d) 0 + (v + d) 2, (v + d) 0]) =
        (@Fin.divNat 4 2 ∘ @Fin.modNat 2 8) (pack ![v 0 + v 3, v 0 + v 1, v 0 + v 2, v 0])) ↔
        ∀ j, d j = d 0 := by
    rw [hpack, hpack]
    simp only [(block16_components ..).1, (block16_components ..).2.1,
      Pi.add_apply, h4, hbit]
    constructor
    · rintro ⟨h3, h1, h2⟩ j
      fin_cases j
      · rfl
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
    · intro h
      exact ⟨(h 3).symm, (h 1).symm, (h 2).symm⟩
  by_cases hd : ∀ j, d j = d 0
  · obtain ⟨e, rfl⟩ : ∃ e : Fin 2, d = fun _ => e := ⟨d 0, funext hd⟩
    simp only [mul_ite, ite_mul, Matrix.mul_smul, Matrix.smul_mul,
      Finset.mul_sum, Finset.sum_mul, conjugate_matrix_unit, mul_zero, zero_mul]
    obtain ⟨a₀, a₁, a₂, a₃, hv⟩ : ∃ a₀ a₁ a₂ a₃, v = ![a₀, a₁, a₂, a₃] :=
      ⟨v 0, v 1, v 2, v 3, by funext j; fin_cases j <;> rfl⟩
    subst v
    fin_cases a₀ <;> fin_cases a₁ <;> fin_cases a₂ <;> fin_cases a₃ <;> fin_cases e <;>
      (delta pack pathPhase Fin.divNat Fin.modNat Function.comp block16;
        norm_num [Fin.sum_univ_succ, Function.update_apply]) <;>
      (try simp only [← Matrix.single_neg]) <;> module
  · rw [ite_eq_right (mt hmatch.mp hd)]
    simp only [ite_eq_right hd, smul_zero, mul_zero, zero_mul]
def gauge (n : ℕ) (e : Fin 2) (x : Fin n → Fin 2) : ℂ :=
  (-1 : ℂ) ^ (e.val * ∑ j : Fin n, (x j).val * (x (site j 1)).val)
lemma site_injective (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (k l : Fin 4) :
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
  fin_cases k <;> (delta windowUpdate; simp [h01, h02, h03, h12, h13, h23])
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
  (delta windowUpdate; simp only [Function.update_apply])
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
      _ ↔ _ := by simpa only [true_and] using hi u x (windowCode i u)
  have hsv : windowUpdate i y (windowCode i v) = v ↔
      windowUpdate i v (windowCode i y) = y := by
    calc
      _ ↔ v = windowUpdate i y (windowCode i v) := eq_comm
      _ ↔ _ := by simpa only [true_and] using hi v y (windowCode i v)
  change (∑ p : Fin 16, ∑ q : Fin 16,
    localChannel (Matrix.single p q 1) (windowCode i x) (windowCode i y) *
      Matrix.single u v 1 (windowUpdate i x p) (windowUpdate i y q)) = _
  simp only [Matrix.single_apply, hi, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, hri, hrj]
  simp [hsu, hsv, ite_and, mul_ite, Finset.sum_ite_irrel]
noncomputable def windowLM (n : ℕ) (i : Fin n) :
    Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) where
  toFun := windowChannel n i
  map_add' := by
    intro a b
    ext u v
    (delta windowChannel; simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib])
  map_smul' := by
    intro c a
    ext u v
    (delta windowChannel; simp only [Matrix.smul_apply, RingHom.id_apply, smul_eq_mul,
      ← Finset.mul_sum, mul_left_comm])
private noncomputable def insertWindow (n : ℕ) (i : Fin n)
    (u v : Fin n → Fin 2) :
    Matrix (Fin 16) (Fin 16) ℂ →ₗ[ℂ] Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (Matrix.stdBasis ℂ (Fin 16) (Fin 16)).constr ℂ
    (fun pq => Matrix.single (windowUpdate i u pq.1) (windowUpdate i v pq.2) 1)
private lemma insertWindow_single (n : ℕ) (i : Fin n) (u v : Fin n → Fin 2)
    (p q : Fin 16) :
    insertWindow n i u v (Matrix.single p q 1) =
      Matrix.single (windowUpdate i u p) (windowUpdate i v q) 1 := by
  change (Matrix.stdBasis ℂ (Fin 16) (Fin 16)).constr ℂ _ _ = _
  rw [← Matrix.stdBasis_eq_single ℂ p q, Module.Basis.constr_basis]
private lemma window_single_insert (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (u v : Fin n → Fin 2) :
    windowChannel n i (Matrix.single u v 1) =
      insertWindow n i u v
        (localChannel (Matrix.single (windowCode i u) (windowCode i v) 1)) := by
  have hs (p q : Fin 16) :
      Matrix.single p q (localChannel (Matrix.single (windowCode i u) (windowCode i v) 1) p q) =
        localChannel (Matrix.single (windowCode i u) (windowCode i v) 1) p q •
          Matrix.single p q 1 := by
    rw [Matrix.smul_single]
    simp only [smul_eq_mul, mul_one]
  rw [window_single n hn]
  conv_rhs => rw [Matrix.matrix_eq_sum_single
    (localChannel (Matrix.single (windowCode i u) (windowCode i v) 1))]
  simp only [map_sum, hs, map_smul, insertWindow_single]
private def windowBits {n : ℕ} (i : Fin n) (x : Fin n → Fin 2) : Fin 4 → Fin 2 :=
  fun k => x (site i k.val)
private def middleUpdate {n : ℕ} (i : Fin n) (x : Fin n → Fin 2)
    (b c : Fin 2) : Fin n → Fin 2 :=
  Function.update (Function.update x (site i 1) b) (site i 2) c
private lemma site_zero {n : ℕ} (i : Fin n) : site i 0 = i := by
  apply Fin.ext
  change (i.val + 0) % n = i.val
  simp only [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
private lemma windowBits_middle (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (x : Fin n → Fin 2) (b c : Fin 2) :
    windowBits i (middleUpdate i x b c) = middleUpdate (0 : Fin 4) (windowBits i x) b c := by
  change windowBits i (middleUpdate i x b c) =
    Function.update (Function.update (windowBits i x) 1 b) 2 c
  have h (k l : Fin 4) := site_injective n hn i k l
  have h01 : site i 0 ≠ site i 1 := fun he => (by decide : (0 : Fin 4) ≠ 1) ((h 0 1).mp he)
  have h02 : site i 0 ≠ site i 2 := fun he => (by decide : (0 : Fin 4) ≠ 2) ((h 0 2).mp he)
  have h12 : site i 1 ≠ site i 2 := fun he => (by decide : (1 : Fin 4) ≠ 2) ((h 1 2).mp he)
  have h31 : site i 3 ≠ site i 1 := fun he => (by decide : (3 : Fin 4) ≠ 1) ((h 3 1).mp he)
  have h32 : site i 3 ≠ site i 2 := fun he => (by decide : (3 : Fin 4) ≠ 2) ((h 3 2).mp he)
  funext k
  fin_cases k <;> (delta windowBits middleUpdate; simp [h01, h02, h12, h31, h32])
private lemma windowUpdate_middle_add (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ x : Fin n → Fin 2) (b c : Fin 2) :
    windowUpdate i (x + δ) (pack (middleUpdate (0 : Fin 4) (windowBits i x) b c + windowBits i δ)) =
      middleUpdate i x b c + δ := by
  have digit_pack (v : Fin 4 → Fin 2) (k : Fin 4) :
      digit (pack v) (3 - k.val) = v k := by
    have h (a b c d : Fin 2) (j : Fin 4) :
        digit (pack ![a, b, c, d]) (3 - j.val) = ![a, b, c, d] j := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases j <;> rfl
    have hv : ![v 0, v 1, v 2, v 3] = v := by funext j; fin_cases j <;> rfl
    simpa only [hv] using h (v 0) (v 1) (v 2) (v 3) k
  funext j
  by_cases hj : ∃ k : Fin 4, j = site i k.val
  · obtain ⟨k, rfl⟩ := hj
    rw [window_update_site n hn, digit_pack]
    change middleUpdate (0 : Fin 4) (windowBits i x) b c k + δ (site i k.val) = _
    rw [← windowBits_middle n hn]
    rfl
  · have h (k : Fin 4) : j ≠ site i k.val := fun he => hj ⟨k, he⟩
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    change j ≠ site i 0 at h0
    change j ≠ site i 1 at h1
    change j ≠ site i 2 at h2
    change j ≠ site i 3 at h3
    (delta windowUpdate middleUpdate; simp [h0, h1, h2, h3])
private lemma windowUpdate_middle (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (x : Fin n → Fin 2) (b c : Fin 2) :
    windowUpdate i x (pack (middleUpdate (0 : Fin 4) (windowBits i x) b c)) =
      middleUpdate i x b c := by
  have hz : windowBits i (0 : Fin n → Fin 2) = 0 := rfl
  simpa only [hz, add_zero] using windowUpdate_middle_add n hn i 0 x b c
def goodWindow {n : ℕ} (i : Fin n) (δ : Fin n → Fin 2) : Prop :=
  ∀ k : Fin 4, δ (site i k.val) = δ i
private lemma window_matrix_unit (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ x : Fin n → Fin 2) :
    windowChannel n i (Matrix.single (x + δ) x 1) =
      if goodWindow i δ then
        (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
          let y := middleUpdate i x b c
          (-1 : ℂ) ^ ((δ i).val * (pathPhase (windowBits i x) + pathPhase (windowBits i y))) •
            Matrix.single (y + δ) y 1
      else 0 := by
  rw [window_single_insert n hn]
  have hc (y : Fin n → Fin 2) : windowCode i y = pack (windowBits i y) := rfl
  have ha : windowBits i (x + δ) = windowBits i x + windowBits i δ := rfl
  rw [hc, hc, ha, local_matrix_unit]
  have hg : (∀ k, windowBits i δ k = windowBits i δ 0) ↔ goodWindow i δ := by
    (delta windowBits goodWindow; simp only [Fin.val_zero, site_zero])
  simp only [hg]
  split_ifs with h
  · change insertWindow n i (x + δ) x
      ((4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
        (-1 : ℂ) ^ ((windowBits i δ 0).val *
          (pathPhase (windowBits i x) +
            pathPhase (middleUpdate (0 : Fin 4) (windowBits i x) b c))) •
          Matrix.single (pack (middleUpdate (0 : Fin 4) (windowBits i x) b c + windowBits i δ))
            (pack (middleUpdate (0 : Fin 4) (windowBits i x) b c)) 1) = _
    simp only [map_smul, map_sum, insertWindow_single, windowUpdate_middle_add n hn,
      windowUpdate_middle n hn, windowBits_middle n hn]
    have h0 : windowBits i δ 0 = δ i := congrArg δ (site_zero i)
    simp only [h0]
  · exact map_zero _
def sectorGauge (n : ℕ) (δ x : Fin n → Fin 2) : ℂ :=
  (-1 : ℂ) ^ ∑ j : Fin n, (δ j).val * (x j).val * (x (site j 1)).val
def gaugedUnit (n : ℕ) (δ x : Fin n → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  sectorGauge n δ x • Matrix.single (x + δ) x 1
lemma sectorGauge_const (n : ℕ) (e : Fin 2) (x : Fin n → Fin 2) :
    sectorGauge n (fun _ => e) x = gauge n e x := by
  change (-1 : ℂ) ^ (∑ j, e.val * (x j).val * (x (site j 1)).val) = _
  congr 1
  simp only [Finset.mul_sum, mul_assoc]
lemma sectorGauge_mul_self (n : ℕ) (δ x : Fin n → Fin 2) :
    sectorGauge n δ x * sectorGauge n δ x = 1 :=
  pow_mul_pow_eq_one _ (by norm_num : (-1 : ℂ) * (-1) = 1)
private lemma site_add {n : ℕ} (i : Fin n) (a b : ℕ) :
    site (site i a) b = site i (a + b) := by
  apply Fin.ext
  change ((i.val + a) % n + b) % n = (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]
lemma site_succ_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => site i 1) := by
  intro i j h
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  apply add_left_injective (1 : Fin n)
  apply Fin.ext
  simpa only [Fin.val_add, Fin.val_one', Nat.add_mod_mod] using
    (show (i.val + 1) % n = (j.val + 1) % n from congrArg Fin.val h)

private lemma middle_edge_unchanged (n : ℕ) (i : Fin n)
    (x : Fin n → Fin 2) (b c : Fin 2) (j : Fin n)
    (hj : j ∉ ({i, site i 1, site i 2} : Finset (Fin n))) :
    middleUpdate i x b c j = x j ∧
      middleUpdate i x b c (site j 1) = x (site j 1) := by
  have h0 : j ≠ i := fun h => hj (by simp [h])
  have h1 : j ≠ site i 1 := fun h => hj (by simp [h])
  have h2 : j ≠ site i 2 := fun h => hj (by simp [h])
  have hs1 : site j 1 ≠ site i 1 := fun h => h0 (site_succ_injective n h)
  have hs2 : site j 1 ≠ site i 2 := by
    intro h
    have he : site j 1 = site (site i 1) 1 := by simpa only [site_add] using h
    exact h1 (site_succ_injective n he)
  (delta middleUpdate; simp [h1, h2, hs1, hs2])
private lemma sectorGauge_phase_change (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ x : Fin n → Fin 2) (b c : Fin 2) (hδ : goodWindow i δ) :
    sectorGauge n δ x * sectorGauge n δ (middleUpdate i x b c) =
      (-1 : ℂ) ^ ((δ i).val *
        (pathPhase (windowBits i x) + pathPhase (windowBits i (middleUpdate i x b c)))) := by
  let y := middleUpdate i x b c
  let f := fun j : Fin n => (-1 : ℂ) ^ ((δ j).val * (x j).val * (x (site j 1)).val) *
    (-1 : ℂ) ^ ((δ j).val * (y j).val * (y (site j 1)).val)
  have hg (z : Fin n → Fin 2) : sectorGauge n δ z =
      ∏ j : Fin n, (-1 : ℂ) ^ ((δ j).val * (z j).val * (z (site j 1)).val) :=
    (Finset.prod_pow_eq_pow_sum _ _ _).symm
  have hout (j : Fin n) (hj : j ∉ ({i, site i 1, site i 2} : Finset (Fin n))) : f j = 1 := by
    obtain ⟨h1, h2⟩ := middle_edge_unchanged n i x b c j hj
    change (-1 : ℂ) ^ _ * (-1 : ℂ) ^ ((δ j).val *
      (middleUpdate i x b c j).val * (middleUpdate i x b c (site j 1)).val) = 1
    rw [h1, h2]
    exact pow_mul_pow_eq_one _ (by norm_num : (-1 : ℂ) * (-1) = 1)
  have hp : (∏ j : Fin n, f j) = ∏ j ∈ ({i, site i 1, site i 2} : Finset (Fin n)), f j := by
    symm
    exact Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => hout j hj)
  rw [hg, hg, ← Finset.prod_mul_distrib]
  change (∏ j : Fin n, f j) = _
  rw [hp]
  have h01 : i ≠ site i 1 := fun h =>
    (by decide : (0 : Fin 4) ≠ 1) ((site_injective n hn i 0 1).mp ((site_zero i).trans h))
  have h02 : i ≠ site i 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) ((site_injective n hn i 0 2).mp ((site_zero i).trans h))
  have h12 : site i 1 ≠ site i 2 :=
    fun h => (by decide : (1 : Fin 4) ≠ 2) ((site_injective n hn i 1 2).mp h)
  have hd1 := hδ 1
  have hd2 := hδ 2
  change δ (site i 1) = δ i at hd1
  change δ (site i 2) = δ i at hd2
  simp only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
    Finset.mem_singleton, h01, h02, h12, or_self, not_false_eq_true, f,
    site_add, hd1, hd2]
  (delta pathPhase windowBits; simp only [Fin.val_zero, site_zero])
  change _ = (-1 : ℂ) ^ ((δ i).val *
    ((x i).val * (x (site i 1)).val + (x (site i 1)).val * (x (site i 2)).val +
      (x (site i 2)).val * (x (site i 3)).val +
      ((y i).val * (y (site i 1)).val + (y (site i 1)).val * (y (site i 2)).val +
      (y (site i 2)).val * (y (site i 3)).val)))
  simp only [← pow_add]
  congr 1
  ring
lemma gauged_window_sector (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ x : Fin n → Fin 2) :
    windowChannel n i (gaugedUnit n δ x) =
      if goodWindow i δ then
        (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
          gaugedUnit n δ (middleUpdate i x b c)
      else 0 := by
  change windowLM n i (sectorGauge n δ x • Matrix.single (x + δ) x 1) = _
  rw [map_smul]
  change sectorGauge n δ x • windowChannel n i (Matrix.single (x + δ) x 1) = _
  rw [window_matrix_unit n hn]
  split_ifs with h
  · rw [smul_comm]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [smul_smul]
    change _ = sectorGauge n δ (middleUpdate i x b c) • _
    congr 1
    rw [← sectorGauge_phase_change n hn i δ x b c h,
      ← mul_assoc, sectorGauge_mul_self, one_mul]
  · exact smul_zero _
lemma matrix_linearMap_ext_gauged (n : ℕ)
    {f g : Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)}
    (h : ∀ δ x, f (gaugedUnit n δ x) = g (gaugedUnit n δ x)) : f = g := by
  apply (Matrix.stdBasis ℂ (Fin n → Fin 2) (Fin n → Fin 2)).ext
  rintro ⟨u, v⟩
  rw [Matrix.stdBasis_eq_single]
  have hv : v + (u + v) = u := by
    funext j
    exact (congrArg ((v j) + ·) (add_comm (u j) (v j))).trans
      (open scoped Fin.CommRing in CharTwo.add_cancel_left (v j) (u j))
  have hu : Matrix.single u v (1 : ℂ) = sectorGauge n (u + v) v • gaugedUnit n (u + v) v := by
    change _ = sectorGauge n (u + v) v •
      (sectorGauge n (u + v) v • Matrix.single (v + (u + v)) v 1)
    rw [smul_smul, sectorGauge_mul_self, one_smul, hv]
  rw [hu, map_smul, map_smul, h]
set_option maxHeartbeats 800000 in
-- Expanding both window actions requires the two coordinate averages.
lemma window_channels_commute (n : ℕ) (hn : 4 ≤ n) (i j : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    windowChannel n i (windowChannel n j a) = windowChannel n j (windowChannel n i a) := by
  have hact (k : Fin n) (δ x : Fin n → Fin 2) :
      windowLM n k (gaugedUnit n δ x) = if goodWindow k δ then
        avg n {site k 1, site k 2} (gaugedUnit n δ) x else 0 := by
    change windowChannel n k (gaugedUnit n δ x) = _
    rw [gauged_window_sector n hn]
    split_ifs
    · have h12 : site k 1 ≠ site k 2 := fun h =>
        (by decide : (1 : Fin 4) ≠ 2) ((site_injective n hn k 1 2).mp h)
      rw [avg_pair_apply n _ _ h12]
      rfl
    · rfl
  have heq : windowLM n i * windowLM n j = windowLM n j * windowLM n i := by
    apply matrix_linearMap_ext_gauged n
    intro δ x
    change windowLM n i (windowLM n j (gaugedUnit n δ x)) =
      windowLM n j (windowLM n i (gaugedUnit n δ x))
    rw [hact, hact]
    by_cases hi : goodWindow i δ <;> by_cases hj : goodWindow j δ
    · simp only [ite_eq_left hi, ite_eq_left hj]
      rw [avg_map, avg_map]
      simp only [hact, ite_eq_left hi, ite_eq_left hj]
      exact congrArg (fun l => l (gaugedUnit n δ) x)
        (avg_commute (V := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
          n {site j 1, site j 2} {site i 1, site i 2}).eq
    · simp only [ite_eq_left hi, ite_eq_right hj, map_zero]
      rw [avg_map]
      simp only [hact, ite_eq_right hj]
      exact (congrFun (map_zero (avg n {site i 1, site i 2})) x).symm
    · simp only [ite_eq_right hi, ite_eq_left hj, map_zero]
      rw [avg_map]
      simp only [hact, ite_eq_right hi]
      exact congrFun (map_zero (avg n {site j 1, site j 2})) x
    · simp only [ite_eq_right hi, ite_eq_right hj, map_zero]
  exact congrArg (fun l => l a) heq
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
-- Standard-basis coordinates identify the superoperator action.
lemma window_superoperator_action (n : ℕ) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : Fin n → Fin 2) :
    (windowSuperoperator n i).mulVec (fun p => a p.1 p.2) (x, y) =
      windowChannel n i a x y := by
  classical
  let b := Matrix.stdBasis ℂ (Fin n → Fin 2) (Fin n → Fin 2)
  have hr (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (p : (Fin n → Fin 2) × (Fin n → Fin 2)) : b.repr M p = M p.1 p.2 := by
    simp [b, Matrix.stdBasis]
  have hb : LinearMap.toMatrix b b (windowLM n i) = windowSuperoperator n i := by
    ext p q
    rw [LinearMap.toMatrix_apply, hr]
    change windowChannel n i (b q) p.1 p.2 = _
    rw [show b q = Matrix.single q.1 q.2 1 from Matrix.stdBasis_eq_single ℂ q.1 q.2]
    rfl
  have h := congrArg (fun v => v (x, y))
    (LinearMap.toMatrix_mulVec_repr b b (windowLM n i) a)
  rw [hb] at h
  change (∑ p, windowSuperoperator n i (x, y) p * b.repr a p) =
    b.repr ((windowLM n i) a) (x, y) at h
  change (∑ p, windowSuperoperator n i (x, y) p * a p.1 p.2) = _
  change (∑ p, windowSuperoperator n i (x, y) p * b.repr a p) =
    b.repr (windowChannel n i a) (x, y) at h
  simpa only [hr] using h
lemma window_idempotent (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    IsIdempotentElem (windowSuperoperator n i) := by
  change windowSuperoperator n i * windowSuperoperator n i = windowSuperoperator n i
  ext x y
  change (windowSuperoperator n i).mulVec
    (fun p => windowChannel n i (Matrix.single y.1 y.2 1) p.1 p.2) x = _
  rw [window_superoperator_action, window_channel_comp n hn]
  rfl
end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
