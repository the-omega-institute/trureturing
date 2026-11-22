/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Width-four scalar column Gram constructions and the large-ratio classification. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel

/-! Rectangular coordinate embeddings and coefficient-kernel bounds at tensor width four. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase

private def coordinateMatrix {I J : Type*} [DecidableEq J] (e : I ↪ J) :
    Matrix J I ℂ := fun j i => if e i = j then 1 else 0

private theorem coordinate_gram {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ↪ J) : (coordinateMatrix e)ᴴ * coordinateMatrix e = 1 := by
  have h : coordinateMatrix e = (1 : Matrix J J ℂ).submatrix (Equiv.refl J) e := by
    ext j i
    simp [coordinateMatrix, Matrix.one_apply, eq_comm]
  rw [h, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv _ _ e (Equiv.refl J) e, Matrix.one_mul,
    Matrix.submatrix_one_embedding]

/-- A sum of four rectangular Kronecker products has the specified scalar column Gram. -/
def FourScalarGram (a b c d : ℕ) (lam : ℝ) : Prop :=
  ∃ (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ),
    (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)

/-- The eight sufficient rows in one orientation. All bounds use natural numbers. -/
def Staircase (a b c d : ℕ) : Prop :=
  (b ≤ a ∧ c ≤ d) ∨
  (a < b ∧ 3 * b ≤ 4 * a ∧ 4 * c ≤ 3 * d) ∨
  (4 * a < 3 * b ∧ 2 * b ≤ 3 * a ∧ 3 * c ≤ 2 * d) ∨
  (3 * a < 2 * b ∧ 3 * b ≤ 5 * a ∧ 5 * c ≤ 3 * d) ∨
  (5 * a < 3 * b ∧ b ≤ 2 * a ∧ 2 * c ≤ d) ∨
  (2 * a < b ∧ 2 * b ≤ 5 * a ∧ 5 * c ≤ 2 * d) ∨
  (5 * a < 2 * b ∧ b ≤ 3 * a ∧ 3 * c ≤ d) ∨
  (3 * a < b ∧ b ≤ 4 * a ∧ 4 * c ≤ d)

private def tensorSum {a b c d k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (Y : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ :=
  ∑ i, kronecker (X i) (Y i)

private theorem scale_tensor {a b c d k : ℕ} (z : ℂ)
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (Y : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    tensorSum (fun i => z • X i) Y = z • tensorSum X Y := by
  rw [tensorSum, tensorSum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => Matrix.smul_kronecker _ _ _)

private theorem of_unit_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (h : (tensorSum X Y)ᴴ * tensorSum X Y = 1) : FourScalarGram a b c d lam := by
  refine ⟨fun i => (Real.sqrt lam : ℂ) • X i, Y, ?_⟩
  change (tensorSum _ _)ᴴ * tensorSum _ _ = _
  rw [scale_tensor, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h]
  have hsquare : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hlam.le
  simp only [Complex.star_def, Complex.conj_ofReal, hsquare]

private theorem swap_gram {a b c d : ℕ} {lam : ℝ}
    (h : FourScalarGram a b c d lam) : FourScalarGram d c b a lam := by
  obtain ⟨X, Y, h⟩ := h
  let rows := Equiv.prodComm (Fin d) (Fin a)
  let cols := Equiv.prodComm (Fin c) (Fin b)
  have heq : tensorSum Y X = (tensorSum X Y).submatrix rows cols := by
    ext i j
    change (∑ r : Fin 4, Y r i.1 j.1 * X r i.2 j.2) =
      ∑ r : Fin 4, X r i.2 j.2 * Y r i.1 j.1
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  refine ⟨Y, X, ?_⟩
  change (tensorSum X Y)ᴴ * tensorSum X Y = _ at h
  change (tensorSum Y X)ᴴ * tensorSum Y X = _
  rw [heq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ cols rows cols, h]
  change (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ).submatrix cols cols = _
  rw [Matrix.submatrix_one_equiv]

private structure Rectangle where
  leftIn : ℕ
  rightIn : ℕ
  leftOut : ℕ
  rightOut : ℕ
  width : ℕ
  height : ℕ

private def Rectangle.covers (R : Rectangle) (x y : ℕ) : Prop :=
  R.leftIn ≤ x ∧ x < R.leftIn + R.width ∧ R.rightIn ≤ y ∧ y < R.rightIn + R.height

private def Rectangle.image (R : Rectangle) (x y : ℕ) : ℕ × ℕ :=
  (R.leftOut + (x - R.leftIn), R.rightOut + (y - R.rightIn))

private theorem rectangles_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (R : Fin 4 → Rectangle)
    (hcover : ∀ x < b, ∀ y < c, ∃ r, (R r).covers x y)
    (hunique : ∀ r s x y, x < b → y < c → (R r).covers x y → (R s).covers x y → r = s)
    (hfit : ∀ r x y, x < b → y < c → (R r).covers x y →
      ((R r).image x y).1 < a ∧ ((R r).image x y).2 < d)
    (hsep : ∀ r s x y u v, r ≠ s → x < b → y < c → u < b → v < c →
      (R r).covers x y → (R s).covers u v → (R r).image x y ≠ (R s).image u v) :
    FourScalarGram a b c d lam := by
  classical
  let slot (p : Fin b × Fin c) := (hcover p.1 p.1.isLt p.2 p.2.isLt).choose
  have hslot (p : Fin b × Fin c) : (R (slot p)).covers p.1 p.2 :=
    (hcover p.1 p.1.isLt p.2 p.2.isLt).choose_spec
  let image (p : Fin b × Fin c) := (R (slot p)).image p.1 p.2
  have hbound (p : Fin b × Fin c) := hfit (slot p) p.1 p.2 p.1.isLt p.2.isLt (hslot p)
  let e : (Fin b × Fin c) ↪ (Fin a × Fin d) :=
    ⟨fun p => (⟨(image p).1, (hbound p).1⟩, ⟨(image p).2, (hbound p).2⟩), by
      intro p q he
      have himage : image p = image q := congrArg
        (fun z : Fin a × Fin d => (z.1.val, z.2.val)) he
      have hs : slot p = slot q := by
        by_contra hne
        exact hsep _ _ _ _ _ _ hne p.1.isLt p.2.isLt q.1.isLt q.2.isLt
          (hslot p) (hslot q) himage
      have hp := (hslot p).1
      have hp' := (hslot p).2.2.1
      have hq := (hslot q).1
      have hq' := (hslot q).2.2.1
      change (R (slot p)).image p.1 p.2 = (R (slot q)).image q.1 q.2 at himage
      rw [← hs] at himage hq hq'
      have hl := congrArg Prod.fst himage
      have hr := congrArg Prod.snd himage
      dsimp [Rectangle.image] at hl hr
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩
  let X (r : Fin 4) : Matrix (Fin a) (Fin b) ℂ :=
    fun i x => if (R r).leftIn ≤ x.val ∧ x.val < (R r).leftIn + (R r).width ∧
      i.val = ((R r).image x 0).1 then 1 else 0
  let Y (r : Fin 4) : Matrix (Fin d) (Fin c) ℂ :=
    fun j y => if (R r).rightIn ≤ y.val ∧ y.val < (R r).rightIn + (R r).height ∧
      j.val = ((R r).image 0 y).2 then 1 else 0
  have hentry (r : Fin 4) (i : Fin a × Fin d) (p : Fin b × Fin c) :
      X r i.1 p.1 * Y r i.2 p.2 =
        if (R r).covers p.1 p.2 ∧ (R r).image p.1 p.2 = (i.1.val, i.2.val)
        then 1 else 0 := by
    dsimp only [X, Y, Rectangle.image, Rectangle.covers]
    rw [Prod.mk.injEq]
    split_ifs <;> simp_all [eq_comm] <;> tauto
  have hroute : tensorSum X Y = coordinateMatrix e := by
    ext i p
    change (∑ r : Fin 4, X r i.1 p.1 * Y r i.2 p.2) = if e p = i then 1 else 0
    rw [Finset.sum_eq_single (slot p)]
    · rw [hentry, if_congr ?_ rfl rfl]
      rw [and_iff_right (hslot p)]
      exact ⟨fun h => Prod.ext (Fin.ext (congrArg Prod.fst h))
        (Fin.ext (congrArg Prod.snd h)), fun h =>
          congrArg (fun z : Fin a × Fin d => (z.1.val, z.2.val)) h⟩
    · intro r _ hne
      rw [hentry, if_neg]
      exact fun h => hne (hunique r (slot p) _ _ p.1.isLt p.2.isLt h.1 (hslot p))
    · simp
  exact of_unit_gram hlam X Y (by rw [hroute, coordinate_gram])

private def blocks (a c : ℕ) : Fin 4 → Rectangle :=
  ![⟨0, 0, 0, 0, a, c⟩, ⟨a, 0, 0, c, a, c⟩,
    ⟨2 * a, 0, 0, 2 * c, a, c⟩, ⟨3 * a, 0, 0, 3 * c, a, c⟩]

set_option maxHeartbeats 1800000 in
private theorem blocks_gram {a b c d k : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hk : k ≤ 4) (hb : b ≤ k * a) (hd : k * c ≤ d) : FourScalarGram a b c d lam := by
  have hba : b ≤ 4 * a := hb.trans (Nat.mul_le_mul_right _ hk)
  apply rectangles_gram hlam (blocks a c)
  · intro x hx y hy
    by_cases h₀ : x < a
    · exact ⟨0, by simp [blocks, Rectangle.covers, h₀, hy]⟩
    by_cases h₁ : x < 2 * a
    · exact ⟨1, by simp [blocks, Rectangle.covers, hy] <;> omega⟩
    by_cases h₂ : x < 3 * a
    · exact ⟨2, by simp [blocks, Rectangle.covers, hy] <;> omega⟩
    exact ⟨3, by simp [blocks, Rectangle.covers, hy] <;> omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [blocks, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    interval_cases k <;> fin_cases r <;>
      simp_all [blocks, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [blocks, Rectangle.covers, Rectangle.image] <;> omega

private def thirds (a b c d : ℕ) : Fin 4 → Rectangle :=
  let excess := b - a
  let spare := d - c
  ![⟨0, 0, 0, 0, a, c⟩, ⟨a, 0, 0, c, excess, spare⟩,
    ⟨a, spare, excess, c, excess, spare⟩, ⟨a, 2 * spare, 2 * excess, c, excess, spare⟩]

set_option maxHeartbeats 1800000 in
private theorem thirds_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hb : 3 * b ≤ 4 * a) (hd : 4 * c ≤ 3 * d) : FourScalarGram a b c d lam := by
  apply rectangles_gram hlam (thirds a b c d)
  · intro x hx y hy
    by_cases h₀ : x < a
    · exact ⟨0, by simp [thirds, Rectangle.covers, h₀, hy]⟩
    by_cases h₁ : y < d - c
    · exact ⟨1, by simp [thirds, Rectangle.covers] <;> omega⟩
    by_cases h₂ : y < 2 * (d - c)
    · exact ⟨2, by simp [thirds, Rectangle.covers] <;> omega⟩
    exact ⟨3, by simp [thirds, Rectangle.covers] <;> omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [thirds, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    fin_cases r <;> simp_all [thirds, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hl := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [thirds, Rectangle.covers, Rectangle.image] <;> omega

private def halves (a b c d : ℕ) : Fin 4 → Rectangle :=
  let excess := b - a
  let spare := d - c
  ![⟨0, 0, 0, 0, a, c⟩, ⟨a, 0, 0, c, excess, spare⟩,
    ⟨a, spare, excess, c, excess, spare⟩, ⟨0, 0, 0, 0, 0, 0⟩]

set_option maxHeartbeats 1800000 in
private theorem halves_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hb : 2 * b ≤ 3 * a) (hd : 3 * c ≤ 2 * d) : FourScalarGram a b c d lam := by
  apply rectangles_gram hlam (halves a b c d)
  · intro x hx y hy
    by_cases h₀ : x < a
    · exact ⟨0, by simp [halves, Rectangle.covers, h₀, hy]⟩
    by_cases h₁ : y < d - c
    · exact ⟨1, by simp [halves, Rectangle.covers] <;> omega⟩
    exact ⟨2, by simp [halves, Rectangle.covers] <;> omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [halves, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    fin_cases r <;> simp_all [halves, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hl := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [halves, Rectangle.covers, Rectangle.image] <;> omega

private def threeFifths (a b c d : ℕ) : Fin 4 → Rectangle :=
  let excess := b - a
  let spare := d - c
  let tail := c - spare
  let left := a - excess
  ![⟨0, 0, 0, 0, a, c⟩, ⟨a, 0, 0, c, excess, spare⟩,
    ⟨a, spare, excess, c, left, tail⟩, ⟨a + left, spare, excess, c + tail, left, tail⟩]

set_option maxHeartbeats 1800000 in
private theorem three_fifths_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hb : 3 * b ≤ 5 * a) (hd : 5 * c ≤ 3 * d) : FourScalarGram a b c d lam := by
  by_cases hroom : 2 * c ≤ d
  · exact blocks_gram (k := 2) hlam (by omega) (by omega) hroom
  apply rectangles_gram hlam (threeFifths a b c d)
  · intro x hx y hy
    by_cases h₀ : x < a
    · exact ⟨0, by simp [threeFifths, Rectangle.covers, h₀, hy]⟩
    by_cases h₁ : y < d - c
    · exact ⟨1, by simp [threeFifths, Rectangle.covers] <;> omega⟩
    by_cases h₂ : x < a + (a - (b - a))
    · exact ⟨2, by simp [threeFifths, Rectangle.covers] <;> omega⟩
    exact ⟨3, by simp [threeFifths, Rectangle.covers] <;> omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [threeFifths, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    fin_cases r <;> simp_all [threeFifths, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hl := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [threeFifths, Rectangle.covers, Rectangle.image] <;> omega

private def twoFifths (a b c d : ℕ) : Fin 4 → Rectangle :=
  let excess := b - 2 * a
  let spare := d - 2 * c
  ![⟨0, 0, 0, 0, a, c⟩, ⟨a, 0, 0, c, a, c⟩,
    ⟨2 * a, 0, 0, 2 * c, excess, spare⟩,
    ⟨2 * a, spare, excess, 2 * c, excess, spare⟩]

set_option maxHeartbeats 1800000 in
private theorem two_fifths_gram {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hb : 2 * b ≤ 5 * a) (hd : 5 * c ≤ 2 * d) : FourScalarGram a b c d lam := by
  apply rectangles_gram hlam (twoFifths a b c d)
  · intro x hx y hy
    by_cases h₀ : x < a
    · exact ⟨0, by simp [twoFifths, Rectangle.covers, h₀, hy]⟩
    by_cases h₁ : x < 2 * a
    · exact ⟨1, by simp [twoFifths, Rectangle.covers, hy] <;> omega⟩
    by_cases h₂ : y < d - 2 * c
    · exact ⟨2, by simp [twoFifths, Rectangle.covers] <;> omega⟩
    exact ⟨3, by simp [twoFifths, Rectangle.covers] <;> omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [twoFifths, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    fin_cases r <;> simp_all [twoFifths, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hl := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [twoFifths, Rectangle.covers, Rectangle.image] <;> omega

private theorem one_orientation {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (h : Staircase a b c d) : FourScalarGram a b c d lam := by
  unfold Staircase at h
  rcases h with ⟨hb, hd⟩ | ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩ |
    ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩
  · exact blocks_gram (k := 1) hlam (by decide) (by simpa using hb) (by simpa using hd)
  · exact thirds_gram hlam hb hd
  · exact halves_gram hlam hb hd
  · exact three_fifths_gram hlam hb hd
  · exact blocks_gram (k := 2) hlam (by decide) hb hd
  · exact two_fifths_gram hlam hb hd
  · exact blocks_gram (k := 3) hlam (by decide) hb hd
  · exact blocks_gram (k := 4) hlam (by decide) hb hd

/-- Empty inputs and the eight rows in either orientation admit the prescribed Gram. -/
theorem staircase_sufficient (a b c d : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (h : b = 0 ∨ c = 0 ∨ Staircase a b c d ∨ Staircase d c b a) :
    FourScalarGram a b c d lam := by
  rcases h with hb | hc | h | h
  · subst b
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · subst c
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · exact one_orientation hlam h
  · exact swap_gram (one_orientation hlam h)

/-- At the first staircase corner, four Kronecker terms are sufficient and three are impossible. -/
theorem exact_width_four_at_three_four (lam : ℝ) (hlam : 0 < lam) :
    FourScalarGram 3 4 3 4 lam ∧
    ¬ ∃ (X : Fin 3 → Matrix (Fin 3) (Fin 4) ℂ) (Y : Fin 3 → Matrix (Fin 4) (Fin 3) ℂ),
      (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
        (lam : ℂ) • (1 : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℂ) := by
  refine ⟨thirds_gram hlam (by decide) (by decide), ?_⟩
  rintro ⟨X, Y, h⟩
  have hb := NativeThreeRectangularBound.native_three_rectangular_bound X Y lam hlam (by decide) h
  omega


open Module
open scoped ComplexOrder
open NativeRectangularBound (stackK stackK_gram block_kernel exact_whitening)
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening (mix mix_apply)
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
  (gram_identity_injective concatK concatK_gram rank_kronecker_one_general)

open NativeFourKernel (compression compression_star hermitian_rank_bound coefficient_geometry)

private theorem compression_add {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (T U : Matrix (Fin 4) (Fin 4) ℂ) :
    compression X (T + U) = compression X T + compression X U := by
  simp only [compression, Matrix.kronecker, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

private theorem compression_smul {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (z : ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ) :
    compression X (z • T) = z • compression X T := by
  simp only [compression, Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul]

private theorem compress_block {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1) (l m : Fin c) :
    compression X (fun r s => ((Y r)ᴴ * Y s) l m -
      (if r = s then if l = m then 1 else 0 else 0)) = 0 := by
  rw [compression, NativeRectangularBound.stackK_compression]
  exact block_kernel X Y hF hX l m


private theorem swap_tensor {a b c d k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (Y : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    tensorSum Y X = (tensorSum X Y).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  ext i j
  change (∑ r : Fin k, Y r i.1 j.1 * X r i.2 j.2) =
    ∑ r : Fin k, X r i.2 j.2 * Y r i.1 j.1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem unit_normalize {a b c d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (h : (tensorSum X Y)ᴴ * tensorSum X Y = (lam : ℂ) • 1) :
    (tensorSum (fun i => ((Real.sqrt lam)⁻¹ : ℂ) • X i) Y)ᴴ *
      tensorSum (fun i => ((Real.sqrt lam)⁻¹ : ℂ) • X i) Y = 1 := by
  have hs : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
  have hscale : ((Real.sqrt lam)⁻¹ : ℂ) * (((Real.sqrt lam)⁻¹ : ℂ) * (lam : ℂ)) = 1 := by
    exact_mod_cast (show (Real.sqrt lam)⁻¹ * ((Real.sqrt lam)⁻¹ * lam) = 1 by
      field_simp [hs]
      nlinarith [Real.sq_sqrt hlam.le])
  rw [scale_tensor, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    h, smul_smul, smul_smul]
  simp [Complex.star_def, hscale]

private theorem cut_dependent_left {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hX : ¬ LinearIndependent ℂ X) :
    ∃ (A : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (B : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      tensorSum A B = tensorSum X Y := by
  classical
  obtain ⟨g, hg, i, hi⟩ := (Fintype.not_linearIndependent_iff.mp hX)
  let A : Fin 3 → Matrix (Fin a) (Fin b) ℂ := fun j => X (i.succAbove j)
  let B : Fin 3 → Matrix (Fin d) (Fin c) ℂ := fun j =>
    Y (i.succAbove j) - (g (i.succAbove j) / g i) • Y i
  have hsplit : (∑ j : Fin 4, g j • X j) =
      g i • X i + ∑ j : Fin 3, g (i.succAbove j) • X (i.succAbove j) := by
    rw [Fin.univ_succAbove 3 i]
    simp [Finset.sum_map]
  have hXi : X i = ∑ j, (-(g (i.succAbove j) / g i)) • A j := by
    rw [hsplit, add_eq_zero_iff_eq_neg] at hg
    rw [(eq_inv_smul_iff₀ hi).mpr hg, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    simp [A, div_eq_mul_inv, smul_smul, neg_smul, mul_comm]
  have hsum : tensorSum X Y =
      kronecker (X i) (Y i) + ∑ j : Fin 3, kronecker (A j) (Y (i.succAbove j)) := by
    rw [tensorSum, Fin.univ_succAbove 3 i]
    simp [A, Finset.sum_map]
  refine ⟨A, B, ?_⟩
  rw [hsum, hXi]
  change (∑ j, (Matrix.kroneckerBilinear (R := ℂ)) _ _) =
    (Matrix.kroneckerBilinear (R := ℂ)) (∑ j, _) _ + ∑ j, _
  simp only [B, map_sum, LinearMap.sum_apply, map_sub, map_smul, LinearMap.smul_apply,
    ← Finset.sum_add_distrib, neg_smul, neg_add_eq_sub]
  exact Finset.sum_congr rfl (fun j _ => by rw [sub_eq_add_neg, add_comm])

private theorem cut_dependent_right {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hY : ¬ LinearIndependent ℂ Y) :
    ∃ (A : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (B : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      tensorSum A B = tensorSum X Y := by
  obtain ⟨B, A, h⟩ := cut_dependent_left Y X hY
  exact ⟨A, B, by rw [swap_tensor B A, swap_tensor Y X, h]⟩

private theorem stack_dimension {a b c d k : ℕ} (hc : 0 < c)
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (Y : Fin k → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1) : b ≤ k * a := by
  classical
  have hinj := gram_identity_injective (tensorSum X Y) hF
  let m : Fin c := ⟨0, hc⟩
  have hS : Function.Injective (stackK X).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    let v : Fin b × Fin c → ℂ := fun p => if p.2 = m then x p.1 else 0
    have hX (i : Fin k) (j : Fin a) : (X i *ᵥ x) j = 0 := congrFun hx (i, j)
    have hv : (tensorSum X Y).mulVecLin v = 0 := by
      ext ⟨i, j⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, tensorSum,
        Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul,
        Fintype.sum_prod_type, v, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Pi.zero_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro r _
      have h := hX r i
      change (∑ q : Fin b, X r i q * x q) = 0 at h
      simpa only [mul_assoc, mul_left_comm, ← Finset.mul_sum, h, mul_zero]
    have hv0 : v = 0 := hinj (hv.trans (map_zero _).symm)
    ext i
    simpa [v] using congrFun hv0 (i, m)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] using
    (LinearMap.finrank_le_finrank_of_injective hS)

private theorem hermitian_to_complex {a b : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (f : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] V)
    (h : ∀ T, T.IsHermitian → compression X T = 0 → f T = 0)
    (T : Matrix (Fin 4) (Fin 4) ℂ) (hT : compression X T = 0) : f T = 0 := by
  let P : Matrix (Fin 4) (Fin 4) ℂ := realPart T
  let Q : Matrix (Fin 4) (Fin 4) ℂ := imaginaryPart T
  have hstar : compression X Tᴴ = 0 := by rw [compression_star, hT, Matrix.conjTranspose_zero]
  have hp : P = (2⁻¹ : ℂ) • (T + Tᴴ) := by
    dsimp [P]
    rw [realPart_apply_coe]
    ext i j
    simp [Matrix.star_eq_conjTranspose, Complex.real_smul]
    norm_num
  have hq : Q = (-Complex.I * 2⁻¹) • (T + (-1 : ℂ) • Tᴴ) := by
    dsimp [Q]
    rw [imaginaryPart_apply_coe]
    ext i j
    simp [Matrix.star_eq_conjTranspose, Complex.real_smul]
    ring
  have hp0 : compression X P = 0 := by
    rw [hp, compression_smul, compression_add, hT, hstar, add_zero, smul_zero]
  have hq0 : compression X Q = 0 := by
    rw [hq, compression_smul, compression_add, compression_smul, hT, hstar, smul_zero,
      add_zero, smul_zero]
  rw [← realPart_add_I_smul_imaginaryPart T, map_add, map_smul]
  rw [h P (realPart T).property.isHermitian hp0, h Q (imaginaryPart T).property.isHermitian hq0]
  simp

private def rightBlock {c d : ℕ}
    (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ) (l m : Fin c) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun r s => ((Y r)ᴴ * Y s) l m

private def rightMix {c d k : ℕ}
    (E : Matrix (Fin 4) (Fin k) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (r : Fin k) : Matrix (Fin d) (Fin c) ℂ := ∑ s, E s r • Y s

private theorem mixed_right_block {c d k : ℕ}
    (E : Matrix (Fin 4) (Fin k) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (r s : Fin k) (l m : Fin c) :
    ((rightMix E Y r)ᴴ * rightMix E Y s) l m = (Eᴴ * rightBlock Y l m * E) r s := by
  classical
  simp only [rightMix, rightBlock, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem right_block_compression {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1) (l m : Fin c) :
    compression X (rightBlock Y l m -
      (if l = m then (1 : ℂ) else 0) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 0 := by
  convert compress_block X Y hF hX l m using 2
  ext r s
  by_cases h : r = s <;> simp [rightBlock, Matrix.one_apply, h]

private theorem neutral_dimension {a b c d k : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1) (hX : ∑ i, (X i)ᴴ * X i = 1)
    (E : Matrix (Fin 4) (Fin k) ℂ) (hE : E.rank = k)
    (hK : ∀ T, T.IsHermitian → compression X T = 0 → Eᴴ * T * E = 0) :
    k * c ≤ d := by
  let f : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    { toFun := fun T => Eᴴ * T * E
      map_add' := by intro T U; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro z T; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hGram (r s : Fin k) : (rightMix E Y r)ᴴ * rightMix E Y s =
      (Eᴴ * E) r s • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    ext l m
    have he := hermitian_to_complex X f hK _ (right_block_compression X Y hF hX l m)
    change Eᴴ * (rightBlock Y l m - (if l = m then (1 : ℂ) else 0) • 1) * E = 0 at he
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, sub_eq_zero] at he
    rw [mixed_right_block, he]
    simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]
  let W := concatK (rightMix E Y)
  have hW : Wᴴ * W = kronecker (Eᴴ * E) (1 : Matrix (Fin c) (Fin c) ℂ) :=
    concatK_gram _ _ hGram
  have hr : (Wᴴ * W).rank ≤ d :=
    (Matrix.rank_mul_le_right _ _).trans (by simpa using W.rank_le_card_height)
  rw [hW, rank_kronecker_one_general, Matrix.rank_conjTranspose_mul_self, hE] at hr
  simpa only [Nat.mul_comm] using hr

private theorem kernel_columns {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ L : Matrix (Fin n) (Fin (n - A.rank)) ℂ, Lᴴ * L = 1 ∧ A * L = 0 ∧
      ∀ {q : ℕ} (W : Matrix (Fin n) (Fin q) ℂ), A * W = 0 → L * (Lᴴ * W) = W := by
  classical
  let K := LinearMap.ker A.toEuclideanLin
  have hr : A.rank = finrank ℂ (LinearMap.range A.toEuclideanLin) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.rank_eq_finrank_range_toLin _ _ _
  have hK : finrank ℂ K = n - A.rank := by
    have h := A.toEuclideanLin.finrank_range_add_finrank_ker
    rw [← hr, finrank_euclideanSpace_fin] at h
    omega
  let B := (stdOrthonormalBasis ℂ K).reindex (finCongr hK)
  let L : Matrix (Fin n) (Fin (n - A.rank)) ℂ := fun i j => (B j).1 i
  have hL (j : Fin (n - A.rank)) : A *ᵥ (fun i => L i j) = 0 := by
    have h : A.toEuclideanLin (B j).1 = 0 := (B j).2
    exact (Matrix.ofLp_toLpLin A (B j).1).symm.trans (by rw [h]; rfl)
  have hL0 : Lᴴ * L = 1 := by
    ext i j
    rw [← inner_matrix_col_col, Matrix.one_apply]
    exact (orthonormal_iff_ite.mp B.orthonormal) i j
  refine ⟨L, hL0, ?_, ?_⟩
  · ext i j
    exact congrFun (hL j) i
  · intro q W hW
    let w (j : Fin q) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => W i j)
    have hw (j : Fin q) : w j ∈ K := by
      change A.toEuclideanLin (w j) = 0
      apply WithLp.ofLp_injective 2
      rw [Matrix.ofLp_toLpLin]
      ext i
      exact congrFun (congrFun hW i) j
    let Z : Matrix (Fin (n - A.rank)) (Fin q) ℂ :=
      fun i j => B.toBasis.repr ⟨w j, hw j⟩ i
    have hW' : W = L * Z := by
      ext i j
      have h := congrArg (fun x : K => x.1 i) (B.toBasis.sum_repr ⟨w j, hw j⟩)
      simpa [Z, L, Matrix.mul_apply, mul_comm, w] using h.symm
    rw [hW', ← Matrix.mul_assoc Lᴴ L Z, hL0, Matrix.one_mul]

private theorem common_kernel_reduction {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1)
    (hX : ∑ r, (X r)ᴴ * X r = 1)
    (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (hK : ∀ T, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0) :
    ∃ p, b ≤ p + a ∧
      ∃ (A : Fin 3 → Matrix (Fin a) (Fin p) ℂ)
        (B : Fin 3 → Matrix (Fin (d - c)) (Fin c) ℂ),
        (tensorSum A B)ᴴ * tensorSum A B = 1 := by
  classical
  let f : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun T => T *ᵥ v
      map_add' := by intro T U; exact Matrix.add_mulVec _ _ _
      map_smul' := by intro z T; exact Matrix.smul_mulVec _ _ _ }
  let Z := ∑ r, v r • Y r
  have hYZ (r : Fin 4) : (Y r)ᴴ * Z = v r • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    ext l m
    have h := congrFun (hermitian_to_complex X f hK _
      (right_block_compression X Y hF hX l m)) r
    change (∑ s, ((rightBlock Y l m - (if l = m then (1 : ℂ) else 0) • 1) r s) *
      v s) = 0 at h
    have he : ((rightBlock Y l m - (if l = m then (1 : ℂ) else 0) • 1) *ᵥ v) =
        (rightBlock Y l m) *ᵥ v - (if l = m then (1 : ℂ) else 0) • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hh := congrFun he r
    change ((rightBlock Y l m - (if l = m then (1 : ℂ) else 0) • 1) *ᵥ v) r = 0 at h
    rw [h] at hh
    have hsum := sub_eq_zero.mp hh.symm
    simpa [Z, Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.mulVec, dotProduct, rightBlock, Matrix.one_apply, mul_comm] using hsum
  let z := star v ⬝ᵥ v
  have hz : z ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
  have hZ : Zᴴ * Z = z • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    rw [show Zᴴ = ∑ r, star (v r) • (Y r)ᴴ by
      simp [Z, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]]
    simp only [Matrix.sum_mul, Matrix.smul_mul, hYZ, smul_smul]
    rw [← Finset.sum_smul]
    rfl
  have hZrank : Zᴴ.rank = c := by
    rw [Matrix.rank_conjTranspose, ← Matrix.rank_conjTranspose_mul_self Z, hZ,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_iff_ne_zero.mpr hz),
      Matrix.rank_one, Fintype.card_fin]
  let W (r : Fin 4) := Y r - (star (v r) / z) • Z
  have hZW (r : Fin 4) : Zᴴ * W r = 0 := by
    have hZY := congrArg Matrix.conjTranspose (hYZ r)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at hZY
    rw [W, Matrix.mul_sub, Matrix.mul_smul, hZY, hZ, smul_smul, div_mul_cancel₀ _ hz, sub_self]
  have hWdep : ¬ LinearIndependent ℂ W := by
    intro h
    apply hv
    funext r
    apply Fintype.linearIndependent_iff.mp h v _ r
    simp only [W, smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
    have hsum : (∑ r, v r * (star (v r) / z)) = 1 := by
      simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      rw [show (∑ r, v r * star (v r)) = z by simp [z, dotProduct, mul_comm]]
      exact mul_inv_cancel₀ hz
    rw [hsum, one_smul]
    exact sub_self Z
  let U := ∑ r, (star (v r) / z) • X r
  have hsplit : tensorSum X Y = kronecker U Z + tensorSum X W := by
    change (∑ i, (Matrix.kroneckerBilinear (R := ℂ)) (X i) (Y i)) =
      (Matrix.kroneckerBilinear (R := ℂ)) (∑ i, (star (v i) / z) • X i) Z +
        ∑ i, (Matrix.kroneckerBilinear (R := ℂ)) (X i) (W i)
    simp only [W, map_sum, LinearMap.sum_apply, map_smul, map_sub, LinearMap.smul_apply,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by abel)
  let p := b - U.rank
  have hp : b ≤ p + a := by
    have hr := U.rank_le_card_height
    simp only [Fintype.card_fin] at hr
    dsimp [p]
    omega
  obtain ⟨L, hL, hUL, _⟩ := kernel_columns U
  have hRcolumns := kernel_columns Zᴴ
  rw [hZrank] at hRcolumns
  obtain ⟨R, hR, _, hfix⟩ := hRcolumns
  let A' : Fin 4 → Matrix (Fin a) (Fin p) ℂ := fun r => X r * L
  let B' : Fin 4 → Matrix (Fin (d - c)) (Fin c) ℂ := fun r => Rᴴ * W r
  have hBdep : ¬ LinearIndependent ℂ B' := by
    intro h
    apply hWdep
    apply LinearIndependent.of_comp (Matrix.mulLeftLinearMap (Fin c) ℂ Rᴴ)
    exact h
  obtain ⟨A, B, hAB⟩ := cut_dependent_right A' B' hBdep
  have hcompress : tensorSum X Y * kronecker L (1 : Matrix (Fin c) (Fin c) ℂ) =
      kronecker (1 : Matrix (Fin a) (Fin a) ℂ) R * tensorSum A B := by
    rw [hsplit, Matrix.add_mul, ← Matrix.mul_kronecker_mul, hUL, Matrix.mul_one,
      Matrix.zero_kronecker, zero_add, hAB]
    simp only [tensorSum, A', B', Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hfix _ (hZW _), Matrix.mul_one]
  have hleft : (kronecker L (1 : Matrix (Fin c) (Fin c) ℂ))ᴴ *
      kronecker L (1 : Matrix (Fin c) (Fin c) ℂ) = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      hL, Matrix.one_mul, Matrix.one_kronecker_one]
  have hright : (kronecker (1 : Matrix (Fin a) (Fin a) ℂ) R)ᴴ *
      kronecker (1 : Matrix (Fin a) (Fin a) ℂ) R = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      hR, Matrix.one_mul, Matrix.one_kronecker_one]
  refine ⟨p, hp, A, B, ?_⟩
  have hg := congrArg (fun M => Mᴴ * M) hcompress
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (tensorSum X Y)ᴴ (tensorSum X Y), hF, Matrix.one_mul,
    ← Matrix.mul_assoc (kronecker (1 : Matrix (Fin a) (Fin a) ℂ) R)ᴴ
      (kronecker (1 : Matrix (Fin a) (Fin a) ℂ) R), hright, hleft] using hg.symm
private theorem trivial_kernel_dimension {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1)
    (hk : ∀ T, T.IsHermitian → compression X T = 0 → T = 0) : 4 * c ≤ d := by
  apply neutral_dimension X Y hF hX (1 : Matrix (Fin 4) (Fin 4) ℂ) (by simp)
  intro T hT h
  simp [hk T hT h]

/-- With a shrinking left factor, a purely rank-two Hermitian coefficient kernel
forces the right output to have at least four thirds of the input dimension. -/
theorem pure_rank_two_kernel_bound {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hab : a < b) (hLI : LinearIndependent ℂ X)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1)
    (hK : ∀ T, T.IsHermitian → compression X T = 0 → T ≠ 0 → T.rank = 2) :
    4 * c ≤ 3 * d := by
  have hRank (T) (hT : T.IsHermitian) (hXT : compression X T = 0) : T.rank ≤ 2 := by
    by_cases hz : T = 0
    · simp [hz]
    · rw [hK T hT hXT hz]
  rcases coefficient_geometry X hLI hRank with h0 | ⟨v, hv, hk⟩ | ⟨E, hE, hn⟩
  · have h := trivial_kernel_dimension X Y hF hX h0
    omega
  · obtain ⟨p, hp, A, B, h⟩ := common_kernel_reduction X Y hF hX v hv hk
    have hg : (tensorSum B A)ᴴ * tensorSum B A = 1 := by
      rw [swap_tensor A B, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv _ _ (Equiv.prodComm _ _) (Equiv.prodComm _ _)
          (Equiv.prodComm _ _), h, Matrix.submatrix_one_equiv]
    have hbnd := stack_dimension (by omega : 0 < p) B A hg
    omega
  · have h := neutral_dimension X Y hF hX E hE hn
    omega

private theorem large_bounds {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hc : 0 < c) (hab : 2 * a < b) (hF : (tensorSum X Y)ᴴ * tensorSum X Y = 1) :
    b ≤ 4 * a ∧ 5 * c ≤ 2 * d ∧ (5 * a < 2 * b → 3 * c ≤ d) ∧
      (3 * a < b → 4 * c ≤ d) := by
  refine ⟨stack_dimension hc X Y hF, ?_⟩
  have reduced (A : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (B : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (h : tensorSum A B = tensorSum X Y) :
      5 * c ≤ 2 * d ∧ (5 * a < 2 * b → 3 * c ≤ d) ∧ (3 * a < b → 4 * c ≤ d) := by
    have h' : (tensorSum A B)ᴴ * tensorSum A B = 1 := by rw [h, hF]
    have hdim := stack_dimension hc A B h'
    have hrect := RestrictedFlatSpectrum.obstruction A B hc hab 1 (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using h')
    omega
  by_cases hXL : LinearIndependent ℂ X
  · by_cases hYL : LinearIndependent ℂ Y
    · obtain ⟨M, _, _, hPres, hMX, hMLI⟩ := exact_whitening X Y hYL hc hF
      let U := mix M X
      let V := mix M.transpose⁻¹ Y
      have hUV : (tensorSum U V)ᴴ * tensorSum U V = 1 := by
        simpa only [tensorSum, U, V, hPres] using hF
      have hinj : Function.Injective (stackK U).mulVecLin := by
        apply gram_identity_injective
        rw [stackK_gram]
        exact hMX
      by_cases hlarge : 3 * a < b
      · have hk (T) (hT : T.IsHermitian) (h : compression U T = 0) : T = 0 := by
          have hr := hermitian_rank_bound U hinj T hT h 3 (by decide) hlarge
          have he (i : Fin 4) : hT.eigenvalues i = 0 := by
            by_contra hi
            haveI : Nonempty {i // hT.eigenvalues i ≠ 0} := ⟨⟨i, hi⟩⟩
            rw [hT.rank_eq_card_non_zero_eigs] at hr
            have := Fintype.card_pos (α := {i // hT.eigenvalues i ≠ 0})
            omega
          rw [hT.spectral_theorem]
          simp [he]
        have h4 := trivial_kernel_dimension U V hUV hMX hk
        omega
      · have hRank (T) (hT : T.IsHermitian) (h : compression U T = 0) : T.rank ≤ 2 := by
          have hr := hermitian_rank_bound U hinj T hT h 2 (by decide) hab
          omega
        rcases coefficient_geometry U (hMLI hXL) hRank with h0 | ⟨v, hv, hk⟩ | ⟨E, hE, hn⟩
        · have h4 := trivial_kernel_dimension U V hUV hMX h0
          omega
        · obtain ⟨p, hp, A, B, hAB⟩ := common_kernel_reduction U V hUV hMX v hv hk
          have hg : (∑ i, kronecker (A i) (B i))ᴴ * (∑ i, kronecker (A i) (B i)) =
              ((1 : ℝ) : ℂ) • 1 := by
            simpa only [Complex.ofReal_one, one_smul] using hAB
          have h5 := NativeThreeRectangularBound.native_three_rectangular_bound A B 1
            (by norm_num) (by omega : a < p) hg
          refine ⟨by omega, ?_, by omega⟩
          intro hb
          have h3 := NativeRectangularBound.bound A B 1 (by norm_num) (by omega : 3 * a < 2 * p) hg
          omega
        · have h3 := neutral_dimension U V hUV hMX E hE hn
          omega
    · obtain ⟨A, B, h⟩ := cut_dependent_right X Y hYL
      exact reduced A B h
  · obtain ⟨A, B, h⟩ := cut_dependent_left X Y hXL
    exact reduced A B h

/-- The three inclusive upper thresholds are necessary and sufficient above twice the left output. -/
theorem native_four_scalar_gram_iff (a b c d : ℕ) (lam : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hab : 2 * a < b) :
    FourScalarGram a b c d lam ↔
      (2 * a < b ∧ 2 * b ≤ 5 * a ∧ 5 * c ≤ 2 * d) ∨
      (5 * a < 2 * b ∧ b ≤ 3 * a ∧ 3 * c ≤ d) ∨
      (3 * a < b ∧ b ≤ 4 * a ∧ 4 * c ≤ d) := by
  constructor
  · rintro ⟨X, Y, h⟩
    obtain ⟨hb, h5, h3, h4⟩ := large_bounds _ _ hc hab (unit_normalize hlam X Y h)
    by_cases hsmall : 2 * b ≤ 5 * a
    · exact Or.inl ⟨hab, hsmall, h5⟩
    by_cases hmid : b ≤ 3 * a
    · exact Or.inr (Or.inl ⟨by omega, hmid, h3 (by omega)⟩)
    exact Or.inr (Or.inr ⟨by omega, hb, h4 (by omega)⟩)
  · intro h
    exact staircase_sufficient a b c d lam hlam (Or.inr (Or.inr (Or.inl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

/-- Exchanging factors gives the exact criterion above twice the right output. -/
theorem native_four_scalar_gram_swap_iff (a b c d : ℕ) (lam : ℝ)
    (hlam : 0 < lam) (hb : 0 < b) (hdc : 2 * d < c) :
    FourScalarGram a b c d lam ↔
      (2 * d < c ∧ 2 * c ≤ 5 * d ∧ 5 * b ≤ 2 * a) ∨
      (5 * d < 2 * c ∧ c ≤ 3 * d ∧ 3 * b ≤ a) ∨
      (3 * d < c ∧ c ≤ 4 * d ∧ 4 * b ≤ a) := by
  exact ⟨fun h => (native_four_scalar_gram_iff d c b a lam hlam hb hdc).mp (swap_gram h),
    fun h => swap_gram ((native_four_scalar_gram_iff d c b a lam hlam hb hdc).mpr h)⟩

example : FourScalarGram 2 5 2 5 1 :=
  (native_four_scalar_gram_iff 2 5 2 5 1 (by norm_num) (by decide) (by decide)).mpr
    (Or.inl ⟨by decide, by decide, by decide⟩)

example : ¬ FourScalarGram 0 1 1 0 1 := by
  rw [native_four_scalar_gram_iff 0 1 1 0 1 (by norm_num) (by decide) (by decide)]
  decide

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
