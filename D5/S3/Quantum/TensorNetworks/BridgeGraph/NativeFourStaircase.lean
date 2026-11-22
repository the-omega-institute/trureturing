/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Width-four scalar column Gram constructions and the large-ratio classification. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification

/-! Rectangular coordinate embeddings and coefficient-kernel bounds at tensor width four. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit (coordinateMatrix coordinate_gram)

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
  exact of_unit_gram hlam X Y (hroute ▸ coordinate_gram e)

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
    · exact ⟨1, by simp [blocks, Rectangle.covers, hy]; omega⟩
    by_cases h₂ : x < 3 * a
    · exact ⟨2, by simp [blocks, Rectangle.covers, hy]; omega⟩
    exact ⟨3, by simp [blocks, Rectangle.covers, hy]; omega⟩
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
    · exact ⟨1, by simp [thirds, Rectangle.covers]; omega⟩
    by_cases h₂ : y < 2 * (d - c)
    · exact ⟨2, by simp [thirds, Rectangle.covers]; omega⟩
    exact ⟨3, by simp [thirds, Rectangle.covers]; omega⟩
  · intro r s x y hx hy hr hs
    fin_cases r <;> fin_cases s <;> simp_all [thirds, Rectangle.covers] <;> omega
  · intro r x y hx hy hr
    fin_cases r <;> simp_all [thirds, Rectangle.covers, Rectangle.image] <;> omega
  · intro r s x y u v hne hx hy hu hv hr hs he
    have hl := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    fin_cases r <;> fin_cases s <;>
      simp_all [thirds, Rectangle.covers, Rectangle.image] <;> omega

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
    · exact ⟨1, by simp [threeFifths, Rectangle.covers]; omega⟩
    by_cases h₂ : x < a + (a - (b - a))
    · exact ⟨2, by simp [threeFifths, Rectangle.covers]; omega⟩
    exact ⟨3, by simp [threeFifths, Rectangle.covers]; omega⟩
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
    · exact ⟨1, by simp [twoFifths, Rectangle.covers, hy]; omega⟩
    by_cases h₂ : y < d - 2 * c
    · exact ⟨2, by simp [twoFifths, Rectangle.covers]; omega⟩
    exact ⟨3, by simp [twoFifths, Rectangle.covers]; omega⟩
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
  · obtain ⟨X, Y, h⟩ := NativeScalarGram.native_scalar_gram_exists a b c d hb hd lam hlam
    refine ⟨Fin.snoc X 0, Fin.snoc Y 0, ?_⟩
    simpa [Fin.sum_univ_castSucc] using h
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

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
