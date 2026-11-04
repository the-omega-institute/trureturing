/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported original-middle reconstruction with its exact signed fiber. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentFiber
import D5.S3.VertexAlgebra.FormalSeries.SupportedCollisionSlice

/-!
Direct composition of the two existing supported inversions and the supported
positive-factor inverse. This is the y<<s<<z chamber, not substitution s=x+y on a raw
distribution. Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions remain
in the suppliers. The numerator need not be a polynomial or finitely supported.
The sector consumer discharges lower support using ORIGINAL v-on-t truncation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldOriginalMiddleInverse
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedChannelSeries SupportedCollisionSlice
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

/-- The actual finite polynomial slice. F may have infinite support in every
coordinate and need not have rectangular Laurent support. -/
def qSlice {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k A B : ℕ) (b : ℤ) (F : ℤ → ℤ → ℤ → V) (s z : ℤ) : V :=
  ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (A + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((A.choose h : ℂ) •
        F (s - 2 * k + p) (b - k - p - h) (z - B - A + h))

/-- Only modes from modeFiber can occur, even after s,z are shifted in a
supported inverse. In particular the fiber is independent of that inverse's
length and of any auxiliary truncation cutoff. -/
theorem qSlice_lower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k A B N : ℕ) (b : ℤ) (F : ℤ → ℤ → ℤ → V)
    (lower : ∀ r : ℤ, r ∈ modeFiber k A b →
      ∀ s z : ℤ, s < -(N : ℤ) → F s (-r - 1) z = 0)
    (s z : ℤ) (hs : s < -(N : ℤ)) :
    qSlice k A B b F s z = 0 := by
  classical
  unfold qSlice
  apply Finset.sum_eq_zero
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_eq_zero
  intro h hh
  have hhA : h ≤ A := by simpa using Finset.mem_range.mp hh
  let r : ℤ := -b + k + p + h - 1
  have member : r ∈ modeFiber k A b :=
    (mem_modeFiber_iff k A b r).2 ⟨p, hpk, h, hhA, rfl⟩
  have hy : b - k - p - h = -r - 1 := by dsimp only [r]; omega
  rw [hy, lower r member _ _ (by omega), smul_zero, smul_zero]

/-- Positive clearing commutes with the two finite polynomial fibers.
This is a finite sum interchange; no unrestricted residue interchange occurs. -/
theorem positiveClear_qSlice {R : Type*} [CommRing R] [Algebra ℂ R]
    (k A B C : ℕ) (b : ℤ) (F : ℤ → ℤ → ℤ → R) (s z : ℤ) :
    positiveClear C (qSlice k A B b F) s z =
      ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (A + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          ((A.choose h : ℂ) •
            positiveClear C
              (fun x y => F (x - 2 * k + p) (b - k - p - h) (y - B - A + h))
              s z) := by
  classical
  simp only [positiveClear, qSlice, Finset.smul_sum]
  let term (j p h : ℕ) : R :=
    (C.choose j : ℂ) •
      ((((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
        ((A.choose h : ℂ) •
          F (s - j - 2 * k + p) (b - k - p - h) (z + j - B - A + h)))
  change (∑ j ∈ Finset.range (C + 1), ∑ p ∈ Finset.range (k + 1),
    ∑ h ∈ Finset.range (A + 1), term j p h) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [term]
  simp only [smul_smul]
  congr 1
  ring


/-- Indices j,l,q of (1-y/s)^(-k),(1+y/z)^(-a1),(1+s/z)^(-a0). -/
abbrev MiddleIndex := ℕ × (ℕ × ℕ)

/-- Literal signed numerator exponents, with no condition on individual s,b,z. -/
def middleInput (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (i : MiddleIndex) : Exponent 3 :=
  ![s + 2 * k + i.1 - i.2.2,
    b + k - i.1 - i.2.1,
    z + a 0 + a 1 + a 2 + i.2.2 + i.2.1]

def middleWeight (k : ℕ) (a : Fin 3 → ℕ) (i : MiddleIndex) : ℂ :=
  ((-1 : ℂ) ^ i.1) * integerBinomial (-(k : ℤ)) i.1 *
    integerBinomial (-(a 1 : ℤ)) i.2.1 * integerBinomial (-(a 0 : ℤ)) i.2.2

def MiddleAdmissible (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (i : MiddleIndex) : Prop := ∀ c : Fin 3, 0 ≤ middleInput k a s b z i c

/-- Exact balances and their signed, nonrectangular bounds. -/
theorem middle_bounds (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (i : MiddleIndex) (hi : MiddleAdmissible k a s b z i) :
    (i.1 : ℤ) + i.2.1 ≤ b + k ∧
    (i.2.2 : ℤ) ≤ s + 2 * k + i.1 ∧
    (i.2.2 : ℤ) + i.2.1 ≤ s + b + 3 * k ∧
    0 ≤ b + k ∧ 0 ≤ s + b + 3 * k ∧
    0 ≤ s + b + z + 3 * k + a 0 + a 1 + a 2 ∧
    middleInput k a s b z i 0 + middleInput k a s b z i 1 =
      s + b + 3 * k - i.2.2 - i.2.1 ∧
    0 ≤ middleInput k a s b z i 1 ∧ middleInput k a s b z i 1 ≤ b + k := by
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  simp only [middleInput, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
  omega

/-- A containing box is filtered by ALL THREE actual numerator constraints. -/
def middleFiber (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ) : Finset MiddleIndex :=
  by
  classical
  exact ((Finset.range ((b + k).toNat + 1)).product
    ((Finset.range ((b + k).toNat + 1)).product
      (Finset.range ((s + b + 3 * k).toNat + 1)))).filter
        (MiddleAdmissible k a s b z)

theorem mem_middleFiber_iff (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (i : MiddleIndex) : i ∈ middleFiber k a s b z ↔ MiddleAdmissible k a s b z i := by
  classical
  unfold middleFiber
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hi
    obtain ⟨hjl, hq, hql, hE, hF, hG, hsum, hm0, hm1⟩ :=
      middle_bounds k a s b z i hi
    apply Finset.mem_filter.mpr
    refine ⟨?_, hi⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩⟩

/-- An actual numerator family M_b(s,z), not a new formal channel. -/
def middleTerm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (i : MiddleIndex) : V :=
  middleWeight k a i • M (middleInput k a s b z i 1)
    (middleInput k a s b z i 0) (middleInput k a s b z i 2)

def middleSum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ) : V :=
  ∑ i ∈ middleFiber k a s b z, middleTerm M k a s b z i

private theorem term_negative {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (native : ∀ b s z : ℤ, s < 0 ∨ b < 0 ∨ z < 0 → M b s z = 0)
    (i : MiddleIndex)
    (h : middleInput k a s b z i 0 < 0 ∨ middleInput k a s b z i 1 < 0 ∨
      middleInput k a s b z i 2 < 0) : middleTerm M k a s b z i = 0 := by
  unfold middleTerm
  rw [native _ _ _ h, smul_zero]

private theorem term_outside {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (native : ∀ b s z : ℤ, s < 0 ∨ b < 0 ∨ z < 0 → M b s z = 0)
    (i : MiddleIndex) (hi : i ∉ middleFiber k a s b z) :
    middleTerm M k a s b z i = 0 := by
  apply term_negative M k a s b z native i
  by_contra h
  apply hi
  apply (mem_middleFiber_iff k a s b z i).2
  intro c
  fin_cases c <;> simp [middleInput] at * <;> omega

/-- These are necessary cones, not rectangular lower support in s,b,z. -/
theorem middleSum_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ)
    (outside : b + k < 0 ∨ s + b + 3 * k < 0 ∨
      s + b + z + 3 * k + a 0 + a 1 + a 2 < 0) : middleSum M k a s b z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hb := middle_bounds k a s b z i ((mem_middleFiber_iff k a s b z i).1 hi)
  rcases outside with h | h | h <;> omega

/-- The genuine successive supported inverse sums before removing T.
Even a negative intermediate s+2k+j is retained; native M then kills its sum. -/
def middleCutoffSum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (T : ℕ) (s b z : ℤ) : V :=
  ∑ l ∈ Finset.range ((b + T).toNat + 1),
    ∑ j ∈ Finset.range ((b - l + T).toNat + 1),
      ∑ q ∈ Finset.range ((s + 2 * k + j).toNat + 1),
        middleTerm M k a s b z (j, (l, q))

private def auxiliaryBox (k T : ℕ) (s b : ℤ) : Finset MiddleIndex :=
  (Finset.range ((b + T).toNat + 1)).product
    ((Finset.range ((b + T).toNat + 1)).product
      (Finset.range ((s + b + T + 2 * k).toNat + 1)))

private theorem sum_eq_auxiliary {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (T : ℕ) (hT : k ≤ T)
    (s b z : ℤ)
    (native : ∀ b s z : ℤ, s < 0 ∨ b < 0 ∨ z < 0 → M b s z = 0) :
    middleSum M k a s b z =
      ∑ i ∈ auxiliaryBox k T s b, middleTerm M k a s b z i := by
  classical
  apply Finset.sum_subset
  · intro i hi
    obtain ⟨hjl, hq, hql, hE, hF, hG, hsum, hm0, hm1⟩ :=
      middle_bounds k a s b z i ((mem_middleFiber_iff k a s b z i).1 hi)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ?_, Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩⟩ <;> omega
  · intro i hi hout
    exact term_outside M k a s b z native i hout

/-- Every enlarged auxiliary T gives the SAME exact relevance fiber.
All padding tails vanish as complete M coefficients, not residue summands. -/
theorem middleCutoffSum_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : ℤ → ℤ → ℤ → V) (k : ℕ) (a : Fin 3 → ℕ) (T : ℕ) (hT : k ≤ T)
    (s b z : ℤ)
    (native : ∀ b s z : ℤ, s < 0 ∨ b < 0 ∨ z < 0 → M b s z = 0) :
    middleCutoffSum M k a T s b z = middleSum M k a s b z := by
  classical
  by_cases hb : 0 ≤ b + T
  · have padq (l j : ℕ) (hj : j ∈ Finset.range ((b - l + T).toNat + 1)) :
        (∑ q ∈ Finset.range ((s + 2 * k + j).toNat + 1),
          middleTerm M k a s b z (j, (l, q))) =
        ∑ q ∈ Finset.range ((s + b + T + 2 * k).toNat + 1),
          middleTerm M k a s b z (j, (l, q)) := by
      have hjb : (j : ℤ) ≤ b + T := by
        have hj' := Finset.mem_range.mp hj
        have hmono := Int.toNat_le_toNat (show b - l + T ≤ b + T by omega)
        omega
      apply Finset.sum_subset
        (Finset.range_mono (Nat.succ_le_succ
          (Int.toNat_le_toNat (show s + 2 * k + j ≤ s + b + T + 2 * k by omega))))
      intro q hq hout
      apply term_negative M k a s b z native
      left
      simp only [middleInput, Matrix.cons_val_zero]
      simp only [Finset.mem_range, not_lt] at hout
      omega
    have padj (l : ℕ) :
        (∑ j ∈ Finset.range ((b - l + T).toNat + 1),
          ∑ q ∈ Finset.range ((s + b + T + 2 * k).toNat + 1),
            middleTerm M k a s b z (j, (l, q))) =
        ∑ j ∈ Finset.range ((b + T).toNat + 1),
          ∑ q ∈ Finset.range ((s + b + T + 2 * k).toNat + 1),
            middleTerm M k a s b z (j, (l, q)) := by
      apply Finset.sum_subset
        (Finset.range_mono (Nat.succ_le_succ
          (Int.toNat_le_toNat (show b - l + T ≤ b + T by omega))))
      intro j hj hout
      apply Finset.sum_eq_zero
      intro q hq
      apply term_negative M k a s b z native
      right
      left
      simp [middleInput]
      simp only [Finset.mem_range, not_lt] at hout
      omega
    calc
      middleCutoffSum M k a T s b z =
          ∑ l ∈ Finset.range ((b + T).toNat + 1),
            ∑ j ∈ Finset.range ((b + T).toNat + 1),
              ∑ q ∈ Finset.range ((s + b + T + 2 * k).toNat + 1),
                middleTerm M k a s b z (j, (l, q)) := by
        unfold middleCutoffSum
        apply Finset.sum_congr rfl
        intro l hl
        calc
          _ = ∑ j ∈ Finset.range ((b - l + T).toNat + 1),
                ∑ q ∈ Finset.range ((s + b + T + 2 * k).toNat + 1),
                  middleTerm M k a s b z (j, (l, q)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact padq l j hj
          _ = _ := padj l
      _ = ∑ i ∈ auxiliaryBox k T s b, middleTerm M k a s b z i := by
        rw [Finset.sum_comm]
        simp only [auxiliaryBox, Finset.product_eq_sprod, Finset.sum_product]
      _ = middleSum M k a s b z := (sum_eq_auxiliary M k a T hT s b z native).symm
  · rw [middleSum_zero M k a s b z (Or.inl (by omega))]
    unfold middleCutoffSum
    apply Finset.sum_eq_zero
    intro l hl
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro q hq
    apply term_negative M k a s b z native
    right
    left
    simp [middleInput]
    omega

/-- Only the finite (y+z)^C z^D clearing; no additional denominator. -/
def partialClear {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → ℤ → R) (C D : ℕ) (s b z : ℤ) : R :=
  positiveClear C (F s) b (z - C - D)

private theorem partialClear_lower {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → ℤ → R) (C D T : ℕ)
    (lower : ∀ s b z : ℤ, b < -(T : ℤ) → F s b z = 0)
    (s b z : ℤ) (hb : b < -(T : ℤ)) : partialClear F C D s b z = 0 := by
  unfold partialClear positiveClear
  apply Finset.sum_eq_zero
  intro h hh
  rw [lower _ _ _ (by omega), smul_zero]

/-- The actual full Q contains BOTH monomial shifts s^k and y^k. -/
theorem qSlice_partialClear {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → ℤ → R) (k C D : ℕ) (b s z : ℤ) :
    qSlice k C D b F s z =
      clear k (fun x y => partialClear F C D x y z) (s - k) (b - k) := by
  unfold qSlice clear partialClear positiveClear
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun v : R =>
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • ((C.choose h : ℂ) • v))
  congr 1 <;> omega

private theorem raw_eq_cutoff {R : Type*} [CommRing R] [Algebra ℂ R]
    (F M : ℤ → ℤ → ℤ → R) (k : ℕ) (a : Fin 3 → ℕ) (T : ℕ)
    (lower : ∀ s b z : ℤ, b < -(T : ℤ) → F s b z = 0)
    (short : ∀ b s z : ℤ, qSlice k (a 1) (a 2) b F s z =
      ∑ q ∈ Finset.range (s.toNat + 1), integerBinomial (-(a 0 : ℤ)) q •
        M b (s - q) (z + q + a 0))
    (s b z : ℤ) (hb : 0 ≤ b + T) :
    F s b z = middleCutoffSum M k a T s b z := by
  classical
  let V := partialClear F (a 1) (a 2)
  calc
    F s b z = ∑ l ∈ Finset.range ((b + T).toNat + 1),
        integerBinomial (-(a 1 : ℤ)) l • V s (b - l) (z + l + a 1 + a 2) := by
      rw [supported_positive_reconstruction (F s) (a 1) T (lower s) b z hb]
      apply Finset.sum_congr rfl
      intro l hl
      apply congrArg (fun v : R => integerBinomial (-(a 1 : ℤ)) l • v)
      dsimp only [V, partialClear]
      congr 1
      omega
    _ = ∑ l ∈ Finset.range ((b + T).toNat + 1),
        integerBinomial (-(a 1 : ℤ)) l •
          (∑ j ∈ Finset.range ((b - l + T).toNat + 1),
            (((-1 : ℂ) ^ j) * integerBinomial (-(k : ℤ)) j) •
              (∑ q ∈ Finset.range ((s + 2 * k + j).toNat + 1),
                integerBinomial (-(a 0 : ℤ)) q •
                  M (b + k - j - l) (s + 2 * k + j - q)
                    (z + a 0 + a 1 + a 2 + q + l))) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlb : 0 ≤ b - l + T := by
        have := Finset.mem_range.mp hl
        omega
      apply congrArg (fun v : R => integerBinomial (-(a 1 : ℤ)) l • v)
      have low : ∀ x y : ℤ, y < -(T : ℤ) →
          V x y (z + l + a 1 + a 2) = 0 := by
        intro x y hy
        exact partialClear_lower F (a 1) (a 2) T lower x y _ hy
      rw [supported_reconstruction (fun x y => V x y (z + l + a 1 + a 2))
        k T low s (b - l) hlb]
      apply Finset.sum_congr rfl
      intro j hj
      apply congrArg (fun v : R => (((-1 : ℂ) ^ j) * integerBinomial (-(k : ℤ)) j) • v)
      have qeq : clear k (fun x y => V x y (z + l + a 1 + a 2))
          (s + k + j) (b - l - j) =
          qSlice k (a 1) (a 2) (b + k - j - l) F
            (s + 2 * k + j) (z + l + a 1 + a 2) := by
        rw [qSlice_partialClear]
        dsimp only [V]
        congr 1 <;> omega
      rw [qeq, short]
      apply Finset.sum_congr rfl
      intro q hq
      apply congrArg (fun v : R => integerBinomial (-(a 0 : ℤ)) q • v)
      congr 1
      omega
    _ = middleCutoffSum M k a T s b z := by
      simp only [middleCutoffSum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      simp only [middleTerm, middleInput, middleWeight, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, smul_smul]
      congr 1
      ring

/-- Exact finite reconstruction in the middle chamber. Lower support licenses
the two supported inverses; the short positive inverse supplies the remaining
factor. Native numerator support removes every auxiliary T tail. -/
theorem original_middle_reconstruction {R : Type*} [CommRing R] [Algebra ℂ R]
    (F M : ℤ → ℤ → ℤ → R) (k : ℕ) (a : Fin 3 → ℕ) (T : ℕ) (hT : k ≤ T)
    (lower : ∀ s b z : ℤ, b < -(T : ℤ) → F s b z = 0)
    (short : ∀ b s z : ℤ, qSlice k (a 1) (a 2) b F s z =
      ∑ q ∈ Finset.range (s.toNat + 1), integerBinomial (-(a 0 : ℤ)) q •
        M b (s - q) (z + q + a 0))
    (native : ∀ b s z : ℤ, s < 0 ∨ b < 0 ∨ z < 0 → M b s z = 0)
    (s b z : ℤ) : F s b z = middleSum M k a s b z := by
  by_cases hb : 0 ≤ b + T
  · exact (raw_eq_cutoff F M k a T lower short s b z hb).trans
      (middleCutoffSum_eq M k a T hT s b z native)
  · rw [lower s b z (by omega), middleSum_zero M k a s b z (Or.inl (by omega))]


end
end D5.S3.VertexAlgebra.ThreeFieldOriginalMiddleInverse
