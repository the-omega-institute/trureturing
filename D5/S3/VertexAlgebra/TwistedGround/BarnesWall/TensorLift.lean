/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorLift
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal Pauli generators preserve the integral Gram and satisfy the triangular lift law. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGram

/-! The integral Pauli rows and their lift exponents in the KRR tensor basis.
See arXiv:2411.13646v2, §2.2 and Appendix A.2. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorLift

open LatticeTwistedGroundRealization (normalExponent normal_exponent_add symmetric_pairing_split)
open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word parity)

local notation "wordFlip" => TailPauliPairing.flip
open TailPauliQuotientMaps (flip_flip toggle)
open TensorSubsetRows (falseCount scaledRow scaledRow_X scaledRow_Z synthesize synthesize_injective)
open TensorGram (gram gram_comm gram_diagonal_even gram_eq_normalized_dotProduct halfGram
  halfGram_bilin_eq_zero_on_block halfGram_eq_zero_of_agree_outside normalizationExponent)

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Integral right-action matrix of the literal generator. The flag is false
for X and true for Z. The flipped coefficient is two to the zero-slot parity. -/
def generator (r : ι) (isZ : Bool) : Matrix (Word ι) (Word ι) ℤ := fun u v =>
  (if v = u then if u r = isZ then -1 else 1 else 0) +
    (if v = wordFlip u r then if u r = isZ then 2 ^ (falseCount u % 2) else 0 else 0)

/-- Entrywise reduction of an integral row-action matrix. -/
def modTwo (g : Matrix (Word ι) (Word ι) ℤ) : Matrix (Word ι) (Word ι) F₂ :=
  g.map (Int.castRingHom F₂)

theorem modTwo_vecMul (a : Word ι → ℤ) (g : Matrix (Word ι) (Word ι) ℤ) :
    (fun u => (↑((a ᵥ* g) u) : F₂)) = (fun u => (a u : F₂)) ᵥ* modTwo g := by
  funext u
  exact RingHom.map_vecMul (Int.castRingHom F₂) g a u

private theorem two_pow_falseCount (u : Word ι) :
    (2 : ℤ) ^ (falseCount u % 2) = if falseCount u % 2 = 0 then 1 else 2 := by
  rcases (show falseCount u % 2 = 0 ∨ falseCount u % 2 = 1 by omega) with h | h <;> simp [h]

private theorem falseCount_mod_two_eq_zero_iff (hodd : (Fintype.card ι : F₂) = 1)
    (u : Word ι) : falseCount u % 2 = 0 ↔ parity u ≠ 0 := by
  have hcast : (falseCount u : F₂) = ∑ r, if u r = false then 1 else 0 := by
    rw [falseCount, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp
  have hsum : (falseCount u : F₂) + parity u = 1 := by
    rw [hcast, parity, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : ι, (1 : F₂) := by
        apply Finset.sum_congr rfl
        intro r _
        cases u r <;> simp
      _ = 1 := by simpa using hodd
  have hzero : (falseCount u : F₂) = 0 ↔ falseCount u % 2 = 0 := by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  rw [← hzero, CharTwo.add_eq_iff_eq_add.mp hsum, CharTwo.add_eq_zero]
  have ht : (1 : F₂) = parity u ↔ (0 : F₂) ≠ parity u := by
    simpa only [zero_add] using toggle 0 (parity u)
  exact ht.trans ne_comm

/-- Only an odd-weight row in the active slot has a flipped term modulo two. -/
theorem generator_modTwo_apply (hodd : (Fintype.card ι : F₂) = 1)
    (r : ι) (isZ : Bool) (u v : Word ι) :
    modTwo (generator r isZ) u v = (if v = u then 1 else 0) +
      (if v = wordFlip u r ∧ u r = isZ ∧ parity u ≠ 0 then 1 else 0) := by
  change (↑(generator r isZ u v) : F₂) = _
  by_cases hd : v = u <;> by_cases hf : v = wordFlip u r <;> by_cases hs : u r = isZ <;>
    by_cases hp : parity u = 0 <;>
    simp [generator, two_pow_falseCount, falseCount_mod_two_eq_zero_iff hodd, hd, hf, hs, hp,
      CharTwo.neg_eq, show (2 : F₂) = 0 by decide]

private def scaledRows : Matrix (Word ι) (Word ι) ℚ := scaledRow

private def gramMatrix : Matrix (Word ι) (Word ι) ℤ := Matrix.of gram

/-- The action on ambient coordinates of one literal Pauli slot. -/
def ambientSlot (r : ι) (isZ : Bool) (f : Word ι → ℚ) (v : Word ι) : ℚ :=
  if isZ then (if v r then -1 else 1) * f v else f (wordFlip v r)

private theorem generator_mul_scaledRows (r : ι) (isZ : Bool) (u v : Word ι) :
    ((generator r isZ).map (Int.castRingHom ℚ) * scaledRows : Matrix (Word ι) (Word ι) ℚ) u v =
      ambientSlot r isZ (scaledRow u) v := by
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply, Int.coe_castRingHom, generator, Int.cast_add, Int.cast_ite,
    Int.cast_zero, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Fintype.sum_ite_eq']
  cases isZ
  · change _ = scaledRow u (wordFlip v r)
    rw [scaledRow_X]
    cases hu : u r <;>
      simp [scaledRows, hu, two_pow_falseCount, Int.cast_ite, sub_eq_add_neg, add_comm]
  · change _ = (if v r then (-1 : ℚ) else 1) * scaledRow u v
    rw [scaledRow_Z]
    cases hu : u r <;>
      simp [scaledRows, hu, two_pow_falseCount, Int.cast_ite, sub_eq_add_neg, add_comm]

/-- Synthesis of a lattice vector intertwines the integral right action with
the literal ambient signed permutation. -/
theorem synthesize_generator (r : ι) (isZ : Bool) (a : Word ι → ℤ) :
    synthesize (a ᵥ* generator r isZ) = ambientSlot r isZ (synthesize a) := by
  let aℚ : Word ι → ℚ := fun u => (a u : ℚ)
  funext v
  calc
    synthesize (a ᵥ* generator r isZ) v =
        ((aℚ ᵥ* (generator r isZ).map (Int.castRingHom ℚ)) ᵥ* scaledRows) v := by
      unfold synthesize
      simp only [Matrix.vecMul_apply_eq_sum, Int.cast_sum, Int.cast_mul, Matrix.map_apply,
        Int.coe_castRingHom, aℚ, scaledRows]
      rfl
    _ = ∑ u, aℚ u * ambientSlot r isZ (scaledRow u) v := by
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_apply_eq_sum]
      simp only [generator_mul_scaledRows]
    _ = _ := by
      cases isZ <;> simp [aℚ, ambientSlot, synthesize, Finset.mul_sum, mul_left_comm]

/-- Applying the literal generator twice fixes every integral lattice vector. -/
theorem generator_involutive (r : ι) (isZ : Bool) :
    Function.Involutive (fun a : Word ι → ℤ => a ᵥ* generator r isZ) := by
  intro a
  apply synthesize_injective
  rw [synthesize_generator, synthesize_generator]
  funext v
  cases isZ
  · change synthesize a (wordFlip (wordFlip v r) r) = synthesize a v
    rw [TailPauliQuotientMaps.flip_flip]
  · cases hv : v r <;> simp [ambientSlot, hv]

private theorem ambientSlot_dot (r : ι) (isZ : Bool) (f h : Word ι → ℚ) :
    (∑ v, ambientSlot r isZ f v * ambientSlot r isZ h v) = ∑ v, f v * h v := by
  cases isZ
  · let e : Word ι ≃ Word ι :=
      ⟨fun v => wordFlip v r, fun v => wordFlip v r, fun v => flip_flip v r, fun v => flip_flip v r⟩
    change (∑ v, f (wordFlip v r) * h (wordFlip v r)) = ∑ v, f v * h v
    exact e.sum_comp (fun v => f v * h v)
  · apply Finset.sum_congr rfl
    intro v _
    cases hv : v r <;> simp [ambientSlot, hv]

private theorem gram_map_rat (hodd : (Fintype.card ι : F₂) = 1) :
    (gramMatrix (ι := ι)).map (Int.castRingHom ℚ) =
      ((2 : ℚ) ^ normalizationExponent (ι := ι))⁻¹ • (scaledRows * scaledRowsᵀ) := by
  apply Matrix.ext
  intro u v
  change (gram u v : ℚ) = ((2 : ℚ) ^ normalizationExponent (ι := ι))⁻¹ *
    (scaledRows * scaledRowsᵀ : Matrix (Word ι) (Word ι) ℚ) u v
  rw [gram_eq_normalized_dotProduct hodd, Matrix.mul_apply, div_eq_mul_inv, mul_comm] <;> rfl

/-- Each literal integral generator preserves the normalized KRR Gram. -/
theorem generator_preserves_gram (hodd : (Fintype.card ι : F₂) = 1) (r : ι) (isZ : Bool) :
    generator r isZ * gramMatrix * (generator r isZ)ᵀ = gramMatrix := by
  let g := (generator r isZ).map (Int.castRingHom ℚ)
  have hdot : (g * scaledRows) * (g * scaledRows)ᵀ = scaledRows * scaledRowsᵀ := by
    apply Matrix.ext
    intro u v
    simp only [Matrix.mul_apply (M := g * scaledRows), Matrix.mul_apply (M := scaledRows),
      Matrix.transpose_apply, g, generator_mul_scaledRows]
    exact ambientSlot_dot r isZ (scaledRow u) (scaledRow v)
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  simp only [Matrix.map_mul (f := Int.castRingHom ℚ), Matrix.transpose_map, gram_map_rat hodd]
  change g * (((2 : ℚ) ^ normalizationExponent (ι := ι))⁻¹ •
    (scaledRows * scaledRowsᵀ)) * gᵀ = _
  rw [Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc g scaledRows scaledRowsᵀ,
    mul_assoc (g * scaledRows) scaledRowsᵀ gᵀ, ← Matrix.transpose_mul, hdot]

/-- A word of generators in right-action order. -/
def wordMatrix : List (ι × Bool) → Matrix (Word ι) (Word ι) ℤ
  | [] => 1
  | (r, isZ) :: tail => generator r isZ * wordMatrix tail

/-- Synthesis intertwines a word matrix with the ambient Pauli word. -/
theorem synthesize_wordMatrix (word : List (ι × Bool)) (a : Word ι → ℤ) :
    synthesize (a ᵥ* wordMatrix word) = TensorSubsetRows.ambientWord word (synthesize a) := by
  induction word generalizing a with
  | nil => simp [wordMatrix, TensorSubsetRows.ambientWord]
  | cons step tail ih =>
    obtain ⟨r, isZ⟩ := step
    rw [wordMatrix, ← Matrix.vecMul_vecMul, ih, synthesize_generator] <;> rfl

@[simp] theorem modTwo_one : modTwo (1 : Matrix (Word ι) (Word ι) ℤ) = 1 :=
  map_one ((Int.castRingHom F₂).mapMatrix : Matrix (Word ι) (Word ι) ℤ →+* _)

@[simp] theorem modTwo_mul (g h : Matrix (Word ι) (Word ι) ℤ) :
    modTwo (g * h) = modTwo g * modTwo h :=
  Matrix.map_mul (f := Int.castRingHom F₂)

theorem wordMatrix_preserves_gram (hodd : (Fintype.card ι : F₂) = 1) (word : List (ι × Bool)) :
    wordMatrix word * gramMatrix * (wordMatrix word)ᵀ = gramMatrix := by
  induction word with
  | nil => simp [wordMatrix]
  | cons step tail ih =>
    obtain ⟨r, isZ⟩ := step
    simp only [wordMatrix, Matrix.transpose_mul]
    calc
      _ = generator r isZ * (wordMatrix tail * gramMatrix * (wordMatrix tail)ᵀ) *
          (generator r isZ)ᵀ := by simp only [mul_assoc]
      _ = _ := by rw [ih, generator_preserves_gram hodd]

variable [order : LinearOrder (Word ι)]

local notation:50 u " ≺ " v => @LT.lt (Word ι) order.toLT u v

private def integralHalfGram : Matrix (Word ι) (Word ι) ℤ := fun u v =>
  (@ite ℤ (v ≺ u) (order.toDecidableLT v u) (gram u v) 0) +
    (if v = u then gram u u / 2 else 0)

private theorem integralHalfGram_add_transpose (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) :
    (integralHalfGram + integralHalfGramᵀ : Matrix (Word ι) (Word ι) ℤ) = gramMatrix := by
  apply Matrix.ext
  intro u v
  rcases @lt_trichotomy (Word ι) order u v with huv | rfl | hvu
  · have hn : ¬ (v ≺ u) := @not_lt_of_gt _ order.toPreorder _ _ huv
    have hne : u ≠ v := @ne_of_lt _ order.toPreorder _ _ huv
    simp [integralHalfGram, gramMatrix, huv, hn, hne, hne.symm, gram_comm v u]
  · change integralHalfGram u u + integralHalfGram u u = gram u u
    have hn : ¬ (u ≺ u) := @lt_irrefl _ order.toPreorder u
    simp only [integralHalfGram, hn, if_false, if_true, zero_add]
    rw [← mul_two, Int.ediv_mul_cancel (gram_diagonal_even hodd hm u)]
  · have hn : ¬ (u ≺ v) := @not_lt_of_gt _ order.toPreorder _ _ hvu
    have hne : v ≠ u := @ne_of_lt _ order.toPreorder _ _ hvu
    simp [integralHalfGram, gramMatrix, hvu, hn, hne, hne.symm]

private def integralDefect (g : Matrix (Word ι) (Word ι) ℤ) : Matrix (Word ι) (Word ι) ℤ :=
  integralHalfGram - g * integralHalfGram * gᵀ

/-- The discrepancy of the two cocycles in row-action convention. -/
def liftDefect (g : Matrix (Word ι) (Word ι) ℤ) : Matrix (Word ι) (Word ι) F₂ :=
  halfGram + modTwo g * halfGram * (modTwo g)ᵀ

private theorem liftDefect_eq_modTwo (g : Matrix (Word ι) (Word ι) ℤ) :
    liftDefect g = modTwo (integralDefect g) := by
  unfold modTwo integralDefect
  rw [Matrix.map_sub _ (map_sub (Int.castRingHom F₂))]
  simp only [Matrix.map_mul (f := Int.castRingHom F₂), Matrix.transpose_map]
  change halfGram + modTwo g * halfGram * (modTwo g)ᵀ =
    halfGram - modTwo g * halfGram * (modTwo g)ᵀ
  apply Matrix.ext
  intro u v
  exact (CharTwo.sub_eq_add _ _).symm

private theorem integralDefect_skew (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (g : Matrix (Word ι) (Word ι) ℤ) (hg : g * gramMatrix * gᵀ = gramMatrix) :
    integralDefect g + (integralDefect g)ᵀ = 0 := by
  unfold integralDefect
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← mul_assoc g integralHalfGramᵀ gᵀ]
  calc
    _ = (integralHalfGram + integralHalfGramᵀ) -
        g * (integralHalfGram + integralHalfGramᵀ) * gᵀ := by
      rw [mul_add, add_mul]
      abel
    _ = 0 := by rw [integralHalfGram_add_transpose hodd hm, hg, sub_self]

/-- Integral skewness reduces to symmetry in characteristic two. -/
theorem liftDefect_symm (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (g : Matrix (Word ι) (Word ι) ℤ) (hg : g * gramMatrix * gᵀ = gramMatrix) :
    (liftDefect g).IsSymm := by
  apply Matrix.IsSymm.ext
  intro u v
  have h : integralDefect g v u + integralDefect g u v = 0 :=
    congrArg (fun M : Matrix (Word ι) (Word ι) ℤ => M v u) (integralDefect_skew hodd hm g hg)
  rw [liftDefect_eq_modTwo]
  change (↑(integralDefect g v u) : F₂) = ↑(integralDefect g u v)
  apply CharTwo.add_eq_zero.mp
  simpa only [Int.cast_add, Int.cast_zero] using congrArg (fun n : ℤ => (n : F₂)) h

/-- The diagonal vanishes integrally, before reduction. -/
theorem liftDefect_diagonal (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (g : Matrix (Word ι) (Word ι) ℤ) (hg : g * gramMatrix * gᵀ = gramMatrix)
    (u : Word ι) : liftDefect g u u = 0 := by
  have h : integralDefect g u u + integralDefect g u u = 0 :=
    congrArg (fun M : Matrix (Word ι) (Word ι) ℤ => M u u) (integralDefect_skew hodd hm g hg)
  have hu : integralDefect g u u = 0 := by omega
  rw [liftDefect_eq_modTwo]
  change (↑(integralDefect g u u) : F₂) = 0
  rw [hu, Int.cast_zero]

/-- The basis-normalized lift exponent, using the upper triangle of the
symmetric mod-two discrepancy. -/
def liftExponent (g : Matrix (Word ι) (Word ι) ℤ) (x : Word ι → F₂) : F₂ :=
  normalExponent (liftDefect g) x

/-- Symmetry permits the lower-triangular convention in KRR (2.2.4). -/
theorem liftExponent_eq_lower (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (g : Matrix (Word ι) (Word ι) ℤ) (hg : g * gramMatrix * gᵀ = gramMatrix)
    (x : Word ι → F₂) :
    liftExponent g x = ∑ u, ∑ v with v ≺ u, liftDefect g u v * x u * x v := by
  unfold liftExponent normalExponent
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [(liftDefect_symm hodd hm g hg).apply u v]
  split <;> ring

private theorem toBilin_sandwich (A B : Matrix (Word ι) (Word ι) F₂) (x y : Word ι → F₂) :
    (A * B * Aᵀ).toBilin' x y = B.toBilin' (x ᵥ* A) (y ᵥ* A) := by
  simp only [Matrix.toBilin'_apply']
  rw [Matrix.mulVec_vecMul, Matrix.dotProduct_mulVec (x ᵥ* A),
    Matrix.dotProduct_mulVec x, Matrix.vecMul_vecMul, mul_assoc]

/-- Polarization is the sum of the original and transported half-Gram
cocycles. This holds for each literal generator and for integral products. -/
theorem liftExponent_polar (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (g : Matrix (Word ι) (Word ι) ℤ) (hg : g * gramMatrix * gᵀ = gramMatrix)
    (x y : Word ι → F₂) :
    liftExponent g (x + y) + liftExponent g x + liftExponent g y =
      halfGram.toBilin' x y + halfGram.toBilin' (x ᵥ* modTwo g) (y ᵥ* modTwo g) := by
  have hsplit : (liftDefect g).toBilin' x y =
      (∑ u, ∑ v with u ≺ v, liftDefect g u v * (x u * y v + y u * x v)) := by
    have hs := @symmetric_pairing_split (Word ι) _ order (liftDefect g)
      (liftDefect_symm hodd hm g hg) x y
    simp only [liftDefect_diagonal hodd hm g hg, zero_mul, Finset.sum_const_zero, zero_add] at hs
    refine hs.trans (Finset.sum_congr rfl ?_)
    intro u _
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    _ = (liftDefect g).toBilin' x y := by
      unfold liftExponent
      rw [add_assoc, normal_exponent_add, ← hsplit, add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    _ = _ := by
      simp only [liftDefect, map_add, LinearMap.add_apply, toBilin_sandwich]

/-- The phase law for a single literal X or Z slot. -/
theorem generator_liftExponent_polar (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) (r : ι) (isZ : Bool) (x y : Word ι → F₂) :
    liftExponent (generator r isZ) (x + y) +
        liftExponent (generator r isZ) x + liftExponent (generator r isZ) y =
      halfGram.toBilin' x y +
        halfGram.toBilin' (x ᵥ* modTwo (generator r isZ)) (y ᵥ* modTwo (generator r isZ)) :=
  liftExponent_polar hodd hm _ (generator_preserves_gram hodd r isZ) x y

/-- The exponent of the composed generator lifts, evaluated in right-action
order on the successive row vectors. -/
def wordLiftExponent : List (ι × Bool) → (Word ι → F₂) → F₂
  | [], _ => 0
  | (r, isZ) :: tail, x =>
      liftExponent (generator r isZ) x + wordLiftExponent tail (x ᵥ* modTwo (generator r isZ))

theorem wordLiftExponent_polar (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (word : List (ι × Bool)) (x y : Word ι → F₂) :
    wordLiftExponent word (x + y) + wordLiftExponent word x + wordLiftExponent word y =
      halfGram.toBilin' x y +
        halfGram.toBilin' (x ᵥ* modTwo (wordMatrix word)) (y ᵥ* modTwo (wordMatrix word)) := by
  induction word generalizing x y with
  | nil => simp [wordLiftExponent, wordMatrix, CharTwo.add_self_eq_zero]
  | cons step tail ih =>
    obtain ⟨r, isZ⟩ := step
    let g := generator r isZ
    let a := x ᵥ* modTwo g
    let b := y ᵥ* modTwo g
    have hxy : (x + y) ᵥ* modTwo g = a + b := Matrix.add_vecMul _ _ _
    have hg := liftExponent_polar hodd hm g (generator_preserves_gram hodd r isZ) x y
    have htail := ih a b
    change (liftExponent g (x + y) + wordLiftExponent tail ((x + y) ᵥ* modTwo g)) +
        (liftExponent g x + wordLiftExponent tail a) +
        (liftExponent g y + wordLiftExponent tail b) = _
    rw [hxy]
    calc
      _ = (liftExponent g (x + y) + liftExponent g x + liftExponent g y) +
          (wordLiftExponent tail (a + b) + wordLiftExponent tail a + wordLiftExponent tail b) := by
        abel
      _ = _ := by
        rw [hg, htail, add_assoc, CharTwo.add_cancel_left]
        simp only [wordMatrix, modTwo_mul, ← Matrix.vecMul_vecMul, a, b, g]

/-- Every nonzero coordinate of the vector agrees with the block label
outside the two indicated slots. -/
def SupportedInBlock (r s : ι) (w : Word ι) (x : Word ι → F₂) : Prop :=
  ∀ u, x u ≠ 0 → ∀ t, t ≠ r → t ≠ s → u t = w t

private theorem single_supported (r s : ι) (w u : Word ι) (c : F₂)
    (hu : ∀ t, t ≠ r → t ≠ s → u t = w t) :
    SupportedInBlock r s w (Pi.single u c) := by
  intro v hv
  by_cases h : v = u
  · subst v
    exact hu
  · exact (hv (by simp [Pi.single_apply, h, Ne.symm h])).elim

private theorem generator_preserves_block (hodd : (Fintype.card ι : F₂) = 1)
    (r s t : ι) (ht : t = r ∨ t = s) (isZ : Bool) (w : Word ι) (x : Word ι → F₂)
    (hx : SupportedInBlock r s w x) :
    SupportedInBlock r s w (x ᵥ* modTwo (generator t isZ)) := by
  intro v hv k hkr hks
  have hkt : k ≠ t := ht.elim (fun h he => hkr (he.trans h)) (fun h he => hks (he.trans h))
  by_contra hne
  apply hv
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hxu : x u = 0
  · simp [hxu]
  · have h : u k = w k := hx u hxu k hkr hks
    have hdiag : v ≠ u := fun he => hne ((congrFun he k).trans h)
    have hflip : v ≠ wordFlip u t := fun he => hne (by
      rw [he]
      simpa only [TailPauliPairing.flip, if_neg hkt] using h)
    rw [generator_modTwo_apply hodd]
    simp [hdiag, hflip]

private theorem generator_liftDefect_eq_zero_on_block
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (r s t : ι) (ht : t = r ∨ t = s) (isZ : Bool) (w u v : Word ι)
    (hu : ∀ k, k ≠ r → k ≠ s → u k = w k) (hv : ∀ k, k ≠ r → k ≠ s → v k = w k) :
    liftDefect (generator t isZ) u v = 0 := by
  let g := modTwo (generator t isZ)
  change halfGram u v + (g * halfGram * gᵀ : Matrix (Word ι) (Word ι) F₂) u v = 0
  have huv : ∀ k, k ≠ r → k ≠ s → u k = v k :=
    fun k hkr hks => (hu k hkr hks).trans (hv k hkr hks).symm
  have hleft := generator_preserves_block hodd r s t ht isZ w _ (single_supported r s w u 1 hu)
  have hright := generator_preserves_block hodd r s t ht isZ w _ (single_supported r s w v 1 hv)
  rw [halfGram_eq_zero_of_agree_outside hodd hm r s u v huv, zero_add,
    ← Matrix.toBilin'_single (g * halfGram * gᵀ), toBilin_sandwich]
  exact halfGram_bilin_eq_zero_on_block hodd hm r s w _ _ hleft hright

private theorem generator_liftExponent_eq_zero_on_block
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (r s t : ι) (ht : t = r ∨ t = s) (isZ : Bool) (w : Word ι) (x : Word ι → F₂)
    (hx : SupportedInBlock r s w x) : liftExponent (generator t isZ) x = 0 := by
  unfold liftExponent normalExponent
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  by_cases hu : x u = 0
  · simp [hu]
  · by_cases hv : x v = 0
    · simp [hv]
    · simp only [generator_liftDefect_eq_zero_on_block hodd hm r s t ht isZ w u v
        (hx u hu) (hx v hv), zero_mul]

/-- For words acting only in two slots, all intermediate vectors stay in
the same block and the composed lift exponent is zero on that block. -/
theorem wordLiftExponent_eq_zero_on_block
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (r s : ι) (w : Word ι) (word : List (ι × Bool))
    (hword : ∀ step ∈ word, step.1 = r ∨ step.1 = s)
    (x : Word ι → F₂) (hx : SupportedInBlock r s w x) : wordLiftExponent word x = 0 := by
  induction word generalizing x with
  | nil => rfl
  | cons step tail ih =>
    obtain ⟨t, isZ⟩ := step
    have ht : t = r ∨ t = s := hword (t, isZ) (List.mem_cons_self)
    have htail : ∀ step ∈ tail, step.1 = r ∨ step.1 = s :=
      fun step hstep => hword step (List.mem_cons_of_mem _ hstep)
    rw [wordLiftExponent, generator_liftExponent_eq_zero_on_block hodd hm r s t ht isZ w x hx,
      ih htail _ (generator_preserves_block hodd r s t ht isZ w x hx), zero_add]

private theorem liftExponent_single (g : Matrix (Word ι) (Word ι) ℤ) (u : Word ι) (c : F₂) :
    liftExponent g (Pi.single u c) = 0 := by
  unfold liftExponent normalExponent
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hv : v = u
  · subst v
    have huw : u ≺ w := (Finset.mem_filter.mp hw).2
    have hne : u ≠ w := @ne_of_lt _ order.toPreorder _ _ huw
    simp [Pi.single_apply, hne, hne.symm]
  · simp [Pi.single_apply, hv, Ne.symm hv]

/-- A word confined to two slots has the same exponent as the normalized
lift of its product matrix. This applies to the KRR words
`[(r,false),(r,true)]` and `[(r,false),(s,false),(s,true)]`. -/
theorem wordLiftExponent_eq_liftExponent
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (r s : ι) (word : List (ι × Bool))
    (hword : ∀ step ∈ word, step.1 = r ∨ step.1 = s) (x : Word ι → F₂) :
    wordLiftExponent word x = liftExponent (wordMatrix word) x := by
  let δ (z : Word ι → F₂) := wordLiftExponent word z + liftExponent (wordMatrix word) z
  have hsingle (u : Word ι) (c : F₂) : δ (Pi.single u c) = 0 := by
    unfold δ
    rw [wordLiftExponent_eq_zero_on_block hodd hm r s u word hword _
      (single_supported r s u u c (fun _ _ _ => rfl)), liftExponent_single, zero_add]
  have hpolar (a b : Word ι → F₂) : δ (a + b) + (δ a + δ b) = 0 := by
    unfold δ
    calc
      _ = (wordLiftExponent word (a + b) + wordLiftExponent word a + wordLiftExponent word b) +
          (liftExponent (wordMatrix word) (a + b) + liftExponent (wordMatrix word) a +
            liftExponent (wordMatrix word) b) := by abel
      _ = 0 := by
        rw [wordLiftExponent_polar hodd (by omega),
          liftExponent_polar hodd (by omega) _ (wordMatrix_preserves_gram hodd word),
          CharTwo.add_self_eq_zero]
  let f : (Word ι → F₂) →+ F₂ :=
    { toFun := δ
      map_zero' := by
        simpa only [add_zero, CharTwo.add_self_eq_zero] using hpolar 0 0
      map_add' := fun a b => CharTwo.add_eq_zero.mp (hpolar a b) }
  apply CharTwo.add_eq_zero.mp
  change f x = 0
  calc
    f x = f (∑ u, Pi.single u (x u)) := congrArg f (Finset.univ_sum_single x).symm
    _ = ∑ u, f (Pi.single u (x u)) := map_sum f _ _
    _ = 0 := Finset.sum_eq_zero fun u _ => hsingle u (x u)

end

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorLift
