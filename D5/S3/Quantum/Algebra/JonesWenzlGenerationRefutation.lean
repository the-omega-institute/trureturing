/- GID: D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim; result=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.result; claim=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim
   digest: Three two-strand Jones-Wenzl boxes fail to generate at the sixth root parameter. -/

import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! Flores--Peltola, arXiv:1811.12364v2, Conjecture 1.2, generation half.
The presentation, Laurent quantum integers and indexing follow issue #25910.
The ambient subalgebra has the ambient unit, as fixed in that formal reading. -/

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Algebra.JonesWenzlGenerationRefutation

noncomputable section

def rel (n : ℕ) (ν : ℂ)
    (x y : FreeAlgebra ℂ (Fin (n - 1))) : Prop :=
  (∃ i, x = FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ i ∧
    y = ν • FreeAlgebra.ι ℂ i) ∨
  (∃ i j : Fin (n - 1), (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    x = FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i ∧
    y = FreeAlgebra.ι ℂ i) ∨
  (∃ i j : Fin (n - 1), (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
    x = FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j ∧
    y = FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i)

abbrev TL (n : ℕ) (ν : ℂ) := RingQuot (rel n ν)

def gen (n : ℕ) (ν : ℂ) (i : ℕ) : TL n ν :=
  if h : 1 ≤ i ∧ i < n then
    RingQuot.mkAlgHom ℂ (rel n ν) (FreeAlgebra.ι ℂ ⟨i - 1, by omega⟩)
  else 0

def qint (q : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, q ^ ((k : ℤ) - 1 - 2 * (j : ℤ))

def pbar (q : ℂ) : ℕ∞ :=
  if q = 1 ∨ q = -1 then ⊤ else
    if orderOf (q ^ 2) = 0 then ⊤ else (orderOf (q ^ 2) : ℕ∞)

def jw (q : ℂ) (n a s : ℕ) : TL n (-q - q⁻¹) :=
  Nat.rec 1 (fun k p => p + (qint q k / qint q (k + 1)) •
    (p * gen n (-q - q⁻¹) (a + k) * p)) s

def compProj (q : ℂ) (σ : List ℕ) : TL σ.sum (-q - q⁻¹) :=
  ((List.range σ.length).map fun i =>
    jw q σ.sum (σ.take i).sum (σ[i]?.getD 0)).prod

def jwGen (q : ℂ) (σ : List ℕ) (i : ℕ) : TL σ.sum (-q - q⁻¹) :=
  compProj q σ * gen σ.sum (-q - q⁻¹) (σ.take i).sum * compProj q σ

def claim : Prop :=
  ∀ q : ℂ, q ≠ 0 → ∀ σ : List ℕ, (∀ s ∈ σ, 0 < s) →
    (∀ s ∈ σ, (s : ℕ∞) < pbar q) →
    ∀ t : TL σ.sum (-q - q⁻¹), compProj q σ * t * compProj q σ ∈
      Algebra.adjoin ℂ (insert (compProj q σ)
        {u | ∃ i, 1 ≤ i ∧ i < σ.length ∧ u = jwGen q σ i})

private def qzero : ℂ := Complex.exp (Real.pi * Complex.I / 6)

private def box : TL 6 (-qzero - qzero⁻¹) :=
  (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 1) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 3) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 5)

private def middle : TL 6 (-qzero - qzero⁻¹) :=
  gen 6 (-qzero - qzero⁻¹) 2 * gen 6 (-qzero - qzero⁻¹) 1 * gen 6 (-qzero - qzero⁻¹) 4 *
    gen 6 (-qzero - qzero⁻¹) 3 *
    gen 6 (-qzero - qzero⁻¹) 2 * gen 6 (-qzero - qzero⁻¹) 5 * gen 6 (-qzero - qzero⁻¹) 4

private theorem parameter : qzero ≠ 0 ∧ pbar qzero = 6 ∧
    -qzero - qzero⁻¹ = -(Real.sqrt 3 : ℂ) := by
  have hq : qzero = (Real.sqrt 3 : ℂ) / 2 + Complex.I / 2 := by
    unfold qzero
    rw [show (Real.pi : ℂ) * Complex.I / 6 =
      (↑(Real.pi / 6) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast
    ring
  have hi : qzero.im = 1 / 2 := by rw [hq]; norm_num
  have hne : ¬ (qzero = 1 ∨ qzero = -1) := by
    rintro (h | h) <;> rw [h] at hi <;> norm_num at hi
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hinv : qzero⁻¹ = (Real.sqrt 3 : ℂ) / 2 - Complex.I / 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [hq]
    linear_combination hs / 4 - Complex.I_sq / 4
  have hord : orderOf (qzero ^ 2) = 6 := by
    have he : qzero ^ 2 = Complex.exp (2 * Real.pi * Complex.I / 6) := by
      rw [qzero, ← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [he]
    exact (Complex.isPrimitiveRoot_exp 6 (by norm_num)).eq_orderOf.symm
  refine ⟨Complex.exp_ne_zero _, ?_, ?_⟩
  · simp only [pbar.eq_1, ite_eq_right hne, hord, OfNat.ofNat_ne_zero, ↓reduceIte]
    rfl
  · rw [hinv, hq]
    ring

private theorem projector : compProj qzero [2, 2, 2] = box := by
  have hq : qint qzero 2 = (Real.sqrt 3 : ℂ) := by
    have hp := parameter.2.2
    norm_num [qint.eq_1, Finset.sum_range_succ] at ⊢
    linear_combination -hp
  have h0 : qint qzero 0 = 0 := by simp only [qint.eq_1, Finset.range_zero, Finset.sum_empty]
  have h1 : qint qzero 1 = 1 := by norm_num [qint.eq_1, Finset.sum_range_succ]
  have hstep (a k : ℕ) : jw qzero 6 a (k + 1) = jw qzero 6 a k +
      (qint qzero k / qint qzero (k + 1)) •
        (jw qzero 6 a k * gen 6 (-qzero - qzero⁻¹) (a + k) * jw qzero 6 a k) := by
    unfold jw
    exact Nat.rec_add_one (C := fun _ => TL 6 (-qzero - qzero⁻¹)) 1
      (fun k p => p + (qint qzero k / qint qzero (k + 1)) •
        (p * gen 6 (-qzero - qzero⁻¹) (a + k) * p)) k
  have hz (a : ℕ) : jw qzero 6 a 0 = 1 := by
    unfold jw
    exact Nat.rec_zero (C := fun _ => TL 6 (-qzero - qzero⁻¹)) 1
      (fun k p => p + (qint qzero k / qint qzero (k + 1)) •
        (p * gen 6 (-qzero - qzero⁻¹) (a + k) * p))
  have hb (a : ℕ) : jw qzero 6 a 2 =
      1 + (Real.sqrt 3 : ℂ)⁻¹ • gen 6 (-qzero - qzero⁻¹) (a + 1) := by
    rw [hstep a 1, hstep a 0, hz]
    simp only [h0, h1, hq, zero_div, zero_smul, add_zero, one_mul, mul_one, one_div]
  change jw qzero 6 0 2 * (jw qzero 6 2 2 * (jw qzero 6 4 2 * 1)) = box
  rw [hb, hb, hb]
  simp only [box.eq_1, mul_one, mul_assoc]

private theorem generators :
    (insert (compProj qzero [2, 2, 2])
      {u | ∃ i, 1 ≤ i ∧ i < ([2, 2, 2] : List ℕ).length ∧
        u = jwGen qzero [2, 2, 2] i}) =
    ({box, box * gen 6 (-qzero - qzero⁻¹) 2 * box, box * gen 6 (-qzero - qzero⁻¹) 4 * box} :
      Set (TL 6 (-qzero - qzero⁻¹))) := by
  ext u
  change (u = compProj qzero [2, 2, 2] ∨
    (∃ i, 1 ≤ i ∧ i < 3 ∧ u = jwGen qzero [2, 2, 2] i)) ↔
    (u = box ∨ u = box * gen 6 (-qzero - qzero⁻¹) 2 * box ∨
      u = box * gen 6 (-qzero - qzero⁻¹) 4 * box)
  constructor
  · rintro (hu | ⟨i, hi, hj, hu⟩)
    · exact Or.inl (hu.trans projector)
    · have : i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl
      · apply Or.inr; apply Or.inl
        change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) *
          gen [2, 2, 2].sum (-qzero - qzero⁻¹) 2 * compProj qzero [2, 2, 2] at hu
        rw [projector] at hu
        exact hu
      · apply Or.inr; apply Or.inr
        change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) *
          gen [2, 2, 2].sum (-qzero - qzero⁻¹) 4 * compProj qzero [2, 2, 2] at hu
        rw [projector] at hu
        exact hu
  · rintro (hu | hu | hu)
    · exact Or.inl (hu.trans projector.symm)
    · apply Or.inr
      refine ⟨1, by omega, by norm_num, ?_⟩
      change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) *
        gen [2, 2, 2].sum (-qzero - qzero⁻¹) 2 * compProj qzero [2, 2, 2]
      rw [projector]
      exact hu
    · apply Or.inr
      refine ⟨2, by omega, by norm_num, ?_⟩
      change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) *
        gen [2, 2, 2].sum (-qzero - qzero⁻¹) 4 * compProj qzero [2, 2, 2]
      rw [projector]
      exact hu

/- The exact coefficient ring has ω² = 3. The nine-dimensional matrices satisfy
all three presentation families. A common left eigenvector for the projected
boundary generators vanishes at coordinate 6, while its witness image there is
−2ω/3. Transporting ω to √3 gives the separating complex representation. -/

private abbrev coeff := QuadraticAlgebra ℚ 3 0

private def exactGen : Fin 5 → Matrix (Fin 9) (Fin 9) coeff :=
  ![!![0, 0, 0, 0, 0, 0, 0, 0, ⟨1, (1/3)⟩;
    0, 0, 0, 0, 0, 0, 0, 0, ⟨1, 1⟩;
    0, 0, 0, 0, 0, 0, 0, 0, ⟨1, (2/3)⟩;
    0, 1, 0, ⟨0, -1⟩, 0, 0, ⟨0, (-1/3)⟩, 0, ⟨1, (2/3)⟩;
    1, 0, 1, 0, ⟨0, -1⟩, ⟨0, (-1/3)⟩, 0, ⟨0, (-1/3)⟩, ⟨2, (2/3)⟩;
    0, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, ⟨0, -1⟩;
    0, 0, 0, 0, 0, 0, 0, 0, -2;
    0, 0, 0, 0, 0, 0, 0, 0, ⟨0, -1⟩],
   !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, ⟨0, -1⟩, 0, 1, 0, 0, ⟨0, (-1/3)⟩, 0, 0;
    0, 0, ⟨0, -1⟩, 0, 1, ⟨0, (-1/3)⟩, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, ⟨0, -1⟩],
   !![⟨0, -1⟩, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, ⟨0, -1⟩, ⟨0, (-1/3)⟩, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, ⟨0, -1⟩, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, ⟨0, -1⟩, 1, 0, 0, 0, 0, 0, ⟨0, (-1/3)⟩;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, ⟨0, -1⟩, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, ⟨0, -1⟩, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, ⟨0, -1⟩, 0, 0, 0, 0, 0, ⟨0, (-1/3)⟩;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, ⟨0, -1⟩, 0, 0, ⟨0, (-1/3)⟩, 0;
    0, 0, 0, 0, 0, ⟨0, -1⟩, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]]

private theorem exactRelations :
    (∀ i, exactGen i * exactGen i = (⟨0, -1⟩ : coeff) • exactGen i) ∧
    (∀ i j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) →
      exactGen i * exactGen j * exactGen i = exactGen i) ∧
    (∀ i j : Fin 5, (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
      exactGen i * exactGen j = exactGen j * exactGen i) := by
  unfold exactGen
  decide +kernel

private def exactP : Matrix (Fin 9) (Fin 9) coeff :=
  !![0, ⟨0, (1/3)⟩, 0, 0, 0, 0, 0, 0, ⟨(1/3), (1/3)⟩;
    0, 1, 0, 0, 0, 0, 0, 0, ⟨1, (1/3)⟩;
    0, ⟨0, (1/3)⟩, 0, 0, 0, 0, 0, 0, ⟨(1/3), (1/3)⟩;
    0, ⟨0, (1/3)⟩, 0, 0, 0, 0, (-1/3), 0, ⟨(2/3), (1/3)⟩;
    0, (2/3), 0, 0, 0, 0, ⟨0, (-2/9)⟩, 0, ⟨(2/3), (4/9)⟩;
    0, 0, 0, 0, 0, 0, ⟨0, (1/3)⟩, 0, ⟨0, (-1/3)⟩;
    0, 0, 0, 0, 0, 0, 1, 0, -1;
    0, 0, 0, 0, 0, 0, ⟨0, (1/3)⟩, 0, ⟨0, (-1/3)⟩;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem exactP_eq : exactP =
    (1 + (⟨0, 1/3⟩ : coeff) • exactGen 0) *
      (1 + (⟨0, 1/3⟩ : coeff) • exactGen 2) *
      (1 + (⟨0, 1/3⟩ : coeff) • exactGen 4) := by
  decide +kernel

private def exactSteps : Fin 8 → Fin 9 → coeff :=
  ![![0, ⟨3, -1⟩, 0, 0, 0, 0, 0, 0, 2],
    ![⟨3, -1⟩, ⟨3, -3⟩, 0, ⟨3, -1⟩, 0, 0, ⟨1, -1⟩, 2, ⟨0, -2⟩],
    ![0, ⟨3, -1⟩, 0, ⟨3, -3⟩, 0, 0, ⟨1, -1⟩, 0, 2],
    ![⟨3, -1⟩, ⟨3, -3⟩, ⟨3, -1⟩, ⟨9, -3⟩, ⟨3, -3⟩, ⟨1, -1⟩, ⟨3, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩],
    ![⟨3, -3⟩, ⟨3, -1⟩, ⟨3, -3⟩, ⟨3, -3⟩, ⟨9, -3⟩, ⟨3, -1⟩, ⟨1, -1⟩, ⟨3, -1⟩, ⟨1, -1⟩],
    ![⟨3, -1⟩, ⟨3, -3⟩, ⟨9, -3⟩, ⟨3, -1⟩, ⟨3, -3⟩, ⟨3, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨3, -1⟩],
    ![⟨3, -3⟩, ⟨9, -3⟩, ⟨9, -9⟩, ⟨3, -3⟩, ⟨9, -3⟩, ⟨3, -3⟩, ⟨3, -1⟩, ⟨3, -1⟩, ⟨3, -3⟩],
    ![⟨9, -3⟩, ⟨9, -9⟩, ⟨9, -3⟩, ⟨9, -3⟩, ⟨3, -3⟩, ⟨3, -1⟩, ⟨3, -3⟩, ⟨3, -1⟩, ⟨3, -3⟩]]

private def exactRow : Fin 9 → coeff := exactSteps 0

private def letters : Fin 7 → Fin 5 := ![1, 0, 3, 2, 1, 4, 3]

private theorem exactCertificate :
    (exactRow ᵥ* exactP = exactRow) ∧
    ((exactRow ᵥ* exactGen 1) ᵥ* exactP = (⟨0, -1/3⟩ : coeff) • exactRow) ∧
    ((exactRow ᵥ* exactGen 3) ᵥ* exactP = (⟨0, -1/3⟩ : coeff) • exactRow) ∧
    (∀ i : Fin 7, exactSteps ⟨i.val + 1, by omega⟩ =
      exactSteps ⟨i.val, by omega⟩ ᵥ* exactGen (letters i)) ∧
    ((exactSteps 7 ᵥ* exactP) 6 = (⟨0, -2/3⟩ : coeff)) := by
  decide +kernel

private def scalarEmbedding : coeff →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨(Real.sqrt 3 : ℂ), by
    norm_num [smul_eq_mul, ← pow_two]
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)⟩

private def modelGen (i : Fin 5) : Matrix (Fin 9) (Fin 9) ℂ :=
  scalarEmbedding.mapMatrix (exactGen i)

private def rho : TL 6 (-qzero - qzero⁻¹) →ₐ[ℂ] Matrix (Fin 9) (Fin 9) ℂ :=
  RingQuot.liftAlgHom ℂ ⟨FreeAlgebra.lift ℂ modelGen, by
    intro a b h
    rcases h with ⟨i, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩
    · simp only [map_mul, map_smul, FreeAlgebra.lift_ι_apply]
      have h := congrArg scalarEmbedding.mapMatrix (exactRelations.1 i)
      rw [map_mul] at h
      simp only [AlgHom.mapMatrix_apply,
        Matrix.map_smul' scalarEmbedding _ _ (map_mul scalarEmbedding)] at h
      rw [parameter.2.2]
      convert h using 1 <;> simp [modelGen.eq_1, scalarEmbedding.eq_1, QuadraticAlgebra.lift_apply_apply]
    · simp only [map_mul, FreeAlgebra.lift_ι_apply]
      have h := congrArg scalarEmbedding.mapMatrix (exactRelations.2.1 i j hij)
      simpa only [map_mul, modelGen.eq_1] using h
    · simp only [map_mul, FreeAlgebra.lift_ι_apply]
      have h := congrArg scalarEmbedding.mapMatrix (exactRelations.2.2 i j hij)
      simpa only [map_mul, modelGen.eq_1] using h⟩

private theorem rho_gen (i : Fin 5) :
    rho (gen 6 (-qzero - qzero⁻¹) (i.val + 1)) = modelGen i := by
  have hi : 1 ≤ i.val + 1 ∧ i.val + 1 < 6 := by have := i.isLt; omega
  simp only [gen.eq_1, dite_eq_left hi, rho.eq_1, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, Nat.add_sub_cancel]

private theorem rho_gens :
    rho (gen 6 (-qzero - qzero⁻¹) 1) = modelGen 0 ∧
    rho (gen 6 (-qzero - qzero⁻¹) 2) = modelGen 1 ∧
    rho (gen 6 (-qzero - qzero⁻¹) 3) = modelGen 2 ∧
    rho (gen 6 (-qzero - qzero⁻¹) 4) = modelGen 3 ∧
    rho (gen 6 (-qzero - qzero⁻¹) 5) = modelGen 4 :=
  ⟨rho_gen 0, rho_gen 1, rho_gen 2, rho_gen 3, rho_gen 4⟩

private theorem rho_box : rho box = scalarEmbedding.mapMatrix exactP := by
  have hs : scalarEmbedding (⟨0, 1/3⟩ : coeff) = (Real.sqrt 3 : ℂ)⁻¹ := by
    change (0 : ℚ) • (1 : ℂ) + (1/3 : ℚ) • (Real.sqrt 3 : ℂ) = _
    norm_num [Algebra.smul_def, ← Complex.ofReal_inv,
      ← Real.sqrt_div_self]
    push_cast
    ring
  rw [exactP_eq]
  simp only [map_mul, map_add, map_one, AlgHom.mapMatrix_apply,
    Matrix.map_smul' scalarEmbedding _ _ (map_mul scalarEmbedding), hs]
  rw [box.eq_1]
  rw [map_mul, map_mul]
  have h1 : rho (gen 6 (-qzero - qzero⁻¹) 1) = modelGen 0 := rho_gen 0
  have h3 : rho (gen 6 (-qzero - qzero⁻¹) 3) = modelGen 2 := rho_gen 2
  have h5 : rho (gen 6 (-qzero - qzero⁻¹) 5) = modelGen 4 := rho_gen 4
  simp only [map_add, map_one, map_smul, h1, h3, h5, modelGen.eq_1,
    AlgHom.mapMatrix_apply]

private theorem exactWitness :
    (exactRow ᵥ* (exactGen 1 * exactGen 0 * exactGen 3 * exactGen 2 *
      exactGen 1 * exactGen 4 * exactGen 3 * exactP)) 6 = (⟨0, -2/3⟩ : coeff) := by
  simp only [← Matrix.vecMul_vecMul]
  change ((((((((exactSteps 0 ᵥ* exactGen 1) ᵥ* exactGen 0) ᵥ* exactGen 3) ᵥ*
    exactGen 2) ᵥ* exactGen 1) ᵥ* exactGen 4) ᵥ* exactGen 3) ᵥ* exactP) 6 = _
  have h0 : exactSteps 1 = exactSteps 0 ᵥ* exactGen 1 := exactCertificate.2.2.2.1 0
  have h1 : exactSteps 2 = exactSteps 1 ᵥ* exactGen 0 := exactCertificate.2.2.2.1 1
  have h2 : exactSteps 3 = exactSteps 2 ᵥ* exactGen 3 := exactCertificate.2.2.2.1 2
  have h3 : exactSteps 4 = exactSteps 3 ᵥ* exactGen 2 := exactCertificate.2.2.2.1 3
  have h4 : exactSteps 5 = exactSteps 4 ᵥ* exactGen 1 := exactCertificate.2.2.2.1 4
  have h5 : exactSteps 6 = exactSteps 5 ᵥ* exactGen 4 := exactCertificate.2.2.2.1 5
  have h6 : exactSteps 7 = exactSteps 6 ᵥ* exactGen 3 := exactCertificate.2.2.2.1 6
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  exact exactCertificate.2.2.2.2

private def row : Fin 9 → ℂ := scalarEmbedding ∘ exactRow

private theorem embedding_row (v : Fin 9 → coeff) (m : Matrix (Fin 9) (Fin 9) coeff) :
    scalarEmbedding ∘ (v ᵥ* m) = (scalarEmbedding ∘ v) ᵥ* scalarEmbedding.mapMatrix m := by
  funext j
  exact RingHom.map_vecMul scalarEmbedding.toRingHom m v j

private theorem embedding_row_smul (c : coeff) (v : Fin 9 → coeff) :
    scalarEmbedding ∘ (c • v) = scalarEmbedding c • (scalarEmbedding ∘ v) := by
  funext j
  exact map_mul scalarEmbedding c (v j)

private theorem row_projector : row ᵥ* scalarEmbedding.mapMatrix exactP = row := by
  have h := congrArg (fun v => scalarEmbedding ∘ v) exactCertificate.1
  simpa only [embedding_row, row.eq_1] using h

private theorem row_generators :
    (row ᵥ* (scalarEmbedding.mapMatrix exactP * modelGen 1 * scalarEmbedding.mapMatrix exactP) =
      scalarEmbedding (⟨0, -1/3⟩ : coeff) • row) ∧
    (row ᵥ* (scalarEmbedding.mapMatrix exactP * modelGen 3 * scalarEmbedding.mapMatrix exactP) =
      scalarEmbedding (⟨0, -1/3⟩ : coeff) • row) := by
  constructor
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, row_projector]
    have h := congrArg (fun v => scalarEmbedding ∘ v) exactCertificate.2.1
    simpa only [embedding_row, embedding_row_smul, row.eq_1, modelGen.eq_1] using h
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, row_projector]
    have h := congrArg (fun v => scalarEmbedding ∘ v) exactCertificate.2.2.1
    simpa only [embedding_row, embedding_row_smul, row.eq_1, modelGen.eq_1] using h

private theorem row_witness : (row ᵥ* rho (box * middle * box)) 6 ≠ 0 := by
  have hmid : rho middle = scalarEmbedding.mapMatrix
      (exactGen 1 * exactGen 0 * exactGen 3 * exactGen 2 *
        exactGen 1 * exactGen 4 * exactGen 3) := by
    unfold middle
    simp only [map_mul]
    rw [rho_gens.1, rho_gens.2.1, rho_gens.2.2.1, rho_gens.2.2.2.1, rho_gens.2.2.2.2]
    rfl
  rw [map_mul, map_mul, rho_box, hmid]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, row_projector,
    Matrix.vecMul_vecMul, ← map_mul]
  change ((scalarEmbedding ∘ exactRow) ᵥ* scalarEmbedding.mapMatrix
    (exactGen 1 * exactGen 0 * exactGen 3 * exactGen 2 * exactGen 1 * exactGen 4 *
      exactGen 3 * exactP)) 6 ≠ 0
  rw [← embedding_row]
  change scalarEmbedding ((exactRow ᵥ* (exactGen 1 * exactGen 0 * exactGen 3 *
    exactGen 2 * exactGen 1 * exactGen 4 * exactGen 3 * exactP)) 6) ≠ 0
  rw [exactWitness]
  change (0 : ℚ) • (1 : ℂ) + (-2/3 : ℚ) • (Real.sqrt 3 : ℂ) ≠ 0
  norm_num [Algebra.smul_def, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]

private def rowStabilizer : Subalgebra ℂ (Matrix (Fin 9) (Fin 9) ℂ) where
  carrier := {m | ∃ c : ℂ, row ᵥ* m = c • row}
  algebraMap_mem' c := ⟨c, by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, Matrix.vecMul_one]⟩
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Matrix.vecMul_add, hc, hd, add_smul]⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [← Matrix.vecMul_vecMul, hc, Matrix.smul_vecMul, hd, smul_smul]⟩

private theorem separation : box * middle * box ∉
    Algebra.adjoin ℂ ({box, box * gen 6 (-qzero - qzero⁻¹) 2 * box,
      box * gen 6 (-qzero - qzero⁻¹) 4 * box} : Set (TL 6 (-qzero - qzero⁻¹))) := by
  intro hz
  have hg : ({box, box * gen 6 (-qzero - qzero⁻¹) 2 * box,
      box * gen 6 (-qzero - qzero⁻¹) 4 * box} : Set (TL 6 (-qzero - qzero⁻¹))) ⊆
      rowStabilizer.comap rho := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · change ∃ c : ℂ, row ᵥ* rho box = c • row
      exact ⟨1, by rw [rho_box, row_projector, one_smul]⟩
    · change ∃ c : ℂ, row ᵥ* rho (box * gen 6 (-qzero - qzero⁻¹) 2 * box) = c • row
      refine ⟨scalarEmbedding (⟨0, -1/3⟩ : coeff), ?_⟩
      rw [map_mul, map_mul, rho_box, rho_gens.2.1]
      exact row_generators.1
    · change ∃ c : ℂ, row ᵥ* rho (box * gen 6 (-qzero - qzero⁻¹) 4 * box) = c • row
      refine ⟨scalarEmbedding (⟨0, -1/3⟩ : coeff), ?_⟩
      rw [map_mul, map_mul, rho_box, rho_gens.2.2.2.1]
      exact row_generators.2
  obtain ⟨c, hc⟩ := Algebra.adjoin_le hg hz
  have h0 : row 6 = 0 := by
    change scalarEmbedding (0 : coeff) = 0
    exact map_zero scalarEmbedding
  have hw := congrFun hc 6
  rw [Pi.smul_apply, h0, smul_zero] at hw
  exact row_witness hw

theorem result : ¬ claim := by
  intro h
  have hp := parameter
  have hz := h qzero hp.1 [2, 2, 2] (by simp) (by
    intro s hs
    have : s = 2 := by simpa using hs
    subst s
    rw [hp.2.1]
    norm_num) middle
  rw [generators, projector] at hz
  exact separation hz

end

end D5.S3.Quantum.Algebra.JonesWenzlGenerationRefutation
