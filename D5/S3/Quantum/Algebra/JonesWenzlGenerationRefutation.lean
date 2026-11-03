/- GID: D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim; result=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.result; claim=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim
   digest: Three two-strand Jones-Wenzl boxes fail to generate at the sixth root parameter. -/

import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Flores--Peltola, arXiv:1811.12364v2, Conjecture 1.2, generation half.
The presentation, Laurent quantum integers and indexing follow issue #25910.
The ambient subalgebra has the ambient unit, as fixed in that formal reading. -/

open scoped BigOperators

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

def compProj (q : ℂ) (ς : List ℕ) : TL ς.sum (-q - q⁻¹) :=
  ((List.range ς.length).map fun i =>
    jw q ς.sum (ς.take i).sum (ς[i]?.getD 0)).prod

def jwGen (q : ℂ) (ς : List ℕ) (i : ℕ) : TL ς.sum (-q - q⁻¹) :=
  compProj q ς * gen ς.sum (-q - q⁻¹) (ς.take i).sum * compProj q ς

def claim : Prop :=
  ∀ q : ℂ, q ≠ 0 → ∀ ς : List ℕ, (∀ s ∈ ς, 0 < s) →
    (∀ s ∈ ς, (s : ℕ∞) < pbar q) →
    ∀ t : TL ς.sum (-q - q⁻¹), compProj q ς * t * compProj q ς ∈
      Algebra.adjoin ℂ (insert (compProj q ς)
        {u | ∃ i, 1 ≤ i ∧ i < ς.length ∧ u = jwGen q ς i})

private def qzero : ℂ := Complex.exp (Real.pi * Complex.I / 6)

private def box : TL 6 (-qzero - qzero⁻¹) :=
  (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 1) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 3) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 (-qzero - qzero⁻¹) 5)

private def middle : TL 6 (-qzero - qzero⁻¹) :=
  gen 6 (-qzero - qzero⁻¹) 2 * gen 6 (-qzero - qzero⁻¹) 1 * gen 6 (-qzero - qzero⁻¹) 4 * gen 6 (-qzero - qzero⁻¹) 3 *
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
  · simp only [pbar, if_neg hne, hord, OfNat.ofNat_ne_zero, ↓reduceIte]
    rfl
  · rw [hinv, hq]
    ring

private theorem projector : compProj qzero [2, 2, 2] = box := by
  have hq : qint qzero 2 = (Real.sqrt 3 : ℂ) := by
    have hp := parameter.2.2
    norm_num [qint, Finset.sum_range_succ] at ⊢
    linear_combination -hp
  have h0 : qint qzero 0 = 0 := by simp only [qint, Finset.range_zero, Finset.sum_empty]
  have h1 : qint qzero 1 = 1 := by norm_num [qint, Finset.sum_range_succ]
  have hstep (a k : ℕ) : jw qzero 6 a (k + 1) = jw qzero 6 a k +
      (qint qzero k / qint qzero (k + 1)) •
        (jw qzero 6 a k * gen 6 (-qzero - qzero⁻¹) (a + k) * jw qzero 6 a k) := rfl
  have hz (a : ℕ) : jw qzero 6 a 0 = 1 := rfl
  have hb (a : ℕ) : jw qzero 6 a 2 =
      1 + (Real.sqrt 3 : ℂ)⁻¹ • gen 6 (-qzero - qzero⁻¹) (a + 1) := by
    rw [hstep a 1, hstep a 0, hz]
    simp only [h0, h1, hq, zero_div, zero_smul, add_zero, one_mul, mul_one, one_div]
  change jw qzero 6 0 2 * (jw qzero 6 2 2 * (jw qzero 6 4 2 * 1)) = box
  rw [hb, hb, hb]
  simpa only [box, mul_one, mul_assoc]

private theorem generators :
    (insert (compProj qzero [2, 2, 2])
      {u | ∃ i, 1 ≤ i ∧ i < ([2, 2, 2] : List ℕ).length ∧
        u = jwGen qzero [2, 2, 2] i}) =
    ({box, box * gen 6 (-qzero - qzero⁻¹) 2 * box, box * gen 6 (-qzero - qzero⁻¹) 4 * box} :
      Set (TL 6 (-qzero - qzero⁻¹))) := by
  ext u
  change (u = compProj qzero [2, 2, 2] ∨ (∃ i, 1 ≤ i ∧ i < 3 ∧ u = jwGen qzero [2, 2, 2] i)) ↔
    (u = box ∨ u = box * gen 6 (-qzero - qzero⁻¹) 2 * box ∨ u = box * gen 6 (-qzero - qzero⁻¹) 4 * box)
  constructor
  · rintro (hu | ⟨i, hi, hj, hu⟩)
    · exact Or.inl (hu.trans projector)
    · have : i = 1 ∨ i = 2 := by norm_num at hj; omega
      rcases this with rfl | rfl
      · apply Or.inr; apply Or.inl
        change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) * gen [2, 2, 2].sum (-qzero - qzero⁻¹) 2 * compProj qzero [2, 2, 2] at hu
        rw [projector] at hu
        exact hu
      · apply Or.inr; apply Or.inr
        change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) * gen [2, 2, 2].sum (-qzero - qzero⁻¹) 4 * compProj qzero [2, 2, 2] at hu
        rw [projector] at hu
        exact hu
  · rintro (hu | hu | hu)
    · exact Or.inl (hu.trans projector.symm)
    · apply Or.inr
      refine ⟨1, by omega, by norm_num, ?_⟩
      change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) * gen [2, 2, 2].sum (-qzero - qzero⁻¹) 2 * compProj qzero [2, 2, 2]
      rw [projector]
      exact hu
    · apply Or.inr
      refine ⟨2, by omega, by norm_num, ?_⟩
      change u = (compProj qzero [2, 2, 2] : TL 6 (-qzero - qzero⁻¹)) * gen [2, 2, 2].sum (-qzero - qzero⁻¹) 4 * compProj qzero [2, 2, 2]
      rw [projector]
      exact hu

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

private theorem separation : box * middle * box ∉
    Algebra.adjoin ℂ ({box, box * gen 6 (-qzero - qzero⁻¹) 2 * box,
      box * gen 6 (-qzero - qzero⁻¹) 4 * box} : Set (TL 6 (-qzero - qzero⁻¹))) := by
  have hcert := exactRelations
  sorry

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
