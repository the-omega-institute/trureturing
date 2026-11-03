/- GID: D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/JonesWenzlGenerationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim; result=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.result; claim=D5/S3/Quantum/Algebra/JonesWenzlGenerationRefutation.claim
   digest: Three two-strand Jones-Wenzl boxes fail to generate at the sixth root parameter. -/

import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ENat.Lattice

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

def TL (n : ℕ) (ν : ℂ) := RingQuot (rel n ν)

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
  (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 _ 1) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 _ 3) *
    (1 + ((Real.sqrt 3 : ℂ)⁻¹) • gen 6 _ 5)

private def middle : TL 6 (-qzero - qzero⁻¹) :=
  gen 6 _ 2 * gen 6 _ 1 * gen 6 _ 4 * gen 6 _ 3 *
    gen 6 _ 2 * gen 6 _ 5 * gen 6 _ 4

private theorem parameter : qzero ≠ 0 ∧ pbar qzero = 6 ∧
    -qzero - qzero⁻¹ = -(Real.sqrt 3 : ℂ) := by
  sorry

private theorem projector : compProj qzero [2, 2, 2] = box := by
  sorry

private theorem generators :
    (insert (compProj qzero [2, 2, 2])
      {u | ∃ i, 1 ≤ i ∧ i < ([2, 2, 2] : List ℕ).length ∧
        u = jwGen qzero [2, 2, 2] i}) =
    ({box, box * gen 6 _ 2 * box, box * gen 6 _ 4 * box} :
      Set (TL 6 (-qzero - qzero⁻¹))) := by
  sorry

private theorem separation : box * middle * box ∉
    Algebra.adjoin ℂ ({box, box * gen 6 _ 2 * box,
      box * gen 6 _ 4 * box} : Set (TL 6 (-qzero - qzero⁻¹))) := by
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

end D5.S3.Quantum.Algebra.JonesWenzlGenerationRefutation
