/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetMatching
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetMatching
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreNormalizedJet]
   utility: none
   digest: The invertible regular blocks yield a formal opposite-slope path with matching regular coefficients and a prescribed quartic forbidden-corner difference. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreNormalizedJet

/-! # Solving the regular equations at orders two, three and four -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreJetMatching

open PeriodicMPSUniformHardCoreJetElimination
open PeriodicMPSUniformHardCoreNormalizedJet
open PeriodicMPSUniformHardCoreHigherJet
open PeriodicMPSUniformHardCoreQuarticSign
open PeriodicMPSUniformHardCoreFirstJet
  (realBlock imagBlock realBlock_det_ne_zero imagBlock_det_ne_zero)
open scoped Matrix

noncomputable section

def addReal₂ (x : Path) (u : Fin 4 → ℝ) : Path :=
  { x with a₂ := x.a₂ + u 0, b₂ := x.b₂ + u 1, c₂ := x.c₂ + u 2, d₂ := x.d₂ + u 3 }

def addImag₃ (x : Path) (u : Fin 3 → ℝ) : Path :=
  { x with b₃ := x.b₃ + u 0, c₃ := x.c₃ + u 1, d₃ := x.d₃ + u 2 }

def addReal₄ (x : Path) (u : Fin 4 → ℝ) : Path :=
  { x with a₄ := x.a₄ + u 0, b₄ := x.b₄ + u 1, c₄ := x.c₄ + u 2, d₄ := x.d₄ + u 3 }

private def realRows : Fin 4 → Fin 7 := ![1, 2, 4, 5]
private def imagRows : Fin 3 → Fin 7 := ![3, 4, 5]

private def realJet (n : ℕ) (x : Path) (k : ℕ) : Fin 4 → ℝ :=
  fun i => normalizedCoeff false n x (realRows i).castSucc k

private def imagJet (n : ℕ) (x : Path) (k : ℕ) : Fin 3 → ℝ :=
  fun i => normalizedCoeff true n x (imagRows i).castSucc k

private def pA (n f : ℝ) : ℝ := 2 * ((3*n-3)*f + (5-4*n)) / 5
private def pB (n f : ℝ) : ℝ := 2 * ((1-n)*f + 3*n) / 5
private def qA (n f : ℝ) : ℝ := 2 * ((19-4*n)*f + (7*n-30)) / 5

private def realMassShift (n f : ℝ) (u : Fin 4 → ℝ) : ℝ :=
  2*n*((f-1)*u 0 + u 1)

private def realRawShift (n f : ℝ) (u : Fin 4 → ℝ) : Fin 7 → ℝ :=
  let p := pA n f * u 0 + pB n f * u 1
  ![realMassShift n f u - 2*p, p,
    qA n f*u 0 + pA n f*u 1 + 2*(2-f)*(u 2+u 3),
    p + (3-2*f)*u 0 - u 1 + (f-1)*(u 2+u 3),
    (3-f)*u 2 + (f-1)*u 3, u 2 + (f-1)*u 3, 0]

private def imagRawShift (f : ℝ) (u : Fin 3 → ℝ) : Fin 7 → ℝ :=
  ![0, 0, 0, -u 0 + (1-f)*(u 1+u 2), (3-f)*u 1+(f-1)*u 2, u 1+(f-1)*u 2, 0]

@[local simp] private theorem monomial_2 (y : Parameters) :
    Sparse.monomialValue y 2 = y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_3 (y : Parameters) :
    Sparse.monomialValue y 3 = y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_4 (y : Parameters) :
    Sparse.monomialValue y 4 = y 0 * y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_5 (y : Parameters) :
    Sparse.monomialValue y 5 = y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_6 (y : Parameters) :
    Sparse.monomialValue y 6 = y 0 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_7 (y : Parameters) :
    Sparse.monomialValue y 7 = y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_8 (y : Parameters) :
    Sparse.monomialValue y 8 = y 0 * y 0 * y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 0) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_9 (y : Parameters) :
    Sparse.monomialValue y 9 = y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_10 (y : Parameters) :
    Sparse.monomialValue y 10 = y 0 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_11 (y : Parameters) :
    Sparse.monomialValue y 11 = y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_12 (y : Parameters) :
    Sparse.monomialValue y 12 = y 0 * y 0 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_13 (y : Parameters) :
    Sparse.monomialValue y 13 = y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_14 (y : Parameters) :
    Sparse.monomialValue y 14 = y 0 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_15 (y : Parameters) :
    Sparse.monomialValue y 15 = y 1 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_16 (y : Parameters) :
    Sparse.monomialValue y 16 = y 0 * y 0 * y 0 * y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 0 * primeCode 0) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_17 (y : Parameters) :
    Sparse.monomialValue y 17 = y 6 := by
  calc
    _ = Sparse.monomialValue y (primeCode 6) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_18 (y : Parameters) :
    Sparse.monomialValue y 18 = y 0 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_19 (y : Parameters) :
    Sparse.monomialValue y 19 = y 7 := by
  calc
    _ = Sparse.monomialValue y (primeCode 7) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_20 (y : Parameters) :
    Sparse.monomialValue y 20 = y 0 * y 0 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_21 (y : Parameters) :
    Sparse.monomialValue y 21 = y 1 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_22 (y : Parameters) :
    Sparse.monomialValue y 22 = y 0 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_23 (y : Parameters) :
    Sparse.monomialValue y 23 = y 8 := by
  calc
    _ = Sparse.monomialValue y (primeCode 8) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_24 (y : Parameters) :
    Sparse.monomialValue y 24 = y 0 * y 0 * y 0 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 0 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_25 (y : Parameters) :
    Sparse.monomialValue y 25 = y 2 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_26 (y : Parameters) :
    Sparse.monomialValue y 26 = y 0 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_27 (y : Parameters) :
    Sparse.monomialValue y 27 = y 1 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_28 (y : Parameters) :
    Sparse.monomialValue y 28 = y 0 * y 0 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_29 (y : Parameters) :
    Sparse.monomialValue y 29 = y 9 := by
  calc
    _ = Sparse.monomialValue y (primeCode 9) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_30 (y : Parameters) :
    Sparse.monomialValue y 30 = y 0 * y 1 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_31 (y : Parameters) :
    Sparse.monomialValue y 31 = y 10 := by
  calc
    _ = Sparse.monomialValue y (primeCode 10) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_33 (y : Parameters) :
    Sparse.monomialValue y 33 = y 1 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_34 (y : Parameters) :
    Sparse.monomialValue y 34 = y 0 * y 6 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 6) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_35 (y : Parameters) :
    Sparse.monomialValue y 35 = y 2 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_36 (y : Parameters) :
    Sparse.monomialValue y 36 = y 0 * y 0 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_37 (y : Parameters) :
    Sparse.monomialValue y 37 = y 11 := by
  calc
    _ = Sparse.monomialValue y (primeCode 11) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_38 (y : Parameters) :
    Sparse.monomialValue y 38 = y 0 * y 7 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 7) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_39 (y : Parameters) :
    Sparse.monomialValue y 39 = y 1 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_41 (y : Parameters) :
    Sparse.monomialValue y 41 = y 12 := by
  calc
    _ = Sparse.monomialValue y (primeCode 12) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_42 (y : Parameters) :
    Sparse.monomialValue y 42 = y 0 * y 1 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_44 (y : Parameters) :
    Sparse.monomialValue y 44 = y 0 * y 0 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_45 (y : Parameters) :
    Sparse.monomialValue y 45 = y 1 * y 1 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 2) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_46 (y : Parameters) :
    Sparse.monomialValue y 46 = y 0 * y 8 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 8) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_49 (y : Parameters) :
    Sparse.monomialValue y 49 = y 3 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 3 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_51 (y : Parameters) :
    Sparse.monomialValue y 51 = y 1 * y 6 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 6) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_52 (y : Parameters) :
    Sparse.monomialValue y 52 = y 0 * y 0 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_54 (y : Parameters) :
    Sparse.monomialValue y 54 = y 0 * y 1 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_55 (y : Parameters) :
    Sparse.monomialValue y 55 = y 2 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_57 (y : Parameters) :
    Sparse.monomialValue y 57 = y 1 * y 7 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 7) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_63 (y : Parameters) :
    Sparse.monomialValue y 63 = y 1 * y 1 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 3) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_65 (y : Parameters) :
    Sparse.monomialValue y 65 = y 2 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_66 (y : Parameters) :
    Sparse.monomialValue y 66 = y 0 * y 1 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_69 (y : Parameters) :
    Sparse.monomialValue y 69 = y 1 * y 8 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 8) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_77 (y : Parameters) :
    Sparse.monomialValue y 77 = y 3 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 3 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_78 (y : Parameters) :
    Sparse.monomialValue y 78 = y 0 * y 1 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_81 (y : Parameters) :
    Sparse.monomialValue y 81 = y 1 * y 1 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 1 * primeCode 1) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_91 (y : Parameters) :
    Sparse.monomialValue y 91 = y 3 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 3 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_99 (y : Parameters) :
    Sparse.monomialValue y 99 = y 1 * y 1 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_117 (y : Parameters) :
    Sparse.monomialValue y 117 = y 1 * y 1 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_121 (y : Parameters) :
    Sparse.monomialValue y 121 = y 4 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4 * primeCode 4) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_143 (y : Parameters) :
    Sparse.monomialValue y 143 = y 4 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_169 (y : Parameters) :
    Sparse.monomialValue y 169 = y 5 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 5 * primeCode 5) := congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]


private theorem weight_real₂ (n : ℕ) (x : Path) (u : Fin 4 → ℝ) (i : Fin 7) :
    -weightValue n (addReal₂ x u) 2 i.val =
      -weightValue n x 2 i.val + realRawShift n (ratio n) u i := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addReal₂, realRawShift, realMassShift, pA, pB, qA] <;> ring

private theorem weight_imag₃ (n : ℕ) (x : Path) (u : Fin 3 → ℝ) (i : Fin 7) :
    -weightValue n (addImag₃ x u) 3 i.val =
      -weightValue n x 3 i.val + imagRawShift (ratio n) u i := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addImag₃, imagRawShift] <;> ring

set_option maxHeartbeats 5000000 in
private theorem weight_real₄ (n : ℕ) (x : Path) (u : Fin 4 → ℝ) (i : Fin 7) :
    weightValue n (addReal₄ x u) 4 i.val =
      weightValue n x 4 i.val + realRawShift n (ratio n) u i := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addReal₄, realRawShift, realMassShift, pA, pB, qA] <;> ring

private theorem weight_two_imag₃ (n : ℕ) (x : Path) (u : Fin 3 → ℝ) (i : Fin 7) :
    weightValue n (addImag₃ x u) 2 i.val = weightValue n x 2 i.val := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addImag₃]

private theorem weight_two_real₄ (n : ℕ) (x : Path) (u : Fin 4 → ℝ) (i : Fin 7) :
    weightValue n (addReal₄ x u) 2 i.val = weightValue n x 2 i.val := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addReal₄]

private theorem weight_three_real₄ (n : ℕ) (x : Path) (u : Fin 4 → ℝ) (i : Fin 7) :
    weightValue n (addReal₄ x u) 3 i.val = weightValue n x 3 i.val := by
  fin_cases i <;> norm_num [weightValue, weights, realWeight, Sparse.value, denominator,
    parameters, addReal₄]

private theorem normalized_zero_same (imag : Bool) (n : ℕ) (hn : 7 ≤ n)
    (x y : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 0 = normalizedCoeff imag n y row 0 := by
  cases imag <;> simp [normalized_zero, mass_zero n hn,
    (raw_zero n hn x row).1, (raw_zero n hn y row).1, (raw_zero n hn x row).2,
    (raw_zero n hn y row).2]

private theorem normalized_one_same (imag : Bool) (n : ℕ) (hn : 7 ≤ n)
    (x y : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 1 = normalizedCoeff imag n y row 1 := by
  cases imag <;> simp [normalized_one _ n hn, mass_zero n hn,
    (raw_first n hn x row).1, (raw_first n hn y row).1, (raw_first n hn x row).2,
    (raw_first n hn y row).2]

private theorem mass_two_formula (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    massCoeff n x 2 = -G n *
      (weightValue n x 2 0 + 2*weightValue n x 2 1 + weightValue n x 2 6) := by
  rw [mass_component, (raw_two n hn x 0).1, (raw_two n hn x 1).1, (raw_two n hn x 6).1]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  ring

private theorem mass_four_formula (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    massCoeff n x 4 = G n *
      (weightValue n x 4 0 + 2*weightValue n x 4 1 + weightValue n x 4 6) := by
  rw [mass_component, (raw_four n hn x 0).1, (raw_four n hn x 1).1, (raw_four n hn x 6).1]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  ring

private theorem mass_two_imag₃ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 3 → ℝ) :
    massCoeff n (addImag₃ x u) 2 = massCoeff n x 2 := by
  simp only [mass_two_formula n hn]
  have h₀ := weight_two_imag₃ n x u 0
  have h₁ := weight_two_imag₃ n x u 1
  have h₆ := weight_two_imag₃ n x u 6
  norm_num at h₀ h₁ h₆
  rw [h₀, h₁, h₆]

private theorem mass_two_real₄ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ) :
    massCoeff n (addReal₄ x u) 2 = massCoeff n x 2 := by
  simp only [mass_two_formula n hn]
  have h₀ := weight_two_real₄ n x u 0
  have h₁ := weight_two_real₄ n x u 1
  have h₆ := weight_two_real₄ n x u 6
  norm_num at h₀ h₁ h₆
  rw [h₀, h₁, h₆]

private theorem mass_shift_real₂ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ) :
    massCoeff n (addReal₂ x u) 2 = massCoeff n x 2 + G n*realMassShift n (ratio n) u := by
  simp only [mass_two n hn, mass₂, realMassShift, addReal₂]
  ring

private theorem mass_shift_real₄ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ) :
    massCoeff n (addReal₄ x u) 4 = massCoeff n x 4 + G n*realMassShift n (ratio n) u := by
  simp only [mass_four_formula n hn]
  have h₀ := weight_real₄ n x u 0
  have h₁ := weight_real₄ n x u 1
  have h₆ := weight_real₄ n x u 6
  norm_num [realRawShift] at h₀ h₁ h₆
  rw [h₀, h₁, h₆]
  ring

private theorem normalized_two_imag₃ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 3 → ℝ)
    (i : Fin 7) :
    normalizedCoeff false n (addImag₃ x u) i.castSucc 2 =
      normalizedCoeff false n x i.castSucc 2 := by
  simp only [normalized_two _ n hn, mass_two_imag₃ n hn, mass_zero n hn,
    normalized_zero_same false n hn (addImag₃ x u) x]
  rw [(raw_two n hn (addImag₃ x u) i.castSucc (by exact i.isLt)).1,
    (raw_two n hn x i.castSucc (by exact i.isLt)).1, Fin.val_castSucc, weight_two_imag₃]

private theorem normalized_two_real₄ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ)
    (i : Fin 7) :
    normalizedCoeff false n (addReal₄ x u) i.castSucc 2 =
      normalizedCoeff false n x i.castSucc 2 := by
  simp only [normalized_two _ n hn, mass_two_real₄ n hn, mass_zero n hn,
    normalized_zero_same false n hn (addReal₄ x u) x]
  rw [(raw_two n hn (addReal₄ x u) i.castSucc (by exact i.isLt)).1,
    (raw_two n hn x i.castSucc (by exact i.isLt)).1, Fin.val_castSucc, weight_two_real₄]

private theorem normalized_three_real₄ (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ)
    (i : Fin 7) :
    normalizedCoeff true n (addReal₄ x u) i.castSucc 3 =
      normalizedCoeff true n x i.castSucc 3 := by
  simp only [normalized_three _ n hn, mass_two_real₄ n hn, mass_zero n hn,
    normalized_one_same true n hn (addReal₄ x u) x]
  rw [(raw_three n hn (addReal₄ x u) i.castSucc (by exact i.isLt)).2,
    (raw_three n hn x i.castSucc (by exact i.isLt)).2, Fin.val_castSucc, weight_three_real₄]

private def baseReal (n : ℕ) (x : Path) : Fin 4 → ℝ :=
  realJet n x 0

private theorem realBlock_eq (n : ℕ) :
    realBlock n =
      let f := F n
      let g := G n
      let z := Z n
      let mA := 2 * (n : ℝ) * (f - g)
      let mB := 2 * (n : ℝ) * g
      let pA' := 2*((3*(n:ℝ)-3)*f+(5-4*(n:ℝ))*g)/5
      let pB' := 2*((1-(n:ℝ))*f+3*(n:ℝ)*g)/5
      let qA' := 2*((19-4*(n:ℝ))*f+(7*(n:ℝ)-30)*g)/5
      !![(z*pA'-g*mA)/z^2, (z*pB'-g*mB)/z^2, 0, 0;
        (z*qA'-(f-g)*mA)/z^2, (z*pA'-(f-g)*mB)/z^2, 2*(2*g-f)/z, 2*(2*g-f)/z;
        0, 0, (3*g-f)/z, (f-g)/z;
        0, 0, g/z, (f-g)/z] := rfl

private theorem normalized_real_shift_row (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ)
    (i : Fin 4) :
    (realBlock n *ᵥ u) i =
      (realRawShift n (ratio n) u (realRows i) - realMassShift n (ratio n) u * baseReal n x i) /
      (ratio n+2) := by
  have hF := F_eq_ratio_mul n hn
  have hZ : Z n = G n*(ratio n+2) := by unfold Z; rw [hF]; ring
  have hg := (G_pos hn).ne'
  have hz := ratio_add_two_ne_zero n hn
  fin_cases i <;>
    simp [baseReal, realJet, realRows, normalized_zero, mass_zero n hn,
      (raw_zero n hn x _).1, realRawShift, realMassShift, pA, pB, qA, realBlock_eq,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hZ, hF] <;> field_simp <;> ring

private theorem normalized_imag_shift_row (n : ℕ) (hn : 7 ≤ n) (u : Fin 3 → ℝ)
    (i : Fin 3) : (imagBlock n *ᵥ u) i =
      imagRawShift (ratio n) u (imagRows i)/(ratio n+2) := by
  have hF := F_eq_ratio_mul n hn
  have hZ : Z n = G n*(ratio n+2) := by unfold Z; rw [hF]; ring
  have hg := (G_pos hn).ne'
  have hz := ratio_add_two_ne_zero n hn
  fin_cases i <;>
    simp [imagRows, imagRawShift, imagBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hZ, hF] <;> field_simp

private theorem adjust (g z raw mass const dr dm : ℝ) (hg : g ≠ 0) (hz : z ≠ 0) :
    ((raw + g*dr) - (mass + g*dm)*const)/(g*z) =
      (raw-mass*const)/(g*z) + (dr-dm*const)/z := by
  field_simp
  ring

private theorem realJet_shift_two (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ) :
    realJet n (addReal₂ x u) 2 = realJet n x 2 + realBlock n *ᵥ u := by
  funext i
  let row := realRows i
  let r := row.castSucc
  change normalizedCoeff false n (addReal₂ x u) r 2 =
    normalizedCoeff false n x r 2 + (realBlock n *ᵥ u) i
  simp only [normalized_two _ n hn, normalized_real_shift_row n hn x, mass_zero n hn,
    mass_shift_real₂ n hn, normalized_zero_same false n hn (addReal₂ x u) x]
  rw [(raw_two n hn (addReal₂ x u) r (by exact row.isLt)).1,
    (raw_two n hn x r (by exact row.isLt)).1, Fin.val_castSucc, weight_real₂, mul_add]
  exact adjust _ _ _ _ _ _ _ (G_pos hn).ne' (ratio_add_two_ne_zero n hn)

private theorem imagJet_shift_three (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 3 → ℝ) :
    imagJet n (addImag₃ x u) 3 = imagJet n x 3 + imagBlock n *ᵥ u := by
  funext i
  let row := imagRows i
  let r := row.castSucc
  change normalizedCoeff true n (addImag₃ x u) r 3 =
    normalizedCoeff true n x r 3 + (imagBlock n *ᵥ u) i
  simp only [normalized_three _ n hn, normalized_imag_shift_row n hn, mass_zero n hn,
    mass_two_imag₃ n hn, normalized_one_same true n hn (addImag₃ x u) x]
  rw [(raw_three n hn (addImag₃ x u) r (by exact row.isLt)).2,
    (raw_three n hn x r (by exact row.isLt)).2, Fin.val_castSucc, weight_imag₃]
  have hg := (G_pos hn).ne'
  have hz := ratio_add_two_ne_zero n hn
  field_simp
  dsimp [row]
  ring

private theorem realJet_shift_four (n : ℕ) (hn : 7 ≤ n) (x : Path) (u : Fin 4 → ℝ) :
    realJet n (addReal₄ x u) 4 = realJet n x 4 + realBlock n *ᵥ u := by
  funext i
  let row := realRows i
  let r := row.castSucc
  change normalizedCoeff false n (addReal₄ x u) r 4 =
    normalizedCoeff false n x r 4 + (realBlock n *ᵥ u) i
  simp only [normalized_four _ n hn, normalized_real_shift_row n hn x, mass_zero n hn,
    mass_shift_real₄ n hn, mass_two_real₄ n hn,
    normalized_zero_same false n hn (addReal₄ x u) x]
  rw [(raw_four n hn (addReal₄ x u) r (by exact row.isLt)).1,
    (raw_four n hn x r (by exact row.isLt)).1, Fin.val_castSucc, weight_real₄]
  have hg := (G_pos hn).ne'
  have hz := ratio_add_two_ne_zero n hn
  unfold baseReal realJet
  rw [normalized_two_real₄ n hn x u row]
  field_simp
  dsimp [r, row]
  ring

private theorem realJet_three_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    realJet n x 3 = 0 := by
  funext i
  let row := realRows i
  exact (by
    change normalizedCoeff false n x row.castSucc 3 = 0
    rw [normalized_three _ n hn, normalized_one _ n hn,
      (raw_three n hn x row.castSucc (by exact row.isLt)).1, (raw_first n hn x _).1]
    simp)

private theorem imagJet_two_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    imagJet n x 2 = 0 := by
  funext i
  let row := imagRows i
  change normalizedCoeff true n x row.castSucc 2 = 0
  rw [normalized_two _ n hn, normalized_zero, (raw_zero n hn x _).2,
    (raw_two n hn x row.castSucc (by exact row.isLt)).2]
  simp

private theorem imagJet_four_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    imagJet n x 4 = 0 := by
  funext i
  let row := imagRows i
  change normalizedCoeff true n x row.castSucc 4 = 0
  have h := congrFun (imagJet_two_zero n hn x) i
  change normalizedCoeff true n x row.castSucc 2 = 0 at h
  rw [normalized_four _ n hn, normalized_zero, (raw_zero n hn x _).2,
    (raw_four n hn x row.castSucc (by exact row.isLt)).2, h]
  simp

private theorem regular_of_blocks (n : ℕ) (x y : Path) (k : ℕ)
    (hr : realJet n x k = realJet n y k) (hi : imagJet n x k = imagJet n y k) :
    regularCoeff n x k = regularCoeff n y k := by
  funext i
  fin_cases i
  · exact congrFun hr 0
  · exact congrFun hr 1
  · exact congrFun hr 2
  · exact congrFun hr 3
  · exact congrFun hi 0
  · exact congrFun hi 1
  · exact congrFun hi 2

/-- Successive real, imaginary and real corrections match all seven regular
readouts up to fourth order, for any prescribed first slope. -/
theorem exists_regular_match (n : ℕ) (hn : 7 ≤ n) (t : ℝ) :
    ∃ x : Path, x.t = t ∧ ∀ k ≤ 4, regularCoeff n x k = regularCoeff n original k := by
  have hR : IsUnit (realBlock n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realBlock_det_ne_zero n hn))
  have hI : IsUnit (imagBlock n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (imagBlock_det_ne_zero n hn))
  let base : Path := { t := t }
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hR
    (realJet n original 2 - realJet n base 2)
  let real₂ := addReal₂ base u
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hI
    (imagJet n original 3 - imagJet n real₂ 3)
  let imag₃ := addImag₃ real₂ v
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hR
    (realJet n original 4 - realJet n imag₃ 4)
  let x := addReal₄ imag₃ w
  refine ⟨x, rfl, ?_⟩
  intro k hk
  apply regular_of_blocks
  all_goals interval_cases k
  · exact funext fun i => normalized_zero_same false n hn x original _
  · exact funext fun i => normalized_one_same false n hn x original _
  · have h₀ : realJet n x 2 = realJet n imag₃ 2 :=
      funext fun i => normalized_two_real₄ n hn imag₃ w (realRows i)
    have h₁ : realJet n imag₃ 2 = realJet n real₂ 2 :=
      funext fun i => normalized_two_imag₃ n hn real₂ v (realRows i)
    rw [h₀, h₁]
    change realJet n (addReal₂ base u) 2 = _
    rw [realJet_shift_two n hn, hu, add_sub_cancel]
  · rw [realJet_three_zero n hn, realJet_three_zero n hn]
  · change realJet n (addReal₄ imag₃ w) 4 = _
    rw [realJet_shift_four n hn, hw, add_sub_cancel]
  · exact funext fun i => normalized_zero_same true n hn x original _
  · exact funext fun i => normalized_one_same true n hn x original _
  · rw [imagJet_two_zero n hn, imagJet_two_zero n hn]
  · have h₀ : imagJet n x 3 = imagJet n imag₃ 3 :=
      funext fun i => normalized_three_real₄ n hn imag₃ w (imagRows i)
    rw [h₀]
    change imagJet n (addImag₃ real₂ v) 3 = _
    rw [imagJet_shift_three n hn, hv, add_sub_cancel]
  · rw [imagJet_four_zero n hn, imagJet_four_zero n hn]

/-- A realized opposite-slope formal jet with regular readouts fixed through
order four, equal fold readout through order three, and the exact quartic separation. -/
theorem exists_opposite_regular_match (n : ℕ) (hn : 7 ≤ n) :
    ∃ x : Path, x.t = oppositeSlope n ∧ x.t ≠ 1 ∧
      (∀ k ≤ 4, regularCoeff n x k = regularCoeff n original k) ∧
      (∀ k ≤ 3, normalizedCoeff false n x 3 k = normalizedCoeff false n original 3 k) ∧
      (∀ k < 4, normalizedCoeff false n x 6 k = normalizedCoeff false n original 6 k) ∧
      normalizedCoeff false n x 6 4 - normalizedCoeff false n original 6 4 = quartic n := by
  obtain ⟨x, hx, hr⟩ := exists_regular_match n hn (oppositeSlope n)
  have h₂ : normalizedCoeff false n x 3 2 = normalizedCoeff false n original 3 2 := by
    have h := normalized_fold_difference n hn x (hr 2 (by decide))
    dsimp only at h
    have ha : foldA (ratio n) ≠ 0 := by
      intro he
      have hh := (denominator_factors hn).2.2.1
      have hg := (G_pos hn).ne'
      have he' : foldA (ratio n)*G n^2 = A n := by
        unfold foldA ratio A
        field_simp
      rw [he, zero_mul] at he'
      rw [← he'] at hh
      exact (lt_irrefl 0 hh)
    have hroot : foldA (ratio n)*x.t + foldB (ratio n) = 0 := by
      rw [hx, oppositeSlope]
      field_simp
      ring
    rw [hroot, mul_zero, zero_div] at h
    exact sub_eq_zero.mp h
  refine ⟨x, hx, hx ▸ oppositeSlope_ne_one n hn, hr, ?_, ?_, ?_⟩
  · intro k hk
    interval_cases k
    · exact normalized_zero_same false n hn x original 3
    · exact normalized_one_same false n hn x original 3
    · exact h₂
    · simp [normalized_three _ n hn, normalized_one _ n hn, (raw_three n hn x 3).1,
        (raw_three n hn original 3).1, (raw_first n hn x 3).1, (raw_first n hn original 3).1]
  · exact (opposite_forbidden_first_difference n hn x hx (fun k hk => hr k (by omega))).1
  · exact (opposite_forbidden_first_difference n hn x hx (fun k hk => hr k (by omega))).2.1

end

#print axioms exists_regular_match
#print axioms exists_opposite_regular_match

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreJetMatching
