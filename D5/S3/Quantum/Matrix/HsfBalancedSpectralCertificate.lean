/- GID: D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfBalancedSpectralCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: A finite weighted Gram certificate for the noncommutative two-level balanced supplier. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-! Finite block coefficient algebra for the alpha-three balanced HSF supplier.
The blocks may have unequal finite dimensions and the positive direction may
be singular. This does not settle the full HSF conjecture. Fractional-power
derivative identification is a separate analytic bridge. The trace and positive
quadratic-form arguments are classical; no literature novelty is asserted.
Unfinished source-binding audits are associated with
https://github.com/the-omega-institute/trureturing/issues/23103. -/

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.HsfBalancedSpectralCertificate

def den (r : ℝ) : ℝ := r^2+r+1
def aux (r : ℝ) : ℝ := 4*r^2+7*r+4

/-- The two-level first divided-difference multiplier, for eigenvalues 1,r³. -/
def tau (r : ℝ) : ℝ := 3*Real.sqrt r*(r+1)/(2*den r)

/-- The repeated-spectral-index cubic remainder. -/
def kappa (r : ℝ) : ℝ :=
  r*(r-1)^2*(r^2-r+1)*(r^2+7*r+1)/(12*(den r)^4)

def gap (r : ℝ) : ℝ := (r-1)^2*aux r/(4*(den r)^2)
def gramGap (r : ℝ) : ℝ :=
  r*(r-1)^2*(r+1)^2*(5*r^4+22*r^3+36*r^2+22*r+5)/
    (3*(den r)^4*aux r)
def pv (r : ℝ) : ℝ :=
  Real.sqrt r*(r^3+2*r^2+10*r+5)/(2*(den r)^2)
def qv (r : ℝ) : ℝ := r*(4*r^3+5*r^2+6*r+3)/(2*(den r)^2)
def pw (r : ℝ) : ℝ := (3*r^3+6*r^2+5*r+4)/(2*(den r)^2)
def qw (r : ℝ) : ℝ :=
  Real.sqrt r*(5*r^3+10*r^2+2*r+1)/(2*(den r)^2)
def pc (r : ℝ) : ℝ :=
  (3*r^3+15*r^2+19*r+8)/(den r*aux r)
def qc (r : ℝ) : ℝ :=
  -Real.sqrt r*(r-1)*(2*r^2+3*r+2)/(den r*aux r)
def pn (r : ℝ) : ℝ :=
  (r^2+2)*(2*r^5+8*r^4+24*r^3+25*r^2+16*r+6)/(3*(den r)^4)
def qn (r : ℝ) : ℝ :=
  r*(2*r^2+1)*(6*r^5+16*r^4+25*r^3+24*r^2+8*r+2)/(3*(den r)^4)

private theorem scalar_gram (r : ℝ) (hr : 0 < r) :
    tau r ^ 2 + gap r = 1 ∧
    tau r * pv r + gap r * pc r = pw r ∧
    tau r * qv r + gap r * qc r = qw r ∧
    pv r ^ 2 + gap r * pc r ^ 2 + gramGap r = pn r ∧
    qv r ^ 2 + gap r * qc r ^ 2 + gramGap r = qn r ∧
    4-tau r ^ 2-2*qv r-pn r = kappa r ∧
    4-tau r ^ 2-2*pw r-qn r = kappa r := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  have ha : aux r ≠ 0 := ne_of_gt (by unfold aux; positivity)
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  unfold tau gap pv pc pw qv qc qw gramGap pn qn kappa
  repeat' constructor
  all_goals field_simp [hd, ha]
  all_goals try dsimp [den, aux]
  all_goals ring_nf
  all_goals simp only [hs]
  all_goals ring


variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem trace_blocks (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (D : Matrix n m ℂ) (H : Matrix n n ℂ) :
    (fromBlocks A C D H).trace = A.trace+H.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- Real trace; cyclicity is used without commuting matrix factors. -/
def tr {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ := M.trace.re

private theorem tr_add {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℂ) :
    tr (M+N) = tr M+tr N := by simp [tr, Matrix.trace_add]
private theorem tr_sub {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℂ) :
    tr (M-N) = tr M-tr N := by simp [tr, Matrix.trace_sub]
private theorem tr_neg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    tr (-M) = -tr M := by simp [tr, Matrix.trace_neg]
private theorem tr_zero {ι : Type*} [Fintype ι] : tr (0 : Matrix ι ι ℂ) = 0 := by
  simp [tr]
private theorem tr_smul {ι : Type*} [Fintype ι] (a : ℝ) (M : Matrix ι ι ℂ) :
    tr (a • M) = a*tr M := by simp [tr, Matrix.trace_smul]
private theorem tr_blocks (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (D : Matrix n m ℂ) (H : Matrix n n ℂ) :
    tr (fromBlocks A C D H) = tr A+tr H := by simp [tr, trace_blocks]
private theorem tr_cycle {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ξ ℂ) (C : Matrix ξ ι ℂ) :
    tr (A*B*C) = tr (B*C*A) := congrArg Complex.re (Matrix.trace_mul_cycle B C A).symm
private theorem tr_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) : tr (A*B) = tr (B*A) :=
  congrArg Complex.re (Matrix.trace_mul_comm A B)

/-- A complex Hermitian block direction, with rectangular off-diagonal block. -/
def direction (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks A C Cᴴ H

/-- The actual first coefficient in the balanced normalization. -/
def first (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  (2/3 : ℝ) • fromBlocks A (tau r • C) (tau r • Cᴴ) H

/-- The confluent second coefficient; both diagonal spectral multiplicities are arbitrary. -/
def second (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks
    ((-1/9 : ℝ) • (A*A) - (r^3*(2*r+1)/(3*(den r)^2)) • (C*Cᴴ))
    (-(Real.sqrt r/(3*(den r)^2)) • ((2*r+1) • (A*C) + (r^2*(r+2)) • (C*H)))
    (-(Real.sqrt r/(3*(den r)^2)) • ((2*r+1) • (Cᴴ*A) + (r^2*(r+2)) • (H*Cᴴ)))
    ((-1/9 : ℝ) • (H*H) - ((r+2)/(3*(den r)^2)) • (Cᴴ*C))

private theorem trace_cube_blocks (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (D : Matrix n m ℂ) (H : Matrix n n ℂ) (t : ℝ) :
    tr ((fromBlocks A (t • C) (t • D) H)^3) =
      tr (A*A*A)+tr (H*H*H)+3*t^2*(tr (A*C*D)+tr (H*D*C)) := by
  simp only [pow_succ, pow_zero, one_mul, fromBlocks_multiply, tr_blocks,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, tr_add, tr_smul]
  try simp only [← Matrix.mul_assoc]
  rw [tr_cycle C D A, tr_cycle D A C, tr_cycle D C H, tr_cycle C H D]
  ring

/-- A row of the finite Gram model. Its four parameters are real scalars. -/
def gramRow (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (v p q w : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (v • A) (p • C) (q • Cᴴ) (w • H)

/-- Diagonal row of the Gram model. -/
def gramDiag (v w : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (v • 1) 0 0 (w • 1)

private theorem row_energy (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (v p q w : ℝ) :
    tr ((gramRow A C H v p q w)ᴴ * direction A C H * gramRow A C H v p q w) =
      v^2*tr (A*A*A)+w^2*tr (H*H*H)+
      (2*v*q+p^2)*tr (A*C*Cᴴ)+(q^2+2*p*w)*tr (H*Cᴴ*C) := by
  simp only [gramRow, direction, fromBlocks_conjTranspose, conjTranspose_smul,
    star_trivial, hA.eq, hH.eq, conjTranspose_conjTranspose,
    fromBlocks_multiply, tr_blocks, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, tr_add, tr_smul]
  try simp only [← Matrix.mul_assoc]
  rw [tr_cycle C Cᴴ A, tr_cycle Cᴴ A C, tr_cycle Cᴴ C H, tr_cycle C H Cᴴ]
  ring


/-- The first positive Schur transform. -/
def transport (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks A (tau r • C) (tau r • Cᴴ) H

/-- The quadratic coefficient entering the Sylvester-free square identity. -/
def balancedQuadratic (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (H : Matrix n n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  (-3 : ℝ) • second r A C H + (3/2 : ℝ) • (first r A C H * first r A C H)

private theorem quadratic_blocks (r : ℝ) (hr : 0 < r) (A : Matrix m m ℂ)
    (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    balancedQuadratic r A C H = fromBlocks
      (A*A+qv r • (C*Cᴴ))
      (((pv r+tau r)/2) • (A*C)+((qw r+tau r)/2) • (C*H))
      (((pv r+tau r)/2) • (Cᴴ*A)+((qw r+tau r)/2) • (H*Cᴴ))
      (H*H+pw r • (Cᴴ*C)) := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  simp only [balancedQuadratic, first, second, fromBlocks_smul, fromBlocks_multiply,
    fromBlocks_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_add, smul_sub, smul_smul]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals try dsimp only [qv, pv, pw, qw, tau]
  all_goals field_simp [hd]
  all_goals try dsimp [den]
  all_goals ring_nf
  all_goals simp only [hs]
  all_goals ring

private theorem diagonal_moment (r : ℝ) (hr : 0 < r) (A : Matrix m m ℂ)
    (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    (gramDiag 1 (tau r))ᴴ * direction A C H * gramDiag 1 (tau r) +
      gap r • ((gramDiag (m := m) (n := n) 0 1)ᴴ * direction A C H * gramDiag 0 1) =
      transport r A C H := by
  have h := (scalar_gram r hr).1
  simp only [gramDiag, direction, transport, fromBlocks_conjTranspose,
    conjTranspose_smul, star_trivial, conjTranspose_one, conjTranspose_zero,
    fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    smul_zero, zero_smul, one_smul, smul_smul, fromBlocks_smul, fromBlocks_add]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals nlinarith [h]

private theorem cross_row (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (v p q w : ℝ) :
    (gramDiag v w)ᴴ * direction A C H * gramRow A C H v p q w +
      (gramRow A C H v p q w)ᴴ * direction A C H * gramDiag v w =
      fromBlocks
        ((2*v^2) • (A*A)+(2*v*q) • (C*Cᴴ))
        ((v*p+v*w) • (A*C)+(v*w+w*q) • (C*H))
        ((v*p+v*w) • (Cᴴ*A)+(v*w+w*q) • (H*Cᴴ))
        ((2*w^2) • (H*H)+(2*w*p) • (Cᴴ*C)) := by
  simp only [gramRow, gramDiag, direction, fromBlocks_conjTranspose,
    conjTranspose_smul, star_trivial, hA.eq, hH.eq, conjTranspose_conjTranspose,
    conjTranspose_one, conjTranspose_zero, fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    smul_smul, fromBlocks_add]
  apply fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

private theorem cross_moment (r : ℝ) (hr : 0 < r) (A : Matrix m m ℂ)
    (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ((gramDiag 1 (tau r))ᴴ * direction A C H * gramRow A C H 1 (pv r) (qv r) (tau r) +
      (gramRow A C H 1 (pv r) (qv r) (tau r))ᴴ * direction A C H * gramDiag 1 (tau r)) +
    gap r • ((gramDiag 0 1)ᴴ * direction A C H * gramRow A C H 0 (pc r) (qc r) 1 +
      (gramRow A C H 0 (pc r) (qc r) 1)ᴴ * direction A C H * gramDiag 0 1) =
    (2 : ℝ) • balancedQuadratic r A C H := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := scalar_gram r hr
  rw [cross_row A C H hA hH, cross_row A C H hA hH, quadratic_blocks r hr]
  simp only [fromBlocks_smul, fromBlocks_add, smul_add, smul_smul]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals nlinarith [h0,h1,h2]

/-- The finite weighted square. The last two rows have zero diagonal component. -/
def squareEnergy (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (W : Matrix (m ⊕ n) (m ⊕ n) ℂ) : ℝ :=
  let S := direction A C H
  let R0 := gramRow A C H 1 (pv r) (qv r) (tau r) - (2 : ℝ) • (gramDiag 1 (tau r)*W)
  let R1 := gramRow A C H 0 (pc r) (qc r) 1 - (2 : ℝ) • (gramDiag 0 1*W)
  let R2 := gramRow A C H 0 1 0 0
  let R3 := gramRow A C H 0 0 1 0
  tr (R0ᴴ*S*R0) + gap r*tr (R1ᴴ*S*R1) +
    gramGap r*tr (R2ᴴ*S*R2) + gramGap r*tr (R3ᴴ*S*R3)

private theorem square_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S V X W : Matrix ι ι ℂ) (hW : W.IsHermitian) :
    tr ((X-(2 : ℝ) • (V*W))ᴴ*S*(X-(2 : ℝ) • (V*W))) =
      tr (Xᴴ*S*X)-2*tr ((Vᴴ*S*X+Xᴴ*S*V)*W)+4*tr ((Vᴴ*S*V)*(W*W)) := by
  simp only [conjTranspose_sub, conjTranspose_smul, star_trivial, conjTranspose_mul,
    hW.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    tr_sub, tr_smul, Matrix.add_mul, tr_add]
  simp only [← Matrix.mul_assoc]
  rw [show tr (W*Vᴴ*S*X) = tr (Vᴴ*S*X*W) by
    simpa only [Matrix.mul_assoc] using tr_comm W (Vᴴ*S*X)]
  rw [show tr (W*Vᴴ*S*V*W) = tr (Vᴴ*S*V*W*W) by
    simpa only [Matrix.mul_assoc] using tr_comm W (Vᴴ*S*V*W)]
  ring


/-- The spectral cube root of the base, with eigenvalues 1,r. -/
def baseRoot (r : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ := gramDiag 1 r

/-- The explicit inverse spectral root. -/
def inverseRoot (r : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ := gramDiag 1 r⁻¹

/-- Inverse of E ↦ P²E+PEP+EP² for a two-level positive diagonal P. -/
def solveRoot (r : ℝ) (M : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks ((1/3 : ℝ) • M.toBlocks₁₁) ((den r)⁻¹ • M.toBlocks₁₂)
    ((den r)⁻¹ • M.toBlocks₂₁) ((3*r^2)⁻¹ • M.toBlocks₂₂)

/-- First cube-root coefficient, prior to squaring and balancing. -/
def rootFirst (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks ((1/3 : ℝ) • A) ((r*Real.sqrt r/den r) • C)
    ((r*Real.sqrt r/den r) • Cᴴ) ((r/3) • H)

/-- Second cube-root coefficient obtained from the cubic recurrence. -/
def rootSecond (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks
    ((-1/9 : ℝ) • (A*A) - ((r+2)*r^3/(3*(den r)^2)) • (C*Cᴴ))
    (-(r*Real.sqrt r/(3*(den r)^2)) • ((r+2) • (A*C)+(r*(1+2*r)) • (C*H)))
    (-(r*Real.sqrt r/(3*(den r)^2)) • ((r+2) • (Cᴴ*A)+(r*(1+2*r)) • (H*Cᴴ)))
    ((-r/9) • (H*H)-((1+2*r)*r/(3*(den r)^2)) • (Cᴴ*C))

/-- Third cube-root coefficient, defined by the ordered cubic recurrence. -/
def rootThird (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  let P := baseRoot (m := m) (n := n) r
  let R := rootFirst r A C H
  let Q := rootSecond r A C H
  solveRoot r (-(P*(R*Q+Q*R)+R*P*Q+Q*P*R+(R*Q+Q*R)*P+R*R*R))

/-- Third coefficient after squaring the cubic-root series and balancing by P⁻¹. -/
def third (r : ℝ) (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  let P := baseRoot (m := m) (n := n) r
  let D := inverseRoot (m := m) (n := n) r
  let R := rootFirst r A C H
  let Q := rootSecond r A C H
  let U := rootThird r A C H
  D*(P*U+U*P+R*Q+Q*R)*D

private theorem solve_root_identity (r : ℝ) (hr : 0 < r)
    (M : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    let P := baseRoot (m := m) (n := n) r
    P*P*solveRoot r M+P*solveRoot r M*P+solveRoot r M*P*P = M := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  dsimp only
  conv_rhs => rw [← M.fromBlocks_toBlocks]
  simp only [baseRoot, gramDiag, solveRoot, fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, smul_zero, one_smul, smul_smul, fromBlocks_add]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals field_simp [hd, ne_of_gt hr]
  all_goals try dsimp [den]
  all_goals ring

private theorem root_second_identity (r : ℝ) (hr : 0 < r)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    let P := baseRoot (m := m) (n := n) r
    let R := rootFirst r A C H
    let Q := rootSecond r A C H
    P*P*Q+P*Q*P+Q*P*P+P*R*R+R*P*R+R*R*P = 0 := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  dsimp only
  simp only [baseRoot, gramDiag, rootFirst, rootSecond, fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, smul_zero, one_smul, smul_smul, fromBlocks_add]
  rw [← fromBlocks_zero (n := m) (l := m) (m := n) (o := n)]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals field_simp [hd]
  all_goals try dsimp [den]
  all_goals ring_nf
  all_goals simp only [hs]
  all_goals ring


private theorem third_trace_normalization (r : ℝ) (hr : 0 < r)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    tr (third r A C H) = tr (first r A C H * second r A C H) -
      (1/3 : ℝ)*tr ((first r A C H)^3) + (2/9 : ℝ)*tr ((direction A C H)^3) := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  simp only [third, rootThird, rootFirst, rootSecond, inverseRoot, baseRoot, gramDiag,
    first, second, direction, solveRoot, pow_succ, pow_zero,
    fromBlocks_multiply, fromBlocks_neg, fromBlocks_add, fromBlocks_smul,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, smul_zero, one_smul, smul_smul,
    smul_add, smul_sub, smul_neg, tr_blocks, tr_add, tr_sub, tr_smul, tr_neg, tr_zero, sub_zero, zero_sub, neg_zero]
  simp only [← Matrix.mul_assoc]
  simp only [tr_cycle C Cᴴ A, tr_cycle Cᴴ A C, tr_cycle Cᴴ C H, tr_cycle C H Cᴴ]
  dsimp only [tau]
  field_simp [hd, ne_of_gt hr]
  dsimp only [den]
  ring_nf
  simp only [hs]
  ring


private theorem first_from_root (r : ℝ) (hr : 0 < r)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    let P := baseRoot (m := m) (n := n) r
    let D := inverseRoot (m := m) (n := n) r
    let R := rootFirst r A C H
    D*(P*R+R*P)*D = first r A C H := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  dsimp only
  simp only [baseRoot, inverseRoot, gramDiag, rootFirst, first, fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, smul_zero, one_smul, smul_smul, fromBlocks_add, fromBlocks_smul]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals try dsimp only [tau]
  all_goals field_simp [hd, ne_of_gt hr]
  all_goals try dsimp only [den]
  all_goals ring

private theorem second_from_root (r : ℝ) (hr : 0 < r)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ) :
    let P := baseRoot (m := m) (n := n) r
    let D := inverseRoot (m := m) (n := n) r
    let R := rootFirst r A C H
    let Q := rootSecond r A C H
    D*(P*Q+Q*P+R*R)*D = second r A C H := by
  have hd : den r ≠ 0 := ne_of_gt (by unfold den; positivity)
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  dsimp only
  simp only [baseRoot, inverseRoot, gramDiag, rootFirst, rootSecond, second,
    fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, smul_zero, one_smul, smul_smul, fromBlocks_add, smul_add, smul_sub]
  apply fromBlocks_inj.mpr
  repeat' constructor
  all_goals match_scalars
  all_goals field_simp [hd, ne_of_gt hr]
  all_goals try dsimp only [den]
  all_goals ring_nf
  all_goals simp only [hs]
  all_goals ring


end D5.S3.Quantum.Matrix.HsfBalancedSpectralCertificate
