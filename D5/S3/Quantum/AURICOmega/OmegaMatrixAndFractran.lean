/- GID: D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaMatrixAndFractran
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer matrix identities, Hurwitz splitting and exact fraction-program semantics. -/

module
prelude
public import OmegaMath.Matrix.Mat2
public import OmegaMath.Matrix.Mat2.Hurwitz
public import OmegaMath.Computability.Fractran

namespace D5.S3.Quantum.AURICOmega.OmegaMatrixAndFractran

open Omega

/-- Cyclicity of the trace for arbitrary integer matrices of size two. -/
public theorem trace_mul_comm (A B : Mat2) : Eq (A.mul B).trace (B.mul A).trace :=
  Mat2.trace_mul_comm A B

/-- Multiplication by the adjugate on either side gives the determinant times the identity. -/
public theorem adjugate_identities (A : Mat2) :
    And (Eq (A.mul A.adj) (Mat2.scale A.det Mat2.one))
      (Eq (A.adj.mul A) (Mat2.scale A.det Mat2.one)) :=
  And.intro (Mat2.mul_adj A) (Mat2.adj_mul A)

/-- The quadratic characteristic polynomial vanishes at every integer matrix of size two. -/
public theorem cayley_hamilton (A : Mat2) :
    Eq (((A.mul A).sub (Mat2.scale A.trace A)).add (Mat2.scale A.det Mat2.one)) Mat2.zero :=
  Mat2.cayley_hamilton A

/-- The twelve representatives have squared norm four in doubled coordinates. -/
public theorem hurwitz_core_unit (u : Hurwitz.Core) :
    Eq u.doubled.normSq (Int.two.mul Int.two) :=
  Hurwitz.core_unit u

/-- Each of the six split generator images is a nonzero outer product modulo five. -/
public theorem mod_five_rank_one (g : Hurwitz.Generator) :
    let f := g.factors
    And (Eq (Hurwitz.split5 g.coordinates) (Hurwitz.Matrix5.outer f.u f.v f.s f.t))
      (Eq (Hurwitz.split5 g.coordinates).isZero Bool.false) :=
  Hurwitz.split_rank_one g

/-- Zero products are exactly the ordered pairs of opposite generators. -/
public theorem mod_five_product_zero (g h : Hurwitz.Generator) :
    Eq ((Hurwitz.split5 g.coordinates).mul (Hurwitz.split5 h.coordinates)).isZero
      (g.isOpposite h) :=
  Hurwitz.split_product_zero g h

/-- The first enabled denominator determines exactly the same transition as the evaluator. -/
public theorem fractran_step_iff (prog : Fractran.Program) (n m : Nat) :
    Iff (Eq (Fractran.step prog n) (.some m)) (Fractran.Step prog n m) :=
  Fractran.step_iff prog n m

/-- Two valid transitions from one input have equal outputs. -/
public theorem fractran_deterministic (prog : Fractran.Program) (n m₁ m₂ : Nat)
    (h₁ : Fractran.Step prog n m₁) (h₂ : Fractran.Step prog n m₂) : Eq m₁ m₂ :=
  h₁.deterministic h₂

/-- Every state reached from a positive input remains positive. -/
public theorem fractran_positive (prog : Fractran.Program) (k n : Nat) (h : Nat.lt Nat.zero n) :
    Nat.lt Nat.zero (Fractran.run prog k n) :=
  Fractran.run_positive prog k n h

/-- All further iterations preserve the state once no rule is enabled. -/
public theorem fractran_stable (prog : Fractran.Program) (k n : Nat)
    (h : Fractran.Halts prog (Fractran.run prog k n)) (extra : Nat) :
    Eq (Fractran.run prog (k.add extra) n) (Fractran.run prog k n) :=
  Fractran.run_stable prog k n h extra

end D5.S3.Quantum.AURICOmega.OmegaMatrixAndFractran
