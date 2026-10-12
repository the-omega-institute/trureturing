# Reset codebook: Order

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (gelfand).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.gelfand`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.gelfand` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Gelfand formula and the intermediate value theorem in mathlib*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d>.

*Commentary.*

The nth root of the norm of the nth power of a finite complex matrix tends to its spectral radius. This is the classical Gelfand formula, applied to the complexification of a real matrix.

**Theorem 1.2 (radius mono).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.radius_mono`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.radius_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite square real matrices A and B, entrywise nonnegativity of A and the entrywise inequality A <= B imply that the complex spectral radius of A is at most that of B. The matrices need not be symmetric or irreducible. Entrywise comparisons of all powers and their row norms are combined with the Gelfand formula.

**Theorem 1.3 (lambda linear).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.lambda_linear`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.lambda_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: lambda=(1-g)/20

**Theorem 1.4 (g tight).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.g_tight`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.g_tight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: 236067/1000000 < g ∧ g < 236068/1000000

**Theorem 1.5 (U scalar 0).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_0`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 0) x = ((-257/5 : ℝ) + (1096/5 : ℝ)*g) + (-g)^6*(x-c0)

**Theorem 1.6 (U scalar 1).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_1`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 1) x = ((-121/10 : ℝ) + (519/10 : ℝ)*g) + (-g)^5*(x-c0)

**Theorem 1.7 (U scalar 2).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_2`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 2) x = ((-7/2 : ℝ) + (121/10 : ℝ)*g) + (-g)^4*(x-c0)

**Theorem 1.8 (U scalar 3).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_3`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 3) x = ((-3/5 : ℝ) + (3 : ℝ)*g) + (-g)^3*(x-c0)

**Theorem 1.9 (U scalar 4).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_4`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 4) x = ((-3/5 : ℝ) + (3/5 : ℝ)*g) + (-g)^2*(x-c0)

**Theorem 1.10 (U scalar 5).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_5`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)

**Theorem 1.11 (V scalar 0).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_0`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 0) x = ((-342/5 : ℝ) + (1451/5 : ℝ)*g) + (-g)^6*(x-c0)

**Theorem 1.12 (V scalar 1).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_1`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 1) x = ((-83/5 : ℝ) + (342/5 : ℝ)*g) + (-g)^5*(x-c0)

**Theorem 1.13 (V scalar 2).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_2`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 2) x = ((-9/2 : ℝ) + (161/10 : ℝ)*g) + (-g)^4*(x-c0)

**Theorem 1.14 (V scalar 3).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_3`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 3) x = ((-3/5 : ℝ) + (4 : ℝ)*g) + (-g)^3*(x-c0)

**Theorem 1.15 (V scalar 4).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_4`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 4) x = ((-1/10 : ℝ) + (11/10 : ℝ)*g) + (-g)^2*(x-c0)

**Theorem 1.16 (V scalar 5).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_5`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)

**Theorem 1.17 (C scalar 0).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_0`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 0) x = ((1/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^20*(x-c0)

**Theorem 1.18 (C scalar 1).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_1`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 1) x = ((1/2 : ℝ) + (3/10 : ℝ)*g) + (-g)^19*(x-c0)

**Theorem 1.19 (C scalar 2).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_2`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 2) x = ((-4/5 : ℝ) + (0 : ℝ)*g) + (-g)^18*(x-c0)

**Theorem 1.20 (C scalar 3).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_3`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 3) x = ((7/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^17*(x-c0)

**Theorem 1.21 (C scalar 4).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_4`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 4) x = ((9/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^16*(x-c0)

**Theorem 1.22 (C scalar 5).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_5`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 5) x = ((1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^15*(x-c0)

**Theorem 1.23 (C scalar 6).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_6`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 6) x = ((-1/2 : ℝ) + (-1/10 : ℝ)*g) + (-g)^14*(x-c0)

**Theorem 1.24 (C scalar 7).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_7`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 7) x = ((-2/5 : ℝ) + (0 : ℝ)*g) + (-g)^13*(x-c0)

**Theorem 1.25 (C scalar 8).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_8`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 8) x = ((-9/10 : ℝ) + (-1/10 : ℝ)*g) + (-g)^12*(x-c0)

**Theorem 1.26 (C scalar 9).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_9`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 9) x = ((6/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^11*(x-c0)

**Theorem 1.27 (C scalar 10).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_10`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 10) x = ((3/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^10*(x-c0)

**Theorem 1.28 (C scalar 11).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_11`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 11) x = ((0 : ℝ) + (1/5 : ℝ)*g) + (-g)^9*(x-c0)

**Theorem 1.29 (C scalar 12).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_12`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 12) x = ((-1/5 : ℝ) + (0 : ℝ)*g) + (-g)^8*(x-c0)

**Theorem 1.30 (C scalar 13).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_13`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 13) x = ((4/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^7*(x-c0)

**Theorem 1.31 (C scalar 14).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_14`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_14` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 14) x = ((3/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^6*(x-c0)

**Theorem 1.32 (C scalar 15).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_15`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 15) x = ((7/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^5*(x-c0)

**Theorem 1.33 (C scalar 16).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_16`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 16) x = ((-1/2 : ℝ) + (1/10 : ℝ)*g) + (-g)^4*(x-c0)

**Theorem 1.34 (C scalar 17).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_17`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 17) x = ((-3/5 : ℝ) + (0 : ℝ)*g) + (-g)^3*(x-c0)

**Theorem 1.35 (C scalar 18).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_18`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 18) x = ((-1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^2*(x-c0)

**Theorem 1.36 (C scalar 19).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_19`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 19) x = ((3/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)

**Theorem 1.37 (U map).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_map`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.U_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) : wordScalar U (coord false D)=coord false (A false+rho*D)

**Theorem 1.38 (V map).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_map`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.V_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) : wordScalar V (coord true D)=coord true (A true+rho*D)

**Theorem 1.39 (C map).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_map`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.C_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (D : ℝ) : wordScalar C (coord low D)=coord low (chi*D)

**Theorem 1.40 (actual errors).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookOrder.actual_errors`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookOrder.actual_errors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : List Label) (r : List (Fin 6)) (x tail : LegalDigits) (hp : addressPrefix w x tail) (hlen : w.length=r.length) (b eps : ℝ) (heps : 0<eps) (hb : 0<b-eps) (hc : wordCost w r (kappa tail)≤b-2*eps) (Q : ℝ→Fin 6) (hQ : ∀ i y, y∈Set.Ioo (cellLower i) (cellUpper i) → Q y=i) : ∃ errors : List ℝ, errors.length=r.length ∧ ∀ p : Fin r.length, |(errors[p.val]?.getD 0)|<b-eps ∧ Q (min (1+t) (max (-1) (kappa (originalT^[p.val] x)+(errors[p.val]?.getD 0))))=r[p.val]

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_map`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_0`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_1`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_10`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_11`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_12`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_13`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_14`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_15`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_16`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_17`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_18`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_19`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_2`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_3`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_4`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_5`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_6`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_7`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_8`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.C_scalar_9`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_map`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_0`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_1`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_2`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_3`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_4`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.U_scalar_5`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_map`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_0`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_1`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_2`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_3`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_4`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.V_scalar_5`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.actual_errors`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.g_tight`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.gelfand`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.lambda_linear`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookOrder.radius_mono`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookModel](ResetCodebookModel.md)
