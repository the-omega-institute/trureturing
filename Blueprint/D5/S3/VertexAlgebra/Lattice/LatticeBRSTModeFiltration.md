# LatticeBRSTModeFiltration

## Abstract

LatticeBRSTModeFiltration

Original lattice matter tensor occupation bc Fock space; signed filtration degree equals plus occupation minus minus occupation plus ghost charge minus one. Every integral mode and charge is retained. Nonzero minus modes shift matter degree by minus one, including positive modes that differentiate plus variables; zero modes are scalar of degree zero. Actual all-state tensor support is derived from coefficients, finite basis expansion and original local finiteness. The accepted d0, R, invM and h preserve this degree, and the original ghost cubic has degree plus one. Momentum decomposes into its actual leading pPlus times aMinus and a strictly raising remainder for nonzero modes. For every original integral charge p, the raw operator a(eMinus,-1) squared tensor c(2) sends the actual basis input with zero matter exponents and ghost occupation {0} to the basis output with two minus oscillators at frequency 1 and empty ghost occupation, with coefficient 1. The signed degree drops by one. This follows by twice applying the original negative-current creation formula and the actual ghost annihilation formula; it is an anonymous compiled application, not an additional retained theorem. Consequently same-sign raw summands cannot be treated as individually raising: the actual two-sided inverse-Gram weighted cancellation is necessary before drawing the quadratic support conclusion. This is algebraic formalization on the repository carrier, without claims of physical completeness or literature novelty.

Full BRST matter-mode capture and assembly into Q minus d0, relative b0 and total-L0 zero-mode cancellation, preservation and bounds of the literal physical shell, full h delta strict raising, rank-26 nilpotence, HPL, cohomology, no-ghost, true Vnatural, strings and AdS/CFT remain unproved here. Original shell59141 is not imported or assumed. Native compilation proves only the exact Lean statements. Earlier provider audit limitations are linked at https://github.com/the-omega-institute/trureturing/issues/25604. That issue preserves all 39 original quartet obligations and names all 107 current retained filtration/Sugawara targets with exact canonical statement, source, type and binding identities: 146 unique unfinished audits, zero declared_validated. All seven original-family/source-selection, reconstruction, realization, whole-family variation, role/anchor sensitivity and observational-dependence evidence gaps remain unresolved. New registrations carry whole-theorem bridges but assertion-valued diagnostic attempts lack faithful operand selection and reconstruction. No declared_validated status, escape certificate or admission is claimed; actual unclassified diagnostics are collected in the scoped report for root review.

**Theorem 1.1 (weight_plus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (t r : ℕ) : variableWeight (plus t,r) = 1

**Theorem 1.2 (weight_minus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_minus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (t r : ℕ) : variableWeight (minus t,r) = -1

**Theorem 1.3 (weight_transverse).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_transverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_transverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (j : Fin t) (r : ℕ) : variableWeight (transverse t j,r) = 0

**Theorem 1.4 (exponentDegree_add).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (m n : Exponents t) : exponentDegree (m+n) = exponentDegree m + exponentDegree n

**Theorem 1.5 (exponentDegree_single).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (k : ℕ) : exponentDegree (Finsupp.single x k) = (k : ℤ) * variableWeight x

**Theorem 1.6 (X_mul_monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.X_mul_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.X_mul_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m : Exponents t) (z : ℂ) : X x * monomial m z = monomial (Finsupp.single x 1 + m) z

**Theorem 1.7 (single_add_sub).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.single_add_sub`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.single_add_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m : Exponents t) (hx : m x ≠ 0) : Finsupp.single x 1 + (m-Finsupp.single x 1) = m

**Theorem 1.8 (derivative_monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m : Exponents t) : pderiv x (monomial m (1 : ℂ)) = (m x : ℂ) • monomial (m-Finsupp.single x 1) 1

**Theorem 1.9 (multiply_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m n : Exponents t) : (X x * monomial m (1 : ℂ)).coeff n = if Finsupp.single x 1 + m = n then 1 else 0

**Theorem 1.10 (derivative_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m n : Exponents t) : (pderiv x (monomial m (1 : ℂ))).coeff n = if m-Finsupp.single x 1 = n then (m x : ℂ) else 0

**Theorem 1.11 (multiply_support_degree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_support_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_support_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m n : Exponents t) (h : (X x * monomial m (1 : ℂ)).coeff n ≠ 0) : exponentDegree n = exponentDegree m + variableWeight x

**Theorem 1.12 (derivative_support_degree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_support_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_support_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) (m n : Exponents t) (h : (pderiv x (monomial m (1 : ℂ))).coeff n ≠ 0) : exponentDegree n = exponentDegree m - variableWeight x

**Theorem 1.13 (create_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (j : ℕ) (S T : Finset ℕ) : (create j (ket S)) T = if j ∈ S then 0 else if insert j S = T then phase j S else 0

**Theorem 1.14 (annihilate_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (j : ℕ) (S T : Finset ℕ) : (annihilate j (ket S)) T = if j ∈ S then (if S.erase j = T then phase j S else 0) else 0

**Theorem 1.15 (create_support_charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_support_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_support_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (j : ℕ) (S T : Finset ℕ) (h : (create j (ket S)) T ≠ 0) : charge T=charge S+siteSign j

**Theorem 1.16 (annihilate_support_charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_support_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_support_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (j : ℕ) (S T : Finset ℕ) (h : (annihilate j (ket S)) T ≠ 0) : charge T=charge S-siteSign j

**Theorem 1.17 (b_support_charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_support_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_support_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (S T : Finset ℕ) (h : (b n (ket S)) T ≠ 0) : charge T=charge S-1

**Theorem 1.18 (c_support_charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_support_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_support_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (S T : Finset ℕ) (h : (c n (ket S)) T ≠ 0) : charge T=charge S+1

**Theorem 1.19 (basis_expand).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.basis_expand`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.basis_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (v : V) : (∑ i ∈ (bas.repr v).support, bas.repr v i • bas i)=v

**Theorem 1.20 (shift_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (k : ℤ) : Shift bas w 0 k

**Theorem 1.21 (shift_one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): : Shift bas w (1 : Module.End ℂ V) 0

**Theorem 1.22 (shift_smul).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A : Module.End ℂ V} {k : ℤ} (z : ℂ) (hA : Shift bas w A k) : Shift bas w (z • A) k

**Theorem 1.23 (shift_add).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A C : Module.End ℂ V} {k : ℤ} (hA : Shift bas w A k) (hC : Shift bas w C k) : Shift bas w (A+C) k

**Theorem 1.24 (shift_mul).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A C : Module.End ℂ V} {a c : ℤ} (hA : Shift bas w A a) (hC : Shift bas w C c) : Shift bas w (A*C) (a+c)

**Theorem 1.25 (shift_sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {J : Type*} (s : Finset J) (A : J → Module.End ℂ V) (k : ℤ) (hA : ∀ j ∈ s, Shift bas w (A j) k) : Shift bas w (∑ j ∈ s, A j) k

**Theorem 1.26 (strictRaises_of_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_of_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_of_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A : Module.End ℂ V} {k : ℤ} (hA : Shift bas w A k) (hk : 1≤k) : StrictRaises bas w A

**Theorem 1.27 (strictRaises_smul).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A : Module.End ℂ V} (z : ℂ) (hA : StrictRaises bas w A) : StrictRaises bas w (z • A)

**Theorem 1.28 (strictRaises_add).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {A C : Module.End ℂ V} (hA : StrictRaises bas w A) (hC : StrictRaises bas w C) : StrictRaises bas w (A+C)

**Theorem 1.29 (shift_diagonal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (f : I → ℂ) : Shift bas w (FiniteSupportEndomorphismCalculus.diagonal bas f) 0

**Theorem 1.30 (multiply_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) : Shift (polynomialBasis t) exponentDegree (LinearMap.mulLeft ℂ (X x)) (variableWeight x)

**Theorem 1.31 (derivative_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {t : ℕ} (x : Variables t) : Shift (polynomialBasis t) exponentDegree (pderiv x).toLinearMap (-variableWeight x)

**Theorem 1.32 (b_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) : Shift occupationBasis charge (b n) (-1)

**Theorem 1.33 (c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) : Shift occupationBasis charge (c n) 1

**Theorem 1.34 (cubic_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubic_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubic_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p q : ℤ) : Shift occupationBasis charge (D5.S3.Quantum.Fermionic.BcGhostBRST.cubic p q) 1

**Theorem 1.35 (cubicTerm_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubicTerm_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubicTerm_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (pq : ℤ × ℤ) : Shift occupationBasis charge (D5.S3.Quantum.Fermionic.BcGhostBRST.cubicTerm pq) 1

**Theorem 1.36 (Qg_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.Qg_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.Qg_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): : Shift occupationBasis charge D5.S3.Quantum.Fermionic.BcGhostBRST.Qg 1

**Theorem 1.37 (cm_plus_negative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) : cm F B F.ePlus p (-(r : ℤ)-1) Q=X (plus t,r)*Q

**Theorem 1.38 (cm_minus_negative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) : cm F B F.eMinus p (-(r : ℤ)-1) Q=X (minus t,r)*Q

**Theorem 1.39 (cm_plus_positive).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) : cm F B F.ePlus p ((r : ℤ)+1) Q=(r+1 : ℂ) • pderiv (minus t,r) Q

**Theorem 1.40 (cm_minus_positive).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) : cm F B F.eMinus p ((r : ℤ)+1) Q=(r+1 : ℂ) • pderiv (plus t,r) Q

**Theorem 1.41 (cm_plus_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (n : ℤ) (hn : n≠0) : Shift (polynomialBasis t) exponentDegree (cm F B F.ePlus p n) 1

**Theorem 1.42 (cm_minus_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (n : ℤ) (hn : n≠0) : Shift (polynomialBasis t) exponentDegree (cm F B F.eMinus p n) (-1)

**Theorem 1.43 (cm_zero_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_zero_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_zero_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u : E D) (p : Charge D) : Shift (polynomialBasis t) exponentDegree (cm F B u p 0) 0

**Theorem 1.44 (cm_transverse_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_transverse_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_transverse_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u : F.K) (p : Charge D) (n : ℤ) : Shift (polynomialBasis t) exponentDegree (cm F B (u : E D) p n) 0

**Theorem 1.45 (sector_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.sector_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.sector_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (Q : PolynomialCoordinates (Label t)) (w : Fock) (i : StateIndex D t) : (actualBasis F B).repr (sector F B p Q w) i = if p=i.1.1 then Q.coeff i.1.2 * w i.2 else 0

**Theorem 1.46 (tensor_current_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_current_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_current_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u : E D) (n : ℤ) (G : Module.End ℂ Fock) (a c : ℤ) (ha : ∀ p : Charge D, Shift (polynomialBasis t) exponentDegree (cm F B u p n) a) (hc : Shift occupationBasis charge G c) : Shift (actualBasis F B) degree (tp (D := D) (LatticeLightConeCoordinates.a u n) G) (a+c)

**Theorem 1.47 (original_plus_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n k : ℤ) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.ePlus n) (c k)) 2

**Theorem 1.48 (original_minus_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n k : ℤ) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.eMinus n) (c k)) 0

**Theorem 1.49 (original_plus_b_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_b_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_b_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n k : ℤ) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.ePlus n) (b k)) 0

**Theorem 1.50 (original_transverse_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u : F.K) (n k : ℤ) : Shift (actualBasis F B) degree (tp (a (u : E D) n) (c k)) 1

**Theorem 1.51 (original_plus_matter_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_matter_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_matter_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.ePlus n) 1) 1

**Theorem 1.52 (original_minus_matter_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_matter_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_matter_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.eMinus n) 1) (-1)

**Theorem 1.53 (original_transverse_matter_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_matter_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_matter_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u : F.K) (n : ℤ) : Shift (actualBasis F B) degree (tp (a (u : E D) n) 1) 0

**Theorem 1.54 (tensor_ghost_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_ghost_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_ghost_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (G : Module.End ℂ Fock) (k : ℤ) (hG : Shift occupationBasis charge G k) : Shift (actualBasis F B) degree (tp (1 : Module.End ℂ (Carrier D)) G) k

**Theorem 1.55 (original_ghost_cubic_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_ghost_cubic_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_ghost_cubic_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): : Shift (actualBasis F B) degree (tp (1 : Module.End ℂ (Carrier D)) D5.S3.Quantum.Fermionic.BcGhostBRST.Qg) 1

**Theorem 1.56 (original_cross_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_cross_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_cross_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (m n k : ℤ) (hm : m≠0) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.ePlus m * a F.eMinus n) (c k)) 1

**Theorem 1.57 (original_reverse_cross_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_reverse_cross_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_reverse_cross_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (m n k : ℤ) (hm : m≠0) (hn : n≠0) : Shift (actualBasis F B) degree (tp (a F.eMinus m * a F.ePlus n) (c k)) 1

**Theorem 1.58 (original_transverse_pair_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_pair_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_pair_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u v : F.K) (m n k : ℤ) : Shift (actualBasis F B) degree (tp (a (u : E D) m * a (v : E D) n) (c k)) 1

**Theorem 1.59 (family_total_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.family_total_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.family_total_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {V I : Type*} [AddCommGroup V] [Module ℂ V] (bas : Module.Basis I ℂ V) (w : I → ℤ) (A : FiniteSupportEndomorphismCalculus.Family V) (k : ℤ) (hA : ∀ r, Shift bas w (A.term r) k) : Shift bas w A.total k

**Theorem 1.60 (dTerm_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.dTerm_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.dTerm_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (r : ℕ) : Shift (actualBasis F B) degree (dTerm F r) 0

**Theorem 1.61 (rTerm_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.rTerm_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.rTerm_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (r : ℕ) : Shift (actualBasis F B) degree (rTerm F r) 0

**Theorem 1.62 (d0_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.d0_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.d0_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) : Shift (actualBasis F B) degree (d0 F p) 0

**Theorem 1.63 (R_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.R_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.R_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) : Shift (actualBasis F B) degree (R F p) 0

**Theorem 1.64 (invM_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.invM_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.invM_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): : Shift (actualBasis F B) degree (invM F B) 0

**Theorem 1.65 (h_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.h_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.h_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) : Shift (actualBasis F B) degree (h F B p) 0

**Theorem 1.66 (a_add_vectors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_add_vectors`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_add_vectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (u v : E D) (n : ℤ) : a (u+v) n=a u n+a v n

**Theorem 1.67 (a_smul_vector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_smul_vector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_smul_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (z : ℂ) (u : E D) (n : ℤ) : a (z • u) n=z • a u n

**Theorem 1.68 (inverse_covector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverse_covector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverse_covector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) (v : E D) (i : Fin D.rank) : (∑ j, H i j * g D v (standardBasis D j))=v i

**Theorem 1.69 (inverseGramPair_eq).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGramPair_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGramPair_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) (u v : E D) : inverseGramPair H u v=g D u v

**Theorem 1.70 (inverseGram_longitudinal_coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) : inverseGramPair H F.ePlus F.ePlus=0 ∧ inverseGramPair H F.eMinus F.eMinus=0 ∧ inverseGramPair H F.ePlus F.eMinus=1 ∧ inverseGramPair H F.eMinus F.ePlus=1

**Theorem 1.71 (momentum_current_decomposition).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentum_current_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentum_current_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (n : ℤ) : a (chargeVector p) n = F.pMinus p • a F.ePlus n + F.pPlus p • a F.eMinus n + a (F.projK (chargeVector p) : E D) n

**Theorem 1.72 (momentumRemainder_formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (n : ℤ) : momentumRemainder F p n = F.pMinus p • tp (a F.ePlus n) (c (-n)) + tp (a (F.projK (chargeVector p) : E D) n) (c (-n))

**Theorem 1.73 (momentumRemainder_strictRaises).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_strictRaises`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_strictRaises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) (n : ℤ) (hn : n≠0) : StrictRaises (actualBasis F B) degree (momentumRemainder F p n)

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.Qg_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.R_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.X_mul_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_add_vectors`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.a_smul_vector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.annihilate_support_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.b_support_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.basis_expand`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.c_support_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_positive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_minus_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_positive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_plus_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_transverse_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cm_zero_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.create_support_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubicTerm_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.cubic_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.d0_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.dTerm_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.derivative_support_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_add`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.exponentDegree_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.family_total_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.h_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.invM_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGramPair_eq`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.inverse_covector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_formula`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentumRemainder_strictRaises`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.momentum_current_decomposition`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.multiply_support_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_cross_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_ghost_cubic_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_minus_matter_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_b_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_plus_matter_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_reverse_cross_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_matter_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.original_transverse_pair_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.rTerm_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.sector_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_add`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_mul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_smul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.shift_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.single_add_sub`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_add`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_of_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.strictRaises_smul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_current_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.tensor_ghost_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_minus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_plus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration.weight_transverse`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](../../Quantum/Fermionic/BcGhostCharge.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCubic](../../Quantum/Fermionic/BcGhostCubic.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](LatticeQuartetContraction.md)
