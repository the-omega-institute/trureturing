# FiniteSupportEndomorphismCalculus

## Abstract

FiniteSupportEndomorphismCalculus

Escape audit remains unfinished for the 39 public calculus and original-quartet targets: 37 compiled typed attempts are declared_unresolved (IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.selection_missing; certificate null), and kernel_number_iff and literal_relative_ground have only full-telescope source bridges. No target is declared_validated. Exact source selection and whole-statement reconstruction remain missing; the two source-bridge-only targets also lack complete whole-family variation, slot sensitivity, actual observational dependence and Contract registration. The current-target limitation is linked at https://github.com/the-omega-institute/trureturing/issues/25604 under CLAUDE section 3.9. This issue supplies neither mathematical proof nor validated registration.

This module supplies statewise finite endomorphism sums and algebraic functional calculus for an arbitrary genuine complex basis. Family includes a bound and a proved vanishing assertion. No support or spectral conclusion is assumed by the quartet application. Existing finitary Mathlib sums and basis constructors are reused; the missing composition capture and natural-count coefficient arguments are proved here. These are repository derivations, without a claim of literature novelty. The scalar field is Complex, with arbitrary algebraic modules and arbitrary basis index types.

**Theorem 1.1 (ac_add_left).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_left`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Anticommutators distribute over addition in the first operand; used in actual paired-mode calculations. Source telescope (with the module variables described above): (A B C : Module.End ℂ V) : ac (A + B) C = ac A C + ac B C

**Theorem 1.2 (ac_add_right).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Anticommutators distribute over addition in the second operand; used in actual paired-mode calculations. Source telescope (with the module variables described above): (A B C : Module.End ℂ V) : ac A (B + C) = ac A B + ac A C

**Theorem 1.3 (ac_smul_left).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_left`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex scalar factors out of the first anticommutator operand. Source telescope (with the module variables described above): (z : ℂ) (A B : Module.End ℂ V) : ac (z • A) B = z • ac A B

**Theorem 1.4 (ac_smul_right).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex scalar factors out of the second anticommutator operand. Source telescope (with the module variables described above): (z : ℂ) (A B : Module.End ℂ V) : ac A (z • B) = z • ac A B

**Theorem 1.5 (Family.total_eq_sum).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every statewise finite total equals a finite truncation at any proved bound for that state. Source telescope (with the module variables described above): (v : V) (N : ℕ) (hN : A.bound v ≤ N) : A.total v = ∑ n ∈ Finset.range N, A.term n v

**Theorem 1.6 (Family.total_ac).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A diagonal local anticommutator law for three statewise finite families implies the anticommutator law for their actual total operators. The proof captures both composed outputs before exchanging finite sums. Source telescope (with the module variables described above): (A B C : Family V) (hab : ∀ i j, ac (A.term i) (B.term j) = if i = j then C.term i else 0) : ac A.total B.total = C.total

**Theorem 1.7 (Family.total_square_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_square_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_square_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairwise anticommuting terms imply the square of their statewise finite total is zero. Source telescope (with the module variables described above): (A : Family V) (haa : ∀ i j, ac (A.term i) (A.term j) = 0) : A.total * A.total = 0

**Theorem 1.8 (Family.total_ac_fixed).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed operator anticommuting with every term anticommutes with the statewise finite total. Source telescope (with the module variables described above): (A : Family V) (T : Module.End ℂ V) (hT : ∀ i, ac T (A.term i) = 0) : ac T A.total = 0

**Theorem 1.9 (Family.total_commutes_fixed).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_commutes_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_commutes_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed operator commuting with every term commutes with the statewise finite total. Source telescope (with the module variables described above): (A : Family V) (T : Module.End ℂ V) (hT : ∀ i, T * A.term i = A.term i * T) : T * A.total = A.total * T

**Theorem 1.10 (signed_sum).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.signed_sum`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.signed_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finitely bounded signed integer sum, with its zero term separately proved zero, equals the paired positive and negative finite sum. Source telescope (with the module variables described above): (f : ℤ → V) (hf0 : f 0 = 0) (N : ℕ) (hN : ∀ r, N ≤ r → f ((r : ℤ)+1) = 0 ∧ f (-((r : ℤ)+1)) = 0) : (∑ᶠ n, f n) = ∑ r ∈ Finset.range N, (f ((r : ℤ)+1) + f (-((r : ℤ)+1)))

**Theorem 1.11 (diagonal_basis).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_basis`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis-defined diagonal endomorphism acts on each basis vector by its specified complex scalar. Source telescope (with the module variables described above): (f : I → ℂ) (i : I) : diagonal b f (b i) = f i • b i

**Theorem 1.12 (diagonal_coefficient).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of a diagonal action equals the specified eigenvalue times the original coefficient. Source telescope (with the module variables described above): (f : I → ℂ) (v : V) (i : I) : b.repr (diagonal b f v) i = f i * b.repr v i

**Theorem 1.13 (spectral_identities).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.spectral_identities`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.spectral_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural-valued basis count, the reciprocal with value zero at zero is a two-sided inverse off the full zero-count projection. The projection is idempotent and is annihilated by the number and inverse operators. Source telescope (with the module variables described above): (q : I → ℕ) : number b q * inverseNumber b q = 1 - projectZero b q ∧ inverseNumber b q * number b q = 1 - projectZero b q ∧ projectZero b q * projectZero b q = projectZero b q ∧ number b q * projectZero b q = 0 ∧ inverseNumber b q * projectZero b q = 0

**Theorem 1.14 (commutes_function).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.commutes_function`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.commutes_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutation with the actual natural-valued number endomorphism implies commutation with every complex function of that count; coefficientwise proof, with no diagonalization or functional-calculus certificate assumed. Source telescope (with the module variables described above): (q : I → ℕ) (A : Module.End ℂ V) (hA : number b q * A = A * number b q) (f : ℕ → ℂ) : diagonal b (fun i => f (q i)) * A = A * diagonal b (fun i => f (q i))

**Theorem 1.15 (kernel_number_iff).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.kernel_number_iff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.kernel_number_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel of a natural-valued basis number endomorphism consists exactly of vectors with zero coefficients at every positive-count basis index. Source telescope (with the module variables described above): (q : I → ℕ) (v : V) : number b q v = 0 ↔ ∀ i, q i ≠ 0 → b.repr v i = 0

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_add_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.ac_smul_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.commutes_function`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_basis`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.diagonal_coefficient`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.kernel_number_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.signed_sum`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.spectral_identities`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_ac_fixed`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_commutes_fixed`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_eq_sum`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus.total_square_zero`
