# Arbitrary-index algebraic Weyl, Taylor and Fock reconstruction

## Abstract

AlgebraicHeisenbergFock

K is an arbitrary characteristic-zero field, M an arbitrary K-module with AddCommGroup, and sigma an arbitrary type, including infinite or empty types. WeylData supplies only its displayed commuting X, commuting D, DX, pointwise nilpotence and pointwise finite activity premises. No basis of M is assumed. The joint vacuum is the intersection of all D kernels. The polynomial-factor monomial basis is used only to convert finite coefficients to a tensor product. The later PositiveCurrents consumer separately assumes finite (possibly empty) iota, full integer-mode CurrentData and LowerBounded A, including its finite homogeneous decomposition and positive-mode grade shift; its Fock conclusions retain that L and the specified inverse-Gram orientations. Empty sigma, empty iota and zero M are allowed; no Nonempty index, nonzero vacuum, positivity of the finite Gram matrix or finite-dimensional grade premise is added. The empty Gram determinant is one.

The derived finite jointCutoff box controls the entire mixed-derivative orbit. Taylor coefficient recursion gives exact left and right boundary terms, hence independence of each valid nilpotence cutoff. Coordinate projectors then commute, and independence of a finite index superset yields the canonical linear vacuum projector. A separate finite-active-set/nilpotence induction proves generation from the vacuum. Factorial coefficient extraction separates every creation monomial, giving coefficients_evaluate; independent generation yields evaluate_coefficients. The polynomial monomial-basis tensor equivalence transports these TWO inverse laws to fockMap/fockInverse and fockEquiv. taylor_reconstruction extends the coefficient sum to the derived box. The PositiveCurrents consumer derives BOTH pointwise nilpotence and finite activity from its independent integer LowerBounded interface before invoking this proof.

Each source signature below is interpreted in its displayed original Lean variable scope; scope commands introduce names and do not add unused parameters. Definitions and records display their actual constructions and fields. All original hypotheses and inferred parameters remain in the mathematical source. The general Weyl reconstruction and the lower-bounded PositiveCurrents application have separate hypotheses. This root alone does not classify arbitrary weak modules.

Original universe/open directives (names are resolved in the original source module and the namespace shown for each entry):

open scoped BigOperators TensorProduct Classical

universe u v w

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted structure:

structure WeylData (K : Type u) (σ : Type v) (M : Type w)

    [Field K] [CharZero K] [AddCommGroup M] [Module K M] where

  X : σ → Module.End K M

  D : σ → Module.End K M

  xx : ∀ i j, Commute (X i) (X j)

  dd : ∀ i j, Commute (D i) (D j)

  dx : ∀ i j v, D i (X j v) = X j (D i v) + if i = j then v else 0

  nilpotent : ∀ i v, ∃ n : ℕ, (D i ^ n) v = 0

  active_finite : ∀ v, {i | D i v ≠ 0}.Finite

Construction and use: The record assumes commuting creators, commuting derivatives, the displayed pointwise DX law, pointwise local nilpotence and pointwise finite active indices. It assumes no representation basis or reconstruction.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.vacuum

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def vacuum : Submodule K M := ⨅ i, LinearMap.ker (W.D i)

Construction and use: Intersect every derivative kernel; an empty intersection is allowed.

**Theorem 1.1 (mem_vacuum).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem mem_vacuum (v : M) : v ∈ W.vacuum ↔ ∀ i, W.D i v = 0

Proof mechanism: Unfold the intersection and linear kernels.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.active

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def active (v : M) : Finset σ := (W.active_finite v).toFinset

Construction and use: Convert the assumed pointwise finite nonzero-derivative set to a finset.

**Theorem 1.2 (mem_active).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_active`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem mem_active (i : σ) (v : M) :

    i ∈ W.active v ↔ W.D i v ≠ 0

Proof mechanism: Unfold that finite-set conversion.

**Theorem 1.3 (active_add_subset).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_add_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_add_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem active_add_subset (v z : M) :

    W.active (v + z) ⊆ W.active v ∪ W.active z

Proof mechanism: If both derivatives vanish, linearity forces the derivative of the sum to vanish.

**Theorem 1.4 (active_smul_subset).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_smul_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_smul_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem active_smul_subset (c : K) (v : M) : W.active (c • v) ⊆ W.active v

Proof mechanism: Linearity preserves vanishing after scalar multiplication.

**Theorem 1.5 (commute_apply).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem commute_apply (A B : Module.End K M) (h : Commute A B) (v : M) :

    A (B v) = B (A v)

Proof mechanism: Evaluate equality of composed endomorphisms at the vector.

**Theorem 1.6 (dx_of_ne).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.dx_of_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.dx_of_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem dx_of_ne {i j : σ} (h : i ≠ j) : Commute (W.D i) (W.X j)

Proof mechanism: Evaluate the Weyl relation off the diagonal, where its delta term vanishes.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.cutoff

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def cutoff (i : σ) (v : M) : ℕ := Nat.find (W.nilpotent i v)

Construction and use: Choose the least pointwise nilpotence exponent with Nat.find.

**Theorem 1.7 (cutoff_spec).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem cutoff_spec (i : σ) (v : M) : (W.D i ^ W.cutoff i v) v = 0

Proof mechanism: Use Nat.find_spec for the given nilpotence witness.

**Theorem 1.8 (cutoff_succ_spec).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_succ_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_succ_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem cutoff_succ_spec (i : σ) (v : M) :

    (W.D i ^ (W.cutoff i v + 1)) v = 0

Proof mechanism: Propagate vanishing to the successor power.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.jointCutoff

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def jointCutoff (v : M) : σ →₀ ℕ :=

  Finsupp.onFinset (W.active v)

    (fun i => if i ∈ W.active v then W.cutoff i v else 0)

    (by intro i hi; by_contra hn; exact hi (by simp [hn]))

Construction and use: Place the coordinate cutoffs on the finite active set and zero elsewhere.

**Theorem 1.9 (jointCutoff_spec).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem jointCutoff_spec (v : M) (i : σ) :

    (W.D i ^ (W.jointCutoff v i + 1)) v = 0

Proof mechanism: Use the coordinate cutoff on active indices and immediate derivative vanishing elsewhere.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.monomialOperator

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def monomialOperator (A : σ → Module.End K M)

    (hA : ∀ i j, Commute (A i) (A j)) (d : σ →₀ ℕ) : Module.End K M :=

  d.support.noncommProd (fun i => A i ^ d i)

    (fun i _ j _ _ => (hA i j).pow_pow _ _)

Construction and use: Take a commuting noncommProd over the finite exponent support.

**Theorem 1.10 (monomialOperator_on).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_on`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem monomialOperator_on (A : σ → Module.End K M)

    (hA : ∀ i j, Commute (A i) (A j)) (d : σ →₀ ℕ)

    (s : Finset σ) (hd : d.support ⊆ s) :

    monomialOperator A hA d =

      s.noncommProd (fun i => A i ^ d i)

        (fun i _ j _ _ => (hA i j).pow_pow _ _)

Proof mechanism: Split off the extra finite indices; their zero exponents contribute identity factors.

**Theorem 1.11 (monomialOperator_add_single).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_add_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem monomialOperator_add_single (A : σ → Module.End K M)

    (hA : ∀ i j, Commute (A i) (A j)) (d : σ →₀ ℕ) (i : σ) :

    monomialOperator A hA (d + Finsupp.single i 1) = A i * monomialOperator A hA d

Proof mechanism: Use a common support, isolate the selected coordinate and apply the successor-power formula.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.derivative

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted abbrev:

abbrev derivative (d : σ →₀ ℕ) : Module.End K M :=

  monomialOperator W.D W.dd d

Construction and use: Use the finite monomial operator for the commuting derivatives.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.creation

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted abbrev:

abbrev creation (d : σ →₀ ℕ) : Module.End K M :=

  monomialOperator W.X W.xx d

Construction and use: Use the finite monomial operator for the commuting creators.

**Theorem 1.12 (derivative_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem derivative_zero : W.derivative 0 = 1

Proof mechanism: The empty finite product is the identity.

**Theorem 1.13 (creation_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem creation_zero : W.creation 0 = 1

Proof mechanism: The empty finite product is the identity.

**Theorem 1.14 (creation_add_single).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_add_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem creation_add_single (d : σ →₀ ℕ) (i : σ) :

    W.creation (d + Finsupp.single i 1) = W.X i * W.creation d

Proof mechanism: Apply monomialOperator_add_single to the creators.

**Theorem 1.15 (derivative_commute).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_commute (d : σ →₀ ℕ) (i : σ) :

    Commute (W.D i) (W.derivative d)

Proof mechanism: Commute the selected derivative through every derivative-power factor.

**Theorem 1.16 (derivative_eq_zero_of_excess).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_excess`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_eq_zero_of_excess (v : M) (b d : σ →₀ ℕ)

    (hb : ∀ i, (W.D i ^ (b i + 1)) v = 0)

    (i : σ) (hi : b i < d i) : W.derivative d v = 0

Proof mechanism: Move the excessive coordinate power next to the input and use propagation of its nilpotence bound.

**Theorem 1.17 (derivative_eq_zero_of_not_le).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_not_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_not_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_eq_zero_of_not_le (v : M) (b d : σ →₀ ℕ)

    (hb : ∀ i, (W.D i ^ (b i + 1)) v = 0) (hd : ¬ d ≤ b) :

    W.derivative d v = 0

Proof mechanism: Extract an excessive coordinate from failure of the pointwise multiindex inequality.

**Theorem 1.18 (derivative_support_subset).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_support_subset (v : M) :

    Function.support (fun d : σ →₀ ℕ => W.derivative d v) ⊆

      (Finset.Iic (W.jointCutoff v) : Set (σ →₀ ℕ))

Proof mechanism: A multiindex outside the derived box has an excessive coordinate and hence zero derivative.

**Theorem 1.19 (derivative_support_finite).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_support_finite (v : M) :

    Function.HasFiniteSupport (fun d : σ →₀ ℕ => W.derivative d v)

Proof mechanism: The Finsupp interval below jointCutoff is finite and contains the derivative support.

**Theorem 1.20 (jointCutoff_orbit).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem jointCutoff_orbit (v : M) (d : σ →₀ ℕ) (i : σ) :

    (W.D i ^ (W.jointCutoff v i + 1)) (W.derivative d v) = 0

Proof mechanism: Commute the bounded coordinate power through an arbitrary mixed derivative and use the original cutoff.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor.coefficient

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted def:

def coefficient (K : Type u) [Field K] (n : ℕ) : K :=

  (-1 : K) ^ n / (n.factorial : K)

Construction and use: Define the signed reciprocal factorial coefficient, with its explicit scalar-field argument.

**Theorem 1.21 (coefficient_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

@[simp] theorem coefficient_zero : coefficient K 0 = 1

Proof mechanism: Simplify the zero power and zero factorial.

**Theorem 1.22 (factorial_ne_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem factorial_ne_zero (n : ℕ) : (n.factorial : K) ≠ 0

Proof mechanism: Cast the positive natural factorial into the characteristic-zero field.

**Theorem 1.23 (coefficient_succ).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem coefficient_succ (n : ℕ) :

    coefficient K (n + 1) * (n + 1 : K) = -coefficient K n

Proof mechanism: Expand factorial_succ, clear the nonzero factorial and successor denominators, and use the scalar ring identity.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor.finite

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted def:

def finite (X D : Module.End K M) (N : ℕ) : Module.End K M :=

  ∑ k ∈ Finset.range (N + 1), coefficient K k • (X ^ k * D ^ k)

Construction and use: Sum the normal-ordered powers X^k D^k with signed reciprocal factorials through the inclusive cutoff.

**Theorem 1.24 (finite_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

@[simp] theorem finite_zero (X D : Module.End K M) : finite X D 0 = 1

Proof mechanism: Only the identity term remains.

**Theorem 1.25 (finite_succ).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem finite_succ (X D : Module.End K M) (N : ℕ) :

    finite X D (N + 1) = finite X D N +

      coefficient K (N + 1) • (X ^ (N + 1) * D ^ (N + 1))

Proof mechanism: Split the final summand of the finite range.

**Theorem 1.26 (D_X_pow).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem D_X_pow (X D : Module.End K M)

    (h : ∀ v, D (X v) = X (D v) + v) (n : ℕ) (v : M) :

    D ((X ^ (n + 1)) v) =

      (X ^ (n + 1)) (D v) + (n + 1 : K) • (X ^ n) v

Proof mechanism: Induct on the creator power using the one-coordinate Weyl law and linearity.

**Theorem 1.27 (D_pow_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem D_pow_X (X D : Module.End K M)

    (h : ∀ v, D (X v) = X (D v) + v) (n : ℕ) (v : M) :

    (D ^ (n + 1)) (X v) =

      X ((D ^ (n + 1)) v) + (n + 1 : K) • (D ^ n) v

Proof mechanism: Induct on the derivative power using the same Weyl law and linearity.

**Theorem 1.28 (D_finite).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem D_finite (X D : Module.End K M)

    (h : ∀ v, D (X v) = X (D v) + v) (N : ℕ) (v : M) :

    D (finite X D N v) =

      coefficient K N • (X ^ N) ((D ^ (N + 1)) v)

Proof mechanism: Induct on the cutoff; D_X_pow and coefficient_succ cancel successive terms, leaving the displayed boundary term.

**Theorem 1.29 (finite_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem finite_X (X D : Module.End K M)

    (h : ∀ v, D (X v) = X (D v) + v) (N : ℕ) (v : M) :

    finite X D N (X v) =

      coefficient K N • (X ^ (N + 1)) ((D ^ N) v)

Proof mechanism: Induct on the cutoff; D_pow_X and coefficient_succ leave precisely the displayed right boundary term.

**Theorem 1.30 (finite_eq_self).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_eq_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_eq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem finite_eq_self (X D : Module.End K M) (N : ℕ) (v : M)

    (hv : D v = 0) : finite X D N v = v

Proof mechanism: Every positive derivative power kills a vector in the derivative kernel, leaving the identity summand.

**Theorem 1.31 (finite_stable).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_stable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem finite_stable (X D : Module.End K M) (v : M) (N L : ℕ)

    (hN : (D ^ (N + 1)) v = 0) (hNL : N ≤ L) :

    finite X D L v = finite X D N v

Proof mechanism: Induct on the difference of valid cutoffs; each added term has a derivative power that already vanishes.

**Theorem 1.32 (finite_independent).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem finite_independent (X D : Module.End K M) (v : M) (N L : ℕ)

    (hN : (D ^ (N + 1)) v = 0) (hL : (D ^ (L + 1)) v = 0) :

    finite X D N v = finite X D L v

Proof mechanism: Enlarge both valid cutoffs to their maximum and use finite_stable in both directions.

**Theorem 1.33 (commute_finite).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.Taylor

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

Exact accepted theorem:

theorem commute_finite (X D T : Module.End K M)

    (hX : Commute T X) (hD : Commute T D) (N : ℕ) :

    Commute T (finite X D N)

Proof mechanism: Commute the endomorphism through each creator and derivative power, then each scalar-weighted finite summand.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.projectionValue

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def projectionValue (i : σ) (v : M) : M :=

  Taylor.finite (W.X i) (W.D i) (W.cutoff i v) v

Construction and use: Evaluate the one-coordinate finite Taylor operator at the chosen pointwise cutoff.

**Theorem 1.34 (projectionValue_eq).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projectionValue_eq (i : σ) (v : M) (N : ℕ)

    (hN : (W.D i ^ (N + 1)) v = 0) :

    W.projectionValue i v = Taylor.finite (W.X i) (W.D i) N v

Proof mechanism: Use Taylor.finite_independent to replace the chosen cutoff by any valid inclusive cutoff.

**Theorem 1.35 (projectionValue_add).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projectionValue_add (i : σ) (v z : M) :

    W.projectionValue i (v + z) = W.projectionValue i v + W.projectionValue i z

Proof mechanism: Use the maximum of two pointwise cutoffs for both summands and their sum, then apply linearity of that fixed finite operator.

**Theorem 1.36 (projectionValue_smul).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projectionValue_smul (i : σ) (c : K) (v : M) :

    W.projectionValue i (c • v) = c • W.projectionValue i v

Proof mechanism: Reuse a valid cutoff for the vector and its scalar multiple, then apply fixed-operator linearity.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.projection

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def projection (i : σ) : Module.End K M where

  toFun := W.projectionValue i

  map_add' := W.projectionValue_add i

  map_smul' := W.projectionValue_smul i

Construction and use: Package the proved additive and scalar-linear projectionValue as an endomorphism.

**Theorem 1.37 (projection_eq).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projection_eq (i : σ) (v : M) (N : ℕ)

    (hN : (W.D i ^ (N + 1)) v = 0) :

    W.projection i v = Taylor.finite (W.X i) (W.D i) N v

Proof mechanism: Use the already proved cutoff-independent pointwise evaluation.

**Theorem 1.38 (D_projection).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem D_projection (i : σ) (v : M) : W.D i (W.projection i v) = 0

Proof mechanism: Taylor.D_finite reduces the derivative to its nilpotent boundary term.

**Theorem 1.39 (projection_eq_self).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projection_eq_self (i : σ) (v : M) (hv : W.D i v = 0) :

    W.projection i v = v

Proof mechanism: Taylor.finite_eq_self fixes vectors already in the derivative kernel.

**Theorem 1.40 (projection_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projection_X (i : σ) (v : M) : W.projection i (W.X i v) = 0

Proof mechanism: Use D_pow_X to validate the input cutoff after creation; Taylor.finite_X then has a vanishing boundary term.

**Theorem 1.41 (projection_idempotent).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projection_idempotent (i : σ) :

    W.projection i * W.projection i = W.projection i

Proof mechanism: The first projection lies in the derivative kernel, which the second projection fixes.

**Theorem 1.42 (commute_projection).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem commute_projection (i : σ) (T : Module.End K M)

    (hX : Commute T (W.X i)) (hD : Commute T (W.D i)) :

    Commute T (W.projection i)

Proof mechanism: A commuting endomorphism preserves a valid cutoff; replace both pointwise projectors by the same finite operator and apply Taylor.commute_finite.

**Theorem 1.43 (D_commute_projection).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem D_commute_projection {i j : σ} (hij : i ≠ j) :

    Commute (W.D i) (W.projection j)

Proof mechanism: Off-diagonal DX and DD supply the two commutation hypotheses of commute_projection.

**Theorem 1.44 (X_commute_projection).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem X_commute_projection {i j : σ} (hij : i ≠ j) :

    Commute (W.X i) (W.projection j)

Proof mechanism: XX and off-diagonal DX supply the two commutation hypotheses of commute_projection.

**Theorem 1.45 (projections_commute).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projections_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projections_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projections_commute (i j : σ) : Commute (W.projection i) (W.projection j)

Proof mechanism: For distinct coordinates use their creator/derivative commutation with the other projector; equal coordinates commute reflexively.

**Theorem 1.46 (projection_preserves_kernel).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_preserves_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_preserves_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem projection_preserves_kernel (i j : σ) (v : M) (hv : W.D j v = 0) :

    W.D j (W.projection i v) = 0

Proof mechanism: At the selected coordinate use D_projection; at another coordinate commute the derivative through the projector.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.finiteProjection

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def finiteProjection (s : Finset σ) : Module.End K M :=

  s.noncommProd W.projection (fun i _ j _ _ => W.projections_commute i j)

Construction and use: Multiply the commuting one-coordinate projectors over a finite index set.

**Theorem 1.47 (finiteProjection_empty).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem finiteProjection_empty : W.finiteProjection ∅ = 1

Proof mechanism: The empty product is the identity.

**Theorem 1.48 (finiteProjection_insert).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem finiteProjection_insert (i : σ) (s : Finset σ) (hi : i ∉ s) :

    W.finiteProjection (insert i s) = W.projection i * W.finiteProjection s

Proof mechanism: Split the inserted factor using the noncommProd insertion law.

**Theorem 1.49 (finiteProjection_fixes).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_fixes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_fixes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem finiteProjection_fixes (s : Finset σ) (v : M)

    (hv : ∀ i ∈ s, W.D i v = 0) : W.finiteProjection s v = v

Proof mechanism: Induct on the finite set and use projection_eq_self for each kernel condition.

**Theorem 1.50 (finiteProjection_preserves_kernel).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_preserves_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_preserves_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem finiteProjection_preserves_kernel (s : Finset σ) (j : σ) (v : M)

    (hv : W.D j v = 0) : W.D j (W.finiteProjection s v) = 0

Proof mechanism: Induct on the finite set and repeatedly use projection_preserves_kernel.

**Theorem 1.51 (finiteProjection_enlarge).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_enlarge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_enlarge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem finiteProjection_enlarge (s t : Finset σ) (hst : s ⊆ t) (v : M)

    (hv : ∀ i ∈ t \ s, W.D i v = 0) :

    W.finiteProjection t v = W.finiteProjection s v

Proof mechanism: Split the larger finite set into the smaller one and its difference; the extra projectors fix the input by the displayed kernel hypotheses.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.vacuumValue

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def vacuumValue (v : M) : M := W.finiteProjection (W.active v) v

Construction and use: Project over exactly the finite active indices of the input vector.

**Theorem 1.52 (vacuumValue_eq).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumValue_eq (s : Finset σ) (v : M) (hv : W.active v ⊆ s) :

    W.vacuumValue v = W.finiteProjection s v

Proof mechanism: Enlarging the active set adds only coordinates whose derivatives already vanish.

**Theorem 1.53 (vacuumValue_add).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumValue_add (v z : M) : W.vacuumValue (v + z) = W.vacuumValue v + W.vacuumValue z

Proof mechanism: Use the union of the two active sets as a common finite projection and apply its linearity.

**Theorem 1.54 (vacuumValue_smul).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumValue_smul (c : K) (v : M) : W.vacuumValue (c • v) = c • W.vacuumValue v

Proof mechanism: The scalar multiple has active set contained in that of the original vector, so both use the same linear finite projection.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.vacuumProjection

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def vacuumProjection : Module.End K M where

  toFun := W.vacuumValue

  map_add' := W.vacuumValue_add

  map_smul' := W.vacuumValue_smul

Construction and use: Package the cutoff-independent vacuumValue as a linear endomorphism.

**Theorem 1.55 (vacuumProjection_eq).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumProjection_eq (s : Finset σ) (v : M) (hv : W.active v ⊆ s) :

    W.vacuumProjection v = W.finiteProjection s v

Proof mechanism: Use finite-index-cutoff independence to evaluate the canonical projector over any finite superset of the active indices.

**Theorem 1.56 (vacuumProjection_mem).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumProjection_mem (v : M) : W.vacuumProjection v ∈ W.vacuum

Proof mechanism: Adjoin an arbitrary coordinate to the active set, isolate its projector and apply D_projection.

**Theorem 1.57 (vacuumProjection_eq_self).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumProjection_eq_self (v : M) (hv : v ∈ W.vacuum) :

    W.vacuumProjection v = v

Proof mechanism: Every coordinate derivative vanishes on a vacuum vector, so finiteProjection_fixes applies.

**Theorem 1.58 (vacuumProjection_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumProjection_X (i : σ) (v : M) : W.vacuumProjection (W.X i v) = 0

Proof mechanism: Adjoin the creator coordinate, place its projector next to the input and apply projection_X.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.vacuumProject

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def vacuumProject : M →ₗ[K] W.vacuum :=

  W.vacuumProjection.codRestrict W.vacuum W.vacuumProjection_mem

Construction and use: Codomain-restrict the canonical endomorphism to its proved joint-kernel image.

**Theorem 1.59 (vacuumProject_coe).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_coe`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem vacuumProject_coe (v : M) : (W.vacuumProject v : M) = W.vacuumProjection v

Proof mechanism: The codomain restriction has the same underlying vector.

**Theorem 1.60 (vacuumProject_subtype).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_subtype`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_subtype` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem vacuumProject_subtype (v : W.vacuum) : W.vacuumProject v = v

Proof mechanism: Use vacuumProjection_eq_self and subtype extensionality.

**Theorem 1.61 (vacuumProjection_idempotent).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem vacuumProjection_idempotent : W.vacuumProjection * W.vacuumProjection = W.vacuumProjection

Proof mechanism: The image lies in the vacuum and is fixed by the same projector.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.factorial

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def factorial (d : σ →₀ ℕ) : ℕ := d.prod (fun _ n => n.factorial)

Construction and use: Multiply coordinate factorials over the finite exponent support; the empty value is one.

**Theorem 1.62 (factorial_pos).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem factorial_pos (d : σ →₀ ℕ) : 0 < factorial d

Proof mechanism: Each coordinate factorial is positive, so their finite product is positive.

**Theorem 1.63 (factorial_cast_ne_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_cast_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_cast_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem factorial_cast_ne_zero (d : σ →₀ ℕ) : (factorial d : K) ≠ 0

Proof mechanism: Cast the positive natural product into the characteristic-zero field.

**Theorem 1.64 (factorial_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem factorial_zero : factorial (0 : σ →₀ ℕ) = 1

Proof mechanism: The explicitly typed zero multiindex has empty support and product one.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.coefficient

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def coefficient (d : σ →₀ ℕ) : M →ₗ[K] W.vacuum :=

  (factorial d : K)⁻¹ • (W.vacuumProject.comp (W.derivative d))

Construction and use: Apply the mixed derivative, then the vacuum projector, then reciprocal multiindex factorial scaling.

**Theorem 1.65 (coefficient_eq_zero_of_derivative).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_eq_zero_of_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_eq_zero_of_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_eq_zero_of_derivative (d : σ →₀ ℕ) (v : M)

    (hv : W.derivative d v = 0) : W.coefficient d v = 0

Proof mechanism: Linearity of projection and scaling sends a zero derivative to zero.

**Theorem 1.66 (coefficient_support_subset).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_support_subset (v : M) :

    Function.support (fun d : σ →₀ ℕ => W.coefficient d v) ⊆

      (Finset.Iic (W.jointCutoff v) : Set (σ →₀ ℕ))

Proof mechanism: Outside the derived simultaneous box, the mixed derivative and thus the coefficient vanish.

**Theorem 1.67 (coefficient_support_finite).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_support_finite (v : M) :

    Function.HasFiniteSupport (fun d : σ →₀ ℕ => W.coefficient d v)

Proof mechanism: Coefficient support is contained in the already finite derivative support.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.coefficients

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def coefficients : M →ₗ[K] ((σ →₀ ℕ) →₀ W.vacuum) where

  toFun v := Finsupp.ofSupportFinite (fun d => W.coefficient d v) (W.coefficient_support_finite v)

  map_add' v z := by

    apply Finsupp.ext

    intro d

    exact map_add (W.coefficient d) v z

  map_smul' c v := by

    apply Finsupp.ext

    intro d

    exact map_smul (W.coefficient d) c v

Construction and use: Assemble the proved finitely supported coefficient family; coordinatewise linearity gives its linear-map laws.

**Theorem 1.68 (coefficients_apply).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem coefficients_apply (v : M) (d : σ →₀ ℕ) :

    W.coefficients v d = W.coefficient d v

Proof mechanism: Evaluate the constructed finite-support function at the requested multiindex.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.evaluate

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def evaluate : ((σ →₀ ℕ) →₀ W.vacuum) →ₗ[K] M :=

  Finsupp.lsum K (fun d => (W.creation d).comp W.vacuum.subtype)

Construction and use: Use Finsupp.lsum to sum actual creation monomials applied to included joint-vacuum coefficients.

**Theorem 1.69 (evaluate_single).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

@[simp] theorem evaluate_single (d : σ →₀ ℕ) (v : W.vacuum) :

    W.evaluate (Finsupp.single d v) = W.creation d v

Proof mechanism: Evaluation of a single finite-support coefficient is exactly its creation action.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.fockMap

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def fockMap : (MvPolynomial σ K ⊗[K] W.vacuum) →ₗ[K] M :=

  W.evaluate.comp

    (TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials σ K)).toLinearMap

Construction and use: Use the polynomial monomial-basis tensor equivalence followed by the actual coefficient evaluation map.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.fockInverse

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def fockInverse : M →ₗ[K] (MvPolynomial σ K ⊗[K] W.vacuum) :=

  (TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials σ K)).symm.toLinearMap.comp

    W.coefficients

Construction and use: Use the actual finite coefficient map followed by the inverse polynomial monomial-basis tensor equivalence.

**Theorem 1.70 (fockMap_monomial).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem fockMap_monomial (d : σ →₀ ℕ) (v : W.vacuum) :

    W.fockMap (MvPolynomial.monomial d (1 : K) ⊗ₜ[K] v) = W.creation d v

Proof mechanism: The polynomial-factor basis equivalence sends a monomial tensor to a single coefficient; evaluate_single then gives the actual creation action.

**Theorem 1.71 (generated_by_vacuum).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.generated_by_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.generated_by_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem generated_by_vacuum (U : Submodule K M)

    (hΩ : W.vacuum ≤ U)

    (hX : ∀ i v, v ∈ U → W.X i v ∈ U) (v : M) : v ∈ U

Proof mechanism: Induct on a finite active-index set and then on the chosen coordinate nilpotence exponent. Its Taylor projection has fewer active coordinates, while positive-derivative tail terms use the smaller exponent. Subtract the tail to recover the input in U.

**Theorem 1.72 (range_evaluate_stable).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.range_evaluate_stable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.range_evaluate_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem range_evaluate_stable (i : σ) (v : M) (hv : v ∈ LinearMap.range W.evaluate) :

    W.X i v ∈ LinearMap.range W.evaluate

Proof mechanism: Move a creator into each finite evaluated coefficient and increment that coordinate's exponent using creation_add_single.

**Theorem 1.73 (finite_reconstruction).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem finite_reconstruction (v : M) :

    ∃ f : (σ →₀ ℕ) →₀ W.vacuum, W.evaluate f = v

Proof mechanism: Apply generated_by_vacuum to the range of evaluate, containing the joint vacuum and stable under every creator.

**Theorem 1.74 (fockMap_surjective).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem fockMap_surjective : Function.Surjective W.fockMap

Proof mechanism: Use finite_reconstruction and transport its coefficient witness through the inverse polynomial-factor tensor equivalence.

**Theorem 1.75 (derivative_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem derivative_X (d : σ →₀ ℕ) (i : σ) (v : M) :

    W.derivative d (W.X i v) = W.X i (W.derivative d v) +

      (d i : K) • W.derivative (d - Finsupp.single i 1) v

Proof mechanism: For zero coordinate degree commute the creator through all derivative factors. Otherwise isolate that derivative power and use Taylor.D_pow_X; the remaining factors commute with the creator.

**Theorem 1.76 (factorial_eq_prod).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_eq_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem factorial_eq_prod (d : σ →₀ ℕ) (s : Finset σ) (hs : d.support ⊆ s) :

    factorial d = ∏ i ∈ s, (d i).factorial

Proof mechanism: Extend the Finsupp product to a finite support superset, where extra zero exponents contribute factorial zero equal to one.

**Theorem 1.77 (factorial_add_single).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_add_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem factorial_add_single (d : σ →₀ ℕ) (i : σ) :

    factorial (d + Finsupp.single i 1) = (d i + 1) * factorial d

Proof mechanism: Use a common support, isolate the changed coordinate and apply factorial_succ. The source records reuse of the existing FactorialFockMetric calculation.

**Theorem 1.78 (restore_sub_single).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.restore_sub_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.restore_sub_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem restore_sub_single (d : σ →₀ ℕ) (i : σ) (hi : 0 < d i) :

    (d - Finsupp.single i 1) + Finsupp.single i 1 = d

Proof mechanism: Check each coordinate; positivity at the selected coordinate reverses truncated subtraction.

**Theorem 1.79 (coefficient_X_of_zero).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_X_of_zero (d : σ →₀ ℕ) (i : σ) (v : M) (hi : d i = 0) :

    W.coefficient d (W.X i v) = 0

Proof mechanism: Use derivative_X and vacuumProjection_X; the occupation-number term vanishes at zero degree.

**Theorem 1.80 (coefficient_X_of_pos).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_X_of_pos (d : σ →₀ ℕ) (i : σ) (v : M) (hi : 0 < d i) :

    W.coefficient d (W.X i v) = W.coefficient (d - Finsupp.single i 1) v

Proof mechanism: Use derivative_X and vacuumProjection_X, then cancel the occupation factor against factorial_add_single with nonzero characteristic-zero denominators.

**Theorem 1.81 (coefficient_vacuum).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_vacuum (ω : W.vacuum) (d : σ →₀ ℕ) :

    W.coefficient d ω = if d = 0 then ω else 0

Proof mechanism: The zero derivative gives the original vacuum vector; every nonzero multiindex has an excessive coordinate over the zero bound and hence vanishes.

**Theorem 1.82 (coefficient_creation).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_creation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficient_creation (e : σ →₀ ℕ) (ω : W.vacuum) :

    ∀ d : σ →₀ ℕ, W.coefficient d (W.creation e ω) = if d = e then ω else 0

Proof mechanism: Induct on the creation multiindex and its selected occupation. The two coefficient_X cases decrement matching positive coordinates; coefficient_vacuum supplies the base. No independence hypothesis on M is used.

**Theorem 1.83 (coefficients_evaluate).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_evaluate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_evaluate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem coefficients_evaluate (f : (σ →₀ ℕ) →₀ W.vacuum) :

    W.coefficients (W.evaluate f) = f

Proof mechanism: Use linear Finsupp induction and coefficient_creation to extract exactly each original coefficient.

**Theorem 1.84 (evaluate_coefficients).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem evaluate_coefficients (v : M) : W.evaluate (W.coefficients v) = v

Proof mechanism: Choose a finite reconstruction already proved independently; coefficients_evaluate identifies its coefficients and recovers the arbitrary vector.

**Theorem 1.85 (fockMap_fockInverse).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_fockInverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_fockInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem fockMap_fockInverse (v : M) : W.fockMap (W.fockInverse v) = v

Proof mechanism: Cancel the two polynomial-factor tensor equivalences and apply evaluate_coefficients.

**Theorem 1.86 (fockInverse_fockMap).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockInverse_fockMap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockInverse_fockMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem fockInverse_fockMap (t : MvPolynomial σ K ⊗[K] W.vacuum) :

    W.fockInverse (W.fockMap t) = t

Proof mechanism: Apply coefficients_evaluate and cancel the polynomial-factor tensor equivalences.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData.fockEquiv

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted def:

def fockEquiv : (MvPolynomial σ K ⊗[K] W.vacuum) ≃ₗ[K] M where

  toLinearMap := W.fockMap

  invFun := W.fockInverse

  left_inv := W.fockInverse_fockMap

  right_inv := W.fockMap_fockInverse

Construction and use: Package fockMap and fockInverse with their two proved inverse laws into the stated linear equivalence.

**Theorem 1.87 (taylor_reconstruction).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.taylor_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.taylor_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.WeylData

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable (W : WeylData K σ M)

Exact accepted theorem:

theorem taylor_reconstruction (v : M) :

    (∑ d ∈ Finset.Iic (W.jointCutoff v), (factorial d : K)⁻¹ •

      W.creation d (W.vacuumProjection (W.derivative d v))) = v

Proof mechanism: Extend the finite coefficient sum to the derived box using coefficient_support_subset, then unfold reciprocal factorial coefficient extraction in evaluate_coefficients.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.CurrentData

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

Exact accepted structure:

structure CurrentData (K : Type u) (ι : Type v) (M : Type w)

    [Field K] [CharZero K] [AddCommGroup M] [Module K M] where

  gram : Matrix ι ι K

  mode : ι → ℤ → Module.End K M

  heisenberg : ∀ a b m n,

    mode a m * mode b n - mode b n * mode a m =

      (if m + n = 0 then (m : K) * gram a b else 0) • 1

Construction and use: The record supplies actual all-integer endomorphism modes, a finite Gram matrix and the displayed full current commutator; it supplies no grading or nilpotence.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.X

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted def:

def X (p : ι × ℕ) : Module.End K M := A.mode p.1 (-(p.2 : ℤ) - 1)

Construction and use: Use the original negative mode at integer frequency minus (n+1).

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.D

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted def:

def D (H : Matrix ι ι K) (p : ι × ℕ) : Module.End K M :=

  ∑ b : ι, (((p.2 + 1 : ℕ) : K)⁻¹ * H p.1 b) • A.mode b ((p.2 : ℤ) + 1)

Construction and use: Take the inverse-Gram row combination of positive modes, divided by the nonzero frequency n+1.

**Theorem 1.88 (mode_commute_of_nonresonant).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mode_commute_of_nonresonant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mode_commute_of_nonresonant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem mode_commute_of_nonresonant (a b : ι) (m n : ℤ) (h : m + n ≠ 0) :

    Commute (A.mode a m) (A.mode b n)

Proof mechanism: The assumed full commutator has zero right side at nonresonant frequencies.

**Theorem 1.89 (X_commute).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem X_commute (p q : ι × ℕ) : Commute ((X A) p) ((X A) q)

Proof mechanism: Two strictly negative integer frequencies cannot sum to zero.

**Theorem 1.90 (smul_commute_smul).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.smul_commute_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.smul_commute_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem smul_commute_smul (T U : Module.End K M) (h : Commute T U) (c d : K) :

    Commute (c • T) (d • U)

Proof mechanism: Move scalar factors through endomorphism composition and use scalar commutativity.

**Theorem 1.91 (D_commute).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem D_commute (H : Matrix ι ι K) (p q : ι × ℕ) :

    Commute ((D A) H p) ((D A) H q)

Proof mechanism: Expand both finite row combinations; all positive-frequency constituent modes commute.

**Theorem 1.92 (D_X_commutator).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem D_X_commutator (H : Matrix ι ι K) (hHG : H * A.gram = 1)

    (p q : ι × ℕ) :

    (D A) H p * (X A) q - (X A) q * (D A) H p =

      (if p = q then (1 : K) else 0) • 1

Proof mechanism: Expand the finite row commutator, separate equal frequencies, contract H*gram=1 and cancel the nonzero positive frequency.

**Theorem 1.93 (D_X).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted theorem:

theorem D_X (H : Matrix ι ι K) (hHG : H * A.gram = 1)

    (p q : ι × ℕ) (v : M) :

    (D A) H p ((X A) q v) = (X A) q ((D A) H p v) + if p = q then v else 0

Proof mechanism: Evaluate the endomorphism commutator on v and rearrange its delta term.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.LowerBounded

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

Exact accepted structure:

structure LowerBounded (A : CurrentData K ι M) where

  grade : ℤ → Submodule K M

  lower : ℤ

  below : ∀ e : ℤ, e < lower → grade e = ⊥

  homogeneous : ∀ v : M, ∃ s : Finset ℤ, ∃ f : ℤ → M,

    (∀ e ∈ s, f e ∈ grade e) ∧ (∑ e ∈ s, f e) = v

  positive_lowers : ∀ a : ι, ∀ n : ℕ, ∀ e : ℤ, ∀ v ∈ grade e,

    A.mode a ((n : ℤ) + 1) v ∈ grade (e - ((n : ℤ) + 1))

Construction and use: The extra record supplies integer subspaces, a lower cutoff, finite homogeneous decomposition and the actual positive-mode lowering law. It supplies no oscillator decomposition or finite-dimensionality.

**Theorem 1.94 (D_mem_grade).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_mem_grade`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_mem_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem D_mem_grade (H : Matrix ι ι K) (p : ι × ℕ) (e : ℤ) (v : M)

    (hv : v ∈ L.grade e) : (D A) H p v ∈ L.grade (e - ((p.2 : ℤ) + 1))

Proof mechanism: Every constituent positive mode lands in the same lower grade, which is closed under finite sums and scalar multiples.

**Theorem 1.95 (D_pow_mem_grade).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_mem_grade`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_mem_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem D_pow_mem_grade (H : Matrix ι ι K) (p : ι × ℕ) (e : ℤ) (v : M)

    (hv : v ∈ L.grade e) (k : ℕ) :

    ((D A) H p ^ k) v ∈ L.grade (e - (k : ℤ) * ((p.2 : ℤ) + 1))

Proof mechanism: Iterate D_mem_grade and combine the integer weight shifts.

**Theorem 1.96 (D_pow_eq_zero_below).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_eq_zero_below`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_eq_zero_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem D_pow_eq_zero_below (H : Matrix ι ι K) (p : ι × ℕ) (e : ℤ) (v : M)

    (hv : v ∈ L.grade e) (k : ℕ)

    (hk : e - (k : ℤ) * ((p.2 : ℤ) + 1) < L.lower) :

    ((D A) H p ^ k) v = 0

Proof mechanism: The iterated output lies in a grade declared bottom below the lower cutoff.

**Theorem 1.97 (graded_bounds).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.graded_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.graded_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem graded_bounds (L : LowerBounded A) (H : Matrix ι ι K) (v : M) :

    ∃ B : ℕ,

      (∀ p : ι × ℕ, ((D A) H p ^ (B + 1)) v = 0) ∧

      (∀ p : ι × ℕ, B ≤ p.2 → (D A) H p v = 0)

Proof mechanism: Take the supremum of the finite component distances above the lower bound. This single vector-dependent B controls both the (B+1)-st power of every normalized derivative and all frequencies indexed at least B.

**Theorem 1.98 (D_locally_nilpotent).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_locally_nilpotent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_locally_nilpotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem D_locally_nilpotent (L : LowerBounded A) (H : Matrix ι ι K) (p : ι × ℕ) (v : M) :

    ∃ n : ℕ, ((D A) H p ^ n) v = 0

Proof mechanism: Use the exponent B+1 supplied by graded_bounds for the selected coordinate and vector.

**Theorem 1.99 (D_active_finite).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_active_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_active_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem D_active_finite (L : LowerBounded A) (H : Matrix ι ι K) (v : M) :

    {p : ι × ℕ | (D A) H p v ≠ 0}.Finite

Proof mechanism: graded_bounds confines nonzero action to the product of finite original rank and Finset.range B.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.weylData

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def weylData (L : LowerBounded A) (H : Matrix ι ι K) (hHG : H * A.gram = 1) :

    WeylData K (ι × ℕ) M where

  X := (X A)

  D := (D A) H

  xx := (X_commute A)

  dd := (D_commute A) H

  dx := by

    intro p q v

    by_cases h : p = q <;> simpa [h] using D_X A H hHG p q v

  nilpotent := (D_locally_nilpotent A) L H

  active_finite := (D_active_finite A) L H

Construction and use: Combine the proved XX, DD, DX, graded local nilpotence and finite activity into the generic WeylData record, retaining the separate LowerBounded data L.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.vacuumProject

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def vacuumProject (H : Matrix ι ι K) (hHG : H * A.gram = 1) :

    M →ₗ[K] ((weylData A) L H hHG).vacuum := ((weylData A) L H hHG).vacuumProject

Construction and use: Consume the generic WeylData vacuum projector for this explicitly graded normalized-current representation.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.reconstructionMap

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def reconstructionMap (H : Matrix ι ι K) (hHG : H * A.gram = 1) :

    (MvPolynomial (ι × ℕ) K ⊗[K] ((weylData A) L H hHG).vacuum) →ₗ[K] M :=

  ((weylData A) L H hHG).fockMap

Construction and use: Consume the generic fockMap for the same normalized currents and joint kernel.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.normalizedFockEquiv

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def normalizedFockEquiv (H : Matrix ι ι K) (hHG : H * A.gram = 1) :

    (MvPolynomial (ι × ℕ) K ⊗[K] ((weylData A) L H hHG).vacuum) ≃ₗ[K] M :=

  ((weylData A) L H hHG).fockEquiv

Construction and use: Consume the generic fockEquiv with both inverse laws for the normalized currents, under L and H*gram=1.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.positiveVacuum

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def positiveVacuum : Submodule K M :=

  ⨅ p : ι × ℕ, LinearMap.ker (A.mode p.1 ((p.2 : ℤ) + 1))

Construction and use: Intersect kernels of the ORIGINAL strictly positive integer modes, leaving zero modes unrestricted.

**Theorem 1.100 (mem_positiveVacuum).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_positiveVacuum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_positiveVacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

@[simp] theorem mem_positiveVacuum (v : M) :

    v ∈ (positiveVacuum A) ↔ ∀ p : ι × ℕ, A.mode p.1 ((p.2 : ℤ) + 1) v = 0

Proof mechanism: Unfold the positive-current kernel intersection.

**Theorem 1.101 (unnormalize).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.unnormalize`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.unnormalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem unnormalize (H : Matrix ι ι K) (hGH : A.gram * H = 1) (a : ι) (n : ℕ) :

    (n + 1 : K) • (∑ b : ι, A.gram a b • (D A) H (b, n)) =

      A.mode a ((n : ℤ) + 1)

Proof mechanism: Expand the row normalization and cancel the positive frequency; contract gram*H=1 in its opposite orientation to recover the original current.

**Theorem 1.102 (normalized_vacuum_eq).**

Lean statement: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.normalized_vacuum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.normalized_vacuum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted theorem:

theorem normalized_vacuum_eq (H : Matrix ι ι K)

    (hHG : H * A.gram = 1) (hGH : A.gram * H = 1) :

    ((weylData A) L H hHG).vacuum = (positiveVacuum A)

Proof mechanism: One implication uses unnormalize with gram*H=1; the other uses the defining finite normalized row sum. The WeylData expression retains L and H*gram=1.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.gradedFockEquiv

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def gradedFockEquiv (H : Matrix ι ι K)

    (hHG : H * A.gram = 1) (hGH : A.gram * H = 1) :

    (MvPolynomial (ι × ℕ) K ⊗[K] (positiveVacuum A)) ≃ₗ[K] M :=

  (LinearEquiv.lTensor (MvPolynomial (ι × ℕ) K)

    (LinearEquiv.ofEq (positiveVacuum A) ((weylData A) L H hHG).vacuum

      ((normalized_vacuum_eq A) L H hHG hGH).symm)).trans

        ((normalizedFockEquiv A) L H hHG)

Construction and use: Transport the polynomial tensor factor along the proved equality of normalized and original positive-current vacua, then compose with normalizedFockEquiv under L and both inverse equations.

D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents.nonsingularFockEquiv

Original namespace: D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock.PositiveCurrents

Original Lean scope:

variable {K : Type u} [Field K] [CharZero K]

variable {σ : Type v} {M : Type w} [AddCommGroup M] [Module K M]

variable {ι : Type v} [Fintype ι]

variable (A : CurrentData K ι M)

variable (L : LowerBounded A)

Exact accepted def:

def nonsingularFockEquiv (hG : IsUnit A.gram.det) :

    (MvPolynomial (ι × ℕ) K ⊗[K] (positiveVacuum A)) ≃ₗ[K] M :=

  (gradedFockEquiv A) L A.gram⁻¹ (Matrix.nonsing_inv_mul A.gram hG)

    (Matrix.mul_nonsing_inv A.gram hG)

Construction and use: Mathlib constructs the inverse from IsUnit det(gram); its two inverse equations feed gradedFockEquiv, still under L. The empty Gram determinant is one.

The exact accepted source SHA256 is 27f1072ae69b1dbda61b8256fa460d4cdf8c1b25b228a11c8c2589f818b55c8c. Static parent acceptance records 239 authored declarations/local instances across the four roots, not 534 new authored theorems. Original comments and supplier attribution remain byte-for-byte in the preserved suffix; no literature or novelty claim is added. Metadata, Scribe and Reg are uncompiled source-only candidates. Native integration owns Scribe/metadata coverage, complete native source/type/axiom checks and real registration. No unconditional all-weak-module nilpotence, nonzero or generating Top, Top=positive-current vacuum, full charged module classification, category/fusion realization, string theory or AdS/CFT completion follows. The global objective remains active and incomplete.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_commutator`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_X_pow`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_active_finite`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_commute_projection`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_finite`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_locally_nilpotent`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_mem_grade`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_eq_zero_below`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_pow_mem_grade`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.D_projection`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.X_commute_projection`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_add_subset`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.active_smul_subset`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_pos`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_X_of_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_creation`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_eq_zero_of_derivative`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_succ`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_finite`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_support_subset`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_vacuum`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficient_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.coefficients_evaluate`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_finite`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.commute_projection`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_add_single`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.creation_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_spec`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.cutoff_succ_spec`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_commute`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_excess`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_eq_zero_of_not_le`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_finite`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_support_subset`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.derivative_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.dx_of_ne`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_coefficients`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.evaluate_single`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_add_single`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_cast_ne_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_eq_prod`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_ne_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_pos`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.factorial_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_empty`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_enlarge`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_fixes`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_insert`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finiteProjection_preserves_kernel`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_eq_self`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_independent`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_reconstruction`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_stable`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_succ`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.finite_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockInverse_fockMap`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_fockInverse`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_monomial`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.fockMap_surjective`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.generated_by_vacuum`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.graded_bounds`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_orbit`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.jointCutoff_spec`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_active`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_positiveVacuum`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mem_vacuum`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.mode_commute_of_nonresonant`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_add_single`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.monomialOperator_on`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.normalized_vacuum_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_add`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projectionValue_smul`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_eq_self`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_idempotent`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projection_preserves_kernel`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.projections_commute`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.range_evaluate_stable`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.restore_sub_single`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.smul_commute_smul`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.taylor_reconstruction`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.unnormalize`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_coe`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProject_subtype`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_X`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_eq_self`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_idempotent`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumProjection_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_add`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock.vacuumValue_smul`
