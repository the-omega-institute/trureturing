# Full mixed Jacobi transports the actual lattice currents

## Abstract

FullJacobiCurrentTransport

D is the original LatticeData, with arbitrary finite rank including zero. M : Type u is arbitrary with AddCommGroup M and Module Complex M, possibly zero. The full original charged source carrier, its Y, translation, vacuum and current states are retained. The record FullJacobiLatticeModule assumes only the source-linear actual Laurent-truncated module fields, vacuum field and full all-integer mixed Jacobi with THREE separately finite supports. Current CCR, translation and finite activity are proved from that data. H is arbitrary in row sums and activity statements; normalized DX uses H*gramComplex D=1, while original-current recovery and the vacuum iff use gramComplex D*H=1. Neither source positivity nor a target grading, local nilpotence, Fock equivalence, faithfulness or nonzero M is a premise of this adapter. At rank zero the active-bound supremum is zero.

Mixed Jacobi at r=0 gives the endomorphism commutator; source nonnegative-product truncation makes its support finite before evaluation. At p=0 it gives the iterate with two separately finite sums. Taking r=-2 and vacuum in that iterate derives module translation, with the exact negative-two binomial coefficient and three integer-sign cases. Source creativity and the actual neutral-current commutator compute every nonnegative current product, so only product index one survives in the all-integer module current CCR. Finite row expansion contracts HG for normalized DX and GH for original positive-current recovery. Genuine Laurent truncation gives per-current cutoffs; their finite-rank supremum proves finite active support, including rank zero. It does not prove local nilpotence.

Each exact source signature below is interpreted in its displayed ORIGINAL Lean variable scope; scope commands introduce names and do not add unused parameters. The sealed native statement-v1 telescope, referenced for every authored entry in transfer-manifest.json, fixes precisely which implicit parameters and instances are actually bound. Definitions and records display their actual constructions/fields. No signature is generalized, specialized, renamed or reproved. Imported suppliers are used only as they occur in the four accepted proofs; their definitions have not been read or repackaged here.

Original universe/open directives (names are resolved in the original source module and the namespace shown for each entry):

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal

open LatticeSugawaraCurrents FieldNormalProduct LatticeFiniteNegativeGeneration

open StateFieldResidueReconstruction (integerBinomial)

open scoped BigOperators VertexOperator

universe u

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.sourceProduct

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

(parameters are displayed in the declaration itself)

Exact accepted abbrev:

abbrev sourceProduct (D : LatticeData) (a : Carrier D) (n : ℤ)

    (b : Carrier D) : Carrier D := ((Y D a)[[n]]) b

Construction and use: Use the actual source state-field coefficient on the full original carrier, with its signed integer index.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.jacobiLeft

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

(parameters are displayed in the declaration itself)

Exact accepted def:

def jacobiLeft {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

    (F : Carrier D →ₗ[ℂ] VertexOperator ℂ M)

    (a b : Carrier D) (w : M) (p q r : ℤ) (i : ℕ) : M :=

  integerBinomial p i • ((F (sourceProduct D a (r + i) b))[[p + q - i]]) w

Construction and use: Define the source-product side of mixed Borcherds with integer binomial p choose i.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.jacobiFirst

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

(parameters are displayed in the declaration itself)

Exact accepted def:

def jacobiFirst {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

    (F : Carrier D →ₗ[ℂ] VertexOperator ℂ M)

    (a b : Carrier D) (w : M) (p q r : ℤ) (i : ℕ) : M :=

  (((-1 : ℂ)^i) * integerBinomial r i) •

    ((F a)[[p + r - i]]) (((F b)[[q + i]]) w)

Construction and use: Define the first ordered module-mode term with its original sign and binomial coefficient.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.jacobiSecond

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

(parameters are displayed in the declaration itself)

Exact accepted def:

def jacobiSecond {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

    (F : Carrier D →ₗ[ℂ] VertexOperator ℂ M)

    (a b : Carrier D) (w : M) (p q r : ℤ) (i : ℕ) : M :=

  (((-1 : ℂ)^i) * integerBinomial r i) •

    (StateFieldResidueReconstruction.epsilon r • ((F b)[[q + r - i]]) (((F a)[[p + i]]) w))

Construction and use: Define the reverse ordered term with the original integer epsilon(r) sign.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.FullJacobiLatticeModule

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

(parameters are displayed in the declaration itself)

Exact accepted structure:

structure FullJacobiLatticeModule (D : LatticeData) (M : Type u)

    [AddCommGroup M] [Module ℂ M] where

  stateField : Carrier D →ₗ[ℂ] VertexOperator ℂ M

  vacuum_field : stateField (vacuum D) = identityField

  borcherds : ∀ (a b : Carrier D) (w : M) (p q r : ℤ),

    Function.HasFiniteSupport (jacobiLeft stateField a b w p q r) ∧

    Function.HasFiniteSupport (jacobiFirst stateField a b w p q r) ∧

    Function.HasFiniteSupport (jacobiSecond stateField a b w p q r) ∧

      (∑ᶠ i : ℕ, jacobiLeft stateField a b w p q r i) =

        ∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial r i) •

          (((stateField a)[[p + r - i]]) (((stateField b)[[q + i]]) w) -

            StateFieldResidueReconstruction.epsilon r • ((stateField b)[[q + r - i]])

              (((stateField a)[[p + i]]) w))

Construction and use: The only module assumptions are a state-linear Laurent-truncated VertexOperator, its vacuum field, and full mixed Jacobi for every original source pair, module vector and three integer parameters, with all three supports separately finite. No CCR, translation, grading or nilpotence is assumed.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.mode

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted abbrev:

abbrev mode (J : FullJacobiLatticeModule D M) (a : Carrier D) (n : ℤ) :

    Module.End ℂ M := (J.stateField a)[[n]]

Construction and use: Evaluate the given module state field at the original integer coefficient.

**Theorem 1.1 (vacuum_modes).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.vacuum_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.vacuum_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem vacuum_modes (J : FullJacobiLatticeModule D M) (n : ℤ) :

    mode J (vacuum D) n = if n = -1 then LinearMap.id else 0

Proof mechanism: Use the vacuum-field axiom and the coefficient formula for the identity field.

**Theorem 1.2 (module_truncation).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_truncation (J : FullJacobiLatticeModule D M)

    (a : Carrier D) (w : M) :

    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode J a n w = 0

Proof mechanism: Extract a vector-dependent high-mode cutoff from the actual Laurent-series order.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.commutatorTerm

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def commutatorTerm (J : FullJacobiLatticeModule D M)

    (a b : Carrier D) (p q : ℤ) (i : ℕ) : Module.End ℂ M :=

  integerBinomial p i • mode J (sourceProduct D a i b) (p + q - i)

Construction and use: Form the endomorphism-valued source-product term with the original integer binomial weighting.

**Theorem 1.3 (commutator_terms_finite).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.commutator_terms_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.commutator_terms_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem commutator_terms_finite (J : FullJacobiLatticeModule D M)

    (a b : Carrier D) (p q : ℤ) :

    Function.HasFiniteSupport (commutatorTerm J a b p q)

Proof mechanism: Use actual source nonnegative-product truncation before evaluation; state linearity sends a zero source product to the zero endomorphism.

**Theorem 1.4 (module_mode_commutator).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_mode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_mode_commutator (J : FullJacobiLatticeModule D M)

    (a b : Carrier D) (p q : ℤ) :

    mode J a p * mode J b q - mode J b q * mode J a p =

      ∑ᶠ i : ℕ, commutatorTerm J a b p q i

Proof mechanism: Specialize mixed Jacobi at r=0. The right side reduces to i=0; finite support permits evaluation of the endomorphism-valued source-product sum on every vector.

**Theorem 1.5 (module_iterate).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_iterate (J : FullJacobiLatticeModule D M)

    (a b : Carrier D) (w : M) (r q : ℤ) :

    Function.HasFiniteSupport (jacobiFirst J.stateField a b w 0 q r) ∧

    Function.HasFiniteSupport (jacobiSecond J.stateField a b w 0 q r) ∧

      mode J (sourceProduct D a r b) q w =

        (∑ᶠ i : ℕ, jacobiFirst J.stateField a b w 0 q r i) -

        (∑ᶠ i : ℕ, jacobiSecond J.stateField a b w 0 q r i)

Proof mechanism: Specialize at p=0. The source-product side reduces to i=0, and the two separately finite right supports justify splitting their difference.

**Theorem 1.6 (module_translation_modes).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_translation_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_translation_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_translation_modes (J : FullJacobiLatticeModule D M)

    (a : Carrier D) (q : ℤ) :

    mode J (translation D a) q = -(q : ℂ) • mode J a (q - 1)

Proof mechanism: Use module_iterate with r=-2 and b=vacuum, the actual source translation_as_mode identity and the negative-two binomial formula. In the negative, zero and positive q cases, identity-field coefficients leave the exact single contributing term or zero.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.currentState

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def currentState (D : LatticeData) (i : Fin D.rank) : Carrier D :=

  ((neutralField D i)[[-1]]) (vacuum D)

Construction and use: Apply the actual source neutral current at mode -1 to the actual vacuum.

**Theorem 1.7 (current_state_field).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_state_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_state_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem current_state_field (D : LatticeData) (i : Fin D.rank) :

    Y D (currentState D i) = neutralField D i

Proof mechanism: Use the existing source stateField_current identity for that creation-defined current.

**Theorem 1.8 (source_current_vacuum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem source_current_vacuum (D : LatticeData) (i : Fin D.rank)

    (n : ℤ) (hn : 0 ≤ n) : neutralMode D i n (vacuum D) = 0

Proof mechanism: Apply actual source creativity to the current and identify its field coefficients with neutralMode.

**Theorem 1.9 (source_current_product).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem source_current_product (D : LatticeData) (i j : Fin D.rank) (k : ℕ) :

    sourceProduct D (currentState D i) k (currentState D j) =

      if k = 1 then (D.G i j : ℂ) • vacuum D else 0

Proof mechanism: Evaluate the actual source neutral-current commutator at (k,-1) on vacuum. Creativity removes one term, so only k=1 yields Gram times vacuum.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.current

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted abbrev:

abbrev current (J : FullJacobiLatticeModule D M) (i : Fin D.rank) (n : ℤ) :

    Module.End ℂ M := mode J (currentState D i) n

Construction and use: Use the given arbitrary-module field of the actual creation-defined source current.

**Theorem 1.10 (module_current_heisenberg).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_current_heisenberg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_current_heisenberg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_current_heisenberg (J : FullJacobiLatticeModule D M)

    (i j : Fin D.rank) (m n : ℤ) :

    current J i m * current J j n - current J j n * current J i m =

      (if m + n = 0 then (m : ℂ) * (D.G i j : ℂ) else 0) •

        (1 : Module.End ℂ M)

Proof mechanism: Insert the computed source_current_product into module_mode_commutator. Only i=1 survives, and vacuum_modes gives the full signed all-integer central term on M.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.rowMode

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def rowMode (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (i : Fin D.rank) (n : ℤ) :

    Module.End ℂ M := ∑ j, H i j • current J j n

Construction and use: Take the finite row combination whose free index is the FIRST matrix index of H.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.creation

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def creation (J : FullJacobiLatticeModule D M) (i : Fin D.rank) (r : ℕ) :

    Module.End ℂ M := current J i (-(r : ℤ) - 1)

Construction and use: Use the original current at mode minus (r+1).

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.annihilation

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def annihilation (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (i : Fin D.rank) (r : ℕ) :

    Module.End ℂ M := (r + 1 : ℂ)⁻¹ • rowMode J H i ((r : ℤ) + 1)

Construction and use: Divide the H-row positive current combination by its nonzero frequency r+1.

**Theorem 1.11 (row_current_commutator).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.row_current_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.row_current_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem row_current_commutator (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (i k : Fin D.rank) (m n : ℤ) :

    rowMode J H i m * current J k n - current J k n * rowMode J H i m =

      (if m + n = 0 then (m : ℂ) * (H * gramComplex D) i k else 0) •

        (1 : Module.End ℂ M)

Proof mechanism: Expand the row and commute scalars through composition, then use the genuine all-integer current relation and Matrix.mul_apply.

**Theorem 1.12 (normalized_XX).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_XX`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_XX` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem normalized_XX (J : FullJacobiLatticeModule D M)

    (i j : Fin D.rank) (r s : ℕ) : Commute (creation J i r) (creation J j s)

Proof mechanism: Two negative frequencies cannot resonate in the proved module current relation.

**Theorem 1.13 (normalized_DD).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DD`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem normalized_DD (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (i j : Fin D.rank) (r s : ℕ) :

    Commute (annihilation J H i r) (annihilation J H j s)

Proof mechanism: Expand the two positive row combinations; every positive-frequency constituent commutator is zero.

**Theorem 1.14 (normalized_DX).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DX`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DX` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem normalized_DX (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)

    (i k : Fin D.rank) (r s : ℕ) :

    annihilation J H i r * creation J k s -

      creation J k s * annihilation J H i r =

        (if r = s then (if i = k then (1 : ℂ) else 0) else 0) •

          (1 : Module.End ℂ M)

Proof mechanism: Use row_current_commutator, contract H*gramComplex=1 and cancel the nonzero frequency. Equality of frequencies and indices gives exactly the two displayed deltas.

**Theorem 1.15 (gram_rowMode).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.gram_rowMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.gram_rowMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem gram_rowMode (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)

    (j : Fin D.rank) (n : ℤ) :

    (∑ i, gramComplex D j i • rowMode J H i n) = current J j n

Proof mechanism: Swap the finite matrix sums and contract gramComplex*H=1 to recover the original current.

**Theorem 1.16 (positive_current_from_normalized).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.positive_current_from_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.positive_current_from_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem positive_current_from_normalized (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)

    (j : Fin D.rank) (r : ℕ) :

    (r + 1 : ℂ) • (∑ i, gramComplex D j i • annihilation J H i r) =

      current J j ((r : ℤ) + 1)

Proof mechanism: Undo the nonzero frequency scaling in the annihilators, then use gram_rowMode with gramComplex*H=1.

**Theorem 1.17 (normalized_vacuum_iff).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_vacuum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_vacuum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem normalized_vacuum_iff (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)

    (w : M) :

    (∀ (i : Fin D.rank) (r : ℕ), annihilation J H i r w = 0) ↔

      (∀ (j : Fin D.rank) (n : ℤ), 0 < n → current J j n w = 0)

Proof mechanism: Recover every strictly positive integer current from the normalized annihilators using gramComplex*H=1; conversely the finite normalized row sum vanishes if each positive current does. No zero-mode condition occurs.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.currentCutoff

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def currentCutoff (J : FullJacobiLatticeModule D M) (i : Fin D.rank) (w : M) : ℕ :=

  (-((HahnModule.of ℂ).symm (J.stateField (currentState D i) w)).order).toNat

Construction and use: Take the natural part of minus the actual Laurent-series order for the selected current acting on w.

**Theorem 1.18 (current_vanish_above_cutoff).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_vanish_above_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_vanish_above_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem current_vanish_above_cutoff (J : FullJacobiLatticeModule D M)

    (i : Fin D.rank) (w : M) (r : ℕ) (hr : currentCutoff J i w ≤ r) :

    current J i ((r : ℤ) + 1) w = 0

Proof mechanism: Apply the Laurent coefficient-order vanishing criterion to the integer mode r+1.

D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport.activeBound

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def activeBound (J : FullJacobiLatticeModule D M) (w : M) : ℕ :=

  Finset.univ.sup (fun i : Fin D.rank => currentCutoff J i w)

Construction and use: Take Finset.univ.sup of the finitely many current cutoffs; for rank zero it is zero.

**Theorem 1.19 (annihilation_vanish_above_bound).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.annihilation_vanish_above_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.annihilation_vanish_above_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_vanish_above_bound (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (i : Fin D.rank) (w : M) (r : ℕ) (hr : activeBound J w ≤ r) :

    annihilation J H i r w = 0

Proof mechanism: The finite-rank supremum bounds every constituent current cutoff, so every summand in the normalized row vanishes.

**Theorem 1.20 (finite_active_support).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.finite_active_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.finite_active_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem finite_active_support (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (w : M) :

    Function.HasFiniteSupport

      (fun x : Fin D.rank × ℕ => annihilation J H x.1 x.2 w)

Proof mechanism: Nonzero normalized action is confined to Fin D.rank times Finset.range(activeBound J w). This uses genuine truncation and finite original rank, with no grading, positivity or local nilpotence.

The exact accepted source SHA256 is e536d0480559b43efffc391c50f331d325db548ddd6b4dd5c6f60a847ccaa2e3. Static parent acceptance records 239 authored declarations/local instances across the four roots, not 534 new authored theorems. Original comments and supplier attribution remain byte-for-byte in the preserved suffix; no literature or novelty claim is added. Canonical integration preserves these exact signatures and constructions, with native source/type/axiom verification and generated Blueprint owned by the canonical commands. The four-slot source-bound audits for the 20 public theorems remain unfinished under CLAUDE.md section 3.9; https://github.com/the-omega-institute/trureturing/issues/29464 records the missing exact source reconstruction, Law equivalence, rejected intervention, sensitivity and observational dependence. The uncompiled sourceScope stub is not retained; no enrollment or declared_validated status is claimed. No unconditional all-weak-module nilpotence, nonzero or generating Top, Top=positive-current vacuum, full charged module classification, category/fusion realization, string theory or AdS/CFT completion follows. The global objective remains active and incomplete.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.annihilation_vanish_above_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.commutator_terms_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_state_field`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.current_vanish_above_cutoff`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.finite_active_support`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.gram_rowMode`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_current_heisenberg`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_iterate`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_translation_modes`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.module_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DD`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_DX`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_XX`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.normalized_vacuum_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.positive_current_from_normalized`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.row_current_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_product`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.source_current_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport.vacuum_modes`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus](../LatticeActualStateFieldCalculus.md)
