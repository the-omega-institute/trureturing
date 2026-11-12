# The genuine Zhu quotient acts on Top with a finite joint current decomposition

## Abstract

FullJacobiZhuTopRepresentation

D is the original LatticeData, M : Type u has only AddCommGroup and Module Complex, and J is the full mixed-Jacobi module of the adapter. Top J is defined using EVERY original homogeneous source state of EVERY integer degree h and EVERY integer n>=h. Its inclusion in positiveCurrentVacuum is one-way. Homogeneous zero-mode stability, the zeroMode action and quotient representation require exactly the displayed positive-definiteness hypothesis on the ORIGINAL real source Gram form hD; the Spectrum section packages that same hypothesis as hPos : Fact (...PosDef...). No target grading or nonzero Top, target finite dimension, basis, faithful action, Top generation or equality with the positive-current vacuum is assumed. The two original local quotient instances use quotientRing D hPos.out and quotientAlgebra D hPos.out. The finite source Node/Grid projectors act ON Top, not on all M. Rank zero is allowed by the literal binders: coordinate claims over Fin 0 are vacuous and the empty joint eigenspace intersection is the whole Top. The finite Grid-indexed conclusions remain exactly as stated, with no nonzero component inferred. Zero M or zero Top is allowed, and neither a projector image nor a component is required nonzero; AllAlpha survival is conditional on the displayed nonzero premise.

Source grading and the full finite commutator prove homogeneous zero-mode stability of the actual Top. The existing internal direct sum gives a source-linear zeroMode for mixed-energy states. All three supports are transported into the existing residue fullLaw; the circle and star residue lemmas then prove that the literal full O-space is in the kernel and that star multiplication is respected on BOTH arbitrary source arguments, using their finite source grade projections. Vacuum gives the unit. Descent through the existing zhuO.liftQ and existing quotient ring/algebra yields the genuine AlgHom on Q. Restrict it to currentAlgebra and map the EXISTING coordinate/grid source projectors. Their finite sums, current eigenidentities and conditional source survival produce the full stated finite joint decomposition ON Top. No faithful action or nonzero component is needed.

Each exact source signature below is interpreted in its displayed ORIGINAL Lean variable scope; scope commands introduce names and do not add unused parameters. The sealed native statement-v1 telescope, referenced for every authored entry in transfer-manifest.json, fixes precisely which implicit parameters and instances are actually bound. Definitions and records display their actual constructions/fields. No signature is generalized, specialized, renamed or reproved. Imported suppliers are reused as they occur in the accepted source proof; the other prepared roots are not republished here.

Original universe/open directives (names are resolved in the original source module and the namespace shown for each entry):

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction

open LatticeSugawaraConformal LatticeSugawaraCurrents LatticePositiveEnergy

open FullJacobiCurrentTransport

open Lattice.ActualZhuProduct

open LatticeHalfFockGroundRightCurrentTransport.Calculus

open scoped BigOperators VertexOperator DirectSum

universe u

open Lattice.ActualZhuCurrentNormalForm Lattice.ActualZhuSourceProjectors

open Lattice.ActualZhuMinimum

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.Top

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def Top (J : FullJacobiLatticeModule D M) : Submodule ℂ M where

  carrier := {w | ∀ (h n : ℤ) (a : Carrier D), a ∈ grade D h → h ≤ n →

    mode J a n w = 0}

  zero_mem' := by

    intro h n a ha hn

    exact map_zero (mode J a n)

  add_mem' := by

    intro v w hv hw h n a ha hn

    rw [map_add, hv h n a ha hn, hw h n a ha hn, add_zero]

  smul_mem' := by

    intro c w hw h n a ha hn

    rw [map_smul, hw h n a ha hn, smul_zero]

Construction and use: Require every original source state of every integer degree h to kill the vector at every integer mode n>=h. Linearity of all actual modes proves the submodule laws.

**Theorem 1.1 (currentState_eq_actual).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_eq_actual`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_eq_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem currentState_eq_actual (i : Fin D.rank) :

    FullJacobiCurrentTransport.currentState D i =

      LatticeActualConformalState.currentState D i

Proof mechanism: Use the existing actual-current creation identity to identify the adapter current state.

**Theorem 1.2 (currentState_mem_grade).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_mem_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_mem_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem currentState_mem_grade (i : Fin D.rank) :

    FullJacobiCurrentTransport.currentState D i ∈ grade D 1

Proof mechanism: Transport the existing actual source current grade-one theorem along currentState_eq_actual.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.positiveCurrentVacuum

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def positiveCurrentVacuum (J : FullJacobiLatticeModule D M) : Submodule ℂ M :=

  ⨅ (i : Fin D.rank) (n : ℤ) (_ : 0 < n), LinearMap.ker (current J i n)

Construction and use: Intersect the actual strictly positive current kernels. This space is only a proved upper bound for Top.

**Theorem 1.3 (top_le_positiveCurrentVacuum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.top_le_positiveCurrentVacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.top_le_positiveCurrentVacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem top_le_positiveCurrentVacuum (J : FullJacobiLatticeModule D M) :

    Top J ≤ positiveCurrentVacuum J

Proof mechanism: Apply the defining Top condition to each grade-one source current at every positive integer n.

**Theorem 1.4 (homogeneous_zero_preserves_top).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.homogeneous_zero_preserves_top`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.homogeneous_zero_preserves_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem homogeneous_zero_preserves_top (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h)

    (w : M) (hw : w ∈ Top J) :

    mode J a (h - 1) w ∈ Top J

Proof mechanism: Commute an arbitrary high mode b_n past a_(h-1). Actual source grading puts each commutator source product in degree k+h-i-1, while its mode is n+h-1-i, high enough to kill the original Top vector. Finite commutator support permits evaluation termwise.

**Theorem 1.5 (module_fullLaw).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.module_fullLaw`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.module_fullLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_fullLaw (J : FullJacobiLatticeModule D M) (a b : Carrier D) :

    fullLaw (J.stateField a) (J.stateField b)

      (fun r => J.stateField (sourceProduct D a r b)) 0

Proof mechanism: Transport all three separately finite mixed-Jacobi supports to the existing residue calculus with Ring.map_choose and the original epsilon sign, then split the finite difference.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.zeroMode

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def zeroMode (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :

    Carrier D →ₗ[ℂ] Module.End ℂ (Top J) :=

  (DirectSum.toModule ℂ ℤ (Module.End ℂ (Top J)) (homogeneousZero J hD)).comp

    (carrierEnergyDecomposition D).toLinearMap

Construction and use: Use homogeneous_zero_preserves_top to define each homogeneous zero mode, then compose DirectSum.toModule with the ACTUAL source carrierEnergyDecomposition. This defines a state-linear action on arbitrary mixed-energy source states.

**Theorem 1.6 (zeroMode_homogeneous).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zeroMode_homogeneous (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (w : Top J) :

    (zeroMode J hD a w).val = mode J a (h - 1) w.val

Proof mechanism: The actual internal direct-sum decomposition sends a homogeneous source vector to its single graded inclusion, so DirectSum.toModule evaluates its mode h-1, including negative integer degrees.

**Theorem 1.7 (zeroMode_finite).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zeroMode_finite (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

    (a : Carrier D) (w : Top J) :

    (zeroMode J hD a w).val = ∑ h ∈ stateEnergies D a,

      mode J (gradeProjection D h a) (h - 1) w.val

Proof mechanism: Expand the arbitrary source state by its genuine finite grade projections, use state linearity and apply zeroMode_homogeneous to each projection.

**Theorem 1.8 (zeroMode_circle).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_circle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zeroMode_circle (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

    (p : ℕ) (a b : Carrier D) (ha : a ∈ grade D (p : ℤ)) :

    zeroMode J hD (Lattice.NormFourZhuFinite.circle D p a b) = 0

Proof mechanism: Decompose only the unrestricted second source argument into its actual finite nonnegative energy pieces. On each piece, actual source grading identifies all zero-mode indices and the imported circle_residue_top applied to module_fullLaw kills the circle sum on Top.

**Theorem 1.9 (zhuO_le_kernel).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zhuO_le_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zhuO_le_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zhuO_le_kernel (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :

    Lattice.ActualZhuFinite.zhuO D ≤ LinearMap.ker (zeroMode J hD)

Proof mechanism: Apply span_le to EVERY literal original circle generator and use zeroMode_circle. This kills the full actual source O-space, not a finite proxy.

**Theorem 1.10 (zeroMode_star).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_star`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zeroMode_star (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a b : Carrier D) :

    zeroMode J hD (star D a b) = zeroMode J hD a * zeroMode J hD b

Proof mechanism: Expand BOTH arbitrary source arguments by their actual finite energy projections. The imported star_residue_top with module_fullLaw proves multiplicativity on each homogeneous pair; finite sum multiplication and source linearity reassemble both original arguments.

**Theorem 1.11 (zeroMode_vacuum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem zeroMode_vacuum (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :

    zeroMode J hD (vacuum D) = 1

Proof mechanism: The actual vacuum has grade zero; zeroMode_homogeneous and the derived vacuum mode at -1 give the identity on Top.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.representation

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def representation (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :

    letI := Lattice.ActualZhuAlgebra.quotientRing D hD

    letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD

    Lattice.ActualZhuAlgebra.Q D →ₐ[ℂ] Module.End ℂ (Top J) := by

  letI := Lattice.ActualZhuAlgebra.quotientRing D hD

  letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD

  let f := (Lattice.ActualZhuFinite.zhuO D).liftQ (zeroMode J hD) (zhuO_le_kernel J hD)

  apply AlgHom.ofLinearMap f

  · exact zeroMode_vacuum J hD

  · intro x y

    obtain ⟨a, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective x

    obtain ⟨b, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective y

    change f (Lattice.ActualZhuAlgebra.quotientProduct D hD _ _) = _

    rw [Lattice.ActualZhuAlgebra.quotientProduct_mk]

    exact zeroMode_star J hD a b

Construction and use: Use the actual zhuO.liftQ with the proved full kernel inclusion. AlgHom.ofLinearMap uses the proved vacuum identity and arbitrary-state star multiplicativity, with the EXISTING Q, quotientProduct, quotientRing and quotientAlgebra.

**Theorem 1.12 (representation_mk).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem representation_mk (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (w : Top J) :

    (representation J hD ((Lattice.ActualZhuFinite.zhuO D).mkQ a) w).val =

      mode J a (h - 1) w.val

Proof mechanism: The quotient lift evaluates the homogeneous representative through zeroMode_homogeneous, retaining the original mode h-1.

**Theorem 1.13 (representation_mk_finite).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem representation_mk_finite (J : FullJacobiLatticeModule D M)

    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Carrier D) (w : Top J) :

    (representation J hD ((Lattice.ActualZhuFinite.zhuO D).mkQ a) w).val =

      ∑ h ∈ stateEnergies D a, mode J (gradeProjection D h a) (h - 1) w.val

Proof mechanism: The quotient lift evaluates arbitrary mixed-energy representatives through the genuine finite source projections in zeroMode_finite.

Original local instance (authored inventory entry, not a public theorem):

local instance : Ring (Lattice.ActualZhuAlgebra.Q D) :=

  Lattice.ActualZhuAlgebra.quotientRing D hPos.out

This reuses the existing quotient structure under hPos; it is retained in place in the mathematical suffix and in the exact native identity map.

Original local instance (authored inventory entry, not a public theorem):

local instance : Algebra ℂ (Lattice.ActualZhuAlgebra.Q D) :=

  Lattice.ActualZhuAlgebra.quotientAlgebra D hPos.out

This reuses the existing quotient structure under hPos; it is retained in place in the mathematical suffix and in the exact native identity map.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.currentZero

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted def:

def currentZero (i : Fin D.rank) : Module.End ℂ (Top J) :=

  homogeneousZero J hPos.out 1

    ⟨FullJacobiCurrentTransport.currentState D i, currentState_mem_grade i⟩

Construction and use: Restrict the actual source-current zero mode to Top by the already proved grade-one stability; use the explicit positive source Gram hypothesis from hPos.

**Theorem 1.14 (currentZero_apply).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem currentZero_apply (i : Fin D.rank) (w : Top J) :

    (currentZero J i w).val = current J i 0 w.val

Proof mechanism: Unfold the grade-one restriction, whose underlying mode is current J i 0.

**Theorem 1.15 (representation_H).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_H`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem representation_H (i : Fin D.rank) :

    representation J hPos.out (H D i) = currentZero J i

Proof mechanism: Represent the actual Zhu current class by its actual grade-one source current; representation_mk and currentState_eq_actual identify its action with currentZero.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.currentRepresentation

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted def:

def currentRepresentation : currentAlgebra D →ₐ[ℂ] Module.End ℂ (Top J) :=

  (representation J hPos.out).comp (currentAlgebra D).val

Construction and use: Restrict the genuine quotient AlgHom along the existing currentAlgebra inclusion.

**Theorem 1.16 (currentRepresentation_generator).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentRepresentation_generator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentRepresentation_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem currentRepresentation_generator (i : Fin D.rank) :

    currentRepresentation J (currentGenerator D i) = currentZero J i

Proof mechanism: Use representation_H on the existing current-algebra generator.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.coordinateProjectorAction

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted def:

def coordinateProjectorAction (i : Fin D.rank) (j : Node D i) : Module.End ℂ (Top J) :=

  currentRepresentation J (coordinateProjector D i j)

Construction and use: Apply the genuine currentRepresentation to the EXISTING source coordinate projector.

**Theorem 1.17 (coordinateProjectorAction_sum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem coordinateProjectorAction_sum (i : Fin D.rank) :

    ∑ j : Node D i, coordinateProjectorAction J i j = 1

Proof mechanism: Apply the unital algebra homomorphism to the source coordinate_sum identity and preserve its finite sum.

**Theorem 1.18 (coordinateProjectorAction_eigen).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem coordinateProjectorAction_eigen (i : Fin D.rank) (j : Node D i) :

    currentZero J i * coordinateProjectorAction J i j =

      (node D i j : ℂ) • coordinateProjectorAction J i j

Proof mechanism: Map the existing source coordinate_eigen identity through the algebra homomorphism and identify its generator action with currentZero.

**Theorem 1.19 (currentZero_coordinate_resolution).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_coordinate_resolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_coordinate_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem currentZero_coordinate_resolution (i : Fin D.rank) :

    currentZero J i = ∑ j : Node D i,

      (node D i j : ℂ) • coordinateProjectorAction J i j

Proof mechanism: Multiply the coordinate-projector sum equal to one by currentZero and use coordinateProjectorAction_eigen termwise.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.projectorAction

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted def:

def projectorAction (r : Grid D) : Module.End ℂ (Top J) :=

  currentRepresentation J (projector D r)

Construction and use: Apply the genuine currentRepresentation to the EXISTING finite-grid source projector.

**Theorem 1.20 (projectorAction_sum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem projectorAction_sum : ∑ r : Grid D, projectorAction J r = 1

Proof mechanism: Map the existing finite source projector_sum through the unital algebra homomorphism.

**Theorem 1.21 (projectorAction_eigen).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem projectorAction_eigen (r : Grid D) (i : Fin D.rank) :

    currentZero J i * projectorAction J r =

      (gridWeight D r i : ℂ) • projectorAction J r

Proof mechanism: Map the existing source projector_eigen through the genuine currentRepresentation and use its actual current-generator identification.

**Theorem 1.22 (projectorAction_survives).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_survives`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_survives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem projectorAction_survives (r : Grid D) (hr : projectorAction J r ≠ 0) :

    AllAlpha D (gridWeight D r)

Proof mechanism: If the source projector were zero its action would be zero, contradicting hr; then the existing projector_survives gives AllAlpha. Only nonzero images force source survival; faithfulness is never used.

D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation.jointEigenspace

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted def:

def jointEigenspace (r : Grid D) : Submodule ℂ (Top J) :=

  ⨅ i : Fin D.rank, (currentZero J i).eigenspace (gridWeight D r i : ℂ)

Construction and use: Intersect the actual restricted currentZero ordinary eigenspaces INSIDE Top at the finite source grid weight.

**Theorem 1.23 (projectorAction_mem_joint).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_mem_joint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_mem_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem projectorAction_mem_joint (r : Grid D) (w : Top J) :

    projectorAction J r w ∈ jointEigenspace J r

Proof mechanism: Evaluate projectorAction_eigen on w and use the ordinary eigenspace membership characterization for each current coordinate.

**Theorem 1.24 (sum_projectorAction).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.sum_projectorAction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.sum_projectorAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem sum_projectorAction (w : Top J) : ∑ r : Grid D, projectorAction J r w = w

Proof mechanism: Evaluate the finite endomorphism sum equal to one on the arbitrary Top vector.

**Theorem 1.25 (finite_joint_current_decomposition).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.finite_joint_current_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.finite_joint_current_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (J : FullJacobiLatticeModule D M)

variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]

Exact accepted theorem:

theorem finite_joint_current_decomposition (w : Top J) :

    ∃ v : Grid D → Top J,

      (∑ r : Grid D, v r) = w ∧

      (∀ r, v r ∈ jointEigenspace J r) ∧

      (∀ r (i : Fin D.rank),

        current J i 0 (v r).val = (gridWeight D r i : ℂ) • (v r).val) ∧

      (∀ r, v r ≠ 0 → AllAlpha D (gridWeight D r)) ∧

      (∀ i : Fin D.rank, current J i 0 w.val = ∑ j : Node D i,

        (node D i j : ℂ) • (coordinateProjectorAction J i j w).val)

Proof mechanism: Choose v(r)=projectorAction J r w. The sum identity recovers w, each component lies in every joint current eigenspace, the original M-valued current equation follows by subtype evaluation, nonzero components force nonzero action and hence AllAlpha, and the coordinate resolution supplies the last asserted formula.

The exact accepted source SHA256 is 1a7a596f44ee6882716c5edfcf094904e154ed4652dd04f20a78d3841125420a. This canonical delivery preserves the selected 39 authored declarations/local instances and all 88 native objects, including generated declarations. Original comments and supplier attribution remain byte-for-byte in the preserved suffix; no literature or novelty claim is added. The canonical Lean report checks exact statements and permitted axiom closures; make emit produces the Blueprint and the canonical writer produces frozen state. The source-bound four-slot audit is unfinished for all 25 public theorems: https://github.com/the-omega-institute/trureturing/issues/29518. The existing typed API attempt lacks variation, sensitivity and dependence. No Contract registration, enrollment or declared_validated status is claimed; the unenrolled sourceScope stub and failed attempt are excluded from the canonical tree. No unconditional all-weak-module nilpotence, nonzero or generating Top, Top=positive-current vacuum, full charged module classification, category/fusion realization, string theory or AdS/CFT completion follows. The global objective remains active and incomplete.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.coordinateProjectorAction_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentRepresentation_generator`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_eq_actual`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentState_mem_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.currentZero_coordinate_resolution`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.finite_joint_current_decomposition`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.homogeneous_zero_preserves_top`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.module_fullLaw`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_mem_joint`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.projectorAction_survives`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_H`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.representation_mk_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.sum_projectorAction`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.top_le_positiveCurrentVacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_circle`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_star`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zeroMode_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation.zhuO_le_kernel`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors](../Lattice/ActualZhuSourceProjectors.md)
- Dependency: [D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport](FullJacobiCurrentTransport.md)
