# The literal original all-charge relative mass shell

## Abstract

The literal original all-charge relative mass shell

D:LatticeData has arbitrary natural rank, including zero, an integral symmetric Gram matrix with even diagonal, and Charge D = Fin D.rank -> Int. Index D = Fin D.rank x Nat and Exponent D = Index D ->_0 Nat. Carrier D is the original finitely supported charge sum of complex multivariate polynomials. The full state space is exactly LatticeMatterGhostCoupling.State D = Carrier D tensor[Complex] CountableOccupationFock.Fock; no finite truncation replaces it.

Write q_D(a)=chargeEnergy D a = bilinear D a a / 2 in Int and w(d)=oscillatorEnergy d=sum_x (x.2+1)*d(x) in Nat. A tensor label i=((a,d),S) denotes single(a,monomial(d,1)) tensor ket S. Its actual total zero-mode eigenvalue is q_D(a)+w(d)+E(S), where E is the unshifted original ghost energy. Only the displayed operator results require H:Matrix (Fin D.rank) (Fin D.rank) Complex with hHG:H*gramComplex D=1 and hGH:gramComplex D*H=1. No Gram positivity, positive rank, nonzero charge or charge-energy-one condition is imposed.

The original operator identities are matterMode D H r=TensorProduct.map (sugawaraMode D H r) id, ghostVirasoro D r=TensorProduct.map id (BcGhostVirasoro.L r), and ghostB D r=TensorProduct.map id (BcGhostFock.b r). totalL0 D H is literally matterMode D H 0+ghostVirasoro D 0. totalCharge D H is the existing T D H plus ghostCharge D, where T is the locally finite original matter/ghost coupling and ghostCharge is the lifted original cubic charge.

The shell at ANY a:Charge D is (fixedMomentum D a intersect ker(ghostB D 0)) intersect ker(totalL0 D H). Under the two inverse identities, it consists exactly of original coefficients with charge a, 3 not in S, and w(d)+R(S)=1-q_D(a) in Int. Its basis is the corresponding subset of the original tensor basis, not a postulated finite model. The exact telescopes below include all premises; finiteness of ShellIndex itself requires neither H nor the inverse identities.

The cutoff N=(1-q_D(a)).toNat works also when q_D(a) is negative. Every nonzero shell coefficient has w(d)<=N and S subset range(2*N+4). If q_D(a)>1 there are no allowed labels and the actual shell is the zero submodule; at q_D(a)=1 the level-zero branch remains. At a=0, q_D(0)=0 and N=1, so zero charge is explicitly included without a positive-Gram assumption. The finite basis and support proofs concern each fixed charge, not a simultaneous finite bound on all lattice charges.

The actual totalCharge preserves fixed momentum by sector preservation of the original summands and preserves both literal kernels using the original zero-mode Ward and covariance identities. At rank 26, the existing LatticeBRST.total_square_anomaly gives totalCharge D H squared equal to zero under the same inverse identities; this is an application of that general theorem, not a separately delivered nilpotence theorem. The preserved finite shell can therefore carry the restricted charge, but this module makes no cohomology, contraction or no-ghost conclusion.

No isometry or stability conclusion is assumed. There is no positivity or positive-Gram claim, including at zero charge, and no full no-ghost, BRST/string, Monster/moonshine, VOA/CFT, anomalies/fusion or AdS completion claim. The exact original-carrier identifications and finite-shell deductions are repo-derived and make no claim of literature novelty.

Registration audit is unfinished for all 43 retained public theorems: https://github.com/the-omega-institute/trureturing/issues/25750. Completed registrations: 0; no declared_validated registration is claimed. The three excluded unconsumed research companions retain their exact statements and proofs in the pinned pre-repair native evidence linked by that issue.

**Definition 1.1 (TensorLabel).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.TensorLabel`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.TensorLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A label consists of the original integer charge, original polynomial exponent and original finite ghost occupation.

Exact Lean telescope: abbrev TensorLabel (D : LatticeData)

**Definition 1.2 (tensorBasis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the tensor product of the original carrier monomial basis and the original occupation ket basis.

Exact Lean telescope: def tensorBasis (D : LatticeData) : Module.Basis (TensorLabel D) ℂ (State D)

**Definition 1.3 (tensorCoeffEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorCoeffEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representation map of the actual tensor basis gives a linear equivalence to finitely supported tensor-label coefficients.

Exact Lean telescope: def tensorCoeffEquiv (D : LatticeData) : State D ≃ₗ[ℂ] (TensorLabel D →₀ ℂ)

**Definition 1.4 (coeff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is evaluation of the actual tensor-basis representation at a label.

Exact Lean telescope: def coeff (D : LatticeData) (x : State D) (i : TensorLabel D) : ℂ

**Theorem 1.5 (tensorBasis_apply).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis vector is literally single(a,monomial(d,1)) tensor ket S on the original State D.

Exact Lean telescope: @[simp] theorem tensorBasis_apply (D : LatticeData) (i : TensorLabel D) : tensorBasis D i = Finsupp.single i.1.1 (MvPolynomial.monomial i.1.2 1) ⊗ₜ[ℂ] ket i.2

**Theorem 1.6 (coeff_tmul).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an arbitrary simple tensor the actual coefficient is the product of the original carrier coefficient and the original Fock coefficient.

Exact Lean telescope: theorem coeff_tmul (D : LatticeData) (v : Carrier D) (w : Fock) (i : TensorLabel D) : coeff D (v ⊗ₜ[ℂ] w) i = carrierCoeffEquiv D v i.1 * w i.2

**Theorem 1.7 (coeff_tmul_original).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul_original`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In charge-polynomial coordinates this product is precisely (v a).coeff d times w S.

Exact Lean telescope: theorem coeff_tmul_original (D : LatticeData) (v : Carrier D) (w : Fock) (a : Charge D) (d : Exponent D) (S : Finset ℕ) : coeff D (v ⊗ₜ[ℂ] w) ((a,d),S) = (v a).coeff d * w S

**Theorem 1.8 (ghostB_zero_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ghostB_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ghostB_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions identify the kernel of the actual tensor b(0): exactly the coefficients whose ghost occupations contain site 3 vanish. Ghost slices transfer the original Fock kernel theorem without postulating a relative tensor space.

Exact Lean telescope: theorem ghostB_zero_iff (D : LatticeData) (x : State D) : ghostB D 0 x = 0 ↔ ∀ i : TensorLabel D, 3 ∈ i.2 → coeff D x i = 0

**Definition 1.9 (totalEnergy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer eigenvalue is original matter energy plus unshifted original ghost energy.

Exact Lean telescope: def totalEnergy (D : LatticeData) (i : TensorLabel D) : ℤ

**Definition 1.10 (totalL0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This abbreviation is exactly matterMode D H 0 + ghostVirasoro D 0 on State D; it is not a coefficient-defined replacement operator.

Exact Lean telescope: abbrev totalL0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D)

**Theorem 1.11 (totalL0_basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original matter zero-mode theorem and original all-integer ghost calculation prove the actual tensor-basis eigenformula under the two displayed inverse-Gram identities.

Exact Lean telescope: theorem totalL0_basis (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (i : TensorLabel D) : totalL0 D H (tensorBasis D i) = (totalEnergy D i : ℂ) • tensorBasis D i

**Theorem 1.12 (totalL0_coeff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tensor induction proves the all-state coefficient formula for the literal sum of actual zero modes, including nonhomogeneous tensors.

Exact Lean telescope: theorem totalL0_coeff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) (i : TensorLabel D) : coeff D (totalL0 D H x) i = (totalEnergy D i : ℂ) * coeff D x i

**Theorem 1.13 (totalL0_zero_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient separation proves both directions of the kernel criterion: every nonzero original tensor coefficient has totalEnergy zero.

Exact Lean telescope: theorem totalL0_zero_iff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) : totalL0 D H x = 0 ↔ ∀ i : TensorLabel D, coeff D x i ≠ 0 → totalEnergy D i = 0

**Definition 1.14 (fixedMomentum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the inverse image of coefficient support at charge a under the original tensor representation; it imposes no oscillator cutoff.

Exact Lean telescope: def fixedMomentum (D : LatticeData) (a : Charge D) : Submodule ℂ (State D)

**Theorem 1.15 (mem_fixedMomentum_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_fixedMomentum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_fixedMomentum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient at a different original integer charge vanishes, for an arbitrary actual state.

Exact Lean telescope: theorem mem_fixedMomentum_iff (D : LatticeData) (a : Charge D) (x : State D) : x ∈ fixedMomentum D a ↔ ∀ i : TensorLabel D, i.1.1 ≠ a → coeff D x i = 0

**Theorem 1.16 (fixedMomentum_eq_span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-charge space is the span of the full original tensor basis restricted only by its charge coordinate.

Exact Lean telescope: theorem fixedMomentum_eq_span (D : LatticeData) (a : Charge D) : fixedMomentum D a = Submodule.span ℂ (tensorBasis D '' {i : TensorLabel D | i.1.1 = a})

**Theorem 1.17 (totalCharge_mem_fixedMomentum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_fixedMomentum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_fixedMomentum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sector preservation of each original Sugawara summand and of the lifted ghost charge proves that the actual totalCharge preserves fixedMomentum for every D,H,a; no inverse-Gram premise is required for this sector statement.

Exact Lean telescope: theorem totalCharge_mem_fixedMomentum (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) {x : State D} (hx : x ∈ fixedMomentum D a) : totalCharge D H x ∈ fixedMomentum D a

**Definition 1.18 (relativeMassShell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The submodule is literally (fixedMomentum D a intersect ker(ghostB D 0)) intersect ker(totalL0 D H), inside the full infinite original tensor carrier.

Exact Lean telescope: def relativeMassShell (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) : Submodule ℂ (State D)

**Theorem 1.19 (mem_relativeMassShell_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_relativeMassShell_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_relativeMassShell_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions hold for every actual state: each nonzero coefficient has charge a, excludes ghost site 3 and obeys oscillatorEnergy(d)+relativeEnergy(S)=1-chargeEnergy(D,a) as an integer equality.

Exact Lean telescope: theorem mem_relativeMassShell_iff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) (x : State D) : x ∈ relativeMassShell D H a ↔ ∀ i : TensorLabel D, coeff D x i ≠ 0 → i.1.1 = a ∧ 3 ∉ i.2 ∧ (oscillatorEnergy i.1.2 : ℤ) + relativeEnergy i.2 = 1 - chargeEnergy D a

**Theorem 1.20 (totalCharge_mem_relativeMassShell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_relativeMassShell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_relativeMassShell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed-momentum preservation, total_ward_b D H 0 and total_covariance D H hHG hGH 0 prove preservation of the actual intersection by the actual totalCharge. There is no assumed stability or isometry premise, and rank 26 is not required for stability.

Exact Lean telescope: theorem totalCharge_mem_relativeMassShell (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) {x : State D} (hx : x ∈ relativeMassShell D H a) : totalCharge D H x ∈ relativeMassShell D H a

**Definition 1.21 (allowedLabels).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.allowedLabels`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.allowedLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The allowed labels impose exactly the original charge, the site-3 exclusion and the integer shell equation. Finiteness is proved later and is not encoded as a premise.

Exact Lean telescope: def allowedLabels (D : LatticeData) (a : Charge D) : Set (TensorLabel D)

**Definition 1.22 (ShellIndex).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ShellIndex`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ShellIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This subtype consists of exactly the allowed original tensor labels.

Exact Lean telescope: abbrev ShellIndex (D : LatticeData) (a : Charge D)

**Theorem 1.23 (relativeMassShell_eq_supported).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_supported`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal kernel intersection equals the inverse image of coefficients supported on allowedLabels under the actual tensor representation.

Exact Lean telescope: theorem relativeMassShell_eq_supported (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) : relativeMassShell D H a = (Finsupp.supported ℂ ℂ (allowedLabels D a)).comap (tensorCoeffEquiv D).toLinearMap

**Theorem 1.24 (relativeMassShell_eq_span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual relative shell equals the span of the allowed original tensor basis vectors, in both directions.

Exact Lean telescope: theorem relativeMassShell_eq_span (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) : relativeMassShell D H a = Submodule.span ℂ (tensorBasis D '' allowedLabels D a)

**Definition 1.25 (shellCoeffEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellCoeffEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A genuine linear equivalence identifies the actual kernel intersection with finitely supported complex coefficients on ShellIndex D a.

Exact Lean telescope: def shellCoeffEquiv (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) : relativeMassShell D H a ≃ₗ[ℂ] (ShellIndex D a →₀ ℂ)

**Definition 1.26 (shellBasis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient equivalence constructs an actual basis of the original relative kernel intersection.

Exact Lean telescope: def shellBasis (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) : Module.Basis (ShellIndex D a) ℂ (relativeMassShell D H a)

**Theorem 1.27 (shellBasis_coe).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis_coe`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every shell basis vector, when coerced into the original State D, is exactly the corresponding original tensor basis vector.

Exact Lean telescope: theorem shellBasis_coe (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) (i : ShellIndex D a) : (shellBasis D H hHG hGH a i : State D) = tensorBasis D i.1

**Definition 1.28 (massShellCutoff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural cutoff is exactly (1-chargeEnergy D a).toNat, for every integer charge including zero and negative charge energy.

Exact Lean telescope: def massShellCutoff (D : LatticeData) (a : Charge D) : ℕ

**Theorem 1.29 (massShellCutoff_cast).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff_cast`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When chargeEnergy D a is at most one, the natural cutoff casts back to precisely 1-chargeEnergy D a in Int.

Exact Lean telescope: theorem massShellCutoff_cast (D : LatticeData) (a : Charge D) (ha : chargeEnergy D a ≤ 1) : (massShellCutoff D a : ℤ) = 1 - chargeEnergy D a

**Theorem 1.30 (relativeMassShell_eq_bot_of_one_lt).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_bot_of_one_lt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_bot_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If chargeEnergy D a is greater than one, nonnegative oscillator and relative ghost energies make the actual shell the zero submodule. A zero natural cutoff alone is not substituted for this empty-shell proof.

Exact Lean telescope: theorem relativeMassShell_eq_bot_of_one_lt (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) (ha : 1 < chargeEnergy D a) : relativeMassShell D H a = ⊥

**Theorem 1.31 (coefficient_support_bound).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coefficient_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coefficient_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero original coefficient of a shell state has charge a, oscillatorEnergy at most the prescribed cutoff and ghost occupation contained in range(2*cutoff+4).

Exact Lean telescope: theorem coefficient_support_bound (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H a) (i : TensorLabel D) (hi : coeff D x i ≠ 0) : i.1.1 = a ∧ oscillatorEnergy i.1.2 ≤ massShellCutoff D a ∧ i.2 ⊆ Finset.range (2 * massShellCutoff D a + 4)

**Theorem 1.32 (shellIndex_finite).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellIndex_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellIndex_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finiteness is proved without H or a sign condition on the Gram form: allowed labels inject into the finite oscillator sublevel times a finite powerset. If charge energy is greater than one, the index subtype is empty. The ghost bound uses relative_level_support with a proved RelativeLevel premise for each ket.

Exact Lean telescope: theorem shellIndex_finite (D : LatticeData) (a : Charge D) : Finite (ShellIndex D a)

**Theorem 1.33 (relativeMassShell_finiteDimensional).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_finiteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed finite original tensor basis proves finite dimensionality for every fixed integer charge under only the two actual inverse-Gram hypotheses.

Exact Lean telescope: theorem relativeMassShell_finiteDimensional (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Charge D) : FiniteDimensional ℂ (relativeMassShell D H a)

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ShellIndex`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.TensorLabel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.allowedLabels`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coeff_tmul_original`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.coefficient_support_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.fixedMomentum_eq_span`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.ghostB_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.massShellCutoff_cast`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_fixedMomentum_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.mem_relativeMassShell_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_bot_of_one_lt`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_span`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_eq_supported`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.relativeMassShell_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellBasis_coe`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.shellIndex_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorBasis_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.tensorCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_fixedMomentum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalCharge_mem_relativeMassShell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell.totalL0_zero_iff`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy](../../Quantum/Fermionic/BcGhostRelativeEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling](LatticeMatterGhostCoupling.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
