# LatticeSugawaraNullFrameEndpoints

## Abstract

LatticeSugawaraNullFrameEndpoints

Actual Sugawara finite capture endpoints on the original matter tensor occupation bc carrier. The absent endpoint at k=n is proved zero on the actual input when it lies outside the asymmetric interval. For every nonzero n, both endpoints yield the original charge momentum current; at n=0, the one endpoint yields the exact integral charge energy. The finite interior shifts signed degree by plus one after the original c mode. Actual fixed-charge quadratic remainders and nonzero leading-subtracted modes strictly raise. An arbitrary finite set of modes, with its genuine zero energy endpoint subtracted and the actual locally finite ghost cubic included, raises degree; so does its product with the genuine quartet homotopy. The fixed-charge input hypothesis is essential. The capture is input-dependent, not a uniform finite endomorphism identity.

Full BRST matter-mode capture and assembly into Q minus d0, relative b0 and total-L0 zero-mode cancellation, preservation and bounds of the literal physical shell, full h delta strict raising, rank-26 nilpotence, HPL, cohomology, no-ghost, true Vnatural, strings and AdS/CFT remain unproved here. Original shell59141 is not imported or assumed. Native compilation proves only the exact Lean statements. Earlier provider audit limitations are linked at https://github.com/the-omega-institute/trureturing/issues/25604. That issue preserves all 39 original quartet obligations and names all 107 current retained filtration/Sugawara targets with exact canonical statement, source, type and binding identities: 146 unique unfinished audits, zero declared_validated. All seven original-family/source-selection, reconstruction, realization, whole-family variation, role/anchor sensitivity and observational-dependence evidence gaps remain unresolved. New registrations carry whole-theorem bridges but assertion-valued diagnostic attempts lack faithful operand selection and reconstruction. No declared_validated status, escape certificate or admission is claimed; actual unclassified diagnostics are collected in the scoped report for root review.

**Theorem 1.1 (zero_mem_capture).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mem_capture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mem_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (v : Carrier D) : 0 ∈ capture n v

**Theorem 1.2 (mode_mem_capture_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mode_mem_capture_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mode_mem_capture_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (n : ℤ) (v : Carrier D) : n ∈ capture n v ↔ n ≤ (vectorFrequencyBound D v : ℤ)

**Theorem 1.3 (mem_interior).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mem_interior`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mem_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {n k : ℤ} {v : Carrier D} (hk : k ∈ interior n v) : k ∈ capture n v ∧ k ≠ 0 ∧ n-k ≠ 0

**Theorem 1.4 (absent_endpoint_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.absent_endpoint_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.absent_endpoint_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) (v : Carrier D) (hn : n ∉ capture n v) : weightedNormal H n n v = 0

**Theorem 1.5 (weighted_interval).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interval`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) (v : Carrier D) : sugawaraMode D H n v = (2 : ℂ)⁻¹ • ∑ k ∈ capture n v, weightedNormal H n k v

**Theorem 1.6 (extract_nonzero_endpoints).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_nonzero_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_nonzero_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) (hn : n ≠ 0) (v : Carrier D) : (∑ k ∈ capture n v, weightedNormal H n k v) = weightedNormal H n 0 v + weightedNormal H n n v + ∑ k ∈ interior n v, weightedNormal H n k v

**Theorem 1.7 (extract_zero_endpoint).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_zero_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_zero_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D) : (∑ k ∈ capture 0 v, weightedNormal H 0 k v) = weightedNormal H 0 0 v + ∑ k ∈ interior 0 v, weightedNormal H 0 k v

**Theorem 1.8 (weighted_endpoint_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (P : Oscillator D) : weightedNormal H n 0 (Finsupp.single p P) = a (chargeVector p) n (Finsupp.single p P)

**Theorem 1.9 (weighted_endpoint_mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (p : Charge D) (n : ℤ) (P : Oscillator D) : weightedNormal H n n (Finsupp.single p P) = a (chargeVector p) n (Finsupp.single p P)

**Theorem 1.10 (charge_pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.charge_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.charge_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) : g D (chargeVector p) (chargeVector p) = (bilinear D p p : ℂ)

**Theorem 1.11 (half_charge_pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.half_charge_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.half_charge_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (p : Charge D) : (2 : ℂ)⁻¹ * g D (chargeVector p) (chargeVector p) = (LatticePositiveEnergy.chargeEnergy D p : ℂ)

**Theorem 1.12 (nonzero_mode_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.nonzero_mode_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.nonzero_mode_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (hn : n ≠ 0) (P : Oscillator D) : sugawaraMode D H n (Finsupp.single p P) = a (chargeVector p) n (Finsupp.single p P) + interiorOperator H n (Finsupp.single p P) (Finsupp.single p P)

**Theorem 1.13 (zero_mode_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mode_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mode_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (P : Oscillator D) : sugawaraMode D H 0 (Finsupp.single p P) = (LatticePositiveEnergy.chargeEnergy D p : ℂ) • Finsupp.single p P + interiorOperator H 0 (Finsupp.single p P) (Finsupp.single p P)

**Theorem 1.14 (remainder_eq_interior_on_sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.remainder_eq_interior_on_sector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.remainder_eq_interior_on_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (P : Oscillator D) : (sugawaraMode D H n - endpoint p n) (Finsupp.single p P) = interiorOperator H n (Finsupp.single p P) (Finsupp.single p P)

**Theorem 1.15 (weighted_interior_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interior_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interior_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (n k q : ℤ) (hk : k ≠ 0) (hl : n-k ≠ 0) : Shift (actualBasis F B) degree (tp (weightedNormal H n k) (c q)) 1

**Theorem 1.16 (finite_interior_c_shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finite_interior_c_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finite_interior_c_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (n : ℤ) (v : Carrier D) : Shift (actualBasis F B) degree (tp (interiorOperator H n v) (c (-n))) 1

**Theorem 1.17 (original_remainder_basis_action).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_basis_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_basis_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (m : Exponents t) (S : Finset ℕ) : let v : Carrier D := Finsupp.single p ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)) tp (sugawaraMode D H n - endpoint p n) (c (-n)) (actualBasis F B (⟨p,m⟩,S)) = tp (interiorOperator H n v) (c (-n)) (actualBasis F B (⟨p,m⟩,S))

**Theorem 1.18 (original_remainder_fixed_charge_degree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_fixed_charge_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_fixed_charge_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr (tp (sugawaraMode D H n - endpoint p n) (c (-n)) (actualBasis F B i)) j ≠ 0) : degree j = degree i + 1

**Theorem 1.19 (quadratic_minus_momentum_fixed_charge_degree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr (tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n)) (actualBasis F B i)) j ≠ 0) : degree j = degree i + 1

**Theorem 1.20 (quadratic_minus_momentum_fixed_charge_raises).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_raises`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_raises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr (tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n)) (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j

**Theorem 1.21 (sugawara_minus_leading_fixed_charge_raises).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.sugawara_minus_leading_fixed_charge_raises`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.sugawara_minus_leading_fixed_charge_raises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr ((tp (sugawaraMode D H n) (c (-n)) - F.pPlus p • tp (a F.eMinus n) (c (-n))) (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j

**Theorem 1.22 (finiteRemainder_fixed_charge_raises).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finiteRemainder_fixed_charge_raises`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finiteRemainder_fixed_charge_raises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (modes : Finset ℤ) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr (finiteRemainder F H p modes (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j

**Theorem 1.23 (h_finiteRemainder_fixed_charge_raises).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.h_finiteRemainder_fixed_charge_raises`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.h_finiteRemainder_fixed_charge_raises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) (modes : Finset ℤ) (i j : StateIndex D t) (hi : i.1.1 = p) (hc : (actualBasis F B).repr ((h F B p * finiteRemainder F H p modes) (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.absent_endpoint_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.charge_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_nonzero_endpoints`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.extract_zero_endpoint`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finiteRemainder_fixed_charge_raises`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.finite_interior_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.h_finiteRemainder_fixed_charge_raises`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.half_charge_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mem_interior`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.mode_mem_capture_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.nonzero_mode_split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_basis_action`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.original_remainder_fixed_charge_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.quadratic_minus_momentum_fixed_charge_raises`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.remainder_eq_interior_on_sector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.sugawara_minus_leading_fixed_charge_raises`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_endpoint_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interior_c_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.weighted_interval`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mem_capture`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints.zero_mode_split`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration](LatticeBRSTModeFiltration.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame](LatticeSugawaraNullFrame.md)
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](../LatticePositiveEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](../LatticeSugawaraVirasoro.md)
