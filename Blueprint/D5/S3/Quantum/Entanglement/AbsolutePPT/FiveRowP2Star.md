# FiveRowP2Star

## Abstract

The complete independently labelled five-row Bell family supplies a balanced vector and a common tail placement. The same vector controls both head and tail charges, including zero entries and ties.

The complete independently labelled five-row Bell family supplies a balanced vector and a common tail placement. The same vector controls both head and tail charges, including zero entries and ties.

**Definition 1.1 (family).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def family (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (π : Edge 5 ≃ Fin 10) (σ : BottomSlot 5 ≃ Fin 15) : Matrix (Fin 5) (Fin 5) ℝ

**Definition 1.2 (FullPSD).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.FullPSD`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.FullPSD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def FullPSD (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) : Prop

**Theorem 1.3 (family mass budget).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_mass_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_mass_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem family_mass_budget (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (hf : FullPSD u v h d) : (∑ i,h i)+(∑ i,d i) ≤ 5*u-10*v

**Definition 1.4 (balanced).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balanced`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def balanced (p : Fin 4 → ℝ) : Fin 5 → ℝ

**Definition 1.5 (coefficient).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.coefficient`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def coefficient (p : Fin 4 → ℝ) : Fin 15 → ℝ

**Theorem 1.6 (five coefficient mass).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.five_coefficient_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.five_coefficient_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem five_coefficient_mass (p : Fin 4 → ℝ) (hp : ∀ i,0 ≤ p i) (ho : Antitone p) (hn : ∑ i,(p i)^2=1) : ∃ S : Finset (Fin 15), S.card=5 ∧ 5/2 ≤ ∑ i ∈ S,coefficient p i

**Theorem 1.7 (star polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem star_polynomial (delta B C : ℝ) : (6*delta^2+3*delta*B+C)^2- 9*delta^2*(4*delta^2+2*delta*B+B^2-2*C) = 18*delta^3*B+30*delta^2*C+6*delta*B*C+C^2

**Theorem 1.8 (star product bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem star_product_bound (delta B C P t : ℝ) (hd : 0 ≤ delta) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P) (ht : 0 ≤ t) (hPe : P=6*delta^2+3*delta*B+C) (hte : t^2=4*delta^2+2*delta*B+B^2-2*C) : 3*delta*t ≤ P

**Theorem 1.9 (star gain).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem star_gain (t R Q delta P : ℝ) (ht : 0 < t) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hd : 0 ≤ delta) (hQP : Q ≤ delta*R) (hP : 3*delta*t ≤ P) : Real.sqrt (t^2+Q) ≤ t+R*P/(6*t^2)

**Theorem 1.10 (capped tail squares).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.capped_tail_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.capped_tail_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem capped_tail_squares (u : ℝ) (d : Fin 15 → ℝ) (hu : 0 ≤ u) (hd : ∀ i,0 ≤ d i) (hdu : ∀ i,d i ≤ u) (ho : Antitone d) (hm : ∑ i,d i ≤ 5*u) : (∑ i,(d i)^2) ≤ u*(∑ i,if i.val < 5 then d i else 0)

**Definition 1.11 (CouplingWitness).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.CouplingWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.CouplingWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

structure CouplingWitness (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) where p : Fin 4 → ℝ p_nonneg : ∀ i,0 ≤ p i p_unit : ∑ i,(p i)^2=1 tail : BottomSlot 5 ≃ Fin 15 weights : (Edge 5 ≃ Fin 10) → ℝ weights_nonneg : ∀ π,0 ≤ weights π weights_sum : ∑ π,weights π=1 head_lower : Real.sqrt (∑ i,(v+h i)^2) ≤ ∑ π,weights π*(∑ e : Edge 5,2*(v+h (π e))*balanced p e.val.1*balanced p e.val.2) tail_lower : (∑ i,(d i)^2)/(2*u) ≤ (∑ i : Fin 5,2*d (tail (.inl i))*(balanced p i)^2)+ ∑ e : Edge 5,2*d (tail (.inr e))*balanced p e.val.1*balanced p e.val.2

**Theorem 1.12 (same vector coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.same_vector_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.same_vector_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem same_vector_coupling (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (hf : FullPSD u v h d) (w : CouplingWitness u v h d) : Real.sqrt (∑ i,(v+h i)^2)+(∑ i,(d i)^2)/(2*u) ≤ 2*u

**Definition 1.13 (BalancedStarExistenceGap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.BalancedStarExistenceGap`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.BalancedStarExistenceGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def BalancedStarExistenceGap : Prop

**Theorem 1.14 (balancedStarExistence).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balancedStarExistence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balancedStarExistence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem balancedStarExistence : BalancedStarExistenceGap

**Theorem 1.15 (family star charges).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_star_charges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_star_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem family_star_charges (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (hu : 0 < u) (hv : 0 ≤ v) (hh : ∀ i, 0 ≤ h i) (hd : ∀ i, 0 ≤ d i) (hdu : ∀ i, d i ≤ u) (hm : ∑ i, d i ≤ 5*u) (hf : FullPSD u v h d) : Real.sqrt (∑ i, (v+h i)^2) + (∑ i, (d i)^2)/(2*u) ≤ 2*u ∧ Real.sqrt (∑ i, (v+h i)^2) + (∑ i, d i)/5 ≤ 2*u

**Theorem 1.16 (family uniform subsets).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_uniform_subsets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_uniform_subsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem family_uniform_subsets (r : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (hf : FullPSD 1 r h d) : h 0 + (d 14+d 13+d 12) ≤ 2-r ∧ (h 0+h 1+h 2) + (d 14+d 13+d 12+d 11+d 10+d 9) ≤ 3-3*r ∧ (h 0+h 1+h 2+h 3+h 4+h 5) + (d 14+d 13+d 12+d 11+d 10+d 9+d 8+d 7+d 6+d 5) ≤ 4-6*r

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.BalancedStarExistenceGap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.CouplingWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.FullPSD`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balanced`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.balancedStarExistence`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.capped_tail_squares`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.coefficient`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_mass_budget`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_star_charges`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.family_uniform_subsets`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.five_coefficient_mass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.same_vector_coupling`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_gain`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_polynomial`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star.star_product_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar](FiveRowP2Scalar.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell](UniformSchmidtBell.md)
