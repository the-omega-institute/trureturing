# Uniform Dimension from Actual Cyclic Projectivity

## Abstract

The finite vector set and actual cyclic norms force the uniform dimension bound for elementary abelian groups over the prime field.

The theorem proves a lower bound for every prime and every rank using actual cyclic restrictions and Burnside counting on the vectors themselves. It makes no sharpness claim; a separate translation construction is outside this formal result.

**Theorem 1.1 (Every prime and every rank).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact public telescope (universe uV): (p r : ℕ) [Fact p.Prime] {V : Type uV} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Nontrivial V] (ρ : Representation (ZMod p) (Multiplicative (Fin r → ZMod p)) V) (hproj : ∀ H : Subgroup (Multiplicative (Fin r → ZMod p)), IsCyclic H → Module.Projective (ZMod p)[H] (Representation.asModule (ρ.comp H.subtype))) : r * p ≤ Module.finrank (ZMod p) V. Thus the hypothesis concerns every actual cyclic subgroup of the actual group, including the trivial subgroup. The vector-space universe is independent of the group universe. There is no faithfulness, local-freeness, splitting, prescribed Jordan form, determinant-pencil, or shifted-cyclic hypothesis.

Write d=finrank V. The private elementary_pow proves g^p=1 coordinatewise in the actual group. For g different from 1, Mathlib's orderOf_eq_prime gives orderOf g=p, and Fintype.card_zpowers gives |H|=p for H=zpowers g. Hence H is a p-group by IsPGroup.of_card. Projectivity on H feeds the necessary direction of PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective with a=1 and p=0 in ZMod p, supplying surjectivity of the actual unnormalised norm onto W=(ρ restricted to H).invariants.

The private cyclic_finrank restricts that norm's codomain by LinearMap.codRestrict. Every vector space over ZMod p is free and therefore projective as an ordinary field module. Module.projective_lifting_property lifts the identity of W through the surjective norm, giving a linear section L with norm(L(w))=w. The public PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section then supplies V linearly equivalent to (H → W). LinearEquiv.finrank_eq and Module.finrank_pi_fintype give d=p*finrank W. This uses the existing public norm equivalence and does not reprove its algebra or import private helpers from any other source.

The private vectorAction makes g act on the vector v by ρ(g)(v), so Burnside is applied to V itself. The private cyclic_mem_invariants_iff proves that W consists exactly of vectors fixed by g: the forward direction evaluates invariance at g, and the reverse direction uses Subgroup.zpowers_le to put H inside the vector's actual stabilizer. The private fixedBy_natCard constructs the resulting equivalence W ≃ MulAction.fixedBy V g. A finite basis supplies the required finite type, and Module.card_eq_pow_finrank with ZMod.card gives |fixedBy V g|=p^n whenever d=p*n. Cancellation of the positive p makes this n independent of the nonidentity element.

For r=0 the conclusion is 0≤d, proved directly. For r>0 the constant function with value 1 gives an actual nonidentity element g₀, witnessed by evaluation at an index of Fin r. Set n=finrank of its cyclic invariant space. The preceding argument gives d=p*n. Nontrivial V implies d>0, hence n>0. Thus no positive-rank argument assumes a nonidentity element exists when r=0, and no positivity is inferred for the zero vector space.

A finite basis makes the actual underlying vector set finite, with |V|=p^d. Its identity fixed set is all of V. Every other group element has fixed-set size p^n. Erasing the identity from the finite sum therefore gives sum_g |fixedBy V g|=p^(p*n)+(p^r-1)*p^n. Mathlib's MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group identifies this same sum with the number of actual orbits times |C_p^r|. Since the group has cardinality p^r, it follows that p^r divides p^(p*n)+(p^r-1)*p^n.

The private rank_le_of_burnside_divisibility supplies the substantive arithmetic step. Put q=p^((p-1)*n). The identity p*n=n+(p-1)*n and positivity of p^r and q rewrite the Burnside sum as p^n*(q-1)+p^r*p^n. Nat.dvd_add_iff_left removes the summand divisible by p^r, yielding p^r dividing p^n*(q-1). Because p≥2 and n>0, the exponent of q is positive, so p divides q. If p also divided q-1, Nat.dvd_add_iff_right and (q-1)+1=q would make p divide 1, contrary to primality. Hence q-1 is coprime to p and to p^r. Nat.Coprime.dvd_of_dvd_mul_right gives p^r dividing p^n, and Nat.pow_dvd_pow_iff_le_right gives r≤n. Multiplying by p gives r*p≤d. This includes p=2 and arbitrary r, with no rank cutoff.

All private declarations are consumed on this endpoint's proof path. The argument is a composition of the public norm-splitting results, the actual underlying-set action, classical finite-set Burnside counting and elementary prime-power divisibility; no literature novelty is claimed. The restricted-representation and invariant-subtype maps, field-module free/projective instances, finite subgroup and vector sets, orbit quotient, finrank transport and natural-number divisibility steps are all part of the Lean proof. The module has a single public theorem and asserts only this dimension lower bound.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing](PGroupProjectiveNormRing.md)
