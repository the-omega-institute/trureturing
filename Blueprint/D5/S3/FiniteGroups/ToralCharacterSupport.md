# Complete Support for Toral Character Triples

## Abstract

Exactly C₂ × C₆ supports faithful pointwise projective character matches without a global match in the stated cyclic-product family.

**Definition 1.1 (Actual character triples).**

$$\forall G \in Type*,\; [Group\left(G\right)] Triple\left(G\right) = Fin\left(3\right) \to MonoidHom\left(G, Units\left(\mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.Triple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A triple is a function from Fin 3 to the homomorphisms G →* ℂˣ. The coordinates are actual complex-unit characters, indexed by 0, 1 and 2. Character multiplication below is pointwise multiplication.

**Definition 1.2 (Trivial projective kernel).**

$$\forall G \in Type*,\; [Group\left(G\right)] \forall X \in Triple\left(G\right),\; ProjectivelyFaithful\left(X\right) \Leftrightarrow \left(\forall g \in G,\; \left(\forall i \in Fin\left(3\right),\; \left(X_{i}\right)\left(g\right) = \left(X_{0}\right)\left(g\right)\right) \Rightarrow g = 1\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.ProjectivelyFaithful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A triple is projectively faithful when the only group element at which all three coordinate values coincide is the identity. Equivalently, the kernels of the two ratios X₁/X₀ and X₂/X₀ intersect trivially.

**Definition 1.3 (A scalar and permutation at each element).**

$$\forall G \in Type*,\; [Group\left(G\right)] \forall X \in Triple\left(G\right),\; \forall Y \in Triple\left(G\right),\; PointwiseMatched\left(X, Y\right) \Leftrightarrow \left(\forall g \in G,\; \exists l \in Units\left(\mathbb{C}\right),\; \exists p \in Perm\left(Fin\left(3\right)\right),\; \forall i \in Fin\left(3\right),\; \left(Y_{i}\right)\left(g\right) = l*\left(X_{p\left(i\right)}\right)\left(g\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.PointwiseMatched` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every element g, a nonzero complex scalar and a permutation match the three values. Both choices may depend on g. The definition permits equal coordinate values and repeated characters.

**Definition 1.4 (One character and one permutation).**

$$\forall G \in Type*,\; [Group\left(G\right)] \forall X \in Triple\left(G\right),\; \forall Y \in Triple\left(G\right),\; GloballyMatched\left(X, Y\right) \Leftrightarrow \left(\exists e \in MonoidHom\left(G, Units\left(\mathbb{C}\right)\right),\; \exists p \in Perm\left(Fin\left(3\right)\right),\; \forall i \in Fin\left(3\right),\; Y_{i} = e*X_{p\left(i\right)}\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.GloballyMatched` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A global match uses one homomorphism G →* ℂˣ and one permutation of Fin 3 for all elements. The displayed equalities are equalities of characters.

**Definition 1.5 (The support predicate).**

$$\forall G \in Type*,\; [Group\left(G\right)] Supports\left(G\right) \Leftrightarrow \left(\exists X \in Triple\left(G\right),\; \exists Y \in Triple\left(G\right),\; ProjectivelyFaithful\left(X\right) \land \left(ProjectivelyFaithful\left(Y\right) \land \left(PointwiseMatched\left(X, Y\right) \land \neg GloballyMatched\left(X, Y\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.Supports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Support requires two projectively faithful triples, pointwise matching, and the absence of a global match. No normalization or compatibility hypothesis is included in this predicate.

**Definition 1.6 (The actual source groups).**

$$\forall a \in Naturals,\; \forall b \in Naturals,\; \forall m \in Naturals,\; Source\left(a, b, m\right) = Cyclic\left(2^{a}\right) \times Cyclic\left(2^{b}*m\right)$$

*Formalization.* `D5/S3/FiniteGroups/ToralCharacterSupport.Source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cyclic n is the existing CyclicPrimePowerAction.Cyclic abbreviation for Multiplicative (ZMod n). For positive n this is a cyclic group of order n; Cyclic 1 is trivial. Source a b m is their actual direct product. The complete support theorem assumes a ≤ b, positive m and odd m.

**Theorem 1.7 (The complete support classification).**

$$\forall a \in Naturals,\; \forall b \in Naturals,\; \forall m \in Naturals,\; a\le b \Rightarrow \left(1\le m \Rightarrow \left(Odd\left(m\right) \Rightarrow \left(Supports\left(Source\left(a, b, m\right)\right) \Leftrightarrow \left(a = 1 \land \left(b = 1 \land m = 3\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/ToralCharacterSupport.support_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a, b and m with a ≤ b and positive odd m, Source a b m supports the specified pairs exactly when a=b=1 and m=3. The statement quantifies over all actual character triples through Supports. It includes a=0, trivial factors, m=1, repeated eigenvalues, and every higher power of two.

When a=0 the source is cyclic. Match at a generator and choose the twisting character as a quotient of two coordinate characters. Equality at the generator gives equality everywhere, including for the trivial group. For a≥1, the Chinese remainder equivalence ZMod.chineseRemainder gives Source a b m ≃ (Cyclic (2^a) × Cyclic (2^b)) × Cyclic m. Support is transported along this actual group equivalence.

Write P=Cyclic (2^a) × Cyclic (2^b) and O=Cyclic m. On P, a matching scalar has order dividing 2^b and its cube is the determinant quotient. Inverting 3 modulo 2^b therefore constructs a single character twist removing these scalars. A faithful triple on a noncyclic finite group has distinct coordinate characters: equality of two coordinates would make a remaining ratio an injective character into a finite cyclic group of roots of unity. The pinned linearIndependent_monoidHom theorem then turns equality of character sums into one permutation aligning the restrictions on P.

After this alignment, at every mixed element (p,o) the matching scalar has order dividing 2^b m. Its cube has order dividing m, because the determinant quotient is trivial on P. Coprimality forces its mth power to be one. Taking mth powers in each coordinate equality and using coprimality again proves that the pointwise permutation preserves the three values on P. These conclusions hold for every odd m.

If b≥2, P is noncyclic and has an element whose square is nonidentity. Faithfulness implies that one of the coordinate ratios has a value whose square is nonidentity. Three successive translates give three distinct values, so one avoids any two forbidden values. Applying this observation to the two ratios constructs one element p₀ on which the three coordinate values are distinct. At every (p₀,o), preservation of those values forces the permutation to be the identity. The odd-factor coordinate quotients consequently agree, supplying a global twisting character. This excludes all b≥2 for every odd m directly.

The remaining noncyclic primary group is C₂². Its faithful ratio map to μ₂ × μ₂ is injective and both groups have four elements, hence it is surjective. This supplies each singleton sign pattern. At an odd cyclic generator, a permitted permutation fixing the singleton is the identity or the complementary transposition. The identity would give a global match. After twisting the first odd coordinate to one, the transpositions for singleton coordinates 0 and 1 force both remaining coordinate values to have cube one. Faithfulness makes the generator's cube the identity, so m divides 3. For m=1 alignment already gives a global match, leaving precisely m=3.

For sufficiency use Γ=(μ₂ × μ₂) × μ₃ and the actual characters X(s,t,z)=(1,sz,tz⁻¹) and Y(s,t,z)=(1,sz⁻¹,tz). Their projective kernels are trivial since μ₂∩μ₃={1}. When s=t, interchange coordinates 1 and 2 with scalar one. When (s,t)=(1,−1), interchange coordinates 0 and 1 with scalar z⁻¹; when (s,t)=(−1,1), interchange coordinates 0 and 2 with scalar z. These exhaust the sign patterns. A global twist is trivial on μ₂² by its square and cube constraints; the distinct restricted characters force its permutation to be the identity. The first coordinate then forces the whole twist to be trivial, which would identify z and z⁻¹ for every cube root, contradicting that μ₃ has three elements. Cyclic/root-of-unity equivalences transport this pair to Source 1 1 3.

## References

- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.GloballyMatched`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.PointwiseMatched`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.ProjectivelyFaithful`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.Source`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.Supports`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.Triple`
- Truth anchor: `D5/S3/FiniteGroups/ToralCharacterSupport.support_iff`
- Dependency: [D5/S3/FiniteGroups/CyclicPrimePowerAction](CyclicPrimePowerAction.md)
