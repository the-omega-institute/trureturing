# The weighted persistent Hodge theorem

## Abstract

Weighted persistent Hodge representatives for actual finite simplicial homology.

**Definition 1.1 (Real chains with positive weights).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.WeightedModule`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.WeightedModule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Let I be any finite type, M any abelian group with a specified integer module structure, a an integer basis of M indexed by I, and w:I→Real any function with w(i)>0 for every i. WeightedModule is Real tensor over Integer with M. Its coefficient equivalence is the base change of a. Dividing each coefficient by sqrt(w(i)) identifies it with the ordinary Euclidean space on I and induces its norm and inner product. Empty I is included.

**Theorem 1.2 (The exact reciprocal-weight metric).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every I, M, a and positive w as above and every pair of real chains x,y, inner(x,y) = sum over i in I of coefficient(x,i) coefficient(y,i) / w(i). The weights may be arbitrary positive reals. The statement assumes no common positive lower bound or upper bound. The inner product is obtained by pulling back Euclidean coordinates, so every subsequent adjoint uses this metric.

**Definition 1.3 (Genuine categorical homology classes).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.cycleClass`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.cycleClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every short complex A→B→C of real modules, cycleClass is the canonical map from the kernel of B→C to Mathlib's actual categorical homology. It uses moduleCatCyclesIso and homologyπ. Its kernel consists precisely of incoming boundaries. For a map of short complexes, cycleMap restricts the actual middle chain map to the cycle kernels, and imageClass takes its target homology class. Naturality identifies its range with the range of the actual induced ShortComplex.homologyMap.

**Definition 1.4 (All admissible incoming chains).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.FillingDomain`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.FillingDomain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For a map φ from A→B→C to X→Y→Z, FillingDomain is {u in X | b(u) lies in range(i)}, where b:X→Y is the target incoming boundary and i:B→Y is the middle component of φ. It is a linear inverse image, so cancellation among arbitrary linear combinations is retained. When i is injective, restrictedBoundary T sends u to the unique vector of B with i(T(u))=b(u). The metric on its domain is inherited from X.

**Definition 1.5 (The persistent operator).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Take abelian real modules A,Y,Z and finite real inner product spaces B,C,X. Let f:A→B, d:B→C, b:X→Y and e:Y→Z be linear, with d f=0 and e b=0. Let φ be any commuting map of these two short complexes whose middle component i is injective. With T the restricted incoming boundary, the operator on B is Delta = T T* + d* d. The star denotes the adjoint for the given metrics, including the inherited domain metric.

**Theorem 1.6 (The energy criterion).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every choice of the six real modules, metrics, four differentials and commuting short-complex map described above, every proof that its middle component is injective, and every x in B, Delta(x)=0 if and only if T*(x)=0 and d(x)=0. The sum of the squared norms of these two vectors equals inner(Delta(x),x). Positivity gives both vanishing conditions even when the spaces or differentials have rank zero.

**Definition 1.7 (Canonical harmonic representatives).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

In addition assume that φ's component C→Z is injective. Restricted incoming boundaries then lie in ker(d), and their image in this cycle space is exactly ker(imageClass). OmegaMath.Topology.PersistentHodge owns the full pullback witness theorem, energy criterion, harmonic classification and uniqueness, and the linear construction of a harmonic representative of every cycle modulo filling boundaries. The mixed model interprets its carriers and operations in these unchanged real chain spaces. fillingPairEquiv is a linear equivalence from the entire inverse-image domain to coherent pairs; fillingPair_inner preserves its inherited first-component form. strictPullbackEquiv identifies those pairs with the strict representation, while strictAdjoints_laws identifies both adjoints through their actual inner-product identities. Mathlib's starProjection supplies an ordinary orthogonal splitting of the incoming range. The strict representative theorem proves surjectivity and its uniqueness theorem proves injectivity of the canonical harmonic-to-image map. The homology interpretation reuses moduleCatHomologyIso and Quotient.mk_eq_zero; persistent exactness, energy and harmonic representatives are not model premises. Only the single-window core has a strict zero-axiom scope; the real metric, native homology and actual simplicial realization remain mixed consumers.

**Theorem 1.8 (The included representative).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For all the same data, both injectivity proofs, and every x in ker(Delta), the value of harmonicEquivImage at x, regarded as a target homology class, equals cycleClass of cycleMap applied to the underlying cycle x. Thus the equivalence sends a harmonic vector to the class of its actual included chain.

**Definition 1.9 (Every natural degree and the zero differential).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.realComplex`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.realComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Let P(n) be a finite real inner product space for every natural n, with linear maps d(n):P(n+1)→P(n) satisfying d(n)d(n+1)=0 for every n. realComplex is the actual full Mathlib chain complex with these terms. outgoing is zero at n=0 and d(n) at degree n+1. window computes its ordinary homology in degree q using the incoming map d(q) and this outgoing differential. windowIso compares it to the actual chain complex's short complex; it includes q=0. No truncation index is introduced.

**Definition 1.10 (The actual full-complex image).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Let Q(n), b(n) be a second such family, and i(n):P(n)→Q(n) injective linear maps in every natural degree, commuting with the successive differentials. For every natural q, naturalHodgeEquiv is a real linear equivalence from the kernel of the corresponding persistent Laplacian to range(HomologicalComplex.homologyMap(realChainMap i,q)). Homology naturality across windowIso transports the short-complex equivalence to this actual homology map.

**Theorem 1.11 (Harmonic chains are ordinary cycles).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodge_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodge_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every pair of natural-degree families P,Q, square-zero boundary families d,b and commuting injective family i as above, every natural q and every harmonic q-chain x, outgoing(d,q)(x)=0. At q=0 this is the unaugmented zero differential.

**Theorem 1.12 (The actual homology-class formula).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every such full family and every degree q and harmonic chain x, naturalHodgeEquiv(x), regarded in target homology, equals includedClass(x). includedClass takes the actual included cycle, forms its ordinary short-complex homology class and applies the inverse of the canonical homology comparison. The middle component of windowIso and its inverse is the identity on q-chains. Naturality of cycleClass therefore identifies includedClass with the actual short-complex cycle projection in the target realComplex at the unchanged included chain i(q)(x). This is the class [i(q)(x)] in the actual target chain-complex homology.

**Definition 1.13 (Real chains on every actual face).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Chain`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Chain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Let V be any finite linearly ordered vertex type, K and L any pre-abstract simplicial complexes on V with K contained in L, and q any natural number. A q-face is an actual face with q+1 vertices, ordered by the vertex order. The integer free face modules, rank-signed deletion boundaries and their square-zero proof are those of FiniteSimplicialSingularHomology. Chain is their scalar extension to Real on chains, before taking homology. The original coordinate equivalence supplies the increasing-face basis. In each degree coefficients identify the chains with all real functions on faces.

**Definition 1.14 (All positive real face weights).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Weights`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Weights` (`✓ std3`).

*Citation.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

Weights supplies a strictly positive real number on every face of L in every natural degree. Its restriction to K uses the identical underlying face. The inner product of chains x,y in degree r is the sum of x(s)y(s)/w(r,s) over actual r-faces. The coefficient metric of WeightedModule gives exactly this inner product on both complexes. No lower or uniform weight bound is assumed.

**Definition 1.15 (Actual zero extension and homology).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.chainInclusion`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.chainInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

The integer inclusion sends each actual face generator of K to that same face generator of L. Its coefficient retraction splits it, and signed face deletion commutes with it. Scalar extension therefore gives injective real zero-extension maps in every degree and a genuine map chainInclusion of the full real simplicial chain complexes. The homology map is HomologicalComplex.homologyMap of this chain map. No identification between scalar extension of homology and homology of scalar extension is assumed.

**Definition 1.16 (The restricted weighted operator).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentLaplacian`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentLaplacian` (`✓ std3`).

*Citation.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

In degree q let U be all chains c of degree q+1 in L whose ordinary boundary belongs to the range of zero extension from degree q of K. U has the inherited weighted inner product. Let T:U→Cq(K) be the unique restricted boundary satisfying i(Tc)=boundary(c). Let D be the outgoing boundary on K, zero at q=0 and the ordinary signed boundary in positive degrees. The operator is Delta = T T* + D* D. Its adjoints use these exact weighted inner products. U includes all linear combinations with cancelling hidden boundary, rather than only individually retained simplices.

**Definition 1.17 (Harmonic chains and the actual image).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentHodgeEquiv`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentHodgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every V, K, L, inclusion, positive weight family and natural degree specified above, persistentHodgeEquiv is a real linear equivalence from ker(Delta) to the range of the actual induced real simplicial homology map Hq(K)→Hq(L). Its construction uses the harmonic orthogonal complement of cycles killed by L filling chains, followed by the canonical comparison with actual chain-complex homology.

**Definition 1.18 (The included homology class).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicClass`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every harmonic chain h, harmonicClass forms the ordinary homology class of its included chain. It is defined using the actual chain map on cycle kernels and the canonical short-complex comparison, independently of persistentHodgeEquiv.

**Theorem 1.19 (The complete weighted theorem).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_persistent_hodge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_persistent_hodge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Facundo Mémoli, Zhengchao Wan and Yusu Wang (2022). *Persistent Laplacians — Properties, Algorithms and Implications*. DOI: [10.1137/21M1435471](https://doi.org/10.1137/21M1435471). URL: <https://arxiv.org/html/2012.02808v3>.

*Commentary.*

For every finite linearly ordered V, every finite simplicial inclusion K contained in L, every natural q, and every strictly positive real weight on every face of L in each degree, both the L and restricted K inner products equal their coefficient sums sum_s x(s)y(s)/w(r,s) in every degree r. In every degree the coefficient of an included chain at a face of K equals its original coefficient, and its coefficient at any face outside K is zero. For every harmonic q-chain h the equivalence sends h to [i(q)(h)] in the actual homology of L. In particular the real finrank of ker(Delta) equals the real finrank of the range of Hq(chainInclusion). Empty face sets, all degrees above dimension, K=L, disconnected complexes, zero boundary ranks and classes killed only by new filling chains in L are included. There is no homology-vanishing, boundary-invertibility, lower-weight-bound or uniform-weight-bound hypothesis. The nullity equality is Theorem 2.7 of Mémoli, Wan and Wang; the explicit canonical representative equivalence is the chain-level interface established here, rather than a verbatim quotation of that theorem.

## References

- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Chain`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.FillingDomain`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.WeightedModule`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.Weights`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.chainInclusion`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.cycleClass`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicClass`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.harmonicEquivImage_apply`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.laplacian_eq_zero`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodgeEquiv_apply`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.naturalHodge_cycle`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentHodgeEquiv`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.persistentLaplacian`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.realComplex`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_inner`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.weighted_persistent_hodge`
- Dependency: [D5/S3/Geometry/SimplicialPersistence/OrderedChains](OrderedChains.md)
