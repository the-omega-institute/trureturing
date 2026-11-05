# A translated ten-column relative path

## Abstract

Translated ten-column action and exact relative paths in characteristic eleven

The ambient additive group is ZMod 11 times an arbitrary finite field K of characteristic eleven. Fix any nonzero u in K. The construction uses every nonzero first-coordinate vertex, including every zero row. It imposes no extension degree or generator-choice restriction. This is the translated construction; column translations are checked as actual affine maps and are not assumed to preserve directed differences.

**Theorem 1.1 (Every finite characteristic-eleven field and every nonzero endpoint).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)][\operatorname{Finite}(K)][\operatorname{CharP}(K,11)]\forall (u:K),u\neq 0\Rightarrow \operatorname{let} M=10\cdot\operatorname{card}(K)+1;\exists (v:\mathbb{N}\to \operatorname{ZMod}(11)\times K),\operatorname{v}(0)=(0,0)\land \operatorname{v}(M)=(0,u)\land \operatorname{Injective}((n:\operatorname{Fin}(M+1)\mapsto \operatorname{v}(n)))\land \operatorname{BijOn}(v,\operatorname{Ioo}(0,M),\{z:\operatorname{ZMod}(11)\times K|\operatorname{fst}(z)\neq 0\})\land \operatorname{BijOn}((n:\mathbb{N}\mapsto \operatorname{v}(n+1)-\operatorname{v}(n)),\operatorname{Iio}(M),\{z:\operatorname{ZMod}(11)\times K|\operatorname{fst}(z)\neq 0\}\cup \{(0,u)\})\land \operatorname{Injective}((k:\operatorname{Fin}(M+1)\mapsto \sum_{i<k}(\operatorname{v}(i+1)-\operatorname{v}(i))))\land (\forall (a:\mathbb{N}),\forall (b:\mathbb{N}),a<b\land b\le M\Rightarrow \sum_{a\le i<b}(\operatorname{v}(i+1)-\operatorname{v}(i))\neq 0)\land \sum_{i<M}(\operatorname{v}(i+1)-\operatorname{v}(i))=(0,u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicElevenDetour.exists_characteristic_eleven_relative_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put q=card(K), M=10q+1, B={(a,h):a is nonzero}, s=(0,0), and t=(0,u). The theorem supplies a natural-indexed vertex function v with v(0)=s and v(M)=t. Its M+1 bounded vertices are injective; its interior indices 0<n<M map bijectively onto B. Its M successive full vector differences map bijectively onto B union {(0,u)}. No value beyond the bounded path is prescribed. All M+1 bounded prefixes, including empty and full, are distinct. Every nonempty interval with 0<=a<b<=M has nonzero sum, and the full sum is (0,u).

Choose a generator r of the cyclic unit group of K. Natural powers of r exhaust all units, order(r)=q-1, and a bounded positive power r^k=2 exists with 1<=k<=q-2. Characteristic eleven excludes 2=0, 2=1 and 2=-1, so a generator cannot be -1. These are the only primitive exclusions needed by the translated lift.

The columns are d=(1,2,4,8,5,10,9,7,3,6). Their shifts are b=(0,u,u,0,0,0,-2u,2u,0,(1+2/r)u). Coordinates (i,x) represent (d_i,(-1)^i*x+b_i). The skew product advances i without changing x until phase nine, then returns to phase zero with row r*x. Conjugation gives the actual nine maps h -> -h+b_i+b_(i+1) and closing map h -> -r*h+(r+2)u. The inverse uses the inverse skew product and the inverse coordinates. A ten-step return is multiplication by r. The published RowOrbitLift.row_same_cycle_iff supplies precisely the two row orbits: zero and all nonzero rows. All ten phases of both are retained.

The heads (2,0),(1,2u),(7,0),(4,u) have normal coordinates (1,u),(0,2u),(7,2u),(2,0). On the long orbit the first three occur at times 1,10k,10k+7 in a traversal of length 10(q-1), in that strict order. The fourth head alone meets the zero-row orbit. Thus the actual first return is rho=(123)(4). For sigma=(1234), sigma*rho=(1324). The proof uses the published FiniteEndpointPairing.first_visit_reattach and same_cycle_of_first_visit and WeightedReattachment.untouched_reattach_iff. It proves every old orbit meets the cuts and that the induced return after endpoint insertion is a full six-cycle. Hence Q=(h1 s)(h1 t)*sigma*P is one cycle on the whole carrier, with Q(t)=s.

The actual physical predecessors are (1,u),(6,u),(9,0),(2,u). Their old labels are (1,-u),(6,u),(9,0),(2,0). The rewired labels are (0,u),(1,-u),(6,u),(9,0), and the edge s -> h1 supplies (2,0). A permutation of the punctured tail carrier proves equality of the full label inventories with multiplicity one; every uncut edge remains. The artificial closing edge t -> s has label (0,-u) and is deleted. Mathlib's IsCycleOn enumeration gives all bounded indices and exact counts. Telescoping gives each prefix v(n)-v(0) and each interval v(b)-v(a); bounded vertex injectivity proves the interval and prefix clauses.

The construction follows Characteristic eleven: row-return order and a translated ten-column lift, sections 2 and 4–6. This is a repository derivation of the specified translated construction using standard finite-field cyclicity and published orbit suppliers. No literature novelty is claimed. It proves only this full nonzero-column relative-path domain. The original arbitrary-subset parent and transport to its original coordinates remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicElevenDetour.exists_characteristic_eleven_relative_path`
- Dependency: [D5/S1/Words/Sequenceability/RowOrbitLift](../../../S1/Words/Sequenceability/RowOrbitLift.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment](../PerfectMatchings/WeightedReattachment.md)
