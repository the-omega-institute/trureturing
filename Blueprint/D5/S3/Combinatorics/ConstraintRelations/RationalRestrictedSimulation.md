# Constructive simulation with a multiplicative face equality

## Abstract

Finite restricted ternary factors preserve each full original assignment weight and the complete visible law.

**Definition 1.1 (Full-table restriction).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.Restricted`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.Restricted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restricted T means that the canonical normalized rational Table T is Strict and T(000)T(110)=T(100)T(010). Its eight entries are tested before assigning a scope. Consequently unvisited entries under identified scope variables retain positivity, support and normalization.

**Definition 1.2 (Normalized vertex activities).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.activityTable`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.activityTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive rational t the allowed entries 000,100,010,110,001 are respectively (1,t,1,t,1)/(3+2t), with zero at 101,011,111. Their sum is one and both sides of the face equality are t divided by the square of (3+2t). The canonical pinTable has all five allowed entries 1/5 and also satisfies the equality. At a zero pin o, activityTable on (u,o,o) supplies weight t when u is one and weight one when u is zero, divided by 3+2t. pinTable on (a,a,b) supplies the exclusion of simultaneous ones, divided by five.

**Definition 1.3 (The finite local factor list).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.LocalIndex`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.LocalIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LocalIndex is Unit plus ((Fin 3 plus Fin 4) plus Unit): one support factor, three edge factors, four activity factors and one top activity factor. Each entry is an actual normalized ternary Table, and repeated factors remain separate entries in the product.

**Definition 1.4 (Replacement on actual variable names).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localFactors`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localFactors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a Strict Table T and names x,y,z,o,p,q of an arbitrary type V, localFactors keeps the original ordered scope (x,y,z) as a pinTable support factor, implements the bottom binary table B(u,v)=T(u,v,0) by three edges and four activities, and appends the activity tau=T(001)/T(000) on (z,o,o). All names are actual variables. The parameters p,q are fresh hidden names in the local extension, while o is shared by the entire replacement network.

**Definition 1.5 (The local normalization scalar).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localScale`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary data consist of a shape, positive rational internal activities alpha,beta, positive terminal activities lambda,mu and scalar c. Write D=1/[5 cubed (3+2alpha)(3+2beta)(3+2lambda)(3+2mu)]. Then localScale(T,hT)=D c/[5(3+2tau)] is positive rational. It excludes the outer common pin and includes every edge and activity normalization in the nine local factors.

**Definition 1.6 (Retaining arbitrary original variables).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localExtension`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Factor f on V, the replacement variable type is V plus (Unit plus Bool). The injection of V retains every original variable. The Unit name is the common zero pin; the two Bool names are the fresh internal bits. Only the ordered original factor scope is passed to the local construction, so repeated or coincident terminals are permitted without an equality primitive.

**Theorem 1.7 (Pointwise complete local simulation).**

$$\forall V \in \mathrm{Type},\; \forall f \in \operatorname{Factor}\left(V\right),\; \forall hf \in \operatorname{Strict}\left(\operatorname{table}\left(f\right)\right),\; {\forall i \in \mathrm{LocalIndex},\; \operatorname{Restricted}\left(\operatorname{table}\left(\operatorname{localExtension}\left(f, hf, i\right)\right)\right)} \land {{0 < \operatorname{localScale}\left(\operatorname{table}\left(f\right), hf\right)} \land {\forall b \in (V) \to \mathrm{Bool},\; \sum_{h \in (\mathrm{Bool}) \to \mathrm{Bool}} {\prod_{i \in \mathrm{LocalIndex}} {\operatorname{value}\left(\operatorname{localExtension}\left(f, hf, i\right), \operatorname{sumElim}\left(b, \operatorname{sumElim}\left(\operatorname{const}\left(\mathrm{Unit}, \mathrm{false}\right), h\right)\right)\right)}} = {\operatorname{localScale}\left(\operatorname{table}\left(f\right), hf\right)} \cdot {\operatorname{value}\left(f, b\right)}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.local_simulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type V, every canonical Factor f on V and proof hf that its full table is Strict, all local replacement factors are Restricted, localScale is positive, and for every complete original assignment b, summing every assignment h of both fresh bits with the common pin set to zero gives localScale times f.value(b). The formula writes sumElim for the canonical Sum.elim operation and const(Unit,false) for the constant zero pin assignment. The scalar depends on the original table, never on b. This is an identity on all eight formal triples and therefore remains valid after arbitrary terminal identifications.

The binary construction is explicit. Put r=B(0,0)B(1,1)/(B(1,0)B(0,1)). When r=1 use internal activities alpha=beta=1 and three harmless edges to the shared zero. The two free hidden bits give the constant matrix M=4. When r>1 use alpha=r-1,beta=1, edges u-p and p-v, and a harmless edge from v to the zero pin. Summing the isolated q gives M=2 times the matrix with rows (r,1) and (1,1). When r<1 use alpha=2/r-1 and beta=2(1-r)/r with the path u-p-q-v. Its rows are (1+alpha+beta,1+alpha) and (1+beta,1). Every case has positive rational entries and M(0,0)M(1,1)=r M(1,0)M(0,1).

Set c=M(0,0)/B(0,0), lambda=B(1,0)M(0,0)/(B(0,0)M(1,0)), and mu=B(0,1)M(0,0)/(B(0,0)M(0,1)). The terminal activities give lambda to the power u times mu to the power v times M(u,v)=c B(u,v) at all four inputs. Both terminal activities and all internal activities use activityTable. The two unused bits in the flat case are freely summed, rather than discarded. No additional zero pin is introduced by these padding slots. Finally T(x,y,z)=pinRaw(x,y,z)B(x,y)tau to the power z at all eight triples, including the three forbidden ones.

**Definition 1.8 (All hidden names).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementHidden`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementHidden` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReplacementHidden(m,k)=Fin m plus (Unit plus (Fin k times Bool)). The original hidden variables remain present even when no factor mentions them. One Unit variable supplies the single shared pin, and each original factor receives its own two fresh bits.

**Definition 1.9 (The global factor list).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementIndex`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReplacementIndex(k)=Unit plus (Fin k times LocalIndex). The first factor is pinTable on the single shared pin repeated three times. Every original factor then contributes its nine local factors. In particular k=0 leaves precisely the common pin factor.

**Definition 1.10 (Embedding before numbering).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.originalEmbedding`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.originalEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical original variable type Fin n plus Fin m embeds into Fin n plus ReplacementHidden(m,k) by the identity on visible labels and the first injection on old hidden labels.

**Definition 1.11 (The actual restricted family).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementFamily`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

replacementFamily(net,hs) constructs the one common pin and each localFactors family on the injected original scope, using the private pair (j,false),(j,true) for old factor j. All factors are canonical Factor values with full Restricted tables. Different old factors may share any original variable or their entire scopes.

**Definition 1.12 (The canonical replacement network).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacement`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

replacement(net,hs) is numberedNetwork applied to replacementFamily. It has the original visible count n, hidden count card(ReplacementHidden(m,k)) and factor count card(ReplacementIndex(k)). Finite equivalences number hidden names and factors while leaving visible labels fixed.

**Definition 1.13 (Complete assignment extension).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.extendAssignment`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.extendAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

extendAssignment(b,h) assigns every old visible or hidden variable its value in b, and every fresh variable its value in h. Its domain is Fin n plus ReplacementHidden(m,k), and h ranges over every function from Unit plus (Fin k times Bool) to Bool.

**Definition 1.14 (The one-pin global scalar).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementScale`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

replacementScale(net,hs)=(1/5) times the product over all original factors j of localScale((net.factor j).table,hs j). It is positive and assignment independent. When k=0 the product is one, so this scalar is exactly 1/5.

**Definition 1.15 (Embedding into actual numbered output variables).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedEmbedding`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

numberedEmbedding is identity on visible labels. On an original hidden label it first injects into ReplacementHidden and then applies its canonical equivalence to Fin(card ReplacementHidden). It is injective, preserving all original distinctions and all identifications in a scope.

**Definition 1.16 (Assignments on the actual numbered output).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedAssignment`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

numberedAssignment(b,h) composes extendAssignment(b,h) with inverse hidden numbering. Evaluation at numberedEmbedding(v) is exactly b(v), for every old variable v and every fresh assignment h.

**Theorem 1.17 (Complete finite-network replacement).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall net \in \operatorname{Network}\left(n, m, k\right),\; \forall hs \in \left(\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Strict}\left(\operatorname{table}\left(\operatorname{factor}\left(net, j\right)\right)\right)\right),\; {\operatorname{Injective}\left(\operatorname{numberedEmbedding}\left(n, m, k\right)\right)} \land {{\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{apply}\left(\operatorname{numberedEmbedding}\left(n, m, k\right), \operatorname{inl}\left(i\right)\right) = \operatorname{inl}\left(i\right)} \land {{\forall b \in (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)) \to \mathrm{Bool},\; \forall h \in (\operatorname{Sum}\left(\mathrm{Unit}, \operatorname{Prod}\left(\operatorname{Fin}\left(k\right), \mathrm{Bool}\right)\right)) \to \mathrm{Bool},\; \forall v \in \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \operatorname{apply}\left(\operatorname{numberedAssignment}\left(b, h\right), \operatorname{apply}\left(\operatorname{numberedEmbedding}\left(n, m, k\right), v\right)\right) = \operatorname{apply}\left(b, v\right)} \land {{\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{scope}\left(\operatorname{factor}\left(\operatorname{replacement}\left(net, hs\right), \operatorname{equivFin}\left(\operatorname{ReplacementIndex}\left(k\right), \operatorname{inr}\left(\operatorname{pair}\left(j, \operatorname{inl}\left(\mathrm{unit}\right)\right)\right)\right)\right)\right) = \operatorname{triple}\left(\operatorname{apply}\left(\operatorname{numberedEmbedding}\left(n, m, k\right), \operatorname{fst}\left(\operatorname{scope}\left(\operatorname{factor}\left(net, j\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{numberedEmbedding}\left(n, m, k\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{scope}\left(\operatorname{factor}\left(net, j\right)\right)\right)\right)\right), \operatorname{apply}\left(\operatorname{numberedEmbedding}\left(n, m, k\right), \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{scope}\left(\operatorname{factor}\left(net, j\right)\right)\right)\right)\right)\right)} \land {{\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ReplacementIndex}\left(k\right)\right)\right),\; \operatorname{Restricted}\left(\operatorname{table}\left(\operatorname{factor}\left(\operatorname{replacement}\left(net, hs\right), i\right)\right)\right)} \land {{0 < \operatorname{replacementScale}\left(net, hs\right)} \land {{\forall b \in (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)) \to \mathrm{Bool},\; \sum_{h \in (\operatorname{Sum}\left(\mathrm{Unit}, \operatorname{Prod}\left(\operatorname{Fin}\left(k\right), \mathrm{Bool}\right)\right)) \to \mathrm{Bool}} {\prod_{i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ReplacementIndex}\left(k\right)\right)\right)} {\operatorname{value}\left(\operatorname{factor}\left(\operatorname{replacement}\left(net, hs\right), i\right), \operatorname{numberedAssignment}\left(b, h\right)\right)}} = {\operatorname{replacementScale}\left(net, hs\right)} \cdot {\prod_{j \in \operatorname{Fin}\left(k\right)} {\operatorname{value}\left(\operatorname{factor}\left(net, j\right), b\right)}}} \land {{0 < \operatorname{partition}\left(net\right)} \land {{0 < \operatorname{partition}\left(\operatorname{replacement}\left(net, hs\right)\right)} \land {{\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; \operatorname{marginal}\left(\operatorname{replacement}\left(net, hs\right), a\right) = {\operatorname{replacementScale}\left(net, hs\right)} \cdot {\operatorname{marginal}\left(net, a\right)}} \land {{\operatorname{partition}\left(\operatorname{replacement}\left(net, hs\right)\right) = {\operatorname{replacementScale}\left(net, hs\right)} \cdot {\operatorname{partition}\left(net\right)}} \land {\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; \operatorname{law}\left(\operatorname{replacement}\left(net, hs\right), a\right) = \operatorname{law}\left(net, a\right)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural n,m,k, every canonical Network net and proof hs that all original full tables are Strict, the numbered embedding is injective and fixes every visible label. Extended assignment evaluation preserves every old variable. The designated support factor of each old factor has precisely its injected original ordered scope. Every output factor is Restricted and the scalar C=replacementScale(net,hs) is positive. For each fixed full original assignment, summing all fresh assignments of the actual numbered replacement multiplies its old complete product by C. Both partitions are positive; every visible marginal is multiplied by C; the partition is multiplied by C; and the full normalized visible law agrees at every assignment.

For a fixed complete original assignment, finite equivalences separate the common pin and the private pairs, then curry the private assignments into one two-bit assignment per old factor. The shared pin kills the entire branch where it is one. On its zero branch, Fintype.prod_sum separates all private hidden sums, giving C times the original product. This computation includes every fresh assignment; excluded assignments have zero weight through actual factors. Summing subsequently over every original hidden assignment gives the marginal identity. The positive original partition and positive C give a positive new partition; division gives identical laws.

With no old factors, the original hidden variables still range over their full Boolean cube and contribute their entire multiplicity. The single additional pin multiplies every original complete assignment weight by 1/5. The proof allows zero visible variables as well as all n at least one, arbitrary original hidden sets, repeated coordinates and completely coincident scopes. It supplies a finite rational replacement, without a size optimality, inference efficiency, causal kernel or sampling interpretation. Source classification and application corollaries are separate results.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.LocalIndex`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementHidden`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.ReplacementIndex`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.Restricted`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.activityTable`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.extendAssignment`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localExtension`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localFactors`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.localScale`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.local_simulation`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedAssignment`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.numberedEmbedding`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.originalEmbedding`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacement`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementFamily`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.replacementScale`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.result`
- Dependency: [D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization](RationalPositiveRealization.md)
